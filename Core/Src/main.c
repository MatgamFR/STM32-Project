/**
 ******************************************************************************
 * @file    main.c
 * @brief   Liaison chiffree entre 2 STM32, chacune reliee a un PC.
 *          Les DEUX PC peuvent envoyer un message a l'autre.
 *
 * PROGRAMME UNIQUE : meme binaire sur les deux cartes, aucun #define de role.
 *
 * Principe :
 *   - Au demarrage, chaque carte est "en attente d'initialisation" (LED 0,5 Hz).
 *   - La carte dont le PC envoie un message devient MAITRE (emetteur) : elle
 *     genere une cle aleatoire 32 bits, l'envoie dans une trame CMD_INIT, puis
 *     envoie le message CHIFFRE dans une trame CMD_MSG.
 *   - L'autre carte applique la configuration (cle, position) et devient
 *     ESCLAVE (recepteur) : elle verifie le CRC, repond CMD_ACK, DECHIFFRE le
 *     message et l'affiche sur son serial monitor.
 *   - Si le PC de l'esclave envoie ensuite un message, les roles s'inversent
 *     (nouvelle cle, nouveau CMD_INIT).
 *   - 3 appuis sur le bouton USER -> CMD_RESET : les deux cartes repartent en
 *     attente d'initialisation.
 *
 * Cible : NUCLEO-F446RE (HAL, HSI 16 MHz, aucune config CubeMX necessaire).
 *   USART2 (PA2/PA3)   : PC via ST-Link (serial monitor)
 *   USART1 (PA9/PA10)  : lien vers l'autre carte (donnees + ACK, full duplex)
 *   Cablage : PA9 (TX) -> PA10 (RX) de l'autre carte
 *             PA10 (RX) <- PA9 (TX) de l'autre carte
 *             GND <-> GND
 *   LED : PA5 (LD2)    Bouton USER : PC13 (actif a l'etat bas)
 *
 * NOTE : si CubeMX a genere stm32f4xx_it.c avec USART1/2_IRQHandler, supprimez
 * ces handlers (ils sont definis dans ce fichier).
 ******************************************************************************
 */

#include "stm32f4xx_hal.h"
#include "protocol_icd.h"

#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <stdbool.h>

/* ========================================================================== */
/*                              CONFIGURATION                                 */
/* ========================================================================== */

/* Parametres de fiabilite (EXG-COM-04) : [X] et [N] */
#define ACK_TIMEOUT_MS      300u    /* [X] ms d'attente d'un ACK               */
#define MAX_RETRIES         3u      /* [N] tentatives                          */

#define UART_BAUDRATE       115200u
#define FRAME_SIZE          (sizeof(ProtocolMessage_t))
#define FRAME_TIMEOUT_MS    50u     /* silence max au milieu d'une trame        */
#define FAULT_LED_MS        1500u   /* duree de signalisation d'un defaut       */
#define BTN_DEBOUNCE_MS     50u
#define BTN_WINDOW_MS       2000u   /* 3 appuis dans cette fenetre = RESET      */
#define BTN_PRESS_COUNT     3u

#define INIT_PAYLOAD_LEN    5u      /* cle (4 octets LE) + position (1 octet)   */

#define LED_PORT            GPIOA
#define LED_PIN             GPIO_PIN_5
#define BTN_PORT            GPIOC
#define BTN_PIN             GPIO_PIN_13

/* ========================================================================== */
/*                               VARIABLES                                    */
/* ========================================================================== */

typedef enum { ST_WAIT_INIT = 0, ST_SYNCED } BoardState_t;
typedef enum { ROLE_NONE = 0, ROLE_MASTER, ROLE_SLAVE } Role_t;
typedef enum { RX_NONE = 0, RX_OK, RX_BAD_CRC, RX_BAD_LEN } RxStatus_t;
typedef enum { EV_NONE = 0, EV_ACK, EV_ERROR } RxEvent_t;

#define RING_SIZE 256u
typedef struct {
    volatile uint8_t  buf[RING_SIZE];
    volatile uint16_t head;
    volatile uint16_t tail;
} Ring_t;

static UART_HandleTypeDef huart_pc;     /* USART2 : PC            */
static UART_HandleTypeDef huart_link;   /* USART1 : autre carte   */

static Ring_t  rb_pc, rb_link;
static uint8_t rx_pc, rx_link;                    /* octet courant en reception IT */

/* Parseur de trames du lien */
static uint8_t  frame_buf[sizeof(ProtocolMessage_t)];
static uint8_t  frame_idx   = 0;
static uint32_t frame_tlast = 0;

static uint32_t     g_board_id    = 0;            /* derive de l'UID du MCU */
static BoardState_t g_state       = ST_WAIT_INIT;
static Role_t       g_role        = ROLE_NONE;
static uint32_t     g_key         = 0;
static uint8_t      g_position    = 0;
static uint32_t     g_fault_until = 0;
static bool         g_initiating  = false;        /* INIT en cours d'emission     */
static bool         g_preempted   = false;        /* collision perdue (voir plus bas) */

/* ========================================================================== */
/*                              PROTOTYPES                                    */
/* ========================================================================== */

static void Error_Handler(void);
static void gpio_init(void);
static void uart_init(UART_HandleTypeDef *h, USART_TypeDef *inst, IRQn_Type irq);

/* ========================================================================== */
/*                             OUTILS GENERIQUES                              */
/* ========================================================================== */

static void ring_put(Ring_t *r, uint8_t b)
{
    uint16_t n = (uint16_t)((r->head + 1u) & (RING_SIZE - 1u));
    if (n != r->tail) { r->buf[r->head] = b; r->head = n; }
}

static bool ring_get(Ring_t *r, uint8_t *b)
{
    if (r->tail == r->head) return false;
    *b = r->buf[r->tail];
    r->tail = (uint16_t)((r->tail + 1u) & (RING_SIZE - 1u));
    return true;
}

/* Log vers le serial monitor (PC) */
static void pc_log(const char *fmt, ...)
{
    char    line[160];
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(line, sizeof(line), fmt, ap);
    va_end(ap);
    if (n < 0) return;
    if (n > (int)sizeof(line) - 1) n = (int)sizeof(line) - 1;
    HAL_UART_Transmit(&huart_pc, (uint8_t *)line, (uint16_t)n, 200);
}

static void pc_hex(const char *prefix, const uint8_t *d, uint8_t len)
{
    char line[96];
    int  n = snprintf(line, sizeof(line), "%s", prefix);
    for (uint8_t i = 0; i < len && n < (int)sizeof(line) - 4; i++)
        n += snprintf(line + n, sizeof(line) - (size_t)n, "%02X ", d[i]);
    pc_log("%s\r\n", line);
}

/* CRC-16/CCITT-FALSE (poly 0x1021, init 0xFFFF) - EXG-TRM-06 */
static uint16_t crc16(const uint8_t *data, size_t len)
{
    uint16_t crc = 0xFFFFu;
    while (len--) {
        crc ^= (uint16_t)((uint16_t)(*data++) << 8);
        for (uint8_t i = 0; i < 8; i++)
            crc = (crc & 0x8000u) ? (uint16_t)((crc << 1) ^ 0x1021u) : (uint16_t)(crc << 1);
    }
    return crc;
}

/* ========================================================================== */
/*                         CHIFFREMENT (XOR + keystream)                      */
/* ========================================================================== */
/* Flux pseudo-aleatoire xorshift32 initialise avec la cle de 32 bits.
 * Symetrique : la meme fonction chiffre et dechiffre.
 * ATTENTION : chiffrement pedagogique, pas de securite cryptographique reelle. */
static void cipher_xor(uint8_t *data, uint8_t len, uint32_t key)
{
    uint32_t s = key ? key : 0xA5A5A5A5u;
    for (uint8_t i = 0; i < len; i++) {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        data[i] ^= (uint8_t)(s >> 24);
    }
}

static uint32_t mix32(uint32_t s)
{
    s ^= s >> 16; s *= 0x85EBCA6Bu;
    s ^= s >> 13; s *= 0xC2B2AE35u;
    s ^= s >> 16;
    return s;
}

/* EXG-MAI-01 : generation de la cle 32 bits.
 * Entropie : ID unique du MCU + compteur de cycles + SysTick + temps.
 * Si votre MCU a un RNG materiel (F4x9, L4, G4...), preferez HAL_RNG_GenerateRandomNumber(). */
static uint32_t generate_key(void)
{
    uint32_t s = mix32(HAL_GetUIDw0() ^ HAL_GetUIDw1() ^ HAL_GetUIDw2()
                       ^ DWT->CYCCNT ^ (HAL_GetTick() << 10) ^ SysTick->VAL);
    return s ? s : 1u;
}

/* ========================================================================== */
/*                                   LED                                      */
/* ========================================================================== */

static void led_set(bool on)
{
    HAL_GPIO_WritePin(LED_PORT, LED_PIN, on ? GPIO_PIN_SET : GPIO_PIN_RESET);
}

static void led_fault(void)                       /* EXG-DIA-05 */
{
    g_fault_until = HAL_GetTick() + FAULT_LED_MS;
}

static void led_update(void)
{
    static uint32_t t_toggle = 0;
    static bool     level = false;
    uint32_t now = HAL_GetTick();

    if ((int32_t)(g_fault_until - now) > 0) {             /* defaut : 5 Hz     */
        if (now - t_toggle >= 100u) { t_toggle = now; level = !level; led_set(level); }
    } else if (g_state == ST_WAIT_INIT) {                 /* attente : 0,5 Hz  */
        if (now - t_toggle >= 1000u) { t_toggle = now; level = !level; led_set(level); }
    } else {                                              /* synchronise : fixe*/
        led_set(true);
        level = true;
    }
}

/* ========================================================================== */
/*                       TRAMES : CONSTRUCTION / RECEPTION                    */
/* ========================================================================== */

/* EXG-TRM-01..06 */
static void frame_build(ProtocolMessage_t *m, CommandType_t cmd,
                        const uint8_t *data, uint8_t len)
{
    if (len > MAX_PAYLOAD_SIZE) len = MAX_PAYLOAD_SIZE;           /* TRM-04 */
    memset(m, 0, sizeof(*m));
    m->header.start_byte   = ICD_START_BYTE;                      /* TRM-02 */
    m->header.command_type = (uint8_t)cmd;                        /* TRM-03 */
    m->header.length       = len;                                 /* TRM-04 */
    m->header.reserve      = 0;
    m->header.id_src       = g_board_id;                          /* TRM-05 */
    if (len && data) memcpy(m->payload, data, len);
    m->crc = crc16((const uint8_t *)m, sizeof(*m) - sizeof(m->crc)); /* TRM-06 */
}

static void link_tx(CommandType_t cmd, const uint8_t *data, uint8_t len)
{
    ProtocolMessage_t m;
    frame_build(&m, cmd, data, len);
    HAL_UART_Transmit(&huart_link, (uint8_t *)&m, (uint16_t)sizeof(m), 200);
}

/* Machine d'etat de reception d'une trame, octet par octet.
 * - TRM-07 : tout octet hors trame different de ICD_START_BYTE est rejete.
 * - TRM-08 : length > MAX_PAYLOAD_SIZE -> RX_BAD_LEN.
 * - CRC invalide -> RX_BAD_CRC. */
static RxStatus_t link_poll(ProtocolMessage_t *out)
{
    uint8_t b;
    while (ring_get(&rb_link, &b)) {
        uint32_t now = HAL_GetTick();
        if (frame_idx > 0 && (now - frame_tlast) > FRAME_TIMEOUT_MS)
            frame_idx = 0;                        /* trame tronquee : resynchro */
        frame_tlast = now;

        if (frame_idx == 0 && b != ICD_START_BYTE)
            continue;                             /* TRM-07 : rejet              */

        frame_buf[frame_idx++] = b;
        if (frame_idx == FRAME_SIZE) {
            frame_idx = 0;
            memcpy(out, frame_buf, FRAME_SIZE);
            if (out->header.length > MAX_PAYLOAD_SIZE)
                return RX_BAD_LEN;                /* TRM-08                      */
            if (out->crc != crc16(frame_buf, FRAME_SIZE - sizeof(out->crc)))
                return RX_BAD_CRC;
            return RX_OK;
        }
    }
    return RX_NONE;
}

static void send_ack(uint8_t acked_cmd)           /* EXG-COM-01 */
{
    link_tx(CMD_ACK, &acked_cmd, 1);
}

static void send_error(uint8_t code)              /* EXG-COM-02 / COM-05 */
{
    link_tx(CMD_ERROR, &code, 1);
}

/* ========================================================================== */
/*                          ETATS / RESET (EXG-DIA-02)                        */
/* ========================================================================== */

static void reset_local(void)
{
    g_key      = 0;
    g_position = 0;
    g_role     = ROLE_NONE;
    g_state    = ST_WAIT_INIT;
    pc_log("[%08lX] En attente d'initialisation\r\n", (unsigned long)g_board_id);
}

/* ========================================================================== */
/*                    TRAITEMENT DES REQUETES DE L'AUTRE CARTE                */
/* ========================================================================== */

static void handle_request(const ProtocolMessage_t *m)
{
    switch (m->header.command_type) {

    case CMD_INIT:                                        /* EXG-ESC-01 */
        if (m->header.length < INIT_PAYLOAD_LEN) { send_error(CMD_INIT); led_fault(); break; }

        /* Collision : les deux cartes initialisent en meme temps.
         * La carte d'id le plus petit gagne et ignore le INIT de l'autre. */
        if (g_initiating && g_board_id < m->header.id_src)
            break;

        send_ack(CMD_INIT);
        g_key = (uint32_t)m->payload[0] | ((uint32_t)m->payload[1] << 8) |
                ((uint32_t)m->payload[2] << 16) | ((uint32_t)m->payload[3] << 24);
        g_position = m->payload[4];
        g_role     = ROLE_SLAVE;
        g_state    = ST_SYNCED;
        if (g_initiating) g_preempted = true;             /* on cede a l'autre carte */
        pc_log("[%08lX] Config recue : ESCLAVE (position %u)\r\n",
               (unsigned long)g_board_id, (unsigned)g_position);
        break;

    case CMD_RESET:                                       /* EXG-DIA-02 */
        send_ack(CMD_RESET);
        reset_local();
        break;

    case CMD_MSG:
        if (g_state != ST_SYNCED || g_role != ROLE_SLAVE) {
            send_error(CMD_MSG);                          /* pas configure en recepteur */
            led_fault();
            break;
        }
        send_ack(CMD_MSG);                                /* COM-01 (CRC deja valide) */
        {                                                 /* EXG-ESC-05 / SEC-02 */
            uint8_t plain[MAX_PAYLOAD_SIZE];
            char    txt[MAX_PAYLOAD_SIZE + 1];
            uint8_t len = m->header.length;
            memcpy(plain, m->payload, len);
            pc_hex("[RECU]   Chiffre: ", plain, len);
            cipher_xor(plain, len, g_key);
            memcpy(txt, plain, len);
            txt[len] = '\0';
            pc_log("[RECU]   Message dechiffre : %s\r\n", txt);
        }
        break;

    default:                                              /* ACK / ERROR hors attente */
        break;
    }
}

/* Aiguille un resultat de link_poll().
 * Retourne un evenement ACK/ERROR si la trame correspond a l'attente de
 * wait_cmd ; les requetes (INIT/RESET/MSG) sont traitees directement. */
static RxEvent_t rx_dispatch(RxStatus_t s, const ProtocolMessage_t *m, uint8_t wait_cmd)
{
    switch (s) {
    case RX_OK:
        switch (m->header.command_type) {
        case CMD_ACK:
            if (m->header.length >= 1 && m->payload[0] == wait_cmd) return EV_ACK;
            break;
        case CMD_ERROR:
            led_fault();
            pc_log("[%08lX] CMD_ERROR recu de l'autre carte\r\n", (unsigned long)g_board_id);
            return EV_ERROR;
        default:
            handle_request(m);
            break;
        }
        break;
    case RX_BAD_CRC:                                      /* ESC-03 / COM-02 */
        send_error(CMD_ERROR);
        led_fault();                                      /* DIA-05 */
        pc_log("[%08lX] Trame rejetee : CRC invalide\r\n", (unsigned long)g_board_id);
        break;
    case RX_BAD_LEN:                                      /* TRM-08 */
        led_fault();
        pc_log("[%08lX] Trame rejetee : length invalide\r\n", (unsigned long)g_board_id);
        break;
    default:
        break;
    }
    return EV_NONE;
}

/* ========================================================================== */
/*                  EMISSION FIABLE (EXG-COM-03/04/05)                        */
/* ========================================================================== */

static bool send_reliable(CommandType_t cmd, const uint8_t *data, uint8_t len)
{
    ProtocolMessage_t tx, rx;
    frame_build(&tx, cmd, data, len);

    for (uint32_t attempt = 1; attempt <= MAX_RETRIES; attempt++) {
        HAL_UART_Transmit(&huart_link, (uint8_t *)&tx, (uint16_t)sizeof(tx), 200);

        uint32_t t0 = HAL_GetTick();
        while ((HAL_GetTick() - t0) < ACK_TIMEOUT_MS) {
            RxEvent_t ev = rx_dispatch(link_poll(&rx), &rx, (uint8_t)cmd);
            if (g_preempted) return false;     /* on a cede : on abandonne */
            if (ev == EV_ACK)   return true;
            if (ev == EV_ERROR) break;         /* l'autre carte signale une erreur */
            led_update();
        }
        pc_log("[%08lX] pas d'ACK (cmd %u), tentative %lu/%u\r\n",
               (unsigned long)g_board_id, (unsigned)cmd,
               (unsigned long)attempt, (unsigned)MAX_RETRIES);
    }

    /* COM-05 : echec -> LED + trame CMD_ERROR */
    led_fault();
    pc_log("[%08lX] ECHEC d'envoi (cmd %u)\r\n", (unsigned long)g_board_id, (unsigned)cmd);
    send_error((uint8_t)cmd);
    return false;
}

/* ========================================================================== */
/*                         PC : saisie des messages                           */
/* ========================================================================== */

/* Assemble une ligne (terminee par \r ou \n) de 16 caracteres max (tronquee au-dela). */
static bool pc_poll_line(uint8_t *out, uint8_t *len)
{
    static uint8_t buf[MAX_PAYLOAD_SIZE];
    static uint8_t n = 0;
    uint8_t b;

    while (ring_get(&rb_pc, &b)) {
        if (b == '\r' || b == '\n') {
            if (n > 0) {
                memcpy(out, buf, n);
                *len = n;
                n = 0;
                return true;
            }
        } else if (n < MAX_PAYLOAD_SIZE) {
            buf[n++] = b;
        }
    }
    return false;
}

/* EXG-MAI-01/02/03 : devenir maitre = nouvelle cle + CMD_INIT vers l'autre carte */
static bool become_master(void)
{
    uint8_t  p[INIT_PAYLOAD_LEN];
    uint32_t key = generate_key();

    p[0] = (uint8_t)(key);
    p[1] = (uint8_t)(key >> 8);
    p[2] = (uint8_t)(key >> 16);
    p[3] = (uint8_t)(key >> 24);
    p[4] = 1;                                   /* position du recepteur */

    pc_log("[%08lX] Envoi CMD_INIT (cle %08lX)\r\n", (unsigned long)g_board_id, (unsigned long)key);

    g_preempted  = false;
    g_initiating = true;
    bool ok = send_reliable(CMD_INIT, p, INIT_PAYLOAD_LEN);
    g_initiating = false;

    if (!ok || g_preempted) return false;

    g_key      = key;
    g_position = 0;
    g_role     = ROLE_MASTER;
    g_state    = ST_SYNCED;
    pc_log("[%08lX] MAITRE : liaison initialisee\r\n", (unsigned long)g_board_id);
    return true;
}

/* EXG-MAI-04/05 : message du PC -> chiffrement -> CMD_MSG */
static void pc_message(const uint8_t *line, uint8_t len)
{
    uint8_t msg[MAX_PAYLOAD_SIZE];
    char    clear[MAX_PAYLOAD_SIZE + 1];

    memcpy(clear, line, len);
    clear[len] = '\0';

    /* Pas encore maitre (attente d'init ou esclave) : on prend la main */
    if (g_state != ST_SYNCED || g_role != ROLE_MASTER) {
        if (!become_master()) {
            pc_log("[%08lX] Message abandonne : %s\r\n", (unsigned long)g_board_id, clear);
            return;
        }
    }

    memcpy(msg, line, len);
    pc_log("[ENVOI]  Clair  : %s\r\n", clear);
    cipher_xor(msg, len, g_key);                /* chiffrement (EXG-SEC-01) */
    pc_hex("[ENVOI]  Chiffre: ", msg, len);

    if (send_reliable(CMD_MSG, msg, len))
        pc_log("[ENVOI]  Message transmis\r\n");
}

/* ========================================================================== */
/*                          BOUTON USER : 3 APPUIS (EXG-DIA-01)               */
/* ========================================================================== */

static bool button_triple_press(void)
{
    static bool     prev_released = true;
    static uint32_t t_edge = 0, t_first = 0;
    static uint8_t  count = 0;

    uint32_t now = HAL_GetTick();
    bool released = (HAL_GPIO_ReadPin(BTN_PORT, BTN_PIN) == GPIO_PIN_SET);

    if (count && (now - t_first) > BTN_WINDOW_MS) count = 0;

    if (prev_released && !released && (now - t_edge) > BTN_DEBOUNCE_MS) {
        t_edge = now;
        if (count == 0) t_first = now;
        if (++count >= BTN_PRESS_COUNT) { count = 0; prev_released = released; return true; }
    }
    prev_released = released;
    return false;
}

/* ========================================================================== */
/*                                   MAIN                                     */
/* ========================================================================== */

int main(void)
{
    HAL_Init();                                  /* horloge HSI 16 MHz par defaut */
    gpio_init();

    uart_init(&huart_pc,   USART2, USART2_IRQn);
    uart_init(&huart_link, USART1, USART1_IRQn);

    /* Compteur de cycles (entropie pour la cle) */
    CoreDebug->DEMCR |= CoreDebug_DEMCR_TRCENA_Msk;
    DWT->CTRL        |= DWT_CTRL_CYCCNTENA_Msk;

    /* Identifiant de la carte (EXG-TRM-05) derive de l'UID unique du MCU */
    g_board_id = mix32(HAL_GetUIDw0() ^ mix32(HAL_GetUIDw1()) ^ mix32(HAL_GetUIDw2() + 1u));
    if (g_board_id == DEFAULT_ID) g_board_id = 1u;

    HAL_UART_Receive_IT(&huart_pc,   &rx_pc,   1);
    HAL_UART_Receive_IT(&huart_link, &rx_link, 1);

    pc_log("\r\n=== STM32 liaison chiffree (ID %08lX) ===\r\n", (unsigned long)g_board_id);
    pc_log("Tapez un message (16 car. max) puis Entree.\r\n");
    reset_local();

    for (;;) {
        ProtocolMessage_t m;
        uint8_t line[MAX_PAYLOAD_SIZE], len = 0;

        led_update();

        /* EXG-DIA-01 : 3 appuis -> CMD_RESET */
        if (button_triple_press()) {
            pc_log("[%08lX] 3 appuis : emission CMD_RESET\r\n", (unsigned long)g_board_id);
            send_reliable(CMD_RESET, NULL, 0);
            reset_local();
            continue;
        }

        /* Trames venant de l'autre carte */
        rx_dispatch(link_poll(&m), &m, 0xFF);

        /* Message tape sur le PC */
        if (pc_poll_line(line, &len))
            pc_message(line, len);
    }
}

/* ========================================================================== */
/*                        INITIALISATION PERIPHERIQUES                        */
/* ========================================================================== */

static void gpio_init(void)
{
    GPIO_InitTypeDef g = {0};

    __HAL_RCC_GPIOA_CLK_ENABLE();
    __HAL_RCC_GPIOC_CLK_ENABLE();
    __HAL_RCC_USART1_CLK_ENABLE();
    __HAL_RCC_USART2_CLK_ENABLE();

    /* LED */
    g.Pin = LED_PIN; g.Mode = GPIO_MODE_OUTPUT_PP; g.Pull = GPIO_NOPULL; g.Speed = GPIO_SPEED_FREQ_LOW;
    HAL_GPIO_Init(LED_PORT, &g);

    /* Bouton USER */
    g.Pin = BTN_PIN; g.Mode = GPIO_MODE_INPUT; g.Pull = GPIO_NOPULL;
    HAL_GPIO_Init(BTN_PORT, &g);

    /* USART2 : PA2 (TX) / PA3 (RX) -> PC */
    g.Pin = GPIO_PIN_2 | GPIO_PIN_3; g.Mode = GPIO_MODE_AF_PP; g.Pull = GPIO_PULLUP;
    g.Speed = GPIO_SPEED_FREQ_VERY_HIGH; g.Alternate = GPIO_AF7_USART2;
    HAL_GPIO_Init(GPIOA, &g);

    /* USART1 : PA9 (TX) / PA10 (RX) -> autre carte (pull-up : ligne au repos = 1) */
    g.Pin = GPIO_PIN_9 | GPIO_PIN_10; g.Alternate = GPIO_AF7_USART1;
    HAL_GPIO_Init(GPIOA, &g);
}

static void uart_init(UART_HandleTypeDef *h, USART_TypeDef *inst, IRQn_Type irq)
{
    h->Instance          = inst;
    h->Init.BaudRate     = UART_BAUDRATE;
    h->Init.WordLength   = UART_WORDLENGTH_8B;
    h->Init.StopBits     = UART_STOPBITS_1;
    h->Init.Parity       = UART_PARITY_NONE;
    h->Init.Mode         = UART_MODE_TX_RX;
    h->Init.HwFlowCtl    = UART_HWCONTROL_NONE;
    h->Init.OverSampling = UART_OVERSAMPLING_16;
    if (HAL_UART_Init(h) != HAL_OK) Error_Handler();

    HAL_NVIC_SetPriority(irq, 1, 0);
    HAL_NVIC_EnableIRQ(irq);
}

/* ========================================================================== */
/*                         INTERRUPTIONS / CALLBACKS                          */
/* ========================================================================== */

void USART1_IRQHandler(void) { HAL_UART_IRQHandler(&huart_link); }
void USART2_IRQHandler(void) { HAL_UART_IRQHandler(&huart_pc);   }

void HAL_UART_RxCpltCallback(UART_HandleTypeDef *h)
{
    if (h->Instance == USART2)      { ring_put(&rb_pc,   rx_pc);   HAL_UART_Receive_IT(&huart_pc,   &rx_pc,   1); }
    else if (h->Instance == USART1) { ring_put(&rb_link, rx_link); HAL_UART_Receive_IT(&huart_link, &rx_link, 1); }
}

/* Erreur UART (overrun, bruit...) : on relance simplement la reception */
void HAL_UART_ErrorCallback(UART_HandleTypeDef *h)
{
    if (h->Instance == USART2)      HAL_UART_Receive_IT(&huart_pc,   &rx_pc,   1);
    else if (h->Instance == USART1) HAL_UART_Receive_IT(&huart_link, &rx_link, 1);
}

static void Error_Handler(void)
{
    __disable_irq();
    while (1) { }
}