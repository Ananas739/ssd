"""
Закрытый бот-модератор для Telegram-группы.
Python 3.10+, aiogram 3.x  ->  pip install aiogram tzdata matplotlib

Запуск:
    export BOT_TOKEN="123456:ABC..."      (Windows: set BOT_TOKEN=...)
    python bot.py
"""

import asyncio
from collections import defaultdict
import html
import io
import logging
import os
import re
import sqlite3
import time
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

from aiogram import BaseMiddleware, Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramAPIError
from aiogram.filters import Command, CommandObject
from aiogram.types import (
    BufferedInputFile,
    CallbackQuery,
    ChatMemberUpdated,
    ChatPermissions,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
)

# ---------------------------- НАСТРОЙКИ ----------------------------
OWNER_IDS = {6782169391, 1651065391}   # только они управляют ботом в ЛС и могут добавлять его в группы
MAX_WARNS = 3                          # сколько варнов до бана
DEFAULT_MUTE = timedelta(hours=1)      # мут без указания времени
DB_PATH = "bot.db"
PREFIX = "/!."                         # команды: /mute, !mute, .mute

BOT_VERSION = "r12.2 · 30.09.2026"     # /ver покажет, какая версия реально запущена

# Часовые пояса: ключ -> (название, зона)
TIMEZONES = {
    "kyiv": ("Киев", "Europe/Kyiv"),
    "moscow": ("Москва", "Europe/Moscow"),
    "cet": ("Центральная Европа", "Europe/Berlin"),
}
TZ_ALIASES = {"киев": "kyiv", "москва": "moscow", "цев": "cet", "европа": "cet", "cet": "cet"}
DEFAULT_TZ = "kyiv"

# Структуры для Анти-рейд системы защиты
warn_logs = defaultdict(list)      # (chat_id, user_id) -> list[timestamp]
kick_ban_logs = defaultdict(list)  # (chat_id, user_id) -> list[timestamp]
blocked_admins = set()             # set of (chat_id, user_id)
immune_admins = {}                 # (chat_id, user_id) -> timestamp_until
# -------------------------------------------------------------------

logging.basicConfig(level=logging.INFO)

db = sqlite3.connect(DB_PATH, check_same_thread=False)
db.executescript(
    """
    CREATE TABLE IF NOT EXISTS users(
        chat_id INTEGER, user_id INTEGER, name TEXT, username TEXT,
        first_seen INTEGER, last_active INTEGER, tag TEXT,
        warns INTEGER DEFAULT 0,
        PRIMARY KEY(chat_id, user_id)
    );
    CREATE TABLE IF NOT EXISTS activity(
        chat_id INTEGER, user_id INTEGER, day TEXT, cnt INTEGER DEFAULT 0,
        PRIMARY KEY(chat_id, user_id, day)
    );
    CREATE TABLE IF NOT EXISTS chat_state(
        chat_id INTEGER PRIMARY KEY, perms TEXT
    );
    CREATE TABLE IF NOT EXISTS settings(
        chat_id INTEGER PRIMARY KEY, tz TEXT, immunity_sec INTEGER DEFAULT 3600,
        max_warn_limit INTEGER DEFAULT 5, max_kb_limit INTEGER DEFAULT 3
    );
    CREATE TABLE IF NOT EXISTS chats(
        chat_id INTEGER PRIMARY KEY, title TEXT
    );
    """
)
db.commit()
try:
    db.execute("ALTER TABLE users ADD COLUMN rank INTEGER DEFAULT 0")
    db.commit()
except sqlite3.OperationalError:
    pass
try:
    db.execute("ALTER TABLE users ADD COLUMN gone INTEGER DEFAULT 0")
    db.commit()
except sqlite3.OperationalError:
    pass
try:
    db.execute("ALTER TABLE settings ADD COLUMN immunity_sec INTEGER DEFAULT 3600")
    db.commit()
except sqlite3.OperationalError:
    pass
try:
    db.execute("ALTER TABLE settings ADD COLUMN max_warn_limit INTEGER DEFAULT 5")
    db.commit()
except sqlite3.OperationalError:
    pass
try:
    db.execute("ALTER TABLE settings ADD COLUMN max_kb_limit INTEGER DEFAULT 3")
    db.commit()
except sqlite3.OperationalError:
    pass


# ============================ УТИЛИТЫ ==============================
def esc(s) -> str:
    return html.escape(str(s or ""))


INVISIBLE = (
    "\u200b\u200c\u200d\u200e\u200f\u2060\u2061\u2062\u2063\u2064\u00a0\u00ad\u034f"
    "\u115f\u1160\u17b4\u17b5\u180e\u2800\u3164\uffa0\ufeff"
)


def clean_name(name, username: str = "", uid: int = 0) -> str:
    """Имя без невидимых символов; если имени фактически нет — @username или «Участник ID»."""
    n = "".join(ch for ch in (name or "") if ch not in INVISIBLE and ch.isprintable()).strip()
    if n:
        return n
    return f"@{username}" if username else f"Участник {uid}"


def link(uid: int, name) -> str:
    return f'<a href="tg://user?id={uid}">{esc(clean_name(name, "", uid))}</a>'


def plural(n: int, w: tuple) -> str:
    n = abs(n)
    if 11 <= n % 100 <= 14:
        return w[2]
    if n % 10 == 1:
        return w[0]
    if 2 <= n % 10 <= 4:
        return w[1]
    return w[2]


def dur_text(sec: float) -> str:
    sec = int(sec)
    for size, words in (
        (86400, ("день", "дня", "дней")),
        (3600, ("час", "часа", "часов")),
        (60, ("минуту", "минуты", "минут")),
    ):
        if sec >= size:
            n = sec // size
            return f"{n} {plural(n, words)}"
    return "меньше минуты"


def ago(sec: float) -> str:
    return "только что" if sec < 60 else dur_text(sec) + " назад"


DUR_RE = re.compile(r"^(\d+)([mhdwмчдн])$", re.I)
UNITS = {"m": 60, "м": 60, "h": 3600, "ч": 3600, "d": 86400, "д": 86400, "w": 604800, "н": 604800}


def parse_dur(s: str):
    m = DUR_RE.match(s)
    if not m:
        return None
    return timedelta(seconds=int(m.group(1)) * UNITS[m.group(2).lower()])


# ========================== ЧАСОВЫЕ ПОЯСА И НАСТРОЙКИ ==========================
def get_zone(name: str) -> ZoneInfo:
    try:
        return ZoneInfo(name)
    except Exception:
        if name == "Europe/Kyiv":
            return ZoneInfo("Europe/Kiev")
        raise


def tz_key(chat_id: int) -> str:
    row = db.execute("SELECT tz FROM settings WHERE chat_id=?", (chat_id,)).fetchone()
    return row[0] if row and row[0] in TIMEZONES else DEFAULT_TZ


def tz_label(chat_id: int) -> str:
    return TIMEZONES[tz_key(chat_id)][0]


def set_tz(chat_id: int, key: str) -> None:
    db.execute(
        "INSERT INTO settings(chat_id,tz) VALUES(?,?) ON CONFLICT(chat_id) DO UPDATE SET tz=excluded.tz",
        (chat_id, key),
    )
    db.commit()


def get_immunity_sec(chat_id: int) -> int:
    row = db.execute("SELECT immunity_sec FROM settings WHERE chat_id=?", (chat_id,)).fetchone()
    return (row[0] if row and row[0] else 3600)


def set_immunity_sec(chat_id: int, sec: int) -> None:
    db.execute(
        "INSERT INTO settings(chat_id,immunity_sec) VALUES(?,?) ON CONFLICT(chat_id) DO UPDATE SET immunity_sec=excluded.immunity_sec",
        (chat_id, sec),
    )
    db.commit()


def get_chat_limits(chat_id: int) -> tuple[int, int]:
    row = db.execute("SELECT max_warn_limit, max_kb_limit FROM settings WHERE chat_id=?", (chat_id,)).fetchone()
    warn_lim = row[0] if (row and row[0] is not None) else 5
    kb_lim = row[1] if (row and row[1] is not None) else 3
    return warn_lim, kb_lim


def set_chat_limits(chat_id: int, warn_lim: int, kb_lim: int) -> None:
    db.execute(
        """INSERT INTO settings(chat_id, max_warn_limit, max_kb_limit) VALUES(?,?,?)
           ON CONFLICT(chat_id) DO UPDATE SET max_warn_limit=excluded.max_warn_limit, max_kb_limit=excluded.max_kb_limit""",
        (chat_id, warn_lim, kb_lim),
    )
    db.commit()


def now_local(chat_id: int) -> datetime:
    return datetime.now(get_zone(TIMEZONES[tz_key(chat_id)][1]))


def now_str(chat_id: int) -> str:
    """Форматированная дата и время с учётом установленного часового пояса чата."""
    dt = now_local(chat_id)
    return f"{dt.strftime('%d.%m.%Y %H:%M:%S')} ({tz_label(chat_id)})"


def today_str(chat_id: int) -> str:
    return now_local(chat_id).date().isoformat()


def week_start(chat_id: int):
    d = now_local(chat_id).date()
    return d - timedelta(days=d.weekday())


def tz_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text=v[0], callback_data=f"tz:{k}")] for k, v in TIMEZONES.items()
        ]
    )


# ========================== БАЗА: СТАТИСТИКА =======================
def touch(chat, u, count: bool = True) -> None:
    chat_id = chat.id
    now = int(time.time())
    db.execute(
        "INSERT OR REPLACE INTO chats(chat_id,title) VALUES(?,?)", (chat_id, chat.title or str(chat_id))
    )
    db.execute(
        """INSERT INTO users(chat_id,user_id,name,username,first_seen,last_active)
           VALUES(?,?,?,?,?,?)
           ON CONFLICT(chat_id,user_id) DO UPDATE SET
             name=excluded.name, username=excluded.username,
             last_active=excluded.last_active, gone=0""",
        (chat_id, u.id, u.full_name, (u.username or "").lower(), now, now),
    )
    if count:
        db.execute(
            """INSERT INTO activity(chat_id,user_id,day,cnt) VALUES(?,?,?,1)
               ON CONFLICT(chat_id,user_id,day) DO UPDATE SET cnt=cnt+1""",
            (chat_id, u.id, today_str(chat_id)),
        )
    db.commit()


def remember(chat, u) -> None:
    """Запомнить участника без учёта сообщения."""
    now = int(time.time())
    db.execute(
        "INSERT OR REPLACE INTO chats(chat_id,title) VALUES(?,?)", (chat.id, chat.title or str(chat.id))
    )
    db.execute(
        """INSERT INTO users(chat_id,user_id,name,username,first_seen,last_active)
           VALUES(?,?,?,?,?,?)
           ON CONFLICT(chat_id,user_id) DO UPDATE SET
             name=excluded.name, username=excluded.username, gone=0""",
        (chat.id, u.id, u.full_name, (u.username or "").lower(), now, now),
    )
    db.commit()


def ensure_user(chat_id: int, uid: int, name: str, username: str = "") -> None:
    """Занести участника в базу данных, если его там ещё нет."""
    now = int(time.time())
    db.execute(
        """INSERT INTO users(chat_id,user_id,name,username,first_seen,last_active)
           VALUES(?,?,?,?,?,?)
           ON CONFLICT(chat_id,user_id) DO UPDATE SET
             name=EXCLUDED.name,
             username=CASE WHEN EXCLUDED.username != '' THEN EXCLUDED.username ELSE users.username END,
             gone=0""",
        (chat_id, uid, name, (username or "").lower(), now, now),
    )
    db.commit()


def msgs_since(chat_id: int, uid: int, since: str | None) -> int:
    if since is None:
        r = db.execute(
            "SELECT COALESCE(SUM(cnt),0) FROM activity WHERE chat_id=? AND user_id=?",
            (chat_id, uid),
        ).fetchone()
    else:
        r = db.execute(
            "SELECT COALESCE(SUM(cnt),0) FROM activity WHERE chat_id=? AND user_id=? AND day>=?",
            (chat_id, uid, since),
        ).fetchone()
    return r[0]


def msgs_day(chat_id, uid):
    return msgs_since(chat_id, uid, today_str(chat_id))


def msgs_week(chat_id, uid):
    return msgs_since(chat_id, uid, week_start(chat_id).isoformat())


def msgs_month(chat_id, uid):
    since = (now_local(chat_id).date() - timedelta(days=29)).isoformat()
    return msgs_since(chat_id, uid, since)


def get_user_row(chat_id: int, uid: int):
    return db.execute(
        "SELECT name,username,first_seen,last_active,tag,warns FROM users WHERE chat_id=? AND user_id=?",
        (chat_id, uid),
    ).fetchone()


def week_text(chat_id: int, uid: int, name: str) -> str:
    """Сколько сообщений участник написал на этой неделе (с понедельника)."""
    start = week_start(chat_id)
    today = now_local(chat_id).date()
    rows = dict(
        db.execute(
            "SELECT day,cnt FROM activity WHERE chat_id=? AND user_id=? AND day>=?",
            (chat_id, uid, start.isoformat()),
        ).fetchall()
    )
    names = ["Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"]
    total = 0
    lines = []
    for i in range(7):
        d = start + timedelta(days=i)
        if d > today:
            break
        c = rows.get(d.isoformat(), 0)
        total += c
        lines.append(f"{names[i]} {d:%d.%m}: {c}")
    head = (
        f"📊 {link(uid, name)} на этой неделе (с {start:%d.%m}): "
        f"<b>{total}</b> {plural(total, ('сообщение', 'сообщения', 'сообщений'))}"
    )
    return head + "\n\n" + "\n".join(lines) + f"\n\n🕐 Пояс: {tz_label(chat_id)}"


PERIOD_TITLES = {
    "day": "за сегодня",
    "week": "за эту неделю",
    "month": "за последние 30 дней",
    "all": "за всё время",
}
PERIOD_ALIASES = {
    "day": "day", "d": "day", "день": "day", "сегодня": "day",
    "week": "week", "w": "week", "неделя": "week", "нед": "week",
    "month": "month", "m": "month", "месяц": "month", "мес": "month",
    "all": "all", "всё": "all", "все": "all", "всего": "all", "история": "all", "вся": "all",
}


def parse_period(args: list[str]) -> str:
    for a in args:
        p = PERIOD_ALIASES.get(a.lower())
        if p:
            return p
    return "week"


def top_text(chat_id: int, period: str = "week") -> str:
    if period == "day":
        since = today_str(chat_id)
    elif period == "week":
        since = week_start(chat_id).isoformat()
    elif period == "month":
        since = (now_local(chat_id).date() - timedelta(days=29)).isoformat()
    else:
        since = None
    cond = "AND a.day>=?" if since else ""
    params = (chat_id, since) if since else (chat_id,)
    rows = db.execute(
        f"""SELECT a.user_id, u.name, u.username, COALESCE(u.gone,0), SUM(a.cnt) c
            FROM activity a
            LEFT JOIN users u ON u.chat_id=a.chat_id AND u.user_id=a.user_id
            WHERE a.chat_id=? {cond}
            GROUP BY a.user_id ORDER BY c DESC LIMIT 10""",
        params,
    ).fetchall()
    if not rows:
        return "Пока нет данных об активности."
    total = db.execute(
        f"SELECT COALESCE(SUM(a.cnt),0) FROM activity a WHERE a.chat_id=? {cond}", params
    ).fetchone()[0]
    medals = ["🥇", "🥈", "🥉"]
    out = [f"📊 <b>Топ активности {PERIOD_TITLES.get(period, PERIOD_TITLES['week'])}</b> (сообщений)\n"]
    for i, (uid, name, uname, gone, c) in enumerate(rows):
        mark = medals[i] if i < 3 else f"{i + 1}."
        shown = clean_name(name, uname or "", uid)
        out.append(f"{mark} {link(uid, shown)} — {c}" + (" 🚪" if gone else ""))
    out.append(f"\nВсего сообщений: {total}")
    return "\n".join(out)


COUNTED_TYPES = {
    "text", "photo", "video", "animation", "audio", "voice", "video_note",
    "document", "sticker", "poll", "dice", "location", "contact", "venue",
}


class Stats(BaseMiddleware):
    async def __call__(self, handler, event: Message, data):
        if event.chat.type in ("group", "supergroup") and event.left_chat_member:
            db.execute(
                "UPDATE users SET gone=1 WHERE chat_id=? AND user_id=?",
                (event.chat.id, event.left_chat_member.id),
            )
            db.commit()
        if event.chat.type in ("group", "supergroup") and event.new_chat_members:
            for nu in event.new_chat_members:
                if not nu.is_bot:
                    remember(event.chat, nu)
        if (
            event.chat.type in ("group", "supergroup")
            and event.from_user
            and not event.from_user.is_bot
            and not event.sender_chat
        ):
            try:
                ct = getattr(event.content_type, "value", event.content_type)
                is_cmd = bool(event.text) and re.match(r"^[\/!\.]\w", event.text) is not None
                touch(event.chat, event.from_user, count=(ct in COUNTED_TYPES and not is_cmd))
            except Exception:
                logging.exception("stats error")
        return await handler(event, data)


# ========================== ПРАВА И ЦЕЛИ ===========================
RANKS = {0: "Участник", 1: "Помощник", 2: "Модератор", 3: "Админ", 4: "Старший админ", 5: "Создатель"}


def rank_title(n: int) -> str:
    return RANKS.get(n, "Участник")


def stars(n: int) -> str:
    return "⭐" * n


def stored_rank(chat_id: int, uid: int) -> int:
    row = db.execute("SELECT rank FROM users WHERE chat_id=? AND user_id=?", (chat_id, uid)).fetchone()
    return (row[0] or 0) if row else 0


async def eff_rank(bot: Bot, chat_id: int, uid: int) -> int:
    if uid in OWNER_IDS:
        return 5
    r = stored_rank(chat_id, uid)
    try:
        mem = await bot.get_chat_member(chat_id, uid)
        if mem.status == "creator":
            r = max(r, 5)
        elif mem.status == "administrator":
            r = max(r, 3)
    except TelegramAPIError:
        pass
    return r


async def get_user_max_rank(bot: Bot, uid: int) -> int:
    """Получить максимальный ранг пользователя среди всех групп бота (для ЛС)."""
    if uid in OWNER_IDS:
        return 5
    chats = db.execute("SELECT chat_id FROM chats").fetchall()
    max_r = 0
    for (cid,) in chats:
        r = await eff_rank(bot, cid, uid)
        if r > max_r:
            max_r = r
    return max_r


async def is_admin_id(bot: Bot, chat_id: int, uid: int) -> bool:
    return await eff_rank(bot, chat_id, uid) >= 1


def clear_rank(chat_id: int, uid: int) -> None:
    db.execute("UPDATE users SET rank=0 WHERE chat_id=? AND user_id=?", (chat_id, uid))
    db.commit()


async def demote_if_admin(bot: Bot, chat_id: int, uid: int) -> None:
    try:
        mem = await bot.get_chat_member(chat_id, uid)
    except TelegramAPIError:
        return
    if mem.status != "administrator":
        return
    try:
        await bot.promote_chat_member(
            chat_id,
            uid,
            is_anonymous=False,
            can_manage_chat=False,
            can_delete_messages=False,
            can_manage_video_chats=False,
            can_restrict_members=False,
            can_promote_members=False,
            can_change_info=False,
            can_invite_users=False,
            can_pin_messages=False,
        )
        clear_rank(chat_id, uid)
    except TelegramAPIError:
        pass


async def require_rank(m: Message, min_rank: int) -> bool:
    if m.sender_chat and m.sender_chat.id == m.chat.id:
        return True
    if not m.from_user:
        return False
    r = await eff_rank(m.bot, m.chat.id, m.from_user.id)
    if r >= min_rank:
        return True
    await m.reply(f"⛔ Команда доступна с ранга [{min_rank}] {rank_title(min_rank)}.")
    return False


# ===================== АНТИ-РЕЙД И ЛИМИТЫ =====================
async def check_protection(m: Message, action_type: str) -> bool:
    """
    Проверка лимитов наказаний (5 минут):
      - Варны (по умолчанию макс. 5)
      - Кики + баны суммарно (по умолчанию макс. 3)
    Владельцы (OWNER_IDS) игнорируют лимиты.
    """
    if not m.from_user or m.sender_chat:
        return True
    uid = m.from_user.id
    cid = m.chat.id

    if uid in OWNER_IDS:
        return True

    key = (cid, uid)
    now = time.time()

    if key in blocked_admins:
        await m.reply("⛔ Вам ограничено использование админ-команд за превышение лимитов. Ожидайте решения владельцев.")
        return False

    if immune_admins.get(key, 0) > now:
        return True

    warn_limit, kb_limit = get_chat_limits(cid)

    logs = warn_logs[key] if action_type == "warn" else kick_ban_logs[key]
    limit = warn_limit if action_type == "warn" else kb_limit
    label = f"{limit} варнов" if action_type == "warn" else f"{limit} киков/банов"

    logs[:] = [t for t in logs if now - t <= 300]
    logs.append(now)

    if len(logs) > limit:
        blocked_admins.add(key)
        await m.reply(
            f"🚨 <b>Внимание!</b> {link(uid, m.from_user.full_name)} превысил лимит действий ({label} за 5 минут)!\n"
            f"Использование админ-команд временно заблокировано. Уведомление отправлено владельцам."
        )

        chat_title = m.chat.title or str(cid)
        sec = get_immunity_sec(cid)
        kb = InlineKeyboardMarkup(
            inline_keyboard=[
                [
                    InlineKeyboardButton(text=f"🔓 Снять защиту ({dur_text(sec)})", callback_data=f"prot_unblock:{cid}:{uid}"),
                    InlineKeyboardButton(text="⛔ Забанить", callback_data=f"prot_ban:{cid}:{uid}")
                ]
            ]
        )
        alert_text = (
            f"🚨 <b>Анти-рейд защита сработала!</b>\n\n"
            f"Группа: <b>{esc(chat_title)}</b> (<code>{cid}</code>)\n"
            f"Администратор: {link(uid, m.from_user.full_name)} (ID: <code>{uid}</code>)\n"
            f"Причина: превышен лимит ({label} за 5 мин).\n\n"
            f"Ему ограничено использование админ-команд. Выберите действие:"
        )

        for owner_id in OWNER_IDS:
            try:
                await m.bot.send_message(owner_id, alert_text, reply_markup=kb)
            except TelegramAPIError:
                pass
        return False

    return True


async def resolve_ref(bot: Bot, chat_id: int, args: list[str]):
    """Определение цели по аргументам в ЛС: @username или ID."""
    if not args:
        return None
    a = args[0]
    rest = args[1:]
    if a.startswith("@"):
        uname = a[1:].lower()
        row = db.execute(
            "SELECT user_id, name FROM users WHERE chat_id=? AND LOWER(username)=?",
            (chat_id, uname),
        ).fetchone()
        if row:
            return row[0], row[1], rest
        try:
            chat = await bot.get_chat(a)
            full_name = clean_name(chat.first_name or "", chat.username or uname, chat.id)
            ensure_user(chat_id, chat.id, full_name, chat.username or uname)
            return chat.id, full_name, rest
        except TelegramAPIError:
            return None
    elif a.isdigit() and len(a) >= 5:
        uid_val = int(a)
        row = db.execute(
            "SELECT user_id, name FROM users WHERE chat_id=? AND user_id=?",
            (chat_id, uid_val),
        ).fetchone()
        if row:
            return row[0], row[1], rest
        try:
            chat = await bot.get_chat(uid_val)
            full_name = clean_name(chat.first_name or "", chat.username or "", chat.id)
            ensure_user(chat_id, chat.id, full_name, chat.username)
            return chat.id, full_name, rest
        except TelegramAPIError:
            return uid_val, f"Участник {uid_val}", rest

    return None


async def resolve(m: Message, args: list[str]):
    """
    Возвращает (uid, name, rest, err_msg).
    Приоритет:
    1. text_mention из entities (упоминание)
    2. Аргументы: @username или ID (БД -> Telegram API get_chat)
    3. Reply на сообщение
    """
    if m.entities:
        for ent in m.entities:
            if ent.type == "text_mention" and ent.user:
                u = ent.user
                ensure_user(m.chat.id, u.id, u.full_name, u.username)
                rest = args[1:] if args else []
                return u.id, u.full_name, rest, None

    if args:
        a = args[0]
        rest = args[1:]

        if a.startswith("@"):
            uname = a[1:].lower()
            row = db.execute(
                "SELECT user_id, name FROM users WHERE chat_id=? AND LOWER(username)=?",
                (m.chat.id, uname),
            ).fetchone()
            if row:
                return row[0], row[1], rest, None

            try:
                chat = await m.bot.get_chat(a)
                full_name = clean_name(chat.first_name or "", chat.username or uname, chat.id)
                ensure_user(m.chat.id, chat.id, full_name, chat.username or uname)
                return chat.id, full_name, rest, None
            except TelegramAPIError:
                return None, None, rest, f"Пользователь {esc(a)} не найден."

        elif a.isdigit() and len(a) >= 5:
            uid_val = int(a)
            row = db.execute(
                "SELECT user_id, name FROM users WHERE chat_id=? AND user_id=?",
                (m.chat.id, uid_val),
            ).fetchone()
            if row:
                return row[0], row[1], rest, None

            try:
                chat = await m.bot.get_chat(uid_val)
                full_name = clean_name(chat.first_name or "", chat.username or "", chat.id)
                ensure_user(m.chat.id, chat.id, full_name, chat.username)
                return chat.id, full_name, rest, None
            except TelegramAPIError:
                return uid_val, f"Участник {uid_val}", rest, None

    if m.reply_to_message and m.reply_to_message.from_user:
        u = m.reply_to_message.from_user
        ensure_user(m.chat.id, u.id, u.full_name, u.username)
        return u.id, u.full_name, args, None

    return None, None, args, "Ответьте на сообщение пользователя или укажите @username / ID."


async def get_target(m: Message, command: CommandObject, allow_admin=False):
    args = (command.args or "").split()
    uid, name, rest, err_msg = await resolve(m, args)
    if uid is None:
        await m.reply(err_msg or "Ответьте на сообщение пользователя или укажите @username / ID.")
        return None
    if uid == m.bot.id:
        await m.reply("Меня трогать не надо 🙂")
        return None
    if not allow_admin:
        actor_owner = bool(m.from_user) and not m.sender_chat and m.from_user.id in OWNER_IDS
        if uid in OWNER_IDS:
            await m.reply("Владельцев бота наказывать нельзя.")
            return None
        if await eff_rank(m.bot, m.chat.id, uid) >= 3:
            if not actor_owner:
                await m.reply("Эту команду нельзя применить к админу.")
                return None
            try:
                if (await m.bot.get_chat_member(m.chat.id, uid)).status == "creator":
                    await m.reply("Создателя чата наказать нельзя — это ограничение Telegram.")
                    return None
            except TelegramAPIError:
                pass
    return uid, name, rest


async def safe(m: Message, coro, ok_text: str) -> bool:
    try:
        await coro
    except TelegramAPIError as e:
        msg = e.message.lower()
        if "administrator" in msg or "owner" in msg or "not enough rights" in msg:
            hint = (
                "Telegram не даёт боту наказывать админов, которых он не назначал сам. "
                "Снимите админку вручную и повторите."
            )
        else:
            hint = "Проверьте, что у бота есть права админа."
        await m.reply(f"⚠️ Не получилось: {esc(e.message)}\n{hint}")
        return False
    await m.reply(ok_text)
    return True


def reason_text(rest: list[str]) -> str:
    return f"\n📝 Причина: {esc(' '.join(rest))}" if rest else ""


# ===================== ОБЩАЯ ЛОГИКА (группа и ЛС) ==================
async def do_lock(bot: Bot, chat_id: int) -> None:
    chat = await bot.get_chat(chat_id)
    p = chat.permissions
    if p and p.can_send_messages is not False:
        db.execute(
            "INSERT OR REPLACE INTO chat_state(chat_id,perms) VALUES(?,?)",
            (chat_id, p.model_dump_json(exclude_none=True)),
        )
        db.commit()
    await bot.set_chat_permissions(chat_id, ChatPermissions(can_send_messages=False))


async def do_unlock(bot: Bot, chat_id: int) -> None:
    row = db.execute("SELECT perms FROM chat_state WHERE chat_id=?", (chat_id,)).fetchone()
    if row:
        perms = ChatPermissions.model_validate_json(row[0])
    else:
        perms = ChatPermissions(
            can_send_messages=True,
            can_send_audios=True,
            can_send_documents=True,
            can_send_photos=True,
            can_send_videos=True,
            can_send_video_notes=True,
            can_send_voice_notes=True,
            can_send_polls=True,
            can_send_other_messages=True,
            can_add_web_page_previews=True,
        )
    await bot.set_chat_permissions(chat_id, perms)
    db.execute("DELETE FROM chat_state WHERE chat_id=?", (chat_id,))
    db.commit()


STATUS_LINES = {
    "creator": "👑 Создатель этого чата",
    "administrator": "🕵 Телеграм-админ этого чата",
    "restricted": "🔇 Ограничен в этом чате",
    "left": "🚪 Покинул этот чат",
    "kicked": "⛔ Забанен в этом чате",
}


def dur_long(sec: float) -> str:
    sec = int(sec)
    if sec < 60:
        return "меньше минуты"
    days = sec // 86400
    if days >= 365:
        n = days // 365
        return f"{n} {plural(n, ('год', 'года', 'лет'))}"
    if days >= 60:
        n = days // 30
        return f"{n} {plural(n, ('месяц', 'месяца', 'месяцев'))}"
    return dur_text(sec)


def first_seen_text(ts: int, cid: int) -> str:
    zone = get_zone(TIMEZONES[tz_key(cid)][1])
    dt = datetime.fromtimestamp(ts, zone)
    today = now_local(cid).date()
    hm = dt.strftime("%H:%M")
    if dt.date() == today:
        when = f"❗ сегодня в {hm}"
    elif dt.date() == today - timedelta(days=1):
        when = f"вчера в {hm}"
    else:
        when = dt.strftime("%d.%m.%Y в %H:%M")
    return f"{when} ({dur_long(time.time() - ts)})"


async def build_card(bot: Bot, cid: int, uid: int, name: str, is_self: bool) -> str:
    try:
        member = await bot.get_chat_member(cid, uid)
        status_line = STATUS_LINES.get(member.status)
        if not name or name == f"Участник {uid}":
            name = clean_name(member.user.full_name, member.user.username or "", uid)
    except TelegramAPIError:
        status_line = None

    row = get_user_row(cid, uid)
    head = "Это вы" if is_self else "Это пользователь"
    rk = await eff_rank(bot, cid, uid)

    lines = [f"👤 {head} {link(uid, name)}"]
    lines.append(f"🆔 ID: <code>{uid}</code>")
    if status_line:
        lines.append(status_line)
    lines.append("")
    lines.append(f"{'⭐ ' if rk else ''}[{rk}] Ранг: {rank_title(rk)}")

    if row:
        _, _, first_seen, last_active, tag, warns = row
        idle = time.time() - last_active
        lines.append(f"Первое появление: {first_seen_text(first_seen, cid)}")
        lines.append(f"Последний актив: {'только что' if idle < 60 else dur_long(idle)}")
        lines.append(
            f"Актив (д|н|м|весь): {msgs_day(cid, uid)} | {msgs_week(cid, uid)} | "
            f"{msgs_month(cid, uid)} | {msgs_since(cid, uid, None)}"
        )
        if tag:
            lines.append(f"🏷 Тег: <b>{esc(tag)}</b>")
        if warns:
            lines.append(f"⚠ Варны: {warns}/{MAX_WARNS}")
    else:
        lines.append("Этот участник ещё ничего не писал при мне.")
    return "\n".join(lines)


def render_chart(rows: list) -> bytes:
    """График активности (дни, в которые были сообщения) за 365 дней."""
    from matplotlib.figure import Figure
    from matplotlib.ticker import MaxNLocator

    n = len(rows)
    ys = [c for _, c in rows]
    labels = [f"{d[8:10]}.{d[5:7]}\n{d[:4]}" for d, _ in rows]

    fig = Figure(figsize=(6.4, 3.3), dpi=110, facecolor="white")
    ax = fig.add_subplot(111)
    ax.bar(range(n), ys, width=0.8, color="#8fae4c")
    pad = 0.9 if n == 1 else 0.6
    ax.set_xlim(-pad, n - 1 + pad)
    ax.set_ylim(0, max(ys) * 1.15)
    ax.set_title("Статистика активности за 365 дней", fontsize=8, color="#555555")
    ax.grid(axis="y", color="#dddddd", linewidth=0.8)
    ax.set_axisbelow(True)
    step = max(1, -(-n // 10))
    ticks = list(range(0, n, step))
    ax.set_xticks(ticks)
    ax.set_xticklabels([labels[i] for i in ticks], fontsize=7, color="#555555")
    ax.yaxis.tick_right()
    ax.yaxis.set_label_position("right")
    ax.yaxis.set_major_locator(MaxNLocator(integer=True, nbins=6))
    ax.set_ylabel("Сообщения", fontsize=7, color="#555555")
    ax.tick_params(axis="y", labelsize=7, colors="#555555", length=0)
    ax.tick_params(axis="x", length=0)
    for side in ("top", "left"):
        ax.spines[side].set_visible(False)
    for side in ("right", "bottom"):
        ax.spines[side].set_color("#cccccc")
    fig.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="png")
    return buf.getvalue()


async def send_card(m: Message, cid: int, uid: int, name: str, is_self: bool) -> None:
    text = await build_card(m.bot, cid, uid, name, is_self)
    since = (now_local(cid).date() - timedelta(days=364)).isoformat()
    rows = db.execute(
        "SELECT day,cnt FROM activity WHERE chat_id=? AND user_id=? AND day>=? ORDER BY day",
        (cid, uid, since),
    ).fetchall()
    png = None
    if rows:
        try:
            png = await asyncio.to_thread(render_chart, rows)
        except Exception:
            logging.warning("Не удалось построить график (установите: pip install matplotlib)", exc_info=True)
    if png:
        await m.reply_photo(BufferedInputFile(png, "activity.png"), caption=text)
    else:
        await m.reply(text)


def set_warns(chat_id: int, uid: int, n: int) -> None:
    db.execute("UPDATE users SET warns=? WHERE chat_id=? AND user_id=?", (n, chat_id, uid))
    db.commit()


# ============================ РОУТЕРЫ ==============================
events = Router()
group = Router()
group.message.filter(F.chat.type.in_({"group", "supergroup"}))
private = Router()
private.message.filter(F.chat.type == "private", F.from_user.id.in_(OWNER_IDS))
deny = Router()
deny.message.filter(F.chat.type == "private", ~F.from_user.id.in_(OWNER_IDS))


# ------------------------ ЗАКРЫТЫЙ ДОСТУП --------------------------
@events.my_chat_member()
async def on_bot_added(ev: ChatMemberUpdated):
    if ev.chat.type not in ("group", "supergroup"):
        return
    was_out = ev.old_chat_member.status in ("left", "kicked")
    now_in = ev.new_chat_member.status in ("member", "administrator")
    if not (was_out and now_in):
        return
    if ev.from_user.id in OWNER_IDS:
        db.execute("INSERT OR REPLACE INTO chats(chat_id,title) VALUES(?,?)", (ev.chat.id, ev.chat.title))
        db.commit()
        try:
            await ev.bot.send_message(
                ev.chat.id, "✅ Бот подключён. Выдайте мне права админа. Список команд: /help"
            )
        except TelegramAPIError:
            pass
    else:
        try:
            await ev.bot.send_message(ev.chat.id, "🔒 Это закрытый бот. Добавлять его могут только владельцы.")
        except TelegramAPIError:
            pass
        try:
            await ev.bot.leave_chat(ev.chat.id)
        except TelegramAPIError:
            pass


@events.chat_member()
async def on_member_update(ev: ChatMemberUpdated):
    if ev.chat.type not in ("group", "supergroup"):
        return
    u = ev.new_chat_member.user
    if u.is_bot:
        return
    if ev.new_chat_member.status in ("member", "administrator", "creator", "restricted"):
        remember(ev.chat, u)
    elif ev.new_chat_member.status in ("left", "kicked"):
        db.execute("UPDATE users SET gone=1 WHERE chat_id=? AND user_id=?", (ev.chat.id, u.id))
        db.commit()


@events.callback_query(F.data.startswith("prot_"))
async def cb_protection(cb: CallbackQuery):
    if cb.from_user.id not in OWNER_IDS:
        await cb.answer("⛔ Только владельцы могут принимать это решение.", show_alert=True)
        return

    parts = cb.data.split(":")
    act = parts[0]
    cid = int(parts[1])
    uid = int(parts[2])
    key = (cid, uid)

    if act == "prot_unblock":
        blocked_admins.discard(key)
        sec = get_immunity_sec(cid)
        immune_admins[key] = time.time() + sec
        warn_logs[key].clear()
        kick_ban_logs[key].clear()

        await cb.message.edit_text(
            cb.message.html_text + f"\n\n✅ <b>Решение:</b> Защита снята. Администратору выдан иммунитет на {dur_text(sec)}."
        )
        await cb.answer("Ограничения сняты")
        try:
            await cb.bot.send_message(cid, f"🔓 Владелец снял ограничения с {link(uid, 'администратора')} и выдал иммунитет на {dur_text(sec)}.")
        except TelegramAPIError:
            pass

    elif act == "prot_ban":
        blocked_admins.discard(key)
        await demote_if_admin(cb.bot, cid, uid)
        try:
            await cb.bot.ban_chat_member(cid, uid)
            clear_rank(cid, uid)
            status = "забанен в чате."
        except TelegramAPIError as e:
            status = f"не удалось забанить ({esc(e.message)})."

        await cb.message.edit_text(
            cb.message.html_text + f"\n\n⛔ <b>Решение:</b> Администратор {status}"
        )
        await cb.answer("Администратор забанен")


# ---------------- НАПИСАТЬ ОТ ЛИЦА БОТА В ЛС (3-5 ранги) ------------
@events.message(F.chat.type == "private", Command("say", "скажи", "echo", "post", "pm", "лс", prefix=PREFIX))
async def dm_say(m: Message, command: CommandObject):
    if not m.from_user:
        return
    rk = await get_user_max_rank(m.bot, m.from_user.id)
    if rk < 3:
        await m.answer("⛔ Команда доступна только для администраторов (ранг 3-5).")
        return

    text = (command.args or "").strip()
    if not text:
        await m.answer(
            "💬 <b>Отправка сообщений от лица бота:</b>\n\n"
            "• В ЛС пользователю: <code>/say @username текст</code> или <code>/say ID_пользователя текст</code>\n"
            "• В чат группы: <code>/say ID_чата текст</code>\n"
            "<i>(ID чата можно узнать в /chats)</i>"
        )
        return

    args = text.split(maxsplit=1)
    ref = args[0]
    msg_text = args[1] if len(args) > 1 else ""

    target_chat_id = None
    target_uid = None

    if ref.startswith("-") and ref[1:].isdigit():
        target_chat_id = int(ref)
    elif ref.isdigit() and len(ref) >= 5:
        target_uid = int(ref)
    elif ref.startswith("@"):
        uname = ref[1:].lower()
        row = db.execute(
            "SELECT user_id FROM users WHERE LOWER(username)=? LIMIT 1",
            (uname,),
        ).fetchone()
        if row:
            target_uid = row[0]
        else:
            try:
                chat = await m.bot.get_chat(ref)
                target_uid = chat.id
            except TelegramAPIError:
                await m.answer(f"❌ Пользователь или чат {esc(ref)} не найден.")
                return

    if not target_chat_id and not target_uid:
        chats = db.execute("SELECT chat_id FROM chats").fetchall()
        if len(chats) == 1:
            target_chat_id = chats[0][0]
            msg_text = text

    if not msg_text:
        await m.answer("Укажите текст сообщения.")
        return

    dest_id = target_chat_id or target_uid
    if not dest_id:
        await m.answer("Укажите получателя (@username, ID пользователя или ID чата).")
        return

    try:
        await m.bot.send_message(dest_id, msg_text)
        await m.answer("✅ Сообщение успешно отправлено от лица бота!")
    except TelegramAPIError as e:
        await m.answer(f"⚠️ Ошибка при отправке: {esc(e.message)}")


@deny.message()
async def deny_dm(m: Message):
    await m.answer("🔒 Это закрытый бот. Доступ только для владельцев и администраторов.")


# ------------------------------- СПРАВКА ---------------------------
GROUP_HELP = f"""<b>Команды бота по рангам</b>
<i>(Каждый следующий ранг включает все возможности предыдущих)</i>

⭐ <b>[1] Помощник:</b>
/del — удалить сообщение (ответом)
/mute [время] [причина] — мут (по умолчанию 1ч)
/unmute — снять мут
/all [текст] — призыв участников
/pin — закрепить сообщение (ответом)
/unpin — открепить сообщение

⭐️⭐ <b>[2] Модератор:</b>
<i>(+ возможности Помощника [1])</i>
/tag текст — выдать тег участнику
/untag — убрать тег
/lock — закрыть чат (пишут только админы)
/unlock — открыть чат
/tz — установка часового пояса

⭐️⭐️⭐️ <b>[3] Админ:</b>
<i>(+ возможности Модератора [2])</i>
/ban [время] [причина] — бан
/unban — разбан
/kick [причина] — кик
/warn [время] [причина] — варн ({MAX_WARNS} варна = бан)
/unwarn — снять варн
/say [текст] — написать от лица бота в чат (/say @user|ID текст — в ЛС)

⭐️⭐️⭐⭐️ <b>[4] Старший админ:</b>
<i>(+ возможности Админа [3])</i>
/rank 1 — назначить Помощника [1]
/rank 0 — снять Помощника [1]

⭐⭐️⭐️⭐️⭐️ <b>[5] Создатель:</b>
Полный доступ ко всем функциям и управление всеми рангами
/unlimit — управление иммунитетом участников
/setimmunity [время] — установить дефолтное время иммунитета (напр. /setimmunity 1h)
/setlimits [варны] [кики/баны] — настройка лимитов анти-рейда (за 5 минут)

⏱ <b>Форматы времени для наказаний (/mute, /ban, /warn):</b>
<code>m</code> / <code>м</code> — минуты (10m, 15м)
<code>h</code> / <code>ч</code> — часы (1h, 2ч)
<code>d</code> / <code>д</code> — дни (1d, 3д)
<code>w</code> / <code>н</code> — недели (1w, 2н)
<i>Примеры: <code>/mute @user 1h</code>, <code>/ban @user 2d спам</code>, <code>/warn 30m</code></i>

<b>Для всех:</b>
/info — инфо об участнике (reply, @username или ID)
/me — инфо о себе
/week — сообщения участника за неделю
/warns — варны участника
/top [день|неделя|месяц|всё] — топ активности
/staff — персонал группы по рангам
/rank — ранг участника, /ranks — описание рангов"""

DM_HELP = """<b>Панель владельца и администратора (ЛС)</b>

/say [@user|ID_чата] [текст] — написать от лица бота в ЛС или чат
/chats — интерактивное меню групп (выбор группы, выход бота из чата)
/top [ID_чата] [день|неделя|месяц|всё] — топ активности
/topweek [ID_чата] — топ активности за эту неделю
/topday [ID_чата] — топ активности за сегодня
/week [ID_чата] @user|ID — сообщения участника за эту неделю
/info [ID_чата] @user|ID — карточка участника
/lock [ID_чата] — закрыть чат
/unlock [ID_чата] — открыть чат
/tz [ID_чата] kyiv|moscow|cet — часовой пояс

ID_чата можно не указывать, если бот состоит только в одной группе."""


@group.message(Command("start", "help", "помощь", prefix=PREFIX))
async def cmd_help(m: Message):
    await m.reply(GROUP_HELP)


# ---------------------- УДАЛЕНИЕ СООБЩЕНИЙ [1] ---------------------
@group.message(Command("del", "delete", "удал", "удалить", prefix=PREFIX))
async def cmd_del(m: Message):
    if not await require_rank(m, 1):
        return
    if not m.reply_to_message:
        await m.reply("Ответьте на сообщение, которое нужно удалить.")
        return
    try:
        await m.reply_to_message.delete()
        try:
            await m.delete()
        except TelegramAPIError:
            pass
    except TelegramAPIError as e:
        await m.reply(f"⚠️ Не удалось удалить сообщение: {esc(e.message)}")


# ---------------------- ЗАКРЕП / ОТКРЕП [1] ------------------------
@group.message(Command("pin", "закреп", "закрепить", prefix=PREFIX))
async def cmd_pin(m: Message):
    if not await require_rank(m, 1):
        return
    if not m.reply_to_message:
        await m.reply("Ответьте на сообщение, которое нужно закрепить.")
        return
    try:
        await m.bot.pin_chat_message(chat_id=m.chat.id, message_id=m.reply_to_message.message_id)
        await m.reply("📌 Сообщение закреплено.")
    except TelegramAPIError as e:
        await m.reply(f"⚠️ Не удалось закрепить: {esc(e.message)}")


@group.message(Command("unpin", "откреп", "открепить", prefix=PREFIX))
async def cmd_unpin(m: Message):
    if not await require_rank(m, 1):
        return
    try:
        if m.reply_to_message:
            await m.bot.unpin_chat_message(chat_id=m.chat.id, message_id=m.reply_to_message.message_id)
        else:
            await m.bot.unpin_chat_message(chat_id=m.chat.id)
        await m.reply("📌 Сообщение откреплено.")
    except TelegramAPIError as e:
        await m.reply(f"⚠️ Не удалось открепить: {esc(e.message)}")


# --------------------------- МУТ [1] -------------------------------
@group.message(Command("mute", "мут", prefix=PREFIX))
async def cmd_mute(m: Message, command: CommandObject):
    if not await require_rank(m, 1):
        return
    t = await get_target(m, command)
    if not t:
        return
    uid, name, rest = t
    delta = DEFAULT_MUTE
    if rest and (d := parse_dur(rest[0])):
        delta, rest = d, rest[1:]
    until = datetime.now(timezone.utc) + delta
    await demote_if_admin(m.bot, m.chat.id, uid)
    await safe(
        m,
        m.bot.restrict_chat_member(
            m.chat.id, uid, permissions=ChatPermissions(can_send_messages=False), until_date=until
        ),
        f"🔇 {link(uid, name)} в муте на {dur_text(delta.total_seconds())}.{reason_text(rest)}",
    )


@group.message(Command("unmute", "размут", prefix=PREFIX))
async def cmd_unmute(m: Message, command: CommandObject):
    if not await require_rank(m, 1):
        return
    t = await get_target(m, command)
    if not t:
        return
    uid, name, _ = t
    chat = await m.bot.get_chat(m.chat.id)
    perms = chat.permissions or ChatPermissions(can_send_messages=True)
    await safe(
        m,
        m.bot.restrict_chat_member(m.chat.id, uid, permissions=perms),
        f"🔊 С {link(uid, name)} снят мут.",
    )


# --------------------------- ПРИЗЫВ [1] ----------------------------
CALL_COOLDOWN = 60
CALL_CHUNK = 40
_last_call: dict[int, float] = {}


def mention(uid: int, name: str, username: str) -> str:
    return f"@{username}" if username else link(uid, name or "участник")


@group.message(Command("all", "призыв", "everyone", "сбор", "калл", "call", prefix=PREFIX))
async def cmd_all(m: Message, command: CommandObject):
    if not await require_rank(m, 1):
        return
    cid = m.chat.id
    wait = CALL_COOLDOWN - (time.time() - _last_call.get(cid, 0))
    if wait > 0:
        await m.reply(f"⏳ Призыв можно повторить через {int(wait)} сек.")
        return

    caller_id = m.from_user.id if m.from_user and not m.sender_chat else 0
    people: dict[int, tuple] = {}
    for uid, name, uname in db.execute(
        "SELECT user_id,name,username FROM users WHERE chat_id=? AND COALESCE(gone,0)=0", (cid,)
    ):
        people[uid] = (name, uname)
    try:
        for a in await m.bot.get_chat_administrators(cid):
            if not a.user.is_bot:
                people[a.user.id] = (a.user.full_name, (a.user.username or "").lower())
    except TelegramAPIError:
        pass
    people.pop(caller_id, None)
    people.pop(m.bot.id, None)
    if not people:
        await m.reply("Некого призывать: я вижу только тех, кто уже писал в чат.")
        return

    _last_call[cid] = time.time()
    text = (command.args or "").strip()[:1000]
    who = link(caller_id, m.from_user.full_name) if caller_id else "админа"
    head = f"📢 <b>Призыв</b> от {who}"
    if text:
        head += f"\n\n{esc(text)}"
    reply_to = m.reply_to_message.message_id if m.reply_to_message else m.message_id

    items = [mention(uid, n, un) for uid, (n, un) in people.items()]
    for i in range(0, len(items), CALL_CHUNK):
        chunk = " ".join(items[i : i + CALL_CHUNK])
        body = f"{head}\n\n{chunk}" if i == 0 else f"📢 <b>Призыв</b> (продолжение)\n\n{chunk}"
        try:
            await m.bot.send_message(cid, body, reply_to_message_id=reply_to)
        except TelegramAPIError as e:
            await m.reply(f"⚠️ Не получилось отправить призыв: {esc(e.message)}")
            return
        if i + CALL_CHUNK < len(items):
            await asyncio.sleep(1.2)


# ---------------------------- ТЕГИ [2] -----------------------------
@group.message(Command("tag", "тег", prefix=PREFIX))
async def cmd_tag(m: Message, command: CommandObject):
    if not await require_rank(m, 2):
        return
    t = await get_target(m, command, allow_admin=True)
    if not t:
        return
    uid, name, rest = t
    text = " ".join(rest).strip()
    if not text:
        await m.reply("Укажите текст тега: /tag @username текст или /tag текст ответом на сообщение.")
        return
    if len(text) > 32:
        await m.reply("Тег слишком длинный (макс. 32 символа).")
        return
    ensure_user(m.chat.id, uid, name)
    db.execute("UPDATE users SET tag=? WHERE chat_id=? AND user_id=?", (text, m.chat.id, uid))
    db.commit()
    await m.reply(f"🏷 {link(uid, name)} получил тег: <b>{esc(text)}</b>")


@group.message(Command("untag", "снятьтег", prefix=PREFIX))
async def cmd_untag(m: Message, command: CommandObject):
    if not await require_rank(m, 2):
        return
    t = await get_target(m, command, allow_admin=True)
    if not t:
        return
    uid, name, _ = t
    db.execute("UPDATE users SET tag=NULL WHERE chat_id=? AND user_id=?", (m.chat.id, uid))
    db.commit()
    await m.reply(f"🏷 Тег у {link(uid, name)} убран.")


# ------------------------- ЗАКРЫТЬ ЧАТ [2] -------------------------
@group.message(Command("lock", "закрыть", prefix=PREFIX))
async def cmd_lock(m: Message):
    if not await require_rank(m, 2):
        return
    await safe(m, do_lock(m.bot, m.chat.id), "🔒 Чат закрыт. Писать могут только админы.")


@group.message(Command("unlock", "открыть", prefix=PREFIX))
async def cmd_unlock(m: Message):
    if not await require_rank(m, 2):
        return
    await safe(m, do_unlock(m.bot, m.chat.id), "🔓 Чат открыт.")


# ---------------------- ЧАСОВОЙ ПОЯС [2] ---------------------------
@group.message(Command("tz", "пояс", prefix=PREFIX))
async def cmd_tz(m: Message):
    if not await require_rank(m, 2):
        return
    await m.reply(
        f"🕐 Текущий часовой пояс: <b>{tz_label(m.chat.id)}</b>\nВыберите новый:", reply_markup=tz_kb()
    )


@group.callback_query(F.data.startswith("tz:"))
async def cb_tz(cb: CallbackQuery):
    key = cb.data[3:]
    if key not in TIMEZONES or not cb.message:
        await cb.answer()
        return
    r = await eff_rank(cb.bot, cb.message.chat.id, cb.from_user.id)
    if r < 2:
        await cb.answer("Команда доступна с ранга [2] Модератор", show_alert=True)
        return
    set_tz(cb.message.chat.id, key)
    await cb.message.edit_text(f"🕐 Часовой пояс: <b>{TIMEZONES[key][0]}</b>")
    await cb.answer("Готово")


# ---------------------- НАПИСАТЬ ОТ ЛИЦА БОТА [3] -------------------
@group.message(Command("say", "скажи", "echo", "post", "pm", "лс", prefix=PREFIX))
async def cmd_say(m: Message, command: CommandObject):
    if not await require_rank(m, 3):
        return

    text = (command.args or "").strip()
    if not text:
        await m.reply("Укажите текст: <code>/say Текст</code> или <code>/say @username/ID Текст</code>")
        return

    args = text.split(maxsplit=1)

    if args:
        ref = args[0]
        res = await resolve_ref(m.bot, m.chat.id, args)
        if res:
            target_uid, _, rest = res
            msg_text = " ".join(rest).strip()
            if not msg_text:
                await m.reply("Укажите текст сообщения.")
                return
            try:
                await m.bot.send_message(target_uid, msg_text)
                await m.reply("✅ Сообщение отправлено пользователю в ЛС.")
            except TelegramAPIError as e:
                await m.reply(f"⚠️ Не удалось отправить сообщение в ЛС: {esc(e.message)}")
            return
        elif ref.startswith("-") and ref[1:].isdigit():
            target_cid = int(ref)
            msg_text = args[1] if len(args) > 1 else ""
            if not msg_text:
                await m.reply("Укажите текст сообщения.")
                return
            try:
                await m.bot.send_message(target_cid, msg_text)
                await m.reply(f"✅ Сообщение отправлено в чат <code>{target_cid}</code>.")
            except TelegramAPIError as e:
                await m.reply(f"⚠ Не удалось отправить сообщение в чат: {esc(e.message)}")
            return

    reply_to_id = m.reply_to_message.message_id if m.reply_to_message else None

    try:
        await m.delete()
    except TelegramAPIError:
        pass

    try:
        await m.bot.send_message(m.chat.id, text, reply_to_message_id=reply_to_id)
    except TelegramAPIError as e:
        await m.reply(f"⚠️ Не удалось отправить сообщение: {esc(e.message)}")


# ---------------------------- БАН [3] ------------------------------
@group.message(Command("ban", "бан", prefix=PREFIX))
async def cmd_ban(m: Message, command: CommandObject):
    if not await require_rank(m, 3):
        return
    if not await check_protection(m, "kick_ban"):
        return
    t = await get_target(m, command)
    if not t:
        return
    uid, name, rest = t
    delta = None
    if rest and (d := parse_dur(rest[0])):
        delta, rest = d, rest[1:]

    until = (datetime.now(timezone.utc) + delta) if delta else None
    await demote_if_admin(m.bot, m.chat.id, uid)
    t_str = now_str(m.chat.id)
    ban_dur_text = f" на {dur_text(delta.total_seconds())}" if delta else ""

    if await safe(
        m,
        m.bot.ban_chat_member(m.chat.id, uid, until_date=until),
        f"⛔ {link(uid, name)} забанен{ban_dur_text}.\n🕒 Время: <code>{t_str}</code>{reason_text(rest)}",
    ):
        clear_rank(m.chat.id, uid)


# ---------------------------- КИК [3] ------------------------------
@group.message(Command("kick", "кик", prefix=PREFIX))
async def cmd_kick(m: Message, command: CommandObject):
    if not await require_rank(m, 3):
        return
    if not await check_protection(m, "kick_ban"):
        return
    t = await get_target(m, command)
    if not t:
        return
    uid, name, rest = t

    async def do_kick():
        await demote_if_admin(m.bot, m.chat.id, uid)
        await m.bot.ban_chat_member(m.chat.id, uid)
        await m.bot.unban_chat_member(m.chat.id, uid, only_if_banned=True)
        clear_rank(m.chat.id, uid)

    t_str = now_str(m.chat.id)
    await safe(m, do_kick(), f"👢 {link(uid, name)} исключён из чата.\n🕒 Время: <code>{t_str}</code>{reason_text(rest)}")


# --------------------------- ВАРНЫ [3] -----------------------------
@group.message(Command("warn", "варн", prefix=PREFIX))
async def cmd_warn(m: Message, command: CommandObject):
    if not await require_rank(m, 3):
        return
    if not await check_protection(m, "warn"):
        return
    t = await get_target(m, command)
    if not t:
        return
    uid, name, rest = t
    delta = None
    if rest and (d := parse_dur(rest[0])):
        delta, rest = d, rest[1:]

    ensure_user(m.chat.id, uid, name)
    row = get_user_row(m.chat.id, uid)
    n = (row[5] or 0) + 1 if row else 1
    t_str = now_str(m.chat.id)
    warn_dur_text = f" на {dur_text(delta.total_seconds())}" if delta else ""
    until = (datetime.now(timezone.utc) + delta) if delta else None

    if n >= MAX_WARNS:
        set_warns(m.chat.id, uid, 0)
        await demote_if_admin(m.bot, m.chat.id, uid)
        if await safe(
            m,
            m.bot.ban_chat_member(m.chat.id, uid, until_date=until),
            f"⚠ {link(uid, name)} получил варн {n}/{MAX_WARNS}{warn_dur_text} и забанен.\n🕒 Время: <code>{t_str}</code>{reason_text(rest)}",
        ):
            clear_rank(m.chat.id, uid)
    else:
        set_warns(m.chat.id, uid, n)
        await m.reply(f"⚠️ {link(uid, name)} получил варн {n}/{MAX_WARNS}{warn_dur_text}.\n🕒 Время: <code>{t_str}</code>{reason_text(rest)}")


@group.message(Command("unwarn", "анварн", prefix=PREFIX))
async def cmd_unwarn(m: Message, command: CommandObject):
    if not await require_rank(m, 3):
        return
    t = await get_target(m, command, allow_admin=True)
    if not t:
        return
    uid, name, _ = t
    row = get_user_row(m.chat.id, uid)
    n = max(0, (row[5] if row else 0) - 1)
    if row:
        set_warns(m.chat.id, uid, n)
    await m.reply(f"✅ У {link(uid, name)} снят варн. Теперь {n}/{MAX_WARNS}.")


@group.message(Command("warns", "варны", prefix=PREFIX))
async def cmd_warns(m: Message, command: CommandObject):
    args = (command.args or "").split()
    uid, name, _, err_msg = await resolve(m, args)
    if uid is None:
        if args:
            await m.reply(err_msg or "Пользователь не найден.")
            return
        uid, name = m.from_user.id, m.from_user.full_name
    row = get_user_row(m.chat.id, uid)
    n = row[5] if row else 0
    await m.reply(f"⚠️ Варны {link(uid, name)}: {n}/{MAX_WARNS}")


@group.message(Command("ver", "версия", prefix=PREFIX))
async def cmd_ver(m: Message):
    await m.reply(f"🤖 Версия бота: <b>{BOT_VERSION}</b>")


# ---------------------------- ИНФО И АКТИВНОСТЬ --------------------
@group.message(Command("info", "who", "инфо", "кто", prefix=PREFIX))
async def cmd_info(m: Message, command: CommandObject):
    args = (command.args or "").split()
    uid, name, _, err_msg = await resolve(m, args)
    if uid is None:
        if args:
            await m.reply(err_msg or "Пользователь не найден.")
            return
        uid, name = m.from_user.id, m.from_user.full_name
    is_self = bool(m.from_user) and uid == m.from_user.id
    await send_card(m, m.chat.id, uid, name, is_self)


@group.message(Command("me", "я", prefix=PREFIX))
async def cmd_me(m: Message):
    if not m.from_user:
        return
    await send_card(m, m.chat.id, m.from_user.id, m.from_user.full_name, True)


@group.message(Command("week", "неделя", "нед", "msgs", prefix=PREFIX))
async def cmd_week(m: Message, command: CommandObject):
    args = (command.args or "").split()
    uid, name, _, err_msg = await resolve(m, args)
    if uid is None:
        if args:
            await m.reply(err_msg or "Пользователь не найден.")
            return
        uid, name = m.from_user.id, m.from_user.full_name
    await m.reply(week_text(m.chat.id, uid, name))


@group.message(Command("top", "топ", prefix=PREFIX))
async def cmd_top(m: Message, command: CommandObject):
    await m.reply(top_text(m.chat.id, parse_period((command.args or "").split())))


@group.message(Command("topweek", "топнеделя", "топнед", prefix=PREFIX))
async def cmd_topweek(m: Message):
    await m.reply(top_text(m.chat.id, "week"))


@group.message(Command("topday", "топдень", "топсегодня", prefix=PREFIX))
async def cmd_topday(m: Message):
    await m.reply(top_text(m.chat.id, "day"))


@group.message(Command("topall", "alltop", "топвсё", "топвсе", "топвсего", prefix=PREFIX))
async def cmd_topall(m: Message):
    await m.reply(top_text(m.chat.id, "all"))


@group.message(Command("staff", "стафф", "админы", prefix=PREFIX))
async def cmd_staff(m: Message):
    cid = m.chat.id
    people: dict[int, list] = {}
    for a in await m.bot.get_chat_administrators(cid):
        if a.user.is_bot:
            continue
        base = 5 if (a.status == "creator" or a.user.id in OWNER_IDS) else 3
        people[a.user.id] = [a.user.full_name, base, getattr(a, "custom_title", None)]
    for uid, name, rk in db.execute("SELECT user_id,name,rank FROM users WHERE chat_id=? AND rank>=1", (cid,)):
        if uid in people:
            people[uid][1] = max(people[uid][1], rk)
        else:
            people[uid] = [name, rk, None]
    by_rank: dict[int, list] = {}
    for uid, (name, rk, title) in people.items():
        by_rank.setdefault(rk, []).append((uid, name, title))
    out = ["👥 <b>Персонал группы</b>"]
    for rk in sorted(by_rank, reverse=True):
        out.append(f"\n{stars(rk)} <b>{rank_title(rk)}</b>")
        for uid, name, title in by_rank[rk]:
            extra = []
            if title:
                extra.append(esc(title))
            row = get_user_row(cid, uid)
            if row and row[4]:
                extra.append(f"🏷 {esc(row[4])}")
            suffix = " — " + ", ".join(extra) if extra else ""
            out.append(f"👤 {link(uid, name)}{suffix}")
    await m.reply("\n".join(out))


# --------------------------- УПРАВЛЕНИЕ ЗАЩИТОЙ И ИММУНИТЕТОМ ---------------------
@group.message(Command("setimmunity", "время_защиты", prefix=PREFIX))
async def cmd_setimmunity(m: Message, command: CommandObject):
    if m.from_user and m.from_user.id not in OWNER_IDS:
        await m.reply("⛔ Настраивать стандартное время иммунитета могут только владельцы бота.")
        return
    args = (command.args or "").split()
    if not args or not (d := parse_dur(args[0])):
        sec = get_immunity_sec(m.chat.id)
        await m.reply(
            f"⚙️ Текущий стандартный лимит иммунитета: <b>{dur_text(sec)}</b>.\n"
            f"Чтобы изменить, укажите время, например: <code>/setimmunity 2h</code> или <code>/setimmunity 30m</code>"
        )
        return
    sec = int(d.total_seconds())
    set_immunity_sec(m.chat.id, sec)
    await m.reply(f"✅ Стандартное время иммунитета изменено на <b>{dur_text(sec)}</b>.")


@group.message(Command("setlimits", "лимиты", "setlimit", "настройка_лимитов", prefix=PREFIX))
async def cmd_setlimits(m: Message, command: CommandObject):
    if m.from_user and m.from_user.id not in OWNER_IDS:
        await m.reply("⛔ Настраивать лимиты анти-рейда могут только владельцы бота.")
        return
    args = (command.args or "").split()
    if len(args) < 2 or not args[0].isdigit() or not args[1].isdigit():
        w_lim, kb_lim = get_chat_limits(m.chat.id)
        await m.reply(
            f"⚙️ <b>Текущие лимиты анти-рейда (за 5 минут):</b>\n"
            f"• Варны: <b>{w_lim}</b>\n"
            f"• Кики и баны (суммарно): <b>{kb_lim}</b>\n\n"
            f"Чтобы изменить, укажите количество: <code>/setlimits [варны] [кики/баны]</code>\n"
            f"Пример: <code>/setlimits 5 3</code>"
        )
        return
    w_lim = int(args[0])
    kb_lim = int(args[1])
    if w_lim < 1 or kb_lim < 1:
        await m.reply("⚠️ Лимиты должны быть не менее 1.")
        return
    set_chat_limits(m.chat.id, w_lim, kb_lim)
    await m.reply(
        f"✅ <b>Новые лимиты анти-рейда сохранены:</b>\n"
        f"• Максимум варнов: <b>{w_lim}</b>\n"
        f"• Максимум киков/банов: <b>{kb_lim}</b>\n"
        f"<i>(Интервал проверки: 5 минут)</i>"
    )


@group.message(Command("unlimit", "иммунитет", "снятьзащиту", prefix=PREFIX))
async def cmd_unlimit(m: Message, command: CommandObject):
    if m.from_user and m.from_user.id not in OWNER_IDS:
        await m.reply("⛔ Управлять защитой и иммунитетом могут только владельцы бота.")
        return

    t = await get_target(m, command, allow_admin=True)
    if not t:
        return
    uid, name, rest = t
    key = (m.chat.id, uid)

    blocked_admins.discard(key)

    if rest and rest[0] == "0":
        immune_admins.pop(key, None)
        await m.reply(f"🔒 Иммунитет для {link(uid, name)} аннулирован. Лимиты защиты снова действуют.")
    elif rest and (d := parse_dur(rest[0])):
        sec = d.total_seconds()
        immune_admins[key] = time.time() + sec
        warn_logs[key].clear()
        kick_ban_logs[key].clear()
        await m.reply(f"🔓 Для {link(uid, name)} сняты ограничения и установлен иммунитет на {dur_text(sec)}.")
    else:
        sec = get_immunity_sec(m.chat.id)
        immune_admins[key] = time.time() + sec
        warn_logs[key].clear()
        kick_ban_logs[key].clear()
        await m.reply(f"🔓 Для {link(uid, name)} сняты ограничения и установлен иммунитет на {dur_text(sec)}.")


# --------------------------- РАНГИ [4] -----------------------------
@group.message(Command("ranks", "ранги", prefix=PREFIX))
async def cmd_ranks(m: Message):
    await m.reply(
        "<b>Ранги и права</b>\n\n"
        f"{stars(1)} [1] Помощник — удаление сообщений (/del), мут (/mute), призыв (/all), закреп/откреп (/pin, /unpin)\n"
        f"{stars(2)} [2] Модератор — все возможности [1] + теги (/tag), /lock, /unlock, часовой пояс (/tz)\n"
        f"{stars(3)} [3] Админ — все возможности [1-2] + баны (/ban), варны (/warn), кик (/kick), отправка сообщений (/say)\n"
        f"{stars(4)} [4] Старший админ — все возможности [1-3] + назначение и снятие только [1] Помощника\n"
        f"{stars(5)} [5] Создатель — полный доступ ко всем функциям и управление всеми рангами\n\n"
        "⏱ <b>Форматы времени наказаний:</b> <code>10m</code>/<code>10м</code>, <code>1h</code>/<code>1ч</code>, <code>1d</code>/<code>1д</code>, <code>1w</code>/<code>1н</code> (напр. <code>/mute @user 1h</code>)\n"
        "Выдать: <code>/rank @username N</code> или ответом: <code>/rank N</code>.\n"
        "Посмотреть: <code>/rank</code> или <code>/rank @user</code>."
    )


@group.message(Command("rank", "ранг", prefix=PREFIX))
async def cmd_rank(m: Message, command: CommandObject):
    args = (command.args or "").split()
    has_reply = bool(m.reply_to_message and m.reply_to_message.from_user)
    if not has_reply and args and re.fullmatch(r"\d", args[0]):
        await m.reply("Ответьте на сообщение участника или укажите юзернейм, например: <code>/rank @username 1</code>")
        return
    uid, name, rest, _ = await resolve(m, args)
    if uid is None:
        if not m.from_user:
            return
        uid, name, rest = m.from_user.id, m.from_user.full_name, []

    if not rest:
        r = await eff_rank(m.bot, m.chat.id, uid)
        await m.reply(f"{stars(r) or '▫'} [{r}] Ранг {link(uid, name)}: <b>{rank_title(r)}</b>")
        return

    if not re.fullmatch(r"[0-5]", rest[0]):
        await m.reply("Ранг — число от 0 до 5. Список: /ranks")
        return
    new = int(rest[0])
    if m.sender_chat or not m.from_user:
        await m.reply("Анонимный админ не может выдавать ранги. Отключите анонимность.")
        return
    if uid == m.bot.id:
        await m.reply("Мне ранг не нужен 🙂")
        return

    actor = await eff_rank(m.bot, m.chat.id, m.from_user.id)
    if actor < 4:
        await m.reply("⛔ Выдавать ранги может ранг [4] Старший админ и выше.")
        return

    target_rank = await eff_rank(m.bot, m.chat.id, uid)

    if actor == 4:
        if new not in (0, 1):
            await m.reply("⛔ Старший админ [4] может назначать только ранг [1] Помощник или снимать его (/rank 0).")
            return
        if new == 1 and target_rank >= 2:
            await m.reply("⛔ Старший админ [4] не может изменять ранг участников с рангом [2] и выше.")
            return
        if new == 0 and target_rank != 1:
            await m.reply("⛔ Старший админ [4] может снимать ранг только у [1] Помощников.")
            return

    if actor < 5 and new >= actor:
        await m.reply("⛔ Нельзя выдать ранг, равный вашему или выше.")
        return
    if actor < 5 and target_rank >= actor:
        await m.reply("⛔ Нельзя менять ранг участника, равного вам или выше.")
        return

    ensure_user(m.chat.id, uid, name)
    db.execute("UPDATE users SET rank=? WHERE chat_id=? AND user_id=?", (new, m.chat.id, uid))
    db.commit()
    final = await eff_rank(m.bot, m.chat.id, uid)
    if new == 0:
        text = f"▫️ Ранг у {link(uid, name)} снят."
    else:
        text = f"{stars(new)} {link(uid, name)} — ранг [{new}] {rank_title(new)}."
    if final != new:
        text += f"\nℹ️ Итоговый ранг [{final}] {rank_title(final)}: выше его даёт статус в Telegram."
    await m.reply(text)


# ====================== ЛС: ПАНЕЛЬ ВЛАДЕЛЬЦА =======================
def pick_chat(args: list[str]):
    if args and re.fullmatch(r"-\d+", args[0]):
        return int(args[0]), args[1:]
    chats = db.execute("SELECT chat_id FROM chats").fetchall()
    if len(chats) == 1:
        return chats[0][0], args
    return None, args


NEED_CHAT = "Укажите ID группы (список: /chats). Пример: <code>/top -1001234567890</code>"


def build_chats_kb() -> InlineKeyboardMarkup | None:
    rows = db.execute("SELECT chat_id, title FROM chats").fetchall()
    if not rows:
        return None
    kb = []
    for cid, title in rows:
        kb.append([InlineKeyboardButton(text=f"💬 {esc(title)}", callback_data=f"pm_chat:{cid}")])
    return InlineKeyboardMarkup(inline_keyboard=kb)


@private.message(Command("start", "help", "помощь", prefix=PREFIX))
async def dm_help(m: Message):
    await m.answer(DM_HELP)


@private.message(Command("ver", "версия", prefix=PREFIX))
async def dm_ver(m: Message):
    await m.answer(f"🤖 Версия бота: <b>{BOT_VERSION}</b>")


@private.message(Command("chats", "чаты", prefix=PREFIX))
async def dm_chats(m: Message):
    kb = build_chats_kb()
    if not kb:
        await m.answer("Бот пока не состоит ни в одной группе.")
        return
    await m.answer("📋 <b>Выберите группу для управления:</b>", reply_markup=kb)


# --- Интерактивные Callback-обработчики управления чатами в ЛС ---
@private.callback_query(F.data.startswith("pm_chat:"))
async def cb_pm_chat(cb: CallbackQuery):
    cid = int(cb.data.split(":")[1])
    row = db.execute("SELECT title FROM chats WHERE chat_id=?", (cid,)).fetchone()
    title = row[0] if row else str(cid)

    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="🔒 Закрыть чат", callback_data=f"pm_act:lock:{cid}"),
                InlineKeyboardButton(text="🔓 Открыть чат", callback_data=f"pm_act:unlock:{cid}"),
            ],
            [
                InlineKeyboardButton(text="🚪 Покинуть чат", callback_data=f"pm_leave_ask:{cid}")
            ],
            [
                InlineKeyboardButton(text="⬅️ Назад к списку", callback_data="pm_back_chats")
            ]
        ]
    )
    await cb.message.edit_text(f"💬 Управление чатом: <b>{esc(title)}</b>\n🆔 ID: <code>{cid}</code>", reply_markup=kb)
    await cb.answer()


@private.callback_query(F.data == "pm_back_chats")
async def cb_pm_back_chats(cb: CallbackQuery):
    kb = build_chats_kb()
    if not kb:
        await cb.message.edit_text("Бот пока не состоит ни в одной группе.")
        return
    await cb.message.edit_text("📋 <b>Выберите группу для управления:</b>", reply_markup=kb)
    await cb.answer()


@private.callback_query(F.data.startswith("pm_leave_ask:"))
async def cb_pm_leave_ask(cb: CallbackQuery):
    cid = int(cb.data.split(":")[1])
    row = db.execute("SELECT title FROM chats WHERE chat_id=?", (cid,)).fetchone()
    title = row[0] if row else str(cid)
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="✅ Да, покинуть", callback_data=f"pm_leave_confirm:{cid}"),
                InlineKeyboardButton(text="❌ Отмена", callback_data=f"pm_chat:{cid}")
            ]
        ]
    )
    await cb.message.edit_text(f"❓ Вы уверены, что хотите, чтобы бот покинул чат <b>{esc(title)}</b>?", reply_markup=kb)
    await cb.answer()


@private.callback_query(F.data.startswith("pm_leave_confirm:"))
async def cb_pm_leave_confirm(cb: CallbackQuery):
    cid = int(cb.data.split(":")[1])
    row = db.execute("SELECT title FROM chats WHERE chat_id=?", (cid,)).fetchone()
    title = row[0] if row else str(cid)
    try:
        await cb.bot.leave_chat(cid)
        db.execute("DELETE FROM chats WHERE chat_id=?", (cid,))
        db.commit()
        await cb.message.edit_text(f"✅ Бот успешно покинул чат <b>{esc(title)}</b> (<code>{cid}</code>).")
    except TelegramAPIError as e:
        await cb.message.edit_text(f"⚠️ Ошибка при попытке покинуть чат: {esc(e.message)}")
    await cb.answer()


@private.callback_query(F.data.startswith("pm_act:"))
async def cb_pm_act(cb: CallbackQuery):
    _, act, cid_str = cb.data.split(":")
    cid = int(cid_str)
    if act == "lock":
        try:
            await do_lock(cb.bot, cid)
            await cb.answer("Чат закрыт", show_alert=True)
        except TelegramAPIError as e:
            await cb.answer(f"Ошибка: {e.message}", show_alert=True)
    elif act == "unlock":
        try:
            await do_unlock(cb.bot, cid)
            await cb.answer("Чат открыт", show_alert=True)
        except TelegramAPIError as e:
            await cb.answer(f"Ошибка: {e.message}", show_alert=True)


# --- Текстовые команды ЛС ---
@private.message(Command("top", "топ", prefix=PREFIX))
async def dm_top(m: Message, command: CommandObject):
    cid, rest = pick_chat((command.args or "").split())
    if cid is None:
        await m.answer(NEED_CHAT)
        return
    await m.answer(top_text(cid, parse_period(rest)))


@private.message(Command("topweek", "топнеделя", "топнед", prefix=PREFIX))
async def dm_topweek(m: Message, command: CommandObject):
    cid, _ = pick_chat((command.args or "").split())
    if cid is None:
        await m.answer(NEED_CHAT)
        return
    await m.answer(top_text(cid, "week"))


@private.message(Command("topday", "топдень", "топсегодня", prefix=PREFIX))
async def dm_topday(m: Message, command: CommandObject):
    cid, _ = pick_chat((command.args or "").split())
    if cid is None:
        await m.answer(NEED_CHAT)
        return
    await m.answer(top_text(cid, "day"))


@private.message(Command("week", "неделя", "нед", prefix=PREFIX))
async def dm_week(m: Message, command: CommandObject):
    cid, rest = pick_chat((command.args or "").split())
    if cid is None:
        await m.answer(NEED_CHAT)
        return
    r = await resolve_ref(m.bot, cid, rest)
    if not r:
        await m.answer("Укажите участника: @username или ID.")
        return
    await m.answer(week_text(cid, r[0], r[1]))


@private.message(Command("info", "инфо", prefix=PREFIX))
async def dm_info(m: Message, command: CommandObject):
    cid, rest = pick_chat((command.args or "").split())
    if cid is None:
        await m.answer(NEED_CHAT)
        return
    r = await resolve_ref(m.bot, cid, rest)
    if not r:
        await m.answer("Укажите участника: @username или ID.")
        return
    await send_card(m, cid, r[0], r[1], False)


@private.message(Command("lock", "закрыть", prefix=PREFIX))
async def dm_lock(m: Message, command: CommandObject):
    cid, _ = pick_chat((command.args or "").split())
    if cid is None:
        await m.answer(NEED_CHAT)
        return
    await safe(m, do_lock(m.bot, cid), "🔒 Чат закрыт. Писать могут только админы.")


@private.message(Command("unlock", "открыть", prefix=PREFIX))
async def dm_unlock(m: Message, command: CommandObject):
    cid, _ = pick_chat((command.args or "").split())
    if cid is None:
        await m.answer(NEED_CHAT)
        return
    await safe(m, do_unlock(m.bot, cid), "🔓 Чат открыт.")


@private.message(Command("tz", "пояс", prefix=PREFIX))
async def dm_tz(m: Message, command: CommandObject):
    cid, rest = pick_chat((command.args or "").split())
    if cid is None:
        await m.answer(NEED_CHAT)
        return
    key = rest[0].lower() if rest else ""
    key = TZ_ALIASES.get(key, key)
    if key not in TIMEZONES:
        await m.answer(
            f"Сейчас: <b>{tz_label(cid)}</b>. Доступно: kyiv (Киев), moscow (Москва), cet (Центральная Европа).\n"
            f"Пример: <code>/tz {cid} moscow</code>"
        )
        return
    set_tz(cid, key)
    await m.answer(f"🕐 Часовой пояс группы: <b>{TIMEZONES[key][0]}</b>")


# ============================== ЗАПУСК =============================
async def main():
    token = os.getenv("BOT_TOKEN", "8224245731:AAH2axPcjq4v8vNubqURc0Q7xatc9d3-K0s")
    if not token:
        raise SystemExit("Задайте токен: export BOT_TOKEN='...'")
    bot = Bot(token, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    logging.info("Версия бота: %s", BOT_VERSION)
    dp = Dispatcher()
    dp.message.outer_middleware(Stats())
    dp.include_router(events)
    dp.include_router(private)
    dp.include_router(deny)
    dp.include_router(group)
    await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())


if __name__ == "__main__":
    asyncio.run(main())