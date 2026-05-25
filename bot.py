import asyncio
import html
import io
import logging
import os
import random
import re
import sqlite3
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from typing import Optional

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from dotenv import load_dotenv
from aiogram import Bot, Dispatcher, F
from aiogram.exceptions import TelegramBadRequest
from aiogram.filters import CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    BotCommand,
    BufferedInputFile,
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    MenuButtonCommands,
    Message,
)

DB_PATH = "bot_data.sqlite3"
TZ = timezone(timedelta(hours=3))  # Europe/Moscow-like default

MAX_STREAK_FREEZES = 2
STREAK_FREEZE_COST = 120

LEAGUE_NAMES = [
    "Бронза",
    "Серебро",
    "Золото",
    "Сапфир",
    "Рубин",
    "Изумруд",
    "Аметист",
    "Жемчуг",
    "Обсидиан",
    "Алмаз",
]
# Порог минут за завершившуюся неделю для повышения.
LEAGUE_PROMOTION_MINUTES = [0, 240, 300, 360, 420, 480, 540, 600, 660, 720, 10**9]
# Если минут ниже safe-порога, будет понижение (кроме Бронзы).
LEAGUE_SAFE_MINUTES = [0, 0, 120, 150, 180, 210, 240, 270, 300, 330, 360]
LEAGUE_PROMOTION_REWARD = [0, 0, 25, 35, 45, 55, 65, 75, 90, 110, 140]
LEAGUE_DEMOTION_PENALTY = [0, 0, 20, 30, 40, 50, 60, 70, 85, 100, 120]

STREAK_CHALLENGE_OPTIONS = {
    7: 100,
    14: 250,
    30: 600,
}

CASINO_SPIN_COST = 10
CASINO_PAYOUTS = {
    "lose": 0,
    "pair": 10,
    "triple": 28,
    "jackpot": 100,
}

DEFAULT_WORKDAYS_MASK = "1111100"  # Mon..Sun
WEEKDAY_LABELS_RU = ["Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"]


class SetupStates(StatesGroup):
    waiting_rate = State()
    waiting_goal = State()
    waiting_gamification_choice = State()
    waiting_manual_time = State()
    waiting_new_rate = State()
    waiting_new_goal = State()
    waiting_market_edit_price = State()
    waiting_silver_per_hour = State()
    waiting_gold_per_hour = State()
    waiting_gold_to_silver_rate = State()
    waiting_bonus_points = State()
    waiting_exchange_gold_amount = State()
    waiting_market_quick_item = State()
    waiting_market_quick_photo = State()
    waiting_bonus_goal_value = State()
    waiting_bonus_goal_custom_deadline = State()
    waiting_bonus_goal_reward = State()
    casino_mode = State()


@dataclass
class Profile:
    user_id: int
    rate_per_hour: float
    goal_amount: float
    notifications_mode: str
    notifications_hour: int
    gamification_enabled: bool
    silver_balance: int
    gold_balance: int
    silver_per_hour: int
    gold_per_hour: int
    gold_to_silver_rate: int


@dataclass
class MarketItem:
    id: int
    user_id: int
    title: str
    cost_points: int
    cost_currency: str
    description: str
    photo_file_id: str
    is_active: bool


@dataclass
class BonusGoal:
    id: int
    user_id: int
    title: str
    target_type: str
    target_value: float
    reward_points: int
    start_at: str
    deadline_at: str
    status: str
    completed_at: str


@dataclass
class HabitState:
    user_id: int
    streak_days: int
    streak_last_counted_date: str
    streak_freezes: int
    league_tier: int
    league_week_start: str
    workdays_mask: str


@dataclass
class StreakChallenge:
    id: int
    user_id: int
    days_target: int
    days_done: int
    wager_points: int
    status: str
    start_date: str
    last_counted_date: str


@contextmanager
def db_conn():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    try:
        yield conn
        conn.commit()
    finally:
        conn.close()


def init_db() -> None:
    with db_conn() as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                rate_per_hour REAL NOT NULL DEFAULT 0,
                goal_amount REAL NOT NULL DEFAULT 0,
                notifications_mode TEXT NOT NULL DEFAULT 'off',
                notifications_hour INTEGER NOT NULL DEFAULT 21,
                gamification_enabled INTEGER NOT NULL DEFAULT 1,
                points_balance INTEGER NOT NULL DEFAULT 0,
                points_per_minute INTEGER NOT NULL DEFAULT 1,
                silver_balance INTEGER NOT NULL DEFAULT 0,
                gold_balance INTEGER NOT NULL DEFAULT 0,
                silver_per_hour INTEGER NOT NULL DEFAULT 60,
                gold_per_hour INTEGER NOT NULL DEFAULT 4,
                gold_to_silver_rate INTEGER NOT NULL DEFAULT 12,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
            """
        )
        columns = {row["name"] for row in conn.execute("PRAGMA table_info(users)").fetchall()}
        if "notifications_mode" not in columns:
            conn.execute("ALTER TABLE users ADD COLUMN notifications_mode TEXT NOT NULL DEFAULT 'off'")
        if "notifications_hour" not in columns:
            conn.execute("ALTER TABLE users ADD COLUMN notifications_hour INTEGER NOT NULL DEFAULT 21")
        if "gamification_enabled" not in columns:
            conn.execute("ALTER TABLE users ADD COLUMN gamification_enabled INTEGER NOT NULL DEFAULT 1")
        if "points_balance" not in columns:
            conn.execute("ALTER TABLE users ADD COLUMN points_balance INTEGER NOT NULL DEFAULT 0")
        if "points_per_minute" not in columns:
            conn.execute("ALTER TABLE users ADD COLUMN points_per_minute INTEGER NOT NULL DEFAULT 1")
        if "silver_balance" not in columns:
            conn.execute("ALTER TABLE users ADD COLUMN silver_balance INTEGER NOT NULL DEFAULT 0")
            conn.execute("UPDATE users SET silver_balance = points_balance")
        if "gold_balance" not in columns:
            conn.execute("ALTER TABLE users ADD COLUMN gold_balance INTEGER NOT NULL DEFAULT 0")
        if "silver_per_hour" not in columns:
            conn.execute("ALTER TABLE users ADD COLUMN silver_per_hour INTEGER NOT NULL DEFAULT 60")
            conn.execute(
                "UPDATE users SET silver_per_hour = CASE WHEN points_per_minute > 0 THEN points_per_minute * 60 ELSE 60 END"
            )
        if "gold_per_hour" not in columns:
            conn.execute("ALTER TABLE users ADD COLUMN gold_per_hour INTEGER NOT NULL DEFAULT 4")
        if "gold_to_silver_rate" not in columns:
            conn.execute("ALTER TABLE users ADD COLUMN gold_to_silver_rate INTEGER NOT NULL DEFAULT 12")
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS work_sessions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                duration_seconds INTEGER NOT NULL,
                source TEXT NOT NULL,
                note TEXT,
                created_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS ui_state (
                user_id INTEGER PRIMARY KEY,
                main_message_id INTEGER,
                updated_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS temp_messages (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                chat_id INTEGER NOT NULL,
                message_id INTEGER NOT NULL,
                created_at TEXT NOT NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS market_items (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                title TEXT NOT NULL,
                cost_points INTEGER NOT NULL,
                cost_currency TEXT NOT NULL DEFAULT 'silver',
                description TEXT NOT NULL DEFAULT '',
                photo_file_id TEXT NOT NULL DEFAULT '',
                is_active INTEGER NOT NULL DEFAULT 1,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            )
            """
        )
        market_item_columns = {row["name"] for row in conn.execute("PRAGMA table_info(market_items)").fetchall()}
        if "cost_currency" not in market_item_columns:
            conn.execute("ALTER TABLE market_items ADD COLUMN cost_currency TEXT NOT NULL DEFAULT 'silver'")
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS point_transactions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                delta_points INTEGER NOT NULL,
                currency TEXT NOT NULL DEFAULT 'silver',
                reason TEXT NOT NULL,
                ref_type TEXT,
                ref_id INTEGER,
                note TEXT,
                created_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            )
            """
        )
        point_columns = {row["name"] for row in conn.execute("PRAGMA table_info(point_transactions)").fetchall()}
        if "currency" not in point_columns:
            conn.execute("ALTER TABLE point_transactions ADD COLUMN currency TEXT NOT NULL DEFAULT 'silver'")
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS market_purchases (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                item_id INTEGER,
                item_title_snapshot TEXT NOT NULL,
                cost_points INTEGER NOT NULL,
                cost_currency TEXT NOT NULL DEFAULT 'silver',
                created_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            )
            """
        )
        market_purchase_columns = {
            row["name"] for row in conn.execute("PRAGMA table_info(market_purchases)").fetchall()
        }
        if "cost_currency" not in market_purchase_columns:
            conn.execute("ALTER TABLE market_purchases ADD COLUMN cost_currency TEXT NOT NULL DEFAULT 'silver'")
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS bonus_goals (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                title TEXT NOT NULL,
                target_type TEXT NOT NULL,
                target_value REAL NOT NULL,
                reward_points INTEGER NOT NULL,
                start_at TEXT NOT NULL,
                deadline_at TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'active',
                completed_at TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS habit_state (
                user_id INTEGER PRIMARY KEY,
                streak_days INTEGER NOT NULL DEFAULT 0,
                streak_last_counted_date TEXT NOT NULL DEFAULT '',
                streak_freezes INTEGER NOT NULL DEFAULT 1,
                league_tier INTEGER NOT NULL DEFAULT 1,
                league_week_start TEXT NOT NULL DEFAULT '',
                workdays_mask TEXT NOT NULL DEFAULT '1111100',
                updated_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            )
            """
        )
        habit_columns = {row["name"] for row in conn.execute("PRAGMA table_info(habit_state)").fetchall()}
        if "workdays_mask" not in habit_columns:
            conn.execute(
                "ALTER TABLE habit_state ADD COLUMN workdays_mask TEXT NOT NULL DEFAULT '1111100'"
            )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS streak_challenges (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                days_target INTEGER NOT NULL,
                days_done INTEGER NOT NULL DEFAULT 0,
                wager_points INTEGER NOT NULL,
                status TEXT NOT NULL DEFAULT 'active',
                start_date TEXT NOT NULL,
                last_counted_date TEXT NOT NULL,
                completed_at TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS discipline_day_overrides (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                target_date TEXT NOT NULL,
                is_workday INTEGER NOT NULL,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                UNIQUE(user_id, target_date),
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            )
            """
        )


def now_iso() -> str:
    return datetime.now(TZ).isoformat()


def now_date() -> datetime.date:
    return datetime.now(TZ).date()


def date_to_iso(value: datetime.date) -> str:
    return value.isoformat()


def iso_to_date(value: str) -> Optional[datetime.date]:
    if not value:
        return None
    try:
        return datetime.fromisoformat(value).date()
    except ValueError:
        return None


def start_of_day(value: datetime.date) -> datetime:
    return datetime.combine(value, datetime.min.time(), TZ)


def end_of_day(value: datetime.date) -> datetime:
    return datetime.combine(value, datetime.max.time(), TZ).replace(microsecond=0)


def week_start_sunday(value: datetime.date) -> datetime.date:
    days_since_sunday = (value.weekday() + 1) % 7
    return value - timedelta(days=days_since_sunday)


def league_name(tier: int) -> str:
    idx = min(max(tier, 1), len(LEAGUE_NAMES)) - 1
    return LEAGUE_NAMES[idx]


def clamp_tier(tier: int) -> int:
    return max(1, min(len(LEAGUE_NAMES), tier))


def normalize_workdays_mask(mask: str) -> str:
    if not mask or len(mask) != 7 or any(ch not in {"0", "1"} for ch in mask):
        return DEFAULT_WORKDAYS_MASK
    if mask == "0000000":
        return DEFAULT_WORKDAYS_MASK
    return mask


def is_regular_workday(mask: str, date_value: datetime.date) -> bool:
    normalized = normalize_workdays_mask(mask)
    return normalized[date_value.weekday()] == "1"


def workdays_mask_label(mask: str) -> str:
    normalized = normalize_workdays_mask(mask)
    labels = [WEEKDAY_LABELS_RU[idx] for idx in range(7) if normalized[idx] == "1"]
    return ", ".join(labels) if labels else "не выбраны"


def get_profile(user_id: int) -> Optional[Profile]:
    with db_conn() as conn:
        row = conn.execute("SELECT * FROM users WHERE user_id = ?", (user_id,)).fetchone()
    if not row:
        return None
    row_keys = set(row.keys())
    return Profile(
        user_id=row["user_id"],
        rate_per_hour=row["rate_per_hour"],
        goal_amount=row["goal_amount"],
        notifications_mode=row["notifications_mode"] if "notifications_mode" in row_keys else "off",
        notifications_hour=row["notifications_hour"] if "notifications_hour" in row_keys else 21,
        gamification_enabled=bool(int(row["gamification_enabled"])) if "gamification_enabled" in row_keys else True,
        silver_balance=(
            int(row["silver_balance"])
            if "silver_balance" in row_keys
            else int(row["points_balance"]) if "points_balance" in row_keys else 0
        ),
        gold_balance=int(row["gold_balance"]) if "gold_balance" in row_keys else 0,
        silver_per_hour=(
            int(row["silver_per_hour"])
            if "silver_per_hour" in row_keys
            else int(row["points_per_minute"]) * 60 if "points_per_minute" in row_keys else 60
        ),
        gold_per_hour=int(row["gold_per_hour"]) if "gold_per_hour" in row_keys else 4,
        gold_to_silver_rate=int(row["gold_to_silver_rate"]) if "gold_to_silver_rate" in row_keys else 12,
    )


def upsert_profile(user_id: int, rate_per_hour: float, goal_amount: float) -> None:
    with db_conn() as conn:
        existing = conn.execute("SELECT user_id FROM users WHERE user_id = ?", (user_id,)).fetchone()
        if existing:
            conn.execute(
                """
                UPDATE users
                SET rate_per_hour = ?, goal_amount = ?, updated_at = ?
                WHERE user_id = ?
                """,
                (rate_per_hour, goal_amount, now_iso(), user_id),
            )
        else:
            conn.execute(
                """
                INSERT INTO users (
                    user_id,
                    rate_per_hour,
                    goal_amount,
                    notifications_mode,
                    notifications_hour,
                    gamification_enabled,
                    points_balance,
                    points_per_minute,
                    silver_balance,
                    gold_balance,
                    silver_per_hour,
                    gold_per_hour,
                    gold_to_silver_rate,
                    created_at,
                    updated_at
                )
                VALUES (?, ?, ?, 'off', 21, 1, 0, 1, 0, 0, 60, 4, 12, ?, ?)
                """,
                (user_id, rate_per_hour, goal_amount, now_iso(), now_iso()),
            )


def update_rate(user_id: int, rate: float) -> None:
    with db_conn() as conn:
        conn.execute(
            "UPDATE users SET rate_per_hour = ?, updated_at = ? WHERE user_id = ?",
            (rate, now_iso(), user_id),
        )


def update_goal(user_id: int, goal: float) -> None:
    with db_conn() as conn:
        conn.execute(
            "UPDATE users SET goal_amount = ?, updated_at = ? WHERE user_id = ?",
            (goal, now_iso(), user_id),
        )


def update_notification_mode(user_id: int, mode: str) -> None:
    with db_conn() as conn:
        conn.execute(
            "UPDATE users SET notifications_mode = ?, updated_at = ? WHERE user_id = ?",
            (mode, now_iso(), user_id),
        )


def update_gamification_enabled(user_id: int, enabled: bool) -> None:
    with db_conn() as conn:
        conn.execute(
            "UPDATE users SET gamification_enabled = ?, updated_at = ? WHERE user_id = ?",
            (1 if enabled else 0, now_iso(), user_id),
        )


def update_silver_per_hour(user_id: int, value: int) -> None:
    with db_conn() as conn:
        conn.execute(
            "UPDATE users SET silver_per_hour = ?, updated_at = ? WHERE user_id = ?",
            (value, now_iso(), user_id),
        )


def update_gold_per_hour(user_id: int, value: int) -> None:
    with db_conn() as conn:
        conn.execute(
            "UPDATE users SET gold_per_hour = ?, updated_at = ? WHERE user_id = ?",
            (value, now_iso(), user_id),
        )


def update_gold_to_silver_rate(user_id: int, value: int) -> None:
    with db_conn() as conn:
        conn.execute(
            "UPDATE users SET gold_to_silver_rate = ?, updated_at = ? WHERE user_id = ?",
            (value, now_iso(), user_id),
        )


def calculate_session_currency(duration_seconds: int, per_hour: int) -> int:
    if duration_seconds <= 0 or per_hour <= 0:
        return 0
    amount = (duration_seconds * per_hour) // 3600
    return max(1, amount)


def normalize_currency(value: str) -> str:
    return "gold" if (value or "").strip().lower() == "gold" else "silver"


def currency_icon(currency: str) -> str:
    return "🥇" if normalize_currency(currency) == "gold" else "🥈"


def currency_name_ru(currency: str) -> str:
    return "золото" if normalize_currency(currency) == "gold" else "серебро"


def profile_balance_by_currency(profile: Profile, currency: str) -> int:
    return profile.gold_balance if normalize_currency(currency) == "gold" else profile.silver_balance


def balance_column(currency: str) -> str:
    normalized = normalize_currency(currency)
    if normalized == "silver":
        return "silver_balance"
    if normalized == "gold":
        return "gold_balance"
    raise ValueError("Unsupported currency")


def apply_currency_transaction(
    user_id: int,
    delta_points: int,
    reason: str,
    currency: str = "silver",
    note: str = "",
    ref_type: str = "",
    ref_id: Optional[int] = None,
    allow_negative: bool = False,
) -> tuple[bool, int]:
    column = balance_column(currency)
    with db_conn() as conn:
        row = conn.execute(
            f"SELECT {column} AS balance FROM users WHERE user_id = ?",
            (user_id,),
        ).fetchone()
        if not row:
            return False, 0

        current_balance = int(row["balance"])
        new_balance = current_balance + delta_points
        if not allow_negative and new_balance < 0:
            return False, current_balance

        conn.execute(
            f"UPDATE users SET {column} = ?, updated_at = ? WHERE user_id = ?",
            (new_balance, now_iso(), user_id),
        )
        conn.execute(
            """
            INSERT INTO point_transactions (user_id, delta_points, currency, reason, ref_type, ref_id, note, created_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (user_id, delta_points, currency, reason, ref_type, ref_id, note, now_iso()),
        )
        return True, new_balance


def apply_points_transaction(
    user_id: int,
    delta_points: int,
    reason: str,
    note: str = "",
    ref_type: str = "",
    ref_id: Optional[int] = None,
    allow_negative: bool = False,
) -> tuple[bool, int]:
    return apply_currency_transaction(
        user_id=user_id,
        delta_points=delta_points,
        reason=reason,
        currency="silver",
        note=note,
        ref_type=ref_type,
        ref_id=ref_id,
        allow_negative=allow_negative,
    )


def award_currencies_for_session(
    user_id: int,
    duration_seconds: int,
    source: str,
    session_id: int,
) -> tuple[int, int]:
    with db_conn() as conn:
        row = conn.execute(
            """
            SELECT silver_balance, gold_balance, silver_per_hour, gold_per_hour
            FROM users
            WHERE user_id = ?
            """,
            (user_id,),
        ).fetchone()
        if not row:
            return 0, 0

        silver = calculate_session_currency(duration_seconds, int(row["silver_per_hour"]))
        gold = calculate_session_currency(duration_seconds, int(row["gold_per_hour"]))
        if silver <= 0 and gold <= 0:
            return 0, 0

        new_silver = int(row["silver_balance"]) + silver
        new_gold = int(row["gold_balance"]) + gold
        conn.execute(
            "UPDATE users SET silver_balance = ?, gold_balance = ?, updated_at = ? WHERE user_id = ?",
            (new_silver, new_gold, now_iso(), user_id),
        )
        if silver > 0:
            conn.execute(
                """
                INSERT INTO point_transactions (user_id, delta_points, currency, reason, ref_type, ref_id, note, created_at)
                VALUES (?, ?, 'silver', 'work_session', 'work_session', ?, ?, ?)
                """,
                (user_id, silver, session_id, source, now_iso()),
            )
        if gold > 0:
            conn.execute(
                """
                INSERT INTO point_transactions (user_id, delta_points, currency, reason, ref_type, ref_id, note, created_at)
                VALUES (?, ?, 'gold', 'work_session', 'work_session', ?, ?, ?)
                """,
                (user_id, gold, session_id, source, now_iso()),
            )
        return silver, gold


def add_session(user_id: int, duration_seconds: int, source: str, note: str = "") -> int:
    with db_conn() as conn:
        cur = conn.execute(
            """
            INSERT INTO work_sessions (user_id, duration_seconds, source, note, created_at)
            VALUES (?, ?, ?, ?, ?)
            """,
            (user_id, duration_seconds, source, note, now_iso()),
        )
    return int(cur.lastrowid)


def total_seconds(user_id: int) -> int:
    with db_conn() as conn:
        row = conn.execute(
            "SELECT COALESCE(SUM(duration_seconds), 0) AS total FROM work_sessions WHERE user_id = ?",
            (user_id,),
        ).fetchone()
    return int(row["total"])


def period_seconds(user_id: int, since: datetime) -> int:
    with db_conn() as conn:
        row = conn.execute(
            """
            SELECT COALESCE(SUM(duration_seconds), 0) AS total
            FROM work_sessions
            WHERE user_id = ? AND created_at >= ?
            """,
            (user_id, since.isoformat()),
        ).fetchone()
    return int(row["total"])


def range_seconds(user_id: int, start: datetime, end: datetime) -> int:
    if end <= start:
        return 0
    with db_conn() as conn:
        row = conn.execute(
            """
            SELECT COALESCE(SUM(duration_seconds), 0) AS total
            FROM work_sessions
            WHERE user_id = ? AND created_at >= ? AND created_at <= ?
            """,
            (user_id, start.isoformat(), end.isoformat()),
        ).fetchone()
    return int(row["total"])


def daily_stats(user_id: int, days: int = 14):
    since = (datetime.now(TZ) - timedelta(days=days - 1)).replace(hour=0, minute=0, second=0, microsecond=0)
    with db_conn() as conn:
        rows = conn.execute(
            """
            SELECT duration_seconds, created_at
            FROM work_sessions
            WHERE user_id = ? AND created_at >= ?
            ORDER BY created_at ASC
            """,
            (user_id, since.isoformat()),
        ).fetchall()

    by_day = {}
    for i in range(days):
        d = (since + timedelta(days=i)).date().isoformat()
        by_day[d] = 0

    for r in rows:
        dt = datetime.fromisoformat(r["created_at"]).astimezone(TZ).date().isoformat()
        if dt in by_day:
            by_day[dt] += int(r["duration_seconds"])

    labels = []
    seconds = []
    for d, sec in by_day.items():
        labels.append(datetime.fromisoformat(d).strftime("%d.%m"))
        seconds.append(sec)
    return labels, seconds


def recent_history(user_id: int, limit: int = 20):
    with db_conn() as conn:
        rows = conn.execute(
            """
            SELECT duration_seconds, source, note, created_at
            FROM work_sessions
            WHERE user_id = ?
            ORDER BY id DESC
            LIMIT ?
            """,
            (user_id, limit),
        ).fetchall()
    return rows


def create_market_item(
    user_id: int,
    title: str,
    cost_points: int,
    cost_currency: str = "silver",
    description: str = "",
    photo_file_id: str = "",
) -> int:
    normalized_currency = normalize_currency(cost_currency)
    with db_conn() as conn:
        cur = conn.execute(
            """
            INSERT INTO market_items (
                user_id,
                title,
                cost_points,
                cost_currency,
                description,
                photo_file_id,
                is_active,
                created_at,
                updated_at
            )
            VALUES (?, ?, ?, ?, ?, ?, 1, ?, ?)
            """,
            (
                user_id,
                title,
                cost_points,
                normalized_currency,
                description,
                photo_file_id,
                now_iso(),
                now_iso(),
            ),
        )
    return int(cur.lastrowid)


def row_to_market_item(row: sqlite3.Row) -> MarketItem:
    row_keys = set(row.keys())
    return MarketItem(
        id=int(row["id"]),
        user_id=int(row["user_id"]),
        title=row["title"],
        cost_points=int(row["cost_points"]),
        cost_currency=normalize_currency(row["cost_currency"]) if "cost_currency" in row_keys else "silver",
        description=row["description"] or "",
        photo_file_id=row["photo_file_id"] or "",
        is_active=bool(row["is_active"]),
    )


def get_market_item(user_id: int, item_id: int, active_only: bool = False) -> Optional[MarketItem]:
    query = "SELECT * FROM market_items WHERE user_id = ? AND id = ?"
    params: list[object] = [user_id, item_id]
    if active_only:
        query += " AND is_active = 1"
    with db_conn() as conn:
        row = conn.execute(query, params).fetchone()
    if not row:
        return None
    return row_to_market_item(row)


def list_market_items(user_id: int, active_only: bool = True, limit: int = 50) -> list[MarketItem]:
    query = "SELECT * FROM market_items WHERE user_id = ?"
    params: list[object] = [user_id]
    if active_only:
        query += " AND is_active = 1"
    query += " ORDER BY id DESC LIMIT ?"
    params.append(limit)
    with db_conn() as conn:
        rows = conn.execute(query, params).fetchall()
    return [row_to_market_item(row) for row in rows]


def count_market_items(user_id: int) -> tuple[int, int]:
    with db_conn() as conn:
        total_row = conn.execute(
            "SELECT COUNT(*) AS count FROM market_items WHERE user_id = ?",
            (user_id,),
        ).fetchone()
        active_row = conn.execute(
            "SELECT COUNT(*) AS count FROM market_items WHERE user_id = ? AND is_active = 1",
            (user_id,),
        ).fetchone()
    return int(active_row["count"]), int(total_row["count"])


def update_market_item_price(user_id: int, item_id: int, new_price: int) -> bool:
    with db_conn() as conn:
        cur = conn.execute(
            """
            UPDATE market_items
            SET cost_points = ?, updated_at = ?
            WHERE user_id = ? AND id = ?
            """,
            (new_price, now_iso(), user_id, item_id),
        )
    return cur.rowcount > 0


def update_market_item_currency(user_id: int, item_id: int, new_currency: str) -> bool:
    currency = normalize_currency(new_currency)
    with db_conn() as conn:
        cur = conn.execute(
            """
            UPDATE market_items
            SET cost_currency = ?, updated_at = ?
            WHERE user_id = ? AND id = ?
            """,
            (currency, now_iso(), user_id, item_id),
        )
    return cur.rowcount > 0


def toggle_market_item(user_id: int, item_id: int) -> Optional[bool]:
    with db_conn() as conn:
        row = conn.execute(
            "SELECT is_active FROM market_items WHERE user_id = ? AND id = ?",
            (user_id, item_id),
        ).fetchone()
        if not row:
            return None
        new_state = 0 if int(row["is_active"]) else 1
        conn.execute(
            "UPDATE market_items SET is_active = ?, updated_at = ? WHERE user_id = ? AND id = ?",
            (new_state, now_iso(), user_id, item_id),
        )
    return bool(new_state)


def delete_market_item(user_id: int, item_id: int) -> bool:
    with db_conn() as conn:
        cur = conn.execute(
            "DELETE FROM market_items WHERE user_id = ? AND id = ?",
            (user_id, item_id),
        )
    return cur.rowcount > 0


def buy_market_item(user_id: int, item_id: int) -> tuple[bool, str, int, str]:
    with db_conn() as conn:
        item_row = conn.execute(
            """
            SELECT id, title, cost_points, cost_currency, is_active
            FROM market_items
            WHERE user_id = ? AND id = ?
            """,
            (user_id, item_id),
        ).fetchone()
        if not item_row or int(item_row["is_active"]) != 1:
            return False, "Позиция недоступна", 0, "silver"

        profile_row = conn.execute(
            "SELECT silver_balance, gold_balance FROM users WHERE user_id = ?",
            (user_id,),
        ).fetchone()
        if not profile_row:
            return False, "Профиль не найден", 0, "silver"

        cost = int(item_row["cost_points"])
        currency = normalize_currency(item_row["cost_currency"])
        balance_col = balance_column(currency)
        current_balance = int(profile_row[balance_col])
        if current_balance < cost:
            return False, f"Недостаточно {currency_name_ru(currency)}", current_balance, currency

        new_balance = current_balance - cost
        conn.execute(
            f"UPDATE users SET {balance_col} = ?, updated_at = ? WHERE user_id = ?",
            (new_balance, now_iso(), user_id),
        )
        conn.execute(
            """
            INSERT INTO point_transactions (user_id, delta_points, currency, reason, ref_type, ref_id, note, created_at)
            VALUES (?, ?, ?, 'market_purchase', 'market_item', ?, ?, ?)
            """,
            (user_id, -cost, currency, int(item_row["id"]), item_row["title"], now_iso()),
        )
        conn.execute(
            """
            INSERT INTO market_purchases (user_id, item_id, item_title_snapshot, cost_points, cost_currency, created_at)
            VALUES (?, ?, ?, ?, ?, ?)
            """,
            (user_id, int(item_row["id"]), item_row["title"], cost, currency, now_iso()),
        )
    return True, item_row["title"], new_balance, currency


def recent_market_purchases(user_id: int, limit: int = 20):
    with db_conn() as conn:
        rows = conn.execute(
            """
            SELECT item_title_snapshot, cost_points, cost_currency, created_at
            FROM market_purchases
            WHERE user_id = ?
            ORDER BY id DESC
            LIMIT ?
            """,
            (user_id, limit),
        ).fetchall()
    return rows


def recent_points_activity(user_id: int, limit: int = 20):
    with db_conn() as conn:
        rows = conn.execute(
            """
            SELECT delta_points, currency, reason, note, created_at
            FROM point_transactions
            WHERE user_id = ?
            ORDER BY id DESC
            LIMIT ?
            """,
            (user_id, limit),
        ).fetchall()
    return rows


def exchange_gold_to_silver(user_id: int, gold_amount: int) -> tuple[bool, str, int, int]:
    if gold_amount <= 0:
        return False, "Количество золота должно быть больше 0.", 0, 0

    with db_conn() as conn:
        row = conn.execute(
            """
            SELECT gold_balance, silver_balance, gold_to_silver_rate
            FROM users
            WHERE user_id = ?
            """,
            (user_id,),
        ).fetchone()
        if not row:
            return False, "Профиль не найден.", 0, 0

        current_gold = int(row["gold_balance"])
        current_silver = int(row["silver_balance"])
        rate = max(1, int(row["gold_to_silver_rate"]))
        if current_gold < gold_amount:
            return False, "Недостаточно золота.", current_gold, current_silver

        silver_gain = gold_amount * rate
        new_gold = current_gold - gold_amount
        new_silver = current_silver + silver_gain

        conn.execute(
            "UPDATE users SET gold_balance = ?, silver_balance = ?, updated_at = ? WHERE user_id = ?",
            (new_gold, new_silver, now_iso(), user_id),
        )
        conn.execute(
            """
            INSERT INTO point_transactions (user_id, delta_points, currency, reason, ref_type, ref_id, note, created_at)
            VALUES (?, ?, 'gold', 'exchange_gold_to_silver', 'exchange', NULL, ?, ?)
            """,
            (user_id, -gold_amount, f"обмен по курсу {rate}", now_iso()),
        )
        conn.execute(
            """
            INSERT INTO point_transactions (user_id, delta_points, currency, reason, ref_type, ref_id, note, created_at)
            VALUES (?, ?, 'silver', 'exchange_gold_to_silver', 'exchange', NULL, ?, ?)
            """,
            (user_id, silver_gain, f"обмен по курсу {rate}", now_iso()),
        )
    return True, f"Обменено: {gold_amount} 🥇 -> {silver_gain} 🥈", new_gold, new_silver


def update_market_item_photo(user_id: int, item_id: int, photo_file_id: str) -> bool:
    with db_conn() as conn:
        cur = conn.execute(
            """
            UPDATE market_items
            SET photo_file_id = ?, updated_at = ?
            WHERE user_id = ? AND id = ?
            """,
            (photo_file_id, now_iso(), user_id, item_id),
        )
    return cur.rowcount > 0


def row_to_bonus_goal(row: sqlite3.Row) -> BonusGoal:
    return BonusGoal(
        id=int(row["id"]),
        user_id=int(row["user_id"]),
        title=row["title"],
        target_type=row["target_type"],
        target_value=float(row["target_value"]),
        reward_points=int(row["reward_points"]),
        start_at=row["start_at"],
        deadline_at=row["deadline_at"],
        status=row["status"],
        completed_at=row["completed_at"] or "",
    )


def create_bonus_goal(
    user_id: int,
    title: str,
    target_type: str,
    target_value: float,
    reward_points: int,
    deadline_at: datetime,
    start_at: Optional[datetime] = None,
) -> int:
    effective_start = start_at or datetime.now(TZ)
    with db_conn() as conn:
        cur = conn.execute(
            """
            INSERT INTO bonus_goals (
                user_id,
                title,
                target_type,
                target_value,
                reward_points,
                start_at,
                deadline_at,
                status,
                completed_at,
                created_at,
                updated_at
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, 'active', '', ?, ?)
            """,
            (
                user_id,
                title,
                target_type,
                target_value,
                reward_points,
                effective_start.isoformat(),
                deadline_at.isoformat(),
                now_iso(),
                now_iso(),
            ),
        )
    return int(cur.lastrowid)


def get_bonus_goal(user_id: int, goal_id: int) -> Optional[BonusGoal]:
    with db_conn() as conn:
        row = conn.execute(
            "SELECT * FROM bonus_goals WHERE user_id = ? AND id = ?",
            (user_id, goal_id),
        ).fetchone()
    if not row:
        return None
    return row_to_bonus_goal(row)


def list_bonus_goals(user_id: int, statuses: tuple[str, ...], limit: int = 50) -> list[BonusGoal]:
    placeholders = ",".join(["?"] * len(statuses))
    with db_conn() as conn:
        rows = conn.execute(
            f"""
            SELECT *
            FROM bonus_goals
            WHERE user_id = ? AND status IN ({placeholders})
            ORDER BY deadline_at ASC, id DESC
            LIMIT ?
            """,
            (user_id, *statuses, limit),
        ).fetchall()
    return [row_to_bonus_goal(row) for row in rows]


def count_bonus_goals(user_id: int) -> tuple[int, int, int]:
    with db_conn() as conn:
        active = conn.execute(
            "SELECT COUNT(*) AS count FROM bonus_goals WHERE user_id = ? AND status = 'active'",
            (user_id,),
        ).fetchone()
        completed = conn.execute(
            "SELECT COUNT(*) AS count FROM bonus_goals WHERE user_id = ? AND status = 'completed'",
            (user_id,),
        ).fetchone()
        expired = conn.execute(
            "SELECT COUNT(*) AS count FROM bonus_goals WHERE user_id = ? AND status = 'expired'",
            (user_id,),
        ).fetchone()
    return int(active["count"]), int(completed["count"]), int(expired["count"])


def delete_bonus_goal(user_id: int, goal_id: int) -> bool:
    with db_conn() as conn:
        cur = conn.execute(
            "DELETE FROM bonus_goals WHERE user_id = ? AND id = ?",
            (user_id, goal_id),
        )
    return cur.rowcount > 0


def parse_iso_dt(value: str) -> datetime:
    return datetime.fromisoformat(value).astimezone(TZ)


def end_of_today(now: datetime) -> datetime:
    return now.replace(hour=23, minute=59, second=59, microsecond=0)


def deadline_this_friday(now: datetime) -> datetime:
    days_to_friday = (4 - now.weekday()) % 7
    deadline = (now + timedelta(days=days_to_friday)).replace(hour=23, minute=59, second=59, microsecond=0)
    if deadline <= now:
        deadline += timedelta(days=7)
    return deadline


def deadline_end_of_month(now: datetime) -> datetime:
    if now.month == 12:
        first_next = now.replace(year=now.year + 1, month=1, day=1, hour=23, minute=59, second=59, microsecond=0)
    else:
        first_next = now.replace(month=now.month + 1, day=1, hour=23, minute=59, second=59, microsecond=0)
    return first_next - timedelta(days=1)


def parse_custom_deadline(text: str, now: Optional[datetime] = None) -> Optional[datetime]:
    reference = now or datetime.now(TZ)
    cleaned = (text or "").strip()
    match = re.match(r"^(\d{1,2})\.(\d{1,2})(?:\.(\d{4}))?(?:\s+(\d{1,2}):(\d{2}))?$", cleaned)
    if not match:
        return None

    day = int(match.group(1))
    month = int(match.group(2))
    year = int(match.group(3)) if match.group(3) else reference.year
    hour = int(match.group(4)) if match.group(4) is not None else 23
    minute = int(match.group(5)) if match.group(5) is not None else 59

    try:
        deadline = datetime(year, month, day, hour, minute, 0, tzinfo=TZ)
    except ValueError:
        return None

    if deadline <= reference:
        return None
    return deadline


def bonus_goal_progress(goal: BonusGoal, profile: Profile, at_time: Optional[datetime] = None) -> float:
    now = at_time or datetime.now(TZ)
    start = parse_iso_dt(goal.start_at)
    deadline = parse_iso_dt(goal.deadline_at)
    period_end = min(now, deadline)
    worked_seconds = range_seconds(goal.user_id, start, period_end)
    if goal.target_type == "money":
        return (worked_seconds / 3600) * profile.rate_per_hour
    return worked_seconds / 3600


def evaluate_bonus_goals(user_id: int) -> list[str]:
    profile = get_profile(user_id)
    if not profile:
        return []

    now = datetime.now(TZ)
    events: list[str] = []
    active_goals = list_bonus_goals(user_id, statuses=("active",), limit=100)
    if not active_goals:
        return events

    with db_conn() as conn:
        for goal in active_goals:
            deadline = parse_iso_dt(goal.deadline_at)
            progress = bonus_goal_progress(goal, profile, at_time=now)
            is_completed = progress >= goal.target_value

            if is_completed and now <= deadline:
                updated = conn.execute(
                    """
                    UPDATE bonus_goals
                    SET status = 'completed', completed_at = ?, updated_at = ?
                    WHERE id = ? AND user_id = ? AND status = 'active'
                    """,
                    (now.isoformat(), now_iso(), goal.id, user_id),
                )
                if updated.rowcount > 0:
                    user_row = conn.execute(
                        "SELECT silver_balance FROM users WHERE user_id = ?",
                        (user_id,),
                    ).fetchone()
                    if user_row:
                        new_balance = int(user_row["silver_balance"]) + goal.reward_points
                        conn.execute(
                            "UPDATE users SET silver_balance = ?, updated_at = ? WHERE user_id = ?",
                            (new_balance, now_iso(), user_id),
                        )
                        conn.execute(
                            """
                            INSERT INTO point_transactions (user_id, delta_points, currency, reason, ref_type, ref_id, note, created_at)
                            VALUES (?, ?, 'silver', 'bonus_goal_reward', 'bonus_goal', ?, ?, ?)
                            """,
                            (user_id, goal.reward_points, goal.id, goal.title, now_iso()),
                        )
                        events.append(
                            f"🏆 <b>Бонус выполнен:</b> {html.escape(goal.title)}\n"
                            f"🥈 Награда: +{goal.reward_points}"
                        )
                continue

            if now > deadline:
                updated = conn.execute(
                    """
                    UPDATE bonus_goals
                    SET status = 'expired', updated_at = ?
                    WHERE id = ? AND user_id = ? AND status = 'active'
                    """,
                    (now_iso(), goal.id, user_id),
                )
                if updated.rowcount > 0:
                    events.append(f"⌛ <b>Бонус истёк:</b> {html.escape(goal.title)}")

    return events


def row_to_habit_state(row: sqlite3.Row) -> HabitState:
    row_keys = set(row.keys())
    return HabitState(
        user_id=int(row["user_id"]),
        streak_days=int(row["streak_days"]),
        streak_last_counted_date=row["streak_last_counted_date"] or "",
        streak_freezes=int(row["streak_freezes"]),
        league_tier=clamp_tier(int(row["league_tier"])),
        league_week_start=row["league_week_start"] or "",
        workdays_mask=normalize_workdays_mask(row["workdays_mask"] if "workdays_mask" in row_keys else DEFAULT_WORKDAYS_MASK),
    )


def ensure_habit_state(user_id: int) -> None:
    with db_conn() as conn:
        row = conn.execute("SELECT user_id FROM habit_state WHERE user_id = ?", (user_id,)).fetchone()
        if row:
            return
        conn.execute(
            """
            INSERT INTO habit_state (
                user_id,
                streak_days,
                streak_last_counted_date,
                streak_freezes,
                league_tier,
                league_week_start,
                workdays_mask,
                updated_at
            )
            VALUES (?, 0, '', 1, 1, ?, ?, ?)
            """,
            (
                user_id,
                date_to_iso(week_start_sunday(now_date())),
                DEFAULT_WORKDAYS_MASK,
                now_iso(),
            ),
        )


def get_habit_state(user_id: int) -> HabitState:
    ensure_habit_state(user_id)
    with db_conn() as conn:
        row = conn.execute("SELECT * FROM habit_state WHERE user_id = ?", (user_id,)).fetchone()
    return row_to_habit_state(row)


def save_habit_state(state: HabitState) -> None:
    mask = normalize_workdays_mask(state.workdays_mask)
    state.workdays_mask = mask
    with db_conn() as conn:
        conn.execute(
            """
            UPDATE habit_state
            SET streak_days = ?,
                streak_last_counted_date = ?,
                streak_freezes = ?,
                league_tier = ?,
                league_week_start = ?,
                workdays_mask = ?,
                updated_at = ?
            WHERE user_id = ?
            """,
            (
                max(0, state.streak_days),
                state.streak_last_counted_date,
                max(0, min(MAX_STREAK_FREEZES, state.streak_freezes)),
                clamp_tier(state.league_tier),
                state.league_week_start,
                mask,
                now_iso(),
                state.user_id,
            ),
        )


def get_day_override(user_id: int, target_date: datetime.date) -> Optional[bool]:
    with db_conn() as conn:
        row = conn.execute(
            """
            SELECT is_workday
            FROM discipline_day_overrides
            WHERE user_id = ? AND target_date = ?
            """,
            (user_id, date_to_iso(target_date)),
        ).fetchone()
    if not row:
        return None
    return bool(int(row["is_workday"]))


def set_day_override(user_id: int, target_date: datetime.date, is_workday: Optional[bool]) -> None:
    date_iso = date_to_iso(target_date)
    with db_conn() as conn:
        if is_workday is None:
            conn.execute(
                "DELETE FROM discipline_day_overrides WHERE user_id = ? AND target_date = ?",
                (user_id, date_iso),
            )
            return
        conn.execute(
            """
            INSERT INTO discipline_day_overrides (user_id, target_date, is_workday, created_at, updated_at)
            VALUES (?, ?, ?, ?, ?)
            ON CONFLICT(user_id, target_date)
            DO UPDATE SET is_workday = excluded.is_workday, updated_at = excluded.updated_at
            """,
            (user_id, date_iso, 1 if is_workday else 0, now_iso(), now_iso()),
        )


def list_day_overrides(user_id: int, from_date: datetime.date, limit: int = 20):
    with db_conn() as conn:
        rows = conn.execute(
            """
            SELECT target_date, is_workday
            FROM discipline_day_overrides
            WHERE user_id = ? AND target_date >= ?
            ORDER BY target_date ASC
            LIMIT ?
            """,
            (user_id, date_to_iso(from_date), limit),
        ).fetchall()
    return rows


def is_effective_workday(user_id: int, target_date: datetime.date, state: Optional[HabitState] = None) -> bool:
    habit = state or get_habit_state(user_id)
    override = get_day_override(user_id, target_date)
    if override is not None:
        return override
    return is_regular_workday(habit.workdays_mask, target_date)


def required_workdays_between(
    user_id: int,
    start_date: datetime.date,
    end_date: datetime.date,
    state: Optional[HabitState] = None,
) -> list[datetime.date]:
    if end_date < start_date:
        return []
    habit = state or get_habit_state(user_id)
    days: list[datetime.date] = []
    cursor = start_date
    while cursor <= end_date:
        if is_effective_workday(user_id, cursor, habit):
            days.append(cursor)
        cursor += timedelta(days=1)
    return days


def toggle_regular_weekday(user_id: int, weekday_idx: int) -> HabitState:
    state = get_habit_state(user_id)
    if weekday_idx < 0 or weekday_idx > 6:
        return state
    mask_list = list(normalize_workdays_mask(state.workdays_mask))
    mask_list[weekday_idx] = "0" if mask_list[weekday_idx] == "1" else "1"
    new_mask = normalize_workdays_mask("".join(mask_list))
    state.workdays_mask = new_mask
    save_habit_state(state)
    return get_habit_state(user_id)


def toggle_day_effective_status(user_id: int, target_date: datetime.date) -> bool:
    state = get_habit_state(user_id)
    regular = is_regular_workday(state.workdays_mask, target_date)
    effective = is_effective_workday(user_id, target_date, state)
    new_effective = not effective
    if new_effective == regular:
        set_day_override(user_id, target_date, None)
    else:
        set_day_override(user_id, target_date, new_effective)
    return new_effective


def row_to_streak_challenge(row: sqlite3.Row) -> StreakChallenge:
    return StreakChallenge(
        id=int(row["id"]),
        user_id=int(row["user_id"]),
        days_target=int(row["days_target"]),
        days_done=int(row["days_done"]),
        wager_points=int(row["wager_points"]),
        status=row["status"],
        start_date=row["start_date"],
        last_counted_date=row["last_counted_date"],
    )


def get_active_streak_challenge(user_id: int) -> Optional[StreakChallenge]:
    with db_conn() as conn:
        row = conn.execute(
            """
            SELECT *
            FROM streak_challenges
            WHERE user_id = ? AND status = 'active'
            ORDER BY id DESC
            LIMIT 1
            """,
            (user_id,),
        ).fetchone()
    if not row:
        return None
    return row_to_streak_challenge(row)


def get_streak_challenge(user_id: int, challenge_id: int) -> Optional[StreakChallenge]:
    with db_conn() as conn:
        row = conn.execute(
            "SELECT * FROM streak_challenges WHERE user_id = ? AND id = ?",
            (user_id, challenge_id),
        ).fetchone()
    if not row:
        return None
    return row_to_streak_challenge(row)


def fail_streak_challenge(user_id: int, challenge_id: int) -> bool:
    with db_conn() as conn:
        cur = conn.execute(
            """
            UPDATE streak_challenges
            SET status = 'failed', completed_at = ?, updated_at = ?
            WHERE user_id = ? AND id = ? AND status = 'active'
            """,
            (now_iso(), now_iso(), user_id, challenge_id),
        )
    return cur.rowcount > 0


def complete_streak_challenge(user_id: int, challenge_id: int, payout_points: int) -> bool:
    with db_conn() as conn:
        cur = conn.execute(
            """
            UPDATE streak_challenges
            SET status = 'completed', completed_at = ?, updated_at = ?
            WHERE user_id = ? AND id = ? AND status = 'active'
            """,
            (now_iso(), now_iso(), user_id, challenge_id),
        )
    if cur.rowcount <= 0:
        return False
    apply_points_transaction(
        user_id,
        payout_points,
        reason="streak_challenge_reward",
        ref_type="streak_challenge",
        ref_id=challenge_id,
        note="награда за дисциплину",
    )
    return True


def challenge_payout(wager_points: int) -> int:
    # Ставка возвращается с бонусом: нетто +50% к риску.
    return int(round(wager_points * 1.5))


def has_activity_on_date(user_id: int, date_value: datetime.date) -> bool:
    return range_seconds(user_id, start_of_day(date_value), end_of_day(date_value)) > 0


def create_streak_challenge(user_id: int, days_target: int, wager_points: int) -> tuple[bool, str]:
    if days_target not in STREAK_CHALLENGE_OPTIONS or STREAK_CHALLENGE_OPTIONS[days_target] != wager_points:
        return False, "Некорректные параметры челленджа"
    if get_active_streak_challenge(user_id):
        return False, "У тебя уже есть активный Streak Challenge"

    ok, _ = apply_points_transaction(
        user_id,
        -wager_points,
        reason="streak_challenge_wager",
        note=f"ставка за {days_target} дней",
        allow_negative=False,
    )
    if not ok:
        return False, "Недостаточно серебра для ставки"

    state = get_habit_state(user_id)
    today = now_date()
    workday_today = is_effective_workday(user_id, today, state)
    had_activity_today = workday_today and has_activity_on_date(user_id, today)
    days_done = 1 if had_activity_today else 0
    if workday_today:
        last_counted_date = today if had_activity_today else (today - timedelta(days=1))
    else:
        last_counted_date = today
    with db_conn() as conn:
        conn.execute(
            """
            INSERT INTO streak_challenges (
                user_id,
                days_target,
                days_done,
                wager_points,
                status,
                start_date,
                last_counted_date,
                created_at,
                updated_at
            )
            VALUES (?, ?, ?, ?, 'active', ?, ?, ?, ?)
            """,
            (
                user_id,
                days_target,
                days_done,
                wager_points,
                date_to_iso(today),
                date_to_iso(last_counted_date),
                now_iso(),
                now_iso(),
            ),
        )
    if had_activity_today:
        return True, "Челлендж начат. Сегодня уже засчитан как 1 рабочий день."
    if workday_today:
        return True, "Челлендж начат. Сегодня рабочий день: добавь запись сегодня, чтобы зачесть день 1."
    return True, "Челлендж начат. Сегодня нерабочий день, отсчёт пойдёт с ближайшего рабочего."


def deduct_points_up_to(
    user_id: int,
    desired_points: int,
    reason: str,
    note: str = "",
    ref_type: str = "",
    ref_id: Optional[int] = None,
) -> int:
    if desired_points <= 0:
        return 0
    with db_conn() as conn:
        row = conn.execute("SELECT silver_balance FROM users WHERE user_id = ?", (user_id,)).fetchone()
        if not row:
            return 0
        balance = int(row["silver_balance"])
        deducted = min(balance, desired_points)
        if deducted <= 0:
            return 0
        conn.execute(
            "UPDATE users SET silver_balance = ?, updated_at = ? WHERE user_id = ?",
            (balance - deducted, now_iso(), user_id),
        )
        conn.execute(
            """
            INSERT INTO point_transactions (user_id, delta_points, currency, reason, ref_type, ref_id, note, created_at)
            VALUES (?, ?, 'silver', ?, ?, ?, ?, ?)
            """,
            (user_id, -deducted, reason, ref_type, ref_id, note, now_iso()),
        )
    return deducted


def evaluate_league_rollover(user_id: int, state: HabitState) -> list[str]:
    events: list[str] = []
    today = now_date()
    current_week = week_start_sunday(today)
    stored_week = iso_to_date(state.league_week_start)
    if not stored_week:
        state.league_week_start = date_to_iso(current_week)
        save_habit_state(state)
        return events
    if stored_week >= current_week:
        return events

    tier = clamp_tier(state.league_tier)
    while stored_week < current_week:
        week_start = stored_week
        week_end = week_start + timedelta(days=6)
        minutes = range_seconds(user_id, start_of_day(week_start), end_of_day(week_end)) // 60
        tier_before = tier
        promo_threshold = LEAGUE_PROMOTION_MINUTES[tier]
        safe_threshold = LEAGUE_SAFE_MINUTES[tier]

        if tier < len(LEAGUE_NAMES) and minutes >= promo_threshold:
            tier += 1
            reward = LEAGUE_PROMOTION_REWARD[tier]
            if reward > 0:
                apply_points_transaction(
                    user_id,
                    reward,
                    reason="league_promotion",
                    note=f"{minutes} мин за неделю",
                    ref_type="league_week",
                    ref_id=int(week_start.strftime("%Y%m%d")),
                )
            events.append(
                f"🏟 <b>Лига повышена:</b> {league_name(tier_before)} → {league_name(tier)}\n"
                f"Неделя: {minutes} мин. Награда: +{reward} 🥈"
            )
        elif tier > 1 and minutes < safe_threshold:
            tier -= 1
            penalty = LEAGUE_DEMOTION_PENALTY[tier_before]
            deducted = deduct_points_up_to(
                user_id,
                penalty,
                reason="league_demotion",
                note=f"{minutes} мин за неделю",
                ref_type="league_week",
                ref_id=int(week_start.strftime("%Y%m%d")),
            )
            events.append(
                f"⬇️ <b>Лига понижена:</b> {league_name(tier_before)} → {league_name(tier)}\n"
                f"Неделя: {minutes} мин. Штраф: -{deducted} 🥈"
            )

        stored_week += timedelta(days=7)

    state.league_tier = tier
    state.league_week_start = date_to_iso(current_week)
    save_habit_state(state)
    return events


def evaluate_discipline(user_id: int) -> list[str]:
    ensure_habit_state(user_id)
    state = get_habit_state(user_id)
    events = evaluate_league_rollover(user_id, state)
    state = get_habit_state(user_id)

    today = now_date()
    challenge = get_active_streak_challenge(user_id)
    if challenge:
        last_ch_date = iso_to_date(challenge.last_counted_date) or (today - timedelta(days=1))
        missed_for_challenge = required_workdays_between(
            user_id,
            last_ch_date + timedelta(days=1),
            today - timedelta(days=1),
            state,
        )
        if missed_for_challenge:
            if fail_streak_challenge(user_id, challenge.id):
                events.append(
                    f"💥 <b>Streak Challenge провален</b>: пропуск рабочего дня.\n"
                    f"Ставка {challenge.wager_points} 🥈 сгорела."
                )
            challenge = None

    last_counted = iso_to_date(state.streak_last_counted_date)
    if not last_counted:
        return events

    missed_workdays = required_workdays_between(
        user_id,
        last_counted + timedelta(days=1),
        today - timedelta(days=1),
        state,
    )
    state_changed = False
    for missed_date in missed_workdays:
        strict_active = challenge is not None

        if strict_active and state.streak_days > 0:
            state.streak_days = 0
            state.streak_last_counted_date = date_to_iso(missed_date)
            events.append("🔥 <b>Стрик сорван</b>: во время Streak Challenge пропуск рабочего дня без freeze.")
            state_changed = True
            break

        if state.streak_days > 0 and state.streak_freezes > 0:
            state.streak_freezes -= 1
            state.streak_last_counted_date = date_to_iso(missed_date)
            state_changed = True
            events.append(
                f"🧊 Использован <b>Streak Freeze</b> за {missed_date.strftime('%d.%m')}. "
                f"Осталось: {state.streak_freezes}/{MAX_STREAK_FREEZES}"
            )
            continue

        if state.streak_days > 0:
            state.streak_days = 0
            state.streak_last_counted_date = date_to_iso(missed_date)
            events.append("🔥 <b>Стрик сорван</b>: не было Streak Freeze на рабочий день.")
            state_changed = True
            break

        state.streak_last_counted_date = date_to_iso(missed_date)
        state_changed = True

    if state_changed:
        save_habit_state(state)

    return events


def register_activity_day(user_id: int) -> list[str]:
    events = evaluate_discipline(user_id)
    state = get_habit_state(user_id)
    today = now_date()
    today_iso = date_to_iso(today)
    workday_today = is_effective_workday(user_id, today, state)
    if not workday_today:
        events.append("ℹ️ Сегодня нерабочий день: стрик и челлендж не изменены.")
        return events

    last_counted = iso_to_date(state.streak_last_counted_date)
    if state.streak_days <= 0:
        state.streak_days = 1
        state.streak_last_counted_date = today_iso
    elif not last_counted:
        state.streak_days = 1
        state.streak_last_counted_date = today_iso
    else:
        missed_before_today = required_workdays_between(
            user_id,
            last_counted + timedelta(days=1),
            today - timedelta(days=1),
            state,
        )
        if (today - last_counted).days == 0:
            pass
        elif missed_before_today:
            state.streak_days = 1
            state.streak_last_counted_date = today_iso
        else:
            state.streak_days += 1
            state.streak_last_counted_date = today_iso

    save_habit_state(state)

    challenge = get_active_streak_challenge(user_id)
    if challenge:
        last_ch_date = iso_to_date(challenge.last_counted_date) or (today - timedelta(days=1))
        if (today - last_ch_date).days == 0:
            pass
        else:
            missed_before_today = required_workdays_between(
                user_id,
                last_ch_date + timedelta(days=1),
                today - timedelta(days=1),
                state,
            )
            if missed_before_today:
                if fail_streak_challenge(user_id, challenge.id):
                    events.append(
                        f"💥 <b>Streak Challenge провален</b>: пропуск рабочего дня.\n"
                        f"Ставка {challenge.wager_points} 🥈 сгорела."
                    )
                challenge = None
            else:
                new_done = challenge.days_done + 1
                with db_conn() as conn:
                    conn.execute(
                        """
                        UPDATE streak_challenges
                        SET days_done = ?, last_counted_date = ?, updated_at = ?
                        WHERE id = ? AND user_id = ? AND status = 'active'
                        """,
                        (new_done, today_iso, now_iso(), challenge.id, user_id),
                    )
                challenge.days_done = new_done
                challenge.last_counted_date = today_iso

        if challenge and challenge.days_done >= challenge.days_target:
            payout = challenge_payout(challenge.wager_points)
            if complete_streak_challenge(user_id, challenge.id, payout):
                events.append(
                    f"🏁 <b>Streak Challenge завершён</b>: {challenge.days_target} рабочих дней подряд.\n"
                    f"Награда: +{payout} 🥈"
                )

    return events


def challenge_progress_text(challenge: StreakChallenge) -> str:
    return (
        f"{challenge.days_done}/{challenge.days_target} раб. дн. "
        f"(ставка {challenge.wager_points} 🥈, выплата {challenge_payout(challenge.wager_points)} 🥈)"
    )


def decode_slot_machine_value(value: int) -> tuple[str, tuple[int, int, int]]:
    if value < 1 or value > 64:
        return "lose", (0, 0, 0)
    if value == 64:
        return "jackpot", (7, 7, 7)

    # Telegram slot mapping from official docs (values 1..63).
    mapping = [1, 2, 3, 0]
    raw = value - 1
    reels = (
        mapping[raw & 0x3],
        mapping[(raw >> 2) & 0x3],
        mapping[(raw >> 4) & 0x3],
    )
    unique = len(set(reels))
    if unique == 1:
        return "triple", reels
    if unique == 2:
        return "pair", reels
    return "lose", reels


def slot_reels_label(reels: tuple[int, int, int]) -> str:
    symbols = {
        0: "BAR",
        1: "🍇",
        2: "🍋",
        3: "7️⃣",
        7: "7️⃣",
    }
    return " | ".join(symbols.get(v, "❔") for v in reels)


def casino_info_text(user_id: int) -> str:
    profile = get_profile(user_id)
    silver_balance = profile.silver_balance if profile else 0
    expected_payout = (
        CASINO_PAYOUTS["pair"] * 36
        + CASINO_PAYOUTS["triple"] * 3
        + CASINO_PAYOUTS["jackpot"]
    ) / 64
    expected_net = expected_payout - CASINO_SPIN_COST
    edge_percent = int(round(((-expected_net) / CASINO_SPIN_COST) * 100))
    return (
        "🎰 <b>Казино</b>\n"
        f"🥈 Баланс: <b>{silver_balance}</b>\n"
        f"Цена спина: <b>{CASINO_SPIN_COST} 🥈</b>\n\n"
        f"Пара: +{CASINO_PAYOUTS['pair']} 🥈 (36/64)\n"
        f"Тройка: +{CASINO_PAYOUTS['triple']} 🥈 (3/64)\n"
        f"Джекпот 777: +{CASINO_PAYOUTS['jackpot']} 🥈 + Freeze (1/64)\n"
        "Проигрыш: 24/64\n\n"
        f"Средний итог на дистанции: <b>{expected_net:+.1f} 🥈</b> за спин (edge ~{edge_percent}%)\n\n"
        "Режим активен: жми «Крутить» или отправляй 🎰/стикер 🎰."
    )


def can_afford_casino_spin(user_id: int) -> bool:
    profile = get_profile(user_id)
    if not profile:
        return False
    return profile.silver_balance >= CASINO_SPIN_COST


def play_casino_spin(user_id: int, slot_value: int, source: str) -> tuple[bool, str]:
    profile = get_profile(user_id)
    if not profile:
        return False, "Профиль не настроен."

    ok, balance_after_bet = apply_points_transaction(
        user_id,
        -CASINO_SPIN_COST,
        reason="casino_bet",
        note=source,
        ref_type="casino",
        ref_id=slot_value,
        allow_negative=False,
    )
    if not ok:
        return False, f"Недостаточно серебра. Нужно {CASINO_SPIN_COST} 🥈"

    tier, reels = decode_slot_machine_value(slot_value)
    payout = CASINO_PAYOUTS.get(tier, 0)
    final_balance = balance_after_bet
    if payout > 0:
        _, final_balance = apply_points_transaction(
            user_id,
            payout,
            reason="casino_win",
            note=f"{tier}:{slot_value}",
            ref_type="casino",
            ref_id=slot_value,
            allow_negative=False,
        )

    freeze_bonus = 0
    if tier == "jackpot":
        habit = get_habit_state(user_id)
        if habit.streak_freezes < MAX_STREAK_FREEZES:
            habit.streak_freezes += 1
            save_habit_state(habit)
            freeze_bonus = 1

    tier_label = {
        "lose": "🙃 Ничего",
        "pair": "✨ Пара",
        "triple": "🔥 Тройка",
        "jackpot": "💎 Джекпот 777",
    }.get(tier, "🙃 Ничего")
    net = payout - CASINO_SPIN_COST
    net_label = f"+{net}" if net >= 0 else str(net)
    bonus_line = f"\n🧊 Бонус джекпота: +{freeze_bonus} Freeze" if freeze_bonus > 0 else ""

    text = (
        "🎰 <b>Результат спина</b>\n"
        f"Итог: <b>{tier_label}</b> ({net_label} 🥈)\n"
        f"Баланс: <b>{final_balance} 🥈</b>"
        f"{bonus_line}"
    )
    return True, text


def clear_progress(user_id: int, keep_goal: bool) -> None:
    with db_conn() as conn:
        conn.execute("DELETE FROM work_sessions WHERE user_id = ?", (user_id,))
        if not keep_goal:
            conn.execute(
                "UPDATE users SET goal_amount = 0, updated_at = ? WHERE user_id = ?",
                (now_iso(), user_id),
            )


def add_temp_message(user_id: int, chat_id: int, message_id: int) -> None:
    with db_conn() as conn:
        conn.execute(
            """
            INSERT INTO temp_messages (user_id, chat_id, message_id, created_at)
            VALUES (?, ?, ?, ?)
            """,
            (user_id, chat_id, message_id, now_iso()),
        )


def get_temp_messages(user_id: int, chat_id: int) -> list[tuple[int, int]]:
    with db_conn() as conn:
        rows = conn.execute(
            """
            SELECT id, message_id
            FROM temp_messages
            WHERE user_id = ? AND chat_id = ?
            ORDER BY id DESC
            """,
            (user_id, chat_id),
        ).fetchall()
    return [(int(r["id"]), int(r["message_id"])) for r in rows]


def clear_temp_messages(user_id: int, chat_id: int) -> None:
    with db_conn() as conn:
        conn.execute(
            "DELETE FROM temp_messages WHERE user_id = ? AND chat_id = ?",
            (user_id, chat_id),
        )


def delete_temp_message(entry_id: int) -> None:
    with db_conn() as conn:
        conn.execute("DELETE FROM temp_messages WHERE id = ?", (entry_id,))


def get_main_message_id(user_id: int) -> Optional[int]:
    with db_conn() as conn:
        row = conn.execute("SELECT main_message_id FROM ui_state WHERE user_id = ?", (user_id,)).fetchone()
    if not row:
        return None
    return row["main_message_id"]


def set_main_message_id(user_id: int, message_id: int) -> None:
    with db_conn() as conn:
        row = conn.execute("SELECT user_id FROM ui_state WHERE user_id = ?", (user_id,)).fetchone()
        if row:
            conn.execute(
                "UPDATE ui_state SET main_message_id = ?, updated_at = ? WHERE user_id = ?",
                (message_id, now_iso(), user_id),
            )
        else:
            conn.execute(
                "INSERT INTO ui_state (user_id, main_message_id, updated_at) VALUES (?, ?, ?)",
                (user_id, message_id, now_iso()),
            )


def fmt_money(value: float) -> str:
    return f"{value:,.0f}".replace(",", " ")


def fmt_duration(seconds: int) -> str:
    seconds = max(seconds, 0)
    h = seconds // 3600
    m = (seconds % 3600) // 60
    s = seconds % 60
    return f"{h:02d}:{m:02d}:{s:02d}"


def next_payday_deadline(now: datetime) -> datetime:
    if now.day < 15:
        return now.replace(day=15, hour=0, minute=0, second=0, microsecond=0)

    if now.month == 12:
        return now.replace(year=now.year + 1, month=1, day=1, hour=0, minute=0, second=0, microsecond=0)
    return now.replace(month=now.month + 1, day=1, hour=0, minute=0, second=0, microsecond=0)


def format_date_ru(dt: datetime) -> str:
    month_names = {
        1: "января",
        2: "февраля",
        3: "марта",
        4: "апреля",
        5: "мая",
        6: "июня",
        7: "июля",
        8: "августа",
        9: "сентября",
        10: "октября",
        11: "ноября",
        12: "декабря",
    }
    return f"{dt.day} {month_names[dt.month]}"


def parse_duration_text(text: str) -> Optional[int]:
    cleaned = text.strip().lower()

    hhmmss = re.search(r"(\d{1,2}):(\d{2}):(\d{2})", cleaned)
    if hhmmss:
        h, m, s = map(int, hhmmss.groups())
        return h * 3600 + m * 60 + s

    hhmm = re.search(r"(\d{1,3}):(\d{2})", cleaned)
    if hhmm:
        h, m = map(int, hhmm.groups())
        return h * 3600 + m * 60

    m = re.search(r"(\d+)\s*м", cleaned)
    h = re.search(r"(\d+)\s*ч", cleaned)
    if h or m:
        hs = int(h.group(1)) if h else 0
        ms = int(m.group(1)) if m else 0
        return hs * 3600 + ms * 60

    if cleaned.isdigit():
        return int(cleaned) * 60

    return None


TIMER_MARKER_RE = re.compile(r"(?:таймер[^\n]*остановлен)|затрачено", re.IGNORECASE)

FORWARDED_BATCH_DELAY = 1.2
_forwarded_batches: dict[int, dict] = {}


def parse_forwarded_timer(message_text: str) -> Optional[int]:
    text = message_text or ""
    if not TIMER_MARKER_RE.search(text):
        return None
    line_match = re.search(r"затрачено[^\n]*", text, re.IGNORECASE)
    target = (line_match.group(0) if line_match else text).lower()

    hhmmss = re.search(r"(\d{1,3}):(\d{2}):(\d{2})", target)
    if hhmmss:
        h, m, s = map(int, hhmmss.groups())
        return h * 3600 + m * 60 + s

    h_match = re.search(r"(\d+)\s*ч", target)
    m_match = re.search(r"(\d+)\s*м(?!с)", target)
    s_match = re.search(r"(\d+)\s*с", target)
    if h_match or m_match or s_match:
        h = int(h_match.group(1)) if h_match else 0
        m = int(m_match.group(1)) if m_match else 0
        s = int(s_match.group(1)) if s_match else 0
        return h * 3600 + m * 60 + s

    return None


def parse_forwarded_timer_label(message_text: str) -> str:
    text = message_text or ""
    task_match = re.search(r"задача\s*:?\s*([^\n]+)", text, re.IGNORECASE)
    if task_match:
        label = task_match.group(1).strip().strip("—-:").strip()
        if label:
            return label
    num_match = re.search(r"таймер\s*#?(\d+)", text, re.IGNORECASE)
    if num_match:
        return f"Таймер #{num_match.group(1)}"
    return "Таймер"


def summary_text(profile: Profile, user_id: int) -> str:
    if profile.gamification_enabled:
        evaluate_discipline(user_id)
    worked = total_seconds(user_id)
    earned = (worked / 3600) * profile.rate_per_hour
    goal = profile.goal_amount
    progress = 0 if goal <= 0 else min(100, int((earned / goal) * 100))
    left_money = max(0.0, goal - earned)

    left_seconds = 0
    if profile.rate_per_hour > 0:
        left_seconds = int((left_money / profile.rate_per_hour) * 3600)

    divider = "────────────"
    if not profile.gamification_enabled:
        return (
            f"🎯 <b>Твоя цель</b>: {fmt_money(goal)} ₽\n"
            f"💰 <b>Текущий заработок</b>: {fmt_money(earned)} ₽ ({progress}%)\n"
            f"⏱️ <b>Отработано</b>: {fmt_duration(worked)}\n"
            f"🧭 <b>Осталось до цели</b>: {fmt_money(left_money)} ₽ | {fmt_duration(left_seconds)}\n\n"
            f"{divider}\n\n"
            f"📈 <b>Ставка</b>: {fmt_money(profile.rate_per_hour)} ₽/ч\n\n"
            "🎮 <b>Геймификация выключена</b>. Включить можно в настройках."
        )

    active_bonus, _, _ = count_bonus_goals(user_id)
    habit = get_habit_state(user_id)
    challenge = get_active_streak_challenge(user_id)
    challenge_line = f"⚔️ <b>Челлендж</b>: {challenge_progress_text(challenge)}\n" if challenge else ""
    return (
        f"🎯 <b>Твоя цель</b>: {fmt_money(goal)} ₽\n"
        f"💰 <b>Текущий заработок</b>: {fmt_money(earned)} ₽ ({progress}%)\n"
        f"⏱️ <b>Отработано</b>: {fmt_duration(worked)}\n"
        f"🧭 <b>Осталось до цели</b>: {fmt_money(left_money)} ₽ | {fmt_duration(left_seconds)}\n\n"
        f"{divider}\n\n"
        f"🥈 <b>Серебро</b>: {profile.silver_balance} (+{profile.silver_per_hour}/ч)\n"
        f"🥇 <b>Золото</b>: {profile.gold_balance} (+{profile.gold_per_hour}/ч)\n\n"
        f"{divider}\n\n"
        f"🔥 <b>Стрик</b>: {habit.streak_days} дн | 🧊 {habit.streak_freezes}/{MAX_STREAK_FREEZES}\n"
        f"🏟 <b>Лига</b>: {league_name(habit.league_tier)}\n"
        f"🏁 <b>Активные бонус-цели</b>: {active_bonus}\n"
        f"📈 <b>Ставка</b>: {fmt_money(profile.rate_per_hour)} ₽/ч\n"
        f"{challenge_line}"
        "Остальные детали смотри в разделах «📊 Отчёты» и «🎮 Геймификация»."
    )


def short_notification_text(profile: Profile, user_id: int) -> str:
    if profile.gamification_enabled:
        evaluate_discipline(user_id)
    now = datetime.now(TZ)
    worked = total_seconds(user_id)
    earned = (worked / 3600) * profile.rate_per_hour
    left_money = max(0.0, profile.goal_amount - earned)
    left_seconds = int((left_money / profile.rate_per_hour) * 3600) if profile.rate_per_hour > 0 else 0

    deadline = next_payday_deadline(now)
    habit = get_habit_state(user_id)
    days_to_deadline = max(1, (deadline.date() - now.date()).days + 1)
    daily_target = left_money / days_to_deadline
    daily_target_seconds = 0
    if profile.rate_per_hour > 0:
        daily_target_seconds = int((daily_target / profile.rate_per_hour) * 3600)
    deadline_label = format_date_ru(deadline)

    divider = "────────────"
    if not profile.gamification_enabled:
        return (
            f"🎯 Цель: {fmt_money(profile.goal_amount)} ₽\n"
            f"💰 Заработано: {fmt_money(earned)} ₽\n"
            f"⏱ Осталось до цели: {fmt_duration(left_seconds)}\n\n"
            f"{divider}\n\n"
            f"📌 Нужно в день до {deadline_label}: {fmt_duration(daily_target_seconds)} | {fmt_money(daily_target)} ₽\n"
            "🎮 Геймификация выключена"
        )

    active_bonus, _, _ = count_bonus_goals(user_id)
    return (
        f"🎯 Цель: {fmt_money(profile.goal_amount)} ₽\n"
        f"💰 Заработано: {fmt_money(earned)} ₽\n"
        f"⏱ Осталось до цели: {fmt_duration(left_seconds)}\n\n"
        f"{divider}\n\n"
        f"🥈 Серебро: {profile.silver_balance} (+{profile.silver_per_hour}/ч)\n"
        f"🥇 Золото: {profile.gold_balance} (+{profile.gold_per_hour}/ч)\n\n"
        f"{divider}\n\n"
        f"🔥 Стрик: {habit.streak_days} дн | 🧊 {habit.streak_freezes}/{MAX_STREAK_FREEZES}\n"
        f"🏟 Лига: {league_name(habit.league_tier)}\n"
        f"🏁 Активные бонус-цели: {active_bonus}\n"
        f"📌 Нужно в день до {deadline_label}: {fmt_duration(daily_target_seconds)} | {fmt_money(daily_target)} ₽"
    )


def main_menu_kb(gamification_enabled: bool = True) -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton(text="➕ Добавить время", callback_data="add_time")],
        [InlineKeyboardButton(text="📊 Отчёты", callback_data="reports")],
    ]
    if gamification_enabled:
        rows.append([InlineKeyboardButton(text="🎮 Геймификация", callback_data="market")])
    rows.append([InlineKeyboardButton(text="⚙️ Настройки", callback_data="settings")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def reports_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="📜 История", callback_data="history")],
            [InlineKeyboardButton(text="📈 Аналитика", callback_data="analytics")],
            [InlineKeyboardButton(text="⬅️ Назад", callback_data="back_main")],
        ]
    )


def settings_kb(gamification_enabled: bool = True) -> InlineKeyboardMarkup:
    toggle_label = "🎮 Геймификация: Вкл" if gamification_enabled else "🎮 Геймификация: Выкл"
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="💸 Изменить ставку", callback_data="set_rate")],
            [InlineKeyboardButton(text="🎯 Изменить цель", callback_data="set_goal")],
            [InlineKeyboardButton(text=toggle_label, callback_data="toggle_gamification")],
            [InlineKeyboardButton(text="🔔 Уведомления", callback_data="notifs")],
            [InlineKeyboardButton(text="🧹 Сбросить прогресс", callback_data="reset_progress")],
            [InlineKeyboardButton(text="⬅️ Назад", callback_data="back_main")],
        ]
    )


def notif_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="❌ Выкл", callback_data="notif_off")],
            [InlineKeyboardButton(text="⏱ Каждый час", callback_data="notif_hourly")],
            [InlineKeyboardButton(text="🌙 Ежедневно", callback_data="notif_daily")],
            [InlineKeyboardButton(text="📅 Раз в неделю", callback_data="notif_weekly")],
            [InlineKeyboardButton(text="⬅️ Назад", callback_data="settings")],
        ]
    )


def reset_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="Сбросить, цель оставить", callback_data="reset_keep_goal")],
            [InlineKeyboardButton(text="Сбросить и удалить цель", callback_data="reset_drop_goal")],
            [InlineKeyboardButton(text="⬅️ Назад", callback_data="settings")],
        ]
    )


def confirm_add_kb(seconds: int, source: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="✅ Добавить", callback_data=f"confirm_add:{seconds}:{source}")],
            [InlineKeyboardButton(text="❌ Отмена", callback_data="cancel_add")],
        ]
    )


def confirm_reset_kb(keep_goal: bool) -> InlineKeyboardMarkup:
    action = "keep" if keep_goal else "drop"
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="✅ Подтвердить", callback_data=f"confirm_reset:{action}")],
            [InlineKeyboardButton(text="❌ Отмена", callback_data="settings")],
        ]
    )


def market_main_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🛍 Покупки", callback_data="market_shop")],
            [InlineKeyboardButton(text="🎮 Геймификация", callback_data="market_game")],
            [InlineKeyboardButton(text="⚙️ Управление", callback_data="market_admin")],
            [InlineKeyboardButton(text="⬅️ Назад", callback_data="back_main")],
        ]
    )


def market_shop_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🛍 Купить из маркета", callback_data="market_buy")],
            [InlineKeyboardButton(text="⚡ Быстро добавить позицию", callback_data="market_add")],
            [InlineKeyboardButton(text="⬅️ Назад в маркет", callback_data="market")],
        ]
    )


def market_game_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🎰 Казино", callback_data="casino_info")],
            [InlineKeyboardButton(text="🎯 Бонус-цели", callback_data="bonus_goals")],
            [InlineKeyboardButton(text="🔥 Дисциплина (кнут)", callback_data="discipline")],
            [InlineKeyboardButton(text="⬅️ Назад в маркет", callback_data="market")],
        ]
    )


def market_admin_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="📦 Управление позициями", callback_data="market_manage")],
            [InlineKeyboardButton(text="🧾 История валют и покупок", callback_data="market_history")],
            [InlineKeyboardButton(text="⚙️ Экономика валют", callback_data="market_economy")],
            [InlineKeyboardButton(text="⬅️ Назад в маркет", callback_data="market")],
        ]
    )


def market_buy_list_kb(items: list[MarketItem], silver_balance: int, gold_balance: int) -> InlineKeyboardMarkup:
    rows = []
    for item in items:
        current_balance = gold_balance if item.cost_currency == "gold" else silver_balance
        marker = "✅" if current_balance >= item.cost_points else "🔒"
        icon = currency_icon(item.cost_currency)
        rows.append(
            [
                InlineKeyboardButton(
                    text=f"{marker} {item.title} — {item.cost_points} {icon}",
                    callback_data=f"market_buy_item:{item.id}",
                )
            ]
        )
    rows.append([InlineKeyboardButton(text="⬅️ Назад к покупкам", callback_data="market_shop")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def market_buy_confirm_kb(item_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="✅ Купить", callback_data=f"market_confirm_buy:{item_id}")],
            [InlineKeyboardButton(text="⚡ Купить и вернуться к списку", callback_data=f"market_confirm_buy_list:{item_id}")],
            [InlineKeyboardButton(text="⬅️ Назад к списку", callback_data="market_buy")],
        ]
    )


def market_item_manage_kb(item_id: int, is_active: bool, item_currency: str = "silver") -> InlineKeyboardMarkup:
    toggle_label = "🚫 Отключить" if is_active else "✅ Включить"
    currency_label = f"💱 Валюта: {currency_icon(item_currency)} (сменить)"
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text=toggle_label, callback_data=f"market_toggle:{item_id}")],
            [InlineKeyboardButton(text="💰 Изменить цену", callback_data=f"market_edit_price:{item_id}")],
            [InlineKeyboardButton(text=currency_label, callback_data=f"market_edit_currency:{item_id}")],
            [InlineKeyboardButton(text="🗑 Удалить позицию", callback_data=f"market_delete_ask:{item_id}")],
        ]
    )


def market_delete_confirm_kb(item_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="✅ Удалить", callback_data=f"market_delete:{item_id}")],
            [InlineKeyboardButton(text="❌ Отмена", callback_data="market_manage")],
        ]
    )


def market_economy_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🥈 Курс серебра за час", callback_data="market_set_silver_rate")],
            [InlineKeyboardButton(text="🥇 Курс золота за час", callback_data="market_set_gold_rate")],
            [InlineKeyboardButton(text="🔁 Курс обмена (1 🥇 -> ? 🥈)", callback_data="market_set_exchange_rate")],
            [InlineKeyboardButton(text="🔄 Обменять золото в серебро", callback_data="market_exchange_gold_silver")],
            [InlineKeyboardButton(text="🎁 Начислить/списать валюту", callback_data="market_bonus_points")],
            [InlineKeyboardButton(text="⬅️ Назад в управление", callback_data="market_admin")],
        ]
    )


def market_bonus_currency_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="🥈 Серебро", callback_data="market_bonus_currency:silver"),
                InlineKeyboardButton(text="🥇 Золото", callback_data="market_bonus_currency:gold"),
            ],
            [InlineKeyboardButton(text="❌ Отмена", callback_data="market_cancel")],
        ]
    )


def casino_kb() -> InlineKeyboardMarkup:
    style_enabled = os.getenv("TG_BUTTON_STYLE", "").strip().lower() in {"1", "true", "yes", "on"}
    spin_icon_custom_emoji_id = (os.getenv("TG_CASINO_SPIN_ICON_EMOJI_ID", "") or "").strip()
    spin_kwargs = {
        "text": "🎰 Крутить",
        "callback_data": "casino_spin",
    }
    if style_enabled:
        spin_kwargs["style"] = "primary"
    if spin_icon_custom_emoji_id:
        spin_kwargs["icon_custom_emoji_id"] = spin_icon_custom_emoji_id
        spin_kwargs["text"] = "Крутить"

    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(**spin_kwargs)],
            [InlineKeyboardButton(text="⬅️ Назад в геймификацию", callback_data="market_game")],
        ]
    )


def market_cancel_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="❌ Отменить", callback_data="market_cancel")]]
    )


def market_back_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="⬅️ Назад в маркет", callback_data="market")]]
    )


def gamification_onboarding_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="✅ Включить", callback_data="setup_gamification:on"),
                InlineKeyboardButton(text="❌ Отключить", callback_data="setup_gamification:off"),
            ]
        ]
    )


def market_photo_choice_kb(item_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="⏭ Пропустить фото", callback_data=f"market_skip_photo:{item_id}")],
            [InlineKeyboardButton(text="❌ Отменить", callback_data="market_cancel")],
        ]
    )


def bonus_goals_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="➕ Новая бонус-цель", callback_data="bonus_create")],
            [InlineKeyboardButton(text="📌 Активные цели", callback_data="bonus_active")],
            [InlineKeyboardButton(text="🧾 Архив целей", callback_data="bonus_archive")],
            [InlineKeyboardButton(text="🔄 Проверить цели сейчас", callback_data="bonus_check_now")],
            [InlineKeyboardButton(text="⬅️ Назад в геймификацию", callback_data="market_game")],
        ]
    )


def bonus_goal_type_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="💰 Цель по деньгам", callback_data="bonus_type:money")],
            [InlineKeyboardButton(text="⏱ Цель по часам", callback_data="bonus_type:hours")],
            [InlineKeyboardButton(text="❌ Отменить", callback_data="market_cancel")],
        ]
    )


def bonus_goal_deadline_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🌙 Сегодня 23:59", callback_data="bonus_deadline:today")],
            [InlineKeyboardButton(text="📅 До пятницы", callback_data="bonus_deadline:friday")],
            [InlineKeyboardButton(text="🗓 До конца месяца", callback_data="bonus_deadline:month")],
            [InlineKeyboardButton(text="✍️ Ввести дату вручную", callback_data="bonus_deadline:custom")],
            [InlineKeyboardButton(text="❌ Отменить", callback_data="market_cancel")],
        ]
    )


def bonus_goal_manage_kb(goal_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🗑 Удалить цель", callback_data=f"bonus_delete_ask:{goal_id}")],
            [InlineKeyboardButton(text="⬅️ Назад к целям", callback_data="bonus_goals")],
        ]
    )


def bonus_goal_delete_confirm_kb(goal_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="✅ Удалить", callback_data=f"bonus_delete:{goal_id}")],
            [InlineKeyboardButton(text="❌ Отмена", callback_data="bonus_active")],
        ]
    )


def discipline_kb(has_active_challenge: bool) -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton(text=f"🧊 Купить Freeze ({STREAK_FREEZE_COST} 🥈)", callback_data="discipline_buy_freeze")],
        [InlineKeyboardButton(text="⚔️ Streak Challenge", callback_data="discipline_challenge_menu")],
        [InlineKeyboardButton(text="📅 Рабочие дни и исключения", callback_data="discipline_workdays")],
        [InlineKeyboardButton(text="🏟 Проверить лигу и стрик", callback_data="discipline_check")],
    ]
    if has_active_challenge:
        rows.append([InlineKeyboardButton(text="💥 Сдаться в челлендже", callback_data="discipline_surrender")])
    rows.append([InlineKeyboardButton(text="⬅️ Назад в геймификацию", callback_data="market_game")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def discipline_challenge_options_kb() -> InlineKeyboardMarkup:
    rows = []
    for days, wager in STREAK_CHALLENGE_OPTIONS.items():
        rows.append(
            [
                InlineKeyboardButton(
                    text=f"{days} рабочих дней — ставка {wager} 🥈",
                    callback_data=f"discipline_start_challenge:{days}",
                )
            ]
        )
    rows.append([InlineKeyboardButton(text="⬅️ Назад", callback_data="discipline")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def discipline_workdays_kb(user_id: int, state: HabitState) -> InlineKeyboardMarkup:
    mask = normalize_workdays_mask(state.workdays_mask)
    day_rows = []
    for idx, label in enumerate(WEEKDAY_LABELS_RU):
        enabled = mask[idx] == "1"
        marker = "✅" if enabled else "▫️"
        day_rows.append(
            InlineKeyboardButton(
                text=f"{marker} {label}",
                callback_data=f"discipline_toggle_wd:{idx}",
            )
        )

    rows = [day_rows[:4], day_rows[4:]]

    today = now_date()
    today_effective = is_effective_workday(user_id, today, state)
    tomorrow = today + timedelta(days=1)
    tomorrow_effective = is_effective_workday(user_id, tomorrow, state)

    rows.append(
        [
            InlineKeyboardButton(
                text="🛑 Сегодня выходной" if today_effective else "✅ Сегодня рабочий",
                callback_data="discipline_toggle_day:0",
            ),
            InlineKeyboardButton(
                text="🛑 Завтра выходной" if tomorrow_effective else "✅ Завтра рабочий",
                callback_data="discipline_toggle_day:1",
            ),
        ]
    )
    rows.append(
        [InlineKeyboardButton(text="⬅️ Назад", callback_data="discipline")]
    )
    return InlineKeyboardMarkup(inline_keyboard=rows)


def build_progress_pie(profile: Profile, user_id: int) -> bytes:
    worked = total_seconds(user_id)
    earned = (worked / 3600) * profile.rate_per_hour
    goal = max(profile.goal_amount, 1.0)
    left = max(0.0, goal - earned)
    progress_pct = min(100, (earned / goal) * 100)

    values = [max(earned, 0.01), max(left, 0.01)]
    labels = ["Заработано", "Осталось"]
    colors = ["#2f9e44", "#ced4da"]

    fig, ax = plt.subplots(figsize=(6, 6), dpi=160)
    wedges, _ = ax.pie(
        values,
        colors=colors,
        startangle=90,
        counterclock=False,
        wedgeprops={"width": 0.35},
    )
    ax.legend(wedges, labels, loc="lower center", bbox_to_anchor=(0.5, -0.05), ncol=2)
    ax.text(
        0,
        0,
        f"{progress_pct:.0f}%\nиз {fmt_money(profile.goal_amount)} ₽",
        ha="center",
        va="center",
        fontsize=14,
        fontweight="bold",
    )
    ax.set(aspect="equal")
    fig.patch.set_facecolor("white")
    plt.tight_layout()

    buf = io.BytesIO()
    plt.savefig(buf, format="png", bbox_inches="tight")
    plt.close(fig)
    return buf.getvalue()


def build_analytics_daily_chart(profile: Profile, user_id: int, days: int = 14) -> bytes:
    labels, secs = daily_stats(user_id, days=days)
    hours = [s / 3600 for s in secs]
    earned = [h * profile.rate_per_hour for h in hours]

    fig, ax1 = plt.subplots(figsize=(8, 4), dpi=160)
    ax2 = ax1.twinx()

    ax1.plot(labels, hours, marker="o", color="#1c7ed6", linewidth=2)
    ax2.bar(labels, earned, alpha=0.25, color="#2f9e44")

    ax1.set_title(f"Динамика за {days} дней")
    ax1.set_ylabel("Часы")
    ax2.set_ylabel("Рубли")
    ax1.grid(axis="y", linestyle="--", alpha=0.4)
    ax1.tick_params(axis="x", rotation=45)
    fig.tight_layout()

    buf = io.BytesIO()
    plt.savefig(buf, format="png", bbox_inches="tight")
    plt.close(fig)
    return buf.getvalue()


def build_analytics_period_chart(profile: Profile, user_id: int) -> bytes:
    now = datetime.now(TZ)
    today_start = now.replace(hour=0, minute=0, second=0, microsecond=0)
    week_start = today_start - timedelta(days=today_start.weekday())
    month_start = today_start.replace(day=1)

    today_sec = period_seconds(user_id, today_start)
    week_sec = period_seconds(user_id, week_start)
    month_sec = period_seconds(user_id, month_start)
    hours = [today_sec / 3600, week_sec / 3600, month_sec / 3600]
    rub = [h * profile.rate_per_hour for h in hours]

    labels = ["Сегодня", "Неделя", "Месяц"]
    x = range(len(labels))

    fig, ax = plt.subplots(figsize=(7, 4), dpi=160)
    bars = ax.bar(x, rub, color=["#74c0fc", "#4dabf7", "#228be6"])
    ax.set_xticks(list(x), labels)
    ax.set_ylabel("Рубли")
    ax.set_title("Сравнение периодов")
    ax.grid(axis="y", linestyle="--", alpha=0.35)

    for idx, bar in enumerate(bars):
        ax.text(
            bar.get_x() + bar.get_width() / 2,
            bar.get_height(),
            f"{hours[idx]:.1f}ч",
            ha="center",
            va="bottom",
            fontsize=9,
        )

    fig.tight_layout()
    buf = io.BytesIO()
    plt.savefig(buf, format="png", bbox_inches="tight")
    plt.close(fig)
    return buf.getvalue()


async def safe_delete(message: Message) -> None:
    try:
        await message.delete()
    except TelegramBadRequest:
        pass


async def cleanup_temp_messages(bot: Bot, chat_id: int, user_id: int) -> None:
    for entry_id, message_id in get_temp_messages(user_id, chat_id):
        try:
            await bot.delete_message(chat_id, message_id)
            delete_temp_message(entry_id)
        except TelegramBadRequest as exc:
            # Keep temporary deletion errors (e.g., animated dice still playing)
            # so the next cleanup attempt can delete the message.
            err = str(exc).lower()
            if "message to delete not found" in err or "message identifier is not specified" in err:
                delete_temp_message(entry_id)


async def send_temp(message: Message, user_id: int, text: str, **kwargs) -> Message:
    sent = await message.answer(text, **kwargs)
    add_temp_message(user_id, message.chat.id, sent.message_id)
    return sent


async def send_temp_photo(
    message: Message,
    user_id: int,
    photo_bytes: bytes,
    filename: str,
    caption: Optional[str] = None,
) -> Message:
    photo = BufferedInputFile(photo_bytes, filename=filename)
    sent = await message.answer_photo(photo=photo, caption=caption)
    add_temp_message(user_id, message.chat.id, sent.message_id)
    return sent


async def send_temp_photo_id(
    message: Message,
    user_id: int,
    photo_file_id: str,
    caption: Optional[str] = None,
    **kwargs,
) -> Message:
    sent = await message.answer_photo(photo=photo_file_id, caption=caption, **kwargs)
    add_temp_message(user_id, message.chat.id, sent.message_id)
    return sent


async def render_main(bot: Bot, chat_id: int, user_id: int) -> None:
    profile = get_profile(user_id)
    if not profile or profile.rate_per_hour <= 0 or profile.goal_amount <= 0:
        return

    caption = summary_text(profile, user_id)
    chart = build_progress_pie(profile, user_id)
    photo = BufferedInputFile(chart, filename="progress.png")

    await cleanup_temp_messages(bot, chat_id, user_id)
    existing_id = get_main_message_id(user_id)
    if existing_id:
        try:
            await bot.delete_message(chat_id, existing_id)
        except TelegramBadRequest:
            pass

    sent = await bot.send_photo(
        chat_id=chat_id,
        photo=photo,
        caption=caption,
        parse_mode="HTML",
        reply_markup=main_menu_kb(profile.gamification_enabled),
    )
    set_main_message_id(user_id, sent.message_id)


def market_overview_text(user_id: int) -> str:
    profile = get_profile(user_id)
    if not profile:
        return "Профиль не настроен."

    habit = get_habit_state(user_id)
    active_items, total_items = count_market_items(user_id)
    active_bonus, completed_bonus, expired_bonus = count_bonus_goals(user_id)
    divider = "────────────"
    return (
        "🛒 <b>Внутренний маркет</b>\n"
        f"🥈 Баланс серебра: <b>{profile.silver_balance}</b>\n"
        f"🥇 Баланс золота: <b>{profile.gold_balance}</b>\n"
        f"⏱ Доход за час: <b>{profile.silver_per_hour} 🥈</b> и <b>{profile.gold_per_hour} 🥇</b>\n"
        f"{divider}\n"
        f"📦 Позиции: <b>{active_items}</b> активных из {total_items}\n"
        f"🔥 Стрик: <b>{habit.streak_days}</b> дн | 🧊 {habit.streak_freezes}/{MAX_STREAK_FREEZES}\n"
        f"🏟 Лига: <b>{league_name(habit.league_tier)}</b>\n"
        f"🎯 Цели: активных <b>{active_bonus}</b>, выполнено <b>{completed_bonus}</b>, просрочено <b>{expired_bonus}</b>\n"
        f"{divider}\n\n"
        "Выбери раздел ниже:"
    )


async def render_market_home(bot: Bot, message: Message, user_id: int) -> None:
    events = evaluate_discipline(user_id) + evaluate_bonus_goals(user_id)
    await cleanup_temp_messages(bot, message.chat.id, user_id)
    text = market_overview_text(user_id)
    if events:
        text = "\n\n".join(events) + "\n\n" + text
    await send_temp(
        message,
        user_id,
        text,
        parse_mode="HTML",
        reply_markup=market_main_kb(),
    )


async def render_market_buy_list(bot: Bot, message: Message, user_id: int) -> None:
    await cleanup_temp_messages(bot, message.chat.id, user_id)
    items = list_market_items(user_id, active_only=True, limit=50)
    if not items:
        await send_temp(
            message,
            user_id,
            "Маркет пока пуст. Добавь первую позицию.",
            reply_markup=market_shop_kb(),
        )
        return
    profile = get_profile(user_id)
    silver_balance = profile.silver_balance if profile else 0
    gold_balance = profile.gold_balance if profile else 0
    await send_temp(
        message,
        user_id,
        (
            f"💳 Баланс: <b>{silver_balance}</b> 🥈 | <b>{gold_balance}</b> 🥇\n\n"
            f"{market_items_text(user_id, active_only=True, profile=profile)}"
        ),
        parse_mode="HTML",
        reply_markup=market_buy_list_kb(items, silver_balance, gold_balance),
    )


async def render_market_manage(bot: Bot, message: Message, user_id: int) -> None:
    await cleanup_temp_messages(bot, message.chat.id, user_id)
    items = list_market_items(user_id, active_only=False, limit=50)
    if not items:
        await send_temp(
            message,
            user_id,
            "Позиции не найдены. Добавь первую позицию в маркете.",
            reply_markup=market_admin_kb(),
        )
        return

    await send_temp(
        message,
        user_id,
        market_manage_text(user_id),
        parse_mode="HTML",
    )
    for item in items:
        icon = currency_icon(item.cost_currency)
        body = (
            f"#{item.id} <b>{html.escape(item.title)}</b>\n"
            f"{icon} Цена: {item.cost_points}\n"
            f"Статус: {'активна' if item.is_active else 'выключена'}"
        )
        if item.description:
            body += f"\n📝 {html.escape(item.description)}"
        if item.photo_file_id:
            await send_temp_photo_id(
                message,
                user_id,
                item.photo_file_id,
                caption=body,
                parse_mode="HTML",
                reply_markup=market_item_manage_kb(item.id, item.is_active, item.cost_currency),
            )
        else:
            await send_temp(
                message,
                user_id,
                body,
                parse_mode="HTML",
                reply_markup=market_item_manage_kb(item.id, item.is_active, item.cost_currency),
            )
    await send_temp(message, user_id, "Вернуться", reply_markup=market_admin_kb())


async def render_bonus_goals_home(bot: Bot, message: Message, user_id: int) -> None:
    events = evaluate_discipline(user_id) + evaluate_bonus_goals(user_id)
    await cleanup_temp_messages(bot, message.chat.id, user_id)
    text = bonus_goals_overview_text(user_id)
    if events:
        text = "\n\n".join(events) + "\n\n" + text
    await send_temp(
        message,
        user_id,
        text,
        parse_mode="HTML",
        reply_markup=bonus_goals_kb(),
    )


async def render_bonus_active_goals(bot: Bot, message: Message, user_id: int) -> None:
    evaluate_discipline(user_id)
    evaluate_bonus_goals(user_id)
    await cleanup_temp_messages(bot, message.chat.id, user_id)
    profile = get_profile(user_id)
    if not profile:
        await send_temp(message, user_id, "Профиль не настроен.", reply_markup=market_game_kb())
        return

    goals = list_bonus_goals(user_id, statuses=("active",), limit=50)
    if not goals:
        await send_temp(
            message,
            user_id,
            "Активных бонус-целей нет. Создай первую цель.",
            reply_markup=bonus_goals_kb(),
        )
        return

    await send_temp(message, user_id, "📌 <b>Активные бонус-цели</b>", parse_mode="HTML")
    for goal in goals:
        await send_temp(
            message,
            user_id,
            bonus_goal_card_text(goal, profile),
            parse_mode="HTML",
            reply_markup=bonus_goal_manage_kb(goal.id),
        )
    await send_temp(message, user_id, "Вернуться", reply_markup=bonus_goals_kb())


async def render_discipline_home(bot: Bot, message: Message, user_id: int) -> None:
    events = evaluate_discipline(user_id)
    await cleanup_temp_messages(bot, message.chat.id, user_id)
    text = discipline_overview_text(user_id)
    if events:
        text = "\n\n".join(events) + "\n\n" + text
    await send_temp(
        message,
        user_id,
        text,
        parse_mode="HTML",
        reply_markup=discipline_kb(has_active_challenge=get_active_streak_challenge(user_id) is not None),
    )


async def render_discipline_workdays(bot: Bot, message: Message, user_id: int) -> None:
    evaluate_discipline(user_id)
    state = get_habit_state(user_id)
    await cleanup_temp_messages(bot, message.chat.id, user_id)
    await send_temp(
        message,
        user_id,
        discipline_workdays_text(user_id),
        parse_mode="HTML",
        reply_markup=discipline_workdays_kb(user_id, state),
    )

async def ensure_setup(message: Message, state: FSMContext):
    profile = get_profile(message.from_user.id)
    if not profile or profile.rate_per_hour <= 0:
        await state.set_state(SetupStates.waiting_rate)
        await send_temp(message, message.from_user.id, "Введите ставку за час в рублях, например: 800")
        return True
    if profile.goal_amount <= 0:
        await state.set_state(SetupStates.waiting_goal)
        await send_temp(message, message.from_user.id, "Введите цель по заработку в рублях, например: 50000")
        return True
    return False


async def run_notification_loop(bot: Bot):
    last_sent = {}
    while True:
        now = datetime.now(TZ)
        with db_conn() as conn:
            users = conn.execute("SELECT user_id, notifications_mode FROM users").fetchall()

        for user in users:
            mode = user["notifications_mode"]
            should_send = False

            if mode == "hourly" and now.minute == 0:
                should_send = True
            elif mode == "daily" and now.hour == 21 and now.minute == 0:
                should_send = True
            elif mode == "weekly" and now.weekday() == 6 and now.hour == 21 and now.minute == 0:
                should_send = True
            if should_send:
                key = (user["user_id"], mode, now.strftime("%Y%m%d%H%M"))
                if key in last_sent:
                    continue
                profile = get_profile(user["user_id"])
                if profile:
                    text = short_notification_text(profile, user["user_id"])
                    try:
                        sent = await bot.send_message(user["user_id"], text)
                        asyncio.create_task(delete_message_later(bot, user["user_id"], sent.message_id, 24 * 60 * 60))
                        last_sent[key] = True
                    except TelegramBadRequest:
                        pass

        await asyncio.sleep(60)


async def delete_message_later(bot: Bot, chat_id: int, message_id: int, delay_seconds: int) -> None:
    await asyncio.sleep(delay_seconds)
    try:
        await bot.delete_message(chat_id, message_id)
    except TelegramBadRequest:
        pass


def parse_money(text: str) -> Optional[float]:
    cleaned = text.replace(" ", "").replace(",", ".")
    try:
        value = float(cleaned)
    except ValueError:
        return None
    if value <= 0:
        return None
    return value


def parse_positive_float(text: str) -> Optional[float]:
    cleaned = text.strip().replace(" ", "").replace(",", ".")
    try:
        value = float(cleaned)
    except ValueError:
        return None
    if value <= 0:
        return None
    return value


def parse_positive_int(text: str) -> Optional[int]:
    cleaned = text.strip().replace(" ", "")
    if not cleaned.isdigit():
        return None
    value = int(cleaned)
    if value <= 0:
        return None
    return value


def parse_signed_int(text: str) -> Optional[int]:
    cleaned = text.strip().replace(" ", "")
    if not cleaned:
        return None
    if cleaned[0] in "+-":
        if len(cleaned) == 1 or not cleaned[1:].isdigit():
            return None
    elif not cleaned.isdigit():
        return None
    value = int(cleaned)
    if value == 0:
        return None
    return value


def parse_market_currency(text: str) -> Optional[str]:
    token = (text or "").strip().lower()
    if token in {"silver", "sil", "s", "серебро", "сер", "🥈"}:
        return "silver"
    if token in {"gold", "g", "золото", "зол", "🥇"}:
        return "gold"
    return None


def parse_market_quick_input(text: str) -> Optional[tuple[str, int, str, str]]:
    cleaned = (text or "").strip()
    if not cleaned:
        return None

    delimiter = ";" if ";" in cleaned else ("|" if "|" in cleaned else None)
    if not delimiter:
        return None

    parts = [part.strip() for part in cleaned.split(delimiter)]
    if len(parts) < 2:
        return None
    title = parts[0]
    if len(title) < 2 or len(title) > 60:
        return None

    cost = parse_positive_int(parts[1])
    if not cost:
        return None

    currency = "silver"
    description = ""
    if len(parts) >= 3:
        maybe_currency = parse_market_currency(parts[2])
        if maybe_currency:
            currency = maybe_currency
            description = " ; ".join(parts[3:]).strip() if len(parts) >= 4 else ""
        else:
            description = " ; ".join(parts[2:]).strip()

    if len(description) > 250:
        return None
    return title, cost, currency, description


def human_number(value: float, decimals: int = 1) -> str:
    text = f"{value:.{decimals}f}"
    if "." in text:
        text = text.rstrip("0").rstrip(".")
    return text.replace(".", ",")


def bonus_target_type_label(target_type: str) -> str:
    return "деньги" if target_type == "money" else "часы"


def bonus_target_value_label(goal: BonusGoal) -> str:
    if goal.target_type == "money":
        return f"{fmt_money(goal.target_value)} ₽"
    return f"{human_number(goal.target_value, 2)} ч"


def bonus_progress_value_label(target_type: str, value: float) -> str:
    if target_type == "money":
        return f"{fmt_money(value)} ₽"
    return f"{human_number(value, 2)} ч"


def make_bonus_goal_title(target_type: str, target_value: float, deadline_at: datetime) -> str:
    due = deadline_at.strftime("%d.%m %H:%M")
    if target_type == "money":
        return f"До {due}: {fmt_money(target_value)} ₽"
    return f"До {due}: {human_number(target_value, 2)} ч"


def history_text(user_id: int) -> str:
    rows = recent_history(user_id)
    if not rows:
        return "История пуста."

    lines = ["📜 <b>Последние записи</b>"]
    for r in rows:
        dt = datetime.fromisoformat(r["created_at"]).astimezone(TZ)
        lines.append(
            f"• {dt.strftime('%d.%m %H:%M')} | {fmt_duration(r['duration_seconds'])} | {r['source']}"
        )
    return "\n".join(lines)


def market_items_text(user_id: int, active_only: bool = True, profile: Optional[Profile] = None) -> str:
    items = list_market_items(user_id, active_only=active_only, limit=50)
    if not items:
        if active_only:
            return "Маркет пока пуст. Добавь первую позицию."
        return "Позиции не найдены."

    lines = ["🛍 <b>Доступные позиции</b>"]
    for item in items:
        description = f" — {html.escape(item.description)}" if item.description else ""
        icon = currency_icon(item.cost_currency)
        availability = ""
        if profile is not None:
            balance = profile_balance_by_currency(profile, item.cost_currency)
            availability = " ✅" if balance >= item.cost_points else " 🔒"
        lines.append(f"• #{item.id} {html.escape(item.title)}: {item.cost_points} {icon}{availability}{description}")
    return "\n".join(lines)


def market_manage_text(user_id: int) -> str:
    items = list_market_items(user_id, active_only=False, limit=50)
    if not items:
        return "Позиции не найдены. Добавь первую позицию в маркете."

    lines = ["📦 <b>Управление позициями</b>"]
    for item in items:
        status = "активна" if item.is_active else "выключена"
        icon = currency_icon(item.cost_currency)
        lines.append(f"• #{item.id} {html.escape(item.title)}: {item.cost_points} {icon} ({status})")
    return "\n".join(lines)


def market_economy_text(user_id: int) -> str:
    profile = get_profile(user_id)
    if not profile:
        return "Профиль не настроен."
    divider = "────────────"
    return (
        "🎮 <b>Экономика геймификации</b>\n"
        f"🥈 Серебро: <b>{profile.silver_balance}</b>\n"
        f"🥇 Золото: <b>{profile.gold_balance}</b>\n"
        f"⏱ Доход в час: <b>{profile.silver_per_hour} 🥈</b> и <b>{profile.gold_per_hour} 🥇</b>\n"
        f"{divider}\n"
        f"🔁 Обмен: <b>1 🥇 = {profile.gold_to_silver_rate} 🥈</b>\n\n"
        "Бонусы и покупки работают только с серебром. Золото можно только обменять в серебро."
    )


def weekly_minutes(user_id: int, week_start: datetime.date) -> int:
    week_end = week_start + timedelta(days=6)
    return range_seconds(user_id, start_of_day(week_start), end_of_day(week_end)) // 60


def discipline_overview_text(user_id: int) -> str:
    state = get_habit_state(user_id)
    challenge = get_active_streak_challenge(user_id)
    today = now_date()
    current_week = week_start_sunday(today)
    minutes = weekly_minutes(user_id, current_week)
    promo_threshold = LEAGUE_PROMOTION_MINUTES[state.league_tier]
    safe_threshold = LEAGUE_SAFE_MINUTES[state.league_tier]
    challenge_line = (
        f"⚔️ Челлендж: {challenge_progress_text(challenge)}\n"
        if challenge
        else "⚔️ Челлендж: нет активного\n"
    )
    if state.league_tier >= len(LEAGUE_NAMES):
        up_line = "🚀 Повышение: это максимальная лига."
    else:
        up_left = max(0, promo_threshold - minutes)
        if up_left == 0:
            up_line = f"🚀 Повышение: порог {promo_threshold} мин уже выполнен."
        else:
            up_line = f"🚀 До повышения не хватает: {up_left} мин (нужно {promo_threshold})."

    if safe_threshold <= 0:
        down_line = "🛡 Понижение: ниже этой лиги уже некуда."
    else:
        down_left = max(0, safe_threshold - minutes)
        if down_left == 0:
            down_line = f"🛡 От понижения защищено: минимум {safe_threshold} мин уже есть."
        else:
            down_line = f"🛡 Чтобы не понизили, добери ещё {down_left} мин (минимум {safe_threshold})."

    today_mode = "рабочий" if is_effective_workday(user_id, today, state) else "нерабочий"
    tomorrow = today + timedelta(days=1)
    tomorrow_mode = "рабочий" if is_effective_workday(user_id, tomorrow, state) else "нерабочий"
    divider = "────────────"
    return (
        "🔥 <b>Дисциплина (метод кнута)</b>\n"
        f"Стрик: <b>{state.streak_days}</b> дн.\n"
        f"Freeze: <b>{state.streak_freezes}/{MAX_STREAK_FREEZES}</b>\n"
        f"{challenge_line}"
        f"{divider}\n"
        f"Лига: <b>{league_name(state.league_tier)}</b>\n"
        f"Рабочие дни: <b>{workdays_mask_label(state.workdays_mask)}</b>\n"
        f"Сегодня: {today_mode}, завтра: {tomorrow_mode}\n"
        f"Эта неделя: <b>{minutes} мин</b>\n"
        f"{up_line}\n"
        f"{down_line}\n"
        "📅 Лига пересчитывается в начале новой недели.\n\n"
        "Пропуск дня может сжечь freeze или сорвать стрик. "
        "В челлендже freeze не работает."
    )


def discipline_workdays_text(user_id: int) -> str:
    state = get_habit_state(user_id)
    today = now_date()
    tomorrow = today + timedelta(days=1)
    today_override = get_day_override(user_id, today)
    tomorrow_override = get_day_override(user_id, tomorrow)

    today_mode = "рабочий" if is_effective_workday(user_id, today, state) else "нерабочий"
    tomorrow_mode = "рабочий" if is_effective_workday(user_id, tomorrow, state) else "нерабочий"
    today_suffix = " (override)" if today_override is not None else ""
    tomorrow_suffix = " (override)" if tomorrow_override is not None else ""

    lines = [
        "📅 <b>Настройка рабочих дней</b>",
        f"Регулярный график: <b>{workdays_mask_label(state.workdays_mask)}</b>",
        f"Сегодня ({today.strftime('%d.%m')}): <b>{today_mode}</b>{today_suffix}",
        f"Завтра ({tomorrow.strftime('%d.%m')}): <b>{tomorrow_mode}</b>{tomorrow_suffix}",
    ]

    overrides = list_day_overrides(user_id, from_date=today, limit=8)
    if overrides:
        lines.append("")
        lines.append("<b>Ближайшие override:</b>")
        for row in overrides:
            d = iso_to_date(row["target_date"])
            if not d:
                continue
            status = "рабочий" if int(row["is_workday"]) == 1 else "нерабочий"
            lines.append(f"• {d.strftime('%d.%m')} ({WEEKDAY_LABELS_RU[d.weekday()]}): {status}")

    lines.append("")
    lines.append("Стрик и челлендж считают только рабочие дни.")
    return "\n".join(lines)


def bonus_goal_card_text(goal: BonusGoal, profile: Profile) -> str:
    now = datetime.now(TZ)
    progress = bonus_goal_progress(goal, profile, at_time=now)
    ratio = 0 if goal.target_value <= 0 else min(100, int((progress / goal.target_value) * 100))
    deadline = parse_iso_dt(goal.deadline_at)

    progress_label = bonus_progress_value_label(goal.target_type, progress)
    target_label = bonus_target_value_label(goal)
    left_value = max(0.0, goal.target_value - progress)
    left_label = bonus_progress_value_label(goal.target_type, left_value)

    status_label = {
        "active": "активна",
        "completed": "выполнена",
        "expired": "просрочена",
    }.get(goal.status, goal.status)

    return (
        f"🎯 <b>#{goal.id} {html.escape(goal.title)}</b>\n"
        f"Тип: {bonus_target_type_label(goal.target_type)}\n"
        f"Прогресс: {progress_label} / {target_label} ({ratio}%)\n"
        f"Осталось: {left_label}\n"
        f"Награда: +{goal.reward_points} 🥈\n"
        f"Дедлайн: {deadline.strftime('%d.%m.%Y %H:%M')}\n"
        f"Статус: {status_label}"
    )


def bonus_goals_overview_text(user_id: int) -> str:
    profile = get_profile(user_id)
    if not profile:
        return "Профиль не настроен."
    active, completed, expired = count_bonus_goals(user_id)
    divider = "────────────"
    return (
        "🎯 <b>Бонус-цели</b>\n"
        f"🥈 Баланс серебра: <b>{profile.silver_balance}</b>\n"
        f"{divider}\n"
        f"• Активные: {active}\n"
        f"• Выполненные: {completed}\n"
        f"• Просроченные: {expired}\n\n"
        "Создавай несколько целей одновременно: например до пятницы и до конца месяца."
    )


def points_activity_text(user_id: int, limit: int = 20) -> str:
    rows = recent_points_activity(user_id, limit=limit)
    if not rows:
        return "💱 История валют пока пуста."

    reason_labels = {
        "work_session": "работа",
        "market_purchase": "покупка",
        "manual_bonus": "бонус",
        "bonus_goal_reward": "награда за цель",
        "streak_challenge_wager": "ставка в челлендже",
        "streak_challenge_reward": "награда за челлендж",
        "league_promotion": "повышение лиги",
        "league_demotion": "понижение лиги",
        "streak_freeze_purchase": "покупка freeze",
        "casino_bet": "казино ставка",
        "casino_win": "казино выигрыш",
        "exchange_gold_to_silver": "обмен золота в серебро",
    }
    lines = ["💱 <b>История валют</b>"]
    for row in rows:
        dt = datetime.fromisoformat(row["created_at"]).astimezone(TZ)
        delta = int(row["delta_points"])
        delta_label = f"+{delta}" if delta > 0 else str(delta)
        currency = row["currency"] if "currency" in row.keys() else "silver"
        currency_icon = "🥇" if currency == "gold" else "🥈"
        reason = reason_labels.get(row["reason"], row["reason"])
        note = f" ({html.escape(row['note'])})" if row["note"] else ""
        lines.append(f"• {dt.strftime('%d.%m %H:%M')} | {delta_label} {currency_icon} | {html.escape(reason)}{note}")
    return "\n".join(lines)


def purchase_history_text(user_id: int, limit: int = 20) -> str:
    rows = recent_market_purchases(user_id, limit=limit)
    if not rows:
        return "🧾 Покупок пока не было."

    lines = ["🧾 <b>Последние покупки</b>"]
    for row in rows:
        dt = datetime.fromisoformat(row["created_at"]).astimezone(TZ)
        icon = currency_icon(row["cost_currency"]) if "cost_currency" in row.keys() else "🥈"
        lines.append(
            f"• {dt.strftime('%d.%m %H:%M')} | {html.escape(row['item_title_snapshot'])} | -{int(row['cost_points'])} {icon}"
        )
    return "\n".join(lines)


def bonus_goals_archive_text(user_id: int, limit: int = 30) -> str:
    goals = list_bonus_goals(user_id, statuses=("completed", "expired"), limit=limit)
    if not goals:
        return "Архив бонус-целей пуст."

    lines = ["🧾 <b>Архив бонус-целей</b>"]
    for goal in goals:
        deadline = parse_iso_dt(goal.deadline_at).strftime("%d.%m %H:%M")
        status = "✅" if goal.status == "completed" else "⌛"
        lines.append(
            f"• {status} #{goal.id} {html.escape(goal.title)} | {bonus_target_value_label(goal)} | до {deadline} | +{goal.reward_points} 🥈"
        )
    return "\n".join(lines)


def analytics_text(user_id: int) -> str:
    profile = get_profile(user_id)
    if not profile:
        return "Профиль не настроен."

    now = datetime.now(TZ)
    today_start = now.replace(hour=0, minute=0, second=0, microsecond=0)
    week_start = today_start - timedelta(days=today_start.weekday())
    month_start = today_start.replace(day=1)

    total_sec = total_seconds(user_id)
    today_sec = period_seconds(user_id, today_start)
    week_sec = period_seconds(user_id, week_start)
    month_sec = period_seconds(user_id, month_start)

    active_days = max(1, (now - month_start).days + 1)
    avg_day_sec = month_sec // active_days
    avg_day_earned = (avg_day_sec / 3600) * profile.rate_per_hour

    total_earned = (total_sec / 3600) * profile.rate_per_hour
    left_money = max(0.0, profile.goal_amount - total_earned)
    if avg_day_earned > 0:
        eta_days = int(left_money / avg_day_earned) + (1 if left_money % avg_day_earned else 0)
    else:
        eta_days = 0

    return (
        "📊 <b>Аналитика эффективности</b>\n"
        f"• Всего: {fmt_duration(total_sec)} ({fmt_money(total_earned)} ₽)\n"
        f"• Сегодня: {fmt_duration(today_sec)} ({fmt_money((today_sec / 3600) * profile.rate_per_hour)} ₽)\n"
        f"• Неделя: {fmt_duration(week_sec)} ({fmt_money((week_sec / 3600) * profile.rate_per_hour)} ₽)\n"
        f"• Месяц: {fmt_duration(month_sec)} ({fmt_money((month_sec / 3600) * profile.rate_per_hour)} ₽)\n"
        f"• Среднее в день (месяц): {fmt_duration(avg_day_sec)} ({fmt_money(avg_day_earned)} ₽)\n"
        f"• Прогноз до цели: ~{eta_days} дн.\n"
    )


def build_dispatcher(bot: Bot) -> Dispatcher:
    dp = Dispatcher(storage=MemoryStorage())

    async def ensure_gamification_enabled(message: Message, state: FSMContext, user_id: int) -> bool:
        profile = get_profile(user_id)
        if not profile:
            return False
        if profile.gamification_enabled:
            return True
        await state.clear()
        await cleanup_temp_messages(bot, message.chat.id, user_id)
        await send_temp(
            message,
            user_id,
            (
                "🎮 <b>Геймификация отключена</b>\n"
                "Монеты продолжают копиться, но игровые разделы скрыты.\n"
                "Включить можно в «⚙️ Настройки»."
            ),
            parse_mode="HTML",
            reply_markup=settings_kb(False),
        )
        return False

    async def show_casino_screen(
        message: Message,
        user_id: int,
        spin_result: str = "",
        include_info: bool = True,
    ) -> None:
        await cleanup_temp_messages(bot, message.chat.id, user_id)
        profile = get_profile(user_id)
        balance = profile.silver_balance if profile else 0
        body_parts = []
        if spin_result:
            body_parts.append(spin_result)
        if include_info:
            body_parts.append(casino_info_text(user_id))
        else:
            body_parts.append(
                f"🥈 Баланс: <b>{balance} 🥈</b>\n"
                f"Спин: <b>{CASINO_SPIN_COST} 🥈</b>\n"
                "Жми «Крутить» для следующего спина."
            )
        body = "\n\n".join(body_parts)
        await send_temp(
            message,
            user_id,
            body,
            parse_mode="HTML",
            reply_markup=casino_kb(),
        )

    async def ensure_setup_for_user(message: Message, state: FSMContext, user_id: int) -> bool:
        profile = get_profile(user_id)
        if not profile or profile.rate_per_hour <= 0:
            await state.set_state(SetupStates.waiting_rate)
            await send_temp(message, user_id, "Введите ставку за час в рублях, например: 800")
            return True
        if profile.goal_amount <= 0:
            await state.set_state(SetupStates.waiting_goal)
            await send_temp(message, user_id, "Введите цель по заработку в рублях, например: 50000")
            return True
        return False

    async def run_casino_spin_via_bot(message: Message, state: FSMContext, user_id: int, source: str) -> None:
        if await state.get_state() != SetupStates.casino_mode.state:
            return
        if await ensure_setup_for_user(message, state, user_id):
            return
        if not await ensure_gamification_enabled(message, state, user_id):
            return
        if not can_afford_casino_spin(user_id):
            await show_casino_screen(
                message,
                user_id,
                f"Недостаточно серебра для спина. Нужно {CASINO_SPIN_COST} 🥈",
                include_info=False,
            )
            return
        # Button-triggered spins use server-side RNG, so casino leaves no dice messages in chat.
        slot_value = random.randint(1, 64)
        success, text = play_casino_spin(user_id, slot_value, source=source)
        if not success:
            await show_casino_screen(message, user_id, text, include_info=False)
            return
        await show_casino_screen(message, user_id, text, include_info=False)

    @dp.message(CommandStart())
    async def cmd_start(message: Message, state: FSMContext):
        await state.clear()
        if await ensure_setup(message, state):
            return
        await render_main(bot, message.chat.id, message.from_user.id)

    @dp.message(F.text == "Меню")
    async def menu_button(message: Message, state: FSMContext):
        await state.clear()
        if await ensure_setup(message, state):
            return
        await render_main(bot, message.chat.id, message.from_user.id)

    @dp.message(F.dice)
    async def casino_dice(message: Message, state: FSMContext):
        if await state.get_state() != SetupStates.casino_mode.state:
            return
        if not message.dice or message.dice.emoji != "🎰":
            return
        if await ensure_setup(message, state):
            return
        if not await ensure_gamification_enabled(message, state, message.from_user.id):
            return
        if getattr(message, "forward_origin", None) is not None:
            await show_casino_screen(
                message,
                message.from_user.id,
                "Пересланный слот не считается. Отправь новый 🎰.",
                include_info=False,
            )
            return

        await safe_delete(message)
        success, text = play_casino_spin(message.from_user.id, message.dice.value, source="user_dice")
        if not success:
            await show_casino_screen(message, message.from_user.id, text, include_info=False)
            return
        await show_casino_screen(message, message.from_user.id, text, include_info=False)

    @dp.message(F.text.regexp(r"^\s*🎰\ufe0f?\s*$"))
    async def casino_text_spin(message: Message, state: FSMContext):
        if await state.get_state() != SetupStates.casino_mode.state:
            return
        await safe_delete(message)
        await run_casino_spin_via_bot(message, state, message.from_user.id, source="text_trigger")

    @dp.message(F.sticker)
    async def casino_sticker_spin(message: Message, state: FSMContext):
        if await state.get_state() != SetupStates.casino_mode.state:
            return
        sticker_emoji = message.sticker.emoji if message.sticker else None
        if sticker_emoji != "🎰":
            return
        await safe_delete(message)
        await run_casino_spin_via_bot(message, state, message.from_user.id, source="sticker_trigger")

    @dp.message(SetupStates.waiting_rate)
    async def set_rate_step(message: Message, state: FSMContext):
        value = parse_money(message.text or "")
        if not value:
            await send_temp(message, message.from_user.id, "Ставка должна быть числом больше 0. Пример: 800")
            return

        profile = get_profile(message.from_user.id)
        goal = profile.goal_amount if profile else 0
        upsert_profile(message.from_user.id, value, goal)
        await state.set_state(SetupStates.waiting_goal)
        await safe_delete(message)
        await send_temp(message, message.from_user.id, "Отлично. Теперь введи цель по заработку в рублях. Пример: 50000")

    @dp.message(SetupStates.waiting_goal)
    async def set_goal_step(message: Message, state: FSMContext):
        value = parse_money(message.text or "")
        if not value:
            await send_temp(message, message.from_user.id, "Цель должна быть числом больше 0. Пример: 50000")
            return

        profile = get_profile(message.from_user.id)
        rate = profile.rate_per_hour if profile else 0
        upsert_profile(message.from_user.id, rate, value)
        await safe_delete(message)
        await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
        await state.set_state(SetupStates.waiting_gamification_choice)
        await send_temp(
            message,
            message.from_user.id,
            (
                "🎮 <b>Включить геймификацию?</b>\n"
                "Если отключишь, останется упрощённый режим: цель, заработок, отчёты и аналитика.\n"
                "Монеты всё равно будут копиться."
            ),
            parse_mode="HTML",
            reply_markup=gamification_onboarding_kb(),
        )

    @dp.callback_query(F.data.startswith("setup_gamification:"))
    async def cb_setup_gamification(callback: CallbackQuery, state: FSMContext):
        try:
            mode = callback.data.split(":")[1]
        except (ValueError, IndexError):
            await callback.answer("Ошибка выбора", show_alert=True)
            return
        if mode not in {"on", "off"}:
            await callback.answer("Ошибка выбора", show_alert=True)
            return
        enabled = mode == "on"
        update_gamification_enabled(callback.from_user.id, enabled)
        await state.clear()
        await callback.answer("Геймификация включена" if enabled else "Геймификация отключена")
        await render_main(bot, callback.message.chat.id, callback.from_user.id)

    @dp.callback_query(F.data == "add_time")
    async def cb_add_time(callback: CallbackQuery, state: FSMContext):
        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await state.set_state(SetupStates.waiting_manual_time)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "Введите время вручную. Примеры: 1:30, 02:10:00, 90 (мин), 2ч 15м",
        )

    @dp.message(SetupStates.waiting_manual_time)
    async def manual_time(message: Message, state: FSMContext):
        seconds = parse_duration_text(message.text or "")
        if not seconds or seconds <= 0:
            await send_temp(message, message.from_user.id, "Не понял формат времени. Пример: 1:30 или 02:10:00")
            return

        await state.clear()
        await safe_delete(message)
        profile = get_profile(message.from_user.id)
        added_money = (seconds / 3600) * (profile.rate_per_hour if profile else 0)
        added_silver = calculate_session_currency(seconds, profile.silver_per_hour if profile else 0)
        added_gold = calculate_session_currency(seconds, profile.gold_per_hour if profile else 0)
        await send_temp(
            message,
            message.from_user.id,
            (
                f"Распознано: {fmt_duration(seconds)} ({fmt_money(added_money)} ₽)\n"
                f"🥈 Начислится: +{added_silver}\n"
                f"🥇 Начислится: +{added_gold}\n"
                "Добавляем?"
            ),
            reply_markup=confirm_add_kb(seconds, "manual"),
        )

    @dp.callback_query(F.data == "reports")
    async def cb_reports(callback: CallbackQuery, state: FSMContext):
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "📊 <b>Отчёты</b>\nВыбери: история добавлений или аналитика.",
            parse_mode="HTML",
            reply_markup=reports_kb(),
        )

    @dp.callback_query(F.data == "history")
    async def cb_history(callback: CallbackQuery, state: FSMContext):
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            history_text(callback.from_user.id),
            parse_mode="HTML",
            reply_markup=reports_kb(),
        )

    @dp.callback_query(F.data == "analytics")
    async def cb_analytics(callback: CallbackQuery, state: FSMContext):
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        profile = get_profile(callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            analytics_text(callback.from_user.id),
            parse_mode="HTML",
            reply_markup=reports_kb(),
        )
        if profile:
            daily_chart = build_analytics_daily_chart(profile, callback.from_user.id, days=14)
            period_chart = build_analytics_period_chart(profile, callback.from_user.id)
            await send_temp_photo(
                callback.message,
                callback.from_user.id,
                daily_chart,
                "analytics_daily.png",
                "График 1: динамика эффективности по дням",
            )
            await send_temp_photo(
                callback.message,
                callback.from_user.id,
                period_chart,
                "analytics_periods.png",
                "График 2: сравнение сегодня/неделя/месяц",
            )
            await send_temp(
                callback.message,
                callback.from_user.id,
                "⬆️ Отчёты обновлены",
                reply_markup=reports_kb(),
            )

    @dp.callback_query(F.data == "market")
    async def cb_market(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await render_market_home(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "market_shop")
    async def cb_market_shop(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "🛍 <b>Покупки</b>\nЗдесь можно покупать награды за 🥈/🥇 и быстро добавлять новые позиции.",
            parse_mode="HTML",
            reply_markup=market_shop_kb(),
        )

    @dp.callback_query(F.data == "market_game")
    async def cb_market_game(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        prev_state = await state.get_state()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        if prev_state == SetupStates.casino_mode.state:
            # Give animated dice a moment to become deletable, then retry cleanup.
            await asyncio.sleep(1.2)
            await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "🎮 <b>Геймификация</b>\nКазино, бонус-цели и дисциплина в одном месте.",
            parse_mode="HTML",
            reply_markup=market_game_kb(),
        )

    @dp.callback_query(F.data == "market_admin")
    async def cb_market_admin(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "⚙️ <b>Управление</b>\nРедактирование позиций, история и экономика валют.",
            parse_mode="HTML",
            reply_markup=market_admin_kb(),
        )

    @dp.callback_query(F.data == "casino_info")
    async def cb_casino_info(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.set_state(SetupStates.casino_mode)
        await show_casino_screen(callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "casino_spin")
    async def cb_casino_spin(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        if await state.get_state() != SetupStates.casino_mode.state:
            await callback.answer("Открой казино в разделе геймификации.", show_alert=True)
            return
        await callback.answer("Кручу...")
        await run_casino_spin_via_bot(callback.message, state, callback.from_user.id, source="casino_button")

    @dp.callback_query(F.data == "bonus_goals")
    async def cb_bonus_goals(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await render_bonus_goals_home(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "bonus_check_now")
    async def cb_bonus_check_now(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer("Проверяю цели...")
        await state.clear()
        await render_bonus_goals_home(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "bonus_active")
    async def cb_bonus_active(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await render_bonus_active_goals(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "bonus_archive")
    async def cb_bonus_archive(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        evaluate_discipline(callback.from_user.id)
        evaluate_bonus_goals(callback.from_user.id)
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            bonus_goals_archive_text(callback.from_user.id),
            parse_mode="HTML",
            reply_markup=bonus_goals_kb(),
        )

    @dp.callback_query(F.data == "bonus_create")
    async def cb_bonus_create(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "Выбери тип бонус-цели.",
            reply_markup=bonus_goal_type_kb(),
        )

    @dp.callback_query(F.data.startswith("bonus_type:"))
    async def cb_bonus_type(callback: CallbackQuery, state: FSMContext):
        try:
            target_type = callback.data.split(":")[1]
        except IndexError:
            await callback.answer("Ошибка данных", show_alert=True)
            return
        if target_type not in {"money", "hours"}:
            await callback.answer("Неподдерживаемый тип", show_alert=True)
            return

        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await state.update_data(bonus_target_type=target_type)
        await state.set_state(SetupStates.waiting_bonus_goal_value)
        prompt = (
            "Введите цель в рублях, например: 30000"
            if target_type == "money"
            else "Введите цель в часах, например: 25 или 37.5"
        )
        await send_temp(
            callback.message,
            callback.from_user.id,
            prompt,
            reply_markup=market_cancel_kb(),
        )

    @dp.message(SetupStates.waiting_bonus_goal_value)
    async def bonus_goal_value_step(message: Message, state: FSMContext):
        data = await state.get_data()
        target_type = str(data.get("bonus_target_type", ""))
        if target_type not in {"money", "hours"}:
            await state.clear()
            await send_temp(message, message.from_user.id, "Сбилась сессия. Начни создание цели заново.")
            return

        if target_type == "money":
            target_value = parse_money(message.text or "")
        else:
            target_value = parse_positive_float(message.text or "")

        if not target_value:
            help_text = "Укажи число больше 0. Пример: 30000" if target_type == "money" else "Укажи часы, например: 25 или 37.5"
            await send_temp(message, message.from_user.id, help_text)
            return

        await state.update_data(bonus_target_value=float(target_value))
        await safe_delete(message)
        await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
        await send_temp(
            message,
            message.from_user.id,
            "Теперь выбери дедлайн.",
            reply_markup=bonus_goal_deadline_kb(),
        )

    @dp.callback_query(F.data.startswith("bonus_deadline:"))
    async def cb_bonus_deadline(callback: CallbackQuery, state: FSMContext):
        choice = callback.data.split(":")[1]
        data = await state.get_data()
        target_type = str(data.get("bonus_target_type", ""))
        try:
            target_value = float(data.get("bonus_target_value", 0.0))
        except (TypeError, ValueError):
            target_value = 0.0
        if target_type not in {"money", "hours"} or target_value <= 0:
            await callback.answer("Сначала выбери тип и значение цели.", show_alert=True)
            return

        now = datetime.now(TZ)
        deadline_at: Optional[datetime] = None
        if choice == "today":
            deadline_at = end_of_today(now)
        elif choice == "friday":
            deadline_at = deadline_this_friday(now)
        elif choice == "month":
            deadline_at = deadline_end_of_month(now)
        elif choice == "custom":
            await callback.answer()
            await state.set_state(SetupStates.waiting_bonus_goal_custom_deadline)
            await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
            await send_temp(
                callback.message,
                callback.from_user.id,
                "Введи дедлайн в формате `ДД.ММ ЧЧ:ММ` или `ДД.ММ.ГГГГ ЧЧ:ММ`",
                parse_mode="Markdown",
                reply_markup=market_cancel_kb(),
            )
            return
        else:
            await callback.answer("Неверный дедлайн", show_alert=True)
            return

        if deadline_at <= now:
            await callback.answer("Дедлайн должен быть в будущем", show_alert=True)
            return

        await callback.answer()
        await state.update_data(bonus_deadline_at=deadline_at.isoformat())
        await state.set_state(SetupStates.waiting_bonus_goal_reward)
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            (
                f"Дедлайн: <b>{deadline_at.strftime('%d.%m.%Y %H:%M')}</b>\n"
                "Теперь укажи награду в серебре (например 40)."
            ),
            parse_mode="HTML",
            reply_markup=market_cancel_kb(),
        )

    @dp.message(SetupStates.waiting_bonus_goal_custom_deadline)
    async def bonus_goal_custom_deadline_step(message: Message, state: FSMContext):
        deadline_at = parse_custom_deadline(message.text or "")
        if not deadline_at:
            await send_temp(
                message,
                message.from_user.id,
                "Не распознал дату. Пример: 28.02 23:59 или 28.02.2026 23:59",
            )
            return

        await state.update_data(bonus_deadline_at=deadline_at.isoformat())
        await state.set_state(SetupStates.waiting_bonus_goal_reward)
        await safe_delete(message)
        await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
        await send_temp(
            message,
            message.from_user.id,
            (
                f"Дедлайн сохранён: <b>{deadline_at.strftime('%d.%m.%Y %H:%M')}</b>\n"
                "Теперь укажи награду в серебре."
            ),
            parse_mode="HTML",
            reply_markup=market_cancel_kb(),
        )

    @dp.message(SetupStates.waiting_bonus_goal_reward)
    async def bonus_goal_reward_step(message: Message, state: FSMContext):
        reward_points = parse_positive_int(message.text or "")
        if not reward_points:
            await send_temp(message, message.from_user.id, "Награда должна быть целым числом больше 0.")
            return
        if reward_points > 1_000_000:
            await send_temp(message, message.from_user.id, "Слишком большая награда. Укажи меньше 1 000 000.")
            return

        data = await state.get_data()
        target_type = str(data.get("bonus_target_type", ""))
        try:
            target_value = float(data.get("bonus_target_value", 0.0))
        except (TypeError, ValueError):
            target_value = 0.0
        deadline_iso = str(data.get("bonus_deadline_at", ""))
        if target_type not in {"money", "hours"} or target_value <= 0 or not deadline_iso:
            await state.clear()
            await send_temp(message, message.from_user.id, "Не удалось создать цель. Попробуй снова.")
            return

        try:
            deadline_at = parse_iso_dt(deadline_iso)
        except ValueError:
            await state.clear()
            await send_temp(message, message.from_user.id, "Некорректный дедлайн. Создай цель заново.")
            return
        title = make_bonus_goal_title(target_type, target_value, deadline_at)
        goal_id = create_bonus_goal(
            user_id=message.from_user.id,
            title=title,
            target_type=target_type,
            target_value=target_value,
            reward_points=reward_points,
            deadline_at=deadline_at,
        )
        await state.clear()
        await safe_delete(message)
        await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
        goal = get_bonus_goal(message.from_user.id, goal_id)
        profile = get_profile(message.from_user.id)
        if goal and profile:
            body = (
                "✅ <b>Бонус-цель создана</b>\n\n"
                f"{bonus_goal_card_text(goal, profile)}"
            )
            await send_temp(
                message,
                message.from_user.id,
                body,
                parse_mode="HTML",
                reply_markup=bonus_goals_kb(),
            )
        else:
            await send_temp(
                message,
                message.from_user.id,
                "✅ Бонус-цель создана",
                reply_markup=bonus_goals_kb(),
            )

    @dp.callback_query(F.data.startswith("bonus_delete_ask:"))
    async def cb_bonus_delete_ask(callback: CallbackQuery):
        try:
            goal_id = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная цель", show_alert=True)
            return

        goal = get_bonus_goal(callback.from_user.id, goal_id)
        if not goal:
            await callback.answer("Цель не найдена", show_alert=True)
            return

        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            f"Удалить бонус-цель <b>{html.escape(goal.title)}</b>?",
            parse_mode="HTML",
            reply_markup=bonus_goal_delete_confirm_kb(goal_id),
        )

    @dp.callback_query(F.data.startswith("bonus_delete:"))
    async def cb_bonus_delete(callback: CallbackQuery, state: FSMContext):
        try:
            goal_id = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная цель", show_alert=True)
            return

        await state.clear()
        if not delete_bonus_goal(callback.from_user.id, goal_id):
            await callback.answer("Цель не найдена", show_alert=True)
            return
        await callback.answer("Цель удалена")
        await render_bonus_active_goals(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "discipline")
    async def cb_discipline(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await render_discipline_home(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "discipline_check")
    async def cb_discipline_check(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer("Проверяю...")
        await state.clear()
        await render_discipline_home(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "discipline_workdays")
    async def cb_discipline_workdays(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await render_discipline_workdays(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data.startswith("discipline_toggle_wd:"))
    async def cb_discipline_toggle_wd(callback: CallbackQuery):
        try:
            weekday_idx = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректный день", show_alert=True)
            return
        toggle_regular_weekday(callback.from_user.id, weekday_idx)
        await callback.answer("Сохранено")
        await render_discipline_workdays(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data.startswith("discipline_toggle_day:"))
    async def cb_discipline_toggle_day(callback: CallbackQuery):
        try:
            offset = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная дата", show_alert=True)
            return
        if offset < 0 or offset > 30:
            await callback.answer("Слишком большой сдвиг", show_alert=True)
            return
        target_date = now_date() + timedelta(days=offset)
        new_mode = toggle_day_effective_status(callback.from_user.id, target_date)
        await callback.answer(f"{target_date.strftime('%d.%m')}: {'рабочий' if new_mode else 'нерабочий'}")
        await render_discipline_workdays(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "discipline_buy_freeze")
    async def cb_discipline_buy_freeze(callback: CallbackQuery):
        state = get_habit_state(callback.from_user.id)
        if state.streak_freezes >= MAX_STREAK_FREEZES:
            await callback.answer("Freeze уже максимум", show_alert=True)
            return

        ok, balance = apply_points_transaction(
            callback.from_user.id,
            -STREAK_FREEZE_COST,
            reason="streak_freeze_purchase",
            note="покупка freeze",
            allow_negative=False,
        )
        if not ok:
            await callback.answer("Недостаточно серебра", show_alert=True)
            return

        state.streak_freezes += 1
        save_habit_state(state)
        await callback.answer(f"Freeze куплен. Баланс: {balance} 🥈")
        await render_discipline_home(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "discipline_challenge_menu")
    async def cb_discipline_challenge_menu(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        active = get_active_streak_challenge(callback.from_user.id)
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        if active:
            await send_temp(
                callback.message,
                callback.from_user.id,
                (
                    "⚔️ <b>У тебя уже активный Streak Challenge</b>\n"
                    f"{challenge_progress_text(active)}"
                ),
                parse_mode="HTML",
                reply_markup=discipline_kb(has_active_challenge=True),
            )
            return
        await send_temp(
            callback.message,
            callback.from_user.id,
            (
                "⚔️ <b>Streak Challenge</b>\n"
                "Как в Duolingo: выбираешь серию рабочих дней подряд, ставишь серебро и рискуешь им.\n"
                "Если пропускаешь рабочий день, ставка сгорает. Freeze не работает."
            ),
            parse_mode="HTML",
            reply_markup=discipline_challenge_options_kb(),
        )

    @dp.callback_query(F.data.startswith("discipline_start_challenge:"))
    async def cb_discipline_start_challenge(callback: CallbackQuery):
        try:
            days = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректный челлендж", show_alert=True)
            return
        wager = STREAK_CHALLENGE_OPTIONS.get(days)
        if not wager:
            await callback.answer("Неизвестная длительность", show_alert=True)
            return
        ok, message_text = create_streak_challenge(callback.from_user.id, days, wager)
        if not ok:
            await callback.answer(message_text, show_alert=True)
            return
        await callback.answer("Челлендж запущен")
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            f"✅ {message_text}",
            reply_markup=discipline_kb(has_active_challenge=True),
        )

    @dp.callback_query(F.data == "discipline_surrender")
    async def cb_discipline_surrender(callback: CallbackQuery):
        active = get_active_streak_challenge(callback.from_user.id)
        if not active:
            await callback.answer("Активного челленджа нет", show_alert=True)
            return
        if not fail_streak_challenge(callback.from_user.id, active.id):
            await callback.answer("Не удалось завершить челлендж", show_alert=True)
            return
        await callback.answer("Челлендж остановлен")
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            (
                "💥 Челлендж завершён досрочно.\n"
                f"Ставка {active.wager_points} 🥈 не возвращается."
            ),
            reply_markup=discipline_kb(has_active_challenge=False),
        )

    @dp.callback_query(F.data == "market_buy")
    async def cb_market_buy(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await render_market_buy_list(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data.startswith("market_buy_item:"))
    async def cb_market_buy_item(callback: CallbackQuery):
        try:
            item_id = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная позиция", show_alert=True)
            return

        item = get_market_item(callback.from_user.id, item_id, active_only=True)
        if not item:
            await callback.answer("Позиция недоступна", show_alert=True)
            return

        profile = get_profile(callback.from_user.id)
        balance = profile_balance_by_currency(profile, item.cost_currency) if profile else 0
        currency_ru = currency_name_ru(item.cost_currency)
        icon = currency_icon(item.cost_currency)
        missing = max(0, item.cost_points - balance)
        caption = (
            f"🛍 <b>{html.escape(item.title)}</b>\n"
            f"{icon} Цена: <b>{item.cost_points}</b>\n"
            f"💳 Баланс ({currency_ru}): <b>{balance}</b> {icon}"
        )
        if missing > 0:
            caption += f"\n🔒 Не хватает: <b>{missing}</b> {icon}"
        if item.description:
            caption += f"\n📝 {html.escape(item.description)}"

        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        if item.photo_file_id:
            await send_temp_photo_id(
                callback.message,
                callback.from_user.id,
                item.photo_file_id,
                caption=caption,
                parse_mode="HTML",
                reply_markup=market_buy_confirm_kb(item.id),
            )
        else:
            await send_temp(
                callback.message,
                callback.from_user.id,
                caption,
                parse_mode="HTML",
                reply_markup=market_buy_confirm_kb(item.id),
            )

    @dp.callback_query(F.data.startswith("market_confirm_buy:"))
    async def cb_market_confirm_buy(callback: CallbackQuery):
        try:
            item_id = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная позиция", show_alert=True)
            return

        success, payload, balance, item_currency = buy_market_item(callback.from_user.id, item_id)
        icon = currency_icon(item_currency)
        currency_ru = currency_name_ru(item_currency)
        if not success:
            if payload.startswith("Недостаточно "):
                await callback.answer(f"{payload}. Баланс: {balance} {icon}", show_alert=True)
            else:
                await callback.answer(payload, show_alert=True)
            return

        await callback.answer("Покупка оформлена")
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            f"✅ Куплено: <b>{html.escape(payload)}</b>\n{icon} Новый баланс ({currency_ru}): <b>{balance}</b>",
            parse_mode="HTML",
            reply_markup=market_main_kb(),
        )

    @dp.callback_query(F.data.startswith("market_confirm_buy_list:"))
    async def cb_market_confirm_buy_list(callback: CallbackQuery):
        try:
            item_id = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная позиция", show_alert=True)
            return

        success, payload, balance, item_currency = buy_market_item(callback.from_user.id, item_id)
        icon = currency_icon(item_currency)
        if not success:
            if payload.startswith("Недостаточно "):
                await callback.answer(f"{payload}. Баланс: {balance} {icon}", show_alert=True)
            else:
                await callback.answer(payload, show_alert=True)
            return

        await callback.answer(f"Куплено: {payload}")
        await render_market_buy_list(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "market_add")
    async def cb_market_add(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await state.set_state(SetupStates.waiting_market_quick_item)
        await send_temp(
            callback.message,
            callback.from_user.id,
            (
                "⚡ <b>Быстрое добавление позиции</b>\n"
                "Отправь одной строкой:\n"
                "<code>Название; цена; валюта; описание (опционально)</code>\n"
                "Валюта: <b>silver</b>/<b>🥈</b> или <b>gold</b>/<b>🥇</b>. Если не указать, будет серебро.\n\n"
                "Примеры:\n"
                "• <code>YouTube 3 часа; 30</code>\n"
                "• <code>Кальян; 15; gold; 30 минут отдыха</code>"
            ),
            parse_mode="HTML",
            reply_markup=market_cancel_kb(),
        )

    @dp.message(SetupStates.waiting_market_quick_item)
    async def market_quick_add_step(message: Message, state: FSMContext):
        parsed = parse_market_quick_input(message.text or "")
        if not parsed:
            await send_temp(
                message,
                message.from_user.id,
                (
                    "Формат не распознан.\n"
                    "Используй: <code>Название; цена; валюта; описание</code>\n"
                    "Валюта опциональна: <code>silver</code>/<code>gold</code>.\n"
                    "Описание можно не указывать."
                ),
                parse_mode="HTML",
            )
            return

        title, cost, item_currency, description = parsed
        icon = currency_icon(item_currency)
        item_id = create_market_item(
            message.from_user.id,
            title=title,
            cost_points=cost,
            cost_currency=item_currency,
            description=description,
            photo_file_id="",
        )
        await state.update_data(
            quick_item_id=item_id,
            quick_item_title=title,
            quick_item_currency=item_currency,
        )
        await state.set_state(SetupStates.waiting_market_quick_photo)
        await safe_delete(message)
        await send_temp(
            message,
            message.from_user.id,
            (
                f"✅ Позиция создана: <b>{html.escape(title)}</b> ({cost} {icon})\n"
                "Теперь отправь фото для карточки или пропусти."
            ),
            parse_mode="HTML",
            reply_markup=market_photo_choice_kb(item_id),
        )

    @dp.message(SetupStates.waiting_market_quick_photo)
    async def market_quick_add_photo_step(message: Message, state: FSMContext):
        data = await state.get_data()
        item_id = int(data.get("quick_item_id", 0))
        item_title = str(data.get("quick_item_title", "позиция"))
        if item_id <= 0:
            await state.clear()
            await send_temp(message, message.from_user.id, "Сессия добавления сброшена. Повтори ещё раз.")
            return

        if (message.text or "").strip() == "-":
            await state.clear()
            await safe_delete(message)
            await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
            await send_temp(
                message,
                message.from_user.id,
                f"✅ Позиция сохранена без фото: <b>{html.escape(item_title)}</b>",
                parse_mode="HTML",
                reply_markup=market_main_kb(),
            )
            return

        if not message.photo:
            await send_temp(
                message,
                message.from_user.id,
                "Отправь фото или нажми «Пропустить фото».",
            )
            return

        photo_file_id = message.photo[-1].file_id
        if not update_market_item_photo(message.from_user.id, item_id, photo_file_id):
            await state.clear()
            await send_temp(message, message.from_user.id, "Не удалось сохранить фото. Попробуй добавить снова.")
            return

        await state.clear()
        await safe_delete(message)
        await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
        await send_temp(
            message,
            message.from_user.id,
            f"✅ Фото добавлено к позиции <b>{html.escape(item_title)}</b>",
            parse_mode="HTML",
            reply_markup=market_main_kb(),
        )

    @dp.callback_query(F.data.startswith("market_skip_photo:"))
    async def cb_market_skip_photo(callback: CallbackQuery, state: FSMContext):
        try:
            item_id = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная позиция", show_alert=True)
            return

        item = get_market_item(callback.from_user.id, item_id, active_only=False)
        if not item:
            await callback.answer("Позиция не найдена", show_alert=True)
            return

        await callback.answer("Сохранено без фото")
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            f"✅ Позиция сохранена: <b>{html.escape(item.title)}</b>",
            parse_mode="HTML",
            reply_markup=market_main_kb(),
        )

    @dp.callback_query(F.data == "market_manage")
    async def cb_market_manage(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await render_market_manage(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data.startswith("market_toggle:"))
    async def cb_market_toggle(callback: CallbackQuery):
        try:
            item_id = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная позиция", show_alert=True)
            return
        new_state = toggle_market_item(callback.from_user.id, item_id)
        if new_state is None:
            await callback.answer("Позиция не найдена", show_alert=True)
            return
        await callback.answer("Позиция включена" if new_state else "Позиция выключена")
        await render_market_manage(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data.startswith("market_edit_price:"))
    async def cb_market_edit_price(callback: CallbackQuery, state: FSMContext):
        try:
            item_id = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная позиция", show_alert=True)
            return

        item = get_market_item(callback.from_user.id, item_id, active_only=False)
        if not item:
            await callback.answer("Позиция не найдена", show_alert=True)
            return

        icon = currency_icon(item.cost_currency)
        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await state.update_data(edit_item_id=item.id, edit_item_title=item.title, edit_item_currency=item.cost_currency)
        await state.set_state(SetupStates.waiting_market_edit_price)
        await send_temp(
            callback.message,
            callback.from_user.id,
            f"Новая цена для <b>{html.escape(item.title)}</b> (текущая {item.cost_points} {icon}):",
            parse_mode="HTML",
            reply_markup=market_cancel_kb(),
        )

    @dp.callback_query(F.data.startswith("market_edit_currency:"))
    async def cb_market_edit_currency(callback: CallbackQuery):
        try:
            item_id = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная позиция", show_alert=True)
            return

        item = get_market_item(callback.from_user.id, item_id, active_only=False)
        if not item:
            await callback.answer("Позиция не найдена", show_alert=True)
            return
        new_currency = "gold" if item.cost_currency == "silver" else "silver"
        if not update_market_item_currency(callback.from_user.id, item_id, new_currency):
            await callback.answer("Не удалось обновить валюту", show_alert=True)
            return
        await callback.answer(
            f"Валюта: {currency_icon(item.cost_currency)} -> {currency_icon(new_currency)}"
        )
        await render_market_manage(bot, callback.message, callback.from_user.id)

    @dp.message(SetupStates.waiting_market_edit_price)
    async def market_edit_price_step(message: Message, state: FSMContext):
        new_price = parse_positive_int(message.text or "")
        if not new_price:
            await send_temp(message, message.from_user.id, "Цена должна быть целым числом больше 0.")
            return

        data = await state.get_data()
        item_id = int(data.get("edit_item_id", 0))
        item_title = str(data.get("edit_item_title", "позиция"))
        item_currency = normalize_currency(str(data.get("edit_item_currency", "silver")))
        icon = currency_icon(item_currency)
        if item_id <= 0 or not update_market_item_price(message.from_user.id, item_id, new_price):
            await state.clear()
            await send_temp(message, message.from_user.id, "Не удалось обновить цену. Попробуй снова.")
            return

        await state.clear()
        await safe_delete(message)
        await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
        await send_temp(
            message,
            message.from_user.id,
            f"✅ Цена обновлена: <b>{html.escape(item_title)}</b> = {new_price} {icon}",
            parse_mode="HTML",
            reply_markup=market_main_kb(),
        )

    @dp.callback_query(F.data.startswith("market_delete_ask:"))
    async def cb_market_delete_ask(callback: CallbackQuery):
        try:
            item_id = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная позиция", show_alert=True)
            return

        item = get_market_item(callback.from_user.id, item_id, active_only=False)
        if not item:
            await callback.answer("Позиция не найдена", show_alert=True)
            return

        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            f"Удалить позицию <b>{html.escape(item.title)}</b>?",
            parse_mode="HTML",
            reply_markup=market_delete_confirm_kb(item.id),
        )

    @dp.callback_query(F.data.startswith("market_delete:"))
    async def cb_market_delete(callback: CallbackQuery):
        try:
            item_id = int(callback.data.split(":")[1])
        except (ValueError, IndexError):
            await callback.answer("Некорректная позиция", show_alert=True)
            return
        if not delete_market_item(callback.from_user.id, item_id):
            await callback.answer("Позиция не найдена", show_alert=True)
            return
        await callback.answer("Позиция удалена")
        await render_market_manage(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "market_history")
    async def cb_market_history(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            purchase_history_text(callback.from_user.id),
            parse_mode="HTML",
        )
        await send_temp(
            callback.message,
            callback.from_user.id,
            points_activity_text(callback.from_user.id),
            parse_mode="HTML",
            reply_markup=market_admin_kb(),
        )

    @dp.callback_query(F.data.in_({"game_settings", "market_economy"}))
    async def cb_market_economy(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            market_economy_text(callback.from_user.id),
            parse_mode="HTML",
            reply_markup=market_economy_kb(),
        )

    @dp.callback_query(F.data == "market_set_silver_rate")
    async def cb_market_set_silver_rate(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await state.set_state(SetupStates.waiting_silver_per_hour)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "Введи новый курс серебра за час (целое число, например 60).",
            reply_markup=market_cancel_kb(),
        )

    @dp.message(SetupStates.waiting_silver_per_hour)
    async def set_silver_per_hour_step(message: Message, state: FSMContext):
        value = parse_positive_int(message.text or "")
        if not value:
            await send_temp(message, message.from_user.id, "Нужно целое число больше 0.")
            return
        if value > 1000:
            await send_temp(message, message.from_user.id, "Слишком большое значение. Укажи до 1000.")
            return

        update_silver_per_hour(message.from_user.id, value)
        await state.clear()
        await safe_delete(message)
        await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
        await send_temp(
            message,
            message.from_user.id,
            f"✅ Курс серебра обновлён: {value} 🥈/ч",
            reply_markup=market_economy_kb(),
        )

    @dp.callback_query(F.data == "market_set_gold_rate")
    async def cb_market_set_gold_rate(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await state.set_state(SetupStates.waiting_gold_per_hour)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "Введи новый курс золота за час (целое число, например 4).",
            reply_markup=market_cancel_kb(),
        )

    @dp.message(SetupStates.waiting_gold_per_hour)
    async def set_gold_per_hour_step(message: Message, state: FSMContext):
        value = parse_positive_int(message.text or "")
        if not value:
            await send_temp(message, message.from_user.id, "Нужно целое число больше 0.")
            return
        if value > 1000:
            await send_temp(message, message.from_user.id, "Слишком большое значение. Укажи до 1000.")
            return

        update_gold_per_hour(message.from_user.id, value)
        await state.clear()
        await safe_delete(message)
        await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
        await send_temp(
            message,
            message.from_user.id,
            f"✅ Курс золота обновлён: {value} 🥇/ч",
            reply_markup=market_economy_kb(),
        )

    @dp.callback_query(F.data == "market_set_exchange_rate")
    async def cb_market_set_exchange_rate(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await state.set_state(SetupStates.waiting_gold_to_silver_rate)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "Введи курс обмена: сколько серебра даёт 1 золото (например 12).",
            reply_markup=market_cancel_kb(),
        )

    @dp.message(SetupStates.waiting_gold_to_silver_rate)
    async def set_gold_to_silver_rate_step(message: Message, state: FSMContext):
        value = parse_positive_int(message.text or "")
        if not value:
            await send_temp(message, message.from_user.id, "Нужно целое число больше 0.")
            return
        if value > 1000:
            await send_temp(message, message.from_user.id, "Слишком большое значение. Укажи до 1000.")
            return

        update_gold_to_silver_rate(message.from_user.id, value)
        await state.clear()
        await safe_delete(message)
        await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
        await send_temp(
            message,
            message.from_user.id,
            f"✅ Курс обмена обновлён: 1 🥇 = {value} 🥈",
            reply_markup=market_economy_kb(),
        )

    @dp.callback_query(F.data == "market_exchange_gold_silver")
    async def cb_market_exchange_gold_silver(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        profile = get_profile(callback.from_user.id)
        rate = profile.gold_to_silver_rate if profile else 12
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await state.set_state(SetupStates.waiting_exchange_gold_amount)
        await send_temp(
            callback.message,
            callback.from_user.id,
            (
                f"Текущий курс: 1 🥇 = {rate} 🥈\n"
                "Введи, сколько золота обменять в серебро (целое число)."
            ),
            reply_markup=market_cancel_kb(),
        )

    @dp.message(SetupStates.waiting_exchange_gold_amount)
    async def exchange_gold_amount_step(message: Message, state: FSMContext):
        amount = parse_positive_int(message.text or "")
        if not amount:
            await send_temp(message, message.from_user.id, "Нужно целое число больше 0.")
            return

        ok, payload, gold_balance, silver_balance = exchange_gold_to_silver(message.from_user.id, amount)
        if not ok:
            await send_temp(message, message.from_user.id, payload)
            return

        await state.clear()
        await safe_delete(message)
        await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
        await send_temp(
            message,
            message.from_user.id,
            (
                f"✅ {payload}\n"
                f"🥇 Новый баланс: {gold_balance}\n"
                f"🥈 Новый баланс: {silver_balance}"
            ),
            reply_markup=market_economy_kb(),
        )

    @dp.callback_query(F.data == "market_bonus_points")
    async def cb_market_bonus_points(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "Выбери валюту для ручной корректировки.",
            reply_markup=market_bonus_currency_kb(),
        )

    @dp.callback_query(F.data.startswith("market_bonus_currency:"))
    async def cb_market_bonus_currency(callback: CallbackQuery, state: FSMContext):
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            await callback.answer("Геймификация отключена", show_alert=True)
            return
        try:
            raw_currency = callback.data.split(":")[1]
        except (ValueError, IndexError):
            await callback.answer("Некорректная валюта", show_alert=True)
            return
        selected_currency = parse_market_currency(raw_currency)
        if not selected_currency:
            await callback.answer("Некорректная валюта", show_alert=True)
            return
        icon = currency_icon(selected_currency)
        currency_ru = currency_name_ru(selected_currency)
        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await state.update_data(bonus_currency=selected_currency)
        await state.set_state(SetupStates.waiting_bonus_points)
        await send_temp(
            callback.message,
            callback.from_user.id,
            f"Введи изменение для {currency_ru}. Примеры: `+30`, `-15` {icon}",
            parse_mode="Markdown",
            reply_markup=market_cancel_kb(),
        )

    @dp.message(SetupStates.waiting_bonus_points)
    async def set_bonus_points_step(message: Message, state: FSMContext):
        delta = parse_signed_int(message.text or "")
        if delta is None:
            await send_temp(message, message.from_user.id, "Неверный формат. Пример: +30 или -15.")
            return

        data = await state.get_data()
        currency = normalize_currency(str(data.get("bonus_currency", "silver")))
        icon = currency_icon(currency)
        currency_ru = currency_name_ru(currency)

        success, new_balance = apply_currency_transaction(
            message.from_user.id,
            delta,
            reason="manual_bonus",
            currency=currency,
            note="ручная корректировка",
            allow_negative=False,
        )
        if not success:
            await send_temp(message, message.from_user.id, f"Недостаточно {currency_ru} для списания.")
            return

        await state.clear()
        await safe_delete(message)
        await cleanup_temp_messages(bot, message.chat.id, message.from_user.id)
        delta_label = f"+{delta}" if delta > 0 else str(delta)
        await send_temp(
            message,
            message.from_user.id,
            f"✅ Баланс {currency_ru} изменён: {delta_label} {icon}\nТекущий баланс: {new_balance} {icon}",
            reply_markup=market_economy_kb(),
        )

    @dp.callback_query(F.data == "market_cancel")
    async def cb_market_cancel(callback: CallbackQuery, state: FSMContext):
        await callback.answer("Отменено")
        current_state = await state.get_state()
        await state.clear()
        bonus_states = {
            SetupStates.waiting_bonus_goal_value.state,
            SetupStates.waiting_bonus_goal_custom_deadline.state,
            SetupStates.waiting_bonus_goal_reward.state,
        }
        if current_state in bonus_states:
            await render_bonus_goals_home(bot, callback.message, callback.from_user.id)
            return
        if not await ensure_gamification_enabled(callback.message, state, callback.from_user.id):
            return
        await render_market_home(bot, callback.message, callback.from_user.id)

    @dp.callback_query(F.data == "settings")
    async def cb_settings(callback: CallbackQuery, state: FSMContext):
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        profile = get_profile(callback.from_user.id)
        enabled = profile.gamification_enabled if profile else True
        status = "включена" if enabled else "выключена"
        await send_temp(
            callback.message,
            callback.from_user.id,
            f"⚙️ Настройки\n🎮 Геймификация сейчас: <b>{status}</b>",
            parse_mode="HTML",
            reply_markup=settings_kb(enabled),
        )

    @dp.callback_query(F.data == "toggle_gamification")
    async def cb_toggle_gamification(callback: CallbackQuery, state: FSMContext):
        profile = get_profile(callback.from_user.id)
        if not profile:
            await callback.answer("Профиль не найден", show_alert=True)
            return
        new_value = not profile.gamification_enabled
        update_gamification_enabled(callback.from_user.id, new_value)
        await callback.answer("Геймификация включена" if new_value else "Геймификация отключена")
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        status = "включена" if new_value else "выключена"
        await send_temp(
            callback.message,
            callback.from_user.id,
            f"⚙️ Настройки\n🎮 Геймификация сейчас: <b>{status}</b>",
            parse_mode="HTML",
            reply_markup=settings_kb(new_value),
        )

    @dp.callback_query(F.data == "back_main")
    async def cb_back_main(callback: CallbackQuery, state: FSMContext):
        await callback.answer()
        await state.clear()
        await render_main(bot, callback.message.chat.id, callback.from_user.id)

    @dp.callback_query(F.data == "set_rate")
    async def cb_set_rate(callback: CallbackQuery, state: FSMContext):
        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await state.set_state(SetupStates.waiting_new_rate)
        await send_temp(callback.message, callback.from_user.id, "Введите новую ставку в рублях за час")

    @dp.message(SetupStates.waiting_new_rate)
    async def set_new_rate(message: Message, state: FSMContext):
        value = parse_money(message.text or "")
        if not value:
            await send_temp(message, message.from_user.id, "Ставка должна быть числом больше 0")
            return
        update_rate(message.from_user.id, value)
        await state.clear()
        await safe_delete(message)
        await render_main(bot, message.chat.id, message.from_user.id)

    @dp.callback_query(F.data == "set_goal")
    async def cb_set_goal(callback: CallbackQuery, state: FSMContext):
        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await state.set_state(SetupStates.waiting_new_goal)
        await send_temp(callback.message, callback.from_user.id, "Введите новую цель в рублях")

    @dp.message(SetupStates.waiting_new_goal)
    async def set_new_goal(message: Message, state: FSMContext):
        value = parse_money(message.text or "")
        if not value:
            await send_temp(message, message.from_user.id, "Цель должна быть числом больше 0")
            return
        update_goal(message.from_user.id, value)
        await state.clear()
        await safe_delete(message)
        await render_main(bot, message.chat.id, message.from_user.id)

    @dp.callback_query(F.data == "notifs")
    async def cb_notifs(callback: CallbackQuery, state: FSMContext):
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(callback.message, callback.from_user.id, "Выбери режим уведомлений", reply_markup=notif_kb())

    @dp.callback_query(F.data.in_({"notif_off", "notif_hourly", "notif_daily", "notif_weekly"}))
    async def cb_notif_mode(callback: CallbackQuery):
        mapping = {
            "notif_off": "off",
            "notif_hourly": "hourly",
            "notif_daily": "daily",
            "notif_weekly": "weekly",
        }
        labels = {
            "off": "Выключены",
            "hourly": "Каждый час",
            "daily": "Ежедневно",
            "weekly": "Раз в неделю",
        }
        mode = mapping[callback.data]
        update_notification_mode(callback.from_user.id, mode)
        await callback.answer("Сохранено")
        await send_temp(callback.message, callback.from_user.id, f"Уведомления: {labels[mode]}")

    @dp.callback_query(F.data == "reset_progress")
    async def cb_reset_progress(callback: CallbackQuery):
        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(callback.message, callback.from_user.id, "Как сбросить прогресс?", reply_markup=reset_kb())

    @dp.callback_query(F.data == "reset_keep_goal")
    async def cb_reset_keep_goal(callback: CallbackQuery):
        await callback.answer()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "Подтвердите: сбросить прогресс, но оставить цель?",
            reply_markup=confirm_reset_kb(keep_goal=True),
        )

    @dp.callback_query(F.data == "reset_drop_goal")
    async def cb_reset_drop_goal(callback: CallbackQuery, state: FSMContext):
        await callback.answer()
        await state.clear()
        await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
        await send_temp(
            callback.message,
            callback.from_user.id,
            "Подтвердите: сбросить прогресс и удалить цель?",
            reply_markup=confirm_reset_kb(keep_goal=False),
        )

    @dp.callback_query(F.data == "cancel_add")
    async def cb_cancel_add(callback: CallbackQuery):
        await callback.answer("Отменено")
        await render_main(bot, callback.message.chat.id, callback.from_user.id)

    @dp.callback_query(F.data.startswith("confirm_add:"))
    async def cb_confirm_add(callback: CallbackQuery):
        try:
            _, seconds_str, source = callback.data.split(":")
            seconds = int(seconds_str)
        except (ValueError, AttributeError):
            await callback.answer("Ошибка данных", show_alert=True)
            return

        session_id = add_session(
            callback.from_user.id,
            seconds,
            source,
            "Подтверждено пользователем",
        )
        silver_earned, gold_earned = award_currencies_for_session(callback.from_user.id, seconds, source, session_id)
        profile = get_profile(callback.from_user.id)
        gamification_enabled = profile.gamification_enabled if profile else True
        discipline_events: list[str] = []
        bonus_events: list[str] = []
        if gamification_enabled:
            discipline_events = register_activity_day(callback.from_user.id)
            bonus_events = evaluate_bonus_goals(callback.from_user.id)
        if silver_earned > 0 or gold_earned > 0:
            await callback.answer(f"Добавлено: +{silver_earned} 🥈 и +{gold_earned} 🥇")
        else:
            await callback.answer("Время добавлено")
        await render_main(bot, callback.message.chat.id, callback.from_user.id)
        all_events = discipline_events + bonus_events
        if all_events:
            await send_temp(
                callback.message,
                callback.from_user.id,
                "\n\n".join(all_events),
                parse_mode="HTML",
            )

    @dp.callback_query(F.data.startswith("confirm_reset:"))
    async def cb_confirm_reset(callback: CallbackQuery, state: FSMContext):
        await callback.answer()
        action = callback.data.split(":")[1]
        if action == "keep":
            clear_progress(callback.from_user.id, keep_goal=True)
            await render_main(bot, callback.message.chat.id, callback.from_user.id)
            return

        if action == "drop":
            clear_progress(callback.from_user.id, keep_goal=False)
            await cleanup_temp_messages(bot, callback.message.chat.id, callback.from_user.id)
            await state.set_state(SetupStates.waiting_goal)
            await send_temp(callback.message, callback.from_user.id, "Прогресс и цель удалены. Введи новую цель в рублях.")
            return

    async def _flush_forwarded_batch(user_id: int):
        try:
            await asyncio.sleep(FORWARDED_BATCH_DELAY)
        except asyncio.CancelledError:
            return
        batch = _forwarded_batches.pop(user_id, None)
        if not batch or not batch["entries"]:
            return
        entries = batch["entries"]
        message = batch["message"]
        total = sum(sec for sec, _ in entries)
        profile = get_profile(user_id)
        rate = profile.rate_per_hour if profile else 0
        added_money = (total / 3600) * rate
        added_silver = calculate_session_currency(total, profile.silver_per_hour if profile else 0)
        added_gold = calculate_session_currency(total, profile.gold_per_hour if profile else 0)
        if len(entries) == 1:
            text = (
                f"Распознано из пересланного: {fmt_duration(total)} ({fmt_money(added_money)} ₽)\n"
                f"🥈 Начислится: +{added_silver}\n"
                f"🥇 Начислится: +{added_gold}\n"
                "Добавляем?"
            )
        else:
            lines = "\n".join(
                f"  {idx}) {label} — {fmt_duration(sec)}"
                for idx, (sec, label) in enumerate(entries, start=1)
            )
            text = (
                f"📥 Найдено пересланных таймеров: {len(entries)}\n"
                f"{lines}\n\n"
                f"🧮 Суммарно: {fmt_duration(total)} ({fmt_money(added_money)} ₽)\n"
                f"🥈 Начислится: +{added_silver}\n"
                f"🥇 Начислится: +{added_gold}\n"
                "Добавляем всё одной записью?"
            )
        await send_temp(
            message,
            user_id,
            text,
            reply_markup=confirm_add_kb(total, "forwarded"),
        )

    @dp.message(F.text)
    async def parse_forwarded(message: Message, state: FSMContext):
        if re.fullmatch(r"\s*🎰\ufe0f?\s*", message.text or ""):
            return
        text = message.text or ""
        seconds = parse_forwarded_timer(text)
        if seconds:
            if await ensure_setup(message, state):
                return
            label = parse_forwarded_timer_label(text)
            await safe_delete(message)
            user_id = message.from_user.id
            batch = _forwarded_batches.get(user_id)
            if batch is None:
                batch = {"entries": [], "message": message, "task": None}
                _forwarded_batches[user_id] = batch
            else:
                batch["message"] = message
                if batch["task"]:
                    batch["task"].cancel()
            batch["entries"].append((seconds, label))
            batch["task"] = asyncio.create_task(_flush_forwarded_batch(user_id))
            return

        profile = get_profile(message.from_user.id)
        if not profile:
            await ensure_setup(message, state)

    return dp


async def main() -> None:
    logging.basicConfig(level=logging.INFO)
    load_dotenv()
    init_db()

    token = os.getenv("BOT_TOKEN", "")
    if not token:
        raise RuntimeError("Set BOT_TOKEN in .env file")

    bot = Bot(token=token)
    await bot.set_my_commands([BotCommand(command="start", description="Меню")])
    await bot.set_chat_menu_button(menu_button=MenuButtonCommands(text="Меню"))
    dp = build_dispatcher(bot)

    notification_task = asyncio.create_task(run_notification_loop(bot))
    try:
        await dp.start_polling(bot)
    finally:
        notification_task.cancel()


if __name__ == "__main__":
    asyncio.run(main())
