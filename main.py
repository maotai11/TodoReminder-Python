# -*- coding: utf-8 -*-
"""
TodoReminder v3.1  -  離線桌面待辦提醒系統
==========================================
功能：
  - 浮動常駐板：拖曳 / 滾輪=透明度 / [釘選] 切換置頂
  - 分類顯示：逾期 / 今天 / 明天 / 未來 / 無截止日 / 已完成
  - 截止日期（月曆選單）/ 提醒時間（鬧鐘選時分）
  - 備註 / 分類標籤 / 重複規則 / 子任務
  - 提醒貪睡（5 / 15 / 30 分）
  - 即時搜尋 + 分類篩選
  - 匯出 TXT / 自動備份（無變動跳過）/ 手動備份
  - 視窗位置與透明度跨次記憶
"""

import calendar
import ctypes
import hashlib
import json
import os
import re
import shutil
import sys
import threading
import time
import tkinter as tk
from datetime import datetime, date, timedelta
from tkinter import filedialog, messagebox, simpledialog

try:
    import pystray
    from PIL import Image, ImageDraw
    HAS_TRAY = True
except ImportError:
    HAS_TRAY = False

# ============================================================
# 常數
# ============================================================

APP_NAME   = '待辦提醒'
APP_VER    = '3.1.0'
MUTEX_NAME = 'TodoReminderApp_SingleInstance_Mutex'

# 顏色（全部 6 字元 hex）
C_BG      = '#1A1A2E'
C_HEADER  = '#E94560'
C_FOOTER  = '#16213E'
C_FG      = '#E8E8E8'
C_DONE    = '#666666'
C_REMIND  = '#FFCC44'
C_ALERT   = '#CC2200'
C_MGRHDR  = '#0F3460'
C_HOVER   = '#252545'
C_SUB     = '#1E1E38'
C_OVERDUE = '#FF4444'
C_TODAY   = '#E94560'
C_TMRW    = '#27AE60'
C_FUTURE  = '#4477AA'
C_NODATE  = '#777799'
C_DONE_S  = '#444455'

# 字型
F_MAIN  = ('Microsoft YaHei', 10)
F_HEAD  = ('Microsoft YaHei', 11, 'bold')
F_SMALL = ('Microsoft YaHei', 8)
F_SEC   = ('Microsoft YaHei', 9, 'bold')
F_BTN   = ('Microsoft YaHei', 10)
F_BIG   = ('Microsoft YaHei', 28, 'bold')

# 佈局
WIN_W     = 300
WIN_W_MGR = 480
HEADER_H  = 36
FOOTER_H  = 62
MIN_H     = 140
MAX_H     = 600
SORTBAR_H = 26

# 區段鍵值（用於折疊狀態）
SEC_KEYS = ('overdue', 'today', 'tomorrow', 'dayafter', 'future', 'nodate', 'done')

WEEKDAY_NAMES = ('一', '二', '三', '四', '五', '六', '日')

# ============================================================
# 路徑
# ============================================================

def _app_dir() -> str:
    if getattr(sys, 'frozen', False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))

APP_DIR       = _app_dir()
DATA_DIR      = os.path.join(APP_DIR, 'data')
TODOS_FILE    = os.path.join(DATA_DIR, 'todos.json')
SETTINGS_FILE = os.path.join(DATA_DIR, 'settings.json')
BACKUP_DIR    = os.path.join(DATA_DIR, 'backups')

# ============================================================
# 單一實例
# ============================================================

_mutex_handle = None

def _acquire_mutex() -> bool:
    global _mutex_handle
    _mutex_handle = ctypes.windll.kernel32.CreateMutexW(None, False, MUTEX_NAME)
    return ctypes.windll.kernel32.GetLastError() != 183

# ============================================================
# 設定
# ============================================================

class Settings:
    DEFAULTS = {
        'backup_time':        '23:00',
        'backup_keep_days':   30,
        'always_on_top':      True,
        'widget_x':           60,
        'widget_y':           100,
        'widget_alpha':       0.88,
        'collapsed_sections': ['done'],   # 預設收起已完成
    }

    def __init__(self):
        self._d = dict(self.DEFAULTS)
        os.makedirs(DATA_DIR, exist_ok=True)
        self._load()

    def _load(self):
        if not os.path.exists(SETTINGS_FILE):
            return
        try:
            with open(SETTINGS_FILE, 'r', encoding='utf-8') as f:
                self._d.update(json.load(f))
        except Exception:
            pass

    def save(self):
        with open(SETTINGS_FILE, 'w', encoding='utf-8') as f:
            json.dump(self._d, f, ensure_ascii=False, indent=2)

    def get(self, key):
        return self._d.get(key, self.DEFAULTS.get(key))

    def set(self, key, value):
        self._d[key] = value
        self.save()

# ============================================================
# 日曆選單
# ============================================================

class DatePicker(tk.Toplevel):
    """
    月曆彈出選單。
    用法：
        dp = DatePicker(parent, initial='2026-03-15')
        parent.wait_window(dp)
        result = dp.result  # "YYYY-MM-DD" 或 None（清除）
    """

    def __init__(self, parent, title='選擇截止日期', initial: str | None = None):
        super().__init__(parent)
        self.title(title)
        self.result: str | None = None
        self.resizable(False, False)
        self.attributes('-topmost', True)
        self.transient(parent)
        self.grab_set()

        today = date.today()
        self._today = today

        if initial:
            try:
                d = date.fromisoformat(initial)
                self._year, self._month = d.year, d.month
                self._selected: date | None = d
            except ValueError:
                self._year, self._month = today.year, today.month
                self._selected = None
        else:
            self._year, self._month = today.year, today.month
            self._selected = None

        self._build()
        self._center(parent)

    def _center(self, parent):
        self.update_idletasks()
        x = parent.winfo_rootx() + max(0, (parent.winfo_width()  - self.winfo_width())  // 2)
        y = parent.winfo_rooty() + max(0, (parent.winfo_height() - self.winfo_height()) // 2)
        self.geometry(f'+{x}+{y}')

    def _build(self):
        self.configure(bg=C_BG)

        # 導覽列
        nav = tk.Frame(self, bg=C_MGRHDR)
        nav.pack(fill='x')

        prev_btn = tk.Label(nav, text='  <  ', bg=C_MGRHDR, fg='white',
                            font=F_BTN, cursor='hand2')
        prev_btn.pack(side='left')
        prev_btn.bind('<Button-1>', lambda _e: self._prev_month())

        self._nav_lbl = tk.Label(nav, text='', bg=C_MGRHDR, fg='white',
                                 font=F_HEAD, width=14)
        self._nav_lbl.pack(side='left', fill='x', expand=True)

        next_btn = tk.Label(nav, text='  >  ', bg=C_MGRHDR, fg='white',
                            font=F_BTN, cursor='hand2')
        next_btn.pack(side='right')
        next_btn.bind('<Button-1>', lambda _e: self._next_month())

        # 星期標題
        dh = tk.Frame(self, bg=C_BG)
        dh.pack(fill='x', padx=6, pady=(6, 0))
        for i, name in enumerate(WEEKDAY_NAMES):
            fg = '#888888' if i < 5 else C_HEADER
            tk.Label(dh, text=name, bg=C_BG, fg=fg,
                     font=F_SMALL, width=4).pack(side='left')

        # 日曆格
        self._grid = tk.Frame(self, bg=C_BG)
        self._grid.pack(padx=6, pady=4)

        # 底部按鈕
        bf = tk.Frame(self, bg=C_FOOTER)
        bf.pack(fill='x')

        today_btn = tk.Label(bf, text=' 今天 ', bg='#16A085', fg='white',
                             font=F_SMALL, cursor='hand2', padx=8, pady=4)
        today_btn.pack(side='left', padx=6, pady=4)
        today_btn.bind('<Button-1>', lambda _e: self._select(self._today))

        cancel_btn = tk.Label(bf, text=' 取消 ', bg='#555555', fg='white',
                              font=F_SMALL, cursor='hand2', padx=8, pady=4)
        cancel_btn.pack(side='right', padx=6, pady=4)
        cancel_btn.bind('<Button-1>', lambda _e: self.destroy())

        clear_btn = tk.Label(bf, text=' 清除日期 ', bg='#7D3C00', fg='white',
                             font=F_SMALL, cursor='hand2', padx=8, pady=4)
        clear_btn.pack(side='right', padx=2, pady=4)
        clear_btn.bind('<Button-1>', lambda _e: self._clear())

        self._draw()

    def _draw(self):
        for ch in self._grid.winfo_children():
            ch.destroy()

        self._nav_lbl.configure(
            text=f'{self._year} 年 {self._month:02d} 月')

        weeks = calendar.monthcalendar(self._year, self._month)
        for week in weeks:
            row = tk.Frame(self._grid, bg=C_BG)
            row.pack()
            for day_num in week:
                if day_num == 0:
                    tk.Label(row, text='  ', bg=C_BG,
                             width=4, font=F_SMALL).pack(side='left')
                    continue
                d = date(self._year, self._month, day_num)
                is_sel   = (d == self._selected)
                is_today = (d == self._today)
                is_past  = (d < self._today)

                if is_sel:
                    bg, fg = C_HEADER, 'white'
                elif is_today:
                    bg, fg = '#16A085', 'white'
                elif is_past:
                    bg, fg = C_BG, '#555555'
                else:
                    bg, fg = C_BG, C_FG

                lbl = tk.Label(row, text=str(day_num),
                               bg=bg, fg=fg, font=F_SMALL,
                               width=4, cursor='hand2', pady=3)
                lbl.pack(side='left')
                lbl.bind('<Button-1>',
                         lambda _e, dd=d: self._select(dd))
                if not is_sel:
                    lbl.bind('<Enter>',
                             lambda _e, l=lbl: l.configure(bg='#333355'))
                    lbl.bind('<Leave>',
                             lambda _e, l=lbl, ob=bg: l.configure(bg=ob))

    def _select(self, d: date):
        self.result = d.strftime('%Y-%m-%d')
        self.destroy()

    def _clear(self):
        self.result = None
        self.destroy()

    def _prev_month(self):
        if self._month == 1:
            self._month, self._year = 12, self._year - 1
        else:
            self._month -= 1
        self._draw()

    def _next_month(self):
        if self._month == 12:
            self._month, self._year = 1, self._year + 1
        else:
            self._month += 1
        self._draw()

# ============================================================
# 時間選單（鬧鐘樣式）
# ============================================================

class TimePicker(tk.Toplevel):
    """
    鬧鐘樣式時間選單。
    用法：
        tp = TimePicker(parent, initial='09:00')
        parent.wait_window(tp)
        result = tp.result  # "HH:MM" 或 None
    """

    def __init__(self, parent, title='設定提醒時間', initial: str | None = None):
        super().__init__(parent)
        self.title(title)
        self.result: str | None = None
        self.resizable(False, False)
        self.attributes('-topmost', True)
        self.transient(parent)
        self.grab_set()

        now = datetime.now()
        self._h = now.hour
        self._m = (now.minute // 5) * 5

        if initial:
            try:
                parts = initial.split(':')
                self._h = int(parts[0])
                self._m = int(parts[1])
            except Exception:
                pass

        self._h_var = tk.StringVar(value=f'{self._h:02d}')
        self._m_var = tk.StringVar(value=f'{self._m:02d}')

        self._build()
        self._center(parent)

    def _center(self, parent):
        self.update_idletasks()
        x = parent.winfo_rootx() + max(0, (parent.winfo_width()  - self.winfo_width())  // 2)
        y = parent.winfo_rooty() + max(0, (parent.winfo_height() - self.winfo_height()) // 2)
        self.geometry(f'+{x}+{y}')

    def _set_h(self, delta: int):
        self._h = (self._h + delta) % 24
        self._h_var.set(f'{self._h:02d}')

    def _set_m(self, delta: int):
        self._m = (self._m + delta) % 60
        self._m_var.set(f'{self._m:02d}')

    def _build(self):
        self.configure(bg=C_BG)

        # 標題
        hf = tk.Frame(self, bg=C_MGRHDR)
        hf.pack(fill='x')
        tk.Label(hf, text='  設定提醒時間',
                 bg=C_MGRHDR, fg='white', font=F_HEAD, pady=7
                 ).pack(side='left', padx=8)

        # 時/分 選擇區
        body = tk.Frame(self, bg=C_BG, pady=10)
        body.pack()

        def _spinner(parent, var, inc_cmd, dec_cmd, wheel_cmd, label_txt):
            col = tk.Frame(parent, bg=C_BG)
            col.pack(side='left', padx=24)

            up = tk.Label(col, text='  +  ', bg='#333355', fg=C_FG,
                          font=F_BTN, cursor='hand2', pady=2)
            up.pack()
            up.bind('<Button-1>', lambda _e: inc_cmd())

            disp = tk.Label(col, textvariable=var,
                            bg=C_BG, fg=C_FG, font=F_BIG, width=3)
            disp.pack()
            disp.bind('<MouseWheel>',
                      lambda e: wheel_cmd(1 if e.delta > 0 else -1))

            dn = tk.Label(col, text='  -  ', bg='#333355', fg=C_FG,
                          font=F_BTN, cursor='hand2', pady=2)
            dn.pack()
            dn.bind('<Button-1>', lambda _e: dec_cmd())

            tk.Label(col, text=label_txt, bg=C_BG, fg='#AAAAAA',
                     font=F_SMALL).pack(pady=(4, 0))
            return col

        _spinner(body, self._h_var,
                 lambda: self._set_h(+1), lambda: self._set_h(-1),
                 self._set_h, '時')

        tk.Label(body, text=':', bg=C_BG, fg=C_FG,
                 font=F_BIG, pady=10).pack(side='left')

        _spinner(body, self._m_var,
                 lambda: self._set_m(+5), lambda: self._set_m(-5),
                 lambda d: self._set_m(d * 5), '分')

        # 快捷按鈕列
        presets = tk.Frame(self, bg=C_BG)
        presets.pack(pady=(0, 4))

        now_btn = tk.Label(presets, text=' 目前時間 ', bg='#333355', fg='#CCCCCC',
                           font=F_SMALL, cursor='hand2', padx=8, pady=3)
        now_btn.pack(side='left', padx=3)
        now_btn.bind('<Button-1>', lambda _e: self._set_now())

        for hh, mm in ((8, 0), (9, 0), (12, 0), (17, 30), (18, 0)):
            lbl = tk.Label(presets, text=f'{hh:02d}:{mm:02d}',
                           bg='#222244', fg='#AAAAAA',
                           font=F_SMALL, cursor='hand2', padx=6, pady=3)
            lbl.pack(side='left', padx=2)
            lbl.bind('<Button-1>',
                     lambda _e, h=hh, m=mm: (self._set_h(h - self._h),
                                              self._set_m(m - self._m)))

        # 底部按鈕
        bf = tk.Frame(self, bg=C_FOOTER)
        bf.pack(fill='x')

        ok_btn = tk.Label(bf, text=' 確認 ', bg=C_HEADER, fg='white',
                          font=F_BTN, cursor='hand2', padx=12, pady=5)
        ok_btn.pack(side='left', padx=8, pady=6)
        ok_btn.bind('<Button-1>', lambda _e: self._ok())

        clear_btn = tk.Label(bf, text=' 清除提醒 ', bg='#7D3C00', fg='white',
                             font=F_BTN, cursor='hand2', padx=8, pady=5)
        clear_btn.pack(side='right', padx=4, pady=6)
        clear_btn.bind('<Button-1>', lambda _e: self._clear_result())

        cancel_btn = tk.Label(bf, text=' 取消 ', bg='#555555', fg='white',
                              font=F_BTN, cursor='hand2', padx=12, pady=5)
        cancel_btn.pack(side='right', padx=4, pady=6)
        cancel_btn.bind('<Button-1>', lambda _e: self.destroy())

    def _set_now(self):
        now = datetime.now()
        diff_h = now.hour - self._h
        diff_m = ((now.minute // 5) * 5) - self._m
        self._set_h(diff_h)
        self._set_m(diff_m)

    def _ok(self):
        self.result = f'{self._h:02d}:{self._m:02d}'
        self.destroy()

    def _clear_result(self):
        self.result = None
        self.destroy()

# ============================================================
# 重複規則選單
# ============================================================

# ============================================================
# 重複規則工具函式
# ============================================================

def _parse_recurrence(rec_str: str) -> dict:
    """將重複規則字串解析為 dict。
    格式: "daily:count=3" / "weekly:0,2:until=2025-03-01" / "monthly:15:count=3"
    回傳: {interval, days, dom, until, count}
    """
    if not rec_str:
        return {}
    parts = rec_str.split(':')
    r: dict = {'interval': parts[0], 'days': [], 'dom': None, 'until': None, 'count': None}
    for p in parts[1:]:
        if p.startswith('until='):
            r['until'] = p[6:]
        elif p.startswith('count='):
            try:
                r['count'] = int(p[6:])
            except ValueError:
                pass
        elif r['interval'] == 'weekly':
            try:
                r['days'] = [int(d) for d in p.split(',') if d.strip().isdigit()]
            except ValueError:
                pass
        elif r['interval'] == 'monthly':
            try:
                r['dom'] = int(p)
            except ValueError:
                pass
    return r


def _generate_occurrence_dates(due_date_str: str, rec_str: str) -> list:
    """依重複規則從 due_date_str 起產生所有日期（含第一天）。
    無結束條件（舊格式）→ 只回傳 [base]，不預產。
    """
    try:
        base = date.fromisoformat(due_date_str)
    except (ValueError, TypeError):
        return []
    r = _parse_recurrence(rec_str)
    if not r:
        return [base]

    interval = r['interval']
    until    = date.fromisoformat(r['until']) if r['until'] else None
    count    = r['count']
    MAX_OCC  = 365

    if not count and not until:
        # 無結束條件 = 視為單次，不預產
        return [base]

    dates: list = []

    if interval == 'daily':
        cur = base
        while True:
            dates.append(cur)
            if count and len(dates) >= count:
                break
            cur += timedelta(days=1)
            if until and cur > until:
                break
            if len(dates) >= MAX_OCC:
                break

    elif interval == 'weekly':
        days = r['days'] or [base.weekday()]
        dates = [base]
        cur = base + timedelta(days=1)
        end = until or (base + timedelta(days=365 * 2))
        while cur <= end and len(dates) < MAX_OCC:
            if cur.weekday() in days:
                dates.append(cur)
                if count and len(dates) >= count:
                    break
            cur += timedelta(days=1)

    elif interval == 'monthly':
        dom = r['dom'] or base.day
        dates = [base]
        y, m = base.year, base.month
        for _ in range(MAX_OCC):
            m += 1
            if m > 12:
                m, y = 1, y + 1
            try:
                d = date(y, m, dom)
            except ValueError:
                import calendar as _cal
                d = date(y, m, _cal.monthrange(y, m)[1])
            if until and d > until:
                break
            dates.append(d)
            if count and len(dates) >= count:
                break

    return dates


class RecurrencePicker(tk.Toplevel):
    """
    重複規則選單（每天 / 每週 / 每月）。
    用法：
        rp = RecurrencePicker(parent, initial='weekly:0,2')
        parent.wait_window(rp)
        result = rp.result  # "daily"/"weekly:0,2"/"monthly:15" 或 None
    """

    def __init__(self, parent, initial: str | None = None):
        super().__init__(parent)
        self.title('設定重複規則')
        self.result: str | None = None
        self.resizable(False, False)
        self.attributes('-topmost', True)
        self.transient(parent)
        self.grab_set()

        self._mode        = tk.StringVar(value='daily')
        self._weekdays    = [tk.BooleanVar() for _ in range(7)]
        self._monthly_day = tk.StringVar(value='1')
        self._end_mode    = tk.StringVar(value='count')
        self._count_var   = tk.StringVar(value='2')
        self._until_date: str | None = None
        self._until_lbl_var = tk.StringVar(value='選擇日期')

        if initial:
            r = _parse_recurrence(initial)
            iv = r.get('interval', 'daily')
            if iv == 'weekly':
                self._mode.set('weekly')
                for d in (r.get('days') or []):
                    if 0 <= d < 7:
                        self._weekdays[d].set(True)
            elif iv == 'monthly':
                self._mode.set('monthly')
                if r.get('dom'):
                    self._monthly_day.set(str(r['dom']))
            else:
                self._mode.set('daily')

            if r.get('until'):
                self._end_mode.set('until')
                self._until_date = r['until']
                self._until_lbl_var.set(r['until'])
            elif r.get('count'):
                self._end_mode.set('count')
                self._count_var.set(str(r['count']))

        self._build()
        self._center(parent)

    def _center(self, parent):
        self.update_idletasks()
        x = parent.winfo_rootx() + max(0, (parent.winfo_width()  - self.winfo_width())  // 2)
        y = parent.winfo_rooty() + max(0, (parent.winfo_height() - self.winfo_height()) // 2)
        self.geometry(f'+{x}+{y}')

    def _build(self):
        self.configure(bg=C_BG)

        hf = tk.Frame(self, bg=C_MGRHDR)
        hf.pack(fill='x')
        tk.Label(hf, text='  設定重複規則',
                 bg=C_MGRHDR, fg='white', font=F_HEAD, pady=7
                 ).pack(side='left', padx=8)

        body = tk.Frame(self, bg=C_BG, padx=20, pady=10)
        body.pack(fill='x')

        rb_kw = dict(bg=C_BG, fg=C_FG, selectcolor='#333355',
                     activebackground=C_BG, font=F_MAIN)

        tk.Radiobutton(body, text='每天', variable=self._mode,
                       value='daily', **rb_kw).pack(anchor='w', pady=3)

        tk.Radiobutton(body, text='每週（勾選星期）', variable=self._mode,
                       value='weekly', **rb_kw).pack(anchor='w', pady=3)

        wd_row = tk.Frame(body, bg=C_BG)
        wd_row.pack(anchor='w', padx=22)
        for i, name in enumerate(WEEKDAY_NAMES):
            fg = C_FG if i < 5 else C_HEADER
            tk.Checkbutton(wd_row, text=name, variable=self._weekdays[i],
                           bg=C_BG, fg=fg, selectcolor='#333355',
                           activebackground=C_BG, font=F_SMALL
                           ).pack(side='left', padx=3)

        tk.Radiobutton(body, text='每月（選擇日期）', variable=self._mode,
                       value='monthly', **rb_kw).pack(anchor='w', pady=(10, 3))

        mf = tk.Frame(body, bg=C_BG)
        mf.pack(anchor='w', padx=22)
        tk.Label(mf, text='每月第', bg=C_BG, fg=C_FG,
                 font=F_MAIN).pack(side='left')
        tk.Spinbox(mf, from_=1, to=31, textvariable=self._monthly_day,
                   width=4, bg='#252545', fg=C_FG,
                   buttonbackground='#333355',
                   font=F_MAIN, relief='flat').pack(side='left', padx=4)
        tk.Label(mf, text='天', bg=C_BG, fg=C_FG,
                 font=F_MAIN).pack(side='left')

        # ---- 結束條件 ----
        tk.Frame(body, bg='#333355', height=1).pack(fill='x', pady=(14, 6))
        tk.Label(body, text='結束條件', bg=C_BG, fg='#888888',
                 font=F_SMALL).pack(anchor='w')

        until_row = tk.Frame(body, bg=C_BG)
        until_row.pack(anchor='w', pady=2)
        tk.Radiobutton(until_row, text='直到某日', variable=self._end_mode,
                       value='until', **rb_kw).pack(side='left')
        self._until_btn = tk.Label(until_row, textvariable=self._until_lbl_var,
                                   bg='#333355', fg='#CCCCCC', font=F_SMALL,
                                   cursor='hand2', padx=8, pady=2)
        self._until_btn.pack(side='left', padx=6)
        self._until_btn.bind('<Button-1>', lambda _e: self._pick_until())

        count_row = tk.Frame(body, bg=C_BG)
        count_row.pack(anchor='w', pady=2)
        tk.Radiobutton(count_row, text='共', variable=self._end_mode,
                       value='count', **rb_kw).pack(side='left')
        tk.Spinbox(count_row, from_=1, to=99, textvariable=self._count_var,
                   width=4, bg='#252545', fg=C_FG,
                   buttonbackground='#333355',
                   font=F_MAIN, relief='flat').pack(side='left', padx=4)
        tk.Label(count_row, text='次', bg=C_BG, fg=C_FG,
                 font=F_MAIN).pack(side='left')

        bf = tk.Frame(self, bg=C_FOOTER)
        bf.pack(fill='x')

        ok_btn = tk.Label(bf, text=' 確認 ', bg=C_HEADER, fg='white',
                          font=F_BTN, cursor='hand2', padx=12, pady=5)
        ok_btn.pack(side='left', padx=8, pady=6)
        ok_btn.bind('<Button-1>', lambda _e: self._ok())

        cancel_btn = tk.Label(bf, text=' 取消 ', bg='#555555', fg='white',
                              font=F_BTN, cursor='hand2', padx=12, pady=5)
        cancel_btn.pack(side='right', padx=8, pady=6)
        cancel_btn.bind('<Button-1>', lambda _e: self.destroy())

    def _pick_until(self):
        self._end_mode.set('until')
        dp = DatePicker(self, initial=self._until_date)
        self.wait_window(dp)
        if dp.result:
            self._until_date = dp.result
            self._until_lbl_var.set(dp.result)

    def _ok(self):
        mode = self._mode.get()
        if mode == 'daily':
            base = 'daily'
        elif mode == 'weekly':
            sel = [str(i) for i, v in enumerate(self._weekdays) if v.get()]
            base = f'weekly:{",".join(sel)}' if sel else 'daily'
        elif mode == 'monthly':
            try:
                day = int(self._monthly_day.get())
                base = f'monthly:{day}' if 1 <= day <= 31 else 'daily'
            except ValueError:
                base = 'daily'
        else:
            base = 'daily'

        end = self._end_mode.get()
        if end == 'until' and self._until_date:
            self.result = f'{base}:until={self._until_date}'
        else:
            try:
                n = max(1, int(self._count_var.get()))
            except ValueError:
                n = 1
            self.result = f'{base}:count={n}'
        self.destroy()

# ============================================================
# 輔助：重複規則顯示文字
# ============================================================

def _fmt_recurrence(rec: str | None) -> str:
    if not rec:
        return ''
    r = _parse_recurrence(rec)
    iv = r.get('interval', 'daily')
    if iv == 'daily':
        s = '每天'
    elif iv == 'weekly':
        days = r.get('days') or []
        s = '每週' + '、'.join(WEEKDAY_NAMES[d] for d in days if d < 7) if days else '每週'
    elif iv == 'monthly':
        dom = r.get('dom')
        s = f'每月{dom}日' if dom else '每月'
    else:
        s = rec
    if r.get('until'):
        s += f'（到{r["until"][5:]}）'   # 顯示 MM-DD
    elif r.get('count') and r['count'] > 1:
        s += f'（共{r["count"]}次）'
    return s

# ============================================================
# 資料模型
# ============================================================

class Todo:
    def __init__(self, id: int, title: str,
                 done: bool = False,
                 reminder: str | None = None,
                 due_date: str | None = None,
                 start_time: str | None = None,
                 done_at: str | None = None,
                 notes: str | None = None,
                 category: str | None = None,
                 recurrence: str | None = None,
                 parent_id: int | None = None,
                 snooze_until: str | None = None):
        self.id           = id
        self.title        = title
        self.done         = done
        self.reminder     = reminder
        self.due_date     = due_date
        self.start_time   = start_time
        self.done_at      = done_at
        self.notes        = notes
        self.category     = category
        self.recurrence   = recurrence
        self.parent_id    = parent_id
        self.snooze_until = snooze_until

    def to_dict(self) -> dict:
        return {k: getattr(self, k) for k in (
            'id', 'title', 'done', 'reminder', 'due_date', 'start_time',
            'done_at', 'notes', 'category', 'recurrence', 'parent_id',
            'snooze_until')}

    @staticmethod
    def from_dict(d: dict) -> 'Todo':
        return Todo(
            d['id'], d['title'],
            d.get('done', False), d.get('reminder'), d.get('due_date'),
            d.get('start_time'), d.get('done_at'), d.get('notes'),
            d.get('category'), d.get('recurrence'), d.get('parent_id'),
            d.get('snooze_until'))

    def category_key(self) -> str:
        if self.done:
            return 'done'
        if not self.due_date:
            return 'nodate'
        today = date.today()
        try:
            dd = date.fromisoformat(self.due_date)
        except ValueError:
            return 'nodate'
        if dd < today:   return 'overdue'
        if dd == today:  return 'today'
        if dd == today + timedelta(days=1): return 'tomorrow'
        if dd == today + timedelta(days=2): return 'dayafter'
        return 'future'

    def should_remind(self, now: datetime) -> bool:
        if self.done or not self.reminder:
            return False
        if self.snooze_until:
            try:
                if now < datetime.strptime(self.snooze_until, '%Y-%m-%d %H:%M'):
                    return False
            except ValueError:
                pass
        if now.strftime('%H:%M') != self.reminder:
            return False
        # 有截止日 → 只在當天提醒
        if self.due_date:
            try:
                return date.fromisoformat(self.due_date) == now.date()
            except ValueError:
                pass
        # 無截止日 → 舊版重複規則邏輯（向下相容）
        rec = self.recurrence or 'daily'
        if rec == 'daily':
            return True
        if rec.startswith('weekly:'):
            try:
                return now.weekday() in [int(x) for x in rec[7:].split(',')]
            except ValueError:
                pass
        if rec.startswith('monthly:'):
            try:
                return now.day == int(rec[8:])
            except ValueError:
                pass
        return True


class TodoStore:
    def __init__(self):
        self._lock  = threading.Lock()
        self._todos: list[Todo] = []
        self._next  = 1
        os.makedirs(DATA_DIR, exist_ok=True)
        self._load()

    def _load(self):
        if not os.path.exists(TODOS_FILE):
            return
        try:
            with open(TODOS_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
            self._todos = [Todo.from_dict(d) for d in data]
            self._next  = max((t.id for t in self._todos), default=0) + 1
        except Exception:
            self._todos = []

    def _save(self):
        with open(TODOS_FILE, 'w', encoding='utf-8') as f:
            json.dump([t.to_dict() for t in self._todos],
                      f, ensure_ascii=False, indent=2)

    def all(self) -> list[Todo]:
        with self._lock:
            return list(self._todos)

    def get(self, todo_id: int) -> 'Todo | None':
        with self._lock:
            for t in self._todos:
                if t.id == todo_id:
                    return t
        return None

    def children(self, parent_id: int) -> list[Todo]:
        with self._lock:
            return [t for t in self._todos if t.parent_id == parent_id]

    def add(self, title: str, reminder=None, due_date=None,
            notes=None, category=None, recurrence=None, parent_id=None) -> Todo:
        now_str = datetime.now().strftime('%Y-%m-%d %H:%M')
        with self._lock:
            # 建立第一個實例（recurrence=None，實例不再重複觸發預產）
            t = Todo(self._next, title, False, reminder, due_date,
                     now_str, None, notes, category, None, parent_id)
            self._next += 1
            self._todos.append(t)

            # 預產後續重複實例（僅限頂層任務且有截止日與重複規則）
            if recurrence and due_date and parent_id is None:
                dates = _generate_occurrence_dates(due_date, recurrence)
                for d in dates[1:]:   # 跳過第一天（已建立）
                    inst = Todo(self._next, title, False, reminder,
                                d.isoformat(), now_str, None,
                                notes, category, None, None)
                    self._next += 1
                    self._todos.append(inst)

            self._save()
        return t

    def update(self, todo_id: int, **kwargs):
        with self._lock:
            for t in self._todos:
                if t.id == todo_id:
                    for k, v in kwargs.items():
                        setattr(t, k, v)
                    break
            self._save()

    def toggle(self, todo_id: int):
        now = datetime.now().strftime('%Y-%m-%d %H:%M')
        with self._lock:
            for t in self._todos:
                if t.id == todo_id:
                    t.done = not t.done
                    t.done_at = now if t.done else None
                    break
            self._save()

    def delete(self, todo_id: int):
        with self._lock:
            self._todos = [t for t in self._todos
                           if t.id != todo_id and t.parent_id != todo_id]
            self._save()

    def clear_done(self):
        with self._lock:
            done_ids = {t.id for t in self._todos if t.done}
            self._todos = [t for t in self._todos
                           if t.id not in done_ids
                           and t.parent_id not in done_ids]
            self._save()

    def reminders_due(self, now: datetime) -> list[Todo]:
        with self._lock:
            fired = []
            for t in self._todos:
                if t.should_remind(now):
                    if t.snooze_until:
                        t.snooze_until = None
                    fired.append(t)
            if fired:
                self._save()
            return fired

    def categories(self) -> list[str]:
        with self._lock:
            return sorted({t.category for t in self._todos if t.category})

    def file_hash(self) -> str:
        if not os.path.exists(TODOS_FILE):
            return ''
        with open(TODOS_FILE, 'rb') as f:
            return hashlib.md5(f.read()).hexdigest()

# ============================================================
# 自動備份執行緒
# ============================================================

class BackupManager(threading.Thread):
    def __init__(self, store: TodoStore, settings: Settings):
        super().__init__(daemon=True, name='BackupManager')
        self.store    = store
        self.settings = settings
        self._last_min = -1
        os.makedirs(BACKUP_DIR, exist_ok=True)

    def run(self):
        while True:
            try:
                now = datetime.now()
                if now.second < 5:
                    minute = now.hour * 60 + now.minute
                    if minute != self._last_min:
                        self._last_min = minute
                        if now.strftime('%H:%M') == self.settings.get('backup_time'):
                            self._try_backup(now)
            except Exception:
                pass
            time.sleep(1)

    def _try_backup(self, now: datetime):
        cur_hash = self.store.file_hash()
        if not cur_hash:
            return
        existing = sorted(
            [f for f in os.listdir(BACKUP_DIR)
             if f.startswith('todos_') and f.endswith('.json')],
            reverse=True)
        if existing:
            with open(os.path.join(BACKUP_DIR, existing[0]), 'rb') as f:
                if hashlib.md5(f.read()).hexdigest() == cur_hash:
                    return  # 無變動，跳過
        shutil.copy2(TODOS_FILE,
                     os.path.join(BACKUP_DIR, f'todos_{now.strftime("%Y%m%d")}.json'))
        keep = self.settings.get('backup_keep_days')
        for old in sorted([f for f in os.listdir(BACKUP_DIR)
                           if f.startswith('todos_') and f.endswith('.json')])[:-keep]:
            try:
                os.remove(os.path.join(BACKUP_DIR, old))
            except Exception:
                pass

# ============================================================
# 提醒檢查執行緒
# ============================================================

class ReminderChecker(threading.Thread):
    def __init__(self, store: TodoStore, on_trigger):
        super().__init__(daemon=True, name='ReminderChecker')
        self.store      = store
        self.on_trigger = on_trigger
        self._last_min  = -1

    def run(self):
        while True:
            try:
                now = datetime.now()
                if now.second < 5:
                    minute = now.hour * 60 + now.minute
                    if minute != self._last_min:
                        self._last_min = minute
                        for todo in self.store.reminders_due(now):
                            self.on_trigger(todo)
            except Exception:
                pass
            time.sleep(1)

# ============================================================
# 鬧鐘彈窗（獨立 Toplevel，不自動消失）
# ============================================================

class AlertWindow:
    """提醒時間到時彈出的鬧鐘視窗，必須由使用者手動選擇完成或貪睡才關閉。"""

    _W, _H = 400, 200   # 視窗尺寸

    def __init__(self, root: tk.Tk, todo: Todo, store: TodoStore,
                 on_close, on_status_msg):
        """
        root          : FloatingWidget 的 tk.Tk 根視窗
        on_close      : 關閉後的回呼（用於顯示下一個排隊提醒）
        on_status_msg : flash_status(msg, color) 回呼
        """
        self.todo         = todo
        self.store        = store
        self.on_close     = on_close
        self.on_status    = on_status_msg

        self._flash_id    = None
        self._flash_state = False
        self._flash_count = 0

        self.win = tk.Toplevel(root)
        self.win.title('待辦提醒')
        self.win.attributes('-topmost', True)
        self.win.resizable(False, False)
        # 關閉視窗 (X) = 貪睡 5 分鐘
        self.win.protocol('WM_DELETE_WINDOW', lambda: self._snooze(5))

        self._build()
        self._do_flash()

        try:
            import winsound
            winsound.PlaySound('SystemExclamation',
                               winsound.SND_ALIAS | winsound.SND_ASYNC)
        except Exception:
            pass

    def _build(self):
        win = self.win
        win.configure(bg='#881100')

        # 置中螢幕
        win.update_idletasks()
        sw = win.winfo_screenwidth()
        sh = win.winfo_screenheight()
        x  = (sw - self._W) // 2
        y  = (sh - self._H) // 2
        win.geometry(f'{self._W}x{self._H}+{x}+{y}')

        tk.Label(win, text=' !! 提醒時間到 !!', bg='#881100', fg='white',
                 font=('Microsoft YaHei', 13, 'bold'), anchor='w'
                 ).pack(fill='x', padx=10, pady=(14, 4))

        short = (self.todo.title[:32] + '...') if len(self.todo.title) > 32 \
                else self.todo.title
        rec   = self.todo.recurrence or ''
        extra = f'（{_fmt_recurrence(rec)}）' if rec else ''
        self._lbl = tk.Label(win, text=f'  {short}{extra}',
                             bg='#881100', fg='#FFDDDD',
                             font=('Microsoft YaHei', 11),
                             anchor='w', wraplength=360)
        self._lbl.pack(fill='x', padx=10, pady=2)

        # 截止日 / 提醒時間資訊
        info = []
        if self.todo.due_date:
            info.append(f'截止：{self.todo.due_date}')
        if self.todo.reminder:
            info.append(f'提醒：{self.todo.reminder}')
        if info:
            self._info_lbl = tk.Label(win, text='  ' + '　'.join(info),
                                      bg='#881100', fg='#FFAAAA',
                                      font=('Microsoft YaHei', 9), anchor='w')
            self._info_lbl.pack(fill='x', padx=10, pady=(0, 6))
        else:
            self._info_lbl = None

        # 按鈕列
        btn_row = tk.Frame(win, bg='#881100')
        btn_row.pack(fill='x', padx=10, pady=(4, 14))

        done_btn = tk.Button(btn_row, text='  已完成  ',
                             bg='#228B22', fg='white',
                             font=('Microsoft YaHei', 10, 'bold'),
                             relief='flat', cursor='hand2',
                             command=self._done)
        done_btn.pack(side='left', padx=(0, 12))

        tk.Label(btn_row, text='延遲：', bg='#881100', fg='#FFDDDD',
                 font=('Microsoft YaHei', 9)).pack(side='left')

        for mins, label in ((5, '+5分'), (15, '+15分'), (30, '+30分')):
            b = tk.Button(btn_row, text=label, bg='#553300', fg='white',
                          font=('Microsoft YaHei', 9),
                          relief='flat', cursor='hand2',
                          command=lambda m=mins: self._snooze(m))
            b.pack(side='left', padx=3)

    def _do_flash(self):
        """閃爍 20 次後停止，但視窗保持開啟。"""
        if self._flash_count < 20:
            self._flash_state = not self._flash_state
            c = '#CC2200' if self._flash_state else '#881100'
            self.win.configure(bg=c)
            self._lbl.configure(bg=c)
            if self._info_lbl:
                self._info_lbl.configure(bg=c)
            self._flash_count += 1
            self._flash_id = self.win.after(500, self._do_flash)

    def _done(self):
        self.store.toggle(self.todo.id)   # 標記已完成
        self._close()

    def _snooze(self, minutes: int):
        until = (datetime.now() + timedelta(minutes=minutes)
                 ).strftime('%Y-%m-%d %H:%M')
        self.store.update(self.todo.id, snooze_until=until)
        self.on_status(f'  已貪睡 {minutes} 分鐘', '#FFAA44')
        self._close()

    def _close(self):
        if self._flash_id:
            try:
                self.win.after_cancel(self._flash_id)
            except Exception:
                pass
        self.win.destroy()
        self.on_close()


# ============================================================
# 浮動提醒板
# ============================================================

class FloatingWidget:
    def __init__(self, store: TodoStore, settings: Settings, on_open_mgr):
        self.store       = store
        self.settings    = settings
        self.on_open_mgr = on_open_mgr

        self._alert_queue:   list[Todo] = []
        self._alert_showing: bool      = False
        self._drag_x = self._drag_y = 0
        # 折疊區段（從設定載入，預設收起已完成）
        self._collapsed: set[str] = set(
            settings.get('collapsed_sections') or ['done'])

        # 子任務展開狀態（parent todo_id set）
        self._expanded: set[int] = set()
        # 排序模式：'category' | 'duedate' | 'created'
        self._sort_mode: str = 'category'
        self._sort_btns: dict[str, tk.Label] = {}

        self._build()

    def _build(self):
        r = tk.Tk()
        r.title(APP_NAME)
        r.overrideredirect(True)
        aot = self.settings.get('always_on_top')
        r.attributes('-topmost', aot)
        r.attributes('-alpha',   self.settings.get('widget_alpha'))
        r.configure(bg=C_BG)
        r.geometry(f'{WIN_W}x{MIN_H}'
                   f'+{self.settings.get("widget_x")}'
                   f'+{self.settings.get("widget_y")}')
        r.resizable(False, False)
        r.protocol('WM_DELETE_WINDOW', lambda: None)
        self.root = r

        # 標題列
        hf = tk.Frame(r, bg=C_HEADER, height=HEADER_H)
        hf.pack(fill='x')
        hf.pack_propagate(False)

        tk.Label(hf, text='  待辦提醒板',
                 bg=C_HEADER, fg='white', font=F_HEAD
                 ).pack(side='left', padx=6, pady=6)

        self._pin_btn = tk.Label(
            hf,
            text='[釘選]' if aot else '[未釘]',
            bg=C_HEADER,
            fg='white' if aot else '#888888',
            font=F_SMALL, cursor='hand2', padx=4)
        self._pin_btn.pack(side='right', padx=2, pady=9)
        self._pin_btn.bind('<Button-1>', lambda _e: self._toggle_topmost())

        self._clock_lbl = tk.Label(hf, text='',
                                   bg=C_HEADER, fg='#CCCCCC',
                                   font=('Microsoft YaHei', 9))
        self._clock_lbl.pack(side='right', padx=4, pady=6)

        for w in (hf, self._clock_lbl, self._pin_btn):
            w.bind('<Button-1>',   self._drag_start)
            w.bind('<B1-Motion>',  self._drag_move)
            w.bind('<MouseWheel>', self._on_scroll)

        # 底部（先 pack side='bottom'，確保不被擠掉）
        tk.Frame(r, bg='#2A1820', height=1).pack(side='bottom', fill='x')
        ff = tk.Frame(r, bg=C_FOOTER)
        ff.pack(side='bottom', fill='x')

        self._status_lbl = tk.Label(
            ff, text='載入中...', bg=C_FOOTER, fg='#AAAAAA', font=F_SMALL)
        self._status_lbl.pack(side='top', padx=8, pady=(4, 0), anchor='w')

        mgr = tk.Label(ff, text='  + 開啟管理員  ',
                       bg='#8B2336', fg='white', font=F_BTN,
                       cursor='hand2', padx=6, pady=3)
        mgr.pack(side='top', pady=(2, 4))
        mgr.bind('<Button-1>', lambda _e: self.on_open_mgr())
        mgr.bind('<Enter>',    lambda _e: mgr.configure(bg=C_HEADER))
        mgr.bind('<Leave>',    lambda _e: mgr.configure(bg='#8B2336'))
        mgr.bind('<MouseWheel>', self._on_scroll)
        ff.bind('<MouseWheel>', self._on_scroll)

        # 分隔線
        tk.Frame(r, bg='#2A1820', height=1).pack(fill='x')

        # 排序列
        sb_frame = tk.Frame(r, bg='#111128')
        sb_frame.pack(fill='x')
        tk.Label(sb_frame, text=' 排序：', bg='#111128', fg='#888888',
                 font=F_SMALL).pack(side='left', padx=(4, 0), pady=3)
        for mode, label in (('category', '分類'), ('duedate', '截止日'), ('created', '建立時間')):
            is_active = (mode == self._sort_mode)
            btn = tk.Label(sb_frame, text=f' {label} ',
                           bg=C_HEADER if is_active else '#222244',
                           fg='white', font=F_SMALL, cursor='hand2',
                           padx=6, pady=3)
            btn.pack(side='left', padx=2, pady=2)
            btn.bind('<Button-1>', lambda _e, m=mode: self._set_sort(m))
            btn.bind('<MouseWheel>', self._on_scroll)
            self._sort_btns[mode] = btn
        sb_frame.bind('<MouseWheel>', self._on_scroll)

        # 可捲動列表
        self._canvas = tk.Canvas(r, bg=C_BG, highlightthickness=0,
                                 width=WIN_W - 12)
        self._sb = tk.Scrollbar(r, orient='vertical', command=self._canvas.yview)
        self._canvas.configure(yscrollcommand=self._sb.set)
        self._sb.pack(side='right', fill='y')
        self._canvas.pack(side='left', fill='both', expand=True)
        self._canvas.bind('<MouseWheel>',
                          lambda e: self._canvas.yview_scroll(
                              -1 * (e.delta // 120), 'units'))

        self._inner = tk.Frame(self._canvas, bg=C_BG)
        self._canvas.create_window(
            (0, 0), window=self._inner, anchor='nw', width=WIN_W - 16)
        self._inner.bind('<Configure>',
                         lambda _e: self._canvas.configure(
                             scrollregion=self._canvas.bbox('all')))

        self._tick_clock()
        self.refresh()

    # ---- 資料更新 ----

    def refresh(self):
        self.root.after(0, self._do_refresh)

    def _do_refresh(self):
        for ch in self._inner.winfo_children():
            ch.destroy()

        todos     = self.store.all()
        top_level = [t for t in todos if t.parent_id is None]
        total     = len(top_level)
        done_n    = sum(1 for t in top_level if t.done)

        groups: dict[str, list] = {k: [] for k in SEC_KEYS}
        # 母任務放入所屬區段
        for t in top_level:
            groups[t.category_key()].append(t)
        # 子任務若截止日與母任務不同區段，額外放入自己的區段顯示
        _parent_cache: dict[int, Todo | None] = {}
        for t in todos:
            if t.parent_id is None:
                continue
            if t.parent_id not in _parent_cache:
                _parent_cache[t.parent_id] = self.store.get(t.parent_id)
            parent = _parent_cache[t.parent_id]
            child_cat  = t.category_key()
            parent_cat = parent.category_key() if parent else None
            if child_cat != parent_cat:
                groups[child_cat].append(t)

        # 依排序模式排序各區段
        if self._sort_mode == 'duedate':
            for items in groups.values():
                items.sort(key=lambda t: (
                    t.due_date or '9999-12-31',
                    t.reminder or '99:99',
                    t.start_time or ''))
        elif self._sort_mode == 'created':
            for items in groups.values():
                items.sort(key=lambda t: t.start_time or '', reverse=True)

        # 動態建立區段列表
        today = date.today()
        wd    = WEEKDAY_NAMES

        def _sec(key, label, color, collapsible=False):
            return (key, label, color, groups[key], collapsible)

        sections = []
        if groups['overdue']:
            sections.append(_sec('overdue', '!! 逾期', C_OVERDUE))
        # 今天：永遠顯示
        sections.append(_sec(
            'today', f'今天（{wd[today.weekday()]}）', C_TODAY))
        # 明天：有任務才顯示
        if groups['tomorrow']:
            sections.append(_sec(
                'tomorrow',
                f'明天（{wd[(today + timedelta(1)).weekday()]}）',
                C_TMRW))
        # 後天：有任務才顯示
        if groups['dayafter']:
            sections.append(_sec(
                'dayafter',
                f'後天（{wd[(today + timedelta(2)).weekday()]}）',
                C_TMRW))
        # 未來可折疊
        if groups['future']:
            sections.append(_sec('future', '未來', C_FUTURE, True))
        if groups['nodate']:
            sections.append(_sec('nodate', '無截止日', C_NODATE, True))
        if groups['done']:
            sections.append(_sec('done', '已完成', C_DONE_S, True))

        has_any = total > 0

        for cat_key, label, color, items, collapsible in sections:
            collapsed = collapsible and (cat_key in self._collapsed)
            count     = len(items)

            sh = tk.Frame(self._inner, bg=C_BG)
            sh.pack(fill='x')

            arrow = ' ▶' if collapsed else (' ▼' if collapsible else '')
            hdr   = tk.Label(sh, text=f' {label}  ({count}){arrow}',
                             bg=C_BG, fg=color, font=F_SEC, anchor='w',
                             padx=8, cursor='hand2' if collapsible else '')
            hdr.pack(side='left', pady=(5, 2))
            if collapsible:
                hdr.bind('<Button-1>', lambda _e, k=cat_key: self._toggle_section(k))
                hdr.bind('<MouseWheel>', self._on_scroll)

            tk.Frame(sh, bg=color, height=1).pack(
                side='left', fill='x', expand=True, padx=(0, 8), pady=(5, 2))

            if not collapsed:
                for t in items:
                    if t.parent_id is not None:
                        # 跨區段子任務：顯示父任務參考 + 完整資訊
                        self._make_child_row_in_section(t)
                    else:
                        self._make_row(t, cat_key)

        if not has_any:
            tk.Label(self._inner,
                     text='  尚無任務，點下方開啟管理員新增',
                     bg=C_BG, fg='#AAAAAA', font=F_SMALL,
                     anchor='w', padx=8, pady=10).pack(fill='x')

        self._status_lbl.configure(
            text=(f'  共 {total} 項   已完成 {done_n} 項  |  滾輪=透明度'
                  if total else '  尚無任務  |  滾輪=透明度'),
            fg='#AAAAAA')

        self._inner.update_idletasks()
        self.root.after(20, self._auto_resize)

    def _make_row(self, t: Todo, cat_key: str):
        all_kids  = self.store.children(t.id)
        k_tot     = len(all_kids)
        k_don     = sum(1 for c in all_kids if c.done)
        # 展開時只顯示「同區段」子任務（其他區段的子任務已在自己的區段顯示）
        kids      = [c for c in all_kids if c.category_key() == cat_key]
        expanded  = (k_tot > 0) and (t.id in self._expanded)

        rf = tk.Frame(self._inner, bg=C_BG)
        rf.pack(fill='x', padx=4, pady=1)

        # 主行：checkbox + 標題 + （折疊箭頭）
        top_row = tk.Frame(rf, bg=C_BG)
        top_row.pack(fill='x')

        chk  = '[v]' if t.done else '[ ]'
        ttxt = t.title if len(t.title) <= 20 else t.title[:18] + '..'

        if t.done:                 fg = C_DONE
        elif cat_key == 'overdue': fg = C_OVERDUE
        elif t.reminder:           fg = C_REMIND
        else:                      fg = C_FG

        lbl = tk.Label(top_row, text=f'{chk} {ttxt}',
                       bg=C_BG, fg=fg, font=F_MAIN,
                       anchor='w', padx=8, cursor='hand2')
        lbl.pack(side='left', fill='x', expand=True)
        lbl.bind('<Button-1>', lambda _e, tid=t.id: self._toggle(tid))

        # 子任務進度 + 折疊按鈕
        if k_tot > 0:
            arrow = ' v ' if expanded else ' > '
            prog_lbl = tk.Label(
                top_row,
                text=f'[{k_don}/{k_tot}]{arrow}',
                bg='#333355', fg='#AAAAAA',
                font=F_SMALL, cursor='hand2', padx=4, pady=2)
            prog_lbl.pack(side='right', padx=(0, 4))
            prog_lbl.bind('<Button-1>',
                          lambda _e, tid=t.id: self._toggle_expand(tid))

        # 子資訊列
        if t.done:
            sub = f'    完成：{t.done_at}' if t.done_at else ''
        else:
            parts = []
            if t.reminder: parts.append(f'@{t.reminder}')
            if t.due_date: parts.append(f'截止：{t.due_date}')
            if t.category: parts.append(f'[{t.category}]')
            sub = '    ' + '  '.join(parts) if parts else ''

        if sub:
            fg_s = '#FF8888' if cat_key == 'overdue' else '#888888'
            tk.Label(rf, text=sub, bg=C_BG, fg=fg_s,
                     font=F_SMALL, anchor='w', padx=8).pack(fill='x')

        def _enter(_e, l=lbl, f=rf, t2=top_row):
            for w in (l, f, t2): w.configure(bg=C_HOVER)

        def _leave(_e, l=lbl, f=rf, t2=top_row):
            for w in (l, f, t2): w.configure(bg=C_BG)

        lbl.bind('<Enter>',    _enter)
        lbl.bind('<Leave>',    _leave)
        rf.bind('<Enter>',     _enter)
        rf.bind('<Leave>',     _leave)
        top_row.bind('<Enter>', _enter)
        top_row.bind('<Leave>', _leave)

        # 展開的子任務列
        if expanded:
            for child in kids:
                self._make_child_row(child)

    def _make_child_row(self, t: Todo):
        """子任務縮排列（在展開的父任務下方顯示）。"""
        rf = tk.Frame(self._inner, bg=C_SUB)
        rf.pack(fill='x', padx=4, pady=0)

        chk  = '[v]' if t.done else '[ ]'
        ttxt = t.title if len(t.title) <= 20 else t.title[:18] + '..'
        fg   = C_DONE if t.done else (C_REMIND if t.reminder else C_FG)

        lbl = tk.Label(rf, text=f'     {chk} {ttxt}',
                       bg=C_SUB, fg=fg, font=F_SMALL,
                       anchor='w', padx=6, pady=2, cursor='hand2')
        lbl.pack(fill='x')
        lbl.bind('<Button-1>', lambda _e, tid=t.id: self._toggle(tid))

        # 子資訊：截止日 + 提醒時間
        if t.done:
            sub = f'       完成：{t.done_at}' if t.done_at else ''
        else:
            parts = []
            if t.reminder:  parts.append(f'@{t.reminder}')
            if t.due_date:  parts.append(f'截止：{t.due_date}')
            sub = '       ' + '  '.join(parts) if parts else ''
        if sub:
            tk.Label(rf, text=sub, bg=C_SUB, fg='#888888',
                     font=F_SMALL, anchor='w', padx=6).pack(fill='x')

        def _enter(_e, l=lbl, f=rf):
            l.configure(bg=C_HOVER); f.configure(bg=C_HOVER)

        def _leave(_e, l=lbl, f=rf):
            l.configure(bg=C_SUB); f.configure(bg=C_SUB)

        lbl.bind('<Enter>', _enter)
        lbl.bind('<Leave>', _leave)
        rf.bind('<Enter>',  _enter)
        rf.bind('<Leave>',  _leave)

    def _make_child_row_in_section(self, t: Todo):
        """跨區段子任務：有自己的截止日且與母任務不同區段，獨立顯示在對應區段。"""
        parent     = self.store.get(t.parent_id)
        pt_short   = (parent.title[:14] + '..') if parent and len(parent.title) > 14 \
                     else (parent.title if parent else '?')

        rf = tk.Frame(self._inner, bg=C_SUB)
        rf.pack(fill='x', padx=4, pady=1)

        # 父任務參考標籤
        tk.Label(rf, text=f'  ↳ {pt_short}',
                 bg=C_SUB, fg='#666688', font=F_SMALL,
                 anchor='w', padx=6).pack(fill='x')

        chk  = '[v]' if t.done else '[ ]'
        ttxt = t.title[:18] + '..' if len(t.title) > 18 else t.title
        fg   = C_DONE if t.done else (C_REMIND if t.reminder else C_FG)

        lbl = tk.Label(rf, text=f'    {chk} {ttxt}',
                       bg=C_SUB, fg=fg, font=F_MAIN,
                       anchor='w', padx=6, cursor='hand2')
        lbl.pack(fill='x')
        lbl.bind('<Button-1>', lambda _e, tid=t.id: self._toggle(tid))

        # 子資訊：提醒 + 分類
        if t.done:
            sub = f'      完成：{t.done_at}' if t.done_at else ''
        else:
            parts = []
            if t.reminder:  parts.append(f'@{t.reminder}')
            if t.category:  parts.append(f'[{t.category}]')
            sub = '      ' + '  '.join(parts) if parts else ''
        if sub:
            tk.Label(rf, text=sub, bg=C_SUB, fg='#888888',
                     font=F_SMALL, anchor='w', padx=6).pack(fill='x')

        def _enter(_e, l=lbl, f=rf):
            l.configure(bg=C_HOVER); f.configure(bg=C_HOVER)
        def _leave(_e, l=lbl, f=rf):
            l.configure(bg=C_SUB); f.configure(bg=C_SUB)

        lbl.bind('<Enter>', _enter)
        lbl.bind('<Leave>', _leave)
        rf.bind('<Enter>',  _enter)
        rf.bind('<Leave>',  _leave)

    def _toggle_section(self, key: str):
        """點擊區段標題折疊 / 展開。"""
        if key in self._collapsed:
            self._collapsed.discard(key)
        else:
            self._collapsed.add(key)
        self.settings.set('collapsed_sections', list(self._collapsed))
        self._do_refresh()

    def _toggle_expand(self, todo_id: int):
        """切換子任務展開 / 收納。"""
        if todo_id in self._expanded:
            self._expanded.discard(todo_id)
        else:
            self._expanded.add(todo_id)
        self._do_refresh()

    def _set_sort(self, mode: str):
        """切換排序模式並更新按鈕樣式。"""
        self._sort_mode = mode
        for m, btn in self._sort_btns.items():
            btn.configure(bg=C_HEADER if m == mode else '#222244')
        self._do_refresh()

    def _auto_resize(self):
        content_h = self._inner.winfo_reqheight()
        max_c     = MAX_H - HEADER_H - 2 - SORTBAR_H - FOOTER_H - 4
        canvas_h  = max(30, min(max_c, content_h))
        self._canvas.configure(height=canvas_h)
        total_h   = max(MIN_H, min(MAX_H,
                        HEADER_H + 2 + SORTBAR_H + canvas_h + FOOTER_H + 4))
        self.root.geometry(
            f'{WIN_W}x{total_h}+{self.root.winfo_x()}+{self.root.winfo_y()}')
        self._canvas.configure(scrollregion=self._canvas.bbox('all'))

    def _toggle(self, todo_id: int):
        self.store.toggle(todo_id)
        self._do_refresh()

    # ---- 提醒 / 鬧鐘彈窗 ----

    def trigger_alert(self, todo: Todo):
        self.root.after(0, lambda: self._enqueue(todo))

    def _enqueue(self, todo: Todo):
        self._alert_queue.append(todo)
        if not self._alert_showing:
            self._show_next()

    def _show_next(self):
        if not self._alert_queue:
            self._alert_showing = False
            return
        self._alert_showing = True
        todo = self._alert_queue.pop(0)
        AlertWindow(
            root          = self.root,
            todo          = todo,
            store         = self.store,
            on_close      = self._on_alert_closed,
            on_status_msg = self.flash_status,
        )

    def _on_alert_closed(self):
        """AlertWindow 關閉後觸發：重新整理面板，並顯示下一個排隊提醒。"""
        self._do_refresh()
        self.root.after(300, self._show_next)

    def flash_status(self, msg: str, color: str = '#FF6060'):
        def _show():
            self._status_lbl.configure(text=msg, fg=color)
            self.root.after(3000, self._do_refresh)
        self.root.after(0, _show)

    def _toggle_topmost(self):
        new = not self.root.attributes('-topmost')
        self.root.attributes('-topmost', new)
        self.settings.set('always_on_top', new)
        self._pin_btn.configure(
            text='[釘選]' if new else '[未釘]',
            fg='white'   if new else '#888888')

    def _drag_start(self, e):
        self._drag_x = e.x
        self._drag_y = e.y

    def _drag_move(self, e):
        x = self.root.winfo_x() + e.x - self._drag_x
        y = self.root.winfo_y() + e.y - self._drag_y
        self.root.geometry(f'+{x}+{y}')
        self.settings.set('widget_x', x)
        self.settings.set('widget_y', y)

    def _on_scroll(self, e):
        a = self.root.attributes('-alpha')
        a = max(0.15, min(1.0, a + (0.05 if e.delta > 0 else -0.05)))
        self.root.attributes('-alpha', a)
        self.settings.set('widget_alpha', round(a, 2))

    def _tick_clock(self):
        self._clock_lbl.configure(text=datetime.now().strftime('%H:%M'))
        self.root.after(5000, self._tick_clock)

# ============================================================
# 管理員視窗
# ============================================================

class ManagerWindow:
    def __init__(self, store: TodoStore, settings: Settings,
                 on_close, on_widget_refresh):
        self.store           = store
        self.settings        = settings
        self._on_close       = on_close
        self._widget_refresh = on_widget_refresh
        self._search_var: tk.StringVar | None = None
        self._cat_filter: str | None = None
        self._build()

    def _build(self):
        w = tk.Toplevel()
        w.title('待辦事項管理員')
        w.configure(bg=C_BG)
        w.attributes('-topmost', True)
        w.resizable(True, True)
        w.minsize(WIN_W_MGR, 480)
        w.geometry(f'{WIN_W_MGR}x660+380+40')
        w.protocol('WM_DELETE_WINDOW', self._close)
        self.win = w

        # 標題列
        hf = tk.Frame(w, bg=C_MGRHDR, height=36)
        hf.pack(fill='x')
        hf.pack_propagate(False)
        tk.Label(hf, text='  待辦事項管理員',
                 bg=C_MGRHDR, fg='white', font=F_HEAD
                 ).pack(side='left', pady=6, padx=6)
        close_lbl = tk.Label(hf, text=' X ', bg=C_HEADER,
                             fg='white', font=F_BTN, cursor='hand2', padx=4)
        close_lbl.pack(side='right', padx=6, pady=5)
        close_lbl.bind('<Button-1>', lambda _e: self._close())

        # 搜尋列
        sf = tk.Frame(w, bg='#111128', pady=4)
        sf.pack(fill='x', padx=6, pady=(4, 0))
        tk.Label(sf, text='搜尋：', bg='#111128', fg='#AAAAAA',
                 font=F_SMALL).pack(side='left', padx=(4, 2))
        self._search_var = tk.StringVar()
        self._search_var.trace_add('write', lambda *_: self._refresh())
        se = tk.Entry(sf, textvariable=self._search_var,
                      bg='#252545', fg=C_FG, insertbackground=C_FG,
                      font=F_MAIN, relief='flat', width=30)
        se.pack(side='left', fill='x', expand=True, padx=4)
        clr = tk.Label(sf, text=' X ', bg='#333355', fg='#AAAAAA',
                       font=F_SMALL, cursor='hand2', padx=3)
        clr.pack(side='left')
        clr.bind('<Button-1>', lambda _e: self._search_var.set(''))

        # 分類篩選列
        self._cat_frame = tk.Frame(w, bg=C_BG)
        self._cat_frame.pack(fill='x', padx=6, pady=(4, 0))
        self._rebuild_cat_bar()

        # 欄位說明
        tk.Label(w, text='  任務（點 [ ] 切換完成，雙擊標題或按 [編] 編輯）                 [編][刪]',
                 bg=C_BG, fg='#555555', font=F_SMALL, anchor='w'
                 ).pack(fill='x', padx=4)
        tk.Frame(w, bg='#333355', height=1).pack(fill='x', padx=4)

        # 底部按鈕（先 pack，確保不被擠掉）
        tk.Frame(w, bg='#333355', height=1).pack(side='bottom', fill='x')
        self._status = tk.Label(w, text='', bg=C_BG, fg='#AAAAAA', font=F_SMALL)
        self._status.pack(side='bottom', fill='x', padx=8, pady=2)

        bf = tk.Frame(w, bg=C_FOOTER)
        bf.pack(side='bottom', fill='x')

        def _btn(parent, text, bg, cmd, hover):
            b = tk.Label(parent, text=text, bg=bg, fg='white',
                         font=F_BTN, cursor='hand2', padx=7, pady=4)
            b.pack(side='left', padx=4, pady=5)
            b.bind('<Button-1>', lambda _e: cmd())
            b.bind('<Enter>',    lambda _e: b.configure(bg=hover))
            b.bind('<Leave>',    lambda _e: b.configure(bg=bg))

        _btn(bf, ' + 新增 ',    '#16A085', self._add,               '#1ABC9C')
        _btn(bf, ' + 子任務 ',  '#1A5276', self._add_subtask_prompt, '#2874A6')
        _btn(bf, ' 匯出 TXT ', '#4A235A', self._export,             '#6C3483')
        _btn(bf, ' 備份 ',      '#2E4057', self._manual_backup,      '#3D5A80')
        _btn(bf, ' 設定 ',      '#2C3E50', self._open_settings,      '#415161')

        clr_btn = tk.Label(bf, text=' 清除已完成 ', bg='#7D3C00',
                           fg='white', font=F_BTN, cursor='hand2', padx=7, pady=4)
        clr_btn.pack(side='right', padx=4, pady=5)
        clr_btn.bind('<Button-1>', lambda _e: self._clear())
        clr_btn.bind('<Enter>',    lambda _e: clr_btn.configure(bg='#AA5500'))
        clr_btn.bind('<Leave>',    lambda _e: clr_btn.configure(bg='#7D3C00'))

        # 可捲動列表（最後 pack）
        canvas = tk.Canvas(w, bg=C_BG, highlightthickness=0)
        sb     = tk.Scrollbar(w, orient='vertical', command=canvas.yview)
        canvas.configure(yscrollcommand=sb.set)
        sb.pack(side='right', fill='y')
        canvas.pack(side='left', fill='both', expand=True)
        canvas.bind('<MouseWheel>',
                    lambda e: canvas.yview_scroll(-1 * (e.delta // 120), 'units'))

        self._inner = tk.Frame(canvas, bg=C_BG)
        canvas.create_window((0, 0), window=self._inner,
                             anchor='nw', width=WIN_W_MGR - 16)
        self._inner.bind('<Configure>',
                         lambda _e: canvas.configure(
                             scrollregion=canvas.bbox('all')))
        self._canvas = canvas
        self._refresh()

    # ---- 分類篩選 ----

    def _rebuild_cat_bar(self):
        for ch in self._cat_frame.winfo_children():
            ch.destroy()
        tk.Label(self._cat_frame, text='分類：', bg=C_BG, fg='#AAAAAA',
                 font=F_SMALL).pack(side='left', padx=(4, 2))

        def _catbtn(text, val):
            active = (self._cat_filter == val)
            lb = tk.Label(self._cat_frame, text=f' {text} ',
                          bg='#334466' if active else '#222244',
                          fg='#FFCC44' if val else 'white',
                          font=F_SMALL, cursor='hand2', padx=4)
            lb.pack(side='left', padx=1)
            lb.bind('<Button-1>', lambda _e, v=val: self._set_cat(v))

        _catbtn('全部', None)
        for cat in self.store.categories():
            _catbtn(cat, cat)

    def _set_cat(self, val):
        self._cat_filter = val
        self._rebuild_cat_bar()
        self._refresh()

    # ---- 列表渲染 ----

    def _refresh(self):
        for ch in self._inner.winfo_children():
            ch.destroy()

        todos     = self.store.all()
        search    = (self._search_var.get().strip().lower()
                     if self._search_var else '')
        top_level = [t for t in todos if t.parent_id is None]

        if self._cat_filter:
            top_level = [t for t in top_level
                         if t.category == self._cat_filter]
        if search:
            top_level = [t for t in top_level
                         if search in t.title.lower()
                         or (t.notes    and search in t.notes.lower())
                         or (t.category and search in t.category.lower())]

        for t in top_level:
            self._make_row(t, indent=0)

        done_n = sum(1 for t in top_level if t.done)
        self._status.configure(
            text=f'  顯示 {len(top_level)} 項   已完成 {done_n} 項'
                 f'  |  資料庫共 {len(todos)} 筆')
        self._rebuild_cat_bar()
        self._inner.update_idletasks()
        self._canvas.configure(scrollregion=self._canvas.bbox('all'))

    def _make_row(self, t: Todo, indent: int = 0):
        kids   = self.store.children(t.id)
        bg_row = C_SUB if indent > 0 else C_BG
        pad_l  = 6 + indent * 18

        rf = tk.Frame(self._inner, bg=bg_row)
        rf.pack(fill='x', padx=2, pady=1)

        top = tk.Frame(rf, bg=bg_row)
        top.pack(fill='x')

        k_tot = len(kids)
        k_don = sum(1 for c in kids if c.done)
        prog  = f' [{k_don}/{k_tot}]' if k_tot > 0 else ''
        chk   = '[v]' if t.done else '[ ]'
        ttxt  = t.title if len(t.title) <= 34 else t.title[:31] + '..'
        cat   = t.category_key()

        if t.done:          col = C_DONE
        elif cat == 'overdue': col = C_OVERDUE
        elif t.reminder:    col = C_REMIND
        else:               col = C_FG

        done_lbl = tk.Label(top, text=chk,
                            bg=bg_row, fg=col, font=F_MAIN,
                            anchor='w', cursor='hand2', padx=pad_l, pady=1)
        done_lbl.pack(side='left')
        done_lbl.bind('<Button-1>', lambda _e, tid=t.id: self._toggle(tid))

        task = tk.Label(top, text=f' {ttxt}{prog}',
                        bg=bg_row, fg=col, font=F_MAIN,
                        anchor='w', cursor='hand2', padx=pad_l, pady=1)
        task.pack(side='left', fill='x', expand=True)
        task.bind('<Double-Button-1>', lambda _e, tid=t.id: self._edit_task(tid))

        edit_lbl = tk.Label(top, text='[編]', bg=bg_row, fg='#6FA8DC',
                            font=F_SMALL, cursor='hand2', padx=4)
        edit_lbl.pack(side='right')
        edit_lbl.bind('<Button-1>', lambda _e, tid=t.id: self._edit_task(tid))

        del_lbl = tk.Label(top, text='[刪]', bg=bg_row, fg='#FF6666',
                           font=F_SMALL, cursor='hand2', padx=4)
        del_lbl.pack(side='right', padx=4)
        del_lbl.bind('<Button-1>', lambda _e, tid=t.id: self._delete(tid))

        # 附加資訊行
        if t.done:
            parts  = []
            sub_fg = '#666666'
            if t.done_at:    parts.append(f'完成：{t.done_at}')
            if t.start_time: parts.append(f'建立：{t.start_time}')
        else:
            parts  = []
            sub_fg = '#FF8888' if cat == 'overdue' else '#888888'
            if t.due_date:   parts.append(f'截止：{t.due_date}')
            if t.reminder:   parts.append(f'提醒：@{t.reminder}')
            if t.recurrence and t.recurrence != 'daily':
                parts.append(f'重複：{_fmt_recurrence(t.recurrence)}')
            if t.category:   parts.append(f'[{t.category}]')
            if t.start_time: parts.append(f'建立：{t.start_time}')

        if parts:
            sub_txt = ' ' * (indent * 3 + 4) + '  |  '.join(parts)
            tk.Label(rf, text=sub_txt, bg=bg_row, fg=sub_fg,
                     font=F_SMALL, anchor='w', padx=pad_l).pack(fill='x')

        # 備註行
        if t.notes:
            note_s = t.notes if len(t.notes) <= 55 else t.notes[:52] + '...'
            nf = tk.Frame(rf, bg=bg_row)
            nf.pack(fill='x')
            tk.Label(nf, text=' ' * (indent * 3 + 4) + '備註：',
                     bg=bg_row, fg='#5588AA', font=F_SMALL,
                     anchor='w', padx=pad_l).pack(side='left')
            nl = tk.Label(nf, text=note_s, bg=bg_row, fg='#7799BB',
                          font=F_SMALL, anchor='w', cursor='hand2')
            nl.pack(side='left', fill='x', expand=True)
            nl.bind('<Button-1>', lambda _e, tid=t.id: self._edit_notes(tid))
        elif indent == 0 and not t.done:
            add_n = tk.Label(rf, text='    + 新增備註',
                             bg=bg_row, fg='#445566',
                             font=F_SMALL, anchor='w',
                             cursor='hand2', padx=pad_l)
            add_n.pack(fill='x')
            add_n.bind('<Button-1>', lambda _e, tid=t.id: self._edit_notes(tid))

        tk.Frame(rf, bg='#252535', height=1).pack(fill='x', pady=(2, 0))

        def _enter(_e, ws=(rf, top, done_lbl, task, edit_lbl, del_lbl)):
            for ww in ws: ww.configure(bg=C_HOVER)

        def _leave(_e, ws=(rf, top, done_lbl, task, edit_lbl, del_lbl), bg=bg_row):
            for ww in ws: ww.configure(bg=bg)

        for ww in (rf, top, done_lbl, task, edit_lbl, del_lbl):
            ww.bind('<Enter>', _enter)
            ww.bind('<Leave>', _leave)

        for child in kids:
            self._make_row(child, indent=indent + 1)

    # ---- 新增對話框 ----

    def _ask_date(self, initial: str | None = None) -> str | None:
        dp = DatePicker(self.win, initial=initial)
        self.win.wait_window(dp)
        return dp.result

    def _ask_time(self, initial: str | None = None) -> str | None:
        tp = TimePicker(self.win, initial=initial)
        self.win.wait_window(tp)
        return tp.result

    def _ask_recurrence(self, initial: str | None = None) -> str | None:
        rp = RecurrencePicker(self.win, initial=initial)
        self.win.wait_window(rp)
        return rp.result

    def _open_task_editor(self, mode: str, todo: Todo | None = None, parent_id: int | None = None):
        dlg = tk.Toplevel(self.win)
        dlg.title('新增任務' if mode == 'add' else '編輯任務')
        dlg.configure(bg=C_BG)
        dlg.transient(self.win)
        dlg.grab_set()
        dlg.resizable(True, False)
        dlg.minsize(620, 360)
        dlg.geometry('700x430')

        title_var = tk.StringVar(value=(todo.title if todo else ''))
        due_var = tk.StringVar(value=(todo.due_date if todo and todo.due_date else ''))
        rem_var = tk.StringVar(value=(todo.reminder if todo and todo.reminder else ''))
        rec_var = tk.StringVar(value=(todo.recurrence if todo and todo.recurrence else ''))
        cat_var = tk.StringVar(value=(todo.category if todo and todo.category else ''))

        body = tk.Frame(dlg, bg=C_BG)
        body.pack(fill='both', expand=True, padx=12, pady=12)
        for c in (1, 3):
            body.grid_columnconfigure(c, weight=1)

        tk.Label(body, text='任務名稱', bg=C_BG, fg=C_FG, font=F_SMALL).grid(row=0, column=0, sticky='w', padx=4, pady=6)
        tk.Entry(body, textvariable=title_var, bg='#252545', fg=C_FG, insertbackground=C_FG, relief='flat').grid(
            row=0, column=1, columnspan=3, sticky='ew', padx=4, pady=6
        )

        tk.Label(body, text='截止日期', bg=C_BG, fg=C_FG, font=F_SMALL).grid(row=1, column=0, sticky='w', padx=4, pady=6)
        tk.Entry(body, textvariable=due_var, bg='#252545', fg=C_FG, insertbackground=C_FG, relief='flat').grid(
            row=1, column=1, sticky='ew', padx=4, pady=6
        )
        tk.Button(body, text='選日期', command=lambda: due_var.set(self._ask_date(due_var.get() or None) or due_var.get()),
                  bg='#334466', fg='white', relief='flat').grid(row=1, column=2, sticky='w', padx=4, pady=6)
        tk.Button(body, text='清空', command=lambda: due_var.set(''),
                  bg='#444444', fg='white', relief='flat').grid(row=1, column=3, sticky='w', padx=4, pady=6)

        tk.Label(body, text='提醒時間', bg=C_BG, fg=C_FG, font=F_SMALL).grid(row=2, column=0, sticky='w', padx=4, pady=6)
        tk.Entry(body, textvariable=rem_var, bg='#252545', fg=C_FG, insertbackground=C_FG, relief='flat').grid(
            row=2, column=1, sticky='ew', padx=4, pady=6
        )
        tk.Button(body, text='選時間', command=lambda: rem_var.set(self._ask_time(rem_var.get() or None) or rem_var.get()),
                  bg='#334466', fg='white', relief='flat').grid(row=2, column=2, sticky='w', padx=4, pady=6)
        tk.Button(body, text='清空', command=lambda: rem_var.set(''),
                  bg='#444444', fg='white', relief='flat').grid(row=2, column=3, sticky='w', padx=4, pady=6)

        tk.Label(body, text='重複規則', bg=C_BG, fg=C_FG, font=F_SMALL).grid(row=3, column=0, sticky='w', padx=4, pady=6)
        tk.Entry(body, textvariable=rec_var, bg='#252545', fg=C_FG, insertbackground=C_FG, relief='flat').grid(
            row=3, column=1, sticky='ew', padx=4, pady=6
        )
        tk.Button(
            body, text='設定重複',
            command=lambda: rec_var.set(self._ask_recurrence(rec_var.get() or 'daily') or rec_var.get()),
            bg='#334466', fg='white', relief='flat'
        ).grid(row=3, column=2, sticky='w', padx=4, pady=6)
        tk.Button(body, text='清空', command=lambda: rec_var.set(''),
                  bg='#444444', fg='white', relief='flat').grid(row=3, column=3, sticky='w', padx=4, pady=6)

        tk.Label(body, text='分類', bg=C_BG, fg=C_FG, font=F_SMALL).grid(row=4, column=0, sticky='w', padx=4, pady=6)
        tk.Entry(body, textvariable=cat_var, bg='#252545', fg=C_FG, insertbackground=C_FG, relief='flat').grid(
            row=4, column=1, columnspan=3, sticky='ew', padx=4, pady=6
        )
        cats = self.store.categories()
        hint = '、'.join(cats[:10]) if cats else '（目前無分類）'
        tk.Label(body, text=f'現有分類：{hint}', bg=C_BG, fg='#8899AA', font=F_SMALL, anchor='w').grid(
            row=5, column=0, columnspan=4, sticky='ew', padx=4, pady=(0, 6)
        )

        tk.Label(body, text='備註', bg=C_BG, fg=C_FG, font=F_SMALL).grid(row=6, column=0, sticky='nw', padx=4, pady=6)
        notes_text = tk.Text(body, height=6, bg='#252545', fg=C_FG, insertbackground=C_FG, relief='flat', wrap='word')
        notes_text.grid(row=6, column=1, columnspan=3, sticky='nsew', padx=4, pady=6)
        body.grid_rowconfigure(6, weight=1)
        if todo and todo.notes:
            notes_text.insert('1.0', todo.notes)

        result = {'ok': False, 'data': None}

        def _submit():
            title = title_var.get().strip()
            if not title:
                messagebox.showwarning('輸入錯誤', '任務名稱不可空白', parent=dlg)
                return
            reminder = rem_var.get().strip() or None
            due_date = due_var.get().strip() or None
            recurrence = rec_var.get().strip() or None
            if not reminder:
                recurrence = None
            notes = notes_text.get('1.0', 'end').strip() or None
            category = cat_var.get().strip() or None
            result['ok'] = True
            result['data'] = {
                'title': title,
                'due_date': due_date,
                'reminder': reminder,
                'recurrence': recurrence,
                'category': category,
                'notes': notes,
                'parent_id': parent_id,
            }
            dlg.destroy()

        btns = tk.Frame(dlg, bg=C_BG)
        btns.pack(fill='x', padx=12, pady=(0, 12))
        tk.Button(btns, text='取消', command=dlg.destroy, bg='#444444', fg='white', relief='flat').pack(side='right', padx=4)
        tk.Button(btns, text='儲存', command=_submit, bg='#16A085', fg='white', relief='flat').pack(side='right', padx=4)

        dlg.wait_window()
        return result['data'] if result['ok'] else None

    def _add(self, parent_id: int | None = None):
        data = self._open_task_editor('add', parent_id=parent_id)
        if not data:
            return
        self.store.add(
            data['title'],
            data['reminder'],
            data['due_date'],
            data['notes'],
            data['category'],
            data['recurrence'],
            data['parent_id'],
        )
        self._refresh()
        self._widget_refresh()

    def _add_subtask_prompt(self):
        todos   = self.store.all()
        parents = [t for t in todos if t.parent_id is None and not t.done]
        if not parents:
            messagebox.showinfo('沒有父任務', '目前沒有未完成的父任務。',
                                parent=self.win)
            return
        choices = '\n'.join(f'ID {t.id}：{t.title}' for t in parents[:20])
        raw = simpledialog.askstring(
            '選擇父任務',
            f'輸入要新增子任務的任務 ID：\n\n{choices}',
            parent=self.win)
        if not raw:
            return
        try:
            pid = int(raw.strip())
        except ValueError:
            return
        if self.store.get(pid):
            self._add(parent_id=pid)

    def _toggle(self, todo_id: int):
        self.store.toggle(todo_id)
        self._refresh()
        self._widget_refresh()

    def _delete(self, todo_id: int):
        self.store.delete(todo_id)
        self._refresh()
        self._widget_refresh()

    def _clear(self):
        self.store.clear_done()
        self._refresh()
        self._widget_refresh()

    def _edit_notes(self, todo_id: int):
        t = self.store.get(todo_id)
        if not t:
            return
        new_n = simpledialog.askstring(
            '編輯備註', '備註內容（清空請按確認不填）：',
            initialvalue=t.notes or '', parent=self.win)
        if new_n is None:
            return
        self.store.update(todo_id, notes=new_n.strip() or None)
        self._refresh()
        self._widget_refresh()

    def _edit_task(self, todo_id: int):
        t = self.store.get(todo_id)
        if not t:
            return
        data = self._open_task_editor('edit', todo=t, parent_id=t.parent_id)
        if not data:
            return
        self.store.update(
            todo_id,
            title=data['title'],
            due_date=data['due_date'],
            reminder=data['reminder'],
            recurrence=data['recurrence'],
            category=data['category'],
            notes=data['notes'],
        )
        self._refresh()
        self._widget_refresh()

    def _export(self):
        todos     = self.store.all()
        top_level = [t for t in todos if t.parent_id is None]

        lines = [
            f'待辦事項匯出  {datetime.now().strftime("%Y-%m-%d %H:%M")}',
            '=' * 60, '',
        ]
        for cat_key, sec_label, _ in SECTIONS:
            items = [t for t in top_level if t.category_key() == cat_key]
            if not items:
                continue
            lines.append(f'[ {sec_label.strip()} ]')
            lines.append('-' * 40)
            for t in items:
                chk = '[x]' if t.done else '[ ]'
                lines.append(f'  {chk} {t.title}')
                meta = []
                if t.due_date:   meta.append(f'截止：{t.due_date}')
                if t.reminder:   meta.append(f'提醒：@{t.reminder}')
                if t.recurrence and t.recurrence != 'daily':
                    meta.append(f'重複：{_fmt_recurrence(t.recurrence)}')
                if t.category:   meta.append(f'分類：{t.category}')
                if t.done_at:    meta.append(f'完成：{t.done_at}')
                if meta:
                    lines.append('       ' + '  |  '.join(meta))
                if t.notes:
                    lines.append(f'       備註：{t.notes}')
                for c in self.store.children(t.id):
                    cchk = '[x]' if c.done else '[ ]'
                    lines.append(f'    {cchk} {c.title}')
                    if c.done_at:
                        lines.append(f'         完成：{c.done_at}')
            lines.append('')

        path = filedialog.asksaveasfilename(
            parent=self.win,
            title='匯出待辦清單',
            initialfile=f'待辦事項_{datetime.now().strftime("%Y%m%d_%H%M")}.txt',
            defaultextension='.txt',
            filetypes=[('文字檔', '*.txt'), ('所有檔案', '*.*')])
        if path:
            with open(path, 'w', encoding='utf-8') as f:
                f.write('\n'.join(lines))
            messagebox.showinfo('匯出完成', f'已儲存至：\n{path}', parent=self.win)

    def _manual_backup(self):
        if not os.path.exists(TODOS_FILE):
            messagebox.showinfo('備份', '尚無資料可備份。', parent=self.win)
            return
        os.makedirs(BACKUP_DIR, exist_ok=True)
        dst = os.path.join(BACKUP_DIR,
                           f'todos_{datetime.now().strftime("%Y%m%d_%H%M")}.json')
        shutil.copy2(TODOS_FILE, dst)
        messagebox.showinfo('備份完成', f'已備份至：\n{dst}', parent=self.win)

    def _open_settings(self):
        bt = simpledialog.askstring(
            '設定 - 自動備份時間',
            f'每日自動備份時間（格式 HH:MM）\n目前設定：{self.settings.get("backup_time")}',
            initialvalue=self.settings.get('backup_time'),
            parent=self.win)
        if bt and re.match(r'^\d{2}:\d{2}$', bt.strip()):
            self.settings.set('backup_time', bt.strip())

        kd = simpledialog.askstring(
            '設定 - 保留備份天數',
            f'最多保留幾份備份\n目前設定：{self.settings.get("backup_keep_days")}',
            initialvalue=str(self.settings.get('backup_keep_days')),
            parent=self.win)
        if kd:
            try:
                self.settings.set('backup_keep_days', max(1, int(kd.strip())))
            except ValueError:
                pass

        messagebox.showinfo(
            '設定已儲存',
            f'自動備份時間：{self.settings.get("backup_time")}\n'
            f'保留備份數：{self.settings.get("backup_keep_days")}',
            parent=self.win)

    def _close(self):
        self._on_close()
        self.win.destroy()

    def lift(self):
        self.win.lift()
        self.win.focus_force()

# ============================================================
# App 協調器
# ============================================================

class App:
    def __init__(self):
        self.store    = TodoStore()
        self.settings = Settings()
        self._widget: FloatingWidget | None = None
        self._mgr:    ManagerWindow  | None = None

    def run(self):
        self._widget = FloatingWidget(
            store=self.store,
            settings=self.settings,
            on_open_mgr=self.open_manager)

        ReminderChecker(self.store, self._on_reminder).start()
        BackupManager(self.store, self.settings).start()

        if HAS_TRAY:
            self._start_tray()

        self._widget.root.mainloop()

    def open_manager(self):
        if self._mgr is not None:
            try:
                self._mgr.lift()
            except Exception:
                pass
            self._widget.flash_status('  管理員已開啟，請勿重複開啟')
            return
        self._mgr = ManagerWindow(
            store=self.store,
            settings=self.settings,
            on_close=self._mgr_closed,
            on_widget_refresh=lambda:
                self._widget.root.after(0, self._widget._do_refresh))

    def _mgr_closed(self):
        self._mgr = None

    def _on_reminder(self, todo: Todo):
        if self._widget:
            self._widget.trigger_alert(todo)

    def _start_tray(self):
        def make_icon():
            img = Image.new('RGBA', (64, 64), (0, 0, 0, 0))
            d   = ImageDraw.Draw(img)
            d.rounded_rectangle([2, 2, 62, 62], radius=10, fill='#E94560')
            for y, wi in [(14, 44), (24, 38), (34, 44), (44, 32)]:
                d.rounded_rectangle([10, y, wi, y + 5], radius=2, fill='white')
            return img

        menu = pystray.Menu(
            pystray.MenuItem('顯示提醒板',
                             lambda: self._widget.root.after(
                                 0, self._widget.root.deiconify),
                             default=True),
            pystray.MenuItem('開啟管理員',
                             lambda: self._widget.root.after(
                                 0, self.open_manager)),
            pystray.Menu.SEPARATOR,
            pystray.MenuItem('結束程式',
                             lambda: self._widget.root.after(0, self._quit)))

        self._tray = pystray.Icon('TodoReminder', make_icon(), APP_NAME, menu)
        threading.Thread(target=self._tray.run, daemon=True).start()

    def _quit(self):
        if HAS_TRAY:
            try:
                self._tray.stop()
            except Exception:
                pass
        self._widget.root.destroy()

# ============================================================
# 程式進入點
# ============================================================

def main():
    if not _acquire_mutex():
        root = tk.Tk()
        root.withdraw()
        messagebox.showinfo(APP_NAME,
                            f'{APP_NAME} 已在執行中！\n請查看右下角系統列圖示。')
        root.destroy()
        sys.exit(0)

    App().run()


if __name__ == '__main__':
    main()
