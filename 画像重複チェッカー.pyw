"""
画像重複チェッカー
指定フォルダ内の画像から「同じ／よく似た」画像をグループ化して表示し、
チェックした画像をゴミ箱に送る、または別フォルダへ移動できるツール。

必要ライブラリ: Pillow, imagehash, (任意)send2trash
    pip install Pillow imagehash send2trash

--------------------------------------------------------------------
このファイルは配布されていた実行ファイル(.exe)を逆コンパイルして復元した
ソースコードをベースに、破損していた箇所を修復し、
「複数ページにまたがる選択をまとめて削除/移動できる」機能を追加したものです。
"""
import os
import sys
import shutil
import threading
import queue
import subprocess
import concurrent.futures
import datetime
from pathlib import Path
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from PIL import Image, ImageTk, ImageDraw, ImageFilter
import imagehash

try:
    from send2trash import send2trash
    HAS_SEND2TRASH = True
except ImportError:
    HAS_SEND2TRASH = False

APP_TITLE = '画像重複チェッカー'
SUPPORTED_EXTS = {
    '.bmp', '.gif', '.jpg', '.png', '.tif', '.jpeg', '.tiff', '.webp'
}
THUMB_SIZE = (220, 220)
THUMB_SIZE_OPTIONS = {
    '小': 90,
    '中': 150,
    '大': 220,
}
GROUPS_PER_PAGE = 50
APP_BG = '#f3f4f6'
CARD_BG = '#ffffff'
BORDER = '#e1e3e7'
TEXT = '#33363b'
MUTED_TEXT = '#6b6f76'
PRIMARY = '#4c9a6b'
ACCENT_BLUE = '#5b7fa6'
DANGER = '#c1666b'
NEUTRAL = '#9aa0a6'
SHADOW = '#d5d7db'


def get_script_dir():
    if getattr(sys, 'frozen', False):
        return Path(sys.executable).parent
    return Path(__file__).resolve().parent


def get_icon_path():
    """icon.ico を .pyw / exe と同じフォルダから探す。無ければ None。"""
    p = get_script_dir() / 'icon.ico'
    return p if p.exists() else None


class _GroupingMixin:
    """ハッシュ計算済みのitems一覧から、しきい値に基づいて類似画像のグループを
    作る処理。ファイルの読み込み(スキャン)そのものとは独立しているので、
    ScanWorker(初回スキャン)とRegroupWorker(しきい値だけ変えた再グループ化)の
    両方から共通で使う。self.threshold / self.q / self._cancel を持つクラスで
    利用することを前提にしている。"""

    def _group_by_similarity(self, items):
        """類似画像をグループ化する。画像が1枚しかないグループ(=似た画像が
        見つからなかった単独の画像)は結果から除外する。"""
        n = len(items)
        parent = list(range(n))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a, b):
            ra = find(a)
            rb = find(b)
            if ra != rb:
                parent[ra] = rb

        try:
            self._compare_with_numpy(items, union)
        except ImportError:
            self._compare_naive(items, union)

        if self._cancel:
            return []

        groups_map = {}
        for idx in range(n):
            root = find(idx)
            groups_map.setdefault(root, []).append(items[idx])

        groups = [g for g in groups_map.values() if len(g) > 1]
        for g in groups:
            g.sort(key=lambda t: t[2], reverse=True)
        groups.sort(key=len, reverse=True)
        return groups

    def _compare_naive(self, items, union):
        n = len(items)
        total_pairs = n * (n - 1) // 2
        done_pairs = 0
        for i in range(n):
            for j in range(i + 1, n):
                if self._cancel:
                    return
                dist = items[i][1] - items[j][1]
                if dist <= self.threshold:
                    union(i, j)
                done_pairs += 1
                if done_pairs % 2000 == 0:
                    self.q.put(('compare_progress', (done_pairs, total_pairs)))

    def _compare_with_numpy(self, items, union):
        """総当たり比較は件数が多いと件数の2乗で時間がかかり、データ数が非常に
        多いフォルダでは実質的に終わらなくなってしまう。ここでは同じ総当たり判定を
        numpyの行列演算(BLAS)にまとめて計算することで、同じ正確さのまま
        大幅に高速化している(近似ではなく厳密な総当たり判定のまま)。"""
        import numpy as np
        n = len(items)
        A = np.array([it[1].hash.flatten() for it in items]).astype(np.float32)
        rowsum = A.sum(axis=1)
        AT = A.T.copy()
        target_cells = 20000000
        block = max(1, min(2048, target_cells // max(n, 1)))
        done = 0
        for start in range(0, n, block):
            if self._cancel:
                return
            end = min(start + block, n)
            sub = A[start:end]
            dot = sub @ AT
            dist = rowsum[start:end, None] + rowsum[None, :] - 2 * dot
            for local_i in range(end - start):
                gi = start + local_i
                if gi + 1 >= n:
                    continue
                row = dist[local_i, gi + 1:]
                matches = np.nonzero(row <= self.threshold)[0]
                for off in matches:
                    union(gi, gi + 1 + int(off))
            done = end
            self.q.put(('compare_progress', (done, n)))


class ScanWorker(_GroupingMixin, threading.Thread):

    def __init__(self, folder, recursive, threshold, out_queue):
        super().__init__(daemon=True)
        self.folder = folder
        self.recursive = recursive
        self.threshold = threshold
        self.q = out_queue
        self._cancel = False
        self._stop_early = False

    def cancel(self):
        self._cancel = True

    def stop_early(self):
        self._stop_early = True

    def run(self):
        try:
            files = self._collect_files()
            total = len(files)
            self.q.put(('status', f'{total}枚の画像を読み込み中...'))
            items = []
            completed = 0
            lock = threading.Lock()
            max_workers = min(8, max(2, (os.cpu_count() or 4)))
            with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as ex:
                futures = {ex.submit(self._process_one, p): p for p in files}
                for fut in concurrent.futures.as_completed(futures):
                    if self._cancel:
                        ex.shutdown(wait=False, cancel_futures=True)
                        self.q.put(('cancelled', None))
                        return
                    result = fut.result()
                    if result is not None:
                        items.append(result)
                    with lock:
                        completed += 1
                        c = completed
                    if c % 5 == 0 or c == total:
                        self.q.put(('progress', (c, total)))
                    if self._stop_early:
                        ex.shutdown(wait=False, cancel_futures=True)
                        self.q.put(('status', f'{c}枚まで読み込んだところで打ち切りました。グループ化しています...'))
                        break

            if self._cancel:
                self.q.put(('cancelled', None))
                return
            self.q.put(('status', f'{len(items)}枚で類似画像をグループ化中...'))
            groups = self._group_by_similarity(items)
            if self._cancel:
                self.q.put(('cancelled', None))
                return
            self.q.put(('done', (groups, items)))
        except Exception as e:
            self.q.put(('error', str(e)))

    def _process_one(self, p):
        """1枚の画像を読み込み、pHash・サイズ・表示用サムネイル(縮小済みPIL Image)を
        まとめて作っておく。ここで縮小画像も作成しておくことで、後で結果一覧に
        表示する際に画像を再度デコードし直す必要がなくなり、体感速度が大きく改善する。"""
        try:
            im = Image.open(p)
            im = im.convert('RGB')
            h = imagehash.phash(im)
            w, ht = im.size
            thumb = im.copy()
            thumb.thumbnail(THUMB_SIZE)
            size_bytes = p.stat().st_size
            return (p, h, size_bytes, w, ht, thumb)
        except Exception:
            return None

    def _collect_files(self):
        files = []
        if self.recursive:
            for root, _dirs, names in os.walk(self.folder):
                for n in names:
                    if Path(n).suffix.lower() in SUPPORTED_EXTS:
                        files.append(Path(root) / n)
        else:
            for p in self.folder.iterdir():
                if p.is_file() and p.suffix.lower() in SUPPORTED_EXTS:
                    files.append(p)
        return files


class RegroupWorker(_GroupingMixin, threading.Thread):
    """スキャン済みのitems(読み込み・ハッシュ計算まで終わったデータ)を使って、
    しきい値だけ変えてグループ化をやり直す。ファイルの再読み込みは行わないため、
    初回スキャンよりずっと短時間で終わる。"""

    def __init__(self, items, threshold, out_queue):
        super().__init__(daemon=True)
        self.items = items
        self.threshold = threshold
        self.q = out_queue
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def stop_early(self):
        self._cancel = True

    def run(self):
        try:
            self.q.put(('status', f'{len(self.items)}枚をしきい値{self.threshold}で再グループ化中...'))
            groups = self._group_by_similarity(self.items)
            if self._cancel:
                self.q.put(('cancelled', None))
                return
            self.q.put(('done', (groups, self.items)))
        except Exception as e:
            self.q.put(('error', str(e)))


class RoundedButton(tk.Canvas):
    SHADOW_H = 3

    def __init__(self, parent, text, command, *, radius=10, bg, fg='#ffffff',
                 hover_bg=None, disabled_bg=None, disabled_fg=None, font=None,
                 padx=14, pady=8, fixed_width=None, stretch_height=False):
        self._text = text
        self._command = command
        self._radius = radius
        self._bg_color = bg
        self._hover_bg = hover_bg or self._shade(bg, -12)
        self._disabled_bg = disabled_bg or self._shade(bg, 30)
        self._fg = fg
        self._disabled_fg = disabled_fg or self._shade(fg, -40) if fg.startswith('#') else fg
        self._font = font or ('', 11, 'bold')
        self._state = 'normal'
        self._stretch_height = stretch_height

        import tkinter.font as tkfont
        f = tkfont.Font(font=self._font)
        lines = text.split('\n')
        text_w = max(f.measure(line) for line in lines)
        text_h = f.metrics('linespace') * len(lines)

        self._bw = fixed_width if fixed_width is not None else text_w + padx * 2
        self._bh = text_h + pady * 2 + self.SHADOW_H
        super().__init__(parent, width=self._bw, height=self._bh, highlightthickness=0, bd=0)

        try:
            self.configure(bg=parent.cget('bg'))
        except tk.TclError:
            try:
                self.configure(bg=parent.winfo_toplevel().cget('bg'))
            except Exception:
                pass

        self._photo_normal = ImageTk.PhotoImage(self._make_button_image(self._bg_color))
        self._photo_hover = ImageTk.PhotoImage(self._make_button_image(self._hover_bg))
        self._photo_disabled = ImageTk.PhotoImage(self._make_button_image(self._disabled_bg))
        self._render('normal')
        self.bind('<Button-1>', self._on_click)
        self.bind('<Enter>', self._on_enter)
        self.bind('<Leave>', self._on_leave)

    def _on_resize(self, event):
        h = event.height
        if h < 20 or h == self._bh:
            return
        self._bh = h
        self._photo_normal = ImageTk.PhotoImage(self._make_button_image(self._bg_color))
        self._photo_hover = ImageTk.PhotoImage(self._make_button_image(self._hover_bg))
        self._photo_disabled = ImageTk.PhotoImage(self._make_button_image(self._disabled_bg))
        self._render('disabled' if self._state == 'disabled' else 'normal')

    def _shade(self, hex_color, amount):
        hex_color = hex_color.lstrip('#')
        r = int(hex_color[0:2], 16)
        g = int(hex_color[2:4], 16)
        b = int(hex_color[4:6], 16)
        r = max(0, min(255, r + amount))
        g = max(0, min(255, g + amount))
        b = max(0, min(255, b + amount))
        return f'#{r:02x}{g:02x}{b:02x}'

    def _lerp_color(self, c1, c2, t):
        r1 = int(c1[1:3], 16)
        g1 = int(c1[3:5], 16)
        b1 = int(c1[5:7], 16)
        r2 = int(c2[1:3], 16)
        g2 = int(c2[3:5], 16)
        b2 = int(c2[5:7], 16)
        r = int(r1 + (r2 - r1) * t)
        g = int(g1 + (g2 - g1) * t)
        b = int(b1 + (b2 - b1) * t)
        return f'#{r:02x}{g:02x}{b:02x}'

    def _make_button_image(self, base_color):
        """光沢感のあるボタン画像を作る。上を明るく・下を暗くした縦グラデーションの
        本体に、ぼかしを入れた柔らかい影を敷く(PILでラスタライズしてCanvasに貼る)。"""
        h = self._bh
        w = self._bw
        sh = self.SHADOW_H
        r = min(self._radius, (w - 2) / 2, (h - 2) / 2)
        img = Image.new('RGBA', (w, h), (0, 0, 0, 0))
        shadow_layer = Image.new('RGBA', (w, h), (0, 0, 0, 0))
        ImageDraw.Draw(shadow_layer).rounded_rectangle(
            [1, 1 + sh, w - 1, h - 1], radius=r, fill=(0, 0, 0, 70))
        shadow_layer = shadow_layer.filter(ImageFilter.GaussianBlur(1.2))
        img.alpha_composite(shadow_layer)

        body_h = max(1, h - 1 - sh)
        lighter = self._shade(base_color, 45)
        darker = self._shade(base_color, -35)
        grad = Image.new('RGB', (w, body_h))
        for y in range(body_h):
            t = y / max(1, body_h - 1)
            if t < 0.45:
                c = self._lerp_color(lighter, base_color, t / 0.45)
            else:
                c = self._lerp_color(base_color, darker, (t - 0.45) / 0.55)
            grad.paste(Image.new('RGB', (w, 1), c), (0, y))

        mask = Image.new('L', (w, body_h), 0)
        ImageDraw.Draw(mask).rounded_rectangle(
            [1, 0, w - 1, body_h - 1], radius=r, fill=255)
        body_rgba = Image.new('RGBA', (w, body_h), (0, 0, 0, 0))
        body_rgba.paste(grad, (0, 0), mask)
        img.alpha_composite(body_rgba, (0, 1))
        return img

    def _render(self, state):
        self.delete('all')
        photo = {
            'normal': self._photo_normal,
            'hover': self._photo_hover,
            'disabled': self._photo_disabled,
        }[state]
        self.create_image(0, 0, anchor='nw', image=photo)
        fg = self._fg if state != 'disabled' else self._disabled_fg
        self.create_text(self._bw / 2, (self._bh - self.SHADOW_H) / 2, text=self._text,
                          fill=fg, font=self._font, justify='center')

    def _on_click(self, _event):
        if self._state == 'disabled':
            return
        if self._command:
            self._command()

    def _on_enter(self, _event):
        if self._state != 'disabled':
            self._render('hover')
            self.configure(cursor='hand2')

    def _on_leave(self, _event):
        if self._state != 'disabled':
            self._render('normal')
            self.configure(cursor='')

    def configure(self, **kwargs):
        if 'state' in kwargs:
            self._state = kwargs.pop('state')
            self._render('disabled' if self._state == 'disabled' else 'normal')
        if kwargs:
            super().configure(**kwargs)

    config = configure

    def cget(self, key):
        if key == 'state':
            return self._state
        return super().cget(key)


class RoundedSlider(tk.Canvas):

    def __init__(self, parent, from_, to, variable, command, length,
                 track_h=6, thumb_r=9, track_color='#e1e3e7', fill_color=PRIMARY,
                 thumb_color='#ffffff', thumb_border=PRIMARY):
        self.from_ = from_
        self.to = to
        self.length = length
        self.thumb_r = thumb_r
        self.track_h = track_h
        self.variable = variable
        self.command = command
        self.track_color = track_color
        self.fill_color = fill_color
        self.thumb_color = thumb_color
        self.thumb_border = thumb_border
        self._dragging = False
        w = length + thumb_r * 2
        h = thumb_r * 2 + 6
        super().__init__(parent, width=w, height=h, highlightthickness=0, bd=0)

        try:
            self.configure(bg=parent.cget('bg'))
        except tk.TclError:
            try:
                self.configure(bg=parent.winfo_toplevel().cget('bg'))
            except Exception:
                pass

        self.bind('<Button-1>', self._on_press)
        self.bind('<B1-Motion>', self._on_drag)
        self.bind('<ButtonRelease-1>', self._on_release)
        self.bind('<Enter>', lambda e: self.configure(cursor='hand2'))
        self.bind('<Leave>', lambda e: self.configure(cursor=''))
        self._redraw()

    def _value_to_x(self, value):
        span = self.to - self.from_
        frac = (value - self.from_) / span if span else 0
        return self.thumb_r + frac * self.length

    def _x_to_value(self, x):
        frac = (x - self.thumb_r) / self.length
        frac = max(0, min(1, frac))
        return round(self.from_ + frac * (self.to - self.from_))

    def _redraw(self):
        self.delete('all')
        y = self.thumb_r + 2
        x0 = self.thumb_r
        x1 = self.thumb_r + self.length
        self.create_line(x0, y, x1, y, width=self.track_h, capstyle='round', fill=self.track_color)
        val = self.variable.get()
        thumb_x = self._value_to_x(val)
        self.create_line(x0, y, thumb_x, y, width=self.track_h, capstyle='round', fill=self.fill_color)
        r = self.thumb_r
        self.create_oval(thumb_x - r, (y - r) + 2, thumb_x + r, y + r + 2, fill=SHADOW, outline=SHADOW)
        self.create_oval(thumb_x - r, y - r, thumb_x + r, y + r, fill=self.thumb_color,
                          outline=self.thumb_border, width=1)

    def _set_from_x(self, x):
        val = self._x_to_value(x)
        if val != self.variable.get():
            self.variable.set(val)
            if self.command:
                self.command(val)
        self._redraw()

    def _on_press(self, event):
        self._dragging = True
        self._set_from_x(event.x)

    def _on_drag(self, event):
        if self._dragging:
            self._set_from_x(event.x)

    def _on_release(self, _event):
        self._dragging = False


class App(tk.Tk):

    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.geometry('800x750')
        self.minsize(800, 500)
        self._apply_window_icon()
        self.folder_var = tk.StringVar()
        self.recursive_var = tk.BooleanVar(value=True)
        self.threshold_var = tk.IntVar(value=0)
        self.thumb_size_var = tk.StringVar(value='中')
        self.action_msg_var = tk.StringVar(value='')
        self._busy = False
        self._spinner_chars = '⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏'
        self._spinner_i = 0
        self._group_frames = []
        self._scan_items = []
        self._all_groups = []
        self._current_page = 0
        self.thumb_cache = []
        self.card_widgets = []
        # 複数ページをまたいで選択状態を保持するための集合。
        # (以前は self.card_widgets だけで選択を管理していたため、
        #  ページ切替のたびに選択がリセットされていた)
        self._selected_paths = set()
        self.worker = None
        self.q = queue.Queue()
        self._build_style()
        self._build_ui()
        self.report_callback_exception = self._log_callback_exception
        self._tick_spinner()

    def _apply_window_icon(self):
        """ウィンドウ左上・タスクバーに表示されるアイコンを設定する。
        (exeファイル自体のアイコンとは別物で、tkinter側で明示的に
        指定しないと反映されない)
        icon.icoが無い/読み込みに失敗しても、通常起動を継続する。"""
        icon_path = get_icon_path()
        if icon_path is None:
            return
        try:
            self.iconbitmap(default=str(icon_path))
        except Exception:
            pass

    def _build_style(self):
        self.configure(bg=APP_BG)
        style = ttk.Style(self)
        try:
            style.theme_use('clam')
        except tk.TclError:
            pass

        style.configure('.', background=APP_BG, foreground=TEXT, font=('', 10))
        style.configure('TFrame', background=APP_BG)
        style.configure('TLabel', background=APP_BG, foreground=TEXT)
        style.configure('TCheckbutton', background=APP_BG, foreground=TEXT)
        style.map('TCheckbutton', background=[('active', APP_BG)])
        style.configure('TButton', background=CARD_BG, foreground=TEXT, bordercolor=BORDER,
                         lightcolor=CARD_BG, darkcolor=CARD_BG, relief='flat', padding=(10, 6))
        style.map('TButton', background=[('active', '#f0f1f3')])
        style.configure('TEntry', fieldbackground=CARD_BG, bordercolor=BORDER,
                         lightcolor=BORDER, darkcolor=BORDER, foreground=TEXT)
        style.configure('TLabelframe', background=APP_BG, bordercolor=BORDER,
                         lightcolor=BORDER, darkcolor=BORDER)
        style.configure('TLabelframe.Label', background=APP_BG, foreground=MUTED_TEXT, font=('', 10, 'bold'))
        style.configure('Horizontal.TProgressbar', troughcolor='#e9eaec', background=PRIMARY,
                         bordercolor='#e9eaec', lightcolor=PRIMARY, darkcolor=PRIMARY)
        style.configure('Horizontal.TScrollbar', background='#c9cbd0', troughcolor=APP_BG,
                         bordercolor=APP_BG, arrowcolor=TEXT)
        style.configure('Vertical.TScrollbar', background='#c9cbd0', troughcolor=APP_BG,
                         bordercolor=APP_BG, arrowcolor=TEXT)
        style.configure('CardText.TLabel', background=CARD_BG, foreground=TEXT)
        style.configure('ThreshText.TLabel', background=CARD_BG, foreground=MUTED_TEXT)
        style.configure('CardText.TRadiobutton', background=CARD_BG, foreground=TEXT, focuscolor=CARD_BG)
        style.map('CardText.TRadiobutton', background=[('active', CARD_BG)])

    def _build_ui(self):
        top = ttk.Frame(self, padding=10)
        top.pack(fill='x')
        row1 = ttk.Frame(top)
        row1.pack(fill='x')
        ttk.Label(row1, text='対象フォルダ:').pack(side='left')
        RoundedButton(row1, text='使い方', command=self._show_help, bg='#eef0f2', fg=MUTED_TEXT,
                      font=('', 9), radius=12, padx=10, pady=6).pack(side='right')
        RoundedButton(row1, text='参照...', command=self._choose_folder, bg='#eef0f2', fg=TEXT,
                      font=('', 10), radius=12, padx=14, pady=7).pack(side='right', padx=(0, 6))
        ttk.Checkbutton(row1, text='サブフォルダも含む', variable=self.recursive_var).pack(side='right', padx=(0, 10))
        entry = ttk.Entry(row1, textvariable=self.folder_var)
        entry.pack(side='left', fill='x', expand=True, padx=5)

        row2 = ttk.Frame(top)
        row2.pack(fill='x', pady=(8, 0))
        thresh_outer = tk.Frame(row2, bg=CARD_BG, highlightbackground=BORDER, highlightthickness=1, bd=0)
        thresh_outer.pack(side='right')
        thresh_inner = tk.Frame(thresh_outer, bg=CARD_BG, padx=10, pady=6)
        thresh_inner.pack(fill='both', expand=True)
        self.thresh_label = ttk.Label(thresh_inner, text='', style='ThreshText.TLabel', anchor='w')
        self.thresh_label.pack(fill='x', anchor='w')
        slider = RoundedSlider(thresh_inner, from_=0, to=20, variable=self.threshold_var,
                                command=self._on_threshold_change, length=200)
        slider.pack(anchor='e', pady=(4, 0))
        self._on_threshold_change(None)

        size_outer = tk.Frame(row2, bg=CARD_BG, highlightbackground=BORDER, highlightthickness=1, bd=0)
        size_outer.pack(side='right', padx=(0, 12))
        size_inner = tk.Frame(size_outer, bg=CARD_BG, padx=10, pady=6)
        size_inner.pack(fill='both', expand=True)
        ttk.Label(size_inner, text='サムネイルサイズ', style='ThreshText.TLabel', anchor='w').pack(fill='x', anchor='w')
        size_radio_row = tk.Frame(size_inner, bg=CARD_BG)
        size_radio_row.pack(anchor='w', pady=(4, 0))
        for label in ('小', '中', '大'):
            ttk.Radiobutton(size_radio_row, text=label, value=label, variable=self.thumb_size_var,
                             command=self._on_thumb_size_change, style='CardText.TRadiobutton',
                             takefocus=0).pack(side='left', padx=(0, 8))

        msg_outer = tk.Frame(row2, bg=CARD_BG, highlightbackground=BORDER, highlightthickness=1, bd=0)
        msg_outer.pack(side='left', fill='both', expand=True)
        self.progress_msg_var = tk.StringVar(value='')
        self.progress_msg_label = tk.Label(msg_outer, textvariable=self.progress_msg_var, bg=CARD_BG,
                                            fg=MUTED_TEXT, font=('', 9), justify='left', anchor='nw',
                                            padx=10, pady=6, height=3)
        self.progress_msg_label.pack(fill='both', expand=True)
        self._progress_lines = {
            'load': '読み込み: -',
            'compare': '比較: -',
            'render': 'サムネイル表示: -',
        }
        self._refresh_progress_msg()

        row3 = ttk.Frame(top)
        row3.pack(fill='x', pady=(8, 0))
        self.scan_btn = RoundedButton(row3, text='スキャン開始', command=self._start_scan, bg=PRIMARY,
                                       fg='white', font=('', 11, 'bold'), radius=14, padx=16, pady=8)
        self.scan_btn.pack(side='right')
        self.regroup_btn = RoundedButton(row3, text='この設定でグループ更新', command=self._start_regroup,
                                          bg=ACCENT_BLUE, fg='white', font=('', 10, 'bold'), radius=14,
                                          padx=12, pady=8)
        self.regroup_btn.pack(side='right', padx=(0, 6))
        self.regroup_btn.configure(state='disabled')
        self.stop_early_btn = RoundedButton(row3, text='打ち切って進む', command=self._stop_early_clicked,
                                             bg=ACCENT_BLUE, fg='white', font=('', 9, 'bold'), radius=12,
                                             padx=10, pady=6)
        self.stop_early_btn.pack(side='right', padx=(0, 6))
        self.stop_early_btn.configure(state='disabled')
        self.cancel_btn = RoundedButton(row3, text='中止', command=self._cancel_scan, bg=NEUTRAL,
                                         fg='white', font=('', 10), radius=12, padx=12, pady=6)
        self.cancel_btn.pack(side='right', padx=(0, 6))
        self.cancel_btn.configure(state='disabled')
        self.progress = ttk.Progressbar(row3, mode='determinate')
        self.progress.pack(side='left', fill='x', expand=True, padx=(0, 8))

        pager_row = ttk.Frame(self, padding=(10, 0))
        pager_row.pack(fill='x')
        self.pager_prev_btn = RoundedButton(pager_row, text='◀ 前のページ', command=self._go_prev_page,
                                             bg='#eef0f2', fg=TEXT, font=('', 9), radius=10, padx=10, pady=5)
        self.pager_prev_btn.pack(side='left')
        self.pager_prev_btn.configure(state='disabled')
        self.pager_next_btn = RoundedButton(pager_row, text='次のページ ▶', command=self._go_next_page,
                                             bg='#eef0f2', fg=TEXT, font=('', 9), radius=10, padx=10, pady=5)
        self.pager_next_btn.pack(side='left', padx=(6, 0))
        self.pager_next_btn.configure(state='disabled')
        self.pager_var = tk.StringVar(value='')
        ttk.Label(pager_row, textvariable=self.pager_var, foreground=MUTED_TEXT).pack(side='left', padx=(12, 0))
        self.page_select_btn = RoundedButton(pager_row, text='このページの全グループで最大以外を選択',
                                              command=self._auto_select_page, bg=ACCENT_BLUE, fg='white',
                                              font=('', 9, 'bold'), radius=10, padx=10, pady=5)
        self.page_select_btn.pack(side='right')
        self.compact_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(pager_row, text='コンパクト表示', variable=self.compact_var,
                         command=self._on_compact_change).pack(side='right', padx=(0, 10))

        mid = ttk.Frame(self)
        mid.pack(fill='both', expand=True, padx=10)
        pin_width = self.scan_btn._bh
        self.pin_select_btn = RoundedButton(mid, text='表\n示\nグ\nル\nー\nプ\n中\nの\n最\n大\n以\n外\nを\n選\n択',
                                             command=self._auto_select_current_group, bg=ACCENT_BLUE,
                                             fg='white', font=('', 10, 'bold'), radius=8,
                                             fixed_width=pin_width, stretch_height=True)
        self.pin_select_btn.pack(side='right', fill='y', padx=(6, 0))
        self.canvas = tk.Canvas(mid, highlightthickness=0, bg=APP_BG)
        vscroll = ttk.Scrollbar(mid, orient='vertical', command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=vscroll.set)
        vscroll.pack(side='right', fill='y')
        self.canvas.pack(side='left', fill='both', expand=True)
        self.result_frame = ttk.Frame(self.canvas)
        self.result_window = self.canvas.create_window((0, 0), window=self.result_frame, anchor='nw')
        self.result_frame.bind('<Configure>', lambda e: self.canvas.configure(scrollregion=self.canvas.bbox('all')))
        self.canvas.bind('<Configure>', lambda e: self.canvas.itemconfig(self.result_window, width=e.width))
        self.canvas.bind_all('<MouseWheel>', self._on_mousewheel)
        vscroll.configure(command=self._on_scrollbar_move)

        bottom = ttk.Frame(self, padding=10)
        bottom.pack(fill='x')
        ttk.Label(bottom, textvariable=self.action_msg_var, foreground=MUTED_TEXT).pack(side='left')
        self.spinner_label = ttk.Label(bottom, text='', foreground=MUTED_TEXT, anchor='w')
        self.spinner_label.pack(side='left', padx=(16, 0))

        trash_label = '選択した画像をゴミ箱へ' if HAS_SEND2TRASH else '選択した画像を削除'
        RoundedButton(bottom, text='選択解除', command=self._clear_selection, bg=NEUTRAL, fg='white',
                      font=('', 11), radius=14).pack(side='right')
        RoundedButton(bottom, text='選択した画像を移動...', command=self._move_selected, bg=ACCENT_BLUE,
                      fg='white', font=('', 11, 'bold'), radius=14).pack(side='right', padx=6)
        RoundedButton(bottom, text=trash_label, command=self._delete_selected, bg=DANGER, fg='white',
                      font=('', 11, 'bold'), radius=14).pack(side='right', padx=6)

    def _reset_current_page_placeholders(self):
        """実体化済みのグループを一旦プレースホルダーに戻し、見えている範囲だけ
        読み込み直す(サムネイルサイズ/コンパクト表示の切り替えで共通して使う)。"""
        if not self._group_frames:
            return
        self.thumb_cache.clear()
        self.card_widgets.clear()
        for gf in self._group_frames:
            if not gf.winfo_exists():
                continue
            for child in gf.winfo_children():
                child.destroy()
            gf.configure(height=self.PLACEHOLDER_HEIGHT)
            gf.pack_propagate(False)
            ph_label = tk.Label(gf, text=f'グループ {gf._group_index} ({len(gf._group_data)}枚) - スクロールすると読み込みます',
                                 bg=APP_BG, fg=MUTED_TEXT)
            ph_label.pack(expand=True)
            gf._placeholder_label = ph_label
            gf._populated = False
        self.after(30, self._check_visible_groups)
        self.after(250, self._poll_visible_groups)

    def _on_thumb_size_change(self):
        self._reset_current_page_placeholders()

    def _on_compact_change(self):
        self._reset_current_page_placeholders()

    def _on_threshold_change(self, _val):
        v = self.threshold_var.get()
        if v <= 3:
            desc = '厳しい(ほぼ同一の画像のみ拾う)'
        elif v <= 8:
            desc = '普通'
        else:
            desc = '緩い(遠目に似ている程度も拾う)'
        self.thresh_label.config(text=f'類似度のしきい値: {v} ({desc})')

    def _refresh_progress_msg(self):
        self.progress_msg_var.set('\n'.join([
            self._progress_lines['load'],
            self._progress_lines['compare'],
            self._progress_lines['render'],
        ]))

    def _set_progress_line(self, key, text):
        self._progress_lines[key] = text
        self._refresh_progress_msg()

    def _reset_progress_lines(self):
        self._progress_lines = {
            'load': '読み込み: -',
            'compare': '比較: -',
            'render': 'サムネイル表示: -',
        }
        self._refresh_progress_msg()

    def _on_mousewheel(self, event):
        self.canvas.yview_scroll(int(-1 * (event.delta / 120)), 'units')
        self._check_visible_groups()

    def _on_scrollbar_move(self, *args):
        self.canvas.yview(*args)
        self._check_visible_groups()

    def _set_busy(self, busy):
        self._busy = busy
        if not busy:
            self.spinner_label.config(text='')

    def _tick_spinner(self):
        if self._busy:
            ch = self._spinner_chars[self._spinner_i % len(self._spinner_chars)]
            self.spinner_label.config(text=f'{ch}  処理中...  {ch}')
            self._spinner_i += 1
        self.after(120, self._tick_spinner)

    def _log_callback_exception(self, exc_type, exc_value, tb):
        import traceback
        log_path = get_script_dir() / 'error_log.txt'
        try:
            with open(log_path, 'a', encoding='utf-8') as f:
                f.write('========================================\n')
                f.write(datetime.datetime.now().isoformat() + '\n')
                traceback.print_exception(exc_type, exc_value, tb, file=f)
        except Exception:
            pass

    def _choose_folder(self):
        d = filedialog.askdirectory(title='対象フォルダを選択')
        if d:
            self.folder_var.set(d)

    def _show_help(self):
        exts = ', '.join(sorted(SUPPORTED_EXTS))
        messagebox.showinfo(APP_TITLE,
            f'【対応している拡張子】\n{exts}\n\n'
            '【使い方】\n'
            '1. 「参照...」で対象フォルダを選ぶ(サブフォルダも含めるかはチェックで切り替え)\n'
            '2. 「類似度のしきい値」で、どれくらい似ていたら同じグループとみなすかを調整する\n'
            '   (値が小さいほど厳密に「そっくり」なものだけを拾う)\n'
            '3. 「スキャン開始」でフォルダを読み込み、類似・重複画像をグループ化する\n'
            '4. しきい値だけ変えて見直したい場合は、「この設定でグループ更新」を押すと\n'
            '   フォルダの再読み込みをせずにグループだけ組み直せる\n'
            '5. 各画像はクリックで選択(赤枠)、右端の固定ボタンや各グループの\n'
            '   ボタンで「最大以外」をまとめて選択できる\n'
            '6. 選択した画像は「ゴミ箱へ」または「移動...」で整理する\n'
            '   (複数ページにまたがって選択しても、まとめて削除・移動できます)\n\n'
            'グループ数が多い場合は複数ページに分けて表示されます。')

    def _start_scan(self):
        folder = self.folder_var.get().strip()
        if not folder or not Path(folder).is_dir():
            messagebox.showwarning(APP_TITLE, '有効なフォルダを選択してください。')
            return
        self._clear_results()
        self._selected_paths.clear()
        self.action_msg_var.set('')
        self._reset_progress_lines()
        self._all_groups = []
        self._current_page = 0
        self._scan_items = []
        self.regroup_btn.config(state='disabled')
        self.pager_var.set('')
        self.pager_prev_btn.config(state='disabled')
        self.pager_next_btn.config(state='disabled')
        self.scan_btn.config(state='disabled')
        self.cancel_btn.config(state='normal')
        self.stop_early_btn.config(state='normal')
        self.progress.config(value=0, maximum=100)
        self._set_busy(True)
        self.worker = ScanWorker(Path(folder), self.recursive_var.get(), self.threshold_var.get(), self.q)
        self.worker.start()
        self.after(100, self._poll_queue)

    def _start_regroup(self):
        if not self._scan_items:
            return
        self._clear_results()
        self._selected_paths.clear()
        self.action_msg_var.set('')
        self._reset_progress_lines()
        self._all_groups = []
        self._current_page = 0
        self.pager_var.set('')
        self.pager_prev_btn.config(state='disabled')
        self.pager_next_btn.config(state='disabled')
        self.scan_btn.config(state='disabled')
        self.regroup_btn.config(state='disabled')
        self.cancel_btn.config(state='normal')
        self.progress.config(value=0, maximum=100)
        self._set_busy(True)
        self.worker = RegroupWorker(self._scan_items, self.threshold_var.get(), self.q)
        self.worker.start()
        self.after(100, self._poll_queue)

    def _cancel_scan(self):
        if self.worker:
            self.worker.cancel()
        self._set_progress_line('load', '読み込み: 中止しています...')
        self.cancel_btn.config(state='disabled')
        self.stop_early_btn.config(state='disabled')

    def _stop_scan_early(self):
        if self.worker:
            self.worker.stop_early()
        self._set_progress_line('load', '読み込み: ここまでの結果で打ち切っています...')
        self.cancel_btn.config(state='disabled')
        self.stop_early_btn.config(state='disabled')

    def _stop_early_clicked(self):
        if self.worker and self.worker.is_alive():
            self._stop_scan_early()

    def _poll_queue(self):
        try:
            kind, payload = self.q.get_nowait()
            if kind == 'status':
                self._set_progress_line('load', payload)
            elif kind == 'progress':
                i, total = payload
                self.progress.config(maximum=max(total, 1), value=i)
                self._set_progress_line('load', f'読み込み: {i}/{total}枚')
            elif kind == 'compare_progress':
                done, total = payload
                self.progress.config(maximum=max(total, 1), value=done)
                self._set_progress_line('compare', f'比較: {done}/{total}')
            elif kind == 'done':
                self._on_scan_done(payload)
                return
            elif kind == 'cancelled':
                self._set_progress_line('load', '読み込み: 中止しました')
                self._scan_finished_ui()
                self._set_busy(False)
                return
            elif kind == 'error':
                messagebox.showerror(APP_TITLE, f'エラーが発生しました:\n{payload}')
                self._scan_finished_ui()
                self._set_busy(False)
                return
        except queue.Empty:
            pass
        self.after(100, self._poll_queue)

    def _scan_finished_ui(self):
        self.scan_btn.config(state='normal')
        self.cancel_btn.config(state='disabled')
        self.stop_early_btn.config(state='disabled')
        self.regroup_btn.config(state='normal' if self._scan_items else 'disabled')

    def _on_scan_done(self, payload):
        groups, items = payload
        self._scan_items = items
        self.cancel_btn.config(state='disabled')
        self.stop_early_btn.config(state='disabled')
        self.scan_btn.config(state='normal')
        self.regroup_btn.config(state='normal' if self._scan_items else 'disabled')
        if not groups:
            self._set_progress_line('render', 'サムネイル表示: 対象なし(類似・重複する画像は見つかりませんでした)')
            self._set_busy(False)
            return
        self._all_groups = groups
        self._current_page = 0
        self._render_page()

    def _clear_results(self):
        for child in self.result_frame.winfo_children():
            child.destroy()
        self.thumb_cache.clear()
        self.card_widgets.clear()
        self._group_frames = []

    def _render_page(self):
        total_groups = len(self._all_groups)
        total_pages = max(1, (total_groups + GROUPS_PER_PAGE - 1) // GROUPS_PER_PAGE)
        self._current_page = max(0, min(self._current_page, total_pages - 1))
        start = self._current_page * GROUPS_PER_PAGE
        end = min(start + GROUPS_PER_PAGE, total_groups)
        page_groups = self._all_groups[start:end]
        self._clear_results()
        total_imgs_page = sum(len(g) for g in page_groups)
        for offset, group in enumerate(page_groups):
            gi = start + offset + 1
            self._create_group_placeholder(gi, group)
        self._set_progress_line(
            'render',
            f'サムネイル表示: {start + 1}〜{end}グループ目 / 全{total_groups}グループ'
            f'(このページ{total_imgs_page}枚、表示分のみ順次読み込み)')
        self.progress.config(maximum=1, value=1)
        self._set_busy(False)
        self.pager_var.set(f'ページ {self._current_page + 1} / {total_pages}(全{total_groups}グループ)')
        self.pager_prev_btn.config(state='normal' if self._current_page > 0 else 'disabled')
        self.pager_next_btn.config(state='normal' if self._current_page < total_pages - 1 else 'disabled')
        self.canvas.yview_moveto(0)
        self.after(30, self._check_visible_groups)
        self.after(250, self._poll_visible_groups)

    def _go_prev_page(self):
        if self._current_page > 0:
            self._current_page -= 1
            self._render_page()

    def _go_next_page(self):
        total_pages = max(1, (len(self._all_groups) + GROUPS_PER_PAGE - 1) // GROUPS_PER_PAGE)
        if self._current_page < total_pages - 1:
            self._current_page += 1
            self._render_page()

    def _poll_visible_groups(self):
        if not getattr(self, 'canvas', None) or not self.canvas.winfo_exists():
            return
        self._check_visible_groups()
        if any((not gf._populated) for gf in self._group_frames if gf.winfo_exists()):
            self.after(250, self._poll_visible_groups)

    PLACEHOLDER_HEIGHT = 190

    def _create_group_placeholder(self, gi, group):
        gframe = tk.Frame(self.result_frame, bg=APP_BG, highlightbackground=BORDER,
                           highlightthickness=1, bd=0, height=self.PLACEHOLDER_HEIGHT)
        gframe.pack(fill='x', padx=4, pady=6)
        gframe.pack_propagate(False)
        ph_label = tk.Label(gframe, text=f'グループ {gi} ({len(group)}枚) - スクロールすると読み込みます',
                             bg=APP_BG, fg=MUTED_TEXT)
        ph_label.pack(expand=True)
        gframe._group_index = gi
        gframe._group_data = group
        gframe._populated = False
        gframe._placeholder_label = ph_label
        self._group_frames.append(gframe)

    def _check_visible_groups(self):
        if not getattr(self, 'canvas', None) or not self.canvas.winfo_exists():
            return
        if not self._group_frames:
            return
        top_y = self.canvas.canvasy(0)
        bottom_y = top_y + self.canvas.winfo_height()
        margin = 600
        MAX_PER_CHECK = 4
        done_count = 0
        for gf in self._group_frames:
            if done_count >= MAX_PER_CHECK:
                break
            if not gf.winfo_exists() or gf._populated:
                continue
            gy = gf.winfo_y()
            gh = gf.winfo_height()
            if gy + gh > top_y - margin and gy < bottom_y + margin:
                self._populate_group(gf)
                done_count += 1

    def _populate_group(self, gframe):
        if gframe._populated:
            return
        gframe._populated = True
        gi = gframe._group_index
        group = gframe._group_data
        for child in gframe.winfo_children():
            child.destroy()
        gframe.pack_propagate(True)
        gframe.configure(height=1)
        header = ttk.Label(gframe, text=f'グループ {gi} ({len(group)}枚)', font=('', 10, 'bold'))
        header.pack(anchor='w', padx=4, pady=(4, 0))
        _canvas, row_frame = self._create_hscroll_row(gframe)
        compact = self.compact_var.get()
        for item in group:
            path, _phash, size_bytes, w, h, thumb = item
            self._add_card(row_frame, gframe, path, size_bytes, w, h, thumb=thumb, compact=compact)

    def _create_hscroll_row(self, parent):
        """グループ内のサムネイル行を横スクロール可能にするキャンバスを作る。
        横スクロールバーと、マウスドラッグ(左ボタンで掴んで横に送る)の両方に対応する。"""
        outer = ttk.Frame(parent)
        outer.pack(fill='x', expand=True)
        canvas = tk.Canvas(outer, highlightthickness=0, bg=APP_BG)
        hbar = ttk.Scrollbar(outer, orient='horizontal', command=canvas.xview)
        canvas.configure(xscrollcommand=hbar.set)
        canvas.pack(side='top', fill='x', expand=True)
        hbar.pack(side='top', fill='x')
        inner = ttk.Frame(canvas)
        canvas.create_window((0, 0), window=inner, anchor='nw')

        def on_inner_configure(_e, c=canvas):
            c.configure(scrollregion=c.bbox('all'))

        inner.bind('<Configure>', on_inner_configure)
        self._bind_drag_scroll(canvas, canvas)
        self._bind_drag_scroll(inner, canvas)
        canvas.bind('<Shift-MouseWheel>', lambda e, c=canvas: c.xview_scroll(int(-1 * (e.delta / 120)), 'units'))
        return (canvas, inner)

    def _bind_drag_scroll(self, widget, canvas):
        widget.bind('<ButtonPress-1>', lambda e, c=canvas: c.scan_mark(e.x_root, e.y_root), add='+')
        widget.bind('<B1-Motion>', lambda e, c=canvas: c.scan_dragto(e.x_root, e.y_root, gain=1), add='+')

    SELECTED_BORDER = DANGER
    SELECTED_THICKNESS = 4

    def _add_card(self, row_frame, group_frame, path, size_bytes, w, h, thumb=None, compact=False):
        card = tk.Frame(row_frame, bg=CARD_BG, highlightbackground=BORDER, highlightthickness=1, bd=0)
        pad = 3 if compact else 8
        inner = tk.Frame(card, bg=CARD_BG, padx=pad, pady=pad)
        inner.pack()
        card.pack(side='left', padx=3 if compact else 6, pady=2 if compact else 4)
        self._bind_drag_scroll(card, self._find_ancestor_canvas(row_frame))
        self._bind_drag_scroll(inner, self._find_ancestor_canvas(row_frame))

        disp_size = THUMB_SIZE_OPTIONS.get(self.thumb_size_var.get(), 150)
        photo = None
        if thumb is not None:
            try:
                disp = thumb.copy()
                disp.thumbnail((disp_size, disp_size))
                photo = ImageTk.PhotoImage(disp)
            except Exception:
                photo = None

        if photo is None:
            try:
                im = Image.open(path)
                im = im.convert('RGB')
                im.thumbnail((disp_size, disp_size))
                photo = ImageTk.PhotoImage(im)
            except Exception:
                photo = None

        if photo:
            self.thumb_cache.append(photo)
            lbl_img = tk.Label(inner, image=photo, cursor='hand2', bg=CARD_BG)
        else:
            lbl_img = tk.Label(inner, text='(表示不可)', width=18, height=8, bg=CARD_BG, fg=MUTED_TEXT)
        lbl_img.pack()
        lbl_img.bind('<Double-Button-1>', lambda e, p=path: self._open_image(p))

        # 選択状態はページをまたいで self._selected_paths に永続化する。
        # var はこのカード(ウィジェット)がある間だけ有効な「表示用」の状態で、
        # 実際の選択の正本は self._selected_paths 側。
        var = tk.BooleanVar(value=(path in self._selected_paths))

        def _update_border(*_args, _card=card, _path=path, _var=var):
            if _var.get():
                _card.configure(highlightbackground=self.SELECTED_BORDER, highlightthickness=self.SELECTED_THICKNESS)
                self._selected_paths.add(_path)
            else:
                _card.configure(highlightbackground=BORDER, highlightthickness=1)
                self._selected_paths.discard(_path)

        var.trace_add('write', _update_border)
        _update_border()  # 復元されたページで選択済みの枠線をすぐに反映する

        def _toggle_select(_e=None, v=var):
            v.set(not v.get())

        lbl_img.bind('<Button-1>', _toggle_select, add='+')

        size_kb = size_bytes / 1024
        info_lbl = None
        if not compact:
            info_text = f'{path.name}\n{w}x{h} / {size_kb:.0f}KB'
            info_lbl = ttk.Label(inner, text=info_text, wraplength=150, justify='center',
                                  font=('', 8), style='CardText.TLabel')
            info_lbl.pack()

        entry = {
            'path': path,
            'var': var,
            'card': card,
            'group_frame': group_frame,
            'row_frame': row_frame,
        }
        self.card_widgets.append(entry)

        menu = tk.Menu(card, tearoff=0)
        menu.add_command(label='この画像を開く', command=lambda p=path: self._open_image(p))
        menu.add_separator()
        trash_txt = 'この画像をゴミ箱へ' if HAS_SEND2TRASH else 'この画像を削除'
        menu.add_command(label=trash_txt, command=lambda e=entry: self._delete_entries([e]))
        menu.add_command(label='この画像を移動...', command=lambda e=entry: self._move_entries([e]))

        def show_menu(event, m=menu):
            m.tk_popup(event.x_root, event.y_root)

        for w_ in (card, lbl_img, info_lbl):
            if w_ is not None:
                w_.bind('<Button-3>', show_menu)

        return entry

    def _find_ancestor_canvas(self, widget):
        w = widget
        while w is not None:
            if isinstance(w, tk.Canvas):
                return w
            w = w.master
        return self.canvas

    def _open_image(self, path):
        try:
            if os.name == 'nt':
                os.startfile(str(path))
            elif sys.platform == 'darwin':
                subprocess.run(['open', str(path)])
            else:
                subprocess.run(['xdg-open', str(path)])
        except Exception as e:
            messagebox.showerror(APP_TITLE, f'画像を開けませんでした:\n{e}')

    def _clear_selection(self):
        self._selected_paths.clear()
        for e in self.card_widgets:
            e['var'].set(False)

    def _auto_select_group(self, group_frame):
        """このグループの中で先頭(=一番サイズが大きい)以外を選択する。"""
        entries = [e for e in self.card_widgets if e['group_frame'] is group_frame]
        for i, e in enumerate(entries):
            e['var'].set(i != 0)

    def _auto_select_page(self):
        """現在のページの全グループについて「最大以外を選択」を適用する。
        未読み込み(プレースホルダー)のグループは先に読み込んでから処理する。"""
        pending = list(self._group_frames)

        def _do_select():
            for gf in self._group_frames:
                if gf.winfo_exists():
                    self._auto_select_group(gf)

        if not pending:
            _do_select()
            return

        self._set_busy(True)

        def _step():
            if not pending:
                self._set_busy(False)
                _do_select()
                return
            gf = pending.pop(0)
            if gf.winfo_exists() and not gf._populated:
                self._populate_group(gf)
            self.after(10, _step)

        _step()

    def _clear_group_selection(self, group_frame):
        for e in self.card_widgets:
            if e['group_frame'] is group_frame:
                e['var'].set(False)

    def _visible_group_frames(self):
        if not self._group_frames:
            return []
        top_y = self.canvas.canvasy(0)
        bottom_y = top_y + self.canvas.winfo_height()
        visible = []
        for gf in self._group_frames:
            if not gf.winfo_exists():
                continue
            gy = gf.winfo_y()
            gh = gf.winfo_height()
            if gy + gh > top_y and gy < bottom_y:
                visible.append(gf)
        return visible

    def _auto_select_current_group(self):
        frames = self._visible_group_frames()
        if not frames:
            messagebox.showinfo(APP_TITLE, '対象のグループがありません。')
            return
        for gf in frames:
            if not gf._populated:
                self._populate_group(gf)
            self._auto_select_group(gf)

    def _get_selected_entries(self):
        """現在のページで選択されているものだけでなく、
        他のページで選択されたまま残っているものも含めて、
        選択中の全画像を返す。"""
        live = [e for e in self.card_widgets if e['var'].get()]
        live_paths = {e['path'] for e in live}
        others = [
            {'path': p, 'var': None, 'card': None, 'group_frame': None, 'row_frame': None}
            for p in self._selected_paths if p not in live_paths
        ]
        return live + others

    def _remove_entries_from_ui(self, entries):
        touched_groups = set()
        for e in entries:
            self._selected_paths.discard(e['path'])
            if e.get('card') is None:
                # 別ページにあり、現在は表示されていない画像。
                continue
            try:
                e['card'].destroy()
            except tk.TclError:
                pass
            if e in self.card_widgets:
                self.card_widgets.remove(e)
            touched_groups.add(id(e['group_frame']))

        remaining_by_group = {}
        for e in self.card_widgets:
            remaining_by_group.setdefault(id(e['group_frame']), []).append(e)

        for e in entries:
            gf = e.get('group_frame')
            if gf is None:
                continue
            gid = id(gf)
            if gid in touched_groups and not remaining_by_group.get(gid):
                try:
                    gf.destroy()
                except tk.TclError:
                    pass
                touched_groups.discard(gid)

    def _delete_selected(self):
        entries = self._get_selected_entries()
        if not entries:
            messagebox.showinfo(APP_TITLE, '画像が選択されていません。')
            return
        self._delete_entries(entries)

    def _delete_entries(self, entries):
        names = '\n'.join(str(e['path'].name) for e in entries[:10])
        more = '' if len(entries) <= 10 else f'\n...他{len(entries) - 10}枚'
        dest = 'ゴミ箱' if HAS_SEND2TRASH else '完全削除(元に戻せません)'
        if not messagebox.askyesno(APP_TITLE,
                                    f'{len(entries)}枚の画像を{dest}に送ります。\n\n{names}{more}\n\nよろしいですか?'):
            return
        errors = []
        done = []
        for e in entries:
            p = e['path']
            try:
                if HAS_SEND2TRASH:
                    send2trash(str(p))
                else:
                    p.unlink()
                done.append(e)
            except Exception as ex:
                errors.append(f'{p.name}: {ex}')
        self._remove_entries_from_ui(done)
        if errors:
            messagebox.showerror(APP_TITLE, '一部の画像を削除できませんでした:\n' + '\n'.join(errors))
        self.action_msg_var.set(f'{len(done)}枚を削除しました。')

    def _move_selected(self):
        entries = self._get_selected_entries()
        if not entries:
            messagebox.showinfo(APP_TITLE, '画像が選択されていません。')
            return
        self._move_entries(entries)

    def _move_entries(self, entries):
        dest_dir = filedialog.askdirectory(title='移動先フォルダを選択')
        if not dest_dir:
            return
        dest_dir = Path(dest_dir)
        errors = []
        done = []
        for e in entries:
            p = e['path']
            try:
                target = dest_dir / p.name
                if target.exists():
                    stem, suffix = p.stem, p.suffix
                    i = 1
                    while target.exists():
                        target = dest_dir / f'{stem}_{i}{suffix}'
                        i += 1
                shutil.move(str(p), str(target))
                done.append(e)
            except Exception as ex:
                errors.append(f'{p.name}: {ex}')
        self._remove_entries_from_ui(done)
        if errors:
            messagebox.showerror(APP_TITLE, '一部の画像を移動できませんでした:\n' + '\n'.join(errors))
        self.action_msg_var.set(f'{len(done)}枚を移動しました。')


def main():
    app = App()
    app.mainloop()


if __name__ == '__main__':
    main()
