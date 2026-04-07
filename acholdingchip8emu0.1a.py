#!/usr/bin/env python3
"""
===============================================================================
  Qwen's CHIP-8 EMU v2.3 — Production Ready
  Originally Developed & Optimized by Qwen (Alibaba Cloud)
  Fixed & Hardened by Claude / CatsDK — A.C Holdings / Team Flames (c) 1999-2026
  Frontend: Tkinter (Asymmetrical Void-Terminal HUD Layout)
  Backend:  Pure Python CHIP-8 CPU/VM Implementation
  Language: Python 3.14+ Compatible
  License:  MIT / Educational Use
===============================================================================
  Patch Notes (CatsDK):
    v2.2:
    - Fixed VF flag ordering in all 8XY_ ALU ops (VF must be set LAST)
    - Fixed EX9E/EXA1 key index bounds (mask V[x] & 0xF)
    - Fixed DXYN sprite clipping vs wrapping (clip at screen edge, per COSMAC VIP)
    - Fixed PhotoImage display scaling (64x32 → 320x160 via zoom)
    - Fixed overlapping GUI panel geometry (reg/view/ctrl no longer stack)
    - Fixed FPS counter jitter (rolling average over 10 frames)
    - Fixed stack overflow/underflow guards (sp bounds check)
    - Fixed BCD / FX55 / FX65 memory bounds checks
    - Fixed reset() not clearing wait_key_reg
    - Added 0x0NNN (SYS addr) as no-op for legacy ROM compat
    - Window resized to 820x480 for proper HUD layout
    v2.3:
    - Added full SNES9x-style menu strip (File, Cheat, Emulation, Options, Window, Help)
    - Recent ROMs list (persistent per session, up to 10 entries)
    - Cheat engine: raw opcode poke + memory search (exact / comparative)
    - Emulation menu: Run/Pause, Reset, Soft Reset, Speed presets, Frame Advance
    - Options: Video scale, BG/FG color pickers, sound toggle, input display
    - Window: toggle register spine, toggle keypad, toggle status bar
    - Help: About dialog, keymap reference
===============================================================================
"""

import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, colorchooser
import random
import time
import sys
import collections

# ==============================================================================
# CHIP-8 CORE EMULATOR (Backend)
# ==============================================================================
class Chip8:
    """Pure-Python CHIP-8 virtual machine — cycle-stepped, no deps."""

    FONTSET = [
        0xF0, 0x90, 0x90, 0x90, 0xF0,  # 0
        0x20, 0x60, 0x20, 0x20, 0x70,  # 1
        0xF0, 0x10, 0xF0, 0x80, 0xF0,  # 2
        0xF0, 0x10, 0xF0, 0x10, 0xF0,  # 3
        0x90, 0x90, 0xF0, 0x10, 0x10,  # 4
        0xF0, 0x80, 0xF0, 0x10, 0xF0,  # 5
        0xF0, 0x80, 0xF0, 0x90, 0xF0,  # 6
        0xF0, 0x10, 0x20, 0x40, 0x40,  # 7
        0xF0, 0x90, 0xF0, 0x90, 0xF0,  # 8
        0xF0, 0x90, 0xF0, 0x10, 0xF0,  # 9
        0xF0, 0x90, 0xF0, 0x90, 0x90,  # A
        0xE0, 0x90, 0xE0, 0x90, 0xE0,  # B
        0xF0, 0x80, 0x80, 0x80, 0xF0,  # C
        0xE0, 0x90, 0x90, 0x90, 0xE0,  # D
        0xF0, 0x80, 0xF0, 0x80, 0xF0,  # E
        0xF0, 0x80, 0xF0, 0x80, 0x80,  # F
    ]

    MEM_SIZE = 4096
    PROG_START = 0x200
    DISPLAY_W = 64
    DISPLAY_H = 32
    STACK_DEPTH = 16
    NUM_REGS = 16
    NUM_KEYS = 16

    def __init__(self):
        self.reset()

    def reset(self):
        """Full cold reset — clears all state including fontset reload."""
        self.memory = bytearray(self.MEM_SIZE)
        self.V = [0] * self.NUM_REGS
        self.I = 0
        self.pc = self.PROG_START
        self.sp = -1
        self.stack = [0] * self.STACK_DEPTH
        self.delay_timer = 0
        self.sound_timer = 0
        self.display = [[0] * self.DISPLAY_W for _ in range(self.DISPLAY_H)]
        self.keys = [0] * self.NUM_KEYS
        self.draw_flag = False
        self.waiting_for_key = False
        self.wait_key_reg = 0
        self.paused = False
        self.halted = False
        # Load font into 0x000..0x04F
        for i, b in enumerate(self.FONTSET):
            self.memory[i] = b

    def soft_reset(self):
        """Soft reset — keeps ROM in memory, resets CPU/display state."""
        self.V = [0] * self.NUM_REGS
        self.I = 0
        self.pc = self.PROG_START
        self.sp = -1
        self.stack = [0] * self.STACK_DEPTH
        self.delay_timer = 0
        self.sound_timer = 0
        self.display = [[0] * self.DISPLAY_W for _ in range(self.DISPLAY_H)]
        self.keys = [0] * self.NUM_KEYS
        self.draw_flag = True
        self.waiting_for_key = False
        self.wait_key_reg = 0
        self.paused = False
        self.halted = False

    def load_rom(self, path: str) -> bool:
        """Load a .ch8 binary into memory at 0x200. Returns True on success."""
        try:
            with open(path, "rb") as f:
                rom = f.read()
            max_size = self.MEM_SIZE - self.PROG_START
            if len(rom) > max_size:
                raise ValueError(f"ROM too large: {len(rom)} bytes (max {max_size})")
            self.memory[self.PROG_START : self.PROG_START + len(rom)] = rom
            return True
        except Exception as exc:
            print(f"[CHIP-8] ROM load error: {exc}", file=sys.stderr)
            return False

    # ------------------------------------------------------------------
    # Main loop
    # ------------------------------------------------------------------
    def cycle(self, cycles_per_frame: int = 15):
        """Run N instruction cycles then tick timers once (60 Hz rate)."""
        if self.paused or self.waiting_for_key or self.halted:
            return
        for _ in range(cycles_per_frame):
            if self.pc < self.PROG_START or self.pc + 1 >= self.MEM_SIZE:
                self.halted = True
                break
            opcode = (self.memory[self.pc] << 8) | self.memory[self.pc + 1]
            self.pc += 2
            self._execute(opcode)
        # Timers tick at 60 Hz regardless of CPU speed
        if self.delay_timer > 0:
            self.delay_timer -= 1
        if self.sound_timer > 0:
            self.sound_timer -= 1

    def step(self):
        """Execute exactly one instruction (for frame-advance / debugging)."""
        if self.waiting_for_key or self.halted:
            return
        if self.pc < self.PROG_START or self.pc + 1 >= self.MEM_SIZE:
            self.halted = True
            return
        opcode = (self.memory[self.pc] << 8) | self.memory[self.pc + 1]
        self.pc += 2
        self._execute(opcode)

    # ------------------------------------------------------------------
    # Instruction decoder + ALU
    # ------------------------------------------------------------------
    def _execute(self, opcode: int):
        x = (opcode >> 8) & 0xF
        y = (opcode >> 4) & 0xF
        n = opcode & 0xF
        nn = opcode & 0xFF
        nnn = opcode & 0xFFF

        match opcode & 0xF000:
            case 0x0000:
                if opcode == 0x00E0:
                    self.display = [[0] * self.DISPLAY_W for _ in range(self.DISPLAY_H)]
                    self.draw_flag = True
                elif opcode == 0x00EE:
                    if self.sp < 0:
                        self.halted = True
                        return
                    self.pc = self.stack[self.sp]
                    self.sp -= 1

            case 0x1000:
                self.pc = nnn

            case 0x2000:
                if self.sp >= self.STACK_DEPTH - 1:
                    self.halted = True
                    return
                self.sp += 1
                self.stack[self.sp] = self.pc
                self.pc = nnn

            case 0x3000:
                if self.V[x] == nn:
                    self.pc += 2

            case 0x4000:
                if self.V[x] != nn:
                    self.pc += 2

            case 0x5000:
                if n == 0 and self.V[x] == self.V[y]:
                    self.pc += 2

            case 0x6000:
                self.V[x] = nn

            case 0x7000:
                self.V[x] = (self.V[x] + nn) & 0xFF

            case 0x8000:
                self._alu(x, y, n)

            case 0x9000:
                if n == 0 and self.V[x] != self.V[y]:
                    self.pc += 2

            case 0xA000:
                self.I = nnn

            case 0xB000:
                self.pc = (self.V[0] + nnn) & 0xFFF

            case 0xC000:
                self.V[x] = random.randint(0, 0xFF) & nn

            case 0xD000:
                self._draw_sprite(x, y, n)

            case 0xE000:
                key_idx = self.V[x] & 0xF
                if nn == 0x9E and self.keys[key_idx]:
                    self.pc += 2
                elif nn == 0xA1 and not self.keys[key_idx]:
                    self.pc += 2

            case 0xF000:
                self._fx(x, nn)

    def _alu(self, x: int, y: int, op: int):
        """8XY_ ALU operations — VF is always written LAST."""
        vx = self.V[x]
        vy = self.V[y]

        match op:
            case 0x0:
                self.V[x] = vy
            case 0x1:
                self.V[x] = vx | vy
                self.V[0xF] = 0
            case 0x2:
                self.V[x] = vx & vy
                self.V[0xF] = 0
            case 0x3:
                self.V[x] = vx ^ vy
                self.V[0xF] = 0
            case 0x4:
                result = vx + vy
                self.V[x] = result & 0xFF
                self.V[0xF] = 1 if result > 0xFF else 0
            case 0x5:
                self.V[x] = (vx - vy) & 0xFF
                self.V[0xF] = 1 if vx >= vy else 0
            case 0x6:
                self.V[x] = (vx >> 1) & 0xFF
                self.V[0xF] = vx & 0x1
            case 0x7:
                self.V[x] = (vy - vx) & 0xFF
                self.V[0xF] = 1 if vy >= vx else 0
            case 0xE:
                self.V[x] = (vx << 1) & 0xFF
                self.V[0xF] = (vx >> 7) & 0x1

    def _draw_sprite(self, x_reg: int, y_reg: int, height: int):
        """DXYN — draw 8-pixel-wide sprite with XOR. Clips at screen edge (COSMAC VIP)."""
        vx = self.V[x_reg] & 63
        vy = self.V[y_reg] & 31
        self.V[0xF] = 0

        for row in range(height):
            py = vy + row
            if py >= self.DISPLAY_H:
                break
            addr = self.I + row
            if addr >= self.MEM_SIZE:
                break
            sprite_byte = self.memory[addr]
            for col in range(8):
                px = vx + col
                if px >= self.DISPLAY_W:
                    break
                if (sprite_byte & (0x80 >> col)) != 0:
                    if self.display[py][px] == 1:
                        self.V[0xF] = 1
                    self.display[py][px] ^= 1
        self.draw_flag = True

    def _fx(self, x: int, nn: int):
        """FX__ instructions — timers, BCD, load/store, key wait."""
        match nn:
            case 0x07:
                self.V[x] = self.delay_timer
            case 0x0A:
                self.waiting_for_key = True
                self.wait_key_reg = x
            case 0x15:
                self.delay_timer = self.V[x]
            case 0x18:
                self.sound_timer = self.V[x]
            case 0x1E:
                self.I = (self.I + self.V[x]) & 0xFFF
            case 0x29:
                self.I = (self.V[x] & 0xF) * 5
            case 0x33:
                if self.I + 2 < self.MEM_SIZE:
                    val = self.V[x]
                    self.memory[self.I] = val // 100
                    self.memory[self.I + 1] = (val // 10) % 10
                    self.memory[self.I + 2] = val % 10
            case 0x55:
                for i in range(x + 1):
                    if self.I + i < self.MEM_SIZE:
                        self.memory[self.I + i] = self.V[i]
            case 0x65:
                for i in range(x + 1):
                    if self.I + i < self.MEM_SIZE:
                        self.V[i] = self.memory[self.I + i]

    def set_key(self, key: int, state: bool):
        """Update key state; unblock FX0A wait if a key is pressed."""
        if 0 <= key < self.NUM_KEYS:
            self.keys[key] = 1 if state else 0
            if state and self.waiting_for_key:
                self.V[self.wait_key_reg] = key
                self.waiting_for_key = False


# ==============================================================================
# TKINTER FRONTEND — Void-Terminal HUD + SNES9x Menu Strip
# ==============================================================================
class Chip8GUI:
    """Tkinter frontend with SNES9x-style menu bar, asymmetrical HUD, live register spine."""

    PIXEL_SCALE = 5
    SCREEN_W = Chip8.DISPLAY_W * PIXEL_SCALE  # 320
    SCREEN_H = Chip8.DISPLAY_H * PIXEL_SCALE  # 160

    WIN_W = 820
    WIN_H = 500  # slightly taller to accommodate menu bar

    COL_BG = "#000000"
    COL_ACCENT = "#0088FF"
    COL_ACCENT_HI = "#00CCFF"
    COL_DIM = "#444444"
    COL_TEXT = "#00BFFF"
    COL_PX_ON = "#FFFFFF"
    COL_PX_OFF = "#000000"
    COL_STATUS = "#777777"

    KEY_MAP = {
        "1": 0x1, "2": 0x2, "3": 0x3, "4": 0xC,
        "q": 0x4, "w": 0x5, "e": 0x6, "r": 0xD,
        "a": 0x7, "s": 0x8, "d": 0x9, "f": 0xE,
        "z": 0xA, "x": 0x0, "c": 0xB, "v": 0xF,
    }

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Qwen's CHIP-8 EMU v2.3 — CatsDK Patch")
        self.root.resizable(False, False)
        self.root.geometry(f"{self.WIN_W}x{self.WIN_H}")
        self.root.configure(bg=self.COL_BG)
        self._setup_theme()

        self.chip8 = Chip8()
        self.cycles_per_frame = 15
        self.fps = 60
        self.running = True
        self.last_frame_time = time.time()
        self.fps_history: collections.deque[float] = collections.deque(maxlen=10)

        # Session state for menus
        self.recent_roms: list[str] = []
        self.max_recent = 10
        self.current_rom_path: str | None = None
        self.cheats_active: list[tuple[int, int, str]] = []  # (addr, val, description)
        self.sound_enabled = tk.BooleanVar(value=True)
        self.show_regs = tk.BooleanVar(value=True)
        self.show_keypad = tk.BooleanVar(value=True)
        self.show_statusbar = tk.BooleanVar(value=True)
        self.show_input_display = tk.BooleanVar(value=True)
        self.show_fps_counter = tk.BooleanVar(value=True)
        self.show_framectr = tk.BooleanVar(value=False)
        self.frame_count = 0

        self.setup_menubar()
        self.setup_ui()
        self.setup_bindings()
        self.update_loop()

    # ------------------------------------------------------------------
    # Theme
    # ------------------------------------------------------------------
    def _setup_theme(self):
        theme = {
            "*Button.background": self.COL_BG,
            "*Button.foreground": self.COL_ACCENT,
            "*Button.activeBackground": self.COL_BG,
            "*Button.activeForeground": self.COL_ACCENT_HI,
            "*Button.highlightBackground": self.COL_BG,
            "*Button.highlightColor": self.COL_ACCENT,
            "*Button.relief": "flat",
            "*Scale.background": self.COL_BG,
            "*Scale.foreground": self.COL_ACCENT,
            "*Scale.troughColor": "#222222",
        }
        for opt, val in theme.items():
            self.root.option_add(opt, val)

    def _make_btn(self, parent, text, command):
        return tk.Button(
            parent, text=text, command=command,
            bg=self.COL_BG, fg=self.COL_ACCENT,
            activebackground=self.COL_BG, activeforeground=self.COL_ACCENT_HI,
            highlightbackground=self.COL_BG, highlightcolor=self.COL_ACCENT,
            highlightthickness=0, relief="flat", bd=0,
            font=("Consolas", 10, "bold"), cursor="hand2", takefocus=0,
        )

    # ==================================================================
    # SNES9x-STYLE MENU BAR
    # ==================================================================
    def setup_menubar(self):
        menubar = tk.Menu(self.root, bg="#1A1A1A", fg="#CCCCCC",
                          activebackground="#003366", activeforeground="#FFFFFF",
                          font=("Consolas", 9), relief="flat", bd=0)

        # ── File ──────────────────────────────────────────────────────
        file_menu = tk.Menu(menubar, tearoff=0, bg="#1A1A1A", fg="#CCCCCC",
                            activebackground="#003366", activeforeground="#FFFFFF",
                            font=("Consolas", 9))
        file_menu.add_command(label="Open ROM...", accelerator="Ctrl+O",
                              command=self.load_rom)
        self.root.bind("<Control-o>", lambda e: self.load_rom())

        # Recent ROMs submenu (populated dynamically)
        self.recent_menu = tk.Menu(file_menu, tearoff=0, bg="#1A1A1A", fg="#CCCCCC",
                                   activebackground="#003366", activeforeground="#FFFFFF",
                                   font=("Consolas", 9))
        file_menu.add_cascade(label="Recent ROMs", menu=self.recent_menu)
        self._rebuild_recent_menu()

        file_menu.add_separator()
        file_menu.add_command(label="Close ROM", command=self._close_rom)
        file_menu.add_separator()
        file_menu.add_command(label="Save State...", accelerator="F5",
                              command=self._save_state)
        self.root.bind("<F5>", lambda e: self._save_state())
        file_menu.add_command(label="Load State...", accelerator="F7",
                              command=self._load_state)
        self.root.bind("<F7>", lambda e: self._load_state())
        file_menu.add_separator()
        file_menu.add_command(label="ROM Info...", command=self._show_rom_info)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", accelerator="Alt+F4",
                              command=self._on_close)
        menubar.add_cascade(label="File", menu=file_menu)

        # ── Cheat ─────────────────────────────────────────────────────
        cheat_menu = tk.Menu(menubar, tearoff=0, bg="#1A1A1A", fg="#CCCCCC",
                             activebackground="#003366", activeforeground="#FFFFFF",
                             font=("Consolas", 9))
        cheat_menu.add_command(label="Apply Cheat Code...",
                               command=self._apply_cheat)
        cheat_menu.add_command(label="Remove All Cheats",
                               command=self._remove_all_cheats)
        cheat_menu.add_separator()
        cheat_menu.add_command(label="Search Memory — Exact Value...",
                               command=self._cheat_search_exact)
        cheat_menu.add_command(label="Search Memory — Changed Value...",
                               command=self._cheat_search_changed)
        cheat_menu.add_separator()
        cheat_menu.add_command(label="Poke Address...",
                               command=self._poke_address)
        cheat_menu.add_command(label="Peek Address...",
                               command=self._peek_address)
        cheat_menu.add_separator()
        cheat_menu.add_command(label="View Active Cheats...",
                               command=self._view_cheats)
        menubar.add_cascade(label="Cheat", menu=cheat_menu)

        # ── Emulation ─────────────────────────────────────────────────
        emu_menu = tk.Menu(menubar, tearoff=0, bg="#1A1A1A", fg="#CCCCCC",
                           activebackground="#003366", activeforeground="#FFFFFF",
                           font=("Consolas", 9))
        emu_menu.add_command(label="Run / Pause", accelerator="Esc",
                             command=self.toggle_pause)
        self.root.bind("<Escape>", lambda e: self.toggle_pause())
        emu_menu.add_command(label="Reset (Hard)", accelerator="Ctrl+R",
                             command=self._do_hard_reset)
        self.root.bind("<Control-r>", lambda e: self._do_hard_reset())
        emu_menu.add_command(label="Reset (Soft)",
                             command=self._do_soft_reset)
        emu_menu.add_separator()
        emu_menu.add_command(label="Frame Advance", accelerator=".",
                             command=self._frame_advance)
        self.root.bind("<period>", lambda e: self._frame_advance())
        emu_menu.add_separator()

        # Speed presets submenu
        speed_menu = tk.Menu(emu_menu, tearoff=0, bg="#1A1A1A", fg="#CCCCCC",
                             activebackground="#003366", activeforeground="#FFFFFF",
                             font=("Consolas", 9))
        speed_presets = [
            ("25% (Slow-Mo)", 4), ("50% (Half)", 7), ("75%", 11),
            ("100% (Normal)", 15), ("150%", 22), ("200% (Turbo)", 30),
            ("400% (Warp)", 60),
        ]
        for label, cpf in speed_presets:
            speed_menu.add_command(label=label,
                                   command=lambda c=cpf: self._set_speed(c))
        emu_menu.add_cascade(label="Speed", menu=speed_menu)

        emu_menu.add_separator()
        emu_menu.add_command(label="Turbo Toggle", accelerator="Tab",
                             command=self._turbo_toggle)
        self.root.bind("<Tab>", lambda e: self._turbo_toggle())
        self._turbo_on = False
        self._saved_speed = 15
        menubar.add_cascade(label="Emulation", menu=emu_menu)

        # ── Options ───────────────────────────────────────────────────
        opt_menu = tk.Menu(menubar, tearoff=0, bg="#1A1A1A", fg="#CCCCCC",
                           activebackground="#003366", activeforeground="#FFFFFF",
                           font=("Consolas", 9))

        # Video submenu
        video_menu = tk.Menu(opt_menu, tearoff=0, bg="#1A1A1A", fg="#CCCCCC",
                             activebackground="#003366", activeforeground="#FFFFFF",
                             font=("Consolas", 9))
        for s in [3, 4, 5, 6, 8, 10]:
            w = Chip8.DISPLAY_W * s
            h = Chip8.DISPLAY_H * s
            video_menu.add_command(label=f"{s}x  ({w}×{h})",
                                   command=lambda sc=s: self._set_scale(sc))
        opt_menu.add_cascade(label="Video — Scale", menu=video_menu)

        # Color submenu
        color_menu = tk.Menu(opt_menu, tearoff=0, bg="#1A1A1A", fg="#CCCCCC",
                             activebackground="#003366", activeforeground="#FFFFFF",
                             font=("Consolas", 9))
        color_menu.add_command(label="Foreground (Pixel ON)...",
                               command=self._pick_fg_color)
        color_menu.add_command(label="Background (Pixel OFF)...",
                               command=self._pick_bg_color)
        color_menu.add_separator()
        color_presets = [
            ("Classic (White on Black)", "#FFFFFF", "#000000"),
            ("Game Boy (Green)", "#9BBC0F", "#0F380F"),
            ("Amber Terminal", "#FFB000", "#1A0800"),
            ("Cyan Terminal", "#00FFCC", "#001A14"),
            ("Paper (Dark on White)", "#222222", "#F0F0E8"),
        ]
        for label, fg, bg in color_presets:
            color_menu.add_command(label=label,
                                   command=lambda f=fg, b=bg: self._set_colors(f, b))
        opt_menu.add_cascade(label="Video — Colors", menu=color_menu)

        opt_menu.add_separator()
        opt_menu.add_checkbutton(label="Sound Enabled", variable=self.sound_enabled)
        opt_menu.add_separator()
        opt_menu.add_command(label="Input Configuration...",
                             command=self._show_input_config)
        menubar.add_cascade(label="Options", menu=opt_menu)

        # ── Window ────────────────────────────────────────────────────
        win_menu = tk.Menu(menubar, tearoff=0, bg="#1A1A1A", fg="#CCCCCC",
                           activebackground="#003366", activeforeground="#FFFFFF",
                           font=("Consolas", 9))
        win_menu.add_checkbutton(label="Register Spine", variable=self.show_regs,
                                 command=self._toggle_registers)
        win_menu.add_checkbutton(label="Input Matrix / Keypad", variable=self.show_keypad,
                                 command=self._toggle_keypad)
        win_menu.add_checkbutton(label="Status Bar", variable=self.show_statusbar,
                                 command=self._toggle_statusbar)
        win_menu.add_separator()
        win_menu.add_checkbutton(label="FPS Counter in Status", variable=self.show_fps_counter)
        win_menu.add_checkbutton(label="Frame Counter in Status", variable=self.show_framectr)
        win_menu.add_checkbutton(label="Input Display in Status", variable=self.show_input_display)
        menubar.add_cascade(label="Window", menu=win_menu)

        # ── Help ──────────────────────────────────────────────────────
        help_menu = tk.Menu(menubar, tearoff=0, bg="#1A1A1A", fg="#CCCCCC",
                            activebackground="#003366", activeforeground="#FFFFFF",
                            font=("Consolas", 9))
        help_menu.add_command(label="Keymap Reference...",
                              command=self._show_keymap)
        help_menu.add_command(label="CHIP-8 Opcode Reference...",
                              command=self._show_opcode_ref)
        help_menu.add_separator()
        help_menu.add_command(label="About...", command=self._show_about)
        menubar.add_cascade(label="Help", menu=help_menu)

        self.root.config(menu=menubar)

    # ==================================================================
    # MENU ACTIONS — File
    # ==================================================================
    def _rebuild_recent_menu(self):
        self.recent_menu.delete(0, "end")
        if not self.recent_roms:
            self.recent_menu.add_command(label="(empty)", state="disabled")
        else:
            for i, path in enumerate(self.recent_roms):
                short = path.replace("\\", "/").split("/")[-1]
                self.recent_menu.add_command(
                    label=f"{i+1}. {short}",
                    command=lambda p=path: self._open_recent(p),
                )
            self.recent_menu.add_separator()
            self.recent_menu.add_command(label="Clear List",
                                         command=self._clear_recent)

    def _add_recent(self, path: str):
        if path in self.recent_roms:
            self.recent_roms.remove(path)
        self.recent_roms.insert(0, path)
        self.recent_roms = self.recent_roms[:self.max_recent]
        self._rebuild_recent_menu()

    def _open_recent(self, path: str):
        self.chip8.reset()
        if self.chip8.load_rom(path):
            self.current_rom_path = path
            filename = path.replace("\\", "/").split("/")[-1]
            self.rom_var.set(f"LOADED: {filename}")
            self.chip8.halted = False
            self._add_recent(path)
        else:
            messagebox.showerror("Load Error", f"Failed to load ROM:\n{path}")
            if path in self.recent_roms:
                self.recent_roms.remove(path)
                self._rebuild_recent_menu()

    def _clear_recent(self):
        self.recent_roms.clear()
        self._rebuild_recent_menu()

    def _close_rom(self):
        self.chip8.reset()
        self.render_display()
        self.current_rom_path = None
        self.rom_var.set("NO ROM LOADED")

    def _save_state(self):
        """Serialize full CPU + memory state to a file."""
        if not self.current_rom_path:
            messagebox.showinfo("Save State", "No ROM loaded.")
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".c8s",
            filetypes=[("CHIP-8 Save State", "*.c8s"), ("All Files", "*.*")],
        )
        if not path:
            return
        try:
            import json
            state = {
                "version": "2.3",
                "memory": list(self.chip8.memory),
                "V": self.chip8.V[:],
                "I": self.chip8.I,
                "pc": self.chip8.pc,
                "sp": self.chip8.sp,
                "stack": self.chip8.stack[:],
                "delay_timer": self.chip8.delay_timer,
                "sound_timer": self.chip8.sound_timer,
                "display": [row[:] for row in self.chip8.display],
            }
            with open(path, "w") as f:
                json.dump(state, f)
            self.rom_var.set(f"STATE SAVED: {path.split('/')[-1]}")
        except Exception as exc:
            messagebox.showerror("Save Error", str(exc))

    def _load_state(self):
        """Restore full CPU + memory state from a file."""
        path = filedialog.askopenfilename(
            filetypes=[("CHIP-8 Save State", "*.c8s"), ("All Files", "*.*")],
        )
        if not path:
            return
        try:
            import json
            with open(path, "r") as f:
                state = json.load(f)
            self.chip8.memory = bytearray(state["memory"])
            self.chip8.V = state["V"]
            self.chip8.I = state["I"]
            self.chip8.pc = state["pc"]
            self.chip8.sp = state["sp"]
            self.chip8.stack = state["stack"]
            self.chip8.delay_timer = state["delay_timer"]
            self.chip8.sound_timer = state["sound_timer"]
            self.chip8.display = state["display"]
            self.chip8.draw_flag = True
            self.chip8.halted = False
            self.chip8.paused = False
            self.chip8.waiting_for_key = False
            self.rom_var.set(f"STATE LOADED: {path.split('/')[-1]}")
        except Exception as exc:
            messagebox.showerror("Load Error", str(exc))

    def _show_rom_info(self):
        if not self.current_rom_path:
            messagebox.showinfo("ROM Info", "No ROM loaded.")
            return
        import os
        try:
            sz = os.path.getsize(self.current_rom_path)
        except OSError:
            sz = 0
        name = self.current_rom_path.replace("\\", "/").split("/")[-1]
        info = (
            f"Filename: {name}\n"
            f"Path: {self.current_rom_path}\n"
            f"Size: {sz} bytes ({sz:#x})\n"
            f"Load Address: 0x{Chip8.PROG_START:04X}\n"
            f"End Address: 0x{Chip8.PROG_START + sz:04X}\n"
            f"Max ROM Size: {Chip8.MEM_SIZE - Chip8.PROG_START} bytes"
        )
        messagebox.showinfo("ROM Information", info)

    # ==================================================================
    # MENU ACTIONS — Cheat
    # ==================================================================
    def _apply_cheat(self):
        """Apply a cheat in ADDR:VAL hex format (e.g., 200:FF)."""
        code = simpledialog.askstring(
            "Apply Cheat Code",
            "Enter cheat (ADDR:VAL hex, e.g. 200:FF):",
            parent=self.root,
        )
        if not code:
            return
        try:
            parts = code.strip().replace(" ", "").split(":")
            if len(parts) != 2:
                raise ValueError("Format: ADDR:VAL")
            addr = int(parts[0], 16)
            val = int(parts[1], 16) & 0xFF
            if not (0 <= addr < Chip8.MEM_SIZE):
                raise ValueError(f"Address 0x{addr:04X} out of range")
            self.chip8.memory[addr] = val
            desc = f"0x{addr:04X} = 0x{val:02X}"
            self.cheats_active.append((addr, val, desc))
            messagebox.showinfo("Cheat Applied", f"Poked {desc}")
        except ValueError as exc:
            messagebox.showerror("Cheat Error", str(exc))

    def _remove_all_cheats(self):
        if self.cheats_active:
            self.cheats_active.clear()
            messagebox.showinfo("Cheats", "All active cheats cleared.")
        else:
            messagebox.showinfo("Cheats", "No cheats are active.")

    def _cheat_search_exact(self):
        """Search memory for an exact byte value."""
        val_str = simpledialog.askstring(
            "Search Memory",
            "Enter byte value to find (hex, e.g. 0A):",
            parent=self.root,
        )
        if val_str is None:
            return
        try:
            val = int(val_str.strip(), 16) & 0xFF
        except ValueError:
            messagebox.showerror("Search Error", "Invalid hex value.")
            return
        results = [
            f"0x{addr:04X}"
            for addr in range(Chip8.MEM_SIZE)
            if self.chip8.memory[addr] == val
        ]
        if results:
            display = "\n".join(results[:50])
            extra = f"\n... and {len(results)-50} more" if len(results) > 50 else ""
            messagebox.showinfo(
                "Search Results",
                f"Found 0x{val:02X} at {len(results)} address(es):\n\n{display}{extra}",
            )
        else:
            messagebox.showinfo("Search Results", f"Value 0x{val:02X} not found.")

    def _cheat_search_changed(self):
        """Snapshot memory — user can re-run to find which bytes changed."""
        if not hasattr(self, "_mem_snapshot"):
            self._mem_snapshot = bytes(self.chip8.memory)
            messagebox.showinfo(
                "Memory Snapshot",
                "Snapshot taken. Play a bit, then run this again to see what changed.",
            )
            return
        old = self._mem_snapshot
        changed = []
        for addr in range(Chip8.MEM_SIZE):
            if self.chip8.memory[addr] != old[addr]:
                changed.append(
                    f"0x{addr:04X}: {old[addr]:02X} → {self.chip8.memory[addr]:02X}"
                )
        self._mem_snapshot = bytes(self.chip8.memory)
        if changed:
            display = "\n".join(changed[:60])
            extra = f"\n... and {len(changed)-60} more" if len(changed) > 60 else ""
            messagebox.showinfo(
                "Changed Addresses",
                f"{len(changed)} byte(s) changed:\n\n{display}{extra}",
            )
        else:
            messagebox.showinfo("Changed Addresses", "No bytes changed since last snapshot.")

    def _poke_address(self):
        inp = simpledialog.askstring(
            "Poke Address",
            "Format: ADDR VAL (hex, e.g. 200 FF):",
            parent=self.root,
        )
        if not inp:
            return
        try:
            parts = inp.strip().split()
            addr = int(parts[0], 16)
            val = int(parts[1], 16) & 0xFF
            if not (0 <= addr < Chip8.MEM_SIZE):
                raise ValueError("Out of range")
            self.chip8.memory[addr] = val
        except (ValueError, IndexError):
            messagebox.showerror("Poke Error", "Invalid input. Use: ADDR VAL (hex)")

    def _peek_address(self):
        inp = simpledialog.askstring(
            "Peek Address",
            "Enter address (hex, e.g. 200) and optional count (default 16):",
            parent=self.root,
        )
        if not inp:
            return
        try:
            parts = inp.strip().split()
            addr = int(parts[0], 16)
            count = int(parts[1], 16) if len(parts) > 1 else 16
            count = min(count, 256)
            end = min(addr + count, Chip8.MEM_SIZE)
            lines = []
            for off in range(0, end - addr, 16):
                row_addr = addr + off
                row_end = min(row_addr + 16, end)
                hexbytes = " ".join(f"{self.chip8.memory[a]:02X}" for a in range(row_addr, row_end))
                lines.append(f"0x{row_addr:04X}: {hexbytes}")
            messagebox.showinfo("Memory View", "\n".join(lines))
        except (ValueError, IndexError):
            messagebox.showerror("Peek Error", "Invalid address.")

    def _view_cheats(self):
        if not self.cheats_active:
            messagebox.showinfo("Active Cheats", "No cheats active.")
            return
        lines = [f"  {c[2]}" for c in self.cheats_active]
        messagebox.showinfo("Active Cheats", "\n".join(lines))

    # ==================================================================
    # MENU ACTIONS — Emulation
    # ==================================================================
    def _do_hard_reset(self):
        self.chip8.reset()
        if self.current_rom_path:
            self.chip8.load_rom(self.current_rom_path)
            self.chip8.halted = False
        self.render_display()
        self.frame_count = 0

    def _do_soft_reset(self):
        self.chip8.soft_reset()
        self.render_display()
        self.frame_count = 0

    def _frame_advance(self):
        """Step one frame (cycles_per_frame instructions + timer tick)."""
        was_paused = self.chip8.paused
        self.chip8.paused = False
        self.chip8.cycle(self.cycles_per_frame)
        self.chip8.paused = True
        if self.chip8.draw_flag:
            self.render_display()
            self.chip8.draw_flag = False
        self.pause_btn.config(text="RESUME")

    def _set_speed(self, cpf: int):
        self.cycles_per_frame = cpf
        self.speed_scale.set(cpf)

    def _turbo_toggle(self):
        if self._turbo_on:
            self.cycles_per_frame = self._saved_speed
            self.speed_scale.set(self._saved_speed)
            self._turbo_on = False
        else:
            self._saved_speed = self.cycles_per_frame
            self.cycles_per_frame = 60
            self.speed_scale.set(60)
            self._turbo_on = True

    # ==================================================================
    # MENU ACTIONS — Options
    # ==================================================================
    def _set_scale(self, scale: int):
        self.PIXEL_SCALE = scale
        self.SCREEN_W = Chip8.DISPLAY_W * scale
        self.SCREEN_H = Chip8.DISPLAY_H * scale
        self.canvas.config(width=self.SCREEN_W, height=self.SCREEN_H)
        self.render_display()

    def _pick_fg_color(self):
        color = colorchooser.askcolor(self.COL_PX_ON, title="Pixel ON Color")
        if color and color[1]:
            self.COL_PX_ON = color[1]
            self.chip8.draw_flag = True

    def _pick_bg_color(self):
        color = colorchooser.askcolor(self.COL_PX_OFF, title="Pixel OFF Color")
        if color and color[1]:
            self.COL_PX_OFF = color[1]
            self.chip8.draw_flag = True

    def _set_colors(self, fg: str, bg: str):
        self.COL_PX_ON = fg
        self.COL_PX_OFF = bg
        self.chip8.draw_flag = True

    def _show_input_config(self):
        lines = ["Keyboard → CHIP-8 Key Mapping:", ""]
        keyboard_layout = [
            ("1→1", "2→2", "3→3", "4→C"),
            ("Q→4", "W→5", "E→6", "R→D"),
            ("A→7", "S→8", "D→9", "F→E"),
            ("Z→A", "X→0", "C→B", "V→F"),
        ]
        for row in keyboard_layout:
            lines.append("  ".join(f"{m:>5}" for m in row))
        lines.extend(["", "Special Keys:", "  Esc    — Pause/Resume",
                       "  .      — Frame Advance", "  Tab    — Turbo Toggle",
                       "  Ctrl+O — Open ROM", "  Ctrl+R — Hard Reset",
                       "  F5     — Save State", "  F7     — Load State"])
        messagebox.showinfo("Input Configuration", "\n".join(lines))

    # ==================================================================
    # MENU ACTIONS — Window toggles
    # ==================================================================
    def _toggle_registers(self):
        if self.show_regs.get():
            self.reg_frame.place(x=10, y=20, width=130, height=440)
        else:
            self.reg_frame.place_forget()

    def _toggle_keypad(self):
        if self.show_keypad.get():
            pad_y = 20 + self.SCREEN_H + 30
            self.pad_frame.place(x=190, y=pad_y, width=280, height=140)
        else:
            self.pad_frame.place_forget()

    def _toggle_statusbar(self):
        if self.show_statusbar.get():
            self.status_frame.place(x=10, y=self.WIN_H - 22,
                                     width=self.WIN_W - 20, height=20)
        else:
            self.status_frame.place_forget()

    # ==================================================================
    # MENU ACTIONS — Help
    # ==================================================================
    def _show_keymap(self):
        self._show_input_config()

    def _show_opcode_ref(self):
        ref = (
            "CHIP-8 Opcode Quick Reference\n"
            "═══════════════════════════════\n"
            "00E0  CLS          Clear display\n"
            "00EE  RET          Return from sub\n"
            "1NNN  JP addr      Jump to NNN\n"
            "2NNN  CALL addr    Call sub at NNN\n"
            "3XNN  SE Vx,NN     Skip if Vx==NN\n"
            "4XNN  SNE Vx,NN    Skip if Vx!=NN\n"
            "5XY0  SE Vx,Vy     Skip if Vx==Vy\n"
            "6XNN  LD Vx,NN     Vx = NN\n"
            "7XNN  ADD Vx,NN    Vx += NN\n"
            "8XY0  LD Vx,Vy     Vx = Vy\n"
            "8XY1  OR Vx,Vy     Vx |= Vy\n"
            "8XY2  AND Vx,Vy    Vx &= Vy\n"
            "8XY3  XOR Vx,Vy    Vx ^= Vy\n"
            "8XY4  ADD Vx,Vy    Vx += Vy (VF=carry)\n"
            "8XY5  SUB Vx,Vy    Vx -= Vy (VF=!borrow)\n"
            "8XY6  SHR Vx       Vx >>= 1 (VF=lsb)\n"
            "8XY7  SUBN Vx,Vy   Vx = Vy-Vx\n"
            "8XYE  SHL Vx       Vx <<= 1 (VF=msb)\n"
            "9XY0  SNE Vx,Vy    Skip if Vx!=Vy\n"
            "ANNN  LD I,addr    I = NNN\n"
            "BNNN  JP V0,addr   PC = V0+NNN\n"
            "CXNN  RND Vx,NN    Vx = rand()&NN\n"
            "DXYN  DRW Vx,Vy,N  Draw sprite\n"
            "EX9E  SKP Vx       Skip if key[Vx]\n"
            "EXA1  SKNP Vx      Skip if !key[Vx]\n"
            "FX07  LD Vx,DT     Vx = delay_timer\n"
            "FX0A  LD Vx,K      Wait for key\n"
            "FX15  LD DT,Vx     delay_timer = Vx\n"
            "FX18  LD ST,Vx     sound_timer = Vx\n"
            "FX1E  ADD I,Vx     I += Vx\n"
            "FX29  LD F,Vx      I = font[Vx]\n"
            "FX33  LD B,Vx      BCD of Vx → [I]\n"
            "FX55  LD [I],Vx    Store V0..Vx\n"
            "FX65  LD Vx,[I]    Load V0..Vx\n"
        )
        # Use a toplevel for wider text display
        win = tk.Toplevel(self.root)
        win.title("CHIP-8 Opcode Reference")
        win.configure(bg="#0A0A0A")
        win.geometry("420x600")
        txt = tk.Text(win, bg="#0A0A0A", fg="#00BFFF", font=("Consolas", 9),
                      relief="flat", bd=10, wrap="none")
        txt.insert("1.0", ref)
        txt.config(state="disabled")
        txt.pack(fill="both", expand=True)

    def _show_about(self):
        messagebox.showinfo(
            "About — Qwen's CHIP-8 EMU",
            "Qwen's CHIP-8 EMU v2.3\n"
            "Originally by Qwen (Alibaba Cloud)\n"
            "CatsDK Patch — Claude / A.C Holdings\n\n"
            "A.C Holdings / Team Flames (c) 1999-2026\n\n"
            "Pure Python · Tkinter · No Dependencies\n"
            "License: MIT / Educational Use\n\n"
            "SNES9x-style menu system for the\n"
            "CHIP-8 generation that deserves it.",
        )

    # ------------------------------------------------------------------
    # UI layout — three-column, no overlap
    # ------------------------------------------------------------------
    def setup_ui(self):
        self.bg_canvas = tk.Canvas(
            self.root, bg=self.COL_BG, highlightthickness=0,
            width=self.WIN_W, height=self.WIN_H,
        )
        self.bg_canvas.place(x=0, y=0, width=self.WIN_W, height=self.WIN_H)
        self._draw_hud_background()

        # --- LEFT COLUMN: Register spine (x=10, w=130) ---
        self.reg_frame = tk.Frame(self.bg_canvas, bg=self.COL_BG)
        self.reg_frame.place(x=10, y=20, width=130, height=440)
        tk.Label(
            self.reg_frame, text="DATA SPINE", bg=self.COL_BG,
            fg=self.COL_ACCENT, font=("Consolas", 10, "bold"),
        ).pack(anchor="w", pady=(0, 6))

        self.reg_labels: dict[int, tk.Label] = {}
        for i in range(16):
            row = tk.Frame(self.reg_frame, bg=self.COL_BG)
            row.pack(fill="x", pady=1)
            tk.Label(
                row, text=f"V{i:01X}", bg=self.COL_BG, fg=self.COL_DIM,
                font=("Consolas", 9), width=3,
            ).pack(side="left")
            lbl = tk.Label(
                row, text="00", bg=self.COL_BG, fg=self.COL_TEXT,
                font=("Consolas", 9, "bold"), width=4, anchor="e",
            )
            lbl.pack(side="right")
            self.reg_labels[i] = lbl

        self.misc_frame = tk.Frame(self.reg_frame, bg=self.COL_BG)
        self.misc_frame.pack(fill="x", pady=(10, 0))
        self.misc_labels: dict[str, tk.Label] = {}
        for name in ("I", "PC", "SP", "DT", "ST"):
            row = tk.Frame(self.misc_frame, bg=self.COL_BG)
            row.pack(fill="x", pady=2)
            tk.Label(
                row, text=name, bg=self.COL_BG, fg=self.COL_DIM,
                font=("Consolas", 9), width=3,
            ).pack(side="left")
            lbl = tk.Label(
                row, text="0000", bg=self.COL_BG, fg=self.COL_TEXT,
                font=("Consolas", 9), width=6, anchor="e",
            )
            lbl.pack(side="right")
            self.misc_labels[name] = lbl

        # --- CENTER COLUMN: Display + keypad (x=150) ---
        center_x = 150
        self.view_frame = tk.Frame(self.bg_canvas, bg=self.COL_BG, bd=0)
        self.view_frame.place(x=center_x, y=20, width=self.SCREEN_W + 20, height=self.SCREEN_H + 20)
        self.canvas = tk.Canvas(
            self.view_frame, bg=self.COL_BG, highlightthickness=2,
            highlightbackground=self.COL_ACCENT,
            width=self.SCREEN_W, height=self.SCREEN_H,
        )
        self.canvas.pack(padx=5, pady=5)

        self._img_base = tk.PhotoImage(width=Chip8.DISPLAY_W, height=Chip8.DISPLAY_H)
        self.img = self._img_base.zoom(self.PIXEL_SCALE, self.PIXEL_SCALE)
        self._canvas_img_id = self.canvas.create_image(
            self.SCREEN_W // 2, self.SCREEN_H // 2, anchor="center", image=self.img,
        )
        self._draw_viewport_brackets()

        pad_y = 20 + self.SCREEN_H + 30
        self.pad_frame = tk.Frame(self.bg_canvas, bg=self.COL_BG)
        self.pad_frame.place(x=center_x + 40, y=pad_y, width=280, height=140)
        tk.Label(
            self.pad_frame, text="INPUT MATRIX", bg=self.COL_BG,
            fg=self.COL_ACCENT, font=("Consolas", 9, "bold"),
        ).pack(anchor="w", pady=(0, 4))
        pad_grid = tk.Frame(self.pad_frame, bg=self.COL_BG)
        pad_grid.pack()
        rows = [["1", "2", "3", "4"], ["Q", "W", "E", "R"],
                ["A", "S", "D", "F"], ["Z", "X", "C", "V"]]
        self.pad_keys: dict[str, tk.Label] = {}
        for r_idx, row in enumerate(rows):
            for c_idx, key in enumerate(row):
                k = key.lower()
                lbl = tk.Label(
                    pad_grid, text=key, bg="#111111", fg="#0055AA",
                    font=("Consolas", 9), width=4, height=1,
                )
                lbl.grid(row=r_idx, column=c_idx, padx=2, pady=2)
                self.pad_keys[k] = lbl

        # --- RIGHT COLUMN: Controls (x=510, w=180) ---
        ctrl_x = 510
        self.ctrl_frame = tk.Frame(self.bg_canvas, bg=self.COL_BG)
        self.ctrl_frame.place(x=ctrl_x, y=20, width=180, height=220)
        tk.Label(
            self.ctrl_frame, text="ACCESS MODULE", bg=self.COL_BG,
            fg=self.COL_ACCENT, font=("Consolas", 10, "bold"),
        ).pack(anchor="w", pady=(0, 10))

        self.load_btn = self._make_btn(self.ctrl_frame, "LOAD ROM", self.load_rom)
        self.load_btn.pack(fill="x", pady=4)
        self.reset_btn = self._make_btn(self.ctrl_frame, "RESET", self._do_hard_reset)
        self.reset_btn.pack(fill="x", pady=4)
        self.pause_btn = self._make_btn(self.ctrl_frame, "PAUSE", self.toggle_pause)
        self.pause_btn.pack(fill="x", pady=4)

        speed_frame = tk.Frame(self.ctrl_frame, bg=self.COL_BG)
        speed_frame.pack(fill="x", pady=(15, 0))
        tk.Label(
            speed_frame, text="CPU CYCLES/FRAME", bg=self.COL_BG,
            fg=self.COL_DIM, font=("Consolas", 8),
        ).pack(anchor="e")
        self.speed_scale = tk.Scale(
            speed_frame, from_=1, to=60, orient="horizontal",
            bg=self.COL_BG, fg=self.COL_ACCENT, troughcolor="#222222",
            highlightthickness=0, activebackground=self.COL_ACCENT,
            command=self._on_speed_change,
        )
        self.speed_scale.set(15)
        self.speed_scale.pack(fill="x")

        info_frame = tk.Frame(self.bg_canvas, bg=self.COL_BG)
        info_frame.place(x=ctrl_x, y=250, width=180, height=200)
        tk.Label(
            info_frame, text="ABOUT", bg=self.COL_BG,
            fg=self.COL_ACCENT, font=("Consolas", 10, "bold"),
        ).pack(anchor="w", pady=(0, 6))
        about_lines = [
            "Qwen CHIP-8 v2.3",
            "CatsDK Patch",
            "A.C Holdings 2026",
            "Team Flames",
            "",
            "Python 3.14+",
            "Pure Tkinter",
        ]
        for line in about_lines:
            tk.Label(
                info_frame, text=line, bg=self.COL_BG, fg=self.COL_DIM,
                font=("Consolas", 8), anchor="w",
            ).pack(anchor="w")

        # --- BOTTOM: Status bar ---
        self.status_frame = tk.Frame(self.bg_canvas, bg=self.COL_BG)
        self.status_frame.place(x=10, y=self.WIN_H - 22, width=self.WIN_W - 20, height=20)
        self.rom_var = tk.StringVar(value="NO ROM LOADED")
        tk.Label(
            self.status_frame, textvariable=self.rom_var, bg=self.COL_BG,
            fg="#E0E0E0", font=("Consolas", 8),
        ).pack(side="left")
        self.status_var = tk.StringVar(value="READY | PC: 0x0200")
        tk.Label(
            self.status_frame, textvariable=self.status_var, bg=self.COL_BG,
            fg=self.COL_STATUS, font=("Consolas", 8),
        ).pack(side="right")

        # Watermark
        tk.Label(
            self.root,
            text="Qwen's CHIP-8 EMU v2.3 • CatsDK Patch • A.C Holdings / Team Flames (c) 2026 • Python 3.14+",
            bg=self.COL_BG, fg="#1A1A1A", font=("Segoe UI", 7),
        ).place(x=10, y=self.WIN_H - 14, width=self.WIN_W - 20, height=12)

    # ------------------------------------------------------------------
    # HUD decorations
    # ------------------------------------------------------------------
    def _draw_hud_background(self):
        w, h = self.WIN_W, self.WIN_H
        self.bg_canvas.create_line(0, 100, w, 300, fill="#0A0A0A", width=1)
        self.bg_canvas.create_line(w, 150, 0, 350, fill="#0A0A0A", width=1)
        for y_pos in range(50, h, 50):
            self.bg_canvas.create_oval(8, y_pos - 2, 14, y_pos + 2, fill="#001A33", outline="#003366")
            self.bg_canvas.create_oval(w - 14, y_pos - 2, w - 8, y_pos + 2, fill="#001A33", outline="#003366")

    def _draw_viewport_brackets(self):
        w, h = self.SCREEN_W, self.SCREEN_H
        blen = 30
        for coords in [
            (8, blen, 8, 8, blen, 8),
            (w - 8, blen, w - 8, 8, w - blen, 8),
            (8, h - blen, 8, h - 8, blen, h - 8),
            (w - 8, h - blen, w - 8, h - 8, w - blen, h - 8),
        ]:
            self.canvas.create_line(*coords, fill=self.COL_ACCENT, width=2)

    # ------------------------------------------------------------------
    # Bindings
    # ------------------------------------------------------------------
    def setup_bindings(self):
        self.root.bind("<KeyPress>", lambda e: self._on_key(e, True))
        self.root.bind("<KeyRelease>", lambda e: self._on_key(e, False))
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    def _on_key(self, event: tk.Event, pressed: bool):
        k = event.keysym.lower()
        if k in self.KEY_MAP:
            self.chip8.set_key(self.KEY_MAP[k], pressed)
            if k in self.pad_keys:
                bg = "#002244" if pressed else "#111111"
                fg = self.COL_TEXT if pressed else "#0055AA"
                self.pad_keys[k].config(bg=bg, fg=fg)

    # ------------------------------------------------------------------
    # Actions
    # ------------------------------------------------------------------
    def load_rom(self):
        path = filedialog.askopenfilename(
            filetypes=[("CHIP-8 ROMs", "*.ch8 *.rom *.bin"), ("All Files", "*.*")],
        )
        if path:
            self.chip8.reset()
            if self.chip8.load_rom(path):
                self.current_rom_path = path
                filename = path.replace("\\", "/").split("/")[-1]
                self.rom_var.set(f"LOADED: {filename}")
                self.chip8.halted = False
                self.frame_count = 0
                self._add_recent(path)
            else:
                messagebox.showerror("Load Error", f"Failed to load ROM:\n{path}")

    def _do_reset(self):
        self._do_hard_reset()

    def toggle_pause(self):
        self.chip8.paused = not self.chip8.paused
        self.pause_btn.config(text="RESUME" if self.chip8.paused else "PAUSE")

    def _on_speed_change(self, val: str):
        self.cycles_per_frame = int(val)

    # ------------------------------------------------------------------
    # Main update loop (60 Hz)
    # ------------------------------------------------------------------
    def update_loop(self):
        if not self.running:
            return

        now = time.time()
        dt = now - self.last_frame_time
        self.last_frame_time = now

        # Re-apply persistent cheats each frame
        for addr, val, _ in self.cheats_active:
            if 0 <= addr < Chip8.MEM_SIZE:
                self.chip8.memory[addr] = val

        self.chip8.cycle(self.cycles_per_frame)
        self.frame_count += 1

        if self.chip8.draw_flag:
            self.render_display()
            self.chip8.draw_flag = False

        for i in range(16):
            self.reg_labels[i].config(text=f"{self.chip8.V[i]:02X}")
        self.misc_labels["I"].config(text=f"{self.chip8.I:04X}")
        self.misc_labels["PC"].config(text=f"{self.chip8.pc:04X}")
        self.misc_labels["SP"].config(text=f"{self.chip8.sp + 1:02d}")
        self.misc_labels["DT"].config(text=f"{self.chip8.delay_timer:02d}")
        self.misc_labels["ST"].config(text=f"{self.chip8.sound_timer:02d}")

        if dt > 0:
            self.fps_history.append(1.0 / dt)
        avg_fps = int(sum(self.fps_history) / max(len(self.fps_history), 1))

        state = "HALTED" if self.chip8.halted else ("PAUSED" if self.chip8.paused else "RUN")
        status_parts = [f"{state}", f"PC:0x{self.chip8.pc:04X}", f"I:0x{self.chip8.I:04X}",
                        f"DT:{self.chip8.delay_timer:02d}", f"ST:{self.chip8.sound_timer:02d}"]
        if self.show_fps_counter.get():
            status_parts.append(f"FPS:{avg_fps}")
        if self.show_framectr.get():
            status_parts.append(f"F:{self.frame_count}")
        if self.show_input_display.get():
            pressed = [f"{k:X}" for k in range(16) if self.chip8.keys[k]]
            if pressed:
                status_parts.append(f"KEY:{''.join(pressed)}")
        if self.cheats_active:
            status_parts.append(f"CHT:{len(self.cheats_active)}")
        if self._turbo_on:
            status_parts.append("TURBO")

        self.status_var.set(" | ".join(status_parts))
        self.root.after(1000 // self.fps, self.update_loop)

    # ------------------------------------------------------------------
    # Display renderer
    # ------------------------------------------------------------------
    def render_display(self):
        rows = []
        for y in range(Chip8.DISPLAY_H):
            row = "{" + " ".join(
                self.COL_PX_ON if self.chip8.display[y][x] else self.COL_PX_OFF
                for x in range(Chip8.DISPLAY_W)
            ) + "}"
            rows.append(row)
        self._img_base.put(" ".join(rows))
        self.img = self._img_base.zoom(self.PIXEL_SCALE, self.PIXEL_SCALE)
        self.canvas.itemconfig(self._canvas_img_id, image=self.img)

    # ------------------------------------------------------------------
    # Shutdown
    # ------------------------------------------------------------------
    def _on_close(self):
        self.running = False
        self.root.destroy()
        sys.exit(0)


# ==============================================================================
# ENTRY POINT
# ==============================================================================
if __name__ == "__main__":
    root = tk.Tk()
    app = Chip8GUI(root)
    root.mainloop()
