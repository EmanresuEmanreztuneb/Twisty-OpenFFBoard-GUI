"""FFBoard Twisty GUI.

Reduced Tkinter replacement for the OpenFFBoard-configurator, limited to a
focused subset of controls/readouts for a VESC-driven wheel. The serial wire
protocol (ffb_protocol.py) and the animation technique (sprite_gauge.py) are
taken 1:1 from the reference projects; everything else here is new.

The Inputs/Effects/Force sections below are positioned with explicit
place(x=, y=) pixel coordinates instead of grid()/pack() - every one of
those coordinates is a named constant imported from Placement.py (which
holds layout data only, no logic), so the numbers can be tuned in one place.

Fixed at firmware compile time (informational only, not controlled from here):
    Driver = VESC, FFBoard CAN ID 64, VESC CAN ID 255, CAN baudrate 500000
"""
import math
import os
import sys
import time
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

from PIL import Image, ImageTk

from ffb_protocol import FFBProtocol
from hid_link import HidLink
from info_window import open_info_window
from sprite_gauge import SpriteGauge
from strip_chart import StripChart

import Placement as P


def resource_path(relative_path):
    """Absolute path to a bundled data file, working both when run as a
    plain script (relative to this file) and when frozen into a single
    .exe via PyInstaller (relative to sys._MEIPASS, the temp folder
    PyInstaller extracts --add-data into at runtime) - same pattern the
    old Twisty_Arduino_GUI used for its own PyInstaller build."""
    base_path = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base_path, relative_path)


IMAGES_DIR = resource_path(os.path.join("data", "images"))


def parse_infostring(reply):
    """Parse OpenFFBoard 'key:value,key:value' info replies (typechar '!')."""
    result = {}
    for part in reply.split(","):
        if ":" not in part:
            continue
        key, _, value = part.partition(":")
        try:
            result[key] = float(value)
        except ValueError:
            pass
    return result


# apin pin indices wired as NTC temperature channels (0-indexed; the
# Configurator's "Pin N" labels are these +1 - e.g. index 5 = "Pin 6", the
# original PT100 channel from Pt100Monitor.h). All three are assumed to use
# the same divider (see ntc_raw_to_celsius) until proven otherwise.
TEMP_PIN_INDICES = (3, 4, 5)

# Prefix of the firmware's wire-break failsafe error line, as produced by
# Error::toString() ("{code}:{type}:{info}") for ErrorCode::temperatureImplausible
# = 16 (see ErrorHandler.h). Used to detect that fault from the plain-text
# sys.errors reply already polled for the log window (_on_fw_errors) instead
# of adding a second, dedicated poll/command just for this one flag.
FW_ERROR_PREFIX_TEMP_IMPLAUSIBLE = "16:"

# Temperature-readout background color by overtemperature stage (L1/L2/L3
# in ReadoutBar - see App._apply_bg_stage; an earlier version colored the
# entire window/every ttk style instead, removed per user request). Driven
# directly by the firmware's own already-debounced pt100stage value (see
# App._on_fw_pt100stage) rather than a second, independently-computed
# hysteresis in the GUI - an earlier version recomputed its own 40C/45C/38C
# thresholds from live temperature readings polled every 30ms, which had no
# debounce of its own and could flip a stage ahead of the real (felt) force
# change on a single noisy sample. Using the real stage value directly means
# there is only ever one source of truth for what "stage" means.
TEMP_BG_COLORS = {0: None, 1: "#EC7D3C", 2: "#F54927"}  # None = restore default

# Low-voltage warning for the VCC readout (ReadoutBar) - a plain client-
# side threshold on the already-polled vesc.0.voltage value (no firmware
# "stage"/debounce like the temperature one above, per user request: VCC
# doesn't need it, it's not a fast-changing/noisy reading like temperature
# was). Reuses the same red as the critical temperature stage per user
# request (chance of both firing at once is negligible).
VOLTAGE_LOW_THRESHOLD_V = 9.0
VOLTAGE_LOW_COLOR = TEMP_BG_COLORS[2]

# Twisty temp-sensor divider: 3.3V -> NTC(~10k @ 25C) -> ADC pin -> 4.7k -> GND.
# NOTE: this is the opposite of what was reported for the physical wiring
# (4.7k on top, NTC on bottom) - that orientation gave ~57C at room
# temperature (implausible), while this one gives a plausible reading, so
# it's used until someone can confirm the wiring against the actual board.
# R25/Beta calibration (2026-09-12): re-fit against apin.0.rawval (see
# on_connected()) after the earlier fit turned out to be against an
# autoranged, moving-target value (apin.0.values). Two-point fit: 34C real
# at a live reading, and 42C real at a live reading the single-point
# formula was showing as 38C. Beta keeps coming out unusually low and
# unstable across different point pairs (2378 with one pair, 2000 with
# this one) - the sensor may not follow a clean Beta curve (self-heating,
# reference-thermometer error, or a non-ideal part), so treat this as
# accurate near 34-42C and increasingly uncertain outside that range.
# Re-fit the same way (see scratchpad calibration script) if a fresh
# reference measurement disagrees.
ADC_BITS = 12  # F407 hadc1 resolution, see AdcHandler::getAdcResolutionBits
NTC_VREF = 3.3
NTC_R_FIXED = 4700.0
NTC_R25 = 8103.36
NTC_BETA = 2000.39
NTC_T25_KELVIN = 298.15


def ntc_raw_to_celsius(axis_val):
    """Convert an apin.0.values entry (see LocalAnalog::getAxes) to degrees C.

    axis_val is (raw12 << bitshift) - 0x7fff, not raw ADC counts or mV -
    undo that scaling first, then invert the voltage-divider + Beta equation.
    Returns None if the reading is at a divider rail (open/shorted sensor).
    """
    bitshift = 16 - ADC_BITS
    fullscale = (1 << ADC_BITS) - 1
    raw12 = (axis_val + 0x7FFF) >> bitshift
    raw12 = max(0, min(fullscale, raw12))
    if raw12 <= 0 or raw12 >= fullscale:
        return None
    vadc = NTC_VREF * raw12 / fullscale
    r_ntc = NTC_R_FIXED * (NTC_VREF - vadc) / vadc
    if r_ntc <= 0:
        return None
    kelvin = 1.0 / (1.0 / NTC_T25_KELVIN + (1.0 / NTC_BETA) * math.log(r_ntc / NTC_R25))
    return kelvin - 273.15


def _load_scaled_image(path, scale):
    """Open a PNG and, if scale != 1.0, resize it (LANCZOS) before wrapping
    it as a PhotoImage - used to shrink the button cluster/solo images
    without touching the source files."""
    img = Image.open(path)
    if scale != 1.0:
        size = (max(1, round(img.width * scale)), max(1, round(img.height * scale)))
        img = img.resize(size, Image.LANCZOS)
    return ImageTk.PhotoImage(img)


class ButtonClusterGauge(tk.Label):
    """Shows one pre-rendered diamond image for a 4-button front cluster,
    picked by which of the 4 named buttons are currently pressed. Images are
    named "<active buttons joined by _>.png" (e.g. "E1_E3.png"), with
    "All_Off.png" for the rest-state - see data/images/Buttons_Links|Rechts."""

    def __init__(self, parent, image_dir, names, scale=1.0, **kwargs):
        super().__init__(parent, **kwargs)
        self.names = names
        self._frames = {}
        for filename in os.listdir(image_dir):
            if filename.lower().endswith(".png") and not filename.startswith("Solo_"):
                key = os.path.splitext(filename)[0]
                self._frames[key] = _load_scaled_image(os.path.join(image_dir, filename), scale)
        self.set_bits((False, False, False, False))

    def set_bits(self, bits):
        active = [name for name, pressed in zip(self.names, bits) if pressed]
        key = "_".join(active) if active else "All_Off"
        img = self._frames.get(key, self._frames.get("All_Off"))
        if img is not None:
            self.configure(image=img)


class SoloLamp(tk.Label):
    """Standalone on/off lamp for a button that is also wired to a shifter
    paddle (electrically the same signal - see Solo_<name>_On/Off.png)."""

    def __init__(self, parent, image_dir, name, scale=1.0, **kwargs):
        super().__init__(parent, **kwargs)
        self.on_img = _load_scaled_image(os.path.join(image_dir, f"Solo_{name}_On.png"), scale)
        self.off_img = _load_scaled_image(os.path.join(image_dir, f"Solo_{name}_Off.png"), scale)
        self.configure(image=self.off_img)

    def set_state(self, active):
        self.configure(image=self.on_img if active else self.off_img)


class RangeSlider(tk.Canvas):
    """Two-thumb vertical range slider spanning -32767..32767, with a
    live-value marker. Top thumb = min, bottom thumb = max (same top-to-bottom
    order as calling code's Min-above/Max-below field layout).

    Mirrors the OpenFFBoard-configurator's QtRangeSlider concept: a track
    with two draggable thumbs (the calibration endpoints) and a marker for
    the axis's current raw reading, so dragging a thumb toward the marker is
    a direct, visual way to calibrate - the space between the thumbs is
    highlighted, everything outside reads as "cut off" even though the
    underlying firmware behaviour is a rescale, not a clip (see
    AnalogAxisProcessing.cpp).
    """

    LIMIT = 32767

    def __init__(self, parent, on_min_change, on_max_change, length=220):
        super().__init__(parent, width=P.RANGESLIDER_THICKNESS, height=length, highlightthickness=0)
        self.on_min_change = on_min_change
        self.on_max_change = on_max_change
        self.min_val = -self.LIMIT
        self.max_val = self.LIMIT
        self.live_val = None
        self.live_item = None
        self._drag = None  # "min" | "max" | None

        self.bind("<Configure>", lambda e: self._redraw_static())
        self.bind("<Button-1>", self._on_press)
        self.bind("<B1-Motion>", self._on_motion)
        self.bind("<ButtonRelease-1>", self._on_release)

    def _val_to_y(self, val):
        h = max(self.winfo_height(), 2 * P.RANGESLIDER_PAD + 1) - 2 * P.RANGESLIDER_PAD
        return P.RANGESLIDER_PAD + (val + self.LIMIT) / (2 * self.LIMIT) * h

    def _y_to_val(self, y):
        h = max(self.winfo_height(), 2 * P.RANGESLIDER_PAD + 1) - 2 * P.RANGESLIDER_PAD
        frac = max(0.0, min(1.0, (y - P.RANGESLIDER_PAD) / h))
        return round(frac * 2 * self.LIMIT - self.LIMIT)

    def set_min(self, val, redraw=True):
        self.min_val = max(-self.LIMIT, min(int(val), self.max_val - 1))
        if redraw:
            self._redraw_static()

    def set_max(self, val, redraw=True):
        self.max_val = min(self.LIMIT, max(int(val), self.min_val + 1))
        if redraw:
            self._redraw_static()

    def set_live(self, val):
        self.live_val = val
        self._redraw_live()

    def _redraw_static(self):
        self.delete("all")
        self.live_item = None
        x = self.winfo_width() // 2
        h = self.winfo_height()
        self.create_line(x, P.RANGESLIDER_PAD, x, h - P.RANGESLIDER_PAD, fill="#c7c7c7", width=P.RANGESLIDER_TRACK_W)
        y_min = self._val_to_y(self.min_val)
        y_max = self._val_to_y(self.max_val)
        self.create_line(x, y_min, x, y_max, fill="#000000", width=P.RANGESLIDER_TRACK_W)
        self._redraw_live()
        for y in (y_min, y_max):
            self.create_rectangle(
                x - P.RANGESLIDER_THUMB_HALF_ACROSS, y - P.RANGESLIDER_THUMB_HALF_ALONG,
                x + P.RANGESLIDER_THUMB_HALF_ACROSS, y + P.RANGESLIDER_THUMB_HALF_ALONG,
                fill="white", outline="#555555",
            )

    def _redraw_live(self):
        """Move/create only the green live-value line, without touching the
        track or thumbs - called on every set_live() (the 30ms poll hot
        path, see InputsCanvas._rawvalues_cb), so it must stay cheap."""
        if self.live_val is None:
            if self.live_item is not None:
                self.delete(self.live_item)
                self.live_item = None
            return
        y_live = self._val_to_y(max(-self.LIMIT, min(self.LIMIT, self.live_val)))
        if self.live_item is None:
            self.live_item = self.create_line(1, y_live, self.winfo_width() - 1, y_live, fill="#10c020", width=2)
        else:
            self.coords(self.live_item, 1, y_live, self.winfo_width() - 1, y_live)

    def _on_press(self, event):
        y_min = self._val_to_y(self.min_val)
        y_max = self._val_to_y(self.max_val)
        self._drag = "min" if abs(event.y - y_min) <= abs(event.y - y_max) else "max"
        self._on_motion(event)

    def _on_motion(self, event):
        if self._drag is None:
            return
        val = self._y_to_val(event.y)
        if self._drag == "min":
            self.set_min(val)
        else:
            self.set_max(val)

    def _on_release(self, _event):
        if self._drag == "min":
            self.on_min_change(self.min_val)
        elif self._drag == "max":
            self.on_max_change(self.max_val)
        self._drag = None


class HSlider(tk.Canvas):
    """Single-thumb horizontal value slider spanning [vmin, vmax], drawn the
    same way as RangeSlider above (a plain track line, a highlighted blue
    fill from the left edge up to the thumb, and a white/grey square thumb)
    but with one thumb instead of two, for one value instead of a min/max
    pair. Like RangeSlider, dragging only updates the on-screen position;
    on_change fires once on release."""

    def __init__(self, parent, vmin, vmax, on_change, resolution=1, **kwargs):
        kwargs.setdefault("highlightthickness", 0)
        super().__init__(parent, **kwargs)
        self.vmin = vmin
        self.vmax = vmax
        self.resolution = resolution
        self.on_change = on_change
        self.value = vmin
        self._dragging = False

        self.bind("<Configure>", lambda e: self._redraw())
        self.bind("<Button-1>", self._on_press)
        self.bind("<B1-Motion>", self._on_motion)
        self.bind("<ButtonRelease-1>", self._on_release)

    def _val_to_x(self, val):
        w = max(self.winfo_width(), 2 * P.HSLIDER_PAD + 1) - 2 * P.HSLIDER_PAD
        return P.HSLIDER_PAD + (val - self.vmin) / (self.vmax - self.vmin) * w

    def _x_to_val(self, x):
        w = max(self.winfo_width(), 2 * P.HSLIDER_PAD + 1) - 2 * P.HSLIDER_PAD
        frac = max(0.0, min(1.0, (x - P.HSLIDER_PAD) / w))
        val = frac * (self.vmax - self.vmin) + self.vmin
        if self.resolution:
            val = round(val / self.resolution) * self.resolution
        return max(self.vmin, min(self.vmax, val))

    def set_value(self, val, redraw=True):
        self.value = max(self.vmin, min(self.vmax, val))
        if redraw:
            self._redraw()

    def _redraw(self):
        self.delete("all")
        y = self.winfo_height() // 2
        w = self.winfo_width()
        self.create_line(P.HSLIDER_PAD, y, w - P.HSLIDER_PAD, y, fill="#c7c7c7", width=P.HSLIDER_TRACK_W)
        x_val = self._val_to_x(self.value)
        self.create_line(P.HSLIDER_PAD, y, x_val, y, fill="#000000", width=P.HSLIDER_TRACK_W)
        self.create_rectangle(
            x_val - P.HSLIDER_THUMB_HALF_ALONG, y - P.HSLIDER_THUMB_HALF_ACROSS,
            x_val + P.HSLIDER_THUMB_HALF_ALONG, y + P.HSLIDER_THUMB_HALF_ACROSS,
            fill="white", outline="#555555",
        )

    def _on_press(self, event):
        self._dragging = True
        self._on_motion(event)

    def _on_motion(self, event):
        if not self._dragging:
            return
        self.set_value(self._x_to_val(event.x))

    def _on_release(self, _event):
        if self._dragging:
            self._dragging = False
            self.on_change(self.value)


class LabeledSlider(ttk.Frame):
    """A labeled slider with an editable value entry.

    Uses the same Canvas-drawn track/thumb widget as the InputsCanvas
    Min/Max sliders (see HSlider) instead of a native tk.Scale.

    percent_max, when given, switches the entry field to percent instead of
    the raw value, with the "%" sign folded directly into the entry text
    (see _raw_to_display/_display_to_raw) rather than a separate label. The
    percent shown is:

        percent = (raw + percent_offset) / percent_max * percent_scale * 100

    For a plain "raw's own range" percent (Power, Endstop Gain, Desktop
    Spring, Overall Gain), percent_offset=0 and percent_scale=1, so
    this reduces to raw/percent_max*100 - the slider's own 0-100% range.

    For the 4 fx gain sliders (Spring/Damper/Friction/Inertia) it instead
    mirrors the firmware's real gainfactor formula (EffectsCalculator.cpp:
    "Gain of 255 = 1x. Prescale with scale factor", gainfactor=(raw+1)/256,
    force = coefficient * gainfactor * scaler.<effect>): percent_offset=1,
    percent_max=256, percent_scale=the effect's fixed scaler constant
    (16/4/1/2). 100% there means "exactly what the game's own effect
    coefficient asked for" - not "slider at max" - so a scaler above 1x
    (Spring, Damper, Inertia) correctly shows *above* 100% once the slider
    amplifies past that point (Spring maxes out at 1600%, matching its
    scaler of 16).

    Typing a percent and pressing Enter converts it back to the raw value
    that produces it and sends that. When percent_max is None (e.g. Range,
    unit="°" - a physical unit that's already directly readable), the entry
    shows/accepts the raw value as before, just with that unit appended.

    Fixed-size composite widget: label/entry/unit/slider are place()d at
    fixed pixel offsets inside this frame (instead of grid()), in that
    left-to-right order (label -> entry -> slider), so the frame itself can
    be place()d by the caller like any other leaf widget.

    width, when given, overrides the shared P.SLIDER_WIDTH for just this
    instance - label/entry/unit keep their usual fixed widths, so the extra
    (or reduced) space goes entirely to the draggable slider track.

    label_width, when given, overrides the shared P.SLIDER_LABEL_W for just
    this instance - the label text itself is anchor="w" (left-aligned) so
    it doesn't move, but a narrower box brings the entry (which starts
    right after it) closer to the text.

    note, when given, appends a short explanatory caption (grey text) after
    the slider - e.g. "Multiplies Game Effect" vs. "Adds to Game Effect",
    to show at a glance whether a slider only scales something the game
    itself sends or is applied by the firmware independently of the game.
    Purely cosmetic: adds its own column (width note_width, default
    P.SLIDER_NOTE_W) onto the end of the frame, without changing the
    label/entry/slider layout computed from `width` above - so callers
    that don't pass a note are laid out exactly as before.
    """

    def __init__(
        self, parent, label, vmin, vmax, on_change, resolution=1,
        percent_max=None, percent_offset=0, percent_scale=1, unit=None, width=None, label_width=None,
        note=None, note_width=None,
    ):
        width = P.SLIDER_WIDTH if width is None else width
        label_width = P.SLIDER_LABEL_W if label_width is None else label_width
        note_width = P.SLIDER_NOTE_W if note_width is None else note_width
        total_width = width + (P.SLIDER_INNER_GAP + note_width if note else 0)
        super().__init__(parent, width=total_width, height=P.SLIDER_HEIGHT)
        self.vmin = vmin
        self.vmax = vmax
        self.on_change = on_change
        self.percent_max = percent_max
        self.percent_offset = percent_offset
        self.percent_scale = percent_scale
        if unit is None and percent_max:
            unit = "%"
        self.unit = unit

        ttk.Label(self, text=label, anchor="w").place(x=0, y=2, width=label_width, height=20)

        # Order is label -> entry -> slider -> note, per user request -
        # entry sits right after the label instead of after the slider.
        # Any unit (e.g. "%", "°") is folded directly into the entry text
        # (_raw_to_display/_display_to_raw below) - no separate unit label,
        # so the slider always starts right after the entry and gets the
        # rest of `width` as its own track.
        entry_x = label_width + P.SLIDER_INNER_GAP
        self.value_var = tk.StringVar(value=self._raw_to_display(vmin))
        self.entry = ttk.Entry(self, textvariable=self.value_var, width=7, justify="center")
        self.entry.place(x=entry_x, y=2, width=P.SLIDER_READOUT_W, height=20)
        self.entry.bind("<Return>", self._on_entry_apply)
        self.entry.bind("<FocusOut>", self._on_entry_apply)

        slider_x = entry_x + P.SLIDER_READOUT_W + P.SLIDER_INNER_GAP
        slider_w = width - label_width - P.SLIDER_READOUT_W - 2 * P.SLIDER_INNER_GAP
        self.slider = HSlider(self, vmin, vmax, self._on_slider_change, resolution=resolution)
        self.slider.place(
            x=slider_x, y=0, width=slider_w, height=P.SLIDER_HEIGHT,
        )

        if note:
            ttk.Label(self, text=note, anchor="w", foreground="#888").place(
                x=width + P.SLIDER_INNER_GAP, y=2, width=note_width, height=20,
            )

    def _raw_to_display(self, raw):
        """Raw firmware value -> text shown in the entry: a percent (rounded
        to the nearest whole percent) if percent_max is set, else the raw
        value itself - with the unit suffix (if any, e.g. "%" or "°")
        folded directly into the text."""
        if self.percent_max:
            pct = (raw + self.percent_offset) / self.percent_max * self.percent_scale * 100
            text = str(round(pct))
        else:
            text = str(int(round(raw)))
        if self.unit:
            text += self.unit
        return text

    def _display_to_raw(self, text):
        """Inverse of _raw_to_display - parses the entry text back to a raw
        value, rounding to the nearest raw step (not floor) so a round-trip
        through percent loses as little of the requested strength as
        possible, and clamped to [vmin, vmax]. A trailing unit suffix is
        optional here (stripped before parsing) - typing just the number
        still works even though the field displays it with the unit
        attached."""
        text = text.strip()
        if self.unit and text.endswith(self.unit):
            text = text[: -len(self.unit)]
        num = float(text.strip())
        if self.percent_max:
            raw = round(num / 100 / self.percent_scale * self.percent_max - self.percent_offset)
        else:
            raw = num
        return max(self.vmin, min(self.vmax, raw))

    def _update_value(self, val):
        self.value_var.set(self._raw_to_display(val))

    def _on_slider_change(self, val):
        self._update_value(val)
        self.on_change(val)

    def _on_entry_apply(self, _event=None):
        try:
            val = self._display_to_raw(self.value_var.get())
        except ValueError:
            self._update_value(self.slider.value)
            return
        self.slider.set_value(val)
        self._update_value(val)
        self.on_change(val)

    def set_from_firmware(self, val):
        val = float(val)
        self.slider.set_value(val)
        self._update_value(val)

    def get_value(self):
        return self.slider.value


class LabeledEntry(ttk.Frame):
    """Label + editable value entry, no slider track - same entry behavior
    as LabeledSlider (Enter/FocusOut applies the typed value, clamped to
    [vmin, vmax], unit suffix folded into the displayed text), for values
    that only need typing, not dragging. Same get_value()/set_from_firmware()
    interface as LabeledSlider so it drops into SAVE_LOAD_FIELDS unchanged.
    """

    def __init__(self, parent, label, vmin, vmax, on_change, unit=None, label_width=None, entry_width=None):
        label_width = P.SLIDER_LABEL_W if label_width is None else label_width
        entry_width = P.SLIDER_READOUT_W if entry_width is None else entry_width
        total_width = label_width + P.SLIDER_INNER_GAP + entry_width
        super().__init__(parent, width=total_width, height=P.SLIDER_HEIGHT)
        self.vmin = vmin
        self.vmax = vmax
        self.on_change = on_change
        self.unit = unit
        self.value = vmin

        ttk.Label(self, text=label, anchor="w").place(x=0, y=2, width=label_width, height=20)

        entry_x = label_width + P.SLIDER_INNER_GAP
        self.value_var = tk.StringVar(value=self._raw_to_display(vmin))
        self.entry = ttk.Entry(self, textvariable=self.value_var, width=7, justify="center")
        self.entry.place(x=entry_x, y=2, width=entry_width, height=20)
        self.entry.bind("<Return>", self._on_entry_apply)
        self.entry.bind("<FocusOut>", self._on_entry_apply)

    def _raw_to_display(self, raw):
        text = str(int(round(raw)))
        if self.unit:
            text += self.unit
        return text

    def _display_to_raw(self, text):
        text = text.strip()
        if self.unit and text.endswith(self.unit):
            text = text[: -len(self.unit)]
        num = float(text.strip())
        return max(self.vmin, min(self.vmax, num))

    def _on_entry_apply(self, _event=None):
        try:
            val = self._display_to_raw(self.value_var.get())
        except ValueError:
            self.value_var.set(self._raw_to_display(self.value))
            return
        self.value = val
        self.value_var.set(self._raw_to_display(val))
        self.on_change(val)

    def set_from_firmware(self, val):
        self.value = float(val)
        self.value_var.set(self._raw_to_display(self.value))

    def get_value(self):
        return self.value


class PlacedGroup:
    """Mixin for builder classes that used to be a bordered Canvas/Frame
    (InputsCanvas/EffectsCanvas, both removed per user request) acting only
    as a place() coordinate origin for their children. Now those children
    are placed directly onto a shared parent (App.main_frame), offset by
    (base_x, base_y) so every existing Placement.py coordinate keeps
    meaning exactly what it always did: relative to this group's own,
    now-virtual, top-left corner - the two groups therefore keep the same
    pixel arrangement relative to each other as before, just without the
    surrounding box."""

    def _init_group(self, parent, base_x, base_y):
        self.parent = parent
        self.base_x = base_x
        self.base_y = base_y

    def _place(self, widget, x, y, **kwargs):
        widget.place(x=self.base_x + x, y=self.base_y + y, **kwargs)
        return widget


class InputsCanvas(PlacedGroup):
    """Value analog 1/2 gauges with their Min/Max calibration sliders, and
    the 10-button digital inputs (4+4 diamond clusters + 2 solo wippen) -
    everything positioned with explicit place() x/y coordinates (see
    Placement.py, INPUTS_* constants), directly on App.main_frame - no
    longer a bordered "Inputs" box (removed per user request, see
    PlacedGroup above).

    Temperature channels are also fed by apin.0.rawval/apin.0.mask, same as
    the calibration sliders' live marker here, but are displayed in App's
    ReadoutBar instead - both classes register their own apin.rawval
    listener, fed by one shared poll() call here.
    """

    MINMAX_LIMIT = 32767

    def __init__(self, parent, link, hid_link, base_x=0, base_y=0):
        self._init_group(parent, base_x, base_y)
        self.link = link
        self.hid_link = hid_link
        self.minmax_vars = {}  # apin adr -> {"min": StringVar, "max": StringVar, ...}

        self._place(ttk.Label(parent, text="Brake"), P.INPUTS_GAUGE1_LABEL_X, P.INPUTS_GAUGE1_LABEL_Y, anchor="n")
        self.gauge1 = SpriteGauge(parent, os.path.join(IMAGES_DIR, "Y"), scale=P.INPUTS_GAUGE1_Y_AXIS_SCALE)
        self._place(self.gauge1, P.INPUTS_GAUGE1_IMAGE_X, P.INPUTS_GAUGE1_IMAGE_Y, anchor="n")
        self.label1 = ttk.Label(parent, text="0")
        self._place(self.label1, P.INPUTS_GAUGE1_NUMBER_X, P.INPUTS_GAUGE1_NUMBER_Y, anchor="n")

        self._build_minmax_entries(
            adr=1,
            min_label_pos=(P.INPUTS_CONTROLS1_MIN_LABEL_X, P.INPUTS_CONTROLS1_MIN_LABEL_Y),
            min_entry_pos=(P.INPUTS_CONTROLS1_MIN_ENTRY_X, P.INPUTS_CONTROLS1_MIN_ENTRY_Y),
            min_button_pos=(P.INPUTS_CONTROLS1_MIN_BUTTON_X, P.INPUTS_CONTROLS1_MIN_BUTTON_Y),
            slider_pos=(P.INPUTS_CONTROLS1_SLIDER_X, P.INPUTS_CONTROLS1_SLIDER_Y),
            invert_button_pos=(P.INPUTS_CONTROLS1_INVERT_X, P.INPUTS_CONTROLS1_INVERT_Y),
            max_label_pos=(P.INPUTS_CONTROLS1_MAX_LABEL_X, P.INPUTS_CONTROLS1_MAX_LABEL_Y),
            max_entry_pos=(P.INPUTS_CONTROLS1_MAX_ENTRY_X, P.INPUTS_CONTROLS1_MAX_ENTRY_Y),
            max_button_pos=(P.INPUTS_CONTROLS1_MAX_BUTTON_X, P.INPUTS_CONTROLS1_MAX_BUTTON_Y),
        )

        self.left_cluster = ButtonClusterGauge(
            parent, os.path.join(IMAGES_DIR, "Buttons_Links"), ["E1", "E2", "E3", "E4"],
            scale=P.INPUTS_BUTTONS_IMAGE_SCALE,
        )
        self._place(self.left_cluster, P.INPUTS_BUTTONS_LEFT_CLUSTER_X, P.INPUTS_BUTTONS_LEFT_CLUSTER_Y, anchor="n")
        self.left_solo = SoloLamp(
            parent, os.path.join(IMAGES_DIR, "Buttons_Links"), "E1", scale=P.INPUTS_BUTTONS_IMAGE_SCALE
        )
        self._place(self.left_solo, P.INPUTS_BUTTONS_LEFT_SOLO_X, P.INPUTS_BUTTONS_LEFT_SOLO_Y, anchor="n")

        self.right_cluster = ButtonClusterGauge(
            parent, os.path.join(IMAGES_DIR, "Buttons_Rechts"), ["E5", "E6", "E7", "E8"],
            scale=P.INPUTS_BUTTONS_IMAGE_SCALE,
        )
        self._place(self.right_cluster, P.INPUTS_BUTTONS_RIGHT_CLUSTER_X, P.INPUTS_BUTTONS_RIGHT_CLUSTER_Y, anchor="n")
        self.right_solo = SoloLamp(
            parent, os.path.join(IMAGES_DIR, "Buttons_Rechts"), "E5", scale=P.INPUTS_BUTTONS_IMAGE_SCALE
        )
        self._place(self.right_solo, P.INPUTS_BUTTONS_RIGHT_SOLO_X, P.INPUTS_BUTTONS_RIGHT_SOLO_Y, anchor="n")

        self._build_minmax_entries(
            adr=0,
            min_label_pos=(P.INPUTS_CONTROLS2_MIN_LABEL_X, P.INPUTS_CONTROLS2_MIN_LABEL_Y),
            min_entry_pos=(P.INPUTS_CONTROLS2_MIN_ENTRY_X, P.INPUTS_CONTROLS2_MIN_ENTRY_Y),
            min_button_pos=(P.INPUTS_CONTROLS2_MIN_BUTTON_X, P.INPUTS_CONTROLS2_MIN_BUTTON_Y),
            slider_pos=(P.INPUTS_CONTROLS2_SLIDER_X, P.INPUTS_CONTROLS2_SLIDER_Y),
            invert_button_pos=(P.INPUTS_CONTROLS2_INVERT_X, P.INPUTS_CONTROLS2_INVERT_Y),
            max_label_pos=(P.INPUTS_CONTROLS2_MAX_LABEL_X, P.INPUTS_CONTROLS2_MAX_LABEL_Y),
            max_entry_pos=(P.INPUTS_CONTROLS2_MAX_ENTRY_X, P.INPUTS_CONTROLS2_MAX_ENTRY_Y),
            max_button_pos=(P.INPUTS_CONTROLS2_MAX_BUTTON_X, P.INPUTS_CONTROLS2_MAX_BUTTON_Y),
        )

        self._place(ttk.Label(parent, text="Accelerate"), P.INPUTS_GAUGE2_LABEL_X, P.INPUTS_GAUGE2_LABEL_Y, anchor="n")
        self.gauge2 = SpriteGauge(parent, os.path.join(IMAGES_DIR, "Z"), scale=P.INPUTS_GAUGE2_Z_AXIS_SCALE)
        self._place(self.gauge2, P.INPUTS_GAUGE2_IMAGE_X, P.INPUTS_GAUGE2_IMAGE_Y, anchor="n")
        self.label2 = ttk.Label(parent, text="0")
        self._place(self.label2, P.INPUTS_GAUGE2_NUMBER_X, P.INPUTS_GAUGE2_NUMBER_Y, anchor="n")

    def _build_minmax_entries(self, adr, min_label_pos, min_entry_pos, min_button_pos,
                               slider_pos, invert_button_pos, max_label_pos, max_entry_pos, max_button_pos):
        parent = self.parent
        min_var = tk.StringVar()
        max_var = tk.StringVar()
        invert_var = tk.BooleanVar(value=False)
        self.minmax_vars[adr] = {"min": min_var, "max": max_var, "raw_value": None, "invert": invert_var}

        self._place(ttk.Label(parent, text="Min:"), min_label_pos[0], min_label_pos[1], anchor="n")
        min_entry = ttk.Entry(parent, textvariable=min_var, width=7, justify="center")
        self._place(min_entry, min_entry_pos[0], min_entry_pos[1], anchor="n")
        min_entry.bind("<Return>", lambda e, a=adr: self._apply_minmax(a, "min"))
        min_entry.bind("<FocusOut>", lambda e, a=adr: self._apply_minmax(a, "min"))
        self._place(
            ttk.Button(
                parent, text="Release + Click", command=lambda a=adr: self._copy_raw_to_field(a, "min"),
                style="DegreeButton.TButton", width=P.BUTTON_WIDTH_CHARS,
            ),
            min_button_pos[0], min_button_pos[1], anchor="n", height=P.EFFECTS_INVERT_ROW_HEIGHT,
        )

        slider = RangeSlider(
            parent,
            on_min_change=lambda v, a=adr: self._on_slider_change(a, "min", v),
            on_max_change=lambda v, a=adr: self._on_slider_change(a, "max", v),
            length=P.INPUTS_SLIDER_LENGTH,
        )
        self._place(slider, slider_pos[0], slider_pos[1], anchor="n")
        self.minmax_vars[adr]["slider"] = slider

        # "Invert Output" toggle (per user request) - swaps which end of
        # the physical travel reads as full/zero deflection, for games
        # that read a trigger backwards (full deflection at rest, zero
        # when pressed). It just flips the firmware's per-channel invert
        # flag (apin.<adr>.invert, applied to the value after min/max
        # scaling - see AnalogAxisProcessing.cpp) - the animation/label
        # stay tied to the physical position regardless (see
        # _update_analog1/2's own un-invert-for-display comment).
        #
        # Same size/shape as Release/Press + Click (width=BUTTON_WIDTH_CHARS,
        # no checkbox indicator - see InvertToggle.TCheckbutton's layout,
        # set up once in EffectsCanvas.__init__), but per user request now
        # gives the same visual on/off feedback as the X-axis's own
        # "Invert Output" toggle: pressed/darker background while active,
        # normal/raised while not - reusing that exact shared ttk style
        # instead of a second, separately-styled one.
        self._place(
            ttk.Checkbutton(
                parent, text="Invert Output", variable=invert_var,
                command=lambda a=adr: self._on_invert_click(a),
                style="InvertToggle.TCheckbutton", width=P.BUTTON_WIDTH_CHARS,
            ),
            invert_button_pos[0], invert_button_pos[1], anchor="n", height=P.EFFECTS_INVERT_ROW_HEIGHT,
        )

        self._place(ttk.Label(parent, text="Max:"), max_label_pos[0], max_label_pos[1], anchor="n")
        max_entry = ttk.Entry(parent, textvariable=max_var, width=7, justify="center")
        self._place(max_entry, max_entry_pos[0], max_entry_pos[1], anchor="n")
        max_entry.bind("<Return>", lambda e, a=adr: self._apply_minmax(a, "max"))
        max_entry.bind("<FocusOut>", lambda e, a=adr: self._apply_minmax(a, "max"))
        self._place(
            ttk.Button(
                parent, text="Press + Click", command=lambda a=adr: self._copy_raw_to_field(a, "max"),
                style="DegreeButton.TButton", width=P.BUTTON_WIDTH_CHARS,
            ),
            max_button_pos[0], max_button_pos[1], anchor="n", height=P.EFFECTS_INVERT_ROW_HEIGHT,
        )

    def _apply_minmax(self, adr, which):
        var = self.minmax_vars[adr][which]
        try:
            value = int(var.get().strip())
        except ValueError:
            return
        value = max(-self.MINMAX_LIMIT, min(self.MINMAX_LIMIT, value))
        var.set(str(value))
        slider = self.minmax_vars[adr]["slider"]
        (slider.set_min if which == "min" else slider.set_max)(value)
        if self.link.connected:
            self.link.set_value("apin", which, value, instance=0, adr=adr)

    def _on_slider_change(self, adr, which, value):
        """User released a slider thumb - reflect the new value in the
        entry field and send it, same as typing it in and pressing Enter."""
        self.minmax_vars[adr][which].set(str(value))
        self._apply_minmax(adr, which)

    def _on_invert_click(self, adr):
        """The Checkbutton's own `variable` has already flipped by the
        time this command fires (same as EffectsCanvas._on_invert_toggle
        for the X-axis) - just read the new state and send it."""
        new_state = self.minmax_vars[adr]["invert"].get()
        if self.link.connected:
            self.link.set_value("apin", "invert", 1 if new_state else 0, instance=0, adr=adr)

    def _on_invert_reply(self, adr, reply):
        try:
            value = int(reply.strip())
        except ValueError:
            return
        self.minmax_vars[adr]["invert"].set(bool(value))

    def _copy_raw_to_field(self, adr, which):
        """Click on a calibration button: use the axis's current raw
        reading as this endpoint (e.g. click "Release + Click" while the
        axis is at rest to calibrate the rest position to -32767)."""
        raw = self.minmax_vars[adr]["raw_value"]
        if raw is None:
            return
        self.minmax_vars[adr][which].set(str(raw))
        self._apply_minmax(adr, which)

    def _on_minmax_reply(self, adr, which, reply):
        text = reply.strip()
        try:
            value = int(text)
        except ValueError:
            return
        self.minmax_vars[adr][which].set(text)
        slider = self.minmax_vars[adr]["slider"]
        (slider.set_min if which == "min" else slider.set_max)(value)

    def on_connected(self):
        # FFBProtocol.connect() clears all listeners, so they must be
        # (re-)added here, once per successful connect.
        self.link.register("apin", "values", self._values_cb, instance=0, typechar="?")
        self.link.register("apin", "rawval", self._rawvalues_cb, instance=0, typechar="?")
        for adr in (0, 1):
            self.link.request_once("apin", "min", lambda reply, a=adr: self._on_minmax_reply(a, "min", reply), instance=0, adr=adr)
            self.link.request_once("apin", "max", lambda reply, a=adr: self._on_minmax_reply(a, "max", reply), instance=0, adr=adr)
            self.link.request_once("apin", "invert", lambda reply, a=adr: self._on_invert_reply(a, reply), instance=0, adr=adr)

    def set_hid_buttons(self, buttons):
        left_bits = tuple(bool(buttons & (1 << i)) for i in range(0, 4))
        right_bits = tuple(bool(buttons & (1 << i)) for i in range(4, 8))
        gp2_bit = bool(buttons & (1 << 8))  # GP2 = DIN8
        gp3_bit = bool(buttons & (1 << 9))  # GP3 = DIN9
        self.left_cluster.set_bits(left_bits)
        self.left_solo.set_state(gp2_bit)  # Wippe links (E1) now driven by GP2
        self.right_cluster.set_bits(right_bits)
        self.right_solo.set_state(gp3_bit)  # Wippe rechts (E5) now driven by GP3

    def _values_cb(self, reply):
        # Channel 0 physically corresponds to the "right" input, channel 1 to
        # "left" - swapped here so "Value analog 1" tracks the left input.
        parts = [p for p in reply.split("\n") if p.strip() != ""]
        try:
            v1 = int(parts[1]) if len(parts) > 1 else 0
            v2 = int(parts[0]) if len(parts) > 0 else 0
        except ValueError:
            return
        if not self.hid_link.connected:
            self._update_analog1(v1)
            self._update_analog2(v2)

    def _rawvalues_cb(self, reply):
        parts = [p for p in reply.split("\n") if p.strip() != ""]
        for adr, entry in self.minmax_vars.items():
            if len(parts) <= adr:
                continue
            try:
                raw = int(parts[adr])
            except ValueError:
                continue
            entry["raw_value"] = raw
            entry["slider"].set_live(raw)

    def _update_analog1(self, v1):
        # v1 already carries the firmware's own "Invert Output" flip
        # (apin.1.invert, applied in AnalogAxisProcessing::processAxes())
        # - negate it back here so the label/animation always tracks the
        # physical trigger position, per user request: inverting the
        # animation too made pressing the trigger look like it was
        # releasing, which felt wrong. Only the actual output (this same
        # v1, sent on to games via HID/serial) stays inverted.
        if self.minmax_vars[1]["invert"].get():
            v1 = -v1
        self.label1.configure(text=str(v1))
        self.gauge1.set_value(v1, -32768, 32767)

    def _update_analog2(self, v2):
        # Same un-invert-for-display as _update_analog1 above, for adr=0.
        if self.minmax_vars[0]["invert"].get():
            v2 = -v2
        self.label2.configure(text=str(v2))
        self.gauge2.set_value(v2, -32768, 32767)

    def set_hid_yz(self, y, z):
        # Same swap as _values_cb: Y/Z carry the same two channels in the same order.
        self._update_analog1(z)
        self._update_analog2(y)

    def poll(self):
        # Shared apin.0.values/apin.0.rawval poll - EffectsCanvas's Force
        # section listens to the same replies without sending its own
        # duplicate request.
        self.link.send_get("apin", "values", instance=0)
        self.link.send_get("apin", "rawval", instance=0)


class EffectsCanvas(PlacedGroup):
    """All FFB effect sliders (Axis Range/Power/Effects intensity/Endstop
    gain/Desktop spring + global fx Spring/Damper/Friction/Inertia Gain)
    stacked on the left, the X-axis degree gauge plus Invert/Center controls
    on the right - place()-positioned (see Placement.py, EFFECTS_*
    constants), directly on App.main_frame. Assumes exactly one axis
    instance (this board's hardware), unlike the old per-instance AxisPanel.

    No longer its own bordered "Effects" LabelFrame (removed per user
    request, see PlacedGroup above) - this class is now a plain builder
    that places its children directly onto the shared parent."""

    GAIN_CMDS = [
        ("spring", "Spring Gain"),
        ("damper", "Damper Gain"),
        ("friction", "Friction Gain"),
        ("inertia", "Inertia Gain"),
    ]

    # "(XX%)" readout for the 4 gain sliders is relative to the GAME's own
    # effect coefficient (its "100%"), not to the slider's own raw range.
    # Firmware: force = coefficient * gainfactor * scaler.<effect>, with
    # gainfactor=(raw+1)/256 (EffectsCalculator.cpp). 100% is where our gain
    # exactly reproduces the game's coefficient, i.e. gainfactor*scaler=1 -
    # a scaler above 1x (everything but Friction) therefore shows *above*
    # 100% once the slider amplifies past that point. GAIN_PERCENT_DENOM is
    # the formula's fixed denominator (256, not a raw value); GAIN_SCALER is
    # each effect's fixed multiplier from EffectsCalculator.h's
    # effect_scaler_t defaults (spring=16, damper=4, friction=1, inertia=2).
    GAIN_PERCENT_DENOM = 256
    GAIN_SCALER = {
        "spring": 16,
        "damper": 4,
        "friction": 1,
        "inertia": 2,
    }

    # Save/Load ".twisty" profile field list, top-to-bottom in the same
    # order as the sliders appear on screen (Power..Permanent Inertia, then
    # Range) - per user request, "invert" is handled separately below
    # since it's a checkbutton/BooleanVar, not a LabeledSlider. Each entry
    # is (firmware command name - also the file's "key=" on each line,
    # command class "axis"/"fx", attribute name on self holding the
    # LabeledSlider - None for "fx" commands, looked up via
    # self.fx_sliders[cmd] instead, since there are 4 of those sharing one
    # dict rather than 4 separate named attributes).
    SAVE_LOAD_FIELDS = [
        ("expo", "axis", "expo_slider"),
        ("power", "axis", "power_slider"),
        ("esgain", "axis", "esgain_slider"),
        ("idlespring", "axis", "idlespring_slider"),
        ("fxratio", "axis", "fxratio_slider"),
        ("spring", "fx", None),
        ("damper", "fx", None),
        ("friction", "fx", None),
        ("inertia", "fx", None),
        ("axisdamper", "axis", "permdamper_slider"),
        ("axisfriction", "axis", "permfriction_slider"),
        ("axisinertia", "axis", "perminertia_slider"),
        ("degrees", "axis", "range_entry"),
    ]
    # Freq/Q (Damper/Friction/Inertia) + Friction's Smooth ramp-up live
    # entirely on the Advanced tab (FxTuningPanel, via self.fx_panel) - no
    # Main-tab slider for these, so they don't fit the SAVE_LOAD_FIELDS/
    # LabeledSlider shape above and are handled separately in
    # _on_save_profile/_load_freq_q_fields. Spring has no Freq/Q row (it's
    # not a filter effect), matching FxTuningPanel's own DOMAINS/cell
    # layout.
    SAVE_LOAD_FREQ_Q_CMDS = ("damper", "friction", "inertia")
    LOAD_STEP_DELAY_MS = 50  # gap between each slider "arriving" on Load - matches the old GUI's own hardcoded 50ms pacing

    def __init__(self, parent, link, hid_link, axis_instance=0, base_x=0, base_y=0):
        self._init_group(parent, base_x, base_y)
        self.link = link
        self.hid_link = hid_link
        self.instance = axis_instance
        self.fx_scales = {cmd: 1.0 for cmd, _ in self.GAIN_CMDS}
        self.fx_sliders = {}
        # Set by App._build_ui() once the Advanced tab exists (this class
        # is built first) - a dict {cmd: LabeledSlider} pointing at
        # FxTuningPanel's own copy of the same 4 gain sliders, for direct
        # Python-side cross-tab sync (see _send_fx()). Not serial-echo
        # based (that was the old, broken approach - the firmware
        # acknowledges a "=" SET with a plain "OK", never the value, so a
        # listener on that echo can never actually learn the new value -
        # see the Save/Load bugfix conversation for the full story).
        self.other_gain_sliders = None
        # Same idea as other_gain_sliders above, but for the single Expo
        # slider (not part of the fx_sliders dict, own LabeledSlider each
        # side) - set by App._build_ui() to FxTuningPanel's expo_slider.
        self.other_expo_slider = None
        # Set by App._build_ui() to the Advanced tab's FxTuningPanel
        # instance - used only by Save/Load for the Freq/Q/Smooth fields,
        # which live entirely on the Advanced tab (no Main-tab slider for
        # those, unlike Gain/Expo) - see SAVE_LOAD_FREQ_Q_FIELDS.
        self.fx_panel = None
        # Set by App._build_ui() to the Main tab's InputsCanvas instance -
        # used only by Save/Load for the Value analog 1/2 Min/Max
        # calibration + Invert Output fields, which live entirely on
        # InputsCanvas (see _load_inputs_fields()).
        self.inputs_canvas = None

        # "Exponential" (61px measured) fits comfortably within the shared
        # SLIDER_LABEL_W (108px, sized for "Permanent Damper") - no
        # per-instance label_width override needed, unlike the earlier,
        # much longer "Minforce Scale ( 1=off )" name.
        self.expo_slider = LabeledSlider(parent, "Exponential", -127, 127, self._send_expo())
        self._place(self.expo_slider, P.EFFECTS_SLIDER_EXPO_X, P.EFFECTS_SLIDER_EXPO_Y)

        # Power is Axis::updateTorque()'s (Axis.cpp) final multiplier over
        # game effects + permanent effects + endstop combined; the endstop
        # torque is computed purely from wheel position, independent of any
        # game effect; Test Spring ("idlespring") is only added while
        # ffb_on is false, i.e. while nothing else (no game) is active.
        # Overall Gain ("effect_margin_scaler", firmware command "fxratio")
        # scales only the game-effect sum excluding the endstop (matches the
        # firmware's own "fxratio" command description).
        self.power_slider = LabeledSlider(
            parent, "Power", 0, 32767, self._send_axis("power"), percent_max=32767,
        )
        self.fxratio_slider = LabeledSlider(
            parent, "Overall Gain", 102, 255, self._send_axis("fxratio"), percent_max=255,
        )
        self.esgain_slider = LabeledSlider(
            parent, "Endstop Gain", 0, 255, self._send_axis("esgain"), percent_max=255,
        )
        self.idlespring_slider = LabeledSlider(
            parent, "Test Spring", 0, 255, self._send_axis("idlespring"), percent_max=255,
        )

        self._place(self.power_slider, P.EFFECTS_SLIDER_POWER_X, P.EFFECTS_SLIDER_POWER_Y)
        self._place(self.fxratio_slider, P.EFFECTS_SLIDER_FXRATIO_X, P.EFFECTS_SLIDER_FXRATIO_Y)
        self._place(self.esgain_slider, P.EFFECTS_SLIDER_ESGAIN_X, P.EFFECTS_SLIDER_ESGAIN_Y)
        self._place(self.idlespring_slider, P.EFFECTS_SLIDER_IDLESPRING_X, P.EFFECTS_SLIDER_IDLESPRING_Y)

        fx_positions = {
            "spring": (P.EFFECTS_SLIDER_SPRING_X, P.EFFECTS_SLIDER_SPRING_Y),
            "damper": (P.EFFECTS_SLIDER_DAMPER_X, P.EFFECTS_SLIDER_DAMPER_Y),
            "friction": (P.EFFECTS_SLIDER_FRICTION_X, P.EFFECTS_SLIDER_FRICTION_Y),
            "inertia": (P.EFFECTS_SLIDER_INERTIA_X, P.EFFECTS_SLIDER_INERTIA_Y),
        }
        for cmd, label in self.GAIN_CMDS:
            # Multiplies the game's own condition effect of this type
            # (EffectsCalculator.cpp) - 0 effect if the current game never
            # sends that effect type, regardless of this slider's value.
            slider = LabeledSlider(
                parent, label, 0, 255, self._send_fx(cmd),
                percent_max=self.GAIN_PERCENT_DENOM, percent_offset=1, percent_scale=self.GAIN_SCALER[cmd],
            )
            x, y = fx_positions[cmd]
            self._place(slider, x, y)
            self.fx_sliders[cmd] = slider

        # The 3 always-on "permanent" effects (moved here from the Advanced
        # Tuning tab's former LimitsPanel per user request - reference
        # Configurator's "Mechanical settings" group, res/axis_ui.ui;
        # Test Spring/Range from that same group are already above).
        # Speed limit (also from that dialog's "Limits" group) was removed
        # again - not needed. percent_max=255 (own vmax, offset=0/scale=1
        # default -> plain raw/255*100): same style as Endstop Gain/Test
        # Spring, not the 4 Gain sliders' gainfactor formula - these 3 are
        # direct linear multipliers in the firmware (Axis.cpp:
        # damperIntensity/frictionIntensity/inertiaIntensity), with no
        # external game coefficient for a "100%" to be relative to.
        # Added to torque unconditionally (Axis.cpp: torque += axisEffectTorque),
        # regardless of what the game sends - always on.
        self.permdamper_slider = LabeledSlider(
            parent, "Permanent Damper", 0, 255, self._send_axis("axisdamper"), percent_max=255,
        )
        self._place(self.permdamper_slider, P.EFFECTS_SLIDER_PERMDAMPER_X, P.EFFECTS_SLIDER_PERMDAMPER_Y)
        self.permfriction_slider = LabeledSlider(
            parent, "Permanent Friction", 0, 255, self._send_axis("axisfriction"), percent_max=255,
        )
        self._place(self.permfriction_slider, P.EFFECTS_SLIDER_PERMFRICTION_X, P.EFFECTS_SLIDER_PERMFRICTION_Y)
        self.perminertia_slider = LabeledSlider(
            parent, "Permanent Inertia", 0, 255, self._send_axis("axisinertia"), percent_max=255,
        )
        self._place(self.perminertia_slider, P.EFFECTS_SLIDER_PERMINERTIA_X, P.EFFECTS_SLIDER_PERMINERTIA_Y)

        self._build_group_dividers()

        # "Save"/"Load" buttons below the left-column sliders, per user
        # request - same design (style="DegreeButton.TButton") as the
        # degree/Invert buttons above the Range slider on the right.
        # Save/Load a plain-text ".twisty" profile of every slider on this
        # page (Power..Permanent Inertia, Range, Invert) - ported from the
        # old Twisty_Arduino_GUI's own Save/Load feature (same idea, same
        # file extension), with two changes: the old GUI wrote/read the
        # literal str() of a Python tuple (positional, fragile - breaks
        # silently on any format drift); this one writes plain
        # "command=value" lines instead, self-documenting and order-
        # independent. And the old GUI stepped through each slider with a
        # blocking time.sleep(0.05)+window.update() pair; this one chains
        # self.after() calls instead, so the same "slider visibly moves
        # into place, one at a time" effect on Load doesn't freeze the
        # rest of the GUI while it plays out. Deliberately excludes the
        # trigger/analog Min/Max calibration (InputsCanvas) per user
        # request - out of scope, not part of this page.
        self._place(
            ttk.Button(
                parent, text="Save", command=self._on_save_profile,
                style="DegreeButton.TButton", width=P.BUTTON_WIDTH_CHARS,
            ),
            P.EFFECTS_SAVE_X, P.EFFECTS_SAVE_LOAD_Y, height=P.EFFECTS_INVERT_ROW_HEIGHT,
        )
        self._place(
            ttk.Button(
                parent, text="Load", command=self._on_load_profile,
                style="DegreeButton.TButton", width=P.BUTTON_WIDTH_CHARS,
            ),
            P.EFFECTS_LOAD_X, P.EFFECTS_SAVE_LOAD_Y, height=P.EFFECTS_INVERT_ROW_HEIGHT,
        )

        self.gauge = SpriteGauge(parent, os.path.join(IMAGES_DIR, "X"), scale=P.EFFECTS_GAUGE_X_AXIS_SCALE)
        self._place(self.gauge, P.EFFECTS_GAUGE_IMAGE_X, P.EFFECTS_GAUGE_IMAGE_Y, anchor="n")

        # Range + the Invert/degree/Center row both moved from their old
        # spots (Range: top of the left slider list; Invert/degree/Center:
        # directly above the gauge) to sit together below the gauge image
        # instead, per user request - same widgets/style, only place()d at
        # new coordinates. Range's old slot in the left list is left empty
        # on purpose (not closed up) - also per user request.
        #
        # Slider track dropped per user request (LabeledSlider -> the
        # slider-less LabeledEntry, same Label+Entry pair/behavior/
        # get_value()/set_from_firmware() interface) and moved to sit right
        # above the Center/Invert row, centered on that row's own horizontal
        # center (EFFECTS_RANGE_ENTRY_X below) instead of the old full-width
        # slider position.
        self.range_entry = LabeledEntry(
            parent, "Range", 10, 330, self._send_axis("degrees"), unit="°",
            label_width=P.EFFECTS_SLIDER_RANGE_LABEL_W,
        )
        self._place(self.range_entry, P.EFFECTS_RANGE_ENTRY_X, P.EFFECTS_RANGE_ENTRY_Y)

        # Real ttk.Button per user request (plan change from an earlier
        # relief="raised" tk.Label - that was meant to look button-ish but
        # stay inert; now it must actually behave like one: same action the
        # old standalone "Set center position" button had, now removed per
        # user request since this one replaces it). width=P.BUTTON_WIDTH_CHARS
        # (shared by every button in the app, per user request) is wide
        # enough for the widest text this button will ever show,
        # ">-330.0°<" (9 chars, covers a negative reading down to -330.0
        # too, not just the positive max), so the button doesn't jitter in
        # width as the live degree value changes length.
        #
        # style="DegreeButton.TButton" - same custom-styled look as the
        # Invert toggle below and the Save/Load buttons above (registered
        # once, right after _build_group_dividers() - see that comment for
        # why a plain ttk.Button/style="Toolbutton" needed a clam-borrowed
        # Button.border element under Windows' native "vista" theme, and
        # why relief="raised" specifically was the missing piece). No
        # "selected"/toggle state here though, since this is a momentary
        # action (fires once), not a persistent on/off like Invert: just
        # normal press/hover feedback, nothing that stays highlighted
        # afterward.
        self.degree_label = ttk.Button(
            parent, text=">0.0°<", command=self._on_set_center, width=P.BUTTON_WIDTH_CHARS,
            style="DegreeButton.TButton",
        )
        self._place(
            self.degree_label, P.EFFECTS_GAUGE_DEGREE_X, P.EFFECTS_GAUGE_DEGREE_Y, anchor="n",
            height=P.EFFECTS_INVERT_ROW_HEIGHT,
        )

        # Toggle button ("Invert") per user request, replacing the
        # "Normal"/"Inverted" segmented control (two ttk.Radiobuttons) -
        # one ttk.Checkbutton, same shared invert_var/command underneath.
        #
        # Plain "Toolbutton" style (tried first) turned out invisible at
        # rest - Windows' native "vista" theme only paints it (border +
        # background) on hover/press, so unchecked-and-not-hovered looked
        # like bare text, not a button (per user's own screenshot). Same
        # root cause as the earlier Black.TCheckbutton problem (Abschnitt
        # 4.20.6): "vista" draws these via the OS visual-style engine and
        # ignores style.configure() on the stock elements. Fixed the same
        # way - borrow "Button.border" from the "clam" theme (which IS
        # plain Tk drawing, so styling it actually works) into a custom
        # Checkbutton layout, so it always shows a normal button-like
        # border + background, in both the checked and unchecked state.
        style = ttk.Style()
        style.element_create("InvertToggle.border", "from", "clam", "Button.border")
        style.layout("InvertToggle.TCheckbutton", [
            ("InvertToggle.border", {"sticky": "nswe", "border": "1", "children": [
                ("Checkbutton.padding", {"sticky": "nswe", "children": [
                    ("Checkbutton.label", {"sticky": "nswe"}),
                ]}),
            ]}),
        ])
        style.configure(
            "InvertToggle.TCheckbutton", anchor="center", borderwidth=P.BUTTON_BORDERWIDTH,
            bordercolor=P.BUTTON_BORDER_COLOR,
            lightcolor=P.BUTTON_SHADOW_LIGHT_COLOR, darkcolor=P.BUTTON_SHADOW_DARK_COLOR,
        )
        style.map(
            "InvertToggle.TCheckbutton",
            background=[("selected", P.BUTTON_PRESSED_COLOR), ("!selected", P.BUTTON_BG_COLOR)],
            relief=[("selected", P.BUTTON_RELIEF_PRESSED), ("!selected", P.BUTTON_RELIEF)],
        )
        self._suppress_invert = False
        self.invert_var = tk.BooleanVar(value=False)
        self._place(
            ttk.Checkbutton(
                parent, text="Invert Output", variable=self.invert_var,
                command=self._on_invert_toggle, style="InvertToggle.TCheckbutton",
                width=P.BUTTON_WIDTH_CHARS,
            ),
            P.EFFECTS_INVERT_X, P.EFFECTS_INVERT_Y, anchor="n",
            height=P.EFFECTS_INVERT_ROW_HEIGHT,
        )

        self._build_force_chart()

    def _build_group_dividers(self):
        """Thin separator lines marking the same two slider-group boundaries
        as before (Test Spring | Overall Gain.. Inertia Gain | Permanent
        Damper..) - the shared caption text per group was removed again per
        user request, and the lines themselves shortened to end where the
        sliders end (previously extended further right to underline the
        now-removed caption column too). See Placement.py's
        EFFECTS_SLIDER_DIVIDER* constants."""
        self._place(
            ttk.Separator(self.parent, orient="horizontal"),
            P.EFFECTS_SLIDER_DIVIDER_X, P.EFFECTS_SLIDER_DIVIDER1_Y, width=P.EFFECTS_SLIDER_DIVIDER_WIDTH,
        )
        self._place(
            ttk.Separator(self.parent, orient="horizontal"),
            P.EFFECTS_SLIDER_DIVIDER_X, P.EFFECTS_SLIDER_DIVIDER2_Y, width=P.EFFECTS_SLIDER_DIVIDER_WIDTH,
        )

    def _build_force_chart(self):
        """The always-on FFB-strength strip chart, placed below the
        Invert/Center row - see Placement.py's EFFECTS_FORCE_CHART_*
        constants. Formerly also had a "FFB Strength" caption and a "Graph"
        show/hide checkbox here (the old standalone ForceCanvas class's
        "Force" section, back when it also included the Voltage/Temp
        readouts) - both removed again per user request: the numeric value
        moved out entirely into App's ReadoutBar ("FFB: +x.x %" at the end
        of that row), and the checkbox's toggle is gone too, since
        without a value label next to it there was nothing left to
        caption - the chart is simply always shown now, no toggle."""
        chart_bg = ttk.Style().lookup("TFrame", "background")
        self.force_chart = StripChart(self.parent, height=P.EFFECTS_FORCE_CHART_HEIGHT, bg=chart_bg)
        self._place(self.force_chart, P.EFFECTS_FORCE_CHART_X, P.EFFECTS_FORCE_CHART_Y, width=P.EFFECTS_FORCE_CHART_WIDTH)

    def _force_torque_cb(self, reply):
        try:
            raw = int(reply)
        except ValueError:
            return
        self.force_chart.add_sample(raw / 100.0)

    def _send_axis(self, cmd):
        def sender(val):
            self.link.set_value("axis", cmd, int(val), instance=self.instance)
        return sender

    def _send_fx(self, cmd):
        def sender(val):
            self.link.set_value("fx", cmd, int(val), instance=0)
            # Direct Python-side mirror of the Advanced tab's copy of this
            # same gain slider - see other_gain_sliders' own comment in
            # __init__ for why this doesn't rely on the firmware's serial
            # reply. set_from_firmware() only redraws that slider, it
            # never re-sends or re-triggers this sender, so this can't
            # loop back and forth between the two tabs.
            if self.other_gain_sliders is not None:
                self.other_gain_sliders[cmd].set_from_firmware(val)
            # Same direct-call approach as above, extended to the Advanced
            # tab's response-curve chart: set_from_firmware() only moves
            # that tab's slider, it never touches FxTuningPanel.gains or
            # redraws the chart - without this, the chart kept showing the
            # gain from the last time it was changed *on the Advanced tab
            # itself* (or the value at connect), silently going stale
            # whenever a gain was changed from the Main tab instead.
            if self.fx_panel is not None:
                self.fx_panel.gains[cmd] = int(val)
                self.fx_panel._redraw_curve(cmd)
        return sender

    def _send_expo(self):
        def sender(val):
            self.link.set_value("axis", "expo", int(val), instance=self.instance)
            if self.other_expo_slider is not None:
                self.other_expo_slider.set_from_firmware(val)
            # Same reasoning as _send_fx() above, for the Expo chart -
            # other_expo_slider.set_from_firmware() already updated
            # fx_panel.expo_slider's value, so _redraw_expo() (which reads
            # that slider) now sees the new value.
            if self.fx_panel is not None:
                self.fx_panel._redraw_expo()
        return sender

    def _fx_scale_cb(self, cmd):
        def cb(reply):
            info = parse_infostring(reply)
            self.fx_scales[cmd] = info.get("scale", 1.0)
        return cb

    def _safe_gain_update(self, cmd):
        """Same as fx_sliders[cmd].set_from_firmware, but tolerates a
        non-numeric reply (e.g. the firmware's plain "OK" acknowledgment
        for a "=" SET command) instead of letting float() raise
        uncaught - see the long comment at its registration in
        on_connected() for how this was found."""
        def cb(reply):
            try:
                self.fx_sliders[cmd].set_from_firmware(reply)
            except ValueError:
                pass
        return cb

    def _on_invert_toggle(self):
        if self._suppress_invert:
            return
        self.link.set_value("axis", "invert", 1 if self.invert_var.get() else 0, instance=self.instance)

    def _on_set_center(self):
        """Same as the official Configurator's "Set center position" button
        - a bare trigger, no confirmation, no value display. Firmware sets
        the current position as the new zero point (Axis.cpp: zeroenc ->
        setPos(0))."""
        if not self.link.connected:
            return
        self.link.send_get("axis", "zeroenc", instance=self.instance)

    def _get_slider_for_field(self, cmd, kind, attr):
        return self.fx_sliders[cmd] if kind == "fx" else getattr(self, attr)

    def _sender_for_field(self, cmd, kind):
        if kind == "fx":
            return self._send_fx(cmd)
        if cmd == "expo":
            return self._send_expo()  # not the generic _send_axis - also mirrors to the Advanced tab's own Expo slider
        return self._send_axis(cmd)

    def _on_save_profile(self):
        """Write every SAVE_LOAD_FIELDS slider's current raw value, plus
        Invert, to a plain-text ".twisty" file as "command=value" lines -
        ported from the old Twisty_Arduino_GUI's Save feature (same file
        extension/idea), but "command=value" lines instead of that GUI's
        str(tuple) format, so the file stays readable and isn't tied to a
        fixed field order. Works whether or not a board is connected - it
        only reads the sliders' current on-screen values, nothing is sent
        anywhere."""
        path = filedialog.asksaveasfilename(
            defaultextension=".twisty", filetypes=[("Twisty Files", "*.twisty")],
        )
        if not path:
            return
        lines = [
            f"{cmd}={int(self._get_slider_for_field(cmd, kind, attr).get_value())}"
            for cmd, kind, attr in self.SAVE_LOAD_FIELDS
        ]
        lines.append(f"invert={int(self.invert_var.get())}")
        if self.fx_panel is not None:
            # The actual "Effect filter profile" dropdown state (Default=0/
            # Custom=1, matching fx.0.filterProfile_id's own wire values) -
            # saved/restored directly per user request, instead of the
            # earlier approach of inferring/forcing "Custom" just because
            # Freq/Q values happened to be present in the file.
            lines.append(f"filterProfile={1 if self.fx_panel.profile_var.get() == 'Custom' else 0}")
            for cmd in self.SAVE_LOAD_FREQ_Q_CMDS:
                lines.append(f"{cmd}_f={self.fx_panel.freq_vars[cmd].get()}")
                lines.append(f"{cmd}_q={self.fx_panel.q_vars[cmd].get()}")
            lines.append(f"frictionPctSpeedToRampup={int(self.fx_panel.smooth_slider.get_value())}")
        if self.inputs_canvas is not None:
            # Value analog 1 ("Brake", adr=1) / Value analog 2
            # ("Accelerate", adr=0) Min/Max calibration + Invert Output - per
            # user request, same "saved/restored as its own set of keys"
            # treatment as filterProfile/Freq/Q above.
            for adr in (1, 0):
                entry = self.inputs_canvas.minmax_vars[adr]
                try:
                    # min/max are blank StringVars until a value arrives
                    # from the firmware (e.g. never connected yet) -
                    # silently skip them then, same as Load already does
                    # for keys missing from a file.
                    lines.append(f"apin{adr}_min={int(entry['min'].get())}")
                    lines.append(f"apin{adr}_max={int(entry['max'].get())}")
                except ValueError:
                    pass
                lines.append(f"apin{adr}_invert={int(entry['invert'].get())}")
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write("\n".join(lines) + "\n")
        except OSError as e:
            messagebox.showerror("Save failed", str(e))

    def _on_load_profile(self):
        """Read a ".twisty" file (same "command=value" lines Save writes)
        and play the values into the sliders one at a time - same visible
        effect as the old GUI's Load (each slider moves, then its value is
        sent to the firmware, with a short pause before the next one), but
        chained via self.after() instead of a blocking time.sleep() +
        forced window.update(), so the rest of the GUI stays responsive
        while it plays out. Unknown/missing keys in the file are silently
        skipped (e.g. a profile saved before a field existed). Works
        without a connected board too - the sliders still move to show the
        loaded profile, the firmware-bound sender calls just silently do
        nothing (link.send_raw() already no-ops when nothing is
        connected, same as every other command in this app)."""
        path = filedialog.askopenfilename(filetypes=[("Twisty Files", "*.twisty")])
        if not path:
            return
        values = {}
        try:
            with open(path, "r", encoding="utf-8") as f:
                for line in f:
                    key, sep, val = line.strip().partition("=")
                    if not sep:
                        continue
                    val = val.strip()
                    try:
                        values[key.strip()] = int(val)
                    except ValueError:
                        try:
                            values[key.strip()] = float(val)  # Q fields (e.g. "0.40") aren't whole numbers
                        except ValueError:
                            continue
        except OSError as e:
            messagebox.showerror("Load failed", str(e))
            return
        self._load_pending = list(self.SAVE_LOAD_FIELDS)
        self._load_values = values
        self._load_next_field()

    def _load_next_field(self):
        if not self._load_pending:
            if "invert" in self._load_values:
                state = bool(self._load_values["invert"])
                self.invert_var.set(state)
                self.link.set_value("axis", "invert", int(state), instance=self.instance)
            if self.fx_panel is not None:
                self._load_freq_q_fields()
            if self.inputs_canvas is not None:
                self._load_inputs_fields()
            return
        cmd, kind, attr = self._load_pending.pop(0)
        if cmd in self._load_values:
            value = self._load_values[cmd]
            self._get_slider_for_field(cmd, kind, attr).set_from_firmware(value)
            self._sender_for_field(cmd, kind)(value)
        # EffectsCanvas (PlacedGroup) is a plain builder, not a Tk widget
        # itself - self.after() doesn't exist here, only on real widgets
        # like self.parent (the frame everything in this class is placed
        # onto).
        self.parent.after(self.LOAD_STEP_DELAY_MS, self._load_next_field)

    def _load_freq_q_fields(self):
        """Freq/Q/Smooth + the filter-profile dropdown live only on the
        Advanced tab (self.fx_panel) - applied all at once at the end of
        Load, rather than staggered like the main slider queue above,
        since they're small text fields rather than a big visual slider
        "arriving" one at a time. Reuses FxTuningPanel's own
        _on_freq_apply()/_on_q_apply() (instead of duplicating their
        raw*100 wire-encoding for Q) - they read straight from
        freq_vars/q_vars, so those are set first.

        The "filterProfile" field restores the actual saved dropdown
        state (Default/Custom) directly - per user request, NOT inferred
        by switching to "Custom" just because Freq/Q values happen to be
        present in the file (an earlier, wrong approach here)."""
        fx = self.fx_panel
        if "filterProfile" in self._load_values:
            fx.profile_var.set("Custom" if int(self._load_values["filterProfile"]) else "Default")
            fx._on_profile_change()
        for cmd in self.SAVE_LOAD_FREQ_Q_CMDS:
            key_f = f"{cmd}_f"
            if key_f in self._load_values:
                fx.freq_vars[cmd].set(str(int(self._load_values[key_f])))
                fx._on_freq_apply(cmd)
            key_q = f"{cmd}_q"
            if key_q in self._load_values:
                fx.q_vars[cmd].set(f"{float(self._load_values[key_q]):.2f}")
                fx._on_q_apply(cmd)
        if "frictionPctSpeedToRampup" in self._load_values:
            val = int(self._load_values["frictionPctSpeedToRampup"])
            fx.smooth_slider.set_from_firmware(val)
            fx._send_fx("frictionPctSpeedToRampup")(val)

    def _load_inputs_fields(self):
        """Value analog 1 ("Brake", adr=1) / Value analog 2 ("Accelerate",
        adr=0) Min/Max calibration + Invert Output live on the Main tab's
        InputsCanvas (self.inputs_canvas) - applied all at once at the end
        of Load, same treatment as _load_freq_q_fields() above."""
        ic = self.inputs_canvas
        for adr in (1, 0):
            entry = ic.minmax_vars[adr]
            for which in ("min", "max"):
                key = f"apin{adr}_{which}"
                if key in self._load_values:
                    entry[which].set(str(int(self._load_values[key])))
                    ic._apply_minmax(adr, which)
            invert_key = f"apin{adr}_invert"
            if invert_key in self._load_values:
                new_state = bool(int(self._load_values[invert_key]))
                entry["invert"].set(new_state)
                if ic.link.connected:
                    ic.link.set_value("apin", "invert", int(new_state), instance=0, adr=adr)

    def _on_invert_reply(self, reply):
        # Firmware calls resetMetrics() on every "invert" set, even if the
        # value doesn't change - suppress so reading the current state at
        # connect time doesn't itself trigger a redundant reset.
        try:
            val = int(reply.strip())
        except ValueError:
            return
        self._suppress_invert = True
        try:
            self.invert_var.set(bool(val))
        finally:
            self._suppress_invert = False

    def _update_gauge(self, degrees):
        self.degree_label.configure(text=f">{degrees:.1f}°<")
        max_range = self.range_entry.get_value() or 360
        self.gauge.set_value(degrees, -max_range / 2, max_range / 2)

    def _curpos_cb(self, reply):
        """Serial fallback: axis.0.curpos is already scaled/clipped exactly
        like the HID report's X field (unlike axis.0.pos, which is raw,
        cumulative encoder ticks)."""
        try:
            val = int(reply)
        except ValueError:
            return
        self.set_hid_x(val)

    def set_hid_x(self, raw_x):
        """raw_x: signed 16-bit value from the HID report's X field, pre-scaled
        by the firmware to +/- half of the current Range (deg) setting.
        Already carries the firmware's own "Invert Output" flip
        (axis.invert, applied in Axis::getEncAngle()) - negated back here
        so the wheel animation always tracks the physical wheel position,
        per user request (an inverted animation made turning the wheel
        look like it was turning the other way, which felt wrong). Only
        the actual output (this same raw_x, sent on to games) stays
        inverted."""
        if self.invert_var.get():
            raw_x = -raw_x
        degrees_range = self.range_entry.get_value() or 360
        degrees = raw_x * degrees_range / 65535.0
        self._update_gauge(degrees)

    def on_connected(self):
        self.link.register("axis", "curpos", self._curpos_cb, instance=self.instance, typechar="?")
        self.link.request_once("axis", "degrees", self.range_entry.set_from_firmware, instance=self.instance)
        self.link.request_once("axis", "power", self.power_slider.set_from_firmware, instance=self.instance)
        self.link.request_once("axis", "fxratio", self.fxratio_slider.set_from_firmware, instance=self.instance)
        self.link.request_once("axis", "esgain", self.esgain_slider.set_from_firmware, instance=self.instance)
        self.link.request_once("axis", "idlespring", self.idlespring_slider.set_from_firmware, instance=self.instance)
        self.link.request_once("axis", "invert", self._on_invert_reply, instance=self.instance)
        self.link.request_once("axis", "axisdamper", self.permdamper_slider.set_from_firmware, instance=self.instance)
        self.link.request_once("axis", "axisfriction", self.permfriction_slider.set_from_firmware, instance=self.instance)
        self.link.request_once("axis", "axisinertia", self.perminertia_slider.set_from_firmware, instance=self.instance)
        self.link.request_once("axis", "expo", self.expo_slider.set_from_firmware, instance=self.instance)

        for cmd, _ in self.GAIN_CMDS:
            self.link.request_once("fx", cmd, self._fx_scale_cb(cmd), instance=0, typechar="!")
            # Both "?" (get reply) and "=" (set echo), but NOT "!" (info
            # string, handled separately above) - catches this slider's
            # initial value on connect (via the send_get() below) and any
            # externally-driven change (e.g. a filter profile reset on the
            # firmware side). NOT what keeps this in sync with the
            # Advanced tab's own copy of the same gain (see
            # other_gain_sliders' comment in __init__ for that - a direct
            # Python-side mirror instead, since the firmware acknowledges
            # a "=" SET with a plain "OK", never the value, so this
            # listener can't learn a same-tab-drag's new value at all). A
            # single typechar=None listener here would also catch the "!"
            # reply above and crash trying to float()-parse its
            # "scale:16.000000,factor:..." text.
            #
            # _safe_gain_update() (not fx_sliders[cmd].set_from_firmware
            # directly) - discovered while testing Load (Abschnitt
            # Save/Load): the firmware's own "=" echo for a SET command is
            # sometimes a plain "OK" acknowledgment instead of the number,
            # which set_from_firmware's bare float(val) can't parse and
            # crashes uncaught ("Callback error (fx.0.damper): could not
            # convert string to float: 'OK'"). This isn't specific to
            # Load - a manual drag on a Gain slider sends the exact same
            # "=" command and would hit the same "OK" reply; Load's rapid
            # back-to-back sends just made it show up first. FxTuningPanel's
            # own _on_gain_reply() already guards the identical case with a
            # try/except - this mirrors that.
            self.link.register("fx", cmd, self._safe_gain_update(cmd), instance=0, typechar="?")
            self.link.register("fx", cmd, self._safe_gain_update(cmd), instance=0, typechar="=")
            self.link.send_get("fx", cmd, instance=0)

        # Force chart (see _build_force_chart) - the "vesc"/"torque"
        # get() itself is sent by ReadoutBar now (needs it unconditionally
        # for its own always-on value display), this just listens for the
        # same broadcast to feed the chart, same shared-poll pattern as
        # InputsCanvas's apin.0.rawval (see that class's docstring).
        self.link.register("vesc", "torque", self._force_torque_cb, instance=0, typechar="?")

    def poll(self):
        if not self.hid_link.connected:
            self.link.send_get("axis", "curpos", instance=self.instance)


class ReadoutBar(ttk.Frame):
    """Single-line VCC + L1/L2/L3 temperature + FFB Strength readout,
    spanning the full window width directly below the toolbar row
    (App._build_ui()) - visible on both the Main and Advanced Tuning pages,
    since it sits above the page switcher. Moved out of EffectsCanvas's old
    _build_readout_section (Voltage/Temp stacked label-above-bold-value
    beside the gauge image) and _build_force_chart (the FFB Strength value
    and its caption, added here at the end of the row per user request as
    "FFB: +x.x %", shortened from "FFB Strength: +x.x %" per a later user
    request - the always-on strip chart itself stays in EffectsCanvas,
    only the numeric value and its caption moved) - one plain-text row
    instead, in the same non-bold font as the rest of the GUI. Temperature
    channels are fed by apin.0.rawval/apin.0.mask, same source
    InputsCanvas/EffectsCanvas already poll/register for their own purposes
    (see InputsCanvas's docstring); FFB Strength is fed by vesc.0.torque,
    which EffectsCanvas's strip chart also listens for (see that class's
    _force_torque_cb) - in
    both cases this class registers its own listener for the same
    broadcast rather than requesting it again, except for vesc.0.torque's
    actual get(), which this class now owns (was EffectsCanvas's job
    before the value display moved here)."""

    VOLTAGE_POLL_INTERVAL_S = 0.2  # supply voltage changes slowly - poll far less often than apin.0.rawval/vesc.0.torque

    # Each of the 5 modules (VCC, L1, L2, L3, FFB) is place()d at its own
    # explicit X/Y/WIDTH_PX from Placement.py (P.READOUTBAR_*) instead of
    # pack()ed left-to-right - per user request, so any module can be
    # freely repositioned just by editing its X/Y there. This frame's own
    # size (P.READOUTBAR_WIDTH_PX/HEIGHT_PX, passed to __init__ below) must
    # stay set explicitly for the same reason: place()d children never
    # propagate their size up to the parent the way pack()/grid() children
    # do. Maps each temp channel's L-number (1/2/3) to its own X/Y/WIDTH_PX
    # constants.
    _TEMP_XYW = {
        1: (P.READOUTBAR_L1_X, P.READOUTBAR_L1_Y, P.READOUTBAR_L1_WIDTH_PX),
        2: (P.READOUTBAR_L2_X, P.READOUTBAR_L2_Y, P.READOUTBAR_L2_WIDTH_PX),
        3: (P.READOUTBAR_L3_X, P.READOUTBAR_L3_Y, P.READOUTBAR_L3_WIDTH_PX),
    }

    def __init__(self, parent, link, **kwargs):
        kwargs.setdefault("width", P.READOUTBAR_WIDTH_PX)
        kwargs.setdefault("height", P.READOUTBAR_HEIGHT_PX)
        super().__init__(parent, **kwargs)
        self.link = link
        self._last_voltage_poll = 0.0
        self.temp_channels = {}  # pin_index -> {"index", "prefix", "label"}

        # Plain tk.Label (not ttk.Label) for all 5 modules - voltage_label
        # and the 3 temp labels need a per-instance background color for
        # the low-voltage/overtemperature warnings (this class's
        # _voltage_cb, App._apply_bg_stage), and ttk.Label's background
        # under Windows' native "vista" theme doesn't reliably respond to
        # per-widget style overrides (same recurring issue as
        # Black.TCheckbutton/DegreeButton.TButton elsewhere in this file)
        # - tk.Label's own bg= always works directly, no style plumbing
        # needed. force_label has no such warning and used to be a plain
        # ttk.Label - switched to tk.Label too (per user finding) since
        # ttk.Label's theme reserves slightly different internal padding
        # than tk.Label, which under the old pack() layout was invisible
        # (pack() aligned every item to the same row regardless) but
        # showed up as a visible few-px vertical offset once each module
        # got its own place()d y= box sized to its own natural height -
        # matching widget types keeps all 5 boxes the same height.
        self._default_bg = ttk.Style().lookup("TFrame", "background")

        # anchor="w" keeps each label's text left-aligned within its fixed
        # WIDTH_PX column (place()'s own default would otherwise center it,
        # visibly shifting as the live value's text length changes).
        self.voltage_label = tk.Label(self, text="VCC: --.- V", bg=self._default_bg, anchor="w")
        self.voltage_label.place(
            x=P.READOUTBAR_VCC_X, y=P.READOUTBAR_VCC_Y, width=P.READOUTBAR_VCC_WIDTH_PX,
        )

        for i, pin_index in enumerate(TEMP_PIN_INDICES):
            prefix = f"L{i + 1}"
            x, y, w = self._TEMP_XYW[i + 1]
            label = tk.Label(self, text=f"{prefix}: --.- °C", bg=self._default_bg, anchor="w")
            label.place(x=x, y=y, width=w)
            self.temp_channels[pin_index] = {"index": None, "prefix": prefix, "label": label}

        self.force_label = tk.Label(self, text="FFB: -- %", bg=self._default_bg, anchor="w")
        self.force_label.place(
            x=P.READOUTBAR_FFB_X, y=P.READOUTBAR_FFB_Y, width=P.READOUTBAR_FFB_WIDTH_PX,
        )

    def on_connected(self):
        self.link.register("vesc", "voltage", self._voltage_cb, instance=0, typechar="?")
        self.link.register("apin", "rawval", self._rawvalues_cb, instance=0, typechar="?")
        self.link.request_once("apin", "mask", self._mask_cb, instance=0)
        self.link.register("vesc", "torque", self._force_cb, instance=0, typechar="?")

    def poll(self):
        now = time.monotonic()
        if now - self._last_voltage_poll >= self.VOLTAGE_POLL_INTERVAL_S:
            self._last_voltage_poll = now
            self.link.send_get("vesc", "voltage", instance=0)
        self.link.send_get("vesc", "torque", instance=0)

    def _voltage_cb(self, reply):
        try:
            raw_mv = int(reply)
        except ValueError:
            return
        voltage = raw_mv / 1000.0
        # Plain threshold on this already-polled reading, per user request
        # - no firmware "stage"/debounce like the temperature warning above
        # needs, and no extra polling loop (VOLTAGE_POLL_INTERVAL_S already
        # covers this).
        color = VOLTAGE_LOW_COLOR if voltage < VOLTAGE_LOW_THRESHOLD_V else self._default_bg
        self.voltage_label.configure(text=f"VCC: {voltage:.1f} V", bg=color)

    def _force_cb(self, reply):
        try:
            raw = int(reply)
        except ValueError:
            return
        self.force_label.configure(text=f"FFB: {raw / 100.0:+.0f} %")

    def _mask_cb(self, reply):
        try:
            mask = int(reply.strip())
        except ValueError:
            return
        for pin_index, chan in self.temp_channels.items():
            if mask & (1 << pin_index):
                chan["index"] = bin(mask & ((1 << pin_index) - 1)).count("1")
            else:
                chan["index"] = None
                chan["label"].configure(text=f"{chan['prefix']}: -- °C")

    def _rawvalues_cb(self, reply):
        parts = [p for p in reply.split("\n") if p.strip() != ""]
        for chan in self.temp_channels.values():
            idx = chan["index"]
            if idx is None or len(parts) <= idx:
                continue
            try:
                vtemp = int(parts[idx])
            except ValueError:
                continue
            temp_c = ntc_raw_to_celsius(vtemp)
            text = f"{temp_c:.1f} °C" if temp_c is not None else "-- °C"
            chan["label"].configure(text=f"{chan['prefix']}: {text}")


class ResponseCurveChart(tk.Canvas):
    """Static torque-response curve (metric on X, torque/output on Y) with
    an optional live crosshair marker - the Tkinter equivalent of the
    reference Configurator's per-effect QtCharts graph
    (effects_tuning_ui.py) and Expo preview graph (expo_ui.py), redrawn from
    a locally computed curve instead of a live chart library. Same
    create_line-based drawing style as RangeSlider/HSlider.

    Axis gridlines/tick labels/axis titles (matching the reference's
    QValueAxis rendering) are opt-in via set_axis() - without it, the chart
    draws just the plain curve+zero-line+marker. All 5 Advanced-tab graphs
    call set_axis() now (see FxTuningPanel), so this fallback is currently
    unused in practice, kept for any future chart that doesn't need axes."""

    MARGIN_LEFT = 46   # reserved for the y-axis title + tick labels, only used once set_axis() is called
    MARGIN_BOTTOM = 28  # reserved for the x-axis title + tick labels
    MARGIN_TOP = 4
    MARGIN_RIGHT = 16  # the rightmost x-tick label (e.g. "100.0") is centered on its gridline, so needs room for half its width past the last tick position

    def __init__(self, parent, x_min, x_max, y_min, y_max, color="#000000", width=None, height=None, **kwargs):
        kwargs.setdefault("bg", P.ADVANCED_CHART_BG)
        kwargs.setdefault("highlightthickness", 0)
        width = P.ADVANCED_CHART_WIDTH if width is None else width
        height = P.ADVANCED_CHART_HEIGHT if height is None else height
        super().__init__(parent, width=width, height=height, **kwargs)
        self.x_min, self.x_max = x_min, x_max
        self.y_min, self.y_max = y_min, y_max
        self.color = color
        self.points = []
        self.marker_x = None
        self.marker_item = None
        self.x_formatter = None
        self.y_formatter = None
        self.x_axis_title = None
        self.y_axis_title = None
        self.num_ticks = 5
        self.bind("<Configure>", lambda e: self._redraw_static())

    def set_axis(self, x_formatter=None, y_formatter=None, x_axis_title=None, y_axis_title=None, num_ticks=5):
        """Turn on gridlines + tick labels + axis titles, matching the
        reference's QValueAxis rendering (res/effects_tuning.ui's
        graph_spring etc.) - x_formatter/y_formatter take a data-space tick
        value and return its label text (e.g. Spring's X converts raw
        curpos to the same "-100..100 (%)" the reference shows, a 1:1
        linear relabeling of the same ±32767 range - see main chat history
        for why that's safe here specifically)."""
        self.x_formatter = x_formatter
        self.y_formatter = y_formatter
        self.x_axis_title = x_axis_title
        self.y_axis_title = y_axis_title
        self.num_ticks = num_ticks
        self._redraw_static()

    def _margins(self):
        if self.x_formatter is None and self.y_formatter is None:
            return 0, 0, 0, 0
        return self.MARGIN_LEFT, self.MARGIN_TOP, self.MARGIN_RIGHT, self.MARGIN_BOTTOM

    def _to_px(self, x, y):
        w = max(1, self.winfo_width())
        h = max(1, self.winfo_height())
        left, top, right, bottom = self._margins()
        plot_w = max(1, w - left - right)
        plot_h = max(1, h - top - bottom)
        px = left + (x - self.x_min) / (self.x_max - self.x_min) * plot_w
        py = top + plot_h - (y - self.y_min) / (self.y_max - self.y_min) * plot_h
        return px, py

    def set_curve(self, points):
        """points: list of (x, y) tuples in data space."""
        self.points = points
        self._redraw_static()

    def set_marker(self, x_value):
        self.marker_x = x_value
        self._redraw_marker()

    def _tick_values(self, vmin, vmax):
        return [vmin + (vmax - vmin) * i / (self.num_ticks - 1) for i in range(self.num_ticks)]

    def _redraw_static(self):
        self.delete("all")
        self.marker_item = None
        w = max(1, self.winfo_width())
        h = max(1, self.winfo_height())
        left, top, right, bottom = self._margins()
        plot_x0, plot_y0 = left, top
        plot_x1, plot_y1 = w - right, h - bottom

        if self.x_formatter is not None:
            for xv in self._tick_values(self.x_min, self.x_max):
                px, _ = self._to_px(xv, self.y_min)
                self.create_line(px, plot_y0, px, plot_y1, fill="#dcdcdc")
                self.create_text(px, plot_y1 + 2, text=self.x_formatter(xv), anchor="n", font=("TkDefaultFont", 7))
            if self.x_axis_title:
                self.create_text(
                    (plot_x0 + plot_x1) / 2, h - 2, text=self.x_axis_title, anchor="s", font=("TkDefaultFont", 7)
                )
        if self.y_formatter is not None:
            for yv in self._tick_values(self.y_min, self.y_max):
                _, py = self._to_px(self.x_min, yv)
                self.create_line(plot_x0, py, plot_x1, py, fill="#dcdcdc")
                self.create_text(plot_x0 - 3, py, text=self.y_formatter(yv), anchor="e", font=("TkDefaultFont", 7))
            if self.y_axis_title:
                self.create_text(
                    8, (plot_y0 + plot_y1) / 2, text=self.y_axis_title, anchor="center",
                    angle=90, font=("TkDefaultFont", 7),
                )

        if self.x_min < 0 < self.x_max:
            zx, _ = self._to_px(0, self.y_min)
            self.create_line(zx, plot_y0, zx, plot_y1, fill="#a0a0a0")
        if self.y_min < 0 < self.y_max:
            _, zy = self._to_px(self.x_min, 0)
            self.create_line(plot_x0, zy, plot_x1, zy, fill="#a0a0a0")
        if len(self.points) >= 2:
            coords = []
            for x, y in self.points:
                px, py = self._to_px(x, y)
                coords.extend((px, py))
            self.create_line(*coords, fill=self.color, width=1.5)
        self._redraw_marker()

    def _redraw_marker(self):
        """Move/create only the marker line, without touching gridlines,
        tick labels or the curve - called on every set_marker() (the 30ms
        poll hot path, see FxTuningPanel._on_metric_reply), so it must stay
        cheap. _redraw_static() resets marker_item to None (delete("all")
        already destroyed the old item) before calling this once itself, so
        a static redraw still ends up with a marker drawn."""
        left, top, right, bottom = self._margins()
        plot_y0, plot_y1 = top, max(1, self.winfo_height()) - bottom
        if self.marker_x is None or not (self.x_min <= self.marker_x <= self.x_max):
            if self.marker_item is not None:
                self.delete(self.marker_item)
                self.marker_item = None
            return
        mx, _ = self._to_px(self.marker_x, self.y_min)
        if self.marker_item is None:
            self.marker_item = self.create_line(mx, plot_y0, mx, plot_y1, fill="#888888", width=1)
        else:
            self.coords(self.marker_item, mx, plot_y0, mx, plot_y1)


class FxTuningPanel(PlacedGroup):
    """No longer its own bordered "Effect response curves" LabelFrame
    (removed per user request, see PlacedGroup) - this class is now a
    plain builder that places its children directly onto the Advanced page
    (AdvancedTuningTab), same place()-positioned pattern as
    InputsCanvas/EffectsCanvas on the Main page.

    5 response-curve graphs plus the Freq/Q biquad filter fields, the
    Friction-only "Smooth" ramp-up slider, the Expo exponent slider, and the
    shared filter-profile (Default/Custom) selector - the Tkinter
    equivalent of the reference Configurator's "Advanced ffb tuning" dialog
    (effects_tuning_ui.py) merged with its "Torque curve..."/Expo dialog
    (expo_ui.py) into one panel (per user request - both dialogs show
    response curves and the user wanted all 5 kept together).

    6 cards total: Spring/Inertia/Damper/Friction response curves, Expo
    (own domain/formula, not a filter effect), and the Effect filter
    profile card (label, combo - matching effects_tuning.ui's QFrame
    "frame", minus its "Restore Default" button, removed per user request
    since a dedicated "Defaults.twisty" Save/Load profile supersedes it -
    plus Save/Load buttons). Each card is independently positioned via its
    own ADVANCED_CARD_*_X/_Y (or ADVANCED_PROFILE_FRAME_X/_Y) in
    Placement.py, per user request, rather than a shared row/column grid -
    every widget inside a card is placed at a fixed DY/DX offset from that
    same card origin (see ADVANCED_CARD_*_DY/ADVANCED_FX_*_DX), so moving a
    card's X/Y moves its title, border and contents together as one block.
    Each cell's internal element order is copied from effects_tuning.ui's
    per-group gridLayout: Graph -> Gain slider -> [Smooth, Friction only]
    -> [Freq/Q, all but Spring]. Expo's own cell copies expo.ui's order:
    Graph -> Slider -> Exponent value + "Reset to 1 (Off)" button. The
    profile card's "Read metrics on axis" axis-selector is intentionally
    left out, since Twisty is hardcoded single-axis everywhere else in
    this GUI (no other panel has an axis picker either).

    Gain sliders are real and editable here (like the reference), same as
    the Main tab's EffectsCanvas sliders for the same fx.<effect> value -
    both are kept in sync via a direct Python-side mirror, each side's
    _send_fx() sender updating other_gain_sliders[cmd].set_from_firmware()
    on the other tab (see EffectsCanvas.other_gain_sliders' own comment),
    so dragging either one updates the other. An earlier version tried to
    do this via the firmware's own "=" SET echo/a shared typechar=None
    listener instead - that never actually worked, since the firmware
    acknowledges a SET with a plain "OK", not the value.

    Curve math (force = f(metric)) is ported 1:1 from the reference's
    calc_condition_effect_force/calc_friction_effect_force
    (effects_tuning_ui.py:417-492) and expo_ui.py's calcExpo (:138-142).
    Freq/Q only shape the *dynamic* (temporal) filtering, not this static
    curve, so they are not part of the redraw trigger - only Gain (all
    four) and Smooth (Friction) are, matching the reference's own
    slider_changed()/filter_changed() split.

    The curve's X-domain is plotted directly in the same raw units as the
    live metric (axis.curpos/curspd/curaccel) rather than converted to
    percent/rpm like the reference's axis labels - same curve shape and
    saturation point either way, but avoids silently mislabeling if a
    conversion factor were ever wrong.
    """

    GAIN_CMDS = ("spring", "damper", "friction", "inertia")

    DOMAINS = {
        "spring": (-32767, 32767, "curpos"),
        "damper": (-1800, 1800, "curspd"),
        "friction": (-720, 720, "curspd"),
        "inertia": (-30000, 30000, "curaccel"),
    }
    TITLES = {
        "spring": "Spring (position effect)",
        "damper": "Damper (speed effect)",
        "friction": "Friction (speed effect)",
        "inertia": "Inertia (acceleration effect)",
    }
    # X-axis title per effect - each domain's raw range (DOMAINS above) is
    # shown as -100..100% of its own chart's own scale (per user decision),
    # same 1:1 relabeling approach as Spring's "wheel range (%)".
    X_AXIS_TITLES = {
        "spring": "wheel range (%)",
        "damper": "wheel speed (%)",
        "friction": "wheel speed (%)",
        "inertia": "wheel acceleration (%)",
    }
    COLORS = {
        "spring": "#0d5b73", "damper": "#1a7a1a", "friction": "#1a7a1a", "inertia": "#a3169e",
    }
    CURVE_POINTS = 60

    def __init__(self, parent, link, axis_instance=0, base_x=0, base_y=0):
        self._init_group(parent, base_x, base_y)
        self.link = link
        self.instance = axis_instance
        self.gains = {cmd: 0 for cmd in self.GAIN_CMDS}
        self.smooth_pct = 0
        self.metrics = {"curpos": 0, "curspd": 0, "curaccel": 0}
        # Set by App._build_ui() once both this panel and the Main tab's
        # EffectsCanvas exist - see EffectsCanvas.other_gain_sliders' own
        # comment for why this is a direct Python-side mirror rather than
        # relying on the firmware's "=" SET echo (which is just "OK", not
        # the value).
        self.other_gain_sliders = None
        # Same idea, for the single Expo slider (own LabeledSlider each
        # side, not part of gain_sliders) - set to EffectsCanvas.expo_slider.
        self.other_expo_slider = None
        self.charts = {}
        self.gain_sliders = {}
        self.freq_vars = {}
        self.q_vars = {}
        self._freq_entries = {}
        self._q_entries = {}

        # (card_x, card_y, card_width, card_height) - each card's own fully
        # independent border box, see Placement.py's
        # ADVANCED_CARD_<NAME>_X/_Y/_WIDTH/_HEIGHT.
        card_origins = {
            "spring": (P.ADVANCED_CARD_SPRING_X, P.ADVANCED_CARD_SPRING_Y, P.ADVANCED_CARD_SPRING_WIDTH, P.ADVANCED_CARD_SPRING_HEIGHT),
            "inertia": (P.ADVANCED_CARD_INERTIA_X, P.ADVANCED_CARD_INERTIA_Y, P.ADVANCED_CARD_INERTIA_WIDTH, P.ADVANCED_CARD_INERTIA_HEIGHT),
            "damper": (P.ADVANCED_CARD_DAMPER_X, P.ADVANCED_CARD_DAMPER_Y, P.ADVANCED_CARD_DAMPER_WIDTH, P.ADVANCED_CARD_DAMPER_HEIGHT),
            "friction": (P.ADVANCED_CARD_FRICTION_X, P.ADVANCED_CARD_FRICTION_Y, P.ADVANCED_CARD_FRICTION_WIDTH, P.ADVANCED_CARD_FRICTION_HEIGHT),
        }

        for cmd, (card_x, card_y, card_width, card_height) in card_origins.items():
            x_min, x_max, _ = self.DOMAINS[cmd]
            title_y = card_y - P.ADVANCED_CARD_TITLE_TO_BORDER_DY
            self._place(ttk.Label(parent, text=self.TITLES[cmd]), card_x, title_y)

            # Border created first so it stacks behind the chart/slider/etc.
            # placed on top of it afterward (same parent, place()'s stacking
            # order follows creation order). bg is the same dynamic ttk
            # lookup EffectsCanvas's force chart uses (not a fixed hex) so
            # the thin strip of border visible around the contents matches
            # the ordinary GUI background exactly, whatever theme is active.
            self._place(
                tk.Frame(
                    parent, bg=ttk.Style().lookup("TFrame", "background"),
                    relief=P.ADVANCED_CARD_RELIEF, bd=P.ADVANCED_CARD_BORDERWIDTH,
                ),
                card_x, card_y, width=card_width, height=card_height,
            )
            # Inset from the border's left edge by CARD_PADDING too (the
            # *_DY offsets below already bake in the vertical padding) -
            # without this, the contents would touch the border's left edge
            # even though top/bottom don't.
            content_x = card_x + P.ADVANCED_CARD_PADDING

            chart = ResponseCurveChart(
                parent, x_min, x_max, -32767, 32767, color=self.COLORS[cmd],
                width=P.ADVANCED_CARD_CHART_WIDTH, height=P.ADVANCED_CARD_CHART_HEIGHT,
            )
            self._place(chart, content_x, card_y + P.ADVANCED_CARD_CHART_DY)
            self.charts[cmd] = chart

            # Narrow label column for "Gain" (short text) - overrides the
            # shared SLIDER_LABEL_W to pull entry+slider much closer to the
            # label, and narrows the slider itself to fit inside the card.
            gain_slider = LabeledSlider(
                parent, "Gain", 0, 255, self._send_fx(cmd),
                percent_max=256, percent_offset=1, percent_scale=EffectsCanvas.GAIN_SCALER[cmd],
                width=P.ADVANCED_CARD_CHART_WIDTH, label_width=P.ADVANCED_CARD_LABEL_W,
            )
            self._place(gain_slider, content_x, card_y + P.ADVANCED_CARD_GAIN_DY)
            self.gain_sliders[cmd] = gain_slider

            # Freq/Q and Smooth rows: Spring has neither; Inertia/Damper get
            # a Freq/Q row right after Gain; Friction gets Smooth in that
            # same slot, then its own Freq/Q row below that (per the
            # reference's row order).
            if cmd == "friction":
                self.smooth_slider = LabeledSlider(
                    parent, "Smooth", 0, 100, self._send_fx("frictionPctSpeedToRampup"), unit="%",
                    width=P.ADVANCED_CARD_CHART_WIDTH, label_width=P.ADVANCED_CARD_LABEL_W,
                )
                self._place(self.smooth_slider, content_x, card_y + P.ADVANCED_CARD_FRICTION_SMOOTH_DY)
                self._build_freq_q_row(cmd, content_x, card_y + P.ADVANCED_CARD_FRICTION_FREQ_DY)
            elif cmd in ("inertia", "damper"):
                self._build_freq_q_row(cmd, content_x, card_y + P.ADVANCED_CARD_FREQ_DY)

        # Gridlines/tick labels/axis titles - rolled out from the Spring
        # prototype to all 4 cells here (Expo, built separately below, gets
        # its own axis setup the same way). Every X is its own raw metric
        # (curpos/curspd/curaccel) relabeled to "-100..100 (%)" of that
        # chart's own DOMAINS range - a linear rescale of each chart's own
        # ±x_max, not a guess at a real-world unit conversion (per user
        # decision). Y is always torque, shared ±32767 range on all 4.
        for cmd in self.GAIN_CMDS:
            _, x_max, _ = self.DOMAINS[cmd]
            self.charts[cmd].set_axis(
                x_formatter=lambda v, xmax=x_max: f"{v / xmax * 100:.1f}",
                y_formatter=lambda v: f"{v:.1f}",
                x_axis_title=self.X_AXIS_TITLES[cmd],
                y_axis_title="torque",
            )

        # Expo card - not a filter effect, own domain/formula; a separate
        # dialog in the reference (expo.ui), merged in here per user
        # request. Internal order copied from that file: Graph -> Slider ->
        # Exponent value + "Reset to 1 (Off)" button. Same bordered "card"
        # as Spring/Inertia/Damper/Friction, independently sized/positioned
        # at ADVANCED_CARD_EXPO_X/_Y/_WIDTH/_HEIGHT.
        expo_card_x, expo_card_y = P.ADVANCED_CARD_EXPO_X, P.ADVANCED_CARD_EXPO_Y
        self._place(
            ttk.Label(parent, text="Exponential"),
            expo_card_x, expo_card_y - P.ADVANCED_CARD_TITLE_TO_BORDER_DY,
        )
        self._place(
            tk.Frame(
                parent, bg=ttk.Style().lookup("TFrame", "background"),
                relief=P.ADVANCED_CARD_RELIEF, bd=P.ADVANCED_CARD_BORDERWIDTH,
            ),
            expo_card_x, expo_card_y,
            width=P.ADVANCED_CARD_EXPO_WIDTH, height=P.ADVANCED_CARD_EXPO_HEIGHT,
        )
        expo_content_x = expo_card_x + P.ADVANCED_CARD_PADDING

        self.expo_chart = ResponseCurveChart(
            parent, -1.0, 1.0, -1.0, 1.0, color="#0d5b73",
            width=P.ADVANCED_CARD_CHART_WIDTH, height=P.ADVANCED_CARD_CHART_HEIGHT,
        )
        self._place(self.expo_chart, expo_content_x, expo_card_y + P.ADVANCED_CARD_CHART_DY)
        # Both axes are already the dimensionless -1.0..1.0 curve domain
        # itself (normalized wheel position in, normalized force scale
        # out) - shown as raw values with generic titles per user decision,
        # unlike the other 4 charts' "-100..100 (%)" relabeling.
        self.expo_chart.set_axis(
            x_formatter=lambda v: f"{v:.1f}",
            y_formatter=lambda v: f"{v:.1f}",
            x_axis_title="input",
            y_axis_title="output",
        )
        self.exposcale = 1
        # label_width overridden to 66 (measured "Exponential" at 61px,
        # +5px margin) instead of the shared ADVANCED_CARD_LABEL_W (47px,
        # sized for "Gain"/"Smooth") - this card is only 260px wide total,
        # so the slider's own track shrinks a bit to 138px (260-66-44-12)
        # to make room, vs. this card's usual ~157px track - a much
        # smaller compromise than the earlier, much longer "Minforce
        # Scale ( 1=off )" name needed (which cut the track to just 74px).
        self.expo_slider = LabeledSlider(
            parent, "Exponential", -127, 127, self._send_expo(),
            width=P.ADVANCED_CARD_CHART_WIDTH, label_width=66,
        )
        self._place(self.expo_slider, expo_content_x, expo_card_y + P.ADVANCED_CARD_GAIN_DY)

        expo_row_y = expo_card_y + P.ADVANCED_CARD_FREQ_DY
        self._place(
            ttk.Label(parent, text="Exponent"),
            expo_content_x + P.ADVANCED_FX_EXPO_EXPONENT_LABEL_DX, expo_row_y, anchor="w",
        )
        self.expo_value_label = ttk.Label(parent, text="1.00")
        self._place(
            self.expo_value_label,
            expo_content_x + P.ADVANCED_FX_EXPO_EXPONENT_VALUE_DX, expo_row_y, anchor="w",
        )
        self._place(
            ttk.Button(parent, text="Reset to 0 (Off)", command=self._on_expo_reset),
            expo_content_x + P.ADVANCED_FX_EXPO_RESET_BUTTON_DX, expo_row_y, anchor="w",
        )

        # Effect filter profile card - its own bordered card (per user
        # request), independently positioned/sized at
        # ADVANCED_PROFILE_FRAME_X/_Y/_WIDTH/_HEIGHT, title "Effect Filter
        # Profile" above the border exactly like the 5 response-curve cards
        # (e.g. "Exponential"/"Spring (position effect)"). Interior, top to
        # bottom: a read-only glossary table explaining the recurring
        # Exponential/Gain/Freq/Q/Smooth terms, then a "Select Profile"
        # label + Default/Custom dropdown row, then Save/Load (own X/Y, see
        # ADVANCED_PROFILE_SAVE_X/_LOAD_X/_SAVE_LOAD_Y below). "Restore
        # Default" button not present - superseded by loading a dedicated
        # "Defaults.twisty" profile instead (see
        # EffectsCanvas.SAVE_LOAD_FIELDS).
        profile_card_x, profile_card_y = P.ADVANCED_PROFILE_FRAME_X, P.ADVANCED_PROFILE_FRAME_Y
        self._place(
            ttk.Label(parent, text="Effect Filter Profile"),
            profile_card_x, profile_card_y - P.ADVANCED_CARD_TITLE_TO_BORDER_DY,
        )
        self._place(
            tk.Frame(
                parent, bg=ttk.Style().lookup("TFrame", "background"),
                relief=P.ADVANCED_CARD_RELIEF, bd=P.ADVANCED_CARD_BORDERWIDTH,
            ),
            profile_card_x, profile_card_y,
            width=P.ADVANCED_PROFILE_FRAME_WIDTH, height=P.ADVANCED_PROFILE_FRAME_HEIGHT,
        )

        # Glossary text - a single read-only tk.Text (state="disabled"),
        # not a table anymore (per user request - dropped the column
        # alignment/monospace look, plain flowing "Term: Explanation"
        # lines read better). Font is "TkDefaultFont" - the same named
        # font every ttk.Label/Button in this GUI already uses without an
        # explicit font= override, so this text matches the rest of the
        # interface exactly instead of its own style. A row is a 1-tuple
        # for a plain heading line (e.g. "Custom Profile:") or a 2-tuple
        # for a term/explanation pair; a blank line separates every entry
        # (per user request, kept from the earlier table version).
        glossary_rows = [
            ("Exponential", "How progressive steering feels"),
            ("Gain", "Overall strength of the effect"),
            ("Freq", "Filter cutoff frequency (Hz)"),
            ("Q", "Filter sharpness / resonance"),
            ("Smooth", "How gently friction ramps in"),
        ]
        glossary_lines = [
            row[0] if len(row) == 1 else f"{row[0]}: {row[1]}"
            for row in glossary_rows
        ]
        glossary_text = "\n\n".join(glossary_lines)
        # bg matches the ordinary window background exactly, whatever
        # theme is active - same live ttk.Style() lookup as the card
        # border Frames use, not a fixed hex (per user request: the table
        # should blend into the GUI background, not stand out as white).
        self.profile_table = tk.Text(
            parent, font="TkDefaultFont",
            bg=ttk.Style().lookup("TFrame", "background"), relief="flat", bd=0, wrap="word",
            cursor="arrow", highlightthickness=0,
        )
        self.profile_table.insert("1.0", glossary_text)
        self.profile_table.configure(state="disabled")
        self._place(
            self.profile_table, P.ADVANCED_PROFILE_TABLE_X, P.ADVANCED_PROFILE_TABLE_Y,
            width=P.ADVANCED_PROFILE_TABLE_WIDTH, height=P.ADVANCED_PROFILE_TABLE_HEIGHT,
        )

        # Default/Custom segmented toggle (two ttk.Radiobuttons sharing one
        # StringVar) - replaces the dropdown per user request: no popup to
        # clash with the buttons below, sits right above Save/Load in the
        # same two columns (ADVANCED_PROFILE_SAVE_X/_LOAD_X) for a clean
        # stacked look, and frees up the vertical space a dropdown + its
        # clearance margin needed, which now goes to the glossary table
        # instead. No separate "Select Profile" caption - the two buttons'
        # own text is self-explanatory, same as the Main tab's single
        # "Invert" toggle needing no extra label.
        #
        # Style borrows the same "clam" Button.border trick as
        # InvertToggle.TCheckbutton above (see that style's own comment for
        # why - the "vista" theme otherwise only paints a button border/bg
        # on hover, not at rest) - applied to TRadiobutton here instead of
        # TCheckbutton, one shared style so both segments look identical
        # except for selected/!selected state.
        style = ttk.Style()
        style.element_create("ProfileToggle.border", "from", "clam", "Button.border")
        style.layout("ProfileToggle.TRadiobutton", [
            ("ProfileToggle.border", {"sticky": "nswe", "border": "1", "children": [
                ("Radiobutton.padding", {"sticky": "nswe", "children": [
                    ("Radiobutton.label", {"sticky": "nswe"}),
                ]}),
            ]}),
        ])
        style.configure(
            "ProfileToggle.TRadiobutton", anchor="center", borderwidth=P.BUTTON_BORDERWIDTH,
            bordercolor=P.BUTTON_BORDER_COLOR,
            lightcolor=P.BUTTON_SHADOW_LIGHT_COLOR, darkcolor=P.BUTTON_SHADOW_DARK_COLOR,
        )
        style.map(
            "ProfileToggle.TRadiobutton",
            background=[("selected", P.BUTTON_PRESSED_COLOR), ("!selected", P.BUTTON_BG_COLOR)],
            relief=[("selected", P.BUTTON_RELIEF_PRESSED), ("!selected", P.BUTTON_RELIEF)],
        )
        # width= here is place()'s own pixel override (ADVANCED_PROFILE_
        # TOGGLE_WIDTH_PX), not the ttk char-count width every other button
        # uses - see that constant's comment for why (a plain char-count
        # match still left this pair 2px wider than Save/Load).
        self.profile_var = tk.StringVar(value="Default")
        self._place(
            ttk.Radiobutton(
                parent, text="Default", variable=self.profile_var, value="Default",
                command=self._on_profile_change, style="ProfileToggle.TRadiobutton",
            ),
            P.ADVANCED_PROFILE_DEFAULT_X, P.ADVANCED_PROFILE_TOGGLE_Y,
            width=P.ADVANCED_PROFILE_TOGGLE_WIDTH_PX, height=P.ADVANCED_PROFILE_TOGGLE_HEIGHT,
        )
        self._place(
            ttk.Radiobutton(
                parent, text="Custom", variable=self.profile_var, value="Custom",
                command=self._on_profile_change, style="ProfileToggle.TRadiobutton",
            ),
            P.ADVANCED_PROFILE_CUSTOM_X, P.ADVANCED_PROFILE_TOGGLE_Y,
            width=P.ADVANCED_PROFILE_TOGGLE_WIDTH_PX, height=P.ADVANCED_PROFILE_TOGGLE_HEIGHT,
        )

        # Save/Load buttons, per user request - a copy of the Main tab's
        # pair, in the card's now-empty 3/4 position (where "Restore
        # Default" used to sit). Same style as the Main tab's for visual
        # consistency; the actual logic lives on EffectsCanvas (it already
        # reaches into this panel via self.fx_panel for the Freq/Q/profile
        # fields) - self.effects_canvas here is the reverse reference,
        # wired once in App._build_ui() alongside the others.
        # Default (top-left) anchor + the same explicit height as the Main
        # tab's own Save/Load pair (EFFECTS_INVERT_ROW_HEIGHT) - per user
        # request, so that identical absolute X/Y (see
        # ADVANCED_PROFILE_SAVE_X/_LOAD_X/_SAVE_LOAD_Y) reproduces the exact
        # same on-screen rectangle as the Main tab's pair, not just a
        # matching center point.
        self.effects_canvas = None
        self._place(
            ttk.Button(
                parent, text="Save", command=lambda: self.effects_canvas._on_save_profile(),
                style="DegreeButton.TButton", width=P.BUTTON_WIDTH_CHARS,
            ),
            P.ADVANCED_PROFILE_SAVE_X, P.ADVANCED_PROFILE_SAVE_LOAD_Y, height=P.EFFECTS_INVERT_ROW_HEIGHT,
        )
        self._place(
            ttk.Button(
                parent, text="Load", command=lambda: self.effects_canvas._on_load_profile(),
                style="DegreeButton.TButton", width=P.BUTTON_WIDTH_CHARS,
            ),
            P.ADVANCED_PROFILE_LOAD_X, P.ADVANCED_PROFILE_SAVE_LOAD_Y, height=P.EFFECTS_INVERT_ROW_HEIGHT,
        )

        for cmd in ("damper", "friction", "inertia"):
            self._update_freq_q_enabled(cmd)
        for cmd in self.GAIN_CMDS:
            self._redraw_curve(cmd)
        self._redraw_expo()

    def _build_freq_q_row(self, cmd, col_x, freq_y):
        parent = self.parent
        freq_var = tk.StringVar(value="0")
        q_var = tk.StringVar(value="0.00")
        self.freq_vars[cmd] = freq_var
        self.q_vars[cmd] = q_var

        self._place(ttk.Label(parent, text="Freq"), col_x + P.ADVANCED_FX_FREQ_LABEL_DX, freq_y, anchor="w")
        freq_entry = ttk.Spinbox(
            parent, textvariable=freq_var, from_=1, to=2000, width=6,
            command=lambda c=cmd: self._on_freq_apply(c),
        )
        self._place(freq_entry, col_x + P.ADVANCED_FX_FREQ_SPIN_DX, freq_y, anchor="w")
        freq_entry.bind("<Return>", lambda e, c=cmd: self._on_freq_apply(c))
        freq_entry.bind("<FocusOut>", lambda e, c=cmd: self._on_freq_apply(c))
        self._freq_entries[cmd] = freq_entry

        self._place(ttk.Label(parent, text="Q"), col_x + P.ADVANCED_FX_Q_LABEL_DX, freq_y, anchor="w")
        q_entry = ttk.Spinbox(
            parent, textvariable=q_var, from_=0.10, to=10.00, increment=0.01, width=6,
            command=lambda c=cmd: self._on_q_apply(c),
        )
        self._place(q_entry, col_x + P.ADVANCED_FX_Q_SPIN_DX, freq_y, anchor="w")
        q_entry.bind("<Return>", lambda e, c=cmd: self._on_q_apply(c))
        q_entry.bind("<FocusOut>", lambda e, c=cmd: self._on_q_apply(c))
        self._q_entries[cmd] = q_entry

    # ---------------------------------------------------------------- send
    def _send_fx(self, cmd):
        def sender(val):
            if self.link.connected:
                self.link.set_value("fx", cmd, int(val), instance=0)
            # Local, immediate redraw for responsiveness.
            if cmd in self.gains:
                self.gains[cmd] = int(val)
                self._redraw_curve(cmd)
                # Direct Python-side mirror of the Main tab's copy of this
                # same gain slider - NOT the firmware's "=" SET echo (that
                # old assumption was wrong: the firmware acknowledges a
                # SET with a plain "OK", never the value, so a listener on
                # that echo could never actually learn the new value - see
                # other_gain_sliders' own comment in __init__).
                # set_from_firmware() only redraws, it never re-sends or
                # re-triggers this sender, so this can't loop between tabs.
                if self.other_gain_sliders is not None:
                    self.other_gain_sliders[cmd].set_from_firmware(val)
            elif cmd == "frictionPctSpeedToRampup":
                self.smooth_pct = int(val)
                self._redraw_curve("friction")
        return sender

    def _send_expo(self):
        """Only ever used for the "expo" axis command in this class (this
        panel has no other bare axis.<cmd> slider) - renamed from the
        previous generic-looking "_send_axis(cmd)" to make that explicit.
        Redraws the curve directly (not waiting for the firmware's echo -
        that's just "OK" for a SET, never the value, same root cause as
        the Gain sliders' cross-tab sync bug) and mirrors the new value to
        the Main tab's own Expo slider, same principle as _send_fx()'s
        other_gain_sliders mirror above."""
        def sender(val):
            if self.link.connected:
                self.link.set_value("axis", "expo", int(val), instance=self.instance)
            self._redraw_expo()
            if self.other_expo_slider is not None:
                self.other_expo_slider.set_from_firmware(val)
        return sender

    def _on_profile_change(self, _event=None):
        idx = 1 if self.profile_var.get() == "Custom" else 0
        if self.link.connected:
            self.link.set_value("fx", "filterProfile_id", idx, instance=0)
        for cmd in ("damper", "friction", "inertia"):
            self._update_freq_q_enabled(cmd)

    def _update_freq_q_enabled(self, cmd):
        state = "normal" if self.profile_var.get() == "Custom" else "disabled"
        self._freq_entries[cmd].configure(state=state)
        self._q_entries[cmd].configure(state=state)

    def _on_freq_apply(self, cmd):
        try:
            val = int(float(self.freq_vars[cmd].get()))
        except ValueError:
            return
        if self.link.connected:
            self.link.set_value("fx", f"{cmd}_f", val, instance=0)

    def _on_q_apply(self, cmd):
        try:
            val = float(self.q_vars[cmd].get())
        except ValueError:
            return
        if self.link.connected:
            self.link.set_value("fx", f"{cmd}_q", round(val * 100), instance=0)

    def _on_expo_reset(self):
        self.expo_slider.set_from_firmware(0)
        self._send_expo()(0)

    # ------------------------------------------------------------- curves
    @staticmethod
    def _gainfactor(raw):
        return (raw + 1) / 256.0

    def _redraw_curve(self, cmd):
        x_min, x_max, metric_key = self.DOMAINS[cmd]
        scaler = EffectsCanvas.GAIN_SCALER[cmd] * self._gainfactor(self.gains[cmd])
        points = []
        for i in range(self.CURVE_POINTS + 1):
            metric = x_min + (x_max - x_min) * i / self.CURVE_POINTS
            if cmd == "friction":
                force = self._friction_force(metric, scaler)
            else:
                force = max(-32767, min(32767, scaler * metric))
            points.append((metric, force))
        self.charts[cmd].set_curve(points)
        self.charts[cmd].set_marker(self.metrics[metric_key])

    def _friction_force(self, speed, scaler):
        if speed == 0:
            return 0.0
        rampup_pct = max(1, round(self.smooth_pct / 100.0 * 32767))
        if abs(speed) < rampup_pct:
            phase = math.pi * (abs(speed) / rampup_pct - 0.5)
            rampup_factor = (1 + math.sin(phase)) / 2
        else:
            rampup_factor = 1.0
        sign = 1 if speed >= 0 else -1
        force = 32767 * rampup_factor * sign * scaler
        return max(-32767, min(32767, force))

    def _redraw_expo(self):
        raw = self.expo_slider.get_value()
        if raw == 0:
            exponent = 1.0
        else:
            val_f = abs(raw / self.exposcale) if self.exposcale else 0.0
            exponent = (1.0 / (1.0 + val_f)) if raw < 0 else (1.0 + val_f)
        self.expo_value_label.configure(text=f"{exponent:.2f}")
        points = []
        for i in range(self.CURVE_POINTS + 1):
            x = -1.0 + 2.0 * i / self.CURVE_POINTS
            y = math.copysign(abs(x) ** exponent, x) if x != 0 else 0.0
            points.append((x, y))
        self.expo_chart.set_curve(points)

    # --------------------------------------------------------- fw callbacks
    def _on_gain_reply(self, cmd):
        def cb(reply):
            try:
                self.gains[cmd] = int(reply)
            except ValueError:
                return
            self.gain_sliders[cmd].set_from_firmware(self.gains[cmd])
            self._redraw_curve(cmd)
        return cb

    def _on_smooth_reply(self, reply):
        try:
            self.smooth_pct = int(reply)
        except ValueError:
            return
        self.smooth_slider.set_from_firmware(self.smooth_pct)
        self._redraw_curve("friction")

    def _on_profile_reply(self, reply):
        try:
            idx = int(reply)
        except ValueError:
            return
        self.profile_var.set("Custom" if idx else "Default")
        for cmd in ("damper", "friction", "inertia"):
            self._update_freq_q_enabled(cmd)

    def _on_freq_reply(self, cmd):
        def cb(reply):
            try:
                self.freq_vars[cmd].set(str(int(reply)))
            except ValueError:
                pass
        return cb

    def _on_q_reply(self, cmd):
        def cb(reply):
            try:
                self.q_vars[cmd].set(f"{int(reply) / 100.0:.2f}")
            except ValueError:
                pass
        return cb

    def _on_exposcale_reply(self, reply):
        try:
            self.exposcale = int(reply) or 1
        except ValueError:
            self.exposcale = 1
        self._redraw_expo()

    def _on_expo_reply(self, reply):
        try:
            val = int(reply)
        except ValueError:
            return
        self.expo_slider.set_from_firmware(val)
        self._redraw_expo()

    def _on_metric_reply(self, key):
        def cb(reply):
            try:
                self.metrics[key] = int(reply)
            except ValueError:
                return
            for cmd, (_, _, metric_key) in self.DOMAINS.items():
                if metric_key == key:
                    self.charts[cmd].set_marker(self.metrics[key])
        return cb

    def on_connected(self):
        # "?" and "=" (not "!"): also catches the "=" echo when the Main
        # tab's EffectsCanvas slider changes the same gain (see class
        # docstring), without matching EffectsCanvas's own "!" info-string
        # request for the same fx.<cmd> (that reply isn't a plain int and
        # would fail to parse here).
        for cmd in self.GAIN_CMDS:
            self.link.register("fx", cmd, self._on_gain_reply(cmd), instance=0, typechar="?")
            self.link.register("fx", cmd, self._on_gain_reply(cmd), instance=0, typechar="=")
            self.link.send_get("fx", cmd, instance=0)
        self.link.register("fx", "frictionPctSpeedToRampup", self._on_smooth_reply, instance=0, typechar=None)
        self.link.send_get("fx", "frictionPctSpeedToRampup", instance=0)
        self.link.register("fx", "filterProfile_id", self._on_profile_reply, instance=0, typechar=None)
        self.link.send_get("fx", "filterProfile_id", instance=0)
        for cmd in ("damper", "friction", "inertia"):
            self.link.request_once("fx", f"{cmd}_f", self._on_freq_reply(cmd), instance=0)
            self.link.request_once("fx", f"{cmd}_q", self._on_q_reply(cmd), instance=0)
        self.link.request_once("axis", "exposcale", self._on_exposcale_reply, instance=self.instance)
        self.link.register("axis", "expo", self._on_expo_reply, instance=self.instance, typechar=None)
        self.link.send_get("axis", "expo", instance=self.instance)
        self.link.register("axis", "curpos", self._on_metric_reply("curpos"), instance=self.instance, typechar="?")
        self.link.register("axis", "curspd", self._on_metric_reply("curspd"), instance=self.instance, typechar="?")
        self.link.register("axis", "curaccel", self._on_metric_reply("curaccel"), instance=self.instance, typechar="?")

    def poll(self):
        if not self.link.connected:
            return
        self.link.send_get("axis", "curpos", instance=self.instance)
        self.link.send_get("axis", "curspd", instance=self.instance)
        self.link.send_get("axis", "curaccel", instance=self.instance)


class AdvancedTuningTab(ttk.Frame):
    """"Advanced Tuning" tab content: just FxTuningPanel (5 response-curve
    graphs) now - Axis info and Limits/Permanent effects moved to the Main
    tab's EffectsCanvas / were removed, per user request.

    No longer wraps its content in a scrollable area (removed per user
    request, same as the Main page's scroll wrapper) - FxTuningPanel's
    content (560px tall) comfortably fits the fixed window, so this class
    is now just the plain page frame FxTuningPanel places itself onto,
    exactly like App.main_frame for InputsCanvas/EffectsCanvas."""

    def __init__(self, parent, link, axis_instance=0, **kwargs):
        super().__init__(parent, **kwargs)
        self.fx_panel = FxTuningPanel(
            self, link, axis_instance,
            base_x=P.ADVANCED_CONTENT_X, base_y=P.ADVANCED_CONTENT_TOP_Y,
        )

    def on_connected(self):
        self.fx_panel.on_connected()

    def poll(self):
        self.fx_panel.poll()


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        # Hidden immediately: _build_ui() below decodes ~27MB of sprite PNGs
        # synchronously, which would otherwise leave a blank/frozen window on
        # screen for that whole time. A small loading window (see
        # _show_loading_window) is shown instead and closed once the real
        # window is fully built.
        self.withdraw()

        self.title(P.WINDOW_TITLE)
        # Replaces Tk's default feather-quill icon in the title bar/Alt-Tab
        # with the Twisty wheelbase render - .ico chosen specifically since
        # PNG isn't accepted there.
        try:
            self.iconbitmap(resource_path(os.path.join("data", "icon.ico")))
        except tk.TclError:
            pass
        if P.WINDOW_SCALING is not None:
            self.tk.call("tk", "scaling", P.WINDOW_SCALING)
        self.geometry(P.WINDOW_GEOMETRY)
        self.resizable(False, False)

        loading_window = self._show_loading_window()

        self._port_map = {}

        self._bg_stage = 0
        self._implausible_temp_fault = False
        self._default_bg = ttk.Style().lookup("TFrame", "background")
        self._known_fw_errors = set()

        self.link = FFBProtocol(self._log, self._on_connection_changed, self._on_incompatible_fw)
        self.hid_link = HidLink(self._on_hid_report, self._log)

        self._build_ui()

        loading_window.destroy()
        self.deiconify()

        self._refresh_ports()
        self._try_autoconnect()

        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(30, self._pump_loop)
        self.after(30, self._fast_poll_loop)
        self.after(1500, self._keepalive_loop)
        self.after(300, self._fw_error_poll_loop)

    # ---------------------------------------------------------------- UI setup
    def _setup_button_style(self):
        """"DegreeButton.TButton": custom bordered/gray-background button
        style, registered here (once, before any button using it is
        created) instead of down in EffectsCanvas where it originally
        lived, since it's now shared by the toolbar buttons and the
        analog-calibration buttons too (per user request) in addition to
        Save/Load and the degree/Center button.

        Needed because a plain ttk.Button (or ttk.Checkbutton with
        style="Toolbutton") renders with no visible border/background at
        rest under Windows' native "vista" theme - "vista" paints these
        via the OS visual-style engine, which ignores style.configure() on
        the stock elements entirely (same root cause as the earlier
        Black.TCheckbutton problem, Abschnitt 4.20.6). Fixed by borrowing
        "Button.border" from the "clam" theme (plain Tk drawing, so
        styling it actually works) into a custom layout - relief="raised"
        is the specific option that makes the border/background actually
        paint (background color alone wasn't enough - confirmed via
        ttk.Style().lookup() in a standalone test)."""
        style = ttk.Style()
        style.element_create("DegreeButton.border", "from", "clam", "Button.border")
        style.layout("DegreeButton.TButton", [
            ("DegreeButton.border", {"sticky": "nswe", "border": "1", "children": [
                ("Button.padding", {"sticky": "nswe", "children": [
                    ("Button.label", {"sticky": "nswe"}),
                ]}),
            ]}),
        ])
        style.configure(
            "DegreeButton.TButton", anchor="center", background=P.BUTTON_BG_COLOR,
            relief=P.BUTTON_RELIEF, borderwidth=P.BUTTON_BORDERWIDTH,
            bordercolor=P.BUTTON_BORDER_COLOR,
            lightcolor=P.BUTTON_SHADOW_LIGHT_COLOR, darkcolor=P.BUTTON_SHADOW_DARK_COLOR,
        )
        style.map(
            "DegreeButton.TButton",
            background=[("pressed", P.BUTTON_PRESSED_COLOR), ("active", P.BUTTON_HOVER_COLOR)],
            relief=[("pressed", P.BUTTON_RELIEF_PRESSED)],
        )

    def _show_loading_window(self):
        """Small borderless window shown while _build_ui() runs, so the user
        gets immediate feedback instead of a blank/unresponsive main window
        during the synchronous sprite PNG loading. Caller destroys it (and
        deiconifies self) once _build_ui() returns."""
        loading = tk.Toplevel(self)
        loading.overrideredirect(True)
        loading.configure(bg="#f0f0f0")
        width, height = 280, 100
        screen_w = loading.winfo_screenwidth()
        screen_h = loading.winfo_screenheight()
        x = (screen_w - width) // 2
        y = (screen_h - height) // 2
        loading.geometry(f"{width}x{height}+{x}+{y}")
        tk.Label(
            loading, text="Loading...", bg="#f0f0f0", font=("Segoe UI", 12),
        ).pack(expand=True, fill="both")
        loading.update()
        return loading

    def _build_ui(self):
        self._setup_button_style()

        # Toolbar: a 2-row grid per user request/sketch - column 0 is the
        # Port row (row 0) stacked over the VCC/Temp/FFB ReadoutBar (row 1,
        # unchanged content, just grid()ed instead of pack()ed so it shares
        # column 0 with the Port row above it); columns 1/2/3 are the 6
        # toolbar buttons, wrapped from one row into 3 columns x 2 rows
        # (Refresh/Disconnect/Info on top, Save to Twisty/Advanced/Err.
        # Reset below); column 4 is the
        # Status/Errors log, which used to be its own full-width row at the
        # very bottom of the window (see log_frame's old spot) - moved up
        # here, per user request, into the horizontal room next to the
        # buttons instead, spanning both rows' height.
        #
        # All pixel gaps below (the 8px between adjacent buttons, the extra
        # 8px on Refresh's left edge to match column 0's own natural width,
        # the 16px before the log column) reproduce/extend the old pack()
        # layout's actual measured spacing (verified against the real
        # running app) rather than being guessed.
        toolbar = ttk.Frame(self, padding=8)
        toolbar.pack(fill="x")

        port_frame = ttk.Frame(toolbar)
        port_frame.grid(row=0, column=0, sticky="w")
        ttk.Label(port_frame, text="Port:").pack(side="left")
        self.port_var = tk.StringVar()
        self.port_combo = ttk.Combobox(port_frame, textvariable=self.port_var, state="readonly", width=45)
        self.port_combo.pack(side="left", padx=4)

        # VCC + L1/L2/L3 temperature + FFB readout - same ReadoutBar class
        # and content as before, just grid()ed into column 0 (row 1) below
        # the Port row instead of pack()ed as its own full-width row. Its
        # own natural content width happens to already closely match
        # port_frame's width (both were deliberately sized/aligned to the
        # Port dropdown in earlier changes), so column 0 doesn't need an
        # explicit width - it sizes to whichever of the two is wider.
        self.readout_bar = ReadoutBar(toolbar, self.link, padding=0)
        self.readout_bar.grid(row=1, column=0, sticky="w", pady=(8, 0))

        # All 5 buttons below share P.BUTTON_WIDTH_CHARS (the same width
        # used by every other button in the app now, per user request -
        # "es sind nicht alle Buttons gleich breit") instead of their own
        # former button_width = len("Disconnect") - sized to the single
        # widest real label anywhere ("Release + Click", the analog-
        # calibration buttons), so every one of these 5 toolbar labels
        # (all shorter) fits with room to spare, no wrapping/growing.
        # style="DegreeButton.TButton" on all 5, per user request - same
        # look as Save/Load elsewhere (see _setup_button_style()).
        ttk.Button(
            toolbar, text="Refresh", width=P.BUTTON_WIDTH_CHARS, command=self._refresh_ports,
            style="DegreeButton.TButton",
        ).grid(row=0, column=1, padx=(8, 4), sticky="w")
        self.connect_btn = ttk.Button(
            toolbar, text="Connect", width=P.BUTTON_WIDTH_CHARS, command=self._toggle_connect,
            style="DegreeButton.TButton",
        )
        self.connect_btn.grid(row=0, column=2, padx=4, sticky="w")
        self.error_reset_btn = ttk.Button(
            toolbar, text="Error Reset", width=P.BUTTON_WIDTH_CHARS, command=self._on_error_reset,
            style="DegreeButton.TButton",
        )
        self.error_reset_btn.grid(row=1, column=3, padx=4, pady=(8, 0), sticky="w")
        self.save_flash_btn = ttk.Button(
            toolbar, text="Save to Twisty", width=P.BUTTON_WIDTH_CHARS,
            command=self._on_save_to_flash, style="DegreeButton.TButton",
        )
        self.save_flash_btn.grid(row=1, column=1, padx=(8, 4), pady=(8, 0), sticky="w")

        # Opens the standalone credits window (info_window.py) thanking
        # Ultrawipf/Yannick Richter for the OpenFFBoard firmware this
        # project builds on.
        ttk.Button(
            toolbar, text="Info", width=P.BUTTON_WIDTH_CHARS,
            command=lambda: open_info_window(self, IMAGES_DIR),
            style="DegreeButton.TButton",
        ).grid(row=0, column=3, padx=4, sticky="w")

        # Page switcher - replaces the old ttk.Notebook tab strip (see
        # "pages" below) per user request. One toggle button instead of two
        # separate ones: its text always names the *other* page (the one a
        # click would take you to), not the page you're currently on - see
        # _show_page().
        self.page_toggle_btn = ttk.Button(
            toolbar, text="Advanced", width=P.BUTTON_WIDTH_CHARS, command=self._toggle_page,
            style="DegreeButton.TButton",
        )
        self.page_toggle_btn.grid(row=1, column=2, padx=4, pady=(8, 0), sticky="w")

        # Status/Errors log - fixed pixel size (not the Text widget's own
        # character/line-based sizing) via a plain tk.Frame with
        # pack_propagate(False), so its right edge lands exactly at the
        # Inputs canvas's rightmost image (the Accelerate/Z-axis gauge, per user
        # request) regardless of font metrics. Originally measured against
        # the real running app at the old button width (66px each, 10
        # chars): wrapper started at x=592, Accelerate gauge's right edge at
        # x=908 (InputsCanvas.gauge2, see Placement.py's
        # INPUTS_GAUGE2_IMAGE_X) -> 908-592=316px Text width + 17px
        # scrollbar = 333 wrapper width. Recomputed analytically (not
        # re-measured live) after P.BUTTON_WIDTH_CHARS widened all 3
        # button columns before this one to 96px each (+30px/column): new
        # start = 592 + 3*30 = 682, so 908-682=226px Text width + 17px =
        # 243 wrapper width. Re-measure and adjust this width if
        # BUTTON_WIDTH_CHARS/PX, the column padx values, or the app's font
        # ever change again - all of those shift where this wrapper
        # starts. Height 58 matches the two button rows' combined height
        # (25px each + 8px pady between). No "Status / Errors:" caption
        # anymore (former log_frame had one) - dropped per user request,
        # the log itself is self-explanatory.
        log_wrapper = tk.Frame(toolbar, width=243, height=58)
        log_wrapper.grid(row=0, column=4, rowspan=2, padx=(16, 0), sticky="nw")
        # pack_propagate (not grid_propagate) - it's keyed to the *child's*
        # geometry manager (Text/Scrollbar below use pack()), not to how
        # log_wrapper itself is placed in the toolbar's grid above; using
        # the wrong one silently does nothing and the frame reverts to
        # sizing itself around its children instead of staying fixed.
        log_wrapper.pack_propagate(False)
        self.log_text = tk.Text(log_wrapper, state="disabled", wrap="word", font=("Arrial Narrow", 8))
        log_scroll = ttk.Scrollbar(log_wrapper, orient="vertical", command=self.log_text.yview)
        self.log_text.configure(yscrollcommand=log_scroll.set)
        log_scroll.pack(side="right", fill="y")
        self.log_text.pack(side="left", fill="both", expand=True)

        # Page container: Main and Advanced Tuning are both full-size
        # frames in the same grid cell, switched by grid_remove()/grid()
        # from the buttons above instead of a ttk.Notebook - same content,
        # just no more native tab strip. See _show_page() for why
        # grid_remove() is used instead of the simpler tkraise().
        pages = ttk.Frame(self)
        pages.pack(fill="both", expand=True)
        pages.grid_rowconfigure(0, weight=1)
        pages.grid_columnconfigure(0, weight=1)

        # "Main" page: the former "Inputs"/"Effects" bordered boxes (each a
        # ttk.LabelFrame plus an inner Canvas/Frame that existed only to
        # give their children a place() coordinate origin) were removed per
        # user request - InputsCanvas/EffectsCanvas now place their content
        # directly onto this frame instead, offset by Placement.py's
        # MAIN_CONTENT_*/MAIN_EFFECTS_BASE_Y constants (see PlacedGroup), so
        # both blocks keep exactly the same pixel arrangement relative to
        # each other as before, just without the surrounding box. No more
        # scrolling here either (removed alongside the boxes, per user
        # request) - both blocks comfortably fit inside the fixed window.
        self.main_frame = ttk.Frame(pages)
        self.main_frame.grid(row=0, column=0, sticky="nsew")

        self.inputs_canvas = InputsCanvas(
            self.main_frame, self.link, self.hid_link,
            base_x=P.MAIN_CONTENT_X, base_y=P.MAIN_CONTENT_TOP_Y,
        )
        self.effects_canvas = EffectsCanvas(
            self.main_frame, self.link, self.hid_link,
            base_x=P.MAIN_CONTENT_X, base_y=P.MAIN_EFFECTS_BASE_Y,
        )

        # "Advanced Tuning" page: features from the official OpenFFBoard
        # Configurator not otherwise in this GUI (see Twisty_README.md).
        self.advanced_tab = AdvancedTuningTab(pages, self.link)
        self.advanced_tab.grid(row=0, column=0, sticky="nsew")

        # Cross-tab gain-slider mirror (see EffectsCanvas.other_gain_sliders'
        # own comment) - wired here since this is the first point both
        # panels exist. Each side's _send_fx() sender uses this to update
        # the other tab's matching slider directly in Python, instead of
        # (incorrectly) relying on the firmware's "=" SET echo to carry
        # the new value.
        self.effects_canvas.other_gain_sliders = self.advanced_tab.fx_panel.gain_sliders
        self.advanced_tab.fx_panel.other_gain_sliders = self.effects_canvas.fx_sliders
        self.effects_canvas.other_expo_slider = self.advanced_tab.fx_panel.expo_slider
        self.advanced_tab.fx_panel.other_expo_slider = self.effects_canvas.expo_slider
        self.effects_canvas.fx_panel = self.advanced_tab.fx_panel
        # Reverse reference, for the Advanced tab's own copy of the
        # Save/Load buttons (see FxTuningPanel.__init__).
        self.advanced_tab.fx_panel.effects_canvas = self.effects_canvas
        # Reference to the Main tab's InputsCanvas, for Save/Load's Value
        # analog 1/2 Min/Max + Invert Output fields (see
        # EffectsCanvas._load_inputs_fields()).
        self.effects_canvas.inputs_canvas = self.inputs_canvas

        self._show_page("main")

    def _toggle_page(self):
        self._show_page("advanced" if self._current_page == "main" else "main")

    def _show_page(self, name):
        # grid_remove()/grid() (fully unmanage the hidden page), not just
        # tkraise() (stacking order only) - with this many place()'d
        # Canvas widgets stacked in the same cell (5 ResponseCurveCharts on
        # Advanced alone), tkraise() left the previously-topmost page still
        # mapped underneath, and Windows/Tk would occasionally fail to
        # invalidate that exact screen region on the next raise, bleeding
        # stale Advanced-tab pixels through onto Main at the same
        # coordinates. grid_remove() actually unmaps the hidden page, so
        # there is nothing left underneath to bleed through.
        self._current_page = name
        if name == "main":
            self.advanced_tab.grid_remove()
            self.main_frame.grid(row=0, column=0, sticky="nsew")
            self.page_toggle_btn.configure(text="Advanced")
        else:
            self.main_frame.grid_remove()
            self.advanced_tab.grid(row=0, column=0, sticky="nsew")
            self.page_toggle_btn.configure(text="Main")

    # -------------------------------------------------------- overtemp background
    def _apply_bg_stage(self, stage):
        """Colors only the 3 temperature readouts' own background (L1/L2/L3
        in ReadoutBar) - per user request, replacing an earlier version
        that recolored the entire window (self.configure(bg=...)) plus
        every TFrame/TLabelframe/TLabel style globally. All 3 always show
        the same color together, since pt100stage is one combined value
        for all 3 channels, not tracked per-channel by the firmware."""
        if stage == self._bg_stage:
            return
        self._bg_stage = stage
        self._update_temp_bg()

    def _update_temp_bg(self):
        """Combines the overtemperature stage and the wire-break failsafe
        into one background color, same "worst wins" rule as the firmware's
        force limit (Pt100Monitor.cpp): a critical overtemp (stage 2) or an
        active implausible-temperature fault both use the same red as
        TEMP_BG_COLORS[2], regardless of which one is currently true."""
        if self._bg_stage == 2 or self._implausible_temp_fault:
            color = TEMP_BG_COLORS[2]
        else:
            color = TEMP_BG_COLORS[self._bg_stage] or self._default_bg
        for ch in self.readout_bar.temp_channels.values():
            ch["label"].configure(bg=color)

    def _log(self, message):
        print(message)
        self.log_text.configure(state="normal")
        self.log_text.insert("end", str(message) + "\n")
        self.log_text.see("end")
        self.log_text.configure(state="disabled")

    # ------------------------------------------------------------- port list
    def _refresh_ports(self):
        ports = self.link.list_ports()
        self._port_map = {}
        display = []
        official_texts = []
        for p in ports:
            marker = " (FFBoard device)" if FFBProtocol.is_official(p) else ""
            text = f"{p.device} : {p.description}{marker}"
            display.append(text)
            self._port_map[text] = p.device
            if marker:
                official_texts.append(text)

        self.port_combo["values"] = display
        if official_texts:
            self.port_combo.set(official_texts[0])
        elif display:
            self.port_combo.set(display[0])
        else:
            self.port_combo.set("")
        return len(official_texts)

    def _try_autoconnect(self):
        self._refresh_ports()
        auto_port = FFBProtocol.find_auto_port()
        if auto_port:
            self.link.connect(auto_port)

    # ------------------------------------------------------------ connection
    def _toggle_connect(self):
        if self.link.connected:
            self.link.disconnect()
            return
        device = self._port_map.get(self.port_var.get())
        if not device:
            self._log("No port selected")
            return
        self.link.connect(device)

    def _on_connection_changed(self, connected):
        self.connect_btn.configure(text="Disconnect" if connected else "Connect")
        self.port_combo.configure(state="disabled" if connected else "readonly")
        if connected:
            self.link.request_once("main", "aintypes", self._ensure_aintypes, instance=0)
            self.link.request_once("main", "btntypes", self._ensure_btntypes, instance=0)
            self.link.register("sys", "errors", self._on_fw_errors, instance=0)
            self.link.register("sys", "pt100stage", self._on_fw_pt100stage, instance=0)
            self.inputs_canvas.on_connected()
            self.effects_canvas.on_connected()
            self.advanced_tab.on_connected()
            self.readout_bar.on_connected()
            if self.hid_link.connect():
                self._log("HID interface connected (for smooth animation)")
        else:
            self.hid_link.disconnect()
            self._known_fw_errors.clear()

    def _ensure_aintypes(self, reply):
        """Bit 0 (LocalAnalog) must be enabled so the HID report's Y/Z fields
        carry the same local analog channels as apin.0.values."""
        try:
            mask = int(reply)
        except ValueError:
            return
        if not (mask & 1):
            self.link.set_value("main", "aintypes", mask | 1, instance=0)

    def _ensure_btntypes(self, reply):
        """Bit 0 (LocalButtons) must be enabled so the HID report's buttons
        field carries the wheel's physical button inputs."""
        try:
            mask = int(reply)
        except ValueError:
            return
        if not (mask & 1):
            self.link.set_value("main", "btntypes", mask | 1, instance=0)

    def _on_hid_report(self, buttons, x, y, z):
        self.effects_canvas.set_hid_x(x)
        self.inputs_canvas.set_hid_yz(y, z)
        self.inputs_canvas.set_hid_buttons(buttons)

    def _on_incompatible_fw(self, fw_version, expected_fw):
        # This GUI targets exactly one firmware version and never offers or
        # performs any firmware update/flash - mismatch is reported, nothing else.
        messagebox.showwarning(
            "Firmware mismatch",
            f"This GUI is built exclusively for firmware v{expected_fw}.\n"
            f"Detected v{fw_version}. Features may differ or be missing.",
        )

    # ------------------------------------------------------------- main loop
    def _pump_loop(self):
        self.link.pump()
        self.hid_link.pump()
        self.after(30, self._pump_loop)

    def _fast_poll_loop(self):
        if self.link.connected:
            self.inputs_canvas.poll()
            self.effects_canvas.poll()
            if self._current_page == "advanced":
                self.advanced_tab.poll()
            self.readout_bar.poll()
            # Polled in the same 30ms tick as apin.0.values (not the slower
            # error-poll loop) so the overtemperature background-color
            # warning (_apply_bg_stage, driven by this) reacts quickly
            # during fast heating - see main chat history: a 300ms gap was
            # enough to show several degrees of disagreement against the
            # L1/L2/L3 temperature readout.
            self.link.send_get("sys", "pt100stage", instance=0)
        self.after(30, self._fast_poll_loop)

    def _keepalive_loop(self):
        self.link.keepalive_tick()
        self.after(1500, self._keepalive_loop)

    def _fw_error_poll_loop(self):
        if self.link.connected:
            self.link.send_get("sys", "errors", instance=0)
        self.after(300, self._fw_error_poll_loop)

    def _on_fw_errors(self, reply):
        text = reply.strip()
        current = set() if text in ("", "None") else set(text.split("\n"))

        for line in current - self._known_fw_errors:
            self._log(f"[{time.strftime('%H:%M:%S')}] Error: {line}")

        self._known_fw_errors = current

        # Drives the same red L1/L2/L3 background as a critical overtemp
        # (see _update_temp_bg) - reacts within one error-poll cycle (300ms)
        # of the fault actually clearing/latching in the firmware.
        implausible_now = any(line.startswith(FW_ERROR_PREFIX_TEMP_IMPLAUSIBLE) for line in current)
        if implausible_now != self._implausible_temp_fault:
            self._implausible_temp_fault = implausible_now
            self._update_temp_bg()

    def _on_error_reset(self):
        if not self.link.connected:
            return
        self.link.send_get("sys", "errorsclr", instance=0)
        self._log("Error reset")
        self.after(80, self._reread_fw_errors_after_reset)

    def _on_save_to_flash(self):
        if not self.link.connected:
            return
        self.save_flash_btn.configure(state="disabled")
        self.after(500, lambda: self.save_flash_btn.configure(state="normal"))
        self.link.request_once("sys", "save", self._on_save_to_flash_reply, instance=0)

    def _on_save_to_flash_reply(self, reply):
        self._log(f"Save to Flash: {reply.strip()}")

    def _reread_fw_errors_after_reset(self):
        if self.link.connected:
            self.link.send_get("sys", "errors", instance=0)

    def _on_fw_pt100stage(self, reply):
        # No visible label for this anymore - kept polled solely to drive
        # the overtemperature background-color warning (_apply_bg_stage).
        try:
            stage = int(reply.strip())
        except ValueError:
            return
        self._apply_bg_stage(stage)

    def _on_close(self):
        self.link.disconnect()
        self.hid_link.disconnect()
        self.destroy()


if __name__ == "__main__":
    App().mainloop()
