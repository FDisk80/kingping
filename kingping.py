#!/usr/bin/env python3
import sys
import time
import collections
import math
import datetime
import re
import socket # For IP resolution
import ipaddress # For private IP check
from typing import List, Tuple

# --- Qt Imports ---
from PySide6.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QHBoxLayout, QLabel, QLineEdit,
    QPushButton, QTextEdit, QGridLayout, QSizePolicy, QSpacerItem, QFrame,
    QMessageBox
)
from PySide6.QtCore import Qt, QThread, Signal, Slot, QObject, QTimer, QPointF
from PySide6.QtGui import QPalette, QColor, QFont

# --- Plotting Imports ---
import pyqtgraph as pg

# --- ICMP Ping Library ---
try:
    import ping3
    ping3.EXCEPTIONS = False # Ensure ping3 returns None/False on error, not exceptions
except ImportError:
    print("Error: 'ping3' library not found. Please install it using 'pip install ping3'", file=sys.stderr)
    try: # Attempt GUI fallback for error
        app_check = QApplication.instance() or QApplication(sys.argv)
        QMessageBox.critical(None, "Error", "Required library 'ping3' not found.\nPlease install it using:\npip install ping3")
    except Exception: pass
    sys.exit(1)

# --- System Utilities Library (for CPU Usage) ---
try:
    import psutil
    PSUTIL_AVAILABLE = True
except ImportError:
    PSUTIL_AVAILABLE = False
    print("Warning: 'psutil' library not found. CPU usage display disabled. Install using 'pip install psutil'", file=sys.stderr)


# --- Configuration ---
DEFAULT_PING_INTERVAL_MS = 50
DEFAULT_PACKET_SIZE = 56
DEFAULT_TTL = 64
DEFAULT_PING_TIMEOUT_S = 2.0 # Default timeout in seconds
MAX_LOG_ENTRIES = 2000
INITIAL_CHART_MAX_Y_MS = 50
MAX_CHART_Y_MS = 5000.0
MAX_HISTORY_BUFFER = 5000 # Total pings to store in memory
INITIAL_VISIBLE_BARS = 75 # How many bars to show in the default view
DESIRED_BAR_PIXEL_WIDTH = 5 # Approx visual width for bars
MIN_VISIBLE_BARS = 20 # Ensure at least some bars are visible
DEFAULT_TARGET = "8.8.8.8"
CHART_BAR_WIDTH = 1.0 # Use full width (no gaps) in data coordinates
MIN_TIMEOUT_S = 0.1
MAX_TIMEOUT_S = 30.0
STATS_TIMER_INTERVAL_MS = 1000 # Update elapsed time & CPU every 1000ms (1 second)

# --- Helper Functions ---
def format_ping_time(ping_ms, default_value="-.-") -> str:
    """Formats ping time in ms, handling None or invalid values."""
    if ping_ms is None or not isinstance(ping_ms, (int, float)) or not math.isfinite(ping_ms) or abs(ping_ms) < 1e-6:
        return default_value
    return f"{ping_ms:.0f}"

def format_timeout_value(timeout_s: float | None) -> str:
    """Formats timeout value for display, handling None."""
    if timeout_s is None or not isinstance(timeout_s, (int, float)) or not math.isfinite(timeout_s):
        return str(DEFAULT_PING_TIMEOUT_S) # Return default if invalid
    return f"{timeout_s:.1f}" if timeout_s != math.floor(timeout_s) else f"{int(timeout_s)}"

def format_elapsed_time(seconds: float) -> str:
    """Formats elapsed seconds into HH:MM:SS string."""
    if seconds < 0: seconds = 0
    secs = int(seconds % 60)
    mins = int((seconds // 60) % 60)
    hours = int(seconds // 3600)
    return f"{hours:02}:{mins:02}:{secs:02}"

def generate_ticks(min_val: float, max_val: float) -> List[List[Tuple[float, str]]]:
    """Generates dynamic ticks for the Y axis (latency in ms)."""
    if max_val <= 0: return [[(0, "0ms")]]
    range_val = max_val - min_val
    # Determine step size based on the range
    if range_val <= 150: step = 10
    elif range_val <= 300: step = 20
    elif range_val <= 750: step = 50
    elif range_val <= 1500: step = 100
    elif range_val <= 3000: step = 200
    elif range_val <= MAX_CHART_Y_MS: step = 500
    else: step = 1000

    # Calculate the first tick value
    first_tick = math.ceil(min_val / step) * step if step > 0 else min_val
    ticks = []; val = first_tick
    # Generate ticks within the range
    while val <= max_val + 1e-9: # Add epsilon for float comparison
        ticks.append((val, f"{int(val)}ms"))
        if step == 0: break # Avoid infinite loop if step is zero
        val += step

    # Ensure 0ms tick is present if needed
    if min_val <= 1e-9 and not any(abs(t[0]) < 1e-9 for t in ticks):
         ticks.insert(0, (0.0, "0ms"))
    elif min_val > 0 and min_val < step and not any(abs(t[0]) < 1e-9 for t in ticks):
         ticks.insert(0, (0.0, "0ms"))

    # Remove duplicate rounded tick values
    final_ticks = []; added_vals = set()
    for tick_val, tick_label in ticks:
        rounded_val = round(tick_val, 6)
        if rounded_val not in added_vals:
            final_ticks.append((tick_val, tick_label))
            added_vals.add(rounded_val)

    # Ensure the max value has a tick if it's significantly far from the last one
    if max_val > 0 and not any(abs(t[0] - max_val) < 1e-6 for t in final_ticks):
        last_tick_val = final_ticks[-1][0] if final_ticks else -1
        # Add max value tick if it's far enough from the last tick
        if max_val > last_tick_val and (step == 0 or max_val - last_tick_val > step / 1.9):
             final_ticks.append((max_val, f"{int(max_val)}ms"))

    return [final_ticks] # Return format expected by pyqtgraph

def create_separator() -> QFrame:
    """Helper function to create a vertical separator line."""
    separator = QFrame()
    separator.setFrameShape(QFrame.Shape.VLine)
    separator.setFrameShadow(QFrame.Shadow.Sunken)
    separator.setObjectName("separator")
    return separator

# --- Ping Worker Thread ---
class PingWorker(QObject):
    """Runs ping operations in a separate thread."""
    result_ready = Signal(float, object, object) # timestamp, time_ms_or_err, error_type
    status_update = Signal(str) # status message
    finished = Signal() # emitted when the run loop finishes

    def __init__(self, target: str, interval_ms: int, size: int, ttl: int, timeout_s: float):
        """Initialize the worker with ping parameters."""
        super().__init__()
        self.target_host = target
        self.interval_s = max(0.05, interval_ms / 1000.0) # Ensure minimum interval
        self.size = size
        self.ttl = ttl
        self.timeout_s = max(MIN_TIMEOUT_S, timeout_s) # Use the provided timeout
        self._is_running = True # Flag to control the loop
        self.packets_sent_local = 0 # Counter for sequence number

    @Slot()
    def run(self):
        """The main ping loop executed in the thread."""
        self.status_update.emit(f"Pinging {self.target_host}...")
        seq = 0 # ICMP sequence number
        while self._is_running:
            loop_start_time = time.monotonic() # Record start time for interval calculation
            seq += 1
            self.packets_sent_local += 1
            # Read current settings (in case they change, though UI prevents this while running)
            current_target = self.target_host; current_interval_s = self.interval_s
            current_size = self.size; current_ttl = self.ttl; current_timeout_s = self.timeout_s
            time_ms: float | None | bool = False; error_type: str | None = None

            try:
                # Perform the ping using ping3 library
                delay = ping3.ping(
                    current_target,
                    timeout=current_timeout_s, # Use the configured timeout
                    unit='ms',
                    seq=seq,
                    size=current_size,
                    ttl=current_ttl
                )
                time_ms = delay # Result can be float (ms), None (timeout), or False (error)

                # Interpret the result from ping3
                if time_ms is None: error_type = "timeout"
                elif time_ms is False: error_type = "host_unknown" # Default error type for False
                elif isinstance(time_ms, (int, float)) and abs(time_ms) < 1e-6:
                     # Handle 0.0ms case: could be localhost or an error
                     ip_regex = r"^(?:[0-9]{1,3}\.){3}[0-9]{1,3}$"
                     is_ip = bool(re.match(ip_regex, current_target))
                     is_valid_ip = False
                     if is_ip: is_valid_ip = all(0 <= int(part) <= 255 for part in current_target.split('.'))
                     # If target isn't localhost or a valid IP, treat 0.0ms as an error
                     if not is_valid_ip and not (current_target == "localhost" or current_target.startswith("127.")):
                         time_ms = False; error_type = "host_unknown"

            # Catch permission errors (common on Linux/macOS without root/capabilities)
            except PermissionError:
                 error_type = "permission_error"; time_ms = False
                 self.status_update.emit("Permission denied (try running with sudo/admin?)")
                 self._is_running = False # Stop if permission denied
            # Catch any other unexpected errors
            except Exception as e:
                error_type = "unk_error"; time_ms = False
                self.status_update.emit(f"Worker Error: {e!r}")

            # Check if stop was requested before emitting result
            if not self._is_running: break
            # Emit the result back to the main thread
            self.result_ready.emit(loop_start_time, time_ms, error_type)

            # Calculate time elapsed in this loop iteration
            elapsed = time.monotonic() - loop_start_time
            # Calculate sleep duration to maintain the desired interval
            sleep_duration = max(0.01, current_interval_s - elapsed) # Ensure minimum sleep

            # Sleep while periodically checking the running flag
            slept_until = time.monotonic() + sleep_duration
            while time.monotonic() < slept_until:
                 if not self._is_running: break
                 time.sleep(0.01) # Short sleep to remain responsive
            if not self._is_running: break # Exit loop if stopped during sleep

        self.finished.emit() # Signal that the worker has finished

    def stop(self):
        """Sets the running flag to False to stop the loop."""
        self._is_running = False


# --- Main Application Window ---
class KingPingAppWindow(QWidget):
    """Main application window."""

    def __init__(self):
        super().__init__()
        # Set the actual window title
        self.setWindowTitle("KINGPING v1.3")
        self.current_chart_max_y = INITIAL_CHART_MAX_Y_MS
        self.setup_ui()
        self.apply_stylesheet()

        # --- State Variables ---
        self.ping_thread = None; self.ping_worker = None
        self.test_running = False; self.start_time = None
        self.packets_sent = 0; self.packets_received = 0
        self.min_time_ms = float('inf'); self.max_time_ms = float('-inf'); self.total_time_ms = 0.0
        self.ping_results = collections.deque(maxlen=MAX_HISTORY_BUFFER)
        self.target_valid = True; self.interval_valid = True; self.size_valid = True; self.ttl_valid = True; self.timeout_valid = True

        # --- Timer for Elapsed Time & CPU ---
        self.stats_update_timer = QTimer(self)
        self.stats_update_timer.setInterval(STATS_TIMER_INTERVAL_MS)
        self.stats_update_timer.timeout.connect(self.update_timed_stats)
        # Start the timer immediately on launch to always update CPU
        self.stats_update_timer.start()

        # --- Initial UI State ---
        self.validate_inputs(); self.update_stats_display(); self.update_button_state()
        self.update_chart_display(); self.target_input.setFocus()
        self.log_message("Tip: Click and drag chart horizontally to scroll history.", "info")
        if not PSUTIL_AVAILABLE:
            self.log_message("Install 'psutil' for CPU usage display.", "warning", "#ffaa00")
        # Call once at start to initialize CPU/Time labels to default values
        self.update_timed_stats()


    def setup_ui(self):
        """Create and arrange widgets."""
        main_layout = QVBoxLayout(self); main_layout.setContentsMargins(5, 5, 5, 5); main_layout.setSpacing(0)
        # --- Input Row ---
        self.input_frame = QFrame(); self.input_frame.setObjectName("input-frame")
        input_layout = QHBoxLayout(self.input_frame); input_layout.setContentsMargins(4, 4, 4, 4); input_layout.setSpacing(6)
        target_label = QLabel("Target:"); self.target_input = QLineEdit(DEFAULT_TARGET); self.target_input.setPlaceholderText("e.g., google.com or 8.8.8.8"); self.target_input.setToolTip("Enter hostname or IP address."); self.target_input.textChanged.connect(self.validate_inputs); self.target_input.returnPressed.connect(self.on_input_submitted)
        input_layout.addWidget(target_label); input_layout.addWidget(self.target_input, 1); input_layout.addWidget(create_separator())
        interval_label = QLabel("Interval:"); self.interval_input = QLineEdit(str(DEFAULT_PING_INTERVAL_MS)); self.interval_input.setPlaceholderText("ms"); self.interval_input.setFixedWidth(45); self.interval_input.setToolTip("Interval between pings (ms). Min 50."); self.interval_input.textChanged.connect(self.validate_inputs); self.interval_input.returnPressed.connect(self.on_input_submitted)
        self.ms_label = QLabel("ms"); self.ms_label.setObjectName("unit-label"); input_layout.addWidget(interval_label); input_layout.addWidget(self.interval_input); input_layout.addWidget(self.ms_label); input_layout.addWidget(create_separator())
        size_label = QLabel("Size:"); self.size_input = QLineEdit(str(DEFAULT_PACKET_SIZE)); self.size_input.setPlaceholderText("bytes"); self.size_input.setFixedWidth(40); self.size_input.setToolTip("Packet data payload size (bytes). Range: 0-65500."); self.size_input.textChanged.connect(self.validate_inputs); self.size_input.returnPressed.connect(self.on_input_submitted)
        self.bytes_label = QLabel("bytes"); self.bytes_label.setObjectName("unit-label"); input_layout.addWidget(size_label); input_layout.addWidget(self.size_input); input_layout.addWidget(self.bytes_label); input_layout.addWidget(create_separator())
        ttl_label = QLabel("TTL:"); self.ttl_input = QLineEdit(str(DEFAULT_TTL)); self.ttl_input.setFixedWidth(35); self.ttl_input.setToolTip("Time To Live (hops). Range: 1-255."); self.ttl_input.textChanged.connect(self.validate_inputs); self.ttl_input.returnPressed.connect(self.on_input_submitted)
        self.hops_label = QLabel("hops"); self.hops_label.setObjectName("unit-label"); input_layout.addWidget(ttl_label); input_layout.addWidget(self.ttl_input); input_layout.addWidget(self.hops_label); input_layout.addWidget(create_separator())
        timeout_label = QLabel("Timeout:"); self.timeout_input = QLineEdit(format_timeout_value(DEFAULT_PING_TIMEOUT_S)); self.timeout_input.setPlaceholderText("s"); self.timeout_input.setFixedWidth(40); self.timeout_input.setToolTip(f"Ping timeout (s). Range: {MIN_TIMEOUT_S}-{MAX_TIMEOUT_S}."); self.timeout_input.textChanged.connect(self.validate_inputs); self.timeout_input.returnPressed.connect(self.on_input_submitted)
        self.s_label = QLabel("s"); self.s_label.setObjectName("unit-label"); input_layout.addWidget(timeout_label); input_layout.addWidget(self.timeout_input); input_layout.addWidget(self.s_label)
        self.start_stop_button = QPushButton("[▶] START"); self.start_stop_button.setCheckable(False); self.start_stop_button.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed); self.start_stop_button.clicked.connect(self.toggle_start_stop); input_layout.addWidget(self.start_stop_button)
        main_layout.addWidget(self.input_frame)
        # --- Chart ---
        self.chart_frame = QFrame(); self.chart_frame.setObjectName("content-frame"); chart_layout = QVBoxLayout(self.chart_frame); chart_layout.setContentsMargins(0, 0, 0, 0); chart_layout.setSpacing(2)
        self.chart_title_label = QLabel("LATENCY CHART (ms)"); self.chart_title_label.setObjectName("content-title"); self.plot_widget = pg.PlotWidget(); self.plot_widget.setBackground(QColor('#0d0d0d')); self.plot_widget.showGrid(x=False, y=True, alpha=0.2); self.plot_widget.setMenuEnabled(False); self.plot_widget.setMinimumHeight(100); self.plot_widget.hideButtons(); self.plot_widget.setMouseEnabled(x=True, y=False)
        self.left_axis = self.plot_widget.getAxis('left'); self.left_axis.setWidth(50); self.left_axis.setLabel(''); self.plot_widget.showAxis('left'); self.plot_widget.hideAxis('bottom'); self.plot_widget.setYRange(0, self.current_chart_max_y, padding=0.05); self.left_axis.setTicks(generate_ticks(0, self.current_chart_max_y))
        self.bar_graph = pg.BarGraphItem(x=[], height=[], width=CHART_BAR_WIDTH, brushes=[]); self.plot_widget.addItem(self.bar_graph); self.chart_tooltip_item = pg.TextItem(html="", anchor=(0.5, 1.0)); self.chart_tooltip_item.setZValue(100); self.chart_tooltip_item.hide(); self.plot_widget.addItem(self.chart_tooltip_item); self.plot_widget.scene().sigMouseMoved.connect(self.handle_chart_mouse_move)
        chart_layout.addWidget(self.chart_title_label); chart_layout.addWidget(self.plot_widget); main_layout.addWidget(self.chart_frame)
        # --- Statistics ---
        self.stats_frame = QFrame(); self.stats_frame.setObjectName("content-frame"); stats_layout = QVBoxLayout(self.stats_frame); stats_layout.setContentsMargins(0, 0, 0, 0); stats_layout.setSpacing(2)
        self.stats_title_label = QLabel("STATISTICS"); self.stats_title_label.setObjectName("content-title"); self.stats_grid_layout = QGridLayout(); self.stats_grid_layout.setContentsMargins(9, 4, 9, 4); self.stats_grid_layout.setSpacing(10)
        self.sent_label = QLabel("Sent: 0"); self.received_label = QLabel("Received: 0"); self.lost_label = QLabel("Lost: 0 (0%)"); self.cpu_label = QLabel("CPU: -- %")
        self.stats_grid_layout.addWidget(self.sent_label, 0, 0); self.stats_grid_layout.addWidget(self.received_label, 0, 1); self.stats_grid_layout.addWidget(self.lost_label, 0, 2); self.stats_grid_layout.addWidget(self.cpu_label, 0, 3)
        self.min_label = QLabel("Min: -.-- ms"); self.max_label = QLabel("Max: -.-- ms"); self.avg_label = QLabel("Avg: -.-- ms"); self.time_label = QLabel("Time: 00:00:00")
        self.stats_grid_layout.addWidget(self.min_label, 1, 0); self.stats_grid_layout.addWidget(self.max_label, 1, 1); self.stats_grid_layout.addWidget(self.avg_label, 1, 2); self.stats_grid_layout.addWidget(self.time_label, 1, 3)
        self.stats_grid_layout.setColumnStretch(0, 1); self.stats_grid_layout.setColumnStretch(1, 1); self.stats_grid_layout.setColumnStretch(2, 1); self.stats_grid_layout.setColumnStretch(3, 1); stats_layout.addWidget(self.stats_title_label); stats_layout.addLayout(self.stats_grid_layout); main_layout.addWidget(self.stats_frame)
        # --- Log ---
        self.log_frame = QFrame(); self.log_frame.setObjectName("content-frame"); log_layout = QVBoxLayout(self.log_frame); log_layout.setContentsMargins(0, 0, 0, 0); log_layout.setSpacing(2)
        self.log_title_label = QLabel("LOG"); self.log_title_label.setObjectName("content-title"); self.log_output = QTextEdit(); self.log_output.setReadOnly(True); self.log_output.setLineWrapMode(QTextEdit.LineWrapMode.NoWrap); self.log_output.setMinimumHeight(80); self.log_output.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        log_layout.addWidget(self.log_title_label); log_layout.addWidget(self.log_output); main_layout.addWidget(self.log_frame)
        # --- Layout Stretch Factors ---
        main_layout.setStretchFactor(self.chart_frame, 3); main_layout.setStretchFactor(self.stats_frame, 0); main_layout.setStretchFactor(self.log_frame, 2)

    def apply_stylesheet(self):
        """Apply QSS for styling the application."""
        self.setStyleSheet(f"""
            QWidget {{ background-color: #1a1a1a; color: #00ff00; font-family: Consolas, Courier New, monospace; font-size: 9pt; }}
            QFrame#input-frame {{ background-color: #1a1a1a; border: none; }}
            QLabel {{ color: #888; padding-top: 3px; font-size: 9pt; }}
            QLabel#unit-label {{ color: #aaa; padding-left: 1px; padding-right: 6px; margin-left: -2px; padding-top: 3px; }}
            QLineEdit {{ background-color: #2a2a2a; border: 1px solid #555; color: #33ff33; padding: 2px 4px; border-radius: 2px; font-size: 9pt; min-height: 20px; }}
            QLineEdit:focus {{ border: 1px solid #00ff00; }}
            QLineEdit[invalid="true"] {{ border: 1px solid #ff0000; color: #ff5555; }}
            QPushButton {{ background-color: #333; color: #ccc; border: 1px solid #555; padding: 2px 8px; min-height: 20px; border-radius: 2px; font-weight: bold; font-size: 9pt; }}
            QPushButton:hover {{ background-color: #555; color: #fff; border: 1px solid #aaa; }}
            QPushButton#start_stop_button[running="true"] {{ background-color: #800000; color: #ffffff; border: 1px solid #ff6666; }}
            QPushButton#start_stop_button[running="true"]:hover {{ background-color: #ff6666; color: #0d0d0d; border: 1px solid #ff0000; }}
            QPushButton#start_stop_button[running="false"] {{ background-color: #005000; color: #ffffff; border: 1px solid #33ff33; }}
            QPushButton#start_stop_button[running="false"]:hover {{ background-color: #33ff33; color: #0d0d0d; border: 1px solid #00dd00; }}
            QTextEdit {{ background-color: #0d0d0d; color: #ccc; font-size: 9pt; border-radius: 0px; border: none; }}
            PlotWidget {{ border: none; background-color: #0d0d0d; }}
            /* Style for statistics labels */
            QLabel#sent_label, QLabel#received_label, QLabel#lost_label,
            QLabel#min_label, QLabel#max_label, QLabel#avg_label,
            QLabel#cpu_label, QLabel#time_label {{
                color: #00ff00; font-weight: bold; font-size: 9pt;
            }}
            QLabel#content-title {{ color: #888; font-weight: bold; qproperty-alignment: 'AlignVCenter | AlignLeft'; padding: 4px 6px 2px 6px; margin: 0; font-size: 9pt; background-color: #1a1a1a; border-bottom: 1px solid #444; }}
            QFrame#content-frame {{ border: 1px solid #444; border-radius: 3px; margin-top: 4px; background-color: #1a1a1a; }}
            QToolTip {{ background-color: #2a2a2a; color: #dddddd; border: 1px solid #555555; padding: 3px; border-radius: 2px; font-size: 8pt; }}
            QFrame#separator {{ border: none; border-left: 1px solid #444; margin-left: 4px; margin-right: 4px; min-height: 20px; }}
        """)
        # Set object names for specific styling via QSS selectors
        self.start_stop_button.setObjectName("start_stop_button")
        self.sent_label.setObjectName("sent_label"); self.received_label.setObjectName("received_label"); self.lost_label.setObjectName("lost_label")
        self.min_label.setObjectName("min_label"); self.max_label.setObjectName("max_label"); self.avg_label.setObjectName("avg_label")
        self.cpu_label.setObjectName("cpu_label"); self.time_label.setObjectName("time_label")
        self.plot_widget.setObjectName("PlotWidget")
        self.chart_title_label.setObjectName("content-title"); self.stats_title_label.setObjectName("content-title"); self.log_title_label.setObjectName("content-title")
        self.ms_label.setObjectName("unit-label"); self.bytes_label.setObjectName("unit-label"); self.hops_label.setObjectName("unit-label"); self.s_label.setObjectName("unit-label")
        self.chart_frame.setObjectName("content-frame"); self.stats_frame.setObjectName("content-frame"); self.log_frame.setObjectName("content-frame")
        self.input_frame.setObjectName("input-frame")
        # Initialize button state property
        self.start_stop_button.setProperty("running", False)
        # Re-polish widgets to apply styles correctly after setting object names/properties
        self.style().unpolish(self.start_stop_button); self.style().polish(self.start_stop_button)

    def validate_inputs(self):
        """Validate target, interval, size, TTL, and timeout inputs."""
        target = self.target_input.text().strip()
        interval_str = self.interval_input.text().strip()
        size_str = self.size_input.text().strip()
        ttl_str = self.ttl_input.text().strip()
        timeout_str = self.timeout_input.text().strip()
        target_ok = False; interval_ok = False; size_ok = False; ttl_ok = False; timeout_ok = False

        # Target Validation
        if target:
            hostname_regex = r"^(?=.{1,253}$)(([a-zA-Z0-9]|[a-zA-Z0-9][a-zA-Z0-9\-]{0,61}[a-zA-Z0-9])\.)*([A-Za-z0-9]|[A-Za-z0-9][A-Za-z0-9\-]{0,61}[A-Za-z0-9])$"
            ip_regex = r"^(?:[0-9]{1,3}\.){3}[0-9]{1,3}$"
            def is_valid_ipv4(ip):
                 match = re.match(ip_regex, ip);
                 if not match: return False
                 try: parts = ip.split('.'); return len(parts) == 4 and all(0 <= int(part) <= 255 for part in parts)
                 except ValueError: return False
            target_ok = target == "localhost" or bool(re.match(hostname_regex, target)) or is_valid_ipv4(target)
        self.target_input.setProperty("invalid", not target_ok); self.target_valid = target_ok

        # Interval Validation
        try: interval_val = int(interval_str); interval_ok = interval_val >= 50
        except ValueError: interval_ok = False
        self.interval_input.setProperty("invalid", not interval_ok); self.interval_valid = interval_ok

        # Size Validation
        try: size_val = int(size_str); size_ok = 0 <= size_val <= 65500
        except ValueError: size_ok = False
        self.size_input.setProperty("invalid", not size_ok); self.size_valid = size_ok

        # TTL Validation
        try: ttl_val = int(ttl_str); ttl_ok = 1 <= ttl_val <= 255
        except ValueError: ttl_ok = False
        self.ttl_input.setProperty("invalid", not ttl_ok); self.ttl_valid = ttl_ok

        # Timeout Validation
        try: timeout_val = float(timeout_str); timeout_ok = MIN_TIMEOUT_S <= timeout_val <= MAX_TIMEOUT_S
        except ValueError: timeout_ok = False
        self.timeout_input.setProperty("invalid", not timeout_ok); self.timeout_valid = timeout_ok

        # Check overall validity and update button state
        all_valid = target_ok and interval_ok and size_ok and ttl_ok and timeout_ok
        self.update_button_state(all_valid)

        # Re-polish inputs to apply/remove invalid style
        self.style().unpolish(self.target_input); self.style().polish(self.target_input)
        self.style().unpolish(self.interval_input); self.style().polish(self.interval_input)
        self.style().unpolish(self.size_input); self.style().polish(self.size_input)
        self.style().unpolish(self.ttl_input); self.style().polish(self.ttl_input)
        self.style().unpolish(self.timeout_input); self.style().polish(self.timeout_input)

        return all_valid

    def update_button_state(self, inputs_valid: bool = True):
        """Enable/disable button and inputs, update button appearance."""
        if self.test_running:
            self.start_stop_button.setText("[■] STOP")
            self.start_stop_button.setProperty("running", True)
            self.start_stop_button.setEnabled(True) # Always enabled when running
            # Disable all input fields while running
            self.target_input.setEnabled(False); self.interval_input.setEnabled(False)
            self.size_input.setEnabled(False); self.ttl_input.setEnabled(False)
            self.timeout_input.setEnabled(False)
        else:
            self.start_stop_button.setText("[▶] START")
            self.start_stop_button.setProperty("running", False)
            # Enable start button only if all inputs are valid
            self.start_stop_button.setEnabled(inputs_valid)
            # Enable all input fields when stopped
            self.target_input.setEnabled(True); self.interval_input.setEnabled(True)
            self.size_input.setEnabled(True); self.ttl_input.setEnabled(True)
            self.timeout_input.setEnabled(True)

        # Re-polish button to apply style changes
        self.style().unpolish(self.start_stop_button); self.style().polish(self.start_stop_button)

    @Slot()
    def on_input_submitted(self):
        """Handle Enter key press in any input field."""
        sender = self.sender(); all_valid = self.validate_inputs()
        # If Enter pressed in target field and inputs are valid, start the test
        if not self.test_running and all_valid and (sender == self.target_input):
             self.toggle_start_stop(); return
        # Move focus to the next input field
        if isinstance(sender, QLineEdit):
            if sender == self.target_input: self.interval_input.setFocus()
            elif sender == self.interval_input: self.size_input.setFocus()
            elif sender == self.size_input: self.ttl_input.setFocus()
            elif sender == self.ttl_input: self.timeout_input.setFocus()
            elif sender == self.timeout_input: self.start_stop_button.setFocus()

    @Slot()
    def toggle_start_stop(self):
        """Start or stop the ping thread based on current state."""
        if self.test_running: self.stop_ping()
        else:
            if self.validate_inputs(): self.start_ping()
            else: self.log_message("Cannot start: Invalid inputs.", "error")

    def start_ping(self):
        """Start the background ping worker thread."""
        if self.test_running: return
        target = self.target_input.text().strip()
        try: # Read and validate inputs
            interval = int(self.interval_input.text().strip()); interval = max(50, interval)
            size = int(self.size_input.text().strip()); size = max(0, min(65500, size))
            ttl = int(self.ttl_input.text().strip()); ttl = max(1, min(255, ttl))
            timeout = float(self.timeout_input.text().strip()); timeout = max(MIN_TIMEOUT_S, min(MAX_TIMEOUT_S, timeout))
        except ValueError: self.log_message("Invalid interval, size, TTL, or timeout.", "error"); return
        # Update input fields with potentially normalized values
        self.interval_input.setText(str(interval)); self.size_input.setText(str(size)); self.ttl_input.setText(str(ttl)); self.timeout_input.setText(format_timeout_value(timeout))

        # --- Get Target IP (for logging) ---
        target_ip = target # Assume target is IP initially
        try:
            # Resolve hostname to IP address (blocking call)
            resolved_ip = socket.gethostbyname(target)
            if resolved_ip != target: # Log if hostname was resolved
                 target_ip = f"{target} ({resolved_ip})"
            else: target_ip = resolved_ip # Target was already an IP
        except socket.gaierror:
             target_ip = f"{target} (Resolution Failed)" # Keep original target name if resolution fails
        except Exception:
             target_ip = f"{target} (Resolution Error)"
        # ---------------------------------

        # Reset stats and UI
        self.packets_sent = 0; self.packets_received = 0; self.min_time_ms = float('inf'); self.max_time_ms = float('-inf'); self.total_time_ms = 0.0
        self.ping_results.clear(); self.log_output.clear();
        self.update_stats_display(); # Update ping stats labels
        self.update_chart_display()

        # Log start message
        self.log_message(f"Pinging {target_ip} with ICMP Size={size} TTL={ttl} Interval={interval}ms Timeout={format_timeout_value(timeout)}s...", "info")
        self.test_running = True; self.start_time = time.monotonic()
        # Timer for CPU/Time is already running, just update display
        self.update_timed_stats()
        self.update_button_state(True)

        # Create and start worker thread
        self.ping_thread = QThread(); self.ping_worker = PingWorker(target, interval, size, ttl, timeout); self.ping_worker.moveToThread(self.ping_thread)
        self.ping_worker.result_ready.connect(self.handle_ping_result); self.ping_worker.status_update.connect(self.handle_status_update); self.ping_worker.finished.connect(self.ping_finished)
        self.ping_thread.started.connect(self.ping_worker.run); self.ping_thread.start()

    def stop_ping(self):
        """Stop the background ping worker thread."""
        if not self.test_running or self.ping_worker is None: return
        self.log_message("Stopping ping test...", "info")
        # Keep stats_update_timer running for CPU updates
        self.start_time = None # Reset start time for elapsed calculation
        if self.ping_worker: self.ping_worker.stop() # Signal worker to stop
        # Update display (will show 00:00:00 time)
        self.update_timed_stats()

    @Slot()
    def ping_finished(self):
        """Called when the worker thread's run() method finishes."""
        self.log_message("Ping worker finished.", "info")
        self.test_running = False
        # Keep stats_update_timer running for CPU updates
        self.start_time = None # Reset start time
        is_valid = self.validate_inputs(); self.update_button_state(is_valid) # Update UI state

        # Clean up the thread and worker objects
        if self.ping_thread is not None:
            self.ping_thread.quit(); self.ping_thread.wait(500) # Wait briefly for cleanup
        self.ping_thread = None; self.ping_worker = None

        # Log final summary statistics if any pings were sent
        if self.packets_sent > 0:
            lost = self.packets_sent - self.packets_received
            loss_perc = (lost / self.packets_sent * 100) if self.packets_sent > 0 else 0
            final_status = f"Stopped. Sent: {self.packets_sent}, Recv: {self.packets_received}, Lost: {lost} ({loss_perc:.0f}%)"
            self.handle_status_update(final_status) # Show final counts in log
            self.log_message(f"Ping statistics for {self.target_input.text().strip()}:", "info")
            self.log_message(f"  Packets: Sent = {self.packets_sent}, Received = {self.packets_received}, Lost = {lost} ({loss_perc:.0f}% loss)", "info")
            min_str = format_ping_time(self.min_time_ms if self.min_time_ms != float('inf') else None)
            max_str = format_ping_time(self.max_time_ms if self.max_time_ms != float('-inf') else None)
            avg_val = (self.total_time_ms / self.packets_received) if self.packets_received > 0 else None
            avg_str = format_ping_time(avg_val)
            self.log_message(f"Approximate round trip times in milli-seconds:", "info")
            self.log_message(f"    Minimum = {min_str}ms, Maximum = {max_str}ms, Average = {avg_str}ms", "info")
        else: self.handle_status_update("Stopped.")
        # Reset time display after logging summary
        self.update_timed_stats()

    @Slot(float, object, object)
    def handle_ping_result(self, timestamp, time_ms_or_err, error_type):
        """Process ping results received from the worker thread."""
        # Ignore results that arrive after the test has been stopped
        if not self.test_running and self.packets_sent > 0: return

        self.packets_sent += 1 # Increment sent count for every result received
        current_target = self.target_input.text().strip()
        log_msg = ""; log_color = "#cccccc" # Default log color

        # Determine if the result is an error
        is_zero_ms = isinstance(time_ms_or_err, (int, float)) and abs(time_ms_or_err) < 1e-6
        is_error = time_ms_or_err is None or time_ms_or_err is False or \
                   (is_zero_ms and current_target != "localhost" and not current_target.startswith("127."))

        if not is_error and isinstance(time_ms_or_err, (int, float)) and math.isfinite(time_ms_or_err):
            # --- Successful Ping ---
            time_ms = time_ms_or_err
            self.packets_received += 1; self.total_time_ms += time_ms
            self.min_time_ms = min(self.min_time_ms, time_ms); self.max_time_ms = max(self.max_time_ms, time_ms)
            log_msg = f"Reply from {current_target}: time={format_ping_time(time_ms)}ms"
            if time_ms > 100: log_color = "#ff4444" # Red for high latency
            elif time_ms > 50: log_color = "#ffff00" # Yellow for medium latency
            else: log_color = "#00ff00" # Green for low latency
            self.ping_results.append((timestamp, time_ms)) # Store successful result
        else:
            # --- Ping Error/Timeout ---
            log_msg = "General failure."; log_color = "#ff4444" # Default error message/color
            if error_type == "timeout" or time_ms_or_err is None: log_msg = "Request timed out."; log_color = "#ffaa00" # Orange for timeouts
            elif time_ms_or_err is False or is_zero_ms or error_type:
                log_msg = f"Destination host unreachable." # Default unreachable message
                if error_type == "host_unknown": log_msg = f"Ping request could not find host {current_target}."
                elif error_type == "ttl_expired": log_msg = "TTL expired in transit."
                elif error_type == "permission_error": log_msg = "Permission denied for ICMP."
                elif error_type == "ping_error": log_msg = "Ping error (check target/network)."
                elif error_type == "unk_error": log_msg = "Unknown worker error."
                log_color = "#ff4444" # Red for errors
            self.ping_results.append((timestamp, None)) # Store error result as None

        # Log the message and update UI
        self.log_message(log_msg, color=log_color)
        self.update_stats_display(); # Update ping stats (Sent, Recv, Lost, Min, Max, Avg)
        self.update_chart_display()

    @Slot(str)
    def handle_status_update(self, status):
        """Log status messages received from the worker thread."""
        self.log_message(f"Status: {status}", "info")

    def log_message(self, message, type="info", color="#cccccc"):
        """Append message to the log QTextEdit with timestamp and color."""
        timestamp = datetime.datetime.now().strftime("%H:%M:%S")
        formatted_message = f'<span style="color:{color};">[{timestamp}] {message}</span>'
        self.log_output.append(formatted_message)
        # Auto-scroll log to the bottom
        self.log_output.verticalScrollBar().setValue(self.log_output.verticalScrollBar().maximum())

    def update_stats_display(self):
        """Update the ping statistics labels (Sent, Recv, Lost, Min, Max, Avg)."""
        # Does NOT update Time or CPU - those are handled by update_timed_stats
        lost = self.packets_sent - self.packets_received
        loss_perc = (lost / self.packets_sent * 100) if self.packets_sent > 0 else 0
        avg_time_ms = (self.total_time_ms / self.packets_received) if self.packets_received > 0 else None
        self.sent_label.setText(f"Sent: {self.packets_sent}")
        self.received_label.setText(f"Received: {self.packets_received}")
        self.lost_label.setText(f"Lost: {lost} ({loss_perc:.0f}%)")
        self.min_label.setText(f"Min: {format_ping_time(self.min_time_ms if self.min_time_ms != float('inf') else None)} ms")
        self.max_label.setText(f"Max: {format_ping_time(self.max_time_ms if self.max_time_ms != float('-inf') else None)} ms")
        self.avg_label.setText(f"Avg: {format_ping_time(avg_time_ms)} ms")

    @Slot()
    def update_timed_stats(self):
        """Update the elapsed time and CPU usage labels, called by the timer."""
        # --- Update Elapsed Time (Conditional) ---
        elapsed_seconds = 0.0
        if self.test_running and self.start_time is not None:
            # Only calculate elapsed time if the test is actually running
            elapsed_seconds = time.monotonic() - self.start_time
            self.time_label.setText(f"Time: {format_elapsed_time(elapsed_seconds)}")
        else:
            # Reset time display if test is not running
            self.time_label.setText("Time: 00:00:00")

        # --- Update CPU Usage (Always) ---
        if PSUTIL_AVAILABLE:
            try:
                # Get overall CPU percentage. interval=None makes it non-blocking.
                cpu_percent = psutil.cpu_percent(interval=None)
                self.cpu_label.setText(f"CPU: {cpu_percent:.1f} %")
            except Exception as e:
                # Handle potential errors getting CPU usage
                self.cpu_label.setText("CPU: Error")
                # Log error only once to avoid flooding
                if not hasattr(self, '_cpu_error_logged') or not self._cpu_error_logged:
                    self.log_message(f"Error getting CPU usage: {e!r}", "error")
                    self._cpu_error_logged = True # Set flag to prevent repeated logs
        else:
            # psutil not available
            self.cpu_label.setText("CPU: N/A")


    def update_chart_display(self):
        """Update the PyQtGraph chart with latency bars."""
        results_to_draw = list(self.ping_results); num_bars = len(results_to_draw)
        # Handle empty chart case
        if num_bars == 0:
            self.bar_graph.setOpts(x=[], height=[], brushes=[])
            self.plot_widget.setXRange(0 - 0.5, max(MIN_VISIBLE_BARS, INITIAL_VISIBLE_BARS) - 0.5, padding=0.01)
            self.plot_widget.setYRange(0, INITIAL_CHART_MAX_Y_MS, padding=0.05)
            self.left_axis.setTicks(generate_ticks(0, INITIAL_CHART_MAX_Y_MS)); return

        # Prepare data for BarGraphItem
        x_values = list(range(num_bars)); heights = []; brushes = []

        # --- Dynamic Y-Axis Scaling ---
        max_visible_ping = 0
        finite_times = [t for _, t in results_to_draw if t is not None and isinstance(t, (int, float)) and math.isfinite(t)]
        if finite_times: max_visible_ping = max(finite_times)
        else: max_visible_ping = self.current_chart_max_y if self.packets_sent > 0 else INITIAL_CHART_MAX_Y_MS
        target_max_y = max(INITIAL_CHART_MAX_Y_MS, max_visible_ping * 1.1)
        # Round the target max Y to a nice value
        if target_max_y <= 150: potential_new_max_y = math.ceil(target_max_y / 10.0) * 10.0
        elif target_max_y <= 300: potential_new_max_y = math.ceil(target_max_y / 20.0) * 20.0
        elif target_max_y <= 750: potential_new_max_y = math.ceil(target_max_y / 50.0) * 50.0
        elif target_max_y <= 1500: potential_new_max_y = math.ceil(target_max_y / 100.0) * 100.0
        else: potential_new_max_y = math.ceil(target_max_y / 200.0) * 200.0
        new_max_y = min(MAX_CHART_Y_MS, max(INITIAL_CHART_MAX_Y_MS / 2, potential_new_max_y))
        # Update Y range and ticks only if changed significantly
        if abs(new_max_y - self.current_chart_max_y) > 1e-6:
            self.current_chart_max_y = new_max_y
            self.plot_widget.setYRange(0, self.current_chart_max_y, padding=0.05)
            self.left_axis.setTicks(generate_ticks(0, self.current_chart_max_y))

        # Define brushes (colors)
        green_brush = pg.mkBrush(color=(0, 255, 0)); yellow_brush = pg.mkBrush(color=(255, 255, 0)); red_brush = pg.mkBrush(color=(255, 0, 0))
        # Populate heights and brushes lists
        for ts, time_ms in results_to_draw:
            if time_ms is None: heights.append(0); brushes.append(red_brush) # Error/Timeout
            else: # Successful ping
                heights.append(time_ms)
                if time_ms > 100: brushes.append(red_brush)
                elif time_ms > 50: brushes.append(yellow_brush)
                else: brushes.append(green_brush)

        # Update the BarGraphItem
        self.bar_graph.setOpts(x=x_values, height=heights, width=CHART_BAR_WIDTH, brushes=brushes)

        # --- Dynamic X-Axis Scrolling ---
        try:
            plot_pixel_width = self.plot_widget.width()
            if plot_pixel_width <= 0: view_width = MIN_VISIBLE_BARS # Fallback
            else:
                bar_pixel_width_estimate = max(1, DESIRED_BAR_PIXEL_WIDTH)
                view_width = max(MIN_VISIBLE_BARS, int(plot_pixel_width / bar_pixel_width_estimate))
                view_width = min(view_width, MAX_HISTORY_BUFFER)
        except Exception: view_width = INITIAL_VISIBLE_BARS # Fallback
        # Calculate visible range and update X-axis
        start_x = max(0, num_bars - view_width); end_x = max(view_width, num_bars)
        self.plot_widget.setXRange(start_x - 0.5, end_x - 0.5, padding=0.01)

    def handle_chart_mouse_move(self, pos):
        """Show tooltip when hovering over chart bars."""
        try:
            vb = self.plot_widget.getViewBox()
            # Check if mouse is within the plot area
            if not vb or not vb.scene() or not vb.sceneBoundingRect().contains(pos):
                  self.chart_tooltip_item.hide(); return

            # Map scene coordinates to view coordinates
            mouse_point = vb.mapSceneToView(pos); x_coord = mouse_point.x(); y_coord = mouse_point.y()
            # Find the nearest bar index
            bar_index = int(round(x_coord))

            # Get current bar data
            current_x_data = self.bar_graph.opts.get('x', [])
            if not isinstance(current_x_data, list) or not current_x_data:
                 self.chart_tooltip_item.hide(); return # Hide if no bars

            # Check if the index is valid
            if 0 <= bar_index < len(self.ping_results):
                timestamp, time_ms = self.ping_results[bar_index] # Get data
                bar_x = bar_index; bar_h = time_ms if time_ms is not None else 0; bar_width_half = CHART_BAR_WIDTH / 2.0
                # Check if mouse is over the bar
                is_over_bar = (bar_x - bar_width_half <= x_coord <= bar_x + bar_width_half and
                               (0 <= y_coord <= bar_h if bar_h > 0 else 0 <= y_coord <= self.current_chart_max_y * 0.05) )

                if is_over_bar:
                    # Format tooltip content
                    if time_ms is not None:
                        original_seq = (self.packets_sent - len(self.ping_results) + bar_index + 1) if self.packets_sent >= len(self.ping_results) else bar_index + 1
                        tooltip_content = f"{format_ping_time(time_ms)} ms (Seq {original_seq})"
                    else: tooltip_content = "Error/Timeout"
                    tooltip_html = f'<div style="background-color:rgba(40, 40, 40, 0.85); color:#DDD; padding: 3px 5px; border-radius: 3px;">{tooltip_content}</div>'
                    self.chart_tooltip_item.setHtml(tooltip_html)
                    # Position and show tooltip
                    tooltip_pos_x = mouse_point.x(); tooltip_pos_y = mouse_point.y()
                    self.chart_tooltip_item.setAnchor((0.5, 1.0)); self.chart_tooltip_item.setPos(tooltip_pos_x, tooltip_pos_y); self.chart_tooltip_item.show()
                    return # Exit after showing
            # Hide tooltip if not over a valid bar
            self.chart_tooltip_item.hide()
        except Exception as e:
             # Log errors during tooltip handling but don't crash
             print(f"Error in handle_chart_mouse_move: {e}", file=sys.stderr)
             try: self.chart_tooltip_item.hide() # Try to hide tooltip on error
             except: pass

    def closeEvent(self, event):
        """Ensure worker thread and timer are stopped when window closes."""
        # Stop the stats timer first
        self.stats_update_timer.stop()
        self.stop_ping() # Signal the worker thread to stop (if running)
        event.accept() # Allow the window to close


# --- Main Execution ---
if __name__ == "__main__":
    app = QApplication(sys.argv)
    # --- Dark Theme Palette ---
    palette = QPalette(); palette.setColor(QPalette.ColorRole.Window, QColor(45, 45, 45)); palette.setColor(QPalette.ColorRole.WindowText, QColor(220, 220, 220)); palette.setColor(QPalette.ColorRole.Base, QColor(25, 25, 25)); palette.setColor(QPalette.ColorRole.AlternateBase, QColor(53, 53, 53)); palette.setColor(QPalette.ColorRole.ToolTipBase, QColor(50,50,50)); palette.setColor(QPalette.ColorRole.ToolTipText, QColor(220,220,220)); palette.setColor(QPalette.ColorRole.Text, QColor(0, 255, 0)); palette.setColor(QPalette.ColorRole.Button, QColor(53, 53, 53)); palette.setColor(QPalette.ColorRole.ButtonText, QColor(220, 220, 220)); palette.setColor(QPalette.ColorRole.BrightText, Qt.GlobalColor.red); palette.setColor(QPalette.ColorRole.Link, QColor(42, 130, 218)); palette.setColor(QPalette.ColorRole.Highlight, QColor(42, 130, 218)); palette.setColor(QPalette.ColorRole.HighlightedText, Qt.GlobalColor.black)
    palette.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.Text, QColor(127, 127, 127)); palette.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.ButtonText, QColor(127, 127, 127)); palette.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.Base, QColor(40, 40, 40)); palette.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.Button, QColor(40, 40, 40))
    app.setPalette(palette)

    # --- Create and Show Window ---
    window = KingPingAppWindow()
    # The window title is now set by the immersive tag's title attribute
    # window.setWindowTitle("KINGPING v1.3") # This line is effectively overridden
    window.apply_stylesheet() # Apply QSS stylesheet
    window.resize(850, 550) # Set initial size
    window.show()

    # --- Start Event Loop ---
    sys.exit(app.exec())
