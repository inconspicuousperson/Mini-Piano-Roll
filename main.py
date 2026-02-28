import subprocess
import os
import pygame
import ctypes
from ctypes import wintypes 
import numpy as np
import sounddevice as sd
import scipy
from scipy import signal
import threading
import queue
import tkinter as tk
from tkinter import filedialog
import time
import math
import random

current_file_path = None

SELECTED_PART = 0
UI_SCALE = 2  # or 1 for compact mode
GRID_SIZE = int(12 * UI_SCALE)
SUB_BUTTON_WIDTH = int(36 * UI_SCALE)
SUB_BUTTON_HEIGHT = int(24 * UI_SCALE)

TEMPO = 72  # BPM
TUNING_A = 440  # Hz
TUNING_SYSTEM = "equal temperament"  # "equal temperament" or "well temperament" or "ptolemaic" (five limit) or "harmonic series"

editing_row = None          # None | 4 (Tempo) | 5 (A=)
edit_value_str = ""
edit_cursor_pos = 0
edit_sel_start = None       # None = no selection, else start index
edit_sel_end = None         # end index (exclusive), always sel_start <= sel_end
edit_blink_timer = 0.0
edit_blink_interval = 0.6   # seconds
edit_blink_visible = True

is_playing = False
playback_start_time = 0.0
playback_position = 0.0
current_stream = None
current_renderer = None
SAMPLE_RATE = 96000
playback_stop_event = threading.Event()
render_queue = queue.Queue(maxsize=60)
playback_session_id = 0

subdivision_mode_names = ["quarter", "eighth", "sixteenth", "triplet", "sextuplet", "quintuplet", "seven five", "twelvetuplet"]
subdivision_modes = {
    "quarter":       [0],                         # 1 note per beat
    "eighth":        [0, 6],                      # 2 notes per beat
    "sixteenth":     [0, 3, 6, 9],                # 4 notes per beat
    "triplet":       [0, 4, 8],                   # 3 notes per beat
    "sextuplet":     [0, 2, 4, 6, 8, 10],         # 6 notes per beat
    "quintuplet":    [0, 2, 5, 7, 10],            # 5 notes per beat (2,3,2,3,2 twelfths)
    "seven five":    [0, 7],                      # 2 notes per beat (7/12, 5/12)
    "twelvetuplet":  list(range(12))              # 12 notes per beat
}
scaled_modes = {
    mode: [s * UI_SCALE for s in values]
    for mode, values in subdivision_modes.items()
}
subdivision_modes = scaled_modes
selected_mode_index = 0  # default to first button

SCROLL_STEP = 1

ZOOM_LEVELS = [GRID_SIZE // 2, GRID_SIZE, GRID_SIZE * 2, GRID_SIZE * 3, GRID_SIZE * 4, GRID_SIZE * 8] # considering adding more zoom levels...
zoom_index = ZOOM_LEVELS.index(GRID_SIZE)
horizontal_zoom = ZOOM_LEVELS[zoom_index]

last_mouse_x = None
last_mouse_y = None

dragging = False
drag_offset_x = 0
drag_offset_y = 0

DRAG_ZONE_HEIGHT = int(21 * UI_SCALE)
DRAG_ZONE_LEFT = int(147 * UI_SCALE)     # pixels from the left edge
DRAG_ZONE_RIGHT = int(59 * UI_SCALE)

# Set up the window
MIDDLE_C_ROW = 60
VISIBLE_ROWS = 21  # number of rows shown at once
TOTAL_ROWS = 112
scroll_y = (MIDDLE_C_ROW - VISIBLE_ROWS // 2) * GRID_SIZE
MAX_SCROLL_Y = (TOTAL_ROWS - VISIBLE_ROWS) * GRID_SIZE

# Grid settings
GRID_X = int(42 * UI_SCALE)  # starting x inside UI.png
GRID_Y = int(90 * UI_SCALE)   # starting y inside UI.png
GRID_WIDTH = int(336 * UI_SCALE)
GRID_HEIGHT = int((VISIBLE_ROWS) * GRID_SIZE)

FULL_GRID_WIDTH = int(336 * 4 * UI_SCALE)  # actual grid width
scroll_x = 0  # starting scroll position
FONT_SIZE = int(12 * UI_SCALE)
BUTTON_SIZE = (int(80 * UI_SCALE), int(24 * UI_SCALE))

notes = []
selected_note = None
last_selected_note = None
copied_note_duration = None
copied_note_pitch = None

file_menu_open = False
menu_was_open = False
hovered_menu_item = None

tuning_menu_open = False
hovered_tuning_item = None
pending_tuning_system = None

tuning_system_names = ["equal temperament", "well temperament", "ptolemaic", "harmonic series"]
tuning_display_names = ["Equal Temperament", "Well Temperament", "Ptolemaic", "Harmonic Series"]

# user32 = ctypes.windll.user32                     # some windows stuff
# screen_width = user32.GetSystemMetrics(0)
# screen_height = user32.GetSystemMetrics(1)

def get_screen_size():
    try:
        output = subprocess.check_output(['xrandr']).decode('utf-8')
        for line in output.split('\n'):
            if ' connected primary' in line or ' connected' in line:
                if 'x' in line:
                    parts = line.split()
                    for part in parts:
                        if 'x' in part and '+' in part:
                            resolution = part.split('+')[0]
                            width, height = resolution.split('x')
                            return int(width), int(height)
    except:
        pass
    # Fallback to pygame's display info
    info = pygame.display.Info()
    return info.current_w, info.current_h

taskbar_height = 48  # Approximate, adjust if needed

WIDTH = GRID_SIZE * 32
HEIGHT = int(372 * UI_SCALE) # VISIBLE_ROWS * GRID_SIZE

pygame.init()
screen_width, screen_height = get_screen_size()
raw_ui_image = pygame.image.load("images/UI linux.png")

pos_x = (screen_width - WIDTH) // 2
pos_y = ((screen_height - taskbar_height - HEIGHT) / 2)

# Set window position before initializing Pygame
os.environ['SDL_VIDEO_WINDOW_POS'] = f"{pos_x},{pos_y}"

# Scale the image if needed
if UI_SCALE != 1:
    raw_ui_image = pygame.transform.scale(
        raw_ui_image,
        (raw_ui_image.get_width() * UI_SCALE, raw_ui_image.get_height() * UI_SCALE)
    )

WIDTH, HEIGHT = raw_ui_image.get_width(), raw_ui_image.get_height()

pygame.quit()
pygame.init()

# Initialize Pygame
pygame.init()
# screen = pygame.display.set_mode((WIDTH, HEIGHT), pygame.NOFRAME) 	<-- windows 11
screen = pygame.display.set_mode((WIDTH, HEIGHT))
ui_image = raw_ui_image.convert()
pygame.display.set_caption("")

# piano stuff
piano_image = pygame.image.load("images/piano.png").convert_alpha()
piano_image = pygame.transform.scale(
    piano_image,
    (int(36 * UI_SCALE), int(144 * UI_SCALE))
)
C4_image = pygame.image.load("images/C4.png").convert()
C4_image.set_colorkey((255, 255, 255))  # Make white transparent
C4_image = pygame.transform.scale(C4_image, (
    int(C4_image.get_width() * UI_SCALE),
    int(C4_image.get_height() * UI_SCALE)
))

piano_width = piano_image.get_width()
piano_height = piano_image.get_height()  # ✅ Now it's defined

grid_pixel_height = GRID_HEIGHT * GRID_SIZE
num_octaves = (grid_pixel_height + piano_height - 1) // piano_height  # round up

piano_surface = pygame.Surface((piano_width, GRID_HEIGHT))

piano_x = int(6 * UI_SCALE)  # left edge of the red area
middle_c_bottom = GRID_Y + MIDDLE_C_ROW * GRID_SIZE
start_y = middle_c_bottom - piano_height

grid_surface = pygame.Surface((GRID_WIDTH, GRID_HEIGHT))
scaled_grid_surface = pygame.transform.scale(grid_surface, (GRID_WIDTH * UI_SCALE, GRID_HEIGHT * UI_SCALE))
screen.blit(scaled_grid_surface, (GRID_X * UI_SCALE, GRID_Y * UI_SCALE))
full_grid_surface = pygame.Surface((FULL_GRID_WIDTH, GRID_HEIGHT))

def ui_locked():
    return file_menu_open or editing_row is not None

def get_max_scroll_x():
    """Calculate maximum scroll based on rightmost note + buffer"""
    if notes:
        rightmost_end = max(note.end_col() for note in notes)
        # Convert to pixels and add 100 beats of buffer
        max_position = ((rightmost_end + 1200) * horizontal_zoom) / 12  # 1200 twelfths = 100 beats
    else:
        # Empty song: allow at least 100 beats
        max_position = 100 * horizontal_zoom

    return max(max_position - GRID_WIDTH, 0)

# Load a sound (make sure you have a .wav file in the same folder)
sound = pygame.mixer.Sound("sounds/note.wav")

def update_playback_scroll():
    """Update scroll position based on playback time"""
    global scroll_x

    if not is_playing:
        return
    # Calculate max scroll - left edge can reach end of song
    if notes:
        last_note_end = max(note.end_col() for note in notes)  # in twelfths
        # Round up to next quarter note
        last_note_end_rounded = math.ceil(last_note_end / 12) * 12
        last_note_end_pixels = (last_note_end_rounded * horizontal_zoom) / 12
        max_scroll_for_left_edge = last_note_end_pixels  # Left edge at end
        absolute_max = get_max_scroll_x()
        max_scroll = min(max_scroll_for_left_edge, absolute_max)
    else:
        max_scroll = get_max_scroll_x()
    # Don't use early return - let it keep scrolling!
    start_quarter = playback_position // 12
    start_scroll = start_quarter * horizontal_zoom

    elapsed = time.time() - playback_start_time
    seconds_per_quarter = 60 / TEMPO
    quarters_played = elapsed / seconds_per_quarter
    current_quarter = start_quarter + quarters_played
    target_scroll_x = int(current_quarter) * horizontal_zoom

    scroll_x = max(start_scroll, min(target_scroll_x, max_scroll))

def stop_playback():
    """Stop playback and cleanup"""
    global is_playing, current_stream, current_renderer

    print(f"DEBUG: stop_playback() called, is_playing was {is_playing}")

    if not is_playing:
        print("DEBUG: Early return - already stopped!")
        return

    playback_stop_event.set()
    print("DEBUG: Stop event set")

    # Wait for stream to stop
    if current_stream:
        print("DEBUG: Stopping stream...")
        try:
            current_stream.stop()
            current_stream.close()
        except Exception as e:
            print(f"DEBUG: Error stopping stream: {e}")
        current_stream = None

    # Wait for renderer thread
    if current_renderer:
        print("DEBUG: Waiting for renderer thread...")
        current_renderer.join(timeout=0.5)
        if current_renderer.is_alive():
            print("DEBUG: WARNING - renderer thread didn't stop in time")
        current_renderer = None

    # Clear queue
    cleared = 0
    if render_queue is not None:  # Safety check
        while not render_queue.empty():
            try:
                render_queue.get_nowait()
                cleared += 1
            except queue.Empty:
                break

    # Small delay to let things settle
    time.sleep(0.5)

    is_playing = False
    playback_stop_event.clear()

def on_playback_finished(session_id):
    """Called when playback finishes naturally"""
    global is_playing
    is_playing = False

def play_song_streaming(notes, tempo, tuning_a, tuningsystem, sample_rate=SAMPLE_RATE):
    global is_playing, playback_start_time, playback_position, current_stream, current_renderer, playback_session_id, render_queue

    playback_session_id += 1
    session = playback_session_id

    if is_playing:
        print("Already playing!")
        return

    # Force cleanup of any lingering resources
    if current_stream is not None:
        print("DEBUG: Cleaning up old stream...")
        try:
            current_stream.stop()
            current_stream.close()
        except:
            pass
        current_stream = None

    if current_renderer is not None:
        print("DEBUG: Cleaning up old renderer...")
        current_renderer = None

    render_queue = queue.Queue(maxsize=20)
    print(f"DEBUG: Created fresh queue for session {session}")

    if not notes:
        print("No notes to play")
        return

    is_playing = True
    playback_stop_event.clear()

    # Calculate timing
    seconds_per_quarter = 60 / tempo
    seconds_per_twelfth = seconds_per_quarter / 12

    # Start playback from current scroll position
    start_quarter = scroll_x // horizontal_zoom
    start_position = start_quarter * 12  # in twelfths
    playback_position = start_position

    # Pre-calculate note data - only include notes that haven't finished yet
    note_data = []
    for note in notes:
        # Skip notes that have already ended before our start position
        if note.end_col() <= start_position:
            continue

        freq = note_to_frequency(note.pitch, tuning_a, tuningsystem)
        # Adjust start time relative to our playback start
        start_time = (note.start_col - start_position) * seconds_per_twelfth
        duration = note.duration * seconds_per_twelfth
        note_data.append({
            'freq': freq,
            'start': start_time,
            'duration': duration,
            'pitch': note.pitch
        })

    print(f"DEBUG: Starting from position {start_position} twelfths, playing {len(note_data)} notes")

    if note_data:
        max_end_time = max(nd['start'] + nd['duration'] for nd in note_data)
        total_duration = max_end_time + 0.7
    else:
        total_duration = 0.7
        print("No notes to play from this position")
        is_playing = False
        return

    chunk_size = 8192
    total_samples = int(total_duration * sample_rate)

    def render_thread():
        """Renders audio chunks ahead of playback"""
        global render_queue
        my_session = session  # Capture the session ID
        sample_offset = 0

        while sample_offset < total_samples and not playback_stop_event.is_set():
            # print(f"DEBUG Session {my_session}: Rendering chunk at offset {sample_offset}")  # ADD THIS
            chunk_start = time.time()

            # Check again before expensive render
            if playback_stop_event.is_set():
                print("DEBUG: Renderer stopping early")
                break

            # Generate chunk
            chunk_start_time = sample_offset / sample_rate
            chunk_end_time = (sample_offset + chunk_size) / sample_rate

            chunk = np.zeros(chunk_size)

            # Add all active notes to this chunk
            notes_in_chunk = 0  # <-- ADD THIS HERE
            for nd in note_data:
                if nd['start'] + nd['duration'] < chunk_start_time:
                    continue
                if nd['start'] > chunk_end_time:
                    continue

                notes_in_chunk += 1  # <-- ADD THIS HERE

                # Calculate time array for this chunk
                t = np.linspace(chunk_start_time, chunk_end_time, chunk_size, endpoint=False)
                note_t = t - nd['start']

                # Only generate where note is active
                active_mask = (note_t >= 0) & (note_t < nd['duration'])
                if not np.any(active_mask):
                    continue

                # Generate note audio
                wave = generate_note_for_chunk(nd['freq'], note_t[active_mask], nd['duration'], sample_rate)
                chunk[active_mask] += wave

            # Clip
            chunk = np.clip(chunk, -0.8, 0.8)

            # Put in queue
            render_queue.put(chunk)
            sample_offset += chunk_size

            chunk_time = time.time() - chunk_start

        render_queue.put(None)

    # Playback callback
    current_chunk = [None]
    chunk_position = [0]

    def audio_callback(outdata, frames, time_info, status):
        """Feeds pre-rendered chunks to output"""
        global render_queue
        if status:
            print(f"DEBUG: Audio status: {status}")

        # Check for stop request
        if playback_stop_event.is_set():
            elapsed = time.time() - playback_start_time
            print(f"DEBUG: Audio callback stopping due to stop event at {elapsed:.2f}s")
            outdata[:] = 0
            raise sd.CallbackStop()

        output_pos = 0

        while output_pos < frames:
            # Get next chunk if needed
            if current_chunk[0] is None or chunk_position[0] >= len(current_chunk[0]):
                try:
                    current_chunk[0] = render_queue.get(timeout=1.0)
                    chunk_position[0] = 0

                    if current_chunk[0] is None:  # End of song
                        elapsed = time.time() - playback_start_time
                        print(f"DEBUG: Audio callback got None at {elapsed:.2f}s elapsed")
                        outdata[output_pos:] = 0
                        raise sd.CallbackStop()
                except queue.Empty:
                    elapsed = time.time() - playback_start_time
                    print(f"DEBUG: Buffer underrun at {elapsed:.2f}s!")
                    outdata[output_pos:] = 0
                    raise sd.CallbackStop()

            # Copy from chunk to output
            remaining_in_chunk = len(current_chunk[0]) - chunk_position[0]
            remaining_in_output = frames - output_pos
            samples_to_copy = min(remaining_in_chunk, remaining_in_output)

            outdata[output_pos:output_pos + samples_to_copy, 0] = \
                current_chunk[0][chunk_position[0]:chunk_position[0] + samples_to_copy]

            chunk_position[0] += samples_to_copy
            output_pos += samples_to_copy

    # Start rendering thread
    renderer = threading.Thread(target=render_thread, daemon=True)
    renderer.start()

    # Give renderer time to buffer
    time.sleep(0.5)

    playback_start_time = time.time()

    stream = sd.OutputStream(
        samplerate=sample_rate,
        channels=1,
        callback=audio_callback,
        blocksize=2048,
        finished_callback=lambda: on_playback_finished(session)
    )

    current_stream = stream
    current_renderer = renderer

    stream.start()

def generate_note_for_chunk(frequency, t, full_duration, sample_rate=SAMPLE_RATE):
    """Generate note audio - uses full 100 harmonics since it's pre-rendered"""
    phase_offset = random.uniform(0, 2 * np.pi)
    if len(t) == 0:
        return np.zeros(0)
    
    # Fade in/out
    fade_in_time = 0.015
    fade_out_time = 0.01
    
    envelope = np.ones_like(t)
    fade_in_mask = (t >= 0) & (t < fade_in_time)
    envelope[fade_in_mask] = t[fade_in_mask] / fade_in_time
    
    fade_out_mask = (t > full_duration - fade_out_time) & (t <= full_duration)
    envelope[fade_out_mask] = (full_duration - t[fade_out_mask]) / fade_out_time
    
    envelope[t < 0] = 0
    envelope[t > full_duration] = 0
    
    # Full quality - 100 harmonics
    max_harmonic = int((sample_rate / 2) / frequency) - 1
    
    square = np.zeros_like(t)
    for n in range(1, min(max_harmonic, 5), 2):
        square += (1 / n) * np.sin(2 * np.pi * frequency * n * t + phase_offset)

    wave = square
    wave *= envelope
    
    decay = np.exp(-0.2 * t)
    wave *= decay
    wave *= 0.3

    nyquist = sample_rate / 2
    cutoff = 8000 / nyquist
    b, a = signal.butter(2, cutoff, btype='low')
    wave = signal.filtfilt(b, a, wave)
    
    return wave

def play_song(notes, tempo, tuning_a, tuningsystem, sample_rate=SAMPLE_RATE):
    """Play all notes in the song"""
    global is_playing
    
    if is_playing:
        return
    
    if not notes:
        print("No notes to play")
        return
    
    is_playing = True
    
    # Find the total length needed in twelfths
    max_end = max(note.end_col() for note in notes)
    
    # Convert tempo to seconds per twelfth
    # tempo is in BPM (quarter notes per minute)
    # 1 quarter note = 12 twelfths
    seconds_per_quarter = 60 / tempo
    seconds_per_twelfth = seconds_per_quarter / 12
    
    # Total duration in seconds
    total_duration = max_end * seconds_per_twelfth
    
    # Create empty audio buffer
    padding_before = int(0.2 * sample_rate)  # 0.5 seconds before
    padding_after = int(0.5 * sample_rate)   # 0.5 seconds after
    total_samples = int(total_duration * sample_rate) + padding_before + padding_after
    mix = np.zeros(total_samples)
    
    # Add each note to the mix
    for note in notes:
        freq = note_to_frequency(note.pitch, tuning_a, tuningsystem)
        note_duration = note.duration * seconds_per_twelfth
        note_start_time = note.start_col * seconds_per_twelfth
        
        # Generate the note
        wave = generate_note(freq, note_duration, sample_rate)
        
        # Add to mix at the correct position (offset by padding_before)
        start_sample = int(note_start_time * sample_rate) + padding_before
        end_sample = start_sample + len(wave)
        
        print(f"  -> samples: {start_sample} to {end_sample}")
        
        if end_sample <= len(mix):
            mix[start_sample:end_sample] += wave
            region_peak = np.max(np.abs(mix[start_sample:end_sample]))
        else:
            # Clip if note extends beyond total duration
            mix[start_sample:] += wave[:len(mix) - start_sample]
        
    print(f"  -> mix length: {len(mix)}, end_sample: {end_sample}, fits: {end_sample <= len(mix)}")    

    peak = np.max(np.abs(mix))
    if peak > 0:
        mix = mix / peak * 0.8  # normalize to 80% volume
    # mix = np.tanh(mix) * 0.8

    # Play
    sd.play(mix, samplerate=sample_rate)
    sd.wait()
    
    is_playing = False  # Reset when done

def generate_note_chunk(frequency, t, full_duration, sample_rate=96000):
    """Generate waveform for a chunk of time"""
    phase_offset = random.uniform(0, 2 * np.pi)
    if len(t) == 0:
        return np.zeros(0)
    
    # Calculate fade-in/out times
    fade_in_time = 0.015  # 15ms
    fade_out_time = 0.01  # 10ms
    
    # Vectorized envelope calculation
    envelope = np.ones_like(t)
    
    # Fade in (vectorized)
    fade_in_mask = (t >= 0) & (t < fade_in_time)
    envelope[fade_in_mask] = t[fade_in_mask] / fade_in_time
    
    # Fade out (vectorized)
    fade_out_mask = (t > full_duration - fade_out_time) & (t <= full_duration)
    envelope[fade_out_mask] = (full_duration - t[fade_out_mask]) / fade_out_time
    
    # Before/after note (vectorized)
    envelope[t < 0] = 0
    envelope[t > full_duration] = 0
    
    # Generate harmonics (unchanged)
    max_harmonic = int((sample_rate / 2) / frequency) - 1
    
    square = np.zeros_like(t)
    for n in range(1, min(max_harmonic, 5), 2):
        square += (1 / n) * np.sin(2 * np.pi * frequency * n * t + phase_offset)

    wave = square
    wave *= envelope
    
    # Decay
    decay = np.exp(-0.2 * t)
    wave *= decay
    wave *= 0.3

    nyquist = sample_rate / 2
    cutoff = 8000 / nyquist
    b, a = signal.butter(2, cutoff, btype='low')
    wave = signal.filtfilt(b, a, wave)
    
    return wave

def sine_wave(frequency, t):
    return np.sin(2 * np.pi * frequency * t)

def square_wave(frequency, t):
    return np.sign(np.sin(2 * np.pi * frequency * t))

def triangle_wave(frequency, t):
    return 2 * np.abs(2 * (t * frequency % 1) - 1) - 1

def sawtooth_wave(frequency, t):
    return 2 * (t * frequency % 1) - 1

def poly_blep(t, dt):                                                               # polyblep stuff
    # t: phase [0, 1)
    # dt: phase increment per sample
    if t < dt:
        return (t / dt) - 1.0
    elif t > 1.0 - dt:
        return (t - 1.0) / dt + 1.0
    else:
        return 0.0
        
def saw_polyblep(frequency, t, sample_rate):
    dt = frequency / sample_rate
    phase = (t * frequency) % 1.0

    # naive saw
    wave = 2.0 * phase - 1.0

    # apply BLEP at discontinuity
    correction = np.vectorize(poly_blep)(phase, dt)
    wave -= correction

    return wave

def square_polyblep(frequency, t, sample_rate):
    dt = frequency / sample_rate
    phase = (t * frequency) % 1.0

    # naive square
    wave = np.where(phase < 0.5, 1.0, -1.0)

    # fix both discontinuities
    correction = np.vectorize(poly_blep)(phase, dt)
    correction2 = np.vectorize(poly_blep)((phase + 0.5) % 1.0, dt)
    wave += correction - correction2

    return wave

def triangle_polyblep(frequency, t, sample_rate):
    # get BLEP square
    sq = square_polyblep(frequency, t, sample_rate)

    # integrate it
    dt = frequency / sample_rate
    tri = np.cumsum(sq) * dt

    # normalize to -1..1
    tri = tri - np.mean(tri)
    tri = tri / np.max(np.abs(tri))

    return tri

def bitcrush(x, bits=8):
    step = 2 ** bits
    return np.round(x * step) / step

def downsample(x, factor=4):
    return np.repeat(x[::factor], factor)

def place_note_with_f_key():
    """Place a note using F key - continues from rightmost note in current part"""
    global notes, SELECTED_PART, selected_note, last_selected_note

    mode_name = subdivision_mode_names[selected_mode_index]
    subdivisions = subdivision_modes[mode_name]  # in scaled pixels

    # Convert subdivisions to twelfths
    subdivisions_twelfths = [s / UI_SCALE for s in subdivisions]

    # Find notes in current part
    part_notes = [n for n in notes if n.part == SELECTED_PART]

    if not part_notes:
        # Empty document - place at middle C, position 0
        pitch = 60
        start_col = 0.0
    else:
        # Find rightmost note in current part
        rightmost = max(part_notes, key=lambda n: n.end_col())
        pitch = rightmost.pitch
        end_pos = rightmost.end_col()

        # Find next subdivision position after end_pos
        beat = int(end_pos / 12)
        pos_in_beat = end_pos % 12

        # Try to find a subdivision in this beat
        start_col = None
        for sub in subdivisions_twelfths:
            candidate = beat * 12 + sub
            if candidate >= end_pos:
                start_col = candidate
                break

        # If no subdivision found in this beat, go to next beat
        if start_col is None:
            beat += 1
            start_col = beat * 12 + subdivisions_twelfths[0]

    # Calculate note duration based on WHERE it starts
    beat = int(start_col / 12)
    pos_in_beat = start_col % 12

    # Find which subdivision we're at
    try:
        current_sub_index = subdivisions_twelfths.index(pos_in_beat)

        # Duration = distance to next subdivision
        if current_sub_index < len(subdivisions_twelfths) - 1:
            note_duration = subdivisions_twelfths[current_sub_index + 1] - subdivisions_twelfths[current_sub_index]
        else:
            # Last subdivision in beat - duration to next beat
            note_duration = 12 - pos_in_beat
    except ValueError:
        # Not aligned to pattern - use default
        if len(subdivisions_twelfths) >= 2:
            note_duration = subdivisions_twelfths[1] - subdivisions_twelfths[0]
        else:
            note_duration = 12
    # Create new note
    new_note = Note(
        pitch=pitch,
        start_col=start_col,
        duration=note_duration,
        part=SELECTED_PART
    )
    # Check for conflicts and advance if necessary
    max_attempts = 100
    attempts = 0
    while attempts < max_attempts:
        conflicts = [n for n in notes if n.part == SELECTED_PART and n.overlaps(new_note)]
        if not conflicts:
            selected_note = new_note
            last_selected_note = new_note
            notes.append(new_note)
            print(f"F-key: Note added at col {new_note.start_col}, pitch {pitch}")
            return

        # Advance to next subdivision
        beat = int(new_note.start_col / 12)
        pos_in_beat = new_note.start_col % 12

        # Find next subdivision in this beat
        found = False
        for sub in subdivisions_twelfths:
            if sub > pos_in_beat:
                new_note.start_col = beat * 12 + sub
                found = True
                break

        if not found:
            # Move to next beat, first subdivision
            beat += 1
            new_note.start_col = beat * 12 + subdivisions_twelfths[0]

        attempts += 1

    print("Could not place note - too many conflicts")

def generate_note(frequency, duration, sample_rate=SAMPLE_RATE):
    """Generate a note waveform"""
    t = np.linspace(0, duration, int(sample_rate * duration), False)

    fade_in = np.linspace(0, 1, int(sample_rate * 0.015))
    fade_out = np.linspace(1, 0, int(sample_rate * 0.01))

    if len(fade_in) + len(fade_out) > len(t):
        envelope = np.linspace(0, 1, len(t))
    else:
        sustain = np.ones(len(t) - len(fade_in) - len(fade_out))
        envelope = np.concatenate([fade_in, sustain, fade_out])

    # Pure sine wave — single fundamental frequency, no harmonics
    wave = np.sin(2 * np.pi * frequency * t)

    wave = wave * envelope
    decay = np.exp(-0.2 * t)
    wave = wave * decay
    volume = 0.3
    wave = wave * volume

    return wave

def note_to_frequency(midi_note, tuning_a=440, tuningsystem="equal temperament"):
    """Convert MIDI note number (0-111) to frequency in Hz"""
    if tuningsystem == "equal temperament":
        # Equal temperament: A4 (note 69) = tuning_a Hz
        flipped_note = 120 - midi_note  # 60 stays 60, 61→59, 59→61, etc.
        return tuning_a * (2 ** ((flipped_note - 69) / 12))

    elif tuningsystem == "well temperament":
        # Werckmeister III (1691) - Bach's tuning
        # Cents from C (not equal temperament)
        well_cents = [
            0,      # C
            90.225, # C#
            192.18, # D
            294.135,# D#
            390.225,# E
            498.045,# F
            588.27, # F#
            696.09, # G
            792.18, # G#
            888.27, # A
            996.09, # A#
            1092.18 # B
        ]

        flipped_note = 120 - midi_note
        octave = flipped_note // 12
        note_in_octave = flipped_note % 12

        # Get C4 frequency
        c4_freq = tuning_a * (2 ** ((60 - 69) / 12))

        # Convert cents to frequency ratio
        cents = well_cents[note_in_octave]
        base_freq = c4_freq * (2 ** (cents / 1200))

        # Adjust for octave
        return base_freq * (2 ** (octave - 5))

    elif tuningsystem == "ptolemaic":
        # Just intonation based on C
        # Ratios relative to C: C=1, D=9/8, E=5/4, F=4/3, G=3/2, A=5/3, B=15/8
        just_ratios = [1, 16/15, 9/8, 6/5, 5/4, 4/3, 45/32, 3/2, 8/5, 5/3, 9/5, 15/8]
        
        # Flip pitch around middle C (note 60)
        flipped_note = 120 - midi_note
        
        # Get C in the same octave as the tuning A
        c4_freq = tuning_a * (2 ** ((60 - 69) / 12))  # C4 frequency
        
        octave = flipped_note // 12
        note_in_octave = flipped_note % 12
        
        ratio = just_ratios[note_in_octave]
        base_freq = c4_freq * ratio
        
        # Adjust for octave (C4 is octave 4, midi note 60 is in octave 5)
        return base_freq * (2 ** (octave - 5))
        
    elif tuningsystem == "harmonic series":
        harmonic_ratios = [
            1,       # C  - Harmonic 1 (fundamental)
            16/15,   # C# - (no clear harmonic match - using 5-limit)
            9/8,     # D  - Harmonic 9/8
            19/16,   # D# - (no clear match, using approximation)
            5/4,     # E  - Harmonic 5/4
            4/3,     # F  - Harmonic 4/3 (derived)
            11/8,    # F# - Harmonic 11/8 (SHARP!)
            3/2,     # G  - Harmonic 3/2
            13/8,    # G# - Harmonic 13/8 (SHARP!)
            5/3,     # A  - Harmonic 5/3 (derived from 5)
            7/4,     # A# - Harmonic 7/4 (FLAT compared to equal!)
            15/8     # B  - Harmonic 15/8
        ]
        
        # Flip pitch around middle C (note 60)
        flipped_note = 120 - midi_note
        
        # Get C in the same octave as the tuning A
        c4_freq = tuning_a * (2 ** ((60 - 69) / 12))  # C4 frequency
        
        octave = flipped_note // 12
        note_in_octave = flipped_note % 12
        
        ratio = harmonic_ratios[note_in_octave]
        base_freq = c4_freq * ratio
        
        # Adjust for octave (C4 is octave 4, midi note 60 is in octave 5)
        return base_freq * (2 ** (octave - 5))

def quantize(x, beat_start_x, mode):
    subdivisions = subdivision_modes[mode]
    rel_x = (x - beat_start_x) * 12 / horizontal_zoom
    closest = min(subdivisions, key=lambda s: abs(s - rel_x))
    return beat_start_x + (closest * horizontal_zoom / 12)

def set_SELECTED_PART(part_index):
    global SELECTED_PART
    SELECTED_PART = part_index
    
    # Update button visuals
    for i, btn in enumerate(part_buttons):
        btn.set_selected(i == part_index)
    
def handle_click(mouse_x, mouse_y, button):
    global SELECTED_PART        
    global scroll_y
    global selected_note
    global last_selected_note
    clicked_row = (mouse_y - GRID_Y + scroll_y) // GRID_SIZE
    
    def handle_part_selection(index):
        global SELECTED_PART
        SELECTED_PART = index
    
    mode_name = subdivision_mode_names[selected_mode_index]
    subdivisions = subdivision_modes[mode_name] # in scaled units (pixels)
    
    # Relative X within the beat
    rel_x = ((mouse_x - GRID_X) % horizontal_zoom)
    length = len(subdivisions)

    # Snap to the nearest subdivision on the left
    snapped_sub = max(s for s in subdivisions if s  * (horizontal_zoom / GRID_SIZE) <= rel_x)

    # Get its index
    sub_index = subdivisions.index(snapped_sub)

    # Calculate duration to next subdivision
    if sub_index < len(subdivisions) - 1:
        note_duration = subdivisions[sub_index + 1] - subdivisions[sub_index]
    else:
        # If it's the last one, you might define duration as the remainder of the beat
        note_duration = GRID_SIZE - subdivisions[sub_index]              # in scaled units, pixels

    # Final column position
    beat_index = (mouse_x - GRID_X + scroll_x) // horizontal_zoom
    note_start = beat_index * 12 + snapped_sub / UI_SCALE # in unscaled units. units of twelvetuplets, not pixels
    
    # Step 2: Adjust for grid position inside UI
    local_x = (mouse_x - GRID_X) / (horizontal_zoom / GRID_SIZE)
    local_y = (mouse_y - GRID_Y)

    # Step 3: Check if click is inside the grid area
    if not (0 <= local_x < GRID_WIDTH / (horizontal_zoom / GRID_SIZE) and 0 <= local_y < GRID_HEIGHT):
        return  # Click was outside the grid

    # Step 4: Convert to grid cell
    col = int((local_x + scroll_x) // GRID_SIZE)
    row = local_y // GRID_SIZE + (scroll_y // GRID_SIZE)
    # if event.type == pygame.MOUSEBUTTONDOWN and event.button in [1, 2, 3]:

    full_col = col * 12  # quarter-note mode

    global selected_note
    clicked_note = None
    clicked_note = None
    for note in notes:
        if note.pitch != clicked_row or note.part != SELECTED_PART:
            continue

        note_x = ((note.start_col * horizontal_zoom) / 12) - scroll_x
        note_y = (note.pitch - (scroll_y // GRID_SIZE)) * GRID_SIZE
        note_width = (note.duration * horizontal_zoom) / 12
        note_height = GRID_SIZE

        if note_x <= mouse_x - GRID_X < note_x + note_width and note_y <= mouse_y - GRID_Y < note_y + note_height:
            clicked_note = note
            break

    if clicked_note is not None:
        if button == 1:
            # Only allow selection if it's in the current part
            if clicked_note.part == SELECTED_PART:
                if selected_note == clicked_note:
                    last_selected_note = selected_note  # ADD THIS - store before deselecting
                    selected_note = None
                else:
                    selected_note = clicked_note
                    last_selected_note = selected_note
        elif button == 3:
            # Only allow deletion if it's in the current part
            if clicked_note.part == SELECTED_PART:
                if clicked_note in notes:
                    notes.remove(clicked_note)
                if selected_note == clicked_note:
                    selected_note = None
    else:
        if button == 1:
            new_note = Note(
                pitch=clicked_row, 
                start_col=note_start,
                duration=note_duration / UI_SCALE,
                part=SELECTED_PART,
            )
            conflicts = []
            for n in notes:
                if n.part == SELECTED_PART and n.overlaps(new_note):
                    conflicts.append(n)
                    print(f"Conflict found: note at {n.start_col} in part {n.part}")

            if not conflicts:
                notes.append(new_note)
                selected_note = new_note
                last_selected_note = new_note
            else:
                print(f"Note blocked - {len(conflicts)} conflict(s) in part {SELECTED_PART}")
                        
            conflicts = []
            for n in notes:
                if n.part == SELECTED_PART and n.overlaps(new_note):
                    conflicts.append(n)
            if not conflicts:
                notes.append(new_note)
            else:
                print(f"Conflicts found: {len(conflicts)}")
                
class Note:                                                     # data stored in unscaled units, twelvetuplets
    def __init__(self, pitch, start_col, duration, part=0): 
        self.pitch = pitch              # 0–111 (A–1 to C9)
        self.start_col = start_col      # Grid column (in twelfths)
        self.duration = duration        # Duration in twelfths (e.g., 12 = quarter note)
        self.part = part                # 0–3 (monophonic part index)
        # self.mode = mode                # Optional: subdivision mode at time of placement

    def end_col(self):
        return self.start_col + self.duration

    def overlaps(self, other):
        return self.part == other.part and not (
            self.end_col() <= other.start_col or self.start_col >= other.end_col()
        )
    
    def time_conflict(self, other):
        return not (
            self.end_col() <= other.start_col or self.start_col >= other.end_col()
        )

class SubImageButton:
    def __init__(self, x, y, image_up, image_down, callback=None):
        self.rect = pygame.Rect(x, y, image_up.get_width(), image_up.get_height())
        self.image_up = image_up
        self.image_down = image_down
        self.selected = False
        self.callback = callback

    def draw(self, surface):
        surface.blit(self.image_down if self.selected else self.image_up, self.rect.topleft)

    def handle_event(self, event):
        if event.type == pygame.MOUSEBUTTONDOWN and self.rect.collidepoint(event.pos):
            if self.callback:
                self.callback()
            return True  # Signal that button was clicked
        return False

    def set_selected(self, value):
        self.selected = value

def set_subdivision_mode(index):
    global selected_mode_index
    selected_mode_index = index

    mode_name = subdivision_mode_names[index]  # Convert index to string key
    current_subdivision = subdivision_modes[mode_name]  # Get subdivision data

    for i, btn in enumerate(buttons):
        btn.set_selected(i == index)

button_images = []
for i in range(8):
    up = pygame.image.load(f"images/subbutton{i + 1}.png").convert_alpha()
    down = pygame.image.load(f"images/subpressed{i + 1}.png").convert_alpha()

    up = pygame.transform.scale(up, (SUB_BUTTON_WIDTH, SUB_BUTTON_HEIGHT))
    down = pygame.transform.scale(down, (SUB_BUTTON_WIDTH, SUB_BUTTON_HEIGHT))
    button_images.append((up, down))

buttons = []
for i, (up, down) in enumerate(button_images):
    x = int((62 + (i * 40)) * UI_SCALE)  # spacing
    y = int(39 * UI_SCALE)
    btn = SubImageButton(x, y, up, down, callback=lambda i=i: set_subdivision_mode(i))
    btn.set_selected(i == selected_mode_index)
    buttons.append(btn)

# Part selection buttons
PART_BUTTON_WIDTH = int(36 * UI_SCALE)
PART_BUTTON_HEIGHT = int(24 * UI_SCALE)

part_button_images = []
for i in range(4):
    up = pygame.image.load(f"images/part{i + 1}.png").convert_alpha()
    down = pygame.image.load(f"images/partpressed{i + 1}.png").convert_alpha()
    
    up = pygame.transform.scale(up, (PART_BUTTON_WIDTH, PART_BUTTON_HEIGHT))
    down = pygame.transform.scale(down, (PART_BUTTON_WIDTH, PART_BUTTON_HEIGHT))
    part_button_images.append((up, down))

part_buttons = []
for i, (up, down) in enumerate(part_button_images):
    x = int((42 + (i * 39)) * UI_SCALE)  # Adjust spacing as needed for your UI
    y = int(66 * UI_SCALE)  # Same vertical coordinate
    btn = SubImageButton(x, y, up, down, callback=lambda i=i: set_SELECTED_PART(i))
    btn.set_selected(i == 0)  # Part 0 selected by default
    part_buttons.append(btn)

file_button_up = pygame.image.load("images/File.png").convert_alpha()
file_button_down = pygame.image.load("images/Filepressed.png").convert_alpha()
file_button_up = pygame.transform.scale(file_button_up, (int(39 * UI_SCALE), int(18 * UI_SCALE)))
file_button_down = pygame.transform.scale(file_button_down, (int(39 * UI_SCALE), int(18 * UI_SCALE)))

settings_button_up = pygame.image.load("images/Settings.png").convert_alpha()
settings_button_up = pygame.transform.scale(settings_button_up, (int(64 * UI_SCALE), int(18 * UI_SCALE)))
help_button_up = pygame.image.load("images/Help.png").convert_alpha()
help_button_up = pygame.transform.scale(help_button_up, (int(40 * UI_SCALE), int(18 * UI_SCALE)))

file_menu_img = pygame.image.load("images/Filemenualt.png").convert_alpha()
file_menu_img = pygame.transform.scale(file_menu_img, (int(106 * UI_SCALE), int(180 * UI_SCALE)))
VISIBLE_MENU_HEIGHT_ORIG = 162  # 9 rows × 18 px (changed from 126)
VISIBLE_MENU_HEIGHT = int(VISIBLE_MENU_HEIGHT_ORIG * UI_SCALE)
visible_menu_rect = pygame.Rect(0, 0, int(106 * UI_SCALE), VISIBLE_MENU_HEIGHT)
file_menu_visible = file_menu_img.subsurface(visible_menu_rect).copy()

tuning_menu_img = pygame.image.load("images/tuningsystems.png").convert_alpha()
tuning_menu_img = pygame.transform.scale(tuning_menu_img, (int(132 * UI_SCALE), int(72 * UI_SCALE)))

DIGIT_WIDTH_ORIG  = 7
DIGIT_HEIGHT_ORIG = 10
DIGIT_PADDING_TOP_ORIG = 4
DIGIT_ROW_Y_ORIG  = 162               # start of bottom row in original pixels
NUM_DIGIT_SLOTS   = 11                # blank + 1..9 + 0

# Scaled values
DIGIT_WIDTH       = int(DIGIT_WIDTH_ORIG  * UI_SCALE)
DIGIT_HEIGHT      = int(DIGIT_HEIGHT_ORIG * UI_SCALE)
DIGIT_PADDING_TOP = int(DIGIT_PADDING_TOP_ORIG * UI_SCALE)
DIGIT_ROW_Y       = int(DIGIT_ROW_Y_ORIG  * UI_SCALE)
MENU_ROW_HEIGHT   = int(18 * UI_SCALE)   # already have this, just confirming

digit_sprites_normal   = []
digit_sprites_inverted = []

for i in range(NUM_DIGIT_SLOTS):
    x_orig = i * DIGIT_WIDTH_ORIG
    # Subsurface on scaled image
    rect = pygame.Rect(
        int(x_orig * UI_SCALE),
        DIGIT_ROW_Y,
        DIGIT_WIDTH,
        MENU_ROW_HEIGHT   # full row height to include padding
    )
    sprite_fullheight = file_menu_img.subsurface(rect).copy()

    # Crop to just the centered digit part
    digit_rect = pygame.Rect(
        0,
        DIGIT_PADDING_TOP,
        DIGIT_WIDTH,
        DIGIT_HEIGHT
    )
    sprite = sprite_fullheight.subsurface(digit_rect)

    digit_sprites_normal.append(sprite)

    # Precompute inverted version
    inv = sprite.copy()
    try:
        pixels = pygame.surfarray.pixels3d(inv)
        mask_black = (pixels[:, :, 0] == 0) & (pixels[:, :, 1] == 0) & (pixels[:, :, 2] == 0)
        mask_grey  = (pixels[:, :, 0] == 239) & (pixels[:, :, 1] == 239) & (pixels[:, :, 2] == 239)

        pixels[mask_black] = [239, 239, 239]
        pixels[mask_grey]  = [0, 0, 0]
    except:
        # Fallback if pixels3d not supported (rare)
        inv.fill((0,0,0))  # placeholder — adjust if needed
    finally:
        if 'pixels' in locals():
            del pixels  # unlock

    digit_sprites_inverted.append(inv)

# Menu position and dimensions
FILE_BUTTON_X = int(2 * UI_SCALE)
FILE_BUTTON_Y = int(2 * UI_SCALE)
FILE_BUTTON_WIDTH = int(39 * UI_SCALE)
FILE_BUTTON_HEIGHT = int(18 * UI_SCALE)

SETTINGS_BUTTON_X = int(42 * UI_SCALE)
HELP_BUTTON_X = int(107 * UI_SCALE)

MENU_X = int(2 * UI_SCALE)
MENU_Y = int(21 * UI_SCALE)
MENU_WIDTH = int(106 * UI_SCALE)
MENU_HEIGHT = int(162 * UI_SCALE)

TUNING_MENU_WIDTH = int(132 * UI_SCALE)
TUNING_MENU_HEIGHT = int(72 * UI_SCALE)  # 4 rows × 18 pixels
TUNING_MENU_X = MENU_X  # Right-aligned with file menu
TUNING_MENU_Y = MENU_Y + VISIBLE_MENU_HEIGHT  # Directly below

MENU_ROW_HEIGHT = int(18 * UI_SCALE)
TEMPO_FIELD_X = int(50 * UI_SCALE)       # Tempo stays at 50
A_FIELD_X = int(35 * UI_SCALE)           # A = moves to 35
DIGIT_SLOT_WIDTH = int(7 * UI_SCALE)

menu_items = ["New", "Open", "Save", "Save As", "Export WAV", "Export PNG", "Tempo", "A =", "Tuning System"]

def menu_new():
    global notes, selected_note, current_file_path, TEMPO, TUNING_A, TUNING_SYSTEM
    notes = []
    selected_note = None
    current_file_path = None
    TEMPO = 72
    TUNING_A = 440
    TUNING_SYSTEM = "equal temperament"

def menu_open():
    global notes, selected_note, current_file_path, TEMPO, TUNING_A, TUNING_SYSTEM, file_menu_open

    filepath = filedialog.askopenfilename(
        title="Open Song",
        filetypes=[("Song", "*.song"), ("All files", "*.*")]
    )

    if not filepath:
        return  # User cancelled

    try:
        with open(filepath, 'r') as f:
            data = eval(f.read())  # Simple format: Python dict

        # Load settings
        TEMPO = data.get('tempo', 72)
        TUNING_A = data.get('tuning_a', 440)
        TUNING_SYSTEM = data.get('tuning_system', 'equal temperament')

        # Load notes
        notes = []
        for note_data in data.get('notes', []):
            note = Note(
                pitch=note_data['pitch'],
                start_col=note_data['start_col'],
                duration=note_data['duration'],
                part=note_data['part']
            )
            notes.append(note)

        selected_note = None
        current_file_path = filepath
        file_menu_open = False
        print(f"Opened: {filepath}")

    except Exception as e:
        print(f"Error opening file: {e}")

def menu_save():
    global current_file_path, file_menu_open

    if current_file_path is None:
        # No file path yet, do Save As
        menu_save_as()
        return

    try:
        save_to_file(current_file_path)
        file_menu_open = False
        print(f"Saved: {current_file_path}")
    except Exception as e:
        print(f"Error saving file: {e}")

def menu_save_as():
    global current_file_path, file_menu_open

    filepath = filedialog.asksaveasfilename(
        title="Save Song",
        defaultextension=".song",
        filetypes=[("Song", "*.song"), ("All files", "*.*")]
    )

    if not filepath:
        return  # User cancelled

    try:
        save_to_file(filepath)
        current_file_path = filepath
        file_menu_open = False
        print(f"Saved as: {filepath}")
    except Exception as e:
        print(f"Error saving file: {e}")

def menu_export_wav():
    print("Export WAV clicked - TODO")

def menu_export_png():
    print("Export PNG clicked - TODO")

def save_to_file(filepath):
    """Helper function to save current state to a file"""
    data = {
        'tempo': TEMPO,
        'tuning_a': TUNING_A,
        'tuning_system': TUNING_SYSTEM,
        'notes': [
            {
                'pitch': note.pitch,
                'start_col': note.start_col,
                'duration': note.duration,
                'part': note.part
            }
            for note in notes
        ]
    }

    with open(filepath, 'w') as f:
        f.write(repr(data))

def menu_tempo():
    print("Tempo clicked")
    # Will show tempo input later

def menu_a_equals():
    print("A = clicked")
    # Will show tuning A input later

def menu_tuning_system():
    global tuning_menu_open, pending_tuning_system
    pending_tuning_system = TUNING_SYSTEM  # Start with current selection
    tuning_menu_open = True
    print("Opening tuning menu")

menu_actions = [menu_new, menu_open, menu_save, menu_save_as, menu_export_wav, menu_export_png, menu_tempo, menu_a_equals, menu_tuning_system]

def draw_file_menu():
    global hovered_menu_item

    # Base cropped menu (no digit row visible)
    screen.blit(file_menu_visible, (MENU_X, MENU_Y))

    RIGHT_MARGIN = int(8 * UI_SCALE)

    for row in range(9):
        row_y = MENU_Y + row * MENU_ROW_HEIGHT
        is_hovered = (hovered_menu_item == row) and editing_row is None   # <--- no hover during edit

        # If hovered (and not editing), draw the color-swapped overlay for baked text
        if is_hovered:
            row_y_orig = row * 18
            row_rect_src = pygame.Rect(
                0,
                int(row_y_orig * UI_SCALE),
                int(106 * UI_SCALE),
                MENU_ROW_HEIGHT
            )
            row_surf = file_menu_img.subsurface(row_rect_src).copy()

            # Color swap
            try:
                pixels = pygame.surfarray.pixels3d(row_surf)
                mask_black = (pixels[:, :, 0] == 0) & (pixels[:, :, 1] == 0) & (pixels[:, :, 2] == 0)
                mask_grey  = (pixels[:, :, 0] == 239) & (pixels[:, :, 1] == 239) & (pixels[:, :, 2] == 239)
                pixels[mask_black] = [239, 239, 239]
                pixels[mask_grey]  = [0, 0, 0]
                del pixels
            except:
                pass

            screen.blit(row_surf, (MENU_X, row_y))

        # Now draw content for this row
        if editing_row == row:
            # Special editing mode: flashing cursor + selection inversion
            draw_editable_number(row, edit_value_str, edit_cursor_pos, edit_sel_start, edit_sel_end)
        elif row in (6, 7):
            # Normal (non-editing) display of Tempo or A=
            value = TEMPO if row == 6 else int(TUNING_A)
            str_val = str(value)

            sprites = digit_sprites_inverted if is_hovered else digit_sprites_normal
            field_x = TEMPO_FIELD_X if row == 6 else A_FIELD_X
            cursor_x = MENU_X + field_x + (4 * DIGIT_SLOT_WIDTH)

            for char in reversed(str_val):
                if char == '0':
                    idx = 10
                else:
                    idx = int(char)

                digit_surf = sprites[idx]
                digit_w = digit_surf.get_width()
                cursor_x -= digit_w

                y_pos = row_y + int(4 * UI_SCALE)
                screen.blit(digit_surf, (cursor_x, y_pos))

def draw_tuning_menu():
    global hovered_tuning_item

    screen.blit(tuning_menu_img, (TUNING_MENU_X, TUNING_MENU_Y))

    # Draw highlights for pending selection and hovered
    for row in range(4):
        row_y = TUNING_MENU_Y + row * MENU_ROW_HEIGHT
        is_selected = (pending_tuning_system == tuning_system_names[row])  # Use pending!
        is_hovered = (hovered_tuning_item == row)

        # If selected or hovered, draw inverted
        if is_selected or is_hovered:
            row_rect_src = pygame.Rect(
                0,
                int(row * 18 * UI_SCALE),
                int(132 * UI_SCALE),
                MENU_ROW_HEIGHT
            )
            row_surf = tuning_menu_img.subsurface(row_rect_src).copy()

            # Color swap
            try:
                pixels = pygame.surfarray.pixels3d(row_surf)
                mask_black = (pixels[:, :, 0] == 0) & (pixels[:, :, 1] == 0) & (pixels[:, :, 2] == 0)
                mask_grey = (pixels[:, :, 0] == 239) & (pixels[:, :, 1] == 239) & (pixels[:, :, 2] == 239)
                pixels[mask_black] = [239, 239, 239]
                pixels[mask_grey] = [0, 0, 0]
                del pixels
            except:
                pass

            screen.blit(row_surf, (TUNING_MENU_X, row_y))

def draw_editable_number(row, value_str, cursor_pos, sel_start, sel_end):
    if row not in (6, 7):
        return

    row_y = MENU_Y + row * MENU_ROW_HEIGHT
    field_x = MENU_X + (TEMPO_FIELD_X if row == 6 else A_FIELD_X)
    field_y = row_y + int(4 * UI_SCALE)             # vertical center
    slot_width = DIGIT_SLOT_WIDTH

    digits_to_show = value_str[-4:].rjust(4)[:4]   # right-align, pad left with ' ' (blank)
    num_digits = len(value_str) # Calculate offset for right-alignment
    offset = 4 - num_digits  # How many blank slots on the left

    for i in range(4):
        char = digits_to_show[i]
        slot_x = field_x + i * slot_width

        if char != ' ':
            idx = 10 if char == '0' else int(char)
            digit_surf = digit_sprites_normal[idx]
            screen.blit(digit_surf, (slot_x, field_y))

        if sel_start is not None and i >= offset and sel_start <= (i - offset) < sel_end:
            slot_rect = pygame.Rect(slot_x, field_y, slot_width, int(10 * UI_SCALE))
            slot_surf = screen.subsurface(slot_rect).copy()
            pixels = pygame.surfarray.pixels3d(slot_surf)
            mask_black = (pixels[:,:,0] == 0) & (pixels[:,:,1] == 0) & (pixels[:,:,2] == 0)
            mask_grey  = (pixels[:,:,0] == 239) & (pixels[:,:,1] == 239) & (pixels[:,:,2] == 239)
            pixels[mask_black] = [239,239,239]
            pixels[mask_grey]  = [0,0,0]
            del pixels
            screen.blit(slot_surf, (slot_x, field_y))

    if edit_blink_visible and (sel_start is None or cursor_pos == sel_end):
        cursor_slot = cursor_pos + offset
        cursor_slot = max(offset, min(cursor_slot, 4))  # Can't go left of first digit, or past slot 4
        cursor_x = field_x + cursor_slot * slot_width
        if cursor_slot == 4:
            cursor_x -= 1 * UI_SCALE  # Move 1 pixel left to stay inside the last slot
        cursor_height = int(10 * UI_SCALE)
        pygame.draw.line(screen, (0,0,0),
                         (cursor_x, field_y),
                         (cursor_x, field_y + cursor_height - 1),
                         width=(1 * UI_SCALE))

def get_full_column(visible_column, mode='quarter'):    # so far this function is unused
    if mode == 'quarter':
        return visible_column * 12

def change_note_length(note, direction, subdivision_mode, notes):
    """Change note duration by subdivision increments"""
    mode_values = subdivision_modes[subdivision_mode]
    subdivisions_twelfths = sorted([s / UI_SCALE for s in mode_values])

    if direction == "shorten":
        # For shortening, find step size at END position
        end_col = note.end_col()
        beat = int(end_col / 12)
        pos_in_beat = end_col % 12

        # Special case: if ending exactly on beat boundary (pos 0), treat as end of previous beat
        if pos_in_beat == 0 and beat > 0:
            beat -= 1
            pos_in_beat = 12

        # Find previous subdivision before current end position
        prev_sub = None
        for sub in reversed(subdivisions_twelfths):
            candidate = beat * 12 + sub
            if candidate < end_col:
                prev_sub = candidate
                break

        # If no subdivision in this beat, go to previous beat
        if prev_sub is None:
            beat -= 1
            if beat >= 0:
                prev_sub = beat * 12 + subdivisions_twelfths[-1]
            else:
                # Can't shorten past beginning
                print("Can't shorten note further")
                return

        step_size = end_col - prev_sub
        new_duration = note.duration - step_size

        # Don't shorten below one subdivision step
        min_duration = subdivisions_twelfths[1] - subdivisions_twelfths[0] if len(subdivisions_twelfths) >= 2 else 12
        if subdivision_mode == "seven five": min_duration = 5
        print(f"new duration: {new_duration}")
        if new_duration >= min_duration:
            note.duration = new_duration
            print(f"Note shortened to duration {note.duration}")
        else:
            print(f"Can't shorten below minimum duration {min_duration}")

    elif direction == "lengthen":
        # For lengthening, find step size at END position
        end_col = note.end_col()
        beat = int(end_col / 12)
        pos_in_beat = end_col % 12

        # Find next subdivision after current end position
        next_sub = None
        for sub in subdivisions_twelfths:
            candidate = beat * 12 + sub
            if candidate > end_col:
                next_sub = candidate
                break

        # If no subdivision in this beat, go to next beat
        if next_sub is None:
            beat += 1
            next_sub = beat * 12 + subdivisions_twelfths[0]

        step_size = next_sub - end_col
        new_duration = note.duration + step_size

        test_note = Note(
            pitch=note.pitch,
            start_col=note.start_col,
            duration=new_duration,
            part=note.part
        )

        conflicts = [
            n for n in notes
            if n != note and n.part == note.part and n.overlaps(test_note)
        ]

        if not conflicts:
            note.duration = new_duration
            print(f"Note lengthened to duration {note.duration}")
        else:
            print("Cannot lengthen - would overlap with another note")

def move_note(note, direction, subdivision_mode, notes):
    # Handle horizontal movement (existing logic)
    if direction in ["left", "right"]:
        if subdivision_mode == "seven five":
            pattern = [0, 7]
            beat = note.start_col // 12
            offset = note.start_col % 12

            try:
                index = pattern.index(offset)
            except ValueError:
                return  # not aligned to pattern

            if direction == "right":
                if index < len(pattern) - 1:
                    new_offset = pattern[index + 1]
                    new_start = beat * 12 + new_offset
                else:
                    new_start = (beat + 1) * 12 + pattern[0]
            elif direction == "left":
                if index > 0:
                    new_offset = pattern[index - 1]
                    new_start = beat * 12 + new_offset
                else:
                    new_start = (beat - 1) * 12 + pattern[-1]

            if new_start < 0:
                return

            # Monophony check
            conflict = any(
                n != note and n.part == note.part and
                n.start_col < new_start + note.duration and new_start < n.end_col()
                for n in notes
            )

            if not conflict:
                note.start_col = new_start

            return  # Prevent falling through to general logic
    
        if subdivision_mode == "quintuplet":
            pattern = [0, 2, 5, 7, 10]
            beat = note.start_col // 12
            offset = note.start_col % 12

            try:
                index = pattern.index(offset)
            except ValueError:
                return  # not aligned to pattern

            if direction == "right":
                if index < len(pattern) - 1:
                    new_offset = pattern[index + 1]
                    new_start = beat * 12 + new_offset
                else:
                    new_start = (beat + 1) * 12 + pattern[0]
            elif direction == "left":
                if index > 0:
                    new_offset = pattern[index - 1]
                    new_start = beat * 12 + new_offset
                else:
                    new_start = (beat - 1) * 12 + pattern[-1]

            if new_start < 0:
                return

            # Monophony check
            conflict = any(
                n != note and n.part == note.part and
                n.start_col < new_start + note.duration and new_start < n.end_col()
                for n in notes
            )

            if not conflict:
                note.start_col = new_start

            return  # Prevent falling through to general logic
    
        mode_values = subdivision_modes[subdivision_mode]
        if len(mode_values) >= 2:
            step_size = (mode_values[1] - mode_values[0]) // UI_SCALE
        else:
            step_size = 12  # quarter note jump

        delta = -step_size if direction == "left" else step_size
        new_start = note.start_col + delta

        if new_start < 0:
            return  # don't allow negative time

        # Monophony check
        conflict = any(
            n != note and n.part == note.part and
            n.start_col < new_start + note.duration and new_start < n.end_col()
            for n in notes
        )

        if not conflict:
            note.start_col = new_start

    # Handle vertical movement
    elif direction in ["up", "down"]:
        new_pitch = note.pitch - (1 if direction == "up" else -1)
        
        # Check pitch bounds (0–111)
        if not (0 <= new_pitch <= 111):
            return

        # Monophony check
        conflict = any(
            n != note and (
                (n.pitch == new_pitch and n.part == note.part and
                 n.start_col < note.start_col + note.duration and note.start_col < n.end_col())
            )
            for n in notes
        )

        if not conflict:
            note.pitch = new_pitch
    
def update_zoom(direction):
    global zoom_index, horizontal_zoom, scroll_x
    if direction == "in" and zoom_index < len(ZOOM_LEVELS) - 1:
        current_start_column = scroll_x / horizontal_zoom
        zoom_index += 1
        horizontal_zoom = ZOOM_LEVELS[zoom_index]
        scroll_x = current_start_column * horizontal_zoom
        scroll_x = max(0, min(scroll_x, get_max_scroll_x()))
    elif direction == "out" and zoom_index > 0 and not (zoom_index == 1 and UI_SCALE == 1):
        current_start_column = scroll_x / horizontal_zoom
        zoom_index -= 1
        horizontal_zoom = ZOOM_LEVELS[zoom_index]
        scroll_x = current_start_column * horizontal_zoom
        scroll_x = max(0, min(scroll_x, get_max_scroll_x()))

def draw_grid():
    global scroll_y
    start_row = scroll_y // GRID_SIZE
    end_row = start_row + VISIBLE_ROWS

    grid_surface.fill((255, 255, 255))
    
    visible_start_col = int(scroll_x / horizontal_zoom)
    visible_end_col = int((scroll_x + WIDTH) / horizontal_zoom)
    
    for col in range(visible_start_col, visible_end_col + 1):
        x = int((col * horizontal_zoom) - scroll_x)
        for row in range(start_row, end_row + 1):
            y = int(row * GRID_SIZE - scroll_y)
            rect = pygame.Rect(x, y, horizontal_zoom, GRID_SIZE)
            color = (191, 191, 191) if (
                (col + row) % 2 == 0
            ) else (159, 159, 159)
            pygame.draw.rect(grid_surface, color, rect)
    
    # First pass: draw notes from OTHER parts (gray)
    for note in notes:
        if note.part != SELECTED_PART and start_row <= note.pitch < end_row and (visible_start_col * 12) <= note.start_col <= (visible_end_col * 12):
            visible_col = note.start_col // 12
            sub_offset = (note.start_col % 12) * UI_SCALE
            x = int((visible_col * GRID_SIZE - (scroll_x / (horizontal_zoom / GRID_SIZE)) + sub_offset) * (horizontal_zoom / GRID_SIZE))
            y = (note.pitch - start_row) * GRID_SIZE
            width = int(((note.duration / 12) * GRID_SIZE) * (horizontal_zoom / GRID_SIZE))
            height = GRID_SIZE

            color = (127, 127, 127)
            pygame.draw.rect(grid_surface, color, pygame.Rect(x, y, width, height))

    # Second pass: draw notes from CURRENT part (black/white on top)
    for note in notes:
        if note.part == SELECTED_PART and start_row <= note.pitch < end_row and (visible_start_col * 12) <= note.start_col <= (visible_end_col * 12):
            visible_col = note.start_col // 12
            sub_offset = (note.start_col % 12) * UI_SCALE
            x = int((visible_col * GRID_SIZE - (scroll_x / (horizontal_zoom / GRID_SIZE)) + sub_offset) * (horizontal_zoom / GRID_SIZE))
            y = (note.pitch - start_row) * GRID_SIZE
            width = int(((note.duration / 12) * GRID_SIZE) * (horizontal_zoom / GRID_SIZE))
            height = GRID_SIZE

            color = (255, 255, 255) if note == selected_note else (0, 0, 0)
            pygame.draw.rect(grid_surface, color, pygame.Rect(x, y, width, height))

    # scaled_width = int(GRID_WIDTH * (horizontal_zoom / GRID_SIZE))
    screen.blit(pygame.transform.scale(grid_surface, (GRID_WIDTH, GRID_HEIGHT)), (GRID_X, GRID_Y))
    
# Main loop
clock = pygame.time.Clock()
running = True
while running:
    menu_was_open = file_menu_open
    screen.fill((255, 255, 255))
    screen.blit(ui_image, (0, 0))  # Draw at top-left
    update_playback_scroll()

    if scroll_y % GRID_SIZE != 0:
        print(f"⚠️ Misaligned scroll_y: {scroll_y}")
    
    # keys = pygame.key.get_pressed()
    # if keys[pygame.K_KP4]:
        # scroll_x = max(0, scroll_x - 1)
    # if keys[pygame.K_KP6]:
        # scroll_x = min(FULL_GRID_WIDTH - GRID_WIDTH, scroll_x + 1)

    if editing_row is not None:
        edit_blink_timer += clock.get_time() / 1000.0
        if edit_blink_timer >= edit_blink_interval:
            edit_blink_timer = 0.0
            edit_blink_visible = not edit_blink_visible
    
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            running = False
        elif event.type == pygame.MOUSEBUTTONDOWN:
            if editing_row is not None or is_playing:
                continue
            mouse_x, mouse_y = pygame.mouse.get_pos()

            # Check if File button clicked
            if FILE_BUTTON_X <= mouse_x <= FILE_BUTTON_X + FILE_BUTTON_WIDTH and \
            FILE_BUTTON_Y <= mouse_y <= FILE_BUTTON_Y + FILE_BUTTON_HEIGHT:
                file_menu_open = not file_menu_open

            elif tuning_menu_open:
                # Modal: ONLY handle clicks inside tuning menu, ignore everything else
                if TUNING_MENU_X <= mouse_x <= TUNING_MENU_X + TUNING_MENU_WIDTH and \
                   TUNING_MENU_Y <= mouse_y <= TUNING_MENU_Y + TUNING_MENU_HEIGHT:
                    # Click inside tuning menu - update pending selection
                    row = (mouse_y - TUNING_MENU_Y) // MENU_ROW_HEIGHT
                    if 0 <= row < 4:
                        pending_tuning_system = tuning_system_names[row]
                        print(f"Pending tuning system: {pending_tuning_system}")
                # If click is outside, do nothing (don't close, don't pass through)
                continue  # Important: stops processing this click event
            # If menu is open, check for menu item clicks or outside clicks
            elif file_menu_open:
                if MENU_X <= mouse_x <= MENU_X + MENU_WIDTH and \
                MENU_Y <= mouse_y <= MENU_Y + VISIBLE_MENU_HEIGHT:      # Clicked inside menu
                    row = (mouse_y - MENU_Y) // MENU_ROW_HEIGHT
                    if 0 <= row < 9:
                        if row in (6, 7):  # Tempo or A=
                            editing_row = row
                            old_value = TEMPO if row == 6 else int(TUNING_A)
                            edit_value_str = str(old_value)
                            num_digits = len(edit_value_str)
                            edit_cursor_pos = num_digits
                            edit_sel_start = 0
                            edit_sel_end = num_digits
                            hovered_menu_item = None
                        elif row == 8:  # Tuning System - keep menu open!
                            menu_actions[row]()
                            # Don't close file_menu_open!
                        else:
                            menu_actions[row]()
                            file_menu_open = False
                else:
                    file_menu_open = False  # Clicked outside menu - close it
                    editing_row = None      # Also exit editing if active
                    continue                # <-- THIS IS THE KEY LINE - stops processing this click event
            # Only handle dragging/notes if menu is closed
            # elif (mouse_y < DRAG_ZONE_HEIGHT and DRAG_ZONE_LEFT <= mouse_x <= WIDTH - DRAG_ZONE_RIGHT):
            #    dragging = True
            #    drag_offset_x = event.pos[0]
            #    drag_offset_y = event.pos[1]
            else:
                handle_click(mouse_x, mouse_y, event.button)
                
        elif event.type == pygame.MOUSEBUTTONUP:
            dragging = False

        elif event.type == pygame.MOUSEMOTION:
            # Ignore mouse motion while editing numbers OR playing
            if editing_row is not None or is_playing:
                hovered_menu_item = None
                hovered_tuning_item = None
                continue

            # Tuning menu hover
            if tuning_menu_open:
                mouse_x, mouse_y = pygame.mouse.get_pos()
                if TUNING_MENU_X <= mouse_x <= TUNING_MENU_X + TUNING_MENU_WIDTH and \
                   TUNING_MENU_Y <= mouse_y <= TUNING_MENU_Y + TUNING_MENU_HEIGHT:
                    hovered_tuning_item = (mouse_y - TUNING_MENU_Y) // MENU_ROW_HEIGHT
                else:
                    hovered_tuning_item = None
            # File menu hover
            elif file_menu_open:
                mouse_x, mouse_y = pygame.mouse.get_pos()
                if MENU_X <= mouse_x <= MENU_X + MENU_WIDTH and \
                MENU_Y <= mouse_y <= MENU_Y + VISIBLE_MENU_HEIGHT:
                    hovered_menu_item = (mouse_y - MENU_Y) // MENU_ROW_HEIGHT
                else:
                    hovered_menu_item = None
            else:
                hovered_menu_item = None
                hovered_tuning_item = None

#        elif event.type == pygame.MOUSEMOTION and dragging:
            # Linux doesn't support frameless window dragging easily
            # Just skip the drag for now - we'll use normal window
#            pass
        """ elif event.type == pygame.MOUSEBUTTONDOWN:
            mouse_x, mouse_y = pygame.mouse.get_pos()
            if (mouse_y < DRAG_ZONE_HEIGHT and DRAG_ZONE_LEFT <= mouse_x <= WIDTH - DRAG_ZONE_RIGHT):
                dragging = True
                # Store the offset from mouse to window corner
                drag_offset_x = event.pos[0]  # Mouse position inside window
                drag_offset_y = event.pos[1]
            else:
                handle_click(mouse_x, mouse_y, event.button)
                
        elif event.type == pygame.MOUSEBUTTONUP:
            dragging = False
        
        elif event.type == pygame.MOUSEMOTION and dragging:
            # Get absolute screen coordinates
            abs_x, abs_y = pygame.mouse.get_pos()
            screen_pos = ctypes.wintypes.POINT()
            ctypes.windll.user32.GetCursorPos(ctypes.byref(screen_pos))
            
            # Set window to maintain offset
            new_window_x = screen_pos.x - drag_offset_x
            new_window_y = screen_pos.y - drag_offset_y
            
            hwnd = pygame.display.get_wm_info()['window']
            ctypes.windll.user32.MoveWindow(hwnd, new_window_x, new_window_y, WIDTH, HEIGHT, False)
            
            pos_x = new_window_x
            pos_y = new_window_y """
        
        if event.type == pygame.MOUSEWHEEL:
            if is_playing:  # Block scrolling during playback
                continue

            mods = pygame.key.get_mods()
            scroll_amount = event.y
            if mods & pygame.KMOD_CTRL and mods & pygame.KMOD_SHIFT:
                if event.y > 0:
                    update_zoom("in")
                elif event.y < 0:
                    update_zoom("out")
            elif pygame.key.get_mods() & pygame.KMOD_SHIFT:
                scroll_x = max(0, min(get_max_scroll_x(), scroll_x - scroll_amount * horizontal_zoom))
            else:
                scroll_y -= scroll_amount * GRID_SIZE * SCROLL_STEP

                # Clamp to bounds
                scroll_y = max(0, min(scroll_y, MAX_SCROLL_Y))

                # Snap to nearest full row
                snapped_scroll_y = (scroll_y // GRID_SIZE) * GRID_SIZE
    
                if scroll_y != snapped_scroll_y:
                    print(f"⚠️ Misaligned scroll_y: {scroll_y} → snapping to {snapped_scroll_y}")

                scroll_y = snapped_scroll_y
    
        elif event.type == pygame.KEYDOWN:
            # Space to play/stop (handle first, even during playback)
            if event.key == pygame.K_SPACE:
                print(f"DEBUG: Space pressed, is_playing={is_playing}")
                if is_playing:
                    stop_playback()
                else:
                    play_song_streaming(notes, TEMPO, TUNING_A, TUNING_SYSTEM)
                    print(f"Playing song: Tempo={TEMPO}, A={TUNING_A}Hz, Tuning={TUNING_SYSTEM}")

            # Block all OTHER keys during playback
            elif is_playing:
                continue

            # File shortcuts (when not editing)
            elif editing_row is None:
                mods = pygame.key.get_mods()

                if event.key == pygame.K_c and (mods & pygame.KMOD_CTRL):
                    if selected_note:
                        copied_note_duration = selected_note.duration
                        copied_note_pitch = selected_note.pitch  # ADD THIS
                        print(f"Copied note: pitch={copied_note_pitch}, duration={copied_note_duration}")
                    else:
                        print("No note selected to copy")
                elif event.key == pygame.K_v and (mods & pygame.KMOD_CTRL):
                    # Paste with copied pitch and duration
                    if copied_note_duration is None or copied_note_pitch is None:
                        print("Nothing copied yet - use Ctrl+C first")
                    else:
                        # Find placement position (same logic as F key)
                        part_notes = [n for n in notes if n.part == SELECTED_PART]

                        if not part_notes:
                            start_col = 0.0
                        else:
                            rightmost = max(part_notes, key=lambda n: n.end_col())
                            end_pos = rightmost.end_col()

                            # Snap to next subdivision
                            mode_name = subdivision_mode_names[selected_mode_index]
                            subdivisions = subdivision_modes[mode_name]
                            subdivisions_twelfths = [s / UI_SCALE for s in subdivisions]

                            beat = int(end_pos / 12)
                            pos_in_beat = end_pos % 12

                            start_col = None
                            for sub in subdivisions_twelfths:
                                candidate = beat * 12 + sub
                                if candidate >= end_pos:
                                    start_col = candidate
                                    break

                            if start_col is None:
                                beat += 1
                                start_col = beat * 12 + subdivisions_twelfths[0]

                        # Create note with COPIED pitch and duration
                        new_note = Note(
                            pitch=copied_note_pitch,  # USE STORED PITCH
                            start_col=start_col,
                            duration=copied_note_duration,
                            part=SELECTED_PART
                        )

                        max_attempts = 100
                        attempts = 0
                        while attempts < max_attempts:
                            conflicts = [n for n in notes if n.part == SELECTED_PART and n.overlaps(new_note)]
                            if not conflicts:
                                notes.append(new_note)
                                selected_note = new_note
                                last_selected_note = new_note
                                break

                            # Advance to next subdivision
                            beat = int(new_note.start_col / 12)
                            pos_in_beat = new_note.start_col % 12

                            found = False
                            for sub in subdivisions_twelfths:
                                if sub > pos_in_beat:
                                    new_note.start_col = beat * 12 + sub
                                    found = True
                                    break

                            if not found:
                                beat += 1
                                new_note.start_col = beat * 12 + subdivisions_twelfths[0]

                            attempts += 1
                elif event.key == pygame.K_DELETE and not is_playing:
                    # Delete selected note
                    if selected_note and selected_note.part == SELECTED_PART:
                        notes.remove(selected_note)
                        print(f"Deleted note at col {selected_note.start_col}")
                        selected_note = None
                    else:
                        print("No note selected to delete")

                elif event.key == pygame.K_BACKSPACE and not is_playing:
                    # Delete selected note and select note to the left
                    if selected_note and selected_note.part == SELECTED_PART:
                        deleted_col = selected_note.start_col
                        notes.remove(selected_note)
                        print(f"Backspace: Deleted note at col {deleted_col}")

                        # Find note to the left in current part
                        candidates = [n for n in notes if n.part == SELECTED_PART and n.start_col < deleted_col]
                        if candidates:
                            selected_note = max(candidates, key=lambda n: n.start_col)
                            last_selected_note = selected_note
                            print(f"Selected note to the left at col {selected_note.start_col}")
                        else:
                            selected_note = None
                            print("No note to the left")
                    else:
                        print("No note selected to delete")
                elif event.key == pygame.K_x and (mods & pygame.KMOD_CTRL):
                    # Cut (copy + delete)
                    if selected_note:
                        # Copy properties
                        copied_note_duration = selected_note.duration
                        copied_note_pitch = selected_note.pitch
                        print(f"Cut note: pitch={copied_note_pitch}, duration={copied_note_duration}")
                        # Delete
                        notes.remove(selected_note)
                        selected_note = None
                    else:
                        print("No note selected to cut")
                elif event.key == pygame.K_s and (mods & pygame.KMOD_CTRL):
                    if mods & pygame.KMOD_SHIFT:
                        menu_save_as()
                    else:
                        menu_save()
                elif event.key == pygame.K_o and (mods & pygame.KMOD_CTRL):
                    menu_open()

            # Escape key
            if event.key == pygame.K_ESCAPE:
                # ... rest of escape handling
                if editing_row is not None:
                    editing_row = None
                elif tuning_menu_open:
                    # Confirm tuning selection (same as Enter)
                    TUNING_SYSTEM = pending_tuning_system
                    print(f"Tuning system confirmed (Esc): {TUNING_SYSTEM}")
                    tuning_menu_open = False
                    pending_tuning_system = None
                    # Update hover based on current mouse position
                    mouse_x, mouse_y = pygame.mouse.get_pos()
                    if MENU_X <= mouse_x <= MENU_X + MENU_WIDTH and \
                       MENU_Y <= mouse_y <= MENU_Y + VISIBLE_MENU_HEIGHT:
                        hovered_menu_item = (mouse_y - MENU_Y) // MENU_ROW_HEIGHT
                    else:
                        hovered_menu_item = None
                elif file_menu_open:
                    file_menu_open = False

            # Number editing mode
            elif editing_row is not None:
                if event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                    try:
                        new_val = int(edit_value_str)
                        if editing_row == 6:
                            TEMPO = max(1, min(9999, new_val))
                        else:
                            TUNING_A = max(1, min(9999, new_val))
                    except ValueError:
                        pass
                    editing_row = None

                elif event.key in range(pygame.K_0, pygame.K_9 + 1) or event.key in range(pygame.K_KP0, pygame.K_KP9 + 1):
                    digit = str(event.key - pygame.K_0 if event.key <= pygame.K_9 else event.key - pygame.K_KP0)
                    if edit_sel_start is not None:
                        edit_value_str = edit_value_str[:edit_sel_start] + digit + edit_value_str[edit_sel_end:]
                        edit_cursor_pos = edit_sel_start + 1
                        edit_sel_start = edit_sel_end = None
                    else:
                        if len(edit_value_str) < 4:
                            edit_value_str = edit_value_str[:edit_cursor_pos] + digit + edit_value_str[edit_cursor_pos:]
                            edit_cursor_pos += 1
                    edit_blink_visible = True

                elif event.key == pygame.K_BACKSPACE:
                    if edit_sel_start is not None and edit_sel_start < edit_sel_end:
                        edit_value_str = edit_value_str[:edit_sel_start] + edit_value_str[edit_sel_end:]
                        edit_cursor_pos = edit_sel_start
                        edit_sel_start = edit_sel_end = None
                    elif edit_cursor_pos > 0:
                        edit_value_str = edit_value_str[:edit_cursor_pos-1] + edit_value_str[edit_cursor_pos:]
                        edit_cursor_pos -= 1

                elif event.key == pygame.K_DELETE:
                    if edit_sel_start is not None and edit_sel_start < edit_sel_end:
                        edit_value_str = edit_value_str[:edit_sel_start] + edit_value_str[edit_sel_end:]
                        edit_cursor_pos = edit_sel_start
                        edit_sel_start = edit_sel_end = None
                    elif edit_cursor_pos < len(edit_value_str):
                        edit_value_str = edit_value_str[:edit_cursor_pos] + edit_value_str[edit_cursor_pos+1:]

                elif event.key == pygame.K_LEFT:
                    mods = pygame.key.get_mods()
                    if mods & pygame.KMOD_SHIFT:
                        if edit_sel_start is None:
                            edit_sel_start = edit_sel_end = edit_cursor_pos
                        edit_cursor_pos = max(0, edit_cursor_pos - 1)
                        edit_sel_start = edit_cursor_pos
                        edit_sel_end = max(edit_sel_start, edit_sel_end)
                    else:
                        if edit_sel_start is not None:
                            edit_cursor_pos = edit_sel_start
                        else:
                            edit_cursor_pos = max(0, edit_cursor_pos - 1)
                        edit_sel_start = edit_sel_end = None

                elif event.key == pygame.K_RIGHT:
                    mods = pygame.key.get_mods()
                    if mods & pygame.KMOD_SHIFT:
                        if edit_sel_start is None:
                            edit_sel_start = edit_sel_end = edit_cursor_pos
                        edit_cursor_pos = min(len(edit_value_str), edit_cursor_pos + 1)
                        edit_sel_end = edit_cursor_pos
                        edit_sel_start = min(edit_sel_start, edit_sel_end)
                    else:
                        if edit_sel_start is not None:
                            edit_cursor_pos = edit_sel_end
                        else:
                            edit_cursor_pos = min(len(edit_value_str), edit_cursor_pos + 1)
                        edit_sel_start = edit_sel_end = None
                # Reset blink
                edit_blink_timer = 0.0
                edit_blink_visible = True

            # All other keys (when NOT editing numbers)
            else:
                if event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                    if tuning_menu_open:
                        # Confirm tuning selection
                        TUNING_SYSTEM = pending_tuning_system
                        print(f"Tuning system confirmed: {TUNING_SYSTEM}")
                        tuning_menu_open = False
                        pending_tuning_system = None
                        # Update hover based on current mouse position
                        mouse_x, mouse_y = pygame.mouse.get_pos()
                        if MENU_X <= mouse_x <= MENU_X + MENU_WIDTH and \
                           MENU_Y <= mouse_y <= MENU_Y + VISIBLE_MENU_HEIGHT:
                            hovered_menu_item = (mouse_y - MENU_Y) // MENU_ROW_HEIGHT
                        else:
                            hovered_menu_item = None
                    elif file_menu_open:
                        file_menu_open = False

                elif event.key == pygame.K_q and not is_playing:
                    set_subdivision_mode(0)  # quarter
                elif event.key == pygame.K_w and not is_playing:
                    set_subdivision_mode(1)  # eighth
                elif event.key == pygame.K_e and not is_playing:
                    set_subdivision_mode(2)  # sixteenth
                elif event.key == pygame.K_r and not is_playing:
                    set_subdivision_mode(3)  # triplet
                elif event.key == pygame.K_t and not is_playing:
                    set_subdivision_mode(4)  # sextuplet
                elif event.key == pygame.K_y and not is_playing:
                    set_subdivision_mode(5)  # quintuplet
                elif event.key == pygame.K_u and not is_playing:
                    set_subdivision_mode(6)  # seven five
                elif event.key == pygame.K_i and not is_playing:
                    set_subdivision_mode(7)  # twelvetuplet

                elif event.key == pygame.K_1 and not is_playing:
                    set_SELECTED_PART(0)
                elif event.key == pygame.K_2 and not is_playing:
                    set_SELECTED_PART(1)
                elif event.key == pygame.K_3 and not is_playing:
                    set_SELECTED_PART(2)
                elif event.key == pygame.K_4 and not is_playing:
                    set_SELECTED_PART(3)

                elif event.key == pygame.K_LEFTBRACKET:
                    scroll_x = 0
                elif event.key == pygame.K_RIGHTBRACKET:
                    if notes:
                        max_end = max(note.end_col() for note in notes)
                        # Round up to next quarter note (multiple of 12)
                        max_end_rounded = math.ceil(max_end / 12) * 12
                        # Put LEFT edge at end (not right edge)
                        target_scroll = (max_end_rounded * horizontal_zoom / 12)
                        scroll_x = max(0, min(target_scroll, get_max_scroll_x()))

                elif event.key == pygame.K_p:
                    play_song(notes, TEMPO, TUNING_A, TUNING_SYSTEM)

                # Zoom
                elif event.key == pygame.K_EQUALS or event.key == pygame.K_PLUS:
                    update_zoom("in")
                elif event.key == pygame.K_MINUS:
                    update_zoom("out")

                elif event.key == pygame.K_LEFT:
                    mods = pygame.key.get_mods()

                    if mods & pygame.KMOD_ALT:
                        # Alt+Left: Scroll left
                        scroll_x = max(0, scroll_x - horizontal_zoom)
                    elif mods & pygame.KMOD_CTRL and selected_note and selected_note.part == SELECTED_PART:
                        # Ctrl+Left: Shorten note
                        change_note_length(selected_note, "shorten", subdivision_mode_names[selected_mode_index], notes)
                    elif mods & pygame.KMOD_SHIFT and selected_note:
                        # Shift+Left: Select note to the left
                        candidates = [n for n in notes if n.part == SELECTED_PART and n.start_col < selected_note.start_col]
                        if candidates:
                            selected_note = max(candidates, key=lambda n: n.start_col)
                            last_selected_note = selected_note
                            print(f"Selected note to the left at col {selected_note.start_col}")
                    elif selected_note and selected_note.part == SELECTED_PART:
                        # Normal: Move note left
                        move_note(selected_note, "left", subdivision_mode_names[selected_mode_index], notes)

                elif event.key == pygame.K_RIGHT:
                    mods = pygame.key.get_mods()

                    if mods & pygame.KMOD_ALT:
                        # Alt+Right: Scroll right
                        scroll_x = min(get_max_scroll_x(), scroll_x + horizontal_zoom)
                    elif mods & pygame.KMOD_CTRL and selected_note and selected_note.part == SELECTED_PART:
                        # Ctrl+Right: Lengthen note
                        change_note_length(selected_note, "lengthen", subdivision_mode_names[selected_mode_index], notes)
                    elif mods & pygame.KMOD_SHIFT and selected_note:
                        # Shift+Right: Select note to the right
                        candidates = [n for n in notes if n.part == SELECTED_PART and n.start_col > selected_note.start_col]
                        if candidates:
                            selected_note = min(candidates, key=lambda n: n.start_col)
                            last_selected_note = selected_note
                            print(f"Selected note to the right at col {selected_note.start_col}")
                    elif selected_note and selected_note.part == SELECTED_PART:
                        # Normal: Move note right
                        move_note(selected_note, "right", subdivision_mode_names[selected_mode_index], notes)

                elif event.key == pygame.K_UP:
                    mods = pygame.key.get_mods()
                    if mods & pygame.KMOD_SHIFT:
                        if selected_note and selected_note.part == SELECTED_PART:
                            # Selected note is in current part - deselect it
                            last_selected_note = selected_note
                            selected_note = None
                            print("Note deselected")
                        else:
                            # Either no selection, or selected note is in different part
                            # Try to reselect last note if it still exists and is in current part
                            if last_selected_note and last_selected_note in notes and last_selected_note.part == SELECTED_PART:
                                selected_note = last_selected_note
                                print(f"Reselected last note at col {selected_note.start_col}")
                            else:
                                # Fall back to rightmost note in current part
                                part_notes = [n for n in notes if n.part == SELECTED_PART]
                                if part_notes:
                                    selected_note = max(part_notes, key=lambda n: n.end_col())
                                    last_selected_note = selected_note
                                    print(f"Selected rightmost note at col {selected_note.start_col}")
                    elif mods & pygame.KMOD_ALT:
                        scroll_y = max(0, scroll_y - GRID_SIZE * SCROLL_STEP)
                    else:
                        if selected_note and selected_note.part == SELECTED_PART:
                            move_note(selected_note, "up", subdivision_mode_names[selected_mode_index], notes)

                elif event.key == pygame.K_DOWN:
                    mods = pygame.key.get_mods()
                    if mods & pygame.KMOD_SHIFT:
                        if selected_note and selected_note.part == SELECTED_PART:
                            # Selected note is in current part - deselect it
                            last_selected_note = selected_note
                            selected_note = None
                            print("Note deselected")
                        else:
                            # Either no selection, or selected note is in different part
                            # Try to reselect last note if it still exists and is in current part
                            if last_selected_note and last_selected_note in notes and last_selected_note.part == SELECTED_PART:
                                selected_note = last_selected_note
                                print(f"Reselected last note at col {selected_note.start_col}")
                            else:
                                # Fall back to rightmost note in current part
                                part_notes = [n for n in notes if n.part == SELECTED_PART]
                                if part_notes:
                                    selected_note = max(part_notes, key=lambda n: n.end_col())
                                    last_selected_note = selected_note
                                    print(f"Selected rightmost note at col {selected_note.start_col}")
                    elif mods & pygame.KMOD_ALT:
                        scroll_y = min(MAX_SCROLL_Y, scroll_y + GRID_SIZE * SCROLL_STEP)
                    else:
                        if selected_note and selected_note.part == SELECTED_PART:
                            move_note(selected_note, "down", subdivision_mode_names[selected_mode_index], notes)

                elif event.key == pygame.K_f and not is_playing:
                    place_note_with_f_key()

        if not menu_was_open:
            for i, btn in enumerate(buttons):
                if btn.handle_event(event):
                    set_subdivision_mode(i)

            for i, btn in enumerate(part_buttons):
                if btn.handle_event(event):
                    set_SELECTED_PART(i)

    for btn in buttons:
        btn.draw(screen)
    for btn in part_buttons:
        btn.draw(screen)

    grid_pixel_height = GRID_HEIGHT
    num_octaves = (grid_pixel_height + piano_height - 1) // piano_height
    
    visible_grid_top = GRID_Y  # top of the pink grid area
    piano_surface = pygame.Surface((piano_width, GRID_HEIGHT))
    
    # middle_c_bottom = GRID_Y + (MIDDLE_C_ROW + 1) * GRID_SIZE
    start_y = GRID_Y - (scroll_y % piano_height) + GRID_SIZE
    
    for i in range(-1, num_octaves + 2):
        y = start_y + i * piano_height - GRID_Y
        piano_surface.blit(piano_image, (0, y))
        
    C4_offset_x = int(20 * UI_SCALE)
    C4_offset_y = int(117 * UI_SCALE)
    
    piano_surface.blit(C4_image, (C4_offset_x, C4_offset_y - scroll_y + 1200))

    screen.blit(piano_surface, (6 * UI_SCALE, GRID_Y))
    
    try:
        scroll_y = (scroll_y // GRID_SIZE) * GRID_SIZE
        top_row = scroll_y // GRID_SIZE
        # print(f"Top visible row: {top_row}")
        draw_grid()
    except Exception as e:
        print(f"Scroll crash: {e}")
    middle_c_top = middle_c_bottom - GRID_SIZE

    file_button_img = file_button_down if file_menu_open else file_button_up
    screen.blit(file_button_img, (FILE_BUTTON_X, FILE_BUTTON_Y))

    screen.blit(settings_button_up, (SETTINGS_BUTTON_X, FILE_BUTTON_Y))
    screen.blit(help_button_up, (HELP_BUTTON_X, FILE_BUTTON_Y))

    if file_menu_open:
        draw_file_menu()
    if tuning_menu_open:
        draw_tuning_menu()

    pygame.display.flip()
    clock.tick(60)

pygame.quit()
