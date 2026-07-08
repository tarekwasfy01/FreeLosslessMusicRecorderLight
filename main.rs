#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use anyhow::{anyhow, Context, Result};
use base64::{engine::general_purpose, Engine as _};
use chrono::Local;
use regex::Regex;
use reqwest::blocking::Client;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::Write;
#[cfg(windows)]
use std::os::windows::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::thread;
use std::thread::JoinHandle;
use std::time::Duration;
use tao::dpi::{LogicalPosition, LogicalSize};
use tao::event::{Event, WindowEvent};
use tao::event_loop::{ControlFlow, EventLoopBuilder};
use tao::window::{Icon, WindowBuilder};
use wry::{Rect, WebView, WebViewBuilder};

#[cfg(windows)]
use windows::Win32::Media::Audio::{
    eConsole, eRender, IAudioCaptureClient, IAudioClient, IMMDeviceEnumerator, MMDeviceEnumerator,
    AUDCLNT_BUFFERFLAGS_SILENT, AUDCLNT_SHAREMODE_SHARED, AUDCLNT_STREAMFLAGS_LOOPBACK,
    WAVEFORMATEX, WAVEFORMATEXTENSIBLE,
};
#[cfg(windows)]
use windows::Win32::System::Com::{
    CoCreateInstance, CoInitializeEx, CoTaskMemFree, CoUninitialize, CLSCTX_ALL,
    COINIT_MULTITHREADED,
};

const APP_TITLE: &str = "Lossless Music Recorder";
const USER_AGENT: &str =
    "LosslessMusicRecorder/0.5 (legal-listening-room-router; contact: local-user)";
const SIDE_W: i32 = 430;

#[derive(Debug, Clone)]
enum UserEvent {
    Ipc(String),
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
struct TrackMeta {
    artist: String,
    title: String,
    album: String,
    cover_url: String,
}

impl TrackMeta {
    fn key(&self) -> String {
        format!("{} - {}", self.artist.trim(), self.title.trim()).to_lowercase()
    }

    fn display(&self) -> String {
        match (self.artist.trim().is_empty(), self.title.trim().is_empty()) {
            (false, false) => format!("{} - {}", self.artist.trim(), self.title.trim()),
            (true, false) => self.title.trim().to_string(),
            (false, true) => self.artist.trim().to_string(),
            (true, true) => "Untitled Track".to_string(),
        }
    }
}

#[derive(Debug, Deserialize)]
struct ClientMessage {
    cmd: String,
    provider: Option<String>,
    url: Option<String>,
    output_dir: Option<String>,
    device: Option<String>,
    room_label: Option<String>,
    channel_id: Option<usize>,
    format: Option<String>,
    bit_depth: Option<String>,
    sample_rate: Option<String>,
    speed4x: Option<bool>,
    auto_split: Option<bool>,
    now_playing_url: Option<String>,
    page_title: Option<String>,
    aural_dir: Option<String>,
    python_exe: Option<String>,
    artist: Option<String>,
    title: Option<String>,
    album: Option<String>,
    cover_url: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
struct ChannelInfo {
    id: usize,
    label: String,
    device: String,
    playback_provider: String,
    playback_url: String,
    running: bool,
    path: String,
    meta: TrackMeta,
    now_playing_url: String,
}

#[derive(Debug)]
struct RecorderProcess {
    child: Child,
    wasapi_stop: Option<Arc<AtomicBool>>,
    wasapi_thread: Option<JoinHandle<Result<()>>>,
    path: PathBuf,
    stderr_log: PathBuf,
    meta: TrackMeta,
    format: String,
    bit_depth: String,
    sample_rate: String,
    speed4x: bool,
}

#[derive(Debug, Clone)]
struct RawAudioFormat {
    sample_rate: u32,
    channels: u16,
    ffmpeg_format: &'static str,
    bytes_per_frame: usize,
}

#[derive(Debug)]
struct Channel {
    id: usize,
    label: String,
    device: String,
    playback_provider: String,
    playback_url: String,
    now_playing_url: String,
    last_meta_key: String,
    meta: TrackMeta,
    process: Option<RecorderProcess>,
}

#[derive(Debug)]
struct AppState {
    channels: Vec<Channel>,
    next_channel_id: usize,
    next_virtual_device_bus: usize,
    output_dir: PathBuf,
    format: String,
    bit_depth: String,
    sample_rate: String,
    speed4x: bool,
    auto_split: bool,
    active_meta: TrackMeta,
    last_now_playing_key: String,
    now_playing_url: String,
    takes: Vec<HashMap<String, String>>,
}

impl AppState {
    fn new() -> Self {
        let output_dir = std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join("recordings");
        let _ = fs::create_dir_all(&output_dir);
        Self {
            channels: Vec::new(),
            next_channel_id: 1,
            next_virtual_device_bus: 2,
            output_dir,
            format: "flac".to_string(),
            bit_depth: "24".to_string(),
            sample_rate: "auto".to_string(),
            speed4x: false,
            auto_split: true,
            active_meta: TrackMeta::default(),
            last_now_playing_key: String::new(),
            now_playing_url: String::new(),
            takes: Vec::new(),
        }
    }

    fn set_common_from_msg(&mut self, msg: &ClientMessage) {
        // Output format is intentionally fixed to FLAC. Old/stale UI messages must not switch it back to WAV.
        self.format = "flac".to_string();

        if let Some(dir) = msg.output_dir.as_ref().filter(|s| !s.trim().is_empty()) {
            self.output_dir = PathBuf::from(dir);
            let _ = fs::create_dir_all(&self.output_dir);
        }
        if let Some(bit_depth) = msg.bit_depth.as_ref() {
            self.bit_depth = bit_depth.clone();
        }
        if let Some(sample_rate) = msg.sample_rate.as_ref() {
            self.sample_rate = sample_rate.clone();
        }
        // 4x playback/save was removed from the UI; stale frontend messages must not enable it.
        self.speed4x = false;
        if let Some(auto_split) = msg.auto_split {
            self.auto_split = auto_split;
        }
        if let Some(now_playing_url) = msg
            .now_playing_url
            .as_ref()
            .filter(|s| !s.trim().is_empty())
        {
            self.now_playing_url = now_playing_url.trim().to_string();
        }

        // Messages for a concrete bus carry bus-local metadata. They must not overwrite the global Now Playing metadata.
        if msg.channel_id.is_none() {
            if let Some(artist) = msg.artist.as_ref().filter(|s| !s.trim().is_empty()) {
                self.active_meta.artist = artist.trim().to_string();
            }
            if let Some(title) = msg.title.as_ref().filter(|s| !s.trim().is_empty()) {
                self.active_meta.title = title.trim().to_string();
            }
            if let Some(album) = msg.album.as_ref().filter(|s| !s.trim().is_empty()) {
                self.active_meta.album = album.trim().to_string();
            }
            if let Some(cover_url) = msg.cover_url.as_ref().filter(|s| !s.trim().is_empty()) {
                self.active_meta.cover_url = cover_url.trim().to_string();
            }
        }
    }

    fn channel_infos(&self) -> Vec<ChannelInfo> {
        self.channels
            .iter()
            .map(|ch| ChannelInfo {
                id: ch.id,
                label: ch.label.clone(),
                device: ch.device.clone(),
                playback_provider: ch.playback_provider.clone(),
                playback_url: ch.playback_url.clone(),
                running: ch.process.is_some(),
                path: ch
                    .process
                    .as_ref()
                    .map(|p| p.path.display().to_string())
                    .unwrap_or_default(),
                meta: ch.meta.clone(),
                now_playing_url: ch.now_playing_url.clone(),
            })
            .collect()
    }
}

fn main() -> Result<()> {
    let event_loop = EventLoopBuilder::<UserEvent>::with_user_event().build();
    let proxy = event_loop.create_proxy();

    let mut window_builder = WindowBuilder::new()
        .with_title(APP_TITLE)
        .with_inner_size(LogicalSize::new(1560.0, 930.0));
    if let Some(icon) = load_app_icon() {
        window_builder = window_builder.with_window_icon(Some(icon));
    }
    let window = window_builder
        .build(&event_loop)
        .context("Failed to create main window")?;

    let size = window.inner_size();
    let side_w = SIDE_W.min((size.width as i32 - 360).max(300));
    let provider_bounds = Rect {
        position: LogicalPosition::new(0.0, 0.0).into(),
        size: LogicalSize::new(
            (size.width as i32 - side_w).max(360) as f64,
            size.height as f64,
        )
        .into(),
    };
    let top_bounds = Rect {
        position: LogicalPosition::new((size.width as i32 - side_w).max(360) as f64, 0.0).into(),
        size: LogicalSize::new(side_w as f64, size.height as f64).into(),
    };

    let top_proxy = proxy.clone();
    let top = WebViewBuilder::new()
        .with_bounds(top_bounds)
        .with_html(top_html())
        .with_ipc_handler(move |req| {
            let _ = top_proxy.send_event(UserEvent::Ipc(req.body().to_string()));
        })
        .build_as_child(&window)
        .context("Failed to create top control WebView")?;

    let provider_proxy = proxy.clone();
    let mut provider = WebViewBuilder::new()
        .with_bounds(provider_bounds)
        .with_url("about:blank")
        .with_initialization_script(provider_metadata_script())
        .with_ipc_handler(move |req| {
            let _ = provider_proxy.send_event(UserEvent::Ipc(req.body().to_string()));
        })
        .build_as_child(&window)
        .context("Failed to create provider WebView")?;

    let mut state = AppState::new();
    ensure_single_recording_bus(&mut state);
    emit_both(&top, &top, "ready", json!({ "title": APP_TITLE }));
    emit_both(
        &top,
        &top,
        "outputDir",
        state.output_dir.display().to_string(),
    );
    emit_both(&top, &top, "log", "Application loaded. A single recording bus is ready with WASAPI loopback selected automatically.");
    match list_audio_devices() {
        Ok(devs) => emit_both(&top, &top, "devices", devs),
        Err(e) => emit_both(
            &top,
            &top,
            "error",
            format!("Could not list audio devices: {e}"),
        ),
    }
    emit_audio_diagnostics(&top, &top);
    emit_both(&top, &top, "channels", state.channel_infos());

    event_loop.run(move |event, _, control_flow| {
        *control_flow = ControlFlow::Wait;
        match event {
            Event::UserEvent(UserEvent::Ipc(body)) => {
                if let Err(e) = handle_ipc(&top, &top, &mut provider, &mut state, &body) {
                    emit_both(&top, &top, "error", e.to_string());
                }
            }
            Event::WindowEvent {
                event: WindowEvent::Resized(size),
                ..
            } => {
                let w = size.width as i32;
                let h = size.height as i32;
                let side_w = SIDE_W.min((w - 360).max(300));
                let provider_w = (w - side_w).max(360);
                let _ = provider.set_bounds(Rect {
                    position: LogicalPosition::new(0.0, 0.0).into(),
                    size: LogicalSize::new(provider_w as f64, h.max(320) as f64).into(),
                });
                let _ = top.set_bounds(Rect {
                    position: LogicalPosition::new(provider_w as f64, 0.0).into(),
                    size: LogicalSize::new(side_w as f64, h.max(320) as f64).into(),
                });
            }
            Event::WindowEvent {
                event: WindowEvent::CloseRequested,
                ..
            } => {
                stop_all_channels(&mut state, &top, &top);
                *control_flow = ControlFlow::Exit;
            }
            _ => {}
        }
    });
}

fn handle_ipc(
    top: &WebView,
    right: &WebView,
    provider: &mut WebView,
    state: &mut AppState,
    body: &str,
) -> Result<()> {
    let msg: ClientMessage = serde_json::from_str(body).context("Bad IPC JSON")?;
    if msg.cmd == "webview_metadata" {
        handle_webview_metadata(top, right, state, &msg);
        return Ok(());
    }
    state.set_common_from_msg(&msg);
    update_channel_meta_from_msg(state, &msg)?;

    match msg.cmd.as_str() {
        "ui_ready" => {
            ensure_single_recording_bus(state);
            emit_both(
                top,
                right,
                "outputDir",
                state.output_dir.display().to_string(),
            );
            if !state.now_playing_url.is_empty() {
                emit_both(top, right, "metadataUrl", state.now_playing_url.clone());
            }
            emit_both(top, right, "metadata", state.active_meta.clone());
            emit_both(top, right, "channels", state.channel_infos());
            emit_both(top, right, "takes", &state.takes);
            match list_audio_devices() {
                Ok(devs) => emit_both(top, right, "devices", devs),
                Err(e) => emit_both(
                    top,
                    right,
                    "error",
                    format!("Could not list audio devices: {e}"),
                ),
            }
            emit_audio_diagnostics(top, right);
        }
        "set_options" => {
            emit_both(top, right, "channels", state.channel_infos());
        }
        "update_channel_meta" => {
            emit_both(top, right, "channels", state.channel_infos());
        }
        "open_provider" => {
            let provider_name = msg.provider.unwrap_or_else(|| "own".to_string());
            let url = provider_url(&provider_name, msg.url.as_deref());
            provider
                .load_url(&url)
                .context("Failed to load provider URL")?;
            // Do not copy the provider page URL into the Now Playing/API field.
            // That field is only for real metadata endpoints; WebView metadata is handled separately.
            emit_both(
                top,
                right,
                "log",
                format!("Loaded in embedded WebView: {url}"),
            );
        }
        "open_provider_external" => {
            let provider_name = msg.provider.unwrap_or_else(|| "own".to_string());
            let url = provider_url(&provider_name, msg.url.as_deref());
            open_url_external(&url)?;
            emit_both(
                top,
                right,
                "log",
                format!("Opened external player/browser window: {url}"),
            );
        }
        "pick_output_dir" => {
            if let Some(folder) = rfd::FileDialog::new()
                .set_directory(&state.output_dir)
                .pick_folder()
            {
                state.output_dir = folder.clone();
                let _ = fs::create_dir_all(&state.output_dir);
                emit_both(top, right, "outputDir", folder.display().to_string());
                emit_both(
                    top,
                    right,
                    "log",
                    format!("Output folder set to {}", folder.display()),
                );
            }
        }
        "open_loopback_setup" => {
            let _ = Command::new("explorer").arg("ms-settings:sound").spawn();
            emit_both(
                top,
                right,
                "log",
                "Opened Windows Sound settings.",
            );
        }
        "add_virtual_device" => {
            let target_bus = state.next_virtual_device_bus.max(state.next_channel_id.max(2));
            create_virtual_audio_device_for_bus(target_bus)?;
            state.next_virtual_device_bus = target_bus + 1;
            emit_both(
                top,
                right,
                "log",
                format!(
                    "Virtual audio device creation started for Bus {target_bus}. Add Device now creates another ROOT\\VirtualAudioDriver instance, not a fake Bus-specific hardware id. Click again for Bus {} after the first one appears. Restart Windows if needed, then press Refresh Devices.",
                    target_bus + 1
                ),
            );
            emit_both(top, right, "restartRequired", "You need to restart Windows before newly created virtual audio devices can appear.");
        }
        "install_driver_package" => {
            let drivers_dir = std::env::current_dir()
                .unwrap_or_else(|_| PathBuf::from("."))
                .join("drivers");
            fs::create_dir_all(&drivers_dir).ok();

            if let Some(installer) = virtual_audio_driver_installer() {
                enable_test_signing_and_run_driver_installer(&installer)?;
                emit_both(
                    top,
                    right,
                    "log",
                    format!(
                        "Automatic driver installer started: Test Signing will be enabled, then {} will run elevated. Restart Windows after it finishes, then press Refresh Devices.",
                        installer.display()
                    ),
                );
                emit_both(top, right, "restartRequired", "You need to restart Windows before the virtual audio device can appear.");
            } else if let Some(inf) = virtual_audio_driver_inf() {
                install_virtual_audio_driver_with_test_signing(&inf)?;
                emit_both(
                    top,
                    right,
                    "log",
                    format!(
                        "Automatic Virtual Audio Driver install started for {}. The app will create the ROOT\\VirtualAudioDriver device automatically, no Add Legacy wizard needed. Restart Windows after it finishes, then press Refresh Devices.",
                        inf.display()
                    ),
                );
                emit_both(top, right, "restartRequired", "You need to restart Windows before the virtual audio device can appear.");
            } else {
                let _ = Command::new("explorer").arg(&drivers_dir).spawn();
                emit_both(top, right, "error", format!("No bundled Virtual Audio Driver package was found. Put the shipped driver folder, installer EXE, devcon.exe, or VirtualAudioDriver.inf inside {} and click Install automatically again.", drivers_dir.display()));
            }
        }
        "restart_windows" => {
            emit_both(top, right, "log", "Restart requested. Windows will restart in a few seconds.");
            let mut cmd = Command::new("shutdown");
            cmd.args(["/r", "/t", "5", "/c", "Virtual Audio Driver installed. Restarting to enable Test Signing and audio endpoints."]);
            spawn_no_console(cmd).context("Failed to request Windows restart")?;
        }
        "open_add_hardware_wizard" => {
            let _ = Command::new("hdwwiz.cpl").spawn();
            emit_both(top, right, "log", "Opened Add Legacy Hardware wizard. Choose Sound, video and game controllers → Have Disk → VirtualAudioDriver.inf.");
        }
        "open_device_manager" => {
            let _ = Command::new("devmgmt.msc").spawn();
            emit_both(top, right, "log", "Opened Device Manager. Check Audio inputs and outputs plus Sound, video and game controllers.");
        }
        "pick_aural_dir" => {
            if let Some(folder) = rfd::FileDialog::new()
                .set_directory(std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")))
                .pick_folder()
            {
                emit_both(top, right, "auralDir", folder.display().to_string());
                emit_both(
                    top,
                    right,
                    "log",
                    format!("Aural folder selected: {}", folder.display()),
                );
            }
        }
        "pick_python_exe" => {
            if let Some(file) = rfd::FileDialog::new()
                .add_filter("Python", &["exe"])
                .pick_file()
            {
                emit_both(top, right, "pythonExe", file.display().to_string());
                emit_both(
                    top,
                    right,
                    "log",
                    format!("Python executable selected: {}", file.display()),
                );
            }
        }
        "launch_aural_gui" => {
            launch_aural(msg.aural_dir.as_deref(), msg.python_exe.as_deref(), "GUI")?;
            emit_both(
                top,
                right,
                "log",
                "Launched Aural virtual cable manager in GUI mode.",
            );
        }
        "launch_aural_cui" => {
            launch_aural(msg.aural_dir.as_deref(), msg.python_exe.as_deref(), "CUI")?;
            emit_both(
                top,
                right,
                "log",
                "Launched Aural virtual cable manager in CUI mode.",
            );
        }
        "open_windows_routing" => {
            let _ = Command::new("explorer")
                .arg("ms-settings:apps-volume")
                .spawn();
            emit_both(
                top,
                right,
                "log",
                "Opened Windows per-app volume and output-device routing settings.",
            );
        }
        "list_devices" => {
            let devs = list_audio_devices()?;
            emit_both(top, right, "devices", devs);
            emit_audio_diagnostics(top, right);
        }
        "add_bus" => {
            let id = ensure_single_recording_bus(state);
            if let Some(label) = msg.room_label.as_deref().map(str::trim).filter(|s| !s.is_empty()) {
                if let Some(ch) = state.channels.iter_mut().find(|c| c.id == id) {
                    ch.label = label.to_string();
                }
            }
            emit_both(top, right, "channels", state.channel_infos());
            emit_both(top, right, "log", "Single-bus mode is active. The existing recording bus is used.");
        }
        "remove_channel" => {
            if let Some(id) = msg.channel_id {
                stop_channel_by_id(state, id, top, right)?;
                state.channels.retain(|c| c.id != id);
                emit_both(top, right, "channels", state.channel_infos());
            }
        }
        "open_channel_player" => {
            let id = msg
                .channel_id
                .ok_or_else(|| anyhow!("Missing channel id."))?;
            let ch = state
                .channels
                .iter()
                .find(|c| c.id == id)
                .ok_or_else(|| anyhow!("Channel {id} not found."))?;
            open_room_player(ch)?;
            emit_both(top, right, "log", format!("Opened playback window for {}. Audio output hint: {}.", ch.label, playback_output_device_hint(&ch.device).unwrap_or_else(|| "default Windows output".to_string())));
        }
        "route_channel" => {
            let _ = Command::new("explorer")
                .arg("ms-settings:apps-volume")
                .spawn();
            emit_both(top, right, "log", "Opened Windows per-app volume and output-device routing. Assign the room player to its virtual cable/output endpoint there.");
        }
        "start_channel" => {
            let id = msg
                .channel_id
                .ok_or_else(|| anyhow!("Missing channel id."))?;
            start_channel_by_id(state, id, top, right)?;
            emit_both(top, right, "channels", state.channel_infos());
        }
        "start_recording" => {
            if state.channels.is_empty() {
                let requested_device = msg.device.as_deref().unwrap_or_default();
                let Some(device) = capture_device_for_new_bus(state, requested_device, top, right)?
                else {
                    return Err(anyhow!("No free FFmpeg-compatible capture endpoint is available. Press Refresh Devices or select another available capture device."));
                };
                let label = msg
                    .room_label
                    .as_deref()
                    .map(str::trim)
                    .filter(|s| !s.is_empty())
                    .unwrap_or("Main Recording");
                let playback_provider = msg.provider.as_deref().unwrap_or("own");
                let playback_url = msg.url.as_deref().unwrap_or("");
                add_channel(
                    state,
                    device.clone(),
                    label.to_string(),
                    playback_provider.to_string(),
                    playback_url.to_string(),
                    msg.now_playing_url.clone().unwrap_or_default(),
                    state.active_meta.clone(),
                );
                emit_both(
                    top,
                    right,
                    "log",
                    format!("Created recording bus '{label}' for {device}."),
                );
            }
            let ids: Vec<usize> = state.channels.iter().map(|c| c.id).collect();
            let mut started = 0usize;
            let mut last_error = None;
            for id in ids {
                match start_channel_by_id(state, id, top, right) {
                    Ok(_) => started += 1,
                    Err(e) => last_error = Some(e),
                }
            }
            emit_both(top, right, "channels", state.channel_infos());
            if started == 0 {
                return Err(
                    last_error.unwrap_or_else(|| anyhow!("No recording bus could be started."))
                );
            }
        }
        "stop_channel" => {
            let id = msg
                .channel_id
                .ok_or_else(|| anyhow!("Missing channel id."))?;
            stop_channel_by_id(state, id, top, right)?;
            emit_both(top, right, "channels", state.channel_infos());
            emit_both(top, right, "takes", &state.takes);
        }
        "start_all" => {
            if state.channels.is_empty() {
                return Err(anyhow!("Recording bus is not ready yet."));
            }
            let ids: Vec<usize> = state.channels.iter().map(|c| c.id).collect();
            for id in ids {
                let _ = start_channel_by_id(state, id, top, right);
            }
            emit_both(top, right, "channels", state.channel_infos());
        }
        "stop_all" => {
            stop_all_channels(state, top, right);
            emit_both(top, right, "channels", state.channel_infos());
            emit_both(top, right, "takes", &state.takes);
        }
        "stop_recording" => {
            stop_all_channels(state, top, right);
            emit_both(top, right, "channels", state.channel_infos());
            emit_both(top, right, "takes", &state.takes);
        }
        "musicbrainz" => {
            let artist = msg.artist.unwrap_or_default();
            let title = msg.title.unwrap_or_default();
            let meta = lookup_musicbrainz(&artist, &title)?;
            state.active_meta = meta.clone();
            emit_both(top, right, "metadata", meta);
        }
        "poll_now_playing" | "poll_channel_now_playing" => {
            let bus_id = msg.channel_id;
            let url_owned = if let Some(id) = bus_id {
                msg.now_playing_url
                    .as_deref()
                    .map(str::trim)
                    .filter(|s| !s.is_empty())
                    .map(ToString::to_string)
                    .or_else(|| {
                        state
                            .channels
                            .iter()
                            .find(|c| c.id == id)
                            .map(|c| c.now_playing_url.trim().to_string())
                            .filter(|s| !s.is_empty())
                    })
            } else {
                msg.now_playing_url
                    .as_deref()
                    .map(str::trim)
                    .filter(|s| !s.is_empty())
                    .map(ToString::to_string)
                    .or_else(|| {
                        let s = state.now_playing_url.trim().to_string();
                        if s.is_empty() { None } else { Some(s) }
                    })
            };
            let Some(url) = url_owned else {
                return Err(anyhow!("Enter a Now Playing API URL first."));
            };
            match fetch_now_playing(&url) {
                Ok(meta) => {
                    let meta = enrich_metadata(meta);
                    if let Some(id) = bus_id {
                        if let Some(channel) = state.channels.iter_mut().find(|c| c.id == id) {
                            channel.now_playing_url = url.clone();
                        }
                        apply_metadata_to_channel(state, id, meta.clone(), top, right, "Bus Now Playing metadata changed")?;
                        emit_both(top, right, "nowPlaying", meta.clone());
                        emit_both(top, right, "log", format!("Bus now playing: {}", meta.display()));
                    } else {
                        let key = meta.key();
                        let changed = !key.is_empty() && key != state.last_now_playing_key;
                        state.active_meta = meta.clone();
                        emit_both(top, right, "nowPlaying", meta.clone());
                        if changed {
                            state.last_now_playing_key = key;
                            emit_both(top, right, "log", format!("Now playing: {}", meta.display()));
                            apply_metadata_to_webview_buses(state, meta, top, right, "Now Playing metadata changed");
                        }
                    }
                }
                Err(e) => emit_both(
                    top,
                    right,
                    "error",
                    format!("Now Playing polling failed: {e}"),
                ),
            }
        }
        "apply_speed" => {
            emit_both(top, right, "log", "4x playback was removed.");
        }
        "log" => {
            if let Some(text) = msg.url {
                emit_both(top, right, "log", text);
            }
        }
        _ => emit_both(top, right, "log", format!("Unknown command: {}", msg.cmd)),
    }
    Ok(())
}

fn handle_webview_metadata(
    top: &WebView,
    right: &WebView,
    state: &mut AppState,
    msg: &ClientMessage,
) {
    // The WebView URL is a normal playback page, not necessarily a Now Playing/API endpoint.
    // Keeping it out of the bus now_playing_url prevents the bus from being treated as
    // an external/API bus and fixes auto-split on WebView metadata changes.

    let mut meta = TrackMeta {
        artist: msg.artist.clone().unwrap_or_default(),
        title: msg.title.clone().unwrap_or_default(),
        album: msg.album.clone().unwrap_or_default(),
        cover_url: msg.cover_url.clone().unwrap_or_default(),
    };

    if meta.artist.trim().is_empty() && meta.title.trim().is_empty() {
        if let Some(page_title) = msg.page_title.as_deref() {
            if let Some(parsed) = parse_webview_title(page_title) {
                meta = parsed;
            }
        }
    }

    if !metadata_is_useful(&meta) {
        return;
    }

    state.active_meta = merge_track_meta(&state.active_meta, &meta);
    let key = state.active_meta.key();
    if !key.is_empty() && key != state.last_now_playing_key {
        state.last_now_playing_key = key;
        emit_both(top, right, "nowPlaying", state.active_meta.clone());
        emit_both(
            top,
            right,
            "log",
            format!("WebView metadata: {}", state.active_meta.display()),
        );
        let active_meta = state.active_meta.clone();
        apply_metadata_to_webview_buses(
            state,
            active_meta,
            top,
            right,
            "WebView metadata changed",
        );
    }
}

fn remember_metadata_url(top: &WebView, right: &WebView, state: &mut AppState, url: &str) {
    let trimmed = url.trim();
    if !is_real_page_url(trimmed) || state.now_playing_url == trimmed {
        return;
    }
    state.now_playing_url = trimmed.to_string();
    emit_both(top, right, "metadataUrl", state.now_playing_url.clone());
}

fn is_real_page_url(url: &str) -> bool {
    let trimmed = url.trim();
    !trimmed.is_empty()
        && !trimmed.eq_ignore_ascii_case("about:blank")
        && !trimmed.starts_with("data:")
        && !trimmed.starts_with("javascript:")
}

fn merge_track_meta(current: &TrackMeta, incoming: &TrackMeta) -> TrackMeta {
    TrackMeta {
        artist: if incoming.artist.trim().is_empty() {
            current.artist.clone()
        } else {
            incoming.artist.trim().to_string()
        },
        title: if incoming.title.trim().is_empty() {
            current.title.clone()
        } else {
            incoming.title.trim().to_string()
        },
        album: if incoming.album.trim().is_empty() {
            current.album.clone()
        } else {
            incoming.album.trim().to_string()
        },
        cover_url: if incoming.cover_url.trim().is_empty() {
            current.cover_url.clone()
        } else {
            incoming.cover_url.trim().to_string()
        },
    }
}

fn metadata_is_useful(meta: &TrackMeta) -> bool {
    let title = meta.title.trim();
    if title.is_empty() {
        return false;
    }
    let lower = title.to_lowercase();
    let generic = [
        "deezer",
        "qobuz",
        "tidal",
        "own web radio",
        "lossless music recorder",
        "web player",
        "music streaming",
    ];
    !generic
        .iter()
        .any(|needle| lower == *needle || lower.contains(needle))
}

fn meta_has_any_value(meta: &TrackMeta) -> bool {
    !meta.artist.trim().is_empty()
        || !meta.title.trim().is_empty()
        || !meta.album.trim().is_empty()
        || !meta.cover_url.trim().is_empty()
}

fn exact_meta_from_msg(msg: &ClientMessage) -> Option<TrackMeta> {
    if msg.artist.is_none() && msg.title.is_none() && msg.album.is_none() && msg.cover_url.is_none()
    {
        return None;
    }
    Some(TrackMeta {
        artist: msg.artist.clone().unwrap_or_default().trim().to_string(),
        title: msg.title.clone().unwrap_or_default().trim().to_string(),
        album: msg.album.clone().unwrap_or_default().trim().to_string(),
        cover_url: msg.cover_url.clone().unwrap_or_default().trim().to_string(),
    })
}

fn update_channel_meta_from_msg(state: &mut AppState, msg: &ClientMessage) -> Result<()> {
    let Some(id) = msg.channel_id else {
        return Ok(());
    };
    let channel = state
        .channels
        .iter_mut()
        .find(|c| c.id == id)
        .ok_or_else(|| anyhow!("Channel {id} not found."))?;

    if let Some(device) = msg.device.as_ref() {
        let trimmed = device.trim();
        if !trimmed.is_empty() {
            channel.device = trimmed.to_string();
        }
    }

    if let Some(url) = msg.now_playing_url.as_ref() {
        channel.now_playing_url = url.trim().to_string();
    }

    let has_meta_field = msg.artist.is_some()
        || msg.title.is_some()
        || msg.album.is_some()
        || msg.cover_url.is_some();
    if has_meta_field {
        channel.meta.artist = msg.artist.clone().unwrap_or_else(|| channel.meta.artist.clone()).trim().to_string();
        channel.meta.title = msg.title.clone().unwrap_or_else(|| channel.meta.title.clone()).trim().to_string();
        channel.meta.album = msg.album.clone().unwrap_or_else(|| channel.meta.album.clone()).trim().to_string();
        channel.meta.cover_url = msg.cover_url.clone().unwrap_or_else(|| channel.meta.cover_url.clone()).trim().to_string();
        channel.last_meta_key = channel.meta.key();
        if let Some(proc_info) = channel.process.as_mut() {
            proc_info.meta = channel.meta.clone();
        }
    }

    Ok(())
}

fn enrich_metadata(mut meta: TrackMeta) -> TrackMeta {
    if meta.album.is_empty() || meta.cover_url.is_empty() {
        if let Ok(mb) = lookup_musicbrainz(&meta.artist, &meta.title) {
            if meta.album.is_empty() {
                meta.album = mb.album;
            }
            if meta.cover_url.is_empty() {
                meta.cover_url = mb.cover_url;
            }
        }
    }
    meta
}

fn set_channel_metadata_exact(state: &mut AppState, id: usize, meta: TrackMeta) -> Result<()> {
    let channel = state
        .channels
        .iter_mut()
        .find(|c| c.id == id)
        .ok_or_else(|| anyhow!("Channel {id} not found."))?;
    channel.last_meta_key = meta.key();
    channel.meta = meta.clone();
    if let Some(proc_info) = channel.process.as_mut() {
        proc_info.meta = meta;
    }
    Ok(())
}

fn apply_metadata_to_channel(
    state: &mut AppState,
    id: usize,
    meta: TrackMeta,
    top: &WebView,
    right: &WebView,
    reason: &str,
) -> Result<()> {
    let new_key = meta.key();
    if new_key.trim().is_empty() {
        return Ok(());
    }

    let (label, old_key, was_running) = {
        let channel = state
            .channels
            .iter()
            .find(|c| c.id == id)
            .ok_or_else(|| anyhow!("Channel {id} not found."))?;
        let old_key = if channel.last_meta_key.trim().is_empty() {
            channel.meta.key()
        } else {
            channel.last_meta_key.clone()
        };
        (channel.label.clone(), old_key, channel.process.is_some())
    };

    let changed = old_key != new_key;
    if changed && was_running && state.auto_split {
        stop_channel_by_id(state, id, top, right)?;
        set_channel_metadata_exact(state, id, meta.clone())?;
        start_channel_by_id(state, id, top, right)?;
        emit_both(top, right, "log", format!("Auto split on {label}: {reason}; new take uses {}.", meta.display()));
    } else {
        set_channel_metadata_exact(state, id, meta.clone())?;
        if changed {
            emit_both(top, right, "log", format!("Metadata changed on {label}: {}.", meta.display()));
        }
    }
    emit_both(top, right, "channels", state.channel_infos());
    emit_both(top, right, "takes", &state.takes);
    Ok(())
}

fn apply_metadata_to_webview_buses(
    state: &mut AppState,
    meta: TrackMeta,
    top: &WebView,
    right: &WebView,
    reason: &str,
) {
    let ids: Vec<usize> = if state.channels.len() <= 1 {
        // In the simplified single-bus UI, the one recorder follows the WebView.
        // Even if an old provider URL was previously copied into now_playing_url,
        // WebView metadata must still update and auto-split this bus.
        state.channels.iter().map(|c| c.id).collect()
    } else {
        state
            .channels
            .iter()
            .filter(|c| c.now_playing_url.trim().is_empty())
            .map(|c| c.id)
            .collect()
    };

    if ids.is_empty() {
        emit_both(top, right, "log", "WebView metadata changed, but no WebView bus is configured yet.");
        return;
    }

    for id in ids {
        if let Err(e) = apply_metadata_to_channel(state, id, meta.clone(), top, right, reason) {
            emit_both(top, right, "error", format!("Could not apply metadata to bus {id}: {e}"));
        }
    }
}

fn parse_webview_title(page_title: &str) -> Option<TrackMeta> {
    let mut title = page_title.trim().to_string();
    if title.is_empty() {
        return None;
    }
    for suffix in [
        " | Deezer",
        " - Deezer",
        " | Qobuz",
        " - Qobuz",
        " | TIDAL",
        " - TIDAL",
        " | YouTube Music",
        " - YouTube Music",
    ] {
        if let Some(stripped) = title.strip_suffix(suffix) {
            title = stripped.trim().to_string();
        }
    }
    parse_artist_title_text(&title)
}

fn virtual_audio_driver_inf() -> Option<PathBuf> {
    driver_search_roots()
        .into_iter()
        .filter(|root| root.exists())
        .find_map(|root| {
            if root.is_file()
                && root
                    .file_name()
                    .and_then(|s| s.to_str())
                    .map(|name| name.eq_ignore_ascii_case("VirtualAudioDriver.inf"))
                    .unwrap_or(false)
            {
                Some(root)
            } else {
                recursive_find_named(&root, "VirtualAudioDriver.inf", 5)
            }
        })
}

fn virtual_audio_driver_installer() -> Option<PathBuf> {
    let preferred = [
        "VirtualAudioDriverSetup.exe",
        "Virtual_Audio_Driver_Setup.exe",
        "virtual_audio_setup.exe",
        "VAD_Setup.exe",
    ];

    for root in driver_search_roots().into_iter().filter(|root| root.exists()) {
        for name in preferred {
            let direct = root.join(name);
            if direct.exists() {
                return Some(direct);
            }
        }
        if let Some(found) = recursive_find_driver_exe(&root, 4) {
            return Some(found);
        }
    }
    None
}

fn driver_search_roots() -> Vec<PathBuf> {
    let mut roots = Vec::new();
    if let Ok(cwd) = std::env::current_dir() {
        roots.push(cwd.join("drivers"));
        roots.push(cwd.join("Virtual Audio Driver"));
        roots.push(cwd);
    }
    if let Ok(exe) = std::env::current_exe() {
        if let Some(exe_dir) = exe.parent() {
            roots.push(exe_dir.join("drivers"));
            roots.push(exe_dir.join("Virtual Audio Driver"));
            roots.push(exe_dir.to_path_buf());
        }
    }
    roots
}

fn recursive_find_named(root: &Path, wanted: &str, max_depth: usize) -> Option<PathBuf> {
    if max_depth == 0 || !root.exists() {
        return None;
    }
    let entries = fs::read_dir(root).ok()?;
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_file()
            && path
                .file_name()
                .and_then(|s| s.to_str())
                .map(|name| name.eq_ignore_ascii_case(wanted))
                .unwrap_or(false)
        {
            return Some(path);
        }
        if path.is_dir() {
            if let Some(found) = recursive_find_named(&path, wanted, max_depth - 1) {
                return Some(found);
            }
        }
    }
    None
}

fn recursive_find_driver_exe(root: &Path, max_depth: usize) -> Option<PathBuf> {
    if max_depth == 0 || !root.exists() {
        return None;
    }
    let entries = fs::read_dir(root).ok()?;
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_file() {
            let name = path
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("")
                .to_ascii_lowercase();
            if name.ends_with(".exe")
                && (name.contains("virtual") || name.contains("audio") || name.contains("vad"))
                && (name.contains("setup") || name.contains("install") || name.contains("driver"))
            {
                return Some(path);
            }
        }
        if path.is_dir() {
            if let Some(found) = recursive_find_driver_exe(&path, max_depth - 1) {
                return Some(found);
            }
        }
    }
    None
}

fn powershell_single_quote(path: &Path) -> String {
    path.display().to_string().replace('\'', "''")
}

fn powershell_string_literal(text: &str) -> String {
    text.replace('\'', "''")
}

fn encode_powershell(script: &str) -> String {
    let bytes: Vec<u8> = script
        .encode_utf16()
        .flat_map(|w| w.to_le_bytes())
        .collect();
    general_purpose::STANDARD.encode(bytes)
}

fn run_elevated_powershell(script: &str, context: &str) -> Result<()> {
    let encoded = encode_powershell(script);
    let command = format!(
        "Start-Process -FilePath 'powershell.exe' -ArgumentList @('-NoProfile','-ExecutionPolicy','Bypass','-EncodedCommand','{}') -Verb RunAs -WindowStyle Normal",
        encoded
    );
    let mut cmd = Command::new("powershell");
    cmd.args([
        "-NoProfile",
        "-ExecutionPolicy",
        "Bypass",
        "-WindowStyle",
        "Hidden",
        "-Command",
        &command,
    ]);
    spawn_no_console(cmd).with_context(|| format!("Failed to start elevated PowerShell for {context}"))
}

fn enable_test_signing_and_run_driver_installer(installer: &Path) -> Result<()> {
    let installer_text = powershell_single_quote(installer);
    let script = format!(
        "$ErrorActionPreference='Continue';\n\
         Write-Host 'Enabling Windows Test Signing...';\n\
         bcdedit /set testsigning on | Out-Host;\n\
         Write-Host 'Launching driver installer...';\n\
         Start-Process -FilePath '{}' -Wait;\n\
         Write-Host '';\n\
         Write-Host 'Done. Restart Windows now if the audio endpoint does not appear.';\n\
         Write-Host 'After restart, open the app and press Refresh Devices.';\n\
         Start-Sleep -Seconds 8;",
        installer_text
    );
    run_elevated_powershell(&script, "automatic driver installer with Test Signing")
}

fn install_virtual_audio_driver_with_test_signing(inf: &Path) -> Result<()> {
    let inf_text = powershell_single_quote(inf);
    let install_script = install_virtual_audio_driver_script();
    let install_command = if let Some(script_path) = install_script {
        format!("& '{}' -InfPath '{}'", powershell_single_quote(&script_path), inf_text)
    } else {
        inline_virtual_audio_driver_install_script(&inf_text)
    };
    let script = format!(
        "$ErrorActionPreference='Continue';\n\
         Write-Host 'Enabling Windows Test Signing...';\n\
         bcdedit /set testsigning on | Out-Host;\n\
         Write-Host 'Installing Virtual Audio Driver automatically...';\n\
         {};\n\
         Write-Host '';\n\
         Write-Host 'Done. If Test Signing was changed, restart Windows once. Then open the recorder and press Refresh Devices.';\n\
         Write-Host 'No Add Legacy Hardware wizard is needed unless Windows blocks the driver completely.';\n\
         Start-Sleep -Seconds 12;",
        install_command
    );
    run_elevated_powershell(&script, "automatic INF driver installation with Test Signing")
}

fn inline_virtual_audio_driver_install_script(inf_text: &str) -> String {
    format!(r#"$InfPath='{}'
$HardwareId='ROOT\VirtualAudioDriver'
Write-Host 'Adding driver package to the Windows driver store...'
pnputil /add-driver $InfPath | Out-Host
Write-Host 'Creating ROOT\VirtualAudioDriver device and binding driver automatically...'
$roots = @((Split-Path -Parent $InfPath), (Get-Location).Path)
$devcon = $null
foreach ($root in $roots) {{
  if (Test-Path $root) {{
    $devcon = Get-ChildItem -Path $root -Filter devcon.exe -File -Recurse -ErrorAction SilentlyContinue | Select-Object -First 1
    if ($devcon) {{ break }}
  }}
}}
if ($devcon) {{
  Write-Host "Using devcon.exe: $($devcon.FullName)"
  & $devcon.FullName install $InfPath $HardwareId | Out-Host
}} else {{
  $src = @"
using System;
using System.Runtime.InteropServices;
public static class RootDeviceInstaller {{
  [StructLayout(LayoutKind.Sequential)]
  public struct SP_DEVINFO_DATA {{ public UInt32 cbSize; public Guid ClassGuid; public UInt32 DevInst; public IntPtr Reserved; }}
  [DllImport("setupapi.dll", SetLastError=true, CharSet=CharSet.Unicode)]
  public static extern IntPtr SetupDiCreateDeviceInfoList(ref Guid ClassGuid, IntPtr hwndParent);
  [DllImport("setupapi.dll", SetLastError=true, CharSet=CharSet.Unicode)]
  public static extern bool SetupDiCreateDeviceInfo(IntPtr DeviceInfoSet, string DeviceName, ref Guid ClassGuid, string DeviceDescription, IntPtr hwndParent, UInt32 CreationFlags, out SP_DEVINFO_DATA DeviceInfoData);
  [DllImport("setupapi.dll", SetLastError=true, CharSet=CharSet.Unicode)]
  public static extern bool SetupDiSetDeviceRegistryProperty(IntPtr DeviceInfoSet, ref SP_DEVINFO_DATA DeviceInfoData, UInt32 Property, byte[] PropertyBuffer, UInt32 PropertyBufferSize);
  [DllImport("setupapi.dll", SetLastError=true)]
  public static extern bool SetupDiCallClassInstaller(UInt32 InstallFunction, IntPtr DeviceInfoSet, ref SP_DEVINFO_DATA DeviceInfoData);
  [DllImport("setupapi.dll", SetLastError=true)]
  public static extern bool SetupDiDestroyDeviceInfoList(IntPtr DeviceInfoSet);
  [DllImport("newdev.dll", SetLastError=true, CharSet=CharSet.Unicode)]
  public static extern bool UpdateDriverForPlugAndPlayDevices(IntPtr hwndParent, string HardwareId, string FullInfPath, UInt32 InstallFlags, out bool RebootRequired);
  public static void Install(string infPath, string hardwareId) {{
    Guid mediaClass = new Guid("4d36e96c-e325-11ce-bfc1-08002be10318");
    IntPtr set = SetupDiCreateDeviceInfoList(ref mediaClass, IntPtr.Zero);
    if (set == IntPtr.Zero || set.ToInt64() == -1) throw new System.ComponentModel.Win32Exception(Marshal.GetLastWin32Error(), "SetupDiCreateDeviceInfoList failed");
    try {{
      SP_DEVINFO_DATA data = new SP_DEVINFO_DATA();
      data.cbSize = (UInt32)Marshal.SizeOf(typeof(SP_DEVINFO_DATA));
      bool created = SetupDiCreateDeviceInfo(set, "VirtualAudioDriver", ref mediaClass, "Virtual Audio Driver", IntPtr.Zero, 0x00000001, out data);
      if (!created) {{
        int err = Marshal.GetLastWin32Error();
        if (err != unchecked((int)0xE000020B) && err != 0x000000B7) throw new System.ComponentModel.Win32Exception(err, "SetupDiCreateDeviceInfo failed");
      }} else {{
        byte[] hwid = System.Text.Encoding.Unicode.GetBytes(hardwareId + "\0\0");
        if (!SetupDiSetDeviceRegistryProperty(set, ref data, 0x00000001, hwid, (UInt32)hwid.Length)) throw new System.ComponentModel.Win32Exception(Marshal.GetLastWin32Error(), "SetupDiSetDeviceRegistryProperty failed");
        if (!SetupDiCallClassInstaller(0x00000019, set, ref data)) throw new System.ComponentModel.Win32Exception(Marshal.GetLastWin32Error(), "SetupDiCallClassInstaller DIF_REGISTERDEVICE failed");
      }}
      bool reboot;
      bool updated = UpdateDriverForPlugAndPlayDevices(IntPtr.Zero, hardwareId, infPath, 0x00000001, out reboot);
      if (!updated) {{
        int err = Marshal.GetLastWin32Error();
        throw new System.ComponentModel.Win32Exception(err, "UpdateDriverForPlugAndPlayDevices failed");
      }}
      if (reboot) Console.WriteLine("Driver requested reboot.");
    }} finally {{ SetupDiDestroyDeviceInfoList(set); }}
  }}
}}
"@
  Add-Type -TypeDefinition $src -Language CSharp
  [RootDeviceInstaller]::Install($InfPath, $HardwareId)
}}
pnputil /scan-devices | Out-Host
Start-Sleep -Seconds 2
$found = Get-PnpDevice -InstanceId 'ROOT\VirtualAudioDriver*' -ErrorAction SilentlyContinue
if (-not $found) {{
  Write-Host 'ROOT\VirtualAudioDriver was not visible yet. Trying pnputil direct install once more...'
  pnputil /add-driver $InfPath /install | Out-Host
  $found = Get-PnpDevice -InstanceId 'ROOT\VirtualAudioDriver*' -ErrorAction SilentlyContinue
}}
if ($found) {{
  $found | Format-Table -AutoSize | Out-Host
  Write-Host 'Virtual Audio Driver device node exists. Restart Windows if the endpoint does not appear yet.'
}} else {{
  throw 'Automatic device creation failed. The driver package may not contain ROOT\VirtualAudioDriver or Windows blocked the driver signature.'
}}
Start-Process -FilePath explorer.exe -ArgumentList 'ms-settings:sound' | Out-Null
"#, inf_text)
}

fn auto_install_virtual_audio_driver(_top: &WebView, _right: &WebView) -> Result<()> {
    Err(anyhow!("No free audio endpoint is available. Click Install automatically to enable Test Signing and create the virtual audio device."))
}

fn install_virtual_audio_driver_script() -> Option<PathBuf> {
    let mut candidates = Vec::new();
    if let Ok(cwd) = std::env::current_dir() {
        candidates.push(cwd.join("tools").join("install_virtual_audio_driver.ps1"));
    }
    if let Ok(exe) = std::env::current_exe() {
        if let Some(exe_dir) = exe.parent() {
            candidates.push(
                exe_dir
                    .join("..")
                    .join("..")
                    .join("tools")
                    .join("install_virtual_audio_driver.ps1"),
            );
        }
    }
    candidates.into_iter().find(|path| path.exists())
}

fn add_channel(
    state: &mut AppState,
    device: String,
    label: String,
    playback_provider: String,
    playback_url: String,
    now_playing_url: String,
    meta: TrackMeta,
) -> usize {
    let id = state.next_channel_id;
    state.next_channel_id += 1;
    state.channels.push(Channel {
        id,
        label,
        device,
        playback_provider,
        playback_url,
        now_playing_url: now_playing_url.trim().to_string(),
        last_meta_key: meta.key(),
        meta,
        process: None,
    });
    id
}

fn ensure_single_recording_bus(state: &mut AppState) -> usize {
    if state.channels.is_empty() {
        return add_channel(
            state,
            "WASAPI Loopback: Default Output".to_string(),
            "Main Recording".to_string(),
            "own".to_string(),
            String::new(),
            state.now_playing_url.clone(),
            state.active_meta.clone(),
        );
    }

    let id = state.channels[0].id;
    if state.channels.len() > 1 {
        state.channels.truncate(1);
    }
    if state.channels[0].device.trim().is_empty() {
        state.channels[0].device = "WASAPI Loopback: Default Output".to_string();
    }
    id
}


fn preferred_device_for_new_bus(
    state: &AppState,
    requested: &str,
    top: &WebView,
    right: &WebView,
) -> Result<Option<String>> {
    // Bus 1 is intentionally always the Windows default WASAPI loopback.
    // It records whatever is already playing on the default output and does not require a virtual driver.
    if state.channels.is_empty() {
        return Ok(Some("WASAPI Loopback: Default Output".to_string()));
    }

    let devices = list_audio_devices()?;

    // For bus 2+ prefer an explicitly selected virtual/loopback endpoint if it is free.
    if !requested.trim().is_empty() && requested != "WASAPI Loopback: Default Output" {
        match compatible_recording_device(requested) {
            Ok(device) if is_virtual_audio_device(&device) && !capture_device_assigned(state, &device) => {
                return Ok(Some(device));
            }
            Ok(device) if capture_device_assigned(state, &device) => emit_both(
                top,
                right,
                "log",
                format!("{device} is already assigned to another bus. Looking for a free virtual endpoint."),
            ),
            Ok(device) => emit_both(
                top,
                right,
                "log",
                format!("{device} is not a virtual bus endpoint. Bus 2+ will use a dedicated virtual device instead."),
            ),
            Err(e) => emit_both(
                top,
                right,
                "log",
                format!("Selected endpoint is not available anymore: {e}. Looking for a free virtual endpoint."),
            ),
        }
    }

    Ok(first_unassigned_virtual_capture_device(state, &devices))
}

fn first_unassigned_virtual_capture_device(state: &AppState, devices: &[String]) -> Option<String> {
    devices
        .iter()
        .filter(|device| is_virtual_audio_device(device))
        .find(|device| !capture_device_assigned(state, device))
        .cloned()
}

fn wait_for_unassigned_virtual_capture_device(
    state: &AppState,
    timeout: Duration,
) -> Result<Option<String>> {
    let start = std::time::Instant::now();
    while start.elapsed() < timeout {
        let devices = list_audio_devices()?;
        if let Some(device) = first_unassigned_virtual_capture_device(state, &devices) {
            return Ok(Some(device));
        }
        thread::sleep(Duration::from_millis(700));
    }
    Ok(None)
}

fn is_virtual_audio_device(device: &str) -> bool {
    let lower = device.to_ascii_lowercase();
    lower.contains("virtual")
        || lower.contains("cable")
        || lower.contains("vb-audio")
        || lower.contains("voicemeeter")
        || lower.contains("vad")
}

fn create_virtual_audio_device_for_bus(bus_number: usize) -> Result<()> {
    let inf = virtual_audio_driver_inf().ok_or_else(|| {
        anyhow!("No bundled VirtualAudioDriver.inf was found. Put the shipped driver folder into ./drivers next to the app.")
    })?;
    create_virtual_audio_device_with_test_signing(&inf, bus_number)
}

fn create_virtual_audio_device_with_test_signing(inf: &Path, bus_number: usize) -> Result<()> {
    let inf_text = powershell_single_quote(inf);
    let safe_bus = bus_number.max(2);
    let device_name = powershell_string_literal(&format!("VirtualAudioDriverBus{:02}", safe_bus));
    let display_name = powershell_string_literal(&format!("Virtual Audio Driver Bus {:02}", safe_bus));
    let install_command = inline_virtual_audio_driver_install_script_for_device(&inf_text, &device_name, &display_name);
    let script = format!(
        "$ErrorActionPreference='Continue';\n\
         Write-Host 'Enabling Windows Test Signing...';\n\
         bcdedit /set testsigning on | Out-Host;\n\
         Write-Host 'Creating dedicated Virtual Audio Driver device for Bus {safe_bus}...';\n\
         {};\n\
         Write-Host '';\n\
         Write-Host 'Done. Restart Windows if the new audio endpoint does not appear yet, then press Refresh Devices.';\n\
         Start-Sleep -Seconds 12;",
        install_command
    );
    run_elevated_powershell(&script, "create dedicated virtual audio bus device")
}

fn inline_virtual_audio_driver_install_script_for_device(
    inf_text: &str,
    _device_name: &str,
    display_name: &str,
) -> String {
    format!(r#"$InfPath='{}'
$HardwareId='ROOT\VirtualAudioDriver'
$RootDeviceId='VirtualAudioDriver'
$DisplayName='{}'
Write-Host 'Adding driver package to the Windows driver store...'
pnputil /add-driver $InfPath | Out-Host
Write-Host "Creating another root-enumerated instance for $HardwareId..."
Write-Host 'Important: every bus uses the same hardware id. Windows should create ROOT\VIRTUALAUDIODRIVER\0000, 0001, 0002, ...'
$before = @(Get-PnpDevice -InstanceId 'ROOT\VIRTUALAUDIODRIVER\*' -ErrorAction SilentlyContinue).Count
Write-Host "Existing ROOT\VIRTUALAUDIODRIVER instances before: $before"
$roots = @((Split-Path -Parent $InfPath), (Get-Location).Path)
$devcon = $null
foreach ($root in $roots) {{
  if (Test-Path $root) {{
    $devcon = Get-ChildItem -Path $root -Filter devcon.exe -File -Recurse -ErrorAction SilentlyContinue | Select-Object -First 1
    if ($devcon) {{ break }}
  }}
}}
if ($devcon) {{
  Write-Host "Using devcon.exe: $($devcon.FullName)"
  & $devcon.FullName install $InfPath $HardwareId | Out-Host
}} else {{
  Write-Host 'devcon.exe was not found. Using built-in SetupAPI/NewDev method.'
  $src = @"
using System;
using System.Runtime.InteropServices;
public static class RootDeviceInstaller {{
  [StructLayout(LayoutKind.Sequential)]
  public struct SP_DEVINFO_DATA {{ public UInt32 cbSize; public Guid ClassGuid; public UInt32 DevInst; public IntPtr Reserved; }}
  [DllImport("setupapi.dll", SetLastError=true, CharSet=CharSet.Unicode)]
  public static extern IntPtr SetupDiCreateDeviceInfoList(ref Guid ClassGuid, IntPtr hwndParent);
  [DllImport("setupapi.dll", SetLastError=true, CharSet=CharSet.Unicode)]
  public static extern bool SetupDiCreateDeviceInfo(IntPtr DeviceInfoSet, string DeviceName, ref Guid ClassGuid, string DeviceDescription, IntPtr hwndParent, UInt32 CreationFlags, out SP_DEVINFO_DATA DeviceInfoData);
  [DllImport("setupapi.dll", SetLastError=true, CharSet=CharSet.Unicode)]
  public static extern bool SetupDiSetDeviceRegistryProperty(IntPtr DeviceInfoSet, ref SP_DEVINFO_DATA DeviceInfoData, UInt32 Property, byte[] PropertyBuffer, UInt32 PropertyBufferSize);
  [DllImport("setupapi.dll", SetLastError=true)]
  public static extern bool SetupDiCallClassInstaller(UInt32 InstallFunction, IntPtr DeviceInfoSet, ref SP_DEVINFO_DATA DeviceInfoData);
  [DllImport("setupapi.dll", SetLastError=true)]
  public static extern bool SetupDiDestroyDeviceInfoList(IntPtr DeviceInfoSet);
  [DllImport("newdev.dll", SetLastError=true, CharSet=CharSet.Unicode)]
  public static extern bool UpdateDriverForPlugAndPlayDevices(IntPtr hwndParent, string HardwareId, string FullInfPath, UInt32 InstallFlags, out bool RebootRequired);
  public static void Install(string infPath, string hardwareId, string rootDeviceId, string displayName) {{
    Guid mediaClass = new Guid("4d36e96c-e325-11ce-bfc1-08002be10318");
    IntPtr set = SetupDiCreateDeviceInfoList(ref mediaClass, IntPtr.Zero);
    if (set == IntPtr.Zero || set.ToInt64() == -1) throw new System.ComponentModel.Win32Exception(Marshal.GetLastWin32Error(), "SetupDiCreateDeviceInfoList failed");
    try {{
      SP_DEVINFO_DATA data = new SP_DEVINFO_DATA();
      data.cbSize = (UInt32)Marshal.SizeOf(typeof(SP_DEVINFO_DATA));
      // DICD_GENERATE_ID creates a new unique instance under ROOT\\VIRTUALAUDIODRIVER\\0000, 0001, ...
      // DeviceName must be the root-enumerated device id from the INF, not a bus-specific id.
      bool created = SetupDiCreateDeviceInfo(set, rootDeviceId, ref mediaClass, displayName, IntPtr.Zero, 0x00000001, out data);
      if (!created) {{
        int err = Marshal.GetLastWin32Error();
        throw new System.ComponentModel.Win32Exception(err, "SetupDiCreateDeviceInfo failed");
      }}
      byte[] hwid = System.Text.Encoding.Unicode.GetBytes(hardwareId + "\0\0");
      if (!SetupDiSetDeviceRegistryProperty(set, ref data, 0x00000001, hwid, (UInt32)hwid.Length)) throw new System.ComponentModel.Win32Exception(Marshal.GetLastWin32Error(), "SetupDiSetDeviceRegistryProperty failed");
      if (!SetupDiCallClassInstaller(0x00000019, set, ref data)) throw new System.ComponentModel.Win32Exception(Marshal.GetLastWin32Error(), "SetupDiCallClassInstaller DIF_REGISTERDEVICE failed");
      bool reboot;
      bool updated = UpdateDriverForPlugAndPlayDevices(IntPtr.Zero, hardwareId, infPath, 0x00000001, out reboot);
      if (!updated) {{
        int err = Marshal.GetLastWin32Error();
        throw new System.ComponentModel.Win32Exception(err, "UpdateDriverForPlugAndPlayDevices failed");
      }}
      if (reboot) Console.WriteLine("Driver requested reboot.");
    }} finally {{ SetupDiDestroyDeviceInfoList(set); }}
  }}
}}
"@
  Add-Type -TypeDefinition $src -Language CSharp
  [RootDeviceInstaller]::Install($InfPath, $HardwareId, $RootDeviceId, $DisplayName)
}}
pnputil /scan-devices | Out-Host
Start-Sleep -Seconds 3
$devices = @(Get-PnpDevice -InstanceId 'ROOT\VIRTUALAUDIODRIVER\*' -ErrorAction SilentlyContinue)
$after = $devices.Count
Write-Host "ROOT\VIRTUALAUDIODRIVER instances after: $after"
if ($devices) {{
  $devices | Format-Table -AutoSize | Out-Host
}}
if ($after -le $before) {{
  Write-Host 'No additional ROOT\VIRTUALAUDIODRIVER instance appeared.' -ForegroundColor Yellow
  Write-Host 'This means Windows or this driver build rejected multi-instance creation. The driver may expose only one speaker/mic pair unless the driver source/INF is changed for multi-instance support.' -ForegroundColor Yellow
  throw 'No new virtual audio device instance appeared.'
}}
Write-Host 'New root device instance was created. Restart Windows if the new audio endpoint is not visible yet.' -ForegroundColor Green
Start-Process -FilePath explorer.exe -ArgumentList 'ms-settings:sound' | Out-Null
"#, inf_text, display_name)
}

fn capture_device_for_new_bus(
    state: &AppState,
    requested: &str,
    top: &WebView,
    right: &WebView,
) -> Result<Option<String>> {
    let devices = list_audio_devices()?;
    if !requested.trim().is_empty() {
        match compatible_recording_device(requested) {
            Ok(device) if !capture_device_assigned(state, &device) => return Ok(Some(device)),
            Ok(device) => emit_both(
                top,
                right,
                "log",
                format!(
                    "{device} is already assigned to another bus. Looking for a free endpoint."
                ),
            ),
            Err(e) => emit_both(
                top,
                right,
                "log",
                format!(
                    "Selected endpoint is not available anymore: {e}. Looking for a free endpoint."
                ),
            ),
        }
    }

    Ok(first_unassigned_capture_device(state, &devices))
}

fn first_unassigned_capture_device(state: &AppState, devices: &[String]) -> Option<String> {
    devices
        .iter()
        .find(|device| !capture_device_assigned(state, device))
        .cloned()
}

fn capture_device_assigned(state: &AppState, device: &str) -> bool {
    let wanted = capture_device_key(device);
    state
        .channels
        .iter()
        .any(|channel| capture_device_key(&channel.device) == wanted)
}

fn capture_device_key(device: &str) -> String {
    let trimmed = device.trim();
    let (kind, name) = if let Some(name) = trimmed.strip_prefix("DirectShow: ") {
        ("dshow", name)
    } else if let Some(name) = trimmed.strip_prefix("WASAPI Loopback: ") {
        ("wasapi", name)
    } else {
        ("dshow", trimmed)
    };
    format!("{kind}:{}", name.trim().to_ascii_lowercase())
}

fn start_channel_by_id(
    state: &mut AppState,
    id: usize,
    top: &WebView,
    right: &WebView,
) -> Result<()> {
    let idx = state
        .channels
        .iter()
        .position(|c| c.id == id)
        .ok_or_else(|| anyhow!("Channel {id} not found."))?;
    if state.channels[idx].process.is_some() {
        emit_both(
            top,
            right,
            "log",
            format!("{} is already recording.", state.channels[idx].label),
        );
        return Ok(());
    }
    let locked_device = compatible_recording_device(&state.channels[idx].device)?;
    if state
        .channels
        .iter()
        .enumerate()
        .any(|(other_idx, channel)| {
            other_idx != idx
                && channel.process.is_some()
                && compatible_recording_device(&channel.device)
                    .map(|device| capture_device_key(&device) == capture_device_key(&locked_device))
                    .unwrap_or(false)
        })
    {
        return Err(anyhow!(
            "{} is already being recorded by another bus. One bus needs one real capture endpoint.",
            locked_device
        ));
    }
    fs::create_dir_all(&state.output_dir)?;
    let mut meta = state.channels[idx].meta.clone();
    if !meta_has_any_value(&meta) {
        meta = state.active_meta.clone();
        state.channels[idx].meta = meta.clone();
    }
    let ext = "flac";
    let stamp = Local::now().format("%Y%m%d_%H%M%S").to_string();
    let base = sanitize_filename(&format!(
        "{}_{}_{}",
        state.channels[idx].label,
        meta.display(),
        stamp
    ));
    let path = state.output_dir.join(format!("{base}.{ext}"));
    let stderr_log = std::env::temp_dir().join(format!("{base}.ffmpeg.log"));
    let (mut child, wasapi_stop, wasapi_thread, effective_device) =
        if locked_device.starts_with("WASAPI Loopback: ") {
            start_wasapi_loopback_recording(
                &locked_device,
                &path,
                &stderr_log,
                &state.format,
                &state.bit_depth,
                &state.sample_rate,
                top,
                right,
                &state.channels[idx].label,
            )?
        } else {
            let (args, effective_device) = ffmpeg_record_args(
                &state.channels[idx].device,
                &path,
                &state.format,
                &state.bit_depth,
                &state.sample_rate,
            )?;
            emit_both(
                top,
                right,
                "log",
                format!(
                    "Starting {}: ffmpeg {}",
                    state.channels[idx].label,
                    args.join(" ")
                ),
            );
            let child = spawn_ffmpeg_encoder(&args, &stderr_log)?;
            (child, None, None, effective_device)
        };

    thread::sleep(Duration::from_millis(700));
    if let Some(status) = child.try_wait()? {
        let log_tail = read_text_tail(&stderr_log, 3000);
        let _ = fs::remove_file(&stderr_log);
        return Err(anyhow!(
            "FFmpeg stopped immediately with exit code {:?}. No FLAC was created.\n\n{}",
            status.code(),
            log_tail
        ));
    }

    state.channels[idx].process = Some(RecorderProcess {
        child,
        wasapi_stop,
        wasapi_thread,
        path: path.clone(),
        stderr_log: stderr_log.clone(),
        meta,
        format: state.format.clone(),
        bit_depth: state.bit_depth.clone(),
        sample_rate: state.sample_rate.clone(),
        speed4x: state.speed4x,
    });
    emit_both(
        top,
        right,
        "log",
        format!(
            "Recording {} from {} to {}",
            state.channels[idx].label,
            effective_device,
            path.display()
        ),
    );
    Ok(())
}

fn stop_channel_by_id(
    state: &mut AppState,
    id: usize,
    top: &WebView,
    right: &WebView,
) -> Result<()> {
    let idx = state
        .channels
        .iter()
        .position(|c| c.id == id)
        .ok_or_else(|| anyhow!("Channel {id} not found."))?;
    let label = state.channels[idx].label.clone();
    if let Some(mut proc_info) = state.channels[idx].process.take() {
        emit_both(top, right, "log", format!("Stopping {label}..."));
        if let Some(stop) = &proc_info.wasapi_stop {
            stop.store(true, Ordering::SeqCst);
            proc_info.child.stdin.take();
        } else if let Some(stdin) = proc_info.child.stdin.as_mut() {
            let _ = stdin.write_all(b"q\n");
        }
        if let Some(worker) = proc_info.wasapi_thread.take() {
            match worker.join() {
                Ok(Ok(())) => {}
                Ok(Err(e)) => emit_both(
                    top,
                    right,
                    "error",
                    format!("WASAPI loopback stopped with an error: {e}"),
                ),
                Err(_) => emit_both(top, right, "error", "WASAPI loopback worker crashed."),
            }
        }
        let mut status = None;
        for _ in 0..40 {
            if let Some(exit_status) = proc_info.child.try_wait()? {
                status = Some(exit_status);
                break;
            }
            thread::sleep(Duration::from_millis(100));
        }
        if status.is_none() {
            let _ = proc_info.child.kill();
            status = proc_info.child.wait().ok();
        }
        let file_len = proc_info.path.metadata().map(|m| m.len()).unwrap_or(0);
        if file_len == 0 {
            let log_tail = read_text_tail(&proc_info.stderr_log, 3000);
            let _ = fs::remove_file(&proc_info.stderr_log);
            emit_both(
                top,
                right,
                "error",
                format!(
                    "No audio file was written for {label}. FFmpeg log:\n{}",
                    log_tail
                ),
            );
            return Ok(());
        }
        if proc_info.path.exists() {
            if let Some(exit_status) = status {
                if !exit_status.success() {
                    emit_both(top, right, "log", format!("FFmpeg ended with exit code {:?}. The file exists, so metadata will still be written if possible.", exit_status.code()));
                }
            }
            if proc_info.speed4x {
                match slow_down_4x(
                    &proc_info.path,
                    &proc_info.format,
                    &proc_info.bit_depth,
                    &proc_info.sample_rate,
                ) {
                    Ok(_) => emit_both(top, right, "log", "4x true-speed post-process finished."),
                    Err(e) => {
                        emit_both(top, right, "error", format!("4x post-process failed: {e}"))
                    }
                }
            }
            match embed_metadata(&proc_info.path, &proc_info.meta, &proc_info.format) {
                Ok(_) => emit_both(
                    top,
                    right,
                    "log",
                    format!("Metadata written to {}", proc_info.path.display()),
                ),
                Err(e) => emit_both(
                    top,
                    right,
                    "error",
                    format!("Metadata embedding failed: {e}"),
                ),
            }
            let mut take = HashMap::new();
            take.insert("channel".to_string(), label);
            take.insert("artist".to_string(), proc_info.meta.artist.clone());
            take.insert("title".to_string(), proc_info.meta.display());
            take.insert("album".to_string(), proc_info.meta.album.clone());
            take.insert("path".to_string(), proc_info.path.display().to_string());
            state.takes.push(take);
        }
        let _ = fs::remove_file(&proc_info.stderr_log);
    }
    Ok(())
}

fn auto_split_on_current_metadata(
    state: &mut AppState,
    top: &WebView,
    right: &WebView,
    reason: &str,
) {
    let meta = state.active_meta.clone();
    apply_metadata_to_webview_buses(state, meta, top, right, reason);
}

fn stop_all_channels(state: &mut AppState, top: &WebView, right: &WebView) {
    let ids: Vec<usize> = state.channels.iter().map(|c| c.id).collect();
    for id in ids {
        let _ = stop_channel_by_id(state, id, top, right);
    }
}

fn ffmpeg_record_args(
    device: &str,
    path: &Path,
    format: &str,
    bit_depth: &str,
    sample_rate: &str,
) -> Result<(Vec<String>, String)> {
    let effective_device = compatible_recording_device(device)?;
    let mut args = vec!["-y".to_string()];
    if effective_device == "WASAPI Loopback: Default Output" {
        args.extend([
            "-f".to_string(),
            "wasapi".to_string(),
            "-i".to_string(),
            "default".to_string(),
        ]);
    } else if let Some(name) = effective_device.strip_prefix("WASAPI Loopback: ") {
        args.extend([
            "-f".to_string(),
            "wasapi".to_string(),
            "-i".to_string(),
            name.to_string(),
        ]);
    } else {
        let dshow_device = effective_device
            .strip_prefix("DirectShow: ")
            .unwrap_or(&effective_device);
        args.extend([
            "-f".to_string(),
            "dshow".to_string(),
            "-i".to_string(),
            format!("audio={dshow_device}"),
        ]);
    }
    args.extend(["-map".to_string(), "0:a".to_string()]);
    if sample_rate != "auto" {
        args.push("-ar".to_string());
        args.push(sample_rate.to_string());
    }
    args.extend(encoder_args(format, bit_depth));
    args.push(path.display().to_string());
    Ok((args, effective_device))
}

fn compatible_recording_device(requested: &str) -> Result<String> {
    let requested = requested.trim();
    if requested.is_empty() {
        return nonempty_default_recording_device().ok_or_else(|| {
            anyhow!(
                "No compatible FFmpeg audio input was found. Install/enable a real recording device or virtual audio driver, then press Refresh."
            )
        });
    }

    if requested.starts_with("WASAPI Loopback: ") {
        return Ok(requested.to_string());
    }

    if requested.starts_with("DirectShow: ") {
        let directshow_devices = directshow_audio_devices();
        if directshow_devices.iter().any(|device| device == &requested) {
            return Ok(requested.to_string());
        }
        return Err(anyhow!("DirectShow audio device '{requested}' was not found by FFmpeg. Install/enable the virtual audio driver, then press Refresh."));
    }

    let directshow_name = format!("DirectShow: {requested}");
    if directshow_audio_devices()
        .iter()
        .any(|device| device == &directshow_name)
    {
        return Ok(directshow_name);
    }

    Err(anyhow!(
        "Audio device '{requested}' was not found by FFmpeg as a real capture endpoint."
    ))
}

fn encoder_args(format: &str, bit_depth: &str) -> Vec<String> {
    let bits = match bit_depth {
        "16" => "16",
        "32" => "32",
        _ => "24",
    };
    if format.eq_ignore_ascii_case("wav") {
        return vec!["-c:a".into(), format!("pcm_s{}le", bits)];
    }
    let mut args = vec!["-c:a".into(), "flac".into()];
    if bits == "16" {
        args.extend(["-sample_fmt".into(), "s16".into()]);
    } else {
        args.extend([
            "-sample_fmt".into(),
            "s32".into(),
            "-bits_per_raw_sample".into(),
            bits.into(),
        ]);
    }
    args
}

fn slow_down_4x(path: &Path, format: &str, bit_depth: &str, sample_rate: &str) -> Result<()> {
    let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("audio");
    let tmp = path.with_extension(format!("tmp.{ext}"));
    let mut args = vec![
        "-y".to_string(),
        "-i".to_string(),
        path.display().to_string(),
        "-filter:a".to_string(),
        "atempo=0.5,atempo=0.5".to_string(),
    ];
    if sample_rate != "auto" {
        args.extend(["-ar".to_string(), sample_rate.to_string()]);
    }
    args.extend(encoder_args(format, bit_depth));
    args.push(tmp.display().to_string());
    run_ffmpeg(args, "4x true-speed post-process")?;
    fs::rename(&tmp, path)?;
    Ok(())
}

fn embed_metadata(path: &Path, meta: &TrackMeta, format: &str) -> Result<()> {
    if meta.artist.trim().is_empty()
        && meta.title.trim().is_empty()
        && meta.album.trim().is_empty()
        && meta.cover_url.trim().is_empty()
    {
        return Ok(());
    }
    let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("audio");
    let tmp = path.with_extension(format!("tagged.{ext}"));
    let mut args = vec![
        "-y".to_string(),
        "-i".to_string(),
        path.display().to_string(),
    ];
    let has_cover = format.eq_ignore_ascii_case("flac") && !meta.cover_url.trim().is_empty();
    if has_cover {
        args.extend(["-i".to_string(), meta.cover_url.clone()]);
        args.extend([
            "-map".to_string(),
            "0:a".to_string(),
            "-map".to_string(),
            "1:v".to_string(),
        ]);
        args.extend([
            "-c:a".to_string(),
            "copy".to_string(),
            "-c:v".to_string(),
            "copy".to_string(),
            "-disposition:v".to_string(),
            "attached_pic".to_string(),
        ]);
    } else {
        args.extend([
            "-map".to_string(),
            "0:a".to_string(),
            "-c:a".to_string(),
            "copy".to_string(),
        ]);
    }
    if !meta.artist.trim().is_empty() {
        args.extend([
            "-metadata".to_string(),
            format!("artist={}", meta.artist.trim()),
        ]);
    }
    if !meta.artist.trim().is_empty() || !meta.title.trim().is_empty() {
        args.extend([
            "-metadata".to_string(),
            format!("title={}", meta.display()),
        ]);
    }
    if !meta.album.trim().is_empty() {
        args.extend([
            "-metadata".to_string(),
            format!("album={}", meta.album.trim()),
        ]);
    }
    args.push(tmp.display().to_string());
    run_ffmpeg(args, "metadata embedding")?;
    fs::rename(&tmp, path)?;
    Ok(())
}

fn run_ffmpeg(args: Vec<String>, context: &str) -> Result<()> {
    let mut cmd = Command::new(find_ffmpeg());
    cmd.args(args).stdout(Stdio::null()).stderr(Stdio::null());
    hide_console(&mut cmd);
    let status = cmd
        .status()
        .with_context(|| format!("Failed to run FFmpeg for {context}"))?;
    if !status.success() {
        return Err(anyhow!(
            "FFmpeg returned a non-zero exit status during {context}."
        ));
    }
    Ok(())
}

fn spawn_ffmpeg_encoder(args: &[String], stderr_log: &Path) -> Result<Child> {
    let mut record_cmd = Command::new(find_ffmpeg());
    record_cmd
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::from(File::create(stderr_log).with_context(
            || format!("Could not create FFmpeg log at {}", stderr_log.display()),
        )?));
    hide_console(&mut record_cmd);
    record_cmd
        .spawn()
        .context("Failed to start FFmpeg. Install ffmpeg.exe or place it next to the app.")
}

fn start_wasapi_loopback_recording(
    device: &str,
    path: &Path,
    stderr_log: &Path,
    format: &str,
    bit_depth: &str,
    sample_rate: &str,
    top: &WebView,
    right: &WebView,
    label: &str,
) -> Result<(
    Child,
    Option<Arc<AtomicBool>>,
    Option<JoinHandle<Result<()>>>,
    String,
)> {
    if device != "WASAPI Loopback: Default Output" {
        emit_both(
            top,
            right,
            "log",
            format!("{device} selected; using the current default Windows output for built-in WASAPI loopback."),
        );
    }
    let raw = wasapi_default_mix_format()?;
    let args = ffmpeg_pipe_record_args(&raw, path, format, bit_depth, sample_rate);
    emit_both(
        top,
        right,
        "log",
        format!(
            "Starting {label}: built-in WASAPI loopback -> ffmpeg {}",
            args.join(" ")
        ),
    );
    let mut child = spawn_ffmpeg_encoder(&args, stderr_log)?;
    let stdin = child
        .stdin
        .take()
        .ok_or_else(|| anyhow!("Could not open FFmpeg stdin for WASAPI loopback."))?;
    let stop = Arc::new(AtomicBool::new(false));
    let worker_stop = stop.clone();
    let worker = thread::spawn(move || wasapi_loopback_to_ffmpeg(stdin, worker_stop));
    Ok((
        child,
        Some(stop),
        Some(worker),
        "WASAPI Loopback: Default Output".to_string(),
    ))
}

fn ffmpeg_pipe_record_args(
    raw: &RawAudioFormat,
    path: &Path,
    format: &str,
    bit_depth: &str,
    sample_rate: &str,
) -> Vec<String> {
    let mut args = vec![
        "-y".to_string(),
        "-f".to_string(),
        raw.ffmpeg_format.to_string(),
        "-ar".to_string(),
        raw.sample_rate.to_string(),
        "-ac".to_string(),
        raw.channels.to_string(),
        "-i".to_string(),
        "pipe:0".to_string(),
        "-map".to_string(),
        "0:a".to_string(),
    ];
    if sample_rate != "auto" {
        args.extend(["-ar".to_string(), sample_rate.to_string()]);
    }
    args.extend(encoder_args(format, bit_depth));
    args.push(path.display().to_string());
    args
}

#[cfg(windows)]
fn wasapi_default_mix_format() -> Result<RawAudioFormat> {
    thread::spawn(wasapi_default_mix_format_inner)
        .join()
        .map_err(|_| anyhow!("WASAPI format worker crashed."))?
}

#[cfg(not(windows))]
fn wasapi_default_mix_format() -> Result<RawAudioFormat> {
    Err(anyhow!("WASAPI loopback is only available on Windows."))
}

#[cfg(windows)]
fn wasapi_default_mix_format_inner() -> Result<RawAudioFormat> {
    unsafe {
        let hr = CoInitializeEx(None, COINIT_MULTITHREADED);
        let co_initialized = hr.is_ok();
        if hr.is_err() {
            return Err(anyhow!("Could not initialize Windows audio COM: {:?}", hr));
        }
        let result = (|| {
            let enumerator: IMMDeviceEnumerator =
                CoCreateInstance(&MMDeviceEnumerator, None, CLSCTX_ALL)?;
            let device = enumerator.GetDefaultAudioEndpoint(eRender, eConsole)?;
            let client: IAudioClient = device.Activate(CLSCTX_ALL, None)?;
            let mix = client.GetMixFormat()?;
            let raw = raw_audio_format_from_waveformat(mix);
            CoTaskMemFree(Some(mix as _));
            raw
        })();
        if co_initialized {
            CoUninitialize();
        }
        result.map_err(|e: anyhow::Error| e)
    }
}

#[cfg(windows)]
fn wasapi_loopback_to_ffmpeg(mut stdin: ChildStdin, stop: Arc<AtomicBool>) -> Result<()> {
    unsafe {
        let hr = CoInitializeEx(None, COINIT_MULTITHREADED);
        let co_initialized = hr.is_ok();
        if hr.is_err() {
            return Err(anyhow!("Could not initialize Windows audio COM: {:?}", hr));
        }
        let result = (|| {
            let enumerator: IMMDeviceEnumerator =
                CoCreateInstance(&MMDeviceEnumerator, None, CLSCTX_ALL)?;
            let device = enumerator.GetDefaultAudioEndpoint(eRender, eConsole)?;
            let client: IAudioClient = device.Activate(CLSCTX_ALL, None)?;
            let mix = client.GetMixFormat()?;
            let raw = raw_audio_format_from_waveformat(mix)?;
            client.Initialize(
                AUDCLNT_SHAREMODE_SHARED,
                AUDCLNT_STREAMFLAGS_LOOPBACK,
                10_000_000,
                0,
                mix,
                None,
            )?;
            CoTaskMemFree(Some(mix as _));
            let capture: IAudioCaptureClient = client.GetService()?;
            client.Start()?;
            let capture_result =
                capture_loopback_packets(&client, &capture, &raw, &mut stdin, &stop);
            let _ = client.Stop();
            capture_result
        })();
        if co_initialized {
            CoUninitialize();
        }
        result
    }
}

#[cfg(not(windows))]
fn wasapi_loopback_to_ffmpeg(_stdin: ChildStdin, _stop: Arc<AtomicBool>) -> Result<()> {
    Err(anyhow!("WASAPI loopback is only available on Windows."))
}

#[cfg(windows)]
unsafe fn capture_loopback_packets(
    _client: &IAudioClient,
    capture: &IAudioCaptureClient,
    raw: &RawAudioFormat,
    stdin: &mut ChildStdin,
    stop: &Arc<AtomicBool>,
) -> Result<()> {
    while !stop.load(Ordering::SeqCst) {
        let mut packet = capture.GetNextPacketSize()?;
        if packet == 0 {
            thread::sleep(Duration::from_millis(10));
            continue;
        }
        while packet > 0 {
            let mut data: *mut u8 = std::ptr::null_mut();
            let mut frames = 0u32;
            let mut flags = 0u32;
            capture.GetBuffer(&mut data, &mut frames, &mut flags, None, None)?;
            let byte_count = frames as usize * raw.bytes_per_frame;
            if flags & AUDCLNT_BUFFERFLAGS_SILENT.0 as u32 != 0 {
                stdin.write_all(&vec![0u8; byte_count])?;
            } else if byte_count > 0 && !data.is_null() {
                let bytes = std::slice::from_raw_parts(data, byte_count);
                stdin.write_all(bytes)?;
            }
            capture.ReleaseBuffer(frames)?;
            packet = capture.GetNextPacketSize()?;
        }
    }
    Ok(())
}

#[cfg(windows)]
unsafe fn raw_audio_format_from_waveformat(ptr: *mut WAVEFORMATEX) -> Result<RawAudioFormat> {
    if ptr.is_null() {
        return Err(anyhow!("Windows returned an empty WASAPI mix format."));
    }
    let tag = std::ptr::addr_of!((*ptr).wFormatTag).read_unaligned();
    let channels = std::ptr::addr_of!((*ptr).nChannels).read_unaligned();
    let sample_rate = std::ptr::addr_of!((*ptr).nSamplesPerSec).read_unaligned();
    let block_align = std::ptr::addr_of!((*ptr).nBlockAlign).read_unaligned();
    let bits = std::ptr::addr_of!((*ptr).wBitsPerSample).read_unaligned();
    let cb_size = std::ptr::addr_of!((*ptr).cbSize).read_unaligned();

    const WAVE_FORMAT_PCM_LOCAL: u16 = 1;
    const WAVE_FORMAT_IEEE_FLOAT_LOCAL: u16 = 3;
    const WAVE_FORMAT_EXTENSIBLE_LOCAL: u16 = 0xfffe;
    let mut effective_tag = tag;
    if tag == WAVE_FORMAT_EXTENSIBLE_LOCAL && cb_size >= 22 {
        let ext = ptr as *const WAVEFORMATEXTENSIBLE;
        let sub = std::ptr::addr_of!((*ext).SubFormat).read_unaligned();
        let pcm = windows::core::GUID::from_u128(0x00000001_0000_0010_8000_00aa00389b71);
        let float = windows::core::GUID::from_u128(0x00000003_0000_0010_8000_00aa00389b71);
        if sub == pcm {
            effective_tag = WAVE_FORMAT_PCM_LOCAL;
        } else if sub == float {
            effective_tag = WAVE_FORMAT_IEEE_FLOAT_LOCAL;
        }
    }

    let ffmpeg_format = match (effective_tag, bits) {
        (WAVE_FORMAT_IEEE_FLOAT_LOCAL, 32) => "f32le",
        (WAVE_FORMAT_PCM_LOCAL, 16) => "s16le",
        (WAVE_FORMAT_PCM_LOCAL, 24) => "s24le",
        (WAVE_FORMAT_PCM_LOCAL, 32) => "s32le",
        _ => {
            return Err(anyhow!(
                "Unsupported WASAPI mix format: tag=0x{tag:04x}, bits={bits}, channels={channels}, rate={sample_rate}."
            ))
        }
    };
    let bytes_per_frame = if block_align > 0 {
        block_align as usize
    } else {
        channels as usize * (bits as usize / 8)
    };
    Ok(RawAudioFormat {
        sample_rate,
        channels,
        ffmpeg_format,
        bytes_per_frame,
    })
}

fn list_audio_devices() -> Result<Vec<String>> {
    let mut devices = Vec::new();
    for dev in directshow_audio_devices() {
        push_device(&mut devices, &dev);
    }

    push_device(&mut devices, "WASAPI Loopback: Default Output");
    if ffmpeg_has_input_device("wasapi") {
        for endpoint in wasapi_loopback_devices() {
            push_device(&mut devices, &endpoint);
        }
        for endpoint in windows_audio_endpoint_names() {
            push_device(&mut devices, &format!("WASAPI Loopback: {endpoint}"));
        }
    }

    devices.sort();
    devices.dedup();
    Ok(devices)
}

fn emit_audio_diagnostics(top: &WebView, right: &WebView) {
    if !ffmpeg_has_input_device("wasapi") {
        emit_both(
            top,
            right,
            "log",
            format!(
                "{} does not expose FFmpeg WASAPI input. The app will use built-in Windows WASAPI loopback capture and pipe it into FFmpeg for encoding.",
                find_ffmpeg()
            ),
        );
    }
}


fn directshow_audio_devices() -> Vec<String> {
    if !ffmpeg_has_input_device("dshow") {
        return Vec::new();
    }

    let mut cmd = Command::new(find_ffmpeg());
    cmd.args([
        "-hide_banner",
        "-list_devices",
        "true",
        "-f",
        "dshow",
        "-i",
        "dummy",
    ])
    .stdout(Stdio::piped())
    .stderr(Stdio::piped());
    hide_console(&mut cmd);
    let Ok(output) = cmd.output() else {
        return Vec::new();
    };
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let Ok(re) = Regex::new(r#"\"([^\"]+)\"\s*\(audio\)"#) else {
        return Vec::new();
    };

    let mut devices = Vec::new();
    for cap in re.captures_iter(&text) {
        push_device(&mut devices, &format!("DirectShow: {}", cap[1].to_string()));
    }
    devices
}

fn wasapi_loopback_devices() -> Vec<String> {
    if !ffmpeg_has_input_device("wasapi") {
        return Vec::new();
    }

    let mut cmd = Command::new(find_ffmpeg());
    cmd.args([
        "-hide_banner",
        "-list_devices",
        "true",
        "-f",
        "wasapi",
        "-i",
        "dummy",
    ])
    .stdout(Stdio::piped())
    .stderr(Stdio::piped());
    hide_console(&mut cmd);
    let Ok(output) = cmd.output() else {
        return Vec::new();
    };
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let Ok(re) = Regex::new(r#""([^"]+)""#) else {
        return Vec::new();
    };

    let mut devices = Vec::new();
    for cap in re.captures_iter(&text) {
        let name = cap[1].trim();
        if !name.eq_ignore_ascii_case("dummy") && !name.is_empty() {
            push_device(&mut devices, &format!("WASAPI Loopback: {name}"));
        }
    }
    devices
}

fn first_directshow_recording_device() -> Option<String> {
    directshow_audio_devices().into_iter().next()
}

fn nonempty_default_recording_device() -> Option<String> {
    if let Some(device) = first_directshow_recording_device() {
        Some(device)
    } else {
        Some("WASAPI Loopback: Default Output".to_string())
    }
}

fn push_device(devices: &mut Vec<String>, device: &str) {
    let device = device.trim();
    if !device.is_empty() && !devices.iter().any(|existing| existing == device) {
        devices.push(device.to_string());
    }
}

fn windows_audio_endpoint_names() -> Vec<String> {
    let script = "Get-PnpDevice -Class AudioEndpoint -Status OK | Select-Object -ExpandProperty FriendlyName";
    let mut cmd = Command::new("powershell");
    cmd.args([
        "-NoProfile",
        "-ExecutionPolicy",
        "Bypass",
        "-Command",
        script,
    ]);
    hide_console(&mut cmd);
    let output = cmd.output();
    let Ok(output) = output else {
        return Vec::new();
    };
    let text = String::from_utf8_lossy(&output.stdout);
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(ToString::to_string)
        .collect()
}

fn ffmpeg_has_input_device(name: &str) -> bool {
    let Some(text) = ffmpeg_devices_text() else {
        return false;
    };
    text.lines().any(|line| {
        let trimmed = line.trim_start();
        trimmed.starts_with('D') && trimmed.split_whitespace().any(|part| part == name)
    })
}

fn ffmpeg_devices_text() -> Option<String> {
    let mut cmd = Command::new(find_ffmpeg());
    cmd.args(["-hide_banner", "-devices"]);
    hide_console(&mut cmd);
    let output = cmd.output().ok()?;
    Some(format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    ))
}

fn virtual_audio_driver_problem_message() -> Option<String> {
    let mut cmd = Command::new("pnputil");
    cmd.args([
        "/enum-devices",
        "/deviceid",
        "ROOT\\VirtualAudioDriver",
        "/drivers",
        "/format",
        "xml",
    ]);
    hide_console(&mut cmd);
    let output = cmd.output().ok()?;
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    if !text.contains("<Device ") {
        return None;
    }

    if text.contains("CM_PROB_UNSIGNED_DRIVER")
        || text.contains("<ProblemCode Problem=\"CM_PROB_UNSIGNED_DRIVER\">52</ProblemCode>")
        || text.contains("<ProblemStatus>0xC0000428</ProblemStatus>")
    {
        return Some("Virtual Audio Driver is installed, but Windows blocks it with Code 52 / 0xC0000428. Click Install automatically to enable Test Signing, restart Windows, then press Refresh Devices. If it still stays blocked, use the latest signed release package.".to_string());
    }

    if text.contains("<Status>Problem</Status>") {
        return Some("Virtual Audio Driver by MTT is installed, but Windows reports a device problem. It will not appear as an audio endpoint until Device Manager shows it as working.".to_string());
    }

    None
}

fn lookup_musicbrainz(artist: &str, title: &str) -> Result<TrackMeta> {
    if artist.trim().is_empty() && title.trim().is_empty() {
        return Err(anyhow!(
            "Artist or title is required for MusicBrainz lookup."
        ));
    }
    let query = if !artist.trim().is_empty() && !title.trim().is_empty() {
        format!(
            "artist:\"{}\" AND recording:\"{}\"",
            artist.trim(),
            title.trim()
        )
    } else if !title.trim().is_empty() {
        format!("recording:\"{}\"", title.trim())
    } else {
        format!("artist:\"{}\"", artist.trim())
    };
    let url = format!("https://musicbrainz.org/ws/2/recording/?query={}&fmt=json&limit=1&inc=artist-credits+releases", urlencoding::encode(&query));
    let client = Client::builder()
        .user_agent(USER_AGENT)
        .timeout(Duration::from_secs(12))
        .build()?;
    let value: Value = client.get(url).send()?.error_for_status()?.json()?;
    let rec = value["recordings"]
        .as_array()
        .and_then(|a| a.first())
        .ok_or_else(|| anyhow!("No MusicBrainz match found."))?;
    let title = rec["title"].as_str().unwrap_or(title).to_string();
    let artist = rec["artist-credit"]
        .as_array()
        .and_then(|a| a.first())
        .and_then(|v| v["artist"]["name"].as_str())
        .unwrap_or(artist)
        .to_string();
    let release = rec["releases"].as_array().and_then(|a| a.first());
    let album = release
        .and_then(|r| r["title"].as_str())
        .unwrap_or("")
        .to_string();
    let cover_url = release
        .and_then(|r| r["id"].as_str())
        .map(|id| format!("https://coverartarchive.org/release/{id}/front-500"))
        .unwrap_or_default();
    Ok(TrackMeta {
        artist,
        title,
        album,
        cover_url,
    })
}

fn fetch_now_playing(url: &str) -> Result<TrackMeta> {
    let client = Client::builder()
        .user_agent(USER_AGENT)
        .timeout(Duration::from_secs(10))
        .build()?;
    let text = client.get(url).send()?.error_for_status()?.text()?;
    if let Ok(value) = serde_json::from_str::<Value>(&text) {
        if let Some(meta) = parse_now_playing_json(&value) {
            return Ok(meta);
        }
    }
    parse_icy_text(&text)
        .ok_or_else(|| anyhow!("Could not parse now-playing metadata from the URL."))
}

fn parse_now_playing_json(v: &Value) -> Option<TrackMeta> {
    if let Some(text) = v.as_str() {
        return parse_artist_title_text(text);
    }

    let candidates = [
        ("artist", "title", "album", "cover_url"),
        ("artist", "song", "album", "art"),
        (
            "now_playing.song.artist",
            "now_playing.song.title",
            "now_playing.song.album",
            "now_playing.song.art",
        ),
        ("song.artist", "song.title", "song.album", "song.art"),
        (
            "track.artist",
            "track.title",
            "track.album",
            "track.artwork_url",
        ),
        (
            "current.artist",
            "current.title",
            "current.album",
            "current.cover",
        ),
        (
            "data.artist",
            "data.title",
            "data.album",
            "data.artwork_url",
        ),
        (
            "currenttrack_artist",
            "currenttrack_title",
            "currenttrack_album",
            "currenttrack_art",
        ),
    ];
    for (artist_path, title_path, album_path, cover_path) in candidates {
        let artist = json_text(v, artist_path).unwrap_or_default();
        let title = json_text(v, title_path).unwrap_or_default();
        if !artist.is_empty() || !title.is_empty() {
            return Some(TrackMeta {
                artist,
                title,
                album: json_text(v, album_path).unwrap_or_default(),
                cover_url: json_text(v, cover_path)
                    .or_else(|| json_text(v, "art"))
                    .or_else(|| json_text(v, "artwork"))
                    .unwrap_or_default(),
            });
        }
    }

    for path in [
        "songtitle",
        "nowplaying",
        "now_playing",
        "current_song",
        "title",
    ] {
        if let Some(text) = json_text(v, path) {
            if let Some(meta) = parse_artist_title_text(&text) {
                return Some(meta);
            }
        }
    }
    None
}

fn parse_icy_text(text: &str) -> Option<TrackMeta> {
    let re = Regex::new(r#"StreamTitle='([^']*)'"#).ok()?;
    let cap = re.captures(text)?;
    let raw = cap.get(1)?.as_str();
    parse_artist_title_text(raw)
}

fn json_text(v: &Value, path: &str) -> Option<String> {
    let mut current = v;
    for part in path.split('.') {
        current = current.get(part)?;
    }
    current
        .as_str()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
}

fn parse_artist_title_text(text: &str) -> Option<TrackMeta> {
    let raw = text.trim().trim_matches('\0').trim();
    if raw.is_empty() {
        return None;
    }
    if let Some((artist, title)) = raw.split_once(" - ") {
        return Some(TrackMeta {
            artist: artist.trim().to_string(),
            title: title.trim().to_string(),
            album: String::new(),
            cover_url: String::new(),
        });
    }
    Some(TrackMeta {
        artist: String::new(),
        title: raw.to_string(),
        album: String::new(),
        cover_url: String::new(),
    })
}

fn find_ffmpeg() -> String {
    let local = std::env::current_exe()
        .ok()
        .and_then(|p| p.parent().map(|d| d.join("ffmpeg.exe")));
    if let Some(path) = local {
        if path.exists() {
            return path.display().to_string();
        }
    }
    "ffmpeg".to_string()
}

fn normalize_custom_url(url: &str) -> String {
    let trimmed = url.trim();
    if trimmed.is_empty() {
        return "about:blank".to_string();
    }
    if trimmed.starts_with("http://")
        || trimmed.starts_with("https://")
        || trimmed.starts_with("about:")
    {
        trimmed.to_string()
    } else {
        format!("https://{}", trimmed)
    }
}

fn provider_url(provider_name: &str, custom: Option<&str>) -> String {
    match provider_name {
        "deezer" => "https://www.deezer.com/".to_string(),
        "qobuz" => "https://www.qobuz.com/".to_string(),
        "tidal" => "https://listen.tidal.com/".to_string(),
        "own" => own_radio_page(),
        "custom" => normalize_custom_url(custom.unwrap_or("about:blank")),
        _ => "about:blank".to_string(),
    }
}

fn open_url_external(url: &str) -> Result<()> {
    #[cfg(windows)]
    {
        Command::new("explorer")
            .arg(url)
            .spawn()
            .context("Failed to open external URL")?;
        return Ok(());
    }
    #[cfg(not(windows))]
    {
        Command::new("xdg-open")
            .arg(url)
            .spawn()
            .context("Failed to open external URL")?;
        Ok(())
    }
}


fn playback_output_device_hint(recording_device: &str) -> Option<String> {
    let mut name = recording_device.trim().to_string();
    if name.eq_ignore_ascii_case("WASAPI Loopback: Default Output") || name.is_empty() {
        return None;
    }
    if let Some(stripped) = name.strip_prefix("DirectShow: ") {
        name = stripped.trim().to_string();
    } else if let Some(stripped) = name.strip_prefix("WASAPI Loopback: ") {
        name = stripped.trim().to_string();
    }

    // Common virtual cable convention: playback goes to "Input", recording reads from "Output".
    // If the endpoint already names an input/output pair, prefer the playback side.
    let lower = name.to_ascii_lowercase();
    if lower.contains("output") {
        name = name.replace("Output", "Input").replace("output", "input");
    } else if lower.contains("record") {
        name = name.replace("Record", "Playback").replace("record", "playback");
    }

    if name.trim().is_empty() {
        None
    } else {
        Some(name)
    }
}

fn open_room_player(channel: &Channel) -> Result<()> {
    let url = provider_url(&channel.playback_provider, Some(&channel.playback_url));
    #[cfg(windows)]
    {
        let profile_root = std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join("room_player_profiles");
        let profile_dir = profile_root.join(sanitize_filename(&format!(
            "{}_{}",
            channel.id, channel.label
        )));
        fs::create_dir_all(&profile_dir)?;
        let edge_paths = [
            PathBuf::from(r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe"),
            PathBuf::from(r"C:\Program Files\Microsoft\Edge\Application\msedge.exe"),
        ];
        let mut cmd = if let Some(edge) = edge_paths.into_iter().find(|p| p.exists()) {
            Command::new(edge)
        } else {
            Command::new("msedge")
        };
        cmd.arg("--new-window")
            .arg(format!("--user-data-dir={}", profile_dir.display()));
        if let Some(output_hint) = playback_output_device_hint(&channel.device) {
            // Chromium/Edge accepts an audio output device hint. On some Windows builds/providers
            // this may still be ignored, but it is the safest automatic routing attempt without
            // globally changing the user's default output device.
            cmd.arg(format!("--audio-output-device={}", output_hint));
        }
        cmd.arg(url);
        spawn_no_console(cmd).context("Failed to open a separate room playback window")?;
        return Ok(());
    }
    #[cfg(not(windows))]
    {
        open_url_external(&url)
    }
}

fn launch_aural(aural_dir: Option<&str>, python_exe: Option<&str>, ui: &str) -> Result<()> {
    let root = aural_dir
        .filter(|s| !s.trim().is_empty())
        .map(PathBuf::from)
        .or_else(|| {
            let cwd = std::env::current_dir().ok()?;
            let candidates = [cwd.join("aural"), cwd.join("Aural"), cwd.join("drivers").join("Aural"), cwd.join("drivers").join("aural")];
            candidates.into_iter().find(|p| p.exists())
        })
        .ok_or_else(|| anyhow!("Aural folder not set. Select the folder that contains Aural main.py, or place it in ./aural or ./drivers/Aural."))?;
    let main_py = [
        root.join("main.py"),
        root.join("Aural").join("main.py"),
        root.join("src").join("main.py"),
    ]
    .into_iter()
    .find(|p| p.exists())
    .ok_or_else(|| {
        anyhow!(
            "Could not find main.py in {}. Select the folder that contains the Aural project.",
            root.display()
        )
    })?;
    let py = python_exe
        .filter(|s| !s.trim().is_empty())
        .unwrap_or("python");
    let mut cmd = Command::new(py);
    cmd.arg(&main_py)
        .args(["-UI", ui])
        .current_dir(main_py.parent().unwrap_or(&root));
    spawn_no_console(cmd)
        .with_context(|| format!("Failed to launch Aural via {}", main_py.display()))
}

fn spawn_no_console(mut cmd: Command) -> Result<()> {
    hide_console(&mut cmd);
    cmd.spawn()?;
    Ok(())
}

fn hide_console(cmd: &mut Command) {
    #[cfg(windows)]
    {
        cmd.creation_flags(0x08000000);
    }
}

fn own_radio_page() -> String {
    "data:text/html;charset=utf-8,%3Chtml%3E%3Cbody%20style%3D%27background%3A%23101114%3Bcolor%3Awhite%3Bfont-family%3ASegoe%20UI%2CArial%3Bpadding%3A24px%27%3E%3Ch1%3EOwn%20Web%20Radio%3C%2Fh1%3E%3Cp%3EUse%20your%20station%20website%20or%20a%20custom%20URL.%20For%20automatic%20track%20splitting%2C%20enter%20your%20Now%20Playing%20metadata%20API%20URL%20in%20the%20top%20bar.%3C%2Fp%3E%3Cp%3EThis%20app%20is%20for%20legal%20audio%20consumption%2C%20room%20routing%2C%20and%20permitted%20recording%20workflows.%3C%2Fp%3E%3C%2Fbody%3E%3C%2Fhtml%3E".to_string()
}

fn sanitize_filename(name: &str) -> String {
    let bad = ['<', '>', ':', '"', '/', '\\', '|', '?', '*'];
    let mut out = String::new();
    for ch in name.chars() {
        if bad.contains(&ch) || ch.is_control() {
            out.push('_');
        } else {
            out.push(ch);
        }
    }
    out.split_whitespace()
        .collect::<Vec<_>>()
        .join("_")
        .chars()
        .take(180)
        .collect()
}

fn read_text_tail(path: &Path, max_chars: usize) -> String {
    match fs::read_to_string(path) {
        Ok(text) => {
            let tail: String = text
                .chars()
                .rev()
                .take(max_chars)
                .collect::<String>()
                .chars()
                .rev()
                .collect();
            let trimmed = tail.trim();
            if trimmed.is_empty() {
                "FFmpeg wrote no diagnostic output.".to_string()
            } else {
                trimmed.to_string()
            }
        }
        Err(_) => format!("Could not read FFmpeg log at {}", path.display()),
    }
}

fn app_icon_path() -> Option<PathBuf> {
    let mut candidates = Vec::new();

    if let Ok(cwd) = std::env::current_dir() {
        candidates.push(cwd.join("app_assets").join("app_icon.png"));
    }
    if let Ok(exe) = std::env::current_exe() {
        if let Some(exe_dir) = exe.parent() {
            candidates.push(exe_dir.join("app_assets").join("app_icon.png"));
            candidates.push(
                exe_dir
                    .join("..")
                    .join("..")
                    .join("app_assets")
                    .join("app_icon.png"),
            );
        }
    }
    candidates.push(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("app_assets")
            .join("app_icon.png"),
    );

    candidates.into_iter().find(|path| path.exists())
}

fn load_app_icon() -> Option<Icon> {
    let path = app_icon_path()?;
    let bytes = fs::read(path).ok()?;
    let image = image::load_from_memory(&bytes).ok()?.into_rgba8();
    let width = image.width();
    let height = image.height();
    Icon::from_rgba(image.into_raw(), width, height).ok()
}

fn app_icon_data_uri() -> String {
    let Some(path) = app_icon_path() else {
        return String::new();
    };
    let Ok(bytes) = fs::read(path) else {
        return String::new();
    };
    format!(
        "data:image/png;base64,{}",
        general_purpose::STANDARD.encode(bytes)
    )
}

fn emit<T: Serialize>(webview: &WebView, event: &str, payload: T) {
    let event_json = serde_json::to_string(event).unwrap_or_else(|_| "\"event\"".to_string());
    let payload_json = serde_json::to_string(&payload).unwrap_or_else(|_| "null".to_string());
    let js = format!("window.__rustEvent && window.__rustEvent({event_json}, {payload_json});");
    let _ = webview.evaluate_script(&js);
}

fn emit_both<T: Serialize>(top: &WebView, _right: &WebView, event: &str, payload: T) {
    emit(top, event, payload);
}

fn provider_metadata_script() -> &'static str {
    r#"
(() => {
  if (window.__losslessRecorderBridge) return;
  window.__losslessRecorderBridge = true;
  const clean = value => value == null ? '' : String(value).trim();
  let lastPayload = '';
  function readMeta() {
    try {
      const payload = {
        cmd: 'webview_metadata',
        url: clean(location.href),
        page_title: clean(document.title)
      };
      const ms = navigator.mediaSession && navigator.mediaSession.metadata;
      if (ms) {
        payload.artist = clean(ms.artist);
        payload.title = clean(ms.title);
        payload.album = clean(ms.album);
        if (ms.artwork && ms.artwork.length) payload.cover_url = clean(ms.artwork[0].src);
      }
      const ogTitle = document.querySelector('meta[property="og:title"],meta[name="twitter:title"]');
      if (!payload.title && ogTitle) payload.title = clean(ogTitle.content);
      const ogImage = document.querySelector('meta[property="og:image"],meta[name="twitter:image"]');
      if (!payload.cover_url && ogImage) payload.cover_url = clean(ogImage.content);
      const serialized = JSON.stringify(payload);
      if (serialized !== lastPayload && window.ipc && window.ipc.postMessage) {
        lastPayload = serialized;
        window.ipc.postMessage(serialized);
      }
    } catch (_) {}
  }
  const hookHistory = name => {
    const original = history[name];
    history[name] = function() {
      const result = original.apply(this, arguments);
      setTimeout(readMeta, 300);
      return result;
    };
  };
  hookHistory('pushState');
  hookHistory('replaceState');
  window.addEventListener('popstate', () => setTimeout(readMeta, 300));
  window.addEventListener('load', () => setTimeout(readMeta, 800));
  setInterval(readMeta, 2500);
  setTimeout(readMeta, 500);
})();
"#
}

fn top_html() -> String {
    let icon_src = app_icon_data_uri();
    let icon_style = if icon_src.is_empty() {
        "display:none"
    } else {
        ""
    };
    r##"<!doctype html>
<html lang="en"><head><meta charset="utf-8" />
<title>Lossless Music Recorder Controls</title>
<style>
:root{color-scheme:dark;font-family:Segoe UI,Arial,sans-serif}*{box-sizing:border-box}body{margin:0;background:#101218;color:#f1f3f7;overflow:hidden}button,input,select{font:inherit}button{background:#242a35;color:white;border:1px solid #3c4657;border-radius:6px;padding:6px 10px;min-height:31px;font-size:12px;white-space:nowrap;cursor:pointer}button:hover{background:#303848}.primary{background:#23603a;border-color:#2d8a51;font-weight:700}.danger{background:#6a2630;border-color:#9a3b47;font-weight:700}.provider{padding:5px 8px}input,select{background:#191d25;color:white;border:1px solid #3c4657;border-radius:6px;padding:6px 8px;min-width:0;height:31px;width:100%}input[type=checkbox]{width:auto;height:auto;min-width:0;padding:0;margin:0;accent-color:#58b36f}select{text-align:center;text-align-last:center}option{text-align:center}label{font-size:11px;color:#c8d1e1;display:block;margin-bottom:4px}.panel{height:100vh;display:flex;flex-direction:column;background:#101218;border-left:1px solid #2b3341}.head{display:flex;align-items:center;gap:8px;padding:10px;border-bottom:1px solid #2b3341;background:#151922}.appIcon{width:30px;height:30px;object-fit:contain;border-radius:6px;flex:0 0 30px}.title{font-size:18px;font-weight:800;line-height:1.05}.sub{font-size:11px;color:#9eabc1;margin-top:2px}.content{flex:1;overflow:auto;padding:10px 10px 44px}.section{border:1px solid #2d3544;background:#151a23;border-radius:8px;padding:10px;margin-bottom:10px;min-width:0}.section h3{font-size:13px;margin:0 0 8px;color:#eef3ff}.busSection{border-color:#3a4f68;background:#161d29}.row{display:flex;align-items:center;gap:6px;margin-top:7px;min-width:0;flex-wrap:wrap}.row>*{min-width:0}.grow{flex:1}.two{display:grid;grid-template-columns:1fr 1fr;gap:7px}.switch{font-size:12px;color:#cbd3e4;display:flex;align-items:center;gap:5px;white-space:normal;line-height:1.25}.notice{font-size:11px;color:#aeb8ca;line-height:1.32;word-break:break-word}.statusLine{position:fixed;left:0;right:0;bottom:0;height:34px;border-top:1px solid #2b3341;background:#0d1016;color:#b8c6dd;font-size:11px;line-height:34px;padding:0 10px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.statusLine.error{color:#ffb7bf}.track{font-size:12px;color:#dfe8fa;background:#10141c;border:1px solid #2b3341;border-radius:6px;padding:7px;min-height:32px;overflow:hidden;white-space:nowrap;text-overflow:ellipsis}.badge{display:inline-block;padding:3px 8px;border-radius:999px;background:#293241;color:#cdd6e8;font-size:12px;margin-left:7px}.running{background:#21442e;color:#d8ffe2}.providerBadge{font-size:11px;color:#b7c5df;background:#1e2633;border:1px solid #344052;border-radius:999px;padding:4px 9px;white-space:nowrap}.modalBackdrop{position:fixed;inset:0;background:rgba(0,0,0,.62);display:none;align-items:center;justify-content:center;z-index:9999}.modal{width:min(380px,calc(100vw - 28px));background:#171d28;border:1px solid #3a4658;border-radius:10px;box-shadow:0 18px 70px rgba(0,0,0,.55);padding:18px}.modal h2{font-size:20px;margin:0 0 8px;color:#fff}.modal p{font-size:13px;color:#cdd6e8;line-height:1.42;margin:0 0 14px}.modalActions{display:flex;justify-content:flex-end;gap:8px}.modalActions button{min-width:92px}.restartBtn{background:#23603a;border-color:#2d8a51;font-weight:700}
</style></head><body>
<div class="panel">
  <div class="head"><img class="appIcon" style="__APP_ICON_STYLE__" src="__APP_ICON_SRC__"/><div><div class="title">Lossless Music Recorder</div><div class="sub">Single WASAPI bus</div></div></div>
  <div id="restartModal" class="modalBackdrop"><div class="modal"><h2>You need to restart</h2><p>Windows must restart once before audio-device changes can appear.</p><div class="modalActions"><button onclick="hideRestartPrompt()">Later</button><button class="restartBtn" onclick="restartNow()">Restart</button></div></div></div>
  <div class="content">
    <div class="section"><h3>Player</h3><div class="row"><button class="provider" onclick="openProvider('own')">Own Radio</button><button class="provider" onclick="openProvider('deezer')">Deezer</button><button class="provider" onclick="openProvider('qobuz')">Qobuz</button><button class="provider" onclick="openProvider('tidal')">TIDAL</button></div><div class="row"><span id="selectedProvider" class="providerBadge">Own Radio</span></div><label style="margin-top:8px">Custom URL or radio page</label><input id="customUrl" placeholder="https://..."/><div class="row"><button onclick="openProvider('custom')">Open in WebView</button><button onclick="openExternal()">External</button></div></div>
    <div class="section busSection"><h3>Recording Bus <span id="busBadge" class="badge">Idle</span></h3><label>Audio device</label><select id="busDevice" onchange="updateMainBus()"><option>WASAPI Loopback: Default Output</option></select><div class="row"><button onclick="openPlayer()">Player</button><button onclick="routeChannel()">Route</button><button onclick="pollBus()">Read</button><button onclick="useCurrentMeta()">Use current</button></div><div class="row"><button class="primary" onclick="startBus()">Rec</button><button class="danger" onclick="stopBus()">Stop</button><button onclick="refreshDevices()">Refresh</button><button onclick="openLoopbackSetup()">Sound</button></div><div class="notice" id="busPath">WASAPI Loopback is selected automatically. You can still choose another available capture device.</div></div>
    <div class="section"><h3>Output</h3><label>Output folder</label><div class="row"><input id="outputDir" class="grow"/><button onclick="pickOutputFolder()">Select</button></div></div>
    <div class="section"><h3>Quality</h3><label>Format</label><input id="format" value="FLAC" readonly/><div class="row"><div class="grow"><label>Bit depth</label><select id="bitDepth"><option value="16">16-bit</option><option value="24" selected>24-bit</option><option value="32">32-bit</option></select></div><div class="grow"><label>Rate</label><select id="sampleRate"><option value="auto">Auto</option><option value="44100">44.1</option><option value="48000">48</option><option value="88200">88.2</option><option value="96000">96</option><option value="176400">176.4</option><option value="192000">192</option></select></div></div><div class="row"><label class="switch"><input type="checkbox" id="autoSplit" checked/> auto split on metadata change</label></div></div>
    <div class="section"><h3>Metadata</h3><label>Now Playing / API URL</label><input id="npUrl" placeholder="Optional JSON / ICY metadata URL"/><div class="row"><label class="switch"><input type="checkbox" id="autoTitle" checked/> auto read title</label><button onclick="pollNowPlaying()">Read now</button><button onclick="lookupMb()">MusicBrainz</button></div><div class="track" id="currentTrack">No title loaded</div><div class="two" style="margin-top:7px"><label>Artist<input id="artist" onchange="updateMainBus()"/></label><label>Title<input id="trackTitle" onchange="updateMainBus()"/></label><label>Album<input id="album" onchange="updateMainBus()"/></label><label>Cover URL<input id="coverUrl" onchange="updateMainBus()"/></label></div><div class="notice" style="margin-top:7px">Title format: %artist% - %title%</div></div>
  </div>
  <div id="topStatus" class="statusLine">Ready.</div>
</div>
<script>
const $=id=>document.getElementById(id);let currentProvider='own';let poller=null;let npDebounce=null;let lastMeta={artist:'',title:'',album:'',cover_url:''};let devices=[];let mainBus=null;
function send(obj){window.ipc.postMessage(JSON.stringify(obj));}
function setStatus(msg,err=false){topStatus.textContent=msg;topStatus.className='statusLine'+(err?' error':'');}
function esc(s){return String(s||'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#039;'}[c]));}
function common(){return{provider:currentProvider,url:customUrl.value,output_dir:outputDir.value,format:'flac',bit_depth:bitDepth.value,sample_rate:sampleRate.value,speed4x:false,auto_split:autoSplit.checked,now_playing_url:npUrl.value,artist:artist.value,title:trackTitle.value,album:album.value,cover_url:coverUrl.value};}
function busPayload(){const id=mainBus?mainBus.id:1;return{...common(),cmd:'update_channel_meta',channel_id:id,device:busDevice.value};}
function updateMainBus(){if(mainBus)send(busPayload());}
function openProvider(p){currentProvider=p;selectedProvider.textContent=p==='custom'?'Custom':p.toUpperCase();send({...common(),cmd:'open_provider'});}function openExternal(){send({...common(),cmd:'open_provider_external'});}function pickOutputFolder(){send({...common(),cmd:'pick_output_dir'});}function refreshDevices(){setStatus('Refreshing devices...');send({cmd:'list_devices'});}function openLoopbackSetup(){send({cmd:'open_loopback_setup'});}function routeChannel(){if(mainBus)send({cmd:'route_channel',channel_id:mainBus.id});}
function openPlayer(){if(mainBus)send({cmd:'open_channel_player',channel_id:mainBus.id});}
function startBus(){if(!mainBus){setStatus('Recorder is not ready yet.',true);return;}send({...busPayload(),cmd:'start_channel'});}function stopBus(){if(mainBus)send({...busPayload(),cmd:'stop_channel'});}function pollBus(){pollNowPlaying();}
function lookupMb(){send({...common(),cmd:'musicbrainz'});}function useCurrentMeta(){artist.value=lastMeta.artist||'';trackTitle.value=lastMeta.title||'';album.value=lastMeta.album||'';coverUrl.value=lastMeta.cover_url||'';updateMainBus();}
function pollNowPlaying(){if(!npUrl.value.trim()){setStatus('Enter a Now Playing API URL first.',true);return;}send({...common(),cmd:'poll_channel_now_playing',channel_id:mainBus?mainBus.id:1,device:busDevice.value});}
function pushOptions(){send({...common(),cmd:'set_options'});updateMainBus();}
function syncMetadataPoll(){clearInterval(poller);poller=null;pushOptions();if((autoTitle.checked||autoSplit.checked)&&npUrl.value.trim()){pollNowPlaying();poller=setInterval(pollNowPlaying,5000);setStatus('Metadata polling is on.');}else if(autoSplit.checked){setStatus('Auto split is on. WebView metadata changes will split the single bus.');}}
function renderDevices(){const selected=mainBus&&mainBus.device?mainBus.device:'WASAPI Loopback: Default Output';let list=devices&&devices.length?devices.slice():['WASAPI Loopback: Default Output'];if(!list.includes('WASAPI Loopback: Default Output'))list.unshift('WASAPI Loopback: Default Output');if(selected&&!list.includes(selected))list.unshift(selected);busDevice.innerHTML=list.map(d=>`<option value="${esc(d)}" ${d===selected?'selected':''}>${esc(d)}</option>`).join('');}
function renderBus(){if(!mainBus)return;renderDevices();busBadge.textContent=mainBus.running?'Recording':'Idle';busBadge.className='badge'+(mainBus.running?' running':'');busPath.textContent=mainBus.path||'WASAPI Loopback is selected automatically. You can still choose another available capture device.';const meta=mainBus.meta||{};artist.value=meta.artist||artist.value||'';trackTitle.value=meta.title||trackTitle.value||'';album.value=meta.album||album.value||'';coverUrl.value=meta.cover_url||coverUrl.value||'';if(mainBus.now_playing_url&&!npUrl.value)npUrl.value=mainBus.now_playing_url;}
function setMetadata(m){lastMeta=m||lastMeta;artist.value=lastMeta.artist||'';trackTitle.value=lastMeta.title||'';album.value=lastMeta.album||'';coverUrl.value=lastMeta.cover_url||'';const a=lastMeta.artist||'Unknown artist';const t=lastMeta.title||'Untitled track';currentTrack.textContent=a+' - '+t;updateMainBus();}
function showRestartPrompt(message){const modal=$('restartModal');if(modal)modal.style.display='flex';if(message)setStatus(message);}
function hideRestartPrompt(){const modal=$('restartModal');if(modal)modal.style.display='none';}
function restartNow(){hideRestartPrompt();setStatus('Restart requested...');send({cmd:'restart_windows'});}
autoTitle.addEventListener('change',syncMetadataPoll);autoSplit.addEventListener('change',syncMetadataPoll);npUrl.addEventListener('input',()=>{clearTimeout(npDebounce);npDebounce=setTimeout(syncMetadataPoll,700);});bitDepth.addEventListener('change',pushOptions);sampleRate.addEventListener('change',pushOptions);
window.__rustEvent=function(event,payload){if(event==='outputDir')outputDir.value=payload;else if(event==='devices'){devices=payload||[];renderBus();}else if(event==='channels'){mainBus=(payload&&payload.length)?payload[0]:mainBus;renderBus();}else if(event==='metadataUrl'){/* WebView URL is not copied into API URL in single WebView mode. */}else if(event==='metadata'||event==='nowPlaying')setMetadata(payload);else if(event==='restartRequired')showRestartPrompt(payload);else if(event==='log')setStatus(payload,false);else if(event==='error')setStatus(payload,true);};
send({cmd:'ui_ready'});refreshDevices();syncMetadataPoll();
</script></body></html>"##
        .replace("__APP_ICON_SRC__", &icon_src)
        .replace("__APP_ICON_STYLE__", icon_style)
}

fn right_html() -> String {
    r##"<!doctype html>
<html lang="en"><head><meta charset="utf-8" />
<title>Lossless Music Recorder Log</title>
<style>
:root{color-scheme:dark;font-family:Segoe UI,Arial,sans-serif}*{box-sizing:border-box}body{margin:0;background:#101218;color:#f1f3f7;overflow:hidden}.wrap{height:100vh;display:grid;grid-template-rows:auto 1fr 110px}.panel{padding:10px;border-bottom:1px solid #2b3341;background:#151922;min-width:0}h3{font-size:16px;margin:0 0 8px}.notice,.small{font-size:12px;color:#aeb8ca;line-height:1.35;word-break:break-word}.takes{overflow:auto;padding:10px;background:#101218}.take{border:1px solid #303948;background:#171b24;border-radius:8px;padding:10px;margin-bottom:8px}.takeTitle{font-size:13px;font-weight:800;color:#eef3ff}.path{font-size:11px;color:#aeb8ca;word-break:break-all;margin-top:4px}#log{overflow:auto;font-size:11px;color:#b8c2d7;padding:8px;white-space:pre-wrap;background:#0d1016;border-top:1px solid #2b3341}
</style></head><body><div class="wrap">
<div class="panel"><h3>Status</h3><div class="notice">Single-bus mode: WASAPI is selected automatically, but another capture device can be chosen in the top Recording Bus box.</div></div>
<div id="takes" class="takes"><div class="notice">No saved takes yet.</div></div>
<div id="log">[ready] Log loaded.</div>
</div><script>
function send(obj){window.ipc.postMessage(JSON.stringify(obj));}
function esc(s){return String(s||'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#039;'}[c]));}
function addLog(x){log.textContent+='['+new Date().toLocaleTimeString()+'] '+x+'\n';log.scrollTop=log.scrollHeight;}
function renderTakes(takes){takes=takes||[];if(!takes.length){document.getElementById('takes').innerHTML='<div class="notice">No saved takes yet.</div>';return;}document.getElementById('takes').innerHTML=takes.slice().reverse().map(t=>`<div class="take"><div class="takeTitle">${esc((t.artist||'')+(t.artist&&t.title?' - ':'')+(t.title||'Untitled'))}</div><div class="small">${esc(t.channel||'Main Recording')}</div><div class="path">${esc(t.path||'')}</div></div>`).join('');}
window.__rustEvent=function(event,payload){if(event==='takes')renderTakes(payload);else if(event==='log')addLog(payload);else if(event==='error')addLog('ERROR: '+payload);};
send({cmd:'ui_ready'});
</script></body></html>"##.to_string()
}

