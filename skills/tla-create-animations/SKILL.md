---
name: tla-create-animations
description: Use when creating TLA+ animations to visualize state transitions. Provides step-by-step guide for animation file structure and SVG elements.
---

# Creating TLA+ Animations

Use this skill to create animations that visualize TLA+ specifications during model checking or trace exploration.

## When to Use

- Visualizing state transitions in a TLA+ spec
- Creating interactive animations for presentations
- Debugging complex state machines visually
- Understanding trace counterexamples

## Quick Start

### 1. Animation File Structure

Create a `.tla` file (e.g., `MySpecAnim.tla`) that EXTENDS your spec:

```tla
---- MODULE MySpecAnim ----
EXTENDS TLC, SVG, IOUtils, MySpec

\* Visual logic - what to show
AnimView == [
    frame |-> "MyAnimation",
    title |-> "My Spec Animation",
    width |-> 800,
    height |-> 600,
    elements |-> AnimElements
]

\* SVG elements
AnimElements == <<
    [shape |-> "rect", x |-> 100, y |-> 100, width |-> 50, height |-> 50, fill |-> "blue"],
    [shape |-> "text", x |-> 125, y |-> 125, text |-> ToString(myVariable)]
>>

\* TLC generation
AnimAlias == [
    view |-> AnimView
]

\* Debugger watch
AnimWatch == AnimView
====
```

### 2. Run with TLC

Use MCP tools to generate animation:

```bash
# Parse the animation spec
tlaplus_mcp_sany_parse --file MySpecAnim.tla

# Explore with animation
tlaplus_mcp_tlc_explore --spec MySpecAnim --config MySpec.cfg
```

## SVG Element Reference

### Rectangle
```tla
[shape |-> "rect", x |-> 100, y |-> 100, width |-> 50, height |-> 50, 
 fill |-> "blue", stroke |-> "black", strokeWidth |-> 2]
```

### Circle
```tla
[shape |-> "circle", cx |-> 200, cy |-> 200, r |-> 30, 
 fill |-> "red", opacity |-> 0.8]
```

### Text
```tla
[shape |-> "text", x |-> 150, y |-> 150, text |-> "Hello", 
 fontSize |-> 16, fill |-> "black", fontFamily |-> "Arial"]
```

### Line
```tla
[shape |-> "line", x1 |-> 0, y1 |-> 0, x2 |-> 100, y2 |-> 100,
 stroke |-> "black", strokeWidth |-> 2]
```

### Path
```tla
[shape |-> "path", d |-> "M 10 10 L 90 90 L 10 90 Z",
 fill |-> "yellow", stroke |-> "black"]
```

### Group
```tla
[shape |-> "g", elements |-> <<
    [shape |-> "rect", ...],
    [shape |-> "circle", ...]
>>]
```

## Animation Patterns

### Conditional Visibility
```tla
IF condition THEN
    [shape |-> "circle", cx |-> 100, cy |-> 100, r |-> 20, fill |-> "green"]
ELSE
    [shape |-> "circle", cx |-> 100, cy |-> 100, r |-> 20, fill |-> "red"]
```

### Dynamic Positioning
```tla
[shape |-> "rect", 
 x |-> position * 50,  \* Position based on variable
 y |-> 100, 
 width |-> 40, 
 height |-> 40]
```

### Sequence Visualization
```tla
LET Elements == {
    [shape |-> "circle", cx |-> i * 60, cy |-> 200, r |-> 20, fill |-> "blue"]
    : i \\in 1..Len(mySequence)
}
IN [shape |-> "g", elements |-> SetToSeq(Elements)]
```

## Best Practices

1. **Start simple**: Begin with basic shapes, add complexity gradually
2. **Use meaningful colors**: Consistent color scheme for states
3. **Add labels**: Text elements help explain what's shown
4. **Test incrementally**: Check animation after each addition
5. **Use groups**: Organize related elements with `g` shape
6. **Dynamic values**: Use `ToString()` to show variable values

## Common Issues

### Animation not showing
- Check that AnimAlias is defined correctly
- Verify EXTENDS includes TLC, SVG, IOUtils
- Ensure AnimView has required fields (frame, elements)

### Elements not visible
- Check x, y coordinates are within width/height bounds
- Verify fill/stroke colors are valid
- Check opacity is not 0

### Performance issues
- Limit number of elements (< 100 for smooth animation)
- Use simpler shapes when possible
- Avoid complex path calculations in hot loops

## MCP Tools for Animations

- `tlaplus_mcp_sany_parse`: Validate animation spec syntax
- `tlaplus_mcp_tlc_explore`: Generate and view animation
- `tlaplus_mcp_tlc_check`: Run model checker with animation output

## Complete Example

See the knowledge base article `tla-animations.md` for complete examples including:
- BatteryRelay: Simple state machine
- BlockingQueue: Producer-consumer pattern
- DiningPhilosophers: Concurrency visualization
- TwoPhase: Distributed protocol animation

---

## Terminal Rendering Workflow

In addition to the SVG-based workflow above, animations can be rendered directly in the terminal using built-in graphics protocols. This eliminates the need to open a browser and allows you to view animation frames inline while working.

### Supported Rendering Paths

There are four rendering paths, selected based on your terminal capabilities:

1. **Kitty Graphics Protocol** -- For terminals that support the Kitty graphics protocol (Kitty terminal, and others implementing the protocol). Frames are displayed as inline PNG images using Kitty escape sequences.

2. **iTerm2 Inline Images** -- For iTerm2 on macOS (and compatible terminals such as WezTerm). Frames are displayed as inline PNG images using the iTerm2 proprietary escape sequence.

3. **ASCII Fallback** -- For terminals without graphics protocol support. Shapes are rendered using Unicode box-drawing characters and ANSI color codes. Suitable for any terminal, including remote SSH sessions.

4. **Browser Fallback** -- When neither graphics nor ASCII is preferred, the frame is saved as an HTML/SVG file and you open it in an external browser. This is the same as the traditional SVG workflow but triggered through the rendering tool.

### How It Works

The terminal rendering workflow follows a detect-then-render pattern:

1. **Detect**: Call `tlaplus_mcp_animation_detect` to query the terminal environment. This inspects environment variables (`TERM`, `TERM_PROGRAM`, `KITTY_WINDOW_ID`, `TMUX`, etc.) and returns a structured result describing your terminal capabilities.

2. **Choose protocol**: Based on the detection result, select the appropriate protocol. If `protocol` is `"kitty"` or `"iterm2"` and passthrough is enabled (or no multiplexer is in use), use that protocol. If `protocol` is `"none"`, fall back to `"ascii"` or `"browser"`.

3. **Render**: Call `tlaplus_mcp_animation_render` with the chosen protocol and your animation data (AnimView record, SVG string, or SVG file path). The tool returns the rendered frame for display.

4. **Navigate**: For trace visualizations with multiple frames, call `tlaplus_mcp_animation_frameCount` first to discover available frames, then render each frame individually by its file path.

---

## Detection Result Interpretation

When you call `tlaplus_mcp_animation_detect`, it returns a JSON object with the following fields:

### Field Reference

| Field | Type | Meaning |
|-------|------|---------|
| `protocol` | `"kitty"` or `"iterm2"` or `"none"` | The graphics protocol your terminal supports. `"none"` means no graphics protocol was detected. |
| `multiplexer` | `"tmux"` or `"screen"` or `"none"` | Whether a terminal multiplexer is in use. Multiplexers can block graphics protocols unless passthrough is enabled. |
| `passthroughEnabled` | `boolean` | Whether graphics passthrough is enabled in the detected multiplexer. When `multiplexer` is `"none"`, this is `true` (no multiplexer means no passthrough needed). When `multiplexer` is `"tmux"`, this reflects the `allow-passthrough` setting. |
| `passthroughVerified` | `boolean` | Whether passthrough was verified via active probe. Always `false` in v1 (reserved for future use). |
| `fallbackAvailable` | `["ascii", "browser"]` | The fallback options that are always available regardless of terminal. |
| `detectionMethod` | `"env"` or `"query"` or `"probe"` | How detection was performed. `"env"` means environment variables were checked. `"query"` means terminal was queried. `"probe"` means an active probe was sent. |
| `confidence` | `"high"` or `"medium"` or `"low"` | Confidence in the detection result. `"high"` means a definitive indicator was found (e.g., `KITTY_WINDOW_ID` is set). `"low"` means no positive identification was made. |
| `environment` | object | Raw environment variables captured during detection, for diagnostics. Contains `TERM`, `TERM_PROGRAM`, `KITTY_WINDOW_ID`, `TMUX`, `STY`, and `LC_TERMINAL` if they are set. |

### Protocol Selection Logic

Use this decision flow after receiving detection results:

```
IF protocol = "kitty" AND (multiplexer = "none" OR passthroughEnabled = true):
    Use protocol "kitty"

ELSE IF protocol = "iterm2" AND (multiplexer = "none" OR passthroughEnabled = true):
    Use protocol "iterm2"

ELSE IF protocol != "none" AND multiplexer != "none" AND passthroughEnabled = false:
    Warn user: multiplexer is blocking graphics
    Suggest: enable passthrough (e.g., `tmux set -g allow-passthrough on`)
    Fall back to "ascii" or "browser"

ELSE (protocol = "none"):
    Use "ascii" or "browser" based on preference
```

### Understanding Confidence Levels

- **high**: A direct, unambiguous environment variable match was found. For example, `KITTY_WINDOW_ID` is set, which only Kitty provides. This is reliable.
- **medium**: An indirect indicator was found. The detection is likely correct but could have edge cases.
- **low**: No positive identification was made. The terminal is unknown. Use a fallback protocol.

---

## Frame Navigation Instructions

For trace visualizations (counterexample traces, behavior exploration), animations consist of multiple frames stored as SVG files in a directory. Use the `tlaplus_mcp_animation_frameCount` tool to discover and navigate these frames.

### Step 1: Discover Available Frames

Call `tlaplus_mcp_animation_frameCount` with the trace directory:

```
tlaplus_mcp_animation_frameCount
  traceDirectory: "/path/to/trace/output/"
  filePattern: "MySpec_anim_*.svg"    (optional, default: "*_anim_*.svg")
```

This returns:
```json
{
  "count": 5,
  "files": [
    "/path/to/trace/output/MySpec_anim_0.svg",
    "/path/to/trace/output/MySpec_anim_1.svg",
    "/path/to/trace/output/MySpec_anim_2.svg",
    "/path/to/trace/output/MySpec_anim_3.svg",
    "/path/to/trace/output/MySpec_anim_4.svg"
  ]
}
```

The files list is sorted by frame number extracted from the filename.

### Step 2: Render a Specific Frame

Use `tlaplus_mcp_animation_render` with the specific file path from the list:

```
tlaplus_mcp_animation_render
  protocol: "kitty"
  useCase: "trace"
  frameIndex: 0
  svgFilePath: "/path/to/trace/output/MySpec_anim_0.svg"
```

### Step 3: Navigate Forward and Backward

To show the next frame, increment the frame index and use the corresponding file path:

```
tlaplus_mcp_animation_render
  protocol: "kitty"
  useCase: "trace"
  frameIndex: 1
  svgFilePath: "/path/to/trace/output/MySpec_anim_1.svg"
```

To go back, decrement the frame index and use the corresponding file path. Frame navigation is manual -- you request each frame individually. There is no automatic playback.

### Navigation Summary

- Use `frameCount` once to get the full file list
- Use `render` repeatedly with specific `svgFilePath` and `frameIndex` values
- Track the current position in the file list yourself
- The `frameIndex` is 0-based: first frame is 0, last frame is `count - 1`

---

## Troubleshooting Common Issues

### Passthrough Not Enabled in tmux

**Symptom**: Detection returns `protocol: "kitty"` (or `"iterm2"`) but `passthroughEnabled: false`, and graphics do not display.

**Cause**: tmux blocks graphics escape sequences by default. The `allow-passthrough` option must be explicitly enabled.

**Fix**: Run the following command in your tmux session:

```bash
tmux set -g allow-passthrough on
```

To make this permanent, add to your `~/.tmux.conf`:

```
set -g allow-passthrough on
```

Then reload: `tmux source-file ~/.tmux.conf`

### Passthrough Not Enabled in GNU Screen

**Symptom**: Detection returns `multiplexer: "screen"` and `passthroughEnabled: false`.

**Cause**: GNU Screen does not natively support graphics passthrough in most versions.

**Fix**: Consider switching to tmux with `allow-passthrough on`, or use the ASCII or browser fallback instead.

### Graphics Protocol Not Detected

**Symptom**: Detection returns `protocol: "none"` even though you are using Kitty or iTerm2.

**Cause**: The relevant environment variables (`KITTY_WINDOW_ID`, `TERM_PROGRAM`) may not be propagated. This often happens when connecting via SSH or when the terminal does not set expected variables.

**Fix**:
- Verify the environment variable is set: run `echo $KITTY_WINDOW_ID` (for Kitty) or `echo $TERM_PROGRAM` (for iTerm2) in your shell.
- If connecting via SSH, ensure your SSH client forwards the relevant environment variables, or use `SendEnv`/`AcceptEnv` configuration.
- As a workaround, you can explicitly specify the protocol when calling render, bypassing detection:
  ```
  tlaplus_mcp_animation_render
    protocol: "kitty"
    ...
  ```

### Terminal Not Detected Correctly

**Symptom**: Detection returns the wrong protocol or low confidence.

**Cause**: The terminal may set unusual or non-standard environment variables.

**Fix**:
- Check the `environment` field in the detection result to see what variables were found.
- If the wrong protocol is detected, override it by specifying the protocol explicitly when calling render.
- Report the issue with the detection result so detection logic can be improved.

### Frame Too Large Error

**Symptom**: Render returns `FRAME_TOO_LARGE` error.

**Cause**: The rendered PNG exceeds the 1MB frame size limit. This typically happens with very large canvas dimensions (e.g., 4000x3000).

**Fix**:
- Reduce the `width` and `height` of your AnimView. For terminal rendering, 800x600 or smaller is recommended.
- Reduce the number of elements in the animation.
- Use the ASCII fallback, which is not subject to the PNG size limit.

### Detection Timeout

**Symptom**: Detect returns `DETECTION_TIMEOUT` error.

**Cause**: Terminal detection exceeded the 500ms time limit. This can happen if a tmux passthrough configuration query hangs.

**Fix**:
- Try running detection again. Transient delays may resolve.
- If in tmux, ensure `allow-passthrough` is configured (even setting it to `off` explicitly is faster than having tmux hang on the query).
- Use ASCII or browser fallback directly by calling render with `protocol: "ascii"` without detection.

---

## Configuration Options Reference

### Environment Variables

| Variable | Effect |
|----------|--------|
| `TLAPLUS_ANIMATION_FALLBACK` | Sets the default fallback preference when no graphics protocol is available. Values: `ascii`, `browser`. When set, the tool uses this fallback automatically instead of prompting. |
| `KITTY_WINDOW_ID` | Presence indicates Kitty terminal. Checked during detection. |
| `TERM_PROGRAM` | Checked for `iTerm.app` during detection. |
| `LC_TERMINAL` | Checked for `iTerm2` during detection. |
| `TMUX` | Presence indicates tmux multiplexer. Format: `/path/to/socket,pid,index`. |
| `STY` | Presence indicates GNU Screen multiplexer. |
| `TERM` | General terminal type. Checked for `xterm-kitty` during detection. |

### Tool Parameters: `tlaplus_mcp_animation_detect`

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `timeout` | number (optional) | 500 | Detection timeout in milliseconds. |

### Tool Parameters: `tlaplus_mcp_animation_render`

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `protocol` | `"kitty"`, `"iterm2"`, `"ascii"`, `"browser"` | Yes | Target rendering protocol. |
| `useCase` | `"live"`, `"static"`, `"trace"` | Yes | Context for the render: `live` for TLC exploration, `static` for a single frame, `trace` for saved trace files. |
| `frameIndex` | number (>= 0) | Yes | Frame index for navigation tracking. |
| `animView` | object | One of three | AnimView record with `frame`, `title`, `width`, `height`, `elements`. |
| `svgContent` | string | One of three | Raw SVG markup string. |
| `svgFilePath` | string | One of three | Absolute path to an SVG file on disk. |
| `asciiConfig` | object (optional) | No | ASCII rendering configuration (see below). |
| `fallbackPreference` | `"ascii"`, `"browser"`, `"prompt"`, `"none"` | No | Preferred fallback when graphics are unavailable. |

Exactly one of `animView`, `svgContent`, or `svgFilePath` must be provided. Providing zero or more than one causes a validation error.

**ASCII Config Sub-Parameters**:

| Parameter | Type | Default | Min | Max | Description |
|-----------|------|---------|-----|-----|-------------|
| `columns` | number | 80 | 40 | 200 | Canvas width in characters. |
| `rows` | number | 24 | 20 | 60 | Canvas height in characters. |
| `colorEnabled` | boolean | true | -- | -- | Whether to include ANSI color codes in output. |

### Tool Parameters: `tlaplus_mcp_animation_frameCount`

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `traceDirectory` | string | Yes | Absolute path to the directory containing trace SVG files. |
| `filePattern` | string | No | Glob pattern for matching trace files. Default: `*_anim_*.svg`. |

### Protocol Override

You can bypass detection entirely by specifying the protocol directly in the render call. This is useful when detection fails or returns incorrect results. The render operation never re-detects -- it trusts the protocol you provide.

---

## Terminal Rendering Examples

### Example 1: Kitty Terminal Workflow

This example shows the complete workflow for rendering an animation in a Kitty terminal.

**Step 1: Detect terminal capabilities**

```
tlaplus_mcp_animation_detect
```

Expected result:
```json
{
  "protocol": "kitty",
  "multiplexer": "none",
  "passthroughEnabled": true,
  "passthroughVerified": false,
  "fallbackAvailable": ["ascii", "browser"],
  "detectionMethod": "env",
  "confidence": "high",
  "environment": {
    "TERM": "xterm-kitty",
    "KITTY_WINDOW_ID": "1"
  }
}
```

The result shows Kitty protocol with high confidence (the `KITTY_WINDOW_ID` variable is a definitive indicator). No multiplexer is present, so passthrough is not a concern.

**Step 2: Render a live animation frame**

```
tlaplus_mcp_animation_render
  protocol: "kitty"
  useCase: "live"
  frameIndex: 0
  animView:
    frame: "0"
    title: "Counter State"
    width: 400
    height: 200
    elements:
      - shape: "rect"
        x: 20
        y: 20
        width: 360
        height: 160
        fill: "#2c3e50"
        stroke: "#ecf0f1"
        strokeWidth: 2
      - shape: "text"
        x: 200
        y: 110
        text: "count = 5"
        fill: "#ecf0f1"
        fontSize: 24
```

The tool rasterizes the AnimView to a PNG, encodes it with the Kitty graphics protocol escape sequence, and returns:
```json
{
  "output": "\u001b_Ga=T,f=100,m=0;iVBORw0KGgo...\u001b\\",
  "protocol": "kitty",
  "frameIndex": 0
}
```

The `output` string, when written to the terminal, displays the image inline.

**Step 3: Render next frame with updated state**

```
tlaplus_mcp_animation_render
  protocol: "kitty"
  useCase: "live"
  frameIndex: 1
  animView:
    frame: "1"
    title: "Counter State"
    width: 400
    height: 200
    elements:
      - shape: "rect"
        x: 20
        y: 20
        width: 360
        height: 160
        fill: "#2c3e50"
        stroke: "#ecf0f1"
        strokeWidth: 2
      - shape: "text"
        x: 200
        y: 110
        text: "count = 6"
        fill: "#ecf0f1"
        fontSize: 24
```

### Example 2: iTerm2 Terminal Workflow

This example shows the workflow for iTerm2 on macOS, including detection through tmux.

**Step 1: Detect terminal capabilities**

```
tlaplus_mcp_animation_detect
```

Expected result (iTerm2 behind tmux with passthrough enabled):
```json
{
  "protocol": "iterm2",
  "multiplexer": "tmux",
  "passthroughEnabled": true,
  "passthroughVerified": false,
  "fallbackAvailable": ["ascii", "browser"],
  "detectionMethod": "env",
  "confidence": "high",
  "environment": {
    "TERM_PROGRAM": "iTerm.app",
    "LC_TERMINAL": "iTerm2",
    "TERM": "xterm-256color",
    "TMUX": "/tmp/tmux-501/default,12345,0"
  }
}
```

The result shows iTerm2 protocol detected via `TERM_PROGRAM`. tmux is present but `passthroughEnabled` is `true`, so graphics will work.

**Step 2: Render a frame from a saved SVG file**

```
tlaplus_mcp_animation_render
  protocol: "iterm2"
  useCase: "static"
  frameIndex: 0
  svgFilePath: "/tmp/MySpec_anim_0.svg"
```

Result:
```json
{
  "output": "\u001b]1337;File=inline=1;size=8432:iVBORw0KGgo...\u0007",
  "protocol": "iterm2",
  "frameIndex": 0
}
```

**Step 3: Navigate a trace with multiple frames**

First discover the frames:
```
tlaplus_mcp_animation_frameCount
  traceDirectory: "/tmp/trace/"
  filePattern: "MySpec_anim_*.svg"
```

Result:
```json
{
  "count": 3,
  "files": [
    "/tmp/trace/MySpec_anim_0.svg",
    "/tmp/trace/MySpec_anim_1.svg",
    "/tmp/trace/MySpec_anim_2.svg"
  ]
}
```

Then render each frame:
```
tlaplus_mcp_animation_render
  protocol: "iterm2"
  useCase: "trace"
  frameIndex: 0
  svgFilePath: "/tmp/trace/MySpec_anim_0.svg"
```

To advance to the next frame:
```
tlaplus_mcp_animation_render
  protocol: "iterm2"
  useCase: "trace"
  frameIndex: 1
  svgFilePath: "/tmp/trace/MySpec_anim_1.svg"
```

### Example 3: ASCII Fallback Workflow

This example shows the workflow when no graphics protocol is available, using the ASCII art fallback.

**Step 1: Detect terminal capabilities**

```
tlaplus_mcp_animation_detect
```

Expected result (plain terminal without graphics):
```json
{
  "protocol": "none",
  "multiplexer": "none",
  "passthroughEnabled": false,
  "passthroughVerified": false,
  "fallbackAvailable": ["ascii", "browser"],
  "detectionMethod": "env",
  "confidence": "low",
  "environment": {
    "TERM": "xterm-256color"
  }
}
```

The result shows no graphics protocol detected. The `fallbackAvailable` field confirms ASCII and browser are available.

**Step 2: Render using ASCII protocol**

Since `protocol` is `"none"`, choose `"ascii"` as the render protocol:

```
tlaplus_mcp_animation_render
  protocol: "ascii"
  useCase: "live"
  frameIndex: 0
  animView:
    frame: "0"
    title: "State Machine"
    width: 200
    height: 100
    elements:
      - shape: "rect"
        x: 10
        y: 10
        width: 80
        height: 40
        fill: "blue"
      - shape: "circle"
        cx: 140
        cy: 30
        r: 15
        fill: "red"
      - shape: "text"
        x: 50
        y: 35
        text: "S0"
        fill: "white"
  asciiConfig:
    columns: 80
    rows: 24
    colorEnabled: true
```

Result:
```json
{
  "output": "\u001b[34m\u250c\u2500\u2500\u2500\u2500\u2500\u2500\u2510\n\u2502      \u2502\n\u2502  S0  \u2502\n\u2502      \u2502\n\u2514\u2500\u2500\u2500\u2500\u2500\u2500\u2518\u001b[0m  \u001b[31m\u25cf\u001b[0m",
  "protocol": "ascii",
  "frameIndex": 0,
  "dimensions": {
    "cols": 80,
    "rows": 24
  }
}
```

The ASCII output uses Unicode box-drawing characters for rectangles and circle symbols, with ANSI color codes applied (blue for the rectangle, red for the circle).

**Step 3: Render without colors (for logging or piping)**

If ANSI colors are not desired (e.g., writing output to a log file), disable them:

```
tlaplus_mcp_animation_render
  protocol: "ascii"
  useCase: "live"
  frameIndex: 0
  animView:
    frame: "0"
    title: "State Machine"
    width: 200
    height: 100
    elements:
      - shape: "rect"
        x: 10
        y: 10
        width: 80
        height: 40
        fill: "blue"
  asciiConfig:
    columns: 60
    rows: 20
    colorEnabled: false
```

This produces plain ASCII without color escape codes, suitable for any output destination.
