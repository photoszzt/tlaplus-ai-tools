---- MODULE CounterAnim ----
EXTENDS TLC, SVG, Sequences, Counter

\* Color based on counter value
CounterColor ==
    CASE x <= 3 -> "green"
      [] x <= 7 -> "yellow"
      [] x <= 10 -> "orange"
      [] OTHER -> "red"

\* Progress bar background
ProgressBarBg ==
    [shape |-> "rect",
     x |-> 50,
     y |-> 150,
     width |-> 500,
     height |-> 40,
     fill |-> "lightgray",
     stroke |-> "black",
     strokeWidth |-> 2]

\* Progress bar fill (proportional to x)
ProgressBarFill ==
    [shape |-> "rect",
     x |-> 50,
     y |-> 150,
     width |-> (x * 50),
     height |-> 40,
     fill |-> CounterColor,
     stroke |-> "none"]

\* Counter value text
CounterText ==
    [shape |-> "text",
     x |-> 300,
     y |-> 100,
     text |-> "Counter: " \o ToString(x),
     fontSize |-> 32,
     fill |-> "black",
     fontFamily |-> "Arial",
     fontWeight |-> "bold"]

\* Status text based on position
StatusText ==
    LET status == CASE x = 0 -> "Initial State"
                    [] x < 5 -> "Incrementing..."
                    [] x < 10 -> "Approaching Limit"
                    [] x = 10 -> "At Maximum!"
                    [] OTHER -> "INVARIANT VIOLATED!"
    IN [shape |-> "text",
        x |-> 300,
        y |-> 250,
        text |-> status,
        fontSize |-> 20,
        fill |-> CounterColor,
        fontFamily |-> "Arial",
        textAnchor |-> "middle"]

\* Scale markers (0, 5, 10)
ScaleMarkers ==
    LET Marker(val) == [shape |-> "g", elements |-> <<
            [shape |-> "line",
             x1 |-> 50 + (val * 50),
             y1 |-> 190,
             x2 |-> 50 + (val * 50),
             y2 |-> 205,
             stroke |-> "black",
             strokeWidth |-> 2],
            [shape |-> "text",
             x |-> 50 + (val * 50),
             y |-> 225,
             text |-> ToString(val),
             fontSize |-> 14,
             fill |-> "black",
             textAnchor |-> "middle"]
        >>]
    IN [shape |-> "g", elements |-> <<
        Marker(0), Marker(5), Marker(10)
    >>]

\* All animation elements
AnimElements == <<
    ProgressBarBg,
    ProgressBarFill,
    CounterText,
    StatusText,
    ScaleMarkers
>>

\* Animation view
AnimView == [
    frame |-> "CounterAnimation",
    title |-> "Counter Specification Animation",
    width |-> 600,
    height |-> 300,
    elements |-> AnimElements
]

\* TLC alias for animation
AnimAlias == [
    view |-> AnimView
]

\* Debugger watch expression
AnimWatch == AnimView

====
