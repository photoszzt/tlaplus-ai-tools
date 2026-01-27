# TLA+ Animation Patterns

Common patterns and techniques for creating effective TLA+ animations.

## Basic Patterns

### Counter/Progress Bar

Visualize numeric progress:
```tla
AnimElements ==
    LET
        barWidth == 700
        progress == (count * barWidth) \div MaxValue
        percentText == ToString((count * 100) \div MaxValue) \o "%"
    IN <<
        \* Background
        [shape |-> "rect", x |-> 50, y |-> 250,
         width |-> barWidth, height |-> 100,
         fill |-> "lightgray", stroke |-> "black", strokeWidth |-> 2],

        \* Progress fill
        [shape |-> "rect", x |-> 50, y |-> 250,
         width |-> progress, height |-> 100,
         fill |-> "blue"],

        \* Percentage text
        [shape |-> "text", x |-> 400, y |-> 310,
         text |-> percentText,
         fontSize |-> 36, fill |-> "white", fontFamily |-> "Arial"]
    >>
```

### State Machine

Visualize state transitions:
```tla
AnimElements ==
    LET
        \* State positions
        states == [
            idle   |-> <<200, 300>>,
            active |-> <<400, 300>>,
            done   |-> <<600, 300>>
        ]

        \* Draw state circle
        StateCircle(name, pos) ==
            [shape |-> "circle",
             cx |-> pos[1], cy |-> pos[2], r |-> 40,
             fill |-> IF status = name THEN "green" ELSE "lightgray",
             stroke |-> "black", strokeWidth |-> 2]

        \* Draw state label
        StateLabel(name, pos) ==
            [shape |-> "text",
             x |-> pos[1], y |-> pos[2] + 5,
             text |-> name,
             fontSize |-> 14, fill |-> "black",
             textAnchor |-> "middle"]
    IN <<
        StateCircle("idle", states.idle),
        StateLabel("idle", states.idle),
        StateCircle("active", states.active),
        StateLabel("active", states.active),
        StateCircle("done", states.done),
        StateLabel("done", states.done)
    >>
```

### Collection Visualization

Visualize sets or sequences:
```tla
AnimElements ==
    LET
        \* Convert set to sequence for iteration
        itemSeq == SetToSeq(items)
        numItems == Len(itemSeq)

        \* Draw item at position i
        DrawItem(i) ==
            [shape |-> "circle",
             cx |-> 100 + i * 60,
             cy |-> 300,
             r |-> 25,
             fill |-> "blue",
             stroke |-> "black"]

        \* Label for item
        ItemLabel(i) ==
            [shape |-> "text",
             x |-> 100 + i * 60,
             y |-> 305,
             text |-> ToString(itemSeq[i]),
             fontSize |-> 12, fill |-> "white",
             textAnchor |-> "middle"]
    IN
        \* Generate elements for all items
        <<DrawItem(i) : i \in 1..numItems>> \o
        <<ItemLabel(i) : i \in 1..numItems>>
```

## Advanced Patterns

### Queue/Buffer

Visualize FIFO queue:
```tla
AnimElements ==
    LET
        queueLen == Len(queue)
        maxSlots == 10
        slotWidth == 60
        slotHeight == 50
        startX == 100
        startY == 250

        \* Draw empty slot
        EmptySlot(i) ==
            [shape |-> "rect",
             x |-> startX + (i-1) * slotWidth,
             y |-> startY,
             width |-> slotWidth - 2,
             height |-> slotHeight,
             fill |-> "white",
             stroke |-> "gray"]

        \* Draw filled slot
        FilledSlot(i) ==
            [shape |-> "rect",
             x |-> startX + (i-1) * slotWidth,
             y |-> startY,
             width |-> slotWidth - 2,
             height |-> slotHeight,
             fill |-> "lightblue",
             stroke |-> "black"]

        \* Draw value in slot
        SlotValue(i, value) ==
            [shape |-> "text",
             x |-> startX + (i-1) * slotWidth + slotWidth \div 2,
             y |-> startY + slotHeight \div 2 + 5,
             text |-> ToString(value),
             fontSize |-> 14, textAnchor |-> "middle"]

        \* Filled slots
        filled == <<FilledSlot(i) : i \in 1..queueLen>>
        \* Empty slots
        empty == <<EmptySlot(i) : i \in (queueLen+1)..maxSlots>>
        \* Values
        values == <<SlotValue(i, queue[i]) : i \in 1..queueLen>>
    IN
        filled \o empty \o values
```

### Actor Network

Visualize communicating processes:
```tla
AnimElements ==
    LET
        \* Process positions in circle
        ProcessPos(p, total) ==
            LET
                angle == (2 * 3.14159 * (p-1)) / total
                radius == 200
                centerX == 400
                centerY == 300
            IN
                <<centerX + radius * Cos(angle),
                  centerY + radius * Sin(angle)>>

        \* Draw process
        DrawProcess(p) ==
            LET pos == ProcessPos(p, NumProcesses)
            IN
                [shape |-> "circle",
                 cx |-> pos[1], cy |-> pos[2], r |-> 30,
                 fill |-> IF p = leader THEN "gold" ELSE "lightblue",
                 stroke |-> "black"]

        \* Draw message in transit
        DrawMessage(from, to) ==
            LET
                fromPos == ProcessPos(from, NumProcesses)
                toPos == ProcessPos(to, NumProcesses)
            IN
                [shape |-> "line",
                 x1 |-> fromPos[1], y1 |-> fromPos[2],
                 x2 |-> toPos[1], y2 |-> toPos[2],
                 stroke |-> "red", strokeWidth |-> 2]

        processes == <<DrawProcess(p) : p \in 1..NumProcesses>>
        messages == <<DrawMessage(msg.from, msg.to) : msg \in network>>
    IN
        messages \o processes  \* Messages behind processes
```

### Timeline

Visualize events over time:
```tla
AnimElements ==
    LET
        maxTime == 20
        timelineY == 300
        startX == 100
        endX == 700
        pixelsPerTime == (endX - startX) / maxTime

        \* Timeline base
        timeline ==
            [shape |-> "line",
             x1 |-> startX, y1 |-> timelineY,
             x2 |-> endX, y2 |-> timelineY,
             stroke |-> "black", strokeWidth |-> 2]

        \* Current time marker
        marker ==
            [shape |-> "line",
             x1 |-> startX + time * pixelsPerTime,
             y1 |-> timelineY - 20,
             x2 |-> startX + time * pixelsPerTime,
             y2 |-> timelineY + 20,
             stroke |-> "red", strokeWidth |-> 3]

        \* Event markers
        Event(t) ==
            [shape |-> "circle",
             cx |-> startX + t * pixelsPerTime,
             cy |-> timelineY,
             r |-> 5,
             fill |-> "blue"]

        events == <<Event(e.time) : e \in eventLog>>
    IN
        <<timeline>> \o events \o <<marker>>
```

## Color Patterns

### State-Based Coloring

```tla
StateColor(s) ==
    CASE s = "idle"   -> "gray"
      [] s = "active" -> "green"
      [] s = "error"  -> "red"
      [] s = "done"   -> "blue"
```

### Value-Based Coloring

```tla
HeatmapColor(value, maxValue) ==
    CASE value = 0                     -> "blue"
      [] value < maxValue \div 3       -> "green"
      [] value < 2 * maxValue \div 3   -> "yellow"
      [] OTHER                          -> "red"
```

### Boolean Coloring

```tla
BoolColor(condition) ==
    IF condition THEN "green" ELSE "red"
```

## Layout Patterns

### Grid Layout

```tla
GridPos(row, col, cellSize) ==
    <<50 + col * cellSize, 50 + row * cellSize>>
```

### Circular Layout

```tla
CirclePos(index, total, radius, center) ==
    LET angle == (2 * PI * index) / total
    IN <<center[1] + radius * Cos(angle),
         center[2] + radius * Sin(angle)>>
```

### Tree Layout

```tla
TreePos(node, level, position) ==
    <<100 + position * 100, 50 + level * 80>>
```

## Conditional Visibility

### Show/Hide Elements

```tla
elements ==
    IF showDetails
    THEN detailedElements
    ELSE simpleElements
```

### Conditional Inclusion

```tla
elements ==
    baseElements \o
    (IF condition THEN specialElements ELSE <<>>)
```

## Animation Helpers

### LET Blocks for Clarity

```tla
AnimElements ==
    LET
        \* Define helpers
        width == 800
        height == 600
        centerX == width \div 2
        centerY == height \div 2

        \* Define components
        background == [...]
        foreground == [...]
        labels == [...]
    IN
        <<background>> \o foreground \o labels
```

### Reusable Element Functions

```tla
LET
    Box(x, y, w, h, color) ==
        [shape |-> "rect", x |-> x, y |-> y,
         width |-> w, height |-> h, fill |-> color]

    Label(x, y, txt) ==
        [shape |-> "text", x |-> x, y |-> y, text |-> txt]
IN
    <<Box(100, 100, 50, 50, "blue"), Label(125, 125, "Box1")>>
```

## Performance Tips

### Limit Element Count

```tla
\* Instead of showing all items
allItems == {DrawItem(i) : i \in items}  \* Could be 1000+

\* Show first N items
limitedItems == {DrawItem(i) : i \in 1..Min(Len(items), 20)}
```

### Simplify for Large State

```tla
elements ==
    IF Cardinality(items) > 100
    THEN summaryView     \* Simple representation
    ELSE detailedView    \* Full visualization
```

## Testing Animations

### Start Simple

```tla
\* Version 1: Just one element
AnimElements == <<[shape |-> "circle", cx |-> 400, cy |-> 300, r |-> 30]>>

\* Version 2: Add position
AnimElements == <<[shape |-> "circle", cx |-> x * 50, cy |-> 300, r |-> 30]>>

\* Version 3: Add color
...
```

### Test with Small Traces

```
/tla-check @SpecAnim.tla with behaviorLength 3
```

Verify animation works before long traces.

### Validate Coordinates

```tla
\* Ensure within canvas
ValidX(x) == x >= 0 /\ x <= 800
ValidY(y) == y >= 0 /\ y <= 600
```

## Common Issues

### Elements Outside Canvas

```tla
\* Problem: x could be negative or > 800
x |-> varValue * 100

\* Fix: Clamp to canvas
x |-> Max(0, Min(800, varValue * 100))
```

### Overlapping Elements

```tla
\* Problem: All at same position
cx |-> 100

\* Fix: Space them out
cx |-> 100 + index * spacing
```

### Invisible Text

```tla
\* Problem: Text color same as background
fill |-> "white"  \* On white background

\* Fix: Contrast color
fill |-> "black"
```

## Best Practices

1. **Start with static layout** - Get positions right
2. **Add dynamics gradually** - One variable at a time
3. **Use meaningful colors** - Consistent scheme
4. **Add labels** - Show variable values
5. **Keep it simple** - Don't over-complicate
6. **Test incrementally** - After each addition
7. **Document layout** - Comment coordinate choices

Effective animations make TLA+ specifications come alive, helping understand system behavior visually.
