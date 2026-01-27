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
