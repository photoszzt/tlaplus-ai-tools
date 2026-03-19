# Path Normalization

When a skill receives a file path argument, it may include a leading `@` prefix (e.g., `@Counter.tla`). This prefix is added by Claude Code's file reference system and should be stripped before use.

## Rules

1. If the argument starts with `@`, remove the leading `@` to get the actual file path
2. If the argument does not start with `@`, use it as-is
3. Both forms (`@Counter.tla` and `Counter.tla`) are equivalent — the `@` is optional

## Example

```
Input:  @test-specs/Counter.tla
Output: test-specs/Counter.tla

Input:  test-specs/Counter.tla
Output: test-specs/Counter.tla
```
