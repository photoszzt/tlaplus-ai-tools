# Path Normalization

When a skill receives a file path argument, it may include a leading `@` prefix (e.g., `@Counter.tla`). Strip this prefix before using the path.

## Rules

1. If the argument starts with `@`, remove only a single leading `@` to get the actual file path (e.g., `@@file` becomes `@file`)
2. If the argument does not start with `@`, use it as-is
3. Both forms (`@Counter.tla` and `Counter.tla`) are equivalent — the `@` is optional
4. If the resulting path is already absolute, use it as-is. Otherwise, resolve it relative to the task's working directory, not the cached plugin directory or MCP server's working directory

Before an MCP call, send the resolved absolute filesystem paths. The examples
below illustrate only removal of the `@` prefix.

## Examples

```
Input:  @test-specs/Counter.tla
Output: test-specs/Counter.tla

Input:  test-specs/Counter.tla
Output: test-specs/Counter.tla

Input:  @/home/user/specs/Counter.tla
Output: /home/user/specs/Counter.tla

Input:  @@literal-at-file.tla
Output: @literal-at-file.tla
```

**Note:** If no path argument is provided, the skill should prompt the user for a file path rather than proceeding with an empty path.
