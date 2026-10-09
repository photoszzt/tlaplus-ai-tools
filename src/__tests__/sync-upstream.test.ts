import { spawnSync } from "child_process";
import * as path from "path";

it("preserves local upstream adaptations and delegates JAR updates", () => {
  const result = spawnSync(
    process.platform === "win32" ? "python" : "python3",
    ["scripts/test_sync_upstream.py"],
    {
      cwd: path.resolve(__dirname, "../.."),
      encoding: "utf8",
      timeout: 30000,
    },
  );
  expect(result.error).toBeUndefined();
  if (result.status !== 0) throw new Error(result.stdout + result.stderr);
  expect(result.status).toBe(0);
});
