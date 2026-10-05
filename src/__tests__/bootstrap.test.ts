import { spawnSync } from "child_process";
import * as path from "path";

it("starts with installed SDK subpath exports and auto-install disabled", () => {
  const root = path.resolve(__dirname, "../..");
  const result = spawnSync(process.execPath, ["scripts/start.js", "--help"], {
    cwd: root,
    env: { ...process.env, TLAPLUS_NO_AUTO_INSTALL: "1" },
    encoding: "utf8",
    timeout: 5000,
  });

  expect(result.error).toBeUndefined();
  expect(result.stderr).toBe("");
  expect(result.status).toBe(0);
  expect(result.stdout).toContain("USAGE:");
});
