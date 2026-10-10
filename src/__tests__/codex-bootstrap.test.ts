import { spawnSync } from "child_process";
import * as fs from "fs";
import * as os from "os";
import * as path from "path";

it("starts a cached plugin after runtime-only install and JAR setup, and stops on setup failure", () => {
  const root = path.resolve(__dirname, "../..");
  const manifest = JSON.parse(
    fs.readFileSync(path.join(root, ".codex-plugin/plugin.json"), "utf8"),
  );
  const config = JSON.parse(fs.readFileSync(path.join(root, manifest.mcpServers), "utf8"))
    .mcpServers.tlaplus;
  expect(fs.existsSync(path.join(root, manifest.skills, "tla-setup/SKILL.md"))).toBe(true);
  const work = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), "codex-bootstrap-")));
  const tools = path.join(work, "jar-cache");
  try {
    fs.mkdirSync(path.join(work, "scripts"));
    fs.mkdirSync(path.join(work, "dist"));
    fs.copyFileSync(path.join(root, "scripts/start.js"), path.join(work, "scripts/start.js"));
    fs.writeFileSync(path.join(work, "package-lock.json"), "{}");
    fs.writeFileSync(
      path.join(work, "dist/index.js"),
      'console.log(JSON.stringify({ready: true, toolsDir: process.argv[process.argv.indexOf("--tools-dir") + 1]}));',
    );
    const preload = path.join(work, "preload.cjs");
    fs.writeFileSync(
      preload,
      `
      const assert = require('node:assert/strict');
      const fs = require('node:fs');
      const path = require('node:path');
      const root = ${JSON.stringify(work)};
      require('node:child_process').execFileSync = (command, args, options) => {
        assert.deepEqual(options.stdio, ['ignore', 'pipe', 'pipe']);
        if (command === 'npm' || command === 'npm.cmd') {
          assert(args.includes('--ignore-scripts') && args.includes('--omit=dev'));
          for (const name of ['@modelcontextprotocol/sdk/server/mcp.js', '@modelcontextprotocol/sdk/server/stdio.js', '@modelcontextprotocol/sdk/server/streamableHttp.js', 'fast-xml-parser/index.js', 'zod/index.js', 'express/index.js', 'adm-zip/index.js']) {
            const file = path.join(root, 'node_modules', name);
            fs.mkdirSync(path.dirname(file), {recursive: true});
            fs.writeFileSync(file, 'module.exports = {};');
          }
          return Buffer.from('INSTALL OUTPUT MUST STAY OFF STDOUT');
        }
        assert.equal(command, process.execPath);
        assert.equal(args[0], path.join(root, 'scripts/setup.js'));
        if (process.env.FAKE_SETUP_FAILURE === '1') throw new Error('SETUP FAILED');
        fs.mkdirSync(process.env.TLA_TOOLS_DIR);
        for (const jar of ['tla2tools.jar', 'CommunityModules-deps.jar']) fs.writeFileSync(path.join(process.env.TLA_TOOLS_DIR, jar), 'fixture');
        return Buffer.from('SETUP OUTPUT MUST STAY OFF STDOUT');
      };
    `,
    );
    const run = (fail: boolean) =>
      spawnSync(process.execPath, ["--require", preload, ...config.args], {
        cwd: path.resolve(work, config.cwd),
        env: {
          ...process.env,
          ...config.env,
          TLAPLUS_NO_AUTO_INSTALL: "0",
          TLA_TOOLS_DIR: tools,
          FAKE_SETUP_FAILURE: fail ? "1" : "0",
        },
        encoding: "utf8",
        timeout: 10000,
      });
    const ready = run(false);
    expect(ready.error).toBeUndefined();
    if (ready.status !== 0) throw new Error(ready.stdout + ready.stderr);
    expect(ready.status).toBe(0);
    expect(JSON.parse(ready.stdout)).toEqual({ ready: true, toolsDir: tools });
    expect(fs.existsSync(path.join(work, "tools"))).toBe(false);
    fs.rmSync(tools, { recursive: true });
    const failed = run(true);
    expect(failed.status).toBe(1);
    expect(failed.stdout).toBe("");
    expect(failed.stderr).toContain("Failed to set up TLA+ tools");
    expect(failed.stderr).toContain("SETUP FAILED");
  } finally {
    fs.rmSync(work, { recursive: true, force: true });
  }
});
