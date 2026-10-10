#!/usr/bin/env node
import { spawn } from "node:child_process";
import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const repo = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const ref = "c37eec888e1c6ff140af79987a40008548b7cc5f";
const npmCli = process.env.npm_execpath;
if (!npmCli) throw new Error("Run this command through npm run test:conformance");
const scratch = await mkdtemp(path.join(tmpdir(), "tlaplus-conformance-"));
const suite = path.join(scratch, "suite");
const results = path.join(repo, "conformance-results");
await mkdir(results, { recursive: true });

function run(command, args, cwd = repo) {
  return new Promise((resolve, reject) => {
    const child = spawn(command, args, { cwd, stdio: "inherit" });
    child.once("error", reject);
    child.once("exit", (code, signal) => {
      if (code === 0) resolve();
      else reject(new Error(`${command} exited with ${code ?? signal}`));
    });
  });
}

async function start(entry, extraArgs = []) {
  const child = spawn(
    process.execPath,
    [
      "--import",
      "tsx",
      entry,
      ...(entry.endsWith("index.ts") ? ["--http", "--port", "0", ...extraArgs] : []),
    ],
    {
      cwd: repo,
      stdio: ["ignore", "pipe", "inherit"],
    },
  );
  let output = "";
  const url = await new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      child.kill();
      reject(new Error(`Startup timed out: ${output}`));
    }, 20000);
    child.once("error", (error) => {
      clearTimeout(timer);
      reject(error);
    });
    child.once("exit", (code) => {
      clearTimeout(timer);
      reject(new Error(`Server exited: ${code}`));
    });
    child.stdout.on("data", (chunk) => {
      output = (output + chunk.toString()).slice(-8192);
      const match = /listening at http:\/\/[^:]+:(\d+)\/mcp/.exec(output);
      if (match) {
        clearTimeout(timer);
        resolve(`http://127.0.0.1:${match[1]}/mcp`);
      }
    });
  }).catch(async (error) => {
    await stop(child);
    throw error;
  });
  return { child, url };
}

async function stop(child) {
  if (!child.pid || child.exitCode !== null || child.signalCode !== null) return;
  await new Promise((resolve) => {
    const timer = setTimeout(() => child.kill("SIGKILL"), 5000);
    child.once("exit", () => {
      clearTimeout(timer);
      resolve();
    });
    child.kill();
  });
}

try {
  await run("git", [
    "clone",
    "--quiet",
    "https://github.com/modelcontextprotocol/conformance.git",
    suite,
  ]);
  await run("git", ["checkout", "--quiet", ref], suite);
  await run(process.execPath, [npmCli, "ci", "--ignore-scripts"], suite);
  const cli = path.join(suite, "src/index.ts");
  const tsx = path.join(suite, "node_modules/tsx/dist/cli.mjs");
  const baseline = path.join(repo, "src/__tests__/fixtures/conformance-baseline.yml");
  const sessionBaseline = path.join(scratch, "session-baseline.yml");
  await writeFile(
    sessionBaseline,
    (await readFile(baseline, "utf8"))
      .split("\n")
      .filter((line) => !line.includes("server-sse-multiple-streams-session"))
      .join("\n"),
  );
  for (const [name, entry] of [
    ["application", path.join(repo, "src/index.ts")],
    ["application-sessions", path.join(repo, "src/index.ts")],
    ["fixtures", path.join(repo, "src/__tests__/fixtures/conformance-server.ts")],
  ]) {
    const { child, url } = await start(
      entry,
      name === "application-sessions" ? ["--http-session"] : [],
    );
    try {
      const args = [
        tsx,
        cli,
        "server",
        "--url",
        url,
        "--suite",
        "active",
        "--spec-version",
        "2025-11-25",
        "--output-dir",
        path.join(results, name),
      ];
      if (name !== "fixtures")
        args.push(
          "--expected-failures",
          name === "application-sessions" ? sessionBaseline : baseline,
        );
      await run(process.execPath, args, suite);
    } finally {
      await stop(child);
    }
  }
  await writeFile(
    path.join(results, "metadata.json"),
    JSON.stringify(
      {
        suiteRef: ref,
        specVersion: "2025-11-25",
        applicationBaseline:
          "20 prescribed fixture scenarios remain expected; not full conformance",
        applicationSessions: "Production session mode; no optional session gate in its baseline",
        fixtures: "Full active suite; no expected failures",
        packageVersion: JSON.parse(await readFile(path.join(repo, "package.json"), "utf8")).version,
      },
      null,
      2,
    ),
  );
  console.log(`Conformance reports: ${results}`);
  console.log(
    "Application baseline checked; fixture conformance passed. These are separate results.",
  );
} catch (error) {
  console.error(error);
  process.exitCode = 1;
} finally {
  await rm(scratch, { recursive: true, force: true });
}
