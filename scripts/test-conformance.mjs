#!/usr/bin/env node
import { spawn } from "node:child_process";
import { mkdtemp, mkdir, readFile, writeFile, readdir, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const repo = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const ref = "c37eec888e1c6ff140af79987a40008548b7cc5f";
const npmCli = process.env.npm_execpath;
if (!npmCli) throw new Error("Run this command through npm run test:conformance");
const flags = process.argv.slice(2);
if (flags.length > 1 || flags.some((flag) => !["--production", "--fixtures"].includes(flag))) {
  throw new Error("Usage: npm run test:conformance -- [--production|--fixtures]");
}
const mode =
  flags[0] === "--production" ? "production" : flags[0] === "--fixtures" ? "fixtures" : "audit";
const productionScenarios = [
  "server-initialize",
  "logging-set-level",
  "ping",
  "tools-list",
  "resources-list",
  "prompts-list",
  "dns-rebinding-protection",
];
const sessionScenarios = ["server-session-lifecycle", "server-sse-multiple-streams"];
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
    if (mode === "production" && name === "fixtures") continue;
    if (mode === "fixtures" && name !== "fixtures") continue;
    const { child, url } = await start(
      entry,
      name === "application-sessions" ? ["--http-session"] : [],
    );
    try {
      const scenarios =
        mode === "production"
          ? [...productionScenarios, ...(name === "application-sessions" ? sessionScenarios : [])]
          : [undefined];
      for (const scenario of scenarios) {
        const outputDir = path.join(
          results,
          mode === "production" ? `${name}-selected` : name,
          ...(scenario ? [scenario] : []),
        );
        await mkdir(outputDir, { recursive: true });
        const previousReports = new Set(await readdir(outputDir));
        const args = [
          tsx,
          cli,
          "server",
          "--url",
          url,
          ...(scenario ? ["--scenario", scenario] : ["--suite", "active"]),
          "--spec-version",
          "2025-11-25",
          "--output-dir",
          outputDir,
        ];
        if (mode === "audit" && name !== "fixtures")
          args.push(
            "--expected-failures",
            name === "application-sessions" ? sessionBaseline : baseline,
          );
        await run(process.execPath, args, suite);
        if (mode === "production") {
          const reports = (await readdir(outputDir, { withFileTypes: true })).filter(
            (entry) => entry.isDirectory() && !previousReports.has(entry.name),
          );
          if (reports.length !== 1) throw new Error(`Expected one fresh report for ${scenario}`);
          const checks = JSON.parse(
            await readFile(path.join(outputDir, reports[0].name, "checks.json"), "utf8"),
          );
          if (
            !Array.isArray(checks) ||
            !checks.some((check) => check.status === "SUCCESS") ||
            checks.some((check) => !["SUCCESS", "INFO"].includes(check.status))
          ) {
            throw new Error(`Unsuccessful or unexercised production scenario: ${scenario}`);
          }
        }
      }
    } finally {
      await stop(child);
    }
  }
  await writeFile(
    path.join(results, "metadata.json"),
    JSON.stringify(
      {
        suiteRef: ref,
        mode,
        specVersion: "2025-11-25",
        ...(mode === "production"
          ? {
              productionScenarios,
              sessionScenarios,
              coverage:
                "Selected production scenarios only; no expected failures; fixture-named tool cases excluded",
            }
          : {}),
        ...(mode === "audit"
          ? {
              applicationBaseline:
                "20 prescribed fixture scenarios remain expected; not full conformance",
              applicationSessions:
                "Production session mode; no optional session gate in its baseline",
            }
          : {}),
        ...(mode !== "production" ? { fixtures: "Full active suite; no expected failures" } : {}),
        packageVersion: JSON.parse(await readFile(path.join(repo, "package.json"), "utf8")).version,
      },
      null,
      2,
    ),
  );
  console.log(`Conformance reports: ${results}`);
  console.log(
    mode === "production"
      ? "Selected production conformance passed with no expected failures."
      : mode === "fixtures"
        ? "Full fixture conformance passed with no expected failures."
        : "Application baseline checked; fixture conformance passed. These are separate results.",
  );
} catch (error) {
  console.error(error);
  process.exitCode = 1;
} finally {
  await rm(scratch, { recursive: true, force: true });
}
