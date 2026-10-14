#!/usr/bin/env node
import { spawn, execFileSync } from "node:child_process";
import { mkdtemp, mkdir, readFile, writeFile, readdir, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { createHash } from "node:crypto";
import { fileURLToPath, pathToFileURL } from "node:url";

const repo = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const ref = "c37eec888e1c6ff140af79987a40008548b7cc5f";
const npmCli = process.env.npm_execpath;
if (!npmCli) throw new Error("Run this command through npm run test:conformance");
const flags = process.argv.slice(2);
if (
  flags.length > 1 ||
  flags.some((flag) => !["--production", "--fixtures", "--raw"].includes(flag))
) {
  throw new Error("Usage: npm run test:conformance -- [--production|--fixtures|--raw]");
}
const raw = flags[0] === "--raw";
const mode =
  flags[0] === "--production" ? "production" : flags[0] === "--fixtures" ? "fixtures" : "audit";
let productionScenarios = [];
const productionSelection = {};
const sessionScenarios = ["server-session-lifecycle", "server-sse-multiple-streams"];
const scratch = await mkdtemp(path.join(tmpdir(), "tlaplus-conformance-"));
const suite = path.join(scratch, "suite");
const workingDir = path.join(scratch, "workspace");
const kbDir = path.join(scratch, "knowledge");
await mkdir(workingDir);
await mkdir(kbDir);
await writeFile(
  path.join(kbDir, ".production-conformance-fixture"),
  "Temporary production conformance inputs\n",
);
await writeFile(
  path.join(workingDir, "Counter.tla"),
  "---- MODULE Counter ----\nEXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == x' = 1 - x\n====\n",
);
await writeFile(path.join(workingDir, "Counter.cfg"), "INIT Init\nNEXT Next\n");
await writeFile(
  path.join(kbDir, "production-check.md"),
  "---\ntitle: Production check\ndescription: Temporary conformance article\n---\nProduction conformance article.\n",
);
const results = path.join(repo, "conformance-results");
await mkdir(results, { recursive: true });
await writeFile(path.join(kbDir, "production-123.md"), "# Production input 123\nParameter 123.\n");

function run(command, args, cwd = repo, timeoutMs) {
  return new Promise((resolve, reject) => {
    const child = spawn(command, args, { cwd, stdio: "inherit" });
    const timer = timeoutMs
      ? setTimeout(() => {
          child.kill("SIGKILL");
          reject(new Error(`${command} timed out after ${timeoutMs}ms`));
        }, timeoutMs)
      : undefined;
    child.once("error", (error) => {
      clearTimeout(timer);
      reject(error);
    });
    child.once("exit", (code, signal) => {
      clearTimeout(timer);
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
  await run(process.execPath, [path.join(repo, "scripts/conformance-bindings.mjs"), "--self-test"]);
  await run(process.execPath, [
    path.join(repo, "scripts/test-production-protocol.mjs"),
    "--self-test",
  ]);
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
  const helper = path.join(suite, "src/connection/sdk-client.ts");
  const helperSource = await readFile(helper, "utf8");
  const hash = (source) => createHash("sha256").update(source).digest("hex");
  if (hash(helperSource) !== "96d8b4efc028ce056b784f846b2dbe1c8872e38d11797330727ee54de2bdea6d")
    throw new Error("Pinned helper changed");
  const scenarioFiles = (await readdir(path.join(suite, "src/scenarios/server"))).filter((file) =>
    file.endsWith(".ts"),
  );
  const fingerprints = Object.fromEntries(
    await Promise.all(
      scenarioFiles.map(async (file) => [
        file,
        hash(await readFile(path.join(suite, "src/scenarios/server", file))),
      ]),
    ),
  );
  await writeFile(
    helper,
    `import { bindOptions, bindClient } from ${JSON.stringify(pathToFileURL(path.join(repo, "scripts/conformance-bindings.mjs")).href)};\n` +
      helperSource
        .replace(
          "  const client = new Client(opts.clientInfo",
          "  opts = bindOptions(opts);\n  const client = new Client(opts.clientInfo",
        )
        .replace(
          "  await client.connect(transport);",
          "  await client.connect(transport);\n  await bindClient(client);",
        ),
  );
  for (const file of scenarioFiles)
    if (hash(await readFile(path.join(suite, "src/scenarios/server", file))) !== fingerprints[file])
      throw new Error(`Original scenario modified: ${file}`);
  await writeFile(
    path.join(results, "original-scenario-fingerprints.json"),
    JSON.stringify(fingerprints, null, 2),
  );
  productionScenarios = JSON.parse(
    execFileSync(
      process.execPath,
      [
        tsx,
        "--eval",
        `import { listActiveClientScenarios, getClientScenario } from './src/scenarios/index.ts';
        (async () => {
          const checks = await getClientScenario('tools-call-image').run({ connect: async () => ({ request: async () => ({ content: [{ type: 'text', text: 'No image' }] }), close: async () => {} }) });
          if (!checks.some((check) => check.status === 'FAILURE' && check.errorMessage?.includes('No image content found'))) throw new Error('Original image assertion negative control failed');
          console.log(JSON.stringify(listActiveClientScenarios()));
        })()`,
      ],
      { cwd: suite, encoding: "utf8" },
    ),
  );
  const bindingScenarios = new Set([
    "completion-complete",
    "tools-call-simple-text",
    "tools-call-image",
    "tools-call-audio",
    "tools-call-embedded-resource",
    "tools-call-mixed-content",
    "tools-call-with-logging",
    "tools-call-error",
    "tools-call-with-progress",
    "tools-call-sampling",
    "tools-call-elicitation",
    "resources-read-text",
    "resources-read-binary",
    "resources-templates-read",
    "resources-subscribe",
    "resources-unsubscribe",
    "prompts-get-simple",
    "prompts-get-with-args",
    "prompts-get-embedded-resource",
    "prompts-get-with-image",
  ]);
  const baseline = path.join(
    repo,
    `src/__tests__/fixtures/conformance-${raw ? "raw-" : ""}baseline.yml`,
  );
  const sessionBaseline = path.join(scratch, "session-baseline.yml");
  await writeFile(
    sessionBaseline,
    (await readFile(baseline, "utf8"))
      .split("\n")
      .filter(
        (line) =>
          !line.includes("server-sse-multiple-streams-session") &&
          (raw ||
            ![
              "tools-call-sampling",
              "tools-call-elicitation",
              "resources-read-binary",
              "resources-subscribe",
              "resources-unsubscribe",
            ].some((name) => line.trim() === `- ${name}`)),
      )
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
      name === "fixtures"
        ? []
        : [
            ...(name === "application-sessions" ? ["--http-session"] : []),
            "--working-dir",
            workingDir,
            "--kb-dir",
            kbDir,
            "--tools-dir",
            path.join(repo, "tools"),
          ],
    );
    try {
      const unsupported = [
        "elicitation-sep1034-defaults",
        "elicitation-sep1330-enums",
        ...(name === "application"
          ? [
              "tools-call-sampling",
              "tools-call-elicitation",
              "resources-read-binary",
              "resources-subscribe",
              "resources-unsubscribe",
              ...sessionScenarios,
            ]
          : []),
      ];
      const scenarios =
        mode === "production"
          ? productionScenarios.filter((scenario) => !unsupported.includes(scenario))
          : [undefined];
      if (mode === "production")
        productionSelection[name] = { included: scenarios, excluded: unsupported };
      for (const scenario of scenarios) {
        const outputDir = path.join(
          results,
          raw ? `${name}-raw` : mode === "production" ? `${name}-selected` : name,
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
        if (!raw && name !== "fixtures") {
          process.env.TLAPLUS_BINDINGS_REPORT = path.join(outputDir, "bindings.jsonl");
          process.env.TLAPLUS_BINDINGS_WORKSPACE = workingDir;
          await writeFile(process.env.TLAPLUS_BINDINGS_REPORT, "");
        }
        try {
          await run(process.execPath, args, suite);
        } finally {
          delete process.env.TLAPLUS_BINDINGS_REPORT;
          delete process.env.TLAPLUS_BINDINGS_WORKSPACE;
        }
        if (mode === "production") {
          if (bindingScenarios.has(scenario)) {
            const bindings = (await readFile(path.join(outputDir, "bindings.jsonl"), "utf8"))
              .trim()
              .split("\n")
              .filter(Boolean)
              .map((line) => JSON.parse(line));
            if (!bindings.some((binding) => binding.kind === "request"))
              throw new Error(`No production binding exercised: ${scenario}`);
          }
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
      if (name !== "fixtures") {
        await run(
          process.execPath,
          [
            "--import",
            "tsx",
            path.join(repo, "scripts/test-production-protocol.mjs"),
            suite,
            url,
            name === "application-sessions" ? "sessions" : "stateless",
            workingDir,
            kbDir,
            path.join(results, `${name}-capabilities`),
          ],
          repo,
          120000,
        );
      }
    } finally {
      await stop(child);
    }
  }
  const changedSuiteFiles = execFileSync("git", ["diff", "--name-only"], {
    cwd: suite,
    encoding: "utf8",
  })
    .trim()
    .split("\n");
  if (JSON.stringify(changedSuiteFiles) !== JSON.stringify(["src/connection/sdk-client.ts"]))
    throw new Error(`Unexpected upstream edits: ${changedSuiteFiles}`);
  await writeFile(
    path.join(results, "metadata.json"),
    JSON.stringify(
      {
        suiteRef: ref,
        mode,
        raw,
        scenarioAssertions:
          "Original scenario files verified unchanged; SHA-256 fingerprints saved separately",
        bindings:
          "Only outgoing request inputs and general elicitation acceptance inputs are adapted; all real server responses remain unchanged",
        specVersion: "2025-11-25",
        ...(mode === "production"
          ? {
              productionScenarios,
              productionSelection,
              sessionScenarios,
              coverage:
                "Original active upstream scenario assertions with request/input bindings to production APIs; fixture-specific schemas and unsupported transport capabilities excluded; complementary behavioral checks retained",
            }
          : {}),
        ...(mode === "audit"
          ? {
              applicationBaseline: raw
                ? "20 unbound prescribed fixture scenarios remain expected"
                : "Stateless: five unsupported features and two fixture-specific elicitation schemas remain expected",
              applicationSessions: raw
                ? "20 unbound prescribed fixture scenarios remain expected"
                : "Session mode: two fixture-specific elicitation schemas remain expected",
            }
          : {}),
        ...(mode !== "production" ? { fixtures: "Full active suite; no expected failures" } : {}),
        ...(mode !== "fixtures"
          ? {
              productionCapabilities:
                "Separate application-capabilities and application-sessions-capabilities reports map all 20 prescribed fixture failures to real production behavior or explicit unsupported capabilities; not official full-suite conformance",
            }
          : {}),
        packageVersion: JSON.parse(await readFile(path.join(repo, "package.json"), "utf8")).version,
      },
      null,
      2,
    ),
  );
  console.log(`Conformance reports: ${results}`);
  console.log(
    mode === "production"
      ? "Selected upstream scenarios and supported production capability checks passed. See separate unsupported capability results."
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
