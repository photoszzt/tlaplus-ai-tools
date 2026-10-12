#!/usr/bin/env node
import assert from "node:assert/strict";
import { readFile, writeFile, mkdir } from "node:fs/promises";
import path from "node:path";
import { pathToFileURL, fileURLToPath } from "node:url";
import {
  ElicitRequestSchema,
  CreateMessageRequestSchema,
  LoggingMessageNotificationSchema,
  ProgressNotificationSchema,
  ResourceUpdatedNotificationSchema,
} from "@modelcontextprotocol/sdk/types.js";

const version = "2025-11-25";
const svg =
  '<svg xmlns="http://www.w3.org/2000/svg" width="64" height="32"><rect width="20" height="10" fill="red"/></svg>';
const articleUri = "tlaplus://knowledge/production-check.md";
const article = (body) =>
  `---\ntitle: Production check\ndescription: Temporary conformance article\n---\n${body}\n`;
const pause = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
async function until(predicate, description) {
  const deadline = Date.now() + 5000;
  while (!(await predicate())) {
    assert(Date.now() < deadline, `Timed out waiting for ${description}`);
    await pause(25);
  }
}
function successful(result) {
  assert.notEqual(result.isError, true, JSON.stringify(result));
  assert(result.content?.length > 0, "Tool returned no content");
  return result;
}
function text(result) {
  successful(result);
  const content = result.content.find((item) => item.type === "text");
  assert(content?.text.length > 0, "Missing nonempty text content");
  return content.text;
}
function requireWireChecks(checks) {
  assert(
    checks.some(
      (check) =>
        check.id === "wire-schema-valid" &&
        check.status === "SUCCESS" &&
        check.details?.messagesValidated > 0,
    ),
    "Missing positive wire-schema evidence",
  );
  assert(
    checks.every((check) => check.status === "SUCCESS"),
    JSON.stringify(checks),
  );
}
function requireNotifications(events, predicate, label) {
  assert(events.some(predicate), `Missing ${label} notification before tool result`);
}

async function runDriver({ suite, url, mode, workingDir, kbDir, outputDir }) {
  assert(["stateless", "sessions"].includes(mode), "Invalid HTTP mode");
  assert.equal(
    await readFile(path.join(kbDir, ".production-conformance-fixture"), "utf8"),
    "Temporary production conformance inputs\n",
    "Only the runner-owned temporary knowledge directory may be modified",
  );
  const { connectToServer } = await import(
    pathToFileURL(path.join(suite, "src/connection/sdk-client.ts"))
  );
  const { withWireRecorder, wireSchemaChecks } = await import(
    pathToFileURL(path.join(suite, "src/validation/wire-schema.ts"))
  );
  const persistent = mode === "sessions";
  const prepare = (client, args = {}) =>
    client.callTool({ name: "tlaplus_mcp_tlc_prepare_config", arguments: args });
  const render = async (client) => {
    const result = successful(
      await client.callTool({
        name: "tlaplus_mcp_animation_render",
        arguments: { protocol: "mcp", useCase: "static", frameIndex: 0, svgContent: svg },
      }),
    );
    const image = result.content.find((item) => item.type === "image");
    assert.equal(image?.mimeType, "image/png");
    const png = Buffer.from(image.data, "base64");
    assert.deepEqual([...png.subarray(0, 8)], [137, 80, 78, 71, 13, 10, 26, 10]);
    assert.deepEqual([png.readUInt32BE(16), png.readUInt32BE(20)], [64, 32]);
    const embedded = result.content.find((item) => item.type === "resource");
    assert.equal(embedded?.resource.mimeType, "image/svg+xml");
    assert.match(embedded.resource.text, /<rect/);
    assert(text(result).length > 0);
    return { image, embedded };
  };
  const elicit = async (client, kind) => {
    let observed = 0;
    client.setRequestHandler(ElicitRequestSchema, async ({ params }) => {
      observed++;
      assert.equal(params.mode, "form");
      const fields = params.requestedSchema.properties;
      if (kind === "defaults") {
        assert.equal(fields.mode.default, "check");
        assert.equal(fields.workers.default, 1);
        assert.equal(fields.checkDeadlock.default, true);
        assert.deepEqual(fields.invariants.default, ["TypeOK", "Safety"]);
      }
      if (kind === "enums") {
        assert.deepEqual(fields.mode.oneOf, [
          { const: "check", title: "Exhaustive check" },
          { const: "simulate", title: "Random simulation" },
          { const: "explore", title: "Explore a trace" },
        ]);
        assert.deepEqual(fields.invariants.items.anyOf, [
          { const: "TypeOK", title: "TypeOK" },
          { const: "Safety", title: "Safety" },
        ]);
      }
      return {
        action: "accept",
        content: { mode: "simulate", workers: 2, checkDeadlock: false, invariants: ["Safety"] },
      };
    });
    const result = JSON.parse(
      text(await prepare(client, { askUser: true, invariants: ["TypeOK", "Safety"] })),
    );
    assert.equal(observed, 1);
    assert.equal(result.mode, "simulate");
    assert.equal(result.workers, 2);
    assert.equal(result.config, "INIT Init\nNEXT Next\nINVARIANT Safety\nCHECK_DEADLOCK FALSE\n");
  };
  const notifications = async (client, checkLogging) => {
    const logs = [];
    const progress = [];
    let completed = false;
    client.setNotificationHandler(LoggingMessageNotificationSchema, ({ params }) =>
      logs.push({ ...params, beforeResult: !completed }),
    );
    client.setNotificationHandler(ProgressNotificationSchema, ({ params }) =>
      progress.push({ ...params, beforeResult: !completed }),
    );
    await client.setLoggingLevel("info");
    const result = await client.callTool({
      name: "tlaplus_mcp_tlc_smoke",
      arguments: {
        fileName: path.join(workingDir, "Counter.tla"),
        timeoutMs: 15000,
        extraJavaOpts: ["-Dtlc2.TLC.progressInterval=1"],
      },
      _meta: { progressToken: 0 },
    });
    completed = true;
    successful(result);
    requireNotifications(
      progress,
      (event) =>
        event.beforeResult &&
        event.progressToken === 0 &&
        String(event.message).includes("states generated"),
      "TLC progress",
    );
    for (let i = 1; i < progress.length; i++)
      assert(progress[i].progress > progress[i - 1].progress);
    if (checkLogging) {
      requireNotifications(
        logs,
        (event) => event.beforeResult && event.level === "info",
        "info logging",
      );
      logs.length = 0;
      await client.setLoggingLevel("error");
      successful(
        await client.callTool({
          name: "tlaplus_mcp_tlc_check",
          arguments: { fileName: path.join(workingDir, "Counter.tla"), timeoutMs: 15000 },
        }),
      );
      assert.equal(logs.length, 0, "Error logging level must suppress informational logs");
    }
  };
  const subscription = async (client, unsubscribe) => {
    const updates = [];
    client.setNotificationHandler(ResourceUpdatedNotificationSchema, ({ params }) =>
      updates.push(params.uri),
    );
    await client.subscribeResource({ uri: articleUri });
    const marker = `Subscribed ${Date.now()}`;
    await writeFile(path.join(kbDir, "production-check.md"), article(marker));
    await until(() => updates.includes(articleUri), "subscribed article update");
    assert.match(
      (await client.readResource({ uri: articleUri })).contents[0].text,
      new RegExp(marker),
    );
    await client.unsubscribeResource({ uri: articleUri });
    if (unsubscribe) {
      updates.length = 0;
      const nextMarker = `Unsubscribed ${Date.now()}`;
      await writeFile(path.join(kbDir, "production-check.md"), article(nextMarker));
      await until(
        async () =>
          (await client.readResource({ uri: articleUri })).contents[0].text.includes(nextMarker),
        "catalog to process unsubscribed edit",
      );
      await pause(200);
      assert.equal(updates.length, 0, "Unsubscribed resource emitted an update");
    }
  };
  const sessionOnly = (run, reason) => (persistent ? { run } : { unsupportedReason: reason });
  const cases = [
    {
      scenario: "completion-complete",
      run: async (client) => {
        assert.deepEqual(
          (
            await client.complete({
              ref: { type: "ref/prompt", name: "tla-check" },
              argument: { name: "fileName", value: "Count" },
            })
          ).completion.values,
          ["Counter.tla"],
        );
      },
    },
    ...["tools-call-image", "tools-call-embedded-resource", "tools-call-mixed-content"].map(
      (scenario) => ({ scenario, run: render }),
    ),
    {
      scenario: "tools-call-audio",
      run: async (client) => {
        const result = await client.callTool({
          name: "tlaplus_mcp_trace_audio",
          arguments: { values: [0, 1, 2] },
        });
        assert(!result.isError);
        const audio = result.content.find((block) => block.type === "audio");
        assert.equal(audio?.mimeType, "audio/wav");
        const wav = Buffer.from(audio.data, "base64");
        assert.equal(wav.toString("ascii", 0, 4), "RIFF");
        assert.equal(wav.toString("ascii", 8, 12), "WAVE");
        assert.equal(wav.length, 7244);
        assert.equal(wav.readUInt32LE(24), 8000);
        assert(wav.subarray(44).some((byte) => byte !== 0));
      },
    },
    { scenario: "tools-call-with-logging", run: (client) => notifications(client, true) },
    { scenario: "tools-call-with-progress", run: (client) => notifications(client, false) },
    {
      scenario: "tools-call-sampling",
      ...sessionOnly(async (client) => {
        let observed = 0;
        client.setRequestHandler(CreateMessageRequestSchema, async ({ params }) => {
          observed++;
          assert.equal(params.includeContext, "none");
          assert.deepEqual(params.messages, [
            { role: "user", content: { type: "text", text: "Explicit specification input" } },
          ]);
          return {
            role: "assistant",
            content: { type: "text", text: "Bound x to 3; unverified" },
            model: "conformance-client",
          };
        });
        const result = JSON.parse(
          text(
            await prepare(client, { useSampling: true, specText: "Explicit specification input" }),
          ),
        );
        assert.equal(observed, 1);
        assert.equal(result.unverifiedSuggestion, "Bound x to 3; unverified");
      }, "Stateless HTTP does not retain client sampling capabilities."),
    },
    ...[
      ["tools-call-elicitation", "basic"],
      ["elicitation-sep1034-defaults", "defaults"],
      ["elicitation-sep1330-enums", "enums"],
    ].map(([scenario, kind]) => ({
      scenario,
      ...sessionOnly(
        (client) => elicit(client, kind),
        "Stateless HTTP does not retain client elicitation capabilities.",
      ),
    })),
    {
      scenario: "resources-read-text",
      run: async (client) => {
        const resource = (await client.readResource({ uri: articleUri })).contents[0];
        assert.equal(resource.mimeType, "text/markdown");
        assert.equal(resource.text.trim(), "Production conformance article.");
        assert(!resource.text.includes("description: Temporary"));
      },
    },
    {
      scenario: "resources-read-binary",
      ...sessionOnly(async (client) => {
        const { image, embedded } = await render(client);
        const resource = (
          await client.readResource({
            uri: embedded.resource.uri.replace("frame.svg", "frame.png"),
          })
        ).contents[0];
        assert.equal(resource.mimeType, "image/png");
        assert.equal(resource.blob, image.data);
      }, "Stateless HTTP does not retain rendered frame resources between requests."),
    },
    {
      scenario: "resources-templates-read",
      run: async (client) => {
        assert(
          (await client.listResourceTemplates()).resourceTemplates.some(
            (item) => item.uriTemplate === "tlaplus://skills/{skill}",
          ),
        );
        const result = (await client.readResource({ uri: "tlaplus://skills/tla-check" }))
          .contents[0];
        assert.equal(result.mimeType, "text/markdown");
        assert.match(result.text, /tlaplus_mcp_tlc_check/);
      },
    },
    ...[
      ["resources-subscribe", false],
      ["resources-unsubscribe", true],
    ].map(([scenario, unsubscribe]) => ({
      scenario,
      ...sessionOnly(
        (client) => subscription(client, unsubscribe),
        "Stateless HTTP has no persistent resource subscriptions.",
      ),
    })),
    ...["prompts-get-simple", "prompts-get-with-args", "prompts-get-embedded-resource"].map(
      (scenario) => ({
        scenario,
        run: async (client) => {
          const name = scenario === "prompts-get-simple" ? "tla-getting-started" : "tla-check";
          const result = await client.getPrompt({
            name,
            ...(scenario === "prompts-get-with-args"
              ? { arguments: { fileName: "Counter.tla", cfgFile: "Counter.cfg" } }
              : {}),
          });
          const embedded = result.messages.find((message) => message.content.type === "resource")
            ?.content.resource;
          assert.equal(embedded?.uri, `tlaplus://skills/${name}`);
          assert(embedded.text.length > 100);
          if (name === "tla-check") assert.match(embedded.text, /tlaplus_mcp_tlc_check/);
          const message = result.messages.find((message) => message.content.type === "text")
            ?.content.text;
          assert(message?.length > 0);
          if (scenario === "prompts-get-with-args") {
            assert.match(message, /Specification: "Counter.tla"/);
            assert.match(message, /Configuration: "Counter.cfg"/);
          }
        },
      }),
    ),
    {
      scenario: "prompts-get-with-image",
      run: async (client) => {
        const result = await client.getPrompt({
          name: "tla-create-animations",
          arguments: {
            svgContent:
              '<svg width="32" height="24"><rect width="32" height="24" fill="red"/></svg>',
          },
        });
        const image = result.messages.find((message) => message.content.type === "image")?.content;
        assert.equal(image?.mimeType, "image/png");
        const png = Buffer.from(image.data, "base64");
        assert.equal(png.subarray(0, 8).toString("hex"), "89504e470d0a1a0a");
        assert.equal(png.readUInt32BE(16), 32);
        assert.equal(png.readUInt32BE(20), 24);
      },
    },
    {
      scenario: "production-tools-call-text",
      run: async (client) => {
        const result = JSON.parse(text(await prepare(client)));
        assert.equal(result.status, "draft");
        assert.equal(result.config, "INIT Init\nNEXT Next\nCHECK_DEADLOCK TRUE\n");
      },
    },
    {
      scenario: "production-tools-call-error",
      run: async (client) => {
        const result = await prepare(client, { init: "invalid name" });
        assert.equal(result.isError, true);
        assert(
          result.content.some(
            (item) => item.type === "text" && /invalid|validation/i.test(item.text),
          ),
        );
      },
    },
  ];
  const baseline = await readFile(
    new URL("../src/__tests__/fixtures/conformance-baseline.yml", import.meta.url),
    "utf8",
  );
  const identifiers = [...baseline.matchAll(/^  - ([^:\n]+)$/gm)].map((match) => match[1]);
  assert.equal(identifiers.length, 20);
  assert.deepEqual(
    cases
      .filter((entry) => !entry.scenario.startsWith("production-"))
      .map((entry) => entry.scenario)
      .sort(),
    identifiers.sort(),
  );
  const unsupported = cases
    .filter((entry) => entry.unsupportedReason)
    .map((entry) => entry.scenario)
    .sort();
  const expectedUnsupported = (
    !persistent
      ? [
          "tools-call-sampling",
          "tools-call-elicitation",
          "elicitation-sep1034-defaults",
          "elicitation-sep1330-enums",
          "resources-read-binary",
          "resources-subscribe",
          "resources-unsubscribe",
        ]
      : []
  ).sort();
  assert.deepEqual(
    unsupported,
    expectedUnsupported,
    "Supported production cases must not silently become unsupported",
  );
  const results = [];
  for (const entry of cases) {
    if (entry.unsupportedReason) {
      results.push({
        scenario: entry.scenario,
        status: "UNSUPPORTED",
        reason: entry.unsupportedReason,
      });
      continue;
    }
    const result = await withWireRecorder(async () => {
      let connection;
      let error;
      let timer;
      try {
        connection = await connectToServer(
          url,
          { capabilities: { sampling: {}, elicitation: { form: {} } } },
          version,
        );
        await Promise.race([
          entry.run(connection.client),
          new Promise((_, reject) => {
            timer = setTimeout(() => reject(new Error(`Case timed out: ${entry.scenario}`)), 30000);
          }),
        ]);
      } catch (caught) {
        error = caught;
      } finally {
        clearTimeout(timer);
        if (connection) await connection.close();
      }
      const checks = wireSchemaChecks(version);
      try {
        requireWireChecks(checks);
      } catch (caught) {
        error ??= caught;
      }
      return {
        scenario: entry.scenario,
        status: error ? "FAILURE" : "SUCCESS",
        ...(error ? { error: String(error.stack ?? error) } : {}),
        checks,
      };
    });
    results.push(result);
    console.log(`${mode}: ${entry.scenario}: ${result.status}`);
    if (result.error) console.error(result.error);
  }
  await mkdir(outputDir, { recursive: true });
  await writeFile(
    path.join(outputDir, "production-capabilities.json"),
    JSON.stringify(
      {
        specVersion: version,
        mode,
        coverage:
          "Production API behavior validated with upstream wire schemas; not the official fixture suite",
        results,
      },
      null,
      2,
    ),
  );
  assert(
    results.every((result) => result.status !== "FAILURE"),
    "Production capability checks failed",
  );
}

if (process.argv[2] === "--self-test") {
  assert.throws(() =>
    successful({ isError: true, content: [{ type: "text", text: "Unknown tool" }] }),
  );
  assert.throws(() => successful({ content: [] }));
  assert.throws(() => requireWireChecks([]));
  assert.throws(() =>
    requireWireChecks([
      { id: "wire-schema-valid", status: "SUCCESS", details: { messagesValidated: 0 } },
    ]),
  );
  assert.throws(() =>
    requireWireChecks([
      { id: "wire-schema-valid", status: "SUCCESS", details: { messagesValidated: 1 } },
      { id: "wire-schema-harness-error", status: "FAILURE" },
    ]),
  );
  assert.throws(() => requireNotifications([], () => true, "progress"));
  assert.throws(() =>
    requireNotifications([{ beforeResult: false }], (event) => event.beforeResult, "progress"),
  );
  requireWireChecks([
    { id: "wire-schema-valid", status: "SUCCESS", details: { messagesValidated: 1 } },
  ]);
  console.log("Production driver negative checks passed");
} else {
  const [suite, url, mode, workingDir, kbDir, outputDir] = process.argv.slice(2);
  assert(
    suite && url && mode && workingDir && kbDir && outputDir,
    `Usage: ${fileURLToPath(import.meta.url)} suite url stateless|sessions workingDir kbDir outputDir`,
  );
  await runDriver({ suite, url, mode, workingDir, kbDir, outputDir });
}
