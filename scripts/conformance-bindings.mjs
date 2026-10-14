import assert from "node:assert/strict";
import { appendFileSync, mkdtempSync, rmSync } from "node:fs";
import path from "node:path";
import { tmpdir } from "node:os";

const svg =
  '<svg xmlns="http://www.w3.org/2000/svg" width="64" height="32"><rect width="20" height="10" fill="red"/></svg>';
const prepare = "tlaplus_mcp_tlc_prepare_config";
const render = {
  name: "tlaplus_mcp_animation_render",
  arguments: { protocol: "mcp", useCase: "static", frameIndex: 0, svgContent: svg },
};
const article = "tlaplus://knowledge/production-check.md";
export function bindOptions(opts) {
  if (!process.env.TLAPLUS_BINDINGS_REPORT) return opts;
  return {
    ...opts,
    capabilities: {
      ...(opts.capabilities ?? { sampling: {}, elicitation: {} }),
      elicitation: { ...opts.capabilities?.elicitation, form: {} },
    },
  };
}
function record(value) {
  appendFileSync(process.env.TLAPLUS_BINDINGS_REPORT, JSON.stringify(value) + "\n");
}
export function mapRequest(request, workingDir) {
  const p = request.params ?? {};
  let mapped;
  if (request.method === "tools/call") {
    const args = p.arguments ?? {};
    const counter = { fileName: path.join(workingDir, "Counter.tla"), timeoutMs: 15000 };
    const tools = {
      test_simple_text: { name: prepare, arguments: {} },
      test_image_content: render,
      test_multiple_content_types: render,
      test_embedded_resource: render,
      test_audio_content: { name: "tlaplus_mcp_trace_audio", arguments: { values: [0, 1, 2] } },
      test_error_handling: { name: prepare, arguments: { init: "invalid identifier" } },
      test_tool_with_logging: { name: "tlaplus_mcp_tlc_check", arguments: counter },
      test_tool_with_progress: {
        name: "tlaplus_mcp_tlc_smoke",
        arguments: { ...counter, extraJavaOpts: ["-Dtlc2.TLC.progressInterval=1"] },
      },
      test_sampling: { name: prepare, arguments: { useSampling: true, specText: args.prompt } },
      test_elicitation: { name: prepare, arguments: { askUser: true } },
    };
    mapped = tools[p.name];
  } else if (request.method === "prompts/get") {
    mapped = {
      test_simple_prompt: { name: "tla-getting-started" },
      test_prompt_with_arguments: {
        name: "tla-check",
        arguments: { fileName: p.arguments?.arg1, cfgFile: p.arguments?.arg2 },
      },
      test_prompt_with_embedded_resource: { name: "tla-check" },
      test_prompt_with_image: { name: "tla-create-animations", arguments: { svgContent: svg } },
    }[p.name];
  } else if (
    request.method === "completion/complete" &&
    p.ref?.name === "test_prompt_with_arguments"
  ) {
    mapped = {
      ref: { ...p.ref, name: "tla-check" },
      argument: { ...p.argument, name: "fileName" },
    };
  } else if (request.method.startsWith("resources/")) {
    const uri = {
      "test://static-text": article,
      "test://watched-resource": article,
      "test://template/123/data": "tlaplus://knowledge/production-123.md",
    }[p.uri];
    if (uri) mapped = { uri };
  }
  return mapped ? { ...request, params: { ...p, ...mapped } } : request;
}
export async function bindClient(client) {
  if (!process.env.TLAPLUS_BINDINGS_REPORT) return;
  const original = client.request.bind(client);
  const tools = new Set((await client.listTools()).tools.map((tool) => tool.name));
  const handler = client.setRequestHandler.bind(client);
  let generalElicitation = false;
  client.setRequestHandler = (schema, callback) =>
    handler(schema, async (request, extra) => {
      const reply = await callback(request, extra);
      if (
        generalElicitation &&
        request.method === "elicitation/create" &&
        reply.action === "accept"
      ) {
        const adapted = {
          ...reply,
          content: { mode: "check", workers: 1, checkDeadlock: true, invariants: [] },
        };
        record({ kind: "client-answer-input", original: reply, actual: adapted });
        return adapted;
      }
      return reply;
    });
  client.request = async (request, schema, options) => {
    let actual = mapRequest(request, process.env.TLAPLUS_BINDINGS_WORKSPACE);
    if (request.method === "resources/read" && request.params.uri === "test://static-binary") {
      assert(tools.has(render.name), `Missing real tool ${render.name}`);
      const result = await client.callTool(render);
      assert.notEqual(result.isError, true, JSON.stringify(result));
      const resource = result.content.find((item) => item.type === "resource")?.resource;
      assert(resource?.uri, "Real renderer did not return a resource URI");
      actual = {
        ...request,
        params: { ...request.params, uri: resource.uri.replace("frame.svg", "frame.png") },
      };
    }
    const bound = actual !== request;
    if (bound && request.method === "tools/call")
      assert(tools.has(actual.params.name), `Missing real tool ${actual.params.name}`);
    if (bound)
      record({
        kind: "request",
        original: request,
        actual,
        ...(request.params?.uri === "test://template/123/data"
          ? {
              note: "The real parameter-123 article is also statically registered; this original assertion does not isolate template callback dispatch. The complementary driver exercises the skills template.",
            }
          : {}),
      });
    generalElicitation = request.params?.name === "test_elicitation";
    try {
      const result = await original(actual, schema, options);
      if (bound && request.method === "tools/call") {
        requireSuccessfulTool(result, request.params.name);
      }
      return result;
    } finally {
      generalElicitation = false;
    }
  };
}

export function requireSuccessfulTool(result, originalName) {
  if (originalName === "test_error_handling") {
    assert.equal(result.isError, true, "Deliberate invalid input must return a tool error");
    assert(
      result.content?.some((item) => item.type === "text" && item.text.length > 0),
      "Tool error must include nonempty text",
    );
    return;
  }
  assert.notEqual(result.isError, true, JSON.stringify(result));
  assert(result.content?.length, "Bound real tool returned no content");
}
async function selfTest() {
  const request = {
    method: "tools/call",
    params: {
      name: "test_tool_with_progress",
      arguments: {},
      _meta: { progressToken: "original-token" },
    },
  };
  const mapped = mapRequest(request, "/tmp/example");
  assert.equal(mapped.params.name, "tlaplus_mcp_tlc_smoke");
  assert.deepEqual(mapped.params._meta, request.params._meta);
  assert.equal(request.params.name, "test_tool_with_progress");
  assert.throws(() =>
    requireSuccessfulTool(
      { isError: true, content: [{ type: "text", text: "failure" }] },
      "test_image_content",
    ),
  );
  assert.throws(() => requireSuccessfulTool({ content: [] }, "test_simple_text"));
  assert.throws(() =>
    requireSuccessfulTool({ content: [{ type: "text", text: "success" }] }, "test_error_handling"),
  );
  const unknown = { method: "tools/call", params: { name: "test_unknown" } };
  assert.equal(mapRequest(unknown, "/tmp"), unknown);
  const args = mapRequest(
    {
      method: "prompts/get",
      params: {
        name: "test_prompt_with_arguments",
        arguments: { arg1: "testValue1", arg2: "testValue2" },
      },
    },
    "/tmp",
  );
  assert.deepEqual(args.params.arguments, { fileName: "testValue1", cfgFile: "testValue2" });
  const scratch = mkdtempSync(path.join(tmpdir(), "binding-self-test-"));
  process.env.TLAPLUS_BINDINGS_REPORT = path.join(scratch, "requests.jsonl");
  process.env.TLAPLUS_BINDINGS_WORKSPACE = scratch;
  try {
    const response = { content: [{ type: "text", text: "Actual tool response" }] };
    const requestOptions = { timeout: 1234 };
    let sent;
    const client = {
      listTools: async () => ({ tools: [{ name: prepare }] }),
      setRequestHandler() {},
      request: async (...args) => {
        sent = args;
        return response;
      },
    };
    await bindClient(client);
    const schema = {};
    const result = await client.request(
      { method: "tools/call", params: { name: "test_simple_text" } },
      schema,
      requestOptions,
    );
    assert.equal(result, response, "Server response must be returned verbatim");
    assert.equal(sent[1], schema);
    assert.equal(sent[2], requestOptions);
    await assert.rejects(
      client.request({ method: "tools/call", params: { name: "test_image_content" } }, schema),
      /Missing real tool/,
    );
  } finally {
    delete process.env.TLAPLUS_BINDINGS_REPORT;
    delete process.env.TLAPLUS_BINDINGS_WORKSPACE;
    rmSync(scratch, { recursive: true, force: true });
  }
  console.log("Original scenario binding self-tests passed");
}

if (process.argv.includes("--self-test"))
  selfTest().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
