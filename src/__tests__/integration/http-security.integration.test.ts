import { spawn, ChildProcess } from "child_process";
import * as http from "http";
import * as path from "path";

describe("HTTP MCP security boundary", () => {
  let child: ChildProcess;
  let port: number;

  beforeAll(async () => {
    child = spawn(
      process.execPath,
      ["--import", "tsx", path.resolve(__dirname, "../../index.ts"), "--http", "--port", "0"],
      { cwd: path.resolve(__dirname, "../../.."), stdio: ["ignore", "pipe", "pipe"] },
    );
    let output = "";
    child.stderr!.on("data", (chunk) => {
      output += chunk.toString();
    });
    await new Promise<void>((resolve, reject) => {
      const timer = setTimeout(
        () => reject(new Error(`Server startup timed out: ${output}`)),
        15000,
      );
      child.once("error", (error) => {
        clearTimeout(timer);
        reject(error);
      });
      child.once("exit", (code) => {
        clearTimeout(timer);
        reject(new Error(`Server exited: ${code}: ${output}`));
      });
      child.stdout!.on("data", (chunk) => {
        output += chunk.toString();
        const match = /listening at http:\/\/[^:]+:(\d+)\/mcp/.exec(output);
        if (match) {
          port = Number(match[1]);
          clearTimeout(timer);
          resolve();
        }
      });
    });
  }, 20000);

  afterAll(async () => {
    if (child?.pid && child.exitCode === null && child.signalCode === null) {
      await new Promise<void>((resolve) => {
        child.once("exit", () => resolve());
        child.kill();
      });
    }
  });

  function request(method: string, headers: http.OutgoingHttpHeaders = {}, body?: string) {
    return new Promise<{ status: number; body: string }>((resolve, reject) => {
      const req = http.request(
        {
          hostname: "127.0.0.1",
          port,
          path: "/mcp",
          method,
          headers: {
            Accept: "application/json, text/event-stream",
            "Content-Type": "application/json",
            ...headers,
          },
        },
        (res) => {
          let output = "";
          res.setEncoding("utf8");
          res.on("data", (chunk) => {
            output += chunk;
          });
          res.on("end", () => resolve({ status: res.statusCode!, body: output }));
        },
      );
      req.on("error", reject);
      req.end(
        body ??
          (method === "POST"
            ? JSON.stringify({
                jsonrpc: "2.0",
                id: 1,
                method: "initialize",
                params: {
                  protocolVersion: "2025-11-25",
                  capabilities: {},
                  clientInfo: { name: "security-test", version: "1.0" },
                },
              })
            : undefined),
      );
    });
  }

  it("allows a client without Origin", async () => {
    expect((await request("POST")).status).toBe(200);
  });

  it.each(["localhost", "127.0.0.1", "[::1]"])(
    "allows its own loopback Origin: %s",
    async (host) => {
      const result = await request("POST", {
        Host: `${host}:${port}`,
        Origin: `http://${host}:${port}`,
      });
      expect(result.status).toBe(200);
      expect(result.body).toContain("serverInfo");
    },
  );

  describe.each(["POST", "GET", "DELETE", "OPTIONS"])("%s", (method) => {
    it.each(["http://evil.example", "null", "http://localhost:1", "http://localhost.evil.example"])(
      "rejects a foreign Origin with a valid Host: %s",
      async (origin) => {
        expect((await request(method, { Origin: origin })).status).toBe(403);
      },
    );
    it("rejects a malicious Host even with a trusted Origin", async () => {
      expect(
        (await request(method, { Host: "evil.example", Origin: `http://localhost:${port}` }))
          .status,
      ).toBe(403);
    });
  });

  it("validates Origin before parsing a malformed body", async () => {
    expect((await request("POST", { Origin: "http://evil.example" }, "invalid JSON")).status).toBe(
      403,
    );
  });

  it("rejects a malicious Host without Origin", async () => {
    expect((await request("POST", { Host: "evil.example" })).status).toBe(403);
  });

  it("rejects duplicate Origins even when the first is trusted", async () => {
    expect(
      (await request("POST", { Origin: [`http://localhost:${port}`, "http://evil.example"] }))
        .status,
    ).toBe(403);
  });
});
