import type { Express } from "express";
import { localhostHostValidation } from "@modelcontextprotocol/sdk/server/middleware/hostHeaderValidation.js";

export function applyHttpSecurity(app: Express): void {
  app.use(localhostHostValidation());
  app.use((req, res, next) => {
    const allowedOrigins = ["localhost", "127.0.0.1", "[::1]"].map(
      (host) => new URL(`http://${host}:${req.socket.localPort}`).origin,
    );
    if (req.headers.origin !== undefined && !allowedOrigins.includes(req.headers.origin)) {
      res.status(403).json({
        jsonrpc: "2.0",
        error: { code: -32000, message: "Invalid Origin header" },
        id: null,
      });
      return;
    }
    next();
  });
}
