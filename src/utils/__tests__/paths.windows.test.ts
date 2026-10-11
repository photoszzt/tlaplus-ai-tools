import * as path from "path";

describe("Windows canonical path containment", () => {
  const originalPlatform = process.platform;
  const shortRoot = String.raw`C:\Users\RUNNER~1\AppData\Local\Temp\workspace`;
  const longRoot = String.raw`C:\Users\runneradmin\AppData\Local\Temp\workspace`;
  let resolvePath: typeof import("../paths").resolveAndValidatePath;

  beforeEach(() => {
    Object.defineProperty(process, "platform", { value: "win32", configurable: true });
    const legacy = jest.fn((file: string) => file);
    const native = jest.fn((file: string) => file.replace(shortRoot, longRoot));
    jest.doMock("fs", () => ({ realpathSync: Object.assign(legacy, { native }) }));
    jest.doMock("path", () => path.win32);
    jest.isolateModules(() => {
      resolvePath = require("../paths").resolveAndValidatePath;
    });
  });

  afterEach(() => {
    Object.defineProperty(process, "platform", { value: originalPlatform, configurable: true });
    jest.dontMock("fs");
    jest.dontMock("path");
    jest.resetModules();
  });

  it("accepts an async-canonicalized SVG inside a working directory using its 8.3 alias", () => {
    const file = path.win32.join(longRoot, "frame.svg");
    expect(resolvePath(file, shortRoot)).toBe(file);
  });

  it("continues to reject a file outside the canonical working directory", () => {
    const file = path.win32.join(`${longRoot}-outside`, "frame.svg");
    expect(() => resolvePath(file, shortRoot)).toThrow("Access denied");
  });
});
