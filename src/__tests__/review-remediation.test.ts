// Spec: docs/review-remediation/spec.md
// Testing: docs/review-remediation/testing.md
//
// White-box tests for the 11 Code Review Remediation requirements.

import * as fs from 'fs';
import * as path from 'path';
import { EventEmitter } from 'events';

// ---------------------------------------------------------------------------
// REQ-REVIEW-001: Shared Error Formatting Module
// ---------------------------------------------------------------------------

describe('REQ-REVIEW-001: Shared Error Formatting Module', () => {
  // @tests REQ-REVIEW-001, SCN-REVIEW-001-01
  it('getSuggestedActions returns non-default suggestions for all 7 error codes', () => {
    // Import directly from the shared module
    const { getSuggestedActions } = require('../tools/shared/error-formatting');
    const { ErrorCode } = require('../utils/errors');

    const codes = [
      ErrorCode.JAVA_NOT_FOUND,
      ErrorCode.CONFIG_TOOLS_NOT_FOUND,
      ErrorCode.FILE_NOT_FOUND,
      ErrorCode.JAR_LOCKED,
      ErrorCode.JAR_ENTRY_NOT_FOUND,
      ErrorCode.JAR_EXTRACTION_FAILED,
      ErrorCode.XMLEXPORTER_USAGE_ERROR,
    ];

    for (const code of codes) {
      const suggestions = getSuggestedActions(code);
      // Each known code should return specific suggestions (not the default)
      expect(suggestions).not.toEqual(['- Check error message for details']);
      expect(suggestions.length).toBeGreaterThanOrEqual(1);
    }
  });

  // @tests REQ-REVIEW-001, SCN-REVIEW-001-01
  it('XMLEXPORTER_USAGE_ERROR entry is present with correct suggestions', () => {
    const { getSuggestedActions } = require('../tools/shared/error-formatting');
    const { ErrorCode } = require('../utils/errors');

    const suggestions = getSuggestedActions(ErrorCode.XMLEXPORTER_USAGE_ERROR);
    expect(suggestions).toContain('- Run `npm run setup` to install pinned tools (v1.8.0)');
    expect(suggestions).toContain(
      '- Verify `tools/tla2tools.jar` matches v1.8.0 with correct checksum'
    );
    expect(suggestions).toContain(
      '- If checksum mismatch: delete `tools/tla2tools.jar` and re-run `npm run setup`'
    );
    expect(suggestions).toContain(
      '- This error indicates XMLExporter argument incompatibility with your TLA+ tools version'
    );
  });

  // @tests REQ-REVIEW-001, SCN-REVIEW-001-01
  it('formatErrorResponse produces structured output with error code', () => {
    const { formatErrorResponse } = require('../tools/shared/error-formatting');
    const { enhanceError, ErrorCode } = require('../utils/errors');

    const err = enhanceError(new Error('Java executable not found'), {
      code: ErrorCode.JAVA_NOT_FOUND,
    });

    const output = formatErrorResponse(err);
    expect(output).toContain('Error [JAVA_NOT_FOUND]');
    expect(output).toContain('Suggested Actions:');
    expect(output).toContain('Install Java 17 or later');
  });

  // @tests SCN-REVIEW-001-02
  it('sany.ts does NOT define formatErrorResponse locally', () => {
    const sanyPath = path.resolve(__dirname, '..', 'tools', 'sany.ts');
    const sanyContent = fs.readFileSync(sanyPath, 'utf-8');

    // No local function definition
    const localDefs = (sanyContent.match(/function formatErrorResponse/g) || []).length;
    expect(localDefs).toBe(0);

    // Imports from shared module
    expect(sanyContent).toContain("from './shared/error-formatting'");
  });

  // @tests SCN-REVIEW-001-03
  it('tlc.ts does NOT define formatErrorResponse locally', () => {
    const tlcPath = path.resolve(__dirname, '..', 'tools', 'tlc.ts');
    const tlcContent = fs.readFileSync(tlcPath, 'utf-8');

    const localDefs = (tlcContent.match(/function formatErrorResponse/g) || []).length;
    expect(localDefs).toBe(0);

    expect(tlcContent).toContain("from './shared/error-formatting'");
  });

  // @tests REQ-REVIEW-001
  it('getSuggestedActions returns default suggestion for unknown codes', () => {
    const { getSuggestedActions } = require('../tools/shared/error-formatting');
    const result = getSuggestedActions('TOTALLY_UNKNOWN_CODE');
    expect(result).toEqual(['- Check error message for details']);
  });
});

// ---------------------------------------------------------------------------
// REQ-REVIEW-002: Typed Server Parameter
// ---------------------------------------------------------------------------

describe('REQ-REVIEW-002: Typed Server Parameter', () => {
  // @tests REQ-REVIEW-002, SCN-REVIEW-002-01
  it('registerSanyTools uses McpServer type (source inspection)', () => {
    const sanyPath = path.resolve(__dirname, '..', 'tools', 'sany.ts');
    const content = fs.readFileSync(sanyPath, 'utf-8');
    // The function declaration spans multiple lines:
    //   export async function registerSanyTools(
    //     server: McpServer,
    // Verify server param is typed as McpServer (not any)
    expect(content).toContain('server: McpServer,');
    // No 'server: any' in the file
    expect(content).not.toContain('server: any');
  });

  // @tests REQ-REVIEW-002, SCN-REVIEW-002-01
  it('registerTlcTools uses McpServer type (source inspection)', () => {
    const tlcPath = path.resolve(__dirname, '..', 'tools', 'tlc.ts');
    const content = fs.readFileSync(tlcPath, 'utf-8');
    expect(content).toContain('server: McpServer,');
    expect(content).not.toContain('server: any');
  });

  // @tests REQ-REVIEW-002, SCN-REVIEW-002-01
  it('registerAnimationTools uses McpServer type (source inspection)', () => {
    const animPath = path.resolve(__dirname, '..', 'tools', 'animation.ts');
    const content = fs.readFileSync(animPath, 'utf-8');
    expect(content).toContain('server: McpServer,');
    expect(content).not.toContain('server: any');
  });
});

// ---------------------------------------------------------------------------
// REQ-REVIEW-003: Eliminate Busy-Wait in Retry Logic
// ---------------------------------------------------------------------------

describe('REQ-REVIEW-003: Async Conversion', () => {
  // @tests REQ-REVIEW-003, SCN-REVIEW-003-01
  it('extractJarEntry is async (returns Promise)', () => {
    const { extractJarEntry } = require('../utils/jarfile');
    // The function itself should be an AsyncFunction
    expect(extractJarEntry.constructor.name).toBe('AsyncFunction');
  });

  // @tests REQ-REVIEW-003, SCN-REVIEW-003-02
  it('extractJarDirectory is async (returns Promise)', () => {
    const { extractJarDirectory } = require('../utils/jarfile');
    expect(extractJarDirectory.constructor.name).toBe('AsyncFunction');
  });

  // @tests REQ-REVIEW-003, SCN-REVIEW-003-03
  it('resolveJarfilePath is async (returns Promise)', () => {
    const { resolveJarfilePath } = require('../utils/jarfile');
    expect(resolveJarfilePath.constructor.name).toBe('AsyncFunction');
  });

  // @tests REQ-REVIEW-003, SCN-REVIEW-003-01
  it('no busy-wait pattern exists in retry.ts', () => {
    const retryPath = path.resolve(__dirname, '..', 'utils', 'errors', 'retry.ts');
    const content = fs.readFileSync(retryPath, 'utf-8');
    // No while(Date.now()...) busy-wait pattern
    expect(content).not.toMatch(/while\s*\(\s*Date\.now\(\)/);
  });

  // @tests REQ-REVIEW-003
  it('withRetrySync no longer exists in the codebase', () => {
    const retryPath = path.resolve(__dirname, '..', 'utils', 'errors', 'retry.ts');
    const content = fs.readFileSync(retryPath, 'utf-8');
    expect(content).not.toContain('withRetrySync');
  });

  // @tests INV-REVIEW-005
  it('sany.ts awaits resolveJarfilePath calls', () => {
    const sanyPath = path.resolve(__dirname, '..', 'tools', 'sany.ts');
    const content = fs.readFileSync(sanyPath, 'utf-8');
    // Every usage of resolveJarfilePath should be preceded by 'await'
    const callSites = content.match(/resolveJarfilePath\(/g) || [];
    const awaitedCallSites = content.match(/await\s+resolveJarfilePath\(/g) || [];
    expect(callSites.length).toBeGreaterThan(0);
    expect(awaitedCallSites.length).toBe(callSites.length);
  });
});

// ---------------------------------------------------------------------------
// REQ-REVIEW-004: Bounded JAR Extraction Cache with LRU Eviction
// ---------------------------------------------------------------------------

describe('REQ-REVIEW-004: LRU Cache', () => {
  // Use direct import of the exported class
  const { LRUCache, getMaxCacheSize } = require('../utils/jarfile');

  // @tests REQ-REVIEW-004, SCN-REVIEW-004-01
  // @tests-invariant INV-REVIEW-001
  it('evicts LRU entry when cache exceeds maxSize', () => {
    const cache = new LRUCache(3);
    cache.set('a', 'v1');
    cache.set('b', 'v2');
    cache.set('c', 'v3');

    // Cache is at capacity (3)
    expect(cache.size).toBe(3);

    // Adding one more should evict 'a' (oldest)
    cache.set('d', 'v4');
    expect(cache.size).toBe(3);
    expect(cache.get('a')).toBeUndefined();
    expect(cache.get('b')).toBe('v2');
    expect(cache.get('c')).toBe('v3');
    expect(cache.get('d')).toBe('v4');
  });

  // @tests REQ-REVIEW-004, SCN-REVIEW-004-01
  // @tests-invariant INV-REVIEW-001
  it('cache size never exceeds maxSize', () => {
    const cache = new LRUCache(5);
    for (let i = 0; i < 100; i++) {
      cache.set(i, `value-${i}`);
      expect(cache.size).toBeLessThanOrEqual(5);
    }
    expect(cache.size).toBe(5);
  });

  // @tests REQ-REVIEW-004, SCN-REVIEW-004-02
  it('getMaxCacheSize returns 256 by default', () => {
    const oldEnv = process.env.TLA_JAR_CACHE_SIZE;
    delete process.env.TLA_JAR_CACHE_SIZE;

    // Note: getMaxCacheSize reads the env at call time
    const size = getMaxCacheSize();
    expect(size).toBe(256);

    // Restore
    if (oldEnv !== undefined) process.env.TLA_JAR_CACHE_SIZE = oldEnv;
  });

  // @tests REQ-REVIEW-004, SCN-REVIEW-004-02
  it('getMaxCacheSize reads TLA_JAR_CACHE_SIZE env var', () => {
    const oldEnv = process.env.TLA_JAR_CACHE_SIZE;
    process.env.TLA_JAR_CACHE_SIZE = '128';

    const size = getMaxCacheSize();
    expect(size).toBe(128);

    // Restore
    if (oldEnv !== undefined) {
      process.env.TLA_JAR_CACHE_SIZE = oldEnv;
    } else {
      delete process.env.TLA_JAR_CACHE_SIZE;
    }
  });

  // @tests REQ-REVIEW-004, SCN-REVIEW-004-02
  it('getMaxCacheSize falls back to 256 for invalid env values', () => {
    const oldEnv = process.env.TLA_JAR_CACHE_SIZE;

    const invalidValues = ['abc', '-1', '0', '', 'NaN'];
    for (const val of invalidValues) {
      process.env.TLA_JAR_CACHE_SIZE = val;
      const size = getMaxCacheSize();
      expect(size).toBe(256);
    }

    if (oldEnv !== undefined) {
      process.env.TLA_JAR_CACHE_SIZE = oldEnv;
    } else {
      delete process.env.TLA_JAR_CACHE_SIZE;
    }
  });

  // @tests REQ-REVIEW-004, SCN-REVIEW-004-03
  it('accessing an entry updates its recency', () => {
    const cache = new LRUCache(3);
    cache.set('a', 'v1');
    cache.set('b', 'v2');
    cache.set('c', 'v3');

    // Access 'a', making it most recently used
    cache.get('a');

    // Now add 'd' - should evict 'b' (least recently used after 'a' was accessed)
    cache.set('d', 'v4');

    expect(cache.get('a')).toBe('v1'); // Kept (was accessed)
    expect(cache.get('b')).toBeUndefined(); // Evicted (LRU)
    expect(cache.get('c')).toBe('v3'); // Kept
    expect(cache.get('d')).toBe('v4'); // Newly added
  });

  // @tests REQ-REVIEW-004, SCN-REVIEW-004-04
  it('logs eviction at debug level when DEBUG or VERBOSE is set', () => {
    const debugSpy = jest.spyOn(console, 'debug').mockImplementation(() => {});
    const oldDebug = process.env.DEBUG;
    process.env.DEBUG = '1';

    const cache = new LRUCache(2);
    cache.set('a', 'v1');
    cache.set('b', 'v2');
    cache.set('c', 'v3'); // Triggers eviction of 'a'

    expect(debugSpy).toHaveBeenCalledWith(
      expect.stringContaining('JAR cache eviction')
    );
    expect(debugSpy).toHaveBeenCalledWith(
      expect.stringContaining('removing entry a')
    );

    debugSpy.mockRestore();
    if (oldDebug !== undefined) {
      process.env.DEBUG = oldDebug;
    } else {
      delete process.env.DEBUG;
    }
  });

  // @tests REQ-REVIEW-004, SCN-REVIEW-004-05
  it('calls onEvict callback when entry is evicted', () => {
    const onEvict = jest.fn();
    const cache = new LRUCache(2, onEvict);

    cache.set('a', '/tmp/path-a');
    cache.set('b', '/tmp/path-b');
    cache.set('c', '/tmp/path-c'); // Triggers eviction of 'a'

    expect(onEvict).toHaveBeenCalledTimes(1);
    expect(onEvict).toHaveBeenCalledWith('a', '/tmp/path-a');
  });

  // @tests REQ-REVIEW-004, SCN-REVIEW-004-05
  it('onEvict callback receives evicted key and value', () => {
    const evictions: Array<{ key: string; value: string }> = [];
    const cache = new LRUCache(2, (key: string, value: string) => {
      evictions.push({ key, value });
    });

    cache.set('x', '/tmp/x');
    cache.set('y', '/tmp/y');
    cache.set('z', '/tmp/z'); // Evicts 'x'
    cache.set('w', '/tmp/w'); // Evicts 'y'

    expect(evictions).toEqual([
      { key: 'x', value: '/tmp/x' },
      { key: 'y', value: '/tmp/y' },
    ]);
  });

  // @tests REQ-REVIEW-004 (boundary: single-entry cache)
  it('works correctly with maxSize=1', () => {
    const cache = new LRUCache(1);
    cache.set('a', 'v1');
    expect(cache.size).toBe(1);
    expect(cache.get('a')).toBe('v1');

    cache.set('b', 'v2');
    expect(cache.size).toBe(1);
    expect(cache.get('a')).toBeUndefined();
    expect(cache.get('b')).toBe('v2');
  });

  // @tests REQ-REVIEW-004 (boundary: updating existing key does not evict)
  it('updating an existing key does not increase size', () => {
    const cache = new LRUCache(3);
    cache.set('a', 'v1');
    cache.set('b', 'v2');
    cache.set('c', 'v3');

    cache.set('b', 'v2-updated');
    expect(cache.size).toBe(3);
    expect(cache.get('b')).toBe('v2-updated');
  });

  // @tests REQ-REVIEW-004 (clear operation)
  it('clear() empties the cache', () => {
    const cache = new LRUCache(10);
    cache.set('a', 'v1');
    cache.set('b', 'v2');
    expect(cache.size).toBe(2);

    cache.clear();
    expect(cache.size).toBe(0);
    expect(cache.get('a')).toBeUndefined();
  });

  // @tests REQ-REVIEW-004 (has operation)
  it('has() returns correct boolean', () => {
    const cache = new LRUCache(10);
    expect(cache.has('a')).toBe(false);
    cache.set('a', 'v1');
    expect(cache.has('a')).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// REQ-REVIEW-005: Single McpServer Instance for HTTP Lifecycle
// (KB caching tested via registerKnowledgeBaseFromCache)
// ---------------------------------------------------------------------------

describe('REQ-REVIEW-005: KB Caching', () => {
  beforeEach(() => {
    jest.resetModules();
  });

  // @tests REQ-REVIEW-005, SCN-REVIEW-005-01
  it('registerKnowledgeBaseFromCache registers resources without disk I/O', async () => {
    // Import knowledge module
    const { registerKnowledgeBaseFromCache } = require('../tools/knowledge');
    const { createMockMcpServer } = require('./helpers/mock-server');
    const mockServer = createMockMcpServer();

    const entries = [
      {
        fileName: 'intro.md',
        resourceUri: 'tlaplus://knowledge/intro.md',
        title: 'Introduction',
        description: 'Intro article',
        content: '---\ntitle: Introduction\n---\n# Hello\nWorld',
      },
      {
        fileName: 'advanced.md',
        resourceUri: 'tlaplus://knowledge/advanced.md',
        title: 'Advanced',
        description: 'Advanced article',
        content: '---\ntitle: Advanced\n---\n# Advanced\nContent',
      },
    ];

    await registerKnowledgeBaseFromCache(mockServer, entries);

    const resources = mockServer.getRegisteredResources();
    expect(resources.size).toBe(2);
    expect(resources.has('tlaplus://knowledge/intro.md')).toBe(true);
    expect(resources.has('tlaplus://knowledge/advanced.md')).toBe(true);
  });

  // @tests REQ-REVIEW-005, SCN-REVIEW-005-01
  it('registerKnowledgeBaseFromCache resource handler uses cached content', async () => {
    const { registerKnowledgeBaseFromCache } = require('../tools/knowledge');
    const { createMockMcpServer, callRegisteredResource } = require('./helpers/mock-server');

    jest.mock('../utils/markdown', () => ({
      parseMarkdownFrontmatter: jest.fn(() => ({ title: 'Test' })),
      removeMarkdownFrontmatter: jest.fn((content: string) => content.replace(/---[\s\S]*?---\n/, '')),
    }));

    const mockServer = createMockMcpServer();
    const entries = [
      {
        fileName: 'test.md',
        resourceUri: 'tlaplus://knowledge/test.md',
        title: 'Test',
        description: 'Test article',
        content: '---\ntitle: Test\n---\n# Content',
      },
    ];

    await registerKnowledgeBaseFromCache(mockServer, entries);
    const result = await callRegisteredResource(mockServer, 'tlaplus://knowledge/test.md');

    expect(result.contents).toHaveLength(1);
    expect(result.contents[0].uri).toBe('tlaplus://knowledge/test.md');
    expect(result.contents[0].mimeType).toBe('text/markdown');
  });

  // @tests REQ-REVIEW-005 (KnowledgeBaseEntry type exported)
  it('KnowledgeBaseEntry interface is exported from knowledge.ts', () => {
    const knowledgePath = path.resolve(__dirname, '..', 'tools', 'knowledge.ts');
    const content = fs.readFileSync(knowledgePath, 'utf-8');
    expect(content).toContain('export interface KnowledgeBaseEntry');
  });

  // @tests REQ-REVIEW-005, SCN-REVIEW-005-03
  it('KB startup failure logs warning and cachedKnowledgeBase remains null', async () => {
    // Isolate the module to get fresh mocks
    jest.resetModules();

    // Mock all dependencies that server.ts imports
    jest.mock('@modelcontextprotocol/sdk/server/mcp.js', () => ({
      McpServer: jest.fn().mockImplementation(() => ({
        connect: jest.fn().mockResolvedValue(undefined),
        close: jest.fn().mockResolvedValue(undefined),
        tool: jest.fn(),
        resource: jest.fn(),
      })),
    }));
    jest.mock('@modelcontextprotocol/sdk/server/stdio.js', () => ({
      StdioServerTransport: jest.fn(),
    }));
    jest.mock('@modelcontextprotocol/sdk/server/streamableHttp.js', () => ({
      StreamableHTTPServerTransport: jest.fn().mockImplementation(() => ({
        handleRequest: jest.fn().mockResolvedValue(undefined),
        close: jest.fn(),
      })),
    }));
    jest.mock('../tools/sany', () => ({ registerSanyTools: jest.fn().mockResolvedValue(undefined) }));
    jest.mock('../tools/tlc', () => ({ registerTlcTools: jest.fn().mockResolvedValue(undefined) }));
    jest.mock('../tools/knowledge', () => ({
      registerKnowledgeBaseResources: jest.fn().mockResolvedValue(undefined),
      registerKnowledgeBaseFromCache: jest.fn().mockResolvedValue(undefined),
    }));
    jest.mock('../tools/animation', () => ({ registerAnimationTools: jest.fn().mockResolvedValue(undefined) }));

    // Mock express to create a controllable HTTP server
    const mockHttpServer: Record<string, any> = {
      on: jest.fn(),
      removeListener: jest.fn(),
      address: jest.fn(() => ({ port: 3000 })),
    };
    mockHttpServer.listen = jest.fn((_port: number, callback: () => void) => {
      setImmediate(() => callback());
      return mockHttpServer;
    });
    const mockApp = {
      use: jest.fn(),
      post: jest.fn(),
      get: jest.fn(),
      delete: jest.fn(),
      listen: jest.fn((_port: number, callback: () => void) => {
        setImmediate(() => callback());
        return mockHttpServer;
      }),
    };
    jest.mock('express', () => {
      const fn = jest.fn(() => mockApp);
      (fn as any).json = jest.fn();
      return fn;
    });

    // Mock fs.promises.readdir to throw for the KB directory
    const readdirError = new Error('EACCES: permission denied');
    jest.spyOn(fs.promises, 'readdir').mockRejectedValue(readdirError);

    // Capture warnings from the logger (Logger.warn uses console.error)
    const consoleErrorSpy = jest.spyOn(console, 'error').mockImplementation(() => {});
    // Suppress console.log too (Logger.info in HTTP mode uses console.log)
    const consoleLogSpy = jest.spyOn(console, 'log').mockImplementation(() => {});

    const { TLAPlusMCPServer } = require('../server');
    const { registerKnowledgeBaseFromCache } = require('../tools/knowledge');

    const server = new TLAPlusMCPServer({
      toolsDir: '/mock/tools',
      workingDir: '/mock/work',
      kbDir: '/mock/kb',  // Configured, but readdir will fail
      javaHome: null,
      verbose: false,
      http: true,
      port: 3000,
    });

    await server.start();

    // Verify: warning was logged (Logger.warn always uses console.error)
    const errorOutput = consoleErrorSpy.mock.calls.map(c => String(c[0])).join(' ');
    expect(errorOutput).toContain('Failed to pre-load knowledge base');

    // Verify: cachedKnowledgeBase remains null -> registerKnowledgeBaseFromCache NOT called
    // (because if cachedKnowledgeBase is null, createMCPServer falls through to disk path)
    expect(registerKnowledgeBaseFromCache).not.toHaveBeenCalled();

    consoleErrorSpy.mockRestore();
    consoleLogSpy.mockRestore();
    jest.restoreAllMocks();
  });
});

// ---------------------------------------------------------------------------
// REQ-REVIEW-006: HTTP Error Handler Discrimination
// ---------------------------------------------------------------------------

describe('REQ-REVIEW-006: HTTP Error Handler', () => {
  // @tests REQ-REVIEW-006, SCN-REVIEW-006-01, SCN-REVIEW-006-02
  it('FATAL_ERROR_CODES contains the expected codes', () => {
    const serverPath = path.resolve(__dirname, '..', 'server.ts');
    const content = fs.readFileSync(serverPath, 'utf-8');

    // Verify the fatal codes are defined
    expect(content).toContain('EADDRINUSE');
    expect(content).toContain('EACCES');
    expect(content).toContain('ENOSPC');
    expect(content).toContain('EMFILE');
    expect(content).toContain('ENFILE');
  });

  // @tests REQ-REVIEW-006, SCN-REVIEW-006-01
  it('no duplicate server.on error handler exists after listen callback', () => {
    const serverPath = path.resolve(__dirname, '..', 'server.ts');
    const content = fs.readFileSync(serverPath, 'utf-8');

    // Verify the startupErrorHandler and operationalErrorHandler pattern
    expect(content).toContain('startupErrorHandler');
    expect(content).toContain('operationalErrorHandler');
    expect(content).toContain("httpServer.removeListener('error', startupErrorHandler)");
    expect(content).toContain("httpServer.on('error', operationalErrorHandler)");

    // No duplicate server.on('error') after the promise
    const afterPromise = content.split('// No duplicate server.on')[1] || '';
    expect(afterPromise).not.toContain("server.on('error'");
  });

  // @tests REQ-REVIEW-006, SCN-REVIEW-006-01
  it('startup error handler rejects the promise instead of process.exit', () => {
    const serverPath = path.resolve(__dirname, '..', 'server.ts');
    const content = fs.readFileSync(serverPath, 'utf-8');

    // The startupErrorHandler calls reject(err)
    const startupSection = content.match(
      /const startupErrorHandler[\s\S]*?};/
    );
    expect(startupSection).not.toBeNull();
    expect(startupSection![0]).toContain('reject(err)');
    expect(startupSection![0]).not.toContain('process.exit');
  });

  // @tests REQ-REVIEW-006, SCN-REVIEW-006-02
  it('ECONNRESET (non-fatal) does NOT call process.exit', async () => {
    jest.resetModules();

    // Mock all server dependencies
    jest.mock('@modelcontextprotocol/sdk/server/mcp.js', () => ({
      McpServer: jest.fn().mockImplementation(() => ({
        connect: jest.fn().mockResolvedValue(undefined),
        close: jest.fn().mockResolvedValue(undefined),
        tool: jest.fn(),
        resource: jest.fn(),
      })),
    }));
    jest.mock('@modelcontextprotocol/sdk/server/stdio.js', () => ({
      StdioServerTransport: jest.fn(),
    }));
    jest.mock('@modelcontextprotocol/sdk/server/streamableHttp.js', () => ({
      StreamableHTTPServerTransport: jest.fn().mockImplementation(() => ({
        handleRequest: jest.fn().mockResolvedValue(undefined),
        close: jest.fn(),
      })),
    }));
    jest.mock('../tools/sany', () => ({ registerSanyTools: jest.fn().mockResolvedValue(undefined) }));
    jest.mock('../tools/tlc', () => ({ registerTlcTools: jest.fn().mockResolvedValue(undefined) }));
    jest.mock('../tools/knowledge', () => ({
      registerKnowledgeBaseResources: jest.fn().mockResolvedValue(undefined),
      registerKnowledgeBaseFromCache: jest.fn().mockResolvedValue(undefined),
    }));
    jest.mock('../tools/animation', () => ({ registerAnimationTools: jest.fn().mockResolvedValue(undefined) }));

    // Create an EventEmitter to simulate the HTTP server
    const mockHttpServer = new EventEmitter() as EventEmitter & {
      listen: jest.Mock;
      address: jest.Mock;
    };
    (mockHttpServer as any).listen = jest.fn((_port: number, callback: () => void) => {
      setImmediate(() => callback());
      return mockHttpServer;
    });
    (mockHttpServer as any).address = jest.fn(() => ({ port: 3000 }));

    const mockApp = {
      use: jest.fn(),
      post: jest.fn(),
      get: jest.fn(),
      delete: jest.fn(),
      listen: jest.fn((_port: number, callback: () => void) => {
        setImmediate(() => callback());
        return mockHttpServer;
      }),
    };
    jest.mock('express', () => {
      const fn = jest.fn(() => mockApp);
      (fn as any).json = jest.fn();
      return fn;
    });

    const exitSpy = jest.spyOn(process, 'exit').mockImplementation((() => {}) as any);
    const consoleErrorSpy = jest.spyOn(console, 'error').mockImplementation(() => {});
    const consoleLogSpy = jest.spyOn(console, 'log').mockImplementation(() => {});

    const { TLAPlusMCPServer } = require('../server');
    const server = new TLAPlusMCPServer({
      toolsDir: '/mock/tools',
      workingDir: '/mock/work',
      kbDir: null,
      javaHome: null,
      verbose: false,
      http: true,
      port: 3000,
    });

    await server.start();

    // Emit a non-fatal ECONNRESET error after startup
    const nonFatalError: NodeJS.ErrnoException = new Error('Connection reset');
    nonFatalError.code = 'ECONNRESET';
    mockHttpServer.emit('error', nonFatalError);

    // Verify: process.exit was NOT called
    expect(exitSpy).not.toHaveBeenCalled();

    exitSpy.mockRestore();
    consoleErrorSpy.mockRestore();
    consoleLogSpy.mockRestore();
    jest.restoreAllMocks();
  });

  // @tests REQ-REVIEW-006, SCN-REVIEW-006-02
  it('EADDRINUSE (fatal) DOES call process.exit(1)', async () => {
    jest.resetModules();

    jest.mock('@modelcontextprotocol/sdk/server/mcp.js', () => ({
      McpServer: jest.fn().mockImplementation(() => ({
        connect: jest.fn().mockResolvedValue(undefined),
        close: jest.fn().mockResolvedValue(undefined),
        tool: jest.fn(),
        resource: jest.fn(),
      })),
    }));
    jest.mock('@modelcontextprotocol/sdk/server/stdio.js', () => ({
      StdioServerTransport: jest.fn(),
    }));
    jest.mock('@modelcontextprotocol/sdk/server/streamableHttp.js', () => ({
      StreamableHTTPServerTransport: jest.fn().mockImplementation(() => ({
        handleRequest: jest.fn().mockResolvedValue(undefined),
        close: jest.fn(),
      })),
    }));
    jest.mock('../tools/sany', () => ({ registerSanyTools: jest.fn().mockResolvedValue(undefined) }));
    jest.mock('../tools/tlc', () => ({ registerTlcTools: jest.fn().mockResolvedValue(undefined) }));
    jest.mock('../tools/knowledge', () => ({
      registerKnowledgeBaseResources: jest.fn().mockResolvedValue(undefined),
      registerKnowledgeBaseFromCache: jest.fn().mockResolvedValue(undefined),
    }));
    jest.mock('../tools/animation', () => ({ registerAnimationTools: jest.fn().mockResolvedValue(undefined) }));

    const mockHttpServer = new EventEmitter() as EventEmitter & {
      listen: jest.Mock;
      address: jest.Mock;
    };
    (mockHttpServer as any).listen = jest.fn((_port: number, callback: () => void) => {
      setImmediate(() => callback());
      return mockHttpServer;
    });
    (mockHttpServer as any).address = jest.fn(() => ({ port: 3000 }));

    const mockApp = {
      use: jest.fn(),
      post: jest.fn(),
      get: jest.fn(),
      delete: jest.fn(),
      listen: jest.fn((_port: number, callback: () => void) => {
        setImmediate(() => callback());
        return mockHttpServer;
      }),
    };
    jest.mock('express', () => {
      const fn = jest.fn(() => mockApp);
      (fn as any).json = jest.fn();
      return fn;
    });

    const exitSpy = jest.spyOn(process, 'exit').mockImplementation((() => {}) as any);
    const consoleErrorSpy = jest.spyOn(console, 'error').mockImplementation(() => {});
    const consoleLogSpy = jest.spyOn(console, 'log').mockImplementation(() => {});

    const { TLAPlusMCPServer } = require('../server');
    const server = new TLAPlusMCPServer({
      toolsDir: '/mock/tools',
      workingDir: '/mock/work',
      kbDir: null,
      javaHome: null,
      verbose: false,
      http: true,
      port: 3000,
    });

    await server.start();

    // Emit a fatal EADDRINUSE error after startup
    const fatalError: NodeJS.ErrnoException = new Error('Address in use');
    fatalError.code = 'EADDRINUSE';
    mockHttpServer.emit('error', fatalError);

    // Verify: process.exit WAS called with 1
    expect(exitSpy).toHaveBeenCalledWith(1);

    exitSpy.mockRestore();
    consoleErrorSpy.mockRestore();
    consoleLogSpy.mockRestore();
    jest.restoreAllMocks();
  });
});

// ---------------------------------------------------------------------------
// REQ-REVIEW-007: Consolidated SVG Parsing in RenderService
// ---------------------------------------------------------------------------

describe('REQ-REVIEW-007: SVG Consolidation', () => {
  // @tests REQ-REVIEW-007, SCN-REVIEW-007-01
  it('only ONE parseElementAttrs function exists in RenderService.ts', () => {
    const renderPath = path.resolve(
      __dirname,
      '..',
      'tools',
      'animation',
      'RenderService.ts'
    );
    const content = fs.readFileSync(renderPath, 'utf-8');

    const matches = content.match(/function parseElementAttrs/g) || [];
    expect(matches.length).toBe(1);

    // Uses hyphenated regex
    expect(content).toContain('[a-zA-Z][a-zA-Z0-9-]*');
    // Has all numeric attributes including hyphenated ones
    expect(content).toContain("'font-size'");
    expect(content).toContain("'stroke-width'");
  });

  // @tests REQ-REVIEW-007, SCN-REVIEW-007-02
  it('only ONE svgToAnimView function exists in RenderService.ts', () => {
    const renderPath = path.resolve(
      __dirname,
      '..',
      'tools',
      'animation',
      'RenderService.ts'
    );
    const content = fs.readFileSync(renderPath, 'utf-8');

    const matches = content.match(/function svgToAnimView/g) || [];
    expect(matches.length).toBe(1);
  });

  // @tests REQ-REVIEW-007, SCN-REVIEW-007-02
  it('svgToAnimView handles all 5 element types including path', () => {
    const renderPath = path.resolve(
      __dirname,
      '..',
      'tools',
      'animation',
      'RenderService.ts'
    );
    const content = fs.readFileSync(renderPath, 'utf-8');

    // Extract the svgToAnimView function body
    const fnStart = content.indexOf('function svgToAnimView');
    expect(fnStart).toBeGreaterThan(-1);

    // Check for all 5 element type regexes within the function
    const afterFn = content.substring(fnStart);
    expect(afterFn).toContain('<rect');
    expect(afterFn).toContain('<circle');
    expect(afterFn).toContain('<text');
    expect(afterFn).toContain('<line');
    expect(afterFn).toContain('<path');
  });

  // @tests REQ-REVIEW-007, SCN-REVIEW-007-03
  it('svgToAnimView extracts dimensions from SVG content (no width/height params)', () => {
    const renderPath = path.resolve(
      __dirname,
      '..',
      'tools',
      'animation',
      'RenderService.ts'
    );
    const content = fs.readFileSync(renderPath, 'utf-8');

    // The function signature should take only svgContent, no width/height
    expect(content).toMatch(/function svgToAnimView\(svgContent:\s*string\)/);
    // Calls extractSvgDimensions
    expect(content).toContain('extractSvgDimensions(svgContent)');
  });

  // @tests REQ-REVIEW-007, SCN-REVIEW-007-04
  it('svgToAnimView defaults title to "Frame" (not "SVG Frame")', () => {
    const renderPath = path.resolve(
      __dirname,
      '..',
      'tools',
      'animation',
      'RenderService.ts'
    );
    const content = fs.readFileSync(renderPath, 'utf-8');

    // In the svgToAnimView function, default title is 'Frame'
    const fnStart = content.indexOf('function svgToAnimView');
    const fnBody = content.substring(fnStart, fnStart + 1000);
    expect(fnBody).toContain("'Frame'");
    // Should NOT use 'SVG Frame' as the default in the merged function
    expect(fnBody).not.toContain("'SVG Frame'");
  });

  // @tests REQ-REVIEW-007, SCN-REVIEW-007-03
  it('no call site passes width/height to svgToAnimView', () => {
    const renderPath = path.resolve(
      __dirname,
      '..',
      'tools',
      'animation',
      'RenderService.ts'
    );
    const content = fs.readFileSync(renderPath, 'utf-8');

    // Find all call sites of svgToAnimView
    const callSites = content.match(/svgToAnimView\([^)]+\)/g) || [];
    for (const call of callSites) {
      // Each call should have exactly one argument (svgContent), no commas
      const argPart = call.replace(/svgToAnimView\(/, '').replace(/\)$/, '');
      expect(argPart).not.toContain(',');
    }
  });
});

// ---------------------------------------------------------------------------
// REQ-REVIEW-008: CLI Missing Value Guards
// ---------------------------------------------------------------------------

describe('REQ-REVIEW-008: CLI Missing Value Guards', () => {
  const { parseArgs } = require('../cli');

  const valueTakingFlags = [
    '--port',
    '--working-dir',
    '--tools-dir',
    '--kb-dir',
    '--java-home',
  ];

  // @tests REQ-REVIEW-008, SCN-REVIEW-008-01, SCN-REVIEW-008-02
  it.each(valueTakingFlags)(
    'throws "Missing value for %s" when %s is the last argument',
    (flag) => {
      expect(() => parseArgs([flag])).toThrow(`Missing value for ${flag}`);
    }
  );

  // @tests REQ-REVIEW-008, SCN-REVIEW-008-01
  it('does NOT throw when flag has a value', () => {
    // --port with a value should not throw
    expect(() => parseArgs(['--port', '8080'])).not.toThrow();
  });

  // @tests REQ-REVIEW-008 (boundary: flag at end after valid flags)
  it('throws when trailing flag follows valid flags', () => {
    expect(() => parseArgs(['--http', '--port'])).toThrow(
      'Missing value for --port'
    );
  });
});

// ---------------------------------------------------------------------------
// REQ-REVIEW-009: Auto-Detection Timeout for execSync
// ---------------------------------------------------------------------------

describe('REQ-REVIEW-009: execSync Timeout', () => {
  // @tests REQ-REVIEW-009, SCN-REVIEW-009-01, SCN-REVIEW-009-02
  it('uses execFileSync with timeout: 5000 in paths.ts', () => {
    const pathsFile = path.resolve(__dirname, '..', 'utils', 'paths.ts');
    const content = fs.readFileSync(pathsFile, 'utf-8');

    // Uses execFileSync (not execSync)
    expect(content).toContain("import { execFileSync } from 'child_process'");
    expect(content).not.toMatch(/import\s*\{[^}]*execSync[^}]*\}\s*from\s*'child_process'/);

    // Has timeout: 5000
    expect(content).toContain('timeout: 5000');

    // Uses the array form: execFileSync('npm', ['root', '-g'], ...)
    expect(content).toContain("execFileSync('npm', ['root', '-g']");
  });
});

// ---------------------------------------------------------------------------
// REQ-REVIEW-011: MCP Server Version from package.json
// ---------------------------------------------------------------------------

describe('REQ-REVIEW-011: Version from package.json', () => {
  // @tests REQ-REVIEW-011, SCN-REVIEW-011-01
  it('server.ts reads version from package.json (not hardcoded 1.0.0)', () => {
    const serverPath = path.resolve(__dirname, '..', 'server.ts');
    const content = fs.readFileSync(serverPath, 'utf-8');

    // Has getPackageVersion function
    expect(content).toContain('function getPackageVersion');
    // Uses PACKAGE_VERSION in McpServer creation
    expect(content).toContain('version: PACKAGE_VERSION');
    // Does NOT hardcode '1.0.0'
    expect(content).not.toMatch(/version:\s*['"]1\.0\.0['"]/);
  });

  // @tests REQ-REVIEW-011, SCN-REVIEW-011-01
  it('package.json version is not 1.0.0', () => {
    const repoRoot = path.resolve(__dirname, '..', '..');
    const packageJson = JSON.parse(
      fs.readFileSync(path.join(repoRoot, 'package.json'), 'utf-8')
    );
    expect(packageJson.version).not.toBe('1.0.0');
    expect(packageJson.version).toBe('2.0.0');
  });

  // @tests REQ-REVIEW-011, SCN-REVIEW-011-01
  it('getPackageVersion falls back to 0.0.0 on failure', () => {
    const serverPath = path.resolve(__dirname, '..', 'server.ts');
    const content = fs.readFileSync(serverPath, 'utf-8');

    // Fallback is '0.0.0' (not '1.0.0')
    expect(content).toContain("return '0.0.0'");
    expect(content).not.toContain("return '1.0.0'");
  });
});

// ---------------------------------------------------------------------------
// REQ-REVIEW-013: @napi-rs/canvas to optionalDependencies
// ---------------------------------------------------------------------------

describe('REQ-REVIEW-013: Optional Canvas', () => {
  // @tests REQ-REVIEW-013, SCN-REVIEW-013-01
  it('@napi-rs/canvas is in optionalDependencies, not dependencies', () => {
    const repoRoot = path.resolve(__dirname, '..', '..');
    const packageJson = JSON.parse(
      fs.readFileSync(path.join(repoRoot, 'package.json'), 'utf-8')
    );

    expect(packageJson.dependencies).not.toHaveProperty('@napi-rs/canvas');
    expect(packageJson.optionalDependencies).toHaveProperty('@napi-rs/canvas');
  });

  // @tests REQ-REVIEW-013, SCN-REVIEW-013-02
  it('getCanvas function has try/catch with user-facing error message', () => {
    const renderPath = path.resolve(
      __dirname,
      '..',
      'tools',
      'animation',
      'RenderService.ts'
    );
    const content = fs.readFileSync(renderPath, 'utf-8');

    // Find the getCanvas function
    expect(content).toContain('async function getCanvas');
    expect(content).toContain(
      'Animation rendering requires @napi-rs/canvas. Install it with: npm install @napi-rs/canvas'
    );
  });

  // @tests REQ-REVIEW-013, SCN-REVIEW-013-02
  it('canvas import failure produces user-facing error via RenderService', async () => {
    jest.resetModules();

    // Mock the @napi-rs/canvas import to fail with MODULE_NOT_FOUND
    jest.mock('@napi-rs/canvas', () => {
      throw Object.assign(new Error('Cannot find module \'@napi-rs/canvas\''), {
        code: 'MODULE_NOT_FOUND',
      });
    });

    // Import RenderService after mocking canvas
    const { createRenderService } = require('../tools/animation/RenderService');

    const service = createRenderService();

    // Call render with kitty protocol which requires canvas rasterization
    const result = await service.render({
      operation: 'render',
      protocol: 'kitty',
      useCase: 'static',
      frameIndex: 0,
      animView: {
        frame: '0',
        title: 'Test',
        width: 100,
        height: 100,
        elements: [],
      },
    });

    // The render method catches the error and returns it as an AnimationError
    // The underlying error message should contain the user-facing message
    expect(result).toBeDefined();
    // The error wraps the canvas import failure
    expect(
      result.output || result.message || JSON.stringify(result)
    ).toContain('Animation rendering requires @napi-rs/canvas');

    jest.restoreAllMocks();
  });
});

// ---------------------------------------------------------------------------
// Security: Error Leakage Verification
// ---------------------------------------------------------------------------

describe('Security: Error Response Does Not Leak Stack Traces', () => {
  // @tests REQ-REVIEW-001 (security: error leakage verification)
  it('formatErrorResponse does NOT include stack trace when VERBOSE/DEBUG not set', () => {
    const { formatErrorResponse } = require('../tools/shared/error-formatting');
    const { enhanceError, ErrorCode } = require('../utils/errors');

    // Ensure VERBOSE and DEBUG are not set
    const oldVerbose = process.env.VERBOSE;
    const oldDebug = process.env.DEBUG;
    delete process.env.VERBOSE;
    delete process.env.DEBUG;

    const err = enhanceError(new Error('Something broke internally'), {
      code: ErrorCode.JAVA_NOT_FOUND,
    });

    const output = formatErrorResponse(err);

    // Should NOT contain stack trace information
    expect(output).not.toContain('Stack Trace:');
    expect(output).not.toMatch(/at\s+\w+\s+\(/); // No "at FunctionName (" patterns
    expect(output).not.toContain('.ts:');  // No TypeScript file references in stack

    // Should still contain the error code and suggestions
    expect(output).toContain('Error [JAVA_NOT_FOUND]');
    expect(output).toContain('Suggested Actions:');

    // Restore env
    if (oldVerbose !== undefined) process.env.VERBOSE = oldVerbose;
    else delete process.env.VERBOSE;
    if (oldDebug !== undefined) process.env.DEBUG = oldDebug;
    else delete process.env.DEBUG;
  });

  // @tests REQ-REVIEW-001 (security: stack traces shown only in VERBOSE mode)
  it('formatErrorResponse DOES include stack trace when VERBOSE is set', () => {
    const { formatErrorResponse } = require('../tools/shared/error-formatting');
    const { enhanceError, ErrorCode } = require('../utils/errors');

    const oldVerbose = process.env.VERBOSE;
    process.env.VERBOSE = '1';

    const err = enhanceError(new Error('Something broke'), {
      code: ErrorCode.JAVA_NOT_FOUND,
    });

    const output = formatErrorResponse(err);

    // Should contain stack trace in verbose mode
    expect(output).toContain('Stack Trace:');

    // Restore env
    if (oldVerbose !== undefined) process.env.VERBOSE = oldVerbose;
    else delete process.env.VERBOSE;
  });
});

// ---------------------------------------------------------------------------
// INV-REVIEW-004: MCP API Compatibility (Invariant)
// ---------------------------------------------------------------------------

describe('INV-REVIEW-004: MCP API Compatibility', () => {
  // @tests-invariant INV-REVIEW-004
  it('all expected tool names are registered by the tool modules', () => {
    const sanyPath = path.resolve(__dirname, '..', 'tools', 'sany.ts');
    const tlcPath = path.resolve(__dirname, '..', 'tools', 'tlc.ts');
    const animPath = path.resolve(__dirname, '..', 'tools', 'animation.ts');

    const sanyContent = fs.readFileSync(sanyPath, 'utf-8');
    const tlcContent = fs.readFileSync(tlcPath, 'utf-8');
    const animContent = fs.readFileSync(animPath, 'utf-8');

    // SANY tools
    expect(sanyContent).toContain('tlaplus_mcp_sany_parse');
    expect(sanyContent).toContain('tlaplus_mcp_sany_symbol');
    expect(sanyContent).toContain('tlaplus_mcp_sany_modules');

    // TLC tools
    expect(tlcContent).toContain('tlaplus_mcp_tlc_check');
    expect(tlcContent).toContain('tlaplus_mcp_tlc_smoke');
    expect(tlcContent).toContain('tlaplus_mcp_tlc_explore');
    expect(tlcContent).toContain('tlaplus_mcp_tlc_trace');

    // Animation tools
    expect(animContent).toContain('tlaplus_mcp_animation_detect');
    expect(animContent).toContain('tlaplus_mcp_animation_render');
    expect(animContent).toContain('tlaplus_mcp_animation_frameCount');
  });
});
