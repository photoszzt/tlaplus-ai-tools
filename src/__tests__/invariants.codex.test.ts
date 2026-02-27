// Spec: docs/codex-fixes/spec.md
// Testing: docs/codex-fixes/testing.md
//
// Invariant tests for INV-CODEX-002 and INV-CODEX-003

import * as path from 'path';
import * as fs from 'fs';

// ---- INV-CODEX-002: No New Runtime Dependencies ----

describe('INV-CODEX-002: No New Runtime Dependencies', () => {
  // @tests-invariant INV-CODEX-002
  it('package.json dependencies contains only the expected runtime packages', () => {
    // Read the real package.json from the repo root
    const repoRoot = path.resolve(__dirname, '..', '..');
    const packageJsonPath = path.join(repoRoot, 'package.json');
    const packageJson = JSON.parse(fs.readFileSync(packageJsonPath, 'utf-8'));

    // The allowed runtime dependencies per spec INV-CODEX-002 and the
    // actual baseline at the time of the codex fix. The spec lists:
    //   @modelcontextprotocol/sdk, adm-zip, express, fast-xml-parser, zod
    // The actual package.json also has @napi-rs/canvas and @opencode-ai/plugin
    // which pre-date the codex fix. The invariant says "no NEW" deps added.
    const allowedDependencies = new Set([
      '@modelcontextprotocol/sdk',
      '@napi-rs/canvas',
      '@opencode-ai/plugin',
      'adm-zip',
      'express',
      'fast-xml-parser',
      'zod',
    ]);

    const actualDependencies = Object.keys(packageJson.dependencies || {});

    // Verify no NEW dependencies have been added beyond the allowed set
    const unexpectedDeps = actualDependencies.filter(
      (dep: string) => !allowedDependencies.has(dep)
    );

    expect(unexpectedDeps).toEqual([]);

    // Also verify the expected deps are still present (sanity check)
    for (const expected of allowedDependencies) {
      expect(actualDependencies).toContain(expected);
    }
  });

  // @tests-invariant INV-CODEX-002
  it('devDependencies are not checked (only runtime deps matter)', () => {
    // This test documents that devDependencies are explicitly out of scope
    // for INV-CODEX-002. The invariant only restricts runtime dependencies.
    const repoRoot = path.resolve(__dirname, '..', '..');
    const packageJsonPath = path.join(repoRoot, 'package.json');
    const packageJson = JSON.parse(fs.readFileSync(packageJsonPath, 'utf-8'));

    // devDependencies should exist (project has dev deps) but are not restricted
    expect(packageJson.devDependencies).toBeDefined();
    expect(Object.keys(packageJson.devDependencies).length).toBeGreaterThan(0);
  });
});

// ---- INV-CODEX-003: Error Response Format Convention ----
// These tests verify that error responses from cfgFile-not-found (TLC tools)
// and jarfile access-denied (SANY tools) use the early-return pattern:
//   { content: [{ type: 'text', text: ... }] }
// with NO isError field.

import { registerTlcTools } from '../tools/tlc';
import { registerSanyTools } from '../tools/sany';
import { createMockMcpServer, callRegisteredTool } from './helpers/mock-server';
import { MINIMAL_CONFIG } from './fixtures/config-samples';

jest.mock('../utils/paths');
jest.mock('../utils/tlc-helpers');
jest.mock('../utils/sany');
jest.mock('../utils/symbols');
jest.mock('../utils/jarfile');
jest.mock('../utils/tla-tools');

import { resolveAndValidatePath } from '../utils/paths';
import { getSpecFiles, runTlcAndWait } from '../utils/tlc-helpers';
import * as jarfile from '../utils/jarfile';
import * as tlaTools from '../utils/tla-tools';

// We need a separate fs mock for the TLC/SANY tool tests.
// The INV-CODEX-002 tests above use the real fs, so we use jest.mock
// only for the modules that the tool handlers import.
jest.mock('fs', () => {
  const actual = jest.requireActual('fs');
  return {
    ...actual,
    existsSync: jest.fn(actual.existsSync),
    readFileSync: actual.readFileSync,
    promises: actual.promises,
  };
});

import { existsSync } from 'fs';

describe('INV-CODEX-003: Error Response Format Convention', () => {
  let mockServer: ReturnType<typeof createMockMcpServer>;

  beforeEach(() => {
    jest.clearAllMocks();
    mockServer = createMockMcpServer();
    (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => p);
    (tlaTools.getModuleSearchPaths as jest.Mock).mockReturnValue([]);
    (jarfile.isJarfileUri as jest.Mock).mockImplementation((p: string) =>
      p.startsWith('jarfile:')
    );
    (jarfile.parseJarfileUri as jest.Mock).mockImplementation((uri: string) => {
      const withoutScheme = uri.slice('jarfile:'.length);
      const sepIdx = withoutScheme.indexOf('!');
      return {
        jarPath: withoutScheme.slice(0, sepIdx),
        innerPath: withoutScheme.slice(sepIdx + 2),
      };
    });
  });

  // Helper to set up TLC tools with standard mocks
  async function setupTlcTools() {
    await registerTlcTools(mockServer, MINIMAL_CONFIG);
    (getSpecFiles as jest.Mock).mockReturnValue({
      tlaFilePath: '/mock/spec.tla',
      cfgFilePath: '/mock/spec.cfg',
    });
    (runTlcAndWait as jest.Mock).mockResolvedValue({
      stdout: 'Model checking completed. No error has been found.',
      stderr: '',
      exitCode: 0,
    });
  }

  // @tests-invariant INV-CODEX-003
  it('cfgFile-not-found error response has content[0].type=text, content[0].text is string, no isError', async () => {
    await setupTlcTools();
    (existsSync as jest.Mock).mockImplementation((p: string) => {
      if (p === '/mock/spec.tla') return true;
      if (p === '/tmp/missing.cfg') return false;
      return true;
    });

    const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
      fileName: '/mock/spec.tla',
      cfgFile: '/tmp/missing.cfg',
    });

    // Verify response structure matches early-return pattern
    expect(response).toBeDefined();
    expect(response).toHaveProperty('content');
    expect(Array.isArray(response.content)).toBe(true);
    expect(response.content.length).toBeGreaterThanOrEqual(1);
    expect(response.content[0]).toHaveProperty('type', 'text');
    expect(typeof response.content[0].text).toBe('string');
    expect(response.content[0].text.length).toBeGreaterThan(0);

    // INV-CODEX-003: No isError field (early-return convention)
    expect(response).not.toHaveProperty('isError');
  });

  // @tests-invariant INV-CODEX-003
  it('jarfile access-denied error response has content[0].type=text, content[0].text is string, no isError', async () => {
    const configWithDir = { ...MINIMAL_CONFIG, workingDir: '/workspace' };
    await registerSanyTools(mockServer, configWithDir);

    // resolveAndValidatePath throws for paths outside workingDir
    (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => {
      if (p === '/etc/evil.jar') {
        throw new Error(
          'Access denied: Path /etc/evil.jar is outside the working directory /workspace'
        );
      }
      return p;
    });

    const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_sany_parse', {
      fileName: 'jarfile:/etc/evil.jar!/Module.tla',
    });

    // Verify response structure matches early-return pattern
    expect(response).toBeDefined();
    expect(response).toHaveProperty('content');
    expect(Array.isArray(response.content)).toBe(true);
    expect(response.content.length).toBeGreaterThanOrEqual(1);
    expect(response.content[0]).toHaveProperty('type', 'text');
    expect(typeof response.content[0].text).toBe('string');
    expect(response.content[0].text.length).toBeGreaterThan(0);

    // INV-CODEX-003: No isError field (early-return convention)
    expect(response).not.toHaveProperty('isError');
  });

  // @tests-invariant INV-CODEX-003
  it('both error paths contain meaningful error text in content[0].text', async () => {
    // Set up TLC
    await setupTlcTools();
    (existsSync as jest.Mock).mockImplementation((p: string) => {
      if (p === '/mock/spec.tla') return true;
      if (p === '/tmp/missing.cfg') return false;
      return true;
    });

    const tlcResponse = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
      fileName: '/mock/spec.tla',
      cfgFile: '/tmp/missing.cfg',
    });

    // Set up SANY
    const configWithDir = { ...MINIMAL_CONFIG, workingDir: '/workspace' };
    const sanyServer = createMockMcpServer();
    await registerSanyTools(sanyServer, configWithDir);

    (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => {
      if (p === '/etc/evil.jar') {
        throw new Error('Access denied: Path /etc/evil.jar is outside the working directory /workspace');
      }
      return p;
    });

    const sanyResponse = await callRegisteredTool(sanyServer, 'tlaplus_mcp_sany_parse', {
      fileName: 'jarfile:/etc/evil.jar!/Module.tla',
    });

    // TLC cfgFile error: contains the path and "does not exist"
    expect(tlcResponse.content[0].text).toContain('Config file');
    expect(tlcResponse.content[0].text).toContain('does not exist on disk');

    // SANY jarfile error: contains "Access denied"
    expect(sanyResponse.content[0].text).toContain('Access denied');
  });
});
