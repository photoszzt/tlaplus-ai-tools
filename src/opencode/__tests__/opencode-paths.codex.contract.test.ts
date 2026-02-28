// Spec: docs/codex-fixes/spec.md
// Contract: docs/codex-fixes/contract.md (parseConfigFile)
// Testing: docs/codex-fixes/testing.md
//
// Contract tests for parseConfigFile JSONC handling.
// Tests exercise the public API only.

import * as fs from 'fs';
import { parseConfigFile } from '../paths';

jest.mock('fs');
jest.mock('os');

const mockFs = fs as jest.Mocked<typeof fs>;

describe('parseConfigFile - Contract Tests (Codex JSONC)', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  // @tests-contract REQ-CODEX-007
  it('JSONC with URL in string parses correctly', () => {
    const content = '{"url": "https://example.com/api"}';
    mockFs.readFileSync.mockReturnValue(content);

    const result = parseConfigFile('/config.jsonc') as any;

    expect(result.url).toBe('https://example.com/api');
  });

  // @tests-contract REQ-CODEX-008
  it('JSONC with real comments parses correctly', () => {
    const content = `{
  // comment
  "key": "value"
  /* block comment */
}`;
    mockFs.readFileSync.mockReturnValue(content);

    const result = parseConfigFile('/config.jsonc') as any;

    expect(result.key).toBe('value');
  });

  // @tests-contract REQ-CODEX-007
  it('JSONC with URL in string and real comment both handled', () => {
    const content = `{
  "url": "https://example.com", // this is a comment
  "name": "test"
}`;
    mockFs.readFileSync.mockReturnValue(content);

    const result = parseConfigFile('/config.jsonc') as any;

    expect(result.url).toBe('https://example.com');
    expect(result.name).toBe('test');
  });
});
