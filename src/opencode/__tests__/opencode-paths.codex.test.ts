// Spec: docs/codex-fixes/spec.md
// Testing: docs/codex-fixes/testing.md
//
// White-box tests for Finding 3: JSONC state machine stripJsonComments

import * as fs from 'fs';
import * as path from 'path';
import { parseConfigFile } from '../paths';

jest.mock('fs');
jest.mock('os');

const mockFs = fs as jest.Mocked<typeof fs>;

describe('stripJsonComments via parseConfigFile - Codex Fixes', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  /**
   * Helper: feed JSONC content through parseConfigFile with .jsonc extension
   * so that stripJsonComments is invoked.
   */
  function parseJsonc(content: string): unknown {
    mockFs.readFileSync.mockReturnValue(content);
    return parseConfigFile('/test/config.jsonc');
  }

  // --- REQ-CODEX-007: String-Aware JSONC Comment Stripping ---

  // @tests REQ-CODEX-007, SCN-CODEX-007-01
  it('URL inside string literal is preserved', () => {
    const content = '{"url": "https://example.com"}';
    const result = parseJsonc(content) as any;

    expect(result.url).toBe('https://example.com');
  });

  // @tests REQ-CODEX-007, SCN-CODEX-007-02
  it('multi-line comment pattern inside string is preserved', () => {
    const content = '{"pattern": "/* not a comment */"}';
    const result = parseJsonc(content) as any;

    expect(result.pattern).toBe('/* not a comment */');
  });

  // @tests REQ-CODEX-007, SCN-CODEX-007-03
  it('escaped quotes inside string are handled correctly', () => {
    const content = '{"msg": "say \\"hello\\""}';
    const result = parseJsonc(content) as any;

    expect(result.msg).toBe('say "hello"');
  });

  // @tests REQ-CODEX-007, SCN-CODEX-007-04
  it('escaped quote followed by comment-like pattern handled correctly', () => {
    const content = `{
  "a": "line with \\"quote\\"",
  "b": "https://example.com" // real comment
}`;
    const result = parseJsonc(content) as any;

    expect(result.a).toBe('line with "quote"');
    expect(result.b).toBe('https://example.com');
  });

  // --- REQ-CODEX-008: Comment and Trailing Comma Removal Preserved ---

  // @tests REQ-CODEX-008, SCN-CODEX-008-01
  it('single-line comment is removed', () => {
    const content = `{
  // This is a comment
  "key": "value"
}`;
    const result = parseJsonc(content) as any;

    expect(result.key).toBe('value');
  });

  // @tests REQ-CODEX-008, SCN-CODEX-008-02
  it('multi-line comment is removed', () => {
    const content = `{
  /* Multi-line
     comment */
  "key": "value"
}`;
    const result = parseJsonc(content) as any;

    expect(result.key).toBe('value');
  });

  // @tests REQ-CODEX-008, SCN-CODEX-008-03
  it('trailing comma is removed', () => {
    const content = `{
  "a": 1,
  "b": 2,
}`;
    const result = parseJsonc(content) as any;

    expect(result.a).toBe(1);
    expect(result.b).toBe(2);
  });

  // --- Adversarial Tests ---

  // @tests REQ-CODEX-007
  // TC-ADV-003: Unclosed string does not cause infinite loop
  it('unclosed string does not infinite-loop', () => {
    // This input has an unclosed string - the parser should not hang.
    // It may produce invalid JSON, but it must terminate.
    const content = '{"key": "value with no closing quote';
    mockFs.readFileSync.mockReturnValue(content);

    // We just need to verify it terminates (no infinite loop).
    // JSON.parse will fail, but stripJsonComments itself should return.
    expect(() => parseConfigFile('/test/config.jsonc')).toThrow();
  });

  // @tests REQ-CODEX-008
  // TC-ADV-004: Unclosed multi-line comment does not infinite-loop
  it('unclosed multi-line comment does not hang (terminates)', () => {
    // The unclosed comment consumes nearly all chars after /*, but the last
    // char leaks through since the while loop terminates at i+1 >= length.
    // This is acceptable: the important thing is it does NOT infinite-loop.
    // JSON.parse may or may not succeed depending on what the trailing char is.
    const content = '/* unclosed comment';
    mockFs.readFileSync.mockReturnValue(content);

    // We just verify it terminates without hanging.
    // The stripped result will likely not be valid JSON.
    expect(() => parseConfigFile('/test/config.jsonc')).toThrow();
  });

  // @tests REQ-CODEX-008
  // TC-ADV-002: empty content
  it('empty content throws JSON parse error', () => {
    mockFs.readFileSync.mockReturnValue('');
    expect(() => parseConfigFile('/test/config.jsonc')).toThrow();
  });

  // @tests REQ-CODEX-007
  // TC-EDGE-002: backslash at end of content
  it('backslash at end of string content does not crash', () => {
    // A trailing backslash in a string: "test\\" is valid JSON for the string "test\"
    const content = '{"x": "test\\\\"}';
    const result = parseJsonc(content) as any;
    expect(result.x).toBe('test\\');
  });

  // @tests REQ-CODEX-008
  // TC-EDGE-003: comment with no newline
  it('single-line comment without newline at end is handled', () => {
    const content = '{"key": "value"} // no newline here';
    const result = parseJsonc(content) as any;
    expect(result.key).toBe('value');
  });

  // Complex scenario: mixture of strings with URLs and actual comments
  // @tests REQ-CODEX-007, REQ-CODEX-008
  it('complex JSONC with URLs in strings and real comments', () => {
    const content = `{
  // Configuration file
  "server": "https://api.example.com/v1",
  /* Database connection */
  "db": "postgres://user:pass@host:5432/db",
  "retry": 3, // max retries
}`;
    const result = parseJsonc(content) as any;

    expect(result.server).toBe('https://api.example.com/v1');
    expect(result.db).toBe('postgres://user:pass@host:5432/db');
    expect(result.retry).toBe(3);
  });
});
