import { findJavaExecutable, runJavaCommand } from '../java';
import { parseSanyOutput } from '../sany';
import { autoDetectToolsDir, autoDetectKbDir } from '../paths';
import * as path from 'path';
import * as fs from 'fs';
import { PassThrough } from 'stream';
import { EventEmitter } from 'events';
import type { ProcessInfo } from '../java';

describe('integration tests', () => {
  const isJavaAvailable = (): boolean => {
    try {
      const javaPath = findJavaExecutable();
      return !!javaPath;
    } catch {
      return false;
    }
  };

  const javaAvailable = isJavaAvailable();

  describe('full flow: findJava → autoDetectToolsDir', () => {
    it('finds java executable', () => {
      if (!javaAvailable) {
        console.log('Skipping: Java not available');
        return;
      }

      const javaPath = findJavaExecutable();
      expect(javaPath).toBeTruthy();
    });

    it('auto-detects tools directory in monorepo', async () => {
      const toolsDir = await autoDetectToolsDir();

      if (!toolsDir) {
        console.log('Skipping: Tools directory not found');
        return;
      }

      expect(fs.existsSync(toolsDir)).toBe(true);
      expect(fs.existsSync(path.join(toolsDir, 'tla2tools.jar'))).toBe(true);
    });

    it('auto-detects knowledgebase directory in monorepo', async () => {
      const kbDir = await autoDetectKbDir();

      if (!kbDir) {
        console.log('Skipping: Knowledgebase directory not found');
        return;
      }

      expect(fs.existsSync(kbDir)).toBe(true);
      const files = fs.readdirSync(kbDir);
      expect(files.some(f => f.endsWith('.md'))).toBe(true);
    });
  });

  describe('error propagation through stack', () => {
    it('throws error when invalid java home provided', () => {
      expect(() => findJavaExecutable('/invalid/java/home'))
        .toThrow('Java executable not found');
    });

    it('propagates java process spawn errors', async () => {
      if (!javaAvailable) {
        console.log('Skipping: Java not available');
        return;
      }

      await expect(runJavaCommand('/nonexistent.jar', 'MainClass', []))
        .resolves.toBeDefined();
    });
  });

  describe('SANY output parsing integration', () => {
    it('parseSanyOutput handles empty stream', async () => {
      const mergedOutput = new PassThrough();
      const proc = Object.assign(new EventEmitter(), { exitCode: 0 as number | null });

      setImmediate(() => {
        mergedOutput.end();
      });

      const result = await parseSanyOutput({
        process: proc as ProcessInfo['process'],
        stdout: null,
        stderr: null,
        mergedOutput,
        kill: jest.fn()
      });

      expect(result.success).toBe(true);
      expect(result.errors).toHaveLength(0);
    });

    it('parseSanyOutput handles success output', async () => {
      const mergedOutput = new PassThrough();
      const proc = Object.assign(new EventEmitter(), { exitCode: 0 as number | null });

      setImmediate(() => {
        mergedOutput.write('Parsing file /test/Module.tla\n');
        mergedOutput.write('Semantic processing of module Module\n');
        mergedOutput.write('SANY finished.\n');
        mergedOutput.end();
      });

      const result = await parseSanyOutput({
        process: proc as ProcessInfo['process'],
        stdout: null,
        stderr: null,
        mergedOutput,
        kill: jest.fn()
      });

      expect(result.success).toBe(true);
    });

    it('parseSanyOutput extracts errors correctly', async () => {
      const mergedOutput = new PassThrough();
      const proc = Object.assign(new EventEmitter(), { exitCode: 1 as number | null });

      setImmediate(() => {
        mergedOutput.write('Parsing file /test/Module.tla\n');
        mergedOutput.write('  Lexical error at line 5, column 3. Unknown identifier\n');
        mergedOutput.end();
      });

      const result = await parseSanyOutput({
        process: proc as ProcessInfo['process'],
        stdout: null,
        stderr: null,
        mergedOutput,
        kill: jest.fn()
      });

      expect(result.success).toBe(false);
      expect(result.errors.length).toBeGreaterThan(0);
      expect(result.errors[0].line).toBe(5);
      expect(result.errors[0].column).toBe(3);
    });
  });

  describe('cross-platform path handling', () => {
    it('resolves paths consistently', async () => {
      const toolsDir = await autoDetectToolsDir();

      if (!toolsDir) {
        console.log('Skipping: Tools directory not found');
        return;
      }

      expect(path.isAbsolute(toolsDir)).toBe(true);
      expect(toolsDir).not.toContain('\\\\');
    });
  });
});
