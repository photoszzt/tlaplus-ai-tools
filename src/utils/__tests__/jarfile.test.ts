import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import AdmZip from 'adm-zip';
import { parseJarfileUri, listJarEntries, listTlaModulesInJar, extractJarEntry, extractJarDirectory, clearJarCache, resolveJarfilePath } from '../jarfile';

let tempDir: string;
let testJarPath: string;

beforeAll(() => {
  tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'jarfile-test-'));
  testJarPath = path.join(tempDir, 'test.jar');

  const zip = new AdmZip();
  zip.addFile('StandardModules/Naturals.tla', Buffer.from('---- MODULE Naturals ----'));
  zip.addFile('StandardModules/Sequences.tla', Buffer.from('---- MODULE Sequences ----'));
  zip.addFile('StandardModules/_TETrace.tla', Buffer.from('---- MODULE _TETrace ----'));
  zip.addFile('StandardModules/README.md', Buffer.from('# Readme'));
  zip.addFile('RootModule.tla', Buffer.from('---- MODULE RootModule ----'));
  zip.addFile('nested/deep/Module.tla', Buffer.from('---- MODULE Module ----'));
  zip.writeZip(testJarPath);
});

afterAll(() => {
  fs.rmSync(tempDir, { recursive: true, force: true });
});

describe('jarfile utilities', () => {
  describe('parseJarfileUri', () => {
    it('parses a valid jarfile URI', () => {
      const result = parseJarfileUri('jarfile:/path/to/archive.jar!/inner/path/Module.tla');
      expect(result).toEqual({
        jarPath: '/path/to/archive.jar',
        innerPath: 'inner/path/Module.tla',
      });
    });

    it('parses jarfile URI with root inner path', () => {
      const result = parseJarfileUri('jarfile:/path/to/archive.jar!/');
      expect(result).toEqual({
        jarPath: '/path/to/archive.jar',
        innerPath: '',
      });
    });

    it('parses jarfile URI without trailing slash', () => {
      const result = parseJarfileUri('jarfile:/path/to/archive.jar!');
      expect(result).toEqual({
        jarPath: '/path/to/archive.jar',
        innerPath: '',
      });
    });

    it('handles Windows paths', () => {
      const result = parseJarfileUri('jarfile:C:/Users/test/tools/archive.jar!/StandardModules/Naturals.tla');
      expect(result).toEqual({
        jarPath: 'C:/Users/test/tools/archive.jar',
        innerPath: 'StandardModules/Naturals.tla',
      });
    });

    it('throws on missing jarfile: prefix', () => {
      expect(() => parseJarfileUri('/path/to/archive.jar!/inner')).toThrow('Invalid jarfile URI');
    });

    it('throws on missing !/ separator', () => {
      expect(() => parseJarfileUri('jarfile:/path/to/archive.jar')).toThrow('Invalid jarfile URI');
    });

    it('throws on empty jar path', () => {
      expect(() => parseJarfileUri('jarfile:!/inner/path')).toThrow('Invalid jarfile URI');
    });
  });

  describe('listJarEntries', () => {
    it('lists files in a directory', () => {
      const entries = listJarEntries(testJarPath, 'StandardModules');
      expect(entries.sort()).toEqual(['Naturals.tla', 'Sequences.tla', '_TETrace.tla', 'README.md'].sort());
    });

    it('lists files at root level', () => {
      const entries = listJarEntries(testJarPath, '');
      expect(entries).toContain('RootModule.tla');
      expect(entries).not.toContain('nested/deep/Module.tla');
    });

    it('returns empty array for non-existent directory', () => {
      const entries = listJarEntries(testJarPath, 'nonexistent');
      expect(entries).toEqual([]);
    });

    it('throws for non-existent JAR file', () => {
      expect(() => listJarEntries('/nonexistent/path.jar', '')).toThrow();
    });

    it('handles directory path with trailing slash', () => {
      const entries = listJarEntries(testJarPath, 'StandardModules/');
      expect(entries.sort()).toEqual(['Naturals.tla', 'Sequences.tla', '_TETrace.tla', 'README.md'].sort());
    });
  });

  describe('listTlaModulesInJar', () => {
    it('lists only .tla files, excluding _ prefixed modules', () => {
      const modules = listTlaModulesInJar(testJarPath, 'StandardModules');
      expect(modules.sort()).toEqual(['Naturals.tla', 'Sequences.tla'].sort());
      expect(modules).not.toContain('_TETrace.tla');
      expect(modules).not.toContain('README.md');
    });

    it('returns full jarfile URIs when returnFullUri is true', () => {
      const modules = listTlaModulesInJar(testJarPath, 'StandardModules', true);
      expect(modules).toContain(`jarfile:${testJarPath}!/StandardModules/Naturals.tla`);
      expect(modules).toContain(`jarfile:${testJarPath}!/StandardModules/Sequences.tla`);
    });

    it('returns full jarfile URIs for root directory', () => {
      const modules = listTlaModulesInJar(testJarPath, '', true);
      expect(modules).toContain(`jarfile:${testJarPath}!/RootModule.tla`);
    });
  });

  describe('extractJarEntry', () => {
    beforeEach(() => {
      clearJarCache();
    });

    it('extracts a single file to cache and returns path', async () => {
      const extractedPath = await extractJarEntry(testJarPath, 'StandardModules/Naturals.tla');
      expect(fs.existsSync(extractedPath)).toBe(true);
      expect(extractedPath.endsWith('Naturals.tla')).toBe(true);
      const content = fs.readFileSync(extractedPath, 'utf-8');
      expect(content).toContain('MODULE Naturals');
    });

    it('returns same path on repeated calls (caching)', async () => {
      const path1 = await extractJarEntry(testJarPath, 'StandardModules/Naturals.tla');
      const path2 = await extractJarEntry(testJarPath, 'StandardModules/Naturals.tla');
      expect(path1).toBe(path2);
    });

    it('throws for non-existent entry', async () => {
      await expect(extractJarEntry(testJarPath, 'nonexistent.tla')).rejects.toThrow('not found in JAR');
    });

    it('rejects path traversal attempts', async () => {
      await expect(extractJarEntry(testJarPath, '../etc/passwd')).rejects.toThrow('path traversal');
    });
  });

  describe('extractJarDirectory', () => {
    beforeEach(() => {
      clearJarCache();
    });

    it('extracts entire directory and returns cache path', async () => {
      const extractedDir = await extractJarDirectory(testJarPath, 'StandardModules');
      expect(fs.existsSync(extractedDir)).toBe(true);
      expect(fs.existsSync(path.join(extractedDir, 'Naturals.tla'))).toBe(true);
      expect(fs.existsSync(path.join(extractedDir, 'Sequences.tla'))).toBe(true);
    });

    it('returns same path on repeated calls (caching)', async () => {
      const dir1 = await extractJarDirectory(testJarPath, 'StandardModules');
      const dir2 = await extractJarDirectory(testJarPath, 'StandardModules');
      expect(dir1).toBe(dir2);
    });
  });

  describe('resolveJarfilePath', () => {
    beforeEach(() => {
      clearJarCache();
    });

    it('extracts module and its directory, returns filesystem path', async () => {
      const uri = `jarfile:${testJarPath}!/StandardModules/Naturals.tla`;
      const fsPath = await resolveJarfilePath(uri);

      expect(fs.existsSync(fsPath)).toBe(true);
      expect(fsPath.endsWith('Naturals.tla')).toBe(true);

      const dir = path.dirname(fsPath);
      expect(fs.existsSync(path.join(dir, 'Sequences.tla'))).toBe(true);
    });

    it('handles root-level modules', async () => {
      const uri = `jarfile:${testJarPath}!/RootModule.tla`;
      const fsPath = await resolveJarfilePath(uri);

      expect(fs.existsSync(fsPath)).toBe(true);
      expect(path.basename(fsPath)).toBe('RootModule.tla');
    });
  });
});
