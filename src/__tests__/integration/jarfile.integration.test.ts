/**
 * Integration tests for JAR module scanning using real tla2tools.jar.
 * These tests require the actual JAR files to be present.
 */
import * as path from 'path';
import * as fs from 'fs';
import {
  listTlaModulesInJar,
  resolveJarfilePath,
  clearJarCache,
} from '../../utils/jarfile';
import { getModuleSearchPaths } from '../../utils/tla-tools';

const TOOLS_DIR = path.resolve(__dirname, '../../../../tools');
const TLA2TOOLS_JAR = path.join(TOOLS_DIR, 'tla2tools.jar');

const describeIfJarExists = fs.existsSync(TLA2TOOLS_JAR) ? describe : describe.skip;

describeIfJarExists('JAR module scanning integration', () => {
  beforeEach(() => {
    clearJarCache();
  });

  it('getModuleSearchPaths returns jarfile: URIs', () => {
    const paths = getModuleSearchPaths(TOOLS_DIR);
    const jarPaths = paths.filter((p) => p.startsWith('jarfile:'));
    expect(jarPaths.length).toBeGreaterThan(0);
    expect(jarPaths.some((p) => p.includes('tla2tools.jar'))).toBe(true);
  });

  it('lists standard modules from tla2tools.jar', () => {
    const modules = listTlaModulesInJar(
      TLA2TOOLS_JAR,
      'tla2sany/StandardModules',
      false
    );

    expect(modules).toContain('Naturals.tla');
    expect(modules).toContain('Sequences.tla');
    expect(modules).toContain('FiniteSets.tla');
    expect(modules).toContain('Integers.tla');

    const underscoreModules = modules.filter((m) => m.startsWith('_'));
    expect(underscoreModules).toHaveLength(0);
  });

  it('resolves jarfile: URI to extractable filesystem path', () => {
    const uri = `jarfile:${TLA2TOOLS_JAR}!/tla2sany/StandardModules/Naturals.tla`;
    const fsPath = resolveJarfilePath(uri);

    expect(fs.existsSync(fsPath)).toBe(true);
    const content = fs.readFileSync(fsPath, 'utf-8');
    expect(content).toContain('MODULE Naturals');
  });

  it('extracted directory contains sibling modules for EXTENDS', () => {
    const uri = `jarfile:${TLA2TOOLS_JAR}!/tla2sany/StandardModules/Integers.tla`;
    const fsPath = resolveJarfilePath(uri);
    const dir = path.dirname(fsPath);

    expect(fs.existsSync(path.join(dir, 'Naturals.tla'))).toBe(true);
  });
});
