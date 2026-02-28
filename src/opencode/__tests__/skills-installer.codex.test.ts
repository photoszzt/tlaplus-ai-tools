// Spec: docs/codex-fixes/spec.md
// Testing: docs/codex-fixes/testing.md
//
// White-box tests for Finding 4: Skills installer SKILL.md comparison + stale removal

import * as fs from 'fs';
import * as path from 'path';
import * as paths from '../paths';
import { installSkills } from '../skills-installer';

jest.mock('fs');
jest.mock('../paths');

const mockFs = fs as jest.Mocked<typeof fs>;
const mockPaths = paths as jest.Mocked<typeof paths>;

function normalizePath(p: string): string {
  return p.split(path.sep).join('/');
}

describe('Skills Installer - Codex SKILL.md Comparison Fixes', () => {
  const pluginRoot = '/usr/lib/node_modules/tlaplus-ai-tools';
  const sourceDir = path.join(pluginRoot, 'skills');
  const targetDir = '/home/user/.config/opencode/skills';

  beforeEach(() => {
    jest.clearAllMocks();
    mockPaths.getGlobalOpenCodeDir.mockReturnValue('/home/user/.config/opencode');
    mockPaths.getCanonicalDir.mockReturnValue(targetDir);
    mockPaths.ensureDir.mockImplementation(() => {});
  });

  // --- REQ-CODEX-010: SKILL.md Content Comparison ---

  // @tests REQ-CODEX-010, SCN-CODEX-010-01
  it('stale SKILL.md content triggers reinstall', () => {
    const skillName = 'tla-getting-started';
    const sourcePath = path.join(sourceDir, skillName);
    const targetPath = path.join(targetDir, skillName);
    const sourceSkillMd = path.join(sourcePath, 'SKILL.md');
    const targetSkillMd = path.join(targetPath, 'SKILL.md');

    let rmSyncCalled = false;
    mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(sourceDir)) return true;
      if (n === normalizePath(sourcePath)) return true;
      if (n === normalizePath(path.join(sourcePath, 'SKILL.md'))) return true;
      if (n === normalizePath(targetPath)) return !rmSyncCalled;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: skillName, isDirectory: () => true } as any,
    ] as any);

    // Target is a directory (not symlink)
    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => false,
      isDirectory: () => true,
    } as fs.Stats);

    // SKILL.md content differs between source and target
    mockFs.readFileSync.mockImplementation((p: fs.PathOrFileDescriptor) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(targetSkillMd)) return 'old skill content';
      if (n === normalizePath(sourceSkillMd)) return 'new skill content';
      return '';
    });

    mockFs.rmSync.mockImplementation(() => { rmSyncCalled = true; });
    mockFs.symlinkSync.mockImplementation(() => {});

    const result = installSkills(pluginRoot);

    expect(result.installedCount).toBe(1);
    expect(result.alreadyInstalledCount).toBe(0);
    expect(result.skills[0].installed).toBe(true);
    expect(mockFs.rmSync).toHaveBeenCalledWith(targetPath, { recursive: true, force: true });
  });

  // @tests REQ-CODEX-010, SCN-CODEX-010-02
  it('matching SKILL.md content returns already installed', () => {
    const skillName = 'tla-getting-started';
    const sourcePath = path.join(sourceDir, skillName);
    const targetPath = path.join(targetDir, skillName);

    mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(sourceDir)) return true;
      if (n === normalizePath(sourcePath)) return true;
      if (n === normalizePath(path.join(sourcePath, 'SKILL.md'))) return true;
      if (n === normalizePath(targetPath)) return true;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: skillName, isDirectory: () => true } as any,
    ] as any);

    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => false,
      isDirectory: () => true,
    } as fs.Stats);

    // Both have same content
    mockFs.readFileSync.mockReturnValue('same skill content');

    const result = installSkills(pluginRoot);

    expect(result.installedCount).toBe(0);
    expect(result.alreadyInstalledCount).toBe(1);
    expect(result.skills[0].installed).toBe(false);
    expect(result.skills[0].error).toBeUndefined();
    expect(mockFs.rmSync).not.toHaveBeenCalled();
  });

  // @tests REQ-CODEX-010, SCN-CODEX-010-03
  it('missing SKILL.md in target directory triggers reinstall', () => {
    const skillName = 'tla-getting-started';
    const sourcePath = path.join(sourceDir, skillName);
    const targetPath = path.join(targetDir, skillName);
    const targetSkillMd = path.join(targetPath, 'SKILL.md');

    let rmSyncCalled = false;
    mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(sourceDir)) return true;
      if (n === normalizePath(sourcePath)) return true;
      if (n === normalizePath(path.join(sourcePath, 'SKILL.md'))) return true;
      if (n === normalizePath(targetPath)) return !rmSyncCalled;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: skillName, isDirectory: () => true } as any,
    ] as any);

    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => false,
      isDirectory: () => true,
    } as fs.Stats);

    // readFileSync throws for target SKILL.md (missing)
    mockFs.readFileSync.mockImplementation((p: fs.PathOrFileDescriptor) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(targetSkillMd)) {
        throw new Error('ENOENT: no such file or directory');
      }
      return 'source content';
    });

    mockFs.rmSync.mockImplementation(() => { rmSyncCalled = true; });
    mockFs.symlinkSync.mockImplementation(() => {});

    const result = installSkills(pluginRoot);

    expect(result.installedCount).toBe(1);
    expect(result.skills[0].installed).toBe(true);
    expect(mockFs.rmSync).toHaveBeenCalledWith(targetPath, { recursive: true, force: true });
  });

  // --- REQ-CODEX-011: Stale skill directory removal ---

  // @tests REQ-CODEX-011, SCN-CODEX-011-02
  it('stale skill directory is removed with recursive flag and reinstalled', () => {
    const skillName = 'tla-model-checking';
    const sourcePath = path.join(sourceDir, skillName);
    const targetPath = path.join(targetDir, skillName);
    const targetSkillMd = path.join(targetPath, 'SKILL.md');
    const sourceSkillMd = path.join(sourcePath, 'SKILL.md');

    let rmSyncCalled = false;
    mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(sourceDir)) return true;
      if (n === normalizePath(sourcePath)) return true;
      if (n === normalizePath(path.join(sourcePath, 'SKILL.md'))) return true;
      if (n === normalizePath(targetPath)) return !rmSyncCalled;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: skillName, isDirectory: () => true } as any,
    ] as any);

    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => false,
      isDirectory: () => true,
    } as fs.Stats);

    mockFs.readFileSync.mockImplementation((p: fs.PathOrFileDescriptor) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(targetSkillMd)) return 'old';
      if (n === normalizePath(sourceSkillMd)) return 'new';
      return '';
    });

    mockFs.rmSync.mockImplementation(() => { rmSyncCalled = true; });
    mockFs.symlinkSync.mockImplementation(() => {});

    const result = installSkills(pluginRoot);

    expect(mockFs.rmSync).toHaveBeenCalledWith(targetPath, { recursive: true, force: true });
    expect(result.skills[0].installed).toBe(true);
    expect(result.skills[0].symlinked).toBe(true);
  });

  // @tests REQ-CODEX-011, SCN-CODEX-011-03
  it('permission failure during skill removal returns error field', () => {
    const skillName = 'tla-model-checking';
    const sourcePath = path.join(sourceDir, skillName);
    const targetPath = path.join(targetDir, skillName);
    const targetSkillMd = path.join(targetPath, 'SKILL.md');
    const sourceSkillMd = path.join(sourcePath, 'SKILL.md');

    mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(sourceDir)) return true;
      if (n === normalizePath(sourcePath)) return true;
      if (n === normalizePath(path.join(sourcePath, 'SKILL.md'))) return true;
      if (n === normalizePath(targetPath)) return true;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: skillName, isDirectory: () => true } as any,
    ] as any);

    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => false,
      isDirectory: () => true,
    } as fs.Stats);

    mockFs.readFileSync.mockImplementation((p: fs.PathOrFileDescriptor) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(targetSkillMd)) return 'old';
      if (n === normalizePath(sourceSkillMd)) return 'new';
      return '';
    });

    const permissionError = new Error('EPERM: operation not permitted');
    (permissionError as NodeJS.ErrnoException).code = 'EPERM';
    mockFs.rmSync.mockImplementation(() => { throw permissionError; });

    const result = installSkills(pluginRoot);

    expect(result.success).toBe(false);
    expect(result.failedCount).toBe(1);
    expect(result.skills[0].installed).toBe(false);
    expect(result.skills[0].error).toContain('Failed to remove stale target');
    expect(mockFs.symlinkSync).not.toHaveBeenCalled();
  });
});
