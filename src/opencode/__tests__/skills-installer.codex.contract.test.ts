// Spec: docs/codex-fixes/spec.md
// Contract: docs/codex-fixes/contract.md (installSkills)
// Testing: docs/codex-fixes/testing.md
//
// Contract tests for installSkills stale handling.

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

describe('installSkills - Contract Tests (Codex)', () => {
  const pluginRoot = '/usr/lib/node_modules/tlaplus-ai-tools';
  const sourceDir = path.join(pluginRoot, 'skills');
  const targetDir = '/home/user/.config/opencode/skills';

  beforeEach(() => {
    jest.clearAllMocks();
    mockPaths.getGlobalOpenCodeDir.mockReturnValue('/home/user/.config/opencode');
    mockPaths.getCanonicalDir.mockReturnValue(targetDir);
    mockPaths.ensureDir.mockImplementation(() => {});
  });

  // @tests-contract REQ-CODEX-010
  it('stale SKILL.md triggers reinstall (installed: true)', () => {
    const skillName = 'skill-a';
    const sourcePath = path.join(sourceDir, skillName);
    const targetPath = path.join(targetDir, skillName);
    const sourceSkillMd = path.join(sourcePath, 'SKILL.md');
    const targetSkillMd = path.join(targetPath, 'SKILL.md');

    let rmCalled = false;
    mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(sourceDir)) return true;
      if (n === normalizePath(sourcePath)) return true;
      if (n === normalizePath(path.join(sourcePath, 'SKILL.md'))) return true;
      if (n === normalizePath(targetPath)) return !rmCalled;
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

    mockFs.rmSync.mockImplementation(() => { rmCalled = true; });
    mockFs.symlinkSync.mockImplementation(() => {});

    const result = installSkills(pluginRoot);

    expect(result.skills[0].installed).toBe(true);
  });

  // @tests-contract REQ-CODEX-011
  it('stale skill directory removed then reinstalled', () => {
    const skillName = 'skill-a';
    const sourcePath = path.join(sourceDir, skillName);
    const targetPath = path.join(targetDir, skillName);
    const sourceSkillMd = path.join(sourcePath, 'SKILL.md');
    const targetSkillMd = path.join(targetPath, 'SKILL.md');

    let rmCalled = false;
    mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(sourceDir)) return true;
      if (n === normalizePath(sourcePath)) return true;
      if (n === normalizePath(path.join(sourcePath, 'SKILL.md'))) return true;
      if (n === normalizePath(targetPath)) return !rmCalled;
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

    mockFs.rmSync.mockImplementation(() => { rmCalled = true; });
    mockFs.symlinkSync.mockImplementation(() => {});

    const result = installSkills(pluginRoot);

    // Contract: stale skill dir removed, new symlink created
    expect(result.skills[0].installed).toBe(true);
    expect(result.skills[0].error).toBeUndefined();
  });
});
