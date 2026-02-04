import * as fs from 'fs';
import * as path from 'path';
import {
  enumerateSkills,
  installSkills,
  uninstallSkill,
  uninstallAllSkills,
  SkillInstallResult,
  InstallSkillsResult,
} from '../skills-installer';
import * as paths from '../paths';

jest.mock('fs');
jest.mock('../paths');

const mockFs = fs as jest.Mocked<typeof fs>;
const mockPaths = paths as jest.Mocked<typeof paths>;

// Helper to normalize paths for cross-platform comparison
function normalizePath(p: string): string {
  return p.split(path.sep).join('/');
}

describe('Skills Installer', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  describe('enumerateSkills', () => {
    it('returns empty array when source directory does not exist', () => {
      mockFs.existsSync.mockReturnValue(false);

      const result = enumerateSkills('/nonexistent/skills');

      expect(result).toEqual([] as any);
      expect(mockFs.existsSync).toHaveBeenCalledWith('/nonexistent/skills');
    });

    it('returns empty array when source directory has no skill directories', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readdirSync.mockReturnValue([
        { name: 'README.md', isDirectory: () => false } as any,
        { name: 'package.json', isDirectory: () => false } as any,
      ] as any);

      const result = enumerateSkills('/repo/skills');

      expect(result).toEqual([] as any);
    });

    it('returns skill names for directories containing SKILL.md', () => {
      mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
        const pathStr = normalizePath(p.toString());
        if (pathStr === '/repo/skills') return true;
        if (pathStr === '/repo/skills/tla-getting-started/SKILL.md') return true;
        if (pathStr === '/repo/skills/tla-model-checking/SKILL.md') return true;
        if (pathStr === '/repo/skills/not-a-skill/SKILL.md') return false;
        return false;
      });

      mockFs.readdirSync.mockReturnValue([
        { name: 'tla-getting-started', isDirectory: () => true } as any,
        { name: 'tla-model-checking', isDirectory: () => true } as any,
        { name: 'not-a-skill', isDirectory: () => true } as any,
        { name: 'README.md', isDirectory: () => false } as any,
      ] as any);

      const result = enumerateSkills('/repo/skills');

      expect(result).toEqual(['tla-getting-started', 'tla-model-checking'] as any);
    });

    it('returns sorted skill names', () => {
      mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
        const pathStr = normalizePath(p.toString());
        if (pathStr === '/repo/skills') return true;
        if (pathStr.endsWith('/SKILL.md')) return true;
        return false;
      });

      mockFs.readdirSync.mockReturnValue([
        { name: 'zebra-skill', isDirectory: () => true } as any,
        { name: 'alpha-skill', isDirectory: () => true } as any,
        { name: 'beta-skill', isDirectory: () => true } as any,
      ] as any);

      const result = enumerateSkills('/repo/skills');

      expect(result).toEqual(['alpha-skill', 'beta-skill', 'zebra-skill'] as any);
    });
  });

  describe('installSkills - global mode', () => {
    beforeEach(() => {
      mockPaths.getGlobalOpenCodeDir.mockReturnValue('/home/user/.config/opencode');
      mockPaths.getCanonicalDir.mockReturnValue('/home/user/.config/opencode/skills');
      mockPaths.ensureDir.mockImplementation(() => {});
    });

    it('creates symlinks for all skills in global mode', () => {
      mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
        const pathStr = normalizePath(p.toString());
        if (pathStr === '/usr/lib/node_modules/tlaplus-ai-tools/skills') return true;
        if (pathStr === '/usr/lib/node_modules/tlaplus-ai-tools/skills/skill-a') return true;
        if (pathStr === '/usr/lib/node_modules/tlaplus-ai-tools/skills/skill-b') return true;
        if (pathStr === '/usr/lib/node_modules/tlaplus-ai-tools/skills/skill-a/SKILL.md') return true;
        if (pathStr === '/usr/lib/node_modules/tlaplus-ai-tools/skills/skill-b/SKILL.md') return true;
        if (pathStr.includes('/.config/opencode/skills/')) return false;
        return false;
      });

      mockFs.readdirSync.mockImplementation((p: fs.PathLike, options?: any) => {
        return [
          { name: 'skill-a', isDirectory: () => true } as any,
          { name: 'skill-b', isDirectory: () => true } as any,
        ] as any;
      });

      mockFs.symlinkSync.mockImplementation(() => {});

      const result = installSkills('/usr/lib/node_modules/tlaplus-ai-tools');

      expect(normalizePath(result.sourceDir)).toBe('/usr/lib/node_modules/tlaplus-ai-tools/skills');
      expect(result.targetDir).toBe('/home/user/.config/opencode/skills');
      expect(result.success).toBe(true);
      expect(result.installedCount).toBe(2);
      expect(result.alreadyInstalledCount).toBe(0);
      expect(result.failedCount).toBe(0);
      expect(result.skills).toHaveLength(2);
      expect(result.skills[0].symlinked).toBe(true);
      expect(result.skills[1].symlinked).toBe(true);
      expect(mockFs.symlinkSync).toHaveBeenCalledTimes(2);
    });
  });




  describe('uninstallSkill', () => {
    it('returns false when skill is not installed', () => {
      mockFs.existsSync.mockReturnValue(false);

      const result = uninstallSkill('skill-a', '/project/.opencode/skills');

      expect(result).toBe(false);
      expect(mockFs.rmSync).not.toHaveBeenCalled();
    });

    it('removes skill directory and returns true', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.rmSync.mockImplementation(() => {});

      const result = uninstallSkill('skill-a', '/project/.opencode/skills');

      expect(result).toBe(true);
      const rmCall = mockFs.rmSync.mock.calls[0];
      expect(normalizePath(rmCall[0] as string)).toBe('/project/.opencode/skills/skill-a');
      expect(rmCall[1]).toEqual({ recursive: true, force: true });
    });
  });

  describe('uninstallAllSkills', () => {
    beforeEach(() => {
      mockPaths.getCanonicalDir.mockReturnValue('/project/.opencode/skills');
    });

    it('returns 0 when skills directory does not exist', () => {
      mockFs.existsSync.mockReturnValue(false);

      const result = uninstallAllSkills();

      expect(result).toBe(0);
      expect(mockFs.rmSync).not.toHaveBeenCalled();
    });

    it('removes all skill directories', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readdirSync.mockReturnValue([
        { name: 'skill-a', isDirectory: () => true, isSymbolicLink: () => false } as any,
        { name: 'skill-b', isDirectory: () => false, isSymbolicLink: () => true } as any,
        { name: 'README.md', isDirectory: () => false, isSymbolicLink: () => false } as any,
      ] as any);

      mockFs.rmSync.mockImplementation(() => {});

      const result = uninstallAllSkills();

      expect(result).toBe(2);
      expect(mockFs.rmSync).toHaveBeenCalledTimes(2);
    });

  });

  describe('idempotency', () => {
    beforeEach(() => {
      mockPaths.getGlobalOpenCodeDir.mockReturnValue('/home/user/.config/opencode');
      mockPaths.getCanonicalDir.mockReturnValue('/home/user/.config/opencode/skills');
      mockPaths.ensureDir.mockImplementation(() => {});
    });

    it('running installSkills twice produces same result', () => {
      const pluginRoot = '/usr/lib/node_modules/tlaplus-ai-tools';

      mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
        const pathStr = normalizePath(p.toString());
        const normalizedRoot = normalizePath(pluginRoot);
        if (pathStr === `${normalizedRoot}/skills`) return true;
        if (pathStr === `${normalizedRoot}/skills/skill-a`) return true;
        if (pathStr === `${normalizedRoot}/skills/skill-a/SKILL.md`) return true;
        if (pathStr.includes('/.config/opencode/skills/')) return false;
        return false;
      });

      mockFs.readdirSync.mockReturnValue([
        { name: 'skill-a', isDirectory: () => true } as any,
      ] as any);

      mockFs.symlinkSync.mockImplementation(() => {});

      const result1 = installSkills(pluginRoot);
      expect(result1.installedCount).toBe(1);

      mockFs.existsSync.mockImplementation((p: fs.PathLike) => {
        const pathStr = normalizePath(p.toString());
        const normalizedRoot = normalizePath(pluginRoot);
        if (pathStr === `${normalizedRoot}/skills`) return true;
        if (pathStr === `${normalizedRoot}/skills/skill-a`) return true;
        if (pathStr === `${normalizedRoot}/skills/skill-a/SKILL.md`) return true;
        if (pathStr === '/home/user/.config/opencode/skills/skill-a') return true;
        return true;
      });

      mockFs.lstatSync.mockReturnValue({
        isSymbolicLink: () => true,
        isDirectory: () => false,
        isFile: () => false,
      } as fs.Stats);

      mockFs.readlinkSync.mockReturnValue(`${pluginRoot}/skills/skill-a`);

      const result2 = installSkills(pluginRoot);
      expect(result2.installedCount).toBe(0);
      expect(result2.alreadyInstalledCount).toBe(1);
      expect(result2.success).toBe(true);
    });
  });
});
