import * as fs from 'fs';
import * as path from 'path';

/**
 * Operational Skills Lint Tests
 *
 * These tests validate the structure and content of operational skill files
 * in skills/ directory. They ensure:
 * - All expected operational skill files exist
 * - Each has valid YAML frontmatter with required keys
 * - Each references the appropriate MCP tools using full names
 * - Each includes usage examples and @ handling notes
 * - Marker strings are present for E2E validation
 * - No positional $N tokens (cross-platform compatibility)
 */

const SKILLS_DIR = path.join(__dirname, '../../skills');

// Expected operational skill directories (formerly commands)
const EXPECTED_SKILLS = [
  'tla-parse',
  'tla-symbols',
  'tla-smoke',
  'tla-check',
  'tla-review',
  'tla-setup'
];

// MCP tool requirements per skill (using full MCP tool names)
const REQUIRED_MCP_TOOLS: Record<string, string[]> = {
  'tla-parse': ['mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse'],
  'tla-symbols': ['mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse', 'mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_symbol'],
  'tla-smoke': ['mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke'],
  'tla-check': ['mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check'],
  'tla-review': ['mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse', 'mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_symbol', 'mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke'],
  'tla-setup': ['mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_modules', 'mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse']
};

/**
 * Minimal frontmatter parser
 * Reads between first two --- lines and extracts key: value pairs
 */
function parseFrontmatter(content: string): Record<string, string> {
  const normalizedContent = content.replace(/^\ufeff/, '');
  const frontmatterMatch = normalizedContent.match(/^---\r?\n([\s\S]*?)\r?\n---/);
  if (!frontmatterMatch) {
    return {};
  }

  const frontmatterText = frontmatterMatch[1];
  const result: Record<string, string> = {};

  // Parse simple key: value pairs (single-line only)
  const lines = frontmatterText.split(/\r?\n/);
  for (const line of lines) {
    const match = line.match(/^([\w-]+):\s*(.+)$/);
    if (match) {
      const [, key, value] = match;
      result[key] = value.trim();
    }
  }

  return result;
}

/**
 * Check if file exists (helper)
 */
function fileExists(filePath: string): boolean {
  try {
    return fs.existsSync(filePath);
  } catch {
    return false;
  }
}

/**
 * Read file content (helper)
 */
function readFile(filePath: string): string {
  return fs.readFileSync(filePath, 'utf-8');
}

describe('Operational Skills Lint Tests', () => {
  describe('Skill Files Existence', () => {
    it('should have skills directory', () => {
      expect(fileExists(SKILLS_DIR)).toBe(true);
    });

    it('should not have commands directory (commands migrated to skills)', () => {
      const commandsDir = path.join(__dirname, '../../commands');
      expect(fileExists(commandsDir)).toBe(false);
    });

    it('should have all expected operational skill directories', () => {
      const missing = EXPECTED_SKILLS.filter(skill =>
        !fileExists(path.join(SKILLS_DIR, skill, 'SKILL.md'))
      );

      if (missing.length > 0) {
        throw new Error(`Missing operational skill files:\n${missing.map(s => `  skills/${s}/SKILL.md`).join('\n')}`);
      }

      expect(missing.length).toBe(0);
    });

    EXPECTED_SKILLS.forEach(skillName => {
      it(`should have ${skillName}/SKILL.md`, () => {
        const filePath = path.join(SKILLS_DIR, skillName, 'SKILL.md');
        if (!fileExists(filePath)) {
          throw new Error(`Missing skill file: ${skillName}/SKILL.md. Expected at ${filePath}`);
        }
        expect(fileExists(filePath)).toBe(true);
      });
    });

    it('should have skill names matching frontmatter names', () => {
      const mismatches: string[] = [];

      EXPECTED_SKILLS.forEach(skillName => {
        const filePath = path.join(SKILLS_DIR, skillName, 'SKILL.md');
        if (fileExists(filePath)) {
          const content = readFile(filePath);
          const frontmatter = parseFrontmatter(content);

          if (frontmatter.name !== skillName) {
            mismatches.push(`${skillName}: frontmatter name "${frontmatter.name}" does not match directory name "${skillName}"`);
          }
        }
      });

      if (mismatches.length > 0) {
        throw new Error(`Name mismatches:\n${mismatches.join('\n')}`);
      }

      expect(mismatches.length).toBe(0);
    });
  });

  describe('Frontmatter Validation', () => {
    EXPECTED_SKILLS.forEach(skillName => {
      describe(skillName, () => {
        let content: string;
        let frontmatter: Record<string, string>;

        beforeAll(() => {
          const filePath = path.join(SKILLS_DIR, skillName, 'SKILL.md');
          expect(fileExists(filePath)).toBe(true);
          content = readFile(filePath);
          frontmatter = parseFrontmatter(content);
        });

        it('should have valid YAML frontmatter', () => {
          expect(Object.keys(frontmatter).length).toBeGreaterThan(0);
        });

        it('should have name key matching skill directory', () => {
          expect(content).toMatch(new RegExp(`^name:\\s*${skillName}\\s*$`, 'm'));
        });

        it('should have description key', () => {
          expect(frontmatter.description).toBeDefined();
          expect(frontmatter.description.length).toBeGreaterThan(0);
          expect(content).toMatch(/^description:\s*.+$/m);
        });

        it('should have version key', () => {
          expect(frontmatter.version).toBeDefined();
          expect(content).toMatch(/^version:\s*.+$/m);
        });

        it('should NOT have agent: build (skills run in main context)', () => {
          expect(frontmatter.agent).toBeUndefined();
          expect(content).not.toMatch(/^agent:\s*build\s*$/m);
        });

        it('should have allowed-tools key', () => {
          expect(content).toMatch(/^allowed-tools:\s*\[.+\]$/m);
        });
      });
    });
  });

  describe('MCP Tool References', () => {
    EXPECTED_SKILLS.forEach(skillName => {
      describe(skillName, () => {
        let content: string;
        const requiredTools = REQUIRED_MCP_TOOLS[skillName];

        beforeAll(() => {
          const filePath = path.join(SKILLS_DIR, skillName, 'SKILL.md');
          expect(fileExists(filePath)).toBe(true);
          content = readFile(filePath);
        });

        requiredTools.forEach(tool => {
          it(`should reference ${tool}`, () => {
            expect(content).toContain(tool);
          });
        });

        it('should use full MCP tool names (not short names)', () => {
          // Ensure no short MCP tool names are used in implementation sections
          const implSection = content.split(/##\s+Implementation/i)[1];
          if (implSection) {
            // Check for short names that should be full names
            const shortNamePatterns = [
              /(?<!\w)tlaplus_mcp_sany_parse(?!\w)/,
              /(?<!\w)tlaplus_mcp_sany_symbol(?!\w)/,
              /(?<!\w)tlaplus_mcp_sany_modules(?!\w)/,
              /(?<!\w)tlaplus_mcp_tlc_check(?!\w)/,
              /(?<!\w)tlaplus_mcp_tlc_smoke(?!\w)/,
              /(?<!\w)tlaplus_mcp_tlc_explore(?!\w)/,
            ];

            shortNamePatterns.forEach(pattern => {
              const match = implSection.match(pattern);
              if (match) {
                // Verify it's the full name (prefixed with mcp__plugin_tlaplus_tlaplus__)
                const fullPattern = new RegExp(`mcp__plugin_tlaplus_tlaplus__${match[0]}`);
                const lineWithMatch = implSection.split('\n').find(line => pattern.test(line));
                if (lineWithMatch && !fullPattern.test(lineWithMatch)) {
                  throw new Error(`${skillName}: Uses short MCP tool name "${match[0]}" in implementation. Use full name "mcp__plugin_tlaplus_tlaplus__${match[0]}" instead.`);
                }
              }
            });
          }
        });
      });
    });
  });

  describe('Marker Contract', () => {
    const REQUIRED_MARKERS: Record<string, string[]> = {
      'tla-parse': ['Spec path:'],
      'tla-symbols': ['Spec path:', 'CFG written:'],
      'tla-smoke': ['Spec path:', 'CFG used:'],
      'tla-check': ['Spec path:', 'CFG used:'],
      'tla-review': ['Spec path:', 'TLA+ SPECIFICATION REVIEW'],
      'tla-setup': ['TLA+ TOOLS SETUP & VERIFICATION']
    };

    EXPECTED_SKILLS.forEach(skillName => {
      describe(skillName, () => {
        let content: string;
        const requiredMarkers = REQUIRED_MARKERS[skillName];

        beforeAll(() => {
          const filePath = path.join(SKILLS_DIR, skillName, 'SKILL.md');
          expect(fileExists(filePath)).toBe(true);
          content = readFile(filePath);
        });

        requiredMarkers.forEach(marker => {
          it(`should contain marker: "${marker}"`, () => {
            expect(content).toContain(marker);
          });
        });
      });
    });
  });

  describe('Cross-Platform Compatibility', () => {
    EXPECTED_SKILLS.forEach(skillName => {
      describe(skillName, () => {
        let content: string;

        beforeAll(() => {
          const filePath = path.join(SKILLS_DIR, skillName, 'SKILL.md');
          expect(fileExists(filePath)).toBe(true);
          content = readFile(filePath);
        });

        it('should not contain positional $N tokens', () => {
          // Check no $0, $1, $2, etc. (positional tokens are not supported in skills)
          const positionalMatch = content.match(/\$[0-9]\b/);
          if (positionalMatch) {
            throw new Error(`${skillName} uses positional variable ${positionalMatch[0]} - not supported in skills`);
          }
        });

        it('should not reference $ARGUMENTS (skills use contextual language)', () => {
          // Skills should not use $ARGUMENTS since they run in main context
          if (content.includes('$ARGUMENTS')) {
            throw new Error(`${skillName} references $ARGUMENTS which is not available in skills. Use contextual language like "the argument to this skill" instead.`);
          }
        });
      });
    });
  });

  describe('Repository Configuration', () => {
    it('plugin.json should not reference commands directory', () => {
      const pluginPath = path.join(__dirname, '../../.claude-plugin/plugin.json');
      expect(fileExists(pluginPath)).toBe(true);

      const pluginContent = readFile(pluginPath);
      const plugin = JSON.parse(pluginContent);

      expect(plugin.commands).toBeUndefined();
      expect(plugin.skills).toBeDefined();
    });
  });

  describe('Skill Content Quality', () => {
    EXPECTED_SKILLS.forEach(skillName => {
      describe(skillName, () => {
        let content: string;

        beforeAll(() => {
          const filePath = path.join(SKILLS_DIR, skillName, 'SKILL.md');
          expect(fileExists(filePath)).toBe(true);
          content = readFile(filePath);
        });

        it('should have implementation section', () => {
          expect(content).toMatch(/##\s+Implementation/i);
        });

        it('should have step-by-step instructions', () => {
          // Look for numbered steps or clear structure
          const hasSteps =
            content.includes('Step 1') ||
            content.includes('**1.') ||
            content.match(/\d+\.\s+\w+/);

          expect(hasSteps).toBeTruthy();
        });

        it('should validate file path', () => {
          // Skills should validate .tla extension and file existence
          const hasValidation =
            content.includes('.tla') &&
            (content.includes('validate') ||
             content.includes('check') ||
             content.includes('exists'));

          expect(hasValidation).toBe(true);
        });

        it('should include anti-fallback warning', () => {
          // All operational skills should warn against using Bash for Java/TLC
          expect(content).toMatch(/Never fall back to running Java/i);
        });
      });
    });
  });

  describe('Usage Examples and @ Handling', () => {
    EXPECTED_SKILLS.forEach(skillName => {
      describe(skillName, () => {
        let content: string;

        beforeAll(() => {
          const filePath = path.join(SKILLS_DIR, skillName, 'SKILL.md');
          expect(fileExists(filePath)).toBe(true);
          content = readFile(filePath);
        });

        // tla-setup doesn't take file arguments, so skip these tests
        if (skillName !== 'tla-setup') {
          it('should include usage example with plain path', () => {
            // Look for example invocations like: /tla-parse test-specs/Counter.tla
            const plainPathPattern = new RegExp(`/${skillName}\\s+[^@\\s][^\\s]*\\.tla`);
            expect(content).toMatch(plainPathPattern);
          });

          it('should include note about @ handling', () => {
            // Check for @ stripping or @ handling documentation
            const hasAtHandling =
              content.includes('leading `@`') ||
              content.includes('@ prefix') ||
              (content.includes('strip') && content.includes('@'));

            expect(hasAtHandling).toBe(true);
          });
        }

        it('should include usage section', () => {
          const hasUsage =
            content.includes('## Usage') ||
            content.includes('Usage:') ||
            content.includes('Example');

          expect(hasUsage).toBe(true);
        });
      });
    });
  });
});
