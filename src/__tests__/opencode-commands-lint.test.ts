import * as fs from 'fs';
import * as path from 'path';

/**
 * OpenCode Commands Lint Tests
 * 
 * These tests validate the structure and content of merged command files
 * in commands/ directory (used by both Claude Code and OpenCode). They ensure:
 * - All expected command files exist
 * - Each has valid YAML frontmatter with required keys for both platforms
 * - Each references the appropriate MCP tools
 * - Each includes usage examples and @ handling notes
 * - Documentation accurately reflects command support
 * - OpenCode marker strings are present for E2E validation
 * - No positional $N tokens (cross-platform compatibility)
 */

const COMMANDS_DIR = path.join(__dirname, '../../commands');
const OPENCODE_DOC = path.join(__dirname, '../../OPENCODE.md');

// Expected command files (from plan)
const EXPECTED_COMMANDS = [
  'tla-parse.md',
  'tla-symbols.md',
  'tla-smoke.md',
  'tla-check.md',
  'tla-review.md',
  'tla-setup.md'
];

// MCP tool requirements per command (from plan lines 661-668)
const REQUIRED_MCP_TOOLS: Record<string, string[]> = {
  'tla-parse.md': ['sany_parse'],
  'tla-symbols.md': ['sany_parse', 'sany_symbol'],
  'tla-smoke.md': ['tlc_smoke'],
  'tla-check.md': ['tlc_check'],
  'tla-review.md': ['sany_parse', 'sany_symbol', 'tlc_smoke'],
  'tla-setup.md': [] // No MCP tools, validation only
};

/**
 * Minimal frontmatter parser (plan lines 655-659)
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
    const match = line.match(/^(\w+):\s*(.+)$/);
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

describe('OpenCode Commands Lint Tests', () => {
  describe('Command Files Existence', () => {
    it('should have commands directory', () => {
      expect(fileExists(COMMANDS_DIR)).toBe(true);
    });

    it('should have exactly 6 expected command files', () => {
      if (!fileExists(COMMANDS_DIR)) {
        throw new Error('commands directory does not exist');
      }

      const actualFiles = fs.readdirSync(COMMANDS_DIR)
        .filter(f => f.endsWith('.md'));
      
      if (actualFiles.length !== EXPECTED_COMMANDS.length) {
        const missing = EXPECTED_COMMANDS.filter(cmd => !actualFiles.includes(cmd));
        const extra = actualFiles.filter(f => !EXPECTED_COMMANDS.includes(f));
        
        let message = `Expected exactly ${EXPECTED_COMMANDS.length} command files, found ${actualFiles.length}.`;
        if (missing.length > 0) {
          message += `\nMissing: ${missing.join(', ')}`;
        }
        if (extra.length > 0) {
          message += `\nUnexpected: ${extra.join(', ')}`;
        }
        throw new Error(message);
      }
      
      expect(actualFiles.length).toBe(EXPECTED_COMMANDS.length);
    });

    EXPECTED_COMMANDS.forEach(commandFile => {
      it(`should have ${commandFile}`, () => {
        const filePath = path.join(COMMANDS_DIR, commandFile);
        if (!fileExists(filePath)) {
          throw new Error(`Missing command file: ${commandFile}. Expected at ${filePath}`);
        }
        expect(fileExists(filePath)).toBe(true);
      });
    });

    it('should have filenames matching command names', () => {
      if (!fileExists(COMMANDS_DIR)) {
        throw new Error('commands directory does not exist');
      }

      const actualFiles = fs.readdirSync(COMMANDS_DIR)
        .filter(f => f.endsWith('.md'));
      
      const mismatches: string[] = [];
      
      actualFiles.forEach(filename => {
        const filePath = path.join(COMMANDS_DIR, filename);
        const content = readFile(filePath);
        const frontmatter = parseFrontmatter(content);
        
        // Extract command name from filename (e.g., "tla-parse.md" -> "tla-parse")
        const expectedCommandName = filename.replace('.md', '');
        
        // Check if content references the command with /command-name
        const commandPattern = new RegExp(`/${expectedCommandName}\\b`);
        if (!commandPattern.test(content)) {
          mismatches.push(`${filename}: does not reference /${expectedCommandName} in content`);
        }
      });
      
      if (mismatches.length > 0) {
        throw new Error(`Filename/command name mismatches:\n${mismatches.join('\n')}`);
      }
      
      expect(mismatches.length).toBe(0);
    });
  });

  describe('Frontmatter Validation', () => {
    EXPECTED_COMMANDS.forEach(commandFile => {
      describe(commandFile, () => {
        let content: string;
        let frontmatter: Record<string, string>;

        beforeAll(() => {
          const filePath = path.join(COMMANDS_DIR, commandFile);
          if (fileExists(filePath)) {
            content = readFile(filePath);
            frontmatter = parseFrontmatter(content);
          }
        });

        it('should have valid YAML frontmatter', () => {
          expect(Object.keys(frontmatter).length).toBeGreaterThan(0);
        });

        it('should have name key matching filename', () => {
          const expectedName = commandFile.replace('.md', '');
          expect(content).toMatch(new RegExp(`^name:\\s*${expectedName}\\s*$`, 'm'));
        });

        it('should have description key', () => {
          expect(frontmatter.description).toBeDefined();
          expect(frontmatter.description.length).toBeGreaterThan(0);
          expect(content).toMatch(/^description:\s*.+$/m);
        });

        it('should have agent: build', () => {
          expect(frontmatter.agent).toBe('build');
          expect(content).toMatch(/^agent:\s*build\s*$/m);
        });

        it('should have allowed-tools key', () => {
          expect(content).toMatch(/^allowed-tools:\s*\[.+\]$/m);
        });
      });
    });
  });

  describe('MCP Tool References', () => {
    EXPECTED_COMMANDS.forEach(commandFile => {
      describe(commandFile, () => {
        let content: string;
        const requiredTools = REQUIRED_MCP_TOOLS[commandFile];

        beforeAll(() => {
          const filePath = path.join(COMMANDS_DIR, commandFile);
          if (fileExists(filePath)) {
            content = readFile(filePath);
          }
        });

        if (requiredTools.length > 0) {
          requiredTools.forEach(tool => {
            it(`should reference ${tool}`, () => {
              expect(content).toContain(tool);
  });

  describe('OpenCode Marker Contract', () => {
    const REQUIRED_MARKERS: Record<string, string[]> = {
      'tla-parse.md': ['Spec path:'],
      'tla-symbols.md': ['Spec path:', 'CFG written:'],
      'tla-smoke.md': ['Spec path:', 'CFG used:'],
      'tla-check.md': ['Spec path:', 'CFG used:'],
      'tla-review.md': ['Spec path:', 'TLA+ SPECIFICATION REVIEW'],
      'tla-setup.md': ['TLA+ TOOLS SETUP & VERIFICATION']
    };

    EXPECTED_COMMANDS.forEach(commandFile => {
      describe(commandFile, () => {
        let content: string;
        const requiredMarkers = REQUIRED_MARKERS[commandFile];

        beforeAll(() => {
          const filePath = path.join(COMMANDS_DIR, commandFile);
          if (fileExists(filePath)) {
            content = readFile(filePath);
          }
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
    EXPECTED_COMMANDS.forEach(commandFile => {
      describe(commandFile, () => {
        let content: string;

        beforeAll(() => {
          const filePath = path.join(COMMANDS_DIR, commandFile);
          if (fileExists(filePath)) {
            content = readFile(filePath);
          }
        });

        it('should not contain positional $N tokens', () => {
          // Check no $0, $1, $2, etc. (allow $ARGUMENTS)
          const positionalMatch = content.match(/\$[0-9]\b/);
          if (positionalMatch) {
            throw new Error(`${commandFile} uses positional variable ${positionalMatch[0]} - use $ARGUMENTS instead`);
          }
        });
      });
    });
  });

  describe('Repository Configuration', () => {
    it('opencode.json should exist at repo root with MCP config', () => {
      const configPath = path.join(__dirname, '../../opencode.json');
      expect(fileExists(configPath)).toBe(true);
      
      const configContent = readFile(configPath);
      const config = JSON.parse(configContent);
      
      expect(config.mcp).toBeDefined();
      expect(config.mcp.tlaplus).toBeDefined();
    });

    it('OPENCODE.md should document OPENCODE_CONFIG_DIR', () => {
      const docPath = path.join(__dirname, '../../OPENCODE.md');
      if (fileExists(docPath)) {
        const content = readFile(docPath);
        expect(content).toMatch(/OPENCODE_CONFIG_DIR/);
      }
    });
  });
          });
        } else {
          it('should not require MCP tools (validation only)', () => {
            // tla-setup is validation only, no MCP tools required
            expect(commandFile).toBe('tla-setup.md');
          });
        }
      });
    });
  });

  describe('Usage Examples and @ Handling', () => {
    EXPECTED_COMMANDS.forEach(commandFile => {
      describe(commandFile, () => {
        let content: string;

        beforeAll(() => {
          const filePath = path.join(COMMANDS_DIR, commandFile);
          if (fileExists(filePath)) {
            content = readFile(filePath);
          }
        });

        // tla-setup doesn't take file arguments, so skip these tests
        if (commandFile !== 'tla-setup.md') {
          it('should include usage example with plain path', () => {
            // Look for example invocations like: /tla-parse test-specs/Counter.tla
            const commandName = commandFile.replace('.md', '');
            const plainPathPattern = new RegExp(`/${commandName}\\s+[^@\\s][^\\s]*\\.tla`);
            expect(content).toMatch(plainPathPattern);
          });

          it('should include note about @ handling', () => {
            // Check for @ stripping or @ handling documentation
            const hasAtHandling = 
              content.includes('Strip Leading @ Symbol') ||
              content.includes('leading `@`') ||
              content.includes('@$1') ||
              content.includes('@ prefix') ||
              content.includes('strip') && content.includes('@');
            
            expect(hasAtHandling).toBe(true);
          });
        }

        it('should include "Preferred" usage example or equivalent', () => {
          // Look for "Preferred" marker or clear usage examples
          const hasPreferredOrExample = 
            content.includes('Preferred') ||
            content.includes('Usage:') ||
            content.includes('Example') ||
            content.includes('Test Invocations');
          
          expect(hasPreferredOrExample).toBe(true);
        });
      });
    });
  });

  describe('Documentation Accuracy', () => {
    it('OPENCODE.md should not claim commands are unsupported', () => {
      if (!fileExists(OPENCODE_DOC)) {
        return;
      }

      const content = readFile(OPENCODE_DOC);
      
      // Check for outdated claims like "Commands | ❌ Not Supported"
      const unsupportedPatterns = [
        /Commands\*\*\s*\|\s*❌\s*Not Supported/i,
        /Commands\*\*\s*\|\s*❌/i,
        /\|\s*Commands\s*\|\s*❌/i,
        /Commands.*Not Supported/i
      ];
      
      const foundPatterns = unsupportedPatterns
        .map((pattern, idx) => ({ pattern, idx, match: pattern.test(content) }))
        .filter(result => result.match);
      
      if (foundPatterns.length > 0) {
        const patternDescriptions = foundPatterns.map(r => 
          `Pattern ${r.idx + 1}: ${unsupportedPatterns[r.idx]}`
        ).join('\n');
        
        throw new Error(
          `OPENCODE.md contains outdated "Commands not supported" claims.\n` +
          `Found patterns:\n${patternDescriptions}\n\n` +
          `Action: Update OPENCODE.md to reflect that commands ARE supported.\n` +
          `Expected: Commands should be marked as ✅ Supported with examples.`
        );
      }
      
      expect(foundPatterns.length).toBe(0);
    });

    it('OPENCODE.md should document command support if it exists', () => {
      if (fileExists(OPENCODE_DOC)) {
        const content = readFile(OPENCODE_DOC);
        
        // If commands exist, docs should mention them
        const commandsExist = EXPECTED_COMMANDS.some(cmd => 
          fileExists(path.join(COMMANDS_DIR, cmd))
        );
        
        if (commandsExist) {
          // Should have some mention of commands being available
          const mentionsCommands = 
            content.includes('/tla-parse') ||
            content.includes('/tla-check') ||
            content.includes('custom commands') ||
            content.includes('Commands') && content.includes('✅');
          
          expect(mentionsCommands).toBe(true);
        }
      }
    });
  });

  describe('Command Content Quality', () => {
    EXPECTED_COMMANDS.forEach(commandFile => {
      describe(commandFile, () => {
        let content: string;

        beforeAll(() => {
          const filePath = path.join(COMMANDS_DIR, commandFile);
          if (fileExists(filePath)) {
            content = readFile(filePath);
          }
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
          // Commands should validate .tla extension and file existence
          const hasValidation = 
            content.includes('.tla') &&
            (content.includes('validate') || 
             content.includes('check') || 
             content.includes('exists'));
          
          expect(hasValidation).toBe(true);
        });
      });
    });
  });
});
