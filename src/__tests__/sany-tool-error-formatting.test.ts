import { ServerConfig } from '../types';
import * as fs from 'fs';
import * as path from 'path';

jest.mock('../utils/symbols');
jest.mock('../utils/sany');
jest.mock('fs');

import { registerSanyTools } from '../tools/sany';
import { extractSymbols } from '../utils/symbols';
import { runSanyParse, parseSanyOutput } from '../utils/sany';

describe('SANY Tool Error Formatting', () => {
  let mockExtractSymbols: jest.MockedFunction<typeof extractSymbols>;
  let mockRunSanyParse: jest.MockedFunction<typeof runSanyParse>;
  let mockParseSanyOutput: jest.MockedFunction<typeof parseSanyOutput>;
  let mockFsExistsSync: jest.MockedFunction<typeof fs.existsSync>;

  beforeEach(() => {
    jest.clearAllMocks();
    
    mockExtractSymbols = extractSymbols as jest.MockedFunction<typeof extractSymbols>;
    mockRunSanyParse = runSanyParse as jest.MockedFunction<typeof runSanyParse>;
    mockParseSanyOutput = parseSanyOutput as jest.MockedFunction<typeof parseSanyOutput>;
    mockFsExistsSync = fs.existsSync as jest.MockedFunction<typeof fs.existsSync>;
    
    mockFsExistsSync.mockReturnValue(true);
  });

  describe('tlaplus_mcp_sany_symbol XMLExporter error formatting', () => {
    it('formats XMLEXPORTER_USAGE_ERROR with suggested actions', async () => {
      const mockServer = {
        handlers: new Map(),
        tool: function(name: string, description: string, schema: any, handler: any) {
          this.handlers.set(name, handler);
        }
      };

      const config: ServerConfig = {
        toolsDir: '/fake/tools',
        workingDir: '/fake/work',
        javaHome: '/fake/java',
        kbDir: null,
        verbose: false,
        http: false,
        port: 3000
      };

      mockExtractSymbols.mockRejectedValue(
        new Error('Only one TLA file to check allowed!')
      );

      await registerSanyTools(mockServer as any, config);

      const symbolHandler = mockServer.handlers.get('tlaplus_mcp_sany_symbol');
      expect(symbolHandler).toBeDefined();

      const response = await symbolHandler({ fileName: '/fake/work/Test.tla' });

      expect(response.content).toBeDefined();
      expect(response.content.length).toBeGreaterThan(0);
      
      const text = response.content[0].text;
      
      expect(text).toContain('Error [XMLEXPORTER_USAGE_ERROR]');
      expect(text).toContain('npm run setup');
      expect(text).toContain('v1.8.0');
      expect(text).not.toContain('Error [FILE_IO_ERROR]');
    });

    it('includes all required suggested actions for XMLEXPORTER_USAGE_ERROR', async () => {
      const mockServer = {
        handlers: new Map(),
        tool: function(name: string, description: string, schema: any, handler: any) {
          this.handlers.set(name, handler);
        }
      };

      const config: ServerConfig = {
        toolsDir: '/fake/tools',
        workingDir: '/fake/work',
        kbDir: null,
        javaHome: null,
        verbose: false,
        http: false,
        port: 3000
      };

      mockExtractSymbols.mockRejectedValue(
        new Error('Only one TLA file to check allowed!')
      );

      await registerSanyTools(mockServer as any, config);

      const symbolHandler = mockServer.handlers.get('tlaplus_mcp_sany_symbol');

      const response = await symbolHandler({ fileName: '/fake/work/Test.tla' });
      const text = response.content[0].text;
      
      expect(text).toContain('Suggested Actions:');
      expect(text).toContain('Run `npm run setup` to install pinned tools (v1.8.0)');
      expect(text).toContain('Verify `tools/tla2tools.jar` matches v1.8.0 with correct checksum');
      expect(text).toContain('If checksum mismatch: delete `tools/tla2tools.jar` and re-run `npm run setup`');
      expect(text).toContain('This error indicates XMLExporter argument incompatibility with your TLA+ tools version');
    });

    it('formats other errors without XMLEXPORTER_USAGE_ERROR suggestions', async () => {
      const mockServer = {
        handlers: new Map(),
        tool: function(name: string, description: string, schema: any, handler: any) {
          this.handlers.set(name, handler);
        }
      };

      const config: ServerConfig = {
        toolsDir: '/fake/tools',
        workingDir: '/fake/work',
        kbDir: null,
        javaHome: null,
        verbose: false,
        http: false,
        port: 3000
      };

      const fileError = new Error('File not found') as NodeJS.ErrnoException;
      fileError.code = 'ENOENT';
      mockExtractSymbols.mockRejectedValue(fileError);

      await registerSanyTools(mockServer as any, config);

      const symbolHandler = mockServer.handlers.get('tlaplus_mcp_sany_symbol');

      const response = await symbolHandler({ fileName: '/fake/work/Missing.tla' });
      const text = response.content[0].text;
      
      expect(text).toContain('Error [FILE_NOT_FOUND]');
      expect(text).not.toContain('npm run setup');
      expect(text).not.toContain('XMLExporter');
    });
  });

  describe('tlaplus_mcp_sany_parse error formatting', () => {
    it('formats errors with error codes', async () => {
      const mockServer = {
        handlers: new Map(),
        tool: function(name: string, description: string, schema: any, handler: any) {
          this.handlers.set(name, handler);
        }
      };

      const config: ServerConfig = {
        toolsDir: '/fake/tools',
        workingDir: '/fake/work',
        kbDir: null,
        javaHome: null,
        verbose: false,
        http: false,
        port: 3000
      };

      mockRunSanyParse.mockRejectedValue(
        new Error('Java executable not found')
      );

      await registerSanyTools(mockServer as any, config);

      const parseHandler = mockServer.handlers.get('tlaplus_mcp_sany_parse');
      expect(parseHandler).toBeDefined();

      const response = await parseHandler({ fileName: '/fake/work/Test.tla' });
      const text = response.content[0].text;
      
      expect(text).toContain('Error [JAVA_NOT_FOUND]');
      expect(text).toContain('Suggested Actions:');
    });
  });

  describe('Error code classification in tool responses', () => {
    it('correctly classifies XMLExporter errors in symbol extraction', async () => {
      const mockServer = {
        handlers: new Map(),
        tool: function(name: string, description: string, schema: any, handler: any) {
          this.handlers.set(name, handler);
        }
      };

      const config: ServerConfig = {
        toolsDir: '/fake/tools',
        workingDir: '/fake/work',
        kbDir: null,
        javaHome: null,
        verbose: false,
        http: false,
        port: 3000
      };

      mockExtractSymbols.mockRejectedValue(
        new Error('SANY failed: Only one TLA file to check allowed! Check your arguments.')
      );

      await registerSanyTools(mockServer as any, config);

      const symbolHandler = mockServer.handlers.get('tlaplus_mcp_sany_symbol');

      const response = await symbolHandler({ fileName: '/fake/work/Test.tla' });
      const text = response.content[0].text;
      
      expect(text).toMatch(/Error \[XMLEXPORTER_USAGE_ERROR\]/);
      expect(text).not.toMatch(/Error \[FILE_IO_ERROR\]/);
    });

    it('does not misclassify generic errors as XMLEXPORTER_USAGE_ERROR', async () => {
      const mockServer = {
        handlers: new Map(),
        tool: function(name: string, description: string, schema: any, handler: any) {
          this.handlers.set(name, handler);
        }
      };

      const config: ServerConfig = {
        toolsDir: '/fake/tools',
        workingDir: '/fake/work',
        kbDir: null,
        javaHome: null,
        verbose: false,
        http: false,
        port: 3000
      };

      mockExtractSymbols.mockRejectedValue(
        new Error('Unknown parsing error')
      );

      await registerSanyTools(mockServer as any, config);

      const symbolHandler = mockServer.handlers.get('tlaplus_mcp_sany_symbol');

      const response = await symbolHandler({ fileName: '/fake/work/Test.tla' });
      const text = response.content[0].text;
      
      expect(text).not.toContain('Error [XMLEXPORTER_USAGE_ERROR]');
      expect(text).toContain('Error [FILE_IO_ERROR]');
    });
  });
});
