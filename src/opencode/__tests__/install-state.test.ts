import * as fs from 'fs';
import * as path from 'path';
import {
  getMarkerPath,
  readInstallState,
  writeInstallState,
  shouldPromptInstall,
  InstallStateMarker,
} from '../install-state';

jest.mock('fs');
jest.mock('child_process');

const mockFs = fs as jest.Mocked<typeof fs>;

describe('install-state', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  describe('getMarkerPath', () => {
    it('should return global path', () => {
      const result = getMarkerPath('/global/dir');
      expect(result).toBe('/global/dir/.tlaplus-install-state.json');
    });
  });

  describe('readInstallState', () => {
    it('should return null if file does not exist', () => {
      mockFs.existsSync.mockReturnValue(false);

      const result = readInstallState('/path/to/marker.json');

      expect(result).toBeNull();
      expect(mockFs.existsSync).toHaveBeenCalledWith('/path/to/marker.json');
    });

    it('should return parsed marker if file exists and valid', () => {
      const marker: InstallStateMarker = {
        state: 'installed',
        version: '2.0.0',
        timestamp: '2026-02-02T19:30:00.000Z',
      };

      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(JSON.stringify(marker));

      const result = readInstallState('/path/to/marker.json');

      expect(result).toEqual(marker);
    });

    it('should return null if JSON is invalid', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue('invalid json');

      const result = readInstallState('/path/to/marker.json');

      expect(result).toBeNull();
    });

    it('should return null if marker structure is invalid (missing state)', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(
        JSON.stringify({
          version: '1.0.0',
          timestamp: '2026-02-02T19:30:00.000Z',
          mode: 'project',
        })
      );

      const result = readInstallState('/path/to/marker.json');

      expect(result).toBeNull();
    });

    it('should return null if state value is invalid', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(
        JSON.stringify({
          state: 'invalid-state',
          version: '2.0.0',
          timestamp: '2026-02-02T19:30:00.000Z',
        })
      );

      const result = readInstallState('/path/to/marker.json');

      expect(result).toBeNull();
    });
  });

  describe('writeInstallState', () => {
    it('should write marker file atomically', () => {
      mockFs.existsSync.mockReturnValue(true);

      writeInstallState('/path/to/marker.json', 'installed');

      expect(mockFs.writeFileSync).toHaveBeenCalledWith(
        '/path/to/marker.json.tmp',
        expect.stringContaining('"state": "installed"'),
        'utf-8'
      );
      expect(mockFs.renameSync).toHaveBeenCalledWith(
        '/path/to/marker.json.tmp',
        '/path/to/marker.json'
      );
    });

    it('should create parent directory if missing', () => {
      mockFs.existsSync.mockReturnValue(false);

      writeInstallState('/path/to/marker.json', 'declined');

      expect(mockFs.mkdirSync).toHaveBeenCalledWith('/path/to', { recursive: true });
    });

    it('should write all required fields', () => {
      mockFs.existsSync.mockReturnValue(true);

      writeInstallState('/path/to/marker.json', 'error');

      const writeCall = mockFs.writeFileSync.mock.calls[0];
      const content = writeCall[1] as string;
      const parsed = JSON.parse(content);

      expect(parsed.state).toBe('error');
      expect(parsed.version).toBe('2.0.0');
      expect(parsed.timestamp).toMatch(/^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d{3}Z$/);
    });
  });

  describe('shouldPromptInstall', () => {
    it('should return true if marker does not exist', () => {
      mockFs.existsSync.mockReturnValue(false);

      const result = shouldPromptInstall('/path/to/marker.json');

      expect(result).toBe(true);
    });

    it('should return false if marker exists with installed state', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(
        JSON.stringify({
          state: 'installed',
          version: '2.0.0',
          timestamp: '2026-02-02T19:30:00.000Z',
        })
      );

      const result = shouldPromptInstall('/path/to/marker.json');

      expect(result).toBe(false);
    });

    it('should return false if marker exists with declined state', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(
        JSON.stringify({
          state: 'declined',
          version: '2.0.0',
          timestamp: '2026-02-02T19:30:00.000Z',
        })
      );

      const result = shouldPromptInstall('/path/to/marker.json');

      expect(result).toBe(false);
    });

    it('should return false if marker exists with error state', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(
        JSON.stringify({
          state: 'error',
          version: '2.0.0',
          timestamp: '2026-02-02T19:30:00.000Z',
        })
      );

      const result = shouldPromptInstall('/path/to/marker.json');

      expect(result).toBe(false);
    });

    it('should return true if marker is invalid', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue('invalid json');

      const result = shouldPromptInstall('/path/to/marker.json');

      expect(result).toBe(true);
    });
  });
});
