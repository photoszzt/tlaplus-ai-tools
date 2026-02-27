// Test lockfile management and asset URL resolution from scripts/setup.js
import * as path from 'path';

// Compute the lock file path the same way setup.js does
const LOCK_FILE_PATH = path.join(__dirname, '..', '..', 'tools', '.setup-lock.json');

// Mock fs before requiring setup.js so the module picks up the mock
const mockReadFileSync = jest.fn();
const mockWriteFileSync = jest.fn();
jest.mock('fs', () => {
  const actualFs = jest.requireActual('fs');
  return {
    ...actualFs,
    readFileSync: (...args: any[]) => {
      // Only intercept calls to the lock file path
      if (args[0] === LOCK_FILE_PATH) {
        return mockReadFileSync(...args);
      }
      return actualFs.readFileSync(...args);
    },
    writeFileSync: (...args: any[]) => {
      if (args[0] === LOCK_FILE_PATH) {
        return mockWriteFileSync(...args);
      }
      return actualFs.writeFileSync(...args);
    }
  };
});

// Mock https for resolveAssetUrl tests
const mockRequest = jest.fn();
jest.mock('https', () => {
  const actualHttps = jest.requireActual('https');
  return {
    ...actualHttps,
    request: (...args: any[]) => mockRequest(...args)
  };
});

import { EventEmitter } from 'events';

// Must require AFTER mocks are set up
const { readLock, writeLock, resolveAssetUrl } = require('../../scripts/setup.js');

describe('Lockfile Management', () => {
  beforeEach(() => {
    mockReadFileSync.mockReset();
    mockWriteFileSync.mockReset();
  });

  describe('readLock', () => {
    it('returns empty object when lockfile does not exist', () => {
      mockReadFileSync.mockImplementation(() => {
        throw new Error('ENOENT: no such file or directory');
      });
      expect(readLock()).toEqual({});
    });

    it('returns empty object when lockfile contains malformed JSON', () => {
      mockReadFileSync.mockReturnValue('not valid json {{{');
      expect(readLock()).toEqual({});
    });

    it('returns parsed object when lockfile is valid', () => {
      const lockData = { tla2tools: { assetUrl: 'https://example.com/asset', sha256: 'abc123' } };
      mockReadFileSync.mockReturnValue(JSON.stringify(lockData));
      expect(readLock()).toEqual(lockData);
    });

    it('returns empty object for empty file', () => {
      mockReadFileSync.mockReturnValue('');
      expect(readLock()).toEqual({});
    });
  });

  describe('writeLock', () => {
    it('merges entry into existing lockfile', () => {
      const existing = { communityModules: { sha256: 'existing' } };
      mockReadFileSync.mockReturnValue(JSON.stringify(existing));

      writeLock('tla2tools', { assetUrl: 'https://cdn.example.com/asset', sha256: 'newsha' });

      expect(mockWriteFileSync).toHaveBeenCalledTimes(1);
      const written = mockWriteFileSync.mock.calls[0][1] as string;
      const parsed = JSON.parse(written);
      expect(parsed.communityModules).toEqual({ sha256: 'existing' });
      expect(parsed.tla2tools).toEqual({ assetUrl: 'https://cdn.example.com/asset', sha256: 'newsha' });
    });

    it('creates new lockfile when none exists', () => {
      mockReadFileSync.mockImplementation(() => {
        throw new Error('ENOENT');
      });

      writeLock('tla2tools', { sha256: 'abc' });

      expect(mockWriteFileSync).toHaveBeenCalledTimes(1);
      const written = mockWriteFileSync.mock.calls[0][1] as string;
      const parsed = JSON.parse(written);
      expect(parsed).toEqual({ tla2tools: { sha256: 'abc' } });
    });

    it('writes file with trailing newline', () => {
      mockReadFileSync.mockReturnValue('{}');

      writeLock('key', { value: 1 });

      const written = mockWriteFileSync.mock.calls[0][1] as string;
      expect(written.endsWith('\n')).toBe(true);
    });

    it('overwrites existing entry for same key', () => {
      const existing = { tla2tools: { sha256: 'old' } };
      mockReadFileSync.mockReturnValue(JSON.stringify(existing));

      writeLock('tla2tools', { sha256: 'new' });

      const written = mockWriteFileSync.mock.calls[0][1] as string;
      const parsed = JSON.parse(written);
      expect(parsed.tla2tools).toEqual({ sha256: 'new' });
    });
  });
});

describe('resolveAssetUrl', () => {
  beforeEach(() => {
    mockRequest.mockReset();
  });

  function makeMockReq() {
    const req = new EventEmitter() as any;
    req.setTimeout = jest.fn();
    req.destroy = jest.fn();
    req.end = jest.fn();
    return req;
  }

  it('returns the URL directly on HTTP 200', async () => {
    const mockReq = makeMockReq();
    mockRequest.mockImplementation((_opts: any, cb: any) => {
      process.nextTick(() => {
        const res = new EventEmitter() as any;
        res.statusCode = 200;
        res.headers = {};
        cb(res);
      });
      return mockReq;
    });

    const result = await resolveAssetUrl('https://example.com/file.jar');
    expect(result).toBe('https://example.com/file.jar');
  });

  it('follows redirects and returns final URL', async () => {
    let callCount = 0;
    mockRequest.mockImplementation((_opts: any, cb: any) => {
      const mockReq = makeMockReq();
      process.nextTick(() => {
        callCount++;
        if (callCount === 1) {
          const res = new EventEmitter() as any;
          res.statusCode = 302;
          res.headers = { location: 'https://cdn.example.com/final.jar' };
          cb(res);
        } else {
          const res = new EventEmitter() as any;
          res.statusCode = 200;
          res.headers = {};
          cb(res);
        }
      });
      return mockReq;
    });

    const result = await resolveAssetUrl('https://github.com/release/file.jar');
    expect(result).toBe('https://cdn.example.com/final.jar');
  });

  it('rejects when max redirects exceeded', async () => {
    await expect(
      resolveAssetUrl('https://example.com/file.jar', 6)
    ).rejects.toThrow('Too many redirects');
  });

  it('rejects on non-200/redirect status', async () => {
    const mockReq = makeMockReq();
    mockRequest.mockImplementation((_opts: any, cb: any) => {
      process.nextTick(() => {
        const res = new EventEmitter() as any;
        res.statusCode = 404;
        res.headers = {};
        cb(res);
      });
      return mockReq;
    });

    await expect(
      resolveAssetUrl('https://example.com/file.jar')
    ).rejects.toThrow('HEAD request returned HTTP 404');
  });

  it('rejects on request error', async () => {
    const mockReq = makeMockReq();
    mockRequest.mockImplementation(() => {
      process.nextTick(() => mockReq.emit('error', new Error('network failure')));
      return mockReq;
    });

    await expect(
      resolveAssetUrl('https://example.com/file.jar')
    ).rejects.toThrow('network failure');
  });

  it('handles relative redirect URLs', async () => {
    let callCount = 0;
    mockRequest.mockImplementation((_opts: any, cb: any) => {
      const mockReq = makeMockReq();
      process.nextTick(() => {
        callCount++;
        if (callCount === 1) {
          const res = new EventEmitter() as any;
          res.statusCode = 301;
          res.headers = { location: '/new/path/file.jar' };
          cb(res);
        } else {
          const res = new EventEmitter() as any;
          res.statusCode = 200;
          res.headers = {};
          cb(res);
        }
      });
      return mockReq;
    });

    const result = await resolveAssetUrl('https://example.com/old/file.jar');
    expect(result).toBe('https://example.com/new/path/file.jar');
  });

  it('sets timeout on requests', async () => {
    const mockReq = makeMockReq();
    mockRequest.mockImplementation((_opts: any, cb: any) => {
      process.nextTick(() => {
        const res = new EventEmitter() as any;
        res.statusCode = 200;
        res.headers = {};
        cb(res);
      });
      return mockReq;
    });

    await resolveAssetUrl('https://example.com/file.jar');
    expect(mockReq.setTimeout).toHaveBeenCalledWith(expect.any(Number), expect.any(Function));
  });
});
