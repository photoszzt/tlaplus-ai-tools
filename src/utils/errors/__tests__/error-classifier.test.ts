// src/utils/errors/__tests__/error-classifier.test.ts
import { classifyError, isRetryable } from '../error-classifier';
import { ErrorCode } from '../error-codes';

describe('classifyError', () => {
  it('classifies errno ENOENT as FILE_NOT_FOUND', () => {
    const err = new Error('File not found') as NodeJS.ErrnoException;
    err.code = 'ENOENT';
    expect(classifyError(err)).toBe(ErrorCode.FILE_NOT_FOUND);
  });

  it('classifies errno EBUSY as FILE_BUSY', () => {
    const err = new Error('Resource busy') as NodeJS.ErrnoException;
    err.code = 'EBUSY';
    expect(classifyError(err)).toBe(ErrorCode.FILE_BUSY);
  });

  it('classifies errno EACCES as FILE_ACCESS_DENIED', () => {
    const err = new Error('Permission denied') as NodeJS.ErrnoException;
    err.code = 'EACCES';
    expect(classifyError(err)).toBe(ErrorCode.FILE_ACCESS_DENIED);
  });

  it('classifies Java not found message', () => {
    const err = new Error('Java executable not found in "/invalid/path"');
    expect(classifyError(err)).toBe(ErrorCode.JAVA_NOT_FOUND);
  });

  it('classifies Java spawn failure message', () => {
    const err = new Error('Failed to launch Java process: spawn EAGAIN');
    expect(classifyError(err)).toBe(ErrorCode.JAVA_SPAWN_FAILED);
  });

  it('classifies path traversal message', () => {
    const err = new Error('Access denied: Path ../etc/passwd is outside the working directory');
    expect(classifyError(err)).toBe(ErrorCode.FILE_PATH_TRAVERSAL);
  });

  it('classifies invalid jarfile URI message', () => {
    const err = new Error('Invalid jarfile URI: missing jarfile: prefix');
    expect(classifyError(err)).toBe(ErrorCode.JAR_INVALID_URI);
  });

  it('classifies JAR entry not found message', () => {
    const err = new Error("Entry 'Foo.tla' not found in JAR: /path/to/jar");
    expect(classifyError(err)).toBe(ErrorCode.JAR_ENTRY_NOT_FOUND);
  });

  it('defaults to FILE_IO_ERROR for unknown errors', () => {
    const err = new Error('Some unknown error');
    expect(classifyError(err)).toBe(ErrorCode.FILE_IO_ERROR);
  });
});

describe('isRetryable', () => {
  it('returns true for transient errors', () => {
    expect(isRetryable(ErrorCode.JAVA_SPAWN_FAILED)).toBe(true);
    expect(isRetryable(ErrorCode.FILE_BUSY)).toBe(true);
    expect(isRetryable(ErrorCode.JAR_LOCKED)).toBe(true);
  });

  it('returns false for permanent errors', () => {
    expect(isRetryable(ErrorCode.JAVA_NOT_FOUND)).toBe(false);
    expect(isRetryable(ErrorCode.FILE_NOT_FOUND)).toBe(false);
  });
});
