// src/utils/errors/__tests__/error-codes.test.ts
import { ErrorCode, ERROR_RETRYABLE } from '../error-codes';

describe('ErrorCode', () => {
  it('defines all required error codes', () => {
    expect(ErrorCode.JAVA_NOT_FOUND).toBe('JAVA_NOT_FOUND');
    expect(ErrorCode.JAVA_SPAWN_FAILED).toBe('JAVA_SPAWN_FAILED');
    expect(ErrorCode.FILE_NOT_FOUND).toBe('FILE_NOT_FOUND');
    expect(ErrorCode.FILE_BUSY).toBe('FILE_BUSY');
    expect(ErrorCode.JAR_LOCKED).toBe('JAR_LOCKED');
  });

  it('marks transient errors as retryable', () => {
    expect(ERROR_RETRYABLE[ErrorCode.JAVA_SPAWN_FAILED]).toBe(true);
    expect(ERROR_RETRYABLE[ErrorCode.FILE_BUSY]).toBe(true);
    expect(ERROR_RETRYABLE[ErrorCode.JAR_LOCKED]).toBe(true);
  });

  it('marks permanent errors as non-retryable', () => {
    expect(ERROR_RETRYABLE[ErrorCode.JAVA_NOT_FOUND]).toBe(false);
    expect(ERROR_RETRYABLE[ErrorCode.FILE_NOT_FOUND]).toBe(false);
    expect(ERROR_RETRYABLE[ErrorCode.JAR_ENTRY_NOT_FOUND]).toBe(false);
  });

  it('has retryability defined for all error codes', () => {
    const allCodes = Object.values(ErrorCode);
    allCodes.forEach(code => {
      expect(ERROR_RETRYABLE).toHaveProperty(code);
    });
  });
});
