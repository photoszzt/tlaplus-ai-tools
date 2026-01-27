// src/utils/errors/__tests__/error-context.test.ts
import { EnhancedError, enhanceError, ErrorMetadata } from '../error-context';
import { ErrorCode } from '../error-codes';

describe('EnhancedError', () => {
  it('wraps original error with metadata', () => {
    const original = new Error('Original message');
    const enhanced = new EnhancedError('Enhanced message', original, {
      code: ErrorCode.FILE_NOT_FOUND,
      context: { filePath: '/test/file.tla' }
    });

    expect(enhanced.message).toBe('Enhanced message');
    expect(enhanced.originalError).toBe(original);
    expect(enhanced.code).toBe(ErrorCode.FILE_NOT_FOUND);
    expect(enhanced.metadata.context).toEqual({ filePath: '/test/file.tla' });
  });

  it('auto-classifies error if code not provided', () => {
    const original = new Error('Java executable not found');
    const enhanced = new EnhancedError('Message', original);

    expect(enhanced.code).toBe(ErrorCode.JAVA_NOT_FOUND);
  });

  it('preserves original stack trace', () => {
    const original = new Error('Original');
    const enhanced = new EnhancedError('Enhanced', original);

    expect(enhanced.metadata.stack).toBe(original.stack);
  });

  it('adds timestamp to metadata', () => {
    const original = new Error('Test');
    const enhanced = new EnhancedError('Test', original);

    expect(enhanced.metadata.timestamp).toBeDefined();
    expect(new Date(enhanced.metadata.timestamp!).getTime()).toBeCloseTo(Date.now(), -2);
  });
});

describe('enhanceError', () => {
  it('wraps plain Error', () => {
    const error = new Error('Test error');
    const enhanced = enhanceError(error, { context: { key: 'value' } });

    expect(enhanced).toBeInstanceOf(EnhancedError);
    expect(enhanced.metadata.context).toEqual({ key: 'value' });
  });

  it('merges metadata when enhancing EnhancedError', () => {
    const original = new Error('Test');
    const first = enhanceError(original, { retryAttempt: 1 });
    const second = enhanceError(first, { retriesExhausted: true });

    expect(second.metadata.retryAttempt).toBe(1);
    expect(second.metadata.retriesExhausted).toBe(true);
  });

  it('does not mutate original error', () => {
    const error = new Error('Test');
    const enhanced = enhanceError(error);

    expect(error).not.toBeInstanceOf(EnhancedError);
  });
});
