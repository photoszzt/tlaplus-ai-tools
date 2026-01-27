// src/utils/errors/__tests__/retry.test.ts
import { withRetry, RetryConfig, DEFAULT_RETRY_CONFIG } from '../retry';
import { enhanceError } from '../error-context';
import { ErrorCode } from '../error-codes';

jest.useFakeTimers();

describe('withRetry', () => {
  afterEach(() => {
    jest.clearAllTimers();
  });

  it('returns successful result without retry', async () => {
    const operation = jest.fn(async () => 'success');

    const promise = withRetry(operation);
    jest.runAllTimers();
    const result = await promise;

    expect(result).toBe('success');
    expect(operation).toHaveBeenCalledTimes(1);
  });

  it('retries transient errors with exponential backoff', async () => {
    let attempts = 0;
    const operation = jest.fn(async () => {
      attempts++;
      if (attempts < 3) {
        const err = enhanceError(new Error('Spawn failed'), {
          code: ErrorCode.JAVA_SPAWN_FAILED
        });
        throw err;
      }
      return 'success';
    });

    const promise = withRetry(operation, {
      maxAttempts: 3,
      initialDelayMs: 100,
      maxDelayMs: 10000,
      backoffMultiplier: 10
    });

    // Let first attempt run
    await jest.advanceTimersByTimeAsync(0);
    expect(attempts).toBe(1);

    // Advance to second attempt (100ms delay)
    await jest.advanceTimersByTimeAsync(100);
    expect(attempts).toBe(2);

    // Advance to third attempt (1000ms delay)
    await jest.advanceTimersByTimeAsync(1000);
    expect(attempts).toBe(3);

    const result = await promise;
    expect(result).toBe('success');
    expect(operation).toHaveBeenCalledTimes(3);
  });

  it('does not retry permanent errors', async () => {
    const operation = jest.fn(async () => {
      const err = enhanceError(new Error('Java not found'), {
        code: ErrorCode.JAVA_NOT_FOUND
      });
      throw err;
    });

    await expect(withRetry(operation)).rejects.toThrow('Java not found');
    expect(operation).toHaveBeenCalledTimes(1);
  });

  it('adds retry metadata when retries exhausted', async () => {
    const operation = jest.fn(async () => {
      const err = enhanceError(new Error('Busy'), {
        code: ErrorCode.FILE_BUSY
      });
      throw err;
    });

    const promise = withRetry(operation, { maxAttempts: 2 }).catch(err => err);

    // Advance through all retry attempts
    await jest.runAllTimersAsync();

    const err = await promise;
    expect(err.metadata.retryAttempt).toBe(2);
    expect(err.metadata.retriesExhausted).toBe(true);
  });

  it('uses custom shouldRetry function', async () => {
    let attempts = 0;
    const operation = jest.fn(async () => {
      attempts++;
      throw new Error('Custom error');
    });

    const shouldRetry = jest.fn((error: Error, attempt: number) => attempt < 2);

    const promise = withRetry(operation, {
      maxAttempts: 3,
      initialDelayMs: 10,
      maxDelayMs: 100,
      backoffMultiplier: 10,
      shouldRetry
    }).catch(err => err);

    // Advance through all retry attempts
    await jest.runAllTimersAsync();

    const err = await promise;
    expect(err.message).toBe('Custom error');
    expect(shouldRetry).toHaveBeenCalledTimes(2);
    expect(attempts).toBe(2);
  });

  it('calculates exponential backoff correctly', async () => {
    let attempts = 0;

    const operation = jest.fn(async () => {
      attempts++;
      const err = enhanceError(new Error('Busy'), { code: ErrorCode.FILE_BUSY });
      throw err;
    });

    const promise = withRetry(operation, {
      maxAttempts: 4,
      initialDelayMs: 100,
      maxDelayMs: 10000,
      backoffMultiplier: 10
    }).catch(err => err); // Catch to prevent unhandled rejection

    // First attempt runs immediately
    await jest.advanceTimersByTimeAsync(0);
    expect(attempts).toBe(1);

    // Second attempt after 100ms delay
    await jest.advanceTimersByTimeAsync(100);
    expect(attempts).toBe(2);

    // Third attempt after 1000ms delay (100 * 10^1)
    await jest.advanceTimersByTimeAsync(1000);
    expect(attempts).toBe(3);

    // Fourth attempt after 10000ms delay (capped at maxDelayMs)
    await jest.advanceTimersByTimeAsync(10000);
    expect(attempts).toBe(4);

    // All retries exhausted, should reject
    const result = await promise;
    expect(result).toBeInstanceOf(Error);
    expect(result.message).toBe('Busy');
  });
});

describe('DEFAULT_RETRY_CONFIG', () => {
  it('has correct default values', () => {
    expect(DEFAULT_RETRY_CONFIG.maxAttempts).toBe(3);
    expect(DEFAULT_RETRY_CONFIG.initialDelayMs).toBe(100);
    expect(DEFAULT_RETRY_CONFIG.maxDelayMs).toBe(10000);
    expect(DEFAULT_RETRY_CONFIG.backoffMultiplier).toBe(10);
  });

  it('retries based on error code retryability', () => {
    const transientError = enhanceError(new Error('Spawn failed'), {
      code: ErrorCode.JAVA_SPAWN_FAILED
    });
    const permanentError = enhanceError(new Error('Not found'), {
      code: ErrorCode.FILE_NOT_FOUND
    });

    expect(DEFAULT_RETRY_CONFIG.shouldRetry!(transientError, 1)).toBe(true);
    expect(DEFAULT_RETRY_CONFIG.shouldRetry!(permanentError, 1)).toBe(false);
  });
});
