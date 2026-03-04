// src/utils/errors/retry.ts
import { classifyError, isRetryable } from './error-classifier';
import { enhanceError } from './error-context';

export interface RetryConfig {
  maxAttempts: number;
  initialDelayMs: number;
  maxDelayMs: number;
  backoffMultiplier: number;
  shouldRetry?: (error: Error, attempt: number) => boolean;
}

export const DEFAULT_RETRY_CONFIG: RetryConfig = {
  maxAttempts: 3,
  initialDelayMs: 100,
  maxDelayMs: 10000,
  backoffMultiplier: 10,
  shouldRetry: (error: Error) => {
    const errorCode = classifyError(error);
    return isRetryable(errorCode);
  }
};

function sleep(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms));
}

function calculateDelay(attempt: number, config: RetryConfig): number {
  const delay = config.initialDelayMs * Math.pow(config.backoffMultiplier, attempt - 1);
  return Math.min(delay, config.maxDelayMs);
}

export async function withRetry<T>(
  operation: () => Promise<T>,
  config: Partial<RetryConfig> = {}
): Promise<T> {
  const mergedConfig: RetryConfig = { ...DEFAULT_RETRY_CONFIG, ...config };
  let lastError: Error;

  for (let attempt = 1; attempt <= mergedConfig.maxAttempts; attempt++) {
    try {
      return await operation();
    } catch (error) {
      lastError = error as Error;

      const shouldRetry = mergedConfig.shouldRetry?.(lastError, attempt) ?? false;

      if (!shouldRetry || attempt >= mergedConfig.maxAttempts) {
        throw enhanceError(lastError, {
          retryAttempt: attempt,
          retriesExhausted: attempt >= mergedConfig.maxAttempts
        });
      }

      // Wait with exponential backoff
      const delay = calculateDelay(attempt, mergedConfig);
      await sleep(delay);
    }
  }

  throw lastError!;
}

