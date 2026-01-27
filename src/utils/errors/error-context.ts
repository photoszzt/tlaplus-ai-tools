// src/utils/errors/error-context.ts
import { ErrorCode } from './error-codes';
import { classifyError } from './error-classifier';

export interface ErrorMetadata {
  code?: ErrorCode;
  retryAttempt?: number;
  retriesExhausted?: boolean;
  context?: Record<string, unknown>;
  timestamp?: string;
  stack?: string;
}

export class EnhancedError extends Error {
  public readonly code: ErrorCode;
  public readonly metadata: ErrorMetadata;
  public readonly originalError: Error;

  constructor(message: string, originalError: Error, metadata: Partial<ErrorMetadata> = {}) {
    super(message);
    this.name = 'EnhancedError';
    this.originalError = originalError;
    this.code = metadata.code ?? classifyError(originalError);
    this.metadata = {
      ...metadata,
      code: this.code,
      timestamp: new Date().toISOString(),
      stack: originalError.stack
    };

    // Preserve stack trace
    if (Error.captureStackTrace) {
      Error.captureStackTrace(this, EnhancedError);
    }
  }
}

export function enhanceError(error: Error, metadata: Partial<ErrorMetadata> = {}): EnhancedError {
  if (error instanceof EnhancedError) {
    // Merge metadata for already-enhanced errors
    return new EnhancedError(
      error.message,
      error.originalError,
      { ...error.metadata, ...metadata }
    );
  }

  return new EnhancedError(error.message, error, metadata);
}
