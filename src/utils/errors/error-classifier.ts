// src/utils/errors/error-classifier.ts
import { ErrorCode, ERROR_RETRYABLE } from './error-codes';

export function classifyError(error: Error): ErrorCode {
  // If already enhanced (has code property), return it
  if ('code' in error && typeof (error as any).code === 'string' && (error as any).code in ErrorCode) {
    return (error as any).code as ErrorCode;
  }

  const message = error.message.toLowerCase();
  const errno = (error as NodeJS.ErrnoException).code;

  // Classify by errno code (most specific)
  if (errno === 'ENOENT') return ErrorCode.FILE_NOT_FOUND;
  if (errno === 'EACCES' || errno === 'EPERM') return ErrorCode.FILE_ACCESS_DENIED;
  if (errno === 'EBUSY') return ErrorCode.FILE_BUSY;

  // Classify by message patterns
  if (message.includes('java executable not found')) {
    return ErrorCode.JAVA_NOT_FOUND;
  }
  if (message.includes('failed to launch java process')) {
    return ErrorCode.JAVA_SPAWN_FAILED;
  }
  if (message.includes('path traversal') || message.includes('outside the working directory')) {
    return ErrorCode.FILE_PATH_TRAVERSAL;
  }
  if (message.includes('invalid jarfile uri')) {
    return ErrorCode.JAR_INVALID_URI;
  }
  if (message.includes('not found in jar')) {
    return ErrorCode.JAR_ENTRY_NOT_FOUND;
  }

  // Default fallback
  return ErrorCode.FILE_IO_ERROR;
}

export function isRetryable(errorCode: ErrorCode): boolean {
  return ERROR_RETRYABLE[errorCode] ?? false;
}
