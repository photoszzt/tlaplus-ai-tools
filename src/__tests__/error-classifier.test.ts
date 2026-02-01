import { classifyError, isRetryable } from '../utils/errors/error-classifier';
import { ErrorCode } from '../utils/errors/error-codes';

describe('Error Classifier', () => {
  describe('classifyError', () => {
    describe('XMLExporter errors', () => {
      it('classifies "Only one TLA file to check allowed!" as XMLEXPORTER_USAGE_ERROR', () => {
        const error = new Error('Only one TLA file to check allowed!');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.XMLEXPORTER_USAGE_ERROR);
      });

      it('classifies case-insensitive variant as XMLEXPORTER_USAGE_ERROR', () => {
        const error = new Error('only one tla file to check allowed!');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.XMLEXPORTER_USAGE_ERROR);
      });

      it('classifies mixed case variant as XMLEXPORTER_USAGE_ERROR', () => {
        const error = new Error('Only ONE TLA File to Check Allowed!');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.XMLEXPORTER_USAGE_ERROR);
      });

      it('classifies error with surrounding context as XMLEXPORTER_USAGE_ERROR', () => {
        const error = new Error('XMLExporter failed: Only one TLA file to check allowed! Please check your arguments.');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.XMLEXPORTER_USAGE_ERROR);
      });

      it('does not misclassify similar but different errors', () => {
        const error = new Error('Multiple TLA files provided');
        const code = classifyError(error);
        expect(code).not.toBe(ErrorCode.XMLEXPORTER_USAGE_ERROR);
      });
    });

    describe('Java errors', () => {
      it('classifies "java executable not found" as JAVA_NOT_FOUND', () => {
        const error = new Error('Java executable not found');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.JAVA_NOT_FOUND);
      });

      it('classifies "failed to launch java process" as JAVA_SPAWN_FAILED', () => {
        const error = new Error('Failed to launch java process');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.JAVA_SPAWN_FAILED);
      });
    });

    describe('File system errors', () => {
      it('classifies ENOENT errno as FILE_NOT_FOUND', () => {
        const error = new Error('File not found') as NodeJS.ErrnoException;
        error.code = 'ENOENT';
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.FILE_NOT_FOUND);
      });

      it('classifies EACCES errno as FILE_ACCESS_DENIED', () => {
        const error = new Error('Permission denied') as NodeJS.ErrnoException;
        error.code = 'EACCES';
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.FILE_ACCESS_DENIED);
      });

      it('classifies EPERM errno as FILE_ACCESS_DENIED', () => {
        const error = new Error('Operation not permitted') as NodeJS.ErrnoException;
        error.code = 'EPERM';
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.FILE_ACCESS_DENIED);
      });

      it('classifies EBUSY errno as FILE_BUSY', () => {
        const error = new Error('Resource busy') as NodeJS.ErrnoException;
        error.code = 'EBUSY';
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.FILE_BUSY);
      });

      it('classifies path traversal message as FILE_PATH_TRAVERSAL', () => {
        const error = new Error('Path traversal detected');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.FILE_PATH_TRAVERSAL);
      });

      it('classifies "outside the working directory" as FILE_PATH_TRAVERSAL', () => {
        const error = new Error('Path is outside the working directory');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.FILE_PATH_TRAVERSAL);
      });
    });

    describe('JAR errors', () => {
      it('classifies "invalid jarfile uri" as JAR_INVALID_URI', () => {
        const error = new Error('Invalid jarfile URI');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.JAR_INVALID_URI);
      });

      it('classifies "not found in jar" as JAR_ENTRY_NOT_FOUND', () => {
        const error = new Error('Module.tla not found in jar');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.JAR_ENTRY_NOT_FOUND);
      });
    });

    describe('Already enhanced errors', () => {
      it('preserves existing error code', () => {
        const error = new Error('Test error') as any;
        error.code = ErrorCode.JAVA_TIMEOUT;
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.JAVA_TIMEOUT);
      });

      it('does not reclassify enhanced errors', () => {
        const error = new Error('java executable not found') as any;
        error.code = ErrorCode.CONFIG_TOOLS_NOT_FOUND;
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.CONFIG_TOOLS_NOT_FOUND);
      });
    });

    describe('Fallback classification', () => {
      it('defaults to FILE_IO_ERROR for unknown errors', () => {
        const error = new Error('Unknown error occurred');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.FILE_IO_ERROR);
      });

      it('defaults to FILE_IO_ERROR for generic I/O errors', () => {
        const error = new Error('Read failed');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.FILE_IO_ERROR);
      });
    });

    describe('Classification priority', () => {
      it('prioritizes errno over message patterns', () => {
        const error = new Error('java executable not found') as NodeJS.ErrnoException;
        error.code = 'ENOENT';
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.FILE_NOT_FOUND);
      });

      it('prioritizes specific patterns over generic fallback', () => {
        const error = new Error('Only one TLA file to check allowed!');
        const code = classifyError(error);
        expect(code).toBe(ErrorCode.XMLEXPORTER_USAGE_ERROR);
        expect(code).not.toBe(ErrorCode.FILE_IO_ERROR);
      });
    });
  });

  describe('isRetryable', () => {
    describe('Non-retryable errors', () => {
      it('marks XMLEXPORTER_USAGE_ERROR as non-retryable', () => {
        expect(isRetryable(ErrorCode.XMLEXPORTER_USAGE_ERROR)).toBe(false);
      });

      it('marks JAVA_NOT_FOUND as non-retryable', () => {
        expect(isRetryable(ErrorCode.JAVA_NOT_FOUND)).toBe(false);
      });

      it('marks FILE_NOT_FOUND as non-retryable', () => {
        expect(isRetryable(ErrorCode.FILE_NOT_FOUND)).toBe(false);
      });

      it('marks FILE_ACCESS_DENIED as non-retryable', () => {
        expect(isRetryable(ErrorCode.FILE_ACCESS_DENIED)).toBe(false);
      });

      it('marks FILE_PATH_TRAVERSAL as non-retryable', () => {
        expect(isRetryable(ErrorCode.FILE_PATH_TRAVERSAL)).toBe(false);
      });

      it('marks JAR_INVALID_URI as non-retryable', () => {
        expect(isRetryable(ErrorCode.JAR_INVALID_URI)).toBe(false);
      });

      it('marks JAR_ENTRY_NOT_FOUND as non-retryable', () => {
        expect(isRetryable(ErrorCode.JAR_ENTRY_NOT_FOUND)).toBe(false);
      });

      it('marks CONFIG_TOOLS_NOT_FOUND as non-retryable', () => {
        expect(isRetryable(ErrorCode.CONFIG_TOOLS_NOT_FOUND)).toBe(false);
      });
    });

    describe('Retryable errors', () => {
      it('marks FILE_BUSY as retryable', () => {
        expect(isRetryable(ErrorCode.FILE_BUSY)).toBe(true);
      });

      it('marks FILE_IO_ERROR as retryable', () => {
        expect(isRetryable(ErrorCode.FILE_IO_ERROR)).toBe(true);
      });

      it('marks JAVA_SPAWN_FAILED as retryable', () => {
        expect(isRetryable(ErrorCode.JAVA_SPAWN_FAILED)).toBe(true);
      });

      it('marks JAR_LOCKED as retryable', () => {
        expect(isRetryable(ErrorCode.JAR_LOCKED)).toBe(true);
      });

      it('marks JAR_EXTRACTION_FAILED as retryable', () => {
        expect(isRetryable(ErrorCode.JAR_EXTRACTION_FAILED)).toBe(true);
      });
    });
  });
});
