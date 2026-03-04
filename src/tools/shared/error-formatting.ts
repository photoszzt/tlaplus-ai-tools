// Shared error formatting for MCP tool responses.
//
// Spec: docs/review-remediation/spec.md
// Contract: docs/review-remediation/contract.md

import { EnhancedError, enhanceError, ErrorCode } from '../../utils/errors';

/**
 * Format an error response with error code and suggested actions
 *
 * @implements REQ-REVIEW-001, SCN-REVIEW-001-01, SCN-REVIEW-001-02, SCN-REVIEW-001-03
 */
export function formatErrorResponse(error: Error): string {
  const enhanced = error instanceof EnhancedError ? error : enhanceError(error);

  const parts = [
    `Error [${enhanced.code}]: ${error.message}`,
    '',
    'Suggested Actions:',
    ...getSuggestedActions(enhanced.code)
  ];

  if (enhanced.metadata.retriesExhausted) {
    parts.push('', `Failed after ${enhanced.metadata.retryAttempt} retry attempts.`);
  }

  if (process.env.VERBOSE || process.env.DEBUG) {
    parts.push('', 'Stack Trace:', enhanced.metadata.stack || 'N/A');
  }

  return parts.join('\n');
}

/**
 * Get suggested actions based on error code
 *
 * @implements REQ-REVIEW-001, SCN-REVIEW-001-01
 */
export function getSuggestedActions(code: ErrorCode): string[] {
  const suggestions: Partial<Record<ErrorCode, string[]>> = {
    [ErrorCode.JAVA_NOT_FOUND]: [
      '- Install Java 17 or later',
      '- Set JAVA_HOME environment variable',
      '- Use --java-home to specify Java location'
    ],
    [ErrorCode.CONFIG_TOOLS_NOT_FOUND]: [
      '- Use --tools-dir to specify TLA+ tools location',
      '- Ensure tla2tools.jar exists in tools directory'
    ],
    [ErrorCode.FILE_NOT_FOUND]: [
      '- Verify the file path is correct',
      '- Check file permissions'
    ],
    [ErrorCode.JAR_LOCKED]: [
      '- Close other programs using the JAR file',
      '- Check for antivirus software locking files'
    ],
    [ErrorCode.JAR_ENTRY_NOT_FOUND]: [
      '- Verify the jarfile URI is correct',
      '- Check that the JAR file contains the expected module'
    ],
    [ErrorCode.JAR_EXTRACTION_FAILED]: [
      '- Check available disk space',
      '- Verify write permissions to temp directory'
    ],
    [ErrorCode.XMLEXPORTER_USAGE_ERROR]: [
      '- Run `npm run setup` to install pinned tools (v1.8.0)',
      '- Verify `tools/tla2tools.jar` matches v1.8.0 with correct checksum',
      '- If checksum mismatch: delete `tools/tla2tools.jar` and re-run `npm run setup`',
      '- This error indicates XMLExporter argument incompatibility with your TLA+ tools version'
    ]
  };

  return suggestions[code] || ['- Check error message for details'];
}
