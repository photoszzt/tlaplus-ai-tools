// src/utils/errors/error-codes.ts
export enum ErrorCode {
  // Java errors
  JAVA_NOT_FOUND = 'JAVA_NOT_FOUND',
  JAVA_SPAWN_FAILED = 'JAVA_SPAWN_FAILED',
  JAVA_TIMEOUT = 'JAVA_TIMEOUT',

  // File system errors
  FILE_NOT_FOUND = 'FILE_NOT_FOUND',
  FILE_ACCESS_DENIED = 'FILE_ACCESS_DENIED',
  FILE_PATH_TRAVERSAL = 'FILE_PATH_TRAVERSAL',
  FILE_IO_ERROR = 'FILE_IO_ERROR',
  FILE_BUSY = 'FILE_BUSY',

  // JAR errors
  JAR_CORRUPTED = 'JAR_CORRUPTED',
  JAR_ENTRY_NOT_FOUND = 'JAR_ENTRY_NOT_FOUND',
  JAR_INVALID_URI = 'JAR_INVALID_URI',
  JAR_EXTRACTION_FAILED = 'JAR_EXTRACTION_FAILED',
  JAR_LOCKED = 'JAR_LOCKED',

  // Parse errors
  PARSE_SYNTAX_ERROR = 'PARSE_SYNTAX_ERROR',
  PARSE_XML_MALFORMED = 'PARSE_XML_MALFORMED',

  // Process errors
  PROCESS_SPAWN_FAILED = 'PROCESS_SPAWN_FAILED',
  PROCESS_TIMEOUT = 'PROCESS_TIMEOUT',

  // Configuration errors
  CONFIG_TOOLS_NOT_FOUND = 'CONFIG_TOOLS_NOT_FOUND',
  CONFIG_INVALID_PATH = 'CONFIG_INVALID_PATH',

  // XMLExporter errors
  XMLEXPORTER_USAGE_ERROR = 'XMLEXPORTER_USAGE_ERROR'
}

export const ERROR_RETRYABLE: Record<ErrorCode, boolean> = {
  // Transient errors (retryable)
  [ErrorCode.JAVA_SPAWN_FAILED]: true,
  [ErrorCode.FILE_BUSY]: true,
  [ErrorCode.FILE_IO_ERROR]: true,
  [ErrorCode.JAR_LOCKED]: true,
  [ErrorCode.JAR_EXTRACTION_FAILED]: true,
  [ErrorCode.PROCESS_SPAWN_FAILED]: true,

  // Permanent errors (non-retryable)
  [ErrorCode.JAVA_NOT_FOUND]: false,
  [ErrorCode.JAVA_TIMEOUT]: false,
  [ErrorCode.FILE_NOT_FOUND]: false,
  [ErrorCode.FILE_ACCESS_DENIED]: false,
  [ErrorCode.FILE_PATH_TRAVERSAL]: false,
  [ErrorCode.JAR_CORRUPTED]: false,
  [ErrorCode.JAR_ENTRY_NOT_FOUND]: false,
  [ErrorCode.JAR_INVALID_URI]: false,
  [ErrorCode.PARSE_SYNTAX_ERROR]: false,
  [ErrorCode.PARSE_XML_MALFORMED]: false,
  [ErrorCode.PROCESS_TIMEOUT]: false,
  [ErrorCode.CONFIG_TOOLS_NOT_FOUND]: false,
  [ErrorCode.CONFIG_INVALID_PATH]: false,
  [ErrorCode.XMLEXPORTER_USAGE_ERROR]: false
};
