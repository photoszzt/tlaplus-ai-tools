/**
 * Logger for the TLA+ MCP server
 */
export class Logger {
  constructor(
    private verbose: boolean,
    private useStderr: boolean
  ) {}

  /**
   * Log an informational message
   */
  info(message: string): void {
    const formatted = this.formatMessage('INFO', message);
    if (this.useStderr) {
      console.error(formatted);
    } else {
      console.log(formatted);
    }
  }

  /**
   * Log a debug message (only if verbose is enabled)
   */
  debug(message: string): void {
    if (!this.verbose) {
      return;
    }
    const formatted = this.formatMessage('DEBUG', message);
    if (this.useStderr) {
      console.error(formatted);
    } else {
      console.log(formatted);
    }
  }

  /**
   * Log a warning message (always to stderr)
   *
   * @implements REQ-REVIEW-005, REQ-REVIEW-006
   */
  warn(message: string, error?: unknown): void {
    const formatted = this.formatMessage('WARN', message);
    console.error(formatted);

    if (!error) {
      return;
    }

    if (error instanceof Error) {
      if (error.stack) {
        console.error(error.stack);
      } else if (error.message) {
        console.error(error.message);
      } else {
        console.error(String(error));
      }
      return;
    }

    if (typeof error === 'object') {
      try {
        console.error(JSON.stringify(error));
      } catch {
        console.error(String(error));
      }
    } else {
      console.error(String(error));
    }
  }

  /**
   * Log an error message (always to stderr)
   */
  error(message: string, error?: Error): void {
    const formatted = this.formatMessage('ERROR', message);
    console.error(formatted);
    if (error && error.stack) {
      console.error(error.stack);
    }
  }

  /**
   * Format a log message with timestamp and level
   */
  private formatMessage(level: string, message: string): string {
    const timestamp = new Date().toISOString();
    return `[${timestamp}] [${level}] ${message}`;
  }
}
