/**
 * Configuration for the TLA+ MCP server
 */
export interface ServerConfig {
  // Transport
  http: boolean;
  port: number;

  // Paths
  workingDir: string | null;
  toolsDir: string | null;
  kbDir: string | null;
  javaHome: string | null;

  // Logging
  verbose: boolean;
}

/**
 * Java execution options
 */
export interface JavaOptions {
  javaHome?: string;
  javaOpts?: string[];
}
