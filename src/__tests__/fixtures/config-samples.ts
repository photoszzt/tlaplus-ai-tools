import { ServerConfig } from '../../types';

/**
 * Sample ServerConfig objects for testing
 */

export const MINIMAL_CONFIG: ServerConfig = {
  toolsDir: '/mock/tools',
  workingDir: '/mock/work',
  kbDir: null,
  javaHome: null,
  verbose: false,
  http: false,
  port: 3000
};

export const HTTP_CONFIG: ServerConfig = {
  toolsDir: '/mock/tools',
  workingDir: '/mock/work',
  kbDir: null,
  javaHome: null,
  verbose: false,
  http: true,
  port: 3000
};

export const FULL_CONFIG: ServerConfig = {
  toolsDir: '/mock/tools',
  workingDir: '/mock/work',
  kbDir: '/mock/kb',
  javaHome: '/mock/java',
  verbose: true,
  http: false,
  port: 3000
};

export const NO_TOOLS_CONFIG: ServerConfig = {
  toolsDir: null,
  workingDir: '/mock/work',
  kbDir: null,
  javaHome: null,
  verbose: false,
  http: false,
  port: 3000
};
