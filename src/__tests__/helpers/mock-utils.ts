/**
 * Mock utility functions for testing
 */

export function mockSanySuccess() {
  return {
    runSanyParse: jest.fn().mockResolvedValue({
      stdout: '',
      stderr: '',
      exitCode: 0
    }),
    parseSanyOutput: jest.fn().mockResolvedValue({
      success: true,
      errors: []
    })
  };
}

export function mockSanyError(errorMessage: string, file: string = 'test.tla', line: number = 5) {
  return {
    runSanyParse: jest.fn().mockResolvedValue({
      stdout: '',
      stderr: errorMessage,
      exitCode: 1
    }),
    parseSanyOutput: jest.fn().mockResolvedValue({
      success: false,
      errors: [{ file, line, message: errorMessage }]
    })
  };
}

export function mockExtractSymbolsSuccess(symbols: any = {}) {
  const defaultSymbols = {
    schemaVersion: 1,
    constants: [],
    variables: [],
    statePredicates: [],
    actionPredicates: [],
    temporalFormulas: [],
    operatorsWithArgs: [],
    theorems: [],
    assumptions: [],
    bestGuess: { init: null, next: null, spec: null },
    ...symbols
  };

  return {
    extractSymbols: jest.fn().mockResolvedValue(defaultSymbols)
  };
}

export function mockExtractSymbolsError(errorMessage: string) {
  return {
    extractSymbols: jest.fn().mockRejectedValue(new Error(errorMessage))
  };
}

export function mockTlcSuccess(output: string[] = [], exitCode: number = 0) {
  return {
    getSpecFiles: jest.fn().mockResolvedValue({
      tlaFilePath: '/mock/spec.tla',
      cfgFilePath: '/mock/spec.cfg'
    }),
    runTlcAndWait: jest.fn().mockResolvedValue({
      exitCode,
      output
    })
  };
}

export function mockTlcNoConfig() {
  return {
    getSpecFiles: jest.fn().mockResolvedValue(null),
    runTlcAndWait: jest.fn()
  };
}

export function mockTlcError(errorMessage: string) {
  return {
    getSpecFiles: jest.fn().mockResolvedValue({
      tlaFilePath: '/mock/spec.tla',
      cfgFilePath: '/mock/spec.cfg'
    }),
    runTlcAndWait: jest.fn().mockRejectedValue(new Error(errorMessage))
  };
}

export function mockFsExists(exists: boolean = true) {
  return {
    existsSync: jest.fn().mockReturnValue(exists)
  };
}

export function mockFsReaddir(files: string[] = []) {
  return {
    promises: {
      readdir: jest.fn().mockResolvedValue(files),
      readFile: jest.fn().mockResolvedValue('mock content')
    }
  };
}

export function mockFsError(errorMessage: string) {
  return {
    existsSync: jest.fn().mockReturnValue(false),
    promises: {
      readdir: jest.fn().mockRejectedValue(new Error(errorMessage)),
      readFile: jest.fn().mockRejectedValue(new Error(errorMessage))
    }
  };
}
