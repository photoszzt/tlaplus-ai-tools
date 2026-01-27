import {
  NormalizedSymbol,
  SymbolLocation,
  CandidateGroups,
  BestGuessItem,
  BestGuess,
  SymbolExtractionResult,
  MatchType
} from '../types';

describe('symbol types', () => {
  it('NormalizedSymbol has required fields', () => {
    const symbol: NormalizedSymbol = {
      name: 'Init',
      module: 'Counter',
      uniqueName: 'Counter!Init',
      level: 1,
      arity: 0,
      rawKind: 'UserDefinedOpKind'
    };

    expect(symbol.name).toBe('Init');
    expect(symbol.module).toBe('Counter');
    expect(symbol.level).toBe(1);
    expect(symbol.arity).toBe(0);
  });

  it('SymbolLocation has start and end positions', () => {
    const loc: SymbolLocation = {
      file: '/path/to/Counter.tla',
      start: { line: 10, col: 1 },
      end: { line: 10, col: 20 }
    };

    expect(loc.start.line).toBe(10);
    expect(loc.end.col).toBe(20);
  });

  it('CandidateGroups has all TLC-oriented groups', () => {
    const groups: CandidateGroups = {
      constants: [],
      variables: [],
      statePredicates: [],
      actionPredicates: [],
      temporalFormulas: [],
      operatorsWithArgs: [],
      theorems: [],
      assumptions: []
    };

    expect(groups.constants).toBeDefined();
    expect(groups.statePredicates).toBeDefined();
    expect(groups.temporalFormulas).toBeDefined();
  });

  it('BestGuessItem includes match and reason', () => {
    const item: BestGuessItem = {
      name: 'Init',
      match: 'exact',
      reason: 'root module exact match on Init in statePredicates'
    };

    expect(item.match).toBe('exact');
    expect(item.reason).toContain('exact match');
  });

  it('SymbolExtractionResult has schemaVersion at top level', () => {
    const result: SymbolExtractionResult = {
      schemaVersion: 1,
      rootModule: 'Counter',
      file: '/path/Counter.tla',
      includeExtendedModules: false,
      candidates: {
        constants: [],
        variables: [],
        statePredicates: [],
        actionPredicates: [],
        temporalFormulas: [],
        operatorsWithArgs: [],
        theorems: [],
        assumptions: []
      },
      bestGuess: {
        init: null,
        next: null,
        spec: null,
        invariants: [],
        properties: []
      },
      extendedModules: {}
    };

    expect(result.schemaVersion).toBe(1);
    expect(result.extendedModules).toBeDefined();
  });

  it('MatchType enum has all match types', () => {
    const types: MatchType[] = [
      'exact',
      'case_insensitive_exact',
      'prefix',
      'contains',
      'fallback_first_candidate'
    ];

    expect(types).toHaveLength(5);
  });
});
