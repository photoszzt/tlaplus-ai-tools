import { computeBestGuess, isStdlibModule } from '../best-guess';
import { NormalizedSymbol } from '../types';

function makeSymbol(overrides: Partial<NormalizedSymbol>): NormalizedSymbol {
  return {
    name: 'Test',
    module: 'TestModule',
    uniqueName: 'TestModule!Test',
    rawKind: 'UserDefinedOpKind',
    ...overrides
  };
}

describe('best-guess', () => {
  describe('isStdlibModule', () => {
    it('identifies standard library modules by name', () => {
      expect(isStdlibModule('Integers')).toBe(true);
      expect(isStdlibModule('Naturals')).toBe(true);
      expect(isStdlibModule('Sequences')).toBe(true);
      expect(isStdlibModule('FiniteSets')).toBe(true);
      expect(isStdlibModule('TLC')).toBe(true);
      expect(isStdlibModule('Bags')).toBe(true);
      expect(isStdlibModule('Reals')).toBe(true);
    });

    it('does not identify user modules as stdlib', () => {
      expect(isStdlibModule('Counter')).toBe(false);
      expect(isStdlibModule('MySpec')).toBe(false);
      expect(isStdlibModule('IntegerUtils')).toBe(false);
    });
  });

  describe('computeBestGuess', () => {
    it('finds exact Init match in root module', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Init', module: 'Counter', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.init).not.toBeNull();
      expect(result.init!.name).toBe('Init');
      expect(result.init!.match).toBe('exact');
      expect(result.init!.reason).toContain('root');
    });

    it('finds exact Next match in root module', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Next', module: 'Counter', level: 2, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.next).not.toBeNull();
      expect(result.next!.name).toBe('Next');
      expect(result.next!.match).toBe('exact');
    });

    it('finds exact Spec match in root module', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Spec', module: 'Counter', level: 3, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.spec).not.toBeNull();
      expect(result.spec!.name).toBe('Spec');
      expect(result.spec!.match).toBe('exact');
    });

    it('finds case-insensitive match when exact not found', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'init', module: 'Counter', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.init).not.toBeNull();
      expect(result.init!.name).toBe('init');
      expect(result.init!.match).toBe('case_insensitive_exact');
    });

    it('finds prefix match when exact not found', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'InitState', module: 'Counter', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.init).not.toBeNull();
      expect(result.init!.name).toBe('InitState');
      expect(result.init!.match).toBe('prefix');
    });

    it('prefers root module over extended modules', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Init', module: 'Extended', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'Init', module: 'Counter', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.init!.reason).toContain('root');
    });

    it('heavily down-ranks stdlib modules', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Init', module: 'Integers', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'InitState', module: 'Counter', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.init!.name).toBe('InitState');
    });

    it('uses stdlib as last resort', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Init', module: 'Integers', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.init).not.toBeNull();
      expect(result.init!.name).toBe('Init');
      expect(result.init!.reason).toContain('stdlib');
    });

    it('finds invariants by name pattern', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'TypeInvariant', module: 'Counter', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'TypeOK', module: 'Counter', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.invariants).toHaveLength(2);
      expect(result.invariants.map((i: { name: string }) => i.name)).toContain('TypeInvariant');
      expect(result.invariants.map((i: { name: string }) => i.name)).toContain('TypeOK');
    });

    it('finds properties by name pattern', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Liveness', module: 'Counter', level: 3, arity: 0, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'SafetyProperty', module: 'Counter', level: 3, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.properties.length).toBeGreaterThanOrEqual(1);
    });

    it('excludes Spec from properties', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Spec', module: 'Counter', level: 3, arity: 0, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'Liveness', module: 'Counter', level: 3, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.properties.map((p: { name: string }) => p.name)).not.toContain('Spec');
    });

    it('returns null for init/next/spec when no candidates', () => {
      const allSymbols: NormalizedSymbol[] = [];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.init).toBeNull();
      expect(result.next).toBeNull();
      expect(result.spec).toBeNull();
    });

    it('uses fallback_first_candidate when no name matches', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'StartState', module: 'Counter', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.init).not.toBeNull();
      expect(result.init!.match).toBe('fallback_first_candidate');
    });

    it('searches extended modules when root has no match', () => {
      const allSymbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Init', module: 'Helper', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = computeBestGuess(allSymbols, 'Counter');

      expect(result.init).not.toBeNull();
      expect(result.init!.reason).toContain('extended');
    });
  });
});
