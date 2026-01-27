import { groupSymbols } from '../grouping';
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

describe('grouping', () => {
  describe('groupSymbols', () => {
    it('groups constants (OpDeclNode, level 0)', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'MaxValue', level: 0, arity: 0, rawKind: 'OpDeclNode' })
      ];

      const result = groupSymbols(symbols);

      expect(result.constants).toHaveLength(1);
      expect(result.constants[0].name).toBe('MaxValue');
    });

    it('groups variables (OpDeclNode, level 1)', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'count', level: 1, arity: 0, rawKind: 'OpDeclNode' })
      ];

      const result = groupSymbols(symbols);

      expect(result.variables).toHaveLength(1);
      expect(result.variables[0].name).toBe('count');
    });

    it('groups state predicates (UserDefinedOpKind, level 1, arity 0)', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Init', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = groupSymbols(symbols);

      expect(result.statePredicates).toHaveLength(1);
      expect(result.statePredicates[0].name).toBe('Init');
    });

    it('groups action predicates (level 2, arity 0)', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Next', level: 2, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = groupSymbols(symbols);

      expect(result.actionPredicates).toHaveLength(1);
      expect(result.actionPredicates[0].name).toBe('Next');
    });

    it('groups temporal formulas (level 3, arity 0)', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Spec', level: 3, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = groupSymbols(symbols);

      expect(result.temporalFormulas).toHaveLength(1);
      expect(result.temporalFormulas[0].name).toBe('Spec');
    });

    it('groups operators with args (arity > 0)', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Add', level: 1, arity: 2, rawKind: 'UserDefinedOpKind' })
      ];

      const result = groupSymbols(symbols);

      expect(result.operatorsWithArgs).toHaveLength(1);
      expect(result.operatorsWithArgs[0].name).toBe('Add');
    });

    it('groups theorems (TheoremDefNode)', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'TypeOK', rawKind: 'TheoremDefNode' })
      ];

      const result = groupSymbols(symbols);

      expect(result.theorems).toHaveLength(1);
      expect(result.theorems[0].name).toBe('TypeOK');
    });

    it('groups assumptions (AssumeDef)', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Assumption1', rawKind: 'AssumeDef' })
      ];

      const result = groupSymbols(symbols);

      expect(result.assumptions).toHaveLength(1);
      expect(result.assumptions[0].name).toBe('Assumption1');
    });

    it('sorts symbols alphabetically within groups', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Zebra', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'Alpha', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'Middle', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = groupSymbols(symbols);

      expect(result.statePredicates.map((s: { name: string }) => s.name)).toEqual(['Alpha', 'Middle', 'Zebra']);
    });

    it('deduplicates symbols by name within groups', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'Init', uniqueName: 'M!Init', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'Init', uniqueName: 'M!Init', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' })
      ];

      const result = groupSymbols(symbols);

      expect(result.statePredicates).toHaveLength(1);
    });

    it('preserves location and comment in output', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({
          name: 'Init',
          level: 1,
          arity: 0,
          rawKind: 'UserDefinedOpKind',
          location: { file: 'Test.tla', start: { line: 10, col: 1 }, end: { line: 10, col: 20 } },
          comment: 'Initial state'
        })
      ];

      const result = groupSymbols(symbols);

      expect(result.statePredicates[0].location).toEqual({
        file: 'Test.tla',
        start: { line: 10, col: 1 },
        end: { line: 10, col: 20 }
      });
      expect(result.statePredicates[0].comment).toBe('Initial state');
    });

    it('returns empty groups when no symbols', () => {
      const result = groupSymbols([]);

      expect(result.constants).toHaveLength(0);
      expect(result.variables).toHaveLength(0);
      expect(result.statePredicates).toHaveLength(0);
      expect(result.actionPredicates).toHaveLength(0);
      expect(result.temporalFormulas).toHaveLength(0);
      expect(result.operatorsWithArgs).toHaveLength(0);
      expect(result.theorems).toHaveLength(0);
      expect(result.assumptions).toHaveLength(0);
    });

    it('handles mixed symbol types correctly', () => {
      const symbols: NormalizedSymbol[] = [
        makeSymbol({ name: 'MaxValue', level: 0, arity: 0, rawKind: 'OpDeclNode' }),
        makeSymbol({ name: 'count', level: 1, arity: 0, rawKind: 'OpDeclNode' }),
        makeSymbol({ name: 'Init', level: 1, arity: 0, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'Next', level: 2, arity: 0, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'Spec', level: 3, arity: 0, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'Add', level: 1, arity: 2, rawKind: 'UserDefinedOpKind' }),
        makeSymbol({ name: 'TypeOK', rawKind: 'TheoremDefNode' }),
        makeSymbol({ name: 'A1', rawKind: 'AssumeDef' })
      ];

      const result = groupSymbols(symbols);

      expect(result.constants).toHaveLength(1);
      expect(result.variables).toHaveLength(1);
      expect(result.statePredicates).toHaveLength(1);
      expect(result.actionPredicates).toHaveLength(1);
      expect(result.temporalFormulas).toHaveLength(1);
      expect(result.operatorsWithArgs).toHaveLength(1);
      expect(result.theorems).toHaveLength(1);
      expect(result.assumptions).toHaveLength(1);
    });
  });
});
