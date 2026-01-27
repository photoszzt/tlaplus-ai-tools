import { NormalizedSymbol, CandidateGroups, OutputSymbol } from './types';

export function groupSymbols(symbols: NormalizedSymbol[]): CandidateGroups {
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

  const seen = new Set<string>();

  for (const symbol of symbols) {
    const key = `${symbol.module}!${symbol.name}!${symbol.rawKind}`;
    if (seen.has(key)) {
      continue;
    }
    seen.add(key);

    const output = toOutputSymbol(symbol);

    if (symbol.rawKind === 'TheoremDefNode') {
      groups.theorems.push(output);
    } else if (symbol.rawKind === 'AssumeDef') {
      groups.assumptions.push(output);
    } else if (symbol.rawKind === 'OpDeclNode') {
      if (symbol.level === 0) {
        groups.constants.push(output);
      } else if (symbol.level === 1) {
        groups.variables.push(output);
      }
    } else if (symbol.rawKind === 'UserDefinedOpKind') {
      if (symbol.arity !== undefined && symbol.arity > 0) {
        groups.operatorsWithArgs.push(output);
      } else if (symbol.level === 1) {
        groups.statePredicates.push(output);
      } else if (symbol.level === 2) {
        groups.actionPredicates.push(output);
      } else if (symbol.level === 3) {
        groups.temporalFormulas.push(output);
      }
    }
  }

  for (const key of Object.keys(groups) as (keyof CandidateGroups)[]) {
    groups[key].sort((a, b) => a.name.localeCompare(b.name));
  }

  return groups;
}

function toOutputSymbol(symbol: NormalizedSymbol): OutputSymbol {
  const output: OutputSymbol = { name: symbol.name };

  if (symbol.location) {
    output.location = symbol.location;
  }

  if (symbol.comment) {
    output.comment = symbol.comment;
  }

  return output;
}
