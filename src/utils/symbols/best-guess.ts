import { NormalizedSymbol, BestGuess, BestGuessItem, MatchType } from './types';

const STDLIB_MODULES = new Set([
  'Integers',
  'Naturals',
  'Sequences',
  'FiniteSets',
  'TLC',
  'Bags',
  'Reals',
  'RealTime',
  'Randomization',
  'Json',
  'IOUtils',
  'CSV',
  'TLCExt',
  'SequencesExt',
  'FiniteSetsExt',
  'Functions',
  'Folds',
  'BagsExt',
  'Relation',
  'Graphs'
]);

export function isStdlibModule(moduleName: string): boolean {
  return STDLIB_MODULES.has(moduleName);
}

const INIT_PATTERNS = { exact: 'Init', prefixes: ['Init'], contains: [] as string[] };
const NEXT_PATTERNS = { exact: 'Next', prefixes: ['Next', 'Step'], contains: [] as string[] };
const SPEC_PATTERNS = { exact: 'Spec', prefixes: ['Spec', 'Behavior'], contains: [] as string[] };

const INVARIANT_PATTERNS = ['Inv', 'Invariant', 'TypeOK', 'TypeInv'];
const PROPERTY_PATTERNS = ['Prop', 'Property', 'Live', 'Liveness', 'Safety'];

const MODULE_PENALTY = {
  root: 0,
  extended: 20,
  stdlib: 200
};

const NAME_PENALTY = {
  exact: 0,
  case_insensitive_exact: 1,
  prefix: 5,
  contains: 10,
  fallback_first_candidate: 100
};

interface ScoredCandidate {
  symbol: NormalizedSymbol;
  score: number;
  match: MatchType;
  reason: string;
}

export function computeBestGuess(allSymbols: NormalizedSymbol[], rootModule: string): BestGuess {
  const statePredicates = allSymbols.filter(s =>
    s.rawKind === 'UserDefinedOpKind' && s.level === 1 && (s.arity === 0 || s.arity === undefined)
  );
  const actionPredicates = allSymbols.filter(s =>
    s.rawKind === 'UserDefinedOpKind' && s.level === 2 && (s.arity === 0 || s.arity === undefined)
  );
  const temporalFormulas = allSymbols.filter(s =>
    s.rawKind === 'UserDefinedOpKind' && s.level === 3 && (s.arity === 0 || s.arity === undefined)
  );

  return {
    init: findBestMatch(statePredicates, rootModule, INIT_PATTERNS, 'Init'),
    next: findBestMatch(actionPredicates, rootModule, NEXT_PATTERNS, 'Next'),
    spec: findBestMatch(temporalFormulas, rootModule, SPEC_PATTERNS, 'Spec'),
    invariants: findAllMatching(statePredicates, rootModule, INVARIANT_PATTERNS, 'invariant'),
    properties: findAllMatching(
      temporalFormulas.filter(s => s.name !== 'Spec' && s.name.toLowerCase() !== 'spec'),
      rootModule,
      PROPERTY_PATTERNS,
      'property'
    )
  };
}

function findBestMatch(
  candidates: NormalizedSymbol[],
  rootModule: string,
  patterns: { exact: string; prefixes: string[]; contains: string[] },
  targetName: string
): BestGuessItem | null {
  if (candidates.length === 0) {
    return null;
  }

  const scored: ScoredCandidate[] = [];

  for (const symbol of candidates) {
    const modulePenalty = getModulePenalty(symbol.module, rootModule);
    const { namePenalty, match } = getNameMatch(symbol.name, patterns);
    const score = modulePenalty + namePenalty;

    const moduleType = symbol.module === rootModule ? 'root' :
      isStdlibModule(symbol.module) ? 'stdlib' : 'extended';

    scored.push({
      symbol,
      score,
      match,
      reason: buildReason(moduleType, match, symbol.name, targetName)
    });
  }

  scored.sort((a, b) => {
    if (a.score !== b.score) return a.score - b.score;
    return a.symbol.name.localeCompare(b.symbol.name);
  });

  const best = scored[0];
  return {
    name: best.symbol.name,
    match: best.match,
    reason: best.reason
  };
}

function findAllMatching(
  candidates: NormalizedSymbol[],
  rootModule: string,
  patterns: string[],
  type: 'invariant' | 'property'
): BestGuessItem[] {
  const matches: BestGuessItem[] = [];

  for (const symbol of candidates) {
    const matchedPattern = patterns.find(p =>
      symbol.name.toLowerCase().includes(p.toLowerCase())
    );

    if (matchedPattern) {
      const moduleType = symbol.module === rootModule ? 'root' :
        isStdlibModule(symbol.module) ? 'stdlib' : 'extended';

      matches.push({
        name: symbol.name,
        match: 'contains',
        reason: `${moduleType} module ${type}, name contains '${matchedPattern}'`
      });
    }
  }

  matches.sort((a, b) => {
    const aRoot = a.reason.includes('root');
    const bRoot = b.reason.includes('root');
    const aStdlib = a.reason.includes('stdlib');
    const bStdlib = b.reason.includes('stdlib');

    if (aRoot !== bRoot) return aRoot ? -1 : 1;
    if (aStdlib !== bStdlib) return aStdlib ? 1 : -1;
    return a.name.localeCompare(b.name);
  });

  return matches;
}

function getModulePenalty(moduleName: string, rootModule: string): number {
  if (moduleName === rootModule) {
    return MODULE_PENALTY.root;
  }
  if (isStdlibModule(moduleName)) {
    return MODULE_PENALTY.stdlib;
  }
  return MODULE_PENALTY.extended;
}

function getNameMatch(
  name: string,
  patterns: { exact: string; prefixes: string[]; contains: string[] }
): { namePenalty: number; match: MatchType } {
  if (name === patterns.exact) {
    return { namePenalty: NAME_PENALTY.exact, match: 'exact' };
  }

  if (name.toLowerCase() === patterns.exact.toLowerCase()) {
    return { namePenalty: NAME_PENALTY.case_insensitive_exact, match: 'case_insensitive_exact' };
  }

  for (const prefix of patterns.prefixes) {
    if (name.startsWith(prefix) || name.toLowerCase().startsWith(prefix.toLowerCase())) {
      return { namePenalty: NAME_PENALTY.prefix, match: 'prefix' };
    }
  }

  for (const contains of patterns.contains) {
    if (name.toLowerCase().includes(contains.toLowerCase())) {
      return { namePenalty: NAME_PENALTY.contains, match: 'contains' };
    }
  }

  return { namePenalty: NAME_PENALTY.fallback_first_candidate, match: 'fallback_first_candidate' };
}

function buildReason(
  moduleType: 'root' | 'extended' | 'stdlib',
  match: MatchType,
  symbolName: string,
  targetName: string
): string {
  const matchDesc = match === 'exact' ? 'exact match' :
    match === 'case_insensitive_exact' ? 'case-insensitive exact match' :
    match === 'prefix' ? 'prefix match' :
    match === 'contains' ? 'contains match' :
    'fallback (first available candidate)';

  if (moduleType === 'stdlib') {
    return `${matchDesc} '${symbolName}' in stdlib module (used as last resort for ${targetName})`;
  }

  return `${moduleType} module ${matchDesc} '${symbolName}' for ${targetName}`;
}
