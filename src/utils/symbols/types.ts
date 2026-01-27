/**
 * Types for TLA+ symbol extraction and TLC config generation
 */

/** Match types for bestGuess scoring */
export type MatchType =
  | 'exact'
  | 'case_insensitive_exact'
  | 'prefix'
  | 'contains'
  | 'fallback_first_candidate';

/** Location within a TLA+ file */
export interface SymbolLocation {
  file?: string;
  start: { line: number; col: number };
  end: { line: number; col: number };
}

/** Raw kind from XMLExporter entry type */
export type RawSymbolKind =
  | 'OpDeclNode'
  | 'UserDefinedOpKind'
  | 'TheoremDefNode'
  | 'AssumeDef'
  | string;

/**
 * Normalized symbol extracted from XMLExporter output
 * 
 * Level meanings (TLA+ semantic levels):
 * - 0: constant expressions
 * - 1: state expressions (can reference variables)
 * - 2: action expressions (can reference primed variables)
 * - 3: temporal formulas
 */
export interface NormalizedSymbol {
  name: string;
  module: string;
  uniqueName: string;
  level?: 0 | 1 | 2 | 3;
  arity?: number;
  location?: SymbolLocation;
  comment?: string;
  rawKind: RawSymbolKind;
}

/** Symbol with minimal info for output (excludes internal fields) */
export interface OutputSymbol {
  name: string;
  location?: SymbolLocation;
  comment?: string;
}

/** TLC-oriented candidate groups (per module) */
export interface CandidateGroups {
  /** CONSTANT declarations (level 0, from OpDeclNode) */
  constants: OutputSymbol[];
  /** VARIABLE declarations (level 1, from OpDeclNode) */
  variables: OutputSymbol[];
  /** State predicates: arity=0, level=1 operators (e.g., Init, TypeOK) */
  statePredicates: OutputSymbol[];
  /** Action predicates: arity=0, level=2 operators (e.g., Next) */
  actionPredicates: OutputSymbol[];
  /** Temporal formulas: arity=0, level=3 operators (e.g., Spec, Liveness) */
  temporalFormulas: OutputSymbol[];
  /** Operators with arguments (arity > 0) */
  operatorsWithArgs: OutputSymbol[];
  /** Theorem definitions */
  theorems: OutputSymbol[];
  /** Assumption definitions */
  assumptions: OutputSymbol[];
}

/** A single bestGuess pick with explanation */
export interface BestGuessItem {
  name: string;
  match: MatchType;
  reason: string;
}

/** bestGuess section with Init/Next/Spec and property lists */
export interface BestGuess {
  init: BestGuessItem | null;
  next: BestGuessItem | null;
  spec: BestGuessItem | null;
  invariants: BestGuessItem[];
  properties: BestGuessItem[];
}

/**
 * Complete symbol extraction result
 * 
 * schemaVersion: Bump only for breaking changes to response shape
 */
export interface SymbolExtractionResult {
  schemaVersion: 1;
  rootModule: string;
  file: string;
  includeExtendedModules: boolean;
  candidates: CandidateGroups;
  bestGuess: BestGuess;
  /** Nested by module name when includeExtendedModules=true */
  extendedModules: Record<string, { candidates: CandidateGroups }>;
}

/** Index file export */
export interface SymbolTypes {
  NormalizedSymbol: NormalizedSymbol;
  OutputSymbol: OutputSymbol;
  CandidateGroups: CandidateGroups;
  BestGuessItem: BestGuessItem;
  BestGuess: BestGuess;
  SymbolExtractionResult: SymbolExtractionResult;
  MatchType: MatchType;
  SymbolLocation: SymbolLocation;
  RawSymbolKind: RawSymbolKind;
}
