import * as path from 'path';
import { runXmlExporter } from './xml-exporter';
import { parseXmlSymbols } from './xml-parser';
import { groupSymbols } from './grouping';
import { computeBestGuess } from './best-guess';
import { SymbolExtractionResult, CandidateGroups } from './types';

export async function extractSymbols(
  tlaFilePath: string,
  toolsDir: string,
  includeExtendedModules: boolean,
  javaHome?: string
): Promise<SymbolExtractionResult> {
  const rootModule = path.basename(tlaFilePath, '.tla');

  const { xml, stderr } = await runXmlExporter(
    tlaFilePath,
    toolsDir,
    includeExtendedModules,
    javaHome
  );

  if (!xml.trim()) {
    throw new Error(`XMLExporter produced no output. stderr: ${stderr}`);
  }

  const allSymbols = parseXmlSymbols(xml);

  const rootSymbols = allSymbols.filter(s => s.module === rootModule);
  const extendedSymbols = allSymbols.filter(s => s.module !== rootModule);

  const candidates = groupSymbols(rootSymbols);

  const extendedModules: Record<string, { candidates: CandidateGroups }> = {};
  if (includeExtendedModules) {
    const moduleNames = [...new Set(extendedSymbols.map(s => s.module))];
    for (const moduleName of moduleNames) {
      const moduleSymbols = extendedSymbols.filter(s => s.module === moduleName);
      extendedModules[moduleName] = {
        candidates: groupSymbols(moduleSymbols)
      };
    }
  }

  const bestGuess = computeBestGuess(allSymbols, rootModule);

  return {
    schemaVersion: 1,
    rootModule,
    file: tlaFilePath,
    includeExtendedModules,
    candidates,
    bestGuess,
    extendedModules
  };
}
