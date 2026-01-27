import { XMLParser } from 'fast-xml-parser';
import { NormalizedSymbol, SymbolLocation, RawSymbolKind } from './types';

export function parseXmlSymbols(xmlContent: string): NormalizedSymbol[] {
  const parser = new XMLParser({
    ignoreAttributes: false,
    attributeNamePrefix: '',
    isArray: (name) => ['entry', 'ModuleNodeRef', 'operands', 'params'].includes(name)
  });

  const xmlObj = parser.parse(xmlContent);

  if (!xmlObj.modules) {
    return [];
  }

  const symbols: NormalizedSymbol[] = [];

  if (xmlObj.modules.context?.entry) {
    for (const entry of xmlObj.modules.context.entry) {
      const symbol = parseEntry(entry);
      if (symbol) {
        symbols.push(symbol);
      }
    }
  }

  return symbols;
}

function parseEntry(entry: unknown): NormalizedSymbol | null {
  const e = entry as Record<string, unknown>;
  let node: Record<string, unknown>;
  let rawKind: RawSymbolKind;

  if (e.UserDefinedOpKind) {
    node = e.UserDefinedOpKind as Record<string, unknown>;
    rawKind = 'UserDefinedOpKind';
  } else if (e.OpDeclNode) {
    node = e.OpDeclNode as Record<string, unknown>;
    rawKind = 'OpDeclNode';
  } else if (e.TheoremDefNode) {
    node = e.TheoremDefNode as Record<string, unknown>;
    rawKind = 'TheoremDefNode';
  } else if (e.AssumeDef) {
    node = e.AssumeDef as Record<string, unknown>;
    rawKind = 'AssumeDef';
  } else {
    return null;
  }

  const uniqueName = node.uniquename as string | undefined;
  if (!uniqueName) {
    return null;
  }

  const { module, name } = parseUniqueName(uniqueName);
  const location = parseLocation(node.location);

  const level = node.level !== undefined ? parseInt(String(node.level), 10) as 0 | 1 | 2 | 3 : undefined;
  const arity = node.arity !== undefined ? parseInt(String(node.arity), 10) : undefined;
  const preComments = node['pre-comments'] as string | undefined;
  const comment = preComments?.trim() || undefined;

  return {
    name,
    module,
    uniqueName,
    level,
    arity,
    location,
    comment,
    rawKind
  };
}

function parseUniqueName(uniqueName: string): { module: string; name: string } {
  const bangIndex = uniqueName.indexOf('!');
  if (bangIndex === -1) {
    return { module: '', name: uniqueName };
  }
  return {
    module: uniqueName.substring(0, bangIndex),
    name: uniqueName.substring(bangIndex + 1)
  };
}

function parseLocation(loc: unknown): SymbolLocation | undefined {
  if (!loc) {
    return undefined;
  }

  const l = loc as Record<string, unknown>;
  const line = l.line as Record<string, unknown> | undefined;
  const column = l.column as Record<string, unknown> | undefined;

  return {
    file: l.filename as string | undefined,
    start: {
      line: parseInt(String(line?.begin || '0'), 10),
      col: parseInt(String(column?.begin || '0'), 10)
    },
    end: {
      line: parseInt(String(line?.end || '0'), 10),
      col: parseInt(String(column?.end || '0'), 10)
    }
  };
}
