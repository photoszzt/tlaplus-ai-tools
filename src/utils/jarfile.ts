import AdmZip from 'adm-zip';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as crypto from 'crypto';
// @implements REQ-REVIEW-003, SCN-REVIEW-003-01, SCN-REVIEW-003-02
import { withRetry, ErrorCode, enhanceError, classifyError } from './errors';

/**
 * Utilities for reading TLA+ modules from JAR files.
 * JAR files are ZIP archives; we use adm-zip for reading.
 *
 * URI format: jarfile:<jar-path>!/<inner-path>
 * Example: jarfile:/path/to/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla
 */

export interface ParsedJarfileUri {
  jarPath: string;
  innerPath: string;
}

/**
 * Parse a jarfile: URI into its components.
 * @param uri - URI in format jarfile:<jar-path>!/<inner-path>
 * @returns Parsed jar path and inner path
 * @throws Error if URI is malformed
 */
export function parseJarfileUri(uri: string): ParsedJarfileUri {
  if (!uri.startsWith('jarfile:')) {
    throw new Error(`Invalid jarfile URI: must start with 'jarfile:' - got: ${uri}`);
  }

  const withoutScheme = uri.slice('jarfile:'.length);
  const separatorIndex = withoutScheme.indexOf('!');

  if (separatorIndex === -1) {
    throw new Error(`Invalid jarfile URI: missing '!' separator - got: ${uri}`);
  }

  const jarPath = withoutScheme.slice(0, separatorIndex);
  if (!jarPath) {
    throw new Error(`Invalid jarfile URI: empty jar path - got: ${uri}`);
  }

  // Inner path is after '!' - may have leading '/' which we strip
  let innerPath = withoutScheme.slice(separatorIndex + 1);
  if (innerPath.startsWith('/')) {
    innerPath = innerPath.slice(1);
  }

  return { jarPath, innerPath };
}

/**
 * Check if a string is a jarfile: URI.
 */
export function isJarfileUri(uriPath: string): boolean {
  return uriPath.startsWith('jarfile:');
}

export function listJarEntries(jarPath: string, innerDir: string): string[] {
  const zip = new AdmZip(jarPath);
  const entries = zip.getEntries();

  let normalizedDir = innerDir.replace(/\\/g, '/');
  if (normalizedDir.endsWith('/')) {
    normalizedDir = normalizedDir.slice(0, -1);
  }

  const prefix = normalizedDir ? normalizedDir + '/' : '';
  const results: string[] = [];

  for (const entry of entries) {
    if (entry.isDirectory) continue;

    const entryPath = entry.entryName.replace(/\\/g, '/');

    if (prefix) {
      if (!entryPath.startsWith(prefix)) continue;
      const relativePath = entryPath.slice(prefix.length);
      if (relativePath.includes('/')) continue;
      results.push(relativePath);
    } else {
      if (entryPath.includes('/')) continue;
      results.push(entryPath);
    }
  }

  return results;
}

export function listTlaModulesInJar(
  jarPath: string,
  innerDir: string,
  returnFullUri: boolean = false
): string[] {
  const entries = listJarEntries(jarPath, innerDir);

  const tlaModules = entries.filter((name) => {
    if (!name.endsWith('.tla')) return false;
    if (name.startsWith('_')) return false;
    return true;
  });

  if (!returnFullUri) {
    return tlaModules;
  }

  let normalizedDir = innerDir.replace(/\\/g, '/');
  if (normalizedDir.endsWith('/')) {
    normalizedDir = normalizedDir.slice(0, -1);
  }

  return tlaModules.map((name) => {
    const innerPath = normalizedDir ? `${normalizedDir}/${name}` : name;
    return `jarfile:${jarPath}!/${innerPath}`;
  });
}

/**
 * Simple LRU cache using Map insertion order.
 * Map.keys() returns keys in insertion order; deleting and re-inserting
 * moves a key to the end (most recently used).
 *
 * @implements REQ-REVIEW-004, SCN-REVIEW-004-01, SCN-REVIEW-004-03
 * @invariant INV-REVIEW-001 (cache size bounded)
 */
export class LRUCache<K, V> {
  private map = new Map<K, V>();
  private readonly maxSize: number;
  private readonly onEvict?: (key: K, value: V) => Promise<void> | void;
  private pendingEvictions = new Set<Promise<void>>();

  constructor(maxSize: number, onEvict?: (key: K, value: V) => Promise<void> | void) {
    if (maxSize < 1) {
      throw new RangeError(`LRUCache maxSize must be at least 1, got ${maxSize}`);
    }
    this.maxSize = maxSize;
    this.onEvict = onEvict;
  }

  private trackEviction(result: Promise<void> | void): void {
    if (result && typeof (result as Promise<void>).then === 'function') {
      const promise = result as Promise<void>;
      this.pendingEvictions.add(promise);
      promise.finally(() => this.pendingEvictions.delete(promise));
    }
  }

  get(key: K): V | undefined {
    if (!this.map.has(key)) {
      return undefined;
    }
    const value = this.map.get(key);
    // Move to end (most recently used)
    this.map.delete(key);
    this.map.set(key, value as V);
    return value as V;
  }

  set(key: K, value: V): void {
    if (this.map.has(key)) {
      this.map.delete(key);
    } else if (this.map.size >= this.maxSize) {
      // Evict least recently used (first key)
      // Use iterator done flag instead of checking value !== undefined,
      // because Map can legitimately contain undefined as a key.
      const firstEntry = this.map.keys().next();
      if (!firstEntry.done) {
        const firstKey = firstEntry.value;
        const evictedValue = this.map.get(firstKey)!;
        this.map.delete(firstKey);
        // @implements SCN-REVIEW-004-05
        this.trackEviction(this.onEvict?.(firstKey, evictedValue));
        // @implements SCN-REVIEW-004-04
        if (process.env.DEBUG || process.env.VERBOSE) {
          console.error(`JAR cache eviction: removing entry ${String(firstKey)} (size: ${this.map.size}/${this.maxSize})`);
        }
      }
    }
    this.map.set(key, value);
  }

  has(key: K): boolean {
    return this.map.has(key);
  }

  clear(): void {
    if (this.onEvict) {
      for (const [key, value] of this.map) {
        this.trackEviction(this.onEvict(key, value));
      }
    }
    this.map.clear();
  }

  async flush(): Promise<void> {
    await Promise.all([...this.pendingEvictions]);
    this.pendingEvictions.clear();
  }

  get size(): number {
    return this.map.size;
  }
}

/**
 * Get maximum cache size from environment variable or default.
 *
 * @implements REQ-REVIEW-004, SCN-REVIEW-004-02
 */
export function getMaxCacheSize(): number {
  const envValue = process.env.TLA_JAR_CACHE_SIZE;
  if (envValue) {
    const parsed = parseInt(envValue, 10);
    if (Number.isFinite(parsed) && parsed > 0) {
      return parsed;
    }
  }
  return 256;
}

// @implements REQ-REVIEW-004, SCN-REVIEW-004-05
const extractionCache = new LRUCache<string, string>(getMaxCacheSize(), async (_key, cachedPath) => {
  // Determine the correct directory to remove.
  // extractJarEntry stores a file path (e.g., <cacheDir>/<hash>/Module.tla),
  // while extractJarDirectory stores a directory path (e.g., <cacheDir>/<hash>).
  // For file paths we must delete the parent directory to avoid orphaned dirs.
  try {
    const stats = await fs.promises.stat(cachedPath);
    const dirToRemove = stats.isFile() ? path.dirname(cachedPath) : cachedPath;
    await fs.promises.rm(dirToRemove, { recursive: true, force: true });
  } catch (err) {
    if (process.env.DEBUG || process.env.VERBOSE) {
      console.error('Failed to remove cached extraction path:', cachedPath, err);
    }
  }
});

async function getCacheDir(): Promise<string> {
  const cacheBase = path.join(os.tmpdir(), 'tlaplus-mcp', 'jar-cache');
  await fs.promises.mkdir(cacheBase, { recursive: true });
  return cacheBase;
}

async function getCacheKey(jarPath: string, innerPath: string): Promise<string> {
  const stats = await fs.promises.stat(jarPath);
  const data = `${jarPath}:${stats.mtimeMs}:${innerPath}`;
  return crypto.createHash('sha256').update(data).digest('hex').slice(0, 16);
}

export async function clearJarCache(): Promise<void> {
  extractionCache.clear();
  await extractionCache.flush();
}

// @implements REQ-REVIEW-003, SCN-REVIEW-003-01
export async function extractJarEntry(jarPath: string, innerPath: string): Promise<string> {
  // Validation stays outside retry
  if (innerPath.includes('..') || path.isAbsolute(innerPath)) {
    throw new Error(`Invalid inner path (path traversal rejected): ${innerPath}`);
  }

  const cacheKey = await getCacheKey(jarPath, innerPath);

  const cached = extractionCache.get(cacheKey);
  if (cached) {
    try {
      await fs.promises.access(cached);
      return cached;
    } catch {
      // Cache entry stale, continue to extraction
    }
  }

  // Wrap extraction in retry (async, no busy-wait)
  return withRetry(
    async () => {
      const zip = new AdmZip(jarPath);
      const entry = zip.getEntry(innerPath) || zip.getEntry(innerPath.replace(/\//g, '\\'));

      if (!entry) {
        throw enhanceError(
          new Error(`Entry '${innerPath}' not found in JAR: ${jarPath}`),
          { code: ErrorCode.JAR_ENTRY_NOT_FOUND }
        );
      }

      const cacheDir = await getCacheDir();
      const extractDir = path.join(cacheDir, cacheKey);

      // Use async fs operations to avoid blocking the event loop in HTTP mode
      try {
        await fs.promises.mkdir(extractDir, { recursive: true });
      } catch (err) {
        throw enhanceError(err as Error, {
          code: ErrorCode.JAR_EXTRACTION_FAILED,
          context: { jarPath, innerPath, extractDir }
        });
      }

      const targetPath = path.join(extractDir, path.basename(innerPath));

      try {
        await fs.promises.writeFile(targetPath, entry.getData());
      } catch (err) {
        throw enhanceError(err as Error, {
          code: ErrorCode.JAR_EXTRACTION_FAILED,
          context: { jarPath, innerPath, targetPath }
        });
      }

      extractionCache.set(cacheKey, targetPath);
      return targetPath;
    },
    {
      maxAttempts: 3,
      initialDelayMs: 100,
      maxDelayMs: 10000,
      backoffMultiplier: 10,
      shouldRetry: (error) => {
        const code = classifyError(error);
        return code === ErrorCode.JAR_LOCKED || code === ErrorCode.JAR_EXTRACTION_FAILED;
      }
    }
  );
}

// @implements REQ-REVIEW-003, SCN-REVIEW-003-02
export async function extractJarDirectory(jarPath: string, innerDir: string): Promise<string> {
  // Validation stays outside retry
  if (innerDir.includes('..') || (innerDir && path.isAbsolute(innerDir))) {
    throw new Error(`Invalid inner path (path traversal rejected): ${innerDir}`);
  }

  const cacheKey = await getCacheKey(jarPath, `dir:${innerDir}`);

  const cached = extractionCache.get(cacheKey);
  if (cached) {
    try {
      await fs.promises.access(cached);
      return cached;
    } catch {
      // Cache entry stale, continue to extraction
    }
  }

  // Wrap extraction in retry (async, no busy-wait)
  return withRetry(
    async () => {
      const zip = new AdmZip(jarPath);
      const entries = zip.getEntries();

      let normalizedDir = innerDir.replace(/\\/g, '/');
      if (normalizedDir.endsWith('/')) {
        normalizedDir = normalizedDir.slice(0, -1);
      }
      const prefix = normalizedDir ? normalizedDir + '/' : '';

      const cacheDir = await getCacheDir();
      const extractDir = path.join(cacheDir, cacheKey);

      // Use async fs operations to avoid blocking the event loop in HTTP mode
      try {
        await fs.promises.mkdir(extractDir, { recursive: true });
      } catch (err) {
        throw enhanceError(err as Error, {
          code: ErrorCode.JAR_EXTRACTION_FAILED,
          context: { jarPath, innerDir, extractDir }
        });
      }

      for (const entry of entries) {
        if (entry.isDirectory) continue;

        const entryPath = entry.entryName.replace(/\\/g, '/');
        if (prefix && !entryPath.startsWith(prefix)) continue;

        const relativePath = prefix ? entryPath.slice(prefix.length) : entryPath;

        if (relativePath.includes('..')) continue;

        const targetPath = path.join(extractDir, relativePath);
        const targetDir = path.dirname(targetPath);

        // Use async fs operations for subdirectory creation
        try {
          await fs.promises.mkdir(targetDir, { recursive: true });
        } catch (err) {
          throw enhanceError(err as Error, {
            code: ErrorCode.JAR_EXTRACTION_FAILED,
            context: { jarPath, innerDir, targetDir }
          });
        }

        // Use async fs operations for file write
        try {
          await fs.promises.writeFile(targetPath, entry.getData());
        } catch (err) {
          throw enhanceError(err as Error, {
            code: ErrorCode.JAR_EXTRACTION_FAILED,
            context: { jarPath, innerDir, targetPath }
          });
        }
      }

      extractionCache.set(cacheKey, extractDir);
      return extractDir;
    },
    {
      maxAttempts: 3,
      initialDelayMs: 100,
      maxDelayMs: 10000,
      backoffMultiplier: 10,
      shouldRetry: (error) => {
        const code = classifyError(error);
        return code === ErrorCode.JAR_LOCKED || code === ErrorCode.JAR_EXTRACTION_FAILED;
      }
    }
  );
}

// @implements REQ-REVIEW-003, SCN-REVIEW-003-03
export async function resolveJarfilePath(uri: string): Promise<string> {
  const { jarPath, innerPath } = parseJarfileUri(uri);

  if (!innerPath) {
    throw new Error(`Cannot resolve jarfile URI without inner path: ${uri}`);
  }

  const innerDir = path.dirname(innerPath).replace(/\\/g, '/');
  const fileName = path.basename(innerPath);

  const normalizedDir = innerDir === '.' ? '' : innerDir;
  const extractedDir = await extractJarDirectory(jarPath, normalizedDir);

  return path.join(extractedDir, fileName);
}
