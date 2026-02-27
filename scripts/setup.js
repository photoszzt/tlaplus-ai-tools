#!/usr/bin/env node

const https = require('https');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

// Pinned versions (strict mode - overrides must match these)
const DEFAULT_TLA_TOOLS_VERSION = '1.8.0';
const DEFAULT_COMMUNITY_MODULES_VERSION = '202601200755';

// Pre-release versions: pinned by commit SHA rather than artifact checksum,
// because GitHub rebuilds the release asset on every commit to the tag.
const PRE_RELEASE_VERSIONS = ['1.8.0'];

// Expected checksums for stable (non-pre-release) versions only.
const EXPECTED_CHECKSUMS = {
  communityModules: {
    version: '202601200755',
    algorithm: 'sha256',
    checksum: '5b7bb6d94ea1ccfdd2611716b81430208f709b493ae7b4f39fa7cb86a602932e'
  }
};

// Get versions from environment or use defaults
const TLA_TOOLS_VERSION = process.env.TLA_TOOLS_VERSION || DEFAULT_TLA_TOOLS_VERSION;
const COMMUNITY_MODULES_VERSION = process.env.COMMUNITY_MODULES_VERSION || DEFAULT_COMMUNITY_MODULES_VERSION;

// Strict mode: reject version overrides that don't match pinned versions
if (TLA_TOOLS_VERSION !== DEFAULT_TLA_TOOLS_VERSION) {
  console.error(`✗ Error: TLA_TOOLS_VERSION override rejected`);
  console.error(`  Expected: ${DEFAULT_TLA_TOOLS_VERSION}`);
  console.error(`  Got: ${TLA_TOOLS_VERSION}`);
  console.error(`  This plugin requires exact version ${DEFAULT_TLA_TOOLS_VERSION}.`);
  process.exit(1);
}

if (COMMUNITY_MODULES_VERSION !== DEFAULT_COMMUNITY_MODULES_VERSION) {
  console.error(`✗ Error: COMMUNITY_MODULES_VERSION override rejected`);
  console.error(`  Expected: ${DEFAULT_COMMUNITY_MODULES_VERSION}`);
  console.error(`  Got: ${COMMUNITY_MODULES_VERSION}`);
  console.error(`  This plugin requires exact version ${DEFAULT_COMMUNITY_MODULES_VERSION} for checksum verification.`);
  process.exit(1);
}

// URLs
const TLA_TOOLS_URL = `https://github.com/tlaplus/tlaplus/releases/download/v${TLA_TOOLS_VERSION}/tla2tools.jar`;
const COMMUNITY_MODULES_URL = `https://github.com/tlaplus/CommunityModules/releases/download/${COMMUNITY_MODULES_VERSION}/CommunityModules-deps.jar`;

// Paths (support TLA_TOOLS_DIR environment variable)
const TOOLS_DIR = process.env.TLA_TOOLS_DIR || path.join(__dirname, '..', 'tools');
const TLA_TOOLS_PATH = path.join(TOOLS_DIR, 'tla2tools.jar');
const COMMUNITY_MODULES_PATH = path.join(TOOLS_DIR, 'CommunityModules-deps.jar');
const LOCK_FILE_PATH = path.join(TOOLS_DIR, '.setup-lock.json');

const MAX_REDIRECTS = 5;
const TIMEOUT_MS = 120000;
const GITHUB_API_TIMEOUT_MS = 10000;

// ---------------------------------------------------------------------------
// Lockfile helpers
// ---------------------------------------------------------------------------

/**
 * Read the setup lockfile, returning {} if missing or malformed.
 * @returns {object}
 */
function readLock() {
  try {
    return JSON.parse(fs.readFileSync(LOCK_FILE_PATH, 'utf8'));
  } catch {
    return {};
  }
}

/**
 * Merge `entry` into the lockfile under `key` and write it back.
 * @param {string} key
 * @param {object} entry
 */
function writeLock(key, entry) {
  const lock = readLock();
  lock[key] = entry;
  fs.writeFileSync(LOCK_FILE_PATH, JSON.stringify(lock, null, 2) + '\n', 'utf8');
}

// ---------------------------------------------------------------------------
// Asset URL resolution (no GitHub API auth required)
// ---------------------------------------------------------------------------

/**
 * Resolve the final URL of a download link by following HTTP redirects
 * using a HEAD request (no body downloaded).
 *
 * GitHub release assets redirect to a CDN URL that embeds an asset ID,
 * e.g. https://objects.githubusercontent.com/github-production-release-asset-NNN/
 * That URL changes whenever the release asset is replaced, even if the
 * tag/release name stays the same — making it a reliable staleness signal
 * without needing GitHub API authentication.
 *
 * @param {string} url           - Starting URL
 * @param {number} redirectCount - Internal recursion counter
 * @returns {Promise<string>}    - Final URL after all redirects
 */
function resolveAssetUrl(url, redirectCount = 0) {
  return new Promise((resolve, reject) => {
    if (redirectCount > MAX_REDIRECTS) {
      reject(new Error(`Too many redirects resolving asset URL`));
      return;
    }

    const parsed = new URL(url);
    const req = https.request(
      {
        hostname: parsed.hostname,
        path: parsed.pathname + parsed.search,
        method: 'HEAD',
        headers: { 'User-Agent': 'tlaplus-ai-tools-setup' }
      },
      (res) => {
        if ([301, 302, 303, 307, 308].includes(res.statusCode) && res.headers.location) {
          const next = res.headers.location.startsWith('http')
            ? res.headers.location
            : `https://${parsed.hostname}${res.headers.location}`;
          resolveAssetUrl(next, redirectCount + 1).then(resolve).catch(reject);
        } else if (res.statusCode === 200) {
          resolve(url);
        } else {
          reject(new Error(`HEAD request returned HTTP ${res.statusCode} for ${url}`));
        }
      }
    );

    req.setTimeout(GITHUB_API_TIMEOUT_MS, () => {
      req.destroy();
      reject(new Error(`HEAD request timed out`));
    });
    req.on('error', reject);
    req.end();
  });
}

// ---------------------------------------------------------------------------
// Checksum helpers
// ---------------------------------------------------------------------------

/**
 * Calculate checksum of a file.
 * @param {string} filePath
 * @param {string} algorithm - e.g. "sha256"
 * @returns {string} Hex-encoded checksum
 */
function calculateChecksum(filePath, algorithm) {
  const hash = crypto.createHash(algorithm);
  const data = fs.readFileSync(filePath);
  hash.update(data);
  return hash.digest('hex');
}

/**
 * Verify file checksum matches expected value.
 * @param {string} filePath
 * @param {string} algorithm
 * @param {string} expectedChecksum
 * @returns {{valid: boolean, actual: string, expected: string}}
 */
function verifyChecksum(filePath, algorithm, expectedChecksum) {
  const actual = calculateChecksum(filePath, algorithm);
  return { valid: actual === expectedChecksum, actual, expected: expectedChecksum };
}

// ---------------------------------------------------------------------------
// Download helpers
// ---------------------------------------------------------------------------

/**
 * Download a file with redirect following.
 * @param {string} url
 * @param {string} destPath
 * @param {number} redirectCount
 * @returns {Promise<void>}
 */
function downloadFile(url, destPath, redirectCount = 0) {
  return new Promise((resolve, reject) => {
    if (redirectCount > MAX_REDIRECTS) {
      reject(new Error(`Too many redirects (max ${MAX_REDIRECTS})`));
      return;
    }

    const tempPath = destPath + '.tmp';
    const file = fs.createWriteStream(tempPath);
    let timeout;

    const cleanup = () => {
      if (timeout) clearTimeout(timeout);
      file.close();
      if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
    };

    timeout = setTimeout(() => {
      cleanup();
      reject(new Error(`Download timeout after ${TIMEOUT_MS / 1000}s`));
    }, TIMEOUT_MS);

    https.get(url, (response) => {
      const { statusCode } = response;

      if ([301, 302, 303, 307, 308].includes(statusCode)) {
        const redirectUrl = response.headers.location;
        if (!redirectUrl) {
          cleanup();
          reject(new Error(`Redirect without Location header (status ${statusCode})`));
          return;
        }
        clearTimeout(timeout);
        file.close();
        if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
        console.log(`  Following redirect...`);
        downloadFile(redirectUrl, destPath, redirectCount + 1).then(resolve).catch(reject);
        return;
      }

      if (statusCode !== 200) {
        cleanup();
        reject(new Error(`HTTP ${statusCode} from ${url}`));
        return;
      }

      response.pipe(file);

      file.on('finish', () => {
        clearTimeout(timeout);
        file.close(() => {
          fs.renameSync(tempPath, destPath);
          resolve();
        });
      });

      file.on('error', (err) => { cleanup(); reject(err); });
    }).on('error', (err) => { cleanup(); reject(err); });
  });
}

// ---------------------------------------------------------------------------
// Core download + verification logic
// ---------------------------------------------------------------------------

/**
 * Download a stable-release file and verify its pinned checksum.
 * Skips download if file already exists and checksum matches.
 *
 * @param {string} name
 * @param {string} url
 * @param {string} destPath
 * @param {string} algorithm
 * @param {string} expectedChecksum
 */
async function downloadAndVerify(name, url, destPath, algorithm, expectedChecksum) {
  if (fs.existsSync(destPath)) {
    console.log(`Verifying ${name} checksum...`);
    const result = verifyChecksum(destPath, algorithm, expectedChecksum);
    if (result.valid) {
      console.log(`✓ ${name} checksum verified (${algorithm}: ${result.expected})`);
      return;
    }
    console.error(`✗ ${name} checksum mismatch!`);
    console.error(`  Expected (${algorithm}): ${result.expected}`);
    console.error(`  Actual   (${algorithm}): ${result.actual}`);
    console.error(`  File may be corrupted. Delete ${destPath} and run setup again.`);
    process.exit(1);
  }

  console.log(`Downloading ${name} from ${url}...`);
  try {
    await downloadFile(url, destPath);
    console.log(`✓ Downloaded ${name}`);
  } catch (err) {
    console.error(`✗ Failed to download ${name}: ${err.message}`);
    process.exit(1);
  }

  console.log(`Verifying ${name} checksum...`);
  const result = verifyChecksum(destPath, algorithm, expectedChecksum);
  if (!result.valid) {
    console.error(`✗ ${name} checksum mismatch after download!`);
    console.error(`  Expected (${algorithm}): ${result.expected}`);
    console.error(`  Actual   (${algorithm}): ${result.actual}`);
    console.error(`  Download may be corrupted or incomplete.`);
    fs.unlinkSync(destPath);
    process.exit(1);
  }
  console.log(`✓ ${name} checksum verified (${algorithm}: ${result.expected})`);
}

/**
 * Download a pre-release file, pinning by the CDN asset URL the release
 * tag currently resolves to.
 *
 * Strategy:
 *  1. Send a HEAD request to the download URL and follow redirects to the
 *     final CDN URL. GitHub's CDN URL embeds an asset ID that changes
 *     whenever the release asset is replaced (even if the tag stays the same).
 *     This requires no GitHub API authentication.
 *  2. If the lockfile records the same CDN URL and the file exists,
 *     verify the stored sha256 and skip the download.
 *  3. Otherwise download the file, compute its sha256, and update the lock.
 *
 * If the HEAD request fails (offline, network error) and the file already
 * exists with a valid stored sha256, we fall back to the cached version
 * with a warning rather than failing the setup.
 *
 * @param {string} name     - Display name, e.g. "tla2tools.jar"
 * @param {string} url      - Download URL
 * @param {string} destPath - Local destination path
 * @param {string} lockKey  - Key inside the lockfile, e.g. "tla2tools"
 */
async function downloadAndVerifyPreRelease(name, url, destPath, lockKey) {
  const lock = readLock();
  const entry = lock[lockKey] || {};

  // --- Step 1: resolve current CDN asset URL via HEAD + redirect ---
  let currentAssetUrl = null;
  try {
    process.stdout.write(`Checking ${name} asset URL...`);
    const rawUrl = await resolveAssetUrl(url);
    // Strip query string: the CDN URL contains time-limited SAS tokens
    // (se=, sig=, jwt=, etc.) that change on every request. Only the path
    // encodes the asset ID, which is the stable staleness signal we care about.
    currentAssetUrl = new URL(rawUrl).origin + new URL(rawUrl).pathname;
    // Print the last two path segments as a short identifier
    const id = currentAssetUrl.split('/').slice(-2).join('/');
    console.log(` ${id}`);
  } catch (err) {
    console.log('');
    console.warn(`  Warning: could not resolve asset URL (${err.message})`);
  }

  // --- Step 2: fast path — asset hasn't changed and file exists ---
  if (currentAssetUrl && currentAssetUrl === entry.assetUrl && fs.existsSync(destPath) && entry.sha256) {
    const result = verifyChecksum(destPath, 'sha256', entry.sha256);
    if (result.valid) {
      console.log(`✓ ${name} up-to-date (asset unchanged, sha256 verified)`);
      return;
    }
    console.warn(`  Stored checksum mismatch — re-downloading ${name}`);
  } else if (!currentAssetUrl && fs.existsSync(destPath) && entry.sha256) {
    // Offline fallback: verify cached file and continue with a warning
    const result = verifyChecksum(destPath, 'sha256', entry.sha256);
    if (result.valid) {
      console.log(`✓ ${name} using cached version (offline, sha256 verified)`);
      return;
    }
    console.warn(`  Cached ${name} sha256 invalid and network unreachable.`);
    console.warn(`  Delete ${destPath} and retry with network access.`);
    process.exit(1);
  } else if (currentAssetUrl && currentAssetUrl !== entry.assetUrl && entry.assetUrl) {
    console.log(`  Asset updated — re-downloading ${name}`);
  }

  // --- Step 3: download ---
  console.log(`Downloading ${name} from ${url}...`);
  try {
    await downloadFile(url, destPath);
    console.log(`✓ Downloaded ${name}`);
  } catch (err) {
    console.error(`✗ Failed to download ${name}: ${err.message}`);
    process.exit(1);
  }

  // --- Step 4: compute sha256 and update lockfile ---
  const sha256 = calculateChecksum(destPath, 'sha256');
  writeLock(lockKey, {
    assetUrl: currentAssetUrl || null,
    sha256,
    downloadedAt: new Date().toISOString()
  });

  console.log(`✓ ${name} locked — sha256: ${sha256}`);
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

async function setup() {
  console.log('TLA+ Tools Setup');
  console.log('================');
  console.log(`TLA Tools Version:        ${TLA_TOOLS_VERSION}`);
  console.log(`Community Modules Version: ${COMMUNITY_MODULES_VERSION}`);
  console.log(`Tools Directory:           ${TOOLS_DIR}`);
  console.log('');

  if (!fs.existsSync(TOOLS_DIR)) {
    console.log(`Creating directory: ${TOOLS_DIR}`);
    fs.mkdirSync(TOOLS_DIR, { recursive: true });
  }

  if (PRE_RELEASE_VERSIONS.includes(TLA_TOOLS_VERSION)) {
    await downloadAndVerifyPreRelease('tla2tools.jar', TLA_TOOLS_URL, TLA_TOOLS_PATH, 'tla2tools');
  } else {
    await downloadAndVerify(
      'tla2tools.jar',
      TLA_TOOLS_URL,
      TLA_TOOLS_PATH,
      EXPECTED_CHECKSUMS.tla2tools.algorithm,
      EXPECTED_CHECKSUMS.tla2tools.checksum
    );
  }

  await downloadAndVerify(
    'CommunityModules-deps.jar',
    COMMUNITY_MODULES_URL,
    COMMUNITY_MODULES_PATH,
    EXPECTED_CHECKSUMS.communityModules.algorithm,
    EXPECTED_CHECKSUMS.communityModules.checksum
  );

  console.log('');
  console.log('Setup complete!');
  console.log('');
  console.log('Next steps:');
  console.log('1. Ensure Java is installed: java -version');
  console.log('2. Test TLC: java -jar tools/tla2tools.jar');
}

// Run setup
if (require.main === module) {
  setup().catch((err) => {
    console.error(`Setup failed: ${err.message}`);
    process.exit(1);
  });
}

module.exports = {
  calculateChecksum,
  verifyChecksum,
  downloadFile,
  downloadAndVerify,
  downloadAndVerifyPreRelease,
  resolveAssetUrl,
  readLock,
  writeLock,
  setup,
  PRE_RELEASE_VERSIONS,
  EXPECTED_CHECKSUMS,
  DEFAULT_TLA_TOOLS_VERSION,
  DEFAULT_COMMUNITY_MODULES_VERSION
};
