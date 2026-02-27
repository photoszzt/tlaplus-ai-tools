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
// GitHub API helpers
// ---------------------------------------------------------------------------

/**
 * Make a simple HTTPS GET request, returning parsed JSON.
 * @param {string} url
 * @param {number} timeoutMs
 * @returns {Promise<object>}
 */
function httpsGetJson(url, timeoutMs = GITHUB_API_TIMEOUT_MS) {
  return new Promise((resolve, reject) => {
    const req = https.get(url, {
      headers: {
        'User-Agent': 'tlaplus-ai-tools-setup',
        'Accept': 'application/vnd.github+json'
      }
    }, (res) => {
      let body = '';
      res.on('data', chunk => { body += chunk; });
      res.on('end', () => {
        if (res.statusCode !== 200) {
          reject(new Error(`GitHub API returned HTTP ${res.statusCode} for ${url}`));
          return;
        }
        try {
          resolve(JSON.parse(body));
        } catch (e) {
          reject(new Error(`Failed to parse GitHub API response: ${e.message}`));
        }
      });
    });
    req.setTimeout(timeoutMs, () => {
      req.destroy();
      reject(new Error(`GitHub API request timed out after ${timeoutMs / 1000}s`));
    });
    req.on('error', reject);
  });
}

/**
 * Resolve the commit SHA that a GitHub tag currently points to.
 * Handles both lightweight tags (type: "commit") and annotated tags
 * (type: "tag", which must be dereferenced to get the commit SHA).
 *
 * @param {string} owner  - GitHub repo owner, e.g. "tlaplus"
 * @param {string} repo   - GitHub repo name, e.g. "tlaplus"
 * @param {string} tag    - Tag name without "v" prefix, e.g. "1.8.0"
 * @returns {Promise<string>} Commit SHA (40-char hex)
 */
async function fetchTagCommitSha(owner, repo, tag) {
  const refUrl = `https://api.github.com/repos/${owner}/${repo}/git/refs/tags/v${tag}`;
  const ref = await httpsGetJson(refUrl);

  if (ref.object.type === 'commit') {
    return ref.object.sha;
  }

  // Annotated tag — dereference to the underlying commit
  const tagUrl = `https://api.github.com/repos/${owner}/${repo}/git/tags/${ref.object.sha}`;
  const tagObj = await httpsGetJson(tagUrl);
  return tagObj.object.sha;
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
 * Download a pre-release file, pinning by the commit SHA the tag points to.
 *
 * Strategy:
 *  1. Query the GitHub API for the current commit SHA of the release tag.
 *  2. If the lockfile records the same commit SHA and the file exists,
 *     verify the stored checksum and skip the download.
 *  3. Otherwise download the file, compute its sha256, and update the lock.
 *
 * If the GitHub API is unreachable (no network, rate-limited, etc.) and the
 * file already exists with a valid stored checksum, we fall back to the
 * cached version with a warning rather than failing the setup.
 *
 * @param {string} name       - Display name, e.g. "tla2tools.jar"
 * @param {string} url        - Download URL
 * @param {string} destPath   - Local destination path
 * @param {string} lockKey    - Key inside the lockfile, e.g. "tla2tools"
 * @param {string} owner      - GitHub owner, e.g. "tlaplus"
 * @param {string} repo       - GitHub repo, e.g. "tlaplus"
 * @param {string} tag        - Version tag without "v", e.g. "1.8.0"
 */
async function downloadAndVerifyPreRelease(name, url, destPath, lockKey, owner, repo, tag) {
  const lock = readLock();
  const entry = lock[lockKey] || {};

  // --- Step 1: resolve current commit SHA via GitHub API ---
  let currentCommitSha = null;
  try {
    process.stdout.write(`Checking ${name} commit SHA for v${tag}...`);
    currentCommitSha = await fetchTagCommitSha(owner, repo, tag);
    console.log(` ${currentCommitSha.slice(0, 12)}`);
  } catch (err) {
    console.log('');
    console.warn(`  Warning: could not reach GitHub API (${err.message})`);
  }

  // --- Step 2: fast path — tag hasn't moved and file exists ---
  if (
    currentCommitSha &&
    currentCommitSha === entry.commitSha &&
    fs.existsSync(destPath) &&
    entry.sha256
  ) {
    const result = verifyChecksum(destPath, 'sha256', entry.sha256);
    if (result.valid) {
      console.log(`✓ ${name} up-to-date (commit ${currentCommitSha.slice(0, 12)}, sha256 verified)`);
      return;
    }
    console.warn(`  Stored checksum mismatch — re-downloading ${name}`);
  } else if (!currentCommitSha && fs.existsSync(destPath) && entry.sha256) {
    // API unreachable: verify cached file and continue with a warning
    const result = verifyChecksum(destPath, 'sha256', entry.sha256);
    if (result.valid) {
      console.log(`✓ ${name} using cached version (offline mode, sha256 verified)`);
      return;
    }
    console.warn(`  Cached ${name} checksum invalid and GitHub API unreachable.`);
    console.warn(`  Delete ${destPath} and retry with network access.`);
    process.exit(1);
  } else if (currentCommitSha && currentCommitSha !== entry.commitSha) {
    if (entry.commitSha) {
      console.log(`  Tag v${tag} moved: ${entry.commitSha.slice(0, 12)} → ${currentCommitSha.slice(0, 12)}`);
    }
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

  // --- Step 4: compute checksum and update lockfile ---
  const sha256 = calculateChecksum(destPath, 'sha256');
  writeLock(lockKey, {
    commitSha: currentCommitSha || null,
    sha256,
    downloadedAt: new Date().toISOString()
  });

  const commitLabel = currentCommitSha ? ` (commit ${currentCommitSha.slice(0, 12)})` : '';
  console.log(`✓ ${name} locked${commitLabel} — sha256: ${sha256}`);
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
    await downloadAndVerifyPreRelease(
      'tla2tools.jar',
      TLA_TOOLS_URL,
      TLA_TOOLS_PATH,
      'tla2tools',
      'tlaplus',
      'tlaplus',
      TLA_TOOLS_VERSION
    );
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
  fetchTagCommitSha,
  readLock,
  writeLock,
  setup,
  PRE_RELEASE_VERSIONS,
  EXPECTED_CHECKSUMS,
  DEFAULT_TLA_TOOLS_VERSION,
  DEFAULT_COMMUNITY_MODULES_VERSION
};
