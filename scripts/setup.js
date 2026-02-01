#!/usr/bin/env node

const https = require('https');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

// Pinned versions (strict mode - overrides must match these)
const DEFAULT_TLA_TOOLS_VERSION = '1.8.0';
const DEFAULT_COMMUNITY_MODULES_VERSION = '202601200755';

// Expected checksums for pinned versions
const EXPECTED_CHECKSUMS = {
  tla2tools: {
    version: '1.8.0',
    algorithm: 'sha1',
    checksum: '8fc5476ff65dad2e65dfe7b3109b3867e27c4f29'
  },
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
  console.error(`  This plugin requires exact version ${DEFAULT_TLA_TOOLS_VERSION} for checksum verification.`);
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

const MAX_REDIRECTS = 5;
const TIMEOUT_MS = 120000;

/**
 * Calculate checksum of a file
 * @param {string} filePath - Path to file
 * @param {string} algorithm - Hash algorithm (sha1, sha256, etc.)
 * @returns {string} Hex-encoded checksum
 */
function calculateChecksum(filePath, algorithm) {
  const hash = crypto.createHash(algorithm);
  const data = fs.readFileSync(filePath);
  hash.update(data);
  return hash.digest('hex');
}

/**
 * Verify file checksum matches expected value
 * @param {string} filePath - Path to file
 * @param {string} algorithm - Hash algorithm
 * @param {string} expectedChecksum - Expected checksum value
 * @returns {{valid: boolean, actual: string, expected: string}}
 */
function verifyChecksum(filePath, algorithm, expectedChecksum) {
  const actual = calculateChecksum(filePath, algorithm);
  return {
    valid: actual === expectedChecksum,
    actual,
    expected: expectedChecksum
  };
}

/**
 * Download a file with redirect handling
 * @param {string} url - URL to download from
 * @param {string} destPath - Destination file path
 * @param {number} redirectCount - Current redirect depth
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
            if (timeout) {
                clearTimeout(timeout);
            }
            file.close();
            if (fs.existsSync(tempPath)) {
                fs.unlinkSync(tempPath);
            }
        };

        timeout = setTimeout(() => {
            cleanup();
            reject(new Error(`Download timeout after ${TIMEOUT_MS / 1000}s`));
        }, TIMEOUT_MS);

        https.get(url, (response) => {
            const statusCode = response.statusCode;

            // Handle redirects
            if (statusCode === 301 || statusCode === 302 || statusCode === 303 || statusCode === 307 || statusCode === 308) {
                const redirectUrl = response.headers.location;
                if (!redirectUrl) {
                    cleanup();
                    reject(new Error(`Redirect without Location header (status ${statusCode})`));
                    return;
                }

                clearTimeout(timeout);
                file.close();
                if (fs.existsSync(tempPath)) {
                    fs.unlinkSync(tempPath);
                }

                console.log(`Following redirect to: ${redirectUrl}`);
                downloadFile(redirectUrl, destPath, redirectCount + 1)
                    .then(resolve)
                    .catch(reject);
                return;
            }

            // Handle non-200 responses
            if (statusCode !== 200) {
                cleanup();
                reject(new Error(`HTTP ${statusCode} from ${url}`));
                return;
            }

            // Download file
            response.pipe(file);

            file.on('finish', () => {
                clearTimeout(timeout);
                file.close(() => {
                    // Atomic rename
                    fs.renameSync(tempPath, destPath);
                    resolve();
                });
            });

            file.on('error', (err) => {
                cleanup();
                reject(err);
            });
        }).on('error', (err) => {
            cleanup();
            reject(err);
        });
    });
}

/**
 * Main setup function
 */
async function setup() {
    console.log('TLA+ Tools Setup');
    console.log('================');
    console.log(`TLA Tools Version: ${TLA_TOOLS_VERSION}`);
    console.log(`Community Modules Version: ${COMMUNITY_MODULES_VERSION}`);
    console.log(`Tools Directory: ${TOOLS_DIR}`);
    console.log('');

    if (!fs.existsSync(TOOLS_DIR)) {
        console.log(`Creating directory: ${TOOLS_DIR}`);
        fs.mkdirSync(TOOLS_DIR, { recursive: true });
    }

    await downloadAndVerify(
        'tla2tools.jar',
        TLA_TOOLS_URL,
        TLA_TOOLS_PATH,
        EXPECTED_CHECKSUMS.tla2tools.algorithm,
        EXPECTED_CHECKSUMS.tla2tools.checksum
    );

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

/**
 * Download file and verify checksum
 * @param {string} name - Display name
 * @param {string} url - Download URL
 * @param {string} destPath - Destination path
 * @param {string} algorithm - Hash algorithm
 * @param {string} expectedChecksum - Expected checksum
 */
async function downloadAndVerify(name, url, destPath, algorithm, expectedChecksum) {
    const fileExists = fs.existsSync(destPath);
    
    if (fileExists) {
        console.log(`Verifying ${name} checksum...`);
        const result = verifyChecksum(destPath, algorithm, expectedChecksum);
        
        if (result.valid) {
            console.log(`✓ ${name} checksum verified (${algorithm}: ${result.expected})`);
            return;
        }
        
        console.error(`✗ ${name} checksum mismatch!`);
        console.error(`  Expected (${algorithm}): ${result.expected}`);
        console.error(`  Actual   (${algorithm}): ${result.actual}`);
        console.error(`  File may be corrupted or from wrong version.`);
        console.error(`  Delete ${destPath} and run setup again.`);
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
    setup,
    EXPECTED_CHECKSUMS,
    DEFAULT_TLA_TOOLS_VERSION,
    DEFAULT_COMMUNITY_MODULES_VERSION
};
