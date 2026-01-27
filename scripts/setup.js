#!/usr/bin/env node

const https = require('https');
const fs = require('fs');
const path = require('path');

// Default versions
const DEFAULT_TLA_TOOLS_VERSION = '1.7.4';
const DEFAULT_COMMUNITY_MODULES_VERSION = '202601200755';

// Get versions from environment or use defaults
const TLA_TOOLS_VERSION = process.env.TLA_TOOLS_VERSION || DEFAULT_TLA_TOOLS_VERSION;
const COMMUNITY_MODULES_VERSION = process.env.COMMUNITY_MODULES_VERSION || DEFAULT_COMMUNITY_MODULES_VERSION;

// URLs
const TLA_TOOLS_URL = `https://github.com/tlaplus/tlaplus/releases/download/v${TLA_TOOLS_VERSION}/tla2tools.jar`;
const COMMUNITY_MODULES_URL = `https://github.com/tlaplus/CommunityModules/releases/download/${COMMUNITY_MODULES_VERSION}/CommunityModules-deps.jar`;

// Paths
const TOOLS_DIR = path.join(__dirname, '..', 'tools');
const TLA_TOOLS_PATH = path.join(TOOLS_DIR, 'tla2tools.jar');
const COMMUNITY_MODULES_PATH = path.join(TOOLS_DIR, 'CommunityModules-deps.jar');

const MAX_REDIRECTS = 5;
const TIMEOUT_MS = 120000;

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
    console.log('');

    // Create tools directory if it doesn't exist
    if (!fs.existsSync(TOOLS_DIR)) {
        console.log(`Creating directory: ${TOOLS_DIR}`);
        fs.mkdirSync(TOOLS_DIR, { recursive: true });
    }

    // Download tla2tools.jar
    if (fs.existsSync(TLA_TOOLS_PATH)) {
        console.log(`✓ tla2tools.jar already exists, skipping download`);
    } else {
        console.log(`Downloading tla2tools.jar from ${TLA_TOOLS_URL}...`);
        try {
            await downloadFile(TLA_TOOLS_URL, TLA_TOOLS_PATH);
            console.log(`✓ Downloaded tla2tools.jar`);
        } catch (err) {
            console.error(`✗ Failed to download tla2tools.jar: ${err.message}`);
            process.exit(1);
        }
    }

    // Download CommunityModules-deps.jar
    if (fs.existsSync(COMMUNITY_MODULES_PATH)) {
        console.log(`✓ CommunityModules-deps.jar already exists, skipping download`);
    } else {
        console.log(`Downloading CommunityModules-deps.jar from ${COMMUNITY_MODULES_URL}...`);
        try {
            await downloadFile(COMMUNITY_MODULES_URL, COMMUNITY_MODULES_PATH);
            console.log(`✓ Downloaded CommunityModules-deps.jar`);
        } catch (err) {
            console.error(`✗ Failed to download CommunityModules-deps.jar: ${err.message}`);
            process.exit(1);
        }
    }

    console.log('');
    console.log('Setup complete!');
    console.log('');
    console.log('Next steps:');
    console.log('1. Ensure Java is installed: java -version');
    console.log('2. Test TLC: java -jar tools/tla2tools.jar');
}

// Run setup
setup().catch((err) => {
    console.error(`Setup failed: ${err.message}`);
    process.exit(1);
});
