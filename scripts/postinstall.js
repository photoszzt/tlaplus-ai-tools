#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

/**
 * Post-install script that runs after `npm install`
 * Automatically downloads TLA+ tools when plugin is installed
 */
async function postinstall() {
  console.log('[postinstall] Starting TLA+ tools setup...');
  console.log('[postinstall] Working directory:', process.cwd());
  console.log('[postinstall] Script directory:', __dirname);

  // Check if we're in development (local git repo with .git folder)
  const isDevelopment = fs.existsSync(path.join(__dirname, '..', '.git'));
  const isPluginInstall = __dirname.includes('.claude/plugins/cache');

  console.log('[postinstall] Development mode:', isDevelopment);
  console.log('[postinstall] Plugin install:', isPluginInstall);

  // Skip in development unless explicitly requested
  if (isDevelopment && !process.env.FORCE_POSTINSTALL) {
    console.log('[postinstall] Skipping TLA+ tools download in development mode');
    console.log('[postinstall] Run `npm run setup` manually to download tools');
    return;
  }

  // Import and run setup
  try {
    const { setup } = require('./setup.js');
    console.log('[postinstall] Running setup to download TLA+ tools...');
    await setup();
    console.log('[postinstall] Setup completed successfully!');
  } catch (err) {
    // Don't fail installation if setup fails - user can run /tla-setup later
    console.warn('[postinstall] Warning: Failed to download TLA+ tools automatically');
    console.warn('[postinstall] Reason:', err.message);
    console.warn('[postinstall] Stack:', err.stack);
    console.warn('[postinstall] You can download them later by running: /tla-setup');
  }
}

// Run postinstall
postinstall().catch((err) => {
  // Don't fail the installation, just warn
  console.warn('[postinstall] Postinstall error:', err.message);
  console.warn('[postinstall] Stack:', err.stack);
  process.exit(0); // Exit successfully even if setup fails
});
