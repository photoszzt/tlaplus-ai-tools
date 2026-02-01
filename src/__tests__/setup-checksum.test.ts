// Test checksum verification from scripts/setup.js
import * as fs from 'fs';
import * as path from 'path';
import * as crypto from 'crypto';

// Import setup helpers
const setupModule = require('../../scripts/setup.js');
const { calculateChecksum, verifyChecksum, EXPECTED_CHECKSUMS } = setupModule;

describe('Setup Checksum Verification', () => {
  let tempDir: string;

  beforeEach(() => {
    // Create temp directory for test files
    tempDir = path.join(__dirname, 'temp-checksum-test');
    if (!fs.existsSync(tempDir)) {
      fs.mkdirSync(tempDir, { recursive: true });
    }
  });

  afterEach(() => {
    // Clean up temp directory
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true, force: true });
    }
  });

  describe('calculateChecksum', () => {
    it('calculates SHA1 checksum correctly', () => {
      const testFile = path.join(tempDir, 'test-sha1.txt');
      const content = 'Hello, TLA+!';
      fs.writeFileSync(testFile, content);

      const expectedSha1 = crypto.createHash('sha1').update(content).digest('hex');
      const actualSha1 = calculateChecksum(testFile, 'sha1');

      expect(actualSha1).toBe(expectedSha1);
    });

    it('calculates SHA256 checksum correctly', () => {
      const testFile = path.join(tempDir, 'test-sha256.txt');
      const content = 'TLA+ Model Checking';
      fs.writeFileSync(testFile, content);

      const expectedSha256 = crypto.createHash('sha256').update(content).digest('hex');
      const actualSha256 = calculateChecksum(testFile, 'sha256');

      expect(actualSha256).toBe(expectedSha256);
    });

    it('produces different checksums for different content', () => {
      const file1 = path.join(tempDir, 'file1.txt');
      const file2 = path.join(tempDir, 'file2.txt');
      
      fs.writeFileSync(file1, 'content1');
      fs.writeFileSync(file2, 'content2');

      const checksum1 = calculateChecksum(file1, 'sha256');
      const checksum2 = calculateChecksum(file2, 'sha256');

      expect(checksum1).not.toBe(checksum2);
    });

    it('produces same checksum for identical content', () => {
      const file1 = path.join(tempDir, 'identical1.txt');
      const file2 = path.join(tempDir, 'identical2.txt');
      
      const content = 'identical content';
      fs.writeFileSync(file1, content);
      fs.writeFileSync(file2, content);

      const checksum1 = calculateChecksum(file1, 'sha256');
      const checksum2 = calculateChecksum(file2, 'sha256');

      expect(checksum1).toBe(checksum2);
    });
  });

  describe('verifyChecksum', () => {
    it('returns valid=true when checksum matches', () => {
      const testFile = path.join(tempDir, 'valid.txt');
      const content = 'valid content';
      fs.writeFileSync(testFile, content);

      const expectedChecksum = crypto.createHash('sha256').update(content).digest('hex');
      const result = verifyChecksum(testFile, 'sha256', expectedChecksum);

      expect(result.valid).toBe(true);
      expect(result.actual).toBe(expectedChecksum);
      expect(result.expected).toBe(expectedChecksum);
    });

    it('returns valid=false when checksum mismatches', () => {
      const testFile = path.join(tempDir, 'invalid.txt');
      fs.writeFileSync(testFile, 'actual content');

      const wrongChecksum = crypto.createHash('sha256').update('wrong content').digest('hex');
      const result = verifyChecksum(testFile, 'sha256', wrongChecksum);

      expect(result.valid).toBe(false);
      expect(result.actual).not.toBe(wrongChecksum);
      expect(result.expected).toBe(wrongChecksum);
    });

    it('detects corrupted file (checksum mismatch)', () => {
      const testFile = path.join(tempDir, 'corrupted.jar');
      
      // Write original content
      const originalContent = Buffer.from('original JAR content');
      fs.writeFileSync(testFile, originalContent);
      const originalChecksum = crypto.createHash('sha1').update(originalContent).digest('hex');

      // Corrupt the file
      const corruptedContent = Buffer.from('corrupted JAR content');
      fs.writeFileSync(testFile, corruptedContent);

      // Verify with original checksum (should fail)
      const result = verifyChecksum(testFile, 'sha1', originalChecksum);

      expect(result.valid).toBe(false);
      expect(result.actual).not.toBe(originalChecksum);
    });

    it('works with different hash algorithms', () => {
      const testFile = path.join(tempDir, 'multi-algo.txt');
      const content = 'test content';
      fs.writeFileSync(testFile, content);

      const sha1Expected = crypto.createHash('sha1').update(content).digest('hex');
      const sha256Expected = crypto.createHash('sha256').update(content).digest('hex');

      const sha1Result = verifyChecksum(testFile, 'sha1', sha1Expected);
      const sha256Result = verifyChecksum(testFile, 'sha256', sha256Expected);

      expect(sha1Result.valid).toBe(true);
      expect(sha256Result.valid).toBe(true);
    });
  });

  describe('EXPECTED_CHECKSUMS', () => {
    it('has correct structure for tla2tools', () => {
      expect(EXPECTED_CHECKSUMS.tla2tools).toBeDefined();
      expect(EXPECTED_CHECKSUMS.tla2tools.version).toBe('1.8.0');
      expect(EXPECTED_CHECKSUMS.tla2tools.algorithm).toBe('sha1');
      expect(EXPECTED_CHECKSUMS.tla2tools.checksum).toMatch(/^[a-f0-9]{40}$/); // SHA1 is 40 hex chars
    });

    it('has correct structure for communityModules', () => {
      expect(EXPECTED_CHECKSUMS.communityModules).toBeDefined();
      expect(EXPECTED_CHECKSUMS.communityModules.version).toBe('202601200755');
      expect(EXPECTED_CHECKSUMS.communityModules.algorithm).toBe('sha256');
      expect(EXPECTED_CHECKSUMS.communityModules.checksum).toMatch(/^[a-f0-9]{64}$/); // SHA256 is 64 hex chars
    });

    it('uses pinned version 1.8.0 for tla2tools', () => {
      expect(EXPECTED_CHECKSUMS.tla2tools.version).toBe('1.8.0');
    });
  });

  describe('Checksum verification workflow', () => {
    it('simulates successful verification on fresh download', () => {
      const testFile = path.join(tempDir, 'tla2tools.jar');
      
      // Simulate download with correct content
      const correctContent = Buffer.from('correct tla2tools v1.8.0 content');
      fs.writeFileSync(testFile, correctContent);
      const correctChecksum = crypto.createHash('sha1').update(correctContent).digest('hex');

      // Verify
      const result = verifyChecksum(testFile, 'sha1', correctChecksum);

      expect(result.valid).toBe(true);
    });

    it('simulates detection of corrupted download', () => {
      const testFile = path.join(tempDir, 'tla2tools.jar');
      
      // Expected checksum for correct file
      const correctContent = Buffer.from('correct tla2tools v1.8.0 content');
      const correctChecksum = crypto.createHash('sha1').update(correctContent).digest('hex');

      // But file is corrupted
      const corruptedContent = Buffer.from('corrupted incomplete download');
      fs.writeFileSync(testFile, corruptedContent);

      // Verify (should fail)
      const result = verifyChecksum(testFile, 'sha1', correctChecksum);

      expect(result.valid).toBe(false);
      expect(result.actual).not.toBe(correctChecksum);
    });

    it('simulates detection of wrong version', () => {
      const testFile = path.join(tempDir, 'tla2tools.jar');
      
      // Expected checksum for v1.8.0
      const v180Content = Buffer.from('tla2tools v1.8.0');
      const v180Checksum = crypto.createHash('sha1').update(v180Content).digest('hex');

      // But user has v1.7.0
      const v170Content = Buffer.from('tla2tools v1.7.0');
      fs.writeFileSync(testFile, v170Content);

      // Verify (should fail)
      const result = verifyChecksum(testFile, 'sha1', v180Checksum);

      expect(result.valid).toBe(false);
      expect(result.actual).not.toBe(v180Checksum);
    });
  });
});
