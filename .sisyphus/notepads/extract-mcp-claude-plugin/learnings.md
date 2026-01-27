## Task 8: GitHub Actions CI/CD Workflows

### Created Files
- `.github/workflows/ci.yml`: CI pipeline for push/PR
- `.github/workflows/publish.yml`: NPM publish on release

### CI Configuration
- **Triggers**: Push to main, PRs to main
- **Matrix**: Node 18/20/22 × Ubuntu/macOS/Windows (9 combinations)
- **Java Setup**: Temurin JDK 11 via actions/setup-java@v4
- **Steps**: checkout → setup-java → setup-node → npm ci → build → test
- **Coverage**: Uploads to Codecov on Ubuntu + Node 22

### Publish Configuration
- **Trigger**: Release published event only
- **Node**: 22 (latest stable)
- **Registry**: npm (registry.npmjs.org)
- **Auth**: NODE_AUTH_TOKEN secret (requires NPM_TOKEN in repo secrets)
- **Steps**: checkout → setup-node → npm ci → build → test → publish

### Key Decisions
1. **No jar downloads in CI**: Tests skip gracefully when jars missing (Jest describe.skip)
2. **Java installed but not used for jar download**: Enables integration tests that need Java runtime
3. **fail-fast: false**: All matrix combinations run even if one fails
4. **Coverage only on Ubuntu+Node22**: Reduces redundant uploads

### Verification
Both files created successfully and are valid YAML.
