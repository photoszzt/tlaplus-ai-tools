import { registerKnowledgeBaseResources } from '../knowledge';
import { createMockMcpServer, callRegisteredResource } from '../../__tests__/helpers/mock-server';
import { expectResourceRegistered } from '../../__tests__/helpers/assertions';
import { MARKDOWN_WITH_FRONTMATTER, MARKDOWN_WITHOUT_FRONTMATTER } from '../../__tests__/fixtures/markdown-samples';

// Mock dependencies
jest.mock('fs', () => ({
  promises: {
    readdir: jest.fn(),
    readFile: jest.fn()
  }
}));
jest.mock('../../utils/markdown');

import * as fs from 'fs';
import { parseMarkdownFrontmatter, removeMarkdownFrontmatter } from '../../utils/markdown';

describe('Knowledge Base Resources', () => {
  let mockServer: ReturnType<typeof createMockMcpServer>;

  beforeEach(() => {
    jest.clearAllMocks();
    mockServer = createMockMcpServer();
  });

  describe('Resource Registration', () => {
    it('registers markdown files as resources', async () => {
      (fs.promises.readdir as jest.Mock).mockResolvedValue(['article1.md', 'article2.md']);
      (fs.promises.readFile as jest.Mock).mockResolvedValue(MARKDOWN_WITH_FRONTMATTER);
      (parseMarkdownFrontmatter as jest.Mock).mockReturnValue({
        title: 'Test Article',
        description: 'Test description'
      });

      await registerKnowledgeBaseResources(mockServer, '/mock/kb');

      expectResourceRegistered(mockServer, 'tlaplus://knowledge/article1.md');
      expectResourceRegistered(mockServer, 'tlaplus://knowledge/article2.md');
      expect(mockServer.resource).toHaveBeenCalledTimes(2);
    });

    it('ignores non-markdown files', async () => {
      (fs.promises.readdir as jest.Mock).mockResolvedValue([
        'article.md',
        'readme.txt',
        'image.png',
        'data.json'
      ]);
      (fs.promises.readFile as jest.Mock).mockResolvedValue(MARKDOWN_WITH_FRONTMATTER);
      (parseMarkdownFrontmatter as jest.Mock).mockReturnValue({ title: 'Article' });

      await registerKnowledgeBaseResources(mockServer, '/mock/kb');

      expect(mockServer.resource).toHaveBeenCalledTimes(1);
      expectResourceRegistered(mockServer, 'tlaplus://knowledge/article.md');
    });

    it('uses frontmatter title when available', async () => {
      (fs.promises.readdir as jest.Mock).mockResolvedValue(['article.md']);
      (fs.promises.readFile as jest.Mock).mockResolvedValue(MARKDOWN_WITH_FRONTMATTER);
      (parseMarkdownFrontmatter as jest.Mock).mockReturnValue({
        title: 'Custom Title',
        description: 'Custom description'
      });

      await registerKnowledgeBaseResources(mockServer, '/mock/kb');

      const resource = mockServer.getRegisteredResources().get('tlaplus://knowledge/article.md');
      expect(resource?.metadata.title).toBe('Custom Title');
      expect(resource?.metadata.description).toBe('Custom description');
    });

    it('falls back to filename when no frontmatter', async () => {
      (fs.promises.readdir as jest.Mock).mockResolvedValue(['article.md']);
      (fs.promises.readFile as jest.Mock).mockResolvedValue(MARKDOWN_WITHOUT_FRONTMATTER);
      (parseMarkdownFrontmatter as jest.Mock).mockReturnValue({});

      await registerKnowledgeBaseResources(mockServer, '/mock/kb');

      const resource = mockServer.getRegisteredResources().get('tlaplus://knowledge/article.md');
      expect(resource?.metadata.title).toBe('article.md');
      expect(resource?.metadata.description).toContain('TLA+ knowledge base article');
    });

    it('sets correct mimeType for all resources', async () => {
      (fs.promises.readdir as jest.Mock).mockResolvedValue(['article.md']);
      (fs.promises.readFile as jest.Mock).mockResolvedValue(MARKDOWN_WITH_FRONTMATTER);
      (parseMarkdownFrontmatter as jest.Mock).mockReturnValue({});

      await registerKnowledgeBaseResources(mockServer, '/mock/kb');

      const resource = mockServer.getRegisteredResources().get('tlaplus://knowledge/article.md');
      expect(resource?.metadata.mimeType).toBe('text/markdown');
    });
  });

  describe('Resource Handlers', () => {
    it('returns content without frontmatter', async () => {
      (fs.promises.readdir as jest.Mock).mockResolvedValue(['article.md']);
      (fs.promises.readFile as jest.Mock).mockResolvedValue(MARKDOWN_WITH_FRONTMATTER);
      (parseMarkdownFrontmatter as jest.Mock).mockReturnValue({ title: 'Test' });
      (removeMarkdownFrontmatter as jest.Mock).mockReturnValue('# Content without frontmatter');

      await registerKnowledgeBaseResources(mockServer, '/mock/kb');
      const result = await callRegisteredResource(mockServer, 'tlaplus://knowledge/article.md');

      expect(result.contents).toHaveLength(1);
      expect(result.contents[0].uri).toBe('tlaplus://knowledge/article.md');
      expect(result.contents[0].mimeType).toBe('text/markdown');
      expect(result.contents[0].text).toBe('# Content without frontmatter');
      expect(removeMarkdownFrontmatter).toHaveBeenCalled();
    });

    it('reads file on each resource fetch', async () => {
      (fs.promises.readdir as jest.Mock).mockResolvedValue(['article.md']);
      (fs.promises.readFile as jest.Mock)
        .mockResolvedValueOnce(MARKDOWN_WITH_FRONTMATTER) // Registration read
        .mockResolvedValueOnce('Updated content'); // Handler read
      (parseMarkdownFrontmatter as jest.Mock).mockReturnValue({ title: 'Test' });
      (removeMarkdownFrontmatter as jest.Mock).mockReturnValue('Updated content');

      await registerKnowledgeBaseResources(mockServer, '/mock/kb');
      await callRegisteredResource(mockServer, 'tlaplus://knowledge/article.md');

      expect(fs.promises.readFile).toHaveBeenCalledTimes(2);
    });
  });

  describe('Error Handling', () => {
    it('handles readdir errors gracefully', async () => {
      (fs.promises.readdir as jest.Mock).mockRejectedValue(new Error('Permission denied'));

      // Should not throw
      await expect(
        registerKnowledgeBaseResources(mockServer, '/mock/kb')
      ).resolves.not.toThrow();

      expect(mockServer.resource).not.toHaveBeenCalled();
    });

    it('handles readFile errors during registration', async () => {
      (fs.promises.readdir as jest.Mock).mockResolvedValue(['article.md']);
      (fs.promises.readFile as jest.Mock).mockRejectedValue(new Error('File read error'));

      // Should not throw, may skip the file
      await expect(
        registerKnowledgeBaseResources(mockServer, '/mock/kb')
      ).resolves.not.toThrow();
    });

    it('handles empty directory gracefully', async () => {
      (fs.promises.readdir as jest.Mock).mockResolvedValue([]);

      await registerKnowledgeBaseResources(mockServer, '/mock/kb');

      expect(mockServer.resource).not.toHaveBeenCalled();
    });
  });
});
