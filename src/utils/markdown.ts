/**
 * Metadata extracted from markdown frontmatter
 */
export interface MarkdownMetadata {
  title?: string;
  description?: string;
}

/**
 * Parse YAML frontmatter from markdown content
 * Frontmatter is delimited by '---' at the start and end
 *
 * @param content Full markdown content
 * @returns Parsed metadata object
 */
export function parseMarkdownFrontmatter(content: string): MarkdownMetadata {
  const normalizedContent = content.replace(/^\ufeff/, '');
  const metadata: MarkdownMetadata = {};

  // Check if content starts with frontmatter delimiter
  if (!normalizedContent.startsWith('---')) {
    return metadata;
  }

  // Find the end of the frontmatter section
  const endIndex = normalizedContent.indexOf('---', 3);
  if (endIndex === -1) {
    return metadata;
  }

  // Extract the frontmatter section (between the two '---' delimiters)
  const frontmatterSection = normalizedContent.substring(3, endIndex).trim();

  // Parse simple YAML key-value pairs
  // We only need to support 'title:' and 'description:' for now
  const lines = frontmatterSection.split(/\r?\n/);

  for (const line of lines) {
    const trimmedLine = line.trim();

    // Parse 'title: value'
    if (trimmedLine.startsWith('title:')) {
      const value = trimmedLine.substring(6).trim();
      // Remove quotes if present
      metadata.title = value.replace(/^["']|["']$/g, '');
    }

    // Parse 'description: value'
    if (trimmedLine.startsWith('description:')) {
      const value = trimmedLine.substring(12).trim();
      // Remove quotes if present
      metadata.description = value.replace(/^["']|["']$/g, '');
    }
  }

  return metadata;
}

/**
 * Remove YAML frontmatter from markdown content
 * Returns the content without the frontmatter section
 *
 * @param content Full markdown content
 * @returns Content without frontmatter
 */
export function removeMarkdownFrontmatter(content: string): string {
  const normalizedContent = content.replace(/^\ufeff/, '');
  // Check if content starts with frontmatter delimiter
  if (!normalizedContent.startsWith('---')) {
    return normalizedContent;
  }

  // Find the end of the frontmatter section
  const endIndex = normalizedContent.indexOf('---', 3);
  if (endIndex === -1) {
    return normalizedContent;
  }

  // Return content after the second '---' delimiter
  // Skip the delimiter and any following newlines
  let startIndex = endIndex + 3;
  while (startIndex < normalizedContent.length && (normalizedContent[startIndex] === '\n' || normalizedContent[startIndex] === '\r')) {
    startIndex++;
  }

  return normalizedContent.substring(startIndex);
}
