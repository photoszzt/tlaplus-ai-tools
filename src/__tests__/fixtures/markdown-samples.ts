/**
 * Sample markdown content for knowledge base testing
 */

export const MARKDOWN_WITH_FRONTMATTER = `---
title: TLC Configuration Files
description: Guide to creating TLC configuration files
---
# TLC Configuration Files

This guide explains how to create configuration files for TLC.

## Basic Structure

A TLC config file specifies:
- CONSTANTS
- INIT predicate
- NEXT predicate
- INVARIANTS
`;

export const MARKDOWN_WITHOUT_FRONTMATTER = `# Simple Article

This is a simple markdown article without frontmatter.

## Section 1

Content here.
`;

export const MARKDOWN_EMPTY_FRONTMATTER = `---
---
# Empty Frontmatter

Content without metadata.
`;

export const MULTIPLE_MARKDOWN_FILES = [
  {
    name: 'article1.md',
    content: MARKDOWN_WITH_FRONTMATTER
  },
  {
    name: 'article2.md',
    content: MARKDOWN_WITHOUT_FRONTMATTER
  },
  {
    name: 'article3.md',
    content: MARKDOWN_EMPTY_FRONTMATTER
  }
];
