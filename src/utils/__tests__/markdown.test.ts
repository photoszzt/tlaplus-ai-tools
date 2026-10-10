import { parseMarkdownFrontmatter, removeMarkdownFrontmatter } from "../markdown";

describe("Maintained skill descriptions", () => {
  it("folds multiline descriptions and stops before the next frontmatter key", () => {
    const source =
      '---\nname: tla-check\ndescription: >-\n  Run exhaustive model checking.\n  Use when asked to "check a spec".\nversion: 1.0\n---\n# Workflow\n';
    expect(parseMarkdownFrontmatter(source).description).toBe(
      'Run exhaustive model checking. Use when asked to "check a spec".',
    );
    expect(removeMarkdownFrontmatter(source)).toBe("# Workflow\n");
  });
});
