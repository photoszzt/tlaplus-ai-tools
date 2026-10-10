import * as fs from "fs/promises";
import * as path from "path";
import { z } from "zod/v4";
import { McpServer, ResourceTemplate } from "@modelcontextprotocol/sdk/server/mcp.js";
import { completable } from "@modelcontextprotocol/sdk/server/completable.js";
import { parseMarkdownFrontmatter, removeMarkdownFrontmatter } from "../utils/markdown";
import type { ServerConfig } from "../types";

const skillsDir = path.resolve(__dirname, "../../skills");

export async function registerWorkflowPrompts(
  server: McpServer,
  config: ServerConfig,
): Promise<void> {
  const skills = new Map<string, { description: string; text: string }>();
  const files = new Map<string, string>();
  const loadReferences = async (dir: string, prefix: string) => {
    for (const entry of await fs.readdir(dir, { withFileTypes: true })) {
      const relative = `${prefix}/${entry.name}`;
      if (entry.isDirectory()) await loadReferences(path.join(dir, entry.name), relative);
      else if (entry.isFile() && /\.(md|tla|cfg)$/.test(entry.name)) {
        const file = path.join(dir, entry.name);
        if ((await fs.stat(file)).size > 1024 * 1024)
          throw new Error(`Workflow reference too large: ${relative}`);
        files.set(
          relative,
          (await fs.readFile(file, "utf8")).replace(/mcp__plugin_tlaplus_tlaplus__/g, ""),
        );
      }
    }
  };
  for (const entry of await fs.readdir(skillsDir, { withFileTypes: true })) {
    if (!entry.isDirectory()) continue;
    if (entry.name === "shared") {
      await loadReferences(path.join(skillsDir, entry.name), entry.name);
      continue;
    }
    if (!/^tla-[a-z-]+$/.test(entry.name)) continue;
    await loadReferences(path.join(skillsDir, entry.name), entry.name);
    const source = await fs.readFile(path.join(skillsDir, entry.name, "SKILL.md"), "utf8");
    const metadata = parseMarkdownFrontmatter(source);
    skills.set(entry.name, {
      description: metadata.description || `TLA+ workflow: ${entry.name}`,
      text: removeMarkdownFrontmatter(source).replace(/mcp__plugin_tlaplus_tlaplus__/g, ""),
    });
  }
  const completeFiles = async (value: string | undefined, extension: string) => {
    if (!config.workingDir) return [];
    return (await fs.readdir(config.workingDir, { withFileTypes: true }))
      .filter(
        (entry) =>
          entry.isFile() && entry.name.endsWith(extension) && entry.name.startsWith(value ?? ""),
      )
      .map((entry) => entry.name)
      .sort()
      .slice(0, 100);
  };
  const specFileSchema = z.string().max(4096).optional();
  const cfgFileSchema = z.string().max(4096).optional();
  const argsSchema = {
    fileName: completable<typeof specFileSchema>(specFileSchema, (value) =>
      completeFiles(value, ".tla"),
    ),
    cfgFile: completable<typeof cfgFileSchema>(cfgFileSchema, (value) =>
      completeFiles(value, ".cfg"),
    ),
  };
  server.registerResource(
    "tla-workflow",
    new ResourceTemplate("tlaplus://skills/{skill}", {
      list: undefined,
      complete: {
        skill: (prefix) => [...skills.keys()].filter((name) => name.startsWith(prefix)).sort(),
      },
    }),
    { mimeType: "text/markdown", description: "Maintained TLA+ workflow instructions" },
    async (uri, variables) => {
      const skill = typeof variables.skill === "string" ? skills.get(variables.skill) : undefined;
      if (!skill) throw new Error("Unknown TLA+ workflow");
      return { contents: [{ uri: uri.href, mimeType: "text/markdown", text: skill.text }] };
    },
  );
  server.registerResource(
    "tla-workflow-file",
    new ResourceTemplate("tlaplus://skills/{skill}/{file}", {
      list: undefined,
      complete: {
        skill: (prefix) =>
          [...new Set([...files.keys()].map((name) => name.split("/")[0]))]
            .filter((name) => name.startsWith(prefix))
            .sort(),
        file: (prefix, context) => {
          const skill = context?.arguments?.skill;
          if (!skill) return [];
          return [...files.keys()]
            .filter((name) => name.startsWith(`${skill}/`))
            .map((name) => name.slice(skill.length + 1))
            .filter((name) => name.startsWith(prefix))
            .sort();
        },
      },
    }),
    { mimeType: "text/plain", description: "Supporting files for maintained TLA+ workflows" },
    async (uri, variables) => {
      const key = `${variables.skill}/${variables.file}`;
      const text =
        typeof variables.skill === "string" && typeof variables.file === "string"
          ? files.get(key)
          : undefined;
      if (text === undefined) throw new Error("Unknown workflow reference");
      return {
        contents: [
          { uri: uri.href, mimeType: key.endsWith(".md") ? "text/markdown" : "text/plain", text },
        ],
      };
    },
  );
  for (const [name, skill] of skills) {
    server.registerPrompt(
      name,
      {
        description: skill.description,
        argsSchema,
      },
      ({ fileName, cfgFile }) => ({
        description: skill.description,
        messages: [
          {
            role: "user",
            content: {
              type: "resource",
              resource: {
                uri: `tlaplus://skills/${name}`,
                mimeType: "text/markdown",
                text: skill.text,
              },
            },
          },
          {
            role: "user",
            content: {
              type: "text",
              text: [
                `Use this workflow with the registered tlaplus_mcp_* tools. Read supporting files through tlaplus://skills/${name}/{file}, URL-encoding the relative file path. Shared config selection is available at tlaplus://skills/shared/cfg-selection-algorithm.md.`,
                fileName
                  ? `Specification: ${JSON.stringify(fileName)}`
                  : "Ask for a specification when this workflow requires one.",
                cfgFile
                  ? `Configuration: ${JSON.stringify(cfgFile)}`
                  : "Select or request a configuration when required.",
              ].join("\n"),
            },
          },
        ],
      }),
    );
  }
}
