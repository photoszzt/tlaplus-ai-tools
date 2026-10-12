import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { z } from "zod/v4";

export function registerTraceAudioTool(server: McpServer): void {
  server.registerTool(
    "tlaplus_mcp_trace_audio",
    {
      description:
        "Sonify 1–32 caller-supplied scalar state values as pitches from 220 to 880 Hz. Does not parse traces or check correctness.",
      inputSchema: { values: z.array(z.number().finite()).min(1).max(32) },
    },
    ({ values }, extra) => {
      extra.signal.throwIfAborted();
      const scale = Math.max(...values.map(Math.abs)) || 1;
      const scaled = values.map((value) => value / scale);
      const low = Math.min(...scaled);
      const span = Math.max(...scaled) - low;
      const samplesPerValue = 1200;
      const pcmBytes = values.length * samplesPerValue * 2;
      const wav = Buffer.alloc(44 + pcmBytes);
      wav.write("RIFF", 0);
      wav.writeUInt32LE(36 + pcmBytes, 4);
      wav.write("WAVEfmt ", 8);
      wav.writeUInt32LE(16, 16);
      wav.writeUInt16LE(1, 20);
      wav.writeUInt16LE(1, 22);
      wav.writeUInt32LE(8000, 24);
      wav.writeUInt32LE(16000, 28);
      wav.writeUInt16LE(2, 32);
      wav.writeUInt16LE(16, 34);
      wav.write("data", 36);
      wav.writeUInt32LE(pcmBytes, 40);
      scaled.forEach((value, index) => {
        const frequency = span === 0 ? 550 : 220 + (660 * (value - low)) / span;
        for (let sample = 0; sample < samplesPerValue; sample++) {
          const fade = Math.min(1, sample / 80, (samplesPerValue - 1 - sample) / 80);
          const amplitude = Math.round(
            4096 * fade * Math.sin((2 * Math.PI * frequency * sample) / 8000),
          );
          wav.writeInt16LE(amplitude, 44 + (index * samplesPerValue + sample) * 2);
        }
      });
      extra.signal.throwIfAborted();
      return {
        content: [
          {
            type: "text",
            text: `Supplied scalar state values: ${JSON.stringify(values)}. Pitches span 220–880 Hz relative to this sequence; constant sequences use 550 Hz. Each value lasts 150 ms. This audio does not establish correctness.`,
          },
          { type: "audio", mimeType: "audio/wav", data: wav.toString("base64") },
        ],
      };
    },
  );
}
