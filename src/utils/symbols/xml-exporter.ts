import * as path from 'path';
import { runJavaCommand, ProcessInfo } from '../java';
import { getClassPath } from '../tla-tools';

const XML_EXPORTER_MAIN_CLASS = 'tla2sany.xml.XMLExporter';

export interface XmlExporterResult {
  xml: string;
  stderr: string;
}

export async function runXmlExporter(
  tlaFilePath: string,
  toolsDir: string,
  includeExtendedModules: boolean,
  javaHome?: string
): Promise<XmlExporterResult> {
  const classPath = getClassPath(toolsDir);

  const args = ['-o', '-u'];
  if (!includeExtendedModules) {
    args.push('-r');
  }
  args.push(path.basename(tlaFilePath));

  const workingDir = path.dirname(tlaFilePath);

  const procInfo: ProcessInfo = await runJavaCommand(
    classPath,
    XML_EXPORTER_MAIN_CLASS,
    args,
    [],
    javaHome,
    workingDir
  );

  let xml = '';
  let stderr = '';

  if (procInfo.stdout) {
    for await (const chunk of procInfo.stdout) {
      xml += chunk.toString();
    }
  }

  if (procInfo.stderr) {
    for await (const chunk of procInfo.stderr) {
      stderr += chunk.toString();
    }
  }

  if (procInfo.process.exitCode === null) {
    await new Promise<void>((resolve) => {
      procInfo.process.once('close', () => resolve());
    });
  }

  return { xml, stderr };
}
