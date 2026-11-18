// persistent bridge to the authoritative haskell checker; responses carry request versions.
import * as childProcess from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
interface PendingRequest {
  resolve: (value: CompilerResult) => void;
  command: CompilerCommand;
  version: number;
}
type CompilerCommand =
  "check" | "type" | "proof" | "format" | "highlight" | "names" | "cancel";
interface CompilerDiagnostic {
  kind: "parse" | "type" | "goal";
  path?: string;
  start: number;
  end: number;
  message: string;
}
interface ProofDependency {
  symbol: { module: string; name: string };
  name: string;
  type: string;
  kind: "sorry" | "axiom" | "host";
  host?: string;
}
interface ProofResult {
  kind: "proof";
  audit: { name: string; type: string; dependencies: ProofDependency[] };
  verified: boolean;
  message: string;
  report: string;
}
type ErrorResult = { kind: "error"; message: string };
type CompilerResult =
  | { kind: "check"; diagnostics: CompilerDiagnostic[] }
  | { kind: "type"; type: string }
  | ProofResult
  | { kind: "format"; source: string }
  | ({ kind: "highlight" } & SourceSyntax)
  | ({ kind: "names" } & SourceNames)
  | ErrorResult;
// a command's reply is a result of its own kind or an error.
type ResultOf<Command extends CompilerCommand> = Extract<
  CompilerResult,
  { kind: Command | "error" }
>;
interface CompilerResponse {
  protocol: 1;
  id: number;
  version: number;
  result: CompilerResult;
}
type SourceRole = [
  start: number,
  end: number,
  role: string,
  modifiers: string[],
];
// the compiler's one parse of a source: roles, tokens, and the concrete
// tree's declarations and imports, and each local binder with the span where
// it is seen, by UTF-16 offset.
interface SourceSyntax {
  roles: SourceRole[];
  tokens: [start: number, end: number, kind: string][];
  declarations: {
    kind: string;
    start: number;
    end: number;
    headerEnd: number;
    shown: boolean;
    doc: string | null;
  }[];
  imports: { path: string; alias: string | null; start: number; end: number }[];
  scopes: [start: number, end: number, scopeStart: number, scopeEnd: number][];
}
// the compiler's names for a document: each written name checking resolved
// to a global and whether that global nameth a type, the names it may write
// at top level, and the file each bring path it reacheth resolved to. a module
// is `<root>` for the document itself, `<primitive>`, or a bring path.
interface SourceNames {
  files: Record<string, string>;
  resolved: [
    start: number,
    end: number,
    module: string,
    name: string,
    type: boolean,
  ][];
  visible: [
    written: string,
    module: string,
    name: string,
    constructor: boolean,
  ][];
}
// a source the session checketh; a file document's uri nameth its path.
type SourceDocument = { uri?: string; text: string };
// a request in flight. `cancel` settleth it as an error and asketh the
// session to stop its work.
type Running<Result> = {
  process: childProcess.ChildProcessWithoutNullStreams | undefined;
  requestId: number;
  version: number;
  result: Promise<Result>;
  cancel(): void;
};
const mapResult = <From, To>(
  running: Running<From>,
  map: (result: From) => To,
): Running<To> => ({ ...running, result: running.result.then(map) });
const emptyNames: SourceNames = { files: {}, resolved: [], visible: [] };
const emptySyntax: SourceSyntax = {
  roles: [],
  tokens: [],
  declarations: [],
  imports: [],
  scopes: [],
};
class CompilerBridge {
  tongue: string | undefined;
  executablePath: string | undefined;
  libraryRoots: string[] = [];
  executable: string | undefined;
  session: childProcess.ChildProcessWithoutNullStreams | undefined;
  pending = new Map<number, PendingRequest>();
  nextRequestId = 1;
  output = "";
  // a changed configuration endeth the session; the result telleth whether
  // anything changed.
  configure(
    tongue: string | undefined,
    libraryRoots: string[] = [],
    executablePath?: string,
  ) {
    const tongueChanged = tongue !== this.tongue;
    const executableChanged = executablePath !== this.executablePath;
    const rootsChanged =
      libraryRoots.length !== this.libraryRoots.length ||
      libraryRoots.some((root, index) => root !== this.libraryRoots[index]);
    const changed = tongueChanged || rootsChanged || executableChanged;
    if (changed) {
      this.dispose();
      if (tongueChanged || executableChanged) this.executable = undefined;
    }
    this.tongue = tongue;
    this.executablePath = executablePath;
    this.libraryRoots = [...libraryRoots];
    return changed;
  }
  available() {
    return Boolean(this.findExecutable());
  }
  check(document: SourceDocument, texts: [string, string][], version = 0) {
    return this.request(
      "check",
      document.text,
      texts,
      "",
      version,
      documentPath(document.uri),
    );
  }
  names(document: SourceDocument, texts: [string, string][], version = 0) {
    return mapResult(
      this.request(
        "names",
        document.text,
        texts,
        "",
        version,
        documentPath(document.uri),
      ),
      (result): SourceNames | undefined =>
        result.kind === "names" ? result : undefined,
    );
  }
  typeOf(
    document: SourceDocument,
    texts: [string, string][],
    name: string,
    version = 0,
  ) {
    return this.request(
      "type",
      document.text,
      texts,
      name,
      version,
      documentPath(document.uri),
    );
  }
  proof(
    document: SourceDocument,
    texts: [string, string][],
    name: string,
    version = 0,
    allowedAxioms?: string[],
  ) {
    return this.request(
      "proof",
      document.text,
      texts,
      name,
      version,
      documentPath(document.uri),
      allowedAxioms,
    );
  }
  format(source: string, version = 0) {
    return mapResult(
      this.request("format", source, [], "", version),
      (result) => (result.kind === "format" ? result.source : undefined),
    );
  }
  highlight(source: string, version = 0) {
    return mapResult(
      this.request("highlight", source, [], "", version),
      (result): SourceSyntax | undefined =>
        result.kind === "highlight" ? result : undefined,
    );
  }
  request<Command extends CompilerCommand>(
    command: Command,
    source: string,
    texts: [string, string][],
    name: string,
    version: number,
    path?: string,
    allowedAxioms?: string[],
  ): Running<ResultOf<Command>> {
    const executable = this.findExecutable();
    if (!executable) {
      return {
        process: undefined,
        requestId: 0,
        version,
        result: Promise.resolve<ErrorResult>({
          kind: "error",
          message: "could not find the tung executable",
        }),
        cancel() {},
      };
    }
    const process = this.ensureSession(executable);
    const requestId = this.nextRequestId++;
    // `consume` settleth a request only with its own kind or an error.
    const result = new Promise<CompilerResult>((resolve) =>
      this.pending.set(requestId, { resolve, command, version }),
    ) as Promise<ResultOf<Command>>;
    process.stdin.write(
      sessionRequest(
        requestId,
        version,
        command,
        name,
        source,
        texts,
        path,
        allowedAxioms,
      ),
    );
    return {
      process,
      requestId,
      version,
      result,
      cancel: () => this.cancel(requestId, version),
    };
  }
  ensureSession(executable: string) {
    if (
      this.session &&
      this.session.exitCode === null &&
      !this.session.killed
    ) {
      return this.session;
    }
    const process = childProcess.spawn(executable, ["--editor-session"], {
      cwd: this.tongue,
      env: this.libraryRoots.length
        ? {
            ...globalThis.process.env,
            TUNG_PATH: this.libraryRoots.join(path.delimiter),
          }
        : globalThis.process.env,
      stdio: ["pipe", "pipe", "pipe"],
    });
    this.session = process;
    this.output = "";
    let stderr = "";
    process.stdout.setEncoding("utf8");
    process.stderr.setEncoding("utf8");
    process.stdout.on("data", (chunk) => this.consume(chunk, process));
    process.stderr.on("data", (chunk) => (stderr += chunk));
    process.on("error", (error) => {
      this.failSession(
        process,
        `could not run the haskell checker: ${error.message}`,
      );
    });
    process.on("close", () => {
      const detail = stderr.trim();
      this.failSession(
        process,
        detail
          ? `haskell checker session stopped: ${detail}`
          : "haskell checker session stopped",
      );
    });
    process.stdin.on("error", (error) => {
      this.failSession(
        process,
        `could not write to the checker: ${error.message}`,
      );
    });
    return process;
  }
  consume(chunk: string, process = this.session) {
    if (!process || process !== this.session) return;
    this.output += chunk;
    while (true) {
      const newline = this.output.indexOf("\n");
      if (newline < 0) return;
      const line = this.output.slice(0, newline);
      this.output = this.output.slice(newline + 1);
      let response: unknown;
      try {
        response = JSON.parse(line);
      } catch {
        this.failSession(process, "invalid JSON from the checker");
        return;
      }
      if (!isCompilerResponse(response)) {
        this.failSession(process, "invalid checker response schema");
        return;
      }
      const pending = this.pending.get(response.id);
      if (!pending) continue;
      if (
        pending.version !== response.version ||
        (response.result.kind !== pending.command &&
          response.result.kind !== "error")
      ) {
        this.failSession(process, "checker response did not match its request");
        return;
      }
      this.pending.delete(response.id);
      pending.resolve(response.result);
    }
  }
  cancel(requestId: number, version: number) {
    const pending = this.pending.get(requestId);
    if (!pending) return;
    this.pending.delete(requestId);
    pending.resolve({ kind: "error", message: "checker request cancelled" });
    if (this.session?.exitCode === null && !this.session.killed) {
      this.session.stdin.write(
        sessionRequest(requestId, version, "cancel", "", "", []),
      );
    }
  }
  failSession(
    process: childProcess.ChildProcessWithoutNullStreams,
    message: string,
  ) {
    if (this.session !== process) return;
    this.reset(message);
    if (process.exitCode === null && !process.killed) process.kill();
  }
  dispose() {
    const process = this.reset("checker request cancelled");
    if (process && process.exitCode === null && !process.killed) process.kill();
  }
  reset(message: string) {
    const process = this.session;
    this.session = undefined;
    for (const { resolve } of this.pending.values()) {
      resolve({ kind: "error", message });
    }
    this.pending.clear();
    this.output = "";
    return process;
  }
  findExecutable() {
    if (this.executable && fs.existsSync(this.executable)) {
      return this.executable;
    }
    if (this.executablePath) {
      try {
        this.executable = fs.statSync(this.executablePath).isFile()
          ? this.executablePath
          : undefined;
      } catch {
        this.executable = undefined;
      }
      return this.executable;
    }
    this.executable = this.tongue
      ? this.findCabalExecutable(this.tongue) ||
        this.findDistExecutable(this.tongue) ||
        findOnPath()
      : findOnPath();
    return this.executable;
  }
  findCabalExecutable(tongue: string) {
    const result = childProcess.spawnSync("cabal", ["list-bin", "exe:tung"], {
      cwd: tongue,
      encoding: "utf8",
    });
    const found = result.status === 0 ? result.stdout.trim() : "";
    return found && fs.existsSync(found) ? found : undefined;
  }
  findDistExecutable(tongue: string) {
    return findFile(path.join(tongue, "dist-newstyle", "build"), (file) =>
      file.endsWith(path.join("x", "tung", "build", "tung", "tung")),
    );
  }
}
const findOnPath = () => {
  const names = process.platform === "win32" ? ["tung.exe", "tung"] : ["tung"];
  for (const directory of (process.env.PATH || "").split(path.delimiter)) {
    if (!directory) continue;
    for (const name of names) {
      const candidate = path.join(directory, name);
      try {
        if (fs.statSync(candidate).isFile()) {
          fs.accessSync(candidate, fs.constants.X_OK);
          return candidate;
        }
      } catch {
        // the next PATH entry may contain the compiler.
      }
    }
  }
  return undefined;
};
const findFile = (root: string, predicate: (file: string) => boolean) => {
  if (!fs.existsSync(root)) return undefined;
  const stack = [root];
  let current: string | undefined;
  while ((current = stack.pop()) !== undefined) {
    const stat = fs.statSync(current);
    if (stat.isFile() && predicate(current)) return current;
    if (stat.isDirectory()) {
      for (const entry of fs.readdirSync(current)) {
        stack.push(path.join(current, entry));
      }
    }
  }
  return undefined;
};
const isObject = (value: unknown): value is Record<string, unknown> =>
  value !== null && typeof value === "object" && !Array.isArray(value);
const isStrings = (value: unknown): value is string[] =>
  Array.isArray(value) && value.every((item) => typeof item === "string");
const isRange = (start: unknown, end: unknown) =>
  Number.isSafeInteger(start) &&
  Number.isSafeInteger(end) &&
  (start as number) >= 0 &&
  (end as number) >= (start as number);
const isDiagnostic = (value: unknown): value is CompilerDiagnostic =>
  isObject(value) &&
  ["parse", "type", "goal"].includes(value.kind as string) &&
  (value.path === undefined || typeof value.path === "string") &&
  isRange(value.start, value.end) &&
  typeof value.message === "string";
const isRole = (value: unknown): value is SourceRole =>
  Array.isArray(value) &&
  value.length === 4 &&
  isRange(value[0], value[1]) &&
  typeof value[2] === "string" &&
  isStrings(value[3]);
const isProofDependency = (value: unknown): value is ProofDependency =>
  isObject(value) &&
  isObject(value.symbol) &&
  typeof value.symbol.module === "string" &&
  typeof value.symbol.name === "string" &&
  typeof value.name === "string" &&
  typeof value.type === "string" &&
  ["sorry", "axiom", "host"].includes(value.kind as string) &&
  (value.kind === "host"
    ? typeof value.host === "string"
    : value.host === undefined);
const isResult = (value: unknown): value is CompilerResult => {
  if (!isObject(value)) return false;
  switch (value.kind) {
    case "check":
      return (
        Array.isArray(value.diagnostics) &&
        value.diagnostics.every(isDiagnostic)
      );
    case "type":
      return typeof value.type === "string";
    case "proof":
      return (
        isObject(value.audit) &&
        typeof value.audit.name === "string" &&
        typeof value.audit.type === "string" &&
        Array.isArray(value.audit.dependencies) &&
        value.audit.dependencies.every(isProofDependency) &&
        typeof value.verified === "boolean" &&
        typeof value.message === "string" &&
        typeof value.report === "string"
      );
    case "format":
      return typeof value.source === "string";
    case "highlight":
      return (
        Array.isArray(value.roles) &&
        value.roles.every(isRole) &&
        Array.isArray(value.tokens) &&
        value.tokens.every(
          (token) =>
            Array.isArray(token) &&
            isRange(token[0], token[1]) &&
            typeof token[2] === "string",
        ) &&
        Array.isArray(value.declarations) &&
        value.declarations.every(
          (declaration) =>
            isObject(declaration) &&
            typeof declaration.kind === "string" &&
            isRange(declaration.start, declaration.end) &&
            Number.isSafeInteger(declaration.headerEnd) &&
            typeof declaration.shown === "boolean",
        ) &&
        Array.isArray(value.imports) &&
        value.imports.every(
          (entry) =>
            isObject(entry) &&
            typeof entry.path === "string" &&
            isRange(entry.start, entry.end),
        ) &&
        Array.isArray(value.scopes) &&
        value.scopes.every(
          (row) =>
            Array.isArray(row) &&
            row.length === 4 &&
            row.every(Number.isSafeInteger),
        )
      );
    case "names":
      return (
        isObject(value.files) &&
        Object.values(value.files).every((file) => typeof file === "string") &&
        Array.isArray(value.resolved) &&
        value.resolved.every(
          (entry) =>
            Array.isArray(entry) &&
            isRange(entry[0], entry[1]) &&
            typeof entry[2] === "string" &&
            typeof entry[3] === "string" &&
            typeof entry[4] === "boolean",
        ) &&
        Array.isArray(value.visible) &&
        value.visible.every(
          (entry) =>
            Array.isArray(entry) &&
            typeof entry[0] === "string" &&
            typeof entry[1] === "string" &&
            typeof entry[2] === "string" &&
            typeof entry[3] === "boolean",
        )
      );
    case "error":
      return typeof value.message === "string";
    default:
      return false;
  }
};
const isCompilerResponse = (value: unknown): value is CompilerResponse =>
  isObject(value) &&
  value.protocol === 1 &&
  Number.isSafeInteger(value.id) &&
  (value.id as number) > 0 &&
  Number.isSafeInteger(value.version) &&
  isResult(value.result);
// a file document nameth its path, so the session can reuse the project's
// interface cache.
const documentPath = (uri: string | undefined) => {
  if (!uri?.startsWith("file:")) return undefined;
  try {
    return fileURLToPath(uri);
  } catch {
    return undefined;
  }
};
// open documents send their unsaved texts by path; the compiler resolveth
// brings and readeth every other module from disk.
const sessionRequest = (
  id: number,
  version: number,
  command: CompilerCommand,
  name: string,
  source: string,
  texts: [string, string][],
  path?: string,
  allowedAxioms?: string[],
) =>
  JSON.stringify({
    protocol: 1,
    id,
    version,
    command,
    name,
    source,
    texts: Object.fromEntries(texts),
    ...(path === undefined ? {} : { path }),
    ...(allowedAxioms === undefined ? {} : { allowedAxioms }),
  }) + "\n";
export { CompilerBridge, emptyNames, emptySyntax, sessionRequest };
export type {
  CompilerDiagnostic,
  CompilerResult,
  ErrorResult,
  ProofResult,
  ResultOf,
  Running,
  SourceDocument,
  SourceNames,
  SourceRole,
  SourceSyntax,
};
