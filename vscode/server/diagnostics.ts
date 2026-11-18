// debounced, versioned checks and the diagnostics they publish. a root
// document's check may find an error in one of its imports: each root keepeth
// its own report, and a uri showeth every report that targeteth it.
// cancellation stoppeth obsolete work in the compiler session before a newer
// request is sent.
import {
  type Connection,
  type Diagnostic,
  DiagnosticSeverity,
  type Range,
  type TextDocuments,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import type {
  CompilerBridge,
  CompilerDiagnostic,
  ResultOf,
  Running,
} from "./checker.ts";
import { uniqueByKey, type WorkspaceIndex } from "./workspace.ts";
const defaultCheckDelay = 500;
type Report = { targetUri: string; diagnostic: Diagnostic };
class DiagnosticPublisher {
  timers = new Map<string, NodeJS.Timeout>();
  checks = new Map<string, Running<ResultOf<"check">>>();
  reports = new Map<string, Report[]>();
  // the goals of the latest successful check, by document.
  goals = new Map<string, CompilerDiagnostic[]>();
  constructor(
    public connection: Connection,
    public documents: TextDocuments<TextDocument>,
    public workspace: WorkspaceIndex,
    public compiler: CompilerBridge,
    // why no check can run, if anything stoppeth every check.
    public blocked: () => string | undefined,
  ) {}
  schedule(document: TextDocument, delay = defaultCheckDelay) {
    this.cancel(document.uri);
    this.timers.set(
      document.uri,
      setTimeout(() => this.run(document), delay),
    );
  }
  scheduleAll() {
    for (const document of this.documents.all()) this.schedule(document, 0);
  }
  cancel(uri: string) {
    clearTimeout(this.timers.get(uri));
    this.timers.delete(uri);
    this.checks.get(uri)?.cancel();
    this.checks.delete(uri);
  }
  // a closed document withdraweth its diagnostics from every document they name.
  close(uri: string) {
    this.cancel(uri);
    const previous = this.reports.get(uri) ?? [];
    this.reports.delete(uri);
    this.goals.delete(uri);
    for (const { targetUri } of previous) this.refresh(targetUri);
    this.refresh(uri);
  }
  goalAt(uri: string, offset: number) {
    return this.goals
      .get(uri)
      ?.find(({ start, end }) => start <= offset && offset < end);
  }
  async run(document: TextDocument) {
    this.timers.delete(document.uri);
    const blocked = this.blocked();
    if (blocked) {
      this.publish(document, blocked);
      return;
    }
    // imports come from the compiler's syntax of each document; a newer edit
    // or check supersedeth this one meanwhile.
    await this.workspace.ready();
    const model = this.workspace.model(document.uri);
    if (
      !model ||
      this.timers.has(document.uri) ||
      this.checks.has(document.uri) ||
      this.documents.get(document.uri)?.version !== document.version
    )
      return;
    const running = this.compiler.check(
      model,
      this.workspace.openTexts(),
      document.version,
    );
    this.checks.set(document.uri, running);
    const output = await running.result;
    if (this.checks.get(document.uri) !== running) return;
    this.checks.delete(document.uri);
    const current = this.documents.get(document.uri);
    if (!current || current.version !== running.version) return;
    const diagnostics = output.kind === "check" ? output.diagnostics : [];
    const goals = diagnostics.filter(({ kind }) => kind === "goal");
    this.goals.set(current.uri, goals);
    this.publish(
      current,
      output.kind === "error"
        ? output.message
        : diagnostics.find(({ kind }) => kind !== "goal"),
      goals,
    );
  }
  publish(
    document: TextDocument,
    problem: string | CompilerDiagnostic | undefined,
    goals: CompilerDiagnostic[] = [],
  ) {
    const previous = this.reports.get(document.uri) ?? [];
    // a root buffer's goals retain their locations when an import hath an error.
    const items: Report[] = goals.map(({ start, end, message }) => ({
      targetUri: document.uri,
      diagnostic: {
        range: {
          start: document.positionAt(start),
          end: document.positionAt(end),
        },
        severity: DiagnosticSeverity.Information,
        source: "tung",
        message,
      },
    }));
    const message = typeof problem === "string" ? problem : problem?.message;
    if (problem && message) {
      const owner = this.owner(document, problem);
      items.unshift({
        targetUri: owner.uri,
        diagnostic: {
          range: errorRange(owner, problem),
          severity: DiagnosticSeverity.Error,
          source: "tung",
          message,
        },
      });
    }
    if (items.length) this.reports.set(document.uri, items);
    else this.reports.delete(document.uri);
    for (const uri of new Set([
      document.uri,
      ...[...previous, ...items].map(({ targetUri }) => targetUri),
    ])) {
      this.refresh(uri);
    }
  }
  // an error in an import belongeth to that import's document.
  owner(document: TextDocument, problem: string | CompilerDiagnostic) {
    if (typeof problem === "string" || !problem.path) return document;
    const root = this.workspace.model(document.uri);
    const imported = this.workspace.importModel(root, problem.path);
    if (!imported) return document;
    return (
      this.documents.get(imported.uri) ??
      TextDocument.create(imported.uri, "tung", 0, imported.text)
    );
  }
  refresh(uri: string) {
    const diagnostics = uniqueByKey(
      [...this.reports.values()]
        .flat()
        .filter(({ targetUri }) => targetUri === uri)
        .map(({ diagnostic }) => diagnostic),
      ({ range, message }) =>
        `${range.start.line}:${range.start.character}:${range.end.line}:${range.end.character}:${message}`,
    );
    const open = this.documents.get(uri);
    this.connection.sendDiagnostics({
      uri,
      ...(open ? { version: open.version } : {}),
      diagnostics,
    });
  }
}
// an unlocated problem standeth at the start of its file.
const errorRange = (
  document: TextDocument,
  problem: string | CompilerDiagnostic,
): Range =>
  typeof problem === "string"
    ? {
        start: document.positionAt(0),
        end: document.positionAt(Math.min(1, document.getText().length)),
      }
    : {
        start: document.positionAt(problem.start),
        end: document.positionAt(problem.end),
      };
export { DiagnosticPublisher };
