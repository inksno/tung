// lsp transport and request orchestration. tolerant workspace models serve
// editor features; the compiler bridge alone supplieth authoritative diagnostics.
import * as fs from "node:fs";
import * as path from "node:path";
import {
  type CancellationToken,
  type CompletionItem,
  CompletionItemKind,
  createConnection,
  DidChangeWatchedFilesNotification,
  DidChangeWorkspaceFoldersNotification,
  DocumentHighlightKind,
  type Hover,
  InsertTextFormat,
  type Location,
  MarkupKind,
  type Position,
  ProposedFeatures,
  type Range,
  type SelectionRange,
  SemanticTokensBuilder,
  SymbolKind,
  type TextDocumentPositionParams,
  TextDocuments,
  TextDocumentSyncKind,
  type TextEdit,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import {
  type DocumentModel,
  nameRange,
  roleLabel,
  smallestRegion,
  tokenAtPosition,
  tokenRange,
} from "./analysis.ts";
import {
  CompilerBridge,
  type ErrorResult,
  type ProofResult,
} from "./checker.ts";
import { DiagnosticPublisher } from "./diagnostics.ts";
import {
  buildHighlightRanges,
  tokenModifiers,
  tokenTypes,
} from "./highlight.ts";
import {
  readDeclaredLibraryPaths,
  resolveLibraryPaths,
} from "./library-paths.ts";
import { languageNames } from "./syntax.ts";
import {
  type Completion,
  type Referent,
  toFilePath,
  uniqueByKey,
  WorkspaceIndex,
} from "./workspace.ts";
const connection = createConnection(ProposedFeatures.all);
const documents = new TextDocuments(TextDocument);
const compiler = new CompilerBridge();
const workspace = new WorkspaceIndex(documents, compiler);
const diagnostics = new DiagnosticPublisher(
  connection,
  documents,
  workspace,
  compiler,
  () => checkBlocker(),
);
// navigation readeth models built from the compiler's syntax and names;
// missing ones are fetched before the request is answered. a request that
// searcheth every document fetcheth the names of every document.
const navigation =
  <Arguments extends unknown[], Result>(
    handler: (...parameters: Arguments) => Result,
    everywhere = false,
  ) =>
  async (...parameters: Arguments): Promise<Awaited<Result>> => {
    await workspace.ready(everywhere);
    return await handler(...parameters);
  };
const typeCache = new Map<
  string,
  { promise: Promise<string | undefined>; cancel: () => void }
>();
const dependentCheckDelay = 1000;
const semanticRefreshDelay = 200;
let workspaceRoots: string[] = [];
let canRegisterWatchedFiles = false;
let canRefreshSemanticTokens = false;
let configuredTongue: string | undefined;
let configuredExecutable: string | undefined;
let configuredLibraryPaths: unknown;
let localLibraryRoots: string[] = [];
let libraryResolutionError: string | undefined;
let semanticRefreshTimer: NodeJS.Timeout | undefined;
const keywordHelp = new Map([
  [
    "bring",
    "import a tung file; its last path segment is the default namespace, and an optional alias overrideth it.",
  ],
  [
    "show",
    "publish a declaration, or re-export every visible term, type, and class with a name.",
  ],
  ["yield", "introduce a block result."],
  [
    "sorry",
    "stand for an omitted proof or definition of any type; performing it is a runtime error.",
  ],
  [
    "axiom",
    "assume a named constant of a type without a proof; `--check` lists it, `--no-sorry` alloweth it, and `--no-axiom` refuseth it in a proof check.",
  ],
  [
    "unbuild",
    "name the eliminator of a type or class: `drive unbuild name methods target` performeth structural induction.",
  ],
  ["class", "declare a class and its members."],
  [
    "foreign",
    "bind an annotated file-level let to the host function named by a preceding string key.",
  ],
  ["bizen", "provide evidence and member definitions for a class."],
  [
    "match",
    "match one or more values against exhaustive pattern rows; `;` joineth rows that share a result.",
  ],
  [
    "function",
    "write an annotated function: inputs, a final result type, `^`, and the body.",
  ],
  ["let", "bind a value, curried function, or type alias."],
  [
    "fast",
    "declare an annotated effect whose body may call it without bound; checking never unfoldeth it.",
  ],
  ["effect", "the primitive type of an action the runner performeth."],
  ["type", "declare an inductive type and its constructors."],
]);
// a setting is a non-empty string or absent.
const stringOption = (value: unknown) =>
  typeof value === "string" && value ? value : undefined;
connection.onInitialize((params) => {
  const options = params.initializationOptions;
  configuredTongue = stringOption(options?.tonguePath);
  configuredExecutable = stringOption(options?.executablePath);
  configuredLibraryPaths = options?.libraryPaths;
  canRegisterWatchedFiles = Boolean(
    params.capabilities.workspace?.didChangeWatchedFiles?.dynamicRegistration,
  );
  canRefreshSemanticTokens = Boolean(
    params.capabilities.workspace?.semanticTokens?.refreshSupport,
  );
  workspaceRoots = uniqueByKey(
    [
      ...(params.workspaceFolders ?? []).map(({ uri }) => uri),
      params.rootUri,
    ].flatMap((uri) => toFilePath(uri) ?? []),
  );
  configureWorkspace();
  return {
    capabilities: {
      textDocumentSync: {
        openClose: true,
        change: TextDocumentSyncKind.Incremental,
        save: { includeText: true },
      },
      semanticTokensProvider: {
        legend: { tokenTypes, tokenModifiers },
        full: true,
        range: true,
      },
      completionProvider: { triggerCharacters: ["/", "."] },
      hoverProvider: true,
      definitionProvider: true,
      declarationProvider: true,
      typeDefinitionProvider: true,
      implementationProvider: true,
      referencesProvider: true,
      documentHighlightProvider: true,
      documentSymbolProvider: true,
      workspaceSymbolProvider: true,
      renameProvider: { prepareProvider: true },
      foldingRangeProvider: true,
      selectionRangeProvider: true,
      documentLinkProvider: { resolveProvider: false },
      documentFormattingProvider: true,
      signatureHelpProvider: { triggerCharacters: [" ", "$"] },
      workspace: {
        workspaceFolders: {
          supported: true,
          changeNotifications: true,
        },
      },
    },
    serverInfo: { name: "tung-language-server", version: "0.1.0" },
  };
});
connection.onInitialized(() => {
  if (!canRegisterWatchedFiles) return;
  connection.client
    .register(DidChangeWatchedFilesNotification.type, {
      watchers: [{ globPattern: "**/*.tung" }, { globPattern: "**/tung.yaml" }],
    })
    .catch(() => {});
});
connection.onShutdown(() => {
  workspace.clearSyntax();
  compiler.dispose();
});
connection.onRequest(
  "tung/executable",
  () => compiler.findExecutable() ?? null,
);
connection.onRequest("tung/libraryPath", () =>
  localLibraryRoots.join(path.delimiter),
);
type ProofRequest = {
  textDocument: { uri: string };
  position?: Position;
  name?: unknown;
  allowedAxioms?: string[];
};
connection.onRequest<ProofResult | ErrorResult, never>(
  "tung/checkProof",
  navigation(
    async (
      { textDocument, position, name, allowedAxioms }: ProofRequest,
      cancellation?: CancellationToken,
    ): Promise<ProofResult | ErrorResult> => {
      if (libraryResolutionError)
        return {
          kind: "error",
          message: `project error: ${libraryResolutionError}`,
        };
      const model = workspace.model(textDocument.uri);
      if (!model)
        return { kind: "error", message: "open a tung file to check a proof" };
      const document = documents.get(textDocument.uri);
      const version = document?.version ?? 0;
      const offset = position && document?.offsetAt(position);
      const region =
        offset === undefined
          ? undefined
          : smallestRegion(
              model.regions.filter(
                (candidate) =>
                  candidate.depth === 0 &&
                  (candidate.kind === "let" || candidate.kind === "fast"),
              ),
              offset,
            );
      const declaration =
        region &&
        model.definitions.find(
          (definition) =>
            definition.topLevel &&
            definition.token.index > region.startIndex &&
            definition.token.index <= region.headerEnd,
        );
      const selected =
        typeof name === "string" && name.trim()
          ? name.trim()
          : declaration?.name;
      if (!selected)
        return {
          kind: "error",
          message:
            "select a proof name or place the cursor in its top-level let or fast declaration",
        };
      const reached = JSON.stringify(workspace.reachedTexts(model.uri));
      const running = compiler.proof(
        model,
        workspace.openTexts(),
        selected,
        version,
        allowedAxioms,
      );
      const cancelled = cancellation?.onCancellationRequested(() =>
        running.cancel(),
      );
      try {
        const result = await running.result;
        const current = workspace.model(textDocument.uri);
        if (
          (documents.get(textDocument.uri)?.version ?? 0) !== version ||
          current?.text !== model.text ||
          JSON.stringify(workspace.reachedTexts(model.uri)) !== reached
        )
          return {
            kind: "error",
            message:
              "the proof source or its imports changed; check the proof again",
          };
        return result;
      } finally {
        cancelled?.dispose();
      }
    },
  ),
);
process.on("exit", () => compiler.dispose());
connection.onNotification(
  DidChangeWorkspaceFoldersNotification.type,
  ({ event }) => {
    const removed = new Set(
      event.removed.flatMap(({ uri }) => toFilePath(uri) ?? []),
    );
    workspaceRoots = uniqueByKey([
      ...workspaceRoots.filter((root) => !removed.has(root)),
      ...event.added.flatMap(({ uri }) => toFilePath(uri) ?? []),
    ]);
    configureWorkspace();
    diagnostics.scheduleAll();
    scheduleSemanticRefresh();
  },
);
connection.onDidChangeWatchedFiles(({ changes }) => {
  if (
    changes.some(
      ({ uri }) => path.basename(toFilePath(uri) ?? "") === "tung.yaml",
    )
  ) {
    configureWorkspace();
  }
  for (const { uri } of changes) workspace.invalidate(uri);
  workspace.invalidateFiles();
  diagnostics.scheduleAll();
  scheduleSemanticRefresh();
});
connection.languages.semanticTokens.on(({ textDocument }) =>
  semanticTokens(textDocument.uri),
);
connection.languages.semanticTokens.onRange(({ textDocument, range }) =>
  semanticTokens(textDocument.uri, range),
);
connection.onCompletion(
  navigation(({ textDocument, position }): CompletionItem[] => {
    const model = workspace.model(textDocument.uri);
    const document = documents.get(textDocument.uri);
    if (!model || !document) return [];
    const before = document.getText().slice(0, document.offsetAt(position));
    if (inImportPath(model, position, before)) {
      return workspace.modulePaths(textDocument.uri).map((label) => ({
        label,
        kind: CompletionItemKind.Module,
        detail: "tung module",
      }));
    }
    const prefix = before.match(/[^\s#()[\]{}:,;=.$`'@^]+$/u)?.[0] ?? "";
    const definitionItems = [
      ...workspace.completions(textDocument.uri, position),
      ...workspace.primitiveCompletions(),
    ]
      .map(completionItem)
      .filter(
        ({ label }) =>
          !prefix || label.startsWith(prefix) || label.includes(`.${prefix}`),
      );
    const keywordItems = languageNames.keywords
      .filter((name) => !prefix || name.startsWith(prefix))
      .map((label) => ({
        label,
        kind: CompletionItemKind.Keyword,
        detail: keywordHelp.get(label) ?? "tung keyword",
      }));
    return uniqueByKey(
      [...definitionItems, ...keywordItems],
      ({ label }) => label,
    );
  }),
);
connection.onHover(
  navigation(
    async ({ textDocument, position }, cancellation): Promise<Hover | null> => {
      // a `sorry` showeth the goal and context the latest check found there.
      const open = documents.get(textDocument.uri);
      const goal =
        open && diagnostics.goalAt(textDocument.uri, open.offsetAt(position));
      if (open && goal) {
        return {
          range: {
            start: open.positionAt(goal.start),
            end: open.positionAt(goal.end),
          },
          contents: {
            kind: MarkupKind.Markdown,
            value: `\`\`\`tung\n${goal.message}\n\`\`\``,
          },
        };
      }
      const { token, definition } = workspace.resolveAt(
        textDocument.uri,
        position,
      );
      if (!token) return null;
      if (definition) {
        const inferred = await inspectType(definition, cancellation);
        const docText = definition.documentation
          ? `${definition.documentation}\n\n`
          : "";
        const typeText = inferred
          ? `\n\n**inferred type**\n\n\`\`\`tung\n${definition.bareName}: ${inferred}\n\`\`\``
          : "";
        return {
          range: nameRange(token),
          contents: {
            kind: MarkupKind.Markdown,
            value: `${docText}\`\`\`tung\n${definition.detail}\n\`\`\`\n\n${roleDescription(
              definition,
            )}${typeText}`,
          },
        };
      }
      const help =
        token.kind === "keyword" ? keywordHelp.get(token.text) : undefined;
      if (help) {
        return {
          range: tokenRange(token),
          contents: { kind: MarkupKind.Markdown, value: help },
        };
      }
      const primitive = workspace
        .primitiveCompletions()
        .find(({ label }) => label === token.text);
      return primitive
        ? {
            range: nameRange(token),
            contents: {
              kind: MarkupKind.Markdown,
              value: primitive.definition.detail,
            },
          }
        : null;
    },
  ),
);
const navigateToDefinition = navigation(
  ({ textDocument, position }: TextDocumentPositionParams): Location | null => {
    const { definition } = workspace.resolveAt(textDocument.uri, position);
    return definition && !definition.primitive && definition.uri
      ? { uri: definition.uri, range: definition.selectionRange }
      : null;
  },
);
connection.onDefinition(navigateToDefinition);
connection.onDeclaration(navigateToDefinition);
connection.onTypeDefinition(navigateToDefinition);
connection.onImplementation(
  navigation(({ textDocument, position }) => {
    const { definition } = workspace.resolveAt(textDocument.uri, position);
    return workspace.implementations(definition);
  }),
);
connection.onReferences(
  navigation(({ textDocument, position, context }) => {
    const { definition } = workspace.resolveAt(textDocument.uri, position);
    return workspace.references(definition, context.includeDeclaration);
  }, true),
);
connection.onDocumentHighlight(
  navigation(({ textDocument, position }) => {
    const { definition } = workspace.resolveAt(textDocument.uri, position);
    return workspace
      .references(definition, true, textDocument.uri)
      .filter(({ uri }) => uri === textDocument.uri)
      .map(({ range }) => ({ range, kind: DocumentHighlightKind.Read }));
  }),
);
connection.onDocumentSymbol(
  navigation(({ textDocument }) => {
    const model = workspace.model(textDocument.uri);
    if (!model) return [];
    return model.definitions
      .filter((definition) => !definition.local && definition.topLevel)
      .map((definition) => ({
        name: definition.bareName,
        detail: definition.detail,
        kind: symbolKind(definition.role),
        range:
          smallestRegion(model.regions, definition.token.offset)?.range ??
          definition.selectionRange,
        selectionRange: definition.selectionRange,
      }));
  }),
);
connection.onWorkspaceSymbol(
  navigation(({ query }) => {
    const wanted = query.toLocaleLowerCase();
    return workspace.models().flatMap((model) =>
      model.definitions
        .filter(
          (definition) =>
            !definition.local &&
            (!wanted ||
              definition.bareName.toLocaleLowerCase().includes(wanted)),
        )
        .map((definition) => ({
          name: definition.bareName,
          kind: symbolKind(definition.role),
          location: {
            uri: definition.uri,
            range: definition.selectionRange,
          },
          containerName: definition.containerName,
        })),
    );
  }),
);
connection.onPrepareRename(
  navigation(({ textDocument, position }) => {
    const { token, definition } = workspace.resolveAt(
      textDocument.uri,
      position,
    );
    if (!token || !definition || definition.primitive) return null;
    return { range: nameRange(token), placeholder: definition.bareName };
  }),
);
connection.onRenameRequest(
  navigation(({ textDocument, position, newName }) => {
    if (!validName(newName)) throw new Error(`invalid tung name '${newName}'`);
    const { definition } = workspace.resolveAt(textDocument.uri, position);
    if (!definition || definition.primitive) return null;
    const changes: Record<string, TextEdit[]> = {};
    for (const { uri, range } of workspace.references(definition, true)) {
      (changes[uri] ||= []).push({ range, newText: newName });
    }
    return { changes };
  }, true),
);
connection.onFoldingRanges(
  navigation(
    ({ textDocument }) => workspace.model(textDocument.uri)?.folds ?? [],
  ),
);
connection.onSelectionRanges(
  navigation(({ textDocument, positions }) => {
    const model = workspace.model(textDocument.uri);
    if (!model) return [];
    return positions.map((position) => selectionRange(model, position));
  }),
);
connection.onDocumentLinks(
  navigation(({ textDocument }) => {
    const model = workspace.model(textDocument.uri);
    if (!model) return [];
    return model.imports.flatMap((imported) => {
      const target = workspace.importModel(model, imported.path);
      return target
        ? [
            {
              range: imported.range,
              target: target.uri,
              tooltip: `open ${imported.path}`,
            },
          ]
        : [];
    });
  }),
);
connection.onDocumentFormatting(
  async ({ textDocument }): Promise<TextEdit[]> => {
    const document = documents.get(textDocument.uri);
    if (!document) return [];
    const source = document.getText();
    const version = document.version;
    const formatted = await compiler.format(source, version).result;
    return formatted === undefined ||
      formatted === source ||
      documents.get(textDocument.uri)?.version !== version
      ? []
      : [{ range: fullRange(document), newText: formatted }];
  },
);
connection.onSignatureHelp(
  navigation(({ textDocument, position }) => {
    const model = workspace.model(textDocument.uri);
    if (!model) return null;
    const before = model.tokens
      .filter(
        (token) =>
          token.line < position.line ||
          (token.line === position.line && token.char < position.character),
      )
      .at(-1);
    if (!before) return null;
    const { definition } = workspace.resolveAt(textDocument.uri, {
      line: before.line,
      character: before.char,
    });
    if (!definition || !["function", "method"].includes(definition.role)) {
      return null;
    }
    return {
      signatures: [{ label: definition.detail || definition.bareName }],
      activeSignature: 0,
      activeParameter: 0,
    };
  }),
);
documents.onDidOpen(({ document }) => {
  configureWorkspace();
  workspace.invalidate(document.uri);
  clearTypeCache(document.uri);
  diagnostics.scheduleAll();
});
documents.onDidChangeContent(({ document }) => {
  workspace.invalidate(document.uri);
  clearTypeCache(document.uri);
  diagnostics.schedule(document);
  for (const dependent of documents.all()) {
    if (dependent.uri !== document.uri) {
      diagnostics.schedule(dependent, dependentCheckDelay);
    }
  }
  scheduleSemanticRefresh();
});
documents.onDidSave(({ document }) => {
  workspace.invalidate(document.uri);
  clearTypeCache(document.uri);
});
documents.onDidClose(({ document }) => {
  diagnostics.close(document.uri);
  configureWorkspace();
  workspace.invalidate(document.uri);
  diagnostics.scheduleAll();
});
// requests share one compiler parse per buffer version. navigation refineth only
// names whose constructor identity requireth workspace context.
const semanticTokens = async (uri: string, requestedRange?: Range) => {
  const document = documents.get(uri);
  const builder = new SemanticTokensBuilder();
  if (!document) return builder.build();
  const source = document.getText();
  const version = document.version;
  const { roles } = await workspace.syntax(uri, source, version);
  await workspace.ready();
  if (documents.get(uri)?.version !== version) return builder.build();
  const types = new Map(
    workspace.namesOf(uri).resolved.map(([start, , , , type]) => [start, type]),
  );
  const ranges = buildHighlightRanges(
    source,
    roles,
    (token) =>
      workspace.resolveAt(uri, { line: token.line, character: token.char })
        .definition,
    (start) => types.get(start),
  );
  for (const token of ranges) {
    if (
      requestedRange &&
      (token.line < requestedRange.start.line ||
        token.line > requestedRange.end.line)
    ) {
      continue;
    }
    const type = tokenTypes.indexOf(token.type);
    if (type < 0) continue;
    builder.push(
      token.line,
      token.char,
      token.length,
      type,
      token.modifiers.reduce((bits, name) => {
        const index = tokenModifiers.indexOf(name);
        return index < 0 ? bits : bits | (1 << index);
      }, 0),
    );
  }
  return builder.build();
};
const scheduleSemanticRefresh = (delay = semanticRefreshDelay) => {
  clearTimeout(semanticRefreshTimer);
  semanticRefreshTimer = setTimeout(() => {
    semanticRefreshTimer = undefined;
    if (canRefreshSemanticTokens) {
      Promise.resolve(connection.languages.semanticTokens.refresh()).catch(
        () => {},
      );
    }
  }, delay);
};
// why no check can run: the project's libraries do not resolve, or there is
// no compiler.
const checkBlocker = () => {
  if (libraryResolutionError) return `project error: ${libraryResolutionError}`;
  if (compiler.available()) return undefined;
  return configuredExecutable
    ? `could not find tung executable at ${configuredExecutable}`
    : "could not find tung executable; install tung or set tung.executablePath";
};
const inspectType = (
  definition: Referent,
  cancellation?: CancellationToken,
): Promise<string | undefined> => {
  if (definition.primitive || !definition.uri || !compiler.available()) {
    return Promise.resolve(undefined);
  }
  const model = workspace.model(definition.uri);
  if (!model) return Promise.resolve(undefined);
  const key = `${definition.uri}\0${definition.bareName}\0${model.text}`;
  const cached = typeCache.get(key);
  if (cached) return cached.promise;
  const version = documents.get(definition.uri)?.version ?? 0;
  const running = compiler.typeOf(
    model,
    workspace.openTexts(),
    definition.bareName,
    version,
  );
  const entry = {
    cancel: running.cancel,
    promise: running.result.then((output) =>
      output.kind === "type" ? output.type : undefined,
    ),
  };
  typeCache.set(key, entry);
  const cancelled = cancellation?.onCancellationRequested(() => {
    if (typeCache.get(key) !== entry) return;
    typeCache.delete(key);
    entry.cancel();
  });
  return entry.promise.finally(() => cancelled?.dispose());
};
const clearTypeCache = (uri: string) => {
  for (const key of typeCache.keys()) {
    if (!key.startsWith(`${uri}\0`)) continue;
    typeCache.get(key)?.cancel();
    typeCache.delete(key);
  }
};
const completionItem = ({ label, definition }: Completion): CompletionItem => ({
  label,
  kind: completionKind(definition.role),
  detail: definition.detail,
  documentation: definition.documentation,
  insertText: label,
  insertTextFormat: InsertTextFormat.PlainText,
  sortText: `${definition.primitive ? 2 : definition.local ? 0 : 1}-${label}`,
});
const roleKinds: Record<string, [CompletionItemKind, SymbolKind]> = {
  namespace: [CompletionItemKind.Module, SymbolKind.Namespace],
  type: [CompletionItemKind.TypeParameter, SymbolKind.TypeParameter],
  class: [CompletionItemKind.Interface, SymbolKind.Interface],
  function: [CompletionItemKind.Function, SymbolKind.Function],
  method: [CompletionItemKind.Method, SymbolKind.Method],
  variable: [CompletionItemKind.Variable, SymbolKind.Variable],
  parameter: [CompletionItemKind.Variable, SymbolKind.Variable],
  property: [CompletionItemKind.Field, SymbolKind.Field],
  enumMember: [CompletionItemKind.EnumMember, SymbolKind.EnumMember],
};
const completionKind = (role: string) =>
  roleKinds[role]?.[0] ?? CompletionItemKind.Text;
const symbolKind = (role: string) => roleKinds[role]?.[1] ?? SymbolKind.String;
const roleDescription = (definition: Referent) => {
  if (definition.primitive) return `built-in · ${roleLabel(definition.role)}`;
  const file = toFilePath(definition.uri);
  const visibility = definition.exported
    ? "shown"
    : definition.local
      ? "local"
      : "private";
  return [
    visibility,
    roleLabel(definition.role),
    file ? `defined in \`${path.basename(file)}\`` : "",
  ]
    .filter(Boolean)
    .join(" · ");
};
// the token, then each bracket pair around it, innermost first.
const selectionRange = (
  model: DocumentModel,
  position: Position,
): SelectionRange => {
  const token = tokenAtPosition(model, position);
  const start = token?.offset ?? model.text.length;
  const end = token?.endOffset ?? model.text.length;
  const enclosing = [...model.pairs.entries()]
    .filter(
      ([open, close]) =>
        model.tokens[open].offset <= start &&
        end <= model.tokens[close].endOffset,
    )
    .sort(([a], [b]) => b - a)
    .map(([open, close]) =>
      tokenRange(model.tokens[open], model.tokens[close]),
    );
  return {
    range: token ? tokenRange(token) : { start: position, end: position },
    parent: enclosing.reduceRight<SelectionRange | undefined>(
      (parent, range) => ({ range, parent }),
      undefined,
    ),
  };
};
// a parsed bring path, or the word after an unfinished `bring`.
const inImportPath = (
  model: DocumentModel,
  position: Position,
  before: string,
) =>
  model.imports.some(({ range }) => positionInRange(position, range)) ||
  /(?:^|\s)bring\s+[^\s]*$/.test(before);
const fullRange = (document: TextDocument): Range => ({
  start: { line: 0, character: 0 },
  end: document.positionAt(document.getText().length),
});
const positionInRange = (position: Position, range: Range) =>
  comparePosition(range.start, position) <= 0 &&
  comparePosition(position, range.end) <= 0;
const comparePosition = (left: Position, right: Position) =>
  left.line - right.line || left.character - right.character;
const validName = (name: string) =>
  Boolean(name) && name !== "*" && !/[\s#()[\]{}:,;=.$`'@^]/u.test(name);
const configureWorkspace = () => {
  localLibraryRoots = resolveLibraryPaths(
    [],
    configuredLibraryPaths,
    process.env.TUNG_PATH,
  );
  if (
    compiler.configure(
      findTongueDir(configuredTongue),
      localLibraryRoots,
      configuredExecutable,
    )
  ) {
    workspace.clearSyntax();
  }
  let declared: string[] = [];
  libraryResolutionError = undefined;
  try {
    const openProjects = documents
      .all()
      .flatMap(({ uri }) => toFilePath(uri) ?? []);
    declared = readDeclaredLibraryPaths(
      compiler.findExecutable(),
      openProjects.length ? openProjects : workspaceRoots,
    );
  } catch (error) {
    libraryResolutionError = String(error);
    connection.console.error(libraryResolutionError);
  }
  workspace.configure(
    workspaceRoots,
    resolveLibraryPaths(declared, localLibraryRoots, undefined),
  );
};
// the compiler checkout: a configured directory, `TUNG_TONGUE`, a workspace
// root, or the repository this extension was built in.
const findTongueDir = (configured: string | undefined) => {
  const roots = [
    configured && path.resolve(configured),
    process.env.TUNG_TONGUE && path.resolve(process.env.TUNG_TONGUE),
    ...workspaceRoots,
    path.resolve(__dirname, "..", "..", ".."),
  ];
  for (const root of roots) {
    if (!root) continue;
    for (const candidate of [root, path.join(root, "tongue")]) {
      if (fs.existsSync(path.join(candidate, "tung.cabal"))) return candidate;
    }
  }
  return undefined;
};
documents.listen(connection);
connection.listen();
