// document model over the compiler's one parse of a buffer, complete or not:
// its roles, tokens, declarations, docs, imports, and local scopes. it addeth
// ownership; it never checketh types.
import type { Position, Range } from "vscode-languageserver/node";
import { emptySyntax, type SourceRole, type SourceSyntax } from "./checker.ts";
import {
  bracketPairs,
  lastQualifiedSegment,
  sourceTokens,
  tokenDepths,
  type SourceToken,
} from "./syntax.ts";
// a token's lsp role and modifiers.
type TokenRole = { type: string; modifiers: string[] };
// a declaration the compiler's tree holdeth. its header endeth at the index
// of the first token of its body, and its depth is its first token's.
type Region = {
  kind: string;
  startOffset: number;
  endOffset: number;
  startIndex: number;
  headerEnd: number;
  depth: number;
  shown: boolean;
  doc: string | undefined;
  range: Range;
};
// a name a document declareth, seen from `scopeStart` to `scopeEnd`.
type Definition = {
  primitive: false;
  id: string;
  uri: string;
  name: string;
  bareName: string;
  role: string;
  token: SourceToken;
  selectionRange: Range;
  scopeStart: number;
  scopeEnd: number;
  exported: boolean;
  local: boolean;
  topLevel: boolean;
  detail: string;
  callableConstructor: boolean;
  documentation: string | undefined;
  containerName: string | undefined;
};
type Instance = { className: string; uri: string; range: Range };
type DocumentModel = ReturnType<typeof analyzeDocument>;
const ownedKinds = new Set(["type", "class"]);
const localRoles = new Set(["parameter", "typeParameter"]);
// lsp role names stay in the protocol; people read them in tung's terms.
const roleNames: Record<string, string> = {
  type: "type",
  typeParameter: "type input",
  class: "class",
  enumMember: "constructor",
  method: "member",
};
const roleLabel = (role: string) => roleNames[role] ?? role;
const analyzeDocument = (
  text: string,
  uri = "",
  syntax: SourceSyntax = emptySyntax,
) => {
  const tokens = sourceTokens(text, syntax);
  const depths = tokenDepths(tokens);
  const pairs = bracketPairs(tokens);
  const regions = declarationRegions(tokens, depths, syntax);
  const { roles, callableConstructors } = compilerRoles(
    tokens,
    syntax.roles,
    regions,
    depths,
  );
  const imports = syntax.imports.flatMap(({ path, start, end }) => {
    const first = tokenAt(tokens, start);
    const last = tokenEndingAt(tokens, end);
    return first && last ? [{ path, range: tokenRange(first, last) }] : [];
  });
  return {
    uri,
    text,
    tokens,
    roles,
    pairs,
    regions,
    imports,
    instances: collectInstances(uri, tokens, roles, regions),
    definitions: documentDefinitions(
      { uri, text, tokens, depths, regions, roles, callableConstructors },
      syntax,
    ),
    occurrences: tokens.filter((token) => token.kind === "name"),
    folds: [...pairs.entries()]
      .map(([open, close]) => ({
        startLine: tokens[open].line,
        endLine: tokens[close].line - 1,
      }))
      .filter(({ startLine, endLine }) => endLine > startLine),
  };
};
// compiler roles become the model's token roles. a header binder arriveth as
// `headerPattern`, since only name resolution can tell a binder from a
// constructor: it is a parameter here, and resolution prefereth a visible
// constructor of the same name. a direct declaration in a class or bizen
// body is a method; nested declarations retain their own roles.
const compilerRoles = (
  tokens: SourceToken[],
  sourceRoles: SourceRole[],
  regions: Region[],
  depths: number[],
) => {
  const byOffset = new Map(tokens.map((token) => [token.offset, token]));
  const roles = new Map<number, TokenRole>();
  const callableConstructors = new Set<string>();
  for (const [start, , role, modifiers] of sourceRoles) {
    const token = byOffset.get(start);
    if (!token || token.kind !== "name") continue;
    const declared = modifiers.includes("declaration");
    let type = role;
    let roleModifiers = modifiers.filter(
      (modifier) => modifier !== "constructor",
    );
    if (modifiers.includes("constructor")) {
      type = "enumMember";
      if (role === "function") {
        callableConstructors.add(lastQualifiedSegment(token.text));
      }
    } else if (role === "headerPattern") {
      type = "parameter";
      roleModifiers = ["declaration"];
    } else if (role === "call" && declared) {
      type = "function";
    }
    if (
      declared &&
      (type === "variable" || type === "function") &&
      regions.some(
        (region) =>
          (region.kind === "class" || region.kind === "bizen") &&
          depths[token.index] === region.depth + 1 &&
          token.index > region.headerEnd &&
          token.offset <= region.endOffset &&
          token.offset >= region.startOffset,
      )
    ) {
      type = "method";
    }
    roles.set(token.index, { type, modifiers: roleModifiers });
  }
  return { roles, callableConstructors };
};
const collectInstances = (
  uri: string,
  tokens: SourceToken[],
  roles: Map<number, TokenRole>,
  regions: Region[],
): Instance[] =>
  regions
    .filter(({ kind }) => kind === "bizen")
    .flatMap((region) => {
      for (
        let index = region.headerEnd - 1;
        index > region.startIndex;
        index -= 1
      ) {
        if (
          roles.get(index)?.type === "class" &&
          tokens[index]?.kind === "name"
        )
          return [
            {
              className: lastQualifiedSegment(tokens[index].text),
              uri,
              range: tokenRange(tokens[index]),
            },
          ];
      }
      return [];
    });
// regions supply ownership and source extents for symbols, folding, docs, and
// local scope. each is a declaration the compiler's tree holdeth.
const declarationRegions = (
  tokens: SourceToken[],
  depths: number[],
  syntax: SourceSyntax,
): Region[] =>
  syntax.declarations.flatMap(({ kind, start, end, headerEnd, shown, doc }) => {
    const startToken = tokenAt(tokens, start);
    const endToken = tokenEndingAt(tokens, end);
    if (!startToken || !endToken) return [];
    const header = tokens.findIndex((token) => token.offset >= headerEnd);
    return [
      {
        kind,
        startOffset: start,
        endOffset: end,
        startIndex: startToken.index,
        headerEnd: header < 0 ? tokens.length : header,
        depth: depths[startToken.index],
        shown,
        doc: doc ?? undefined,
        range: tokenRange(startToken, endToken),
      },
    ];
  });
const tokenAt = (tokens: SourceToken[], offset: number) =>
  tokens.find((token) => token.offset === offset);
const tokenEndingAt = (tokens: SourceToken[], offset: number) =>
  tokens.findLast((token) => token.endOffset === offset);
const documentDefinitions = (
  document: {
    uri: string;
    text: string;
    tokens: SourceToken[];
    depths: number[];
    regions: Region[];
    roles: Map<number, TokenRole>;
    callableConstructors: Set<string>;
  },
  syntax: SourceSyntax,
): Definition[] => {
  const { uri, text, tokens, depths, regions, roles } = document;
  // the parser giveth each local binder the span where it is seen; every
  // other declaration is seen by the whole document.
  const scopes = new Map(
    syntax.scopes.map(([start, , scopeStart, scopeEnd]) => [
      start,
      { start: scopeStart, end: scopeEnd },
    ]),
  );
  const documentEnd = tokens.at(-1)?.endOffset || 0;
  const definitions: Definition[] = [];
  for (const [index, role] of roles) {
    if (!role.modifiers.includes("declaration")) continue;
    const token = tokens[index];
    if (
      !token ||
      token.kind !== "name" ||
      token.text === "_" ||
      role.type === "namespace"
    ) {
      continue;
    }
    const bareName = lastQualifiedSegment(token.text);
    const region = smallestRegion(regions, token.offset);
    const owner =
      region && ownedKinds.has(region.kind) && token.index > region.headerEnd
        ? region
        : enclosingOwner(regions, region, token.offset);
    const binder = scopes.get(token.offset);
    const local = Boolean(binder) || localRoles.has(role.type);
    const primary =
      region &&
      token.index > region.startIndex &&
      token.index <= region.headerEnd;
    const exported =
      !local &&
      Boolean(
        (region?.shown && primary) ||
        (owner?.shown &&
          ["enumMember", "method", "function"].includes(role.type)),
      );
    // a local the parser could not scope, in broken source, keepeth to its
    // declaration.
    const scope =
      binder ??
      (local && region
        ? { start: region.startOffset, end: region.endOffset }
        : { start: 0, end: documentEnd });
    definitions.push({
      primitive: false,
      id: `${uri}:${token.offset}`,
      uri,
      name: token.text,
      bareName,
      role: role.type,
      token,
      selectionRange: tokenRange(token),
      scopeStart: scope.start,
      scopeEnd: scope.end,
      exported: !binder && exported,
      local,
      topLevel: !binder && depths[token.index] === 0,
      detail:
        binder && localRoles.has(role.type)
          ? `parameter ${bareName}`
          : declarationDetail(text, tokens, token, region, role.type),
      callableConstructor:
        !binder &&
        role.type === "enumMember" &&
        document.callableConstructors.has(bareName),
      documentation: binder ? undefined : region?.doc,
      containerName: binder ? undefined : ownerName(tokens, roles, owner),
    });
  }
  return definitions;
};
const declarationDetail = (
  text: string,
  tokens: SourceToken[],
  token: SourceToken,
  region: Region | undefined,
  role: string,
) => {
  const fallback = `${roleLabel(role)} ${lastQualifiedSegment(token.text)}`;
  if (!region) return fallback;
  const end = tokens[region.headerEnd]?.offset ?? token.endOffset;
  const header = text
    .slice(region.startOffset, end)
    .replace(/\s+/g, " ")
    .trim();
  return header || fallback;
};
const smallestRegion = (
  regions: Region[],
  offset: number,
  kind: string | undefined = undefined,
) =>
  regions
    .filter(
      (region) =>
        (!kind || region.kind === kind) &&
        region.startOffset <= offset &&
        offset <= region.endOffset,
    )
    .sort((a, b) => a.endOffset - a.startOffset - (b.endOffset - b.startOffset))
    .at(0);
const enclosingOwner = (
  regions: Region[],
  region: Region | undefined,
  offset: number,
) =>
  smallestRegion(
    regions.filter(
      (candidate) => ownedKinds.has(candidate.kind) && candidate !== region,
    ),
    offset,
  );
const ownerName = (
  tokens: SourceToken[],
  roles: Map<number, TokenRole>,
  owner: Region | undefined,
) => {
  if (!owner) return undefined;
  for (let index = owner.startIndex + 1; index <= owner.headerEnd; index += 1) {
    const role = roles.get(index);
    if (role?.modifiers.includes("declaration") && !localRoles.has(role.type)) {
      return tokens[index].text;
    }
  }
  return undefined;
};
const findDefinition = (
  model: { definitions: Definition[] },
  token: SourceToken | undefined,
  offset = token?.offset,
) => {
  if (!token || token.kind !== "name" || offset === undefined) return undefined;
  const name = lastQualifiedSegment(token.text);
  return model.definitions
    .filter(
      (definition) =>
        definition.bareName === name &&
        definition.scopeStart <= offset &&
        offset <= definition.scopeEnd,
    )
    .sort((a, b) => {
      const aWidth = a.scopeEnd - a.scopeStart;
      const bWidth = b.scopeEnd - b.scopeStart;
      if (aWidth !== bWidth) return aWidth - bWidth;
      return (
        Math.abs(offset - a.token.offset) - Math.abs(offset - b.token.offset)
      );
    })
    .at(0);
};
const tokenAtPosition = (
  model: { tokens: SourceToken[] },
  position: Position,
) =>
  model.tokens.find(
    (token) =>
      token.line === position.line &&
      token.char <= position.character &&
      token.endChar > position.character,
  );
const tokenRange = (first: SourceToken, last = first): Range => ({
  start: { line: first.line, character: first.char },
  end: { line: last.endLine, character: last.endChar },
});
// a qualified name's range without its namespace.
const nameRange = (token: SourceToken): Range => {
  const split = token.text.indexOf("~");
  const delta = split < 0 ? 0 : split + 1;
  return {
    start: { line: token.line, character: token.char + delta },
    end: { line: token.endLine, character: token.endChar },
  };
};
export {
  analyzeDocument,
  findDefinition,
  nameRange,
  roleLabel,
  smallestRegion,
  tokenAtPosition,
  tokenRange,
};
export type { Definition, DocumentModel, Instance, Region };
