-- | the canonical two-space tidier for the cli and editor. it parseth the
-- source first and refuseth what doth not parse. it shorteneth each redundant
-- η-expansion, `{a ^ a f}` to `f`, droppeth redundant parentheses, and
-- flatteneth a product's last item of bare slots into it. layout
-- then followeth only the tokens, their brackets, and the comments between
-- them: whitespace in the source never changeth the output, so each concrete
-- syntax tree hath one tidy form, and tidying is idempotent. `Shorten`
-- rewriteth the tokens, this module buildeth a document from the concrete
-- tree, and `Layout` layeth it out.
module Tung.Format (formatSource) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Char (isSpace)
import Data.List (dropWhileEnd, groupBy, mapAccumL, sort, sortOn)
import Data.Maybe (listToMaybe)
import Tung.Concrete (Leaf (..), NodeKind (..), Tree (..))
import Tung.Format.Layout (Doc (..), Out (..), Tag (..), layout, render)
import Tung.Format.Shorten (shorten)
import Tung.Source.Parse (parseProgram, sourceTree)
import Tung.Token hiding (Piece (..), PieceKind (..), Placement (..))
import Tung.Token qualified as T

formatSource :: String -> Either String String
formatSource written = do
  _ <- parseProgram written
  let source = shorten written
      (declarations, closing) = topLevel (sourceTree source)
      result = render (renderDeclarations (sortBrings declarations) closing)
      output = if all isSpace result then "" else dropWhileEnd (== '\n') result ++ "\n"
  -- layout only moveth whitespace and comments, so the tokens agree.
  after <- lexTokens output
  before <- lexTokens source
  if sort (map show after) == sort (map show before)
    then Right output
    else Left "the tidier changed the tokens; this is a compiler fault"

-- a token's own text with the comments before it and the one that endeth its
-- line, as the concrete tree attacheth them.
data Piece = Piece
  { pieceText :: String,
    pieceToken :: Maybe Token,
    pieceLeading :: [String],
    pieceTrailing :: Maybe String,
    -- zero-width tags around the text, which mark case rows for alignment.
    pieceBefore :: [Tag],
    pieceAfter :: [Tag]
  }

piece :: Leaf -> Piece
piece Leaf {..} = Piece (maybe "" T.pieceText leafPiece) (leafPiece >>= token) (comments leafLeading) (listToMaybe (comments leafTrailing)) [] []
  where
    token T.Piece {pieceKind = T.Lexeme lexeme} = Just lexeme
    token _ = Nothing
    comments pieces = [dropWhileEnd isSpace (T.pieceText comment) | comment@T.Piece {pieceKind = T.Comment _} <- pieces]

-- a bracket's inside is its items, each with the separator that endeth it:
-- the slots, rows, members, or declarations the parser marked, or else the
-- whole inside as one item.
data Node = Atom Piece | Bracket Piece Inside Piece

data Inside = Inside
  { insideItems :: [[Node]],
    -- the inside holdeth declarations, as a block or a class's members.
    insideDeclares :: Bool,
    -- the inside holdeth case rows.
    insideRows :: Bool
  }

-- top-level declarations, and the comments that close the file.
topLevel :: Tree -> ([[Node]], [String])
topLevel = \case
  TreeNode FileNode children -> ([nodes declaration | TreeNode DeclarationNode declaration <- children], [comment | TreeLeaf leaf@Leaf {leafPiece = Nothing} <- children, comment <- pieceLeading (piece leaf)])
  tree -> ([nodes [tree]], [])

nodes :: [Tree] -> [Node]
nodes = concatMap \case
  TreeLeaf leaf -> [Atom (piece leaf)]
  TreeNode BracketNode (TreeLeaf open : rest)
    | not (null rest), TreeLeaf close <- last rest -> [Bracket (piece open) (inside (init rest)) (piece close)]
  TreeNode _ children -> nodes children

inside :: [Tree] -> Inside
inside children
  | any marked children = Inside (concatMap expand groups) (any (kind DeclarationNode) children) (any (kind RowNode) children)
  | otherwise = Inside [nodes children | not (null children)] False False
  where
    -- each marked child, with the separators after it.
    groups = [(kind RowNode child, nodes group) | group@(child : _) <- groupBy (\_ next -> not (marked next)) children]
    expand (row, item) = if row then map tagRow (filter (not . null) (split item)) else [item]
    marked child = any (`kind` child) [DeclarationNode, ItemNode, RowNode]
    kind wanted = \case
      TreeNode found _ -> found == wanted
      _ -> False
    -- a row's `;` endeth one alternative and beginneth the next.
    split = \case
      [] -> []
      item ->
        let (alternative, rest) = break (atomIn [TSemicolon]) item
         in case rest of
              semicolon : after -> (alternative ++ [semicolon]) : split after
              [] -> [alternative]

-- a row's columns end at its pattern commas, and its patterns end before
-- `^` or `;`; the tags let alignment find them in the laid-out lines.
tagRow :: [Node] -> [Node]
tagRow item = case break (atomIn [TMapsTo]) item of
  (left@(_ : _), caret : right) -> start (columns (tagLast ResultStart left)) ++ caret : right
  _ -> case reverse item of
    semicolon : before@(_ : _) | atomIn [TSemicolon] semicolon -> start (columns (tagLast AlternativeEnd (reverse before))) ++ [semicolon]
    _ -> item
  where
    columns = map \node -> if atomIn [TComma] node then after ColumnEnd node else node
    start = \case
      Atom piece : rest -> Atom piece {pieceBefore = RowStart : pieceBefore piece} : rest
      Bracket open contents close : rest -> Bracket open {pieceBefore = RowStart : pieceBefore open} contents close : rest
      [] -> []
    tagLast tag nodes' = case reverse nodes' of
      final : before -> reverse before ++ [after tag final]
      [] -> []
    after tag = \case
      Atom piece -> Atom piece {pieceAfter = pieceAfter piece ++ [tag]}
      Bracket open contents close -> Bracket open contents close {pieceAfter = pieceAfter close ++ [tag]}

-- an atom that is one of these tokens.
atomIn :: [Token] -> Node -> Bool
atomIn tokens = \case
  Atom piece -> maybe False (`elem` tokens) (pieceToken piece)
  _ -> False

isBraceKeyword :: Token -> Bool
isBraceKeyword = \case
  TBraceKeyword _ -> True
  _ -> False

-- consecutive `bring` declarations are sorted by path.
sortBrings :: [[Node]] -> [[Node]]
sortBrings = \case
  [] -> []
  declarations@(first : _)
    | bringing first ->
        let (brings, rest) = span bringing declarations
         in sortOn bringKey brings ++ sortBrings rest
  declaration : rest -> declaration : sortBrings rest
  where
    bringKey = map pieceText . concatMap nodePieces

bringing :: [Node] -> Bool
bringing = \case
  node : _ -> atomIn [TImport] node
  _ -> False

nodePieces :: Node -> [Piece]
nodePieces = \case
  Atom piece -> [piece]
  Bracket open Inside {insideItems} close -> open : concatMap (concatMap nodePieces) insideItems ++ [close]

-- one blank line between declarations, none between `bring`s.
renderDeclarations :: [[Node]] -> [String] -> [Out]
renderDeclarations declarations closing =
  let rendered = [(bringing declaration, layout (declarationDoc declaration)) | declaration <- declarations]
      joined = concat (zipWith separator (Nothing : map (Just . fst) rendered) rendered)
      separator previous (isBring, text) = case previous of
        Nothing -> text
        Just wasBring -> map Out (if wasBring && isBring then "\n" else "\n\n") ++ text
      ending = if null closing then [] else map Out (if null rendered then "" else "\n\n") ++ layout (commentsDoc closing)
   in joined ++ ending

declarationDoc :: [Node] -> Doc
declarationDoc written =
  let (comments, nodes) = hoistLeading written
   in commentsDoc comments <> case (declaresBody nodes, reverse nodes) of
        (True, Bracket open inside close : before)
          | braceLike open ->
              sequenceDoc (reverse before) <> Text " " <> bracketDoc (if any (atomIn [TClass, TInstance]) nodes then MemberBody else DeclarationBody) open inside close
        _ -> itemDoc nodes
  where
    declaresBody = \case
      node : rest -> if atomIn [TExport] node then declaresBody rest else atomIn [TType, TClass, TInstance] node
      _ -> False

-- a brace that holdeth a type's constructors, a class's members, or a
-- bizen's members is a declaration body, and one after `match …` is a match
-- body: both are padded. a declaration body and a case block of more than one
-- row always break, and a blank line standeth between a class's or a bizen's
-- members.
data Context = Ordinary | DeclarationBody | MemberBody | MatchBody
  deriving (Eq)

-- an item is one slot, row, member, or argument of its bracket. a binding
-- `≔` or a row's `^` keepeth its left side and breaketh before the right one,
-- unless the right side openeth a block.
-- the comments before an item stand at the item's own indentation.
hoistLeading :: [Node] -> ([String], [Node])
hoistLeading = \case
  Atom piece : rest -> (pieceLeading piece, Atom piece {pieceLeading = []} : rest)
  Bracket open inside close : rest -> (pieceLeading open, Bracket open {pieceLeading = []} inside close : rest)
  [] -> ([], [])

itemDoc :: [Node] -> Doc
itemDoc written =
  let (comments, nodes) = hoistLeading written
   in commentsDoc comments <> itemBody nodes

itemBody :: [Node] -> Doc
itemBody nodes
  | Just binding <- bindingDoc nodes = binding
  | otherwise = arrowBody nodes

-- a `let`, `fast`, or `axiom` that doth not fit on one line putteth its `≔ body`
-- on a line of its own, two columns in, and its `: annotation` too when the
-- name and annotation do not fit together; a block after `≔` openeth on that
-- line. without `≔`, the annotation stayeth beside the name and wrappeth.
bindingDoc :: [Node] -> Maybe Doc
bindingDoc nodes = do
  let (keywords, afterKeywords) = span (atomIn [TExport, TLet, TFix, TAxiom]) nodes
  name : rest <- Just afterKeywords
  guard (any (atomIn [TLet, TFix, TAxiom]) keywords)
  let (annotation, body) = case rest of
        Atom colon : afterColon
          | pieceToken colon == Just TColon -> case splitAtToken TEquals afterColon of
              Just (written, sign, right) -> (Just (colon, written), Just (sign, right))
              Nothing -> (Just (colon, afterColon), Nothing)
        _ -> (Nothing, fmap (\(_, sign, right) -> (sign, right)) (splitAtToken TEquals rest))
      named = Group (sequenceDoc (keywords ++ [name]) <> foldMap (\(colon, written) -> Nest 2 (SoftLine <> pieceDoc colon <> Text " " <> sequenceDoc written)) annotation)
  -- a body that openeth a block standeth outside the group, so the binding
  -- need fit only up to the block's opening; the block decideth its own form.
  pure case body of
    Just (sign, right)
      | opensBlock right -> Group (named <> Nest 2 (Line <> pieceDoc sign)) <> Text " " <> sequenceDoc right
      | otherwise -> Group (named <> Nest 2 (Line <> pieceDoc sign <> (if null right then Nil else Text " " <> sequenceDoc right)))
    Nothing -> Group (sequenceDoc (keywords ++ [name]) <> foldMap (\(colon, written) -> pieceDoc colon <> Text " " <> sequenceDoc written) annotation)

-- a row's `^`, or a binding outside a declaration, keepeth its left side on
-- the line and breaketh before the right one unless that openeth a block.
arrowBody :: [Node] -> Doc
arrowBody nodes = case splitAtToken TEquals nodes <|> splitAtToken TMapsTo nodes of
  Just (left, sign, right) -> sequenceDoc left <> Text " " <> pieceDoc sign <> rightDoc right
  Nothing -> sequenceDoc nodes
  where
    rightDoc right
      | null right = Nil
      | opensBlock right = Text " " <> sequenceDoc right
      | otherwise = Group (Nest 2 (Line <> sequenceDoc right))

-- the first top-level occurrence of a token, outside a `match` head.
splitAtToken :: Token -> [Node] -> Maybe ([Node], Piece, [Node])
splitAtToken wanted nodes = case break (atomIn [wanted]) nodes of
  (before, Atom piece : after) -> Just (before, piece, after)
  _ -> Nothing

-- a right side that beginneth with a brace, a block of declarations, or a
-- `match` keepeth to the line of its sign.
opensBlock :: [Node] -> Bool
opensBlock = \case
  Bracket open inside _ : _ -> braceLike open || insideDeclares inside
  node : _ -> atomIn [TMatch] node
  _ -> False

braceLike :: Piece -> Bool
braceLike piece = maybe False (\token -> token == TLBrace || isBraceKeyword token) (pieceToken piece)

-- terms of one item: each space may break, filling lines, except after `:`
-- and `$`, and there is no space inside a name such as `x.field` or `@α`.
-- a term that doth not fit beginneth a continuation line, two columns in. a
-- `match` head and a brace opening a block stay on the line before them.
sequenceDoc :: [Node] -> Doc
sequenceDoc = mconcat . snd . mapAccumL joined (Nothing, False)
  where
    -- the state is the previous node, and whether a `match` head is open.
    joined (previous, matching) node =
      let term = nodeDoc (if matching then MatchBody else Ordinary) node
          stillMatching = case node of
            Atom piece -> matching || pieceToken piece == Just TMatch
            Bracket open _ _ -> matching && not (braceLike open)
       in ( (Just node, stillMatching),
            case previous of
              Nothing -> term
              Just earlier
                | glued (lastPiece earlier) (firstPiece node) -> term
                | matching || pieceToken (lastPiece earlier) `elem` [Just TColon, Just TDollar] || braceLike (firstPiece node) -> Text " " <> term
                | otherwise -> Group (Nest 2 (Line <> term))
          )

nodeDoc :: Context -> Node -> Doc
nodeDoc context = \case
  Atom piece -> pieceDoc piece
  Bracket open inside close -> bracketDoc context open inside close

glued :: Piece -> Piece -> Bool
glued left right =
  maybe False noSpaceAfter (pieceToken left) || maybe False noSpaceBefore (pieceToken right)
  where
    noSpaceAfter token = token `elem` [TLParen, TLBracket, TLBrace, TAt, TDot] || isBraceKeyword token
    noSpaceBefore token = token `elem` [TRParen, TRBracket, TRBrace, TComma, TSemicolon, TColon, TDot]

firstPiece, lastPiece :: Node -> Piece
firstPiece = \case
  Atom piece -> piece
  Bracket open _ _ -> open
lastPiece = \case
  Atom piece -> piece
  Bracket _ _ close -> close

bracketDoc :: Context -> Piece -> Inside -> Piece -> Doc
bracketDoc context open Inside {..} close
  | null insideItems = pieceDoc open <> pieceDoc close
  | open `has` TLBracket = pieceDoc open <> Nest 2 (fillItems insideItems) <> pieceDoc close
  | open `has` TLParen, insideDeclares = blockDoc False False
  | open `has` TLParen = pieceDoc open <> itemDoc (concat insideItems) <> pieceDoc close
  | maybe False isBraceKeyword (pieceToken open),
    first : rest <- insideItems =
      FromLine (Group (pieceDoc open <> itemDoc first <> Nest 2 (mconcat [Line <> itemDoc item | item <- rest]) <> SoftLine <> pieceDoc close))
  | otherwise = blockDoc (context /= Ordinary) ((context `elem` [DeclarationBody, MemberBody] && (several || insideDeclares)) || (insideRows && several))
  where
    has piece token = pieceToken piece == Just token
    several = length insideItems > 1
    blockDoc padded forced =
      let between = if context == MemberBody then BlankLine else Line
          inner = mconcat (zipWith (\index item -> (if index == (0 :: Int) then Nil else between) <> itemDoc item) [0 ..] insideItems)
          edge = if padded then Line else SoftLine
          body = pieceDoc open <> Nest 2 (edge <> inner) <> edge <> pieceDoc close
       in FromLine (if forced then Break body else Group body)

-- slots fill their line and wrap where they must.
fillItems :: [[Node]] -> Doc
fillItems = \case
  [] -> Nil
  first : rest -> itemDoc first <> mconcat [Group (Line <> itemDoc item) | item <- rest]

pieceDoc :: Piece -> Doc
pieceDoc Piece {..} =
  commentsDoc pieceLeading <> foldMap Marker pieceBefore <> Text pieceText <> foldMap Marker pieceAfter <> maybe Nil (\comment -> Text " " <> Comment comment <> HardLine) pieceTrailing

commentsDoc :: [String] -> Doc
commentsDoc comments = mconcat [HardLine <> Comment comment <> HardLine | comment <- comments]
