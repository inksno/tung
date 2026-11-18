-- | shortening rewriteth tokens before layout: η-expansions, redundant
-- parentheses, and nested products, until none applieth, as one may expose
-- another. each rewrite readeth the lexed pieces, so comments stay put.
module Tung.Format.Shorten (shorten) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Bifunctor (bimap)
import Data.List (nub)
import Data.Maybe (isJust, listToMaybe)
import Tung.Token hiding (Piece (..), PieceKind (..), Placement (..))
import Tung.Token qualified as T

shorten :: String -> String
shorten written = let once = shortenBrackets (shortenParens (shortenEta written)) in if once == written then written else shorten once

-- a lambda whose binders are its body's last arguments is η-expanded:
-- `{a₁, …, aₙ ^ a₁ f a₂ … aₙ}` is `f`, and `{b ^ m tweak b}` is `m tweak`,
-- parenthesised unless the lambda is a whole expression. its
-- binders are distinct bare names, the rest is names and literals that never
-- name a binder, and no comment standeth inside. an annotated binder keepeth
-- its expansion, as elaboration may need it. the tidier readeth no names,
-- so a binder may be a constructor; a one-row match on one then checketh only
-- when that constructor is its type's sole, nullary one, and the shortened
-- function agreeth with it on every input. a shortening may complete an
-- outer one, so it is repeated.
shortenEta :: String -> String
shortenEta = rewritePieces \before -> \case
  opening@T.Piece {T.pieceKind = T.Lexeme TLBrace} : rest
    | not (matchRows before),
      (inside, T.Piece {T.pieceKind = T.Lexeme TRBrace} : after) <- break closing rest,
      all spaceOrLexeme inside,
      Just kept <- reduced [(token, T.pieceText piece) | piece@T.Piece {T.pieceKind = T.Lexeme token} <- inside] ->
        let alone = wholeExpression before after
            text = case kept of
              [single] -> single
              _ | alone -> unwords kept
              _ -> "(" ++ unwords kept ++ ")"
         in Just (opening {T.pieceText = text} : after)
  _ -> Nothing
  where
    -- `match scrutinees {rows}`: its brace holdeth rows, not a function.
    matchRows = (== Just TMatch) . listToMaybe . dropWhile (`notElem` (TMatch : expressionStarts))
    closing = \case
      T.Piece {T.pieceKind = T.Lexeme token} -> token `elem` [TLBrace, TRBrace]
      _ -> False
    -- the written tokens that remain, or nothing when the lambda is needed.
    reduced written = do
      let tokens = map fst written
      (header, TMapsTo : body) <- Just (break (== TMapsTo) tokens)
      binders <- names header
      guard ("_" `notElem` binders && nub binders == binders)
      let bound = map TIdent binders
          count = length binders
          offset = length header + 1
          texts = map snd (drop offset written)
          free = all (`notElem` bound)
      case body of
        -- every argument is a binder: `a₁ f a₂ … aₙ` is `f`.
        first : function@(TIdent _) : others
          | first : others == bound, free [function] -> Just [texts !! 1]
        _
          | length body - count >= 2,
            drop (length body - count) body == bound,
            all atomic (take (length body - count) body),
            free (take (length body - count) body) ->
              Just (take (length body - count) texts)
        _ -> Nothing
    atomic = \case
      TIdent "_" -> False
      TKindStar -> False
      TSorry -> False
      token -> literalOrName token
    names = \case
      [TIdent name] -> Just [name]
      TIdent name : TComma : rest -> (name :) <$> names rest
      _ -> Nothing

-- parentheses are redundant where the parse cannot change: around one atom,
-- a name, literal, or bracketed group, unless a `:` or `.` followeth, so an
-- implicit argument is written `@{…}` or `@[…]`; and around a run of atoms
-- that is a whole expression. a comment inside keepeth them, and each becometh a space,
-- so no tokens join.
shortenParens :: String -> String
shortenParens = rewritePieces \before -> \case
  opening@T.Piece {T.pieceKind = T.Lexeme TLParen} : rest
    | (inside, closer@T.Piece {T.pieceKind = T.Lexeme TRParen} : after) <- matching rest,
      all spaceOrLexeme inside,
      Just items <- atoms (concatMap lexemes inside),
      redundant before after items ->
        Just (blanked opening : inside ++ blanked closer : after)
  _ -> Nothing
  where
    redundant before after = \case
      [_] -> listToMaybe (concatMap lexemes after) `notElem` [Just TColon, Just TDot]
      _ : _ : _ -> wholeExpression before after
      [] -> False
    -- the top-level items of a run, each an atom or a bracketed group. a
    -- stray closer is a top-level token that is neither.
    atoms tokens =
      let top = [token | (0, token) <- nested pure tokens]
       in top <$ guard (all (\token -> literalOrName token || opener token) top && length (filter opener tokens) == length (filter closer tokens))

-- a product whose last item is a product of bare slots is that product's
-- rest: `[a: α, [β, γ]]` is `[a: α, β, γ]`, and `[[ℕ, *]]` is `[ℕ, *]`. an
-- inner slot that is named or implicit keepeth the brackets, as flattening
-- would bind its name in a let's body or make a type's index a parameter. a
-- comment inside keepeth them, and each becometh a space.
shortenBrackets :: String -> String
shortenBrackets = rewritePieces \before -> \case
  opening@T.Piece {T.pieceKind = T.Lexeme TLBracket} : rest
    | listToMaybe before `elem` [Just TLBracket, Just TComma],
      (inside@(_ : _), closer : after) <- matching rest,
      all spaceOrLexeme inside,
      and [depth /= 0 || token `notElem` [TColon, TAt] | (depth, token) <- nested pure (concatMap lexemes inside)],
      listToMaybe (concatMap lexemes after) == Just TRBracket ->
        Just (blanked opening : inside ++ blanked closer : after)
  _ -> Nothing

-- the first rewrite that applieth to the pieces from some point on, given the
-- lexemes before that point, nearest first; repeated until none applieth.
rewritePieces :: ([Token] -> [T.Piece] -> Maybe [T.Piece]) -> String -> String
rewritePieces step source = maybe source (rewritePieces step . concatMap T.pieceText) (go [] (T.lexPieces source))
  where
    go _ [] = Nothing
    go before pieces@(first : rest) = step before pieces <|> ((first :) <$> go (lexemes first ++ before) rest)

-- a bracket that is dropped becometh a space, so no tokens join.
blanked :: T.Piece -> T.Piece
blanked piece = piece {T.pieceText = " ", T.pieceKind = T.Space}

-- the pieces before the bracket that closeth the outermost depth, and the rest.
matching :: [T.Piece] -> ([T.Piece], [T.Piece])
matching pieces = bimap (map snd) (map snd) (break (\(depth, piece) -> depth == 0 && any closer (lexemes piece)) (nested lexemes pieces))

-- each item with the bracket depth before it.
nested :: (a -> [Token]) -> [a] -> [(Int, a)]
nested tokens items = zip (scanl (\depth item -> depth + count opener item - count closer item) 0 items) items
  where
    count test = length . filter test . tokens

opener, closer :: Token -> Bool
opener = isJust . closingBracket
closer = isClosingBracket

-- a whole expression followeth one of these, or `yield`, and precedeth a
-- closing bracket, a separator, the next declaration, or the end.
expressionStarts :: [Token]
expressionStarts = [TLParen, TLBracket, TLBrace, TComma, TMapsTo, TEquals, TSemicolon]

wholeExpression :: [Token] -> [T.Piece] -> Bool
wholeExpression before after =
  maybe False (`elem` (TYield : expressionStarts)) (listToMaybe before)
    && maybe True (`elem` ends) (listToMaybe (concatMap lexemes after))
  where
    ends = [TRParen, TRBracket, TRBrace, TComma, TSemicolon, TLet, TFix, TExport, TType, TClass, TInstance, TAxiom, TImport, TYield]

lexemes :: T.Piece -> [Token]
lexemes = \case
  T.Piece {T.pieceKind = T.Lexeme token} -> [token]
  _ -> []

spaceOrLexeme :: T.Piece -> Bool
spaceOrLexeme = \case
  T.Piece {T.pieceKind = T.Space} -> True
  T.Piece {T.pieceKind = T.Lexeme _} -> True
  _ -> False

literalOrName :: Token -> Bool
literalOrName = \case
  TIdent _ -> True
  TNatural _ -> True
  TInteger _ -> True
  TFloat _ -> True
  TUnicode _ -> True
  TText _ -> True
  TKindStar -> True
  TSorry -> True
  _ -> False
