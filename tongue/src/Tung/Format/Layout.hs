-- | the tidier's layout: a document laid out to the line limit, and the
-- alignment of consecutive case rows in the laid-out lines.
module Tung.Format.Layout
  ( Doc (..),
    Tag (..),
    Out (..),
    layout,
    render,
  )
where

import Data.Char (isSpace)
import Data.List (dropWhileEnd, intercalate, isPrefixOf)
import Data.Maybe (fromMaybe, isJust, isNothing)

-- the widest line the tidier leaveth when the line can be broken.
lineLimit :: Int
lineLimit = 80

-- laid-out lines without trailing blanks, with consecutive case rows aligned.
render :: [Out] -> String
render = intercalate "\n" . alignRows . map (dropWhileEnd blank) . outLines

-- a document of the kind wadler and leijen describe. a comment endeth its
-- line with a hard line, which a group may hold and still lie flat;
-- consecutive line breaks merge into one.
data Doc
  = Nil
  | Text String
  | Comment String
  | Line
  | SoftLine
  | HardLine
  | -- a break that leaveth exactly one empty line.
    BlankLine
  | Nest Int Doc
  | Group Doc
  | Break Doc
  | -- a block: its inside is indented from the line it beginneth on, so it
    -- closeth at that line's indentation.
    FromLine Doc
  | Marker Tag
  | Doc :<> Doc

instance Semigroup Doc where
  (<>) = (:<>)

instance Monoid Doc where
  mempty = Nil

data Mode = Flat | Broken
  deriving (Eq)

-- laid-out text with the zero-width tags that mark case rows.
data Out = Out Char | Tag Tag

data Tag = RowStart | ColumnEnd | ResultStart | AlternativeEnd
  deriving (Eq)

blank :: Out -> Bool
blank = \case
  Out character -> isSpace character
  Tag _ -> True

outLines :: [Out] -> [[Out]]
outLines outs = case break (\case Out '\n' -> True; _ -> False) outs of
  (line, _ : rest) -> line : outLines rest
  (line, []) -> [line]

layout :: Doc -> [Out]
layout doc = dropWhileEnd blank (go 0 (Just 0) 0 [(0, Broken, doc)])
  where
    -- `pending` is the indentation awaited by a fresh line; consecutive
    -- breaks merge into one, so no break leaveth an empty line. `lineAt` is
    -- the indentation of the line being written.
    go :: Int -> Maybe Int -> Int -> [(Int, Mode, Doc)] -> [Out]
    go _ _ _ [] = []
    go column pending lineAt ((indent, mode, current) : rest) = case current of
      Nil -> go column pending lineAt rest
      Text "" -> go column pending lineAt rest
      Text text -> map Out (start ++ text) ++ go (here + length text) Nothing current' rest
      Comment comment ->
        let wrapped = wrapComment (lineLimit - here) comment
         in map Out (start ++ intercalate ("\n" ++ replicate here ' ') wrapped) ++ go (here + length (last wrapped)) Nothing current' rest
      Marker tag -> Tag tag : go column pending lineAt rest
      left :<> right -> go column pending lineAt ((indent, mode, left) : (indent, mode, right) : rest)
      Nest more inner -> go column pending lineAt ((indent + more, mode, inner) : rest)
      FromLine inner -> go column pending lineAt ((current', mode, inner) : rest)
      Line | mode == Flat -> if isNothing pending then Out ' ' : go (column + 1) Nothing lineAt rest else go column pending lineAt rest
      BlankLine | mode == Flat -> go column pending lineAt ((indent, mode, Line) : rest)
      BlankLine -> map Out (if isJust pending then "\n" else "\n\n") ++ go column (Just indent) lineAt rest
      SoftLine | mode == Flat -> go column pending lineAt rest
      Group inner
        | mode == Flat -> go column pending lineAt ((indent, Flat, inner) : rest)
        | fits (lineLimit - here) [(indent, Flat, inner)] rest -> go column pending lineAt ((indent, Flat, inner) : rest)
        | otherwise -> go column pending lineAt ((indent, Broken, inner) : rest)
      Break inner -> go column pending lineAt ((indent, Broken, inner) : rest)
      _ -> case pending of
        Just _ -> go column (Just indent) lineAt rest
        Nothing -> Out '\n' : go column (Just indent) lineAt rest
      where
        here = fromMaybe column pending
        start = maybe "" (`replicate` ' ') pending
        current' = fromMaybe lineAt pending
    fits width items rest
      | width < 0 = False
      | otherwise = case items of
          [] -> case rest of
            [] -> True
            next : others -> fits width [next] others
          (indent, mode, current) : others -> case current of
            Nil -> fits width others rest
            Text text -> fits (width - length text) others rest
            Comment comment -> fits (width - length comment) others rest
            Marker _ -> fits width others rest
            left :<> right -> fits width ((indent, mode, left) : (indent, mode, right) : others) rest
            Nest more inner -> fits width ((indent + more, mode, inner) : others) rest
            FromLine inner -> fits width ((indent, mode, inner) : others) rest
            Line | mode == Flat -> fits (width - 1) others rest
            BlankLine | mode == Flat -> fits (width - 1) others rest
            SoftLine | mode == Flat -> fits width others rest
            Group inner -> fits width ((indent, mode, inner) : others) rest
            Break inner -> fits width ((indent, Broken, inner) : others) rest
            -- what followeth a comment's line end must fit the next line.
            HardLine -> fits (lineLimit - indent) others rest
            _ -> True

-- a comment wider than its room breaketh at its last fitting space, keeping
-- its marker; a block comment is never broken.
wrapComment :: Int -> String -> [String]
wrapComment room comment
  | length comment <= room || "/*" `isPrefixOf` comment = [comment]
  | otherwise =
      let marker = if "##" `isPrefixOf` comment then "##" else "#"
          text = dropWhile isSpace (drop (length marker) comment)
          lead = marker ++ " "
          spaces = [index | (index, ' ') <- zip [0 ..] text, index > 0, length lead + index <= room]
       in case spaces of
            [] -> [comment]
            _ ->
              let position = last spaces
               in (lead ++ take position text) : wrapComment room (lead ++ dropWhile isSpace (drop position text))

-- consecutive case rows of one indentation with as many pattern columns
-- align: each column is padded after its comma, and `^` followeth the widest
-- last column. a `;` alternative is a row without a result. rows that would
-- grow wider than the limit are left unaligned.
data CaseRow = CaseRow
  { rowIndent :: String,
    rowColumns :: [String],
    rowResult :: Maybe String
  }

alignRows :: [[Out]] -> [String]
alignRows = \case
  [] -> []
  lines'@(line : rest)
    | Just row <- caseRow line ->
        let (group, remaining) = spanRows row lines'
            aligned = map (renderRow (widths group)) group
            original = map plain (take (length group) lines')
         in (if all ((<= lineLimit) . length) aligned then aligned else original) ++ alignRows remaining
    | otherwise -> plain line : alignRows rest
  where
    plain line = [character | Out character <- line]
    spanRows first = \case
      line : rest
        | Just row <- caseRow line,
          rowIndent row == rowIndent first,
          length (rowColumns row) == length (rowColumns first) ->
            let (group, remaining) = spanRows first rest in (row : group, remaining)
      remaining -> ([], remaining)
    widths group = foldr1 (zipWith max) [map length (rowColumns row) | row <- group]
    renderRow columnWidths CaseRow {..} =
      let padded = [column ++ "," ++ replicate (width - length column + 1) ' ' | (column, width) <- zip (init rowColumns) columnWidths]
          final = last rowColumns
       in rowIndent ++ concat padded ++ case rowResult of
            Just result -> final ++ replicate (last columnWidths - length final) ' ' ++ " ^" ++ (if null result then "" else ' ' : result)
            Nothing -> final ++ ";"

-- a line that holdeth one whole row from its start.
caseRow :: [Out] -> Maybe CaseRow
caseRow line = do
  let (lead, content) = span blank line
  (columns, ending) <- case [() | Tag RowStart <- lead] of
    [_] -> columnsOf [] content
    _ -> Nothing
  pure (CaseRow [character | Out character@' ' <- lead] columns ending)
  where
    text outs = trim [character | Out character <- outs]
    columnsOf done outs = case break (\case Tag tag -> tag `elem` [ColumnEnd, ResultStart, AlternativeEnd]; _ -> False) outs of
      (column, Tag ColumnEnd : rest) -> columnsOf (done ++ [dropWhileEnd (== ',') (text column)]) rest
      (column, Tag ResultStart : rest) -> Just (done ++ [text column], Just (trim (drop 1 (text rest))))
      (column, Tag AlternativeEnd : _) -> Just (done ++ [text column], Nothing)
      _ -> Nothing

trim :: String -> String
trim = dropWhile isSpace . dropWhileEnd isSpace
