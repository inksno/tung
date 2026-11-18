-- the compiler library's modules form layers, and a module importeth only
-- from its own layer or an earlier one. a new module must be given a layer.
module Test.Layering (group) where

import Data.Char (isSpace)
import Data.List (intercalate, isPrefixOf, stripPrefix)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.FilePath (dropExtension, makeRelative, splitDirectories, takeExtension, (</>))
import Test.Harness (Test, expectEq)

group :: IO [Test]
group = do
  root <- sourceRoot
  files <- haskellFiles root
  modules <- traverse (\file -> (moduleName root file,) . imports <$> readFile file) files
  pure
    [ expectEq "every library module hath a layer" [] [name | (name, _) <- modules, Nothing <- [layer name]],
      expectEq "no library module importeth a later layer" [] [(name, imported) | (name, used) <- modules, imported <- used, layer imported > layer name]
    ]

-- shared foundations come first, then the core, the source front end, the
-- runner, and the clients that present them.
layer :: String -> Maybe Int
layer name
  | name `elem` ["Tung.Token", "Tung.Concrete", "Tung.Identity", "Tung.Name", "Tung.Primitive", "Tung.Web"] = Just 0
  | within "Tung.Core" = Just 1
  | within "Tung.Source" = Just 2
  | name == "Tung.Run" = Just 3
  | within "Tung.Format" || name `elem` ["Tung", "Tung.Highlight", "Tung.Project", "Tung.Library", "Tung.Diagnostic", "Tung.Editor", "Tung.Metadata"] = Just 4
  | otherwise = Nothing
  where
    within prefix = name == prefix || (prefix ++ ".") `isPrefixOf` name

-- the library modules a source importeth.
imports :: String -> [String]
imports source =
  [ takeWhile (\character -> not (isSpace character) && character /= '(') name
  | line <- lines source,
    Just rest <- [stripPrefix "import " line],
    let name = unqualified (dropWhile isSpace rest),
    "Tung" `isPrefixOf` name
  ]
  where
    unqualified text = maybe text (dropWhile isSpace) (stripPrefix "qualified " text)

-- tests may run from the package or the repository root.
sourceRoot :: IO FilePath
sourceRoot = do
  inPackage <- doesFileExist ("src" </> "Tung.hs")
  pure (if inPackage then "src" else "tongue" </> "src")

haskellFiles :: FilePath -> IO [FilePath]
haskellFiles directory = do
  entries <- map (directory </>) <$> listDirectory directory
  concat <$> traverse (\entry -> doesDirectoryExist entry >>= \nested -> if nested then haskellFiles entry else pure [entry | takeExtension entry == ".hs"]) entries

moduleName :: FilePath -> FilePath -> String
moduleName root = intercalate "." . splitDirectories . dropExtension . makeRelative root
