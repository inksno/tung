{-# LANGUAGE OverloadedStrings #-}

-- runner effects beyond the console: files, arguments, environment, exit,
-- processes, tasks, and the web server, against a simulated world.
module Test.Host (group) where

import Data.List (isPrefixOf)
import Data.Map.Strict qualified as Map
import Test.Harness (Test, expectEq)
import Test.Support
import Tung.Source (SourceProgram)

group :: IO [Test]
group = do
  example <- exampleSource "host_effects.tung"
  library <- loadLibrary ["_foreign.tung", "effect/file.tung", "type/one.tung", "type/optional.tung", "type/and.tung", "type/or.tung"]
  pure (tests (compileWith library "dependent_host.tung") example)

tests :: (String -> Either String SourceProgram) -> String -> [Test]
tests compiled example =
  [ expectEq "the host example runneth every effect in order" (Right (Right 0, "saved\nno file absent.txt\nfrom a task\nung\n", Map.fromList [("note.txt", "saved")])) do
      (status, after) <- run example world
      pure (status, worldOutput after, worldFiles after),
    expectEq "an environment variable is an optional" (Right (Right 0, "hello\nabsent\n")) $
      output
        ( host
            ++ "let environment:[string, (string optional) effect] ≔ 'environment' foreign "
            ++ "let lookup:[string, 𝟙 effect] ≔ {name ^ (name environment) effect_bind {none ^ 'absent' line, value some ^ value line}} "
            ++ "let main:𝟙 effect ≔ ('GREETING' lookup) then ('OTHER' lookup) "
        )
        world {worldEnvironment = [("GREETING", "hello")]},
    expectEq "exit endeth the run with its status" (Right (Right 3, "before\n")) $
      fmap worldOutput <$> run (host ++ "let exit:[@a:*, ℕ, a effect] ≔ 'exit' foreign let main:𝟙 effect ≔ ('before' line) then (3 exit) ") world,
    expectEq "a failed task hath no outcome" (Right (Right 0, "no outcome\n")) $
      output (host ++ "let exit:[@a:*, ℕ, a effect] ≔ 'exit' foreign let main:𝟙 effect ≔ (3 exit) fork $ await ") world
  ]
  where
    host = unlines (takeWhile (not . isPrefixOf "let main:") (lines example))
    run source start = compiled source >>= runWorld start
    output source start = fmap worldOutput <$> run source start
