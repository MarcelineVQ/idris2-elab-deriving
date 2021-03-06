module Main

import Data.Maybe
import Data.List
import Data.List1
import Data.Strings

import System
import System.Directory
import System.File
import System.Info
import System.Path

%default covering

------------------------------------------------------------------------
-- Test cases

basicTests : List String
basicTests
    = [
       "deceq" 
       ,"eq"
       ,"show"
       ]

------------------------------------------------------------------------
-- Options

||| Options for the test driver.
record Options where
  constructor MkOptions
  ||| Name of the idris2 executable
  idris2      : String
  ||| Should we only run some specific cases?
  onlyNames   : List String
  ||| Should we run the test suite interactively?
  interactive : Bool

usage : String
usage = "Usage: runtests <idris2 path> [--interactive] [--only [NAMES]]"

options : List String -> Maybe Options
options args = case args of
    (_ :: idris2 :: rest) => go rest (MkOptions idris2 [] False)
    _ => Nothing

  where
    go : List String -> Options -> Maybe Options
    go rest opts = case rest of
      []                      => pure opts
      ("--interactive" :: xs) => go xs (record { interactive = True } opts)
      ("--only" :: xs)        => pure $ record { onlyNames = xs } opts
      _ => Nothing

------------------------------------------------------------------------
-- Actual test runner

fail : String -> IO ()
fail err
    = do putStrLn err
         exitWith (ExitFailure 1)

-- on Windows, we just ignore backslashes and slashes when comparing,
-- similarity up to that is good enough. Leave errors that depend
-- on the confusion of slashes and backslashes to unix machines.
normalize : String -> String
normalize str =
    if isWindows
      then pack $ filter (\ch => ch /= '/' && ch /= '\\') (unpack str)
      else str

runTest : Options -> String -> IO Bool
runTest opts testPath
    = do changeDir testPath
         isSuccess <- runTest'
         changeDir "../.."
         pure isSuccess
    where
        getAnswer : IO Bool
        getAnswer = do
          str <- getLine
          case str of
            "y" => pure True
            "n" => pure False
            _   => do putStrLn "Invalid Answer."
                      getAnswer

        printExpectedVsOutput : String -> String -> IO ()
        printExpectedVsOutput exp out = do
          putStrLn "Expected:"
          printLn exp
          putStrLn "Given:"
          printLn out

        mayOverwrite : Maybe String -> String -> IO ()
        mayOverwrite mexp out = do
          the (IO ()) $ case mexp of
            Nothing => putStr $ unlines
              [ "Golden value missing. I computed the following result:"
              , out
              , "Accept new golden value? [yn]"
              ]
            Just exp => do
              putStrLn "Golden value differs from actual value."
              code <- system "git diff --no-index --exit-code --word-diff=color expected output"
              when (code < 0) $ printExpectedVsOutput exp out
              putStrLn "Accept actual value as new golden value? [yn]"
          b <- getAnswer
          when b $ do Right _ <- writeFile "expected" out
                          | Left err => print err
                      pure ()
        runTest' : IO Bool
        runTest'
            = do putStr $ testPath ++ ": "
                 system $ "sh ./run " ++ idris2 opts ++ " | tr -d '\\r' > output"
                 Right out <- readFile "output"
                     | Left err => do print err
                                      pure False
                 Right exp <- readFile "expected"
                     | Left FileNotFound => do
                         if interactive opts
                           then mayOverwrite Nothing out
                           else print FileNotFound
                         pure False
                     | Left err => do print err
                                      pure False
                 let result = normalize out == normalize exp
                 if result
                    then putStrLn "success"
                    else do
                      putStrLn "FAILURE"
                      if interactive opts
                         then mayOverwrite (Just exp) out
                         else printExpectedVsOutput exp out

                 pure result

filterTests : Options -> List String -> List String
filterTests opts = case onlyNames opts of
  [] => id
  xs => filter (\ name => any (`isInfixOf` name) xs)

export
main : IO ()
main
    = do args <- getArgs
         let (Just opts) = options args
              | _ => do print args
                        putStrLn usage
         let filteredTests =
              filterTests opts $ concat $
                 [ testPaths "basic" basicTests
                 ]
         testRes <- traverse (runTest opts) filteredTests
         let res = testRes
         putStrLn (show (length (filter id res)) ++ "/" ++ show (length res)
                       ++ " tests successful")
         if (any not res)
            then exitWith (ExitFailure 1)
            else exitWith ExitSuccess
    where
         testPaths : String -> List String -> List String
         testPaths dir tests = map (\test => dir ++ "/" ++ test) tests
