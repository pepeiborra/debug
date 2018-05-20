{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns    #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures  #-}

module DebugPP(main) where

import           Control.Monad
import           Data.List
import           Data.Yaml.Config
import           Instrument
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO

usage :: String -> String
usage progName = unlines [
  "Usage: ",
  progName ++ " [FILENAME] [SOURCE] [DEST]",
  "  Instrument Haskell module for debugging from SOURCE (derived from FILENAME) and write",
  "  standard Haskell to DEST.",
  "  If no FILENAME, use SOURCE as the original name.",
  "  If no DEST or if DEST is `-', write to standard output.",
  "  If no SOURCE or if SOURCE is `-', read standard input.",
  progName ++ " --defaults",
  "  Dump a well documented set of default config values to standard output."
  ]


readConfig :: IO Config
readConfig = do
  cwd <- getCurrentDirectory
  home <- getHomeDirectory
  system <- getXdgDirectory XdgConfig "debug-pp"
  from <- filterM doesFileExist $
        [d </> ".debug-pp.yaml" | d <- reverse (ancestors cwd)] ++
        [ system </> "config.yaml"
        , home </> ".debug-pp.yaml"]
  case from of
    [] -> return defaultConfig
    _  -> loadYamlSettings from [] ignoreEnv
  where
    ancestors = map joinPath . tail . inits . splitPath

defConfig :: String
defConfig = unlines
  ["# debug-pp configuration file"
  ,"# ==========================="
  ,""
  ,"# List of Haskell module names to exclude from instrumentation"
  ,"excluded: []"
  , ""
  , "# If true, use the Hoed backend for trace generation."
  , "useHoedBackend: false"
  , ""
  , "# If true then insert a call to debugRun in the main function."
  , "instrumentMain: true"
  , ""
  , "# When the Hoed backend is used, instruct the debug TH wrapper to insert Observable instances for types that derive Generic."
  , "generateObservableInstances: true"
  , ""
  , "# When the Hoed backend is used, instruct the debug TH wrapper to insert Generic instances for types that don't derive Generic."
  , "generateGenericInstances: false"
  , ""
  , "# If the hoed backend is used, insert the ExtendedDefaultRules pragma."
  , "enableExtendedDefaultingRules: true"
  , ""
  , ""
  , "# List of types excluded from instance generation"
  , "excludedFromInstanceGeneration: []"
  , ""
  , "# If true, print a line for every instrumented module."
  , "verbose: false"
  , ""
  ]

main :: IO ()
main = do
  args <- getArgs
  progName <- getProgName
  (orig, inp, out) <- case args of
    ["--defaults"] -> do
      putStrLn defConfig
      exitSuccess
    ["--help"] -> do
      putStrLn $ usage progName
      exitSuccess
    []     -> return ("input",Nothing,Nothing)
    [i]    -> return (i, Just i, Nothing)
    [i,o]  -> return (i, Just i, Just o)
    [orig,i,o] -> return (orig, Just i, Just o)
    _ -> do
      putStrLn $ usage progName
      error "Unrecognized set of command line arguments"
  hIn  <- maybe (return stdin)  (`openFile` ReadMode) inp
  hOut <- maybe (return stdout) (`openFile` WriteMode) out
  contents <- hGetContents hIn
  config@Config{..} <- readConfig
  hPutStr hOut $ instrument config contents
  unless (hOut == stdout) $ hClose hOut
  when verbose $
    putStrLn $ "[debug-pp] Instrumented " ++ orig

