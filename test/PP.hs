{-# LANGUAGE ScopedTypeVariables #-}
module PP where

import Control.Monad
import Instrument
import System.Exit
import System.FilePath
import System.IO.Extra
import System.Process.Extra
import GHC.Stack

main :: IO ()
main = forM_ moduleBodies $ \b -> do
  let config = defaultConfig
  putStr "."
  valid <- doesCompile b
  when valid $ do
    let instrumented = instrument config b
    stillValid <- doesCompile instrumented
    unless stillValid $
      fail $ "The program:\n\n" ++ b ++ "\n\nis incorrectly instrumented as:\n\n" ++ instrumented

pragmas, imports, modules, blockComments, bodies :: [[String]]
pragmas = [ [], ["{-# LANGUAGE NoImplicitPrelude #-}"]]
imports = [ [], ["import System.IO"]]
modules =
  [ []
  , ["module Foo where"]
  , ["module Foo (where) where"]
  , ["module ("
    ,"  where "
    ,"  ) where"
    ]
  ]
blockComments =
  [[]
  ,["{- module Foo where -}"]
  ,["{- where -}"]
  ,["{-", "where -}"]
  ,["{- import Foo -}"]
  ,["{-", "import Foo -}"]
  ]

bodies =
  [["where_ = 1"
   ,""
   ,"main :: IO ()"
   ,"main = return ()"
   ]
  ,[]
  ]

moduleBodies :: [String]
moduleBodies = do
  p <- pragmas
  b1 <- blockComments
  m <- modules
  b2 <- blockComments
  i <- imports
  b3 <- blockComments
  b <- bodies
  return $ unlines $ concat [p, b1, m, b2, i, b3, b]

validModuleBodies :: IO [String]
validModuleBodies = filterM doesCompile moduleBodies

-- | Test that a module body compiles
doesCompile :: HasCallStack => String -> IO Bool
doesCompile moduleBody = withTempDir $ \d -> do
  let fp = d </> "test.hs"
  writeFile fp moduleBody
  let p = (proc "ghc" ["-v0", "-fno-code", fp]) {std_out = NoStream, std_err = NoStream}
  withCreateProcess p $ \_ _ _ pid -> do
    ex <- waitForProcess pid
    return (ex == ExitSuccess)

shouldCompile b = do
  res <- doesCompile b
  unless res $ fail b
