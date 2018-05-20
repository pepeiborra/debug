
module Main(main) where

import qualified Hoed
import qualified Variables
import qualified PP
import System.IO

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    Variables.main
    PP.main
    Hoed.main
