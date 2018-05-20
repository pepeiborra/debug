{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RecordWildCards #-}
module Util(equivalentTrace, sanityCheck) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Debug.DebugTrace
import Text.Printf

equivalentTrace :: DebugTrace -> DebugTrace -> Bool
equivalentTrace tr1 tr2 =
  Set.fromList (functions tr1)  == Set.fromList (functions tr2) &&
  Set.fromList (variables tr1)  == Set.fromList (variables tr2) &&
  Set.fromList (fleshCalls tr1) == Set.fromList (fleshCalls tr2)

data FleshedCallData = FleshedCallData
  { function :: Function
  , depends, parents :: Set FleshedCallData
  , vals :: Set (Text, Text)
  }
  deriving (Eq, Ord)

fleshCalls :: DebugTrace -> [FleshedCallData]
fleshCalls DebugTrace{..} = map fleshCall calls
  where
    result = map fleshCall calls
    sansStack call = call{depends = [], parents = []}
    fleshCall CallData{..} = FleshedCallData{..} where
      function = functions !! callFunctionId
      depends  = Set.fromList $ map (sansStack . (result !!)) callDepends
      parents  = Set.fromList $ map (sansStack . (result !!)) callParents
      vals     = Set.fromList [ (label, variables !! v) | (label,v) <- callVals ]

-- | Performs basic checks on a trace value.
--   In particular, it checks that all the references are valid.
--   Returns a list of errors.
sanityCheck :: DebugTrace -> [String]
sanityCheck DebugTrace{..} = concatMap (uncurry checkCall) (zip [(0::Int)..] calls)
  where
    funs = length functions
    vars = length variables
    callsL = length calls
    checkCall :: Int -> CallData -> [String]
    checkCall i CallData{..} =
      [ printf "Call %d contains an invalid reference to function %d" callFunctionId
      | callFunctionId >= funs ] ++
      [ printf "Call %d contains an invalid reference to call %d" i c
      | c <- callDepends ++ callParents
      , c >= callsL ] ++
      [ printf "Call %d contains an invalid reference to variable %d" i vi
      | (_, vi) <- callVals
      , vi >= vars ]
