{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Util(TraceDiff(..), diffTrace, isEqualDiffTrace, pprTraceDiff, equivalentTrace) where

import Data.Algorithm.Diff
import Data.List (sort)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Debug.DebugTrace

type TextDiff = []

data FunctionDiff = FunctionDiff
    {funDiffName :: Text
    ,funDiffSource :: [Diff Text]
    ,funDiffArguments :: [Diff Text] -- ^ Variables for the arguments to the function
    ,funDiffResult :: Diff Text -- ^ Variable for the result of the function
    }

data TraceDiff = TraceDiff
  { diffFunctions :: [Diff [Function]]
  , diffVariables :: [Diff [Text]]
  , diffCalls     :: [Diff [FleshedCallData]]
  }
  deriving Show

isEqualDiffTrace TraceDiff{..} =
  all isBoth diffFunctions && all isBoth diffVariables && all isBoth diffCalls
  where
    isBoth Both{} = True
    isBoth _ = False

diffTrace tr1 tr2 = TraceDiff
  (getGroupedDiff (sort $ functions tr1) (sort $ functions tr2))
  (getGroupedDiff (sort $ variables tr1) (sort $ variables tr2))
  (getGroupedDiff (sort $ fleshCalls tr1) (sort $ fleshCalls tr2))

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
  deriving (Eq, Ord, Show)

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


-----------------------------------------------------------------------------------------
-- Pretty printing diffs


instance Pretty Function where
  pretty = pretty . show

pprTraceDiff = renderLazy . renderTraceDiff

renderTraceDiff :: TraceDiff -> SimpleDocStream AnsiStyle
renderTraceDiff = layoutPretty defaultLayoutOptions . reAnnotate f . prettyTraceDiff
  where
    f FirstDiff  = color Blue
    f SecondDiff = color Red

prettyTraceDiff TraceDiff{..} =
  vcat
    [nest 4 ("Functions:" <> line <> vcat (map (prettyDiffWith (vcat . map pretty)) diffFunctions))
    ,nest 4 ("Variables:" <> line <> vcat (map (prettyDiffWith (vcat . map pretty)) diffVariables))
    ,nest 4 ("Calls:" <> line <> vcat (map (prettyDiffWith (vcat . map pretty)) diffCalls))
    ]

data DiffAnnotation = FirstDiff | SecondDiff

prettyDiffWith ppr (First  a) = annotate FirstDiff  $ ppr a
prettyDiffWith ppr (Second a) = annotate SecondDiff $ ppr a
prettyDiffWith ppr (Both a _) = ppr a

instance Pretty FleshedCallData where
  pretty FleshedCallData{..} = nest 4 $
    pretty (funName function) <+> encloseSep lparen rparen comma ( [ pretty n <+> " = " <+> pretty v | (n,v) <- Set.toList vals])
    <> line <> dependsSection
    <> line <> parentsSection
    where
      dependsSection
        | null depends = mempty
        | otherwise    = group ("* Depends:" <+> pretty(Set.toList depends))
      parentsSection
        | null parents = mempty
        | otherwise    = group ("* Parents:" <+> pretty(Set.toList parents))
