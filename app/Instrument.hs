{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns    #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-} -- GHC 8.0 doesn't know about COMPLETE pragmas
module Instrument where

import           Data.Aeson.Types
import           Data.Char
import           Data.List
import           Data.Maybe
import           GHC.Generics
import           Text.Printf

data Config = Config_
  { _excluded                            :: Maybe [String]
  , _instrumentMain                      :: Maybe Bool
  , _useHoedBackend                      :: Maybe Bool
  , _disablePartialTypeSignatureWarnings :: Maybe Bool
  , _enableExtendedDefaultingRules       :: Maybe Bool
  , _generateObservableInstances         :: Maybe Bool
  , _generateGenericInstances            :: Maybe Bool
  , _excludedFromInstanceGeneration      :: Maybe [String]
  , _verbose                             :: Maybe Bool
  } deriving (Generic, Show)

configJsonOptions :: Options
configJsonOptions = defaultOptions{fieldLabelModifier = tail}

instance FromJSON Config where parseJSON = genericParseJSON configJsonOptions
instance ToJSON Config where toJSON = genericToJSON configJsonOptions

{-# COMPLETE Config #-}
pattern Config { excluded
               , instrumentMain
               , useHoedBackend
               , disablePartialTypeSignatureWarnings
               , enableExtendedDefaultingRules
               , generateGenericInstances
               , generateObservableInstances
               , excludedFromInstanceGeneration
               , verbose
               } <-
  Config_
  { _excluded = (fromMaybe [] -> excluded)
  , _instrumentMain = (fromMaybe True -> instrumentMain)
  , _useHoedBackend = (fromMaybe False -> useHoedBackend)
  , _disablePartialTypeSignatureWarnings = (fromMaybe True -> disablePartialTypeSignatureWarnings)
  , _enableExtendedDefaultingRules = (fromMaybe True -> enableExtendedDefaultingRules)
  , _generateObservableInstances = (fromMaybe True -> generateObservableInstances)
  , _generateGenericInstances = (fromMaybe False -> generateGenericInstances)
  , _excludedFromInstanceGeneration = (fromMaybe [] -> excludedFromInstanceGeneration)
  , _verbose = (fromMaybe False -> verbose)
  }
  where Config a b c d e f g h i = Config_ (Just a) (Just b) (Just c) (Just d) (Just e) (Just f) (Just g) (Just h) (Just i)

defaultConfig :: Config
defaultConfig = Config_ Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing

instrument :: String -> Config -> String -> String
instrument filename Config {..} contents
  | name `elem` excluded =
    printf "{-# LINE 0 %s #-}\n" (show filename) ++ contents
  | otherwise = unlines [top', modules', body''', annotations']
  where
    (top, name, modules, body, bodyStartLine) = parseModule contents
    debugModule = "Debug" ++ if useHoedBackend then ".Hoed" else ""
    modules' = unlines $ modules ++
      ["import qualified " ++ debugModule ++ " as Debug"] ++
      ["import qualified GHC.Generics" | generateGenericInstances]
    top' =
      unlines $
      [ "{-# LANGUAGE TemplateHaskell #-}"
      , "{-# LANGUAGE PartialTypeSignatures #-}"
      , "{-# LANGUAGE ViewPatterns #-}"
      , "{-# LANGUAGE FlexibleContexts #-}"
      ] ++
      [ "{-# OPTIONS -Wno-partial-type-signatures #-}"
      | disablePartialTypeSignatureWarnings
      ] ++
      ["{-# LANGUAGE ExtendedDefaultRules #-}" | useHoedBackend && enableExtendedDefaultingRules] ++
      ["{-# LANGUAGE DeriveAnyClass #-}"       | useHoedBackend && (generateObservableInstances || generateGenericInstances)] ++
      ["{-# LANGUAGE DerivingStrategies #-}"   | useHoedBackend && (generateObservableInstances || generateGenericInstances)] ++
      ["{-# LANGUAGE DeriveGeneric #-}"        | useHoedBackend && generateGenericInstances] ++
      top
    (annotations, body') = partition (\l -> "{-# ANN" `isPrefixOf` l) body
    body'' =
      map
        (if instrumentMain
           then instrumentMainFunction
           else id)
        body'
    debugWrapper
      | useHoedBackend && (generateGenericInstances || generateObservableInstances) =
        printf
          "Debug.debug' Debug.Config{Debug.generateGenericInstances=%s,Debug.generateObservableInstances=%s, Debug.excludeFromInstanceGeneration=%s}"
          (show generateGenericInstances)
          (show generateObservableInstances)
          (show excludedFromInstanceGeneration)
      | otherwise =
        "Debug.debug"
    body''' = unlines $
      printf "{-# LINE %d %s #-}" bodyStartLine (show filename) :
      (debugWrapper ++ " [d|") :
      map indent (body'' ++ ["  |]"])
    -- Annotations contain names and because of this, they need to go in a follow-up TH splice
    annotations' = unlines $ "id [d| " : map indent annotations ++ ["  |]"]

instrumentMainFunction :: String -> String
instrumentMainFunction l
  | ('m':'a':'i':'n':rest) <- l
  , ('=':rest') <- dropWhile isSpace rest
  , not ("debugRun" `isPrefixOf` rest') = "main = Debug.debugRun $ " ++ rest'
  | otherwise = l

parseModule :: String -> ([String], String, [String], [String], Int)
parseModule contents = (map fst top, name, modules, body, bodyStartLine + length modules0)
  where
    contents' = annotateBlockComments (lines contents)
    moduleLine =
      findIndex (\(l,insideComment) -> not insideComment && isModuleLine l) contents'
    firstImportLine =
      findIndex (\(l, insideComment) -> not insideComment && isImportLine l) contents'
    lastPragmaLine =
      case takeWhile (\(_,(l, insideComment)) -> not insideComment && isPragmaLine l) (zip [(0::Int)..] contents') of
        [] -> Nothing
        xx -> Just $ fst $ last xx
    (top, rest) = splitAt bodyStartLine contents'
    bodyStartLine
      | Just l <- firstImportLine = l-1
      | Just m <- moduleLine
      , Just lastModuleLine <- findIndex ((\(l, insideComment) -> not insideComment && "where" `isSuffixOf` l)) (drop m contents')
      = m + lastModuleLine + 1
      | Just p <- lastPragmaLine  = p+1
      | otherwise = 0
    (reverse -> body0, reverse -> modules0) =
      break (\(l,insideComment) -> not insideComment && isImportLine l) (reverse rest)
    name
      | Just l <- moduleLine
      = takeWhile (\x -> not (isSpace x || x == '(')) $ drop 7 (fst $ contents' !! l)
      | otherwise
      = "Main"
    body = map fst $ dropWhile snd body0
    modules = map fst modules0 ++ map fst (takeWhile snd body0)

isModuleLine :: String -> Bool
isModuleLine l = "module " `isPrefixOf` l && all (\c -> isAlpha c || c `elem` " ().") l
isImportLine :: String -> Bool
isImportLine = ("import " `isPrefixOf`)
isPragmaLine :: String -> Bool
isPragmaLine = ("{-#" `isPrefixOf`)

indent :: String -> String
indent it@('#':_) = it
indent other      = "  " ++ other

-- Annotate every line with True if its inside the span of a block comment.
-- @
--   {- LANGUAGE foo -}     -- False
--   This is not inside {-  -- False
--   but this is -}         -- True
annotateBlockComments :: [String] -> [(String, Bool)]
annotateBlockComments = annotateBlockComments' False
annotateBlockComments' :: Bool -> [String] -> [(String, Bool)]
annotateBlockComments' _ [] = []
annotateBlockComments' False (l:rest) = (l,False) : annotateBlockComments' (startsBlockComment l) rest
annotateBlockComments' True  (l:rest) = (l,True) : annotateBlockComments' (not $ endsBlockComment l) rest

startsBlockComment :: String -> Bool
startsBlockComment line
    | Just l' <- dropUntilIncluding "{-" line = not $ endsBlockComment l'
    | otherwise = False

endsBlockComment :: String -> Bool
endsBlockComment line
    | Just l' <- dropUntilIncluding "-}" line = not $ startsBlockComment l'
    | otherwise = False

dropUntilIncluding :: Eq a => [a] -> [a] -> Maybe [a]
dropUntilIncluding needle haystack
  | [] <- haystack = Nothing
  | Just x <- stripPrefix needle haystack = Just x
  | x:rest <- haystack = (x:) <$> dropUntilIncluding needle rest
