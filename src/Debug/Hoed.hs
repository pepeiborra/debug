{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP               #-}
{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports    #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE ViewPatterns      #-}

-- | An alternative backend for lazy debugging with call stacks built on top of the "Hoed" package.
--
--   Instrumentation is done via a TH wrapper, which requires the following extensions:
--
--  - 'TemplateHaskell'
--  - 'PartialTypeSignatures'
--  - 'ViewPatterns'
--  - 'ExtendedDefaultRules'
--  - 'FlexibleContexts'
--
--   Moreover, 'Observable' instances are needed for value inspection. The 'debug'' template haskell wrapper can automatically insert these for 'Generic' types.
--
-- > {-# LANGUAGE TemplateHaskell, ViewPatterns, PartialTypeSignatures, ExtendedDefaultRules #-}
-- > {-# OPTIONS_GHC -Wno-partial-type-signatures #-}
-- > module QuickSort(quicksort) where
-- > import Data.List
-- > import Debug.Hoed
-- >
-- > debug [d|
-- >    quicksort :: Ord a => [a] -> [a]
-- >    quicksort [] = []
-- >    quicksort (x:xs) = quicksort lt ++ [x] ++ quicksort gt
-- >        where (lt, gt) = partition (<= x) xs
-- >    |]
--
-- Now we can debug our expression under 'debugRun':
--
-- > $ ghci examples/QuickSortHoed.hs
-- > GHCi, version 8.2.1: http://www.haskell.org/ghc/  :? for help
-- > [1 of 1] Compiling QuickSortHoed    ( QuickSortHoed.hs, interpreted )
-- > Ok, 1 module loaded.
-- > *QuickSort> debugRun $ quicksort "haskell"
-- > "aehklls"
--
-- After our expression is evaluated a web browser is started displaying the recorded
-- information.
--
-- To debug an entire program, wrap the 'main' function below 'debugRun'.
module Debug.Hoed
  (
    debug
  , debug'
  , Config(..)
  , debugRun
    -- * Generate a trace
  , getDebugTrace
    -- * Trace commands
  , debugPrintTrace
  , debugJSONTrace
  , debugViewTrace
  , debugSaveTrace
    -- * Reexported from Hoed
  , Observable(..)
  , observe
  , HoedOptions(..)
  , defaultHoedOptions
  ) where

import           Control.Monad
import           Control.Monad.Intern
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Char
import           Data.Generics.Uniplate.Data
import           Data.Graph.Libgraph
import           Data.Hashable
import           Data.HashMap.Strict         (HashMap)
import qualified Data.HashMap.Strict         as HMS
import qualified Data.IntMap.Strict          as IntMap
import qualified Data.IntSet                 as IntSet
import qualified Data.Map.Strict             as Map
import qualified Data.HashSet                as Set
import           Data.List
import           Data.Maybe
import           Data.Monoid
import           Data.Text                   (Text, pack)
import qualified Data.Text                   as T
import qualified Data.Text.Lazy              as LT
import "Hoed"    Debug.Hoed
import           Debug.Hoed.Render           as Hoed -- (Exp, ExpF, pattern ExpFun, pattern ExpCon)
import           Debug.Util
import           Debug.DebugTrace            as D (CallData (..),
                                                   DebugTrace (..),
                                                   Function (..),
                                                   debugViewTrace,
                                                   debugPrintTrace,
                                                   debugJSONTrace,
                                                   debugViewTrace,
                                                   debugSaveTrace
                                                   )
import           GHC.Exts                    (IsList (..))
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax  as TH
import           System.Clock

{-# ANN module ("hlint: ignore Redundant bracket" :: String) #-}

-- | Runs the program collecting a debugging trace and then opens a web browser to inspect it.
--
--   @ main = debugRun $ do
--       ...
--   @
debugRun :: IO () -> IO ()
debugRun program = getDebugTrace defaultHoedOptions {prettyWidth = 160, verbose = Verbose} program >>= debugViewTrace

-- | Runs the program collecting a debugging trace
getDebugTrace :: HoedOptions -> IO () -> IO DebugTrace
getDebugTrace hoedOptions program = do
  HoedAnalysis{..} <- runO' hoedOptions program
  putStrLn "Please wait while the debug trace is constructed..."
  t <- getTime Monotonic
  let result = convert hoedCompTree hoedExps
      !lv    = length(variables result)
  t' <- getTime Monotonic
  let compTime :: Double = fromIntegral(toNanoSecs(diffTimeSpec t t')) * 1e-9
  putStrLn $ show (length $ functions result) ++ " functions"
  putStrLn $ show lv ++ " variables"
  putStrLn $ show (length $ D.calls result) ++ " calls"
  putStrLn $ "=== Debug Trace (" ++ show compTime ++ " seconds) ==="
  return result

data HoedFunctionKey = HoedFunctionKey
  { label   :: !(Hashed Text)
  , arity   :: !Int
  , clauses :: ![Hashed Text]
  }
  deriving (Eq)

instance Hashable HoedFunctionKey where
  hashWithSalt s HoedFunctionKey{..} =
    s `hashWithSalt` label
      `hashWithSalt` arity
      `hashWithSalt` clauses

type HoedCallKey = Int

data HoedCallDetails = HoedCallDetails
  { argValuesIdx
  , clauseValuesIdx :: [Id]
  , resultIdx :: Id
  , depends, parents :: ![HoedCallKey]
  } deriving (Eq, Generic)


---------------------------------------------------------------------------
-- Cached pred and succ relationships

data AnnotatedCompTree exp = AnnotatedCompTree
  { compTree          :: CompTreeOf exp
  , predsMap, succsMap:: HMS.HashMap (VertexOf exp) [VertexOf exp]
  }

getPreds :: (Eq exp, Hashable exp) => AnnotatedCompTree exp -> VertexOf exp -> [VertexOf exp]
getPreds act v = fromMaybe [] $ HMS.lookup v (predsMap act)

getSuccs :: (Eq exp, Hashable exp) => AnnotatedCompTree exp -> VertexOf exp -> [VertexOf exp]
getSuccs act v =  fromMaybe [] $ HMS.lookup v (succsMap act)

annotateCompTree :: (Eq exp, Hashable exp) => CompTreeOf exp -> AnnotatedCompTree exp
annotateCompTree compTree = AnnotatedCompTree{..}  where
  predsMap  = HMS.fromListWith (++) [ (t, [s]) | Arc s t _ <- arcs compTree]
  succsMap  = HMS.fromListWith (++) [ (s, [t]) | Arc s t _ <- arcs compTree]

---------------------------------------------------------------------------
hoedCallValues :: HoedCallDetails -> [Id]
hoedCallValues HoedCallDetails{..} = resultIdx : (argValuesIdx ++ clauseValuesIdx)

getRelatives :: (exp -> ExpF a) -> (VertexOf exp -> [VertexOf exp]) -> VertexOf exp -> [Int]
getRelatives view rel v =
      [ stmtIdentifier
        | Vertex{vertexStmt = CompStmt {stmtIdentifier, stmtExp = view -> ExpFun_{}}} <- rel v
      ] ++
      [ callKey
        | v'@Vertex{vertexStmt = CompStmt {stmtExp = view -> ExpCon_{}}} <- rel v
        , callKey <- getRelatives view rel v'
      ]

extractHoedCall
  :: AnnotatedCompTree (Interned ExpF, Id)
  -> VertexOf (Interned ExpF, Id)
  -> Maybe (Hashed HoedFunctionKey, HoedCallKey, HoedCallDetails)
extractHoedCall hoedCompTree v@Vertex {vertexStmt = c@CompStmt {stmtExp = fst -> ExpFun_{calls_ = [(args,res)]}, ..}} =
  Just
    ( hashed $ HoedFunctionKey (hashed stmtLabel) (length args) (map fst clauses)
    , stmtIdentifier
    , HoedCallDetails args (map snd clauses) res depends parents)
  where
    clauses =
      [ (hashed stmtLabel, id)
      | Vertex {vertexStmt = CompStmt {stmtLabel, stmtExp = (ExpCon_{}, id)}} <-
          getSuccs hoedCompTree v
      ]
    depends = snub $ getRelatives fst (getSuccs hoedCompTree) v
    parents = snub $ getRelatives fst (getPreds hoedCompTree) v

extractHoedCall _ _ = Nothing

-- | Convert a 'Hoed' trace to a 'debug' trace
convert :: InternedCompTree -> InternMaps ExpF -> DebugTrace
convert hoedCompTree hoedInternMaps = DebugTrace {..}
  where
    -- Ensure top level Exps are present in the intern map
    (hoedCompTree', hoedInternMaps') =
      runInternST (bitraverse ((traverse.traverse) (\exp ->(exp,) <$> internShallow exp)) pure hoedCompTree) hoedInternMaps

    -- Query for all function calls and associated details
    hoedFunctionCalls :: HashMap (Hashed HoedFunctionKey) [(HoedCallKey, HoedCallDetails)]
    hoedFunctionCalls =
      HMS.fromListWith (<>)
        [ (fnKey, [(callKey, callDetails)])
        | Just (fnKey, callKey, callDetails) <-
            map (extractHoedCall (annotateCompTree hoedCompTree')) (vertices hoedCompTree')
        ]

    sortedFunctionCalls =
      sortOn (\(unhashed -> x, _) -> (label x, arity x)) $ toList hoedFunctionCalls

    -- Hoed indexes of all top level expressions
    variableIndexes = foldMap (foldMap (IntSet.fromList . hoedCallValues . snd)) hoedFunctionCalls

    -- Mapping from Hoed exp indexes to Debug variable indexes
    reindex = flip (IntMap.findWithDefault (error "reindex")) (IntMap.fromList $ zip (IntSet.toList variableIndexes) [0..])

    -- Debug variables
    variables :: [Text]
    variables = lookupRenderedExp <$> IntSet.toList variableIndexes

    -- Mapping from Hoed exp indexes to Text
    lookupRenderedExp =
      let renderedMap = fmap (renderExp . fmap (flip (IntMap.findWithDefault "??") renderedMap)) (inflateMap hoedInternMaps')
      in flip (IntMap.findWithDefault (error "bug in Hoed: incomplete hoedExps")) (fmap LT.toStrict renderedMap)
    -- lookupRenderedExp x = hashed $ pack $ show @Hoed.Exp $ evalIntern (inflate x) hoedInternMaps'

    -- Mapping to Debug function indexes
    lookupFunctionIndex = flip (HMS.lookupDefault (error "bug in convert: lookupFunctionIndex")) (HMS.fromList (zip (map fst sortedFunctionCalls) [0 ..]))
    -- Mapping from Hoed Comp uniques to debug call indexes
    lookupCallIndex     = flip (IntMap.findWithDefault (error "bug in convert: lookupCallIndex")) (IntMap.fromList (zip (map fst callsTable) [0 ..]))

    (functions, concat -> callsTable) =
      unzip
      [ (Function{..}
        ,[( callId, CallData {..})
         | (callId, HoedCallDetails {..}) <- toList calls
         , let callVals =
                 map (second reindex) $
                 ("$result", resultIdx) :
                 zipWith (\i v -> ("$arg" <> pack (show i), v)) [(1::Int) ..] argValuesIdx ++
                 zip (map unhashed clauses) clauseValuesIdx
         , let callDepends = map lookupCallIndex depends
         , let callParents = map lookupCallIndex parents
         ])
      | (k@(unhashed -> HoedFunctionKey {..}), calls) <- sortedFunctionCalls
      , let callFunctionId = lookupFunctionIndex k
      , let funResult = "$result"
      , let funArguments = map (\i -> "$arg" <> pack(show i)) [1 .. arity] ++ map unhashed clauses
      -- HACK Expects a multiline label with the function name in the first line, and the code afterwards
      , let (funName,funSource) = T.break (=='\n') (unhashed label)
      ]

    calls = map snd callsTable


snub :: Ord a => [a] -> [a]
snub = map head . group . sort

----------------------------------------------------------------------------
-- Template Haskell

data Config = Config
  { generateGenericInstances      :: Bool      -- ^ Insert @deriving stock Generic@ on type declarations that don't already derive 'Generic'. Requires @DeriveGeneric@ and @DerivingStrategies@.
  , generateObservableInstances   :: Bool      -- ^ Insert @deriving anyclass Observable@ on type declarations that don't already derive 'Observable'. Requires @DeriveAnyClass@ and @DerivingStrategies@.
  , excludeFromInstanceGeneration :: [String]  -- ^ Exclude types from instance generation by name (unqualified).
  }

-- | A @TemplateHaskell@ wrapper to convert normal functions into traced functions.
debug :: Q [Dec] -> Q [Dec]
debug = debug' (Config False False [])

-- | A @TemplateHaskell@ wrapper to convert normal functions into traced functions
--   and optionally insert 'Observable' and 'Generic' instances.
debug' :: Config -> Q [Dec] -> Q [Dec]
debug' Config{..} q = do
  missing <-
    filterM
      (fmap not . isExtEnabled)
      ([ ViewPatterns
       , PartialTypeSignatures
       , ExtendedDefaultRules
       , FlexibleContexts
       ]
#if __GLASGOW_HASKELL__ >= 802
       ++
       [DeriveAnyClass | generateObservableInstances] ++
       [DerivingStrategies | generateObservableInstances] ++
       [DeriveGeneric | generateGenericInstances]
#endif
      )
  when (missing /= []) $
    error $
    "\ndebug [d| ... |] requires additional extensions:\n" ++
    "{-# LANGUAGE " ++ intercalate ", " (map show missing) ++ " #-}\n"
  decs <- q
  let askSig x =
        listToMaybe $
        mapMaybe
          (\case
             SigD y s
               | x == y -> Just s
             _ -> Nothing)
          decs
  let checkSig = maybe True (not . hasRankNTypes) . askSig
  let sourceNames =
        mapMaybe
          (\case
             FunD n _ -> Just n
             ValD (VarP n) _ _ -> Just n
             _ -> Nothing)
          decs
  names <-
    sequence [(n, ) <$> newName (mkDebugName (nameBase n)) | n <- sourceNames]
  let  -- HACK We embed the source code of the function in the label,
       --      which is then unpacked by 'convert'
      createLabel n dec = nameBase n ++ "\n" ++ prettyPrint dec

#if __GLASGOW_HASKELL__ >= 802
      excludedSet = Set.fromList excludeFromInstanceGeneration
      updateDerivs derivs
        | hasGenericInstance <- not $ null $ filterDerivingClausesByName ''Generic derivs
        = [ DerivClause (Just StockStrategy)    [ConT ''Generic]
          | not hasGenericInstance
          , generateGenericInstances
          ] ++
          [ DerivClause (Just AnyclassStrategy) [ConT ''Observable]
          | [] == filterDerivingClausesByName ''Observable derivs
          , hasGenericInstance || generateGenericInstances
          ] ++
          derivs
      filterDerivingClausesByName n' derivs =
        [ it | it@(DerivClause _ preds) <- derivs , ConT n <- preds , n == n']
#endif
  fmap concat $
    forM decs $ \dec ->
      case dec of
        ValD (VarP n) b clauses
          | checkSig n -> do
            let Just n' = lookup n names
                label = createLabel n dec
            newDecl <-
              funD n [clause [] (normalB [|observe (pack label) $(varE n')|]) []]
            let clauses' = transformBi adjustValD clauses
            return [newDecl, ValD (VarP n') b clauses']
        FunD n clauses
          | checkSig n -> do
            let Just n' = lookup n names
                label = createLabel n dec
            newDecl <-
              funD n [clause [] (normalB [|observe (pack label) $(varE n')|]) []]
            let clauses' = transformBi (adjustInnerSigD . adjustValD) clauses
            return [newDecl, FunD n' clauses']
        SigD n ty
          | Just n' <- lookup n names
          , not (hasRankNTypes ty) -> do
            let ty' = adjustTy ty
            ty'' <- renameForallTyVars ty'
            return [SigD n ty', SigD n' ty'']
#if __GLASGOW_HASKELL__ >= 802
        DataD cxt1 name tt k cons derivs
          | not $ Set.member (prettyPrint name) excludedSet
          -> return [DataD cxt1 name tt k cons $ updateDerivs derivs]
        NewtypeD cxt1 name tt k cons derivs
          | not $ Set.member (prettyPrint name) excludedSet
          -> return [NewtypeD cxt1 name tt k cons $ updateDerivs derivs]
#endif
        _ -> return [dec]


mkDebugName :: String -> String
mkDebugName n@(c:_)
  | isAlpha c || c == '_' = n ++ "_debug"
  | otherwise = n ++ "??"
mkDebugName [] = error "unreachable: impossible"

adjustInnerSigD :: Dec -> Dec
adjustInnerSigD (SigD n ty) = SigD n (adjustTy ty)
adjustInnerSigD other       = other

-- Add a wildcard for Observable a
adjustTy :: Type -> Type
adjustTy (ForallT vars ctxt typ) =
    ForallT vars (delete WildCardT ctxt ++ [WildCardT]) typ
adjustTy other = adjustTy $ ForallT [] [] other

-- Tyvar renaming is a work around for http://ghc.haskell.org/trac/ghc/ticket/14643
renameForallTyVars :: Type -> Q Type
renameForallTyVars (ForallT vars ctxt typ) = do
  let allVarNames = case vars of
                      []-> snub $ universeBi ctxt ++ universeBi typ
                      _  -> map getVarNameFromTyBndr vars
  vv <- Map.fromList <$> mapM (\v -> (v,) <$> newName (pprint v)) allVarNames
  let Just renamedCtxt = transformBiM (applyRenaming vv) ctxt
      Just renamedTyp  = transformBiM (applyRenaming vv) typ
      Just renamedVars = mapM (applyRenamingToTyBndr vv) vars
  return $
    ForallT renamedVars renamedCtxt renamedTyp

renameForallTyVars other = return other

applyRenaming :: Map.Map Name Name -> Type -> Maybe Type
applyRenaming nn (VarT n) = VarT <$> Map.lookup n nn
applyRenaming _ other     = return other

getVarNameFromTyBndr :: TyVarBndr -> Name
getVarNameFromTyBndr (PlainTV n)    = n
getVarNameFromTyBndr (KindedTV n _) = n

applyRenamingToTyBndr :: Map.Map Name Name -> TyVarBndr -> Maybe TyVarBndr
applyRenamingToTyBndr vv (PlainTV n)    = PlainTV <$> Map.lookup n vv
applyRenamingToTyBndr vv (KindedTV n k) = (`KindedTV` k) <$> Map.lookup n vv

adjustValD :: Dec -> Dec
adjustValD (ValD pat body decs) = ValD (transform adjustPat pat) (adjustBody body) decs
adjustValD other       = other

adjustPat :: Pat -> Pat
adjustPat (VarP x) = ViewP (VarE 'observe `AppE` (VarE 'pack `AppE` toLit x)) (VarP x)
adjustPat x        = x

adjustBody :: Body -> Body
adjustBody (GuardedB exps) = GuardedB $ map (first adjustGuard) exps
adjustBody other = other

adjustGuard :: Guard -> Guard
adjustGuard (PatG stmts) = PatG $ map adjustStmt stmts
adjustGuard other = other

adjustStmt :: Stmt -> Stmt
adjustStmt (BindS pat exp) = BindS (transform adjustPat pat) exp
adjustStmt (LetS decs) = LetS $ map adjustValD decs
adjustStmt (ParS stmts) = ParS $ map (map adjustStmt) stmts
adjustStmt other = other

toLit :: Name -> TH.Exp
toLit (Name (OccName x) _) = LitE $ StringL x

-------------------------------------------------------------------------------------------
--

newtype Verbatim = Verbatim String
instance Show Verbatim where showsPrec p (Verbatim s) = showParen (p>0) $ showString s
