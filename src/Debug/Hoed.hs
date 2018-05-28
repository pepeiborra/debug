{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PartialTypeSignatures #-}
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
{-# LANGUAGE RecursiveDo       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS -Wall -Wno-name-shadowing #-}

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
  , Config(..), defaultConfig
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
  , runO
  ) where

import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Intern
import           Data.Bifunctor
import           Data.Char
import           Data.Generics.Uniplate.Data
import           Data.Graph.Libgraph
import           Data.Hashable
import qualified Data.HashMap.Strict         as HMS
import qualified Data.IntMap.Strict          as IntMap
import qualified Data.IntSet                 as IntSet
import qualified Data.Map.Strict             as Map
import qualified Data.HashSet                as Set
import           Data.List
import           Data.Maybe
import           Data.Semigroup
import           Data.Text                   (Text, pack)
import qualified Data.Text                   as T
import qualified Data.Text.Lazy              as LT
import qualified Data.Array                  as A
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
import           GHC.Exts                    (IsList (..), inline)
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax  as TH

{-# ANN module ("hlint: ignore Redundant bracket" :: String) #-}

-- | Runs the program collecting a debugging trace and then opens a web browser to inspect it.
--
--   @ main = debugRun $ do
--       ...
--   @
debugRun :: IO () -> IO ()
debugRun program = inline getDebugTrace defaultHoedOptions program >>= \x -> inline debugViewTrace x

-- | Runs the program collecting a debugging trace
getDebugTrace :: HoedOptions -> IO () -> IO DebugTrace
{-# INLINE getDebugTrace #-}
getDebugTrace hoedOptions program = do
  HoedAnalysis{..} <- runO' hoedOptions{verbose=Verbose} program
  putStrLn "Please wait while the debug trace is constructed..."
  convert hoedCompTree hoedExps

type HoedFunctionKey = Int
type HoedCallKey = Int
type Id = Int

data HoedFunctionDetails = HoedFunctionDetails
  { label   :: Text
  , hoedFunctionKey :: !HoedFunctionKey
  , arity   :: !Int
  , clauses :: [Text]
  }
  deriving Generic

instance NFData HoedFunctionDetails

instance Eq HoedFunctionDetails where
  a == b = hoedFunctionKey a == hoedFunctionKey b && arity a == arity b

instance Hashable HoedFunctionDetails where
  hashWithSalt s h = hashWithSalt s (hoedFunctionKey h)

data HoedCallDetails = HoedCallDetails
  { argValuesIdx
  , clauseValuesIdx :: [Key]
  , resultIdx :: Key
  , depends, parents :: [HoedCallKey]
  } deriving (Eq, Generic)

instance NFData HoedCallDetails

---------------------------------------------------------------------------
-- Cached pred and succ relationships

data AnnotatedCompTree exp = AnnotatedCompTree
  { compTree          :: CompTreeOf exp
  , getPreds, getSuccs:: VertexOf exp -> [VertexOf exp]
  }
  deriving Generic

instance NFData e => NFData (AnnotatedCompTree e)

data AnnotatedNode a = AnnotatedNode { annotatedNodePreds, annotatedNodeSuccs :: ![a] }

instance Semigroup (AnnotatedNode a) where
  {-# INLINE (<>) #-}
  x <> y = AnnotatedNode (annotatedNodePreds x <> annotatedNodePreds y) (annotatedNodeSuccs x <> annotatedNodeSuccs y)

instance Monoid (AnnotatedNode a) where
  mempty = AnnotatedNode [] []
  mappend = (<>)

annotateCompTree :: (exp ~ Interned ExpF) => CompTreeOf exp -> AnnotatedCompTree exp
annotateCompTree compTree = AnnotatedCompTree{..}  where
  getPreds  = annotatedNodePreds . flip (HMS.lookupDefault mempty) relMap
  getSuccs  = annotatedNodeSuccs . flip (HMS.lookupDefault mempty) relMap
  relMap    = HMS.fromListWith (<>) $ concat [ [ (s, AnnotatedNode [] [t]), (t, AnnotatedNode [s] []) ] | Arc s t _ <- arcs compTree]

---------------------------------------------------------------------------
hoedCallValues :: HoedCallDetails -> [Id]
hoedCallValues HoedCallDetails{..} = resultIdx : (argValuesIdx ++ clauseValuesIdx)

getConstantDepends :: Ord exp => AnnotatedCompTree exp -> (exp -> ExpF a) -> VertexOf exp -> [VertexOf exp]
getConstantDepends g view v =
  snub $ concat
      [ v' : getConstantDepends g view v'
        | v'@Vertex{vertexStmt = CompStmt {stmtExp = view -> ExpCon_{}}} <- getSuccs g v
        , all (\p -> p == v || v `notElem` getPreds g p) (getPreds g v')
      ]

getDepends :: Ord exp => AnnotatedCompTree exp -> (exp -> ExpF a) -> VertexOf exp -> [Int]
getDepends g view v =
      [ stmtIdentifier
        | Vertex{vertexStmt = CompStmt {stmtIdentifier, stmtExp = view -> ExpFun_{}}} <- getSuccs g v
      ] ++
      [ callKey | v' <- getConstantDepends g view v, callKey <- getDepends g view v' ]

getParents :: AnnotatedCompTree exp -> (exp -> ExpF a) -> VertexOf exp -> [Int]
getParents g view v
  | null funParents = constParents
  | otherwise = funParents
  where
    funParents =
      [ stmtIdentifier
        | Vertex{vertexStmt = CompStmt {stmtIdentifier, stmtExp = view -> ExpFun_{}}} <- getPreds g v
      ]
    constParents =
      [ callKey
        | v'@Vertex{vertexStmt = CompStmt {stmtExp = view -> ExpCon_{}}} <- getPreds g v
        , callKey <- getParents g view v'
      ]

{-# INLINE extractHoedCall #-}
extractHoedCall
  :: AnnotatedCompTree (Interned ExpF)
  -> VertexOf (Interned ExpF)
  -> Maybe (HoedFunctionDetails, HoedCallKey, HoedCallDetails)
extractHoedCall hoedCompTree v@Vertex {vertexStmt = CompStmt {stmtExp = internedShape -> ExpFun_{calls_ = [(args,res)]}, ..}} =
  Just
    ( HoedFunctionDetails stmtLabel stmtObservation (length args) (map fst clauses)
    , stmtIdentifier
    , HoedCallDetails args (map snd clauses) res depends parents)
  where
    clauses =
      -- HACK stmtLabel is expected to be a multiline label with the function name in the first line, and the source code afterwards
      [ (head $ T.lines stmtLabel, id)
      | Vertex {vertexStmt = CompStmt {stmtLabel, stmtExp = Interned id ExpCon_{}}} <- getConstantDepends hoedCompTree internedShape v
      ]
    depends = snub $ getDepends hoedCompTree internedShape v
    parents = snub $ getParents hoedCompTree internedShape v

extractHoedCall _ _ = Nothing

data ConvertState = ConvertState
  { seenFunctions :: !(Set.HashSet HoedFunctionDetails)
    -- ^ Set of seen functions
  , seenExps      :: !IntSet.IntSet
    -- ^ Set of seen Exp keys
  , seenCalls     :: !(IntMap.IntMap Int)
    -- ^ Mapping from Hoed CompStmt uniques to debug call indexes
  }
  deriving Generic

instance NFData ConvertState

instance Monoid ConvertState where
  mempty = ConvertState mempty mempty mempty
  mappend = (<>)

instance Semigroup ConvertState where
  {-# INLINE (<>) #-}
  ConvertState a b c <> ConvertState a' b' c' = ConvertState (a<>a') (b<>b') (c<>c')


-- | Convert a 'Hoed' trace to a 'debug' trace
{-# INLINE convert #-}
convert :: InternedCompTree -> InternMaps ExpF -> IO DebugTrace
convert hoedCompTree hoedInternMaps = do
  aTree <- profiled "aTree" $ annotateCompTree hoedCompTree

      -- We perform two passes to enable fusion on the second pass.
      -- The one pass solution relies on laziness to delay the computation of the indexes which hurts performance

      -- 1st pass to collect "seen" exps, calls and functions
  let {-# INLINE loop1 #-}
      loop1 ConvertState{..} n (fnKey, callId, hoedCallDetails) = {-# SCC "loop" #-}
            ConvertState{ seenFunctions = Set.insert fnKey seenFunctions
                        , seenCalls = IntMap.insert callId n seenCalls
                        , seenExps  = IntSet.fromList (hoedCallValues hoedCallDetails) `IntSet.union` seenExps
                        }
  ConvertState functionSet usedExps callsMapping <- profiled "convert pass 1" $
          foldl' (\st (n,x) -> loop1 st n x) mempty (zip [0..] $ catMaybes $ extractHoedCall aTree <$> vertices hoedCompTree)

      -- Mapping to Debug function indexes
  let lookupFunctionIndex = flip (HMS.lookupDefault (error "bug in convert: lookupFunctionIndex")) (HMS.fromList (zip (toList functionSet) [0 ..]))

      lookupCallIndex = flip (IntMap.findWithDefault (error "bug in convert: lookupCallIndex")) callsMapping
      -- Mapping from Hoed exp indexes to Text
      lookupRenderedExp =
        let renderedMap = fmap (renderExp . fmap (flip (IntMap.findWithDefault "??") renderedMap)) infMap
            infMap = fmap nubLambdaCalls $ inflateMap hoedInternMaps
            nubLambdaCalls it@ExpFun_{..} = it{calls_ = snub calls_}
            nubLambdaCalls x = x
        in flip (IntMap.findWithDefault (error "bug in Hoed: incomplete hoedExps")) (fmap LT.toStrict renderedMap)

      lookupArgName = (A.listArray (0,100) ["$arg" <> pack (show i) | i <- [(0::Int)..50]] A.!)
      -- Mapping from Hoed exp indexes to Debug variable indexes
      lookupExpIndex = flip (IntMap.findWithDefault (error "lookupExpIndex")) (IntMap.fromList $ zip (toList usedExps) [(0::Int)..])

      {-# INLINE loop #-}
      loop (fnKey, _, HoedCallDetails{..}) =
            let callExps = {-# SCC "callExps" #-}
                      ("$result", resultIdx) :
                      zipWith (\i v -> (lookupArgName i, v)) [(1::Int) ..] argValuesIdx ++
                      zip (clauses fnKey) clauseValuesIdx
                callFunctionId = {-# SCC "callFunctionId" #-} lookupFunctionIndex fnKey
                callDepends = {-# SCC "callDepends" #-} map lookupCallIndex depends
                callParents = {-# SCC "callParents" #-} map lookupCallIndex parents
                callVals    = {-# SCC "callVals" #-} map (second lookupExpIndex) callExps
            in CallData{..}

      -- 2nd pass to build the list of call datas
  calls <- profiled "convert pass 2" $ map loop $ mapMaybe (extractHoedCall aTree) (vertices hoedCompTree)

  functions <- profiled "functions" [ Function{..}
                  | k <- toList functionSet
                  , let HoedFunctionDetails{..} = k
                        funArguments = map lookupArgName [1 .. arity] ++ clauses
                        funResult    = "$result"
                        -- HACK Expects a multiline label with the function name in the first line, and the source code afterwards
                        (funName,funSource) = T.break (=='\n') (label)
                  ]
      -- Debug variables
  variables <- profiled "variables" $ lookupRenderedExp <$> toList usedExps

  return DebugTrace {..}

----------------------------------------------------------------------------
-- Template Haskell

data Config = Config
  { generateGenericInstances      :: Bool      -- ^ Insert @deriving stock Generic@ on type declarations that don't already derive 'Generic'. Requires @DeriveGeneric@ and @DerivingStrategies@.
  , generateObservableInstances   :: Bool      -- ^ Insert @deriving anyclass Observable@ on type declarations that don't already derive 'Observable'. Requires @DeriveAnyClass@ and @DerivingStrategies@.
  , excludeFromInstanceGeneration :: [String]  -- ^ Exclude types from instance generation by name (unqualified).
  , includeSourceCode             :: Bool      -- ^ Embed the source code in observation labels
  , dumpInstrumentedCode          :: Bool      -- ^ Dump to files *.hs.debug
  }

defaultConfig :: Config
defaultConfig = Config False False [] True False

-- | A @TemplateHaskell@ wrapper to convert normal functions into traced functions.
debug :: Q [Dec] -> Q [Dec]
debug = debug' defaultConfig

-- | A @TemplateHaskell@ wrapper to convert normal functions into traced functions
--   and optionally insert 'Observable' and 'Generic' instances.
debug' :: Config -> Q [Dec] -> Q [Dec]
debug' config@Config{..} q = do
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
  let sourceNames =
        mapMaybe
          (\case
             FunD n _ -> Just n
             ValD (VarP n) _ _ -> Just n
             _ -> Nothing)
          decs
  names <-
    sequence [(n, ) <$> newName (mkDebugName (nameBase n)) | n <- sourceNames]

  decs' <- fmap concat $ mapM (adjustDec askSig config names) decs

  when dumpInstrumentedCode $ do
    loc <- location
    runIO $ do
      let path = loc_filename loc ++ ".debug"
      writeFile path (unlines $ intersperse [] $ map prettyPrint decs')

  return decs'

adjustDec :: (Name -> Maybe Type) -> Config -> [(Name, Name)] -> Dec -> Q [Dec]
adjustDec askSig Config{..} names = go where
  go dec = case dec of
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
#if __GLASGOW_HASKELL__ < 804
              ty'' <- renameForallTyVars ty'
#else
              let ty'' = ty'
#endif
              return [SigD n ty', SigD n' ty'']
            | otherwise -> return [SigD n (adjustTy ty)]
#if __GLASGOW_HASKELL__ >= 802
          DataD cxt1 name tt k cons derivs
            | not $ Set.member (prettyPrint name) excludedSet
            -> return [DataD cxt1 name tt k cons $ updateDerivs derivs]
          NewtypeD cxt1 name tt k cons derivs
            | not $ Set.member (prettyPrint name) excludedSet
            -> return [NewtypeD cxt1 name tt k cons $ updateDerivs derivs]
#endif
          _ -> return [dec]

  excludedSet = Set.fromList excludeFromInstanceGeneration

    -- HACK We embed the source code of the function in the label,
    --      which is then unpacked by 'convert'
  createLabel n dec
    | includeSourceCode = nameBase n ++ "\n" ++ prettyPrint dec
    | otherwise = nameBase n
  checkSig = maybe True (not . hasRankNTypes) . askSig
#if __GLASGOW_HASKELL__ >= 802
  updateDerivs derivs
    | hasGenericInstance <- not $ null $ filterDerivingClausesByName ''Generic derivs
    = [ DerivClause (Just StockStrategy)    [ConT ''Generic]
      | not hasGenericInstance
      , generateGenericInstances
      ] ++
      [ DerivClause (Just AnyclassStrategy) [ConT ''Observable]
      | [] == filterDerivingClausesByName ''Observable derivs
      , hasGenericInstance || generateGenericInstances
      , generateObservableInstances
      ] ++
      derivs
  filterDerivingClausesByName n' derivs =
    [ it | it@(DerivClause _ preds) <- derivs , ConT n <- preds , n == n']
#endif

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
adjustTy ty@(ForallT vars ctxt typ)
  | not $ null [ () | AppT (ConT n) _ <- ctxt, n == ''Observable]
  = ty -- Avoid inserting wildcards on types that already have Observable constraints
       -- partial type signatures do not support polymorphic recursion
       -- so this is designed as a workaround
  | otherwise =
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

snub :: (Eq a, Ord a) => [a] -> [a]
snub = map head . group . sort

profiled :: NFData a => String -> a -> IO a
profiled _ = return

{-
profiled msg a = do
  (t, res) <- timed (evaluate $ force a)
  printf "%s: %.2f seconds\n" msg t
  return res
timed :: IO b -> IO (Double, b)
timed act = do
  t0 <- getTime Monotonic
  res <- act
  t1 <- getTime Monotonic
  return (duration t0 t1, res)
duration :: TimeSpec -> TimeSpec -> Double
duration t t' = fromIntegral(toNanoSecs(diffTimeSpec t t')) * 1e-9 :: Double
--}
