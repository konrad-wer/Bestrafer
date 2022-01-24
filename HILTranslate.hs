{-# LANGUAGE ViewPatterns #-}

module HILTranslate (translateProgramToHIL) where

import AST
import HIL
import CommonUtils
import HILTranslateUtils
import Control.Lens
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set

translateProgramToHIL :: Program p -> ConstructorsContext -> HILProgram
translateProgramToHIL prog constrs =
  let prefixedProg = prefixSourceVariables <$> prog in
  let ca = Map.map (length . constrArgsTemplates) constrs in
  flip evalState TranslateState {_constrArities = ca, _freshVarNum = 0} $
    mapM (translateExpr 0 Set.empty Map.empty (getGlobalNames prefixedProg)) prefixedProg

translateExpr :: Int -> Set.Set CapturedVar -> TranslateContext -> Set.Set Var -> Expr p -> State TranslateState HILExpr
translateExpr _ _ _ _ EUnit {} = return HILUnit
translateExpr _ _ c globalVars (EVar _ x) =
  case x `Map.lookup` c of
    Just (Captured x') -> return $ HILClosureVar x'
    Just Self -> return HILSelfRef
    Nothing -> if x `Set.member` globalVars then
       return $ HILGlobalVar x
      else
       return $ HILVar x
translateExpr _ _ _ _ (EBool _ v) = return $ HILBool v
translateExpr _ _ _ _ (EInt _ v) = return $ HILInt v
translateExpr _ _ _ _ (EFloat _ v) = return $ HILFloat v
translateExpr _ _ _ _ (EChar _ v) = return $ HILChar v
translateExpr _ _ _ _ (EString _ v) = return $ HILString v
translateExpr n capturedVars c globalVars (ELambda _ x e) =
  let (c', n', newCaptures) = Set.foldl processCapture (c, n, Set.empty) capturedVars in
  HILClosure x (Set.filter (\y -> not (isWeak y){-} && unpackCapturedVar y /= x -}) capturedVars) <$>
                translateExpr n' (Set.insert (Strong x) (Weak x `Set.delete` newCaptures))
                (Map.delete x c') (x `Set.delete` globalVars) e
  where
    processCapture (c_, n_, newCaptures) (Weak v) = (Map.insert v Self c_, n_, Set.insert (SelfCapture v) newCaptures)
    processCapture (c_, n_, newCaptures) (Strong v) = (Map.insert v (Captured n_) c_, n_ + 1, newCaptures)
    processCapture (c_, n_, newCaptures) (SelfCapture v) = (Map.insert v (Captured n_) c_, n_ + 1, newCaptures)
    isWeak (Weak _) = True
    isWeak _ = False
translateExpr n capturedVars c globalVars (ESpine _ fun args) =
  HILSpine <$> translateExpr n capturedVars c globalVars fun <*> mapM (translateExpr n capturedVars c globalVars) args
translateExpr n capturedVars c globalVars (EDef _ x e) = HILDef x <$> translateExpr n capturedVars c globalVars e
translateExpr n capturedVars c globalVars (ELet    _ x e1 e2) = do
  x' <- uniquifyVariable x
  let e2' = alfaConvert x x' e2
  let capturedVars' = Strong x `Set.delete` (Weak x `Set.delete` capturedVars)
  HILLet x' <$> translateExpr n capturedVars c globalVars e1 <*>
                translateExpr n (Strong x' `Set.insert` capturedVars') (Map.delete x c) (x `Set.delete` globalVars) e2'
translateExpr n capturedVars c globalVars (ERec    _ _ x e1 e2) = do
  x' <- uniquifyVariable x
  let e1' = alfaConvert x x' e1
  let e2' = alfaConvert x x' e2
  let capturedVars' = Strong x `Set.delete` (Weak x `Set.delete` capturedVars)
  HILRec x' <$> translateExpr n (Weak x' `Set.insert` capturedVars') (Map.delete x c) (x `Set.delete` globalVars) e1' <*>
                translateExpr n (Strong x' `Set.insert` capturedVars') (Map.delete x c) (x `Set.delete` globalVars) e2'
translateExpr n capturedVars c globalVars (EAnnot  _ e _) = translateExpr n capturedVars c globalVars e
translateExpr n capturedVars c globalVars (ETuple  _ es _) = HILTuple <$> mapM (translateExpr n capturedVars c globalVars) es
translateExpr n capturedVars c globalVars (EConstr p name es) = do
  ca <- view constrArities <$> get
  if ca Map.! name == length es then
    HILConstr name <$> mapM (translateExpr n capturedVars c globalVars) es
  else do
    freshNum <- view freshVarNum <$> get
    modify $ over freshVarNum (+ (ca Map.! name - length es))
    let vars = ("g_" ++) . show .  (+ freshNum) <$> [0 .. ca Map.! name - length es - 1]
    let f = foldr (ELambda p) (EConstr p name (es ++ map (EVar p) vars)) vars
    translateExpr n capturedVars c globalVars f
translateExpr n capturedVars c globalVars (ECase   _ es bs) = do
  es' <- mapM (translateExpr n capturedVars c globalVars) es
  vs <- mapM (const freshVar) es
  bs' <- HILPatternExpr <$> translateBranches n (Set.fromList (Strong <$> vs) `Set.union` capturedVars) c globalVars (HILInspectVar <$> vs) bs
  return $ foldr (uncurry HILLet) bs' $ zip vs es'
translateExpr n capturedVars c globalVars (EIf     _ e1 e2 e3) =
  HILIf <$> translateExpr n capturedVars c globalVars e1 <*>
            translateExpr n capturedVars c globalVars e2 <*>  translateExpr n capturedVars c globalVars e3
translateExpr n capturedVars c globalVars (EBinOp  _ binOp e1 e2) =
  HILBinOp binOp <$> translateExpr n capturedVars c globalVars e1 <*>  translateExpr n capturedVars c globalVars e2
translateExpr n capturedVars c globalVars (EUnOp   _ unOp e) =
  HILUnOp unOp <$> translateExpr n capturedVars c globalVars e
translateExpr n capturedVars c globalVars (ETry    _ e catches) =
  HILTry <$> translateExpr n capturedVars c globalVars e <*> mapM (translateCatch n capturedVars c globalVars) catches
translateExpr n capturedVars c globalVars (EError  _ e) = HILError <$> translateExpr n capturedVars c globalVars e

data PatternKind p
  = AllVars [(Maybe Var, Branch p)]
  | AllConstructors [Branch p]
  | VarsFirstSplit [(Maybe Var, Branch p)] [Branch p]
  | ConstructorsFirstSplit [Branch p] [Branch p]

classifyPatternKinds :: [Branch p] -> PatternKind p
classifyPatternKinds bs = case bs of
  ((PWild _ : ptrns@_, e, p) : branches) -> startsWithVar [(Nothing, (ptrns, e, p))] branches
  ((PVar _ v : ptrns@_, e, p) : branches) -> startsWithVar [(Just v, (ptrns, e, p))] branches
  (branch@_ : ps) -> startsWithConstr [branch] ps
  _ -> undefined
  where
    startsWithVar :: [(Maybe Var, Branch p)] -> [Branch p] -> PatternKind p
    startsWithVar acc [] = AllVars $ reverse acc
    startsWithVar acc ((PVar _ v : ptrns@_, e, p) : branches)  = startsWithVar ((Just v, (ptrns, e, p)) : acc) branches
    startsWithVar acc ((PWild _ : ptrns@_, e, p) : branches)  = startsWithVar ((Nothing, (ptrns, e, p)) : acc) branches
    startsWithVar acc ps = VarsFirstSplit (reverse acc) ps

    startsWithConstr :: [Branch p] -> [Branch p] -> PatternKind p
    startsWithConstr acc [] = AllConstructors $ reverse acc
    startsWithConstr acc branches@((PVar {} : _, _, _) : _)  =  ConstructorsFirstSplit (reverse acc) branches
    startsWithConstr acc branches@((PWild _ : _, _, _) : _)  = ConstructorsFirstSplit (reverse acc) branches
    startsWithConstr acc (branch@_ : ps) = startsWithConstr (branch:acc) ps

data PatternClassifier
  = PCTuple Int
  | PCUnit
  | PCBool   Bool
  | PCInt    Integer
  | PCFloat  Double
  | PCChar   Char
  | PCString String
  | PCConstr String Int deriving (Eq, Ord)

groupByConstr :: [Branch p] -> [(PatternClassifier, [Branch p])]
groupByConstr branches = aux branches Map.empty
  where
    aux :: [Branch p] ->  Map.Map PatternClassifier [Branch p] -> [(PatternClassifier, [Branch p])]
    aux [] acc = Map.toAscList $ Map.map reverse acc
    aux ((ptrns@(ptrn : _), e, p) : bs) acc = aux bs $ Map.alter (insertToBucket (ptrns, e, p)) (getPatternClassifier ptrn) acc
    aux _ _ = undefined

    insertToBucket :: a -> Maybe [a] -> Maybe [a]
    insertToBucket x Nothing = Just [x]
    insertToBucket x (Just xs) =  Just (x : xs)

    getPatternClassifier PVar {} = undefined
    getPatternClassifier PWild {} = undefined
    getPatternClassifier (PTuple _ _ n) = PCTuple n
    getPatternClassifier PUnit {} = PCUnit
    getPatternClassifier (PBool   _ v) = PCBool v
    getPatternClassifier (PInt    _ v) = PCInt v
    getPatternClassifier (PFloat  _ v) = PCFloat v
    getPatternClassifier (PChar   _ v) = PCChar v
    getPatternClassifier (PString _ v) = PCString v
    getPatternClassifier (PConstr _ c ps) = PCConstr c $ length ps

translatePatternClassifier :: PatternClassifier -> HILPattern
translatePatternClassifier PCTuple {} = undefined
translatePatternClassifier PCUnit {} = undefined
translatePatternClassifier (PCBool   v) = HILPBool   v
translatePatternClassifier (PCInt    v) = HILPInt    v
translatePatternClassifier (PCFloat  v) = HILPFloat  v
translatePatternClassifier (PCChar   v) = HILPChar   v
translatePatternClassifier (PCString v) = HILPString v
translatePatternClassifier (PCConstr constr _) = HILPConstr constr

translateAllVarPatterns
  :: Int -> Set.Set CapturedVar -> TranslateContext -> Set.Set Var
  -> [HILInspectableExpr] -> [(Maybe Var, Branch p)] -> State TranslateState HILPatternExpr
translateAllVarPatterns n capturedVars c globalVars es branches = do
  v <- freshVar
  HILPtrnExprLet v (head es) <$>
    translateBranches n (Strong v `Set.insert` foldl removeCaptures capturedVars branches)
      c globalVars (tail es) (transformBranch v <$> branches)
  where
    transformBranch _ (Nothing, b) = b
    transformBranch y (Just x, b) = alfaConvertBranch x y b

    removeCaptures cv (Nothing, _) = cv
    removeCaptures cv (Just x, _) = Strong x `Set.delete` (Weak x `Set.delete` cv)

eliminatePattern :: Branch p -> Branch p
eliminatePattern (PVar {} : ps, e, p) = (ps, e, p)
eliminatePattern (PWild {} : ps, e, p) = (ps, e, p)
eliminatePattern (PUnit {} : ps, e, p) = (ps, e, p)
eliminatePattern (PTuple _ ptrns _ : ps, e, p) = (ptrns ++ ps, e, p)
eliminatePattern (PBool   {} : ps, e, p) = (ps, e, p)
eliminatePattern (PInt    {} : ps, e, p) = (ps, e, p)
eliminatePattern (PFloat  {} : ps, e, p) = (ps, e, p)
eliminatePattern (PChar   {} : ps, e, p) = (ps, e, p)
eliminatePattern (PString {} : ps, e, p) = (ps, e, p)
eliminatePattern (PConstr _ _ ptrns : ps, e, p) = (ptrns ++ ps, e, p)
eliminatePattern ([], _, _) = undefined

translateAllConstructorsPatterns
  :: Int -> Set.Set CapturedVar -> TranslateContext -> Set.Set Var
  -> [HILInspectableExpr] -> [Branch p] -> State TranslateState HILPatternExpr
translateAllConstructorsPatterns _ _ _ _ [] _ = undefined
translateAllConstructorsPatterns n capturedVars c globalVars (e : es) branches =
  case groupByConstr branches of
    [(PCTuple l, bs)] -> do
      e' <- freshVar
      HILPtrnExprLet e' e <$>
        translateBranches n capturedVars c globalVars (map (flip HILInspectElem e') [0 .. l - 1] ++ es) (map eliminatePattern bs)
    [(PCUnit, bs)] -> translateBranches n capturedVars c globalVars es $ map eliminatePattern bs
    ps@((PCConstr {}, _) : _) -> do
      e' <- freshVar
      HILPtrnExprLet e' e . HILCase e' <$> mapM (\p@(PCConstr _ l, _) -> traverseRight $
        cross translatePatternClassifier
        (translateBranches n capturedVars c globalVars (map (flip HILInspectElem e') [0 .. l - 1] ++ es) . map eliminatePattern) p) ps
    ps -> do
      e' <- freshVar
      HILPtrnExprLet e' e . HILCase e' <$>
       mapM (traverseRight . cross translatePatternClassifier (translateBranches n capturedVars c globalVars es . map eliminatePattern)) ps

   where
      traverseRight :: Monad m => (a, m b) -> m (a, b)
      traverseRight (l, r) = do
        r' <- r
        return (l, r')

translateBranches
  :: Int -> Set.Set CapturedVar -> TranslateContext -> Set.Set Var
  -> [HILInspectableExpr] -> [Branch p] -> State TranslateState HILPatternExpr
translateBranches n capturedVars c globalVars [] [([], e, _)] = HILMatchedExpr <$> translateExpr n capturedVars c globalVars e
translateBranches n capturedVars c globalVars es (classifyPatternKinds -> AllVars branches) =
  translateAllVarPatterns n capturedVars c globalVars es branches
translateBranches n capturedVars c globalVars es (classifyPatternKinds -> AllConstructors branches) =
  translateAllConstructorsPatterns n capturedVars c globalVars es branches
translateBranches n capturedVars c globalVars es (classifyPatternKinds -> VarsFirstSplit ptrns1 ptrns2) =
  HILCaseJoin <$> translateAllVarPatterns n capturedVars c globalVars es ptrns1 <*> translateBranches n capturedVars c globalVars es ptrns2
translateBranches n capturedVars c globalVars es (classifyPatternKinds -> ConstructorsFirstSplit ptrns1 ptrns2) =
  HILCaseJoin <$> translateAllConstructorsPatterns n capturedVars c globalVars es ptrns1 <*> translateBranches n capturedVars c globalVars es ptrns2
translateBranches _ _ _ _ _ _ = undefined

translateCatch :: Int -> Set.Set CapturedVar -> TranslateContext -> Set.Set Var -> Catch p -> State TranslateState HILCatch
translateCatch n capturedVars c globalVars (BestraferException _ exc Nothing, e) =
  (,) (HILBestraferException exc Nothing) <$> translateExpr n capturedVars c globalVars e
translateCatch n capturedVars c globalVars (BestraferException _ exc (Just v), e) =
  (,) (HILBestraferException exc (Just v)) <$> translateExpr n (Strong v `Set.insert` capturedVars) (Map.delete v c) (v `Set.delete` globalVars) e
