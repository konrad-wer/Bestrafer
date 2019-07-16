module ASTBuilder (buildAST) where

import AST
import Control.Monad
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import CommonUtils
import Typechecker
import TypecheckerUtils

data ASTBuilderError p
  = ConstrFormednessError (ConstrDef p)
  | WrongConstrResultTypeError (ConstrDef p)
  | WrongConstrResultTypeParamsNumberError (ConstrDef p)
  | WrongConstrResultTypeParameter (ConstrDef p) String GADTParameterTemplate
  | GADTDuplicateParamError p String [GADTDefParameter]
  | MoreThanOneGADTDefinition String
  | ConstrFormednessTypeError (TypeError p)
  | TypeParamIsNotMonotypeError p GADTDefParameter GADTParameterTemplate
  | FunctionLacksAnnotationError p Var
  | FunctionLacksImplementationError p Var
  | MoreThanOneTypeAnnotationError p Var
  | FunDuplicateArgumentError p Var
  | FunDifferentNumberOfArgs p Var
  | InternalCompilerASTBuilderError p String
  deriving (Show)

operatorsTypeContext :: FunTypeContext
operatorsTypeContext = Map.fromList
  [
    ("!u", TArrow TBool TBool),
    ("+u", TArrow TInt TInt),
    ("-u", TArrow TInt TInt),
    ("+.u", TArrow TFloat TFloat),
    ("-.u", TArrow TFloat TFloat),
    ("+", TArrow TInt $ TArrow TInt TInt),
    ("-", TArrow TInt $ TArrow TInt TInt),
    ("*", TArrow TInt $ TArrow TInt TInt),
    ("/", TArrow TInt $ TArrow TInt TInt),
    ("%", TArrow TInt $ TArrow TInt TInt),
    ("+.", TArrow TFloat $ TArrow TFloat TFloat),
    ("-.", TArrow TFloat $ TArrow TFloat TFloat),
    ("*.", TArrow TFloat $ TArrow TFloat TFloat),
    ("/.", TArrow TFloat $ TArrow TFloat TFloat),
    ("&&", TArrow TBool $ TArrow TBool TBool),
    ("||", TArrow TBool $ TArrow TBool TBool),
    ("==", TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    ("!=", TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    ("<=", TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    (">=", TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    ("<", TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    (">", TUniversal (UTypeVar "a") KStar (TArrow (TUVar $ UTypeVar "a") $ TArrow (TUVar $ UTypeVar "a") TBool)),
    ("++", TUniversal (UTypeVar "a") KStar . TUniversal (UTypeVar "n1") KNat . TUniversal (UTypeVar "n2") KNat $
    TArrow (TGADT "Vec" [ParameterMonotype $ MUVar $ UTypeVar "n1", ParameterType $ TUVar $ UTypeVar "a"]) $ TArrow
    (TGADT "Vec" [ParameterMonotype $ MUVar $ UTypeVar "n1", ParameterType $ TUVar $ UTypeVar "a"])
    (TExistential (UTypeVar "m") KNat $ TGADT "Vec" [ParameterMonotype $ MUVar $ UTypeVar "m", ParameterType $ TUVar $ UTypeVar "a"])),
    (".", TUniversal (UTypeVar "a") KStar . TUniversal (UTypeVar "b") KStar . TUniversal (UTypeVar "c") KStar $
    TArrow (TArrow (TUVar $ UTypeVar "b") (TUVar $ UTypeVar "c")) $ TArrow (TArrow (TUVar $ UTypeVar "a") (TUVar $ UTypeVar "b"))
    (TArrow (TUVar $ UTypeVar "a") (TUVar $ UTypeVar "c"))),
    ("|>",  TUniversal (UTypeVar "a") KStar . TUniversal (UTypeVar "b") KStar . TArrow (TUVar $ UTypeVar "a") $
    TArrow (TArrow (TUVar $ UTypeVar "a") (TUVar $ UTypeVar "b")) (TUVar $ UTypeVar "b"))
  ]

vecGADTDef :: (String, [GADTDefParameter])
vecGADTDef = ("Vec", [GADTDefParamMonotype KNat, GADTDefParamType "`A"])

vecConstructorsContext :: ConstructorsContext
vecConstructorsContext = Map.fromList
  [
    ("[]", Constructor "Vec" ["`#0", "`A"] [] [(MTParam "`#0", MTMono MZero)] []),
    (":", Constructor "Vec" ["`#0", "`A"] [(UTypeVar "a", KNat)] [(MTParam "`#0", MTMono $ MSucc . MUVar $ UTypeVar "a")]
    [TTParam "`A", TTGADT "Vec" [ParameterMonotypeT . MUVar $ UTypeVar "a", ParameterTypeT $ TTParam "`A"]])
  ]

isBlockGADTDef :: ProgramBlock p -> Bool
isBlockGADTDef GADTDef {} = True
isBlockGADTDef _ = False

buildGADTContexts :: [ProgramBlock p] -> Either (ASTBuilderError p) (ConstructorsContext, GADTDefs)
buildGADTContexts blocks = do
  let gadtDefBlocks = filter isBlockGADTDef blocks
  iterM checkGADTDefParams gadtDefBlocks
  let gDefsList = map unpackNameAndParams gadtDefBlocks
  let gDefsNames = Set.fromList $ map fst gDefsList
  if Set.size gDefsNames /= length gDefsList then
    let countedNames = foldl (flip (Map.update (return . (+ 1)))) (Map.fromSet (const (0 :: Integer)) gDefsNames) $ map fst gDefsList in
    let duplicateName = fst . head . filter ((> 1) . snd) . Map.toList $ countedNames in
    Left $ MoreThanOneGADTDefinition duplicateName
  else do
    let gDefs = Map.fromList $ vecGADTDef : gDefsList
    contstrContext <- foldM (buildGADTDef gDefs) vecConstructorsContext gadtDefBlocks
    return (contstrContext, gDefs)
    where
      unpackNameAndParams (GADTDef _ name params _) = (name, params)
      unpackNameAndParams _ = ("", [])

checkGADTDefParams :: ProgramBlock p -> Either (ASTBuilderError p) ()
checkGADTDefParams (GADTDef p name params _) =
  let typeParams = filter isGADTDefParamType params in
  if (Set.size . Set.fromList $ typeParams) == length typeParams then
    return ()
  else
    Left $ GADTDuplicateParamError p name params
  where
    isGADTDefParamType GADTDefParamType {} = True
    isGADTDefParamType _ = False
checkGADTDefParams _ = return ()

buildGADTDef ::
  GADTDefs -> ConstructorsContext -> ProgramBlock p
  -> Either (ASTBuilderError p) ConstructorsContext
buildGADTDef gDefs cc (GADTDef _ name params constrDefs) = do
  constrs <- mapM (buildConstructor gDefs name params) constrDefs
  let constrNames = map constrDefName constrDefs
  return $ foldl (flip (uncurry Map.insert)) cc $ zip constrNames constrs
buildGADTDef _ cc _ = return cc

buildConstructor ::
  GADTDefs -> String -> [GADTDefParameter] -> ConstrDef p -> Either (ASTBuilderError p) Constructor
buildConstructor g typeName typeParams (ConstrDef p cname pt) = do
  checkTypeTemplateWellFormedness p [] g pt
  (uvars, props, args) <- buildForall pt ([], [] ,[])
  return $ Constructor typeName (buildTypeParmsTemplate typeParams (0 :: Integer)) uvars props args
  where
    buildForall (TTUniversal x k t) (uvars, props, args) = buildForall t ((x, k) : uvars, props, args)
    buildForall t (uvars, props, args) = buildArrow t (uvars, props, args)
    buildArrow (TTArrow arg t) (uvars, props, args) = buildArrow t (uvars, props, arg : args)
    buildArrow t (uvars, props, args) = buildRes t (uvars, props, args)
    buildRes (TTGADT name params) (uvars, _, args)
      | typeName /= name = Left $ WrongConstrResultTypeError (ConstrDef p cname pt)
      | length params /= length typeParams = Left $ WrongConstrResultTypeParamsNumberError (ConstrDef p cname pt)
      | otherwise = do
        props <- checkParamsPositionsAndBuildProps typeParams params [] (0 :: Integer)
        return (uvars, props, reverse args)
    buildRes _  _ = Left $ ConstrFormednessError (ConstrDef p cname pt)
    buildTypeParmsTemplate [] _ = []
    buildTypeParmsTemplate (GADTDefParamType name : ps) n = name : buildTypeParmsTemplate ps (n + 1)
    buildTypeParmsTemplate (GADTDefParamMonotype _ : ps) n = ("`#" ++ show n) : buildTypeParmsTemplate ps (n + 1)
    checkParamsPositionsAndBuildProps [] _ props _ = return props
    checkParamsPositionsAndBuildProps _ [] props _ = return props
    checkParamsPositionsAndBuildProps (GADTDefParamType x : tps)  (ParameterTypeT (TTParam y) : ps) props n
      | x /= y = Left $ WrongConstrResultTypeParameter (ConstrDef p cname pt) x (ParameterTypeT (TTParam y))
      | otherwise = checkParamsPositionsAndBuildProps tps ps props (n + 1)
    checkParamsPositionsAndBuildProps (GADTDefParamType x : _) (prm : _) _ _ =
      Left $ WrongConstrResultTypeParameter (ConstrDef p cname pt) x prm
    checkParamsPositionsAndBuildProps (GADTDefParamMonotype _ : tps) (ParameterMonotypeT m : ps) props n =
      checkParamsPositionsAndBuildProps tps ps ((MTParam . ("`#" ++ ) . show $ n, MTMono m) : props) (n + 1)
    checkParamsPositionsAndBuildProps (_ : tps) (_: ps) props n =
      checkParamsPositionsAndBuildProps tps ps props (n + 1)

runTypecheckerFun :: StateT TypecheckerState (Either (TypeError p)) a -> GADTDefs -> (Either (ASTBuilderError p)) a
runTypecheckerFun res g =
  case evalStateT res TypecheckerState {_freshVarNum = 0,  _gadtDefs = g, _constrContext = Map.empty, _funContext = Map.empty} of
    Left e -> Left $ ConstrFormednessTypeError e
    Right x -> return x

checkGADTParameterTemplateWellFormedness ::
  p -> Context -> GADTDefs -> (GADTDefParameter, GADTParameterTemplate)
  -> Either (ASTBuilderError p) ()
checkGADTParameterTemplateWellFormedness p c g (GADTDefParamType _, ParameterTypeT pt) = checkTypeTemplateWellFormedness p c g pt
checkGADTParameterTemplateWellFormedness p c g (GADTDefParamMonotype k, ParameterMonotypeT m) =
  runTypecheckerFun (checkMonotypeHasKind p c m k) g
checkGADTParameterTemplateWellFormedness p c g (GADTDefParamType _, ParameterMonotypeT m) =
  runTypecheckerFun (checkMonotypeHasKind p c m KStar) g
checkGADTParameterTemplateWellFormedness p _ _ (GADTDefParamMonotype m, ParameterTypeT pt) =
  Left $ TypeParamIsNotMonotypeError p (GADTDefParamMonotype m) (ParameterTypeT pt)

checkPropTemplateWellFormedness :: p -> Context -> GADTDefs -> PropositionTemplate ->  Either (ASTBuilderError p) ()
checkPropTemplateWellFormedness p c g (MTMono m1, MTMono m2) =
  runTypecheckerFun (inferMonotypeKind p c m1 >>= checkMonotypeHasKind p c m2) g
checkPropTemplateWellFormedness p _ _ _ = Left $ InternalCompilerASTBuilderError p "checkPropTemplateWellFormedness"

checkTypeTemplateWellFormedness :: p -> Context -> GADTDefs -> TypeTemplate -> Either (ASTBuilderError p) ()
checkTypeTemplateWellFormedness _ _ _ TTUnit     = return ()
checkTypeTemplateWellFormedness _ _ _ TTBool     = return ()
checkTypeTemplateWellFormedness _ _ _ TTInt      = return ()
checkTypeTemplateWellFormedness _ _ _ TTFloat    = return ()
checkTypeTemplateWellFormedness _ _ _ TTChar     = return ()
checkTypeTemplateWellFormedness _ _ _ TTString   = return ()
checkTypeTemplateWellFormedness _ _ _ TTParam {} = return ()
checkTypeTemplateWellFormedness p c g (TTArrow t1 t2)  =
   checkTypeTemplateWellFormedness p c g t1 >> checkTypeTemplateWellFormedness p c g t2
checkTypeTemplateWellFormedness p c g (TTGADT name ts) = do
  let gadtDefParams = Map.lookup name g
  case gadtDefParams of
    Nothing -> Left . ConstrFormednessTypeError $ UndeclaredGADTError p name
    Just params
      | length params /= length ts -> Left . ConstrFormednessTypeError $ MismatchedGADTArityError p name (length params) $ length ts
      | otherwise -> foldM_ ((.)(.)(.) (checkGADTParameterTemplateWellFormedness p c g) (flip const)) () $ zip params ts
checkTypeTemplateWellFormedness p c g (TTProduct ts _) = foldM_ ((.)(.)(.) (checkTypeTemplateWellFormedness p c g) (flip const)) () ts
checkTypeTemplateWellFormedness p c g (TTImp pr t) = checkPropTemplateWellFormedness p c g pr >> checkTypeTemplateWellFormedness p c g t
checkTypeTemplateWellFormedness p c g (TTAnd t pr) = checkTypeTemplateWellFormedness p c g t >> checkPropTemplateWellFormedness p c g pr
checkTypeTemplateWellFormedness p c g (TTUniversal x k t) = checkTypeTemplateWellFormedness p (CTypeVar (U x) k : c) g t
checkTypeTemplateWellFormedness p c g (TTExistential x k t) = checkTypeTemplateWellFormedness p (CTypeVar (U x) k : c) g t
checkTypeTemplateWellFormedness p c g (TTVec n t) =
   runTypecheckerFun (checkMonotypeHasKind p c n KNat) g >>
  checkTypeTemplateWellFormedness p c g t
checkTypeTemplateWellFormedness p c _ (TTEVar x) =
  case typeVarContextLookup c $ eTypeVarName x of
    Just (CTypeVar (E _) KStar) -> return ()
    Just (CETypeVar _ KStar _) -> return ()
    Just (CTypeVar (E _) KNat) -> Left . ConstrFormednessTypeError $ TypeHasWrongKindError p (TEVar x) KStar KNat
    Just (CETypeVar _ KNat _) -> Left . ConstrFormednessTypeError $ TypeHasWrongKindError p (TEVar x) KStar KNat
    _ -> Left . ConstrFormednessTypeError $ UndeclaredETypeVarError p x
checkTypeTemplateWellFormedness p c _ (TTUVar x) =
  case typeVarContextLookup c $ uTypeVarName x of
    Just (CTypeVar (U _) KStar) -> return ()
    Just (CTypeVar (U _) KNat) -> Left . ConstrFormednessTypeError $ TypeHasWrongKindError p (TUVar x) KStar KNat
    _ -> Left . ConstrFormednessTypeError $ UndeclaredUTypeVarError p x c

buildFunctions :: [ProgramBlock p] -> Either (ASTBuilderError p) ([Expr p], FunTypeContext)
buildFunctions programBlocks = do
  let names = getNames programBlocks Set.empty
  let defs = groupDefinitions programBlocks $ Map.fromSet (const ([], [])) names
  foldM buildFunction ([], operatorsTypeContext) defs
  where
    getNames [] acc = acc
    getNames (FunTypeAnnot _ name _ : blocks) acc = getNames blocks $ Set.insert name acc
    getNames (FunDefCase _ name _  _ : blocks) acc = getNames blocks $ Set.insert name acc
    getNames (GADTDef {} : blocks) acc = getNames blocks acc
    groupDefinitions [] acc = Map.map (cross id reverse) acc
    groupDefinitions (def @ (FunTypeAnnot _ name _) : defs) acc =
      groupDefinitions defs (Map.update (return . cross (def :) id) name acc)
    groupDefinitions (def @ (FunDefCase _ name _ _) : defs) acc =
      groupDefinitions defs (Map.update (return . cross id (def :)) name acc)
    groupDefinitions (GADTDef {} : defs) acc = groupDefinitions defs acc

buildFunction :: ([Expr p], FunTypeContext) -> ([ProgramBlock p], [ProgramBlock p]) -> Either (ASTBuilderError p) ([Expr p], FunTypeContext)
buildFunction (_, _) ([], FunDefCase p name _ _ : _) = Left $ FunctionLacksAnnotationError p name
buildFunction (_, _) ([FunTypeAnnot p name _], []) = Left $ FunctionLacksImplementationError p name
buildFunction (_, _) (FunTypeAnnot p name _ : _ : _, _) = Left $ MoreThanOneTypeAnnotationError p name
buildFunction (erecs, funCntxt) ([FunTypeAnnot annotPos name t], defs) = do
  let (FunDefCase _ _ argsExample _) = head defs
  branches <- mapM (getBranch $ length argsExample) defs
  let args = zipWith (++) (map (const "_x") argsExample) $ map show [1 .. length argsExample]
  let caseExpr = ECase annotPos (ETuple annotPos (map (EVar annotPos) args) $ length argsExample) branches
  let lambdasExpr = foldr (ELambda annotPos) caseExpr args
  return (ERec annotPos name (EAnnot annotPos lambdasExpr t) : erecs, Map.insert name t funCntxt)
  where
    getBranch numArgs (FunDefCase p _ ptrns e)
      | numArgs /= length ptrns = Left $ FunDifferentNumberOfArgs annotPos name
      | otherwise = return ([PTuple p ptrns $ length ptrns], e, p)
    getBranch _ (FunTypeAnnot p _ _) = Left $ InternalCompilerASTBuilderError p "getBranch"
    getBranch _ (GADTDef p _ _ _) = Left $ InternalCompilerASTBuilderError p "getBranch"
buildFunction (erecs, funCntxt) _ = return (erecs, funCntxt)

mergeUnOpsWithNumConsts :: Expr p -> Expr p
mergeUnOpsWithNumConsts (EVar    p x) = EVar p x
mergeUnOpsWithNumConsts (EUnit   p)   = EUnit p
mergeUnOpsWithNumConsts (ENil    p)   = ENil p
mergeUnOpsWithNumConsts (EBool   p b) = EBool p b
mergeUnOpsWithNumConsts (EInt    p x) = EInt p x
mergeUnOpsWithNumConsts (EFloat  p x) = EFloat p x
mergeUnOpsWithNumConsts (EChar p c)   = EChar p c
mergeUnOpsWithNumConsts (EString p s) = EString p s
mergeUnOpsWithNumConsts (ELambda p x e)  = ELambda p x $ mergeUnOpsWithNumConsts e
mergeUnOpsWithNumConsts (ESpine  p e s)  = ESpine p (mergeUnOpsWithNumConsts e) $ map mergeUnOpsWithNumConsts s
mergeUnOpsWithNumConsts (ERec    p f e)  = ERec p f $ mergeUnOpsWithNumConsts e
mergeUnOpsWithNumConsts (EAnnot  p e t)  = EAnnot p (mergeUnOpsWithNumConsts e) t
mergeUnOpsWithNumConsts (ETuple  p es n) = ETuple p (map mergeUnOpsWithNumConsts es) n
mergeUnOpsWithNumConsts (EConstr p c es) = EConstr p c (map mergeUnOpsWithNumConsts es)
mergeUnOpsWithNumConsts (ECase   p e bs) = ECase p (mergeUnOpsWithNumConsts e) bs
mergeUnOpsWithNumConsts (ECons   p e1 e2) = ECons p (mergeUnOpsWithNumConsts e1) (mergeUnOpsWithNumConsts e2)
mergeUnOpsWithNumConsts (EIf     p e1 e2 e3) = EIf p (mergeUnOpsWithNumConsts e1) (mergeUnOpsWithNumConsts e2) (mergeUnOpsWithNumConsts e3)
mergeUnOpsWithNumConsts (ELet    p x e1 e2)  = ELet p x (mergeUnOpsWithNumConsts e1) (mergeUnOpsWithNumConsts e2)
mergeUnOpsWithNumConsts (EBinOp  p op e1 e2) = EBinOp p op (mergeUnOpsWithNumConsts e1) (mergeUnOpsWithNumConsts e2)
mergeUnOpsWithNumConsts (EUnOp   p UnOpPlus (EInt _ x))         = EInt p x
mergeUnOpsWithNumConsts (EUnOp   p UnOpPlus (EFloat _ x))       = EFloat p x
mergeUnOpsWithNumConsts (EUnOp   p UnOpPlusFloat (EFloat _ x))  = EFloat p x
mergeUnOpsWithNumConsts (EUnOp   p UnOpMinus (EInt _ x))        = EInt p (-x)
mergeUnOpsWithNumConsts (EUnOp   p UnOpMinus (EFloat _ x))      = EFloat p (-x)
mergeUnOpsWithNumConsts (EUnOp   p UnOpMinusFloat (EFloat _ x)) = EFloat p (-x)
mergeUnOpsWithNumConsts (EUnOp   p op e) = EUnOp p op $ mergeUnOpsWithNumConsts e

buildAST :: [ProgramBlock p] ->  Either (ASTBuilderError p) (Program p, ConstructorsContext, GADTDefs, FunTypeContext)
buildAST blocks = do
  (cContext, gDefs) <- buildGADTContexts blocks
  (funs, fContext) <- buildFunctions blocks
  return (map mergeUnOpsWithNumConsts funs, cContext, gDefs, fContext)