module Formula where

import Control.Monad (liftM, liftM2, replicateM)
import Control.Monad.Trans.State (State, evalState, get, put)
import Data.List (delete, intercalate, sort)
import qualified Data.Map as Map
import Util (functions, ordNub, prefixes, update)

type VarName = String

type FunName = String

type RelName = String

data Term = Var VarName | Fun FunName [Term] deriving (Eq, Show, Ord)

type FunInt a = FunName -> [a] -> a

type Env a = VarName -> a

data Formula
  = F
  | T
  | Rel RelName [Term]
  | Not Formula
  | Or Formula Formula
  | And Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | Exists VarName Formula
  | Forall VarName Formula
  deriving (Eq, Show, Ord)

type VarMapping = Map.Map VarName VarName

type Arity = Int

type Signature = [(FunName, Arity)]

type FunSignature = Map.Map Arity [FunName]

type VarAssignment = Map.Map VarName Term

type Substitution = Map.Map VarName Term

varsT :: Term -> [VarName]
varsT (Var x) = [x]
varsT (Fun _ ts) = ordNub $ concatMap varsT ts

variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0 ..]]

vars :: Formula -> [VarName]
vars T = []
vars F = []
vars (Rel _ ts) = varsT (Fun "dummy" ts)
vars (Not phi) = vars phi
vars (And phi psi) = ordNub $ vars phi ++ vars psi
vars (Or phi psi) = ordNub $ vars phi ++ vars psi
vars (Implies phi psi) = ordNub $ vars phi ++ vars psi
vars (Iff phi psi) = ordNub $ vars phi ++ vars psi
vars (Exists x phi) = ordNub $ x : vars phi
vars (Forall x phi) = ordNub $ x : vars phi

fv :: Formula -> [VarName]
fv T = []
fv F = []
fv (Rel _ ts) = varsT (Fun "dummy" ts)
fv (Not phi) = fv phi
fv (And phi psi) = ordNub $ fv phi ++ fv psi
fv (Or phi psi) = ordNub $ fv phi ++ fv psi
fv (Implies phi psi) = ordNub $ fv phi ++ fv psi
fv (Iff phi psi) = ordNub $ fv phi ++ fv psi
fv (Exists x phi) = delete x $ fv phi
fv (Forall x phi) = delete x $ fv phi

renameT :: VarName -> VarName -> Term -> Term
renameT x y (Var z)
  | z == x = Var y
  | otherwise = Var z
renameT x y (Fun f ts) = Fun f (map (renameT x y) ts)

rename :: VarName -> VarName -> Formula -> Formula
rename x y T = T
rename x y F = F
rename x y (Rel r ts) = Rel r (map (renameT x y) ts)
rename x y (Not phi) = Not (rename x y phi)
rename x y (And phi psi) = And (rename x y phi) (rename x y psi)
rename x y (Or phi psi) = Or (rename x y phi) (rename x y psi)
rename x y (Implies phi psi) = Implies (rename x y phi) (rename x y psi)
rename x y (Iff phi psi) = Iff (rename x y phi) (rename x y psi)
rename x y (Forall z phi)
  | z == x = Forall z phi
  | otherwise = Forall z (rename x y phi)
rename x y (Exists z phi)
  | z == x = Exists z phi
  | otherwise = Exists z (rename x y phi)

substT :: Substitution -> Term -> Term
substT sigma (Var x) = sigma Map.! x
substT sigma (Fun f ts) = Fun f (map (substT sigma) ts)

subst :: Substitution -> Formula -> Formula
subst _ T = T
subst _ F = F
subst sigma (Rel r ts) = Rel r $ map (substT sigma) ts
subst sigma (Not phi) = Not $ subst sigma phi
subst sigma (And phi psi) = And (subst sigma phi) (subst sigma psi)
subst sigma (Or phi psi) = Or (subst sigma phi) (subst sigma psi)
subst sigma (Implies phi psi) = Implies (subst sigma phi) (subst sigma psi)
subst sigma (Iff phi psi) = Iff (subst sigma phi) (subst sigma psi)
subst sigma (Exists x phi) = Exists x (subst (update sigma x (Var x)) phi)
subst sigma (Forall x phi) = Forall x (subst (update sigma x (Var x)) phi)

generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where
    go [] = phi
    go (x : xs) = Forall x $ go xs

concretize :: Formula -> Formula
concretize phi = go $ fv phi
  where
    go [] = phi
    go (x : xs) = Exists x $ go xs

fresh :: Formula -> Formula
fresh phi = evalState (go phi) []
  where
    go :: Formula -> State [VarName] Formula
    go T = return T
    go F = return F
    go phi@(Rel _ _) = return phi
    go (Not phi) = fmap Not (go phi)
    go (And phi psi) = liftM2 And (go phi) (go psi)
    go (Or phi psi) = liftM2 Or (go phi) (go psi)
    go (Implies phi psi) = liftM2 Implies (go phi) (go psi)
    go (Iff phi psi) = liftM2 Iff (go phi) (go psi)
    go (Forall x phi) = go2 Forall x phi
    go (Exists x phi) = go2 Exists x phi

    go2 quantifier x phi =
      do
        xs <- get
        let y = head [y | y <- variants x, y `notElem` xs]
        let psi = rename x y phi
        put $ y : xs
        quantifier y <$> go psi

notOfNnf :: Formula -> Formula
notOfNnf (Not T) = T
notOfNnf (Not F) = F
notOfNnf (Not (Rel v terms)) = Rel v terms
notOfNnf T = F
notOfNnf F = T
notOfNnf (phi `And` psi) = notOfNnf phi `Or` notOfNnf psi
notOfNnf (phi `Or` psi) = notOfNnf phi `And` notOfNnf psi
notOfNnf (Forall v phi) = Exists v (notOfNnf phi)
notOfNnf (Exists v phi) = Forall v (notOfNnf phi)
notOfNnf (Rel v terms) = Not (Rel v terms)
notOfNnf f = error $ "found not NNF formula: " ++ show f

nnf :: Formula -> Formula
nnf (Not F) = T
nnf (Not T) = F
nnf (Not (Rel v terms)) = Not (Rel v terms)
nnf (Not (phi `And` psi)) = nnf (Not phi) `Or` nnf (Not psi)
nnf (Not (phi `Or` psi)) = nnf (Not phi) `And` nnf (Not psi)
nnf (Not (phi `Implies` psi)) = nnf phi `And` nnf (Not psi)
nnf (Not (phi `Iff` psi)) = (nnfPhi `And` notOfNnf nnfPsi) `Or` (nnfPsi `And` notOfNnf nnfPhi)
  where
    nnfPsi = nnf psi
    nnfPhi = nnf phi
nnf (Not (Forall v phi)) = Exists v (nnf (Not phi))
nnf (Not (Exists v phi)) = Forall v (nnf (Not phi))
nnf (Not (Not phi)) = nnf phi
nnf T = T
nnf F = F
nnf (Rel v terms) = Rel v terms
nnf (phi `And` psi) = nnf phi `And` nnf psi
nnf (phi `Or` psi) = nnf phi `Or` nnf psi
nnf (phi `Implies` psi) = nnf (Not phi) `Or` nnf psi
nnf (phi `Iff` psi) = (nnfPhi `Or` notOfNnf nnfPsi) `And` (nnfPsi `Or` notOfNnf nnfPhi)
  where
    nnfPsi = nnf psi
    nnfPhi = nnf phi
nnf (Forall v phi) = Forall v (nnf phi)
nnf (Exists v phi) = Exists v (nnf phi)

pnfOfNnfBinOp :: Formula -> Formula -> (Formula -> Formula -> Formula) -> Formula
pnfOfNnfBinOp (Forall v1 phi) (Forall v2 psi) op = Forall v1 (Forall v2 (pnfOfNnf (phi `op` psi)))
pnfOfNnfBinOp (Exists v1 phi) (Exists v2 psi) op = Exists v1 (Exists v2 (pnfOfNnf (phi `op` psi)))
pnfOfNnfBinOp (Exists v1 phi) (Forall v2 psi) op = Exists v1 (Forall v2 (pnfOfNnf (phi `op` psi)))
pnfOfNnfBinOp (Forall v1 phi) (Exists v2 psi) op = Forall v1 (Exists v2 (pnfOfNnf (phi `op` psi)))
pnfOfNnfBinOp (Forall v1 phi) psi op = Forall v1 (pnfOfNnf (phi `op` psi))
pnfOfNnfBinOp (Exists v1 phi) psi op = Exists v1 (pnfOfNnf (phi `op` psi))
pnfOfNnfBinOp psi (Forall v1 phi) op = Forall v1 (pnfOfNnf (phi `op` psi))
pnfOfNnfBinOp psi (Exists v1 phi) op = Exists v1 (pnfOfNnf (phi `op` psi))
pnfOfNnfBinOp phi psi op = phi `op` psi

pnfOfNnf :: Formula -> Formula
pnfOfNnf T = T
pnfOfNnf F = F
pnfOfNnf (Not phi) = Not (pnfOfNnf phi)
pnfOfNnf (Rel v terms) = Rel v terms
pnfOfNnf (Forall v phi) = Forall v (pnfOfNnf phi)
pnfOfNnf (Exists v phi) = Exists v (pnfOfNnf phi)
pnfOfNnf (phi `And` psi) = pnfOfNnfBinOp (pnfOfNnf phi) (pnfOfNnf psi) And
pnfOfNnf (phi `Or` psi) = pnfOfNnfBinOp (pnfOfNnf phi) (pnfOfNnf psi) Or
pnfOfNnf f = error $ "found not NNF formula: " ++ show f

renameTerms :: VarMapping -> Term -> Term
renameTerms r (Var z) = case Map.lookup z r of
  Nothing -> Var z
  Just y -> Var y
renameTerms r (Fun f ts) = Fun f (map (renameTerms r) ts)

pnf :: Formula -> Formula
pnf = pnfOfNnf . fresh . nnf

substituteT :: Map.Map VarName [Term] -> [Term] -> [Term]
substituteT _ [] = []
substituteT as (f@(Fun _ _) : ts) = f : substituteT as ts
substituteT as (Var v : ts) = t' : substituteT as ts
  where
    t' = case Map.lookup v as of
      Nothing -> Var v
      Just b -> Fun v b

substitute :: Map.Map VarName [Term] -> [Term] -> Formula -> Formula
substitute _ _ T = T
substitute _ _ F = F
substitute as vs (Not phi) = Not (substitute as vs phi)
substitute as _ (Rel v terms) = Rel v (substituteT as terms)
substitute as vs (Forall v phi) = Forall v (substitute as (Var v : vs) phi)
substitute as vs (Exists v phi) = substitute (Map.insert v vs as) vs phi
substitute as vs (phi `And` psi) = substitute as vs phi `And` substitute as vs psi
substitute as vs (phi `Or` psi) = substitute as vs phi `Or` substitute as vs psi
substitute _ _ f = error $ "found not NNF formula: " ++ show f

skolemise :: Formula -> Formula
skolemise phi = inPnf
  where
    concrete = concretize phi
    inNnf = nnf concrete
    withFresh = fresh inNnf
    replaced = substitute Map.empty [] withFresh
    inPnf = pnf replaced

sigT :: Term -> Signature
sigT (Var _) = []
sigT (Fun f ts) = ordNub $ (f, length ts) : concatMap sigT ts

sig :: Formula -> Signature
sig T = []
sig F = []
sig (Rel r ts) = concatMap sigT ts
sig (Not phi) = sig phi
sig (And phi psi) = ordNub $ sig phi ++ sig psi
sig (Or phi psi) = ordNub $ sig phi ++ sig psi
sig (Implies phi psi) = ordNub $ sig phi ++ sig psi
sig (Iff phi psi) = ordNub $ sig phi ++ sig psi
sig (Exists _ phi) = sig phi
sig (Forall _ phi) = sig phi

constants :: Signature -> [Term]
constants s = if null xs then [Fun "c" []] else xs
  where
    xs = [Fun c [] | (c, 0) <- s]

notConstants :: Signature -> FunSignature
notConstants s = foldr update Map.empty notConst
  where
    notConst = filter (\(_, c) -> c > 0) s
    update (n, a) acc = Map.insert a ns' acc
      where
        ns' = case Map.lookup a acc of
          Nothing -> [n]
          Just ns -> n : ns

applyFunctions :: FunSignature -> [Arity] -> [Term] -> [Term]
applyFunctions fs as ts = concatMap applyCombined as
  where
    arityArgs a _ = replicateM a ts
    aritiesArgs = Map.mapWithKey arityArgs fs
    combineArgs fs args = [Fun f a | a <- args, f <- fs]
    applyCombined a = combineArgs (fs Map.! a) (aritiesArgs Map.! a)

universe :: [Term] -> [Term] -> FunSignature -> [Term]
universe ts acc fs = if Map.null fs then ts else ordNub $ go ts acc
  where
    as = Map.keys fs
    go ts acc = ts ++ go ts' acc'
      where
        ts' = applyFunctions fs as acc
        acc' = ordNub $ acc ++ ts'

withAssignmentT :: VarAssignment -> Term -> Term
withAssignmentT c (Var n) = case Map.lookup n c of
  Just n' -> n'
  Nothing -> error $ "unknown variable name in formula: " ++ show n
withAssignmentT c (Fun f ts) = Fun f (map (withAssignmentT c) ts)

withAssignment :: Formula -> VarAssignment -> Formula
withAssignment T _ = T
withAssignment F _ = F
withAssignment (Rel r ts) c = Rel r (map (withAssignmentT c) ts)
withAssignment (Not phi) c = Not (withAssignment phi c)
withAssignment (And phi psi) c = withAssignment phi c `And` withAssignment psi c
withAssignment (Or phi psi) c = withAssignment phi c `Or` withAssignment psi c
withAssignment (Implies phi psi) c = withAssignment phi c `Implies` withAssignment psi c
withAssignment (Iff phi psi) c = withAssignment phi c `Iff` withAssignment psi c
withAssignment f@(Exists _ _) _ = error $ "expected quantifier-free formula: " ++ show f
withAssignment f@(Forall _ _) _ = error $ "expected quantifier-free formula: " ++ show f

groundInstances :: Formula -> [Formula]
groundInstances phi = ordNub $ map (withAssignment phi) cases
  where
    s = sig phi -- `debug` "s"
    ts = constants s -- `debug` "ts"
    fs = notConstants s -- `debug` "fs"
    vs = sort (fv phi) -- `debug` "vs"
    nvs = length vs -- `debug` "nvs"
    us = universe ts ts fs
    partUs = prefixes us
    varAssForParUs part = map (Map.fromAscList . zip vs) (replicateM nvs part)
    cases = concatMap varAssForParUs partUs

atomicFormulas :: Formula -> [Formula]
atomicFormulas T = []
atomicFormulas F = []
atomicFormulas phi@(Rel _ _) = [phi]
atomicFormulas (Not phi) = atomicFormulas phi
atomicFormulas (And phi psi) = ordNub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Or phi psi) = ordNub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Implies phi psi) = ordNub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Iff phi psi) = ordNub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Exists x phi) = atomicFormulas phi
atomicFormulas (Forall x phi) = atomicFormulas phi

sat :: Formula -> Bool
sat phi = or [ev int phi | int <- fs]
  where
    atoms = atomicFormulas phi
    fs = functions atoms [True, False]

    ev :: Map.Map Formula Bool -> Formula -> Bool
    ev int T = True
    ev int F = False
    ev int atom@(Rel _ _) = int Map.! atom
    ev int (Not phi) = not (ev int phi)
    ev int (Or phi psi) = ev int phi || ev int psi
    ev int (And phi psi) = ev int phi && ev int psi
    ev _ phi = error $ "unexpected formula: " ++ show phi

noUniversalPrefix :: Formula -> Formula
noUniversalPrefix (Forall _ phi) = noUniversalPrefix phi
noUniversalPrefix phi = phi

conjunction :: [Formula] -> Formula
conjunction [] = error "expected not empty formula candidates"
conjunction [x] = x
conjunction (x : xs) = x `And` conjunction xs

tautology :: Formula -> Bool
tautology phi = or unSat
  where
    gen = generalise phi
    skol = skolemise (Not gen)
    phi' = noUniversalPrefix skol
    gi = groundInstances phi'
    pref = prefixes gi
    phis = map conjunction pref
    unSat = map (not . sat) phis
