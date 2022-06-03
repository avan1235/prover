{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module Formula where

import Data.List (delete, nub)
import Util (update)

type VarName = String

type FunName = String

type RelName = String

data Term = Var VarName | Fun FunName [Term] deriving (Eq, Show)

variables :: Term -> [VarName]
variables (Var x) = [x]
variables (Fun _ ts) = nub $ concatMap variables ts

variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0 ..]]

type FunInt a = FunName -> [a] -> a

type Env a = VarName -> a

evalTerm :: FunInt a -> Env a -> Term -> a
evalTerm _ rho (Var x) = rho x
evalTerm int rho (Fun f ts) = int f $ map (evalTerm int rho) ts

data Formula =
      F
    | T
    | Rel RelName [Term]
    | Not Formula
    | Or Formula Formula
    | And Formula Formula
    | Implies Formula Formula
    | Iff Formula Formula
    | Exists VarName Formula
    | Forall VarName Formula deriving (Eq, Show)

type Substitution = Env Term

apply :: Substitution -> Formula -> Formula
apply _ F = F
apply _ T = T
apply f (Rel r ts) = Rel r $ map (evalTerm Fun f) ts
apply f (Not phi) = Not (apply f phi)
apply f (Or phi psi) = Or (apply f phi) (apply f psi)
apply f (And phi psi) = And (apply f phi) (apply f psi)
apply f (Implies phi psi) = Implies (apply f phi) (apply f psi)
apply f (Iff phi psi) = Iff (apply f phi) (apply f psi)
apply f (Exists x phi) = Exists x (apply (update f x (Var x)) phi)
apply f (Forall x phi) = Forall x (apply (update f x (Var x)) phi)

type SATSolver = Formula -> Bool

type FOProver = Formula -> Bool

fv :: Formula -> [VarName]
fv T = []
fv F = []
fv (Rel _ ts) = variables (Fun "dummy" ts)
fv (Not phi) = fv phi
fv (And phi psi) = nub $ fv phi ++ fv psi
fv (Or phi psi) = nub $ fv phi ++ fv psi
fv (Implies phi psi) = nub $ fv phi ++ fv psi
fv (Iff phi psi) = nub $ fv phi ++ fv psi
fv (Exists x phi) = delete x $ fv phi
fv (Forall x phi) = delete x $ fv phi