module Hezarfen.FunDefn

import Hezarfen.Prover
import Language.Reflection.Utils

%access public export

||| Looking at a proof term, collect the initial lambda argument names and
||| their types, and return the remaining proof term after the initial lambdas.
collect : Tm -> (List (TTName, Tm), Tm)
collect (RBind n' (Lam b) t') with (collect t')
  | (xs, rest) = ((n', b) :: xs, rest)
collect t' = ([], t')

||| Returns a left and right hand side for a fun clause
lambdas : TTName -> Tm -> Elab (Tm, Tm)
lambdas n t =
    let (xs, rhs) = collect t in
    let apps = foldl (\t, (name, _) => RApp t (Var name)) (Var n) xs in
    let xsRev = reverse xs in
    pure (binds xsRev apps, binds xsRev rhs)
  where
    ||| The list should be reversed beforehand
    binds : List (TTName, Ty) -> Tm -> Raw
    binds [] t' = t'
    binds ((n', ty) :: xs) t' = binds xs $ RBind n' (PVar ty) t'

||| Currently does not do anything smart.
definitionize : TTName -> Tm -> Elab (FunDefn Raw)
definitionize n t =
  let (lhs, rhs) = !(lambdas n t) in
     pure $ DefineFun n [MkFunClause lhs rhs]
