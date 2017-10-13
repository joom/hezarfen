module Hezarfen.FunDefn

import Hezarfen.Prover
import Hezarfen.Simplify
import Language.Reflection.Utils

%access public export

||| Looking at a proof term, collect the initial lambda argument names and
||| their types, and return the remaining proof term after the initial lambdas.
collect : Tm -> (List (TTName, Ty), Tm)
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

||| Takes a list of the arguments parsed by `collect`, and the rest of
||| the proof term. Checks how many consecutive `fst` and `snd` projections
||| in the beginning of `rest`. Returns a list of the names of the pairs they
||| project on, and what the projections are named. Also returns the rest
||| of the proof term stripped from the projections.
pairProjections : (lamIntro : List (TTName, Tm)) -> (rest : Tm)
               -> Elab (List (TTName, (TTName, TTName)), Tm)
pairProjections lamIntro rest =
  case rest of
    RBind n1 (Let a `(Prelude.Basics.fst {a=~a1} {b=~b1} ~(Var p1)))
      (RBind n2 (Let b `(Prelude.Basics.snd {a=~a2} {b=~b2} ~(Var p2))) t) =>
      if p1 == p2 && (p1 `elem` (fst <$> lamIntro)) && not (p1 `isBound` t)
         then do (xs, t') <- pairProjections lamIntro t
                 pure ((p1, (n1, n2)) :: xs, t)
         else pure ([], rest)
    RBind n b t =>
      if n `elem` (fst <$> lamIntro)
         then pure ([], rest)
         else do (xs, t') <- pairProjections lamIntro t
                 pure (xs, RBind n b t')
    RApp t1 t2 =>
      do (xs, t1') <- pairProjections lamIntro t1
         (ys, t2') <- pairProjections lamIntro t2
         pure (xs ++ ys, RApp t1' t2')
    _ => pure ([], rest)

||| The entry point for other modules.
definitionize : TTName -> Tm -> Elab (FunDefn Raw)
definitionize n t =
  let (lhs, rhs) = !(lambdas n t) in
  -- TODO figure out how to create LHS and RHS that respects the pair patterns
  -- let (pairReplacements, rest) = pairProjections _ rhs
  pure $ DefineFun n [MkFunClause lhs rhs]
