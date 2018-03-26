module Hezarfen.Simplify

import Hezarfen.Prover
import Language.Reflection.Utils

%access public export

||| subst n u t = t [u/n]
||| Different from `alphaRaw` in Pruviloj in the sense that we can replace
||| names with terms here, not just names with names.
subst : (n : TTName) -> (u : Raw) -> (t : Raw) -> Elab Raw
subst n u (Var n') = pure $ if n == n' then u else Var n'
subst n u (RBind n' b t) =
  if n == n'
    then RBind n' <$> sequence (map (subst n u) b) <*> pure t
    else do fr <- fresh
            t' <- subst n' (Var fr) t
            RBind fr <$> sequence (map (subst n u) b)
                     <*> subst n u t'
subst n u (RApp t1 t2) = RApp <$> subst n u t1 <*> subst n u t2
subst n u t = pure t

||| Check if `n` occurs in `t` freely.
isBound : (n : TTName) -> (t : Raw) -> Bool
isBound n (Var n') = n == n'
isBound n (RBind n' b t) =
  let isInB = or (map (Delay . isBound n) b) in
  if n == n' then isInB else (isBound n t || isInB)
isBound n (RApp t1 t2) = (isBound n t1) || (isBound n t2)
isBound n t = False

||| Count how many times `n` occurs in `t` freely.
countOccurrences : (n : TTName) -> (t : Raw) -> Nat
countOccurrences n (Var n') = if n == n' then 1 else 0
countOccurrences n (RBind n' b t) =
  let countInB = sum (map (countOccurrences n) b) in
  if n == n' then countInB else (countOccurrences n t + countInB)
countOccurrences n (RApp t1 t2) = countOccurrences n t1 + countOccurrences n t2
countOccurrences _ _ = 0

reduce : Raw -> Elab Raw
reduce t = case t of
  -- Eta reduction
  -- (\x => f x) becomes f
  RBind n (Lam b) (RApp t' (Var n')) =>
    if n == n'
      then reduce t'
      else pure $ RBind n (Lam b) !(reduce (RApp !(reduce t') (Var n')))

  -- ((\x => x) y) becomes y
  RApp (RBind n (Lam b) (Var n')) y =>
    if n == n'
    then reduce y
    else pure $ RApp (RBind n (Lam b) (Var n')) !(reduce y)

  -- (id x) becomes x
  RApp (RApp (Var `{id}) c) x => reduce x

  -- (id . f) becomes f
  RApp (RApp (RApp (RApp (RApp (Var `{(.)}) c) a) b) (RApp (Var `{id}) _)) f => reduce f

  -- (f . id) becomes f
  RApp (RApp (RApp (RApp (RApp (Var `{(.)}) c) a) b) f) (RApp (Var `{id}) _) => reduce f

  -- (\x => x) becomes id
  RBind n (Lam b) (Var n') =>
    if n == n'
    then reduce (RApp (Var `{id}) b)
    else pure t

  -- (\x => g (f x)) becomes (g . f)
  -- This is a bit problematic because composition takes the types
  -- as implicit arguments, however we don't have the types here.
  -- It works for now if we erase the types in the composition.
  -- We might need to test this more.
  RBind n (Lam b) (RApp g (RApp f (Var n'))) => do
    g' <- reduce g
    f' <- reduce f
    if n == n' && not (n `isBound` g) && not (n `isBound` f)
      then pure `((.) {c = ~idk} {a = ~b} {b = ~idk} ~g' ~f')
      else pure $ RBind n (Lam b) (RApp g' (RApp f' (Var n')))

  -- (let x = t in x) becomes t
  RBind n (Let ty v) (Var n') =>
    pure $ if n == n'
    then v
    else (Var n') -- let binding unused, so remove

  RBind n (Let ty v) t' => do
    t'' <- reduce t'
    case countOccurrences n t' of
      -- If a let binding isn't used, remove it.
      Z => pure t''
      -- If a let binding is only used once,
      -- remove the binding and replace the occurrence
      S Z => subst n v t''
      -- If it's used more than once, leave the binding
      _ => pure $ RBind n (Let ty v) t''

  RBind n b t' => pure $ RBind n b !(reduce t')
  RApp t1 t2 => pure $ RApp !(reduce t1) !(reduce t2)
  _ => pure t

untilFixpointM : (Monad m, Eq a) => (a -> m a) -> a -> m a
untilFixpointM f x =
  do x' <- f x ; if x == x' then pure x else untilFixpointM f x'

||| Not efficient, but works for now.
reduceLoop : Raw -> Elab Raw
reduceLoop = untilFixpointM reduce
