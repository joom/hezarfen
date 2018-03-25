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
            RBind fr <$> sequence (map (subst n u) b)
                     <*> subst n' (Var fr) t
subst n u (RApp t1 t2) = RApp <$> subst n u t1 <*> subst n u t2
subst n u t = pure t

||| Check if `n` occurs in `t` freely.
isBound : (n : TTName) -> (t : Raw) -> Bool
isBound n (Var n') = n == n'
isBound n (RBind n' b t) =
  -- if n == n' then or (map (Delay . isBound n) b) else isBound n t
  if n == n'
  then or (map (Delay . isBound n) b)
  else isBound n t || or (map (Delay . isBound n) b)
isBound n (RApp t1 t2) = (isBound n t1) || (isBound n t2)
isBound n t = False

reduce : Raw -> Raw
reduce t = case t of
  -- Eta reduction
  -- (\x => f x) becomes f
  RBind n (Lam b) (RApp t' (Var n')) =>
    if n == n'
      then reduce t'
      else RBind n (Lam b) $ reduce (RApp (reduce t') (Var n'))

  -- ((\x => x) y) becomes y
  RApp (RBind n (Lam b) (Var n')) y =>
    if n == n'
      then reduce y
      else RApp (RBind n (Lam b) (Var n')) (reduce y)

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
      else t

  -- (\x => g (f x)) becomes (g . f)
  -- This is a bit problematic because composition takes the types
  -- as implicit arguments, however we don't have the types here.
  -- It works for now if we erase the types in the composition.
  -- We might need to test this more.
  RBind n (Lam b) (RApp g (RApp f (Var n'))) =>
    let idk = RConstant Forgot in -- I don't know
    if n == n' && not (n `isBound` g) && not (n `isBound` f)
      then `((.) {c = ~idk} {a = ~b} {b = ~idk} ~(reduce g) ~(reduce f))
      else RBind n (Lam b) (RApp (reduce g) (RApp (reduce f) (Var n')))

  -- (let x = t in x) becomes t
  RBind n (Let ty v) (Var n') =>
    if n == n'
    then v
    else (Var n') -- let binding unused, so remove

  -- If a let binding isn't used, remove it.
  RBind n (Let ty v) t' =>
    if n `isBound` t'
    then RBind n (Let ty v) (reduce t')
    else reduce t'

  RBind n b t' => RBind n b (reduce t')
  RApp t1 t2 => RApp (reduce t1) (reduce t2)
  _ => t

||| Not efficient, but works for now.
reduceLoop : Raw -> Raw
reduceLoop t = getFirst (zip s (tail s))
  where
    s : Stream Raw
    s = iterate reduce t

    getFirst : Stream (Raw, Raw) -> Raw
    getFirst ((x, y) :: xs) = if x == y then x else getFirst xs
