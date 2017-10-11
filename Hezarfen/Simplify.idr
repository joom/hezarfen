module Hezarfen.Simplify

import Hezarfen.Prover
import Language.Reflection.Utils

%access public export

reduce : Raw -> Raw
reduce t = case t of
  -- Eta reduction
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

  -- (\x => x) becomes id
  RBind n (Lam b) (Var n') =>
    if n == n'
      then reduce (RApp (Var `{id}) b)
      else t

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
