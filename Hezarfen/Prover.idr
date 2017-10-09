module Prover

import Language.Reflection.Utils
%access public export

fresh : Elab TTName
fresh = gensym "x"

Ty : Type
Ty = Raw

Tm : Type
Tm = Raw

data Context = Ctx (List (TTName, Ty)) (List (TTName, Ty))
data Sequent = Seq Context Ty

concludeWithBotL : Context -> TTName -> Ty -> Tm
concludeWithBotL (Ctx g o) n c = `(void {a=~c} ~(Var n))

concludeWithInit : Context -> TTName -> Ty -> Tm
concludeWithInit (Ctx g o) n c = Var n

concludeWithTopR : Context -> Tm
concludeWithTopR (Ctx g o) = `(MkUnit)

insert : TTName -> Ty -> Context -> Context
insert n p (Ctx g o) = case p of
  `(~(Var x) -> ~B)   => Ctx ((n, p) :: g) o
  `((~A -> ~B) -> ~D) => Ctx ((n, p) :: g) o
  Var x               => Ctx ((n, p) :: g) o
  _                   => Ctx g ((n, p) :: o)

appConjR : Context -> (Ty, Ty) -> (Sequent, Sequent)
appConjR ctx (a, b) = (Seq ctx a, Seq ctx b)

appImplR : Context -> (Ty, Ty) -> Elab (TTName, Sequent)
appImplR ctx (a, b) = do n <- fresh ; pure (n, Seq (insert n a ctx) b)

appConjL : Context -> (Ty, Ty, Ty) -> Elab (TTName, TTName, Sequent)
appConjL ctx (a, b, c) =
  do n1 <- fresh ; n2 <- fresh
     pure (n1, n2, Seq ((insert n1 b . insert n2 a) ctx) c)

appTopImplL : Context -> Ty -> Ty -> Elab (TTName, Sequent)
appTopImplL ctx b c = do n <- fresh ; pure (n, Seq (insert n b ctx) c)

appDisjImplL : Context -> (Ty, Ty, Ty, Ty) -> Elab (TTName, TTName, Sequent)
appDisjImplL ctx (d, e, b, c) =
  do n1 <- fresh ; n2 <- fresh
     pure (n1, n2, Seq ((insert n2 `(~e -> ~b) . insert n1 `(~d -> ~b)) ctx) c)

except : Nat -> List a -> List a
except n xs = (take n xs) ++ (drop (S n) xs)

allCtxs : List a -> List (a, List a)
allCtxs [] = []
allCtxs (x :: xs) = zipWith (\y,i => (y, except i (x :: xs)))
                            (reverse (x :: xs))
                            [(length xs) .. 0]

appDisjL : Context -> (Ty, Ty, Ty)
        -> Elab ((TTName, Sequent), (TTName, Sequent))
appDisjL ctx (a, b, c) =
  let (n1, n2) = (!fresh, !fresh) in
  let (ctx1, ctx2) = (insert n1 a ctx, insert n2 b ctx) in
  pure ((n1, Seq ctx1 c), (n2, Seq ctx2 c))

appConjImplL : Context -> (Ty, Ty, Ty, Ty) -> Elab (TTName, Sequent)
appConjImplL (Ctx g o) (d, e, b, c) =
  do n <- fresh
     pure (n, Seq (insert n `(~d -> (~e -> ~b)) (Ctx g o)) c)

appAtomImplL : List (TTName, Ty) -> (Ty, Ty, Ty) -> Elab (TTName, Sequent)
appAtomImplL g (p, b, c) =
  do n <- fresh
     if p `elem` (map snd g) -- TODO ?
        then pure (n, Seq (insert n b (Ctx g [])) c)
        else fail [TextPart "Not in context in appAtomImplL"]

appImplImplL : Context -> (Ty, Ty, Ty, Ty)
            -> Elab ((TTName, TTName, Sequent), (TTName, Sequent))
appImplImplL (Ctx g o) (d, e, b, c) =
  let (n1, n2, n3) = (!fresh, !fresh, !fresh) in
  let ctx1 = (insert n1 d . insert n2 `(~e -> ~b)) (Ctx g o) in
  let ctx2 = insert n3 b (Ctx g o) in
  pure ((n1, n2, Seq ctx1 e), (n3, Seq ctx2 c))

mutual
  breakdown : Sequent -> Elab Tm
  breakdown goal = case goal of
    Seq ctx `(Unit) => pure $ concludeWithTopR ctx
    Seq ctx `(Pair ~a ~b) =>
      let (newgoal1, newgoal2) = appConjR ctx (a, b) in
      let (tm1, tm2) = (!(breakdown newgoal1), !(breakdown newgoal2)) in
      pure `(MkPair {A=~a} {B=~b} ~tm1 ~tm2)
    Seq ctx `(~a -> ~b) =>
      let (n, newgoal) = !(appImplR ctx (a, b)) in
      let tm = !(breakdown newgoal) in
      pure $ RBind n (Lam a) tm
    Seq (Ctx g ((p, `(Pair ~a ~b)) :: o)) c =>
      let (n1, n2, newgoal) = !(appConjL (Ctx g o) (a, b, c)) in
      pure $ RBind n1 (Let a `(fst {a=~a} {b=~b} ~(Var p)))
           $ RBind n2 (Let b `(snd {a=~a} {b=~b} ~(Var p)))
             !(breakdown newgoal)
    Seq (Ctx g ((_, `(Unit)) :: o)) c => breakdown (Seq (Ctx g o) c)
    Seq (Ctx g ((n, `(Void)) :: o)) c =>
      pure $ concludeWithBotL (Ctx g o) n c
    Seq (Ctx g ((n, `(Either ~a ~b)) :: o)) c =>
      let ((n1, newgoal1), (n2, newgoal2)) = !(appDisjL (Ctx g o) (a, b, c)) in
      let (tm1, tm2) = (!(breakdown newgoal1), !(breakdown newgoal2)) in
      let lm1 = RBind n1 (Lam a) tm1 in
      let lm2 = RBind n2 (Lam b) tm2 in
      pure `(either {c=~c} {b=~b} {a=~a} (Delay ~lm1) (Delay ~lm2) ~(Var n))
    Seq (Ctx g ((n, `(Unit -> ~b)) :: o)) c =>
      let (n', newgoal) = !(appTopImplL (Ctx g o) b c) in
      pure $ RBind n' (Let b (RApp (Var n) `(MkUnit))) !(breakdown newgoal)
    Seq (Ctx g ((n, `(Void -> ~b)) :: o)) c => breakdown (Seq (Ctx g o) c)
    Seq (Ctx g ((n, `((Pair ~d ~e) -> ~b)) :: o)) c =>
      let (n', newgoal) = !(appConjImplL (Ctx g o) (d, e, b, c)) in
      pure $ RBind n' (Let `(~d -> ~e -> ~b)
                            `(curry {c=~b} {b=~e} {a=~d} ~(Var n)))
                      !(breakdown newgoal)
    Seq (Ctx g ((n, `((Either ~d ~e) -> ~b)) :: o)) c =>
      let (n1, n2, newgoal) = !(appDisjImplL (Ctx g o) (d, e, b, c)) in
      let (l1, l2) = (!fresh, !fresh) in
      pure $ RBind n1 (Let `(~d -> ~b)
                        (RBind l1 (Lam d) (RApp (Var n)
                          `(Left {a=~d} {b=~e} ~(Var l1)))))
           $ RBind n2 (Let `(~e -> ~b)
                        (RBind l2 (Lam e) (RApp (Var n)
                          `(Right {a=~d} {b=~e} ~(Var l2)))))
             !(breakdown newgoal)
    Seq (Ctx g []) `(Either ~a ~b) => ?e
          -- (OneInf DisjL  <$> searchSync g p)
      -- <|> (OneInf DisjR1 <$> breakdown (Seq ctx a))
      -- <|> (OneInf DisjR2 <$> breakdown (Seq ctx b)) <*> pure goal
    Seq (Ctx g []) c => searchSync g c
    _ => fail [TextPart "No rule applies in breakdown"]

  searchSync : List (TTName, Ty) -> Ty -> Elab Tm
  searchSync g c = choiceMap (eliminate c) (allCtxs g)

  eliminate : Ty -> ((TTName, Ty), List (TTName, Ty)) -> Elab Ty
  eliminate (Var y) ((n2, Var x), ctx) =
    if x == y
    then pure $ concludeWithInit (Ctx ((n2, Var x) :: ctx) []) n2 (Var y)
    else fail [TextPart "Var comparison failed in eliminate"]
  eliminate _ ((_, Var _), _) =
    fail [TextPart "Eliminate argument not a var"]
  eliminate c ((n, `(~(Var x) -> ~b)), ctx) =
    let goal = Seq (Ctx ((n, `(~(Var x) -> ~b)) :: ctx) []) c in
    let (n', newgoal) = !(appAtomImplL ctx (Var x, b, c)) in
    pure $ ?l
    -- pure $ OneInf AtomImplL !(breakdown newgoal) goal
  eliminate c ((n, `((~d -> ~e) -> ~b)), ctx) =
    let goal = Seq (Ctx ((n, `((~d -> ~e) -> ~b)) :: ctx) []) c in
    let ((a1, a2, newgoal1), (a3, newgoal2)) =
      !(appImplImplL (Ctx ctx []) (d, e, b, c)) in
   pure $ ?l2
    -- pure $ TwoInf ImplImplL !(breakdown newgoal1) !(breakdown newgoal2) goal
  eliminate _ _ = fail [TextPart "No rule applies in eliminate"]

prove : Ty -> Elab Tm
prove c = breakdown (Seq (Ctx [] []) c)
