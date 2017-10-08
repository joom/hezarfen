module Prover

import Language.Reflection.Utils
%access public export

data Prop =
  Atom Raw | Conj Prop Prop | Disj Prop Prop | Impl Prop Prop | Top | Bot

Eq Prop where
  (Atom x) == (Atom y) = x == y
  (Conj a b) == (Conj c d) = a == c && b == d
  (Disj a b) == (Disj c d) = a == c && b == d
  (Impl a b) == (Impl c d) = a == c && b == d
  Top == Top = True
  Bot == Bot = True
  _ == _ = False

data Context = Ctx (List Prop) (List Prop)
data Sequent = Seq Context Prop

data Rule =
    ConjR | ConjL | TopR | ImplR | ImplL | Init
  | DisjL | DisjR1 | DisjR2 | TopL | BotL | AtomImplL | ConjImplL
  | TopImplL | DisjImplL | BotImplL | ImplImplL

data Derivation =
    ZeroInf Rule Sequent
  | OneInf  Rule Derivation Sequent
  | TwoInf  Rule Derivation Derivation Sequent

concludeWithBotL : Context -> Prop -> Derivation
concludeWithBotL (Ctx g o) c = ZeroInf BotL $ Seq (Ctx (Bot :: g) o) c

concludeWithInit : Context -> Prop -> Derivation
concludeWithInit (Ctx g o) c = ZeroInf Init $ Seq (Ctx g o) c

concludeWithTopR : Context -> Derivation
concludeWithTopR (Ctx g o) = ZeroInf TopR $ Seq (Ctx g o) Top

insert : Prop -> Context -> Context
insert p (Ctx g o) = case p of
  Atom x            => Ctx (p :: g) o
  Impl (Atom x) b   => Ctx (p :: g) o
  Impl (Impl a b) d => Ctx (p :: g) o
  _                 => Ctx g (p :: o)

appConjR : Context -> (Prop, Prop) -> (Sequent, Sequent)
appConjR ctx (a, b) = (Seq ctx a, Seq ctx b)

appImplR : Context -> (Prop, Prop) -> Sequent
appImplR ctx (a, b) = Seq (insert a ctx) b

appConjL : Context -> (Prop, Prop, Prop) -> Sequent
appConjL ctx (a, b, c) = Seq ((insert b . insert a) ctx) c

appTopL : Context -> Prop -> Sequent
appTopL = Seq

appTopImplL : Context -> Prop -> Prop -> Sequent
appTopImplL ctx b c = Seq (insert b ctx) c

appDisjImplL : Context -> (Prop, Prop, Prop, Prop) -> Sequent
appDisjImplL ctx (d, e, b, c) =
  Seq ((insert (Impl e b) . insert (Impl d b)) ctx) c

except : Nat -> List a -> List a
except n xs = (take n xs) ++ (drop (S n) xs)

allCtxs : List a -> List (a, List a)
allCtxs [] = []
allCtxs (x :: xs) = zipWith (\y,i => (y, except i (x :: xs)))
                            (reverse (x :: xs))
                            [(length xs) .. 0]

appDisjL : Context -> (Prop, Prop, Prop) -> (Sequent, Sequent)
appDisjL ctx (a, b, c) =
  let (ctx1, ctx2) = (insert a ctx, insert b ctx) in
  (Seq ctx1 c, Seq ctx2 c)

appConjImplL : Context -> (Prop, Prop, Prop, Prop) -> Sequent
appConjImplL (Ctx g o) (d, e, b, c) =
  Seq (insert (Impl d (Impl e b)) (Ctx g o)) c

appAtomImplL : List Prop -> (Prop, Prop, Prop) -> Maybe Sequent
appAtomImplL g (p, b, c) =
  if p `elem` g then Just $ Seq (insert b (Ctx g [])) c else Nothing

appImplImplL : Context -> (Prop, Prop, Prop, Prop) -> (Sequent, Sequent)
appImplImplL (Ctx g o) (d, e, b, c) =
  let ctx1 = (insert d . insert (Impl e b)) (Ctx g o) in
  let ctx2 = insert b (Ctx g o) in
  (Seq ctx1 e, Seq ctx2 c)

mutual
  breakdown : Sequent -> Maybe Derivation
  breakdown (Seq (Ctx g o) p) =
    let ctx = Ctx g o in
    let goal = Seq (Ctx g o) p in
    case goal of
      Seq ctx Top => pure $ concludeWithTopR ctx
      Seq ctx (Conj a b) =>
        let (newgoal1, newgoal2) = appConjR ctx (a, b) in
        pure $ TwoInf ConjR !(breakdown newgoal1) !(breakdown newgoal2) goal
      Seq _ (Impl a b) =>
        let newgoal = appImplR ctx (a, b) in
        pure $ OneInf ImplR !(breakdown newgoal) goal
      Seq (Ctx g ((Conj a b) :: o)) c =>
        let newgoal = appConjL (Ctx g o) (a, b, c) in
        pure $ OneInf ConjL !(breakdown newgoal) goal
      Seq (Ctx g (Top :: o)) c =>
        let newgoal = appTopL (Ctx g o) c in
        pure $ OneInf TopL !(breakdown newgoal) goal
      Seq (Ctx g (Bot :: o)) c => pure $ concludeWithBotL (Ctx g o) c
      Seq (Ctx g ((Disj a b) :: o)) c =>
        let (newgoal1, newgoal2) = appDisjL (Ctx g o) (a, b, c) in
        pure $ TwoInf DisjL !(breakdown newgoal1) !(breakdown newgoal2) goal
      Seq (Ctx g ((Impl Top b) :: o)) c =>
        let newgoal = appTopImplL (Ctx g o) b c in
        pure $ OneInf TopImplL !(breakdown newgoal) goal
      Seq (Ctx g ((Impl Bot b) :: o)) c =>
        let newgoal = Seq (Ctx g o) c in
        pure $ OneInf TopImplL !(breakdown newgoal) goal
      Seq (Ctx g ((Impl (Conj d e) b) :: o)) c =>
        let newgoal = appConjImplL (Ctx g o) (d, e, b, c) in
        pure $ OneInf TopImplL !(breakdown newgoal) goal
      Seq (Ctx g ((Impl (Disj d e) b) :: o)) c =>
        let newgoal = appDisjImplL (Ctx g o) (d, e, b, c) in
        pure $ OneInf DisjImplL !(breakdown newgoal) goal
      Seq (Ctx g []) (Disj a b) =>
            (searchSync g (Disj a b)      >>= \x => pure (OneInf DisjL  x goal))
        <|> (breakdown (Seq (Ctx g []) a) >>= \x => pure (OneInf DisjR1 x goal))
        <|> (breakdown (Seq (Ctx g []) b) >>= \x => pure (OneInf DisjR2 x goal))
      Seq (Ctx g []) c => searchSync g c
      _ => empty

  searchSync : List Prop -> Prop -> Maybe Derivation
  searchSync g c = choiceMap (eliminate c) (allCtxs g)

  eliminate : Prop -> (Prop, List Prop) -> Maybe Derivation
  eliminate (Atom y) (Atom x, ctx) =
    if x == y
    then pure $ concludeWithInit (Ctx (Atom x :: ctx) []) (Atom y)
    else empty
  eliminate _ (Atom x, _) = empty
  eliminate c (Impl (Atom x) b, ctx) =
    let goal = Seq (Ctx ((Impl (Atom x) b) :: ctx) []) c in
    pure $ OneInf AtomImplL !(breakdown !(appAtomImplL ctx (Atom x, b, c))) goal
  eliminate c (Impl (Impl d e) b, ctx) =
    let goal = Seq (Ctx ((Impl (Impl d e) b) :: ctx) []) c in
    let (newgoal1, newgoal2) = appImplImplL (Ctx ctx []) (d, e, b, c) in
    pure $ TwoInf ImplImplL !(breakdown newgoal1) !(breakdown newgoal2) goal
  eliminate _ _ = Nothing

prove : Prop -> Maybe Derivation
prove c = breakdown (Seq (Ctx [] []) c)

-- Converting proofs to Idris terms

expFromDeriv : Derivation -> Raw
expFromDeriv (ZeroInf r s) = ?c
expFromDeriv (OneInf r d s) = ?c2
expFromDeriv (TwoInf r d1 d2 s) = ?c3

propFromType : Raw -> Prop
propFromType r = case r of
  `(~A -> ~B)     => Impl (propFromType A) (propFromType B)
  `(Pair ~A ~B)   => Conj (propFromType A) (propFromType B)
  `(Either ~A ~B) => Disj (propFromType A) (propFromType B)
  `(Unit)         => Top
  `(Void)         => Bot
  _               => Atom r

getExpr : (ty : Raw) -> Maybe Raw
getExpr ty = expFromDeriv <$> prove (propFromType ty)
