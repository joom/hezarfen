module Prover

import Language.Reflection.Utils
%access public export

||| A hacky way to convert any integer to a string.
||| It initially tries to get a single character string,
||| but if the number is too high then it adds some number afterwards.
||| Does not generate good variable names for negative numbers.
intToStr : Int -> String
intToStr i = let d = i `div` 25 in
             pack [chr (97 + (i `mod` 25))] ++
             (if d == 0 then "" else show d)

||| A hacky way to generate fresh variable names that are readable.
||| It assumes that the `gensym` function will return a `MN` that holds
||| an integer at least 101, which is currently the case, but
||| this function needs to rewritten if that changes in the future.
fresh : Elab TTName
fresh =
  do MN i "x" <- gensym "x"
        | _ => fail [TextPart "Bug in ", NamePart `{gensym}]
     when (i < 101) (fail [TextPart "Bug in", NamePart `{fresh}])
     let n = UN $ intToStr (i - 101)
     case !(lookupTy n) of
       [] => pure n
       _ => fresh -- we will eventually get a fresh name

Ty : Type
Ty = Raw

Tm : Type
Tm = Raw

data Context = Ctx (List (TTName, Ty)) (List (TTName, Ty))

ctxPart : Context -> ErrorReportPart
ctxPart (Ctx xs ys) =
    SubReport $ [TextPart "(", g xs, TextPart "||",  g ys, TextPart ")"]
  where
    f : (TTName, Ty) -> ErrorReportPart
    f (n, t) = SubReport [TextPart "(", NamePart n,
                          TextPart ":", RawPart t, TextPart ")"]
    g : List (TTName, Ty) -> ErrorReportPart
    g l = SubReport $ intersperse (TextPart ",") (map f l)

data Sequent = Seq Context Ty

isAtom : Ty -> Bool
isAtom `(Either ~_ ~_) = False
isAtom `(Pair ~_ ~_) = False
isAtom `(~_ -> ~_) = False
isAtom `(Unit) = False
isAtom `(Void) = False
isAtom _ = True

insert : TTName -> Ty -> Context -> Context
insert n p (Ctx g o) = case p of
  `((~a -> ~b) -> ~d) => Ctx ((n, p) :: g) o
  `(~a -> ~b) => if isAtom a then Ctx ((n, p) :: g) o else Ctx g ((n, p) :: o)
  _           => if isAtom p then Ctx ((n, p) :: g) o else Ctx g ((n, p) :: o)

appConjR : Context -> (Ty, Ty) -> (Sequent, Sequent)
appConjR ctx (a, b) = (Seq ctx a, Seq ctx b)

appImplR : TTName -> Context -> (Ty, Ty) -> Sequent
appImplR n ctx (a, b) = Seq (insert n a ctx) b

appConjL : Context -> (Ty, Ty, Ty) -> Elab (TTName, TTName, Sequent)
appConjL ctx (a, b, c) =
  let (n1, n2) = (!fresh, !fresh) in
  pure (n1, n2, Seq ((insert n2 b . insert n1 a) ctx) c)

appTopImplL : Context -> Ty -> Ty -> Elab (TTName, Sequent)
appTopImplL ctx b c = do n <- fresh ; pure (n, Seq (insert n b ctx) c)

appDisjImplL : Context -> (Ty, Ty, Ty, Ty) -> Elab (TTName, TTName, Sequent)
appDisjImplL ctx (d, e, b, c) =
  let (n1, n2) = (!fresh, !fresh) in
  pure (n1, n2, Seq ((insert n2 `(~e -> ~b) . insert n1 `(~d -> ~b)) ctx) c)

except : Nat -> List a -> List a
except n xs = (take n xs) ++ (drop (S n) xs)

allCtxs : List a -> List (a, List a)
allCtxs [] = []
allCtxs (x :: xs) = zipWith (\y,i => (y, except i (x :: xs)))
                            (reverse (x :: xs)) [(length xs) .. 0]

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

appAtomImplL : List (TTName, Ty) -> (Ty, Ty, Ty)
            -> Elab (TTName, Sequent, TTName)
appAtomImplL g (p, b, c) =
  do n <- fresh
     case find (\(m, x) => x == p) g of
        Just (m, x) => pure (n, Seq (insert n b (Ctx g [])) c, m)
        _ => fail [TextPart "Not in context in appAtomImplL"]

appImplImplL : Context -> (Ty, Ty, Ty, Ty)
            -> Elab ((TTName, TTName, Sequent), (TTName, Sequent))
appImplImplL (Ctx g o) (d, e, b, c) =
  let (n1, n2, n3) = (!fresh, !fresh, !fresh) in
  let ctx1 = (insert n1 d . insert n2 `(~e -> ~b)) (Ctx g o) in
  let ctx2 = insert n3 b (Ctx g o) in
  pure ((n1, n2, Seq ctx1 e), (n3, Seq ctx2 c))

hErr : String -> Sequent -> Elab a
hErr s (Seq ctx g) =
  fail [ TextPart ("No rule applies in " ++ s ++ " with goal")
       , RawPart g
       , TextPart "with context "
       , ctxPart ctx]

mutual
  breakdown : Sequent -> Elab Tm
  breakdown goal = case goal of
    -- Introduce as many lambdas as soon as possible
    -- This way it's easier to collapse them into function definitions.
    Seq ctx (RBind orig (Pi a _) b) =>
      let newn = !fresh in
      -- If the Pi type has __pi_arg in the beginning, that means it wasn't
      -- explicitly named, hence not used later in the type.
      -- Therefore it is safe it give it a fresh, readable name
      -- Explicitly named Pi arguments can be used in predicates,
      -- which we only handle as atoms, so it's better to keep those names
      -- as they are provided
      let n = case orig of
                   UN s => if isPrefixOf "__pi_arg" s then newn else orig
                   _ => newn in
      let newgoal = appImplR n ctx (a, b) in
      let tm = !(breakdown newgoal) in
      pure $ RBind n (Lam a) tm
    Seq ctx `(Unit) => pure `(MkUnit)
    Seq (Ctx g ((n, `(Void)) :: o)) c =>
      pure `(void {a=~c} ~(Var n))
    -- Unpack the pairs as soon as possible, so that they happen before
    -- the `either`s, which allows us to incorporate them into patterns
    -- in definitions easily.
    Seq (Ctx g ((p, `(Pair ~a ~b)) :: o)) c =>
      let (n1, n2, newgoal) = !(appConjL (Ctx g o) (a, b, c)) in
      pure $ RBind n1 (Let a `(Prelude.Basics.fst {a=~a} {b=~b} ~(Var p)))
           $ RBind n2 (Let b `(Prelude.Basics.snd {a=~a} {b=~b} ~(Var p)))
             !(breakdown newgoal)
    Seq ctx `(Pair ~a ~b) =>
      let (newgoal1, newgoal2) = appConjR ctx (a, b) in
      let (tm1, tm2) = (!(breakdown newgoal1), !(breakdown newgoal2)) in
      pure `(MkPair {A=~a} {B=~b} ~tm1 ~tm2)
    Seq (Ctx g ((_, `(Unit)) :: o)) c => breakdown (Seq (Ctx g o) c)
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
    Seq (Ctx g []) `(Either ~a ~b) =>
         (searchSync g `(Either ~a ~b))
     <|> (do t <- breakdown (Seq (Ctx g []) a); pure `(Left {a=~a} {b=~b} ~t))
     <|> (do t <- breakdown (Seq (Ctx g []) b); pure `(Right {a=~a} {b=~b} ~t))
     <|> hErr "breakdown either case" goal
    Seq (Ctx g []) c => searchSync g c
    _ => hErr "breakdown" goal

  searchSync : List (TTName, Ty) -> Ty -> Elab Tm
  searchSync g c = choiceMap (eliminate c) (allCtxs g)
               <|> hErr "searchSync" (Seq (Ctx g []) c)

  eliminate : Ty -> ((TTName, Ty), List (TTName, Ty)) -> Elab Ty
  eliminate c ((n, `((~d -> ~e) -> ~b)), ctx) =
    let ((a1, a2, newgoal1), (a3, newgoal2)) =
      !(appImplImplL (Ctx ctx []) (d, e, b, c)) in
    let (tm1, tm2) = (!(breakdown newgoal1), !(breakdown newgoal2)) in
    let n' = !fresh in
    let q = RBind a2 (Lam `(~e -> ~b)) (RBind a1 (Lam d) tm1) in
    pure $ RApp (RBind a3 (Lam b) tm2) $
             RApp (Var n) $ RApp q $ RBind n' (Lam e)
               (RApp (Var n) (RBind !fresh (Lam d) (Var n')))
  eliminate c ((n, `(~x -> ~b)), ctx) =
    if not (isAtom x)
    then fail [RawPart x, TextPart "is not an atom"]
    else let (n', newgoal, m) = !(appAtomImplL ctx (x, b, c)) in
         let tm = !(breakdown newgoal) in
         pure $ RApp (RBind n' (Lam b) tm) (RApp (Var n) (Var m))
  eliminate y ((n2, x), ctx) =
    if x == y && isAtom y && isAtom x
    then pure $ Var n2
    else fail [TextPart "Atom comparison failed in eliminate"]
  eliminate _ _ = fail [TextPart "No rule applies in eliminate"]

prove : Ty -> Elab Tm
prove c = breakdown (Seq (Ctx [] []) c)
