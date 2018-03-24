module Examples

import Hezarfen
import Hezarfen.Prover
import Hezarfen.Definitions

%language ElabReflection
%default total

-- You can generate proofs as expressions, but it's better to
-- generate definitions instead since they are more readable.

f1 : (a -> b) -> (b -> c) -> a -> c
f1 = %runElab hezarfenExpr

-- `f1` is generated as an expression, the rest will be definitions.

f2 : (a -> b) -> (b -> c) -> (c -> d) -> a -> d
%runElab (hezarfen `{f2})

f3 : Either a (Either b c) -> Either (Either a b) c
%runElab (hezarfen `{f3})

f4 : (a, b, c) -> (c, b, a)
%runElab (hezarfen `{f4})

f5 : (p -> q, p -> r) -> p -> (q, r)
%runElab (hezarfen `{f5})

f6 : (((a -> b) -> c) -> d) -> ((a -> b) -> c) -> (a -> b) -> d
%runElab (hezarfen `{f6})

demorgan1 : Not (Either p q) -> (Not p, Not q)
%runElab (hezarfen `{demorgan1})

demorgan2 : (Not p, Not q) -> Not (Either p q)
%runElab (hezarfen `{demorgan2})

demorgan3 : Either (Not p) (Not q) -> Not (p, q)
%runElab (hezarfen `{demorgan3})

-- This one is classical so it cannot be proved by Hezarfen
-- demorgan4 : Not (p, q) -> Either (Not p) (Not q)
-- demorgan4 = %runElab hezarfen

noContradiction : Not (p , Not p)
%runElab (hezarfen `{noContradiction})

contrapositive : (p -> q) -> (Not q -> Not p)
%runElab (hezarfen `{contrapositive})

-- Examples with default values for some types

nat : Nat
%runElab (add [`{Z}] >>= hezarfen' `{nat})

bool : (Bool, a -> a)
%runElab (add [`{True}] >>= hezarfen' `{bool})

-- Using a lemma
data Even : Nat -> Type where
  EvenZ : Even Z
  EvenSS : Even n -> Even (S (S n))

data Odd : Nat -> Type where
  Odd1 : Odd 1
  OddSS : Odd n -> Odd (S (S n))

evenOrOdd : (n : Nat) -> Either (Even n) (Odd n)
evenOrOdd Z = Left EvenZ
evenOrOdd (S Z) = Right Odd1
evenOrOdd (S (S n)) = case evenOrOdd n of
                           Left ev => Left $ EvenSS ev
                           Right o => Right $ OddSS o

oddOrEven : (n : Nat) -> Either (Odd n) (Even n)
%runElab (add [`{evenOrOdd}] >>= hezarfen' `{oddOrEven})

evenOrOddSS : (n : Nat) -> Either (Even (S (S n))) (Odd (S (S n)))
%runElab (add [`{evenOrOdd}, `{EvenSS}, `{OddSS}] >>= hezarfen' `{evenOrOddSS})

decUnit : Dec Unit
%runElab (hezarfen `{decUnit})

decVoid : Dec Void
%runElab (hezarfen `{decVoid})

swapEither : Either a b -> Either b a
%runElab (hezarfen `{swapEither})

swapDec : Dec a -> Dec (Not a)
%runElab (hezarfen `{swapDec})

-- Equalities
eq1 : x = x
%runElab (hezarfen `{eq1})
