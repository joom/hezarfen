module Examples

import Hezarfen
import Hezarfen.Prover

%language ElabReflection

f1 : (a -> b) -> (b -> c) -> a -> c
f1 = %runElab hezarfen

f2 : (a -> b) -> (b -> c) -> (c -> d) -> a -> d
f2 = %runElab hezarfen

f3 : Either a (Either b c) -> Either (Either a b) c
f3 = %runElab hezarfen

f4 : (a, b, c) -> (c, b, a)
f4 = %runElab hezarfen

f5 : (p -> q, p -> r) -> p -> (q, r)
f5 = %runElab hezarfen

f6 : (((a -> b) -> c) -> d) -> ((a -> b) -> c) -> (a -> b) -> d
f6 = %runElab hezarfen

demorgan1 : Not (Either p q) -> (Not p, Not q)
demorgan1 = %runElab hezarfen

demorgan2 : (Not p, Not q) -> Not (Either p q)
demorgan2 = %runElab hezarfen

demorgan3 : Either (Not p) (Not q) -> Not (p, q)
demorgan3 = %runElab hezarfen

-- This one is classical so it cannot be proved by Hezarfen
-- demorgan4 : Not (p, q) -> Either (Not p) (Not q)
-- demorgan4 = %runElab hezarfen

noContradiction : Not (p , Not p)
noContradiction = %runElab hezarfen

-- Examples with default values for some types

nat : Nat
nat = %runElab (add [`{Z}] >>= hezarfen')

bool : (Bool, a -> a)
bool = %runElab (add [`{True}] >>= hezarfen')

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
oddOrEven = %runElab (add [`{evenOrOdd}] >>= hezarfen')
