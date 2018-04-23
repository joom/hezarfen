module Examples

import Hezarfen
import Hezarfen.Hint
import Hezarfen.Prover
import Hezarfen.Definitions

%language ElabReflection
%default total

-- You can generate proofs as expressions, but it's better to
-- generate definitions instead since they are more readable.

f1 : (a -> b) -> (b -> c) -> a -> c
f1 = %runElab hezarfenExpr

-- `f1` is generated as an expression, the rest will be definitions.

f1' : (a -> b) -> (b -> c) -> a -> c
%runElab (hezarfen `{f1'})

-- You can also use the `derive` syntax.

f2 : (a -> b) -> (b -> c) -> (c -> d) -> a -> d
derive f2

f3 : Either a (Either b c) -> Either (Either a b) c
derive f3

f4 : (a, b, c) -> (c, b, a)
derive f4

f5 : (p -> q, p -> r) -> p -> (q, r)
derive f5

f6 : (((a -> b) -> c) -> d) -> ((a -> b) -> c) -> (a -> b) -> d
derive f6

myFst : (a, b) -> a
derive myFst

mySnd : (a, b) -> b
derive mySnd

demorgan1 : Not (Either p q) -> (Not p, Not q)
derive demorgan1

demorgan2 : (Not p, Not q) -> Not (Either p q)
derive demorgan2

demorgan3 : Either (Not p) (Not q) -> Not (p, q)
derive demorgan3

-- This one is classical so it cannot be proved by Hezarfen
-- demorgan4 : Not (p, q) -> Either (Not p) (Not q)
-- demorgan4 = %runElab hezarfen

noContradiction : Not (p , Not p)
derive noContradiction

contrapositive : (p -> q) -> (Not q -> Not p)
derive contrapositive

-- Examples with default values for some types

nat : Nat
%runElab (hezarfen' `{nat} !(add [`{Z}]))

-- Using the more readable syntax

bool : (Bool, a -> a)
obtain bool from [`{True}]

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

-- You can also use a hint database
hint evenOrOdd
hint EvenSS
hint OddSS

oddOrEven : (n : Nat) -> Either (Odd n) (Even n)
derive' oddOrEven -- derive using hints

evenOrOddSS : (n : Nat) -> Either (Even (S (S n))) (Odd (S (S n)))
derive' evenOrOddSS

decUnit : Dec Unit
derive decUnit

decVoid : Dec Void
derive decVoid

swapEither : Either a b -> Either b a
derive swapEither

swapDec : Dec a -> Dec (Not a)
derive swapDec

notDec : Not a -> Dec a
derive notDec

decNotNot : Dec p -> (Not p -> Void) -> p
derive decNotNot

-- Equalities
eq1 : x = x
derive eq1

eq2 : True = True
derive eq2

-- Treat equalities as an atom if it's not obviously solvable
eq3 : (x = y) -> (x = y)
derive eq3

eq4 : True = False -> False = True
derive eq4

eq5 : x = y -> y = x
derive eq5

eqDec : x = y -> Dec (y = x)
derive eqDec

eqEither : Either (x = y) (y = z) -> Either (z = y) (y = x)
derive eqEither

congS : x = y -> S x = S y
derive congS

decCongB : x = y -> Dec (not x = not y)
derive decCongB

twoToThree : (x = y, y = z) -> (z = y, y = y, y = x)
derive twoToThree

doesntLoop : (a -> b) -> (b -> a) -> a -> b
derive doesntLoop
