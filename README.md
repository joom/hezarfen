# Hezarfen

An Idris implementation of a theorem prover for [Roy Dyckhoff's
LJT](https://rd.host.cs.st-andrews.ac.uk/publications/jsl57.pdf), a sequent
calculus for propositional intuitionistic logic that is decidable and does
_not_ need loop checking.  Ported from [Ayberk Tosun's Standard ML
implementation](https://github.com/ayberkt/sequents).

The main goal of the project is to make use of the [elaborator
reflection](http://docs.idris-lang.org/en/latest/reference/elaborator-reflection.html).
Similar to [Lennart Augustsson's Djinn](https://github.com/augustss/djinn), a
theorem prover that generates Haskell expressions, Hezarfen generates Idris expressions.
Unlike Djinn, Hezarfen is not a standalone program, it is a library that
generates Idris expressions of the type `Raw`, one of the types used for the
inner representation of the core language of Idris. This means these
expressions can easily be spliced into your programs. Hezarfen provides a
tactic that lets you do this:

```idris
f2 : (a -> b) -> (b -> c) -> (c -> d) -> a -> d
f2 = %runElab hezarfen

f5 : (p -> q, p -> r) -> p -> (q, r)
f5 = %runElab hezarfen

demorgan1 : Not (Either p q) -> (Not p, Not q)
demorgan1 = %runElab hezarfen
```

It can also make use of your existing lemmas:

```idris
evenOrOdd : (n : Nat) -> Either (Even n) (Odd n)
... -- some definition of an existing lemma

oddOrEven : (n : Nat) -> Either (Odd n) (Even n)
oddOrEven = %runElab (add [`{evenOrOdd}] >>= hezarfen')

-- something more complex, but passing the constructors for Even and Odd
evenOrOddSS : (n : Nat) -> Either (Even (S (S n))) (Odd (S (S n)))
evenOrOddSS = %runElab (add [`{evenOrOdd}, `{EvenSS}, `{OddSS}] >>= hezarfen')
```

For details, look at [Examples.idr](https://github.com/joom/hezarfen/blob/master/Examples.idr).

## Future Work

Some support for deriving terms with type classes can be implemented, à la Djinn.

***

*hezarfen* (/hezaɾfæn/, sounds like "has are fan") is a Turkish word that means
polymath, literally "a thousand sciences".
