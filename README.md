# Hezarfen

An Idris implementation of a theorem prover for [Roy Dyckhoff's
LJT](https://scholar.google.com/scholar?cluster=14155439887209124225), a sequent
calculus for propositional intuitionistic logic that is decidable and does
_not_ need loop checking. Initially ported from [Ayberk Tosun's Standard ML
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
f2 = %runElab hezarfenExpr
```

However, instead of creating proof terms, you can also create definitions that
are more readable when you print their definitions.

```idris
f2 : (a -> b) -> (b -> c) -> (c -> d) -> a -> d
%runElab (hezarfen `{f2})
```

Or with the more readable syntax extension:

```idris
demorgan3 : Either (Not p) (Not q) -> Not (p, q)
derive demorgan3

contrapositive : (p -> q) -> (Not q -> Not p)
derive contrapositive
```

It can also make use of your existing lemmas:

```idris
evenOrOdd : (n : Nat) -> Either (Even n) (Odd n)
... -- some definition of an existing lemma

oddOrEven : (n : Nat) -> Either (Odd n) (Even n)
%runElab (hezarfen' `{oddOrEven} !(add [`{evenOrOdd}]))

-- something more complex, but passing the constructors for Even and Odd
-- using the more readable syntax
evenOrOddSS : (n : Nat) -> Either (Even (S (S n))) (Odd (S (S n)))
obtain evenOrOddSS from [`{evenOrOdd}, `{EvenSS}, `{OddSS}]
```

We also have a Coq-style hint database system that lets us keep a list of hint names that will be used to prove theorems. To use the hints in proofs, change `derive` to `derive'` and `obtain` to `obtain'`. Then the names in the hint database will be automatically added to the context in which the theorem prover runs.

```idris
hint evenOrOdd
hint EvenSS
hint OddSS

evenOrOddSS : (n : Nat) -> Either (Even (S (S n))) (Odd (S (S n)))
derive' evenOrOddSS
```

The even/odd example is beyond the logic Hezarfen is trying to decide. `Even n` and `Even (S (S n))` happen to be one function away, namely `EvenSS`.

Hezarfen attempts to prove a tiny bit more than propositional intuitionistic logic,
especially when it comes to equalities and `Dec`.
Even though this part is a bit ad hoc, it can currently prove things of this nature:

```idris
eqDec : x = y -> Dec (y = x)
derive eqDec

decCongB : x = y -> Dec (not x = not y)
derive decCongB
```

For details, look at [Examples.idr](https://github.com/joom/hezarfen/blob/master/Examples.idr).

## Edit-Time Tactics

The original purpose of Hezarfen was to be a part of a master's thesis on
"edit-time tactics", meaning that we would be able to run it from the editor.
Then it would be an alternative to the built-in proof search in Idris.
[Here](http://cattheory.com/editTimeTacticsDraft.pdf) is the draft of the
thesis. And below you can see how it works in the editor:

[![Screencast of how Hezarfen works in Emacs](https://asciinema.org/a/rrwboxAr2VdiUQsZov0RDinJw.png)](https://asciinema.org/a/rrwboxAr2VdiUQsZov0RDinJw)

The feature that allows this has not landed on the Idris compiler or the Idris
mode yet, but it should be merged soon!

## Future Work

Some support for deriving terms with type classes can be implemented, à la Djinn.

One of the end goals of Hezarfen is to generate proofs that are easy to read:

* Fresh variable names should be readable. Currently there is a hacky `fresh` function in [Prover.idr](https://github.com/joom/hezarfen/blob/master/Hezarfen/Prover.idr) that does that.
* There is [already some work on simplifying the proof terms](https://github.com/joom/hezarfen/blob/master/Hezarfen/Simplify.idr) generated by Hezarfen. There are some tricks Hezarfen can learn from Haskell's [pointfree](https://hackage.haskell.org/package/pointfree) package. ([web version](http://pointfree.io/))
* Currently Hezarfen primarily generates expressions as proofs. However when we are writing functions, we often use function definitions instead of lambda terms, and we pattern match on pairs in the function definition, instead of writing `let a = fst p in let b = snd p in ...` or `case p of (x, y) => ...` to do projections. There is [some work](https://github.com/joom/hezarfen/blob/master/Hezarfen/FunDefn.idr) on translating these proof terms to readable function definitions.

The definition it generates looks like this:
```idris
> :printdef contrapositive
contrapositive : (p -> q) -> Not q -> Not p
contrapositive c d = void . d . c
```

As opposed to proof term:
```idris
contrapositive : (p -> q) -> Not q -> Not p
contrapositive = \i20, j20 => void . j20 . i20
```

***

*hezarfen* (/hezaɾfæn/, sounds like "has are fan") is a Turkish word that means
polymath, literally "a thousand sciences".
