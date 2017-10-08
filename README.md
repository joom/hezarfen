# Hezarfen

(work in progress)

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
expressions can easily be spliced into your programs. Hezarfen will eventually
provide a tactic that lets you do this:

```idris
p : (a -> b) -> (c -> d) -> a -> d
p = %runElab hezarfen
```

***

*hezarfen* is a Turkish word that means polymath, literally "a thousand sciences".
