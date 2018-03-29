||| Hacky and rudimentary hint database for Idris using elaborator reflection.
||| You can now write tactics that does `getHints`
||| and try to prove the goal with the lemmas there.
module Hezarfen.Hint
import Language.Reflection.Utils
%language ElabReflection
%access public export

||| The hint to pass the machine generated names. Note that the word hint here
||| is used literally, not in the theorem prover sense.
mnString : String
mnString = "hint"

||| The number from which we can creating machine generated variables.
startNumber : Int
startNumber = 0

||| Create a metavariable name that will only be used in compile time.
hintName : Int -> TTName
hintName i = NS (SN (MetaN (UN mnString) (MN i mnString))) ["Hint", "Hezarfen"]

||| Learn the number of the last hint, if it exists at all.
learnLastHint : Elab (Maybe Int)
learnLastHint = up startNumber
  where up : Int -> Elab (Maybe Int)
        up i = (do lookupTyExact (hintName i) ; up (i + 1))
          <|> pure (if i == startNumber then Nothing else Just (i - 1))

||| Adds the given name to the hint database.
newHint : TTName -> Elab ()
newHint n = do
  let new = hintName (fromMaybe startNumber ((+ 1) <$> !learnLastHint))
  declareType (Declare new [] (Var `{TTName}))
  defineFunction (DefineFun new [MkFunClause (Var new) (quote n)])

reifyString : TT -> Elab String
reifyString (TConst (Str s)) = pure s
reifyString t = fail [ TextPart "Failed to reify", TermPart t
                     , TextPart "as a" , NamePart `{{String}}]

reifyInt : TT -> Elab Int
reifyInt (TConst (I i)) = pure i
reifyInt t = fail [ TextPart "Failed to reify", TermPart t
                  , TextPart "as an" , NamePart `{{Int}}]

reifyList : (TT -> Elab a) -> TT -> Elab (List a)
reifyList f `(Prelude.List.Nil {elem=~a}) = pure []
reifyList f `(Prelude.List.(::) {elem=~a} ~x ~xs) =
  (::) <$> f x <*> reifyList f xs
reifyList f t = fail [ TextPart "Failed to reify", TermPart t
                     , TextPart "as a" , NamePart `{List}]

reifyTTName : TT -> Elab TTName
reifyTTName `(UN ~x) = UN <$> reifyString x
reifyTTName `(NS ~n ~xs) = NS <$> reifyTTName n <*> reifyList reifyString xs
reifyTTName `(MN ~i ~s) = MN <$> reifyInt i <*> reifyString s
reifyTTName t = fail [ TextPart "Failed to reify", TermPart t
                     , TextPart "as a", NamePart `{TTName}]

reifyHint : Int -> Elab TTName
reifyHint i = do
    DefineFun _ [MkFunClause _ t] <- lookupFunDefnExact (hintName i)
    reifyTTName t

||| The `Elab` action to get the names of all the hints.
getHints : Elab (List TTName)
getHints = maybe (pure []) go !learnLastHint
  where go : Int -> Elab (List TTName)
        go i = if i < startNumber then pure []
                                  else (::) <$> reifyHint i <*> go (i - 1)

-- Defining Coq-style syntax for hints.
decl syntax "hint" {n} = %runElab (newHint `{n})
