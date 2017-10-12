module Hezarfen

import Hezarfen.Prover
import Hezarfen.Simplify
import Hezarfen.FunDefn
import Language.Reflection.Utils

%access public export

(++) : Context -> Context -> Context
(Ctx xs ys) ++ (Ctx xs' ys') = Ctx (xs ++ xs') (ys ++ ys')

forget' : TT -> Elab Raw
forget' t = case forget t of
                 Nothing => fail [TextPart "Couldn't forget type"]
                 Just x => pure x

getCtx : Elab Context
getCtx = Ctx <$> xs <*> pure []
  where
    xs : Elab (List (TTName, Ty))
    xs = do env <- getEnv
            pure $ mapMaybe id $ map (\(n, b) =>
              MkPair n <$> forget (binderTy b)) env

getTy : TTName -> Elab (TTName, Ty)
getTy n = case !(lookupTyExact n) of
  (n, _, ty) => pure (n, !(forget' ty))

add : List TTName -> Elab Context
add xs = (flip Ctx) [] <$> traverse getTy xs

hezarfen' : Context -> Elab ()
hezarfen' c =
  do goal <- forget' (snd !getGoal)
     fill $ reduceLoop !(breakdown $ Seq (c ++ !getCtx) goal)
     solve

hezarfen : Elab ()
hezarfen = hezarfen' (Ctx [] [])

-- Generate declarations

hezarfenDecl' : TTName -> Context -> Elab ()
hezarfenDecl' n c = case !(lookupTy n) of
  [] => fail [TextPart "No type found for", NamePart n]
  [(_, _, tt)] =>
    do tt' <- normalise !getEnv tt
       -- normalization is necessary to change `Not p` into `p -> Void`, etc
       ty <- forget' tt'
       tm <- breakdown (Seq (c ++ !getCtx) ty)
       let proofTerm = reduceLoop tm
       proofDefn <- definitionize n proofTerm
       defineFunction proofDefn
  _ => fail [TextPart "Ambiguity: multiple types found for", NamePart n]

||| Generates a function definition for a previously undefined name.
||| Note that there should already be a type signature for that name.
||| Example usage:
||| ```
||| f : a -> a
||| %runElab (hezarfenDecl `{f})
||| ```
hezarfenDecl : TTName -> Elab ()
hezarfenDecl n = hezarfenDecl' n (Ctx [] [])
