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

hezarfenExpr' : Context -> Elab ()
hezarfenExpr' c =
  do goal <- forget' (snd !getGoal)
     fill !(reduceLoop !(breakdown False $ Seq (c ++ !getCtx) goal))
     solve

hezarfenExpr : Elab ()
hezarfenExpr = hezarfenExpr' (Ctx [] [])

-- Generate declarations

hezarfen' : TTName -> Context -> Elab ()
hezarfen' n c = case !(lookupTy n) of
  [] => fail [TextPart "No type found for", NamePart n]
  [(_, _, tt)] =>
    do tt' <- normalise !getEnv tt
       -- normalization is necessary to change `Not p` into `p -> Void`, etc
       ty <- forget' tt'
       tm <- breakdown False (Seq (c ++ !getCtx) ty)
       proofTerm <- reduceLoop tm
       proofDefn <- definitionize n proofTerm
       defineFunction proofDefn
  _ => fail [TextPart "Ambiguity: multiple types found for", NamePart n]

||| Generates a function definition for a previously undefined name.
||| Note that there should already be a type signature for that name.
||| Example usage:
||| ```
||| f : a -> a
||| derive f
||| ```
hezarfen : TTName -> Elab ()
hezarfen n = hezarfen' n (Ctx [] [])

||| Returns reflected proof term directly
hezarfenTT : (shouldReduce : Bool) -> TTName -> Elab TT
hezarfenTT b n =
  do (_, _, ty) <- lookupTyExact n
     pf <- prove !(forget' ty)
     pf' <- (if b then reduceLoop else pure) pf
     env <- getEnv
     fst <$> check env pf'

decl syntax "derive" {n} = %runElab (hezarfen `{n})

decl syntax "obtain" {n} "from" [xs] = %runElab (hezarfen' `{n} !(add xs))
