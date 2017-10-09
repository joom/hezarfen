module Hezarfen

import Hezarfen.Prover
import Language.Reflection.Utils

%access public export

(++) : Context -> Context -> Context
(Ctx xs ys) ++ (Ctx xs' ys') = Ctx (xs ++ xs') (ys ++ ys')

getCtx : Elab Context
getCtx = Ctx <$> xs <*> pure []
  where
    xs : Elab (List (TTName, Ty))
    xs = do env <- getEnv
            pure $ mapMaybe id $ map (\(n, b) =>
              MkPair n <$> forget (binderTy b)) env

getTy : TTName -> Elab (TTName, Ty)
getTy n = case !(lookupTyExact n) of
  (n, _, ty) => case forget ty of
                     Nothing => empty
                     Just ty' => pure (n, ty')

add : List TTName -> Elab Context
add xs = (flip Ctx) [] <$> traverse getTy xs

hezarfen' : Context -> Elab ()
hezarfen' c = case !(forget . snd <$> getGoal) of
  Nothing => fail [TextPart "Couldn't get the goal"]
  Just ty => fill !(breakdown $ Seq (c ++ !getCtx) ty) *> solve

hezarfen : Elab ()
hezarfen = hezarfen' (Ctx [] [])
