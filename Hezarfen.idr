module Hezarfen

import Hezarfen.Prover
import Language.Reflection.Utils

public export
hezarfen : Elab ()
hezarfen = case !(forget . snd <$> getGoal) of
  Nothing => fail [TextPart "Internal error"]
  Just ty => fill !(prove ty) *> solve
