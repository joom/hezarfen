module Hezarfen

import Hezarfen.Prover
import Language.Reflection.Utils

hezarfen : Elab ()
hezarfen = case !(forget . snd <$> getGoal) of
  Nothing => fail [TextPart "Internal error"]
  Just ty => case getExpr ty of
                Nothing => fail [TextPart "Couldn't find a proof"]
                Just tm => fill tm *> solve
