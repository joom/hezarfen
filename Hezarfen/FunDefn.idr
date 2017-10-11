module Hezarfen.FunDefn

import Language.Reflection.Utils

%access public export

||| Currently does not do anything smart.
definitionize : TTName -> Raw -> Elab (FunDefn Raw)
definitionize n t =
  pure $ DefineFun n [MkFunClause (Var n) t]
