module Hezarfen.Definitions

%access public export

||| Simply-typed eliminator for `Dec`
dec : {a, c : Type} -> Lazy (a -> c) -> Lazy ((a -> Void) -> c) -> Dec a -> c
dec f _ (Yes prf) = f prf
dec _ g (No contra) = g contra
