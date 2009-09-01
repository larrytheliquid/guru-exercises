Include "../../../guru-lang/lib/mult.g".

Define proof : Forall(x:nat)(y:nat) . { (lt Z (plus (S x) y)) = tt } :=
  foralli(x y:nat). join (lt Z (plus (S x) y)) tt.
