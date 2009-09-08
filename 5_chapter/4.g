Include "../../../guru-lang/lib/mult.g".

Define proof : Forall(x y:nat)(u:{(mult y (S x)) = Z}). { y = Z } :=
foralli(x:nat).
induction(y:nat) return Forall(u:{(mult y (S x)) = Z}). { y = Z } with
  Z => foralli(u:{(mult y (S x)) = Z}). y_eq
| S y' => foralli(u:{(mult y (S x)) = Z}).
          contra
          trans symm u
          trans cong (mult * (S x)) y_eq
          trans join (mult (S y') (S x)) (S (plus x (mult y' (S x))))
          clash (S (plus x (mult y' (S x)))) Z
          { y = Z }
end.
