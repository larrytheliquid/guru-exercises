Include "../../../guru-lang/lib/pow.g".

Define proof : Forall(b e : nat)(u:{ b != Z }). { (le (S Z) (pow b e)) = tt } :=
foralli(b e:nat)(u:{ b != Z }).
case (pow b e) by v ignore with
  Z => contra
       trans symm v
       [pow_not_zero b e u]
       { (le (S Z) (pow b e)) = tt }
| S x => trans cong (le (S Z) *) v
         trans [S_le_S Z x]
         [leZ x]
end.
