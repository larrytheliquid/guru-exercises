Include "../../../guru-lang/lib/mult.g".

Define proof : Forall(x y z :nat). { (mult (plus x y) z) = (plus (mult x z) (mult y z)) } :=
induction(x:nat) return Forall(y z :nat). { (mult (plus x y) z) = (plus (mult x z) (mult y z)) } with
  Z => 
  foralli(y z:nat).
  trans cong (mult (plus * y) z) x_eq
  trans join (mult (plus Z y) z) (plus (mult Z z) (mult y z))
        cong (plus (mult * z) (mult y z)) symm x_eq

| S x' =>
  foralli(y z:nat).
  trans cong (mult (plus * y) z) x_eq
  trans join (mult (plus (S x') y) z) (plus z (mult (plus x' y) z))
  trans cong (plus z *) [x_IH x' y z]
  trans symm [plus_assoc z (mult x' z) (mult y z)]
  trans join (plus (plus z (mult x' z)) (mult y z))
             (plus (mult (S x') z) (mult y z))
        cong (plus (mult * z) (mult y z)) symm x_eq
end.  
