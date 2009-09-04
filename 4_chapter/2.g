Include "../../../guru-lang/lib/mult.g".

Define proof : Forall(x y z:nat). { (plus x (plus y z)) = (plus z (plus y x)) } :=
foralli(x y z:nat).
  trans cong (plus x *) [plus_comm y z]
  trans [plus_comm x (plus z y)]
        [plus_assoc z y x].
