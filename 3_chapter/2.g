Include "../../../guru-lang/lib/mult.g".

Define mult_zero_is_zero : Forall(x:nat). { (mult Z x) = Z } :=
  foralli(x:nat). join (mult Z x) Z.
