Include "../../../guru-lang/lib/mult.g".

Define proof : Forall(n:nat). { (mult n Z) = Z} :=
induction(n:nat) return { (mult n Z) = Z } with
  Z => trans cong (mult * Z) n_eq  
             join (mult Z Z) Z
| S n' => trans cong (mult * Z) n_eq
          trans join (mult (S n') Z) (mult n' Z)
                [n_IH n']
end.
