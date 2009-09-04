Include "../../../guru-lang/lib/mult.g".

Define proof : Forall(x : nat) . { (le Z x) = tt } :=
  foralli(n:nat).
    case n with
      Z =>  trans cong (le Z *) n_eq
                join (le Z Z) tt
    | S n' => trans cong (le Z *) n_eq
                    join (le Z (S n')) tt
    end.
