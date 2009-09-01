Include "../../../guru-lang/lib/nat.g".

Define not_equal :=
  fun not_equal(n m:nat):bool.
    match n with 
      Z => match m with
             Z => ff
           | S m' => tt
         end
    | S n' => match m with
                Z => tt
              | S m' => (not_equal n' m')
              end
    end.

Classify join (not_equal Z Z) ff.
Classify join (not_equal one Z) tt.
Classify join (not_equal Z three) tt.
Classify join (not_equal one three) tt.
