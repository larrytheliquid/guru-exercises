Include "../../../guru-lang/lib/plus.g".

Define plus' : Fun(n m:nat).nat :=
  fun plus' (n m:nat):nat.
    match m with 
      Z => n
    | S m' => (S (plus' n m'))
    end.

Classify join (plus' zero zero) zero.
Classify join (plus' zero one) one.
Classify join (plus' two three) five.
Classify join (plus' five three) eight.

Interpret (plus' two three).
