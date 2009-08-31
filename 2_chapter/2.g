Include "../../../guru-lang/lib/plus.g".

Define plus' : Fun(n m:nat).nat :=
  fun plus' (n m:nat):nat.
    match m with 
      Z => n
    | S m' => (S (plus' n m'))
    end.

% Any natural number plus 0 is the same number
Define plus'_n_zero_is_n: 
  Forall(n:nat). {(plus' n zero) = n} :=
    foralli(n:nat). join (plus' n zero) n.
  
Classify join (plus' zero zero) zero.
Classify join (plus' zero one) one.
Classify join (plus' two three) five.
Classify join (plus' five three) eight.
