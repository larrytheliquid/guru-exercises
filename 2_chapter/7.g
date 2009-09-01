Include "../../../guru-lang/lib/plus.g".

Define double := fun(x:nat).(plus x x).

Define iter : Fun(n:nat)(f:Fun(x:nat).nat)(m:nat).nat :=
  fun iter(n:nat)(f:Fun(x:nat).nat)(m:nat):nat.
    match n with
      Z => m
    | S n' => (f (iter n' f m))
    end.

Classify join (iter Z double two) two.
% Proving properties about the base case seems repeatedly easy
Classify foralli(n:nat)(f:Fun(x:nat).nat).
           join (iter Z f n) n.
Classify join (iter two double two) eight.
Classify join (iter three double three) (double (double six)).
