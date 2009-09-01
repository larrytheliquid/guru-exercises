Include "../../../guru-lang/lib/mult.g".

Define satisfies :=
  fun satisfies(x:nat)(f:Fun(x:nat).bool):nat.
    match (f x) with
      ff => (satisfies (S x) f)
    | tt => x
    end.

Define first :=
  fun(f:Fun(x:nat).bool).
    (satisfies Z f).

Interpret (first fun(x:nat). (eqnat (mult x x) nine)).
