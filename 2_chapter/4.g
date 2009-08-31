Include "3.g".
Include "../../../guru-lang/lib/nat.g".

Define nth_day :=
  fun nth_day(d:day)(n:nat):day.
    match n with
      Z => d
    | S n' => (nth_day (next_day d) n')
    end.

Classify join (nth_day Monday two) Wednesday.
Classify join (nth_day Saturday five) Thursday.
