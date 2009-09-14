Include trusted "../../../guru-lang/lib/list.g".

Define fill_total : Forall(A:type)(a:A)(n:nat). Exists(z:<list A>). { (fill a n) = z } :=
foralli(A:type)(a:A).
induction(n:nat) return Exists(z:<list A>). { (fill a n) = z } with
  Z => existsi (nil A) { (fill a n) = * }
       trans cong (fill a *) n_eq
       join (fill a Z) nil
| S n' => existse [n_IH n']
          foralli(z':<list A>)(u:{ (fill a n') = z' }).
          existsi (cons A a z') { (fill a n) = * }
          trans cong (fill a *) n_eq
          trans join (fill a (S n')) (cons a (fill a n'))
          cong (cons a *) u
end.

Total fill fill_total.
