Include trusted "../../../guru-lang/lib/list.g".

Define proof : 
  Forall(A:type)(a:A)(n m:nat).
    { (fill a (plus n m)) = (append (fill a n) (fill a m)) } :=
foralli(A:type)(a:A).
induction(n:nat) return Forall(m:nat).
    { (fill a (plus n m)) = (append (fill a n) (fill a m)) } with
  Z => foralli(m:nat).
       trans cong (fill a (plus * m)) n_eq
       trans join (fill a (plus Z m)) (fill a m)
       trans join (fill a m) (append (fill a Z) (fill a m)) 
       cong (append (fill a *) (fill a m)) symm n_eq
| S n' => foralli(m:nat).
          trans cong (fill a (plus * m)) n_eq
          trans join (fill a (plus (S n') m)) (cons a (fill a (plus n' m)))
          trans cong (cons a *) [n_IH n' m]
          trans join (cons a (append (fill a n') (fill a m))) (append (fill a (S n')) (fill a m))
          cong (append (fill a *) (fill a m)) symm n_eq
end.

