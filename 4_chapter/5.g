Include "../../../guru-lang/lib/pow.g".
Include "4.g".

% The parity of two numbers added together is logical xor (ff:even tt:odd)
Define plus_parity : Forall(m n: nat). { (mod2 (plus n m)) = (xor (mod2 n) (mod2 m)) } :=

induction(m n:nat) return { (mod2 (plus n m)) = (xor (mod2 n) (mod2 m)) } with
  Z => trans cong (mod2 (plus * m)) n_eq
       trans join (mod2 (plus Z m)) (xor (mod2 Z) (mod2 m))
             cong (xor (mod2 *) (mod2 m)) symm n_eq
       
| S n' => trans cong (mod2 (plus * m)) n_eq
          trans join (mod2 (plus (S n') m)) (mod2 (S (plus n' m)))
          trans join (mod2 (S (plus n' m))) (not (mod2 (plus n' m)))
          trans cong (not *) [n_IH m n']
          trans symm [lemma (mod2 n') (mod2 m)]
          trans join (xor (not (mod2 n')) (mod2 m)) (xor (mod2 (S n')) (mod2 m))
                cong (xor (mod2 *) (mod2 m)) symm n_eq
end.
Classify plus_parity.

% An even number added to an even number is even
Classify join (mod2 (plus two four)) ff.

% An even number added to an odd number is odd
Classify join (mod2 (plus two three)) tt.

% An odd number added to an odd number is even
Classify join (mod2 (plus three seven)) ff.

