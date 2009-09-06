Include "../../../guru-lang/lib/pow.g".
Include "4.g".

% { (xor (not x) y) = (not (xor x y)) }
% The parity of two numbers added together is logical xor (ff:even tt:odd)
Define plus_parity : Forall(n m : nat). { (mod2 (plus n m)) = (xor (mod2 n) (mod2 m)) } :=
induction(m n:nat) return { (mod2 (plus n m)) = (xor (mod2 n) (mod2 m)) } with
  Z => trans cong (mod2 (plus * m)) n_eq
       trans join (mod2 (plus Z m)) (xor (mod2 Z) (mod2 m))
             cong (xor (mod2 *) (mod2 m)) symm n_eq
       
| S n' => truei
end.

%-
% An even number added to an even number is even
Classify join [plus_parity two four] ff.

% An even number added to an odd number is odd
Classify join [plus_parity two three] tt.

% An odd number added to an odd number is even
Classify join [plus_parity three seven] ff.
-%
