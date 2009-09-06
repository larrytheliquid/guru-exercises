Include "../../../guru-lang/lib/bool.g".

Define lemma : Forall(x y : bool). { (xor (not x) y) = (not (xor x y)) } :=
  foralli(x y:bool).
    case x with
      ff => trans cong (xor (not *) y) x_eq
            trans join (xor (not ff) y) (xor tt y)
            trans join (xor tt y) (not y)
            trans join (not y) (not (xor ff y))
                  cong (not (xor * y)) symm x_eq
    | tt => trans cong (xor (not *) y) x_eq
            trans join (xor (not tt) y) (xor ff y)
            trans join (xor ff y) y
            trans symm [not_not y]
            trans join (not (not y)) (not (xor tt y))
                  cong (not (xor * y)) symm x_eq
    end.

