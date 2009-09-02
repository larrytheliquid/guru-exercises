Include "../../../guru-lang/lib/mult.g".

Define proof : Forall(b:bool). { (and b b) = b } :=
  foralli(b:bool).
    case b with
      ff => trans cong (and * *) b_eq
            trans join (and ff ff) ff
                  symm b_eq
    | tt => trans cong (and * *) b_eq
            trans join (and tt tt) tt
                  symm b_eq
    end.
