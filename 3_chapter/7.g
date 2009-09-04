Include "../../../guru-lang/lib/mult.g".

Inductive penta : type := 
  MacBride : penta 
| MacLean : penta 
| Schaeffer : penta 
| Jessup : penta 
| OldCapitol : penta.

Define clockwise :=
  fun(p:penta).
    match p with
      MacBride => Schaeffer
    | MacLean => Jessup
    | Schaeffer => MacLean
    | Jessup => MacBride
    | OldCapitol => OldCapitol
    end.

Define counter :=
  fun(p:penta).
    match p with
      MacBride => Jessup
    | MacLean => Schaeffer
    | Schaeffer => MacBride
    | Jessup => MacLean
    | OldCapitol => OldCapitol
    end.

Define proof : Forall(p:penta). { (counter (clockwise p)) = p } :=
  .
