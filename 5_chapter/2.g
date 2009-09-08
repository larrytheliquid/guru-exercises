Include "../../../guru-lang/lib/nat.g".

% Each natural number greater than 0 is the successor of a previous natural number
Define proof : Forall(x:nat)(u:{(lt Z x) = tt}). Exists(x’:nat). { x = (S x’) } :=
foralli(x:nat)(u:{(lt Z x) = tt}).
case x with
  Z => contra
       trans symm u
       trans cong (lt Z *) x_eq
       trans join (lt Z Z) ff
       clash ff tt
       Exists(x':nat). { x = (S x') }
| S x' => existsi x' { x = (S *) }
          x_eq
end.

