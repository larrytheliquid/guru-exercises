Include trusted "../../../guru-lang/lib/list.g".

Inductive slist : Fun(n:nat).type :=
  snil : <slist Z>
| scons : Fun(x n:nat)(l:<slist n>)
              (u:{ (le n x) = tt }).
              <slist x>.
