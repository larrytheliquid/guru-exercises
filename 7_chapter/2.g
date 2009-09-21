Include "1.g".
Include trusted "../../../guru-lang/lib/minmax.g".

Define insert : Fun(x n:nat)(l:<slist n>).<slist (max x n)> :=

fun insert(x n:nat)(l:<slist n>):<slist (max x n)>.
match l with
  snil => cast (scons x Z snil [Z_le x]) by
          cong <slist *> symm
          trans 
            trans cong (max x *) inj <slist *> l_Eq
                  [max_comm x Z]
            join (max Z x) x
| scons _ n` l` u => 
  match (le n x) by u` _ with
    ff => (scons n (max x n`) (insert x n` l`) 
           % { (le (max x n`) n) }
           [max_bound x n` n [le_ff_implies_le n x u`] u])
  | tt => cast (scons x n l u`) by 
          cong <slist *> symm
          trans symm [max_comm n x]
                [max_le n x u`]
  end
end.
