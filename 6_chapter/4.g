Include trusted "../../../guru-lang/lib/list.g".

Define some : Fun(A C:type)(^#owned c:C)
                 (f:Fun(^#owned c:C)(^#owned a:A).bool)
                 (^#owned l:<list A>).bool :=
fun(A C:type)(^#owned c:C)
   (f:Fun(^#owned c:C)(^#owned a:A).bool).
(foldr A bool C c
       fun(^#owned c:C)(^#owned a:A)(r:bool).
          (or (f c a) r) ff).


