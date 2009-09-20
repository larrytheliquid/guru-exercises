Include "../../../guru-lang/lib/unit.g".
Include trusted "../../../guru-lang/lib/list.g".

%-
fun foldr`(A B:type)(f:Fun(a:A)(b:B).B)(b:B)(l:<list A>):B. 
match l with 
  nil _ => b 
| cons _ a l’ => (f a (foldr’ A B f b l’)) 
end. 

fun map`(A B:type)(f:Fun(x:A).B)(l:<list A>). 
(foldr’ A <list B> 
fun(x:A)(l2:<list B>).
  (cons B (f x) l2) 
(nil B) 
l)

fun(A B C: type)(^#owned cookie:C)
     (fcn: Fun(^#owned cookie:C)(^#owned a:A).B)
     (^#owned l : <list A>): <list B>.
    let Fcookie = (mk_map_i A B C fcn (inc C cookie)) in
    let ret = 
     (foldr A <list B> <map_i A B> Fcookie (map_h A B) (nil B) l) 
    in 
   do (dec <map_i A B> Fcookie)
      ret
   end
-%

Define proof : 
Forall(A B C:type) 
      (f:Fun(u:Unit)(x:A).B) 
      (g:Fun(u:Unit)(x:B).C) 
      (l:<list A>). 
        { (map unit g (map unit f l)) = (map unit fun(u x).(g u (f u x)) l) } :=
foralli(A B C:type)(f:Fun(u:Unit)(x:A).B)(g:Fun(u:Unit)(x:B).C).
induction(l:<list A>) return
{ (map unit g (map unit f l)) = (map unit fun(u x).(g u (f u x)) l) } with
  nil _ => trans cong (map unit g (map unit f *)) l_eq
         trans join (map unit g (map unit f nil)) (map unit fun(u x).(g u (f u x)) nil)
         cong (map unit fun(u)(x). (g u (f u x)) *) symm l_eq
| cons _ a l` => trans cong (map unit g (map unit f *)) l_eq
                 trans join (map unit g (map unit f (cons a l`)))
                            (cons (g unit (f unit a)) (map unit g (map unit f l`)))
                 trans cong (cons (g unit (f unit a)) *) [l_IH l`]
                 trans join (cons (g unit (f unit a)) (map unit fun(u)(x). (g u (f u x)) l`))
                            (map unit fun(u)(x). (g u (f u x)) (cons a l`))
                 cong (map unit fun(u)(x). (g u (f u x)) *) symm l_eq
end.
