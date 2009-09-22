%-
Read the signature, nuff said
fun vec_cat(A:type)(spec n m:nat)(l : <vec <vec A m> n>):
      <vec A (mult n m)>.

Gets value at position m, always less than the length of l
fun vec_get(A:type)(spec n:nat)(l:<vec A n>)(m:nat)(u:{ (lt m n) = tt }):A.
-%
