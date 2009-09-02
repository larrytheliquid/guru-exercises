Include "../../../guru-lang/lib/mult.g".

Define proof : Forall(x:bool). { (and ff x) = ff } :=
  foralli(b:bool). join (and ff b) ff.
