/- End-to-end test: the proj-scrutinee string-literal expansion site.
   `String.utf8ByteSize` is `ByteArray.size ∘ String.toByteArray` and
   `String.toByteArray` projects its argument, so the `Eq.refl` forces
   `.proj String 0 ""`: the scrutinee whnfs to a string literal, which
   must expand to its *reduced* constructor form
   (`String.ofByteArray _`) for the projection to fire — the
   references' proj expansion site (official `reduce_proj_core`),
   mirroring the `String.utf8ByteSize_empty` shape from Init. -/

--#export utf8SizeEmpty

theorem utf8SizeEmpty : Eq (String.utf8ByteSize "") 0 := Eq.refl 0
