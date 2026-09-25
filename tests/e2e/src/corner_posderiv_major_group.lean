--#export GT.rec GT.rec_1 GT.rec_2
/- Corner case (lane POSDERIV, the item-9 adversarial pass for the MAJOR
   check): nesting through ONE member `GC1` of a mutual container group
   whose other member `GC2` the block never reaches.  Official copies every
   member of the group (`I_val->get_all()`, inductive.cpp v4.34.0 :1100)
   and generates `GT.rec_2` on `GC2 GT`, an instantiation the positivity
   walk never visits.  Official 0. -/
mutual
inductive GC1 (α : Type) where
  | mk : α → GC1 α
inductive GC2 (α : Type) where
  | mk : α → GC2 α
end
inductive GT where
  | leaf : GT
  | mk : GC1 GT → GT
