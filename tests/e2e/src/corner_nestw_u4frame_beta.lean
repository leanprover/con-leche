--#export SB.rec

/- Corner case (lane NESTKERN, the item-9 adversarial pass for U4 on a
   CONTAINER constructor at the instantiation): `Sigma.mk (fst : List SB)
   (snd : (fun _ : List SB => Nat) fst)` at `Sigma (fun l : List SB =>
   (fun _ : List SB => Nat) l)` — the later field mentions the nested
   field only inside a β-redex.  Official (v4.34.0) ACCEPTS; the extended
   U4 reads the frame's whnf'd telescope, where `snd : Nat`, and accepts
   too (target 0). -/

inductive SB where
  | mk (x : Sigma (fun (l : List SB) => (fun (_ : List SB) => Nat) l)) : SB
