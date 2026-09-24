--#export VT.rec

/- Corner case, the GOOD half (lane NESTW, the closure witness (W) for
   nested blocks): the block `VT` with its would-be nested occurrence
   pointed at the unrelated type `VPin` — an ordinary, non-nested block
   every checker accepts.  The forged twin `corner_nestw_u4frame_bad`
   (`scripts/mk_nestw_bad.py`) writes the family's `p.2` as the raw
   projection `.proj Prod 1 p` and repoints `VPin` to `VT` inside `VT`'s
   block, giving a CONTAINER CONSTRUCTOR, at the instantiation, WHOSE
   LATER FIELD READS A NESTED FIELD'S VALUE: `Sigma.mk (fst : Prod VT Nat)
   (snd : Fin fst.2)` at `Sigma (Prod VT Nat) (fun p => Fin p.2)`.
   Official (Lean v4.33.0, the declaration added through the kernel)
   REJECTS it: "(kernel) invalid projection p.2". -/

inductive VPin where
  | pin : VPin
inductive VT where
  | node : Sigma (fun p : Prod VPin Nat => Fin p.2) → VT
