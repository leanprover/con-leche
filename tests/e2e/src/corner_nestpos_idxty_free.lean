--#export IdxT.rec

/- Corner case, the GOOD half (positivity through
   containers): the block `IdxT` with its would-be nested occurrence
   pointed at the unrelated type `IPin` — an ordinary, non-nested
   block every checker accepts.  The forged twin
   `corner_nestpos_idxty_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `IPin` to `IdxT` inside `IdxT`'s block, giving
   a container whose INDEX TYPE depends on its parameter (`IdxC α : Idx α → Type`), nested at `IdxC IdxT 0`: the auxiliary type former `Idx IdxT → Type` is checked before the block exists (official (N2)).
   Official (Lean v4.29.1 and v4.34.0, the block written in Lean)
   REJECTS it: "(kernel) unknown constant 'IdxT'". -/

def Idx (_α : Type) : Type := Nat
inductive IdxC (α : Type) : Idx α → Type where
  | mk : IdxC α (0 : Nat)
inductive IPin where
  | pin : IPin
inductive IdxT where
  | leaf : IdxT
  | mk : IdxC IPin (0 : Nat) → IdxT
