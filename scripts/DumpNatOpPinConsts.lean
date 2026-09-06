import Lech.Kernel.NatOpPins
import Lech.Kernel.Checker

/-!
Dump, per pin-certified Nat operation, the constant names referenced by
the generated pinned defining expression and certificate proof blobs
(`Lech/Kernel/NatOpPins.lean`).  Paired with
`scripts/diagnose_natop_prefix.py`, which diffs the output against the
declared-before-op prefix of a stream — the diagnosis workflow for a
"pin ground constants absent" decline (see DESIGN.md, "Prefix
allowlists vs. stream order").

Run: `lake env lean scripts/DumpNatOpPinConsts.lean > pinconsts.txt`
-/

open Lech

partial def collect (e : Expr) (acc : List Name) : List Name :=
  match e with
  | .const n _ => if acc.contains n then acc else n :: acc
  | .app f a => collect a (collect f acc)
  | .lam _ ty b _ => collect b (collect ty acc)
  | .forallE _ ty b _ => collect b (collect ty acc)
  | .letE _ ty v b => collect b (collect v (collect ty acc))
  | .fvar _ _ ty => collect ty acc
  | _ => acc

partial def nameStr : Name → String
  | .anonymous => ""
  | .str p s => (match nameStr p with | "" => s | ps => ps ++ "." ++ s)
  | .num p n => (match nameStr p with | "" => toString n | ps => ps ++ "." ++ toString n)

def dumpOp (label : String) (pin : Expr) (proofs : List Expr) : IO Unit := do
  let pinC := collect pin []
  let prfC := proofs.foldl (fun acc p => collect p acc) []
  IO.println s!"== {label} pin"
  for n in pinC.reverse do IO.println (nameStr n)
  IO.println s!"== {label} proofs"
  for n in prfC.reverse do IO.println (nameStr n)

#eval do
  dumpOp "Nat.land" natLandDeclPin natLandCertProofs
  dumpOp "Nat.lor" natLorDeclPin natLorCertProofs
  dumpOp "Nat.xor" natXorDeclPin natXorCertProofs
  dumpOp "Nat.gcd" natGcdDeclPin natGcdCertProofs
  dumpOp "Nat.shiftLeft" natShiftLeftDeclPin natShiftLeftCertProofs
  dumpOp "Nat.shiftRight" natShiftRightDeclPin natShiftRightCertProofs
  dumpOp "Nat.div" natDivDeclPin natDivCertProofs
  dumpOp "Nat.mod" natModDeclPin natModCertProofs
