import ConLeche.Kernel.NatOpPins
import ConLeche.Kernel.Checker

/-!
Dump, per pin-certified Nat operation, the constant names referenced by
the generated pinned defining expression and certificate proof blobs
(`ConLeche/Kernel/NatOpPins.lean`).  Paired with
`scripts/diagnose_natop_prefix.py`, which diffs the output against the
declared-before-op prefix of a stream — the diagnosis workflow for a
"pin ground constants absent" decline (see DESIGN.md, "Prefix
allowlists vs. stream order").

Run: `lake env lean scripts/DumpNatOpPinConsts.lean > pinconsts.txt`
-/

open ConLeche

partial def collect (e : Expr) (acc : List Name) : List Name :=
  match e with
  | .const n _ => if acc.contains n then acc else n :: acc
  | .app f a => collect a (collect f acc)
  | .lam ty b _ => collect b (collect ty acc)
  | .forallE ty b _ => collect b (collect ty acc)
  | .letE ty v b => collect b (collect v (collect ty acc))
  | .fvar _ ty => collect ty acc
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

-- one section per PIN VARIANT (task #273: the binary embeds the dumps
-- of several toolchains, `natOpPinSets`); the section label is
-- `<toolchain> <op>`, which `diagnose_natop_prefix.py` reads
#eval do
  for ps in natOpPinSets do
    for c in natDivModNames do
      dumpOp s!"{ps.toolchain} {nameStr c}" (divModDeclPin ps c) (divModCertProofs ps c)
