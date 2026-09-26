module

public import ConLeche.Kernel.Inductives.FieldNf

@[expose] public section

/-!
# CONFORMANCE: K.53 at a call the recursor check makes off the walk

**Not needed for soundness.**  Official's recursors call, on a recursive
field, the member heading the field's type AS ITS KERNEL NORMALISES IT
(`whnf(infer_type(u_i))` with the Πs opened, `mk_rec_rules`,
`inductive.cpp` v4.34.0 :763–775), at exactly that type's indices.  A
supplied family whose call only DEFEQ-matches the field (`List ((fun _ =>
T) Nat)` against `List T`) is none official generates (K.53, charter
item 9).  Where the recursor check reads the positivity walk it compares
against the walk's record (K.53′, `targetCallOk`); off the walk (PRIMREC,
lane FLATHOME: an intra-SCC call of a family checked without the walk,
`targetIntraCallOk`) it computes the same normal form itself — the walk's
own helper, `nestNf` (`Kernel/Inductives/FieldNf.lean`), ONE stage, on
the field's type with the class head's group as HOLES (the free
variables `lo ..< lo + k`) — reads the holes back to their constants
and compares, up to the free variables' annotations.  Nothing a proof
reads: the soundness of the call is its typing's (the hole defeq).
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- The holes `lo ..< lo + names.length` read back to their members at
`lvls`. -/
def targetHoleReadback (names : List Name) (lvls : List Level) (lo : Nat) (e : Expr) : Expr :=
  e.replaceFVars fun i =>
    if lo ≤ i ∧ i < lo + names.length then some (.const (names.getD (i - lo) default) lvls)
    else none

/-- **K.53 off the walk**: the called field's type `fld` (its class
head's group the holes `lo ..< lo + names.length`, at depth `d`) through
the walk's normal form (`nestNf`), read back (`targetHoleReadback`), is the callee's major domain under the call's
telescope, `want`, up to the free variables' annotations. -/
def targetK53Conform (ops : CheckerOps m) (env : Env) (cn : Name) (names : List Name)
    (lvls : List Level) (lo d : Nat) (fld want : Expr) : m Unit := do
  let nf ← nestNf ops env names lo (lo + names.length) (whnfWalkFuel fld) d fld
  unless (targetHoleReadback names lvls lo nf).eraseFVarTys == want.eraseFVarTys do
    throw (.invalid s!"target rec (K.53): the rule of {cn} calls a recursor whose major is \
      not the called field's type as its kernel normalises it")

end ConLeche
