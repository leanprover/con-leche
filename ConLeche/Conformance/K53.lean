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

/-! ## K.53 on the nested route (PRIMREC / NESTKN-R)

On a hot layer (`Kernel/Inductives/RecNestK.lean`) the called field's normal form is the
node's own (`nestTeleNf` at the node's layout), read back to constants at the class's
instance.  Official instantiates its auxiliary types with SIMPLIFYING level substitution
(`instantiate_lparams`, `level.cpp` `mk_max`), so the comparison takes universe levels up
to `Level.isEquiv` (this checker never simplifies a level); everything else is syntactic,
up to the free variables' annotations. -/

/-- Structural equality after annotation erasure, levels by `Level.isEquiv`, memoised on
the pair (DAG inputs). -/
def Expr.k53EqGo : Nat → Expr → Expr → Std.HashMap (Expr × Expr) Bool →
    Bool × Std.HashMap (Expr × Expr) Bool
  | 0, _, _, memo => (false, memo)
  | fuel + 1, a, b, memo =>
    if a == b then (true, memo) else
    match memo[(a, b)]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap (Expr × Expr) Bool :=
        match a, b with
        | .sort u, .sort v => ((Level.isEquiv u v).getD false, memo)
        | .const n us, .const n' vs => (n == n' && (Level.isEquivList us vs).getD false, memo)
        | .app f x, .app g y =>
          let (r1, memo) := k53EqGo fuel f g memo
          if r1 then k53EqGo fuel x y memo else (false, memo)
        | .lam t x m, .lam t' y m' | .forallE t x m, .forallE t' y m' =>
          if m != m' then (false, memo) else
          let (r1, memo) := k53EqGo fuel t t' memo
          if r1 then k53EqGo fuel x y memo else (false, memo)
        | .letE t v x, .letE t' v' y =>
          let (r1, memo) := k53EqGo fuel t t' memo
          if !r1 then (false, memo) else
          let (r2, memo) := k53EqGo fuel v v' memo
          if r2 then k53EqGo fuel x y memo else (false, memo)
        | .proj s i x, .proj s' i' y =>
          if s == s' && i == i' then k53EqGo fuel x y memo else (false, memo)
        | _, _ => (false, memo)
      (r, memo.insert (a, b) r)

/-- **K.53's comparison on the nested route**: `got` and `want` alike up to the free
variables' annotations and universe levels up to `Level.isEquiv`. -/
def Expr.k53EqK (got want : Expr) : Bool :=
  let a := got.eraseFVarTys
  let b := want.eraseFVarTys
  a == b || (Expr.k53EqGo (a.depth + b.depth + 1) a b {}).1

/-- **K.53 at a call of a hot layer** (reject-only): the called field's normal form at its
node, read back at the class's instance (`got`), is the callee's major domain under the
call's telescope (`want`). -/
def targetK53ConformK (cn : Name) (got want : Expr) : m Unit := do
  unless got.k53EqK want do
    throw (.invalid s!"target rec (K.53): the rule of {cn} calls a recursor whose major is \
      not the called field's type as its kernel normalises it (nested route)")

end ConLeche
