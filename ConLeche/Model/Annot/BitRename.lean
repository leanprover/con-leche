module

public import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Verify.Denote.Rename

public section

/-!
# The reading's two blindnesses (task #161, IND TIER)

`denoteMeta`'s transposes of the two lemmas the modeled-block member key
runs on (`Verify/Denote/Rename.lean`'s
`denote_renameConsts_resolve` and `Verify/Denote/Inst.lean`'s
`denote_erasedEq`):

* **`denoteMeta_erasedEq`** — the reading is blind to exactly what
  `Expr.ErasedEq` ignores.  The mirror is verbatim because `ErasedEq`
  keeps the binder *metadata* (`m = m'`), which is the only part of a
  binder `denoteMeta` reads that `denote` does not (`pwBit φ m.pw`).  It
  ignores binder names and `fvar` type annotations, and `denoteMeta`'s
  binder clauses instantiate with the binder's own name and type — so
  the recursive step goes through `Expr.ErasedEq.instantiate1` at two
  `fvar`s with the same index, exactly as v1's does.
* **`denoteMeta_renameConsts_resolve`** — renaming preserves the reading
  of a *resolving* expression under the first and third `RenameOkT`
  clauses alone.  This is the form the block renaming needs: it is
  used at a *member* environment, where the block's later members are
  not stored yet, so the full `RenameOkT` is unavailable (task #148
  T6's finding, one currency over).

Neither literal clause moves: `Expr.renameConsts` does not descend
into a literal, and the string clause's seven leaves are read by name
off the environment rather than off the subject.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-- **Erasure-equal expressions read equally** (`denote_erasedEq`'s
transpose). -/
theorem denoteMeta_erasedEq {acval : Name → (Name → Nat) → AnnotTerm}
    {env : Env} {φ : Name → Nat} :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ →
      ∀ d : Nat, denoteMeta acval env φ d e₁ = denoteMeta acval env φ d e₂
  | .bvar i, e₂, he, _ => by
    match e₂, he with
    | .bvar j, he => obtain rfl : i = j := he; rfl
  | .fvar i ty, e₂, he, d => by
    match e₂, he with
    | .fvar j ty', he =>
      obtain rfl : i = j := he
      simp [denoteMeta_fvar]
  | .sort u, e₂, he, _ => by
    match e₂, he with
    | .sort u', he => obtain rfl : u = u' := he; rfl
  | .const n us, e₂, he, _ => by
    match e₂, he with
    | .const n' us', he =>
      obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := he
      rfl
  | .app f a, e₂, he, d => by
    match e₂, he with
    | .app g b, he =>
      obtain ⟨h1, h2⟩ : Expr.ErasedEq f g ∧ Expr.ErasedEq a b := he
      simp only [denoteMeta_app, denoteMeta_erasedEq h1 d,
        denoteMeta_erasedEq h2 d]
  | .forallE ty body m, e₂, he, d => by
    match e₂, he with
    | .forallE ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ :
          m = m' ∧ Expr.ErasedEq ty ty' ∧ Expr.ErasedEq body body' := he
      simp only [denoteMeta_forallE, denoteMeta_erasedEq h1 d,
        denoteMeta_erasedEq (Expr.ErasedEq.instantiate1 h2
          (show Expr.ErasedEq (.fvar d ty) (.fvar d ty') from rfl))
          (d + 1)]
  | .lam ty body m, e₂, he, d => by
    match e₂, he with
    | .lam ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ :
          m = m' ∧ Expr.ErasedEq ty ty' ∧ Expr.ErasedEq body body' := he
      simp only [denoteMeta_lam, denoteMeta_erasedEq h1 d,
        denoteMeta_erasedEq (Expr.ErasedEq.instantiate1 h2
          (show Expr.ErasedEq (.fvar d ty) (.fvar d ty') from rfl))
          (d + 1)]
  | .letE ty vl body, e₂, he, d => by
    match e₂, he with
    | .letE ty' vl' body', he => rw [denoteMeta, denoteMeta]
  | .lit l, e₂, he, _ => by
    match e₂, he with
    | .lit l', he => obtain rfl : l = l' := he; rfl
  | .proj sn i pe, e₂, he, d => by
    match e₂, he with
    | .proj sn' i' pe', he =>
      obtain ⟨rfl, rfl, h⟩ :
          sn = sn' ∧ i = i' ∧ Expr.ErasedEq pe pe' := he
      simp only [denoteMeta_proj, denoteMeta_erasedEq h d]
termination_by e₁ => e₁.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

end ConLeche.Model
