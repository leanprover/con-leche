import Setlec.SetP.Annot.ValidV

/-!
# `BitAgree`: two readings of the same term (task #161, ENDGAME E)

The basis tier's type readings need a bridge that does not exist yet,
and the ENDGAME D resume-here's item 2 understated it.  Its claim was

> `denoteP acval env ψ 0 (basis decl type) = some (BConst.type2 c us)`

and that equation is **false as stated**, for two independent reasons,
neither of which is a defect:

* `denoteP`'s `forallE` clause emits `.pi 0 (pwBit φ m.pw) ta ba` — the
  domain slot is always the literal `0`, because the reading has no
  sort run to take a domain sort from.  `BConst.type2` carries the
  *exact* domain sort at every binder, because its consumers
  (`AnnotOk2`'s binder clauses, `Skeleton.sound_pi`) read it;
* `denoteP`'s codomain slot is a `pwBit`, canonically in `{0, 1}`.
  `BConst.type2` carries the tower's result sort, which can be any
  numeral.

Both slots therefore differ as *numerals* while agreeing on everything
that is read.  `interp2` dispatches on the codomain slot only through
`v = 0` (`piR`/`lamR` are `if v = 0`), and on the domain slot **not at
all**; `AnnotOk2` and `AnnotValidV` do the same.  So the right bridge is
not an equation between readings but a congruence:

**`BitAgree e e'` — same tree, same leaves, binder numerals agreeing on
zero-ness, domain numerals unconstrained.**

It carries everything the P tier reads: the interpretation on the nose
(`interp2_eq`), and both grading predicates as iffs (`ok2`, `validV`),
hence `AnnotOkP` (`okP`).  With it, a basis type reading is discharged
by *computing* `denoteP` and exhibiting a `BitAgree` to `BConst.type2`,
after which `bval2_mem_type` and `AnnotOkP_bconst_type` apply
unchanged — which is what the resume-here meant.

The relation is deliberately **not** an equivalence-by-erasure: it
demands the two trees be structurally identical, so it cannot silently
identify a `.lam` with a `.pi` or move a leaf.  `erase_eq` records that
it refines erasure-equality, and it is strictly finer.
-/

-- `AVExpr.BitAgree` extends `Setlec.Semantics.AVExpr` (dot notation on
-- readings), so this module stays in the semantic tier's namespace.
namespace Setlec.Semantics
open Setlec.SetModel Setlec.SetP

open Setlec.Semantics SetTheory Setlec.SetModel

universe w

/-- **Two readings of the same term, differing only in binder
numerals' non-zero values.**  Structurally identical trees; at each
binder the codomain numerals agree on zero-ness and the domain numerals
are unconstrained (nothing reads them). -/
inductive AVExpr.BitAgree : AVExpr → AVExpr → Prop where
  | bvar (i : Nat) : BitAgree (.bvar i) (.bvar i)
  | sort (u : Nat) : BitAgree (.sort u) (.sort u)
  | const (c : Setlec.TT.BConst) (us : List Nat) :
      BitAgree (.const c us) (.const c us)
  | prf : BitAgree .prf .prf
  | app {f f' a a' : AVExpr} :
      BitAgree f f' → BitAgree a a' → BitAgree (.app f a) (.app f' a')
  | lam {v v' : Nat} {A A' b b' : AVExpr} :
      (v = 0 ↔ v' = 0) → BitAgree A A' → BitAgree b b' →
      BitAgree (.lam v A b) (.lam v' A' b')
  | pi {u u' v v' : Nat} {A A' B B' : AVExpr} :
      (v = 0 ↔ v' = 0) → BitAgree A A' → BitAgree B B' →
      BitAgree (.pi u v A B) (.pi u' v' A' B')
  | letE {T T' e e' b b' : AVExpr} :
      BitAgree T T' → BitAgree e e' → BitAgree b b' →
      BitAgree (.letE T e b) (.letE T' e' b')
  | eqE {T T' a a' b b' : AVExpr} :
      BitAgree T T' → BitAgree a a' → BitAgree b b' →
      BitAgree (.eqE T a b) (.eqE T' a' b')
  | proj {i : Nat} {e e' : AVExpr} :
      BitAgree e e' → BitAgree (.proj i e) (.proj i e')

namespace AVExpr.BitAgree

/-- Reflexivity — every reading agrees with itself. -/
theorem refl : ∀ e : AVExpr, BitAgree e e
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c us => .const c us
  | .prf => .prf
  | .app f a => .app (refl f) (refl a)
  | .lam _ A b => .lam Iff.rfl (refl A) (refl b)
  | .pi _ _ A B => .pi Iff.rfl (refl A) (refl B)
  | .letE T e b => .letE (refl T) (refl e) (refl b)
  | .eqE T a b => .eqE (refl T) (refl a) (refl b)
  | .proj _ e => .proj (refl e)

/-- Symmetry. -/
theorem symm : ∀ {e e' : AVExpr}, BitAgree e e' → BitAgree e' e := by
  intro e e' h
  induction h with
  | bvar i => exact .bvar i
  | sort u => exact .sort u
  | const c us => exact .const c us
  | prf => exact .prf
  | app _ _ ihf iha => exact .app ihf iha
  | lam hz _ _ ihA ihb => exact .lam hz.symm ihA ihb
  | pi hz _ _ ihA ihB => exact .pi hz.symm ihA ihB
  | letE _ _ _ ihT ihe ihb => exact .letE ihT ihe ihb
  | eqE _ _ _ ihT iha ihb => exact .eqE ihT iha ihb
  | proj _ ih => exact .proj ih

/-- **The relation refines erasure-equality** — and strictly: erasure
also forgets the *structure* of the numerals' binders, while `BitAgree`
demands the trees be identical. -/
theorem erase_eq : ∀ {e e' : AVExpr}, BitAgree e e' →
    e.erase = e'.erase := by
  intro e e' h
  induction h with
  | bvar i => rfl
  | sort u => rfl
  | const c us => rfl
  | prf => rfl
  | app _ _ ihf iha => simp [AVExpr.erase, ihf, iha]
  | lam _ _ _ ihA ihb => simp [AVExpr.erase, ihA, ihb]
  | pi _ _ _ ihA ihB => simp [AVExpr.erase, ihA, ihB]
  | letE _ _ _ ihT ihe ihb => simp [AVExpr.erase, ihT, ihe, ihb]
  | eqE _ _ _ ihT iha ihb => simp [AVExpr.erase, ihT, iha, ihb]
  | proj _ ih => simp [AVExpr.erase, ih]

variable (V : Type w) [SetTheory V]

/-- **The interpretation is invariant** — `interp2` reads a codomain
numeral only through `v = 0` (`piR_zero_agree`/`lamR_zero_agree`) and a
domain numeral not at all. -/
theorem interp2_eq : ∀ {e e' : AVExpr}, BitAgree e e' →
    ∀ ρ : Nat → V, interp2 V ρ e = interp2 V ρ e' := by
  intro e e' h
  induction h with
  | bvar i => intro ρ; rfl
  | sort u => intro ρ; rfl
  | const c us => intro ρ; rfl
  | prf => intro ρ; rfl
  | app _ _ ihf iha => intro ρ; simp only [interp2_app, ihf, iha]
  | lam hz _ _ ihA ihb =>
    intro ρ
    simp only [interp2_lam, ihA ρ]
    exact lamR_zero_agree hz fun x _ => ihb (cons x ρ)
  | pi hz _ _ ihA ihB =>
    intro ρ
    simp only [interp2_pi, ihA ρ]
    exact piR_zero_agree hz fun x _ => ihB (cons x ρ)
  | letE _ _ _ ihT ihe ihb =>
    intro ρ; simp only [interp2_letE, ihe ρ]; exact ihb _
  | eqE _ _ _ ihT iha ihb =>
    intro ρ; simp only [interp2_eqE, iha, ihb]
  | proj _ ih => intro ρ; simp only [interp2_proj, ih]

/-- **Truthfulness is invariant.**  The `lam`/`app` clauses' fibre
obligations are `v = 0 → …`, so zero-agreement transfers them; every
other clause is structural. -/
theorem ok2 : ∀ {e e' : AVExpr}, BitAgree e e' →
    ∀ ρ : Nat → V, (AnnotOk2 V ρ e ↔ AnnotOk2 V ρ e') := by
  intro e e' h
  induction h with
  | bvar i => intro ρ; simp
  | sort u => intro ρ; simp
  | const c us => intro ρ; simp
  | prf => intro ρ; simp
  | app hf ha ihf iha =>
    intro ρ
    rw [AnnotOk2_app, AnnotOk2_app, ihf ρ, iha ρ,
      interp2_eq V hf ρ, interp2_eq V ha ρ]
  | lam hz hA hb ihA ihb =>
    intro ρ
    rw [AnnotOk2_lam, AnnotOk2_lam, ihA ρ, interp2_eq V hA ρ]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihb (cons x ρ)))
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_)
        ⟨fun hh h0 => hh (hz.mpr h0), fun hh h0 => hh (hz.mp h0)⟩))
    rw [interp2_eq V hb (cons x ρ)]
  | pi _ hA hB ihA ihB =>
    intro ρ
    rw [AnnotOk2_pi, AnnotOk2_pi, ihA ρ, interp2_eq V hA ρ]
    exact and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl (ihB (cons x ρ)))
  | letE _ he _ ihT ihe ihb =>
    intro ρ
    rw [AnnotOk2_letE, AnnotOk2_letE, ihT ρ, ihe ρ,
      interp2_eq V he ρ, ihb _]
  | eqE _ _ _ ihT iha ihb =>
    intro ρ; rw [AnnotOk2_eqE, AnnotOk2_eqE, iha ρ, ihb ρ]
  | proj he ih =>
    intro ρ
    rw [AnnotOk2_proj, AnnotOk2_proj, ih ρ, interp2_eq V he ρ]

/-- **Bit validity is invariant.**  The one clause that reads a numeral
is `pi`'s `v = 0 → …`, and zero-agreement is exactly what it needs. -/
theorem validV : ∀ {e e' : AVExpr}, BitAgree e e' →
    ∀ ρ : Nat → V, (AnnotValidV V ρ e ↔ AnnotValidV V ρ e') := by
  intro e e' h
  induction h with
  | bvar i => intro ρ; simp
  | sort u => intro ρ; simp
  | const c us => intro ρ; simp
  | prf => intro ρ; simp
  | app _ _ ihf iha =>
    intro ρ; rw [AnnotValidV_app, AnnotValidV_app, ihf ρ, iha ρ]
  | lam _ hA hb ihA ihb =>
    intro ρ
    rw [AnnotValidV_lam, AnnotValidV_lam, ihA ρ, interp2_eq V hA ρ]
    exact and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl (ihb (cons x ρ)))
  | pi hz hA hB ihA ihB =>
    intro ρ
    rw [AnnotValidV_pi, AnnotValidV_pi, ihA ρ, interp2_eq V hA ρ]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihB (cons x ρ)))
      ⟨fun hh h0 x hx => ?_, fun hh h0 x hx => ?_⟩)
    · rw [← interp2_eq V hB (cons x ρ)]; exact hh (hz.mpr h0) x hx
    · rw [interp2_eq V hB (cons x ρ)]; exact hh (hz.mp h0) x hx
  | letE _ he _ ihT ihe ihb =>
    intro ρ
    rw [AnnotValidV_letE, AnnotValidV_letE, ihT ρ, ihe ρ,
      interp2_eq V he ρ, ihb _]
  | eqE _ _ _ ihT iha ihb =>
    intro ρ; rw [AnnotValidV_eqE, AnnotValidV_eqE, iha ρ, ihb ρ]
  | proj _ ih => intro ρ; rw [AnnotValidV_proj, AnnotValidV_proj, ih ρ]

end AVExpr.BitAgree

end Setlec.Semantics
