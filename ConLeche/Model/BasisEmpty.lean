module

public import ConLeche.Model.BasisStep
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen

import ConLeche.Model.BasisLfp
public import ConLeche.Model.Cover
public section

/-!
# The `Empty` block, P tier: the type-reading recipe, executed once
(task #161, ENDGAME F)

The ENDGAME E seal itemized the basis tier's remaining bill and its
item 2 — "compute `denoteMeta` at each basis `ConstantInfo`'s type and
exhibit `AnnotTerm.BitAgree` to `BConst.typeAV c us`" — is the only item
with twenty-two instances.  This file executes it at the smallest
block, and the point is not the two constants: it is that **the recipe
is now a proof and not a design**.

## The recipe, in four moves

1. `show` the pinned `ConstantInfo`'s type as a literal `Expr` tree
   (`show … from rfl`) — the `denoteMeta` clauses are `match`es and will
   not reduce until the scrutinee is a constructor application;
2. walk it with `denoteMeta_forallE`/`denoteMeta_sort`/`denoteMeta_app`/
   `denoteMeta_fvar` and `Expr.instantiate1_eq_self` at every closed
   binder body, with the constant leaves supplied by
   `acval_basis_pinned` (`Model/BasisCons.lean`) — the P tier's
   basis leaves are pinned *for free*, so no new field is needed;
3. exhibit `AnnotTerm.BitAgree` from the reading to `BConst.typeAV`;
4. `bitAgree_wellDenotedV` + `WellDenotedV_bconst_type` grades it and
   `interp_eq` + `bval_mem_type` inhabits it.

## THE FINDING: the bits match because `pwBit` and `typeAV` were written
## from the same pin

Move 3 is where the batch could have failed, and it does not, for a
reason worth naming.  `denoteMeta`'s codomain slot at a binder is
`pwBit ψ mb.pw`, and `pwBit ψ pw = if pw.holds ψ then 0 else 1`.  At
`Empty.rec`'s stored binders the pins are `.never` (the motive's
domain) and `.ifAllZero [u]` (the two outer binders), so the reading's
numerals are `1` and `0 ↔ ψ u = 0`.  `BConst.typeAV .emptyRec [1, v]`
carries `v + 1` and `v` in those same three slots.  Zero-ness agrees on
the nose — `1 = 0 ↔ v + 1 = 0` (both false) and `pwBit ψ (.ifAllZero
[u]) = 0 ↔ ψ u = 0` — which is the ENDGAME E doctrine *seen from the
other side*: E showed the hand-built towers' bits are read off the type
pins; here the **type readings'** bits are read off the same pins, and
`BitAgree` is precisely the statement that the two readings never
disagree where anything looks.

Nothing in this file chooses a numeral.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  emptyA emptyRecA emptyName uN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## `Empty` -/

/-- The `Empty` former's type reading: `Sort 1`, which is
`BConst.typeAV .empty [1]` on the nose (no `BitAgree` needed — the
former has no binder, so there is no numeral to disagree about). -/
theorem denoteMeta_emptyA_type
    {acval : Name → (Name → Nat) → AnnotTerm} (ψ : Name → Nat) :
    denoteMeta acval ⟨emptyA :: env.consts⟩ ψ 0 emptyA.toConstantVal.type
      = some (BConst.typeAV .empty [1]) := by
  rw [show emptyA.toConstantVal.type = Expr.sort (.succ .zero) from rfl,
    denoteMeta_sort]
  rfl

/-- **`Empty`, installed at the P tier.** -/
theorem extendEmpty (mp : EnvModelM V μ env)
    (hfresh : env.find? emptyName = none)
    (hwf : EnvWF ⟨emptyA :: env.consts⟩) :
    CoverStep mp ⟨emptyA :: env.consts⟩ := by
  -- the pinned block's lfp clause is recorded at its former
  refine coverTo_addLfp (D := emptyLfp emptyName 1)
    (hL := emptyLfp_clause 1 (fun _ _ => by unfold acvalWith; split; rfl; exact absurd rfl ‹_›)) (hst := lfp0_stored)
    (hrd := lfp0_reads (by rw [ConLeche.Env.find?_cons]; exact if_pos rfl)
      (fun ψ => by show denoteMeta _ _ _ 0 (.sort _) = _; rw [denoteMeta_sort]; rfl))
    (hrdC := lfp0_ctorReads (by rw [ConLeche.Env.find?_cons]; exact if_pos rfl)
      (fun ψ => ⟨_, by show denoteMeta _ _ _ 0 (.sort _) = _; rw [denoteMeta_sort]⟩) fun j hj => absurd hj (Nat.not_lt_zero j))
    (hlic := lfpLicUniq_of_noFields (fun _ => Nat.zero_le 1) fun _ _ _ => rfl)
    (hnd := nodup_one _) (hlen := rfl)
    (hall := lfpAll_one (n := emptyName) (c := emptyA) rfl rfl
      (by rw [ConLeche.Env.find?_cons]; exact if_pos rfl)
      (fun _ _ h => by injection h with _ h; subst h; rfl))
    (hown := lfpOwn_former0 (c₀ := emptyA) mp.base2.wf rfl hfresh rfl rfl rfl (by decide) fun _ => rfl)
    (hex := filter_not_mem_self _)
    (coverA_pend hfresh <| declStep_preserves_of_basis_cons mp
    (A := fun _ => AnnotTerm.const .empty [1]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT emptyA.name ψ
          = some (Term.const .empty [1]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, denoteMeta_emptyA_type ψ⟩) ?_ ?_)
  · intro ψ ta h ρ
    rw [denoteMeta_emptyA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact WellDenotedV_bconst_type V .empty [1] ρ
  · intro ψ ta h ρ
    rw [denoteMeta_emptyA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval_mem_type V .empty [1] ρ

/-! ## `Empty.rec` — the recipe's real instance

Two binders, three stored `PropWhen` pins, and the reading's numerals
are all three of them. -/

/-- `pwBit` at a `.never` pin: the graph regime, unconditionally. -/
theorem pwBit_never (ψ : Name → Nat) :
    pwBit ψ ConLeche.PropWhen.never = 1 := by rfl

/-- `pwBit` at a one-parameter `.ifAllZero` pin: zero exactly when the
parameter is.  One of the *three* shapes every basis binder reduces to
— see `pwBit_ifAllZero_nil` for another. -/
theorem pwBit_ifAllZero_single (ψ : Name → Nat) (n : Name) :
    pwBit ψ (ConLeche.PropWhen.ifAllZero [n]) = 0 ↔ ψ n = 0 := by
  rw [pwBit_eq_zero_iff]
  simp

/-! ### The basis binders' `pwBit` shapes

Over `BasisKind.declsA`'s stored `PropWhen`s:

| shape | where | `pwBit` |
|---|---|---|
| `.never` | everywhere | `1` (`pwBit_never`) |
| `.ifAllZero [p]` | `Nat.rec`, `PUnit.rec`, `Empty.rec`, `Eq.rec`, `Quot.mk`, `Quot.lift` | `0 ↔ ψ p = 0` |
| `.ifAllZero []` | `Eq.refl`, `Quot.lift`, `Quot.ind`, `Quot.sound` | `0`, unconditionally |
-/

/-- `pwBit` at the *empty* `.ifAllZero` pin: zero unconditionally,
because `[].all _` is `true`.  The pin the `Prop`-valued basis
constants carry (`Eq.refl`, `Quot.ind`, `Quot.sound`,
and `Quot.lift`'s invariance binder). -/
theorem pwBit_ifAllZero_nil (ψ : Name → Nat) :
    pwBit ψ (ConLeche.PropWhen.ifAllZero []) = 0 := by
  rw [pwBit_eq_zero_iff]
  simp

/-- **`Empty.rec`'s type reading.**  The four moves of the module
docstring; the leaves are `acval_basis_pinned` at `Empty`. -/
theorem denoteMeta_emptyRecA_type {m : EnvModel V env}
    {A : (Name → Nat) → AnnotTerm} (ψ : Name → Nat)
    (hE : env.find? emptyName = some emptyA) :
    denoteMeta (acvalWith m.acval emptyRecA.name A)
        ⟨emptyRecA :: env.consts⟩ ψ 0 emptyRecA.toConstantVal.type
      = some (.pi 0 (pwBit ψ (.ifAllZero [uN]))
          (.pi 0 (pwBit ψ .never) (.const .empty [1]) (.sort (ψ uN)))
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .empty [1])
            (.app (.bvar 1) (.bvar 0)))) := by
  have hpd : ConLeche.Verify.pinnedStructT emptyName ψ
      = some (Term.const .empty [1]) := by
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hleaf : acvalWith m.acval emptyRecA.name A emptyName ψ
      = AnnotTerm.const .empty [1] := by
    rw [acvalWith_ne (by decide)]
    exact acval_basis_pinned hE (by decide) hpd
  have hEc : ∀ d : Nat,
      denoteMeta (acvalWith m.acval emptyRecA.name A)
          ⟨emptyRecA :: env.consts⟩ ψ d (.const emptyName [])
        = some (AnnotTerm.const .empty [1]) := by
    intro d
    have hf : (⟨emptyRecA :: env.consts⟩ : Env).find? emptyName
        = some emptyA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]; exact hE
    rw [denoteMeta_levelless_const hf (by rfl), hleaf]
  rw [show emptyRecA.toConstantVal.type
      = Expr.forallE
          (Expr.forallE (.const emptyName [])
            (.sort (.param uN)) { pw := .never })
          (Expr.forallE (.const emptyName [])
            (.app (.bvar 1) (.bvar 0))
            { pw := .ifAllZero [uN] })
          { pw := .ifAllZero [uN] } from rfl]
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
    Expr.instantiate1, hEc, Level.eval]

/-- **The reading agrees with `BConst.typeAV` on every numeral anything
reads.**  Three binders, three `pwBit`s, three `typeAV` slots, and the
iffs are `pwBit_never` and `pwBit_ifAllZero_single` — nothing here is
chosen. -/
theorem bitAgree_emptyRecA (ψ : Name → Nat) :
    AnnotTerm.BitAgree
      (.pi 0 (pwBit ψ (.ifAllZero [uN]))
        (.pi 0 (pwBit ψ .never) (.const .empty [1]) (.sort (ψ uN)))
        (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.const .empty [1])
          (.app (.bvar 1) (.bvar 0))))
      (BConst.typeAV .emptyRec [1, ψ uN]) := by
  have hz : pwBit ψ (ConLeche.PropWhen.ifAllZero [uN]) = 0 ↔ ψ uN = 0 :=
    pwBit_ifAllZero_single ψ uN
  refine .pi hz (.pi ?_ (.const _ _) (.sort _))
    (.pi hz (.const _ _) (.app (.bvar 1) (.bvar 0)))
  rw [pwBit_never]
  simp

/-- **`Empty.rec`, installed at the P tier.** -/
theorem extendEmptyRec (mp : EnvModelM V μ env)
    (hE : env.find? emptyName = some emptyA)
    (hfresh : env.find? emptyRecA.name = none)
    (hwf : EnvWF ⟨emptyRecA :: env.consts⟩) {ex : List Name} :
    CoverTo mp ex ⟨emptyRecA :: env.consts⟩ ex := by
  have hty := fun ψ =>
    denoteMeta_emptyRecA_type (m := mp.base2)
      (A := fun ψ => AnnotTerm.const .emptyRec [1, ψ uN]) ψ hE
  refine coverTo_cons hfresh (fun _ _ h => nomatch h) (declStep_preserves_of_basis_cons mp
    (A := fun ψ => AnnotTerm.const .emptyRec [1, ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => by injection h with _ _ _ h4; exact h4 ▸ rfl)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT emptyRecA.name ψ
          = some (Term.const .emptyRec [1, ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => by injection h with _ _ _ h4
                           intro r hr; rw [← h4] at hr; exact nomatch hr))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_wellDenotedV (bitAgree_emptyRecA ψ) ρ).mpr
      (WellDenotedV_bconst_type V .emptyRec [1, ψ uN] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AnnotTerm.BitAgree.interp_eq V (bitAgree_emptyRecA ψ) ρ]
    exact bval_mem_type V .emptyRec [1, ψ uN] ρ

/-! ## The block

`BasisInstallRun` is a right-nested `∧` chain, so the walk is an
`obtain` and two steps — there is no fold to invert. -/

/-- **The `Empty` block, installed at the P tier.**  `BasisStepPB`'s
`emptyK` branch. -/
theorem declBasisPB_emptyK {env₂ : Env} (mp : EnvModelM V μ env)
    (h : ConLeche.Semantics.BasisInstallRun env ConLeche.BasisKind.emptyK.declsA env₂) :
    CoverStep mp env₂ := by
  rw [show ConLeche.BasisKind.emptyK.declsA = [emptyA, emptyRecA] from rfl]
    at h
  obtain ⟨h1, h2, hnil⟩ := h
  subst hnil
  have hf1 : env.find? emptyA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨emptyA :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
  refine (extendEmpty mp hf1 hwf1).trans fun mp1 => ?_
  have hE : (⟨emptyA :: env.consts⟩ : Env).find? emptyName
      = some emptyA := by
    rw [ConLeche.Env.find?_cons]; exact if_pos rfl
  have hf2 : (⟨emptyA :: env.consts⟩ : Env).find? emptyRecA.name
      = none := Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨emptyRecA :: emptyA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq),
      (fun _ _ _ _ heq => by
        injection heq with _ _ _ h4
        subst h4
        intro r hr; exact nomatch hr),
      (fun _ heq => nomatch heq),
      (by first
        | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
            first | exact absurd h (by decide) | rfl)
        | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    show Expr.constsResolve _ emptyRecA.toConstantVal.type = true
    simp only [show emptyRecA.toConstantVal.type
        = Expr.forallE
            (Expr.forallE (.const emptyName [])
              (.sort (.param uN)) { pw := .never })
            (Expr.forallE (.const emptyName [])
              (.app (.bvar 1) (.bvar 0))
              { pw := .ifAllZero [uN] })
            { pw := .ifAllZero [uN] } from rfl,
      Expr.constsResolve, Bool.and_eq_true, Option.isSome_iff_exists]
    have hf : (⟨emptyRecA :: emptyA :: env.consts⟩ : Env).find?
        emptyName = some emptyA := by
      rw [ConLeche.Env.find?_cons, if_neg (by decide)]
      exact hE
    rw [hf]
    simp
  exact extendEmptyRec mp1 hE hf2 hwf2

end ConLeche.Model
