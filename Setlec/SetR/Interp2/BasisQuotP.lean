import Setlec.SetR.Interp2.BasisBlocksP

/-!
# The `Quot` block, P tier (task #161, ENDGAME H)

The basis tier's fourth block, and the only one that

* stores an **axiom** (`Quot.sound` — the `hred` disjunct's second
  branch, unused by every earlier block), and
* reads a leaf that is **not** `pinnedDirectT`: `Quot.lift`'s and
  `Quot.sound`'s stored types both mention the pinned `Eq` former,
  whose annotated leaf is the basis install's own tower.  Where v1
  crosses that gap with `EnvS.eq_lawV` (`quotInv_interpS` /
  `quotSoundTy_interpS`), the P tier crosses it with **`EqLawP`** —
  the `EnvS2PM` field whose *supplier* is this very bundle, and whose
  grading half (v1 has no analogue: `AnnotOkV` has no bit content) is
  exactly what the reading's `htyOk` row needs.  The field is
  available at the `Quot` cons because `DeclBasisR`'s first conjunct
  puts `Eq` in the prefix.

Everything else is the `BasisBlocksP.lean` recipe: five pinned
towers, five type readings, two `.plain` `RecRuleLawP` rows.  Both
recursors' motives land in `Sort 0`, so both rows are `Prop`-motive
rows and both fired equalities are the `PUnit.rec` observation seen
twice more — the reading's `lamR 0` and the value law's squash regime
are the same point.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule uN u1N vN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

section Quot

open Setlec (quotA quotMkA quotLiftA quotIndA quotSoundA quotName
  quotMkName quotLiftName quotIndName quotSoundName eqA eqName)

variable {m : EnvS2Core V env} {A : (Name → Nat) → AVExpr}

/-! ## The block's two pinned leaves

`Quot` and `Quot.mk` are read by every later constant in the block. -/

/-- The pinned `Quot` leaf at an extension, at any level. -/
theorem denoteP_quotLeaf {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = quotName)
    (hQ : env.find? quotName = some quotA) (d : Nat) (l : Level) :
    denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const quotName [l])
      = some (AVExpr.const .quot [l.eval ψ]) := by
  refine denoteP_pinned_const (m := m) hne hQ (by decide) (by rfl) ?_ d
  simp +decide [Setlec.TTVerify.pinnedDirectT]
  show Level.substFn ψ [uN] [l] uN = Level.eval ψ l
  simp [Level.substFn]

/-- The pinned `Quot.mk` leaf at an extension, at any level. -/
theorem denoteP_quotMkLeaf {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = quotMkName)
    (hM : env.find? quotMkName = some quotMkA) (d : Nat) (l : Level) :
    denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const quotMkName [l])
      = some (AVExpr.const .quotMk [l.eval ψ]) := by
  refine denoteP_pinned_const (m := m) hne hM (by decide) (by rfl) ?_ d
  simp +decide [Setlec.TTVerify.pinnedDirectT]
  show Level.substFn ψ [uN] [l] uN = Level.eval ψ l
  simp [Level.substFn]

/-! ## `Quot` and `Quot.mk` -/

/-- The relation binder's domain reading — shared by every constant in
the block, and `.never` at both of its own binders. -/
def quotRelTyP (i : Nat) : AVExpr :=
  .pi 0 1 (.bvar i) (.pi 0 1 (.bvar (i + 1)) (.sort 0))

/-- **`Quot`'s type reading.** -/
theorem denoteP_quotA_type
    {acval : Name → (Name → Nat) → AVExpr} (ψ : Name → Nat) :
    denoteP acval ⟨quotA :: env.consts⟩ ψ 0 quotA.toConstantVal.type
      = some (.pi 0 (pwBit ψ .never) (.sort (ψ uN))
          (.pi 0 (pwBit ψ .never) (quotRelTyP 0) (.sort (ψ uN)))) := by
  simp [quotA, ConstantInfo.toConstantVal, denoteP_forallE,
    denoteP_sort, denoteP_fvar, Expr.instantiate1, quotRelTyP,
    pwBit_never, Level.eval, uN]

/-- **The `Quot` reading agrees with `BConst.type2`.**  Every binder in
the block's type formers is `.never`, so every numeral is `1` against a
successor or a `Nat.max _ 1`. -/
theorem bitAgree_quotRelTyP (i j : Nat) :
    AVExpr.BitAgree (quotRelTyP i) (relT2 j (.bvar i)) :=
  .pi (Iff.intro (fun h => nomatch h)
      (fun h => absurd h (maxOne_ne_zero j)))
    (.bvar i) (.pi Iff.rfl (.bvar (i + 1)) (.sort 0))

theorem bitAgree_quotA (ψ : Name → Nat) :
    AVExpr.BitAgree
      (.pi 0 (pwBit ψ .never) (.sort (ψ uN))
        (.pi 0 (pwBit ψ .never) (quotRelTyP 0) (.sort (ψ uN))))
      (BConst.type2 .quot [ψ uN]) := by
  have h1 : pwBit ψ Setlec.PropWhen.never = 0 ↔ ψ uN + 1 = 0 := by
    rw [pwBit_never]
    exact Iff.intro (fun h => nomatch h) (fun h => nomatch h)
  exact .pi h1 (.sort _) (.pi h1 (bitAgree_quotRelTyP 0 (ψ uN))
    (.sort _))

/-- **`Quot.mk`'s type reading.**  Stated at *any* extension whose cons
is neither `Quot` nor `Quot.mk` as well, because both recursor rows
read it as their fired constructor's telescope (`TVja`). -/
theorem denoteP_quotMkTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = quotName)
    (hQ : env.find? quotName = some quotA) :
    denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ 0
        quotMkA.toConstantVal.type
      = some (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.sort (ψ uN))
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (quotRelTyP 0)
            (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.bvar 1)
              (.app (.app (.const .quot [ψ uN]) (.bvar 2))
                (.bvar 1))))) := by
  have hQc : ∀ d : Nat,
      denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (Expr.const (Name.str Name.anonymous "Quot")
          [Level.param (Name.str Name.anonymous "u")])
        = some (AVExpr.const .quot
            [ψ (Name.str Name.anonymous "u")]) := by
    intro d
    exact denoteP_quotLeaf (m := m) (A := A) (c₀ := c₀) ψ hne hQ d
      (Level.param uN)
  simp [quotMkA, ConstantInfo.toConstantVal, denoteP_forallE,
    denoteP_sort, denoteP_app, denoteP_fvar, Expr.instantiate1,
    quotRelTyP, pwBit_never, hQc, Level.eval, uN]

theorem denoteP_quotMkA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA) :
    denoteP (acvalWith m.acval quotMkA.name A)
        ⟨quotMkA :: env.consts⟩ ψ 0 quotMkA.toConstantVal.type
      = some (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.sort (ψ uN))
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (quotRelTyP 0)
            (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.bvar 1)
              (.app (.app (.const .quot [ψ uN]) (.bvar 2))
                (.bvar 1))))) :=
  denoteP_quotMkTy (m := m) (A := A) ψ (by decide) hQ

theorem bitAgree_quotMkA (ψ : Name → Nat) :
    AVExpr.BitAgree
      (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.sort (ψ uN))
        (.pi 0 (pwBit ψ (.ifAllZero [uN])) (quotRelTyP 0)
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.bvar 1)
            (.app (.app (.const .quot [ψ uN]) (.bvar 2)) (.bvar 1)))))
      (BConst.type2 .quotMk [ψ uN]) := by
  have hz : pwBit ψ (Setlec.PropWhen.ifAllZero [uN]) = 0 ↔ ψ uN = 0 :=
    pwBit_ifAllZero_single ψ uN
  exact .pi hz (.sort _)
    (.pi hz (bitAgree_quotRelTyP 0 (ψ uN))
      (.pi hz (.bvar 1)
        (.app (.app (.const _ _) (.bvar 2)) (.bvar 1))))

/-! ### The first two installs -/

/-- **`Quot`, installed at the P tier.** -/
theorem extendQuotP (mp : EnvS2PM V μ env)
    (hfresh : env.find? quotName = none)
    (hbase : EnvS V ⟨quotA :: env.consts⟩)
    (hag : ∀ n, n ≠ quotA.name → mp.base2.base.cval n = hbase.cval n)
    (hcv : ∀ ψ, hbase.cval quotA.name ψ = VExpr.const .quot [ψ uN]) :
    Nonempty (EnvS2PM V μ ⟨quotA :: env.consts⟩) := by
  refine declStepPM_of_basis_cons mp
    (A := fun ψ => AVExpr.const .quot [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    hbase hag
    (fun ψ => by rw [hcv ψ]; rfl)
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, denoteP_quotA_type ψ⟩) ?_ ?_
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [denoteP_quotA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_okP (bitAgree_quotA ψ) ρ).mpr
      (AnnotOkP_bconst_type V .quot [ψ uN] ρ)
  · intro ψ ta h ρ
    rw [denoteP_quotA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AVExpr.BitAgree.interp2_eq V (bitAgree_quotA ψ) ρ]
    exact bval2_mem_type V .quot [ψ uN] ρ

/-- **`Quot.mk`, installed at the P tier.** -/
theorem extendQuotMkP (mp : EnvS2PM V μ env)
    (hQ : env.find? quotName = some quotA)
    (hfresh : env.find? quotMkName = none)
    (hbase : EnvS V ⟨quotMkA :: env.consts⟩)
    (hag : ∀ n, n ≠ quotMkA.name → mp.base2.base.cval n = hbase.cval n)
    (hcv : ∀ ψ, hbase.cval quotMkA.name ψ
      = VExpr.const .quotMk [ψ uN]) :
    Nonempty (EnvS2PM V μ ⟨quotMkA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_quotMkA_type (m := mp.base2)
      (A := fun ψ => AVExpr.const .quotMk [ψ uN]) ψ hQ
  refine declStepPM_of_basis_cons mp
    (A := fun ψ => AVExpr.const .quotMk [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    hbase hag
    (fun ψ => by rw [hcv ψ]; rfl)
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_okP (bitAgree_quotMkA ψ) ρ).mpr
      (AnnotOkP_bconst_type V .quotMk [ψ uN] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AVExpr.BitAgree.interp2_eq V (bitAgree_quotMkA ψ) ρ]
    exact bval2_mem_type V .quotMk [ψ uN] ρ

end Quot

end Setlec.SetR.Interp2
