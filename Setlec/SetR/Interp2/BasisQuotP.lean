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
def quotRelTyP : AVExpr :=
  .pi 0 1 (.bvar 0) (.pi 0 1 (.bvar 1) (.sort 0))

/-- **`Quot`'s type reading.** -/
theorem denoteP_quotA_type
    {acval : Name → (Name → Nat) → AVExpr} (ψ : Name → Nat) :
    denoteP acval ⟨quotA :: env.consts⟩ ψ 0 quotA.toConstantVal.type
      = some (.pi 0 (pwBit ψ .never) (.sort (ψ uN))
          (.pi 0 (pwBit ψ .never) (quotRelTyP) (.sort (ψ uN)))) := by
  simp [quotA, ConstantInfo.toConstantVal, denoteP_forallE,
    denoteP_sort, denoteP_fvar, Expr.instantiate1, quotRelTyP,
    pwBit_never, Level.eval, uN]

/-- **The `Quot` reading agrees with `BConst.type2`.**  Every binder in
the block's type formers is `.never`, so every numeral is `1` against a
successor or a `Nat.max _ 1`. -/
theorem bitAgree_quotRelTyP (j : Nat) :
    AVExpr.BitAgree quotRelTyP (relT2 j (.bvar 0)) :=
  .pi (Iff.intro (fun h => absurd h Nat.one_ne_zero)
      (fun h => absurd h (maxOne_ne_zero j)))
    (.bvar 0) (.pi Iff.rfl (.bvar 1) (.sort 0))

theorem bitAgree_quotA (ψ : Name → Nat) :
    AVExpr.BitAgree
      (.pi 0 (pwBit ψ .never) (.sort (ψ uN))
        (.pi 0 (pwBit ψ .never) (quotRelTyP) (.sort (ψ uN))))
      (BConst.type2 .quot [ψ uN]) := by
  have h1 : pwBit ψ Setlec.PropWhen.never = 0 ↔ ψ uN + 1 = 0 := by
    rw [pwBit_never]
    exact Iff.intro (fun h => nomatch h) (fun h => nomatch h)
  exact .pi h1 (.sort _) (.pi h1 (bitAgree_quotRelTyP (ψ uN))
    (.sort _))

/-- `Quot.mk`'s type reading, named: three binders at the pin's bit. -/
def quotMkTyP (b u : Nat) : AVExpr :=
  .pi 0 b (.sort u)
    (.pi 0 b quotRelTyP
      (.pi 0 b (.bvar 1)
        (.app (.app (.const .quot [u]) (.bvar 2)) (.bvar 1))))

/-- **`Quot.mk`'s type reading.**  Stated at *any* extension whose cons
is neither `Quot` nor `Quot.mk` as well, because both recursor rows
read it as their fired constructor's telescope (`TVja`). -/
theorem denoteP_quotMkTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = quotName)
    (hQ : env.find? quotName = some quotA) :
    denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ 0
        quotMkA.toConstantVal.type
      = some (quotMkTyP (pwBit ψ (.ifAllZero [uN])) (ψ uN)) := by
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
    quotRelTyP, quotMkTyP, pwBit_never, hQc, Level.eval, uN]

theorem denoteP_quotMkA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA) :
    denoteP (acvalWith m.acval quotMkA.name A)
        ⟨quotMkA :: env.consts⟩ ψ 0 quotMkA.toConstantVal.type
      = some (quotMkTyP (pwBit ψ (.ifAllZero [uN])) (ψ uN)) :=
  denoteP_quotMkTy (m := m) (A := A) ψ (by decide) hQ

theorem bitAgree_quotMkA (ψ : Name → Nat) :
    AVExpr.BitAgree (quotMkTyP (pwBit ψ (.ifAllZero [uN])) (ψ uN))
      (BConst.type2 .quotMk [ψ uN]) := by
  have hz : pwBit ψ (Setlec.PropWhen.ifAllZero [uN]) = 0 ↔ ψ uN = 0 :=
    pwBit_ifAllZero_single ψ uN
  rw [quotMkTyP]
  exact .pi hz (.sort _)
    (.pi hz (bitAgree_quotRelTyP (ψ uN))
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

/-! ## `Quot.ind`

The block's `Prop`-valued eliminator.  Every one of its binders is
pinned `.ifAllZero []`, so `pwBit_ifAllZero_nil` makes **every numeral
in the reading the literal `0`** — the reading is stated that way, and
the whole tower then lives in the squash regime.  `bval2 .quotInd` is
`pt` for the same reason (its result sort *is* `0`), so the row's
fired equality is `pt = pt` by `app_pt` and needs no value law at
all. -/

/-- `@Quot.{u} A r`, at two de Bruijn slots. -/
def quotAppP (u i j : Nat) : AVExpr :=
  .app (.app (.const .quot [u]) (.bvar i)) (.bvar j)

/-- `@Quot.mk.{u} A r a`, at three de Bruijn slots. -/
def quotMkAppP (u i j k : Nat) : AVExpr :=
  .app (.app (.app (.const .quotMk [u]) (.bvar i)) (.bvar j)) (.bvar k)

/-- `Quot.ind`'s motive binder domain reading. -/
def quotIndMotiveTyP (u : Nat) : AVExpr :=
  .pi 0 1 (quotAppP u 1 0) (.sort 0)

/-- `Quot.ind`'s minor binder domain reading. -/
def quotIndMinorTyP (u : Nat) : AVExpr :=
  .pi 0 0 (.bvar 2) (.app (.bvar 1) (quotMkAppP u 3 2 0))

/-- The motive space: `Quot A r → Prop`. -/
noncomputable def quotIndMotiveSpace (V : Type w) [SetTheory V]
    (u : Nat) (Aset R : V) : V :=
  piR 1 (quotSet u Aset R) fun _ => (univ 0 : V)

/-- The minor space: `∀ a, M (Quot.mk a)`. -/
noncomputable def quotIndMinorSpace (V : Type w) [SetTheory V]
    (u : Nat) (Aset R M : V) : V :=
  piR 0 Aset fun a => app M (quotClass u Aset R a)

/-! ### The two applied formers, graded and evaluated

`Quot A r` and `Quot.mk A r a` occur at four different de Bruijn
depths across the block, so both are stated against an arbitrary
environment through its slot values.  The `∃ w S F` witnesses are
`bconst_app_data2`/`_data3` — nothing is chosen. -/

theorem relT2_interp (u : Nat) (ρ : Nat → V) (Aset : V) :
    interp2 V (cons Aset ρ) (relT2 u (.bvar 0)) = relSpace2 V u Aset := by
  simp [relT2, relSpace2, AVExpr.lift, AVExpr.liftN, interp2_pi,
    interp2_bvar, interp2_sort, cons]

theorem quotRelTyP_interp (u : Nat) (ρ : Nat → V) (Aset : V) :
    interp2 V (cons Aset ρ) quotRelTyP = relSpace2 V u Aset := by
  rw [← relT2_interp u ρ Aset]
  exact AVExpr.BitAgree.interp2_eq V (bitAgree_quotRelTyP u) _

/-- The relation binder's domain is graded, unconditionally: both of
its binders are in the graph regime. -/
theorem quotRelTyP_okP (ρ : Nat → V) : AnnotOkP V ρ quotRelTyP :=
  ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩,
    ⟨trivial,
      fun _ _ => ⟨trivial, fun _ _ => trivial,
        fun h => absurd h Nat.one_ne_zero⟩,
      fun h => absurd h Nat.one_ne_zero⟩⟩

theorem quotApp_data {u i j : Nat} {ρ : Nat → V} {Aset R : V}
    (hi : ρ i = Aset) (hj : ρ j = R)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace2 V u Aset) :
    AnnotOk2 V ρ (quotAppP u i j) ∧ AnnotValidV V ρ (quotAppP u i j) ∧
      interp2 V ρ (quotAppP u i j) = quotSet u Aset R := by
  have hAi : interp2 V ρ (AVExpr.bvar i) = Aset := by
    rw [interp2_bvar, hi]
  have hRj : interp2 V ρ (AVExpr.bvar j) = R := by
    rw [interp2_bvar, hj]
  have hA' : Aset ∈ˢ interp2 V ρ (AVExpr.sort u) := by
    rw [interp2_sort]; exact hA
  have hR' : R ∈ˢ interp2 V (cons Aset ρ) (relT2 u (.bvar 0)) := by
    rw [relT2_interp]; exact hR
  refine ⟨?_, ⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩
  · rw [quotAppP, AnnotOk2_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [AnnotOk2_app]
      refine ⟨trivial, trivial, ?_⟩
      have h := bconst_app_data V .quot [u] ρ (A := .sort u) rfl hA'
      rw [← hAi] at h
      exact h
    · have h := bconst_app_data2 V .quot [u] ρ
        (A := .sort u) (A2 := relT2 u (.bvar 0)) rfl hA' hR'
      rw [← hAi, ← hRj] at h
      simpa [interp2_const, bval2, Setlec.TT.lv] using h
  · rw [quotAppP]
    simp only [interp2_app, interp2_const, bval2, Setlec.TT.lv,
      List.getD_cons_zero, hAi, hRj]
    exact quotV2_app V hA hR

theorem quotMkApp_data {u i j k : Nat} {ρ : Nat → V} {Aset R a : V}
    (hi : ρ i = Aset) (hj : ρ j = R) (hk : ρ k = a)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace2 V u Aset)
    (ha : a ∈ˢ Aset) :
    AnnotOk2 V ρ (quotMkAppP u i j k) ∧
      AnnotValidV V ρ (quotMkAppP u i j k) ∧
      interp2 V ρ (quotMkAppP u i j k) = quotClass u Aset R a := by
  have hAi : interp2 V ρ (AVExpr.bvar i) = Aset := by
    rw [interp2_bvar, hi]
  have hRj : interp2 V ρ (AVExpr.bvar j) = R := by
    rw [interp2_bvar, hj]
  have hak : interp2 V ρ (AVExpr.bvar k) = a := by
    rw [interp2_bvar, hk]
  have hA' : Aset ∈ˢ interp2 V ρ (AVExpr.sort u) := by
    rw [interp2_sort]; exact hA
  have hR' : R ∈ˢ interp2 V (cons Aset ρ) (relT2 u (.bvar 0)) := by
    rw [relT2_interp]; exact hR
  have ha' : a ∈ˢ interp2 V (cons R (cons Aset ρ)) (AVExpr.bvar 1) := by
    simpa [interp2_bvar, cons] using ha
  refine ⟨?_, ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩, ?_⟩
  · rw [quotMkAppP, AnnotOk2_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [AnnotOk2_app]
      refine ⟨?_, trivial, ?_⟩
      · rw [AnnotOk2_app]
        refine ⟨trivial, trivial, ?_⟩
        have h := bconst_app_data V .quotMk [u] ρ (A := .sort u) rfl hA'
        rw [← hAi] at h
        exact h
      · have h := bconst_app_data2 V .quotMk [u] ρ
          (A := .sort u) (A2 := relT2 u (.bvar 0)) rfl hA' hR'
        rw [← hAi, ← hRj] at h
        simpa [interp2_const, bval2, Setlec.TT.lv] using h
    · have h := bconst_app_data3 V .quotMk [u] ρ
        (A := .sort u) (A2 := relT2 u (.bvar 0)) (A3 := .bvar 1)
        rfl hA' hR' ha'
      rw [← hAi, ← hRj, ← hak] at h
      simpa [interp2_const, bval2, Setlec.TT.lv] using h
  · rw [quotMkAppP]
    simp only [interp2_app, interp2_const, bval2, Setlec.TT.lv,
      List.getD_cons_zero, hAi, hRj, hak]
    exact quotMkV2_app V hA hR ha

/-! ### The motive and minor spaces -/

theorem quotIndMotiveTyP_interp {u : Nat} {Aset R : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace2 V u Aset) :
    interp2 V (cons R (cons Aset ρ)) (quotIndMotiveTyP u)
      = quotIndMotiveSpace V u Aset R := by
  rw [quotIndMotiveTyP, interp2_pi, quotIndMotiveSpace,
    (quotApp_data (u := u) (i := 1) (j := 0) (ρ := cons R (cons Aset ρ))
      (by simp [cons]) (by simp [cons]) hA hR).2.2]
  exact piR_congr fun _ _ => by rw [interp2_sort]

theorem quotIndMinorTyP_interp {u : Nat} {Aset R M : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace2 V u Aset) :
    interp2 V (cons M (cons R (cons Aset ρ))) (quotIndMinorTyP u)
      = quotIndMinorSpace V u Aset R M := by
  rw [quotIndMinorTyP, interp2_pi, quotIndMinorSpace]
  simp only [interp2_bvar, cons]
  refine piR_congr fun a ha => ?_
  rw [interp2_app,
    (quotMkApp_data (u := u) (i := 3) (j := 2) (k := 0)
      (ρ := cons a (cons M (cons R (cons Aset ρ))))
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      hA hR ha).2.2]
  simp [interp2_bvar, cons]

/-! ### The type reading -/

/-- `Quot.ind`'s type reading, named: five binders, every numeral the
literal `0`. -/
def quotIndTyP (u : Nat) : AVExpr :=
  .pi 0 0 (.sort u)
    (.pi 0 0 quotRelTyP
      (.pi 0 0 (quotIndMotiveTyP u)
        (.pi 0 0 (quotIndMinorTyP u)
          (.pi 0 0 (quotAppP u 3 2) (.app (.bvar 2) (.bvar 0))))))

/-- **`Quot.ind`'s type reading.** -/
theorem denoteP_quotIndA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA) :
    denoteP (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ 0 quotIndA.toConstantVal.type
      = some (quotIndTyP (ψ uN)) := by
  have hQc : ∀ d : Nat,
      denoteP (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ d (.const quotName [.param uN])
        = some (AVExpr.const .quot [ψ uN]) := fun d =>
    denoteP_quotLeaf (m := m) (A := A) ψ (by decide) hQ d
      (Level.param uN)
  have hMc : ∀ d : Nat,
      denoteP (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ d (.const quotMkName [.param uN])
        = some (AVExpr.const .quotMk [ψ uN]) := fun d =>
    denoteP_quotMkLeaf (m := m) (A := A) ψ (by decide) hM d
      (Level.param uN)
  rw [show quotIndA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "\u03b1") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default, pw := .never })
              { bi := .default, pw := .never })
            (Expr.forallE (Name.anonymous.str "\u03b2")
              (Expr.forallE (Name.anonymous.str "a")
                (.app (.app (.const quotName [.param uN]) (.bvar 1))
                  (.bvar 0)) (.sort .zero)
                { bi := .default, pw := .never })
              (Expr.forallE (Name.anonymous.str "mk")
                (Expr.forallE (Name.anonymous.str "a") (.bvar 2)
                  (.app (.bvar 1)
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 3)) (.bvar 2)) (.bvar 0)))
                  { bi := .default, pw := .ifAllZero [] })
                (Expr.forallE (Name.anonymous.str "q")
                  (.app (.app (.const quotName [.param uN]) (.bvar 3))
                    (.bvar 2))
                  (.app (.bvar 2) (.bvar 0))
                  { bi := .default, pw := .ifAllZero [] })
                { bi := .default, pw := .ifAllZero [] })
              { bi := .implicit, pw := .ifAllZero [] })
            { bi := .implicit, pw := .ifAllZero [] })
          { bi := .implicit, pw := .ifAllZero [] } from rfl]
  simp [denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    Expr.instantiate1, quotRelTyP, quotAppP, quotMkAppP,
    quotIndMotiveTyP, quotIndMinorTyP, quotIndTyP, pwBit_never,
    pwBit_ifAllZero_nil, hQc, hMc, Level.eval]

theorem bitAgree_quotIndA (ψ : Name → Nat) :
    AVExpr.BitAgree (quotIndTyP (ψ uN))
      (BConst.type2 .quotInd [ψ uN]) :=
  .pi Iff.rfl (.sort _)
    (.pi Iff.rfl (bitAgree_quotRelTyP (ψ uN))
      (.pi Iff.rfl
        (.pi Iff.rfl (.app (.app (.const _ _) (.bvar 1)) (.bvar 0))
          (.sort 0))
        (.pi Iff.rfl
          (.pi Iff.rfl (.bvar 2)
            (.app (.bvar 1)
              (.app (.app (.app (.const _ _) (.bvar 3)) (.bvar 2))
                (.bvar 0))))
          (.pi Iff.rfl (.app (.app (.const _ _) (.bvar 3)) (.bvar 2))
            (.app (.bvar 2) (.bvar 0))))))

/-! ### The squash-regime kit

Everything `Quot.ind` builds — its tower, its rule's right-hand side,
and every application of either — lives at bit `0`, where `lamR` is
`pt` and a fibre only has to be an inhabited truth value.  These three
lemmas are that observation, stated once; `Quot.sound` and (at the
`PSigma'` block) `PSigma'.rec` read them too. -/

/-- The inhabited truth value a squash-regime tower's grading picks for
its fibre: `True`, as a `piR 0`. -/
noncomputable def unitPropR (V : Type w) [SetTheory V] : V :=
  piR 0 (unitSet : V) fun _ => unitSet

theorem unitPropR_mem_univZero : unitPropR V ∈ˢ (univZero : V) :=
  piR_zero_mem_univZero

theorem pt_mem_unitPropR : (pt : V) ∈ˢ unitPropR V :=
  pt_mem_piR_zero fun _ _ => ⟨pt, pt_mem_unitSet⟩

/-- **A squash-regime `λ` whose body is the canonical proof is graded**
— the fibre is `unitPropR`, and both of `AnnotOk2`'s residual
obligations are its two facts. -/
theorem AnnotOkP_lam_zero_pt {ρ : Nat → V} {Aa b : AVExpr}
    (hA : AnnotOkP V ρ Aa)
    (hb : ∀ x, x ∈ˢ interp2 V ρ Aa → AnnotOkP V (cons x ρ) b)
    (hpt : ∀ x, x ∈ˢ interp2 V ρ Aa → interp2 V (cons x ρ) b = pt) :
    AnnotOkP V ρ (.lam 0 Aa b) := by
  refine ⟨?_, ?_⟩
  · rw [AnnotOk2_lam]
    exact ⟨hA.1, fun x hx => (hb x hx).1, fun _ => unitPropR V,
      fun x hx => by rw [hpt x hx]; exact pt_mem_unitPropR,
      fun _ x _ => unitPropR_mem_univZero⟩
  · rw [AnnotValidV_lam]
    exact ⟨hA.2, fun x hx => (hb x hx).2⟩

/-- **The canonical proof applied to anything is graded, and is again
the canonical proof.**  The `∃ w S F` witness is `w = 0`, the
argument's own domain, and the constant `unitPropR` fibre. -/
theorem AnnotOkP_app_pt {ρ : Nat → V} {f a : AVExpr} {S : V}
    (hf : AnnotOkP V ρ f) (hfi : interp2 V ρ f = pt)
    (ha : AnnotOkP V ρ a) (hmem : interp2 V ρ a ∈ˢ S) :
    AnnotOkP V ρ (.app f a) ∧ interp2 V ρ (.app f a) = pt := by
  refine ⟨⟨?_, ⟨hf.2, ha.2⟩⟩, by rw [interp2_app, hfi, app_pt]⟩
  rw [AnnotOk2_app]
  exact ⟨hf.1, ha.1, 0, S, fun _ => unitPropR V,
    by rw [hfi]; exact pt_mem_piR_zero fun _ _ => ⟨pt, pt_mem_unitPropR⟩,
    hmem, fun _ _ _ => unitPropR_mem_univZero⟩

/-! ### The two domains, graded -/

theorem quotIndMotiveTyP_okP {u : Nat} {Aset R : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace2 V u Aset) :
    AnnotOkP V (cons R (cons Aset ρ)) (quotIndMotiveTyP u) := by
  obtain ⟨hok, hval, -⟩ := quotApp_data (u := u) (i := 1) (j := 0)
    (ρ := cons R (cons Aset ρ)) (by simp [cons]) (by simp [cons]) hA hR
  exact ⟨⟨hok, fun _ _ => trivial⟩,
    ⟨hval, fun _ _ => trivial, fun h => absurd h Nat.one_ne_zero⟩⟩

theorem quotIndMinorTyP_okP {u : Nat} {Aset R M : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace2 V u Aset)
    (hM : M ∈ˢ quotIndMotiveSpace V u Aset R) :
    AnnotOkP V (cons M (cons R (cons Aset ρ))) (quotIndMinorTyP u) := by
  have hdom : interp2 V (cons M (cons R (cons Aset ρ)))
      (AVExpr.bvar 2) = Aset := by simp [interp2_bvar, cons]
  have hstep : ∀ a : V, a ∈ˢ Aset →
      (AnnotOk2 V (cons a (cons M (cons R (cons Aset ρ))))
          (.app (.bvar 1) (quotMkAppP u 3 2 0)) ∧
        AnnotValidV V (cons a (cons M (cons R (cons Aset ρ))))
          (.app (.bvar 1) (quotMkAppP u 3 2 0))) ∧
      interp2 V (cons a (cons M (cons R (cons Aset ρ))))
        (.app (.bvar 1) (quotMkAppP u 3 2 0))
          ∈ˢ (univZero : V) := by
    intro a ha
    obtain ⟨hok, hval, hint⟩ := quotMkApp_data (u := u)
      (i := 3) (j := 2) (k := 0)
      (ρ := cons a (cons M (cons R (cons Aset ρ))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA hR ha
    have hMb : interp2 V (cons a (cons M (cons R (cons Aset ρ))))
        (AVExpr.bvar 1) = M := by simp [interp2_bvar, cons]
    have hcl : quotClass u Aset R a ∈ˢ quotSet u Aset R :=
      quotClass_mem ha
    have hMc : app M (quotClass u Aset R a) ∈ˢ (univ 0 : V) :=
      app_mem_piR_pos (A := quotSet u Aset R)
        (B := fun _ => (univ 0 : V)) Nat.one_ne_zero hM hcl
    refine ⟨⟨?_, ⟨trivial, hval⟩⟩, ?_⟩
    · rw [AnnotOk2_app]
      exact ⟨trivial, hok, 1, quotSet u Aset R, fun _ => (univ 0 : V),
        by rw [hMb]; exact hM, by rw [hint]; exact hcl,
        fun h => absurd h Nat.one_ne_zero⟩
    · rw [interp2_app, hMb, hint, ← univ_zero]
      exact hMc
  exact ⟨⟨trivial, fun a ha => (hstep a (by rwa [hdom] at ha)).1.1⟩,
    ⟨trivial, fun a ha => (hstep a (by rwa [hdom] at ha)).1.2,
      fun _ a ha => (hstep a (by rwa [hdom] at ha)).2⟩⟩

/-! ### The rule, its right-hand side, and the row -/

/-- `Quot.ind`'s rule's RHS reading. -/
def quotIndRaP (u : Nat) : AVExpr :=
  .lam 0 (.sort u)
    (.lam 0 quotRelTyP
      (.lam 0 (quotIndMotiveTyP u)
        (.lam 0 (quotIndMinorTyP u)
          (.lam 0 (.bvar 3) (.app (.bvar 1) (.bvar 0))))))

theorem quotIndRaP_interp (u : Nat) (ρ : Nat → V) :
    interp2 V ρ (quotIndRaP u) = (pt : V) := by
  rw [quotIndRaP, interp2_lam, lamR_zero]

/-- **`Quot.ind`'s RHS tower is graded** — five squash-regime `λ`s
whose bodies are all the canonical proof (the innermost because the
minor premise itself is, by `eq_pt_of_mem_piR_zero` on its
`Prop`-valued product). -/
theorem quotIndRaP_okP (u : Nat) (ρ : Nat → V) :
    AnnotOkP V ρ (quotIndRaP u) := by
  rw [quotIndRaP]
  refine AnnotOkP_lam_zero_pt ⟨trivial, trivial⟩ ?_
    (fun _ _ => by rw [interp2_lam, lamR_zero])
  intro Aset hAset
  rw [interp2_sort] at hAset
  refine AnnotOkP_lam_zero_pt (quotRelTyP_okP _) ?_
    (fun _ _ => by rw [interp2_lam, lamR_zero])
  intro R hR
  rw [quotRelTyP_interp u] at hR
  refine AnnotOkP_lam_zero_pt (quotIndMotiveTyP_okP ρ hAset hR) ?_
    (fun _ _ => by rw [interp2_lam, lamR_zero])
  intro M hM
  rw [quotIndMotiveTyP_interp ρ hAset hR] at hM
  refine AnnotOkP_lam_zero_pt (quotIndMinorTyP_okP ρ hAset hR hM) ?_
    (fun _ _ => by rw [interp2_lam, lamR_zero])
  intro mk hmk
  rw [quotIndMinorTyP_interp ρ hAset hR, quotIndMinorSpace] at hmk
  have hmkpt : mk = pt := eq_pt_of_mem_piR_zero hmk
  have hdom : interp2 V (cons mk (cons M (cons R (cons Aset ρ))))
      (AVExpr.bvar 3) = Aset := by simp [interp2_bvar, cons]
  have hbody : ∀ a : V, a ∈ˢ Aset →
      AnnotOkP V (cons a (cons mk (cons M (cons R (cons Aset ρ)))))
          (.app (.bvar 1) (.bvar 0)) ∧
        interp2 V (cons a (cons mk (cons M (cons R (cons Aset ρ)))))
          (.app (.bvar 1) (.bvar 0)) = pt := by
    intro a ha
    refine AnnotOkP_app_pt (S := Aset) ⟨trivial, trivial⟩ ?_
      ⟨trivial, trivial⟩ ?_
    · rw [interp2_bvar]
      show cons a (cons mk (cons M (cons R (cons Aset ρ)))) 1 = pt
      rw [show cons a (cons mk (cons M (cons R (cons Aset ρ)))) 1
        = mk from rfl]
      exact hmkpt
    · rw [interp2_bvar]
      exact ha
  refine AnnotOkP_lam_zero_pt ⟨trivial, trivial⟩ ?_ ?_
  · exact fun a ha => (hbody a (by rwa [hdom] at ha)).1
  · exact fun a ha => (hbody a (by rwa [hdom] at ha)).2

/-- **`Quot.ind`'s rule's RHS reading.** -/
theorem denoteP_quotInd_rhs (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA) :
    denoteP (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ 0 quotIndRule.rhs
      = some (quotIndRaP (ψ uN)) := by
  have hQc : ∀ d : Nat,
      denoteP (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ d (.const quotName [.param uN])
        = some (AVExpr.const .quot [ψ uN]) := fun d =>
    denoteP_quotLeaf (m := m) (A := A) ψ (by decide) hQ d
      (Level.param uN)
  have hMc : ∀ d : Nat,
      denoteP (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ d (.const quotMkName [.param uN])
        = some (AVExpr.const .quotMk [ψ uN]) := fun d =>
    denoteP_quotMkLeaf (m := m) (A := A) ψ (by decide) hM d
      (Level.param uN)
  simp only [quotIndRule]
  simp [denoteP_lam, denoteP_forallE, denoteP_sort, denoteP_app,
    denoteP_fvar, Expr.instantiate1, quotRelTyP, quotAppP, quotMkAppP,
    quotIndMotiveTyP, quotIndMinorTyP, quotIndRaP, pwBit_never,
    pwBit_ifAllZero_nil, hQc, hMc, Level.eval]

/-- **`Quot.ind`'s `RecRuleLawP` row.**  The rule is `.plain`, so both
`.nested` conjuncts are `nomatch`; the fired equality is `pt = pt`
(`bval2 .quotInd` is the canonical proof and so is the RHS tower), and
the transport is five `AnnotOkP_app_pt` steps whose domains come
straight off the two telescope fits — no domain has to be
identified. -/
theorem quotIndLawP {m : EnvS2Core V env}
    (m₂ : EnvS2Core V ⟨quotIndA :: env.consts⟩)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hac : m₂.acval = acvalWith m.acval quotIndA.name
      (fun ψ => AVExpr.const .quotInd [ψ uN]))
    (φ : Name → Nat) :
    RecRuleLawP m₂ φ quotIndA.name quotIndA.toConstantVal 4 4
      quotIndRule := by
  refine ⟨Nat.le_refl 4, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ quotIndA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hRa : denoteP m₂.acval ⟨quotIndA :: env.consts⟩ φ 0
      (quotIndRule.rhs.instantiateLevelParams
        quotIndA.toConstantVal.levelParams us)
      = some (quotIndRaP (ψ uN)) := by
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteP_quotInd_rhs (m := m) _ hQ hM]
  refine ⟨quotIndRaP (ψ uN), hRa, fun ρ => quotIndRaP_okP _ ρ, ?_, ?_⟩
  · intro _ _ h
    exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev hplain hnested hpin hTVa hTVja hfitR hfitC
  -- the fired constructor is `Quot.mk`, stored in the prefix
  have hM' : (⟨quotIndA :: env.consts⟩ : Env).find? quotMkName
      = some quotMkA := by
    rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hM
  rw [show RecRule.ctor quotIndRule = quotMkName from rfl, hM'] at hfj
  obtain ⟨rfl, rfl, rfl⟩ :
      cvj = quotMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 1 := by
    injection Option.some.inj hfj with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  obtain ⟨x1, x2, x3, x4, rfl⟩ : ∃ p q r s, xs = [p, q, r, s] := by
    match xs, hxs with
    | [p, q, r, s], _ => exact ⟨p, q, r, s, rfl⟩
  obtain ⟨y1, y2, y3, rfl⟩ : ∃ p q r, ys = [p, q, r] := by
    match ys, hys with
    | [p, q, r], _ => exact ⟨p, q, r, rfl⟩
  have hTyRead : denoteP m₂.acval ⟨quotIndA :: env.consts⟩ φ 0
      (quotIndA.toConstantVal.type.instantiateLevelParams
        quotIndA.toConstantVal.levelParams us)
      = some (quotIndTyP (ψ uN)) := by
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteP_quotIndA_type (m := m) _ hQ hM, ← hψ]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hCtorRead : denoteP m₂.acval ⟨quotIndA :: env.consts⟩ φ 0
      (quotMkA.toConstantVal.type.instantiateLevelParams
        quotMkA.toConstantVal.levelParams usj)
      = some (quotMkTyP
          (pwBit (Level.substFn φ quotMkA.toConstantVal.levelParams usj)
            (.ifAllZero [uN]))
          (Level.substFn φ quotMkA.toConstantVal.levelParams usj uN)) := by
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteP_quotMkTy (m := m) _ (by decide) hQ]
  obtain rfl : TVja = _ :=
    (Option.some.inj (hCtorRead.symm.trans hTVja)).symm
  have hrecL : m₂.acval quotIndA.name
      (Level.substFn φ quotIndA.toConstantVal.levelParams us)
      = AVExpr.const .quotInd [ψ uN] := by
    rw [hac, acvalWith_self, hψ]
  rw [quotIndTyP] at hfitR
  rw [quotMkTyP] at hfitC
  cases hfitR with | cons f1 hfitR =>
  cases hfitR with | cons f2 hfitR =>
  cases hfitR with | cons f3 hfitR =>
  cases hfitR with | cons f4 hfitR =>
  cases hfitR with | cons f5 _ =>
  cases hfitC with | cons g1 hfitC =>
  cases hfitC with | cons g2 hfitC =>
  cases hfitC with | cons g3 _ =>
  refine ⟨?_, ?_⟩
  · -- the fired equality: both sides are the canonical proof
    simp only [show RecRule.ctor quotIndRule = quotMkName from rfl,
      show quotIndRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      AVExpr.mkAppN_cons, AVExpr.mkAppN_nil,
      hrecL, interp2_app, interp2_const, bval2, quotIndRaP_interp,
      app_pt]
  · -- the transport: five squash-regime applications
    intro hxsA hysA
    simp only [show quotIndRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      AVExpr.mkAppN_cons, AVExpr.mkAppN_nil]
    have h1 := AnnotOkP_app_pt (quotIndRaP_okP (ψ uN) ρ)
      (quotIndRaP_interp (ψ uN) ρ) (hxsA x1 (by simp)) f1
    have h2 := AnnotOkP_app_pt h1.1 h1.2 (hxsA x2 (by simp)) f2
    have h3 := AnnotOkP_app_pt h2.1 h2.2 (hxsA x3 (by simp)) f3
    have h4 := AnnotOkP_app_pt h3.1 h3.2 (hxsA x4 (by simp)) f4
    exact (AnnotOkP_app_pt h4.1 h4.2 (hysA y3 (by simp)) g3).1

/-- **`Quot.ind`, installed at the P tier.** -/
theorem extendQuotIndP (mp : EnvS2PM V μ env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hfresh : env.find? quotIndA.name = none)
    (hbase : EnvS V ⟨quotIndA :: env.consts⟩)
    (hag : ∀ n, n ≠ quotIndA.name →
      mp.base2.base.cval n = hbase.cval n)
    (hcv : ∀ ψ, hbase.cval quotIndA.name ψ
      = VExpr.const .quotInd [ψ uN]) :
    Nonempty (EnvS2PM V μ ⟨quotIndA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_quotIndA_type (m := mp.base2)
      (A := fun ψ => AVExpr.const .quotInd [ψ uN]) ψ hQ hM
  refine declStepPM_of_basis_rec_cons mp
    (A := fun ψ => AVExpr.const .quotInd [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    hbase hag
    (fun ψ => by rw [hcv ψ]; rfl)
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_okP (bitAgree_quotIndA ψ) ρ).mpr
      (AnnotOkP_bconst_type V .quotInd [ψ uN] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AVExpr.BitAgree.interp2_eq V (bitAgree_quotIndA ψ) ρ]
    exact bval2_mem_type V .quotInd [ψ uN] ρ
  · intro m₂ hac φ
    refine recRulesP_cons_rec mp hfresh quotIndA_eq m₂ hac φ ?_
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact quotIndLawP (m := mp.base2) m₂ hQ hM hac φ
    · exact nomatch hr'

/-! ## The `Eq` bridge

`Quot.sound`'s and `Quot.lift`'s stored types conclude at the pinned
`Eq` former, whose annotated leaf is **not** `pinnedDirectT` (the
ENDGAME D finding) — it is the basis install's own tower.  v1 crosses
the gap with `EnvS.eq_lawV`; here the crossing is `EqLawP`, the
`EnvS2PM` field this very bundle supplies, and it crosses **both**
halves at once: its value half computes the spine, and its grading
half — which v1 has no analogue for, because `AnnotOkV` has no bit
content — is exactly the reading's `htyOk` obligation at that slot.

Both consumers below take the two halves as plain hypotheses at the
level the constant reads `Eq` at, so neither mentions `EnvS2PM`. -/

/-- The stored `Eq` former's leaf at a `Quot`-block extension: the
prefix's own, by `acvalWith_ne`. -/
theorem denoteP_eqLeaf {c₀ : ConstantInfo} (ψ : Name → Nat) (l : Level)
    (hne : ¬ c₀.name = eqName)
    (hE : env.find? eqName = some eqA) (d : Nat) :
    denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const eqName [l])
      = some (m.acval eqName (Level.substFn ψ [uN] [l])) := by
  have hf' : (⟨c₀ :: env.consts⟩ : Env).find? eqName = some eqA := by
    rw [Setlec.Env.find?_cons, if_neg hne]; exact hE
  rw [denoteP_const hf' (by rfl), acvalWith_ne (fun h => hne h.symm)]
  rfl

/-- The relation, applied to two of its arguments. -/
theorem relApp_data {u i j k : Nat} {ρ : Nat → V} {Aset R a b : V}
    (hi : ρ i = R) (hj : ρ j = a) (hk : ρ k = b)
    (hR : R ∈ˢ relSpace2 V u Aset) (ha : a ∈ˢ Aset) (hb : b ∈ˢ Aset) :
    AnnotOk2 V ρ (.app (.app (.bvar i) (.bvar j)) (.bvar k)) ∧
      AnnotValidV V ρ (.app (.app (.bvar i) (.bvar j)) (.bvar k)) ∧
      interp2 V ρ (.app (.app (.bvar i) (.bvar j)) (.bvar k))
        = app (app R a) b := by
  have hRi : interp2 V ρ (AVExpr.bvar i) = R := by rw [interp2_bvar, hi]
  have haj : interp2 V ρ (AVExpr.bvar j) = a := by rw [interp2_bvar, hj]
  have hbk : interp2 V ρ (AVExpr.bvar k) = b := by rw [interp2_bvar, hk]
  have hR' : R ∈ˢ piR (Nat.max u 1) Aset
      (fun _ => piR 1 Aset fun _ => (univ 0 : V)) := hR
  have hRa : app R a ∈ˢ piR 1 Aset fun _ => (univ 0 : V) :=
    app_mem_piR_pos (maxOne_ne_zero u) hR' ha
  refine ⟨?_, ⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩
  · rw [AnnotOk2_app]
    refine ⟨?_, trivial, 1, Aset, fun _ => (univ 0 : V), ?_, ?_,
      fun h => absurd h Nat.one_ne_zero⟩
    · rw [AnnotOk2_app]
      exact ⟨trivial, trivial, Nat.max u 1, Aset,
        fun _ => piR 1 Aset fun _ => (univ 0 : V),
        by rw [hRi]; exact hR',
        by rw [haj]; exact ha,
        fun h => absurd h (maxOne_ne_zero u)⟩
    · rw [interp2_app, hRi, haj]; exact hRa
    · rw [hbk]; exact hb
  · rw [interp2_app, interp2_app, hRi, haj, hbk]

/-! ## `Quot.sound`

The block's stored axiom, and the basis blocks' only one: its
`reduce_ops` row is the `hred` disjunct's second branch (`Quot.sound`
is not a trusted operation), unused by every earlier block.  Its type
is `Prop`-valued throughout, so the membership obligation is `pt` in a
five-deep `piR 0` — five `pt_mem_piR_zero` steps whose innermost
witness is the quotient's own soundness. -/

/-- `Quot.sound`'s type reading, named. -/
def quotSoundTyP (E : AVExpr) (u : Nat) : AVExpr :=
  .pi 0 0 (.sort u)
    (.pi 0 0 quotRelTyP
      (.pi 0 0 (.bvar 1)
        (.pi 0 0 (.bvar 2)
          (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
            (.app (.app (.app E (quotAppP u 4 3))
              (quotMkAppP u 4 3 2)) (quotMkAppP u 4 3 1))))))

/-- **`Quot.sound`'s type reading.** -/
theorem denoteP_quotSoundA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA) :
    denoteP (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts⟩ ψ 0 quotSoundA.toConstantVal.type
      = some (quotSoundTyP (m.acval eqName ψ) (ψ uN)) := by
  have hQc : ∀ d : Nat,
      denoteP (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts⟩ ψ d (.const quotName [.param uN])
        = some (AVExpr.const .quot [ψ uN]) := fun d =>
    denoteP_quotLeaf (m := m) (A := A) ψ (by decide) hQ d
      (Level.param uN)
  have hMc : ∀ d : Nat,
      denoteP (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts⟩ ψ d (.const quotMkName [.param uN])
        = some (AVExpr.const .quotMk [ψ uN]) := fun d =>
    denoteP_quotMkLeaf (m := m) (A := A) ψ (by decide) hM d
      (Level.param uN)
  have hEc : ∀ d : Nat,
      denoteP (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts⟩ ψ d (.const eqName [.param uN])
        = some (m.acval eqName ψ) := by
    intro d
    rw [denoteP_eqLeaf (m := m) (A := A) ψ (Level.param uN)
      (by decide) hE d,
      show ([Level.param uN] : List Level)
        = List.map Level.param [uN] from rfl,
      Level.substFn_param_self ψ [uN]]
  rw [show quotSoundA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default, pw := .never })
              { bi := .default, pw := .never })
            (Expr.forallE (Name.anonymous.str "a") (.bvar 1)
              (Expr.forallE (Name.anonymous.str "b") (.bvar 2)
                (Expr.forallE Name.anonymous
                  (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app (.const eqName [.param uN])
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 2)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 1)))
                  { bi := .default, pw := .ifAllZero [] })
                { bi := .implicit, pw := .ifAllZero [] })
              { bi := .implicit, pw := .ifAllZero [] })
            { bi := .implicit, pw := .ifAllZero [] })
          { bi := .implicit, pw := .ifAllZero [] } from rfl]
  simp [denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    Expr.instantiate1, quotRelTyP, quotAppP, quotMkAppP, quotSoundTyP,
    pwBit_never, pwBit_ifAllZero_nil, hQc, hMc, hEc, Level.eval]

/-- **A `Prop`-valued product's grading step**, stated so the five
binders of `Quot.sound`'s type (and the three of `Quot.lift`'s
invariance premise) are five applications of one lemma: the product is
graded and *is itself* a truth value, which is exactly what the next
binder out needs. -/
theorem AnnotOkP_pi_zero {ρ : Nat → V} {Aa B : AVExpr}
    (hA : AnnotOkP V ρ Aa)
    (hB : ∀ x, x ∈ˢ interp2 V ρ Aa → AnnotOkP V (cons x ρ) B)
    (hz : ∀ x, x ∈ˢ interp2 V ρ Aa →
      interp2 V (cons x ρ) B ∈ˢ (univZero : V)) :
    AnnotOkP V ρ (.pi 0 0 Aa B) ∧
      interp2 V ρ (.pi 0 0 Aa B) ∈ˢ (univZero : V) := by
  refine ⟨⟨⟨hA.1, fun x hx => (hB x hx).1⟩,
    ⟨hA.2, fun x hx => (hB x hx).2, fun _ x hx => hz x hx⟩⟩, ?_⟩
  rw [interp2_pi]
  exact piR_zero_mem_univZero

/-- **`Quot.sound`'s type reading is graded** — five
`AnnotOkP_pi_zero` steps whose innermost slot is `EqLawP`'s grading
half. -/
theorem quotSoundTyP_okP {E : AVExpr} {u : Nat} (ρ : Nat → V)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : AVExpr),
      AnnotOkP V ρ' Aa → AnnotOkP V ρ' la → AnnotOkP V ρ' ra →
      interp2 V ρ' Aa ∈ˢ (univ u : V) →
      interp2 V ρ' la ∈ˢ interp2 V ρ' Aa →
      interp2 V ρ' ra ∈ˢ interp2 V ρ' Aa →
      AnnotOkP V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp2 V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V)) :
    AnnotOkP V ρ (quotSoundTyP E u) := by
  -- the innermost slot: `EqLawP`'s grading half at the three spine
  -- arguments, whose readings are the block's two applied formers
  have hin : ∀ Aset R a b w : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace2 V u Aset → a ∈ˢ Aset → b ∈ˢ Aset →
      AnnotOkP V (cons w (cons b (cons a (cons R (cons Aset ρ)))))
          (.app (.app (.app E (quotAppP u 4 3)) (quotMkAppP u 4 3 2))
            (quotMkAppP u 4 3 1)) ∧
        interp2 V (cons w (cons b (cons a (cons R (cons Aset ρ)))))
          (.app (.app (.app E (quotAppP u 4 3)) (quotMkAppP u 4 3 2))
            (quotMkAppP u 4 3 1)) ∈ˢ (univZero : V) := by
    intro Aset R a b w hAset hR ha hb
    obtain ⟨hTok, hTval, hTint⟩ := quotApp_data (u := u) (i := 4) (j := 3)
      (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
      (by simp [cons]) (by simp [cons]) hAset hR
    obtain ⟨hlok, hlval, hlint⟩ := quotMkApp_data (u := u) (i := 4)
      (j := 3) (k := 2)
      (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR ha
    obtain ⟨hrok, hrval, hrint⟩ := quotMkApp_data (u := u) (i := 4)
      (j := 3) (k := 1)
      (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR hb
    exact hgr _ _ _ _ ⟨hTok, hTval⟩ ⟨hlok, hlval⟩ ⟨hrok, hrval⟩
      (by rw [hTint]; exact quotSet_mem_univ hAset)
      (by rw [hTint, hlint]; exact quotClass_mem ha)
      (by rw [hTint, hrint]; exact quotClass_mem hb)
  have h5 : ∀ Aset R a b : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace2 V u Aset → a ∈ˢ Aset → b ∈ˢ Aset →
      AnnotOkP V (cons b (cons a (cons R (cons Aset ρ))))
          (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
            (.app (.app (.app E (quotAppP u 4 3)) (quotMkAppP u 4 3 2))
              (quotMkAppP u 4 3 1))) ∧
        interp2 V (cons b (cons a (cons R (cons Aset ρ))))
          (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
            (.app (.app (.app E (quotAppP u 4 3)) (quotMkAppP u 4 3 2))
              (quotMkAppP u 4 3 1))) ∈ˢ (univZero : V) := by
    intro Aset R a b hAset hR ha hb
    obtain ⟨hrok, hrval, -⟩ := relApp_data (u := u) (i := 2) (j := 1)
      (k := 0) (ρ := cons b (cons a (cons R (cons Aset ρ))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hR ha hb
    exact AnnotOkP_pi_zero ⟨hrok, hrval⟩
      (fun w _ => (hin Aset R a b w hAset hR ha hb).1)
      (fun w _ => (hin Aset R a b w hAset hR ha hb).2)
  have h4 : ∀ Aset R a : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace2 V u Aset → a ∈ˢ Aset →
      AnnotOkP V (cons a (cons R (cons Aset ρ)))
          (.pi 0 0 (.bvar 2)
            (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
              (.app (.app (.app E (quotAppP u 4 3))
                (quotMkAppP u 4 3 2)) (quotMkAppP u 4 3 1)))) ∧
        interp2 V (cons a (cons R (cons Aset ρ)))
          (.pi 0 0 (.bvar 2)
            (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
              (.app (.app (.app E (quotAppP u 4 3))
                (quotMkAppP u 4 3 2)) (quotMkAppP u 4 3 1))))
          ∈ˢ (univZero : V) := by
    intro Aset R a hAset hR ha
    have hdom : interp2 V (cons a (cons R (cons Aset ρ)))
        (AVExpr.bvar 2) = Aset := by simp [interp2_bvar, cons]
    exact AnnotOkP_pi_zero (Aa := .bvar 2) ⟨trivial, trivial⟩
      (fun b hb => (h5 Aset R a b hAset hR ha (by rwa [hdom] at hb)).1)
      (fun b hb => (h5 Aset R a b hAset hR ha (by rwa [hdom] at hb)).2)
  have h3 : ∀ Aset R : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace2 V u Aset →
      AnnotOkP V (cons R (cons Aset ρ))
          (.pi 0 0 (.bvar 1)
            (.pi 0 0 (.bvar 2)
              (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                (.app (.app (.app E (quotAppP u 4 3))
                  (quotMkAppP u 4 3 2)) (quotMkAppP u 4 3 1))))) ∧
        interp2 V (cons R (cons Aset ρ))
          (.pi 0 0 (.bvar 1)
            (.pi 0 0 (.bvar 2)
              (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                (.app (.app (.app E (quotAppP u 4 3))
                  (quotMkAppP u 4 3 2)) (quotMkAppP u 4 3 1)))))
          ∈ˢ (univZero : V) := by
    intro Aset R hAset hR
    have hdom : interp2 V (cons R (cons Aset ρ)) (AVExpr.bvar 1)
        = Aset := by simp [interp2_bvar, cons]
    exact AnnotOkP_pi_zero (Aa := .bvar 1) ⟨trivial, trivial⟩
      (fun a ha => (h4 Aset R a hAset hR (by rwa [hdom] at ha)).1)
      (fun a ha => (h4 Aset R a hAset hR (by rwa [hdom] at ha)).2)
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ u : V) →
      AnnotOkP V (cons Aset ρ)
          (.pi 0 0 quotRelTyP
            (.pi 0 0 (.bvar 1)
              (.pi 0 0 (.bvar 2)
                (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app E (quotAppP u 4 3))
                    (quotMkAppP u 4 3 2)) (quotMkAppP u 4 3 1)))))) ∧
        interp2 V (cons Aset ρ)
          (.pi 0 0 quotRelTyP
            (.pi 0 0 (.bvar 1)
              (.pi 0 0 (.bvar 2)
                (.pi 0 0 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app E (quotAppP u 4 3))
                    (quotMkAppP u 4 3 2)) (quotMkAppP u 4 3 1))))))
          ∈ˢ (univZero : V) := by
    intro Aset hAset
    exact AnnotOkP_pi_zero (Aa := quotRelTyP) (quotRelTyP_okP _)
      (fun R hR => (h3 Aset R hAset
        (by rwa [quotRelTyP_interp u] at hR)).1)
      (fun R hR => (h3 Aset R hAset
        (by rwa [quotRelTyP_interp u] at hR)).2)
  rw [quotSoundTyP]
  exact (AnnotOkP_pi_zero (Aa := .sort u) ⟨trivial, trivial⟩
    (fun Aset hAset => (h2 Aset (by rwa [interp2_sort] at hAset)).1)
    (fun Aset hAset => (h2 Aset (by rwa [interp2_sort] at hAset)).2)).1

/-- **`Quot.sound` inhabits its type's reading.**  Five
`pt_mem_piR_zero` steps; the innermost witness is the quotient's own
soundness (`SetTheory.quotSound`), read through `EqLawP`'s value
half. -/
theorem quotSoundTyP_mem {E : AVExpr} {u : Nat} (ρ : Nat → V)
    (hval : ∀ (ρ' : Nat → V) (T a b : V), T ∈ˢ (univ u : V) →
      a ∈ˢ T → b ∈ˢ T →
      app (app (app (interp2 V ρ' E) T) a) b = eqv a b) :
    (pt : V) ∈ˢ interp2 V ρ (quotSoundTyP E u) := by
  rw [quotSoundTyP, interp2_pi]
  refine pt_mem_piR_zero fun Aset hAset => ⟨pt, ?_⟩
  rw [interp2_sort] at hAset
  rw [interp2_pi]
  refine pt_mem_piR_zero fun R hR => ⟨pt, ?_⟩
  rw [quotRelTyP_interp u] at hR
  rw [interp2_pi]
  refine pt_mem_piR_zero fun a ha => ⟨pt, ?_⟩
  rw [show interp2 V (cons R (cons Aset ρ)) (AVExpr.bvar 1) = Aset
    from by simp [interp2_bvar, cons]] at ha
  rw [interp2_pi]
  refine pt_mem_piR_zero fun b hb => ⟨pt, ?_⟩
  rw [show interp2 V (cons a (cons R (cons Aset ρ))) (AVExpr.bvar 2)
    = Aset from by simp [interp2_bvar, cons]] at hb
  rw [interp2_pi]
  refine pt_mem_piR_zero fun w hw => ⟨pt, ?_⟩
  obtain ⟨-, -, hrint⟩ := relApp_data (u := u) (i := 2) (j := 1) (k := 0)
    (ρ := cons b (cons a (cons R (cons Aset ρ))))
    (by simp [cons]) (by simp [cons]) (by simp [cons]) hR ha hb
  rw [hrint] at hw
  obtain ⟨-, -, hTint⟩ := quotApp_data (u := u) (i := 4) (j := 3)
    (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
    (by simp [cons]) (by simp [cons]) hAset hR
  obtain ⟨-, -, hlint⟩ := quotMkApp_data (u := u) (i := 4) (j := 3)
    (k := 2) (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
    (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR ha
  obtain ⟨-, -, hrint'⟩ := quotMkApp_data (u := u) (i := 4) (j := 3)
    (k := 1) (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
    (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR hb
  rw [interp2_app, interp2_app, interp2_app, hTint, hlint, hrint',
    hval _ _ _ _ (quotSet_mem_univ hAset) (quotClass_mem ha)
      (quotClass_mem hb),
    quotSound (u := u) ha hb hw]
  exact pt_mem_eqv_self _

/-- **`Quot.sound`, installed at the P tier** — the basis blocks' one
stored axiom, and the one place the `reduce_ops` disjunct's second
branch is taken. -/
theorem extendQuotSoundP (mp : EnvS2PM V μ env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA)
    (hfresh : env.find? quotSoundA.name = none)
    (hbase : EnvS V ⟨quotSoundA :: env.consts⟩)
    (hag : ∀ n, n ≠ quotSoundA.name →
      mp.base2.base.cval n = hbase.cval n)
    (hcv : ∀ ψ, hbase.cval quotSoundA.name ψ
      = VExpr.const .quotSound [ψ uN]) :
    Nonempty (EnvS2PM V μ ⟨quotSoundA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_quotSoundA_type (m := mp.base2)
      (A := fun ψ => AVExpr.const .quotSound [ψ uN]) ψ hQ hM hE
  refine declStepPM_of_basis_cons mp
    (A := fun ψ => AVExpr.const .quotSound [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inr (by decide))
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
    exact quotSoundTyP_okP ρ (mp.eq_lawP hE ψ).2
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [interp2_const]
    show (pt : V) ∈ˢ _
    exact quotSoundTyP_mem ρ (mp.eq_lawP hE ψ).1

end Quot

end Setlec.SetR.Interp2
