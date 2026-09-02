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

/-- **`Quot.mk`'s type reading.**  Stated at *any* extension whose cons
is neither `Quot` nor `Quot.mk` as well, because both recursor rows
read it as their fired constructor's telescope (`TVja`). -/
theorem denoteP_quotMkTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = quotName)
    (hQ : env.find? quotName = some quotA) :
    denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ 0
        quotMkA.toConstantVal.type
      = some (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.sort (ψ uN))
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (quotRelTyP)
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
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (quotRelTyP)
            (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.bvar 1)
              (.app (.app (.const .quot [ψ uN]) (.bvar 2))
                (.bvar 1))))) :=
  denoteP_quotMkTy (m := m) (A := A) ψ (by decide) hQ

theorem bitAgree_quotMkA (ψ : Name → Nat) :
    AVExpr.BitAgree
      (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.sort (ψ uN))
        (.pi 0 (pwBit ψ (.ifAllZero [uN])) (quotRelTyP)
          (.pi 0 (pwBit ψ (.ifAllZero [uN])) (.bvar 1)
            (.app (.app (.const .quot [ψ uN]) (.bvar 2)) (.bvar 1)))))
      (BConst.type2 .quotMk [ψ uN]) := by
  have hz : pwBit ψ (Setlec.PropWhen.ifAllZero [uN]) = 0 ↔ ψ uN = 0 :=
    pwBit_ifAllZero_single ψ uN
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

/-- **`Quot.ind`'s type reading.** -/
theorem denoteP_quotIndA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA) :
    denoteP (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts⟩ ψ 0 quotIndA.toConstantVal.type
      = some (.pi 0 0 (.sort (ψ uN))
          (.pi 0 0 (quotRelTyP)
            (.pi 0 0 (quotIndMotiveTyP (ψ uN))
              (.pi 0 0 (quotIndMinorTyP (ψ uN))
                (.pi 0 0 (quotAppP (ψ uN) 3 2)
                  (.app (.bvar 2) (.bvar 0))))))) := by
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
    quotIndMotiveTyP, quotIndMinorTyP, pwBit_never,
    pwBit_ifAllZero_nil, hQc, hMc, Level.eval]

theorem bitAgree_quotIndA (ψ : Name → Nat) :
    AVExpr.BitAgree
      (.pi 0 0 (.sort (ψ uN))
        (.pi 0 0 (quotRelTyP)
          (.pi 0 0 (quotIndMotiveTyP (ψ uN))
            (.pi 0 0 (quotIndMinorTyP (ψ uN))
              (.pi 0 0 (quotAppP (ψ uN) 3 2)
                (.app (.bvar 2) (.bvar 0)))))))
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

end Quot

end Setlec.SetR.Interp2
