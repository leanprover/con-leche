module

public import ConLeche.Model.BasisBlocks
import ConLeche.Semantics.BasisRules
import ConLeche.Model.Cover
import ConLeche.Verify.PropWhen

public section

/-!
# The `Quot` block, P tier (task #161)

The basis tier's fourth block, and the only one that

* stores an **axiom** (`Quot.sound` — the `hred` disjunct's second
  branch, unused by every earlier block), and
* reads a leaf that is **not** `pinnedStructT`: `Quot.lift`'s and
  `Quot.sound`'s stored types both mention the pinned `Eq` former,
  whose leaf is the basis install's own tower.  The P tier
  crosses that gap with **`EqLaw`** — the `EnvModelM` field whose
  *supplier* is the `Eq` block, and whose grading half is exactly what
  the reading's `htyOk` row needs.  The field is
  available at the `Quot` cons because `DeclBasisRun`'s first conjunct
  puts `Eq` in the prefix.

Everything else is the `BasisBlocks.lean` recipe: five pinned
towers, five type readings, two `.plain` `RecRuleLaw` rows.  Both
recursors' motives land in `Sort 0`, so both rows are `Prop`-motive
rows; `Quot.ind`'s fired equality is `pt = pt`.  The relation
space's reading is `SetModel`'s `relSpace`, the space the value
constants abstract over.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule uN u1N vN)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env}

section Quot

/- The pins are written in the builder's vocabulary; the readings below walk
them as plain `Expr` trees. -/
attribute [local simp] ConLeche.BasisDSL.bv ConLeche.BasisDSL.srt ConLeche.BasisDSL.prop
  ConLeche.BasisDSL.cnst ConLeche.BasisDSL.pi ConLeche.BasisDSL.piI ConLeche.BasisDSL.piA
  ConLeche.BasisDSL.ap2 ConLeche.BasisDSL.ap3 ConLeche.BasisDSL.u ConLeche.BasisDSL.v ConLeche.BasisDSL.uN ConLeche.BasisDSL.vN ConLeche.BasisDSL.bn
  ConLeche.quotRel ConLeche.quotLiftF ConLeche.quotLiftH ConLeche.quotIndMotive ConLeche.quotIndMk

open ConLeche (quotA quotMkA quotLiftA quotIndA quotSoundA quotName
  quotMkName quotLiftName quotIndName quotSoundName eqA eqName)

variable {m : EnvModel V env} {A : (Name → Nat) → Term}

/-! ## The block's two pinned leaves

`Quot` and `Quot.mk` are read by every later constant in the block. -/

/-- The pinned `Quot` leaf at an extension, at any level. -/
theorem denote_quotLeaf {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = quotName)
    (hQ : env.find? quotName = some quotA) (d : Nat) (l : Level) :
    denote (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ d
        (.const quotName [l])
      = some (Term.const .quot [l.eval ψ]) := by
  refine denote_pinned_const (m := m) hne hQ (by decide) (by rfl) ?_ d
  simp +decide [ConLeche.Verify.pinnedStructT]
  show Level.substFn ψ [uN] [l] uN = Level.eval ψ l
  simp [Level.substFn]

/-- The pinned `Quot.mk` leaf at an extension, at any level. -/
theorem denote_quotMkLeaf {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = quotMkName)
    (hM : env.find? quotMkName = some quotMkA) (d : Nat) (l : Level) :
    denote (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ d
        (.const quotMkName [l])
      = some (Term.const .quotMk [l.eval ψ]) := by
  refine denote_pinned_const (m := m) hne hM (by decide) (by rfl) ?_ d
  simp +decide [ConLeche.Verify.pinnedStructT]
  show Level.substFn ψ [uN] [l] uN = Level.eval ψ l
  simp [Level.substFn]

/-! ## `Quot` and `Quot.mk` -/

/-- The relation binder's domain reading — shared by every constant in
the block, and `.never` at both of its own binders. -/
def quotRelTy : Term :=
  .pi (.bvar 0) (.pi (.bvar 1) (.sort 0))

/-- **`Quot`'s type reading.** -/
theorem denote_quotA_type
    {acval : Name → (Name → Nat) → Term} (ψ : Name → Nat) :
    denote acval ⟨quotA :: env.consts, env.tables⟩ ψ 0 quotA.toConstantVal.type
      = some (.pi (.sort (ψ uN))
          (.pi (quotRelTy) (.sort (ψ uN)))) := by
  simp [quotA, ConstantInfo.toConstantVal, denote_forallE,
    denote_sort, denote_fvar, Expr.instantiate1, quotRelTy,
    Level.eval, uN]

/-- The relation binder's domain is `BConst.typeAV`'s relation type. -/
theorem quotRelTy_eq : quotRelTy = relAV (.bvar 0) := by rfl

/-- **The `Quot` reading is `BConst.typeAV`'s.** -/
theorem quotA_reading_eq (ψ : Name → Nat) :
    (Term.pi (.sort (ψ uN)) (.pi (quotRelTy) (.sort (ψ uN))))
      = BConst.typeAV .quot [ψ uN] := by rfl

/-- `Quot.mk`'s type reading, named: three binders. -/
def quotMkTy (u : Nat) : Term :=
  .pi (.sort u)
    (.pi quotRelTy
      (.pi (.bvar 1)
        (.app (.app (.const .quot [u]) (.bvar 2)) (.bvar 1))))

/-- **`Quot.mk`'s type reading.**  Stated at *any* extension whose cons
is neither `Quot` nor `Quot.mk` as well, because both recursor rows
read it as their fired constructor's telescope (`TVja`). -/
theorem denote_quotMkTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = quotName)
    (hQ : env.find? quotName = some quotA) :
    denote (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ 0
        quotMkA.toConstantVal.type
      = some (quotMkTy (ψ uN)) := by
  have hQc : ∀ d : Nat,
      denote (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ d
        (Expr.const quotName
          [Level.param (Name.str Name.anonymous "u")])
        = some (Term.const .quot
            [ψ (Name.str Name.anonymous "u")]) := by
    intro d
    exact denote_quotLeaf (m := m) (A := A) (c₀ := c₀) ψ hne hQ d
      (Level.param uN)
  simp [quotMkA, ConstantInfo.toConstantVal, denote_forallE,
    denote_sort, denote_app, denote_fvar, Expr.instantiate1,
    quotRelTy, quotMkTy, hQc, Level.eval, uN]

theorem denote_quotMkA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA) :
    denote (acvalWith m.acval quotMkA.name A)
        ⟨quotMkA :: env.consts, env.tables⟩ ψ 0 quotMkA.toConstantVal.type
      = some (quotMkTy (ψ uN)) :=
  denote_quotMkTy (m := m) (A := A) ψ (by decide) hQ

/-- **The `Quot.mk` reading is `BConst.typeAV`'s.** -/
theorem quotMkA_reading_eq (ψ : Name → Nat) :
    quotMkTy (ψ uN) = BConst.typeAV .quotMk [ψ uN] := by rfl

theorem relAV_interp (ρ : Nat → V) (Aset : V) :
    interp V (cons Aset ρ) (relAV (.bvar 0)) = relSpace V Aset := by
  simp [relAV, relSpace, Term.lift, Term.liftN, interp_pi,
    interp_bvar, interp_sort, cons]

theorem quotRelTy_interp (ρ : Nat → V) (Aset : V) :
    interp V (cons Aset ρ) quotRelTy = relSpace V Aset := by
  rw [quotRelTy_eq]; exact relAV_interp ρ Aset

theorem IsTy_relSpace (Aset : V) : IsTy (relSpace V Aset) := IsTy_piV

/-! ### The first two installs -/

/-- **`Quot`, installed at the P tier.** -/
theorem extendQuot (mp : EnvModelM V env)
    (hfresh : env.find? quotName = none)
    (hwf : EnvWF ⟨quotA :: env.consts, env.tables⟩) {ex : List Name} :
    CoverTo mp ex ⟨quotA :: env.consts, env.tables⟩ ex := by
  refine coverTo_cons hfresh (fun _ _ _ => rfl) (declStep_preserves_of_basis_cons mp
    (A := fun ψ => Term.const .quot [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT quotA.name ψ
          = some (Term.const .quot [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]) (fun _ _ _ _ _ h => nomatch h))
    ?_
    (fun _ _ => trivial)
    (fun ψ => ⟨_, denote_quotA_type ψ⟩) ?_ ?_
    (hind := indStrictHead_cons
      (ab := fun ψ => [.sort (ψ uN), quotRelTy])
      (s := fun ψ => ψ uN) (fun ψ => denote_quotA_type ψ) fun ψ hu ρ vs hsp => by
        match vs, hsp with
        | [Aset, R], ⟨hA, hR, _⟩ =>
          have hR' : R ∈ˢ relSpace V Aset := by
            rw [quotRelTy_interp ρ Aset] at hR; exact hR
          show Strict (SetTheory.app (SetTheory.app (quotV V (ψ uN)) Aset) R)
          have hA' : Aset ∈ˢ (univ (ψ uN) : V) := hA
          rw [quotV_app V hA' hR']
          exact strict_quotSet hu Aset R))
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [denote_quotA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [quotA_reading_eq]
    exact WellDenotedTy_bconst_type V .quot [ψ uN] ρ
  · intro ψ ta h ρ
    rw [denote_quotA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [quotA_reading_eq]
    exact bval_mem_type V .quot [ψ uN] ρ

/-- **`Quot.mk`, installed at the P tier.** -/
theorem extendQuotMk (mp : EnvModelM V env)
    (hQ : env.find? quotName = some quotA)
    (hfresh : env.find? quotMkName = none)
    (hwf : EnvWF ⟨quotMkA :: env.consts, env.tables⟩) {ex : List Name} :
    CoverTo mp ex ⟨quotMkA :: env.consts, env.tables⟩ ex := by
  have hty := fun ψ =>
    denote_quotMkA_type (m := mp.base2)
      (A := fun ψ => Term.const .quotMk [ψ uN]) ψ hQ
  refine coverTo_cons hfresh (fun _ _ h => nomatch h)
    (hhead := hhead_ctor (c₀ := quotMkA) rfl rfl rfl (Or.inr ⟨_, _, hQ, rfl⟩))
    (declStep_preserves_of_basis_cons mp
    (A := fun ψ => Term.const .quotMk [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT quotMkA.name ψ
          = some (Term.const .quotMk [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]) (fun _ _ _ _ _ h => nomatch h))
    ?_
    (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [quotMkA_reading_eq]
    exact WellDenotedTy_bconst_type V .quotMk [ψ uN] ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [quotMkA_reading_eq]
    exact bval_mem_type V .quotMk [ψ uN] ρ

/-! ## The substitution-peeling kit

`TeleFitPA` peels by `B.inst a` at cut `0`, so after `k` peels a
domain carries a *chain* of instantiations at cuts `k-1, …, 0`.
`interp_inst0` turns the outermost into a `cons`; these four turn the
rest into `cons`es too, so a `k`-deep telescope domain's reading is
read at the `k`-fold `cons` environment — which is the environment
every space lemma below is stated at.  (`BasisBlocks.lean`'s
`interp_liftN_succ_inst` is the special case where the domain is a
*lifted* earlier argument; this is the general shape.) -/

theorem interp_inst_cons1 (e a : Term) (x1 : V) (ρ : Nat → V) :
    interp V (cons x1 ρ) (e.inst a 1)
      = interp V (cons x1 (cons (interp V ρ a) ρ)) e := by
  have hsh : shiftE 1 0 (cons x1 ρ) = ρ := by
    funext j; simp [shiftE, cons]
  rw [interp_inst, hsh]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | (_ + 2) => rfl

theorem interp_inst_cons2 (e a : Term) (x1 x2 : V) (ρ : Nat → V) :
    interp V (cons x2 (cons x1 ρ)) (e.inst a 2)
      = interp V (cons x2 (cons x1 (cons (interp V ρ a) ρ))) e := by
  have hsh : shiftE 2 0 (cons x2 (cons x1 ρ)) = ρ := by
    funext j; simp [shiftE, cons]
  rw [interp_inst, hsh]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (_ + 3) => rfl

theorem interp_inst_cons3 (e a : Term) (x1 x2 x3 : V) (ρ : Nat → V) :
    interp V (cons x3 (cons x2 (cons x1 ρ))) (e.inst a 3)
      = interp V (cons x3 (cons x2 (cons x1 (cons (interp V ρ a) ρ))))
          e := by
  have hsh : shiftE 3 0 (cons x3 (cons x2 (cons x1 ρ))) = ρ := by
    funext j; simp [shiftE, cons]
  rw [interp_inst, hsh]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | (_ + 4) => rfl

theorem interp_inst_cons4 (e a : Term) (x1 x2 x3 x4 : V)
    (ρ : Nat → V) :
    interp V (cons x4 (cons x3 (cons x2 (cons x1 ρ)))) (e.inst a 4)
      = interp V (cons x4 (cons x3 (cons x2 (cons x1
          (cons (interp V ρ a) ρ))))) e := by
  have hsh : shiftE 4 0 (cons x4 (cons x3 (cons x2 (cons x1 ρ)))) = ρ := by
    funext j; simp [shiftE, cons]
  rw [interp_inst, hsh]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | (_ + 5) => rfl

/-! ## `Quot.ind`

The block's `Prop`-valued eliminator.  Its motive lands in `Prop`, so
the whole tower lives in the truth-value regime: the minor premise is a
truth value, its inhabitant the point, and so is every abstraction over
it (`lamV_eq_pt`).  `bval .quotInd` is `pt` for the same reason, so the
row's fired equality is `pt = pt` by `app_pt` and needs no value law at
all. -/

/-- `@Quot.{u} A r`, at two de Bruijn slots. -/
def quotApp (u i j : Nat) : Term :=
  .app (.app (.const .quot [u]) (.bvar i)) (.bvar j)

/-- `@Quot.mk.{u} A r a`, at three de Bruijn slots. -/
def quotMkApp (u i j k : Nat) : Term :=
  .app (.app (.app (.const .quotMk [u]) (.bvar i)) (.bvar j)) (.bvar k)

/-- `Quot.ind`'s motive binder domain reading. -/
def quotIndMotiveTy (u : Nat) : Term :=
  .pi (quotApp u 1 0) (.sort 0)

/-- `Quot.ind`'s minor binder domain reading. -/
def quotIndMinorTy (u : Nat) : Term :=
  .pi (.bvar 2) (.app (.bvar 1) (quotMkApp u 3 2 0))

/-- The motive space: `Quot A r → Prop`. -/
noncomputable def quotIndMotiveSpace (V : Type w) [SetTheory V]
    (u : Nat) (Aset R : V) : V :=
  piV (quotSet u Aset R) fun _ => (univ 0 : V)

/-- The minor space: `∀ a, M (Quot.mk a)`. -/
noncomputable def quotIndMinorSpace (V : Type w) [SetTheory V]
    (u : Nat) (Aset R M : V) : V :=
  piV Aset fun a => app M (quotClass u Aset R a)

/-! ### The two applied formers, graded and evaluated

`Quot A r` and `Quot.mk A r a` occur at four different de Bruijn
depths across the block, so both are stated against an arbitrary
environment through its slot values.  The `∃ w S F` witnesses are
`bconst_app_data2`/`_data3` — nothing is chosen. -/

/-- The relation binder's domain is graded, unconditionally. -/
theorem quotRelTy_wellDenoted (ρ : Nat → V) (hA : IsTy (ρ 0)) :
    WellDenoted V ρ quotRelTy :=
  ⟨trivial, hA, fun _ _ => ⟨trivial, hA, fun _ _ => trivial, fun _ _ => IsTy_univ 0⟩,
    fun _ _ => IsTy_piV⟩

theorem quotApp_data {u i j : Nat} {ρ : Nat → V} {Aset R : V}
    (hi : ρ i = Aset) (hj : ρ j = R)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V Aset) :
    WellDenoted V ρ (quotApp u i j) ∧
      interp V ρ (quotApp u i j) = quotSet u Aset R := by
  have hAi : interp V ρ (Term.bvar i) = Aset := by
    rw [interp_bvar, hi]
  have hRj : interp V ρ (Term.bvar j) = R := by
    rw [interp_bvar, hj]
  have hA' : Aset ∈ˢ interp V ρ (Term.sort u) := by
    rw [interp_sort]; exact hA
  have hR' : R ∈ˢ interp V (cons Aset ρ) (relAV (.bvar 0)) := by
    rw [relAV_interp]; exact hR
  refine ⟨?_, ?_⟩
  · rw [quotApp, WellDenoted_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨trivial, trivial, ?_⟩
      have h := bconst_app_data V .quot [u] ρ (A := .sort u) rfl hA' (IsTy_univ u)
      rw [← hAi] at h
      exact h
    · have h := bconst_app_data2 V .quot [u] ρ
        (A := .sort u) (A2 := relAV (.bvar 0)) rfl hA' hR'
        (by rw [relAV_interp]; exact IsTy_relSpace _)
      rw [← hAi, ← hRj] at h
      simpa [interp_const, bval, ConLeche.Term.lv] using h
  · rw [quotApp]
    simp only [interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero, hAi, hRj]
    exact quotV_app V hA (hR)

theorem quotMkApp_data {u i j k : Nat} {ρ : Nat → V} {Aset R a : V}
    (hi : ρ i = Aset) (hj : ρ j = R) (hk : ρ k = a)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V Aset)
    (ha : a ∈ˢ Aset) :
    WellDenoted V ρ (quotMkApp u i j k) ∧
      interp V ρ (quotMkApp u i j k) = quotClass u Aset R a := by
  have hAi : interp V ρ (Term.bvar i) = Aset := by
    rw [interp_bvar, hi]
  have hRj : interp V ρ (Term.bvar j) = R := by
    rw [interp_bvar, hj]
  have hak : interp V ρ (Term.bvar k) = a := by
    rw [interp_bvar, hk]
  have hA' : Aset ∈ˢ interp V ρ (Term.sort u) := by
    rw [interp_sort]; exact hA
  have hR' : R ∈ˢ interp V (cons Aset ρ) (relAV (.bvar 0)) := by
    rw [relAV_interp]; exact hR
  have ha' : a ∈ˢ interp V (cons R (cons Aset ρ)) (Term.bvar 1) := by
    simpa [interp_bvar, cons] using ha
  refine ⟨?_, ?_⟩
  · rw [quotMkApp, WellDenoted_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨?_, trivial, ?_⟩
      · rw [WellDenoted_app]
        refine ⟨trivial, trivial, ?_⟩
        have h := bconst_app_data V .quotMk [u] ρ (A := .sort u) rfl hA' (IsTy_univ u)
        rw [← hAi] at h
        exact h
      · have h := bconst_app_data2 V .quotMk [u] ρ
          (A := .sort u) (A2 := relAV (.bvar 0)) rfl hA' hR'
          (by rw [relAV_interp]; exact IsTy_relSpace _)
        rw [← hAi, ← hRj] at h
        simpa [interp_const, bval, ConLeche.Term.lv] using h
    · have h := bconst_app_data3 V .quotMk [u] ρ
        (A := .sort u) (A2 := relAV (.bvar 0)) (A3 := .bvar 1)
        rfl hA' hR' ha' (by simpa [interp_bvar, cons] using IsTy_of_mem_univ hA)
      rw [← hAi, ← hRj, ← hak] at h
      simpa [interp_const, bval, ConLeche.Term.lv] using h
  · rw [quotMkApp]
    simp only [interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero, hAi, hRj, hak]
    exact quotMkV_app V hA (hR) ha

/-! ### The motive and minor spaces -/

theorem quotIndMotiveTy_interp {u : Nat} {Aset R : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V Aset) :
    interp V (cons R (cons Aset ρ)) (quotIndMotiveTy u)
      = quotIndMotiveSpace V u Aset R := by
  rw [quotIndMotiveTy, interp_pi, quotIndMotiveSpace,
    (quotApp_data (u := u) (i := 1) (j := 0) (ρ := cons R (cons Aset ρ))
      (by simp [cons]) (by simp [cons]) hA hR).2]
  exact piV_congr fun _ _ => by rw [interp_sort]

theorem quotIndMinorTy_interp {u : Nat} {Aset R M : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V Aset) :
    interp V (cons M (cons R (cons Aset ρ))) (quotIndMinorTy u)
      = quotIndMinorSpace V u Aset R M := by
  rw [quotIndMinorTy, interp_pi, quotIndMinorSpace]
  simp only [interp_bvar, cons]
  refine piV_congr fun a ha => ?_
  rw [interp_app,
    (quotMkApp_data (u := u) (i := 3) (j := 2) (k := 0)
      (ρ := cons a (cons M (cons R (cons Aset ρ))))
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      hA hR ha).2]
  simp [interp_bvar, cons]

/-! ### The type reading -/

/-- `Quot.ind`'s type reading, named: five binders. -/
def quotIndTy (u : Nat) : Term :=
  .pi (.sort u)
    (.pi quotRelTy
      (.pi (quotIndMotiveTy u)
        (.pi (quotIndMinorTy u)
          (.pi (quotApp u 3 2) (.app (.bvar 2) (.bvar 0))))))

/-- **`Quot.ind`'s type reading.** -/
theorem denote_quotIndA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA) :
    denote (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts, env.tables⟩ ψ 0 quotIndA.toConstantVal.type
      = some (quotIndTy (ψ uN)) := by
  have hQc : ∀ d : Nat,
      denote (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts, env.tables⟩ ψ d (.const quotName [.param uN])
        = some (Term.const .quot [ψ uN]) := fun d =>
    denote_quotLeaf (m := m) (A := A) ψ (by decide) hQ d
      (Level.param uN)
  have hMc : ∀ d : Nat,
      denote (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts, env.tables⟩ ψ d (.const quotMkName [.param uN])
        = some (Term.const .quotMk [ψ uN]) := fun d =>
    denote_quotMkLeaf (m := m) (A := A) ψ (by decide) hM d
      (Level.param uN)
  rw [show quotIndA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE
            (Expr.forallE (.bvar 0)
              (Expr.forallE (.bvar 1) (.sort .zero)))
            (Expr.forallE
              (Expr.forallE
                (.app (.app (.const quotName [.param uN]) (.bvar 1))
                  (.bvar 0)) (.sort .zero))
              (Expr.forallE
                (Expr.forallE (.bvar 2)
                  (.app (.bvar 1)
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 3)) (.bvar 2)) (.bvar 0))))
                (Expr.forallE
                  (.app (.app (.const quotName [.param uN]) (.bvar 3))
                    (.bvar 2))
                  (.app (.bvar 2) (.bvar 0)))))) from rfl]
  simp [denote_forallE, denote_sort, denote_app, denote_fvar,
    Expr.instantiate1, quotRelTy, quotApp, quotMkApp,
    quotIndMotiveTy, quotIndMinorTy, quotIndTy,
    hQc, hMc, Level.eval]

theorem quotIndA_reading_eq (ψ : Name → Nat) :
    quotIndTy (ψ uN) = BConst.typeAV .quotInd [ψ uN] := by rfl

/-! ### The truth-value kit

Everything `Quot.ind` builds — its tower, its rule's right-hand side,
and every application of either — is the canonical proof, and a fibre
only has to be an inhabited truth value.  These lemmas are that
observation, stated once; `Quot.sound` reads them too. -/

/-- The inhabited truth value a proof tower's grading picks for its
fibre: `True`, as a `piR 0`. -/
noncomputable def unitPropR (V : Type w) [SetTheory V] : V :=
  piR 0 (unitSet : V) fun _ => unitSet

theorem unitPropR_mem_univZero : unitPropR V ∈ˢ (univZero : V) :=
  piR_zero_mem_univZero

theorem pt_mem_unitPropR : (pt : V) ∈ˢ unitPropR V :=
  pt_mem_piR_zero fun _ _ => ⟨pt, pt_mem_unitSet⟩

/-- **A `λ` whose body is the canonical proof is graded** — the fibre is
`unitPropR`, a type; and it is the canonical proof itself. -/
theorem WellDenoted_lam_zero_pt {ρ : Nat → V} {Aa b : Term}
    (hA : WellDenotedTy V ρ Aa)
    (hb : ∀ x, x ∈ˢ interp V ρ Aa → WellDenoted V (cons x ρ) b)
    (hpt : ∀ x, x ∈ˢ interp V ρ Aa → interp V (cons x ρ) b = pt) :
    WellDenoted V ρ (.lam Aa b) ∧ interp V ρ (.lam Aa b) = pt := by
  refine ⟨?_, by rw [interp_lam]; exact lamV_eq_pt hpt⟩
  rw [WellDenoted_lam]
  exact ⟨hA.1, hA.2, fun x hx => hb x hx, fun _ => unitPropR V,
    fun x hx => by rw [hpt x hx]; exact pt_mem_unitPropR,
    fun _ _ => Or.inl unitPropR_mem_univZero⟩

/-- **The canonical proof applied to anything is graded, and is again
the canonical proof.**  The `∃ w S F` witness is `w = 0`, the
argument's own domain, and the constant `unitPropR` fibre. -/
theorem WellDenoted_app_pt {ρ : Nat → V} {f a : Term} {S : V}
    (hf : WellDenoted V ρ f) (hfi : interp V ρ f = pt)
    (ha : WellDenoted V ρ a) (hmem : interp V ρ a ∈ˢ S) :
    WellDenoted V ρ (.app f a) ∧ interp V ρ (.app f a) = pt := by
  refine ⟨?_, by rw [interp_app, hfi, app_pt]⟩
  rw [WellDenoted_app]
  exact ⟨hf, ha, 0, S, fun _ => unitPropR V,
    by rw [hfi]; exact pt_mem_piR_zero fun _ _ => ⟨pt, pt_mem_unitPropR⟩,
    hmem, fun _ _ _ => unitPropR_mem_univZero, fun h => absurd rfl h⟩

/-! ### The two domains, graded -/

theorem quotIndMotiveTy_wellDenoted {u : Nat} {Aset R : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V Aset) :
    WellDenotedTy V (cons R (cons Aset ρ)) (quotIndMotiveTy u) := by
  obtain ⟨hok, hint⟩ := quotApp_data (u := u) (i := 1) (j := 0)
    (ρ := cons R (cons Aset ρ)) (by simp [cons]) (by simp [cons]) hA hR
  exact ⟨⟨hok, by rw [hint]; exact IsTy_of_mem_univ (quotSet_mem_univ hA),
      fun _ _ => trivial, fun _ _ => IsTy_univ 0⟩, IsTy_piV⟩

theorem quotIndMinorTy_wellDenoted {u : Nat} {Aset R M : V} (ρ : Nat → V)
    (hA : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V Aset)
    (hM : M ∈ˢ quotIndMotiveSpace V u Aset R) :
    WellDenotedTy V (cons M (cons R (cons Aset ρ))) (quotIndMinorTy u) := by
  have hdom : interp V (cons M (cons R (cons Aset ρ)))
      (Term.bvar 2) = Aset := by simp [interp_bvar, cons]
  have hstep : ∀ a : V, a ∈ˢ Aset →
      WellDenoted V (cons a (cons M (cons R (cons Aset ρ))))
          (.app (.bvar 1) (quotMkApp u 3 2 0)) ∧
      interp V (cons a (cons M (cons R (cons Aset ρ))))
        (.app (.bvar 1) (quotMkApp u 3 2 0))
          ∈ˢ (univZero : V) := by
    intro a ha
    obtain ⟨hok, hint⟩ := quotMkApp_data (u := u)
      (i := 3) (j := 2) (k := 0)
      (ρ := cons a (cons M (cons R (cons Aset ρ))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hA hR ha
    have hMb : interp V (cons a (cons M (cons R (cons Aset ρ))))
        (Term.bvar 1) = M := by simp [interp_bvar, cons]
    have hcl : quotClass u Aset R a ∈ˢ quotSet u Aset R :=
      quotClass_mem ha
    have hMc : app M (quotClass u Aset R a) ∈ˢ (univ 0 : V) := app_mem_piV hM hcl
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨trivial, hok, ?_⟩
      rw [hMb, hint]
      exact slot_of_mem_piV V hM hcl (IsTy_of_mem_univ (quotSet_mem_univ hA))
    · rw [interp_app, hMb, hint, ← univ_zero]
      exact hMc
  exact ⟨⟨trivial, by rw [hdom]; exact IsTy_of_mem_univ hA,
      fun a ha => (hstep a (by rwa [hdom] at ha)).1,
      fun a ha => Or.inl (hstep a (by rwa [hdom] at ha)).2⟩, IsTy_piV⟩

/-! ### The rule, its right-hand side, and the row -/

/-- `Quot.ind`'s rule's RHS reading. -/
def quotIndRa (u : Nat) : Term :=
  .lam (.sort u)
    (.lam quotRelTy
      (.lam (quotIndMotiveTy u)
        (.lam (quotIndMinorTy u)
          (.lam (.bvar 3) (.app (.bvar 1) (.bvar 0))))))

/-- The three inner `λ`s of `Quot.ind`'s RHS, at a type and a relation. -/
theorem quotIndRa_inner (u : Nat) (ρ : Nat → V) {Aset R : V}
    (hAset : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V Aset) :
    WellDenoted V (cons R (cons Aset ρ))
        (.lam (quotIndMotiveTy u) (.lam (quotIndMinorTy u)
          (.lam (.bvar 3) (.app (.bvar 1) (.bvar 0))))) ∧
      interp V (cons R (cons Aset ρ))
        (.lam (quotIndMotiveTy u) (.lam (quotIndMinorTy u)
          (.lam (.bvar 3) (.app (.bvar 1) (.bvar 0))))) = pt := by
  have hM3 : ∀ M, M ∈ˢ quotIndMotiveSpace V u Aset R →
      WellDenoted V (cons M (cons R (cons Aset ρ)))
          (.lam (quotIndMinorTy u) (.lam (.bvar 3) (.app (.bvar 1) (.bvar 0)))) ∧
        interp V (cons M (cons R (cons Aset ρ)))
          (.lam (quotIndMinorTy u) (.lam (.bvar 3) (.app (.bvar 1) (.bvar 0)))) = pt := by
    intro M hM
    have hmk : ∀ mk, mk ∈ˢ quotIndMinorSpace V u Aset R M →
        WellDenoted V (cons mk (cons M (cons R (cons Aset ρ))))
            (.lam (.bvar 3) (.app (.bvar 1) (.bvar 0))) ∧
          interp V (cons mk (cons M (cons R (cons Aset ρ))))
            (.lam (.bvar 3) (.app (.bvar 1) (.bvar 0))) = pt := by
      intro mk hmk
      have hmkpt : mk = pt := eq_pt_of_mem_piV
        (fun a ha => univ_zero (V := V) ▸ app_mem_piV hM (quotClass_mem ha)) hmk
      have hdom : interp V (cons mk (cons M (cons R (cons Aset ρ))))
          (Term.bvar 3) = Aset := by simp [interp_bvar, cons]
      have hbody : ∀ a : V, a ∈ˢ Aset →
          WellDenoted V (cons a (cons mk (cons M (cons R (cons Aset ρ)))))
              (.app (.bvar 1) (.bvar 0)) ∧
            interp V (cons a (cons mk (cons M (cons R (cons Aset ρ)))))
              (.app (.bvar 1) (.bvar 0)) = pt := fun a ha =>
        WellDenoted_app_pt (S := Aset) trivial (by
          rw [interp_bvar]
          show cons a (cons mk (cons M (cons R (cons Aset ρ)))) 1 = pt
          exact hmkpt) trivial (by rw [interp_bvar]; exact ha)
      exact WellDenoted_lam_zero_pt
        ⟨trivial, by rw [hdom]; exact IsTy_of_mem_univ hAset⟩
        (fun a ha => (hbody a (by rwa [hdom] at ha)).1)
        (fun a ha => (hbody a (by rwa [hdom] at ha)).2)
    exact WellDenoted_lam_zero_pt (quotIndMinorTy_wellDenoted ρ hAset hR hM)
      (fun mk h => (hmk mk (by rwa [quotIndMinorTy_interp ρ hAset hR] at h)).1)
      (fun mk h => (hmk mk (by rwa [quotIndMinorTy_interp ρ hAset hR] at h)).2)
  exact WellDenoted_lam_zero_pt (quotIndMotiveTy_wellDenoted ρ hAset hR)
    (fun M h => (hM3 M (by rwa [quotIndMotiveTy_interp ρ hAset hR] at h)).1)
    (fun M h => (hM3 M (by rwa [quotIndMotiveTy_interp ρ hAset hR] at h)).2)

/-- **`Quot.ind`'s RHS tower is graded, and is the canonical proof** —
five `λ`s whose bodies are all the canonical proof (the innermost
because the minor premise itself is: its fibres are truth values,
`eq_pt_of_mem_piV`). -/
theorem quotIndRa_facts (u : Nat) (ρ : Nat → V) :
    WellDenoted V ρ (quotIndRa u) ∧ interp V ρ (quotIndRa u) = (pt : V) := by
  rw [quotIndRa]
  refine WellDenoted_lam_zero_pt ⟨trivial, IsTy_univ _⟩ ?_ ?_
  rotate_left
  · intro Aset hAset
    rw [interp_sort] at hAset
    refine (WellDenoted_lam_zero_pt
      ⟨quotRelTy_wellDenoted _ (IsTy_of_mem_univ hAset), IsTy_piV⟩ ?_ ?_).2 <;>
    intro R hR <;> rw [quotRelTy_interp] at hR
    · exact (quotIndRa_inner u ρ hAset hR).1
    · exact (quotIndRa_inner u ρ hAset hR).2
  intro Aset hAset
  rw [interp_sort] at hAset
  refine (WellDenoted_lam_zero_pt
    ⟨quotRelTy_wellDenoted _ (IsTy_of_mem_univ hAset), IsTy_piV⟩ ?_ ?_).1 <;>
  intro R hR <;> rw [quotRelTy_interp] at hR
  · exact (quotIndRa_inner u ρ hAset hR).1
  · exact (quotIndRa_inner u ρ hAset hR).2

theorem quotIndRa_interp (u : Nat) (ρ : Nat → V) :
    interp V ρ (quotIndRa u) = (pt : V) := (quotIndRa_facts u ρ).2

theorem quotIndRa_wellDenoted (u : Nat) (ρ : Nat → V) :
    WellDenoted V ρ (quotIndRa u) := (quotIndRa_facts u ρ).1

/-- **`Quot.ind`'s rule's RHS reading.** -/
theorem denote_quotInd_rhs (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA) :
    denote (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts, env.tables⟩ ψ 0 quotIndRule.rhs
      = some (quotIndRa (ψ uN)) := by
  have hQc : ∀ d : Nat,
      denote (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts, env.tables⟩ ψ d (.const quotName [.param uN])
        = some (Term.const .quot [ψ uN]) := fun d =>
    denote_quotLeaf (m := m) (A := A) ψ (by decide) hQ d
      (Level.param uN)
  have hMc : ∀ d : Nat,
      denote (acvalWith m.acval quotIndA.name A)
        ⟨quotIndA :: env.consts, env.tables⟩ ψ d (.const quotMkName [.param uN])
        = some (Term.const .quotMk [ψ uN]) := fun d =>
    denote_quotMkLeaf (m := m) (A := A) ψ (by decide) hM d
      (Level.param uN)
  simp only [quotIndRule]
  simp [denote_lam, denote_forallE, denote_sort, denote_app,
    denote_fvar, Expr.instantiate1, quotRelTy, quotApp, quotMkApp,
    quotIndMotiveTy, quotIndMinorTy, quotIndRa,
    hQc, hMc, Level.eval]

/-! ### The ι facts, shared by both rows

Both recursors fire `Quot.mk`, whose family `Quot.{u} α r : Sort u` is
`Prop` exactly at `u = 0`: the stored `Quot` records `zeronessOf u`,
so a constructor level the case split exempts is never zero and the major's domain,
`quotSet` above `Prop`, is strict; where the major is the point the
level is `0`, and there `Quot.mk`'s value is the canonical proof. -/

/-- **The ι case split at `Quot.mk`**: the constructor's level is not
zero at any valuation (the stored `Quot`'s `sortZ` is `zeronessOf u`). -/
theorem quotMk_neverProp_ne_zero {find? : Name → Option ConstantInfo}
    (hQ : find? quotName = some quotA) {usj : List Level}
    (h : ConLeche.iotaCtorNeverProp find? quotMkA.toConstantVal usj = true)
    (φ : Name → Nat) :
    Level.substFn φ quotMkA.toConstantVal.levelParams usj uN ≠ 0 := by
  obtain ⟨cvT, caps, hq, hlp, hz⟩ : ∃ cvT caps,
      quotA = .indInfo cvT caps ∧ cvT.levelParams = [uN] ∧
        caps.sortZ = .ifAllZero [uN] := ⟨_, _, rfl, rfl, rfl⟩
  have hfn : (quotMkA.toConstantVal.type.piResult).getAppFn
      = .const quotName [.param uN] := by rfl
  rw [hq] at hQ
  unfold ConLeche.iotaCtorNeverProp at h
  rw [hfn] at h
  simp only [hQ, Bool.and_eq_true] at h
  have hnv := h.2
  unfold ConLeche.capsNeverZero at hnv
  rw [hlp, hz] at hnv
  have hh : (Level.substPW [uN] usj (ConLeche.PropWhen.ifAllZero [uN])).holds φ = false := by
    generalize Level.substPW [uN] usj (ConLeche.PropWhen.ifAllZero [uN]) = pw at hnv ⊢
    cases pw with
    | never => rfl
    | ifAllZero ps => exact nomatch hnv
  rw [ConLeche.Level.holds_substPW] at hh
  intro h0
  have h0' : Level.substFn φ [uN] usj uN = 0 := h0
  simp [h0'] at hh

/-- A spine on `Quot.mk` at `Prop` is the canonical proof. -/
theorem interp_quotMk_zero_spine (ρ : Nat → V) :
    ∀ (ys : List Term) {f : Term}, interp V ρ f = pt →
      interp V ρ (Term.mkAppN f ys) = pt
  | [], _, h => h
  | y :: ys, f, h => by
    rw [Term.mkAppN_cons]
    exact interp_quotMk_zero_spine ρ ys (by rw [interp_app, h, app_pt])

/-- The ι facts of a `Quot.mk` rule, from the major's domain.
`hmaj` reads the major of a fitting recursor spine into `quotSet` at
the recursor's level `u`, which is the constructor's (`hulev`). -/
theorem quotRuleExtra_of {find? : Name → Option ConstantInfo}
    (hQ : find? quotName = some quotA)
    {acv : Term} {u : Nat} {usj : List Level} {φ : Name → Nat}
    (hulev : Level.substFn φ quotMkA.toConstantVal.levelParams usj uN = u)
    (hctor : acv = Term.const .quotMk [u])
    {P : (Nat → V) → Term → Prop}
    (hmaj : ∀ ρ a, P ρ a → ∃ Aset R : V, interp V ρ a ∈ˢ quotSet u Aset R) :
    (ConLeche.iotaCtorNeverProp find? quotMkA.toConstantVal usj = true →
      ∀ ρ a, P ρ a → interp V ρ a ≠ pt) ∧
    (∀ ρ a, P ρ a → interp V ρ a = pt →
      ∀ ys : List Term, interp V ρ (Term.mkAppN acv ys) = pt) := by
  refine ⟨fun hlic ρ a hP ha => ?_, fun ρ a hP ha ys => ?_⟩
  · obtain ⟨Aset, R, hm⟩ := hmaj ρ a hP
    have hne := quotMk_neverProp_ne_zero hQ hlic φ
    rw [hulev] at hne
    rw [ha] at hm
    exact (strict_quotSet hne Aset R).2 hm
  · obtain ⟨Aset, R, hm⟩ := hmaj ρ a hP
    rw [ha] at hm
    have h0 : u = 0 := Classical.byContradiction fun hne =>
      (strict_quotSet hne Aset R).2 hm
    subst hctor h0
    refine interp_quotMk_zero_spine ρ ys ?_
    simp only [interp_const, bval, ConLeche.Term.lv, List.getD_cons_zero]
    exact lamV_eq_pt fun _ _ => lamV_eq_pt fun _ _ => lamV_eq_pt fun _ _ =>
      mem_univ_zero (quotSet_mem_univ ‹_›) (quotClass_mem ‹_›)

/-- **(T) for a `Quot.mk` rule**: a fired `Quot.mk` application at the
constructor's own level `u'`, not the point, lying in the quotient at
the recursor's level `u ≠ 0` and parameters `x1 x2`, is the class of
its representative there; so it is `Quot.mk` at the recursor's level
applied to the recursor's parameters and the same representative,
which fits `Quot.mk`'s telescope at `u`. -/
theorem quotRuleT_of {u u' : Nat} (hu : u ≠ 0) {acvJ acvC : Term}
    (hJ : acvJ = Term.const .quotMk [u']) (hC : acvC = Term.const .quotMk [u])
    {ρ : Nat → V} {x1 x2 y1 y2 y3 : Term} {restC : Term}
    (f1 : interp V ρ x1 ∈ˢ (univ u : V))
    (f2 : interp V ρ x2 ∈ˢ relSpace V (interp V ρ x1))
    (hfitC : TeleFitPA V ρ (quotMkTy u') [y1, y2, y3] restC)
    (hmem : interp V ρ (Term.mkAppN acvJ [y1, y2, y3])
      ∈ˢ quotSet u (interp V ρ x1) (interp V ρ x2))
    (hne : interp V ρ (Term.mkAppN acvJ [y1, y2, y3]) ≠ pt) :
    ∃ restC', TeleFitPA V ρ (quotMkTy u) [x1, x2, y3] restC' ∧
      interp V ρ (Term.mkAppN acvC [x1, x2, y3])
        = interp V ρ (Term.mkAppN acvJ [y1, y2, y3]) := by
  rw [quotMkTy] at hfitC
  cases hfitC with | cons g1 hfitC =>
  cases hfitC with | cons g2 hfitC =>
  cases hfitC with | cons g3 _ =>
  rw [interp_sort] at g1
  rw [interp_inst0, quotRelTy_interp] at g2
  rw [interp_inst0, interp_inst_cons1] at g3
  simp only [interp_bvar, cons] at g3
  have hvJ : interp V ρ (Term.mkAppN acvJ [y1, y2, y3])
      = quotClass u' (interp V ρ y1) (interp V ρ y2) (interp V ρ y3) := by
    simp only [Term.mkAppN_cons, Term.mkAppN_nil, interp_app, hJ, interp_const, bval,
      ConLeche.Term.lv, List.getD_cons_zero]
    exact quotMkV_app V g1 g2 g3
  have hu' : u' ≠ 0 := by
    intro h0
    apply hne
    rw [hvJ, h0]
    unfold quotClass
    rw [ite_eq_left rfl]
  rw [hvJ] at hmem ⊢
  obtain ⟨hy3, hcls⟩ := quotClass_of_mem_quotSet_pos hu hu' g3 hmem
  have g1' : interp V ρ x1 ∈ˢ interp V ρ (Term.sort u) := by rw [interp_sort]; exact f1
  refine ⟨_, .cons g1' (.cons ?_ (.cons ?_ .nil)), ?_⟩
  · rw [interp_inst0, quotRelTy_interp]; exact f2
  · rw [interp_inst0, interp_inst_cons1]
    simp only [interp_bvar, cons]
    exact hy3
  · simp only [Term.mkAppN_cons, Term.mkAppN_nil, interp_app, hC, interp_const, bval,
      ConLeche.Term.lv, List.getD_cons_zero]
    rw [quotMkV_app V f1 f2 hy3, hcls]

/-- **`Quot.ind`'s ι facts**: not K; `Quot.mk`'s arity; (S)
and (P) from the major's domain (`quotRuleExtra_of`); (T) from the
class's representative (`quotRuleT_of`); no indices, a `.plain` rule,
so (U) is the trivial index pin. -/
theorem quotIndExtra {m : EnvModel V env}
    (m₂ : EnvModel V ⟨quotIndA :: env.consts, env.tables⟩)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hac : m₂.acval = acvalWith m.acval quotIndA.name
      (fun ψ => Term.const .quotInd [ψ uN]))
    (φ : Name → Nat) :
    RecRuleExtra m₂ φ quotIndA.name quotIndA.toConstantVal 4 4 false
      quotIndRule := by
  intro us _ TVa hTVa
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ quotIndA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hTyRead : denote m₂.acval ⟨quotIndA :: env.consts, env.tables⟩ φ 0
      (quotIndA.toConstantVal.type.instantiateLevelParams
        quotIndA.toConstantVal.levelParams us)
      = some (quotIndTy (ψ uN)) := by
    rw [denote_instLevels m₂.acval_params φ, hac,
      denote_quotIndA_type (m := m) _ hQ hM, ← hψ]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hM' : (⟨quotIndA :: env.consts, env.tables⟩ : Env).find? quotMkName
      = some quotMkA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hM
  have hQ' : (⟨quotIndA :: env.consts, env.tables⟩ : Env).find? quotName
      = some quotA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hQ
  refine ⟨fun h => (nomatch h), fun cvj cnP cnF hfj => ?_⟩
  rw [show RecRule.ctor quotIndRule = quotMkName from rfl, hM'] at hfj
  obtain ⟨rfl, rfl, rfl⟩ :
      cvj = quotMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 1 := by
    injection Option.some.inj hfj with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  refine ⟨rfl, fun _ => ?_⟩
  -- the comparand level is the recursor's own `u`
  have hulevOf : ∀ usj : List Level,
      Level.substFn φ quotMkA.toConstantVal.levelParams usj
        = Level.substFn φ quotMkA.toConstantVal.levelParams
            (ConLeche.recFireComparands quotIndRule 2 quotIndA.toConstantVal.levelParams us
              quotMkA.toConstantVal.levelParams [] 4).1 →
      Level.substFn φ quotMkA.toConstantVal.levelParams usj uN = ψ uN := by
    intro usj hlev
    rw [congrFun hlev uN, hψ]
    show Level.eval φ (Level.subst quotIndA.toConstantVal.levelParams
      us (.param uN)) = _
    rw [Level.subst, Level.eval_subst_go]
  have hctorOf : ∀ usj : List Level,
      m₂.acval (RecRule.ctor quotIndRule)
        (Level.substFn φ quotMkA.toConstantVal.levelParams usj)
      = Term.const .quotMk [Level.substFn φ quotMkA.toConstantVal.levelParams usj uN] := by
    intro usj
    rw [show RecRule.ctor quotIndRule = quotMkName from rfl, hac,
      acvalWith_ne (by decide)]
    refine EnvModel.acval_pinned m hM (by decide) ?_
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hCtorRead : ∀ usj : List Level,
      denote m₂.acval ⟨quotIndA :: env.consts, env.tables⟩ φ 0
        (quotMkA.toConstantVal.type.instantiateLevelParams
          quotMkA.toConstantVal.levelParams usj)
      = some (quotMkTy
          (Level.substFn φ quotMkA.toConstantVal.levelParams usj uN)) := by
    intro usj
    rw [denote_instLevels m₂.acval_params φ, hac,
      denote_quotMkTy (m := m) _ (by decide) hQ]
  -- the major's domain: the quotient at the recursor's parameters
  have hpeel : ∀ (ρ : Nat → V) (xs : List Term) (a restR : Term), xs.length = 4 →
      TeleFitPA V ρ (quotIndTy (ψ uN)) (xs ++ [a]) restR →
      ∃ x1 x2 : Term, x1 ∈ xs ∧ x2 ∈ xs ∧ interp V ρ x1 ∈ˢ (univ (ψ uN) : V) ∧
        interp V ρ x2 ∈ˢ relSpace V (interp V ρ x1) ∧
        interp V ρ a ∈ˢ quotSet (ψ uN) (interp V ρ x1) (interp V ρ x2) := by
    intro ρ xs a restR hxs hfit
    obtain ⟨x1, x2, x3, x4, rfl⟩ : ∃ p q r s, xs = [p, q, r, s] := by
      match xs, hxs with
      | [p, q, r, s], _ => exact ⟨p, q, r, s, rfl⟩
    rw [quotIndTy] at hfit
    cases hfit with | cons f1 hfit =>
    cases hfit with | cons f2 hfit =>
    cases hfit with | cons f3 hfit =>
    cases hfit with | cons f4 hfit =>
    cases hfit with | cons f5 _ =>
    rw [interp_sort] at f1
    rw [interp_inst0, quotRelTy_interp] at f2
    rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
      interp_inst_cons3,
      (quotApp_data (u := ψ uN) (i := 3) (j := 2)
        (ρ := cons (interp V ρ x4) (cons (interp V ρ x3)
          (cons (interp V ρ x2) (cons (interp V ρ x1) ρ))))
        (by simp [cons]) (by simp [cons]) f1 f2).2] at f5
    exact ⟨x1, x2, by simp, by simp, f1, f2, f5⟩
  have hext := fun usj hlev => quotRuleExtra_of (V := V) hQ' (hulevOf usj hlev)
    ((hctorOf usj).trans (by rw [hulevOf usj hlev]))
    (P := fun ρ a => ∃ (xs : List Term) (restR : Term),
      xs.length = 4 ∧ TeleFitPA V ρ (quotIndTy (ψ uN)) (xs ++ [a]) restR)
    (fun ρ a ⟨xs, restR, hxs, hfit⟩ => by
      obtain ⟨x1, x2, _, _, _, _, hm⟩ := hpeel ρ xs a restR hxs hfit
      exact ⟨_, _, hm⟩)
  refine ⟨fun hlic ρ xs a restR hxs hfit =>
      (hext _ rfl).1 hlic ρ a ⟨xs, restR, hxs, hfit⟩, ?_, ?_⟩
  · -- (T): the fired `Quot.mk` at the recursor's level and parameters
    intro hlic usj _ TVja hTVja ρ xs ys restR restC hxl hyl hfitR hfitC hxwd hywd hne
    have hu : ψ uN ≠ 0 := by
      have := quotMk_neverProp_ne_zero hQ' hlic φ
      rwa [hulevOf _ rfl] at this
    obtain rfl : TVja = _ := (Option.some.inj ((hCtorRead usj).symm.trans hTVja)).symm
    obtain ⟨y1, y2, y3, rfl⟩ : ∃ p q r, ys = [p, q, r] := by
      match ys, hyl with
      | [p, q, r], _ => exact ⟨p, q, r, rfl⟩
    obtain ⟨-, hfitMaj⟩ : ∃ restR', TeleFitPA V ρ (quotIndTy (ψ uN)) (xs ++ [Term.mkAppN
        (m₂.acval (RecRule.ctor quotIndRule)
          (Level.substFn φ quotMkA.toConstantVal.levelParams usj)) [y1, y2, y3]]) restR' :=
      ⟨_, hfitR⟩
    obtain ⟨x1, x2, hx1, hx2, f1, f2, hm⟩ := hpeel ρ xs _ restR hxl hfitR
    obtain ⟨restC', hfitC', hval⟩ := quotRuleT_of hu (hctorOf usj)
      ((hctorOf _).trans (by rw [hulevOf _ rfl])) f1 f2 hfitC hm hne
    refine ⟨_, [x1, x2, y3], _, restC', rfl, rfl, by rw [hCtorRead, hulevOf _ rfl], rfl, rfl,
      ?_, hfitC', hval⟩
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact hxwd _ hx1
    · exact hxwd _ hx2
    · exact hywd _ (by simp)
  intro usj _ hlev TVja _
  refine ⟨fun ρ xs a restR hxs hfit ha ys _ _ _ _ =>
      (hext usj hlev).2 ρ a ⟨xs, restR, hxs, hfit⟩ ha ys, ?_⟩
  intro ρ xs ys restR restC _ _ _ _ _ _ _ _ _ _
  exact ⟨restC, [], rfl, Or.inl rfl, fun i hi => absurd hi (by omega)⟩

/-- **`Quot.ind`'s `RecRuleLaw` row.**  The rule is `.plain`, so both
`.nested` conjuncts are `nomatch`; the fired equality is `pt = pt`
(`bval .quotInd` is the canonical proof and so is the RHS tower), and
the transport is five `WellDenoted_app_pt` steps whose domains come
straight off the two telescope fits — no domain has to be
identified. -/
theorem quotIndLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨quotIndA :: env.consts, env.tables⟩)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hac : m₂.acval = acvalWith m.acval quotIndA.name
      (fun ψ => Term.const .quotInd [ψ uN]))
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ quotIndA.name quotIndA.toConstantVal 4 4 false
      quotIndRule := by
  refine ⟨Nat.le_refl 4, fun us hus => ?_,
    quotIndExtra (m := m) m₂ hQ hM hac φ⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ quotIndA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hRa : denote m₂.acval ⟨quotIndA :: env.consts, env.tables⟩ φ 0
      (quotIndRule.rhs.instantiateLevelParams
        quotIndA.toConstantVal.levelParams us)
      = some (quotIndRa (ψ uN)) := by
    rw [denote_instLevels m₂.acval_params φ, hac, hψ,
      denote_quotInd_rhs (m := m) _ hQ hM]
  refine ⟨quotIndRa (ψ uN), hRa, fun ρ => quotIndRa_wellDenoted _ ρ, ?_, ?_⟩
  · intro _ _ h
    exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hpin hTVa hTVja hfitR hfitC
  -- the fired constructor is `Quot.mk`, stored in the prefix
  have hM' : (⟨quotIndA :: env.consts, env.tables⟩ : Env).find? quotMkName
      = some quotMkA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hM
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
  have hTyRead : denote m₂.acval ⟨quotIndA :: env.consts, env.tables⟩ φ 0
      (quotIndA.toConstantVal.type.instantiateLevelParams
        quotIndA.toConstantVal.levelParams us)
      = some (quotIndTy (ψ uN)) := by
    rw [denote_instLevels m₂.acval_params φ, hac,
      denote_quotIndA_type (m := m) _ hQ hM, ← hψ]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hCtorRead : denote m₂.acval ⟨quotIndA :: env.consts, env.tables⟩ φ 0
      (quotMkA.toConstantVal.type.instantiateLevelParams
        quotMkA.toConstantVal.levelParams usj)
      = some (quotMkTy
          (Level.substFn φ quotMkA.toConstantVal.levelParams usj uN)) := by
    rw [denote_instLevels m₂.acval_params φ, hac,
      denote_quotMkTy (m := m) _ (by decide) hQ]
  obtain rfl : TVja = _ :=
    (Option.some.inj (hCtorRead.symm.trans hTVja)).symm
  have hrecL : m₂.acval quotIndA.name
      (Level.substFn φ quotIndA.toConstantVal.levelParams us)
      = Term.const .quotInd [ψ uN] := by
    rw [hac, acvalWith_self, hψ]
  rw [quotIndTy] at hfitR
  rw [quotMkTy] at hfitC
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
      List.take, List.drop, List.cons_append, List.nil_append,
      Term.mkAppN_cons, Term.mkAppN_nil,
      hrecL, interp_app, interp_const, bval, quotIndRa_interp,
      app_pt]
  · -- the transport: five applications of the canonical proof
    intro hxsA hysA
    simp only [
      List.take, List.drop, List.cons_append, List.nil_append,
      Term.mkAppN_cons, Term.mkAppN_nil]
    have h1 := WellDenoted_app_pt (quotIndRa_wellDenoted (ψ uN) ρ)
      (quotIndRa_interp (ψ uN) ρ) (hxsA x1 (by simp)) f1
    have h2 := WellDenoted_app_pt h1.1 h1.2 (hxsA x2 (by simp)) f2
    have h3 := WellDenoted_app_pt h2.1 h2.2 (hxsA x3 (by simp)) f3
    have h4 := WellDenoted_app_pt h3.1 h3.2 (hxsA x4 (by simp)) f4
    exact (WellDenoted_app_pt h4.1 h4.2 (hysA y3 (by simp)) g3).1

/-- **`Quot.ind`, installed at the P tier.** -/
theorem extendQuotInd (mp : EnvModelM V env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hfresh : env.find? quotIndA.name = none)
    (hwf : EnvWF ⟨quotIndA :: env.consts, env.tables⟩) {ex : List Name} :
    CoverTo mp ex ⟨quotIndA :: env.consts, env.tables⟩ ex := by
  have hty := fun ψ =>
    denote_quotIndA_type (m := mp.base2)
      (A := fun ψ => Term.const .quotInd [ψ uN]) ψ hQ hM
  refine coverTo_cons hfresh (fun _ _ h => nomatch h) (declStep_preserves_of_basis_rec_cons mp
    (A := fun ψ => Term.const .quotInd [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT quotIndA.name ψ
          = some (Term.const .quotInd [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp])
      (fun _ _ _ _ _ heq r hr => by
        injection heq with _ _ _ _ h4
        rw [← h4] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨_, _, _, hM, rfl⟩
        · exact nomatch hr'))
    ?_
    (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [quotIndA_reading_eq]
    exact WellDenotedTy_bconst_type V .quotInd [ψ uN] ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [quotIndA_reading_eq]
    exact bval_mem_type V .quotInd [ψ uN] ρ
  · intro m₂ hac φ
    refine recRules_cons_rec mp hfresh quotIndA_eq m₂ hac φ ?_
    intro rl hrl
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact quotIndLaw (m := mp.base2) m₂ hQ hM hac φ
    · exact nomatch hr'

/-! ## The `Eq` bridge

`Quot.sound`'s and `Quot.lift`'s stored types conclude at the pinned
`Eq` former, whose leaf is **not** `pinnedStructT` — it is
the basis install's own tower.  The crossing is `EqLaw`, the
`EnvModelM` field, and it crosses **both** halves at once: its value
half computes the spine, and its grading half is exactly the reading's
`htyOk` obligation at that slot.

Both consumers below take the two halves as plain hypotheses at the
level the constant reads `Eq` at, so neither mentions `EnvModelM`. -/

/-- The stored `Eq` former's leaf at a `Quot`-block extension: the
prefix's own, by `acvalWith_ne`. -/
theorem denote_eqLeaf {c₀ : ConstantInfo} (ψ : Name → Nat) (l : Level)
    (hne : ¬ c₀.name = eqName)
    (hE : EqStored env) (d : Nat) :
    denote (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ d
        (.const eqName [l])
      = some (m.acval eqName (Level.substFn ψ [eqLp env] [l])) := by
  obtain ⟨ci, hf, hl⟩ := hE
  have hf' : (⟨c₀ :: env.consts, env.tables⟩ : Env).find? eqName = some ci := by
    rw [ConLeche.Env.find?_cons, ite_eq_right hne]; exact hf
  rw [denote_const hf' (by rw [hl]; rfl), acvalWith_ne (fun h => hne h.symm), hl]

/-- The relation, applied to two of its arguments, is a type. -/
theorem IsTy_relV_app {Aset R a b : V} (hR : R ∈ˢ relSpace V Aset)
    (ha : a ∈ˢ Aset) (hb : b ∈ˢ Aset) : IsTy (app (app R a) b) :=
  have hRa : app R a ∈ˢ piV Aset fun _ => (univ 0 : V) := app_mem_piV hR ha
  IsTy_of_mem_univ (app_mem_piV hRa hb)

/-- The relation, applied to two of its arguments. -/
theorem relApp_data {i j k : Nat} {ρ : Nat → V} {Aset R a b : V}
    (hi : ρ i = R) (hj : ρ j = a) (hk : ρ k = b)
    (hR : R ∈ˢ relSpace V Aset) (ha : a ∈ˢ Aset) (hb : b ∈ˢ Aset)
    (hAty : IsTy Aset) :
    WellDenoted V ρ (.app (.app (.bvar i) (.bvar j)) (.bvar k)) ∧
      interp V ρ (.app (.app (.bvar i) (.bvar j)) (.bvar k))
        = app (app R a) b := by
  have hRi : interp V ρ (Term.bvar i) = R := by rw [interp_bvar, hi]
  have haj : interp V ρ (Term.bvar j) = a := by rw [interp_bvar, hj]
  have hbk : interp V ρ (Term.bvar k) = b := by rw [interp_bvar, hk]
  have hRa : app R a ∈ˢ piV Aset fun _ => (univ 0 : V) := app_mem_piV hR ha
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨trivial, trivial, ?_⟩
      rw [hRi, haj]
      exact slot_of_mem_piV V hR ha hAty
    · rw [interp_app, hRi, haj, hbk]
      exact slot_of_mem_piV V hRa hb hAty
  · rw [interp_app, interp_app, hRi, haj, hbk]

/-! ## `Quot.sound`

The block's stored axiom, and the basis blocks' only one: its
`reduce_ops` row is the `hred` disjunct's second branch (`Quot.sound`
is not a trusted operation), unused by every earlier block.  Its type
is `Prop`-valued throughout, so the membership obligation is `pt` in a
five-deep `piR 0` — five `pt_mem_piR_zero` steps whose innermost
witness is the quotient's own soundness. -/

/-- `Quot.sound`'s type reading, named. -/
def quotSoundTy (E : Term) (u : Nat) : Term :=
  .pi (.sort u)
    (.pi quotRelTy
      (.pi (.bvar 1)
        (.pi (.bvar 2)
          (.pi (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
            (.app (.app (.app E (quotApp u 4 3))
              (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1))))))

/-- **`Quot.sound`'s type reading.** -/
theorem denote_quotSoundA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : EqStored env) :
    denote (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts, env.tables⟩ ψ 0 quotSoundA.toConstantVal.type
      = some (quotSoundTy (m.acval eqName (Level.substFn ψ [eqLp env] [Level.param uN])) (ψ uN)) := by
  have hQc : ∀ d : Nat,
      denote (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts, env.tables⟩ ψ d (.const quotName [.param uN])
        = some (Term.const .quot [ψ uN]) := fun d =>
    denote_quotLeaf (m := m) (A := A) ψ (by decide) hQ d
      (Level.param uN)
  have hMc : ∀ d : Nat,
      denote (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts, env.tables⟩ ψ d (.const quotMkName [.param uN])
        = some (Term.const .quotMk [ψ uN]) := fun d =>
    denote_quotMkLeaf (m := m) (A := A) ψ (by decide) hM d
      (Level.param uN)
  have hEc : ∀ d : Nat,
      denote (acvalWith m.acval quotSoundA.name A)
        ⟨quotSoundA :: env.consts, env.tables⟩ ψ d (.const eqName [.param uN])
        = some (m.acval eqName (Level.substFn ψ [eqLp env] [Level.param uN])) := fun d =>
    denote_eqLeaf (m := m) (A := A) ψ (Level.param uN) (by decide) hE d
  rw [show quotSoundA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE
            (Expr.forallE (.bvar 0)
              (Expr.forallE (.bvar 1) (.sort .zero)))
            (Expr.forallE (.bvar 1)
              (Expr.forallE (.bvar 2)
                (Expr.forallE
                  (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app (.const eqName [.param uN])
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 2)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 1))))))) from rfl]
  simp [denote_forallE, denote_sort, denote_app, denote_fvar,
    Expr.instantiate1, quotRelTy, quotApp, quotMkApp, quotSoundTy,
    hQc, hMc, hEc, Level.eval]

/-- **A `Prop`-valued Π-type's grading step**, stated so the five
binders of `Quot.sound`'s type (and the three of `Quot.lift`'s
invariance premise) are five applications of one lemma: the Π-type is
graded and *is itself* a truth value, which is exactly what the next
binder out needs. -/
theorem WellDenoted_pi_zero {ρ : Nat → V} {Aa B : Term}
    (hA : WellDenoted V ρ Aa) (hAt : IsTy (interp V ρ Aa))
    (hB : ∀ x, x ∈ˢ interp V ρ Aa → WellDenoted V (cons x ρ) B)
    (hz : ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) B ∈ˢ (univZero : V)) :
    WellDenoted V ρ (.pi Aa B) ∧
      interp V ρ (.pi Aa B) ∈ˢ (univZero : V) := by
  refine ⟨⟨hA, hAt, fun x hx => hB x hx, fun x hx => Or.inl (hz x hx)⟩, ?_⟩
  rw [interp_pi, piV_eq_zero hz]
  exact piR_zero_mem_univZero

/-- **`Quot.sound`'s type reading is graded** — five
`WellDenoted_pi_zero` steps whose innermost slot is `EqLaw`'s grading
half. -/
theorem quotSoundTy_wellDenoted {E : Term} {u : Nat} (ρ : Nat → V)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : Term),
      WellDenoted V ρ' Aa → WellDenoted V ρ' la → WellDenoted V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ u : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenoted V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V)) :
    WellDenotedTy V ρ (quotSoundTy E u) := by
  -- the innermost slot: `EqLaw`'s grading half at the three spine
  -- arguments, whose readings are the block's two applied formers
  have hin : ∀ Aset R a b w : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset → a ∈ˢ Aset → b ∈ˢ Aset →
      WellDenoted V (cons w (cons b (cons a (cons R (cons Aset ρ)))))
          (.app (.app (.app E (quotApp u 4 3)) (quotMkApp u 4 3 2))
            (quotMkApp u 4 3 1)) ∧
        interp V (cons w (cons b (cons a (cons R (cons Aset ρ)))))
          (.app (.app (.app E (quotApp u 4 3)) (quotMkApp u 4 3 2))
            (quotMkApp u 4 3 1)) ∈ˢ (univZero : V) := by
    intro Aset R a b w hAset hR ha hb
    obtain ⟨hTok, hTint⟩ := quotApp_data (u := u) (i := 4) (j := 3)
      (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
      (by simp [cons]) (by simp [cons]) hAset hR
    obtain ⟨hlok, hlint⟩ := quotMkApp_data (u := u) (i := 4)
      (j := 3) (k := 2)
      (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR ha
    obtain ⟨hrok, hrint⟩ := quotMkApp_data (u := u) (i := 4)
      (j := 3) (k := 1)
      (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR hb
    exact hgr _ _ _ _ hTok hlok hrok
      (by rw [hTint]; exact quotSet_mem_univ hAset)
      (by rw [hTint, hlint]; exact quotClass_mem ha)
      (by rw [hTint, hrint]; exact quotClass_mem hb)
  have h5 : ∀ Aset R a b : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset → a ∈ˢ Aset → b ∈ˢ Aset →
      WellDenoted V (cons b (cons a (cons R (cons Aset ρ))))
          (.pi (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
            (.app (.app (.app E (quotApp u 4 3)) (quotMkApp u 4 3 2))
              (quotMkApp u 4 3 1))) ∧
        interp V (cons b (cons a (cons R (cons Aset ρ))))
          (.pi (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
            (.app (.app (.app E (quotApp u 4 3)) (quotMkApp u 4 3 2))
              (quotMkApp u 4 3 1))) ∈ˢ (univZero : V) := by
    intro Aset R a b hAset hR ha hb
    obtain ⟨hrok, hrint⟩ := relApp_data (i := 2) (j := 1)
      (k := 0) (ρ := cons b (cons a (cons R (cons Aset ρ))))
      (by simp [cons]) (by simp [cons]) (by simp [cons]) hR ha hb
      (IsTy_of_mem_univ hAset)
    exact WellDenoted_pi_zero hrok (by rw [hrint]; exact IsTy_relV_app hR ha hb)
      (fun w _ => (hin Aset R a b w hAset hR ha hb).1)
      (fun w _ => (hin Aset R a b w hAset hR ha hb).2)
  have h4 : ∀ Aset R a : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset → a ∈ˢ Aset →
      WellDenoted V (cons a (cons R (cons Aset ρ)))
          (.pi (.bvar 2)
            (.pi (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
              (.app (.app (.app E (quotApp u 4 3))
                (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1)))) ∧
        interp V (cons a (cons R (cons Aset ρ)))
          (.pi (.bvar 2)
            (.pi (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
              (.app (.app (.app E (quotApp u 4 3))
                (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1))))
          ∈ˢ (univZero : V) := by
    intro Aset R a hAset hR ha
    have hdom : interp V (cons a (cons R (cons Aset ρ)))
        (Term.bvar 2) = Aset := by simp [interp_bvar, cons]
    exact WellDenoted_pi_zero (Aa := .bvar 2) trivial
      (by rw [hdom]; exact IsTy_of_mem_univ hAset)
      (fun b hb => (h5 Aset R a b hAset hR ha (by rwa [hdom] at hb)).1)
      (fun b hb => (h5 Aset R a b hAset hR ha (by rwa [hdom] at hb)).2)
  have h3 : ∀ Aset R : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset →
      WellDenoted V (cons R (cons Aset ρ))
          (.pi (.bvar 1)
            (.pi (.bvar 2)
              (.pi (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                (.app (.app (.app E (quotApp u 4 3))
                  (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1))))) ∧
        interp V (cons R (cons Aset ρ))
          (.pi (.bvar 1)
            (.pi (.bvar 2)
              (.pi (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                (.app (.app (.app E (quotApp u 4 3))
                  (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1)))))
          ∈ˢ (univZero : V) := by
    intro Aset R hAset hR
    have hdom : interp V (cons R (cons Aset ρ)) (Term.bvar 1)
        = Aset := by simp [interp_bvar, cons]
    exact WellDenoted_pi_zero (Aa := .bvar 1) trivial
      (by rw [hdom]; exact IsTy_of_mem_univ hAset)
      (fun a ha => (h4 Aset R a hAset hR (by rwa [hdom] at ha)).1)
      (fun a ha => (h4 Aset R a hAset hR (by rwa [hdom] at ha)).2)
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ u : V) →
      WellDenoted V (cons Aset ρ)
          (.pi quotRelTy
            (.pi (.bvar 1)
              (.pi (.bvar 2)
                (.pi (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app E (quotApp u 4 3))
                    (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1)))))) ∧
        interp V (cons Aset ρ)
          (.pi quotRelTy
            (.pi (.bvar 1)
              (.pi (.bvar 2)
                (.pi (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app E (quotApp u 4 3))
                    (quotMkApp u 4 3 2)) (quotMkApp u 4 3 1))))))
          ∈ˢ (univZero : V) := by
    intro Aset hAset
    exact WellDenoted_pi_zero (Aa := quotRelTy)
      (quotRelTy_wellDenoted _ (IsTy_of_mem_univ hAset))
      (by rw [quotRelTy_interp]; exact IsTy_relSpace _)
      (fun R hR => (h3 Aset R hAset
        (by rwa [quotRelTy_interp] at hR)).1)
      (fun R hR => (h3 Aset R hAset
        (by rwa [quotRelTy_interp] at hR)).2)
  rw [quotSoundTy]
  have h := WellDenoted_pi_zero (Aa := .sort u) trivial (IsTy_univ u)
    (fun Aset hAset => (h2 Aset (by rwa [interp_sort] at hAset)).1)
    (fun Aset hAset => (h2 Aset (by rwa [interp_sort] at hAset)).2)
  exact ⟨h.1, Or.inl h.2⟩

/-- A function space whose fibres are inhabited truth values is an
inhabited truth value. -/
theorem pt_tv {A : V} {B : V → V}
    (h : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ B x) :
    piV A B ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ piV A B := by
  rw [piV_eq_zero fun x hx => (h x hx).1]
  exact ⟨piR_zero_mem_univZero, pt_mem_piR_zero_of fun x hx => (h x hx).2⟩

/-- **`Quot.sound` inhabits its type's reading.**  Five
`pt_tv` steps; the innermost witness is the quotient's own
soundness (`SetTheory.quotSound`), read through `EqLaw`'s value
half. -/
theorem quotSoundTy_mem {E : Term} {u : Nat} (ρ : Nat → V)
    (hval : ∀ (ρ' : Nat → V) (T a b : V), T ∈ˢ (univ u : V) →
      a ∈ˢ T → b ∈ˢ T →
      app (app (app (interp V ρ' E) T) a) b = eqv a b) :
    (pt : V) ∈ˢ interp V ρ (quotSoundTy E u) := by
  rw [quotSoundTy, interp_pi]
  refine (pt_tv fun Aset hAset => ?_).2
  rw [interp_sort] at hAset
  rw [interp_pi]
  refine pt_tv fun R hR => ?_
  rw [quotRelTy_interp] at hR
  rw [interp_pi]
  refine pt_tv fun a ha => ?_
  rw [show interp V (cons R (cons Aset ρ)) (Term.bvar 1) = Aset
    from by simp [interp_bvar, cons]] at ha
  rw [interp_pi]
  refine pt_tv fun b hb => ?_
  rw [show interp V (cons a (cons R (cons Aset ρ))) (Term.bvar 2)
    = Aset from by simp [interp_bvar, cons]] at hb
  rw [interp_pi]
  refine pt_tv fun w hw => ?_
  obtain ⟨-, hrint⟩ := relApp_data (i := 2) (j := 1) (k := 0)
    (ρ := cons b (cons a (cons R (cons Aset ρ))))
    (by simp [cons]) (by simp [cons]) (by simp [cons]) hR ha hb
    (IsTy_of_mem_univ hAset)
  rw [hrint] at hw
  obtain ⟨-, hTint⟩ := quotApp_data (u := u) (i := 4) (j := 3)
    (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
    (by simp [cons]) (by simp [cons]) hAset hR
  obtain ⟨-, hlint⟩ := quotMkApp_data (u := u) (i := 4) (j := 3)
    (k := 2) (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
    (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR ha
  obtain ⟨-, hrint'⟩ := quotMkApp_data (u := u) (i := 4) (j := 3)
    (k := 1) (ρ := cons w (cons b (cons a (cons R (cons Aset ρ)))))
    (by simp [cons]) (by simp [cons]) (by simp [cons]) hAset hR hb
  rw [interp_app, interp_app, interp_app, hTint, hlint, hrint',
    hval _ _ _ _ (quotSet_mem_univ hAset) (quotClass_mem ha)
      (quotClass_mem hb)]
  refine ⟨eqv_mem_univZero _ _, ?_⟩
  rw [quotSound (u := u) ha hb hw]
  exact pt_mem_eqv_self _

/-- `Eq` at `Quot.sound`'s parameter. -/
theorem quotSound_eqLaws (mp : EnvModelM V env) (hE : EqStored env) (ψ : Name → Nat) :
    (∀ (ρ : Nat → V) (T x y : V), T ∈ˢ (univ (ψ uN) : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ (mp.base2.acval eqName
        (Level.substFn ψ [eqLp env] [Level.param uN]))) T) x) y = eqv x y) ∧
    (∀ (ρ : Nat → V) (Aa la ra : Term),
      WellDenoted V ρ Aa → WellDenoted V ρ la → WellDenoted V ρ ra →
      interp V ρ Aa ∈ˢ (univ (ψ uN) : V) →
      interp V ρ la ∈ˢ interp V ρ Aa →
      interp V ρ ra ∈ˢ interp V ρ Aa →
      WellDenoted V ρ (.app (.app (.app (mp.base2.acval eqName
          (Level.substFn ψ [eqLp env] [Level.param uN])) Aa) la) ra) ∧
        interp V ρ (.app (.app (.app (mp.base2.acval eqName
          (Level.substFn ψ [eqLp env] [Level.param uN])) Aa) la) ra)
          ∈ˢ (univZero : V)) := by
  have hEuN : Level.substFn ψ [eqLp env] [Level.param uN] (eqLp env) = ψ uN := by
    simp [Level.substFn, Level.eval]
  obtain ⟨hval0, hgr0⟩ :=
    EqLaw.at mp.eq_law hE (Level.substFn ψ [eqLp env] [Level.param uN])
  rw [hEuN] at hval0 hgr0
  exact ⟨hval0, hgr0⟩

/-- **`Quot.sound`, installed at the P tier** — the basis blocks' one
stored axiom, and the one place the `reduce_ops` disjunct's second
branch is taken. -/
theorem extendQuotSound (mp : EnvModelM V env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : EqStored env)
    (hfresh : env.find? quotSoundA.name = none)
    (hwf : EnvWF ⟨quotSoundA :: env.consts, env.tables⟩) {ex : List Name} :
    CoverTo mp ex ⟨quotSoundA :: env.consts, env.tables⟩ ex := by
  have hty := fun ψ =>
    denote_quotSoundA_type (m := mp.base2)
      (A := fun ψ => Term.const .quotSound [ψ uN]) ψ hQ hM hE
  refine coverTo_cons hfresh (fun _ _ h => nomatch h) (declStep_preserves_of_basis_cons mp
    (A := fun ψ => Term.const .quotSound [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inr (by decide))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT quotSoundA.name ψ
          = some (Term.const .quotSound [ψ uN]) from rfl] at hp
        rw [← Option.some.inj hp]) (fun _ _ _ _ _ h => nomatch h))
    ?_
    (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact quotSoundTy_wellDenoted ρ (quotSound_eqLaws mp hE ψ).2
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [interp_const]
    show (pt : V) ∈ˢ _
    exact quotSoundTy_mem ρ (quotSound_eqLaws mp hE ψ).1

/-! ## `Quot.lift`

The block's last constant, and the only one whose type reading is not
`Prop`-valued.  The invariance premise is `Prop`-valued throughout and
concludes at the `Eq` former read **at `v`**, so the bridge is
`EqLaw` at the substituted assignment. -/

/-- One application step, with the fibre named — the shape every
`RecRuleLaw` transport peels with. -/
theorem WellDenoted_app_fibre {ρ : Nat → V} {f a : Term} {S : V}
    {F : V → V} (hf : WellDenoted V ρ f) (ha : WellDenoted V ρ a)
    (hfm : interp V ρ f ∈ˢ piV S F) (ham : interp V ρ a ∈ˢ S) (hS : IsTy S) :
    WellDenoted V ρ (.app f a) ∧
      interp V ρ (.app f a) ∈ˢ F (interp V ρ a) :=
  ⟨by rw [WellDenoted_app]; exact ⟨hf, ha, slot_of_mem_piV V hfm ham hS⟩,
    by rw [interp_app]; exact app_mem_piV hfm ham⟩

/-- A `.pi`, graded from its parts. -/
theorem WellDenoted_pi_of {ρ : Nat → V} {Aa B : Term}
    (hA : WellDenoted V ρ Aa) (hAt : IsTy (interp V ρ Aa))
    (hB : ∀ x, x ∈ˢ interp V ρ Aa → WellDenoted V (cons x ρ) B)
    (hBt : ∀ x, x ∈ˢ interp V ρ Aa → IsTy (interp V (cons x ρ) B)) :
    WellDenoted V ρ (.pi Aa B) :=
  ⟨hA, hAt, hB, hBt⟩

/-- A `.pi`'s reading is a type. -/
theorem IsTy_interp_pi {ρ : Nat → V} {Aa B : Term} :
    IsTy (interp V ρ (.pi Aa B)) := by
  rw [interp_pi]; exact IsTy_piV

/-- **A `λ`, graded and placed at once** — the combined step every
basis tower's walk takes: the fibre named once serves both
`WellDenoted`'s existential and `lamV_mem`'s hypothesis. -/
theorem WellDenoted_lam_piV {ρ : Nat → V} {Aa bd : Term}
    {F : V → V} (hA : WellDenoted V ρ Aa) (hAt : IsTy (interp V ρ Aa))
    (hb : ∀ x, x ∈ˢ interp V ρ Aa → WellDenoted V (cons x ρ) bd ∧
      interp V (cons x ρ) bd ∈ˢ F x)
    (hFt : ∀ x, x ∈ˢ interp V ρ Aa → IsTy (F x)) :
    WellDenoted V ρ (.lam Aa bd) ∧
      interp V ρ (.lam Aa bd) ∈ˢ piV (interp V ρ Aa) F := by
  refine ⟨⟨hA, hAt, fun x hx => (hb x hx).1, F, fun x hx => (hb x hx).2, hFt⟩, ?_⟩
  rw [interp_lam]
  exact lamV_mem (fun x hx => (hb x hx).2) hFt

/-- `Quot.lift`'s invariance premise, read. -/
def quotLiftInvTy (E : Term) : Term :=
  .pi (.bvar 3)
    (.pi (.bvar 4)
      (.pi (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
        (.app (.app (.app E (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
          (.app (.bvar 3) (.bvar 1)))))

/-- `Quot.lift`'s type reading, named. -/
def quotLiftTy (E : Term) (u v : Nat) : Term :=
  .pi (.sort u)
    (.pi quotRelTy
      (.pi (.sort v)
        (.pi (.pi (.bvar 2) (.bvar 1))
          (.pi (quotLiftInvTy E)
            (.pi (quotApp u 4 3) (.bvar 3))))))

/-- **The invariance premise's reading is `quotInvSpace`, and it is
graded** — the `Eq` bridge's two halves, at the three-binder
`Prop`-valued telescope `Interp/Value.lean` states the law at. -/
theorem quotLiftInvTy_data {E : Term} {v : Nat} {Aset R B f : V}
    (ρ : Nat → V)
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : Term),
      WellDenoted V ρ' Aa → WellDenoted V ρ' la → WellDenoted V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenoted V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (hR : R ∈ˢ relSpace V Aset) (hAty : IsTy Aset) (hB : B ∈ˢ (univ v : V))
    (hf : f ∈ˢ piV Aset fun _ => B) :
    interp V (cons f (cons B (cons R (cons Aset ρ))))
        (quotLiftInvTy E) = quotInvSpace V Aset R f ∧
      WellDenoted V (cons f (cons B (cons R (cons Aset ρ))))
        (quotLiftInvTy E) := by
  have hfm : ∀ a : V, a ∈ˢ Aset → app f a ∈ˢ B := fun a ha => app_mem_piV hf ha
  have hd1 : interp V (cons f (cons B (cons R (cons Aset ρ)))) (Term.bvar 3) = Aset := by
    simp [interp_bvar, cons]
  have hd2 : ∀ a : V, interp V (cons a (cons f (cons B (cons R (cons Aset ρ))))) (Term.bvar 4) = Aset := by
    intro a; simp [interp_bvar, cons]
  have hbody : ∀ a b : V, a ∈ˢ Aset → b ∈ˢ Aset → ∀ w : V,
      interp V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
          (.app (.app (.app E (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
            (.app (.bvar 3) (.bvar 1)))
        = eqv (app f a) (app f b) ∧
      WellDenoted V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
          (.app (.app (.app E (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
            (.app (.bvar 3) (.bvar 1))) ∧
      interp V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
          (.app (.app (.app E (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
            (.app (.bvar 3) (.bvar 1))) ∈ˢ (univZero : V) := by
    intro a b ha hb w
    have hB' : interp V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ))))))) (Term.bvar 4)
        = B := by simp [interp_bvar, cons]
    have hfa : interp V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
        (.app (.bvar 3) (.bvar 2)) = app f a := by
      simp [interp_app, interp_bvar, cons]
    have hfb : interp V (cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
        (.app (.bvar 3) (.bvar 1)) = app f b := by
      simp [interp_app, interp_bvar, cons]
    have hokfa : WellDenoted V (cons w (cons b (cons a
        (cons f (cons B (cons R (cons Aset ρ)))))))
        (.app (.bvar 3) (.bvar 2)) :=
      (WellDenoted_app_fibre (S := Aset) (F := fun _ => B)
        (ρ := cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
        (f := .bvar 3) (a := .bvar 2) trivial trivial
        (by simpa [interp_bvar, cons] using hf) (by simpa [interp_bvar, cons] using ha)
        hAty).1
    have hokfb : WellDenoted V (cons w (cons b (cons a
        (cons f (cons B (cons R (cons Aset ρ)))))))
        (.app (.bvar 3) (.bvar 1)) :=
      (WellDenoted_app_fibre (S := Aset) (F := fun _ => B)
        (ρ := cons w (cons b (cons a (cons f (cons B (cons R (cons Aset ρ)))))))
        (f := .bvar 3) (a := .bvar 1) trivial trivial
        (by simpa [interp_bvar, cons] using hf) (by simpa [interp_bvar, cons] using hb)
        hAty).1
    have hspine := hgr _ (.bvar 4) (.app (.bvar 3) (.bvar 2))
      (.app (.bvar 3) (.bvar 1)) trivial hokfa hokfb
      (by rw [hB']; exact hB)
      (by rw [hB', hfa]; exact hfm a ha)
      (by rw [hB', hfb]; exact hfm b hb)
    refine ⟨?_, hspine.1, hspine.2⟩
    rw [interp_app, interp_app, interp_app, hB', hfa, hfb,
      hval _ _ _ _ hB (hfm a ha) (hfm b hb)]
  have hstep : ∀ a : V, a ∈ˢ Aset → ∀ b : V, b ∈ˢ Aset →
      WellDenoted V (cons b (cons a (cons f (cons B (cons R (cons Aset ρ))))))
          (.pi (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
            (.app (.app (.app E (.bvar 4))
              (.app (.bvar 3) (.bvar 2)))
              (.app (.bvar 3) (.bvar 1)))) ∧
        interp V (cons b (cons a (cons f (cons B (cons R (cons Aset ρ))))))
          (.pi (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
            (.app (.app (.app E (.bvar 4))
              (.app (.bvar 3) (.bvar 2)))
              (.app (.bvar 3) (.bvar 1)))) ∈ˢ (univZero : V) := by
    intro a ha b hb
    obtain ⟨hrok, hrint⟩ := relApp_data (i := 4)
      (j := 1) (k := 0) (ρ := cons b (cons a (cons f (cons B (cons R (cons Aset ρ))))))
      (by simp [cons]) (by simp [cons])
      (by simp [cons]) hR ha hb hAty
    exact WellDenoted_pi_zero hrok
      (by rw [hrint]; exact IsTy_relV_app hR ha hb)
      (fun w _ => (hbody a b ha hb w).2.1)
      (fun w _ => (hbody a b ha hb w).2.2)
  have hlev : ∀ a : V, a ∈ˢ Aset →
      WellDenoted V (cons a (cons f (cons B (cons R (cons Aset ρ)))))
          (.pi (.bvar 4)
            (.pi (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
              (.app (.app (.app E (.bvar 4))
                (.app (.bvar 3) (.bvar 2)))
                (.app (.bvar 3) (.bvar 1))))) ∧
        interp V (cons a (cons f (cons B (cons R (cons Aset ρ)))))
          (.pi (.bvar 4)
            (.pi (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
              (.app (.app (.app E (.bvar 4))
                (.app (.bvar 3) (.bvar 2)))
                (.app (.bvar 3) (.bvar 1)))))
          ∈ˢ (univZero : V) := fun a ha =>
    WellDenoted_pi_zero (Aa := .bvar 4) trivial
      (by rw [hd2 a]; exact hAty)
      (fun b hb => (hstep a ha b (by rwa [hd2 a] at hb)).1)
      (fun b hb => (hstep a ha b (by rwa [hd2 a] at hb)).2)
  constructor
  · rw [quotLiftInvTy, interp_pi, quotInvSpace, hd1]
    refine piV_congr fun a ha => ?_
    rw [interp_pi, hd2 a]
    refine piV_congr fun b hb => ?_
    obtain ⟨-, hrint⟩ := relApp_data (i := 4) (j := 1)
      (k := 0) (ρ := cons b (cons a (cons f (cons B (cons R (cons Aset ρ))))))
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      hR ha hb hAty
    rw [interp_pi, hrint]
    exact piV_congr fun w _ => (hbody a b ha hb w).1
  · rw [quotLiftInvTy]
    exact (WellDenoted_pi_zero (Aa := .bvar 3) trivial
      (by rw [hd1]; exact hAty)
      (fun a ha => (hlev a (by rwa [hd1] at ha)).1)
      (fun a ha => (hlev a (by rwa [hd1] at ha)).2)).1

/-- **`Quot.lift`'s type reading is graded.** -/
theorem quotLiftTy_wellDenoted {E : Term} {u v : Nat}
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : Term),
      WellDenoted V ρ' Aa → WellDenoted V ρ' la → WellDenoted V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenoted V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (ρ : Nat → V) :
    WellDenotedTy V ρ (quotLiftTy E u v) := by
  have h6 : ∀ Aset R B f h : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset → B ∈ˢ (univ v : V) →
      WellDenoted V (cons h (cons f (cons B (cons R (cons Aset ρ)))))
        (.pi (quotApp u 4 3) (.bvar 3)) := by
    intro Aset R B f h hAset hR hB
    obtain ⟨hqok, hqint⟩ := quotApp_data (u := u) (i := 4) (j := 3)
      (ρ := cons h (cons f (cons B (cons R (cons Aset ρ)))))
      (by simp [cons]) (by simp [cons]) hAset hR
    exact WellDenoted_pi_of hqok
      (by rw [hqint]; exact IsTy_of_mem_univ (quotSet_mem_univ hAset))
      (fun _ _ => trivial)
      (fun q _ => by
        rw [show interp V (cons q (cons h (cons f (cons B
            (cons R (cons Aset ρ)))))) (Term.bvar 3) = B
          from by simp [interp_bvar, cons]]
        exact IsTy_of_mem_univ hB)
  have h5 : ∀ Aset R B f : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset → B ∈ˢ (univ v : V) →
      f ∈ˢ piV Aset (fun _ => B) →
      WellDenoted V (cons f (cons B (cons R (cons Aset ρ))))
        (.pi (quotLiftInvTy E)
          (.pi (quotApp u 4 3) (.bvar 3))) := by
    intro Aset R B f hAset hR hB hf
    obtain ⟨hinvEq, hinv⟩ := quotLiftInvTy_data ρ hval hgr hR
      (IsTy_of_mem_univ hAset) hB hf
    exact WellDenoted_pi_of hinv (by rw [hinvEq]; exact IsTy_piR _ _ _)
      (fun h _ => h6 Aset R B f h hAset hR hB) (fun _ _ => IsTy_interp_pi)
  have h4 : ∀ Aset R B : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset → B ∈ˢ (univ v : V) →
      WellDenoted V (cons B (cons R (cons Aset ρ)))
        (.pi (.pi (.bvar 2) (.bvar 1))
          (.pi (quotLiftInvTy E)
            (.pi (quotApp u 4 3) (.bvar 3)))) := by
    intro Aset R B hAset hR hB
    have hdom : interp V (cons B (cons R (cons Aset ρ)))
        (Term.pi (.bvar 2) (.bvar 1))
        = piV Aset (fun _ => B) := by
      rw [interp_pi]
      simp only [interp_bvar, cons]
    refine WellDenoted_pi_of ?_ IsTy_interp_pi
      (fun f hf => h5 Aset R B f hAset hR hB (by rwa [hdom] at hf))
      (fun _ _ => IsTy_interp_pi)
    exact WellDenoted_pi_of (Aa := .bvar 2) trivial
      (by simpa [interp_bvar, cons] using IsTy_of_mem_univ hAset)
      (fun _ _ => trivial)
      (fun a _ => by simpa [interp_bvar, cons] using IsTy_of_mem_univ hB)
  have h3 : ∀ Aset R : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset →
      WellDenoted V (cons R (cons Aset ρ))
        (.pi (.sort v)
          (.pi (.pi (.bvar 2) (.bvar 1))
            (.pi (quotLiftInvTy E)
              (.pi (quotApp u 4 3) (.bvar 3))))) := fun Aset R hAset hR =>
    WellDenoted_pi_of (Aa := .sort v) trivial (IsTy_univ v)
      (fun B hB => h4 Aset R B hAset hR (by rwa [interp_sort] at hB))
      (fun _ _ => IsTy_interp_pi)
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ u : V) →
      WellDenoted V (cons Aset ρ)
        (.pi quotRelTy
          (.pi (.sort v)
            (.pi (.pi (.bvar 2) (.bvar 1))
              (.pi (quotLiftInvTy E)
                (.pi (quotApp u 4 3) (.bvar 3)))))) := fun Aset hAset =>
    WellDenoted_pi_of (Aa := quotRelTy)
      (quotRelTy_wellDenoted _ (IsTy_of_mem_univ hAset))
      (by rw [quotRelTy_interp]; exact IsTy_relSpace _)
      (fun R hR => h3 Aset R hAset (by rwa [quotRelTy_interp] at hR))
      (fun _ _ => IsTy_interp_pi)
  rw [quotLiftTy]
  exact ⟨WellDenoted_pi_of (Aa := .sort u) trivial (IsTy_univ u)
    (fun Aset hAset => h2 Aset (by rwa [interp_sort] at hAset))
    (fun _ _ => IsTy_interp_pi), IsTy_interp_pi⟩

/-- **`Quot.lift` inhabits its type's reading**: the reading is
`quotLiftV_mem`'s function space, binder by binder (the invariance
premise's reading is `quotInvSpace`, the quotient's is `quotSet`). -/
theorem quotLiftTy_mem {E : Term} {u v : Nat}
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : Term),
      WellDenoted V ρ' Aa → WellDenoted V ρ' la → WellDenoted V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenoted V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (ρ : Nat → V) :
    quotLiftV V u v ∈ˢ interp V ρ (quotLiftTy E u v) := by
  suffices heq : interp V ρ (quotLiftTy E u v) = piV (univ u : V) fun A =>
      piV (relSpace V A) fun R => piV (univ v : V) fun B =>
        piV (piV A fun _ => B) fun f => piV (quotInvSpace V A R f) fun _ =>
          piV (quotSet u A R) fun _ => B by
    rw [heq]; exact quotLiftV_mem V u v
  rw [quotLiftTy, interp_pi, interp_sort]
  refine piV_congr fun Aset hA => ?_
  rw [interp_pi, quotRelTy_interp]
  refine piV_congr fun R hR => ?_
  rw [interp_pi, interp_sort]
  refine piV_congr fun B hB => ?_
  have hdom : interp V (cons B (cons R (cons Aset ρ)))
      (Term.pi (.bvar 2) (.bvar 1)) = piV Aset (fun _ => B) := by
    rw [interp_pi]; simp only [interp_bvar, cons]
  rw [interp_pi, hdom]
  refine piV_congr fun f hf => ?_
  rw [interp_pi, (quotLiftInvTy_data ρ hval hgr hR (IsTy_of_mem_univ hA) hB hf).1]
  refine piV_congr fun _ _ => ?_
  rw [interp_pi, (quotApp_data (u := u) (i := 4) (j := 3) (by simp [cons]) (by simp [cons])
    hA hR).2]
  exact piV_congr fun _ _ => by simp [interp_bvar, cons]

/-! ### `Quot.lift`'s type reading, and its rule -/

/-- **`Quot.lift`'s type reading.** -/
theorem denote_quotLiftA_type (ψ : Name → Nat)
    (hQ : env.find? quotName = some quotA)
    (hE : EqStored env) :
    denote (acvalWith m.acval quotLiftA.name A)
        ⟨quotLiftA :: env.consts, env.tables⟩ ψ 0 quotLiftA.toConstantVal.type
      = some (quotLiftTy
          (m.acval eqName (Level.substFn ψ [eqLp env] [Level.param vN]))
          (ψ uN) (ψ vN)) := by
  have hQc : ∀ d : Nat,
      denote (acvalWith m.acval quotLiftA.name A)
        ⟨quotLiftA :: env.consts, env.tables⟩ ψ d (.const quotName [.param uN])
        = some (Term.const .quot [ψ uN]) := fun d =>
    denote_quotLeaf (m := m) (A := A) ψ (by decide) hQ d
      (Level.param uN)
  have hEc : ∀ d : Nat,
      denote (acvalWith m.acval quotLiftA.name A)
        ⟨quotLiftA :: env.consts, env.tables⟩ ψ d (.const eqName [.param vN])
        = some (m.acval eqName
            (Level.substFn ψ [eqLp env] [Level.param vN])) := fun d =>
    denote_eqLeaf (m := m) (A := A) ψ (Level.param vN) (by decide)
      hE d
  rw [show quotLiftA.toConstantVal.type
      = Expr.forallE (.sort (.param uN))
          (Expr.forallE
            (Expr.forallE (.bvar 0)
              (Expr.forallE (.bvar 1) (.sort .zero)))
            (Expr.forallE (.sort (.param vN))
              (Expr.forallE
                (Expr.forallE (.bvar 2)
                  (.bvar 1))
                (Expr.forallE
                  (Expr.forallE (.bvar 3)
                    (Expr.forallE (.bvar 4)
                      (Expr.forallE
                        (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                        (.app (.app (.app (.const eqName [.param vN])
                          (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
                          (.app (.bvar 3) (.bvar 1))))))
                  (Expr.forallE
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3))
                    (.bvar 3)))))) from rfl]
  simp [denote_forallE, denote_sort, denote_app, denote_fvar,
    Expr.instantiate1, quotRelTy, quotApp, quotLiftInvTy,
    quotLiftTy, hQc, hEc, Level.eval]

/-- `Quot.lift`'s rule's RHS reading. -/
def quotLiftRa (E : Term) (u v : Nat) : Term :=
  .lam (.sort u)
    (.lam quotRelTy
      (.lam (.sort v)
        (.lam (.pi (.bvar 2) (.bvar 1))
          (.lam (quotLiftInvTy E)
            (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0)))))))

/-- **`Quot.lift`'s rule's RHS reading.** -/
theorem denote_quotLift_rhs (ψ : Name → Nat)
    (hE : EqStored env) :
    denote (acvalWith m.acval quotLiftA.name A)
        ⟨quotLiftA :: env.consts, env.tables⟩ ψ 0 quotLiftRule.rhs
      = some (quotLiftRa
          (m.acval eqName (Level.substFn ψ [eqLp env] [Level.param vN]))
          (ψ uN) (ψ vN)) := by
  have hEc : ∀ d : Nat,
      denote (acvalWith m.acval quotLiftA.name A)
        ⟨quotLiftA :: env.consts, env.tables⟩ ψ d (.const eqName [.param vN])
        = some (m.acval eqName
            (Level.substFn ψ [eqLp env] [Level.param vN])) := fun d =>
    denote_eqLeaf (m := m) (A := A) ψ (Level.param vN) (by decide)
      hE d
  simp only [quotLiftRule]
  simp [denote_lam, denote_forallE, denote_sort, denote_app,
    denote_fvar, Expr.instantiate1, quotRelTy, quotLiftInvTy,
    quotLiftRa, hEc, Level.eval]

/-! ### The RHS tower's space, membership and grading -/

/-- The function space the RHS tower inhabits. -/
noncomputable def quotLiftRaSpace (V : Type w) [SetTheory V]
    (u v : Nat) : V :=
  piV (univ u : V) fun Aset =>
    piV (relSpace V Aset) fun R =>
      piV (univ v : V) fun B =>
        piV (piV Aset fun _ => B) fun f =>
          piV (quotInvSpace V Aset R f) fun _ =>
            piV Aset fun _ => B

/-- **The RHS tower is graded, and a member of `quotLiftRaSpace`.** -/
theorem quotLiftRa_facts {E : Term} {u v : Nat}
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : Term),
      WellDenoted V ρ' Aa → WellDenoted V ρ' la → WellDenoted V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenoted V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (ρ : Nat → V) :
    WellDenoted V ρ (quotLiftRa E u v) ∧
      interp V ρ (quotLiftRa E u v) ∈ˢ quotLiftRaSpace V u v := by
  have h6 : ∀ Aset R B f h : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset → B ∈ˢ (univ v : V) →
      f ∈ˢ piV Aset (fun _ => B) →
      WellDenoted V (cons h (cons f (cons B (cons R (cons Aset ρ)))))
          (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0))) ∧
        interp V (cons h (cons f (cons B (cons R (cons Aset ρ)))))
          (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0)))
          ∈ˢ piV Aset (fun _ => B) := by
    intro Aset R B f h hAset hR hB hf
    have hdom : interp V (cons h (cons f (cons B
        (cons R (cons Aset ρ))))) (Term.bvar 4) = Aset := by
      simp [interp_bvar, cons]
    have := WellDenoted_lam_piV (F := fun _ => B) (bd := .app (.bvar 2) (.bvar 0))
      (ρ := cons h (cons f (cons B (cons R (cons Aset ρ))))) (Aa := .bvar 4) trivial
      (by rw [hdom]; exact IsTy_of_mem_univ hAset)
      (fun a ha => WellDenoted_app_fibre (S := Aset) (F := fun _ => B)
        (ρ := cons a (cons h (cons f (cons B (cons R (cons Aset ρ))))))
        (f := .bvar 2) (a := .bvar 0) trivial trivial
        (by simpa [interp_bvar, cons] using hf)
        (by rw [hdom] at ha; simpa [interp_bvar, cons] using ha)
        (IsTy_of_mem_univ hAset))
      (fun _ _ => IsTy_of_mem_univ hB)
    rwa [hdom] at this
  have h5 : ∀ Aset R B f : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset → B ∈ˢ (univ v : V) →
      f ∈ˢ piV Aset (fun _ => B) →
      WellDenoted V (cons f (cons B (cons R (cons Aset ρ))))
          (.lam (quotLiftInvTy E)
            (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0)))) ∧
        interp V (cons f (cons B (cons R (cons Aset ρ))))
          (.lam (quotLiftInvTy E)
            (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0))))
          ∈ˢ piV (quotInvSpace V Aset R f)
            (fun _ => piV Aset (fun _ => B)) := by
    intro Aset R B f hAset hR hB hf
    obtain ⟨hinvint, hinvok⟩ := quotLiftInvTy_data ρ hval hgr
      hR (IsTy_of_mem_univ hAset) hB hf
    have := WellDenoted_lam_piV (F := fun _ => piV Aset (fun _ => B)) hinvok
      (by rw [hinvint]; exact IsTy_piR _ _ _)
      (fun h _ => h6 Aset R B f h hAset hR hB hf) (fun _ _ => IsTy_piV)
    rwa [hinvint] at this
  have h4 : ∀ Aset R B : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset → B ∈ˢ (univ v : V) →
      WellDenoted V (cons B (cons R (cons Aset ρ)))
          (.lam (.pi (.bvar 2) (.bvar 1))
            (.lam (quotLiftInvTy E)
              (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0))))) ∧
        interp V (cons B (cons R (cons Aset ρ)))
          (.lam (.pi (.bvar 2) (.bvar 1))
            (.lam (quotLiftInvTy E)
              (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0)))))
          ∈ˢ piV (piV Aset (fun _ => B))
            (fun f => piV (quotInvSpace V Aset R f)
              (fun _ => piV Aset (fun _ => B))) := by
    intro Aset R B hAset hR hB
    have hdom : interp V (cons B (cons R (cons Aset ρ)))
        (Term.pi (.bvar 2) (.bvar 1))
        = piV Aset (fun _ => B) := by
      rw [interp_pi]; simp only [interp_bvar, cons]
    have hdok : WellDenoted V (cons B (cons R (cons Aset ρ)))
        (Term.pi (.bvar 2) (.bvar 1)) :=
      WellDenoted_pi_of (Aa := .bvar 2) trivial
        (by simpa [interp_bvar, cons] using IsTy_of_mem_univ hAset)
        (fun _ _ => trivial)
        (fun a _ => by simpa [interp_bvar, cons] using IsTy_of_mem_univ hB)
    have := WellDenoted_lam_piV (F := fun f => piV (quotInvSpace V Aset R f)
        (fun _ => piV Aset (fun _ => B))) hdok IsTy_interp_pi
      (fun f hf => h5 Aset R B f hAset hR hB (by rwa [hdom] at hf))
      (fun _ _ => IsTy_piV)
    rwa [hdom] at this
  have h3 : ∀ Aset R : V, Aset ∈ˢ (univ u : V) →
      R ∈ˢ relSpace V Aset →
      WellDenoted V (cons R (cons Aset ρ))
          (.lam (.sort v)
            (.lam (.pi (.bvar 2) (.bvar 1))
              (.lam (quotLiftInvTy E)
                (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0)))))) ∧
        interp V (cons R (cons Aset ρ))
          (.lam (.sort v)
            (.lam (.pi (.bvar 2) (.bvar 1))
              (.lam (quotLiftInvTy E)
                (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0))))))
          ∈ˢ piV (univ v : V) (fun B =>
            piV (piV Aset (fun _ => B))
              (fun f => piV (quotInvSpace V Aset R f)
                (fun _ => piV Aset (fun _ => B)))) := by
    intro Aset R hAset hR
    have := WellDenoted_lam_piV (F := fun B => piV (piV Aset (fun _ => B))
        (fun f => piV (quotInvSpace V Aset R f) (fun _ => piV Aset (fun _ => B))))
      (Aa := .sort v) (ρ := cons R (cons Aset ρ)) trivial (IsTy_univ v)
      (fun B hB => h4 Aset R B hAset hR (by rwa [interp_sort] at hB))
      (fun _ _ => IsTy_piV)
    rwa [interp_sort] at this
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ u : V) →
      WellDenoted V (cons Aset ρ)
          (.lam quotRelTy
            (.lam (.sort v)
              (.lam (.pi (.bvar 2) (.bvar 1))
                (.lam (quotLiftInvTy E)
                  (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0))))))) ∧
        interp V (cons Aset ρ)
          (.lam quotRelTy
            (.lam (.sort v)
              (.lam (.pi (.bvar 2) (.bvar 1))
                (.lam (quotLiftInvTy E)
                  (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0)))))))
          ∈ˢ piV (relSpace V Aset) (fun R =>
            piV (univ v : V) (fun B =>
              piV (piV Aset (fun _ => B))
                (fun f => piV (quotInvSpace V Aset R f)
                  (fun _ => piV Aset (fun _ => B))))) := by
    intro Aset hAset
    have := WellDenoted_lam_piV (F := fun R => piV (univ v : V) (fun B =>
        piV (piV Aset (fun _ => B))
          (fun f => piV (quotInvSpace V Aset R f) (fun _ => piV Aset (fun _ => B)))))
      (quotRelTy_wellDenoted _ (IsTy_of_mem_univ hAset))
      (by rw [quotRelTy_interp]; exact IsTy_relSpace _)
      (fun R hR => h3 Aset R hAset (by rwa [quotRelTy_interp] at hR))
      (fun _ _ => IsTy_piV)
    rwa [quotRelTy_interp] at this
  have := WellDenoted_lam_piV (F := fun Aset => piV (relSpace V Aset) (fun R =>
      piV (univ v : V) (fun B =>
        piV (piV Aset (fun _ => B))
          (fun f => piV (quotInvSpace V Aset R f) (fun _ => piV Aset (fun _ => B))))))
    (Aa := .sort u) (ρ := ρ) trivial (IsTy_univ u)
    (fun Aset hAset => h2 Aset (by rwa [interp_sort] at hAset))
    (fun _ _ => IsTy_piV)
  rw [interp_sort] at this
  exact this

theorem quotLiftRa_wellDenoted {E : Term} {u v : Nat}
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : Term),
      WellDenoted V ρ' Aa → WellDenoted V ρ' la → WellDenoted V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenoted V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (ρ : Nat → V) :
    WellDenoted V ρ (quotLiftRa E u v) :=
  (quotLiftRa_facts hval hgr ρ).1

/-! ### The two sides of the fired equality -/

/-- **`Quot.lift` fires against a class, at every numeral.**  At
`v ≠ 0` this is `quotLiftV_app` + `quotLiftR_app` + the
quotient's own `app_eq_of_quotClass_eq`; at `v = 0` both sides are the
canonical proof, because a `piR 0`-valued function *is* one. -/
theorem quotLiftV_fired {u v : Nat} {Aset R B f h a : V}
    (hAset : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V Aset)
    (hB : B ∈ˢ (univ v : V)) (hf : f ∈ˢ piV Aset fun _ => B)
    (hh : h ∈ˢ quotInvSpace V Aset R f) (ha : a ∈ˢ Aset) :
    app (app (app (app (app (app (quotLiftV V u v) Aset) R) B) f) h)
        (quotClass u Aset R a) = app f a := by
  rw [quotLiftV_app V hAset hR hB hf hh, quotLiftR_app V (quotClass_mem ha)]
  obtain ⟨hrep, hcls⟩ :=
    qrep_spec (u := u) (R := R) (quotClass_mem (u := u) ha)
  exact app_eq_of_quotClass_eq hAset hrep ha (quotInv_of_mem V hh)
    hcls.symm

/-- …and the RHS tower's own six-fold application is the same value
(`app_lamV` six times, on the domains). -/
theorem quotLiftRa_app {E : Term} {u v : Nat}
    (hval : ∀ (ρ' : Nat → V) (T x y : V), T ∈ˢ (univ v : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ' E) T) x) y = eqv x y)
    (hgr : ∀ (ρ' : Nat → V) (Aa la ra : Term),
      WellDenoted V ρ' Aa → WellDenoted V ρ' la → WellDenoted V ρ' ra →
      interp V ρ' Aa ∈ˢ (univ v : V) →
      interp V ρ' la ∈ˢ interp V ρ' Aa →
      interp V ρ' ra ∈ˢ interp V ρ' Aa →
      WellDenoted V ρ' (.app (.app (.app E Aa) la) ra) ∧
        interp V ρ' (.app (.app (.app E Aa) la) ra)
          ∈ˢ (univZero : V))
    (ρ : Nat → V) {Aset R B f h a : V}
    (hAset : Aset ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V Aset)
    (hB : B ∈ˢ (univ v : V)) (hf : f ∈ˢ piV Aset fun _ => B)
    (hh : h ∈ˢ quotInvSpace V Aset R f) (ha : a ∈ˢ Aset) :
    app (app (app (app (app (app (interp V ρ (quotLiftRa E u v))
        Aset) R) B) f) h) a = app f a := by
  have hdom : interp V (cons B (cons R (cons Aset ρ)))
      (Term.pi (.bvar 2) (.bvar 1)) = piV Aset (fun _ => B) := by
    rw [interp_pi]; simp only [interp_bvar, cons]
  obtain ⟨hinvint, -⟩ := quotLiftInvTy_data ρ hval hgr hR
    (IsTy_of_mem_univ hAset) hB hf
  rw [quotLiftRa, interp_lam, interp_sort, app_lamV hAset,
    interp_lam, quotRelTy_interp, app_lamV hR,
    interp_lam, interp_sort, app_lamV hB,
    interp_lam, hdom, app_lamV hf,
    interp_lam, hinvint, app_lamV hh,
    interp_lam,
    show interp V (cons h (cons f (cons B (cons R (cons Aset ρ)))))
      (Term.bvar 4) = Aset from by simp [interp_bvar, cons],
    app_lamV ha]
  simp [interp_app, interp_bvar, cons]

/-! ### The row -/

/-- **`Quot.lift`'s ι facts**: as `quotIndExtra`, the major's
domain read off the sixth binder. -/
theorem quotLiftExtra {m : EnvModel V env}
    (m₂ : EnvModel V ⟨quotLiftA :: env.consts, env.tables⟩)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : EqStored env)
    (hac : m₂.acval = acvalWith m.acval quotLiftA.name
      (fun ψ => Term.const .quotLift [ψ uN, ψ vN]))
    (φ : Name → Nat) :
    RecRuleExtra m₂ φ quotLiftA.name quotLiftA.toConstantVal 5 5 false
      quotLiftRule := by
  intro us _ TVa hTVa
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ quotLiftA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hTyRead : denote m₂.acval ⟨quotLiftA :: env.consts, env.tables⟩ φ 0
      (quotLiftA.toConstantVal.type.instantiateLevelParams
        quotLiftA.toConstantVal.levelParams us)
      = some (quotLiftTy
          (m.acval eqName (Level.substFn ψ [eqLp env] [Level.param vN]))
          (ψ uN) (ψ vN)) := by
    rw [denote_instLevels m₂.acval_params φ, hac, hψ,
      denote_quotLiftA_type (m := m) _ hQ hE]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hM' : (⟨quotLiftA :: env.consts, env.tables⟩ : Env).find? quotMkName
      = some quotMkA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hM
  have hQ' : (⟨quotLiftA :: env.consts, env.tables⟩ : Env).find? quotName
      = some quotA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hQ
  refine ⟨fun h => (nomatch h), fun cvj cnP cnF hfj => ?_⟩
  rw [show RecRule.ctor quotLiftRule = quotMkName from rfl, hM'] at hfj
  obtain ⟨rfl, rfl, rfl⟩ :
      cvj = quotMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 1 := by
    injection Option.some.inj hfj with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  refine ⟨rfl, fun _ => ?_⟩
  -- the comparand level is the recursor's own `u`
  have hulevOf : ∀ usj : List Level,
      Level.substFn φ quotMkA.toConstantVal.levelParams usj
        = Level.substFn φ quotMkA.toConstantVal.levelParams
            (ConLeche.recFireComparands quotLiftRule 2 quotLiftA.toConstantVal.levelParams us
              quotMkA.toConstantVal.levelParams [] 5).1 →
      Level.substFn φ quotMkA.toConstantVal.levelParams usj uN = ψ uN := by
    intro usj hlev
    rw [congrFun hlev uN, hψ]
    show Level.eval φ (Level.subst quotLiftA.toConstantVal.levelParams
      us (.param uN)) = _
    rw [Level.subst, Level.eval_subst_go]
  have hctorOf : ∀ usj : List Level,
      m₂.acval (RecRule.ctor quotLiftRule)
        (Level.substFn φ quotMkA.toConstantVal.levelParams usj)
      = Term.const .quotMk [Level.substFn φ quotMkA.toConstantVal.levelParams usj uN] := by
    intro usj
    rw [show RecRule.ctor quotLiftRule = quotMkName from rfl, hac,
      acvalWith_ne (by decide)]
    refine EnvModel.acval_pinned m hM (by decide) ?_
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hCtorRead : ∀ usj : List Level,
      denote m₂.acval ⟨quotLiftA :: env.consts, env.tables⟩ φ 0
        (quotMkA.toConstantVal.type.instantiateLevelParams
          quotMkA.toConstantVal.levelParams usj)
      = some (quotMkTy
          (Level.substFn φ quotMkA.toConstantVal.levelParams usj uN)) := by
    intro usj
    rw [denote_instLevels m₂.acval_params φ, hac,
      denote_quotMkTy (m := m) _ (by decide) hQ]
  -- the major's domain: the quotient at the recursor's parameters
  have hpeel : ∀ (ρ : Nat → V) (xs : List Term) (a restR : Term), xs.length = 5 →
      TeleFitPA V ρ (quotLiftTy
          (m.acval eqName (Level.substFn ψ [eqLp env] [Level.param vN]))
          (ψ uN) (ψ vN)) (xs ++ [a]) restR →
      ∃ x1 x2 : Term, x1 ∈ xs ∧ x2 ∈ xs ∧ interp V ρ x1 ∈ˢ (univ (ψ uN) : V) ∧
        interp V ρ x2 ∈ˢ relSpace V (interp V ρ x1) ∧
        interp V ρ a ∈ˢ quotSet (ψ uN) (interp V ρ x1) (interp V ρ x2) := by
    intro ρ xs a restR hxs hfit
    obtain ⟨x1, x2, x3, x4, x5, rfl⟩ :
        ∃ p q r s t, xs = [p, q, r, s, t] := by
      match xs, hxs with
      | [p, q, r, s, t], _ => exact ⟨p, q, r, s, t, rfl⟩
    rw [quotLiftTy] at hfit
    cases hfit with | cons f1 hfit =>
    cases hfit with | cons f2 hfit =>
    cases hfit with | cons f3 hfit =>
    cases hfit with | cons f4 hfit =>
    cases hfit with | cons f5 hfit =>
    cases hfit with | cons f6 _ =>
    rw [interp_sort] at f1
    rw [interp_inst0, quotRelTy_interp] at f2
    rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
      interp_inst_cons3, interp_inst_cons4,
      (quotApp_data (u := ψ uN) (i := 4) (j := 3)
        (ρ := cons (interp V ρ x5) (cons (interp V ρ x4)
          (cons (interp V ρ x3) (cons (interp V ρ x2)
            (cons (interp V ρ x1) ρ)))))
        (by simp [cons]) (by simp [cons]) f1 f2).2] at f6
    exact ⟨x1, x2, by simp, by simp, f1, f2, f6⟩
  have hext := fun usj hlev => quotRuleExtra_of (V := V) hQ' (hulevOf usj hlev)
    ((hctorOf usj).trans (by rw [hulevOf usj hlev]))
    (P := fun ρ a => ∃ (xs : List Term) (restR : Term),
      xs.length = 5 ∧ TeleFitPA V ρ (quotLiftTy
          (m.acval eqName (Level.substFn ψ [eqLp env] [Level.param vN]))
          (ψ uN) (ψ vN)) (xs ++ [a]) restR)
    (fun ρ a ⟨xs, restR, hxs, hfit⟩ => by
      obtain ⟨x1, x2, _, _, _, _, hm⟩ := hpeel ρ xs a restR hxs hfit
      exact ⟨_, _, hm⟩)
  refine ⟨fun hlic ρ xs a restR hxs hfit =>
      (hext _ rfl).1 hlic ρ a ⟨xs, restR, hxs, hfit⟩, ?_, ?_⟩
  · -- (T): the fired `Quot.mk` at the recursor's level and parameters
    intro hlic usj _ TVja hTVja ρ xs ys restR restC hxl hyl hfitR hfitC hxwd hywd hne
    have hu : ψ uN ≠ 0 := by
      have := quotMk_neverProp_ne_zero hQ' hlic φ
      rwa [hulevOf _ rfl] at this
    obtain rfl : TVja = _ := (Option.some.inj ((hCtorRead usj).symm.trans hTVja)).symm
    obtain ⟨y1, y2, y3, rfl⟩ : ∃ p q r, ys = [p, q, r] := by
      match ys, hyl with
      | [p, q, r], _ => exact ⟨p, q, r, rfl⟩
    obtain ⟨x1, x2, hx1, hx2, f1, f2, hm⟩ := hpeel ρ xs _ restR hxl hfitR
    obtain ⟨restC', hfitC', hval⟩ := quotRuleT_of hu (hctorOf usj)
      ((hctorOf _).trans (by rw [hulevOf _ rfl])) f1 f2 hfitC hm hne
    refine ⟨_, [x1, x2, y3], _, restC', rfl, rfl, by rw [hCtorRead, hulevOf _ rfl], rfl, rfl,
      ?_, hfitC', hval⟩
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact hxwd _ hx1
    · exact hxwd _ hx2
    · exact hywd _ (by simp)
  intro usj _ hlev TVja _
  refine ⟨fun ρ xs a restR hxs hfit ha ys _ _ _ _ =>
      (hext usj hlev).2 ρ a ⟨xs, restR, hxs, hfit⟩ ha ys, ?_⟩
  intro ρ xs ys restR restC _ _ _ _ _ _ _ _ _ _
  exact ⟨restC, [], rfl, Or.inl rfl, fun i hi => absurd hi (by omega)⟩

set_option maxHeartbeats 1000000 in
/-- **`Quot.lift`'s `RecRuleLaw` row.**  The rule is `.plain`, so both
`.nested` conjuncts are `nomatch`.  The two telescope fits are peeled
with `interp_inst_cons1`..`_cons4`, which put every substituted domain
at exactly the `cons` environment its space lemma is stated at; the
fired equality is `quotLiftV_fired` against `quotLiftRa_app`; the
transport is six `WellDenoted_app_fibre` steps over `quotLiftRaSpace`. -/
theorem quotLiftLaw {m : EnvModel V env}
    (m₂ : EnvModel V ⟨quotLiftA :: env.consts, env.tables⟩)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : EqStored env) (heq : EqLaw m)
    (hac : m₂.acval = acvalWith m.acval quotLiftA.name
      (fun ψ => Term.const .quotLift [ψ uN, ψ vN]))
    (φ : Name → Nat) :
    RecRuleLaw m₂ φ quotLiftA.name quotLiftA.toConstantVal 5 5 false
      quotLiftRule := by
  refine ⟨Nat.le_refl 5, fun us hus => ?_,
    quotLiftExtra (m := m) m₂ hQ hM hE hac φ⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ quotLiftA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hEuN : Level.substFn ψ [eqLp env] [Level.param vN] (eqLp env) = ψ vN := by
    simp [Level.substFn, Level.eval]
  obtain ⟨hval0, hgr0⟩ :=
    EqLaw.at heq hE (Level.substFn ψ [eqLp env] [Level.param vN])
  rw [hEuN] at hval0 hgr0
  have hRa : denote m₂.acval ⟨quotLiftA :: env.consts, env.tables⟩ φ 0
      (quotLiftRule.rhs.instantiateLevelParams
        quotLiftA.toConstantVal.levelParams us)
      = some (quotLiftRa
          (m.acval eqName (Level.substFn ψ [eqLp env] [Level.param vN]))
          (ψ uN) (ψ vN)) := by
    rw [denote_instLevels m₂.acval_params φ, hac, hψ,
      denote_quotLift_rhs (m := m) _ hE]
  refine ⟨_, hRa,
    fun ρ => quotLiftRa_wellDenoted hval0 hgr0 ρ, ?_, ?_⟩
  · intro _ _ h
    exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev _ hpin hTVa hTVja hfitR hfitC
  have hM' : (⟨quotLiftA :: env.consts, env.tables⟩ : Env).find? quotMkName
      = some quotMkA := by
    rw [ConLeche.Env.find?_cons, ite_eq_right (by decide)]; exact hM
  rw [show RecRule.ctor quotLiftRule = quotMkName from rfl, hM'] at hfj
  obtain ⟨rfl, rfl, rfl⟩ :
      cvj = quotMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 1 := by
    injection Option.some.inj hfj with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  obtain ⟨x1, x2, x3, x4, x5, rfl⟩ :
      ∃ p q r s t, xs = [p, q, r, s, t] := by
    match xs, hxs with
    | [p, q, r, s, t], _ => exact ⟨p, q, r, s, t, rfl⟩
  obtain ⟨y1, y2, y3, rfl⟩ : ∃ p q r, ys = [p, q, r] := by
    match ys, hys with
    | [p, q, r], _ => exact ⟨p, q, r, rfl⟩
  -- the constructor's level is the recursor's own `u`
  have hulev : Level.substFn φ quotMkA.toConstantVal.levelParams usj uN
      = ψ uN := by
    rw [congrFun hlev uN, hψ]
    show Level.eval φ (Level.subst quotLiftA.toConstantVal.levelParams
      us (.param uN)) = _
    rw [Level.subst, Level.eval_subst_go]
  -- the two readings, identified
  have hTyRead : denote m₂.acval ⟨quotLiftA :: env.consts, env.tables⟩ φ 0
      (quotLiftA.toConstantVal.type.instantiateLevelParams
        quotLiftA.toConstantVal.levelParams us)
      = some (quotLiftTy
          (m.acval eqName (Level.substFn ψ [eqLp env] [Level.param vN]))
          (ψ uN) (ψ vN)) := by
    rw [denote_instLevels m₂.acval_params φ, hac, hψ,
      denote_quotLiftA_type (m := m) _ hQ hE]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hCtorRead : denote m₂.acval ⟨quotLiftA :: env.consts, env.tables⟩ φ 0
      (quotMkA.toConstantVal.type.instantiateLevelParams
        quotMkA.toConstantVal.levelParams usj)
      = some (quotMkTy
          (Level.substFn φ quotMkA.toConstantVal.levelParams usj uN)) := by
    rw [denote_instLevels m₂.acval_params φ, hac,
      denote_quotMkTy (m := m) _ (by decide) hQ]
  obtain rfl : TVja = _ :=
    (Option.some.inj (hCtorRead.symm.trans hTVja)).symm
  -- peel the recursor's telescope
  rw [quotLiftTy] at hfitR
  cases hfitR with | cons f1 hfitR =>
  cases hfitR with | cons f2 hfitR =>
  cases hfitR with | cons f3 hfitR =>
  cases hfitR with | cons f4 hfitR =>
  cases hfitR with | cons f5 hfitR =>
  cases hfitR with | cons f6 _ =>
  rw [interp_sort] at f1
  rw [interp_inst0, quotRelTy_interp] at f2
  rw [interp_inst0, interp_inst_cons1, interp_sort] at f3
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    interp_pi] at f4
  simp only [interp_bvar, cons] at f4
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    interp_inst_cons3,
    (quotLiftInvTy_data ρ hval0 hgr0 f2 (IsTy_of_mem_univ f1) f3 f4).1] at f5
  rw [interp_inst0, interp_inst_cons1, interp_inst_cons2,
    interp_inst_cons3, interp_inst_cons4,
    (quotApp_data (u := ψ uN) (i := 4) (j := 3)
      (ρ := cons (interp V ρ x5) (cons (interp V ρ x4)
        (cons (interp V ρ x3) (cons (interp V ρ x2)
          (cons (interp V ρ x1) ρ)))))
      (by simp [cons]) (by simp [cons]) f1 f2).2] at f6
  -- peel the constructor's telescope
  rw [quotMkTy] at hfitC
  cases hfitC with | cons g1 hfitC =>
  cases hfitC with | cons g2 hfitC =>
  cases hfitC with | cons g3 _ =>
  rw [hulev, interp_sort] at g1
  rw [interp_inst0, quotRelTy_interp] at g2
  rw [interp_inst0, interp_inst_cons1] at g3
  simp only [interp_bvar, cons] at g3
  -- the two leaves
  have hrecL : m₂.acval quotLiftA.name
      (Level.substFn φ quotLiftA.toConstantVal.levelParams us)
      = Term.const .quotLift [ψ uN, ψ vN] := by
    rw [hac, acvalWith_self, hψ]
  have hctorL0 : m₂.acval quotMkName
      (Level.substFn φ quotMkA.toConstantVal.levelParams usj)
      = Term.const .quotMk
        [Level.substFn φ quotMkA.toConstantVal.levelParams usj uN] := by
    rw [hac, acvalWith_ne (by decide)]
    refine EnvModel.acval_pinned m hM (by decide) ?_
    simp +decide [ConLeche.Verify.pinnedStructT]
  have hctorL : m₂.acval quotMkName
      (Level.substFn φ quotMkA.toConstantVal.levelParams usj)
      = Term.const .quotMk [ψ uN] := by rw [hctorL0, hulev]
  -- the major premise's fit: the class formed at the CONSTRUCTOR's
  -- parameters lies in the quotient at the recursor's, which is all the
  -- rule needs — the two parameter spines are never compared
  have hmem : quotClass (ψ uN) (interp V ρ y1) (interp V ρ y2) (interp V ρ y3)
      ∈ˢ quotSet (ψ uN) (interp V ρ x1) (interp V ρ x2) := by
    simp only [show RecRule.ctor quotLiftRule = quotMkName from rfl,
      Term.mkAppN_cons, Term.mkAppN_nil, interp_app,
      hctorL, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero] at f6
    rwa [quotMkV_app V g1 (g2) g3] at f6
  obtain ⟨hg3, hcls⟩ := quotClass_of_mem_quotSet f1 g1 g3 hmem
  refine ⟨?_, ?_⟩
  · -- the fired equality
    simp only [show RecRule.ctor quotLiftRule = quotMkName from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      Term.mkAppN_cons, Term.mkAppN_nil, hrecL, hctorL,
      interp_app, interp_const, bval, ConLeche.Term.lv,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [quotMkV_app V g1 (g2) g3, hcls,
      quotLiftV_fired f1 f2 f3 f4 f5 hg3,
      quotLiftRa_app hval0 hgr0 ρ f1 f2 f3 f4 f5 hg3]
  · -- the transport
    intro hxsA hysA
    simp only [
      List.take, List.drop, List.cons_append, List.nil_append,
      Term.mkAppN_cons, Term.mkAppN_nil]
    have hRa := quotLiftRa_facts (u := ψ uN) hval0 hgr0 ρ
    have hRm := hRa.2
    rw [quotLiftRaSpace] at hRm
    have h1 := WellDenoted_app_fibre hRa.1 (hxsA x1 (by simp)) hRm f1 (IsTy_univ _)
    have h2 := WellDenoted_app_fibre h1.1 (hxsA x2 (by simp)) h1.2 f2 (IsTy_relSpace _)
    have h3 := WellDenoted_app_fibre h2.1 (hxsA x3 (by simp)) h2.2 f3 (IsTy_univ _)
    have h4 := WellDenoted_app_fibre h3.1 (hxsA x4 (by simp)) h3.2 f4 IsTy_piV
    have h5 := WellDenoted_app_fibre h4.1 (hxsA x5 (by simp)) h4.2 f5 (IsTy_piR _ _ _)
    exact (WellDenoted_app_fibre h5.1 (hysA y3 (by simp)) h5.2 hg3
      (IsTy_of_mem_univ f1)).1

/-- The two `EqLaw` halves at the assignment `Quot.lift` reads the
`Eq` former at — `v`, not the constant's own first parameter. -/
theorem quotLift_eqLaws (mp : EnvModelM V env)
    (hE : EqStored env) (ψ : Name → Nat) :
    (∀ (ρ : Nat → V) (T x y : V), T ∈ˢ (univ (ψ vN) : V) →
      x ∈ˢ T → y ∈ˢ T →
      app (app (app (interp V ρ (mp.base2.acval eqName
        (Level.substFn ψ [eqLp env] [Level.param vN]))) T) x) y = eqv x y) ∧
    (∀ (ρ : Nat → V) (Aa la ra : Term),
      WellDenoted V ρ Aa → WellDenoted V ρ la → WellDenoted V ρ ra →
      interp V ρ Aa ∈ˢ (univ (ψ vN) : V) →
      interp V ρ la ∈ˢ interp V ρ Aa →
      interp V ρ ra ∈ˢ interp V ρ Aa →
      WellDenoted V ρ (.app (.app (.app (mp.base2.acval eqName
          (Level.substFn ψ [eqLp env] [Level.param vN])) Aa) la) ra) ∧
        interp V ρ (.app (.app (.app (mp.base2.acval eqName
          (Level.substFn ψ [eqLp env] [Level.param vN])) Aa) la) ra)
          ∈ˢ (univZero : V)) := by
  have hEuN : Level.substFn ψ [eqLp env] [Level.param vN] (eqLp env) = ψ vN := by
    simp [Level.substFn, Level.eval]
  obtain ⟨hval0, hgr0⟩ :=
    EqLaw.at mp.eq_law hE (Level.substFn ψ [eqLp env] [Level.param vN])
  rw [hEuN] at hval0 hgr0
  exact ⟨hval0, hgr0⟩

/-- **`Quot.lift`, installed at the P tier.** -/
theorem extendQuotLift (mp : EnvModelM V env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : EqStored env)
    (hfresh : env.find? quotLiftA.name = none)
    (hwf : EnvWF ⟨quotLiftA :: env.consts, env.tables⟩) {ex : List Name} :
    CoverTo mp ex ⟨quotLiftA :: env.consts, env.tables⟩ ex := by
  have hty := fun ψ =>
    denote_quotLiftA_type (m := mp.base2)
      (A := fun ψ => Term.const .quotLift [ψ uN, ψ vN]) ψ hQ hE
  refine coverTo_cons hfresh (fun _ _ h => nomatch h) (declStep_preserves_of_basis_rec_cons mp
    (A := fun ψ => Term.const .quotLift [ψ uN, ψ vN]) hfresh
    (fun _ _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHead.ofBasis hwf (fun _ => trivial) rfl
      (fun ψ t hp => by
        rw [show ConLeche.Verify.pinnedStructT quotLiftA.name ψ
          = some (Term.const .quotLift [ψ uN, ψ vN]) from rfl] at hp
        rw [← Option.some.inj hp])
      (fun _ _ _ _ _ heq r hr => by
        injection heq with _ _ _ _ h4
        rw [← h4] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨_, _, _, hM, rfl⟩
        · exact nomatch hr'))
    ?_
    (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by
        show uN ∈ [uN, vN]
        exact List.mem_cons_self),
      hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact quotLiftTy_wellDenoted (quotLift_eqLaws mp hE ψ).1
      (quotLift_eqLaws mp hE ψ).2 ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [interp_const]
    exact quotLiftTy_mem (quotLift_eqLaws mp hE ψ).1
      (quotLift_eqLaws mp hE ψ).2 ρ
  · intro m₂ hac φ
    refine recRules_cons_rec mp hfresh quotLiftA_eq m₂ hac φ ?_
    intro rl hrl
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact quotLiftLaw (m := mp.base2) m₂ hQ hM hE mp.eq_law hac φ
    · exact nomatch hr'

theorem quotStored_of {env : Env} {n : Name} {pin : ConstantInfo}
    (h : (match env.find? n with
      | some c => c.beqP pin
      | none => false) = true) : env.find? n = some pin := by
  cases hf : env.find? n with
  | none => rw [hf] at h; exact nomatch h
  | some c =>
    rw [hf] at h
    exact congrArg some (ConstantInfo.eq_of_beqP h)

/-- **A quotient record, installed at the P tier**: its slot's constant, on
the slots it needs. -/
theorem declQuotPB {env₁ : Env} (mp : EnvModelM V env) {k : ConLeche.QuotKind} {cv : ConstantVal}
    (h : ConLeche.Semantics.DeclQuotRun env k cv env₁) :
    CoverStep mp env₁ := by
  obtain ⟨-, hp, hfr, rfl⟩ := h
  have hcons : ∀ {c₀ : ConstantInfo} {n : Name} {ci : ConstantInfo}, ¬ c₀.name = n →
      env.find? n = some ci → (⟨c₀ :: env.consts, env.tables⟩ : Env).find? n = some ci :=
    fun hne hf => by rw [ConLeche.Env.find?_cons, ite_eq_right hne]; exact hf
  cases k with
  | type =>
    have hf1 : env.find? quotA.name = none := Option.isNone_iff_eq_none.mp hfr
    have hwf1 : EnvWF ⟨quotA :: env.consts, env.tables⟩ :=
      EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
        (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ _ heq => nomatch heq),
        (by first
          | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
              first | exact absurd h (by decide) | rfl)
          | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
    exact extendQuot mp hf1 hwf1
  | ctor =>
    have hQ : env.find? quotName = some quotA := quotStored_of hp
    have hf2 : env.find? quotMkA.name = none := Option.isNone_iff_eq_none.mp hfr
    have hwf2 : EnvWF ⟨quotMkA :: env.consts, env.tables⟩ := by
      refine EnvWF.cons mp.base2.wf ⟨rfl, rfl, ?_, rfl,
        (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ _ heq => nomatch heq),
        (by first
          | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
              first | exact absurd h (by decide) | rfl)
          | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
      show Expr.constsResolve _ quotMkA.toConstantVal.type = true
      have hf : (⟨quotMkA :: env.consts, env.tables⟩ : Env).find? quotName = some quotA :=
        hcons (by decide) hQ
      rw [show quotMkA.toConstantVal.type
        = Expr.forallE (.sort (.param uN))
            (Expr.forallE
              (Expr.forallE (.bvar 0)
                (Expr.forallE (.bvar 1) (.sort .zero)))
              (Expr.forallE (.bvar 1)
                (.app (.app (.const quotName [.param uN]) (.bvar 2))
                  (.bvar 1)))) from rfl]
      simp [Expr.constsResolve, hf]
    exact extendQuotMk mp hQ hf2 hwf2
  | lift =>
    simp only [ConLeche.quotPredsOk, Bool.and_eq_true] at hp
    obtain ⟨⟨hEs, hQs⟩, hMs⟩ := hp
    have hE : EqStored env := mp.base2.basis_pinned.eqStored hEs
    have hQ : env.find? quotName = some quotA := quotStored_of hQs
    have hM : env.find? quotMkName = some quotMkA := quotStored_of hMs
    obtain ⟨ciE, hfE0, hlE⟩ := hE
    have hf3 : env.find? quotLiftA.name = none := Option.isNone_iff_eq_none.mp hfr
    have hwf3 : EnvWF ⟨quotLiftA :: env.consts, env.tables⟩ := by
      have hfQ : (⟨quotLiftA :: env.consts, env.tables⟩ : Env).find? quotName = some quotA :=
        hcons (by decide) hQ
      have hfE : (⟨quotLiftA :: env.consts, env.tables⟩ : Env).find? eqName = some ciE :=
        hcons (by decide) hfE0
      refine EnvWF.cons mp.base2.wf ⟨rfl, rfl, ?_, rfl,
        (fun _ _ _ heq => nomatch heq), ?_,
        (by first
          | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
              first | exact absurd h (by decide) | rfl)
          | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
      · show Expr.constsResolve _ quotLiftA.toConstantVal.type = true
        rw [show quotLiftA.toConstantVal.type
            = Expr.forallE (.sort (.param uN))
                (Expr.forallE
                  (Expr.forallE (.bvar 0)
                    (Expr.forallE (.bvar 1) (.sort .zero)))
                  (Expr.forallE
                    (.sort (.param vN))
                    (Expr.forallE
                      (Expr.forallE (.bvar 2)
                        (.bvar 1))
                      (Expr.forallE
                        (Expr.forallE (.bvar 3)
                          (Expr.forallE (.bvar 4)
                            (Expr.forallE
                              (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                              (.app (.app (.app
                                (.const eqName [.param vN]) (.bvar 4))
                                (.app (.bvar 3) (.bvar 2)))
                                (.app (.bvar 3) (.bvar 1))))))
                        (Expr.forallE
                          (.app (.app (.const quotName [.param uN])
                            (.bvar 4)) (.bvar 3))
                          (.bvar 3)))))) from rfl]
        simp [Expr.constsResolve, hfQ, hfE]
      · intro cv mI rP isK rules heq
        injection heq with h1' _ _ _ h4'
        subst h1'; subst h4'
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨rfl, rfl, by
            show Expr.constsResolve _ (RecRule.rhs quotLiftRule) = true
            simp [Expr.constsResolve, quotLiftRule, hfE], rfl,
            fun lvls pins heqf => nomatch heqf⟩
        · exact nomatch hr'
    exact extendQuotLift mp hQ hM ⟨ciE, hfE0, hlE⟩ hf3 hwf3
  | ind =>
    simp only [ConLeche.quotPredsOk, Bool.and_eq_true] at hp
    have hQ : env.find? quotName = some quotA := quotStored_of hp.1
    have hM : env.find? quotMkName = some quotMkA := quotStored_of hp.2
    have hf4 : env.find? quotIndA.name = none := Option.isNone_iff_eq_none.mp hfr
    have hwf4 : EnvWF ⟨quotIndA :: env.consts, env.tables⟩ := by
      have hfQ : (⟨quotIndA :: env.consts, env.tables⟩ : Env).find? quotName = some quotA :=
        hcons (by decide) hQ
      have hfM : (⟨quotIndA :: env.consts, env.tables⟩ : Env).find? quotMkName = some quotMkA :=
        hcons (by decide) hM
      refine EnvWF.cons mp.base2.wf ⟨rfl, rfl, ?_, rfl,
        (fun _ _ _ heq => nomatch heq), ?_,
        (by first
          | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
              first | exact absurd h (by decide) | rfl)
          | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
      · show Expr.constsResolve _ quotIndA.toConstantVal.type = true
        rw [show quotIndA.toConstantVal.type
            = Expr.forallE (.sort (.param uN))
                (Expr.forallE
                  (Expr.forallE (.bvar 0)
                    (Expr.forallE (.bvar 1) (.sort .zero)))
                  (Expr.forallE
                    (Expr.forallE
                      (.app (.app (.const quotName [.param uN]) (.bvar 1))
                        (.bvar 0)) (.sort .zero))
                    (Expr.forallE
                      (Expr.forallE (.bvar 2)
                        (.app (.bvar 1)
                          (.app (.app (.app
                            (.const quotMkName [.param uN])
                            (.bvar 3)) (.bvar 2)) (.bvar 0))))
                      (Expr.forallE
                        (.app (.app (.const quotName [.param uN])
                          (.bvar 3)) (.bvar 2))
                        (.app (.bvar 2) (.bvar 0)))))) from rfl]
        simp [Expr.constsResolve, hfQ, hfM]
      · intro cv mI rP isK rules heq
        injection heq with h1' _ _ _ h4'
        subst h1'; subst h4'
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨rfl, rfl, by
            show Expr.constsResolve _ (RecRule.rhs quotIndRule) = true
            simp [Expr.constsResolve, quotIndRule, hfQ, hfM], rfl,
            fun lvls pins heqf => nomatch heqf⟩
        · exact nomatch hr'
    exact extendQuotInd mp hQ hM hf4 hwf4
  | sound =>
    simp only [ConLeche.quotPredsOk, Bool.and_eq_true] at hp
    obtain ⟨⟨hEs, hQs⟩, hMs⟩ := hp
    have hE : EqStored env := mp.base2.basis_pinned.eqStored hEs
    have hQ : env.find? quotName = some quotA := quotStored_of hQs
    have hM : env.find? quotMkName = some quotMkA := quotStored_of hMs
    obtain ⟨ciE, hfE0, hlE⟩ := hE
    have hf5 : env.find? quotSoundA.name = none := Option.isNone_iff_eq_none.mp hfr
    have hwf5 : EnvWF ⟨quotSoundA :: env.consts, env.tables⟩ := by
      have hfQ : (⟨quotSoundA :: env.consts, env.tables⟩ : Env).find? quotName = some quotA :=
        hcons (by decide) hQ
      have hfM : (⟨quotSoundA :: env.consts, env.tables⟩ : Env).find? quotMkName = some quotMkA :=
        hcons (by decide) hM
      have hfE : (⟨quotSoundA :: env.consts, env.tables⟩ : Env).find? eqName = some ciE :=
        hcons (by decide) hfE0
      refine EnvWF.cons mp.base2.wf ⟨rfl, rfl, ?_, rfl,
        (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ _ heq => nomatch heq),
        (by first
          | (refine ConLeche.IndCapsWF.of_caps ?_ ?_ <;> intro h <;>
              first | exact absurd h (by decide) | rfl)
          | exact fun _ _ heq => ConstantInfo.noConfusion heq)⟩
      show Expr.constsResolve _ quotSoundA.toConstantVal.type = true
      rw [show quotSoundA.toConstantVal.type
          = Expr.forallE (.sort (.param uN))
              (Expr.forallE
                (Expr.forallE (.bvar 0)
                  (Expr.forallE (.bvar 1) (.sort .zero)))
                (Expr.forallE (.bvar 1)
                  (Expr.forallE (.bvar 2)
                    (Expr.forallE
                      (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                      (.app (.app (.app (.const eqName [.param uN])
                        (.app (.app (.const quotName [.param uN])
                          (.bvar 4)) (.bvar 3)))
                        (.app (.app (.app
                          (.const quotMkName [.param uN])
                          (.bvar 4)) (.bvar 3)) (.bvar 2)))
                        (.app (.app (.app
                          (.const quotMkName [.param uN])
                          (.bvar 4)) (.bvar 3)) (.bvar 1))))))) from rfl]
      simp [Expr.constsResolve, hfQ, hfM, hfE]
    exact extendQuotSound mp hQ hM ⟨ciE, hfE0, hlE⟩ hf5 hwf5

end Quot

end ConLeche.Model
