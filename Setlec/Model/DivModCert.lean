import Setlec.Model.NatOps
import Setlec.Model.NatLit
import Setlec.Model.Annotate
import Setlec.Model.TypeChecker
import Setlec.Model.Basis.Eq.Install
import Setlec.Model.FvarsOkLemmas
import Setlec.Verify.Leaves
import Setlec.Verify.InferLeaves
import Setlec.Verify.BridgeWfImp
import Setlec.Model.Extend.Inversions

/-!
# Soundness of the `Nat.div`/`Nat.mod` characterization certificates

The kernel checks each pinned certificate over an opened `fvar`
telescope (`checkDivModCerts`): the vendored proof, self-references
substituted with the stored annotated value, is applied to
`x := fvar 0`, `y := fvar 1` and hypothesis variables carrying the
pinned `ble`-guard types, annotated, inferred, and its type compared
against the pinned characteristic equation.  This module turns a
successful run into the value-level guarded recurrence (`vl = vr` at
the interpreted equation sides), the content of `DivModEqs`:

* the certificate frame's valuation puts the proof point at the
  hypothesis variables — inhabitation of the interpreted guard types
  is exactly the semantic guard equalities (`pt_mem_eqv_self`);
* `annotate_sound`/`inferTypeCore_sound` give the applied proof's
  membership in its inferred type; `isDefEqCore_sound` identifies that
  type with the pinned equation's interpretation, computed by the
  (depth-generic) `eqSide` machinery through the pinned `Eq` value
  (`eqVal_app₃`); `mem_eqv` closes.

The vendored proof blob stays completely opaque: nothing here inspects
it — only the runs it went through.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}

open SetTheory Expr

/-! ## The certificate frame -/

/-- The certificate frame's valuation: `x`, `y`, then the proof point
at the hypothesis slots. -/
def rho4 (x y : V) : Nat → V :=
  updV V (updV V (updV V (updV V (rho0 V) 0 x) 1 y) 2 pt) 3 pt

@[simp] theorem rho4_0 {x y : V} : rho4 x y 0 = x := by simp [rho4, updV]
@[simp] theorem rho4_1 {x y : V} : rho4 x y 1 = y := by simp [rho4, updV]
@[simp] theorem rho4_2 {x y : V} : rho4 x y 2 = pt := by simp [rho4, updV]
@[simp] theorem rho4_3 {x y : V} : rho4 x y 3 = pt := by simp [rho4, updV]

/-! ## The pinned equality in the model -/

/-- A stored (hence pinned) `Eq` carries the `eqVal` valuation. -/
theorem valEq_of_pinned (m : EnvModel V env)
    (hEqA : env.find? eqName = some eqA) :
    ∀ ψ' : Name → Nat, m.val eqName ψ' = eqVal V ψ' := by
  intro ψ'
  obtain ⟨-, hval⟩ := m.ind_ok.right.right.right.left eqName eqA hEqA
    rfl (by decide)
  rw [hval ψ']
  show pinnedVal V eqName ψ' = eqVal V ψ'
  delta pinnedVal
  rw [if_pos rfl]

/-- The level assignment of `Eq.{1}`. -/
def psiEq1 (ψ : Name → Nat) : Name → Nat :=
  Level.substFn ψ [uN] [.succ .zero]

theorem psiEq1_uN : psiEq1 ψ uN = 1 := rfl

/-- Interpretation of the `Eq.{1}` head. -/
theorem interp_eqHead (m : EnvModel V env)
    (hEqA : env.find? eqName = some eqA) {d : Nat} {ρ : Nat → V} :
    interpExpr V m.val env ψ d ρ (.const eqName [.succ .zero]) =
      some (eqVal V (psiEq1 ψ)) := by
  simp only [interpExpr, hEqA]
  rw [if_pos (by decide)]
  simp only [Option.some.injEq]
  rw [show eqA.toConstantVal.levelParams = [uN] from rfl]
  exact valEq_of_pinned m hEqA (psiEq1 ψ)

/-- The full pinned-equality application over a stored monomorphic
domain constant, as an equation side: value `eqv vl vr`, home
`univ 0`. -/
theorem eqSide_eqApp (m : EnvModel V env)
    (hEqA : env.find? eqName = some eqA)
    {A : Name} {ci : ConstantInfo} {dd : Nat} {ρ : Nat → V}
    {l r : Expr} {vl vr : V}
    (hAf : env.find? A = some ci)
    (hAlp : ci.toConstantVal.levelParams = [])
    (hAu : m.val A ψ ∈ˢ univ 1)
    (hl : EqSideOk env m.val ψ dd ρ l vl (m.val A ψ))
    (hr : EqSideOk env m.val ψ dd ρ r vr (m.val A ψ)) :
    EqSideOk env m.val ψ dd ρ
      (.app (.app (.app (.const eqName [.succ .zero]) (.const A [])) l) r)
      (eqv vl vr) (univ 0) := by
  obtain ⟨hli, hlm, hlA, hlF, hlW, hlB, hlL⟩ := hl
  obtain ⟨hri, hrm, hrA, hrF, hrW, hrB, hrL⟩ := hr
  have hu1 : psiEq1 ψ uN = 1 := psiEq1_uN
  have hAu' : m.val A ψ ∈ˢ univ (psiEq1 ψ uN) := by rw [hu1]; exact hAu
  have hAi : interpExpr V m.val env ψ dd ρ (.const A []) =
      some (m.val A ψ) := interp_const_mono hAf hAlp
  have hEqI := interp_eqHead (ψ := ψ) m hEqA (d := dd) (ρ := ρ)
  -- the three application stages' memberships
  have hm0 : eqVal V (psiEq1 ψ) ∈ˢ
      pi (Nat.max (psiEq1 ψ uN) (Nat.max (psiEq1 ψ uN) 1))
        (univ (psiEq1 ψ uN))
        (fun X => pi (Nat.max (psiEq1 ψ uN) 1) X fun _ =>
          pi 1 X fun _ => (univ 0 : V)) := eqVal_mem (V := V) (ψ := psiEq1 ψ)
  have hfib0 : ∀ X, X ∈ˢ univ (psiEq1 ψ uN) →
      (pi (Nat.max (psiEq1 ψ uN) 1) X fun _ => pi 1 X fun _ => (univ 0 : V)) ∈ˢ
        univ (Nat.max (psiEq1 ψ uN) (Nat.max (psiEq1 ψ uN) 1)) :=
    fun X hX => eq_fibre_mem (ψ := psiEq1 ψ) hX
  have hm1 : SetTheory.app (eqVal V (psiEq1 ψ)) (m.val A ψ) ∈ˢ
      pi (Nat.max (psiEq1 ψ uN) 1) (m.val A ψ)
        (fun _ => pi 1 (m.val A ψ) fun _ => (univ 0 : V)) :=
    eqVal_app_mem (ψ := psiEq1 ψ) hAu'
  have hfib1 : ∀ x, x ∈ˢ m.val A ψ →
      (pi 1 (m.val A ψ) fun _ => (univ 0 : V)) ∈ˢ
        univ (Nat.max (psiEq1 ψ uN) 1) := by
    intro x hx
    have h := pi_mem_univ (u := psiEq1 ψ uN) (v := 1)
      (B := fun _ => univ 0) hAu' (fun _ _ => univ_mem_univ 0)
    simpa using h
  have hm2 : SetTheory.app (SetTheory.app (eqVal V (psiEq1 ψ))
      (m.val A ψ)) vl ∈ˢ pi 1 (m.val A ψ) (fun _ => (univ 0 : V)) :=
    eqVal_app₂_mem (ψ := psiEq1 ψ) hAu' hlm
  have hfib2 : ∀ x, x ∈ˢ m.val A ψ → univ 0 ∈ˢ (univ 1 : V) :=
    fun _ _ => univ_mem_univ 0
  refine ⟨?_, eqv_mem_univ vl vr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [interp_app1 (interp_app1 (interp_app1 hEqI hAi) hli) hri]
    rw [eqVal_app₃ (ψ := psiEq1 ψ) hAu' hlm hrm]
  · -- AnnotOk of the application chain
    simp only [AnnotOk]
    refine ⟨⟨⟨trivial, trivial,
        eqVal V (psiEq1 ψ), m.val A ψ, _, univ (psiEq1 ψ uN), _,
        hEqI, hAi, hm0, hAu', hfib0⟩,
      hlA,
        SetTheory.app (eqVal V (psiEq1 ψ)) (m.val A ψ), vl, _,
        m.val A ψ, _, interp_app1 hEqI hAi, hli, hm1, hlm, hfib1⟩,
      hrA,
        SetTheory.app (SetTheory.app (eqVal V (psiEq1 ψ)) (m.val A ψ)) vl,
        vr, 1, m.val A ψ, fun _ => univ 0,
        interp_app1 (interp_app1 hEqI hAi) hli, hri, hm2, hrm, hfib2⟩
  · intro lf hlf
    simp only [Expr.fvarLeaves, List.mem_append, List.not_mem_nil,
      false_or, List.nil_append] at hlf
    rcases hlf with hlf | hlf
    · exact hlF lf hlf
    · exact hrF lf hlf
  · simp only [WScoped]
    exact ⟨⟨⟨trivial, trivial⟩, hlW⟩, hrW⟩
  · simp [Expr.looseBVarsBounded, hlB, hrB]
  · intro lf hlf
    simp only [Expr.fvarLeaves, List.mem_append, List.not_mem_nil,
      false_or, List.nil_append] at hlf
    rcases hlf with hlf | hlf
    · exact hlL lf hlf
    · exact hrL lf hlf

/-! ## The workhorse: one certificate run to one value equation -/

/-- A successful certificate run — annotate, infer, defeq against the
pinned equation — identifies the equation sides' values.  The proof
blob (`proofS`) is opaque: only its runs matter. -/
theorem divModCert_extract (m : EnvModel V env) (F : Nat)
    {proofS : Expr} {hypsS : List Expr} {eqS : Expr}
    {ρ : Nat → V} {vE : V} {appliedA tp : Expr}
    (hFv : FvarsOk V m.val env ψ 4 ρ (divModCertApplied proofS hypsS))
    (hW : WScoped 4 (divModCertApplied proofS hypsS))
    (hB : (divModCertApplied proofS hypsS).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (divModCertApplied proofS hypsS))
    (heq : EqSideOk env m.val ψ 4 ρ eqS vE (univ 0))
    (hann : annotateCore env F 4 (divModCertApplied proofS hypsS) =
      .ok appliedA)
    (hinf : inferTypeCore env F 4 appliedA = .ok tp)
    (hde : isDefEqCore env F 4 tp eqS = .ok true) :
    ∃ w, w ∈ˢ vE := by
  obtain ⟨hei, hem, heA, heF, heW, heB, heL⟩ := heq
  -- the annotate run: truthful annotations for the applied proof
  have hAappA : AnnotOk V m.val env ψ 4 ρ appliedA :=
    annotate_sound m _ hann hW hB hLb ρ hFv
  have hsub := annotateCore_leaves_sub F _ hann hW hB
  have hFappA : FvarsOk V m.val env ψ 4 ρ appliedA :=
    FvarsOk.of_subset hsub hFv
  have hWappA : WScoped 4 appliedA := annotateCore_WScoped F _ hann hW
  have hBappA : appliedA.looseBVarsBounded 0 = true :=
    annotateCore_looseBVars F _ hann hB
  have hLappA : Expr.LeavesBounded appliedA :=
    fun l hl => hLb l (hsub l hl)
  -- the inference run: the applied proof inhabits its inferred type
  obtain ⟨⟨v, tv, hvi, htvi, hvm⟩, hWtp, hAtp⟩ :=
    inferTypeCore_sound (φ := ψ) m F hinf hWappA hBappA hLappA hFappA hAappA
  -- the defeq run: the inferred type is the pinned equation's value
  have hFtp : FvarsOk V m.val env ψ 4 ρ tp :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf F hinf hWappA) hFappA
  have hLtp : Expr.LeavesBounded tp :=
    fun l hl => hLappA l (inferTypeCore_fvarLeaves m.wf F hinf hWappA l hl)
  have hBtp : tp.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf F hinf hWappA hBappA hLappA
  have heqv : tv = vE :=
    isDefEqCore_sound (φ := ψ) m F hde hWtp heW hBtp heB hLtp heL
      hFtp heF hAtp heA htvi hei
  exact ⟨v, heqv ▸ hvm⟩

/-! ## `Bool`-side equation components -/

/-- The `Bool` pins hidden in `Nat.ble`'s pinned type. -/
theorem natOpTyPinned_boolFacts {ty : Expr}
    (h : natOpTyPinned env natBleName ty = true) :
    ∃ ci, env.find? boolName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type = .sort (.succ .zero) := by
  unfold natOpTyPinned at h
  rw [if_neg (by decide)] at h
  revert h
  match ty with
  | .forallE nm dom (.forallE nm2 dom2 body mb2) mb => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _
  | .forallE _ _ (.bvar _) _ | .forallE _ _ (.fvar _ _ _) _
  | .forallE _ _ (.sort _) _ | .forallE _ _ (.const _ _) _
  | .forallE _ _ (.app _ _) _ | .forallE _ _ (.lam _ _ _ _) _
  | .forallE _ _ (.letE _ _ _ _) _ | .forallE _ _ (.lit _) _
  | .forallE _ _ (.proj _ _ _) _ =>
    intro h; exact nomatch h
  intro h
  simp only [Bool.and_eq_true] at h
  have hcod := h.1.1.2
  unfold natOpCod at hcod
  rw [if_pos (by decide)] at hcod
  revert hcod
  split
  · next ci heq =>
    intro hcod
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hcod
    exact ⟨ci, heq, hcod.2.1, hcod.2.2⟩
  · intro hcod
    simp at hcod

section BoolSides

variable (m : EnvModel V env) {dd : Nat} {ρ : Nat → V}

/-- A `Bool` constructor stored at the pinned type `Bool`, as an
equation side valued in the `Bool` value. -/
theorem eqSide_boolCtor {bn : Name} {cib cin : ConstantInfo}
    (hbf : env.find? bn = some cib)
    (hblp : cib.toConstantVal.levelParams = [])
    (hbty : cib.toConstantVal.type = .const boolName [])
    (hnf : env.find? boolName = some cin)
    (hnlp : cin.toConstantVal.levelParams = []) :
    EqSideOk env m.val ψ dd ρ (.const bn []) (m.val bn ψ)
      (m.val boolName ψ) := by
  refine ⟨interp_const_mono hbf hblp, ?_, by simp [AnnotOk],
    fun l hl => by simp [Expr.fvarLeaves] at hl, by simp [WScoped], rfl,
    fun l hl => by simp [Expr.fvarLeaves] at hl⟩
  obtain ⟨T, hT, hmem⟩ := m.mem_type _ (find?_mem hbf) ψ
  have hname : cib.name = bn := by
    have := List.find?_some hbf
    simpa using this
  rw [hname] at hmem
  rw [hbty] at hT
  rw [show interpClosed V m.val env ψ (.const boolName []) =
      some (m.val boolName ψ) from interp_const_mono hnf hnlp] at hT
  obtain rfl := Option.some.inj hT
  exact hmem

end BoolSides

/-! ## The applied certificate's frame facts -/

section AppliedFacts

variable {cval : ConstVal V} {d : Nat} {ρ : Nat → V}

/-- `FvarsOk` composes over applications. -/
theorem FvarsOk.app_intro {f a : Expr}
    (hf : FvarsOk V cval env ψ d ρ f) (ha : FvarsOk V cval env ψ d ρ a) :
    FvarsOk V cval env ψ d ρ (.app f a) := by
  intro l hl
  simp only [Expr.fvarLeaves, List.mem_append] at hl
  rcases hl with hl | hl
  · exact hf l hl
  · exact ha l hl

/-- `FvarsOk` at a free variable. -/
theorem FvarsOk.fvar_intro {idx : Nat} {n : Name} {ty : Expr} {T : V}
    (hidx : idx < d) (hA : AnnotOk V cval env ψ d ρ ty)
    (hT : interpExpr V cval env ψ d ρ ty = some T) (hm : ρ idx ∈ˢ T)
    (hty : FvarsOk V cval env ψ d ρ ty) :
    FvarsOk V cval env ψ d ρ (.fvar idx n ty) := by
  intro l hl
  simp only [Expr.fvarLeaves, List.mem_cons] at hl
  rcases hl with rfl | hl
  · exact ⟨hidx, hA, T, hT, hm⟩
  · exact hty l hl

/-- `LeavesBounded` composes over applications. -/
theorem LeavesBounded.app_intro {f a : Expr}
    (hf : Expr.LeavesBounded f) (ha : Expr.LeavesBounded a) :
    Expr.LeavesBounded (.app f a) := by
  intro l hl
  simp only [Expr.fvarLeaves, List.mem_append] at hl
  rcases hl with hl | hl
  · exact hf l hl
  · exact ha l hl

/-- `LeavesBounded` at a free variable. -/
theorem LeavesBounded.fvar_intro {idx : Nat} {n : Name} {ty : Expr}
    (hb : ty.looseBVarsBounded 0 = true) (hty : Expr.LeavesBounded ty) :
    Expr.LeavesBounded (.fvar idx n ty) := by
  intro l hl
  simp only [Expr.fvarLeaves, List.mem_cons] at hl
  rcases hl with rfl | hl
  · exact hb
  · exact hty l hl

/-- The `Nat`-typed frame variables, as leaf bundles. -/
private theorem natFvar_facts (m : EnvModel V env)
    (hs : natLitSupported env = true) {idx : Nat} {n : Name}
    (hidx : idx < 4) (hm : ρ idx ∈ˢ m.val natName ψ) :
    FvarsOk V m.val env ψ 4 ρ (.fvar idx n (.const natName [])) ∧
    Expr.LeavesBounded (.fvar idx n (.const natName [])) := by
  constructor
  · exact FvarsOk.fvar_intro hidx (by simp [AnnotOk])
      (interpExpr_const_nat hs) hm
      (fun l hl => by simp [Expr.fvarLeaves] at hl)
  · exact LeavesBounded.fvar_intro rfl
      (fun l hl => by simp [Expr.fvarLeaves] at hl)

/-- Frame facts for a two-hypothesis certificate. -/
theorem applied_facts2 (m : EnvModel V env) {proofS h1 h2 : Expr}
    {H1 H2 : V}
    (hpf : proofS.hasFvar = false)
    (hpb : proofS.looseBVarsBounded 0 = true)
    (hs : natLitSupported env = true)
    (hnat0 : ρ 0 ∈ˢ m.val natName ψ) (hnat1 : ρ 1 ∈ˢ m.val natName ψ)
    (hs1 : EqSideOk env m.val ψ 4 ρ h1 H1 (univ 0)) (hpt1 : ρ 2 ∈ˢ H1)
    (hs2 : EqSideOk env m.val ψ 4 ρ h2 H2 (univ 0)) (hpt2 : ρ 3 ∈ˢ H2)
    (hw1 : h1.wscopedB 2 = true) (hw2 : h2.wscopedB 2 = true) :
    FvarsOk V m.val env ψ 4 ρ (divModCertApplied proofS [h1, h2]) ∧
    WScoped 4 (divModCertApplied proofS [h1, h2]) ∧
    (divModCertApplied proofS [h1, h2]).looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded (divModCertApplied proofS [h1, h2]) := by
  obtain ⟨h1i, -, h1A, h1F, -, h1B, h1L⟩ := hs1
  obtain ⟨h2i, -, h2A, h2F, -, h2B, h2L⟩ := hs2
  obtain ⟨hxF, hxL⟩ := natFvar_facts (n := .str .anonymous "x") m hs
    (by omega) hnat0
  obtain ⟨hyF, hyL⟩ := natFvar_facts (n := .str .anonymous "y") m hs
    (by omega) hnat1
  have hpF : FvarsOk V m.val env ψ 4 ρ proofS :=
    FvarsOk.of_not_hasFvar hpf
  have hpL : Expr.LeavesBounded proofS :=
    Expr.LeavesBounded.of_not_hasFvar hpf
  refine ⟨?_, WScoped.of_wscopedB
      (divModCertApplied_wscopedB hpf (by
        intro hyp hh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with rfl | rfl
        · exact hw1
        · exact hw2)), ?_, ?_⟩
  · exact FvarsOk.app_intro
      (FvarsOk.app_intro
        (FvarsOk.app_intro (FvarsOk.app_intro hpF hxF) hyF)
        (FvarsOk.fvar_intro (by omega) h1A h1i hpt1 h1F))
      (FvarsOk.fvar_intro (by omega) h2A h2i hpt2 h2F)
  · simp [divModCertApplied, Expr.looseBVarsBounded, hpb, h1B, h2B]
  · exact LeavesBounded.app_intro
      (LeavesBounded.app_intro
        (LeavesBounded.app_intro (LeavesBounded.app_intro hpL hxL) hyL)
        (LeavesBounded.fvar_intro h1B h1L))
      (LeavesBounded.fvar_intro h2B h2L)

/-- Frame facts for a one-hypothesis certificate. -/
theorem applied_facts1 (m : EnvModel V env) {proofS h1 : Expr} {H1 : V}
    (hpf : proofS.hasFvar = false)
    (hpb : proofS.looseBVarsBounded 0 = true)
    (hs : natLitSupported env = true)
    (hnat0 : ρ 0 ∈ˢ m.val natName ψ) (hnat1 : ρ 1 ∈ˢ m.val natName ψ)
    (hs1 : EqSideOk env m.val ψ 4 ρ h1 H1 (univ 0)) (hpt1 : ρ 2 ∈ˢ H1)
    (hw1 : h1.wscopedB 2 = true) :
    FvarsOk V m.val env ψ 4 ρ (divModCertApplied proofS [h1]) ∧
    WScoped 4 (divModCertApplied proofS [h1]) ∧
    (divModCertApplied proofS [h1]).looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded (divModCertApplied proofS [h1]) := by
  obtain ⟨h1i, -, h1A, h1F, -, h1B, h1L⟩ := hs1
  obtain ⟨hxF, hxL⟩ := natFvar_facts (n := .str .anonymous "x") m hs
    (by omega) hnat0
  obtain ⟨hyF, hyL⟩ := natFvar_facts (n := .str .anonymous "y") m hs
    (by omega) hnat1
  have hpF : FvarsOk V m.val env ψ 4 ρ proofS :=
    FvarsOk.of_not_hasFvar hpf
  have hpL : Expr.LeavesBounded proofS :=
    Expr.LeavesBounded.of_not_hasFvar hpf
  refine ⟨?_, WScoped.of_wscopedB
      (divModCertApplied_wscopedB hpf (by
        intro hyp hh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with rfl
        exact hw1)), ?_, ?_⟩
  · exact FvarsOk.app_intro
      (FvarsOk.app_intro (FvarsOk.app_intro hpF hxF) hyF)
      (FvarsOk.fvar_intro (by omega) h1A h1i hpt1 h1F)
  · simp [divModCertApplied, Expr.looseBVarsBounded, hpb, h1B]
  · exact LeavesBounded.app_intro
      (LeavesBounded.app_intro (LeavesBounded.app_intro hpL hxL) hyL)
      (LeavesBounded.fvar_intro h1B h1L)

end AppliedFacts


/-! ## Inversion of the fueled certificate run -/

/-- Pairwise facts over the certificate statement/proof lists. -/
inductive CertRuns (P : (List Expr × Expr) → Expr → Prop) :
    List (List Expr × Expr) → List Expr → Prop
  | nil : CertRuns P [] []
  | cons {st : List Expr × Expr} {proof : Expr}
      {srest : List (List Expr × Expr)} {prest : List Expr} :
      P st proof → CertRuns P srest prest →
      CertRuns P (st :: srest) (proof :: prest)

/-- The per-certificate content of a successful run. -/
def CertRunFacts (env : Env) (F : Nat) (c : Name) (annVal : Expr)
    (st : List Expr × Expr) (proof : Expr) : Prop :=
  divModCertGuard env c annVal st.1 st.2 proof = true ∧
  ∃ appliedA tp,
    annotateCore env F 4 (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))) = .ok appliedA ∧
    inferTypeCore env F 4 appliedA = .ok tp ∧
    isDefEqCore env F 4 tp (Expr.substConst0 c annVal st.2) = .ok true

/-- Unpack a successful `checkDivModCerts` run, per certificate. -/
theorem checkDivModCerts_inv {env : Env} {F : Nat} {c : Name}
    {annVal : Expr} :
    ∀ {stmts : List (List Expr × Expr)} {proofs : List Expr},
      checkDivModCerts (fueledOps F) env c annVal stmts proofs = .ok true →
      CertRuns (CertRunFacts env F c annVal) stmts proofs
  | [], [], _ => CertRuns.nil
  | [], _ :: _, h => by
    simp [checkDivModCerts, pure, Except.pure] at h
  | _ :: _, [], h => by
    simp [checkDivModCerts, pure, Except.pure] at h
  | (hyps, eqE) :: srest, proof :: prest, h => by
    simp only [checkDivModCerts, fueledOps_annotate, fueledOps_inferType,
      fueledOps_isDefEq, Bind.bind, Except.bind] at h
    revert h
    split
    case isFalse => intro h; simp [pure, Except.pure] at h
    case isTrue hg =>
      cases hann : annotateCore env F 4 (divModCertApplied
          (Expr.substConstAll c annVal proof)
          (hyps.map (Expr.substConst0 c annVal))) with
      | error e => intro h; exact nomatch h
      | ok appliedA =>
        intro h
        dsimp only at h
        revert h
        cases hinf : inferTypeCore env F 4 appliedA with
        | error e => intro h; exact nomatch h
        | ok tp =>
          intro h
          dsimp only at h
          revert h
          cases hde : isDefEqCore env F 4 tp
              (Expr.substConst0 c annVal eqE) with
          | error e => intro h; exact nomatch h
          | ok b =>
            cases b with
            | false => intro h; simp [pure, Except.pure] at h
            | true =>
              intro h
              simp only [↓reduceIte] at h
              exact CertRuns.cons ⟨hg, appliedA, tp, hann, hinf, hde⟩
                (checkDivModCerts_inv h)


/-! ## Clause extraction: run facts to the value equation -/

section Clauses

variable (m : EnvModel V env)

/-- The frame's `Nat` variables as equation sides. -/
private theorem fvSide (hs : natLitSupported env = true) {x y : V}
    {idx : Nat} {nm : Name} (hidx : idx < 4)
    (hval : rho4 x y idx ∈ˢ m.val natName ψ) :
    EqSideOk env m.val ψ 4 (rho4 x y)
      (.fvar idx nm (.const natName [])) (rho4 x y idx)
      (m.val natName ψ) :=
  eqSide_fvar m hs hidx hval

/-- Two-hypothesis clause: a successful run identifies the applied
operation's value with the right-hand side's. -/
private theorem clause_extract2 (F : Nat)
    (hs : natLitSupported env = true)
    (hEqA : env.find? eqName = some eqA)
    {ciN : ConstantInfo} (hNf : env.find? natName = some ciN)
    (hNlp : ciN.toConstantVal.levelParams = [])
    {value' : Expr} (hvf : value'.hasFvar = false)
    (hvb : value'.looseBVarsBounded 0 = true)
    (hAv : AnnotOk V m.val env ψ 0 (rho0 V) value')
    {hv : V} (hvi : interpClosed V m.val env ψ value' = some hv)
    (hHm : hv ∈ˢ pi 1 (m.val natName ψ)
      (fun _ => pi 1 (m.val natName ψ) (fun _ => m.val natName ψ)))
    {x y : V} (hx : x ∈ˢ m.val natName ψ) (hy : y ∈ˢ m.val natName ψ)
    {h1E h2E : Expr} {H1 H2 : V}
    (hs1 : EqSideOk env m.val ψ 4 (rho4 x y) h1E H1 (univ 0))
    (hpt1 : (pt : V) ∈ˢ H1)
    (hs2 : EqSideOk env m.val ψ 4 (rho4 x y) h2E H2 (univ 0))
    (hpt2 : (pt : V) ∈ˢ H2)
    (hw1 : h1E.wscopedB 2 = true) (hw2 : h2E.wscopedB 2 = true)
    {rhsE : Expr} {vr : V}
    (hrhs : EqSideOk env m.val ψ 4 (rho4 x y) rhsE vr (m.val natName ψ))
    {proofS : Expr} (hpf : proofS.hasFvar = false)
    (hpb : proofS.looseBVarsBounded 0 = true)
    {appliedA tp : Expr}
    (hann : annotateCore env F 4 (divModCertApplied proofS [h1E, h2E]) =
      .ok appliedA)
    (hinf : inferTypeCore env F 4 appliedA = .ok tp)
    (hde : isDefEqCore env F 4 tp
      (.app (.app (.app (.const eqName [.succ .zero]) (.const natName []))
        (.app (.app value'
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.fvar 1 (.str .anonymous "y") (.const natName []))))
        rhsE) = .ok true) :
    SetTheory.app (SetTheory.app hv x) y = vr := by
  have hfx := fvSide m hs (idx := 0) (nm := .str .anonymous "x")
    (x := x) (y := y) (by omega) (by rw [rho4_0]; exact hx)
  have hfy := fvSide m hs (idx := 1) (nm := .str .anonymous "y")
    (x := x) (y := y) (by omega) (by rw [rho4_1]; exact hy)
  rw [rho4_0] at hfx
  rw [rho4_1] at hfy
  have hHi4 : interpExpr V m.val env ψ 4 (rho4 x y) value' = some hv :=
    (interp_closed_invariant hvf 4 _).trans hvi
  have hlhs := eqSide_app2 m hs hHi4
    (AnnotOk.closed_invariant hvf 4 _ hAv)
    (FvarsOk.of_not_hasFvar hvf) (WScoped.of_not_hasFvar hvf) hvb
    (Expr.LeavesBounded.of_not_hasFvar hvf) hHm
    (natVal_mem_univ m hs ψ) hfx hfy
  have heqS := eqSide_eqApp m hEqA hNf hNlp (natVal_mem_univ m hs ψ)
    hlhs hrhs
  obtain ⟨hF, hW, hB, hL⟩ := applied_facts2 m hpf hpb hs
    (by rw [rho4_0]; exact hx) (by rw [rho4_1]; exact hy)
    hs1 (by rw [rho4_2]; exact hpt1) hs2 (by rw [rho4_3]; exact hpt2)
    hw1 hw2
  obtain ⟨w, hw⟩ := divModCert_extract m F hF hW hB hL heqS hann hinf hde
  exact mem_eqv hw

/-- One-hypothesis clause. -/
private theorem clause_extract1 (F : Nat)
    (hs : natLitSupported env = true)
    (hEqA : env.find? eqName = some eqA)
    {ciN : ConstantInfo} (hNf : env.find? natName = some ciN)
    (hNlp : ciN.toConstantVal.levelParams = [])
    {value' : Expr} (hvf : value'.hasFvar = false)
    (hvb : value'.looseBVarsBounded 0 = true)
    (hAv : AnnotOk V m.val env ψ 0 (rho0 V) value')
    {hv : V} (hvi : interpClosed V m.val env ψ value' = some hv)
    (hHm : hv ∈ˢ pi 1 (m.val natName ψ)
      (fun _ => pi 1 (m.val natName ψ) (fun _ => m.val natName ψ)))
    {x y : V} (hx : x ∈ˢ m.val natName ψ) (hy : y ∈ˢ m.val natName ψ)
    {h1E : Expr} {H1 : V}
    (hs1 : EqSideOk env m.val ψ 4 (rho4 x y) h1E H1 (univ 0))
    (hpt1 : (pt : V) ∈ˢ H1)
    (hw1 : h1E.wscopedB 2 = true)
    {rhsE : Expr} {vr : V}
    (hrhs : EqSideOk env m.val ψ 4 (rho4 x y) rhsE vr (m.val natName ψ))
    {proofS : Expr} (hpf : proofS.hasFvar = false)
    (hpb : proofS.looseBVarsBounded 0 = true)
    {appliedA tp : Expr}
    (hann : annotateCore env F 4 (divModCertApplied proofS [h1E]) =
      .ok appliedA)
    (hinf : inferTypeCore env F 4 appliedA = .ok tp)
    (hde : isDefEqCore env F 4 tp
      (.app (.app (.app (.const eqName [.succ .zero]) (.const natName []))
        (.app (.app value'
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.fvar 1 (.str .anonymous "y") (.const natName []))))
        rhsE) = .ok true) :
    SetTheory.app (SetTheory.app hv x) y = vr := by
  have hfx := fvSide m hs (idx := 0) (nm := .str .anonymous "x")
    (x := x) (y := y) (by omega) (by rw [rho4_0]; exact hx)
  have hfy := fvSide m hs (idx := 1) (nm := .str .anonymous "y")
    (x := x) (y := y) (by omega) (by rw [rho4_1]; exact hy)
  rw [rho4_0] at hfx
  rw [rho4_1] at hfy
  have hHi4 : interpExpr V m.val env ψ 4 (rho4 x y) value' = some hv :=
    (interp_closed_invariant hvf 4 _).trans hvi
  have hlhs := eqSide_app2 m hs hHi4
    (AnnotOk.closed_invariant hvf 4 _ hAv)
    (FvarsOk.of_not_hasFvar hvf) (WScoped.of_not_hasFvar hvf) hvb
    (Expr.LeavesBounded.of_not_hasFvar hvf) hHm
    (natVal_mem_univ m hs ψ) hfx hfy
  have heqS := eqSide_eqApp m hEqA hNf hNlp (natVal_mem_univ m hs ψ)
    hlhs hrhs
  obtain ⟨hF, hW, hB, hL⟩ := applied_facts1 m hpf hpb hs
    (by rw [rho4_0]; exact hx) (by rw [rho4_1]; exact hy)
    hs1 (by rw [rho4_2]; exact hpt1) hw1
  obtain ⟨w, hw⟩ := divModCert_extract m F hF hW hB hL heqS hann hinf hde
  exact mem_eqv hw

end Clauses


/-! ## The certificates' semantic content: `DivModEqs` -/

/-- `natOpStoredOk`, split. -/
theorem natOpStoredOk_tyPinned {n : Name}
    (h : natOpStoredOk env n = true) :
    ∃ cv v hint, env.find? n = some (.defnInfo cv v hint) ∧
      natOpTyPinned env n cv.type = true := by
  unfold natOpStoredOk at h
  revert h
  split
  · next cv v hint heq =>
    intro h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨cv, v, hint, heq, h.2⟩
  · intro h; exact nomatch h

set_option maxHeartbeats 1600000 in
/-- The checked certificates make the stored operation satisfy its
`ble`-guarded value-level recurrences, for any valuation that maps the
operation to the stored value's interpretation and agrees with the
model elsewhere — the head obligation `extend_model` forwards into
`DivModOk`. -/
theorem divmod_certs_sound (m : EnvModel V env) (F : Nat)
    {c : Name} (hc : c ∈ natDivModNames)
    {value' : Expr}
    (hvf : value'.hasFvar = false)
    (hvb : value'.looseBVarsBounded 0 = true)
    (hAval : ∀ ψ' : Name → Nat, AnnotOk V m.val env ψ' 0 (rho0 V) value')
    (hs : natLitSupported env = true)
    (hEqA : env.find? eqName = some eqA)
    (hble : natOpStoredOk env natBleName = true)
    (hsub : natOpStoredOk env natSubName = true)
    (hbT : ∃ ci, env.find? boolTrueName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type = .const boolName [])
    (hbF : ∃ ci, env.find? boolFalseName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type = .const boolName [])
    (hHm : ∀ ψ' : Name → Nat, ∃ hv,
      interpClosed V m.val env ψ' value' = some hv ∧
      hv ∈ˢ pi 1 (m.val natName ψ') (fun _ => pi 1 (m.val natName ψ')
        (fun _ => m.val natName ψ')))
    (hruns : CertRuns (CertRunFacts env F c value')
      (divModCertStmts c) (divModCertProofs c)) :
    ∀ val' : ConstVal V,
      (∀ ψ' : Name → Nat, interpClosed V m.val env ψ' value' =
        some (val' c ψ')) →
      (∀ n, n ≠ c → ∀ ψ' : Name → Nat, val' n ψ' = m.val n ψ') →
      DivModEqs V val' c := by
  intro val' hval'c hval'ne
  -- name disequalities: everything the equations mention is not `c`
  have hne : natName ≠ c ∧ natZeroName ≠ c ∧ natSuccName ≠ c ∧
      natBleName ≠ c ∧ natSubName ≠ c ∧ boolTrueName ≠ c ∧
      boolFalseName ≠ c := by
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl <;>
      exact ⟨by decide, by decide, by decide, by decide, by decide,
        by decide, by decide⟩
  intro ψ0 x y hx hy
  -- move the frame memberships to the model's valuation
  rw [hval'ne natName hne.1 ψ0] at hx hy
  -- the stored value's interpretation is `val' c`
  obtain ⟨hv, hvi, hvPi⟩ := hHm ψ0
  have hveq : val' c ψ0 = hv := by
    have h1 := hval'c ψ0
    rw [hvi] at h1
    exact (Option.some.inj h1).symm
  -- `ble`/`sub`/`Bool` facts at `ψ0`
  obtain ⟨cvbl, vbl, hintbl, hfbl, hlpbl, -, hbleFn⟩ :=
    natOpStored_facts m hble hs ψ0
  obtain ⟨Cb, hblePi, hCbu, -, hCbBool⟩ := hbleFn (by decide)
  rw [hCbBool (Or.inr rfl)] at hblePi
  have hBu : m.val boolName ψ0 ∈ˢ (univ 1 : V) := by
    rw [← hCbBool (Or.inr rfl)]
    exact hCbu
  obtain ⟨cvsu, vsu, hintsu, hfsu, hlpsu, -, hsubFn⟩ :=
    natOpStored_facts m hsub hs ψ0
  obtain ⟨Cs, hsubPi, -, hCsid, -⟩ := hsubFn (by decide)
  rw [hCsid (by decide) (by decide)] at hsubPi
  obtain ⟨cvbl', vbl', hintbl', hfbl', htybl'⟩ := natOpStoredOk_tyPinned hble
  obtain ⟨ciB, hBf, hBlp, -⟩ := natOpTyPinned_boolFacts (by
    rw [show cvbl' = cvbl from by
      rw [hfbl] at hfbl'
      exact (ConstantInfo.defnInfo.injEq .. ▸ Option.some.inj hfbl').1.symm]
      at htybl'
    exact htybl')
  obtain ⟨ciT, hTf, hTlp, hTty⟩ := hbT
  obtain ⟨ciF, hFf, hFlp, hFty⟩ := hbF
  obtain ⟨cvN, capsN, cv0, i0, j0, cv1, i1, j1, hnn, hzz, hss, hlN, -⟩ :=
    natLitSupported_inv hs
  -- frame variable sides
  have hfx := fvSide m hs (idx := 0) (nm := .str .anonymous "x")
    (x := x) (y := y) (by omega) (by rw [rho4_0]; exact hx)
  have hfy := fvSide m hs (idx := 1) (nm := .str .anonymous "y")
    (x := x) (y := y) (by omega) (by rw [rho4_1]; exact hy)
  rw [rho4_0] at hfx
  rw [rho4_1] at hfy
  -- `Bool`-side components
  have htrueSide : EqSideOk env m.val ψ0 4 (rho4 x y)
      (.const boolTrueName []) (m.val boolTrueName ψ0)
      (m.val boolName ψ0) :=
    eqSide_boolCtor m hTf hTlp hTty hBf hBlp
  have hfalseSide : EqSideOk env m.val ψ0 4 (rho4 x y)
      (.const boolFalseName []) (m.val boolFalseName ψ0)
      (m.val boolName ψ0) :=
    eqSide_boolCtor m hFf hFlp hFty hBf hBlp
  have hbleYX : EqSideOk env m.val ψ0 4 (rho4 x y)
      (.app (.app (.const natBleName [])
        (.fvar 1 (.str .anonymous "y") (.const natName [])))
        (.fvar 0 (.str .anonymous "x") (.const natName [])))
      (SetTheory.app (SetTheory.app (m.val natBleName ψ0) y) x)
      (m.val boolName ψ0) :=
    eqSide_app2c m hs hfbl hlpbl hblePi hBu hfy hfx
  have hone : EqSideOk env m.val ψ0 4 (rho4 x y)
      (.app (.const natSuccName []) (.const natZeroName []))
      (SetTheory.app (m.val natSuccName ψ0) (m.val natZeroName ψ0))
      (m.val natName ψ0) :=
    eqSide_succ m hs (eqSide_zero m hs)
  have hble1Y : EqSideOk env m.val ψ0 4 (rho4 x y)
      (.app (.app (.const natBleName [])
        (.app (.const natSuccName []) (.const natZeroName [])))
        (.fvar 1 (.str .anonymous "y") (.const natName [])))
      (SetTheory.app (SetTheory.app (m.val natBleName ψ0)
        (SetTheory.app (m.val natSuccName ψ0) (m.val natZeroName ψ0))) y)
      (m.val boolName ψ0) :=
    eqSide_app2c m hs hfbl hlpbl hblePi hBu hone hfy
  -- the hypothesis types, assembled
  have hyp1T := eqSide_eqApp m hEqA hBf hBlp hBu hbleYX htrueSide
  have hyp1F := eqSide_eqApp m hEqA hBf hBlp hBu hbleYX hfalseSide
  have hyp2T := eqSide_eqApp m hEqA hBf hBlp hBu hble1Y htrueSide
  have hyp2F := eqSide_eqApp m hEqA hBf hBlp hBu hble1Y hfalseSide
  -- scoping of the hypothesis types (kernel-computed)
  have hwYXT : (Expr.app (.app (.app (.const eqName [.succ .zero])
      (.const boolName []))
      (.app (.app (.const natBleName [])
        (.fvar 1 (.str .anonymous "y") (.const natName [])))
        (.fvar 0 (.str .anonymous "x") (.const natName []))))
      (.const boolTrueName [])).wscopedB 2 = true := by decide +kernel
  have hwYXF : (Expr.app (.app (.app (.const eqName [.succ .zero])
      (.const boolName []))
      (.app (.app (.const natBleName [])
        (.fvar 1 (.str .anonymous "y") (.const natName [])))
        (.fvar 0 (.str .anonymous "x") (.const natName []))))
      (.const boolFalseName [])).wscopedB 2 = true := by decide +kernel
  have hw1YT : (Expr.app (.app (.app (.const eqName [.succ .zero])
      (.const boolName []))
      (.app (.app (.const natBleName [])
        (.app (.const natSuccName []) (.const natZeroName [])))
        (.fvar 1 (.str .anonymous "y") (.const natName []))))
      (.const boolTrueName [])).wscopedB 2 = true := by decide +kernel
  have hw1YF : (Expr.app (.app (.app (.const eqName [.succ .zero])
      (.const boolName []))
      (.app (.app (.const natBleName [])
        (.app (.const natSuccName []) (.const natZeroName [])))
        (.fvar 1 (.str .anonymous "y") (.const natName []))))
      (.const boolFalseName [])).wscopedB 2 = true := by decide +kernel
  -- the stored value's facts at frame depth
  have hNatU := natVal_mem_univ m hs ψ0
  have hsubXY : EqSideOk env m.val ψ0 4 (rho4 x y)
      (.app (.app (.const natSubName [])
        (.fvar 0 (.str .anonymous "x") (.const natName [])))
        (.fvar 1 (.str .anonymous "y") (.const natName [])))
      (SetTheory.app (SetTheory.app (m.val natSubName ψ0) x) y)
      (m.val natName ψ0) :=
    eqSide_app2c m hs hfsu hlpsu hsubPi hNatU hfx hfy
  have hHi4 : interpExpr V m.val env ψ0 4 (rho4 x y) value' = some hv :=
    (interp_closed_invariant hvf 4 _).trans hvi
  have hHA4 := AnnotOk.closed_invariant hvf 4 (rho4 x y) (hAval ψ0)
  have hHF4 : FvarsOk V m.val env ψ0 4 (rho4 x y) value' :=
    FvarsOk.of_not_hasFvar hvf
  have hHW4 : WScoped 4 value' := WScoped.of_not_hasFvar hvf
  have hHL4 : Expr.LeavesBounded value' :=
    Expr.LeavesBounded.of_not_hasFvar hvf
  have hopSub : EqSideOk env m.val ψ0 4 (rho4 x y)
      (.app (.app value'
        (.app (.app (.const natSubName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.fvar 1 (.str .anonymous "y") (.const natName []))))
        (.fvar 1 (.str .anonymous "y") (.const natName [])))
      (SetTheory.app (SetTheory.app hv
        (SetTheory.app (SetTheory.app (m.val natSubName ψ0) x) y)) y)
      (m.val natName ψ0) :=
    eqSide_app2 m hs hHi4 hHA4 hHF4 hHW4 hvb hHL4 hvPi hNatU hsubXY hfy
  have hNlp' : (ConstantInfo.indInfo cvN capsN).toConstantVal.levelParams
      = [] := hlN
  -- split on the operation: the pinned statement lists become concrete
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl
  case inl =>
    -- Nat.div
    simp +decide only [divModCertStmts, divModCertProofs,
      natDivCertProofs] at hruns
    rcases hruns with _ | ⟨hcert1, _ | ⟨hcert2, _ | ⟨hcert3, _⟩⟩⟩
    obtain ⟨hg1, appliedA1, tp1, hann1, hinf1, hde1⟩ := hcert1
    obtain ⟨hg2, appliedA2, tp2, hann2, hinf2, hde2⟩ := hcert2
    obtain ⟨hg3, appliedA3, tp3, hann3, hinf3, hde3⟩ := hcert3
    simp +decide only [Expr.substConst0, List.map] at hann1 hann2 hann3
    simp +decide only [Expr.substConst0, List.map] at hde1 hde2 hde3
    unfold divModCertGuard at hg1 hg2 hg3
    simp only [Bool.and_eq_true] at hg1 hg2 hg3
    have hpf1 : (Expr.substConstAll natDivName value'
        divRecProof).hasFvar = false := by simpa using hg1.1.1.1.1.2
    have hpb1 := hg1.1.1.1.1.1
    have hpf2 : (Expr.substConstAll natDivName value'
        divBaseGtProof).hasFvar = false := by simpa using hg2.1.1.1.1.2
    have hpb2 := hg2.1.1.1.1.1
    have hpf3 : (Expr.substConstAll natDivName value'
        divBaseZeroProof).hasFvar = false := by simpa using hg3.1.1.1.1.2
    have hpb3 := hg3.1.1.1.1.1
    refine ⟨?_, ?_, ?_⟩
    · -- the recurrence clause
      intro hgv1 hgv2
      rw [hval'ne natBleName hne.2.2.2.1 ψ0,
        hval'ne boolTrueName hne.2.2.2.2.2.1 ψ0] at hgv1
      rw [hval'ne natBleName hne.2.2.2.1 ψ0,
        hval'ne natSuccName hne.2.2.1 ψ0,
        hval'ne natZeroName hne.2.1 ψ0,
        hval'ne boolTrueName hne.2.2.2.2.2.1 ψ0] at hgv2
      have hpt1 : (pt : V) ∈ˢ eqv (SetTheory.app (SetTheory.app
          (m.val natBleName ψ0) y) x) (m.val boolTrueName ψ0) := by
        rw [hgv1]
        exact pt_mem_eqv_self _
      have hpt2 : (pt : V) ∈ˢ eqv (SetTheory.app (SetTheory.app
          (m.val natBleName ψ0) (SetTheory.app (m.val natSuccName ψ0)
            (m.val natZeroName ψ0))) y) (m.val boolTrueName ψ0) := by
        rw [hgv2]
        exact pt_mem_eqv_self _
      have hrhs : EqSideOk env m.val ψ0 4 (rho4 x y)
          (.app (.const natSuccName [])
            (.app (.app value'
              (.app (.app (.const natSubName [])
                (.fvar 0 (.str .anonymous "x") (.const natName [])))
                (.fvar 1 (.str .anonymous "y") (.const natName []))))
              (.fvar 1 (.str .anonymous "y") (.const natName []))))
          (SetTheory.app (m.val natSuccName ψ0)
            (SetTheory.app (SetTheory.app hv
              (SetTheory.app (SetTheory.app (m.val natSubName ψ0) x) y))
              y))
          (m.val natName ψ0) := eqSide_succ m hs hopSub
      have heq := clause_extract2 m F hs hEqA hnn hNlp' hvf hvb
        (hAval ψ0) hvi hvPi hx hy hyp1T hpt1 hyp2T hpt2 hwYXT hw1YT
        hrhs hpf1 hpb1 hann1 hinf1 hde1
      rw [if_pos rfl, hveq, hval'ne natSuccName hne.2.2.1 ψ0,
        hval'ne natSubName hne.2.2.2.2.1 ψ0]
      exact heq
    · -- base: `ble y x = false`
      intro hgv1
      rw [hval'ne natBleName hne.2.2.2.1 ψ0,
        hval'ne boolFalseName hne.2.2.2.2.2.2 ψ0] at hgv1
      have hpt1 : (pt : V) ∈ˢ eqv (SetTheory.app (SetTheory.app
          (m.val natBleName ψ0) y) x) (m.val boolFalseName ψ0) := by
        rw [hgv1]
        exact pt_mem_eqv_self _
      have hrhs : EqSideOk env m.val ψ0 4 (rho4 x y)
          (.const natZeroName []) (m.val natZeroName ψ0)
          (m.val natName ψ0) := eqSide_zero m hs
      have heq := clause_extract1 m F hs hEqA hnn hNlp' hvf hvb
        (hAval ψ0) hvi hvPi hx hy hyp1F hpt1 hwYXF
        hrhs hpf2 hpb2 hann2 hinf2 hde2
      rw [if_pos rfl, hveq, hval'ne natZeroName hne.2.1 ψ0]
      exact heq
    · -- base: `ble 1 y = false`
      intro hgv1
      rw [hval'ne natBleName hne.2.2.2.1 ψ0,
        hval'ne natSuccName hne.2.2.1 ψ0,
        hval'ne natZeroName hne.2.1 ψ0,
        hval'ne boolFalseName hne.2.2.2.2.2.2 ψ0] at hgv1
      have hpt1 : (pt : V) ∈ˢ eqv (SetTheory.app (SetTheory.app
          (m.val natBleName ψ0) (SetTheory.app (m.val natSuccName ψ0)
            (m.val natZeroName ψ0))) y) (m.val boolFalseName ψ0) := by
        rw [hgv1]
        exact pt_mem_eqv_self _
      have hrhs : EqSideOk env m.val ψ0 4 (rho4 x y)
          (.const natZeroName []) (m.val natZeroName ψ0)
          (m.val natName ψ0) := eqSide_zero m hs
      have heq := clause_extract1 m F hs hEqA hnn hNlp' hvf hvb
        (hAval ψ0) hvi hvPi hx hy hyp2F hpt1 hw1YF
        hrhs hpf3 hpb3 hann3 hinf3 hde3
      rw [if_pos rfl, hveq, hval'ne natZeroName hne.2.1 ψ0]
      exact heq
  case inr =>
    -- Nat.mod
    simp +decide only [divModCertStmts, divModCertProofs,
      natModCertProofs] at hruns
    rcases hruns with _ | ⟨hcert1, _ | ⟨hcert2, _ | ⟨hcert3, _⟩⟩⟩
    obtain ⟨hg1, appliedA1, tp1, hann1, hinf1, hde1⟩ := hcert1
    obtain ⟨hg2, appliedA2, tp2, hann2, hinf2, hde2⟩ := hcert2
    obtain ⟨hg3, appliedA3, tp3, hann3, hinf3, hde3⟩ := hcert3
    simp +decide only [Expr.substConst0, List.map] at hann1 hann2 hann3
    simp +decide only [Expr.substConst0, List.map] at hde1 hde2 hde3
    unfold divModCertGuard at hg1 hg2 hg3
    simp only [Bool.and_eq_true] at hg1 hg2 hg3
    have hpf1 : (Expr.substConstAll natModName value'
        modRecProof).hasFvar = false := by simpa using hg1.1.1.1.1.2
    have hpb1 := hg1.1.1.1.1.1
    have hpf2 : (Expr.substConstAll natModName value'
        modBaseGtProof).hasFvar = false := by simpa using hg2.1.1.1.1.2
    have hpb2 := hg2.1.1.1.1.1
    have hpf3 : (Expr.substConstAll natModName value'
        modBaseZeroProof).hasFvar = false := by simpa using hg3.1.1.1.1.2
    have hpb3 := hg3.1.1.1.1.1
    refine ⟨?_, ?_, ?_⟩
    · -- the recurrence clause
      intro hgv1 hgv2
      rw [hval'ne natBleName hne.2.2.2.1 ψ0,
        hval'ne boolTrueName hne.2.2.2.2.2.1 ψ0] at hgv1
      rw [hval'ne natBleName hne.2.2.2.1 ψ0,
        hval'ne natSuccName hne.2.2.1 ψ0,
        hval'ne natZeroName hne.2.1 ψ0,
        hval'ne boolTrueName hne.2.2.2.2.2.1 ψ0] at hgv2
      have hpt1 : (pt : V) ∈ˢ eqv (SetTheory.app (SetTheory.app
          (m.val natBleName ψ0) y) x) (m.val boolTrueName ψ0) := by
        rw [hgv1]
        exact pt_mem_eqv_self _
      have hpt2 : (pt : V) ∈ˢ eqv (SetTheory.app (SetTheory.app
          (m.val natBleName ψ0) (SetTheory.app (m.val natSuccName ψ0)
            (m.val natZeroName ψ0))) y) (m.val boolTrueName ψ0) := by
        rw [hgv2]
        exact pt_mem_eqv_self _
      have heq := clause_extract2 m F hs hEqA hnn hNlp' hvf hvb
        (hAval ψ0) hvi hvPi hx hy hyp1T hpt1 hyp2T hpt2 hwYXT hw1YT
        hopSub hpf1 hpb1 hann1 hinf1 hde1
      rw [if_neg (by decide), hveq,
        hval'ne natSubName hne.2.2.2.2.1 ψ0]
      exact heq
    · -- base: `ble y x = false`
      intro hgv1
      rw [hval'ne natBleName hne.2.2.2.1 ψ0,
        hval'ne boolFalseName hne.2.2.2.2.2.2 ψ0] at hgv1
      have hpt1 : (pt : V) ∈ˢ eqv (SetTheory.app (SetTheory.app
          (m.val natBleName ψ0) y) x) (m.val boolFalseName ψ0) := by
        rw [hgv1]
        exact pt_mem_eqv_self _
      have heq := clause_extract1 m F hs hEqA hnn hNlp' hvf hvb
        (hAval ψ0) hvi hvPi hx hy hyp1F hpt1 hwYXF
        hfx hpf2 hpb2 hann2 hinf2 hde2
      rw [if_neg (by decide), hveq]
      exact heq
    · -- base: `ble 1 y = false`
      intro hgv1
      rw [hval'ne natBleName hne.2.2.2.1 ψ0,
        hval'ne natSuccName hne.2.2.1 ψ0,
        hval'ne natZeroName hne.2.1 ψ0,
        hval'ne boolFalseName hne.2.2.2.2.2.2 ψ0] at hgv1
      have hpt1 : (pt : V) ∈ˢ eqv (SetTheory.app (SetTheory.app
          (m.val natBleName ψ0) (SetTheory.app (m.val natSuccName ψ0)
            (m.val natZeroName ψ0))) y) (m.val boolFalseName ψ0) := by
        rw [hgv1]
        exact pt_mem_eqv_self _
      have heq := clause_extract1 m F hs hEqA hnn hNlp' hvf hvb
        (hAval ψ0) hvi hvPi hx hy hyp2F hpt1 hw1YF
        hfx hpf3 hpb3 hann3 hinf3 hde3
      rw [if_neg (by decide), hveq]
      exact heq


/-! ## Inversion of the fueled pin-gate run -/

/-- Unpack a successful `checkDivModPin` run. -/
theorem checkDivModPin_inv {env env2 : Env} {F : Nat} {c : Name} {u : Unit}
    (h : checkDivModPin (fueledOps F) env env2 c = .ok u) :
    divModEnvGuard env2 c = true ∧
    ∃ cv' value' hint',
      env2.find? c = some (.defnInfo cv' value' hint') ∧
      (divModPinGuard env c && divModCertsGuard env c value') = true ∧
      (∃ pinA, annotateCore env F 0 (divModDeclPin c) = .ok pinA ∧
        isDefEqCore env F 0 value' pinA = .ok true) ∧
      checkDivModCerts (fueledOps F) env c value'
        (divModCertStmts c) (divModCertProofs c) = .ok true := by
  unfold checkDivModPin at h
  revert h
  split
  case isFalse => intro h; exact nomatch h
  case isTrue hg =>
    refine fun h => ⟨hg, ?_⟩
    revert h
    cases hfind : env2.find? c with
    | none => intro h; exact nomatch h
    | some ci =>
      cases ci with
      | axiomInfo cv' => intro h; exact nomatch h
      | thmInfo cv' v' => intro h; exact nomatch h
      | indInfo cv' caps => intro h; exact nomatch h
      | ctorInfo cv' nP nF => intro h; exact nomatch h
      | recInfo cv' mI rP rules => intro h; exact nomatch h
      | projInfo _ => intro h; exact nomatch h
      | defnInfo cv' value' hint' =>
        dsimp only
        split
        case isFalse => intro h; exact nomatch h
        case isTrue hping =>
          simp only [fueledOps_annotate, fueledOps_isDefEq, Bind.bind,
            Except.bind]
          cases hann : annotateCore env F 0 (divModDeclPin c) with
          | error e => intro h; exact nomatch h
          | ok pinA =>
            intro h
            dsimp only at h
            revert h
            cases hde : isDefEqCore env F 0 value' pinA with
            | error e => intro h; exact nomatch h
            | ok b =>
              cases b with
              | false => intro h; simp [throw, throwThe,
                  MonadExceptOf.throw] at h
              | true =>
                intro h
                simp only [↓reduceIte] at h
                revert h
                cases hcert : checkDivModCerts (fueledOps F) env c value'
                    (divModCertStmts c) (divModCertProofs c) with
                | error e => intro h; exact nomatch h
                | ok ok =>
                  cases ok with
                  | false => intro h; simp [throw, throwThe,
                      MonadExceptOf.throw] at h
                  | true =>
                    intro h
                    exact ⟨cv', value', hint', rfl, hping,
                      ⟨pinA, rfl, hde⟩, hcert⟩


/-- The pin names are distinct from every constant the install path
transports (the `Nat`/`Bool` pins, the pinned equality, and the
already-certified dependencies). -/
theorem natDivModNames_ne_env {c : Name} (hc : c ∈ natDivModNames) :
    c ≠ natName ∧ c ≠ natZeroName ∧ c ≠ natSuccName ∧ c ≠ boolName ∧
    c ≠ boolTrueName ∧ c ≠ boolFalseName ∧ c ≠ eqName ∧
    c ≠ natBleName ∧ c ≠ natSubName ∧ c ≠ natPredName ∧
    c ≠ natBeqName := by
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `divModEnvGuard`, split into facts. -/
theorem divModEnvGuard_inv {env2 : Env} {c : Name}
    (h : divModEnvGuard env2 c = true) :
    natOpGuard env2 c = true ∧
    (natOpDeps c).all (natOpStoredOk env2) = true ∧
    env2.find? eqName = some eqA ∧
    (∃ ci, env2.find? boolTrueName = some ci ∧
      ci.toConstantVal.type = .const boolName []) ∧
    (∃ ci, env2.find? boolFalseName = some ci ∧
      ci.toConstantVal.type = .const boolName []) := by
  unfold divModEnvGuard at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hg, hdeps⟩, heq⟩, hbT⟩, hbF⟩ := h
  refine ⟨hg, hdeps, by simpa using heq, ?_, ?_⟩
  · revert hbT
    split
    · next ci hfind =>
      intro hbT
      exact ⟨ci, hfind, by simpa using hbT⟩
    · intro hbT; exact nomatch hbT
  · revert hbF
    split
    · next ci hfind =>
      intro hbF
      exact ⟨ci, hfind, by simpa using hbF⟩
    · intro hbF; exact nomatch hbF

end Setlec
