import Setlec.SetP.DirectEntryLawP

/-!
# The projection entry's cons (task #175 W4c, P3 module 7, part 6)

`stageEntry`: the P step at a tower entry's cons.  The entry's leaf is
a constant-bit λ-tower over the entry type's binder data with a
**choice body**: `Classical.choice` at the residual — the residual is
inhabited at every satisfying frame (the graph regime by the tower's
projection membership, the squash regime by the proof field at the
point prefix, or, at the first field, by the fitting chain's head),
so the leaf inhabits the entry type whatever the instantiation.  (The
projection *value* is never the leaf's business: a `.proj` node reads
as `projAV`, and the stored constant is a table entry no term
names.)  The leaf's walks are the entry frame's; the entry's law is
`entryLawP`, assembled from the three semantic cores over the frames.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta ProjEntry projFnName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The choice body -/

/-- The point witnesses a non-empty set's double negation. -/
theorem pt_mem_dnegSpace2 {A x : V} (hx : x ∈ˢ A) : (pt : V) ∈ˢ dnegSpace2 V A := by
  unfold dnegSpace2
  rw [piR_zero]
  refine pt_mem_truthVal fun f hf => ?_
  exfalso
  rw [piR_zero] at hf
  obtain ⟨hp, -⟩ := mem_truthVal.mp hf
  obtain ⟨y, hy⟩ := hp x hx
  exact not_mem_empty y hy

/-- `Classical.choice` at level `u` inhabits its type's reading. -/
theorem choiceV2_mem (u : Nat) :
    choiceV2 V u ∈ˢ piR u (univ u : V)
      (fun A => piR u (dnegSpace2 V A) fun _ => A) := by
  unfold choiceV2
  refine lamR_mem (V := V) fun A _ => ?_
  refine lamR_mem (V := V) fun h hh => ?_
  obtain ⟨x, hx⟩ := exists_mem_of_dneg2 V hh
  exact schoice_mem hx

/-- A residual's level: some universe every satisfying frame's reading
lands in (`0` if none). -/
noncomputable def resLevel (V : Type w) [SetTheory V] (Γ : List AVExpr) (R : AVExpr) : Nat :=
  Classical.epsilon fun u : Nat => ∀ ρ : Nat → V, Sat2 V Γ ρ → interp2 V ρ R ∈ˢ (univ u : V)

theorem resLevel_spec {Γ : List AVExpr} {R : AVExpr}
    (h : ∃ u : Nat, ∀ ρ : Nat → V, Sat2 V Γ ρ → interp2 V ρ R ∈ˢ (univ u : V)) :
    ∀ ρ : Nat → V, Sat2 V Γ ρ → interp2 V ρ R ∈ˢ (univ (resLevel V Γ R) : V) :=
  Classical.epsilon_spec h

/-- The entry leaf's body: choice at the residual. -/
def entryBody (u : Nat) (R : AVExpr) : AVExpr :=
  .app (.app (.const .choice [u]) R) .prf

/-- The body is graded, bit-valid and a member of the residual wherever
the residual is a non-empty set of level `u`. -/
theorem entryBody_ok {u : Nat} {R : AVExpr} {ρ : Nat → V}
    (hokR : AnnotOkP V ρ R) (hu : interp2 V ρ R ∈ˢ (univ u : V))
    (hne : ∃ y, y ∈ˢ interp2 V ρ R) :
    AnnotOk2 V ρ (entryBody u R) ∧ AnnotValidV V ρ (entryBody u R) ∧
      interp2 V ρ (entryBody u R) ∈ˢ interp2 V ρ R := by
  obtain ⟨y, hy⟩ := hne
  have hval : interp2 V ρ (entryBody u R) = schoice (interp2 V ρ R) := by
    show SetTheory.app (SetTheory.app (bval2 V .choice [u]) (interp2 V ρ R)) pt = _
    exact choiceV2_app V hu (pt_mem_dnegSpace2 hy)
  refine ⟨?_, ?_, by rw [hval]; exact schoice_mem hy⟩
  · unfold entryBody
    rw [AnnotOk2_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [AnnotOk2_app]
      refine ⟨trivial, hokR.1, u, univ u,
        fun A => piR u (dnegSpace2 V A) fun _ => A, ?_, hu, fun h0 _ _ => ?_⟩
      · show bval2 V .choice [u] ∈ˢ _
        exact choiceV2_mem u
      · subst h0
        exact piR_zero_mem_univZero
    · refine ⟨u, dnegSpace2 V (interp2 V ρ R), fun _ => interp2 V ρ R, ?_,
        by rw [interp2_prf]; exact pt_mem_dnegSpace2 hy, fun h0 _ _ => ?_⟩
      · show SetTheory.app (bval2 V .choice [u]) (interp2 V ρ R) ∈ˢ _
        by_cases hu0 : u = 0
        · subst hu0
          show SetTheory.app (choiceV2 V 0) _ ∈ˢ _
          rw [choiceV2, lamR_zero, app_pt, piR_zero]
          exact pt_mem_truthVal fun _ _ => ⟨y, hy⟩
        · show SetTheory.app (choiceV2 V u) _ ∈ˢ _
          rw [choiceV2, app_lamR_pos hu0 hu]
          exact lamR_mem fun h hh => schoice_mem hy
      · subst h0
        rw [← univ_zero]
        exact hu
  · unfold entryBody
    rw [AnnotValidV_app, AnnotValidV_app]
    exact ⟨⟨trivial, hokR.2⟩, trivial⟩

omit [SetTheory V] in
theorem entryBody_below {u : Nat} {R : AVExpr} {k : Nat} (h : VExpr.bvarsBelow k R.erase) :
    VExpr.bvarsBelow k (entryBody u R).erase :=
  ⟨⟨trivial, h⟩, trivial⟩

/-! ## The residual is inhabited -/

/-- At a squash instance under the guard, the point inhabits the field
at the point prefix. -/
theorem squash_pt_mem {nP nF i : Nat} {ds : List (Nat × Nat × AVExpr)} {sorts : List Level}
    {ψ : Name → Nat} {ρ' : Nat → V}
    (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hsorts : ∀ j, j < nF → ∀ as : List V,
      SpineFit ρ' (((ds.drop nP).map (·.2.2)).take j) as →
      interp2 V (consList as ρ') (((ds.drop nP).map (·.2.2)).getD j default)
        ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    (hguard : ∀ j, j ≤ i → (sorts.getD j .zero).eval ψ = 0)
    {as' : List V} (hspAs : SpineFit ρ' ((ds.drop nP).map (·.2.2)) as') :
    (pt : V) ∈ˢ interp2 V (consList (List.replicate i pt) ρ')
      (((ds.drop nP).map (·.2.2)).getD i default) := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)
  have hrep : as'.take i = List.replicate i pt := by
    have := spineFit_eq_replicate_pt hpre ?_
    · rwa [List.length_take, hlenFs, show min i nF = i from by omega] at this
    intro j hj bs hbs
    rw [List.length_take, hlenFs] at hj
    rw [List.take_take, show min j i = j from by omega] at hbs
    have := hsorts j (by omega) bs hbs
    rw [hguard j (by omega)] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
      ← List.getD_eq_getElem?_getD]
    exact this
  have hz := hsorts i hi _ hpre
  rw [hguard i (Nat.le_refl _)] at hz
  have hval := mem_univ_zero hz hnext
  rw [hval, hrep] at hnext
  exact hnext

end Setlec.SetR.Interp2
