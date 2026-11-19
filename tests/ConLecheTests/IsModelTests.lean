module

public import ConLeche.IsModel
public import ConLeche.Semantics.IsModelBasis
public import ConLecheTests.IotaEqTests
public import ConLecheTests.CompareAttack

public section

/-!
# What a model of a stream says (task #617)

Two demonstrations over the public notion `IsModel` (`ConLeche/IsModel.lean`), read off the
stream's own records, with nothing of the environment the checker builds:

* `T_a_ne_T_b`: in every model of a stream holding `inductive T | a | b` with its recursor and
  declaring the prelude's `Eq`, `T.a` and `T.b` are different sets.  The recursor's two rules
  hold (`RuleHolds`); at the motive `fun _ => Prop` and the minors `False` (`∅`) and `True`
  (`{pt}`) they make `T.rec` send `T.a` to `∅` and `T.b` to `{pt}`.
* `no_model`: no model of a stream that also holds `def f : T := T.a` and the hole
  `t : f = T.b` (an axiom of its statement) exists: `f` is what its value denotes, `Eq` is
  equality, so the hole's type is `eqv ⟦T.a⟧ ⟦T.b⟧`, which is empty.  The fixtures
  `CmpHomeA`/`CmpHomeC` use `def f : Nat := 3` and `t : f = 5`; the argument is the same, with
  `Nat.rec`'s rules in place of `T.rec`'s.
-/

namespace ConLeche.IsModelTest

open BasisDSL SetTheory ConLeche.SetModel ConLeche.IotaEqTest ConLeche.CompareAttackTest

universe w
variable {V : Type w} [SetTheory V]

/-- `T : Type`. -/
@[expose] def tCV : ConstantVal := ⟨tN, [], srt (.succ .zero)⟩

/-- The block `inductive T | a | b` with its recursor, as a stream carries it. -/
@[expose] def tBlock : List ConstantInfo :=
  [.indInfo tCV {}, .ctorInfo taCV 0 0 tN, .ctorInfo tbCV 0 0 tN,
    .recInfo trecCV 3 3 false [ruleA, ruleB]]

/-- The block's declaration. -/
@[expose] def tDecl : Declaration := .indDecl tBlock 0

/-- The block's records are its constants: the recursor's major is `T`, a type former of the
block, so its rules fire `.plain`, as they are written. -/
theorem tDecl_records : tDecl.records = tBlock := by rfl

theorem iotaEqAt_ruleA : iotaEqAt taCV 0 trecCV 3 3 ruleA = some (tEq taN ruleA.rhs) :=
  iotaEq_ruleA (find? := fun _ => some (.ctorInfo taCV 0 0 tN)) rfl

theorem iotaEqAt_ruleB : iotaEqAt tbCV 0 trecCV 3 3 ruleB = some (tEq tbN ruleB.rhs) :=
  iotaEq_ruleB (find? := fun _ => some (.ctorInfo tbCV 0 0 tN)) rfl

/-- The level assignment `T.rec.{1}` is read at. -/
abbrev φ1 : LevelParam → Nat := Level.assign [uN] [1]

/-- **In every model of a stream holding `T` and declaring `Eq`, `T.a` and `T.b` are different
sets.** -/
theorem T_a_ne_T_b {ds : List Declaration} {model : Name → List Nat → V}
    (h : IsModel V model ds) (hT : tDecl ∈ ds) (hE : DeclaresEq ds) :
    model taN [] ≠ model tbN [] := by
  intro hab
  have hrec : ∀ c ∈ tBlock, Satisfies V model ds c := fun c hc =>
    h tDecl hT c (by rw [tDecl_records]; exact hc)
  -- the type and its constructors
  have hTm : model tN [] ∈ˢ (univ 1 : V) := (hrec (.indInfo tCV {}) (by simp [tBlock]) [] rfl).1
  have hTa : model taN [] ∈ˢ model tN [] :=
    (hrec (.ctorInfo taCV 0 0 tN) (by simp [tBlock]) [] rfl).1
  have hTb : model tbN [] ∈ˢ model tN [] :=
    (hrec (.ctorInfo tbCV 0 0 tN) (by simp [tBlock]) [] rfl).1
  -- the recursor, at the motive `fun _ => Prop` and the minors `∅` and `{pt}`
  obtain ⟨hR, hrules⟩ := hrec (.recInfo trecCV 3 3 false [ruleA, ruleB]) (by simp [tBlock]) [1] rfl
  let m : V := lamV (model tN []) fun _ => univ 0
  have hm : m ∈ˢ piV (model tN []) (fun _ => (univ 1 : V)) :=
    lamV_mem (fun _ _ => univ_mem_univ 0) (fun _ _ => IsTy_of_mem_univ (univ_mem_univ 1))
  have hmc : ∀ c, c ∈ˢ model tN [] → app m c = univ 0 := fun c hc => app_lamV hc
  have hmA : (empty : V) ∈ˢ app m (model taN []) := by rw [hmc _ hTa]; exact empty_mem_univ 0
  have hmB : (unitSet : V) ∈ˢ app m (model tbN []) := by rw [hmc _ hTb]; exact unitSet_mem_univ 0
  have hR' : model trecN [1] ∈ˢ piV (piV (model tN []) fun _ => (univ 1 : V)) (fun mo =>
      piV (app mo (model taN [])) fun _ => piV (app mo (model tbN [])) fun _ =>
        piV (model tN []) fun t => app mo t) := hR
  have hrecAt : ∀ c, c ∈ˢ model tN [] →
      app (app (app (app (model trecN [1]) m) empty) unitSet) c ∈ˢ (univ 0 : V) := by
    intro c hc
    have h1 := app_mem_piV hR' hm
    have h2 := app_mem_piV h1 hmA
    have h3 := app_mem_piV h2 hmB
    have h4 := app_mem_piV h3 hc
    rw [← hmc c hc]
    exact h4
  -- a rule's equation at the motive and the minors
  have hrule : ∀ (ca : Name) (x : V) (sel : V → V → V), model ca [] ∈ˢ model tN [] →
      (∀ a b, a ∈ˢ (univ 0 : V) → b ∈ˢ (univ 0 : V) → sel a b ∈ˢ (univ 0 : V)) →
      x ∈ˢ piV (piV (model tN []) fun _ => (univ 1 : V)) (fun mo =>
        piV (app mo (model taN [])) fun a => piV (app mo (model tbN [])) fun b =>
          app (app (app (model eqName [1]) (app mo (model ca [])))
            (app (app (app (app (model trecN [1]) mo) a) b) (model ca [])))
            (app (app (app (lamV (piV (model tN []) fun _ => (univ 1 : V)) fun mo' =>
              lamV (app mo' (model taN [])) fun a' => lamV (app mo' (model tbN [])) fun b' =>
                sel a' b') mo) a) b)) →
      app (app (app (app (model trecN [1]) m) empty) unitSet) (model ca []) = sel empty unitSet := by
    intro ca x sel hca hsel hx
    have h1 := app_mem_piV hx hm
    have h2 := app_mem_piV h1 hmA
    have h3 := app_mem_piV h2 hmB
    rw [app_lamV hm, app_lamV hmA, app_lamV hmB, hmc _ hca,
      IsModel.eq_eqv h hE (univ_mem_univ 0) (hrecAt _ hca)
        (hsel _ _ (empty_mem_univ 0) (unitSet_mem_univ 0))] at h3
    exact eq_of_mem_eqv h3
  obtain ⟨xa, hxa⟩ := hrules ruleA (by simp) tDecl hT taCV 0 0 tN
    (by rw [tDecl_records]; simp [tBlock]) rfl _ iotaEqAt_ruleA
  obtain ⟨xb, hxb⟩ := hrules ruleB (by simp) tDecl hT tbCV 0 0 tN
    (by rw [tDecl_records]; simp [tBlock]) rfl _ iotaEqAt_ruleB
  have ha := hrule taN xa (fun a _ => a) hTa (fun a _ ha _ => ha) hxa
  have hb := hrule tbN xb (fun _ b => b) hTb (fun _ b _ hb => hb) hxb
  rw [hab, hb] at ha
  exact not_mem_empty _ (ha ▸ pt_mem_unitSet)

/-- **No model of the attack's stream**: `T`, `Eq`, `def f : T := T.a` and the hole
`t : f = T.b`.  `f` is `T.a`, `Eq` is equality, so the hole's type is `eqv ⟦T.a⟧ ⟦T.b⟧`, empty
by `T_a_ne_T_b`. -/
theorem no_model {ds : List Declaration} {model : Name → List Nat → V}
    (h : IsModel V model ds) (hT : tDecl ∈ ds) (hE : DeclaresEq ds) {hint : ReducibilityHint}
    (hf : Declaration.defnDecl fCV (cnst taN) hint ∈ ds)
    (ht : Declaration.axiomDecl holeCV ∈ ds) : False := by
  have hTm : model tN [] ∈ˢ (univ 1 : V) :=
    (h tDecl hT (.indInfo tCV {}) (by rw [tDecl_records]; simp [tBlock]) [] rfl).1
  have hTb : model tbN [] ∈ˢ model tN [] :=
    (h tDecl hT (.ctorInfo tbCV 0 0 tN) (by rw [tDecl_records]; simp [tBlock]) [] rfl).1
  -- `f` is what its value denotes
  have hfr : ConstantInfo.defnInfo fCV (cnst taN) hint ∈ (Declaration.defnDecl fCV (cnst taN) hint).records := by
    simp only [Declaration.records]
    rw [ite_eq_right (by decide)]
    exact List.mem_singleton_self _
  obtain ⟨hfm, hfv⟩ := h _ hf _ hfr [] rfl
  change model fN [] ∈ˢ model tN [] at hfm
  change model fN [] = model taN [] at hfv
  -- the hole's type is the truth value of `f = T.b`
  have hhr : ConstantInfo.axiomInfo holeCV ∈ (Declaration.axiomDecl holeCV).records := by
    simp only [Declaration.records]
    rw [ite_eq_right (by decide), ite_eq_right (by decide)]
    exact List.mem_singleton_self _
  have hh := (h _ ht _ hhr [] rfl).1
  change model holeN [] ∈ˢ app (app (app (model eqName [1]) (model tN [])) (model fN []))
    (model tbN []) at hh
  rw [IsModel.eq_eqv h hE hTm hfm hTb] at hh
  exact T_a_ne_T_b h hT hE (hfv.symm.trans (eq_of_mem_eqv hh))

end ConLeche.IsModelTest
