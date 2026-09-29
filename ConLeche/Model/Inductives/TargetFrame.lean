module

public import ConLeche.Model.Inductives.TargetIhSlot
import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The target rule's frame: prefix and fields

The target check opens the rule's frame in three steps: the recursor's prefix off its stored type (`openPisAtFvars rP recTy 0`),
the constructor at the major's parameters (`instPisWith`), its fields
off that (`openPisAtFvars nF crest rP`).  The frame's opener list is
therefore scoped, and its annotations are bvar-closed, name stored
constants and draw their leaves from the frame again — the frame facts
`walkCtx_blockFrame` and `targetIh_scope` take, proved here from the
three openings.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal CheckMode)

/-- **The major's parameters, scoped at the rule prefix**:
each is scoped at the prefix's depth, bvar-closed, names stored constants
and draws its leaves from the prefix openers.  At a member major they ARE
the first `nP` prefix openers (`tgtDsOk_of_take`); at an outside major
they are the arguments of the recursor type's major domain. -/
@[expose] def TgtDsOk (envT : Env) (rP : Nat) (fvsPref ds : List Expr) : Prop :=
  ∀ a ∈ ds, Expr.WScoped rP a ∧ a.looseBVarsBounded 0 = true ∧ ConstsBound envT a ∧
    ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref

/-- **The target rule's frame facts** from its three openings. -/
theorem targetFrame_facts {envT : Env} {rP nF : Nat} {recTy cty crest oP cbody : Expr}
    {fvsPref fvsF ds : List Expr}
    (h₁ : ConLeche.openPisAtFvars rP recTy 0 = some (fvsPref, oP))
    (hcr : ConLeche.instPisWith ds cty = some crest) (hds : TgtDsOk envT rP fvsPref ds)
    (h₂ : ConLeche.openPisAtFvars nF crest rP = some (fvsF, cbody))
    (hTf : recTy.hasFvar = false) (hTb : recTy.looseBVarsBounded 0 = true)
    (hTc : ConstsBound envT recTy)
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hCc : ConstsBound envT cty) :
    FvarList (rP + nF) (fvsPref ++ fvsF).reverse ∧
    (∀ x ∈ fvsPref ++ fvsF, (Expr.fvarTypeD x).looseBVarsBounded 0 = true) ∧
    (∀ x ∈ fvsPref ++ fvsF, ConstsBound envT x) ∧
    (∀ x ∈ fvsPref ++ fvsF, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF) := by
  rw [instPisWith_eq_instPisAt] at hcr
  obtain ⟨⟨cpref, crest'⟩, hinstC, hcr⟩ := Option.map_eq_some_iff.mp hcr
  have hcr' : crest = crest' := hcr.symm
  subst hcr'
  have hw₁ : Expr.WScoped 0 recTy := Expr.WScoped.of_not_hasFvar hTf
  have hL1 : FvarList rP fvsPref.reverse := by
    have := fvarList_of_open fvarList_nil h₁ hw₁
    rwa [Nat.zero_add, List.append_nil] at this
  have hw₂ : Expr.WScoped rP crest :=
    (instPisAt_WScoped (d := rP) _ cty hinstC (Expr.WScoped.of_not_hasFvar hCf)
      (fun a ha => (hds a ha).1)).2
  have hL2 := fvarList_of_open hL1 h₂ hw₂
  have h₃ : ConLeche.openPisAtFvars 0 (Expr.sort .zero) (rP + nF)
      = some ([], Expr.sort .zero) := rfl
  have hb₂ : crest.looseBVarsBounded 0 = true :=
    (ConLeche.Verify.instPisAt_bounded _ hinstC hCb (fun a ha => (hds a ha).2.1)).2
  have hc₂ : ConstsBound envT crest :=
    constsBound_instPisAt _ hinstC hCc (fun a ha => (hds a ha).2.2.1)
  have hctyNil : cty.fvarLeaves = [] := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf
  have hcrestLeaf : ∀ l ∈ crest.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref := by
    intro l hl
    rcases ConLeche.instPisAt_fvarLeaves _ cty hinstC l hl with h' | ⟨a, ha, hla⟩
    · rw [hctyNil] at h'; exact nomatch h'
    · exact (hds a ha).2.2.2 l hla
  obtain ⟨hlb, -⟩ := blockRuleHlbF_of h₁ h₂ h₃ hTb hb₂ rfl
  have hcb := blockRuleHcbF_of h₁ h₂ h₃ hTc hc₂ (by simp)
  have hcl := blockRuleHclF_of (nR := 0) (ihTele' := Expr.sort .zero) (o₃ := Expr.sort .zero)
    (fvsIh := []) h₁ h₂ rfl hTf hcrestLeaf (fun l hl => by simp [Expr.fvarLeaves] at hl)
  simp only [List.append_nil] at hlb hcb hcl
  exact ⟨by rw [List.reverse_append]; exact hL2, hlb, hcb, hcl⟩

/-- The frame's opener list extended by the `ih` variables. -/
theorem fvarList_ihs {B : Nat} {L : List Expr} (hL : FvarList B L) (tys : List Expr)
    (hws : ∀ t ∈ tys, Expr.WScoped B t) :
    FvarList (B + tys.length) ((ihFvarsAt B tys).reverse ++ L) := by
  suffices key : ∀ n, n ≤ tys.length →
      FvarList (B + n)
        (((List.range n).map fun r => Expr.fvar (B + r) (tys.getD r default)).reverse ++ L) by
    exact key tys.length (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro _; simpa using hL
  | succ n ih =>
    intro hn
    have h := (ih (by omega)).cons (tys.getD n default)
      (((hws _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact List.getElem_mem _)).mono (by omega)))
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    rw [show B + (n + 1) = B + n + 1 from by omega]
    exact h

end ConLeche.Model
