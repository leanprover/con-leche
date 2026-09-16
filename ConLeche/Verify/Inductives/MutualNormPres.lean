module

public import ConLeche.Verify.InferLeaves
public import ConLeche.Verify.InferLemmas
public import ConLeche.Verify.Abstract
public import ConLeche.Verify.ExceptBind
public import ConLeche.Kernel.Inductives.MutualInstall

public section

/-!
# The constructors' positivity normalisation, preserved (task #315 L-B)

`normCtorValM`'s field-domain normalisation (`normPosDomM`,
`Kernel/Inductives/MutualInstall.lean`) `whnf`s a domain that mentions
a member of the block and, while a member occurs, walks under its Π
binders — opening each body at a fresh variable and closing it again
(`abstract1`).  Its output is therefore NOT the input syntactically
(the λ-pin domain `(fun _ => PT α) k` reduces), which is why
`CopyCtorInst.ordF`'s ordinary arm is stated at the READING (DESIGN
§U.30).  The reading law itself is `normPosDomM_read`
(`Model/Inductives/MutualNorm.lean`); what it needs of the run is
here: the walk preserves scope, the loose-bvar bound and the leaf set,
which is what the `abstract1`/`instantiate1` round trip and the
context extension ask for.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A thrown step never succeeds. -/
private theorem normThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact normThrow_ne_ok (by assumption))
        | (exfalso; exact normThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-- **The positivity normalisation preserves the frame**: its output
is scoped at the same depth, carries no loose bvar, and its `fvar`
leaves are among the input's.  Each `whnf` step preserves all three
(`whnf_WScoped`, `whnf_looseBVars`, `whnf_fvarLeaves`); the Π step
opens at `.fvar d dom` — whose leaf is the domain's own, already in
the input — and closes with `abstract1`, which removes exactly the
index-`d` leaves (`Expr.fvarLeaves_abstract1_ne`). -/
theorem normPosDomM_pres {env : Env} (henv : EnvWF env) {memberNames : List Name} {F : Nat} :
    ∀ (fuel : Nat) {d : Nat} {e e' : Expr},
      normPosDomM (m := CheckM) (fueledOps mode F) env memberNames d fuel e = .ok e' →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.WScoped d e' ∧ e'.looseBVarsBounded 0 = true ∧
        ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves := by
  intro fuel
  induction fuel with
  | zero =>
    intro d e e' h _ _
    rw [normPosDomM] at h
    close_throw
  | succ fuel ih =>
    intro d e e' h hws hb
    rw [normPosDomM] at h
    by_cases hm : mentionsMember memberNames e = true
    · rw [if_neg (by simp [hm])] at h
      obtain ⟨w, hw, h⟩ := exceptBind_ok h
      have hwws : Expr.WScoped d w := whnf_WScoped henv F hw hws
      have hwb : w.looseBVarsBounded 0 = true := whnf_looseBVars henv F hw hb
      have hwl : ∀ l ∈ w.fvarLeaves, l ∈ e.fvarLeaves := whnf_fvarLeaves henv F hw
      by_cases hmw : mentionsMember memberNames w = true
      · rw [if_neg (by simp [hmw])] at h
        cases w with
        | forallE dom body bm =>
          simp only at h
          by_cases hmd : mentionsMember memberNames dom = true
          · rw [if_pos hmd] at h; close_throw
          · rw [if_neg (by simpa using hmd)] at h
            obtain ⟨body', hbody', h⟩ := exceptBind_ok h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            obtain rfl := h
            simp only [Expr.WScoped] at hwws
            obtain ⟨hwd, hwbo⟩ := hwws
            simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwb
            have hopen : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d dom)) :=
              Expr.WScoped.instantiate1 hwd 0 hwbo
            have hopenb : (body.instantiate1 (.fvar d dom)).looseBVarsBounded 0 = true :=
              looseBVarsBounded_instantiate1 body 0 hwb.2
            obtain ⟨hw', hb', hl'⟩ := ih hbody' hopen hopenb
            refine ⟨?_, ?_, ?_⟩
            · simp only [Expr.WScoped]
              exact ⟨hwd, WScoped.abstract1 0 hw'⟩
            · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
              exact ⟨hwb.1, looseBVarsBounded_abstract1 body' 0 hb'⟩
            · intro l hl
              simp only [Expr.fvarLeaves, List.mem_append] at hl
              rcases hl with hl | hl
              · exact hwl l (by simp [Expr.fvarLeaves, hl])
              · obtain ⟨hl₁, hl₂⟩ := Expr.fvarLeaves_abstract1_ne body' 0 hw' l hl
                rcases Expr.fvarLeaves_instantiate1 body 0 (hl' l hl₁) with h2 | h2
                · exact hwl l (by simp [Expr.fvarLeaves, h2])
                · rw [Expr.fvarLeaves] at h2
                  rcases List.mem_cons.mp h2 with rfl | h3
                  · exact absurd rfl hl₂
                  · exact hwl l (by simp [Expr.fvarLeaves, h3])
        | _ =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          obtain rfl := h
          exact ⟨hwws, hwb, hwl⟩
      · rw [if_pos (by simpa using hmw)] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        obtain rfl := h
        exact ⟨hwws, hwb, hwl⟩
    · rw [if_pos (by simpa using hm)] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl := h
      exact ⟨hws, hb, fun _ hl => hl⟩

end ConLeche
