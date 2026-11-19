module

public import ConLeche.Model.Modular.Read
public import ConLeche.Verify.Cached.Scoped

public section

/-!
# A read-scoped environment, read over a predicate

The bridge from the model-free `Scoped` (`Verify/Cached/Scoped.lean`, which every accepted
environment is: `declsRun_scoped`) to the amalgamation's vocabulary: every stored constant is
`EntryScopedP` at "stored in `E`".
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Cached ConLeche.Modular

/-- **Every stored constant of a read-scoped environment reads stored names.** -/
theorem _root_.ConLeche.Cached.Scoped.entryScopedP {E : Env} (h : Scoped E) :
    ∀ n ci, E.find? n = some ci →
      EntryScopedP (fun d => (E.find? d).isSome = true) E n ci := by
  intro n ci hf
  have hn := Env.find?_name hf
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.1 ci (Env.find?_mem hf)
  have hR := fun {x : Expr} (hx : x.constsResolve E = true) => (Expr.constsResolve_iff E).mp hx
  refine ⟨hR h1, fun cv v hh he => hR (h2 cv v hh he), fun cv mI rP isK rules he r hr => ?_,
    fun cv caps he => ⟨h4 cv caps he, fun t ht => ?_⟩, fun d hd => ?_⟩
  · obtain ⟨a, b, c⟩ := h3 cv mI rP isK rules he r hr
    exact ⟨hR a, b, fun lvls ps hfire q hq => hR (c lvls ps hfire q hq)⟩
  · obtain ⟨c1, c2⟩ := h.2 t (Env.findTable?_mem ht).1
    exact ⟨c1, fun b hb => hR (c2 b hb)⟩
  · rw [← hn] at hd
    exact h5 d hd

end ConLeche.Model.Modular
