module

import ConLeche.Verify.Cached.DeclPushes
public import ConLeche.Cached.Decls
public import ConLeche.SetTheory.Core
import ConLeche.Verify.Cached.MainC

public section

/-!
# A theorem record of the stream is stored under its own name

The letters of the fold (`ConLeche/Verify/Cached/MainC.lean`) are about
the environment `checkDecls` RETURNS.  This module carries one fact the
other way, from the fold's INPUT: a `thmDecl` record whose declared type
is a bare constant is stored, with that very type, and the constant
survives to the end of the run.

Three ingredients, one per step of the walk:

* **the header is stored as declared.**  The check runs guards only;
  the stored header is the declared one, used directly.
* **a theorem record is never dropped.**  The check's `thmDecl` arm
  either throws or pushes `declConstants` of the record, the theorem at
  its declared type: `checkDeclStepC_pushes`.
* **pushed constants persist.**  An accepting `DeclsRun` only ever
  extends the constants list, so what the theorem's step pushed is still
  there at the end of the run.

`checkDecls_thmDecl_const` is the three composed: the returned
environment holds a constant of the record's declared type.  Nothing
here is about `False` in particular; the main corollary
(`no_False_theorem_accepted`, `ConLeche/MainTheorem.lean`) instantiates
it at `falseName`.
-/

namespace ConLeche.Cached

open ConLeche

variable {pins : List NatOpPinSet}

/-! ## A theorem record is installed, with its declared type -/

/-- **A theorem record of the stream is stored**: if the fold's run accepts a list of records
containing a `thmDecl` whose declared type is a bare constant, the environment it returns holds a
constant of that type. -/
theorem declsRun_thmDecl_const {mode : CheckMode} {ds : List Declaration}
    {cv : ConstantVal} {value : Expr} {n : Name} {ls : List Level}
    (hty : cv.type = .const n ls) (hmem : Declaration.thmDecl cv value ∈ ds)
    {p q : Nat × FEnv} (h : DeclsRun mode pins maxNatSize ds p q) :
    ∃ c ∈ q.2.env.consts, c.toConstantVal.type = .const n ls := by
  induction h with
  | nil p => exact absurd hmem (List.not_mem_nil)
  | @cons pd ds p p₁ q hstep rest ih =>
    obtain ⟨fe₁, s₁, rfl, hstepC⟩ := declStep_ok hstep
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · -- the record is this step's: its constant is pushed here
      have hpush := checkDeclStepC_pushes (pins := pins) mode p.2 (.thmDecl cv value) _ fe₁ s₁ hstepC
      have henv := declsRun_env mode rest
      have hmemc : ConstantInfo.thmInfo cv ∈ (streamEnv ds fe₁.env).consts := by
        have hconsts : ∀ (l : List Declaration) (e : Env), e.consts ⊆ (streamEnv l e).consts := by
          intro l
          induction l with
          | nil => intro e; exact List.Subset.refl _
          | cons d l ih =>
            intro e c hc
            refine ih (e.pushDelta (declConstants d) (declTables d)) ?_
            simp [Env.pushDelta, hc]
        refine hconsts ds fe₁.env ?_
        rw [hpush, pushDelta_env]
        simp [Env.pushDelta, declConstants]
      rw [henv]
      exact ⟨_, hmemc, by simp [ConstantInfo.toConstantVal, hty]⟩
    · exact ih hmem'

/-- **The main corollary's ingredient at the stream**: an accepted stream
that declares a theorem of a bare constant type leaves a constant of
that type in the environment. -/
theorem checkDecls_thmDecl_const {mode : CheckMode} {ds : Array Declaration} {env : Env}
    {cv : ConstantVal} {value : Expr} {n : Name} {ls : List Level}
    (hty : cv.type = .const n ls) (hmem : Declaration.thmDecl cv value ∈ ds)
    (h : checkDecls mode pins maxNatSize ds = .ok env) :
    ∃ c ∈ env.consts, c.toConstantVal.type = .const n ls := by
  obtain ⟨_, _, run, rfl⟩ := checkDecls_run mode h
  exact declsRun_thmDecl_const hty (Array.mem_toList_iff.mpr hmem) run

end ConLeche.Cached

namespace ConLeche

universe w

/-- **The main corollary, at the stream.**  A stream that declares a
theorem of type `False` is never accepted.  Two steps: the record is
installed under its own name with its declared type and that constant
survives the run (`checkDecls_thmDecl_const`), so an accepted
environment would hold a constant of type `False` — and it cannot,
because in the model of the main theorem that type denotes the empty
set, which the constant would have to be a member of
(`no_proof_of_False_cached`).  The main corollary
(`no_False_declaration`, `ConLeche/MainTheorem.lean`) rests on this. -/
theorem no_False_theorem_accepted (V : Type w) [SetTheory V]
    (ds : Array Declaration) (cv : ConstantVal) (v : Expr)
    (hmem : Declaration.thmDecl cv v ∈ ds) (hty : cv.type = .const falseName []) :
    ∀ env, Cached.checkDecls .verified pins maxNatSize ds ≠ .ok env := by
  intro env accepted
  obtain ⟨c, hc, hcty⟩ := Cached.checkDecls_thmDecl_const hty hmem accepted
  exact Cached.no_proof_of_False_cached V accepted c hc hcty

end ConLeche
