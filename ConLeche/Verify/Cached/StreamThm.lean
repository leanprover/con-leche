module

public import ConLeche.Cached.Installed
public import ConLeche.SetTheory.Core
import ConLeche.Verify.Cached.MainC
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.BridgeCS4

public section

/-!
# A theorem record of the stream is stored under its own name

The letters of the fold (`ConLeche/Verify/Cached/MainC.lean`) are about
the environment `checkDecls` RETURNS.  This module carries one fact the
other way, from the fold's INPUT: a `thmDecl` record whose declared type
is a bare constant is installed, with that very type, and the constant
survives to the end of the run.

Three ingredients, one per step of the walk:

* **the header is stored as declared.**  Phase A's header install
  (`installHeaderC`) runs guards only; the stored header is the
  declared one, used directly.
* **a theorem record is never dropped.**  `installStepC`'s `thmDecl` arm
  either throws or pushes `.thmInfo ⟨cv.name, cv.levelParams, jty⟩`
  with the declared type `jty`: `installStepC_thm_consts`.
* **pushed constants persist.**  An accepting `InstallRun` only ever
  extends the constants list (`installRun_trace`, `PushChain`), so what
  the theorem's step pushed is still there at the end of phase A —
  and phase B pushes nothing at all.

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

/-- Phase A's step at a `thmDecl` record with a bare declared type:
the constant it pushes is a `.thmInfo` of that very type. -/
theorem installStepC_thm_consts {mode : CheckMode} {i : Nat} {fe : FEnv}
    {pend : Array PendingCheck} {cv : ConstantVal} {value : Expr}
    {n : Name} {ls : List Level} {s₀ s' : CState}
    {fe' : FEnv} {pend' : Array PendingCheck} (hty : cv.type = .const n ls)
    (h : installStepC mode pins i fe pend (.thmDecl cv value) s₀ = .ok ((fe', pend'), s')) :
    fe'.env.consts =
      ConstantInfo.thmInfo ⟨cv.name, cv.levelParams, .const n ls⟩ ::
        fe.env.consts := by
  unfold installStepC at h
  simp only [] at h
  obtain ⟨_, s₁, hfl, h⟩ := bindC_ok h
  rw [show (flushC : CheckCM Unit) s₀ = .ok ((), s₀.flushed) from rfl] at hfl
  have hs₁ : s₀.flushed = s₁ := congrArg Prod.snd (Except.ok.inj hfl)
  subst hs₁
  obtain ⟨_, s₂, _hcv, h'⟩ := bindC_ok h
  obtain ⟨hv, _⟩ := pureC_ok h'
  obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ hv
  rw [← hty]
  rfl

/-! ## The constant survives to the end of phase A -/

/-- **A theorem record of the stream is stored**: if phase A accepts a
list of records containing a `thmDecl` whose declared type is a bare
constant, the environment it returns holds a constant of that type. -/
theorem installRun_thmDecl_const {mode : CheckMode} {ds : List Declaration}
    {cv : ConstantVal} {value : Expr} {n : Name} {ls : List Level}
    (hty : cv.type = .const n ls) (hmem : Declaration.thmDecl cv value ∈ ds)
    {p q : Nat × FEnv × Array PendingCheck}
    (h : InstallRun mode pins ds p q) (hcanon : p.2.1 = mkFEnv p.2.1.env) :
    ∃ c ∈ q.2.1.env.consts, c.toConstantVal.type = .const n ls := by
  induction h with
  | nil p => exact absurd hmem (List.not_mem_nil)
  | @cons pd ds p p₁ q hstep rest ih =>
    obtain ⟨fe₁, pend₁, s₁, rfl, hstepC⟩ := installDeclStep_ok hstep
    have hchain : PushChain p.2.1.env fe₁ :=
      (installStepC_push mode p.1 (PushChain.self hcanon) p.2.2 pd {} (fe₁, pend₁) s₁
        hstepC).1
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · -- the record is this step's: its constant is pushed here
      have hconsts := installStepC_thm_consts hty hstepC
      obtain ⟨⟨_, ⟨new, hnew⟩, _⟩, _⟩ :=
        installRun_trace mode rest (PushChain.self hchain.canon)
      refine ⟨ConstantInfo.thmInfo ⟨cv.name, cv.levelParams, .const n ls⟩, ?_, rfl⟩
      rw [hnew]
      exact List.mem_append_right _ (hconsts ▸ List.mem_cons_self)
    · exact ih hmem' hchain.canon

/-- **The main corollary's ingredient at the stream**: an accepted stream
that declares a theorem of a bare constant type leaves a constant of
that type in the environment. -/
theorem checkDecls_thmDecl_const {mode : CheckMode} {ds : Array Declaration} {env : Env}
    {cv : ConstantVal} {value : Expr} {n : Name} {ls : List Level}
    (hty : cv.type = .const n ls) (hmem : Declaration.thmDecl cv value ∈ ds)
    (h : checkDecls mode pins ds = .ok env) :
    ∃ c ∈ env.consts, c.toConstantVal.type = .const n ls := by
  obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked mode h
  obtain ⟨_, run⟩ := fc.1.run
  exact installRun_thmDecl_const hty (Array.mem_toList_iff.mpr hmem) run rfl

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
    ∀ env, Cached.checkDecls .verified pins ds ≠ .ok env := by
  intro env accepted
  obtain ⟨c, hc, hcty⟩ := Cached.checkDecls_thmDecl_const hty hmem accepted
  exact Cached.no_proof_of_False_cached V rfl accepted c hc hcty

end ConLeche
