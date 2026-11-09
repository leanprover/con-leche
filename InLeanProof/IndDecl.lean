module

public import InLeanProof.IndOps
-- `Expr.hasLooseBVars`'s body (the generator's output closedness check)
import all Lean.Expr

/-!
# O7: InLean's inductive declaration against master's (task #451, lane O7)

**The top of O7**, `checkIndDeclC_sim_of`: InLean's `checkIndDeclC .verified fe
block nP` accepting from a state with the residue (`CSOKIF`) means master's
pure fueled declaration kind check accepts the translated block
(`ConLeche.checkDeclKind (fueledOps .verified F) pins L (.indDecl cb nP)`
with `toBlock block = some cb`): `checkModeledOrNativeSF_run`'s and
`checkDeclStepC_run`'s `.indDecl` arm, for InLean.  The reserved names' check
after it is `InLeanProof.basisNamesOk_tr`'s (`IndBasis.lean`).  P4 composes
them with master's fold theorem; P3r's `IndGroupPresBP` gives the environment
relation after the step.

The dispatch is proved here: the declared parameter count
(`indParamsOk_tr`), the reader (`readBlock_tr`), the generated entries'
agreement (`genEntriesAgree` changes no state, `genEntriesAgree_noSt`) and the
reader's reject (a throw, it never accepts).  A pinned
basis block takes the same route.  The job run is a named hypothesis, stated
as the cached driver's `_run` lemma it twins: `BlockKSSimI`
(`checkBlockKS_run`'s twin), the recognised block's job
(`InLeanProof/IndBlockKS.lean` reduces it to the job's stages).
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

/-! ## Runs of `CheckCM` programs -/

theorem bindI_of_ok {α β : Type} {x : InLean.CheckCM α} {k : α → InLean.CheckCM β}
    {s₀ s₁ s' : InLean.CState} {a : α} {v : β}
    (h₁ : x s₀ = .ok (a, s₁)) (h₂ : k a s₁ = .ok (v, s')) : (x >>= k) s₀ = .ok (v, s') := by
  simp only [Bind.bind, StateT.bind, h₁]
  exact h₂

theorem bindI_ok {α β : Type} {x : InLean.CheckCM α} {k : α → InLean.CheckCM β}
    {s₀ : InLean.CState} {v : β} {s' : InLean.CState}
    (h : (x >>= k) s₀ = .ok (v, s')) :
    ∃ a s₁, x s₀ = .ok (a, s₁) ∧ k a s₁ = .ok (v, s') := by
  simp only [Bind.bind, StateT.bind] at h
  cases hx : x s₀ with
  | error e => rw [hx] at h; exact nomatch h
  | ok pr =>
    obtain ⟨a, s₁⟩ := pr
    rw [hx] at h
    exact ⟨a, s₁, rfl, h⟩

theorem pureI_ok {α : Type} {a : α} {s₀ : InLean.CState} {v : α} {s' : InLean.CState}
    (h : (pure a : InLean.CheckCM α) s₀ = .ok (v, s')) : a = v ∧ s₀ = s' := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact h

theorem throwI_ok {α : Type} {e : InLean.CheckError} {s₀ : InLean.CState} {v : α}
    {s' : InLean.CState} (h : (throw e : InLean.CheckCM α) s₀ = .ok (v, s')) : False :=
  nomatch h

/-- **A program that reads and writes no state.** -/
@[expose] def NoSt {α : Type} (x : InLean.CheckCM α) : Prop :=
  ∀ s a s', x s = .ok (a, s') → s' = s

theorem NoSt.pure {α : Type} (a : α) : NoSt (pure a : InLean.CheckCM α) :=
  fun _ _ _ h => (pureI_ok h).2.symm

theorem NoSt.throw {α : Type} (e : InLean.CheckError) : NoSt (throw e : InLean.CheckCM α) :=
  fun _ _ _ h => (throwI_ok h).elim

theorem NoSt.bind {α β : Type} {x : InLean.CheckCM α} {k : α → InLean.CheckCM β}
    (hx : NoSt x) (hk : ∀ a, NoSt (k a)) : NoSt (x >>= k) := by
  intro s b s' h
  obtain ⟨a, s₁, h1, h2⟩ := bindI_ok h
  rw [hk a s₁ b s' h2, hx s a s₁ h1]

theorem NoSt.ite {α : Type} {c : Prop} [Decidable c] {x y : InLean.CheckCM α}
    (hx : NoSt x) (hy : NoSt y) : NoSt (if c then x else y) := by
  split <;> assumption

theorem NoSt.forIn {α β : Type} (l : List α) (b : β)
    {f : α → β → InLean.CheckCM (ForInStep β)} (hf : ∀ a b, NoSt (f a b)) :
    NoSt (forIn l b f) := by
  induction l generalizing b with
  | nil => rw [List.forIn_nil]; exact NoSt.pure b
  | cons a l ih =>
    rw [List.forIn_cons]
    refine NoSt.bind (hf a b) fun r => ?_
    cases r with
    | done b' => exact NoSt.pure b'
    | yield b' => exact ih b'

theorem NoSt.foldlM {α β : Type} (l : List α) (b : β)
    {f : β → α → InLean.CheckCM β} (hf : ∀ b a, NoSt (f b a)) : NoSt (l.foldlM f b) := by
  induction l generalizing b with
  | nil => rw [List.foldlM_nil]; exact NoSt.pure b
  | cons a l ih =>
    rw [List.foldlM_cons]
    exact NoSt.bind (hf b a) fun b' => ih b'

/-- **The generated entries' check changes no state.** -/
theorem genEntriesAgree_noSt (p : InLean.BlockShape) (block : List Lean.ConstantInfo) :
    NoSt (genEntriesAgree p block) := by
  unfold genEntriesAgree
  repeat' (first
    | exact NoSt.pure _
    | exact NoSt.throw _
    | (apply NoSt.bind <;> intros)
    | (apply NoSt.forIn; intros)
    | apply NoSt.ite
    | split)

/-- What the declaration step checks of the generator's output (`constInRange`)
is the range premise here. -/
theorem CIRange_of_constInRange {ci : Lean.ConstantInfo} (h : InLean.constInRange ci = true) :
    CIRange ci := by
  cases ci with
  | recInfo v =>
    simp only [InLean.constInRange, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨(RangeOk_of_inRange h.1).1, fun r hr => (RangeOk_of_inRange (h.2 r hr)).1⟩
  | _ => exact (RangeOk_of_inRange h).1

/-- A closed term with a closed reading: its reading has no loose bound variable. -/
theorem lbb_trC_of_closed {e : Lean.Expr} (hok : okC e = true) (h : e.hasLooseBVars = false) :
    (trC e).looseBVarsBounded 0 = true := by
  have hb := looseBVarRange_toExpr fvarsOnly_none (RangeOk_of_okE hok) (toExpr_of_okE _ hok)
  rw [ConLeche.Expr.looseBVarsBounded_iff]
  change decide (e.looseBVarRange > 0) = false at h
  simp only [hb, decide_eq_false_iff_not] at h
  show (trE _ e).bvarBound ≤ 0
  omega

/-! ## The job run, named -/

/-- **What the tail reads of the recognised shape beyond the pass** (lane
TailSim): at a one-constructor member, the projection bodies in range
at every field (`projBodyOk`, which the inductive check runs on the generated
block, `projBodiesAllOk`), and the stream recursors' rules with a closed reading
(the block's `CIOk`).  `checkIndDeclC_sim_of` derives it from the generated
entries' agreement (`genEntriesAgree`). -/
structure TailShapeOkI (p : InLean.BlockShape) : Prop where
  steps : ∀ ms ∈ p.members, ∀ c, ms.ctors = [c] → ∀ i < c.2,
    InLean.projBodyOk ms.declared.name p.nP i c.1.type = true
  rules : ∀ rc ∈ p.recs, ∀ r ∈ rc.rules, okC r.rhs = true

/-- **A recognised block's job** (`checkBlockKS_run`'s twin): accepted by
InLean from a state with the residue, accepted by master's pure fueled
`checkBlock` on the translated block and shape, and the residue kept
(`InLeanProof/IndBlockKS.lean` reduces it to the job's stages). -/
@[expose] def BlockKSSimI : Prop :=
  ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (block : List Lean.ConstantInfo) (nP : Nat)
    (p : InLean.BlockShape) (s₀ s' : InLean.CState),
    JobEnvI fe L → (∀ ci ∈ block, ci.name = InLean.sorryAxName → fe.coreAxioms = true) →
    CSOKIF s₀ → (∀ ci ∈ block, CIRange ci) → (∀ ci ∈ block, CIClosed ci) →
    (∀ ci ∈ block, isBlockKind ci = true ∧ okC ci.toConstantVal.type = true) →
    InLean.readBlock nP block = .ok p → TailShapeOkI p →
    InLean.checkBlockKS .verified fe block p s₀ = .ok ((), s') →
    CSOKIF s' ∧ ∃ F L', ConLeche.checkBlock (ConLeche.fueledOps .verified F) L (block.map trCI)
      (trShape p) = .ok L'

variable {pins : List ConLeche.NatOpPinSet}

/-- **O7's top: InLean's inductive declaration simulates master's pure
declaration kind check** on the translated block (`checkDeclStepC_run`'s
`.indDecl` arm and `checkModeledOrNativeSF_run`, for InLean), from the job
run, and the shape facts the tail reads (`TailShapeOkI`) from the generated
entries' agreement. -/
theorem checkIndDeclC_sim_of (hK : BlockKSSimI)
    {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {block : List Lean.ConstantInfo} {cb : List ConLeche.ConstantInfo} {nP : Nat}
    (hso : ∀ ci ∈ block, ci.name = InLean.sorryAxName → fe.coreAxioms = true)
    {s₀ s' : InLean.CState} (hs : CSOKIF s₀) (hr : ∀ ci ∈ block, CIRange ci)
    (hcl : ∀ ci ∈ block, CIClosed ci) (hb : toBlock block = some cb)
    (hTS : ∀ p s, InLean.readBlock nP block = .ok p →
      InLean.genEntriesAgree p block s = .ok ((), s) → TailShapeOkI p)
    (h : InLean.checkIndDeclC .verified fe block nP s₀ = .ok ((), s')) :
    CSOKIF s' ∧ ∃ F L', ConLeche.checkDeclKind (ConLeche.fueledOps .verified F) pins L
      (.indDecl cb nP) = .ok L' := by
  obtain ⟨rfl, hk⟩ := toBlock_eq hb hr
  unfold InLean.checkIndDeclC at h
  by_cases hok : InLean.indParamsOk nP block = true
  · rw [ite_eq_left hok] at h
    cases hsh : InLean.readBlock nP block with
    | error e =>
      rw [hsh] at h
      exact (throwI_ok h).elim
    | ok p =>
      rw [hsh] at h
      obtain ⟨u, s₁, h1, h2⟩ := bindI_ok h
      have hs1 : s₁ = s₀ := genEntriesAgree_noSt p block s₀ u s₁ h1
      subst hs1
      obtain ⟨hs', F, L', hF⟩ := hK fe L block nP p s₁ s' hJ hso hs hr hcl hk hsh
        (hTS p s₁ hsh (by cases u; exact h1)) h2
      refine ⟨hs', F, L', ?_⟩
      have hok' : ConLeche.indParamsOk nP (block.map trCI) = true := by
        rw [indParamsOk_tr]; exact hok
      simp only [ConLeche.checkDeclKind, hok', ↓reduceIte,
        readBlock_tr nP block (fun ci h => (hk ci h).2) hsh]
      exact hF
  · rw [ite_eq_right hok] at h
    exact (throwI_ok h).elim

end InLeanProof
