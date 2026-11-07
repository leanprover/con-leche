module

public import InLeanProof.IndOps

/-!
# O7: InLean's inductive declaration against master's (task #451, lane O7)

**The top of O7**, `checkIndDeclC_sim`: InLean's `checkIndDeclC .verified fe
block nP` accepting from a state with the residue (`CSOKIF`) means master's
pure fueled declaration step accepts the translated block
(`ConLeche.checkDecl .verified (fueledOps .verified F) pins L (.indDecl cb nP)`
with `toBlock block = some cb`): `checkModeledOrNativeSF_run`'s and
`checkDeclStepC_run`'s `.indDecl` arm, for InLean.  P4 composes it with
master's fold theorem; P3r's `IndGroupPresBP` gives the environment relation
after the step.

The dispatch is proved here: the pinned blocks by name (`basisNameHit_tr`),
the declared parameter count (`indParamsOk_tr`), the recogniser
(`blockShape?_tr`), the generated entries' agreement (`genEntriesAgree`
changes no state, `genEntriesAgree_noSt`) and the shapeless decline (it
never accepts, `checkShapelessS_not_ok`).  The two job runs are named
hypotheses, each stated as the cached driver's `_run` lemma it twins:

* `BasisBlockSimI` (`checkBasisBlockC_spec`'s twin): a pinned block accepted by
  InLean is accepted by master's `checkBasisBlock` on the translation.  What
  it needs: `pinListOk` (InLean's pins, compared up to `mdata` and binder
  data, `pinAgrees`) against master's on the translated block, and the
  freshness of the names through `EnvPresI`.
* `BlockKSSimI` (`checkBlockKS_run`'s twin): the recognised block's job
  (`InLeanProof/IndBlockKS.lean` reduces it to the job's stages).
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

/-! ## Runs of `CheckCM` programs -/

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

/-- **A pinned block's check changes no state.** -/
theorem checkBasisBlockC_noSt (fe : InLean.FEnv) (kind : InLean.BasisKind)
    (block : List Lean.ConstantInfo) : NoSt (InLean.checkBasisBlockC fe kind block) := by
  unfold InLean.checkBasisBlockC
  repeat' (first
    | exact NoSt.pure _
    | exact NoSt.throw _
    | (apply NoSt.bind <;> intros)
    | (apply NoSt.foldlM; intros)
    | apply NoSt.ite
    | split)

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

/-- **The shapeless branch never accepts** (it declines after its former
checks, `checkShapeless`'s twin). -/
theorem checkShapelessS_not_ok {mode : InLean.CheckMode} {fe : InLean.FEnv}
    {block : List Lean.ConstantInfo} {s₀ s' : InLean.CState} {v : Unit}
    (h : InLean.checkShapelessS mode fe block s₀ = .ok (v, s')) : False := by
  unfold InLean.checkShapelessS at h
  obtain ⟨_, _, _, h⟩ := bindI_ok h
  exact throwI_ok h

/-- What the declaration step checks of the generator's output (`constInRange`)
is the range premise here. -/
theorem CIRange_of_constInRange {ci : Lean.ConstantInfo} (h : InLean.constInRange ci = true) :
    CIRange ci := by
  cases ci with
  | recInfo v =>
    simp only [InLean.constInRange, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨(RangeOk_of_inRange h.1).1, fun r hr => (RangeOk_of_inRange (h.2 r hr)).1⟩
  | _ => exact (RangeOk_of_inRange h).1

/-! ## The two job runs, named -/

/-- **A pinned block** (`checkBasisBlockC_spec`'s twin): accepted by InLean,
accepted by master's `checkBasisBlock` on the translated block.  Open: InLean's
`pinListOk` (its own pins, compared by `pinAgrees` up to `mdata` and binder
data) against master's on the translation, and the names' freshness in `L`
read through `EnvPresI`. -/
@[expose] def BasisBlockSimI : Prop :=
  ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (kind : InLean.BasisKind)
    (block : List Lean.ConstantInfo) (s₀ s' : InLean.CState),
    JobEnvI fe L → (∀ ci ∈ block, CIOk ci) → (∀ ci ∈ block, isBlockKind ci = true) →
    InLean.basisNameHit block = some kind →
    InLean.checkBasisBlockC fe kind block s₀ = .ok ((), s') →
    ∃ L', ConLeche.checkBasisBlock (m := ConLeche.CheckM) L (trKind kind) (block.map trCI) = .ok L'

/-- **A recognised block's job** (`checkBlockKS_run`'s twin): accepted by
InLean from a state with the residue, accepted by master's pure fueled
`checkBlock` on the translated block and shape, and the residue kept
(`InLeanProof/IndBlockKS.lean` reduces it to the job's stages). -/
@[expose] def BlockKSSimI : Prop :=
  ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (block : List Lean.ConstantInfo) (nP : Nat)
    (p : InLean.BlockShape) (s₀ s' : InLean.CState),
    JobEnvI fe L → (∀ ci ∈ block, ci.name = InLean.sorryAxName → fe.coreAxioms = true) →
    CSOKIF s₀ → (∀ ci ∈ block, CIRange ci) →
    (∀ ci ∈ block, isBlockKind ci = true ∧ okC ci.toConstantVal.type = true) →
    InLean.blockShape? nP block = some p →
    InLean.checkBlockKS .verified fe block p s₀ = .ok ((), s') →
    CSOKIF s' ∧ ∃ F L', ConLeche.checkBlock (ConLeche.fueledOps .verified F) L (block.map trCI)
      (trShape p) = .ok L'

variable {pins : List ConLeche.NatOpPinSet}

/-- **O7's top: InLean's inductive declaration simulates master's pure
declaration step** on the translated block (`checkDeclStepC_run`'s `.indDecl`
arm and `checkModeledOrNativeSF_run`, for InLean), from the two job runs. -/
theorem checkIndDeclC_sim (hB : BasisBlockSimI) (hK : BlockKSSimI)
    {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {block : List Lean.ConstantInfo} {cb : List ConLeche.ConstantInfo} {nP : Nat}
    (hso : ∀ ci ∈ block, ci.name = InLean.sorryAxName → fe.coreAxioms = true)
    {s₀ s' : InLean.CState} (hs : CSOKIF s₀) (hr : ∀ ci ∈ block, CIRange ci)
    (hb : toBlock block = some cb)
    (h : InLean.checkIndDeclC .verified fe block nP s₀ = .ok ((), s')) :
    CSOKIF s' ∧ ∃ F L', ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins L
      (.indDecl cb nP) = .ok L' := by
  have hok := toBlock_CIOk hb hr
  obtain ⟨rfl, hk⟩ := toBlock_eq hb hr
  unfold InLean.checkIndDeclC at h
  cases hbn : InLean.basisNameHit block with
  | some kind =>
    rw [hbn] at h
    simp only at h
    have hst : s' = s₀ := checkBasisBlockC_noSt fe kind block s₀ () s' h
    obtain ⟨L', hL'⟩ := hB fe L kind block s₀ s' hJ hok (fun ci h => (hk ci h).1) hbn h
    refine ⟨hst ▸ hs, 0, L', ?_⟩
    simp only [ConLeche.checkDecl, basisNameHit_tr, hbn, Option.map_some]
    exact hL'
  | none =>
    rw [hbn] at h
    simp only at h
    by_cases hok : InLean.indParamsOk nP block = true
    · rw [ite_eq_left hok] at h
      cases hsh : InLean.blockShape? nP block with
      | none =>
        rw [hsh] at h
        exact (checkShapelessS_not_ok h).elim
      | some p =>
        rw [hsh] at h
        obtain ⟨u, s₁, h1, h2⟩ := bindI_ok h
        have hs1 : s₁ = s₀ := genEntriesAgree_noSt p block s₀ u s₁ h1
        subst hs1
        obtain ⟨hs', F, L', hF⟩ := hK fe L block nP p s₁ s' hJ hso hs hr hk hsh h2
        refine ⟨hs', F, L', ?_⟩
        have hok' : ConLeche.indParamsOk nP (block.map trCI) = true := by
          rw [indParamsOk_tr]; exact hok
        simp only [ConLeche.checkDecl, basisNameHit_tr, hbn, Option.map_none, hok', ↓reduceIte,
          blockShape?_tr nP block (fun ci h => (hk ci h).2), hsh, Option.map_some]
        exact hF
    · rw [ite_eq_right hok] at h
      exact (throwI_ok h).elim

end InLeanProof
