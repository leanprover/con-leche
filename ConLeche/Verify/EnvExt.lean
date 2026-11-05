module

public import ConLeche.Verify.Cached.DiscC3
import ConLeche.Verify.Fueled

/-!
# A run does not see an extension of the environment (spike, task #480)

Pure fuelled knot, `env₁` extended to `env₂`: a term whose constants and literals resolve in
`env₁` runs alike at both.  This is the statement and two arms; see DESIGN #480 for the
census of the knot's reads.  `whnf`'s reach into `infer`/`defeq` through the rescues is why
the claim is for the whole knot (`ExtClaims`).
-/

@[expose] public section

namespace ConLeche.Verify

open ConLeche ConLeche.Cached

/-- **`env₂` extends `env₁`**: every stored constant stays, a stored structure's table stays,
and the facts about what is installed together, which every declaration boundary has. -/
structure EnvExt (env₁ env₂ : Env) : Prop where
  find : ∀ n ci, env₁.find? n = some ci → env₂.find? n = some ci
  table : ∀ T, (env₁.find? T).isSome = true → env₂.findTable? T = env₁.findTable? T
  /-- the `Nat` block is installed at once -/
  natTrio : (env₁.find? natName).isSome = true ∨ (env₁.find? natSuccName).isSome = true →
    (env₁.find? natName).isSome = true ∧ (env₁.find? natZeroName).isSome = true ∧
      (env₁.find? natSuccName).isSome = true
  /-- a stored `Nat` operation has `Nat` below it -/
  natOps : ∀ c, natOpWfNames.contains c = true → (env₁.find? c).isSome = true →
    (env₁.find? natName).isSome = true

theorem EnvExt.find_of_isSome {env₁ env₂ : Env} (h : EnvExt env₁ env₂) {n : Name}
    (hn : (env₁.find? n).isSome = true) : env₂.find? n = env₁.find? n := by
  cases hf : env₁.find? n with
  | none => rw [hf] at hn; exact nomatch hn
  | some ci => exact h.find n ci hf

/-- The `Nat` guard, wherever a name it depends on is stored. -/
theorem EnvExt.natLit {env₁ env₂ : Env} (h : EnvExt env₁ env₂)
    (hn : (env₁.find? natName).isSome = true) :
    natLitSupported env₂ = natLitSupported env₁ := by
  obtain ⟨h₁, h₂, h₃⟩ := h.natTrio (.inl hn)
  unfold natLitSupported
  rw [h.find_of_isSome h₁, h.find_of_isSome h₂, h.find_of_isSome h₃]

/-- A stored operation's capability is read at the operation. -/
theorem EnvExt.natOpStored {env₁ env₂ : Env} (h : EnvExt env₁ env₂) {c : Name}
    (hc : (env₁.find? c).isSome = true) :
    ConLeche.natOpStored env₂ c = ConLeche.natOpStored env₁ c := by
  unfold ConLeche.natOpStored
  rw [h.find_of_isSome hc]

/-- The claims at one fuel: on a resolved term the knot's entry points agree. -/
structure ExtClaims (mode : CheckMode) (eager : Bool) (env₁ env₂ : Env) (fuel : Nat) : Prop where
  whnf : ∀ {d : Nat} {e : Expr}, e.constsResolve env₁ = true →
    ConLeche.whnf mode eager env₂ fuel d e = ConLeche.whnf mode eager env₁ fuel d e
  inferIO : ∀ {d : Nat} {e : Expr}, e.constsResolve env₁ = true →
    inferTypeIO mode eager env₂ fuel d e = inferTypeIO mode eager env₁ fuel d e

variable {mode : CheckMode} {eager : Bool} {env₁ env₂ : Env} {fuel : Nat}

/-- **The `Nat` arm**: `reduceNat` on a resolved term.  Its reads are the head constant, whose
guards are read at stored names. -/
theorem reduceNat_ext (hx : EnvExt env₁ env₂) (ih : ExtClaims mode eager env₁ env₂ fuel) {d : Nat}
    {e : Expr} (hr : e.constsResolve env₁ = true) :
    reduceNat (pureFns mode eager env₂ fuel) env₂ d e =
      reduceNat (pureFns mode eager env₁ fuel) env₁ d e := by
  match e with
  | .bvar _ | .fvar _ _ | .sort _ | .lam _ _ | .forallE _ _
  | .letE _ _ _ | .lit _ | .proj _ _ _ | .const _ _ => rfl
  | .app f a =>
    have hfa : f.constsResolve env₁ = true ∧ a.constsResolve env₁ = true := by
      simpa [Expr.constsResolve] using hr
    have hw : (pureFns mode eager env₂ fuel).whnf d a = (pureFns mode eager env₁ fuel).whnf d a :=
      ih.whnf hfa.2
    match f with
    | .bvar _ | .fvar _ _ | .sort _ | .lam _ _ | .forallE _ _
    | .letE _ _ _ | .lit _ | .proj _ _ _ => rfl
    | .const c us =>
      match us with
      | _ :: _ => rfl
      | [] =>
        have hc : (env₁.find? c).isSome = true := by simpa [Expr.constsResolve] using hfa.1
        simp only [reduceNat, hw]
        by_cases hs : c = natSuccName
        · subst hs
          have hN := (hx.natTrio (.inr hc)).1
          rw [hx.natLit hN]
        · simp [hs]
    | .app f' a' =>
      match f' with
      | .bvar _ | .fvar _ _ | .sort _ | .lam _ _ | .forallE _ _
      | .letE _ _ _ | .lit _ | .proj _ _ _ | .app _ _ => rfl
      | .const c us =>
        match us with
        | _ :: _ => rfl
        | [] =>
          have hfa' : (Expr.const c []).constsResolve env₁ = true ∧ a'.constsResolve env₁ = true := by
            simpa [Expr.constsResolve] using hfa.1
          have hc : (env₁.find? c).isSome = true := by simpa [Expr.constsResolve] using hfa'.1
          have hw' : (pureFns mode eager env₂ fuel).whnf d a' =
              (pureFns mode eager env₁ fuel).whnf d a' := ih.whnf hfa'.2
          have hl : (natOpWfNames.contains c = true ∧ natLitSupported env₂ = true) ↔
              (natOpWfNames.contains c = true ∧ natLitSupported env₁ = true) :=
            ⟨fun h => ⟨h.1, by rw [← hx.natLit (hx.natOps c h.1 hc)]; exact h.2⟩,
              fun h => ⟨h.1, by rw [hx.natLit (hx.natOps c h.1 hc)]; exact h.2⟩⟩
          simp only [reduceNat, hw, hw', hx.natOpStored hc, hl]

/-- The walk to a sort, on a resolved term: what `whnf` returns on a resolved term resolves
(`hres`), and opening a binder at a variable of a resolved domain keeps it so. -/
theorem formerSortLoop_ext (ih : ExtClaims mode eager env₁ env₂ fuel)
    (hres : ∀ {d : Nat} {e w : Expr}, e.constsResolve env₁ = true →
      ConLeche.whnf mode eager env₁ fuel d e = .ok w → w.constsResolve env₁ = true)
    (hopen : ∀ {d : Nat} {dom b : Expr}, (Expr.forallE dom b).constsResolve env₁ = true →
      (b.instantiate1 (.fvar d dom)).constsResolve env₁ = true) :
    ∀ {n d : Nat} {e : Expr}, e.constsResolve env₁ = true →
      formerSortLoop (pureFns mode eager env₂ fuel).whnf d n e =
        formerSortLoop (pureFns mode eager env₁ fuel).whnf d n e
  | 0, d, e, he => by
    unfold formerSortLoop
    rw [show (pureFns mode eager env₂ fuel).whnf d e = (pureFns mode eager env₁ fuel).whnf d e
      from ih.whnf he]
  | n + 1, d, e, he => by
    unfold formerSortLoop
    rw [show (pureFns mode eager env₂ fuel).whnf d e = (pureFns mode eager env₁ fuel).whnf d e
      from ih.whnf he]
    cases hw : (pureFns mode eager env₁ fuel).whnf d e with
    | error err => rfl
    | ok w =>
      cases w with
      | forallE dom b =>
        exact formerSortLoop_ext ih hres hopen (hopen (hres he hw))
      | _ => rfl

/-- A family's sort at a use, read off its closed former. -/
theorem formerNeverZeroAt_ext (ih : ExtClaims mode eager env₁ env₂ fuel)
    (hres : ∀ {d : Nat} {e w : Expr}, e.constsResolve env₁ = true →
      ConLeche.whnf mode eager env₁ fuel d e = .ok w → w.constsResolve env₁ = true)
    (hopen : ∀ {d : Nat} {dom b : Expr}, (Expr.forallE dom b).constsResolve env₁ = true →
      (b.instantiate1 (.fvar d dom)).constsResolve env₁ = true)
    {cvT : ConstantVal} {caps : IndCaps} {us : List Level}
    (hT : (cvT.type.instantiateLevelParams cvT.levelParams us).constsResolve env₁ = true) :
    formerNeverZeroAt (pureFns mode eager env₂ fuel).whnf cvT caps us =
      formerNeverZeroAt (pureFns mode eager env₁ fuel).whnf cvT caps us := by
  unfold formerNeverZeroAt
  split
  · rfl
  · rw [formerSortLoop_ext ih hres hopen hT]

/-- **A rescue's arm** (`mtcEtaCont`): the η rescue past the major's type.  It reads the table
of a stored family and its walked sort, each stable. -/
theorem mtcEtaCont_ext (hx : EnvExt env₁ env₂) (ih : ExtClaims mode eager env₁ env₂ fuel)
    (hres : ∀ {d : Nat} {e w : Expr}, e.constsResolve env₁ = true →
      ConLeche.whnf mode eager env₁ fuel d e = .ok w → w.constsResolve env₁ = true)
    (hopen : ∀ {d : Nat} {dom b : Expr}, (Expr.forallE dom b).constsResolve env₁ = true →
      (b.instantiate1 (.fvar d dom)).constsResolve env₁ = true)
    {d : Nat} {major tmaj : Expr} {T : Name} {cvT : ConstantVal} {caps : IndCaps}
    (hTs : (env₁.find? T).isSome = true)
    (hty : ∀ us : List Level,
      (cvT.type.instantiateLevelParams cvT.levelParams us).constsResolve env₁ = true) :
    mtcEtaCont (pureFns mode eager env₂ fuel) env₂ d major T cvT caps tmaj =
      mtcEtaCont (pureFns mode eager env₁ fuel) env₁ d major T cvT caps tmaj := by
  have htow : towerSlotsAll env₂ T caps.etaFields = towerSlotsAll env₁ T caps.etaFields := by
    unfold towerSlotsAll
    refine congrArg _ (funext fun j => ?_)
    unfold Env.findProj?
    rw [hx.table T hTs]
  unfold mtcEtaCont
  split
  · rw [htow]
    split
    · rw [formerNeverZeroAt_ext ih hres hopen (hty _)]
    · rfl
  · rfl

/-- **A former's reduct at an extension is the one at the prefix**: the consequence the block's
second path reads. -/
theorem reducedFormer_ext {envB env : Env} (hwf : EnvWF envB) (hx : EnvExt envB env)
    {cv : ConstantVal} {n F : Nat} {f : ConstantVal} (hr : cv.type.constsResolve envB = true)
    (h : reducedFormer (fueledOps .verified F) envB cv n = .ok f) :
    ∃ F', reducedFormer (fueledOps .verified F') env cv n = .ok f := by
  sorry

end ConLeche.Verify
