module

public import ConLeche.Verify.Denote
public import ConLeche.Verify.EnvPreds

public section

/-!
# The pinned basis constants' direct valuations

`pinnedStructT` — what a reserved basis constant denotes to in the
declarative layer, where it denotes to a bare `BConst` built-in.

The definition is `V`-free — a table from the checker's reserved
names to `ConLeche/Term/Const.lean`'s built-ins (task #148).  The
level-parameter names it reads are `ConLeche/Verify/EnvPreds.lean`'s
`uN`/`vN`/`u1N`.
-/

namespace ConLeche.Verify

open ConLeche.Term

/-- What a reserved basis constant denotes to, where it denotes to a
bare built-in.  `none` for the four the layer derives rather than
carries (see the section note).

**Two entries were wrong until the basis install elaborated them**
(task #119, `DESIGN.md` §8.2's defect, in its "unproved definition"
form).  `Empty` is stored *level-monomorphically* (`levelParams = []`),
so its valuation may not read the assignment at all — its level is
fixed by its pinned type, `Sort 1`.  `Empty.rec` binds **one** level
where the layer's `emptyRec` takes two, the first being `Empty`'s own.

`False` (task #181) is `Empty.{0}` in the layer's currency: the
built-in `empty` at level `0` is `Sort 0`-valued, and
`False.rec` is `emptyRec` at `[0, u]`.  No new built-in.

Each would have been caught only here: nothing before the install
asserts the valuation's level parameters for a basis constant. -/
@[expose] def pinnedStructT (n : Name) (ψ : Name → Nat) : Option Term :=
  if n = natName then some (.const .nat [])
  else if n = natZeroName then some (.const .natZero [])
  else if n = natSuccName then some (.const .natSucc [])
  else if n = natName.str "rec" then some (.const .natRec [ψ uN])
  else if n = emptyName then some (.const .empty [1])
  else if n = emptyName.str "rec" then
    some (.const .emptyRec [1, ψ uN])
  else if n = falseName then some (.const .empty [0])
  else if n = falseName.str "rec" then
    some (.const .emptyRec [0, ψ uN])
  else if n = quotName then some (.const .quot [ψ uN])
  else if n = quotMkName then some (.const .quotMk [ψ uN])
  else if n = quotLiftName then some (.const .quotLift [ψ uN, ψ vN])
  else if n = quotIndName then some (.const .quotInd [ψ uN])
  else if n = quotSoundName then some (.const .quotSound [ψ uN])
  else none

/-- **A constant is a copy of a pin**: the pin at the constant's own
level-parameter names, distinct and as many as the pin's. -/
@[expose] def PinCopy (ci pin : ConstantInfo) : Prop :=
  ci = pin.atLps ci.toConstantVal.levelParams ∧
  ci.toConstantVal.levelParams.Nodup ∧
  ci.toConstantVal.levelParams.length = pin.toConstantVal.levelParams.length

/-- **The assignment a copy's leaf reads the pin's parameters at**: the
pin's `i`-th parameter at the copy's `i`-th name. -/
@[expose] def pinVal (pin ps : List Name) (ψ : Name → Nat) : Name → Nat :=
  Level.substFn ψ pin (ps.map Level.param)

/-- **A stored recursor copy links its rules' constructors as its pin
does**: what a `.plain` rule reads of the constructor's parameters, by
name (`recFireComparands`), is the pin's, at every instantiation. -/
@[expose] def PinLinked (env : Env) (n : Name) (ci : ConstantInfo) : Prop :=
  ∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules →
    ∀ rl ∈ rules, RecRule.fire rl = .plain → ∀ cvj cnP cnF,
      env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
      ∀ us : List Level, us.length = cv.levelParams.length →
        cvj.levelParams.map (fun p => Level.subst cv.levelParams us (.param p)) =
          (pinnedInfo (RecRule.ctor rl)).toConstantVal.levelParams.map
            (fun p => Level.subst (pinnedInfo n).toConstantVal.levelParams us (.param p))

/-- The link reads constructors only. -/
theorem PinLinked.mono {env env' : Env} {n : Name} {ci : ConstantInfo}
    (h : PinLinked env n ci)
    (hc : ∀ x cvj cnP cnF, env'.find? x = some (.ctorInfo cvj cnP cnF) →
      env.find? x = some (.ctorInfo cvj cnP cnF)) :
    PinLinked env' n ci :=
  fun cv mI rP isK rules hci rl hrl hp cvj cnP cnF hf us hus =>
    h cv mI rP isK rules hci rl hrl hp cvj cnP cnF (hc _ _ _ _ hf) us hus

/-- Every stored reserved-basis constant is a copy of the pinned
*declaration*, links its constructors as the pin does, and — where the
layer still carries it — is valued by its direct pin.

The valuation clause makes a reduction's *syntactic* match usable: a
constructor head matched by name denotes the pinned built-in.

**The declaration clause is unconditional** (task #283): a stored
reserved name holds a copy of the pin whatever its kind — which is what
lets `Model.eq_equality` (`ConLeche/Denotes.lean`)
speak about the stored `Eq` without hypothesising its declaration. -/
@[expose] def BasisPinnedTT (env : Env) (cval : Name → (Name → Nat) → Term) : Prop :=
  ∀ (n : Name) (ci : ConstantInfo),
    env.find? n = some ci →
    reservedBasisNames.contains n = true →
    PinCopy ci (pinnedInfo n) ∧ PinLinked env n ci ∧
    ∀ (t : Term) (ψ : Name → Nat),
      pinnedStructT n (pinVal (pinnedInfo n).toConstantVal.levelParams
        ci.toConstantVal.levelParams ψ) = some t →
      cval n ψ = t

/-- The one level parameter the stored `Eq` is at. -/
@[expose] def eqLp (env : Env) : Name :=
  match env.find? eqName with
  | some ci => ci.toConstantVal.levelParams.headD default
  | none => default

/-- **`Eq` is stored**, at the one parameter `eqLp` names. -/
@[expose] def EqStored (env : Env) : Prop :=
  ∃ ci, env.find? eqName = some ci ∧ ci.toConstantVal.levelParams = [eqLp env]

/-- A copy of the `Eq` pin is an inductive's. -/
theorem eqCopy_not_rec {ci : ConstantInfo} (h : PinCopy ci (pinnedInfo eqName))
    (cv : ConstantVal) (mI rP : Nat) (isK : Bool) (rules : List RecRule) :
    ci ≠ .recInfo cv mI rP isK rules := by
  intro hc
  have h1 := h.1
  rw [hc] at h1
  simp only [show pinnedInfo eqName = eqA from rfl, eqA, ConstantInfo.atLps] at h1
  exact nomatch h1

/-- A reserved `Eq` is a copy of the pin, at one parameter. -/
theorem BasisPinnedTT.eqStored {env : Env} {cval : Name → (Name → Nat) → Term}
    (h : BasisPinnedTT env cval) (hs : (env.find? eqName).isSome = true) : EqStored env := by
  obtain ⟨ci, hf⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨-, -, hl⟩ := (h eqName ci hf (by decide)).1
  refine ⟨ci, hf, ?_⟩
  have hl' : ci.toConstantVal.levelParams.length = 1 := hl
  simp only [eqLp, hf]
  match hq : ci.toConstantVal.levelParams, hl' with
  | [p], _ => rfl

/-- `Eq.{l}`'s reading. -/
theorem denote_eqConst {acval : Name → (Name → Nat) → Term} {env : Env} (hs : EqStored env)
    (ψ : Name → Nat) (d : Nat) (l : Level) :
    denote acval env ψ d (.const eqName [l])
      = some (acval eqName (Level.substFn ψ [eqLp env] [l])) := by
  obtain ⟨ci, hf, hl⟩ := hs
  have := denote_const (acval := acval) (φ := ψ) (d := d) (us := [l]) hf (by rw [hl]; rfl)
  rw [hl] at this
  exact this

theorem BasisPinnedTT.empty (cval : Name → (Name → Nat) → Term) :
    BasisPinnedTT Env.empty cval := by
  intro n ci h
  simp [Env.find?, Env.empty] at h

end ConLeche.Verify
