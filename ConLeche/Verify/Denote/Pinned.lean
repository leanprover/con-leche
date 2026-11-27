module

public import ConLeche.Verify.Denote
public import ConLeche.Verify.EnvPreds

public section

/-!
# The pinned basis constants' direct valuations

`pinnedStructT` — what a reserved basis constant denotes to in the
declarative layer, where it denotes to a bare `BConst` built-in, or,
for the one proof among them (`Quot.sound`), to the canonical proof.

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
@[expose] def pinnedStructTAt (lifted : Bool) (n : Name) (ψ : Name → Nat) : Option Term :=
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
  else if n = quotName then some (.const .quot [ψ uN, lifted.toNat])
  else if n = quotMkName then some (.const .quotMk [ψ uN, lifted.toNat])
  else if n = quotLiftName then some (.const .quotLift [ψ uN, ψ vN, lifted.toNat])
  else if n = quotIndName then some (.const .quotInd [ψ uN, lifted.toNat])
  -- a proof: the canonical one, the leaf of every proof (an importer may meet another copy)
  else if n = quotSoundName then some .prf
  else none

/-- The pinned leaves in the released kernel's quotient form. -/
@[expose] def pinnedStructT (n : Name) (ψ : Name → Nat) : Option Term :=
  pinnedStructTAt false n ψ


/-- **A constant is a copy of a pin**: the pin at the constant's own
level-parameter names, distinct and as many as the pin's. -/
@[expose] def PinCopy (ci pin : ConstantInfo) : Prop :=
  ci = pin.atLps ci.toConstantVal.levelParams ∧
  ci.toConstantVal.levelParams.Nodup ∧
  ci.toConstantVal.levelParams.length = pin.toConstantVal.levelParams.length

/-- **The quotient constants whose leaf reads the stored `Quot`'s form**: the type former, its
constructor and its two eliminators (`Quot.sound`'s leaf is the canonical proof). -/
@[expose] def quotFormNames : List Name := [quotName, quotMkName, quotLiftName, quotIndName]

/-- **A quotient constant is read in the stored `Quot`'s form**: at one of `quotFormNames`,
`Quot` is stored, as a copy of its pin in the form `lifted`. -/
@[expose] def QuotForm (env : Env) (n : Name) (lifted : Bool) : Prop :=
  quotFormNames.contains n = true →
    ∃ ciQ, env.find? quotName = some ciQ ∧ PinCopy ciQ (pinnedInfoAt lifted quotName)

/-- Away from `quotFormNames`, the form clause is vacuous. -/
theorem QuotForm.of_not_mem {env : Env} {n : Name} {lifted : Bool}
    (h : quotFormNames.contains n = false) : QuotForm env n lifted :=
  fun h' => absurd (h.symm.trans h') (by decide)

/-- Away from `quotFormNames`, a pinned leaf does not read the form. -/
theorem pinnedStructTAt_of_not_mem {n : Name} (b : Bool) (ψ : Name → Nat)
    (h : quotFormNames.contains n = false) : pinnedStructTAt b n ψ = pinnedStructT n ψ := by
  have h1 : n ≠ quotName := by rintro rfl; exact absurd h (by decide)
  have h2 : n ≠ quotMkName := by rintro rfl; exact absurd h (by decide)
  have h3 : n ≠ quotLiftName := by rintro rfl; exact absurd h (by decide)
  have h4 : n ≠ quotIndName := by rintro rfl; exact absurd h (by decide)
  cases b
  · rfl
  · simp only [pinnedStructT, pinnedStructTAt, h1, h2, h3, h4, ite_false]

/-- **The assignment a copy's leaf reads the pin's parameters at**: the
pin's `i`-th parameter at the copy's `i`-th name. -/
@[expose] def pinVal (pin ps : List Name) (ψ : Name → Nat) : Name → Nat :=
  Level.substFn ψ pin (ps.map Level.param)

/-- **A stored recursor copy links its rules' constructors as its pin
does**: what a `.plain` rule reads of the constructor's parameters, by
name (`recFireComparands`), is the pin's, at every instantiation. -/
@[expose] def PinLinked (env : Env) (n : Name) (ci : ConstantInfo) : Prop :=
  ∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules →
    ∀ rl ∈ rules, RecRule.fire rl = .plain → ∀ cvj cnP cnF T,
      env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF T) →
      ∀ us : List Level, us.length = cv.levelParams.length →
        cvj.levelParams.map (fun p => Level.subst cv.levelParams us (.param p)) =
          (pinnedInfo (RecRule.ctor rl)).toConstantVal.levelParams.map
            (fun p => Level.subst (pinnedInfo n).toConstantVal.levelParams us (.param p))

/-- The link reads constructors only. -/
theorem PinLinked.mono {env env' : Env} {n : Name} {ci : ConstantInfo}
    (h : PinLinked env n ci)
    (hc : ∀ x cvj cnP cnF T, env'.find? x = some (.ctorInfo cvj cnP cnF T) →
      env.find? x = some (.ctorInfo cvj cnP cnF T)) :
    PinLinked env' n ci :=
  fun cv mI rP isK rules hci rl hrl hp cvj cnP cnF T hf us hus =>
    h cv mI rP isK rules hci rl hrl hp cvj cnP cnF T (hc _ _ _ _ _ hf) us hus

/-- Every stored reserved-basis constant is a copy of the pinned
*declaration*, links its constructors as the pin does, and — where the
layer still carries it — is valued by its direct pin.

The valuation clause makes a reduction's *syntactic* match usable: a
constructor head matched by name denotes the pinned built-in.

**The declaration clause is unconditional** (task #283): a stored
reserved name holds a copy of the pin, in one of its forms (`pinnedInfoAt`: `Quot` and
`Quot.sound` have two), whatever its kind; the quotient package's type former, constructor and
eliminators are read in the stored `Quot`'s form (`QuotForm`), and so are their leaves
(`pinnedStructTAt`) — which is what
lets `Model.eq_equality_of` (`ConLeche/Model/OfEnvModelM.lean`)
speak about the stored `Eq` without hypothesising its declaration. -/
@[expose] def BasisPinnedTT (env : Env) (cval : Name → (Name → Nat) → Term) : Prop :=
  ∀ (n : Name) (ci : ConstantInfo),
    env.find? n = some ci →
    reservedBasisNames.contains n = true →
    ∃ lifted, PinCopy ci (pinnedInfoAt lifted n) ∧ QuotForm env n lifted ∧ PinLinked env n ci ∧
    ∀ (t : Term) (ψ : Name → Nat),
      pinnedStructTAt lifted n (pinVal (pinnedInfo n).toConstantVal.levelParams
        ci.toConstantVal.levelParams ψ) = some t →
      cval n ψ = t

/-- A basis constant other than `Quot` and `Quot.sound` has one form. -/
theorem pinnedInfoAt_of_ne {n : Name} (b : Bool) (hq : n ≠ quotName) (hs : n ≠ quotSoundName) :
    pinnedInfoAt b n = pinnedInfo n := by
  cases b
  · rfl
  · simp only [pinnedInfo, pinnedInfoAt, hq, hs, ite_false]

/-- Both forms of a basis constant have its level parameters. -/
theorem pinnedInfoAt_lps (b : Bool) (n : Name) :
    (pinnedInfoAt b n).toConstantVal.levelParams = (pinnedInfo n).toConstantVal.levelParams := by
  by_cases hq : n = quotName
  · subst hq; cases b <;> rfl
  by_cases hs : n = quotSoundName
  · subst hs; cases b <;> rfl
  rw [pinnedInfoAt_of_ne b hq hs]

/-- **Which form a copy of `Quot` or `Quot.sound` is in**: whether its universe is the lifted
`max 1 u` (lean4#15023), read where the two forms differ: `Quot`'s result sort, `Quot.sound`'s
`Eq` level.  A renaming of level parameters keeps the `max`. -/
@[expose] def pinFormOf : ConstantInfo → Bool
  | .indInfo cv _ =>
    match cv.type with
    | .forallE _ (.forallE _ (.sort (.max _ _))) => true
    | _ => false
  | .axiomInfo cv =>
    match cv.type with
    | .forallE _ (.forallE _ (.forallE _ (.forallE _ (.forallE _
        (.app (.app (.app (.const _ [.max _ _]) _) _) _))))) => true
    | _ => false
  | _ => false

/-- **A constant copies one form of its pin**: the two forms of `Quot` and of `Quot.sound` have no
common copy, and every other pin has one form. -/
theorem PinCopy.form_unique {c : ConstantInfo} {b b' : Bool} {n : Name}
    (h : PinCopy c (pinnedInfoAt b n)) (h' : PinCopy c (pinnedInfoAt b' n)) :
    pinnedInfoAt b n = pinnedInfoAt b' n := by
  have hl : c.toConstantVal.levelParams.length = 1 → ∃ q, c.toConstantVal.levelParams = [q] :=
    fun hl => match c.toConstantVal.levelParams, hl with | [q], _ => ⟨q, rfl⟩
  by_cases hq : n = quotName
  · subst hq
    obtain ⟨q, hq⟩ := hl (by rw [h.2.2]; cases b <;> rfl)
    have e := congrArg pinFormOf (h.1.symm.trans h'.1)
    rw [hq] at e
    cases b <;> cases b' <;> first
      | rfl
      | (change true = false at e; cases e)
      | (change false = true at e; cases e)
  by_cases hs : n = quotSoundName
  · subst hs
    obtain ⟨q, hq⟩ := hl (by rw [h.2.2]; cases b <;> rfl)
    have e := congrArg pinFormOf (h.1.symm.trans h'.1)
    rw [hq] at e
    cases b <;> cases b' <;> first
      | rfl
      | (change true = false at e; cases e)
      | (change false = true at e; cases e)
  rw [pinnedInfoAt_of_ne b hq hs, pinnedInfoAt_of_ne b' hq hs]

/-- **A stored basis constant other than `Quot` and `Quot.sound` is a copy of its one pin.** -/
theorem BasisPinnedTT.copy {env : Env} {cval : Name → (Name → Nat) → Term}
    (h : BasisPinnedTT env cval) {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hres : reservedBasisNames.contains n = true) (hq : n ≠ quotName) (hs : n ≠ quotSoundName) :
    PinCopy ci (pinnedInfo n) := by
  obtain ⟨b, hc, -⟩ := h n ci hf hres
  rwa [pinnedInfoAt_of_ne b hq hs] at hc

/-- A stored basis constant has its pin's level-parameter count. -/
theorem BasisPinnedTT.lps_length {env : Env} {cval : Name → (Name → Nat) → Term}
    (h : BasisPinnedTT env cval) {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hres : reservedBasisNames.contains n = true) :
    ci.toConstantVal.levelParams.length = (pinnedInfo n).toConstantVal.levelParams.length := by
  obtain ⟨b, ⟨-, -, hl⟩, -⟩ := h n ci hf hres
  rw [hl, pinnedInfoAt_lps]

/-- A stored `Nat`, `Nat.zero`, `Nat.succ` is a copy of its pin, so of its pin's kind. -/
theorem BasisPinnedTT.natKinds {env : Env} {cval : Name → (Name → Nat) → Term}
    (h : BasisPinnedTT env cval) : NatKinds env := by
  refine ⟨fun c hf => ?_, fun c hf => ?_, fun c hf => ?_⟩
  · rw [(h.copy hf (by decide) (by decide) (by decide)).1]; exact ⟨_, _, rfl⟩
  · rw [(h.copy hf (by decide) (by decide) (by decide)).1]; exact ⟨_, _, _, _, rfl⟩
  · rw [(h.copy hf (by decide) (by decide) (by decide)).1]; exact ⟨_, _, _, _, rfl⟩

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
  simp only [show pinnedInfo eqName = eqI from rfl, eqI, ConstantInfo.atLps] at h1
  exact nomatch h1

/-- A reserved `Eq` is a copy of the pin, at one parameter. -/
theorem BasisPinnedTT.eqStored {env : Env} {cval : Name → (Name → Nat) → Term}
    (h : BasisPinnedTT env cval) (hs : (env.find? eqName).isSome = true) : EqStored env := by
  obtain ⟨ci, hf⟩ := Option.isSome_iff_exists.mp hs
  have hl := h.lps_length hf (by decide)
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
