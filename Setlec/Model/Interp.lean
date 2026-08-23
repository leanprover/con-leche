import Setlec.Kernel.TypeChecker
import Setlec.Kernel.Checker
import Setlec.Verify.Abstract
import Setlec.SetTheory.Basic
import Setlec.Verify.Level
import Setlec.Verify.Shift
import Setlec.Verify.Subst
import Setlec.Verify.EnvWF
import Setlec.Verify.Leaves
import Setlec.Model.BasisVal
import Setlec.Model.IndModel

/-!
# Interpretation of expressions in the set model

`interpExpr cval env φ d ρ e` maps a kernel expression to an element of
the set-theoretic universe `V`, where

* `cval` values the constants (level-polymorphically: each constant is a
  function of the level-parameter assignment),
* `φ` assigns the universe level parameters,
* `d` is the current binder depth,
* `ρ : Nat → V` values the free variables (`fvar idx …` ↦ `ρ idx`; the
  annotation at an `fvar` leaf is *not* read).

It is partial (`Option`): unsupported expression forms are uninterpreted,
and it grows in lockstep with the checker.

A constant `const n us` is valued at the assignment sending the
constant's own parameters to the evaluation of `us` under `φ` (and other
names to `φ` itself — `Level.substFn`); an `EnvModel`'s `val_params`
field records that the valuation only reads its own parameters, so the
tail is irrelevant.

A `∀`-type is interpreted by opening the binder at index `d` — exactly as
the checker does — and forming the dependent product `SetTheory.pi` over
the domain; the Prop/Type classifier `pi` needs is the evaluation of the
binder's stored codomain-sort annotation (`BinderMeta.cod`) — unannotated
binders are uninterpreted.  `AnnotOk` states that annotations are
*truthful* (each fibre lands in the annotated universe, hereditarily);
it is established once by the annotation pass (`annotate_sound`) and is
a hypothesis of the soundness theorems.

`FvarsOk` states the typing assumptions about the (implicit) local
context.  `EnvModel` packages a model of a whole environment.
-/

set_option linter.unusedVariables false
set_option linter.defProp false

namespace Setlec

variable (V : Type u) [SetTheory V]

open SetTheory

/-- Update a valuation at one index. -/
def updV (ρ : Nat → V) (d : Nat) (x : V) : Nat → V :=
  fun i => if i = d then x else ρ i

/-- The value of a `Nat` literal: the `Nat.succ` value iterated on the
`Nat.zero` value. -/
def natLitVal (zv sv : V) : Nat → V
  | 0 => zv
  | n + 1 => SetTheory.app sv (natLitVal zv sv n)

/-- The value of the character-list part of a string literal's
constructor form (`strLitToConstructor`): the `List.cons.{0} Char`
value folded over the characters' `Char.ofNat`-of-numeral values, ending
in the `List.nil.{0} Char` value. -/
def charListVal (nilV consV ofNatV zv sv : V) : List Char → V
  | [] => nilV
  | c :: cs =>
    SetTheory.app
      (SetTheory.app consV (SetTheory.app ofNatV (natLitVal V zv sv c.toNat)))
      (charListVal nilV consV ofNatV zv sv cs)

/-- The stored level-parameter list of a constant (`[]` when absent) —
what the interpretation of a string literal instantiates the
`List.nil`/`List.cons` valuations with (their one parameter at level
`0`, exactly as the `.const` case does on the literal's constructor
form). -/
def Env.levelParamsAt (env : Env) (n : Name) : List Name :=
  match env.find? n with
  | some ci => ci.toConstantVal.levelParams
  | none => []

/-- The value of a `String` literal: the interpretation of its
constructor form (`strLitToConstructor`), written out value-level —
each constant valued exactly as the interpretation's `.const` clause
values it on that form.  Meaningful under `strLitSupported`. -/
def strLitVal (cval : ConstVal V) (env : Env) (φ : Name → Nat) (s : String) : V :=
  SetTheory.app (cval stringOfListName (Level.substFn φ [] []))
    (charListVal V
      (SetTheory.app
        (cval listNilName
          (Level.substFn φ (env.levelParamsAt listNilName) [.zero]))
        (cval charName (Level.substFn φ [] [])))
      (SetTheory.app
        (cval listConsName
          (Level.substFn φ (env.levelParamsAt listConsName) [.zero]))
        (cval charName (Level.substFn φ [] [])))
      (cval charOfNatName (Level.substFn φ [] []))
      (cval natZeroName (Level.substFn φ [] []))
      (cval natSuccName (Level.substFn φ [] []))
      s.toList)

/-- Interpret an expression under constant valuation `cval`, level
assignment `φ`, binder depth `d` and free-variable valuation `ρ`. -/
def interpExpr (cval : ConstVal V) (env : Env) (φ : Name → Nat) :
    (d : Nat) → (ρ : Nat → V) → Expr → Option V
  | _, _, .sort u => some (univ (u.eval φ))
  | _, ρ, .fvar idx _ _ => some (ρ idx)
  | _, _, .const n us =>
    match env.find? n with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        some (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
      else none
    | none => none
  | d, ρ, .forallE n ty body m =>
    match m.cod with
    | none => none
    | some v =>
      match interpExpr cval env φ d ρ ty with
      | none => none
      | some A => some (pi (v.eval φ) A fun x =>
          (interpExpr cval env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty)
  | d, ρ, .lam n ty body m =>
    match m.cod with
    | none => none
    | some v =>
      match interpExpr cval env φ d ρ ty with
      | none => none
      | some A => some (SetTheory.lam (v.eval φ) A fun x =>
          (interpExpr cval env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty)
  | d, ρ, .app f a =>
    match interpExpr cval env φ d ρ f, interpExpr cval env φ d ρ a with
    | some vf, some va => some (SetTheory.app vf va)
    | _, _ => none
  | d, ρ, .letE n ty val body =>
    -- a `let` is its body at the value: open the binder at index `d`
    -- (exactly as the binder clauses do) and extend the valuation with
    -- the value's interpretation; the `fvar` annotation is not read, so
    -- the substitution lemma (`interp_beta`) identifies this with the
    -- interpretation of the zeta reduct `body[val]`
    match interpExpr cval env φ d ρ val with
    | none => none
    | some xv =>
      interpExpr cval env φ (d + 1) (updV V ρ d xv)
        (body.instantiate1 (.fvar d n ty))
  | d, ρ, .proj _ i e =>
    match interpExpr cval env φ d ρ e with
    | some ve =>
      if i = 0 then some (sfst ve) else if i = 1 then some (ssnd ve) else none
    | none => none
  | _, _, .lit (.natVal n) =>
    -- guarded exactly like the checker's literal paths; the zero/succ
    -- values match the `.const` case's given the guard's shape facts
    if natLitSupported env then
      some (natLitVal V (cval natZeroName (Level.substFn φ [] []))
        (cval natSuccName (Level.substFn φ [] [])) n)
    else none
  | _, _, .lit (.strVal s) =>
    -- the interpretation of the literal's constructor form
    -- (`strLitToConstructor`), written out value-level (`strLitVal`)
    if strLitSupported env then some (strLitVal V cval env φ s)
    else none
  | _, _, _ => none
termination_by _ _ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Truthfulness of the codomain-sort annotations: every `∀`-subterm is
annotated, and over every member of the domain's interpretation the
(defined) fibre lands in the annotated universe, hereditarily; `lam`
bodies are covered so that the invariant survives beta reduction. -/
def AnnotOk (cval : ConstVal V) (env : Env) (φ : Name → Nat) :
    (d : Nat) → (ρ : Nat → V) → Expr → Prop
  | d, ρ, .forallE n ty body m =>
    AnnotOk cval env φ d ρ ty ∧
    (∃ v, m.cod = some v) ∧
    ∀ x A, interpExpr V cval env φ d ρ ty = some A → x ∈ˢ A →
      AnnotOk cval env φ (d + 1) (updV V ρ d x) (body.instantiate1 (.fvar d n ty)) ∧
      ∀ v, m.cod = some v →
        ∃ w, interpExpr V cval env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty)) = some w ∧
          w ∈ˢ univ (v.eval φ)
  | d, ρ, .lam n ty body m =>
    AnnotOk cval env φ d ρ ty ∧
    (∃ v, m.cod = some v) ∧
    ∀ x A, interpExpr V cval env φ d ρ ty = some A → x ∈ˢ A →
      AnnotOk cval env φ (d + 1) (updV V ρ d x) (body.instantiate1 (.fvar d n ty)) ∧
      ∀ v, m.cod = some v →
        ∃ w B, interpExpr V cval env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty)) = some w ∧
          w ∈ˢ B ∧ B ∈ˢ univ (v.eval φ)
  | d, ρ, .app f a =>
    AnnotOk cval env φ d ρ f ∧ AnnotOk cval env φ d ρ a ∧
    ∃ vf va vE A B, interpExpr V cval env φ d ρ f = some vf ∧
      interpExpr V cval env φ d ρ a = some va ∧
      vf ∈ˢ pi vE A B ∧ va ∈ˢ A ∧ ∀ x, x ∈ˢ A → B x ∈ˢ univ vE
  | d, ρ, .letE n ty val body =>
    -- the value interprets, and the body opened at the value's
    -- interpretation is truthful — exactly what `AnnotOk_beta` needs to
    -- transport truthfulness onto the zeta reduct `body[val]`
    AnnotOk cval env φ d ρ ty ∧
    AnnotOk cval env φ d ρ val ∧
    ∃ xv, interpExpr V cval env φ d ρ val = some xv ∧
      AnnotOk cval env φ (d + 1) (updV V ρ d xv)
        (body.instantiate1 (.fvar d n ty))
  | d, ρ, .proj _ i e =>
    AnnotOk cval env φ d ρ e ∧ i < 2 ∧
    ∃ ve u v A Bf, interpExpr V cval env φ d ρ e = some ve ∧
      ve ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v
  | _, _, _ => True
termination_by d ρ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- The typing assumptions about the implicit local context, as
conditions on the free-variable leaf closure: every leaf (including
those inside annotations, hereditarily) is bounded by the depth, its
annotation's annotations are truthful, and its valuation is a member of
its annotated type's interpretation. -/
def FvarsOk (cval : ConstVal V) (env : Env) (φ : Name → Nat) (d : Nat) (ρ : Nat → V)
    (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ AnnotOk V cval env φ d ρ l.2.2 ∧
    ∃ T, interpExpr V cval env φ d ρ l.2.2 = some T ∧ ρ l.1 ∈ˢ T

/-- The canonical valuation for closed terms. -/
def rho0 : Nat → V := fun _ => SetTheory.empty

/-- Interpretation of a closed expression (as they appear in declarations). -/
def interpClosed (cval : ConstVal V) (env : Env) (φ : Name → Nat) (e : Expr) : Option V :=
  interpExpr V cval env φ 0 (rho0 V) e

/-- Values fitting an opened `∀`-telescope: each value is a member of
the interpretation of the corresponding (progressively instantiated)
domain; `d'`, `ρ'`, `rest` describe the fully opened residual body. -/
inductive TeleFit (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (φ : Name → Nat) :
    Nat → (Nat → V) → Expr → List V → Nat → (Nat → V) → Expr → Prop
  | nil {d ρ e} : TeleFit V cval env φ d ρ e [] d ρ e
  | cons {d ρ n ty body m x xs d' ρ' rest A} :
      interpExpr V cval env φ d ρ ty = some A →
      x ∈ˢ A →
      TeleFit V cval env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty)) xs d' ρ' rest →
      TeleFit V cval env φ d ρ (.forallE n ty body m) (x :: xs) d' ρ' rest


/-- Values fitting a `∀`-telescope along an *expression* spine: each
argument expression interprets to a member of the corresponding domain,
and the telescope is instantiated one argument at a time (mirroring the
iota certificates' walk).  The last index is the fully instantiated
residual body. -/
inductive TeleFitI (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (φ : Name → Nat)
    (d : Nat) (ρ : Nat → V) : Expr → List Expr → List V → Expr → Prop
  | nil {e} : TeleFitI V cval env φ d ρ e [] [] e
  | cons {n ty body m arg args x xs A rest} :
      interpExpr V cval env φ d ρ ty = some A →
      interpExpr V cval env φ d ρ arg = some x →
      x ∈ˢ A →
      Expr.fvarsBelow d body →
      Expr.WScoped d arg →
      arg.looseBVarsBounded 0 = true →
      AnnotOk V cval env φ d ρ arg →
      TeleFitI V cval env φ d ρ (body.instantiate1 arg) args xs rest →
      TeleFitI V cval env φ d ρ (.forallE n ty body m) (arg :: args) (x :: xs)
        rest


/-- A spine of free variables (indices below the frame) whose valuation
values are the given list (shared with the iota-walk machinery in
`Setlec/Model/IotaWalk.lean`, which holds its lemmas). -/
def FvarSpine {W : Type u} (D : Nat) (ρ : Nat → W) :
    List Expr → List W → Prop
  | [], [] => True
  | a :: as, v :: vs =>
    (∃ i n ty, a = .fvar i n ty ∧ i < D ∧ ρ i = v) ∧
    FvarSpine D ρ as vs
  | _, _ => False

/-- Close a λ-tower over opened frame variables: each variable
(outermost first, frame-ordered) becomes a `λ`-binder whose domain is
the variable's own type annotation, paired with the given binder
metadata; the variable is abstracted from everything inside.  Inverse
of the interpretation's own binder opening when the variables sit at
consecutive indices starting at the interpretation depth. -/
def closeLamsAt : List (Expr × BinderMeta) → Expr → Expr
  | [], b => b
  | (.fvar i nm ty, m) :: rest, b =>
    .lam nm ty ((closeLamsAt rest b).abstract1 i) m
  | (_, _) :: rest, b => closeLamsAt rest b

/-- The canonical iota left-hand side of a fireable recursor rule `r`
of recursor `n` (stored value `cv`, non-index prefix `rP`), as a
closed λ-tower: the binders are the recursor's non-index prefix
(opened on its stored type at frame indices `0..rP-1`) followed by the
constructor's fields (opened on the stored constructor type at
`rP..rP+nfields-1`, parameters instantiated at the leading prefix
variables for a `.plain` rule and at the stored pin expressions for a
`.nested` one), with binder metadata copied from the stored rule
right-hand side; the body applies the recursor to the prefix
variables, the constructor's canonical index tuple (the trailing
arguments of its instantiated residual type), and the constructor
spine.  `RecRulesOk` states that its interpretation **equals** the
rule right-hand side's — the total λ-equality of function graphs that
the iota step's soundness consumes by pure `app` congruence. -/
def ruleLhsAux (n : Name) (cv : ConstantVal) (rP : Nat) (r : RecRule)
    (fvsP : List Expr) (usC : List Level) (cargs : List Expr)
    (cty : Expr) : Option (List (Expr × BinderMeta) × Expr) :=
  match Expr.instPisAt cargs cty with
  | none => none
  | some (cdoms, crest) =>
    match openPisAtFvars (RecRule.nfields r) crest rP with
    | none => none
    | some (xFvs, crest2) =>
      match (RecRule.rhs r).stripLams (rP + RecRule.nfields r) with
      | none => none
      | some (rbs, rbody) =>
        some ((fvsP ++ xFvs).zip (rbs.map (·.2.2)),
          Expr.mkAppN (.const n (cv.levelParams.map .param))
            (fvsP ++ crest2.getAppArgs.drop (RecRule.ctorParams r) ++
              [Expr.mkAppN (.const (RecRule.ctor r) usC) (cargs ++ xFvs)]))

/-- The frame/body decomposition behind `ruleLhs` (see the
construction's docstring on `ruleLhsAux`): the closing frame paired
with the recursor-redex body, before `closeLamsAt` assembles the
tower.  `RecRulesOk` is stated against this decomposition so consumers
recover the components deterministically. -/
def ruleLhsParts (n : Name) (cv : ConstantVal) (rP : Nat) (r : RecRule)
    (cvj : ConstantVal) : Option (List (Expr × BinderMeta) × Expr) :=
  match openPisAtFvars rP cv.type 0 with
  | none => none
  | some (fvsP, rest0) =>
    match RecRule.fire r with
    | .plain =>
      ruleLhsAux n cv rP r fvsP (cvj.levelParams.map Level.param)
        (fvsP.take (RecRule.ctorParams r)) cvj.type
    | .nested lvls pins =>
      ruleLhsAux n cv rP r fvsP lvls
        (pins.map fun p => Expr.instSpine fvsP (rP - 1) p)
        (cvj.type.instantiateLevelParams cvj.levelParams lvls)
    | .inert => none

/-- The canonical iota left-hand side λ-tower itself (documentation
form; the contract and its consumers work with `ruleLhsParts`). -/
def ruleLhs (n : Name) (cv : ConstantVal) (rP : Nat) (r : RecRule)
    (cvj : ConstantVal) : Option Expr :=
  (ruleLhsParts n cv rP r cvj).map fun p => closeLamsAt p.1 p.2

/-- Well-formedness of a closing frame over a body: the variables sit
at consecutive indices starting at `d`; each annotation is scoped
below its own index, free of loose bvars, and paired with a
codomain-sort annotation; and each variable is mentioned
*consistently* (same name and annotation) by the body and by every
later variable's annotation — what the abstraction/instantiation
roundtrip of `closeLamsAt` needs (`Setlec/Model/RuleTower.lean`). -/
def FrameWf : Nat → List (Expr × BinderMeta) → Expr → Prop
  | d, [], bL => Expr.WScoped d bL ∧ bL.looseBVarsBounded 0 = true
  | d, (fv, m) :: rest, bL =>
    (∃ nm ty, fv = .fvar d nm ty ∧ Expr.WScoped d ty ∧
      ty.looseBVarsBounded 0 = true ∧
      Expr.fvarConsistent d nm ty bL ∧
      ∀ p ∈ rest, Expr.fvarConsistent d nm ty (Expr.fvarTypeD p.1)) ∧
    FrameWf (d + 1) rest bL

/-- The **total λ-equality** of every stored fireable recursor rule
(task #58): the interpretation of the rule's canonical left-hand side
λ-tower (`ruleLhs` — the recursor applied, under the telescope of its
non-index prefix and the constructor's fields, to the prefix, the
canonical index tuple and the constructor spine) **equals** the
interpretation of the stored rule right-hand side, *as sets*, at every
level assignment — together with the tower's and the rhs's truthful
annotations.  Two dependent-function graphs over interp-equal domain
chains are equal iff they agree on fitting inputs (off-domain both
apply to canonical junk; under the Prop collapse both are the proof
point), which is exactly what the checked `_model.iota_j` theorem
supplies at install; the iota step's soundness consumes the equality
by pure `app` congruence plus the tower's own beta fold
(`closeLamsAt_fold`).  Basis blocks discharge this from the
hand-written values; modeled blocks from their checked `_model`
theorems.  `.inert` rules never fire and carry no obligation. -/
def RecRulesOk (env : Env) (val : ConstVal V) : Prop :=
  ∀ n cv mI rP rules,
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ r ∈ rules,
      (∀ ψ : Name → Nat, AnnotOk V val env ψ 0 (rho0 V) (RecRule.rhs r)) ∧
      -- a fireable rule's prefix fits under the major's position, and a
      -- canonical rule's constructor parameters sit inside the prefix
      -- (part of `Expr.recRulePlain` resp. `nestedRuleShape`, whose
      -- install-time computation backs the stored flag)
      (RecRule.fire r ≠ .inert → rP ≤ mI) ∧
      (RecRule.fire r = .plain → RecRule.ctorParams r ≤ rP) ∧
      (∀ lvls pins, RecRule.fire r = .nested lvls pins →
        pins.length = RecRule.ctorParams r) ∧
      ∀ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF) →
        RecRule.fire r ≠ .inert →
        ∃ fvms bL, ruleLhsParts n cv rP r cvj = some (fvms, bL) ∧
          FrameWf 0 fvms bL ∧
          fvms.length = rP + RecRule.nfields r ∧
          (closeLamsAt fvms bL).constsResolve env = true ∧
          ∀ ψ : Name → Nat,
            AnnotOk V val env ψ 0 (rho0 V) (closeLamsAt fvms bL) ∧
            ∃ Rv, interpClosed V val env ψ (closeLamsAt fvms bL) = some Rv ∧
              interpClosed V val env ψ (RecRule.rhs r) = some Rv

theorem RecRulesOk.empty (val : ConstVal V) :
    RecRulesOk V Env.empty val := by
  intro n cv mI rP rules h
  simp [Env.find?, Env.empty] at h

/-- `ProjOk` is preserved by a fresh extension, given the head's own
obligation (vacuous unless the head is a native entry). -/
theorem ProjOk.cons {env : Env} {c₀ : ConstantInfo}
    (h : ProjOk env) (hfresh : env.find? c₀.name = none)
    (hhead : ∀ entry, c₀ = .projInfo entry → entry.native = true →
      (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA) :
    ProjOk ⟨c₀ :: env.consts⟩ := by
  have keep : ∀ {s : Name} {X : ConstantInfo}, env.find? s = some X →
      Env.find? ⟨c₀ :: env.consts⟩ s = some X := by
    intro s X hs
    rw [Env.find?_cons, if_neg ?_]
    · exact hs
    · intro he
      rw [← he, hfresh] at hs
      exact nomatch hs
  intro n entry hf hnat
  rw [Env.find?_cons] at hf
  split at hf
  · next hn =>
    obtain hceq := Option.some.inj hf
    obtain ⟨hpin, h1, h2⟩ := hhead entry hceq hnat
    exact ⟨hpin, keep h1, keep h2⟩
  · next hn =>
    obtain ⟨hpin, h1, h2⟩ := h n entry hf hnat
    exact ⟨hpin, keep h1, keep h2⟩

/-- `ProjOk` only reads lookups, so it transports across any
environment correspondence that at most swaps stored recursors' rule
lists. -/
theorem ProjOk.env_swap {env₁ env₂ : Env}
    (hcorr : ∀ n : Name, env₂.find? n = env₁.find? n ∨
      ∃ cv mI rP rules₁ rules₂,
        env₁.find? n = some (.recInfo cv mI rP rules₁) ∧
        env₂.find? n = some (.recInfo cv mI rP rules₂))
    (h : ProjOk env₁) : ProjOk env₂ := by
  intro n entry hf hnat
  have hf₁ : env₁.find? n = some (.projInfo entry) := by
    rcases hcorr n with heq | ⟨cv, mI, rP, rules₁, rules₂, h₁, h₂⟩
    · rw [← heq]; exact hf
    · rw [h₂] at hf
      exact nomatch (Option.some.inj hf)
  obtain ⟨hpin, h1, h2⟩ := h n entry hf₁ hnat
  have move : ∀ {s : Name} {X : ConstantInfo},
      (∀ cv mI rP rules, X ≠ .recInfo cv mI rP rules) →
      env₁.find? s = some X → env₂.find? s = some X := by
    intro s X hnr hs
    rcases hcorr s with heq | ⟨cv, mI, rP, rules₁, rules₂, h₁, h₂⟩
    · rw [heq]; exact hs
    · rw [h₁] at hs
      exact absurd (Option.some.inj hs).symm (hnr cv mI rP rules₁)
  exact ⟨hpin, move (fun _ _ _ _ h => by simp [psigmaA] at h) h1,
    move (fun _ _ _ _ h => by simp [psigmaMkA] at h) h2⟩


/-- The semantic eta law of an eta-capable stored structure: every
member of the interpreted type (fitting the type former's parameter
telescope) is the constructor model's value applied to the projection
models'.  Derived at install from the checked `T._model.eta` theorem
(`eta_rule_fold`); the pair-eta rule's soundness consumes it. -/
def EtaLaw (env : Env) (val : ConstVal V) (T : Name) (cvT : ConstantVal)
    (caps : IndCaps) : Prop :=
  ∀ (φ' : Name → Nat) (us : List Level) (ps : List V) (x : V)
    (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V) (rest : Expr),
    ps.length = caps.etaParams →
    x ∈ˢ SpineFold V (val T (Level.substFn φ' cvT.levelParams us)) ps →
    TeleFit V val env φ' d₁ ρ₁
      (cvT.type.instantiateLevelParams cvT.levelParams us) ps d₂ ρ₂
      rest →
    x = SpineFold V
      (val (caps.etaCtor.str "_model")
        (Level.substFn φ' cvT.levelParams us))
      (ps ++ (List.range caps.etaFields).map fun j =>
        SpineFold V (val (projModelName T j)
          (Level.substFn φ' cvT.levelParams us)) (ps ++ [x]))

/-- The semantic unit-like law of a unit-like stored family: any two
members of the interpreted type are equal.  Derived at install from
the checked `T._model.unitlike` theorem (`unit_rule_fold`); the
proof-irrelevance rule's soundness consumes it. -/
def UnitLaw (env : Env) (val : ConstVal V) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ (φ' : Name → Nat) (us : List Level) (ps : List V) (x y : V)
    (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V) (rest : Expr),
    ps.length = caps.unitParams →
    x ∈ˢ SpineFold V (val T (Level.substFn φ' cvT.levelParams us)) ps →
    y ∈ˢ SpineFold V (val T (Level.substFn φ' cvT.levelParams us)) ps →
    TeleFit V val env φ' d₁ ρ₁
      (cvT.type.instantiateLevelParams cvT.levelParams us) ps d₂ ρ₂
      rest →
    x = y

/-- **The artifact linkage.**  Every constant the *modeled* install
path creates is valued by its `_model` companion; this clause records
that assignment.

*Why it exists.*  The preprocessor proves its certificate theorems over
`_model` names — it cannot say anything about the opaque public
constants — so when a later modeled block's rules mention an
**earlier** artifact-installed constant, the rename-and-transport step
that checks them needs `val T = val (T._model)` for that earlier `T`.

*Lifetime.*  Per constant, from its artifact install to the end of the
stream — **not** group-local: models are built out of earlier models,
so block 500 may consume block 3's linkage.

*Why it is free to carry.*  It records the valuation assignment the
modeled install *makes* (`val T := val (T._model)`), not an extra
obligation on anybody.

*End of life.*  Vacuous for basis blocks (reserved names) and for
directly installed blocks (no companion exists, so the premise fails);
its footprint shrinks as directly recognised classes displace
`lean-inductive-models`, and the clause is deletable once the last
modeled class is gone.

The companion's *existence* is a **premise**, not a conclusion: an
artifact-installed constant has one, so this is exactly as strong as an
unconditional bridge there, while a directly installed constant — which
has no companion by construction (`directNoModel`) — owes nothing. -/
def ModeledOk (env : Env) (val : ConstVal V) : Prop :=
  (∀ n cv cnP cnF, env.find? n = some (.ctorInfo cv cnP cnF) →
    reservedBasisNames.contains n = false →
    (env.find? (n.str "_model")).isSome = true →
    ∀ ψ : Name → Nat, val n ψ = val (n.str "_model") ψ) ∧
  (∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps) (j : Nat)
      (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    env.find? T = some (.indInfo cvT capsT) →
    env.find? (projFnName T j) = some (.recInfo cv mI rP rules) →
    (env.find? (projModelName T j)).isSome = true →
    ∀ ψ : Name → Nat,
      val (projFnName T j) ψ = val (projModelName T j) ψ) ∧
  -- The capability laws below are **provenance-abstract** by design:
  -- they say what the reduction rules consume and nothing about how the
  -- family was built, so a basis pin, an artifact check and a direct
  -- construction all discharge them the same way (the `IndOk` pattern,
  -- and the move `RecRulesOk` made in task #58).  `UnitLaw` is already
  -- free of `_model` names; `EtaLaw` still reaches the constructor and
  -- the projections through theirs, which is why the direct install
  -- declares `eta := false` — see DESIGN.md.
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    reservedBasisNames.contains T = false →
    (env.find? (caps.etaCtor.str "_model")).isSome = true ∧
    (∀ j, j < caps.etaFields →
      (env.find? (projModelName T j)).isSome = true) ∧
    EtaLaw V env val T cvT caps) ∧
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.unitlike = true →
    reservedBasisNames.contains T = false →
    UnitLaw V env val T cvT caps) ∧
  -- a stored projection function's parent is stored (blocks install the
  -- type former first); monotone, so extensions preserve it for free
  (∀ (T : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
    env.find? (projFnName T j) = some (.recInfo cv mI rP rules) →
    (env.find? T).isSome = true)

/-- A stored structural-Nat operation's semantic certificate
(established at install by `certifyNatEqs` and the pinned-shape
checks): its literal fast-path guard holds, and it satisfies its
defining recurrence equations semantically — at every level
assignment, for every valuation of the equations' two free variables
by members of the `Nat` value.  `reduceNat`'s soundness consumes the
equations by meta-level induction on the literal. -/
def NatOpsOk (env : Env) (val : ConstVal V) : Prop :=
  ∀ c ∈ natOpNames, ∀ cv v hint, env.find? c = some (.defnInfo cv v hint) →
    natOpGuard env c = true ∧
    ∀ eq ∈ natOpEquations 0 c, ∀ (ψ : Name → Nat) (x y : V),
      (∀ T, interpExpr V val env ψ 2 (rho0 V) (.const natName []) = some T →
        x ∈ˢ T ∧ y ∈ˢ T) →
      interpExpr V val env ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y) eq.1 =
      interpExpr V val env ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y) eq.2

theorem NatOpsOk.empty (val : ConstVal V) : NatOpsOk V Env.empty val := by
  intro c hc cv v hint h
  simp [Env.find?, Env.empty] at h

/-- The value-level clauses of a pin-certified WF-recursive operation
`c` at valuation `val`, mirroring the pinned certificate statements
(`divModCertStmts`) clause for clause: `ble`-guarded recurrences over
the already-certified ground operations' values, with the base cases
on the guard's `false` value.  Purely value-level — no expression
interpretation — so environment transports only touch the guard/lookup
side of `DivModOk`. -/
def DivModClauses (val : ConstVal V) (c : Name) (ψ : Name → Nat)
    (x y : V) : Prop :=
  let vT := val boolTrueName ψ
  let vF := val boolFalseName ψ
  let one : V := app (val natSuccName ψ) (val natZeroName ψ)
  let two : V := app (val natSuccName ψ) one
  let ble2 : V → V → V := fun a b => app (app (val natBleName ψ) a) b
  let op2 : V → V → V := fun a b => app (app (val c ψ) a) b
  let sub2 : V → V → V := fun a b => app (app (val natSubName ψ) a) b
  let add2 : V → V → V := fun a b => app (app (val natAddName ψ) a) b
  let mul2 : V → V → V := fun a b => app (app (val natMulName ψ) a) b
  let div2 : V → V → V := fun a b => app (app (val natDivName ψ) a) b
  let mod2 : V → V → V := fun a b => app (app (val natModName ψ) a) b
  if c = natGcdName then
    (ble2 one x = vT → op2 x y = op2 (mod2 y x) x) ∧
    (ble2 one x = vF → op2 x y = y)
  else if c = natShiftLeftName then
    (ble2 one y = vT → op2 x y = op2 (mul2 two x) (sub2 y one)) ∧
    (ble2 one y = vF → op2 x y = x)
  else if c = natShiftRightName then
    (ble2 one y = vT → op2 x y = div2 (op2 x (sub2 y one)) two) ∧
    (ble2 one y = vF → op2 x y = x)
  else if c = natLog2Name then
    (ble2 two x = vT →
      app (val c ψ) x =
        app (val natSuccName ψ) (app (val c ψ) (div2 x two))) ∧
    (ble2 two x = vF → app (val c ψ) x = val natZeroName ψ)
  else if c = natLandName then
    (ble2 one x = vT →
      op2 x y = add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mul2 (mod2 x two) (mod2 y two))) ∧
    (ble2 one x = vF → op2 x y = val natZeroName ψ)
  else if c = natLorName then
    (ble2 one x = vT →
      op2 x y = add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (sub2 (add2 (mod2 x two) (mod2 y two))
          (mul2 (mod2 x two) (mod2 y two)))) ∧
    (ble2 one x = vF → op2 x y = y)
  else if c = natXorName then
    (ble2 one x = vT →
      op2 x y = add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mod2 (add2 (mod2 x two) (mod2 y two)) two)) ∧
    (ble2 one x = vF → op2 x y = y)
  else
    -- `Nat.div`/`Nat.mod`
    (ble2 y x = vT → ble2 one y = vT →
     op2 x y =
       (if c = natDivName then app (val natSuccName ψ) (op2 (sub2 x y) y)
        else op2 (sub2 x y) y)) ∧
    (ble2 y x = vF →
     op2 x y = (if c = natDivName then val natZeroName ψ else x)) ∧
    (ble2 one y = vF →
     op2 x y = (if c = natDivName then val natZeroName ψ else x))

/-- The `ble`-guarded value-level clauses of a pin-certified operation,
for all members of the `Nat` value. -/
def DivModEqs (val : ConstVal V) (c : Name) : Prop :=
  ∀ (ψ : Name → Nat) (x y : V),
    x ∈ˢ val natName ψ → y ∈ˢ val natName ψ →
    DivModClauses V val c ψ x y

/-- A stored pin-certified WF-recursive operation (`Nat.div`/`Nat.mod`)
carries its literal-fast-path guard and satisfies its guarded
recurrences at the value level.  Established at install from the
checked characterization certificates (checked like theorems, never
installed); consumed by `reduceNat`'s soundness through meta-level
strong induction (`natOpVal_div`/`natOpVal_mod`). -/
def DivModOk (env : Env) (val : ConstVal V) : Prop :=
  ∀ c ∈ natDivModNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    natOpGuard env c = true ∧ DivModEqs V val c

theorem DivModOk.empty (val : ConstVal V) : DivModOk V Env.empty val := by
  intro c hc cv v hint h
  simp [Env.find?, Env.empty] at h

theorem ModeledOk.empty (val : ConstVal V) : ModeledOk V Env.empty val := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n cv cnP cnF h
    simp [Env.find?, Env.empty] at h
  · intro T cvT capsT j cv mI rP rules h
    simp [Env.find?, Env.empty] at h
  · intro T cvT caps h
    simp [Env.find?, Env.empty] at h
  · intro T cvT caps h
    simp [Env.find?, Env.empty] at h
  · intro T j cv mI rP rules h
    simp [Env.find?, Env.empty] at h

/-- A model of an environment: a set-theoretic value for every constant
(a function of the level-parameter assignment), such that

* the environment is syntactically well-formed,
* each constant's value only reads its own level parameters,
* each constant is a member of the interpretation of its type, and
* each definition's value equals the interpretation of its body.

Not a degenerate condition: `interpExpr` is undefined outside the
supported fragment, so an environment using unsupported constructs
provably has no `EnvModel`. -/
structure EnvModel (env : Env) where
  /-- The interpretation of each constant. -/
  val : ConstVal V
  /-- Stored declarations are syntactically well-formed. -/
  wf : EnvWF env
  /-- A constant's value only depends on its own level parameters. -/
  val_params : ∀ n ci, env.find? n = some ci →
    ∀ φ₁ φ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      val n φ₁ = val n φ₂
  /-- Every constant is a member of (the interpretation of) its type. -/
  mem_type : ∀ c ∈ env.consts, ∀ φ : Name → Nat,
    ∃ t, interpClosed V val env φ c.toConstantVal.type = some t ∧ val c.name φ ∈ˢ t
  /-- Every definition is interpreted by its body. -/
  defn_eq : ∀ cv value hint, ConstantInfo.defnInfo cv value hint ∈ env.consts → ∀ φ : Name → Nat,
    interpClosed V val env φ value = some (val cv.name φ)
  /-- Every theorem is interpreted by its proof value, which carries
  truthful annotations (theorem values delta-unfold in reduction, like
  the reference kernels'). -/
  thm_ok : ∀ cv value, ConstantInfo.thmInfo cv value ∈ env.consts → ∀ φ : Name → Nat,
    interpClosed V val env φ value = some (val cv.name φ) ∧
    AnnotOk V val env φ 0 (rho0 V) value
  /-- Stored types (and definition bodies) carry truthful annotations. -/
  annot_ok : ∀ c ∈ env.consts, ∀ φ : Name → Nat,
    AnnotOk V val env φ 0 (rho0 V) c.toConstantVal.type ∧
    ∀ cv value hint, c = ConstantInfo.defnInfo cv value hint →
      AnnotOk V val env φ 0 (rho0 V) value
  /-- Every stored inductive-kind constant has a model: the semantic
  facts the checker rules consume (`IndOk`), independent of the
  concrete construction that realizes them. -/
  ind_ok : IndOk V env val
  /-- Every stored recursor rule has a verified fold equation. -/
  rec_rules : RecRulesOk V env val
  /-- Every stored native projection-table entry is a pinned pair
  entry with its block stored (see `ProjOk`). -/
  proj_ok : ProjOk env
  /-- Non-reserved inductive-kind constants carry their model values. -/
  modeled_ok : ModeledOk V env val
  /-- Every stored structural-Nat operation satisfies its recurrence
  equations semantically (established at install by `certifyNatEqs`). -/
  nat_ops : NatOpsOk V env val
  /-- Every stored pin-certified WF-recursive operation
  (`Nat.div`/`Nat.mod`) satisfies its `ble`-guarded recurrences at the
  value level (established at install from the checked
  characterization certificates). -/
  div_mod : DivModOk V env val

/-- The empty environment has a (trivial) model. -/
def EnvModel.empty : EnvModel V Env.empty where
  val := fun _ _ => SetTheory.empty
  wf := by intro c hc; cases hc
  val_params := by
    intro n ci h
    simp [Env.find?, Env.empty] at h
  mem_type := by intro c hc; cases hc
  defn_eq := by intro cv value hint h; cases h
  thm_ok := by intro cv value h; cases h
  annot_ok := by intro c hc; cases hc
  ind_ok := IndOk.empty V _ (fun _ x hx => SetTheory.not_mem_empty x hx)
  rec_rules := RecRulesOk.empty V _
  proj_ok := ProjOk.empty
  modeled_ok := ModeledOk.empty V _
  nat_ops := NatOpsOk.empty V _
  div_mod := DivModOk.empty V _

/-! ## The literal guard, inverted

`natLitSupported` (and its slot checks) as separate facts, plus the
congruence the environment-relating lemmas use.  The literal fragment
of the model proper lives in `Setlec.Model.NatLit`.
-/

theorem Level.substFn_nil (φ : Name → Nat) : Level.substFn φ [] [] = φ :=
  funext fun _ => rfl

/-- Everything `natLitSupported` checked, as separate facts. -/
theorem natLitSupported_inv {env : Env} (hs : natLitSupported env = true) :
    ∃ cv caps cv0 i0 j0 cv1 i1 j1,
      env.find? natName = some (.indInfo cv caps) ∧
      env.find? natZeroName = some (.ctorInfo cv0 i0 j0) ∧
      env.find? natSuccName = some (.ctorInfo cv1 i1 j1) ∧
      cv.levelParams = [] ∧ cv0.levelParams = [] ∧ cv1.levelParams = [] ∧
      cv.type = .sort (.succ .zero) ∧ cv0.type = .const natName [] ∧
      ∃ nm mb, cv1.type = .forallE nm (.const natName []) (.const natName []) mb ∧
        mb.cod = some (.succ .zero) := by
  unfold natLitSupported at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨hi, hz⟩, hsc⟩ := hs
  unfold natIndOk at hi
  split at hi
  case h_2 => simp at hi
  next cv caps heqN =>
    unfold natZeroOk at hz
    split at hz
    case h_2 => simp at hz
    next cv0 i0 j0 heqZ =>
      unfold natSuccOk at hsc
      split at hsc
      case h_2 => simp at hsc
      next cv1 i1 j1 heqS =>
        simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hi hz hsc
        refine ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, heqN, heqZ, heqS,
          hi.1, hz.1, hsc.1, hi.2, hz.2, ?_⟩
        obtain ⟨-, h6⟩ := hsc
        revert h6
        split
        case h_2 => intro h; simp at h
        next nm c1 c2 mb heq =>
          intro h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          exact ⟨nm, mb, by rw [heq, h.1.1, h.1.2], h.2⟩

/-- The literal guard ignores a stored recursor's rule list (the slot
checks only ever accept inductive/constructor kinds). -/
theorem natLitSupported_cons_recRules {cvA : ConstantVal} {mI rP : Nat}
    {rules₁ rules₂ : List RecRule} {env : Env} :
    natLitSupported ⟨ConstantInfo.recInfo cvA mI rP rules₁ :: env.consts⟩ =
    natLitSupported ⟨ConstantInfo.recInfo cvA mI rP rules₂ :: env.consts⟩ := by
  unfold natLitSupported
  rw [Env.find?_cons, Env.find?_cons, Env.find?_cons, Env.find?_cons,
    Env.find?_cons, Env.find?_cons]
  simp only [ConstantInfo.toConstantVal, ConstantInfo.name]
  by_cases h1 : cvA.name = natName <;> by_cases h2 : cvA.name = natZeroName <;>
    by_cases h3 : cvA.name = natSuccName <;>
    simp [h1, h2, h3, natIndOk, natZeroOk, natSuccOk]

/-- The literal guard only reads the three `Nat` slots. -/
theorem natLitSupported_congr {env₁ env₂ : Env}
    (h1 : env₁.find? natName = env₂.find? natName)
    (h2 : env₁.find? natZeroName = env₂.find? natZeroName)
    (h3 : env₁.find? natSuccName = env₂.find? natSuccName) :
    natLitSupported env₁ = natLitSupported env₂ := by
  unfold natLitSupported
  rw [h1, h2, h3]

/-- The names the string-literal guard (and the string-literal clause of
the interpretation) reads off the environment: the `Nat` literal slots
plus the seven string-support slots. -/
def strLitNames : List Name :=
  [natName, natZeroName, natSuccName, stringName, stringOfListName,
    listName, listNilName, listConsName, charName, charOfNatName]

/-- Everything `strLitSupported` checked beyond `natLitSupported`, as
separate facts (level-parameter lists and exact annotated types of the
seven string-support constants). -/
theorem strLitSupported_inv {env : Env} (hs : strLitSupported env = true) :
    natLitSupported env = true ∧
    ∃ ciS ciO ciL ciN ciC ciH ciF pL pN pC,
      env.find? stringName = some ciS ∧
      env.find? stringOfListName = some ciO ∧
      env.find? listName = some ciL ∧
      env.find? listNilName = some ciN ∧
      env.find? listConsName = some ciC ∧
      env.find? charName = some ciH ∧
      env.find? charOfNatName = some ciF ∧
      ciS.toConstantVal.levelParams = [] ∧
      ciO.toConstantVal.levelParams = [] ∧
      ciL.toConstantVal.levelParams = [pL] ∧
      ciN.toConstantVal.levelParams = [pN] ∧
      ciC.toConstantVal.levelParams = [pC] ∧
      ciH.toConstantVal.levelParams = [] ∧
      ciF.toConstantVal.levelParams = [] ∧
      ciS.toConstantVal.type = .sort (.succ .zero) ∧
      ciH.toConstantVal.type = .sort (.succ .zero) ∧
      (∃ nm mb, ciO.toConstantVal.type =
        .forallE nm (.app (.const listName [.zero]) (.const charName []))
          (.const stringName []) mb ∧ mb.cod = some (.succ .zero)) ∧
      (∃ nm mb, ciL.toConstantVal.type =
        .forallE nm (.sort (.succ (.param pL))) (.sort (.succ (.param pL))) mb ∧
        mb.cod = some (.succ (.succ (.param pL)))) ∧
      (∃ nm mb, ciN.toConstantVal.type =
        .forallE nm (.sort (.succ (.param pN)))
          (.app (.const listName [.param pN]) (.bvar 0)) mb ∧
        mb.cod = some (.succ (.param pN))) ∧
      (∃ nm1 nm2 nm3 mb1 mb2 mb3, ciC.toConstantVal.type =
        .forallE nm1 (.sort (.succ (.param pC)))
          (.forallE nm2 (.bvar 0)
            (.forallE nm3 (.app (.const listName [.param pC]) (.bvar 1))
              (.app (.const listName [.param pC]) (.bvar 2)) mb3) mb2) mb1 ∧
        mb3.cod = some (.succ (.param pC)) ∧
        mb2.cod = some (.imax (.succ (.param pC)) (.succ (.param pC))) ∧
        mb1.cod = some (.imax (.succ (.param pC))
          (.imax (.succ (.param pC)) (.succ (.param pC))))) ∧
      (∃ nm mb, ciF.toConstantVal.type =
        .forallE nm (.const natName []) (.const charName []) mb ∧
        mb.cod = some (.succ .zero)) := by
  unfold strLitSupported at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hnat, hS⟩, hO⟩, hL⟩, hN⟩, hC⟩, hH⟩, hF⟩ := hs
  refine ⟨hnat, ?_⟩
  unfold stringTyOk at hS
  unfold stringOfListTyOk at hO
  unfold listTyOk at hL
  unfold listNilTyOk at hN
  unfold listConsTyOk at hC
  unfold charTyOk at hH
  unfold charOfNatTyOk at hF
  split at hS; case h_2 => simp at hS
  next ciS heqS =>
  split at hO; case h_2 => simp at hO
  next ciO heqO =>
  split at hL; case h_2 => simp at hL
  next ciL heqL =>
  split at hN; case h_2 => simp at hN
  next ciN heqN =>
  split at hC; case h_2 => simp at hC
  next ciC heqC =>
  split at hH; case h_2 => simp at hH
  next ciH heqH =>
  split at hF; case h_2 => simp at hF
  next ciF heqF =>
  simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hS hH
  -- List: one level parameter, pinned type
  revert hL
  split; case h_2 => intro h; exact nomatch h
  next pL heqPL =>
  split
  case h_2 => intro h; simp at h
  next nmL u1L u2L mbL heqTL =>
  intro hL
  simp only [Bool.and_eq_true, beq_iff_eq] at hL
  -- List.nil
  revert hN
  split; case h_2 => intro h; exact nomatch h
  next pN heqPN =>
  split
  case h_2 => intro h; simp at h
  next nmN u1N l1N us1N mbN heqTN =>
  intro hN
  simp only [Bool.and_eq_true, beq_iff_eq] at hN
  -- List.cons
  revert hC
  split; case h_2 => intro h; exact nomatch h
  next pC heqPC =>
  split
  case h_2 => intro h; simp at h
  next nmC1 u1C nmC2 nmC3 l1C us1C l2C us2C mb3C mb2C mb1C heqTC =>
  intro hC
  simp only [Bool.and_eq_true, beq_iff_eq] at hC
  -- Char.ofNat
  revert hF
  simp only [Bool.and_eq_true, List.isEmpty_iff]
  rintro ⟨hF1, hF2⟩
  revert hF2
  split
  case h_2 => intro h; simp at h
  next nmF c1F c2F mbF heqTF =>
  intro hF2
  simp only [Bool.and_eq_true, beq_iff_eq] at hF2
  -- String.ofList
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hO
  obtain ⟨hO1, hO2⟩ := hO
  revert hO2
  split
  case h_2 => intro h; simp at h
  next nmO l1O us1O c1O c2O mbO heqTO =>
  intro hO2
  simp only [Bool.and_eq_true, beq_iff_eq] at hO2
  refine ⟨ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC,
    heqS, heqO, heqL, heqN, heqC, heqH, heqF,
    hS.1, hO1, heqPL, heqPN, heqPC, hH.1, hF1, hS.2, hH.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨nmO, mbO, by
      rw [heqTO, hO2.1.1.1.1, hO2.1.1.1.2, hO2.1.1.2, hO2.1.2], hO2.2⟩
  · exact ⟨nmL, mbL, by rw [heqTL, hL.1.1, hL.1.2], hL.2⟩
  · exact ⟨nmN, mbN, by rw [heqTN, hN.1.1.1, hN.1.1.2, hN.1.2], hN.2⟩
  · exact ⟨nmC1, nmC2, nmC3, mb1C, mb2C, mb3C, by
      rw [heqTC, hC.1.1.1.1.1.1.1, hC.1.1.1.1.1.1.2, hC.1.1.1.1.1.2,
        hC.1.1.1.1.2, hC.1.1.1.2],
      hC.1.1.2, hC.1.2, hC.2⟩
  · exact ⟨nmF, mbF, by rw [heqTF, hF2.1.1, hF2.1.2], hF2.2⟩

/-- The string-support shape checks read a stored constant only through
its `toConstantVal`. -/
theorem strTyOk_toCV : ∀ {o₁ o₂ : Option ConstantInfo},
    o₁.map ConstantInfo.toConstantVal = o₂.map ConstantInfo.toConstantVal →
    stringTyOk o₁ = stringTyOk o₂ ∧ stringOfListTyOk o₁ = stringOfListTyOk o₂ ∧
    listTyOk o₁ = listTyOk o₂ ∧ listNilTyOk o₁ = listNilTyOk o₂ ∧
    listConsTyOk o₁ = listConsTyOk o₂ ∧ charTyOk o₁ = charTyOk o₂ ∧
    charOfNatTyOk o₁ = charOfNatTyOk o₂
  | none, none, _ => by simp
  | some ci₁, some ci₂, h => by
    simp only [Option.map_some, Option.some.injEq] at h
    simp [stringTyOk, stringOfListTyOk, listTyOk, listNilTyOk,
      listConsTyOk, charTyOk, charOfNatTyOk, h]
  | none, some _, h => by simp at h
  | some _, none, h => by simp at h

/-- The string-literal guard ignores a stored recursor's rule list. -/
theorem strLitSupported_cons_recRules {cvA : ConstantVal} {mI rP : Nat}
    {rules₁ rules₂ : List RecRule} {env : Env} :
    strLitSupported ⟨ConstantInfo.recInfo cvA mI rP rules₁ :: env.consts⟩ =
    strLitSupported ⟨ConstantInfo.recInfo cvA mI rP rules₂ :: env.consts⟩ := by
  have hfind : ∀ n : Name,
      ((⟨ConstantInfo.recInfo cvA mI rP rules₁ :: env.consts⟩ :
        Env).find? n).map ConstantInfo.toConstantVal =
      ((⟨ConstantInfo.recInfo cvA mI rP rules₂ :: env.consts⟩ :
        Env).find? n).map ConstantInfo.toConstantVal := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases h : (ConstantInfo.recInfo cvA mI rP rules₁).name = n
    · rw [if_pos h, if_pos (by simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using h)]
      rfl
    · rw [if_neg h, if_neg (by simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using h)]
  unfold strLitSupported
  rw [natLitSupported_cons_recRules (rules₁ := rules₁) (rules₂ := rules₂),
    (strTyOk_toCV (hfind stringName)).1,
    (strTyOk_toCV (hfind stringOfListName)).2.1,
    (strTyOk_toCV (hfind listName)).2.2.1,
    (strTyOk_toCV (hfind listNilName)).2.2.2.1,
    (strTyOk_toCV (hfind listConsName)).2.2.2.2.1,
    (strTyOk_toCV (hfind charName)).2.2.2.2.2.1,
    (strTyOk_toCV (hfind charOfNatName)).2.2.2.2.2.2]

/-- The string-literal guard transfers between environments whose
lookups agree up to constant kind (`toConstantVal`), given the `Nat`
guard transfers (the latter also reads kinds). -/
theorem strLitSupported_env_ext {env₁ env₂ : Env}
    (htoCV : ∀ n, (env₁.find? n).map ConstantInfo.toConstantVal =
      (env₂.find? n).map ConstantInfo.toConstantVal)
    (hnat : natLitSupported env₁ = natLitSupported env₂) :
    strLitSupported env₁ = strLitSupported env₂ := by
  unfold strLitSupported
  rw [hnat, (strTyOk_toCV (htoCV stringName)).1,
    (strTyOk_toCV (htoCV stringOfListName)).2.1,
    (strTyOk_toCV (htoCV listName)).2.2.1,
    (strTyOk_toCV (htoCV listNilName)).2.2.2.1,
    (strTyOk_toCV (htoCV listConsName)).2.2.2.2.1,
    (strTyOk_toCV (htoCV charName)).2.2.2.2.2.1,
    (strTyOk_toCV (htoCV charOfNatName)).2.2.2.2.2.2]

/-- The string-literal guard only reads the pinned slots
(`strLitNames`). -/
theorem strLitSupported_congr {env₁ env₂ : Env}
    (hNat : env₁.find? natName = env₂.find? natName)
    (hZero : env₁.find? natZeroName = env₂.find? natZeroName)
    (hSucc : env₁.find? natSuccName = env₂.find? natSuccName)
    (hS : env₁.find? stringName = env₂.find? stringName)
    (hO : env₁.find? stringOfListName = env₂.find? stringOfListName)
    (hL : env₁.find? listName = env₂.find? listName)
    (hN : env₁.find? listNilName = env₂.find? listNilName)
    (hC : env₁.find? listConsName = env₂.find? listConsName)
    (hH : env₁.find? charName = env₂.find? charName)
    (hF : env₁.find? charOfNatName = env₂.find? charOfNatName) :
    strLitSupported env₁ = strLitSupported env₂ := by
  unfold strLitSupported
  rw [natLitSupported_congr hNat hZero hSucc, hS, hO, hL, hN, hC, hH, hF]

/-- The stored level-parameter list only reads the constant's slot. -/
theorem Env.levelParamsAt_congr {env₁ env₂ : Env} {n : Name}
    (h : env₁.find? n = env₂.find? n) :
    env₁.levelParamsAt n = env₂.levelParamsAt n := by
  unfold Env.levelParamsAt
  rw [h]

/-- The stored level-parameter list only reads the constant's
level-parameter slot. -/
theorem Env.levelParamsAt_congr' {env₁ env₂ : Env} {n : Name}
    (h : (env₁.find? n).map (fun ci => ci.toConstantVal.levelParams) =
      (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams)) :
    env₁.levelParamsAt n = env₂.levelParamsAt n := by
  unfold Env.levelParamsAt
  cases h1 : env₁.find? n <;> cases h2 : env₂.find? n <;>
    rw [h1, h2] at h <;> simp at h ⊢ <;> exact h

/-- The interpretation of a string literal, unfolded through the
guard. -/
theorem interpExpr_strLit {env : Env} {cval : ConstVal V} {φ : Name → Nat}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} {s : String} :
    interpExpr V cval env φ d ρ (.lit (.strVal s)) =
      some (strLitVal V cval env φ s) := by
  simp [interpExpr, hs]

/-- The interpretation of a string literal without the guard is
undefined. -/
theorem interpExpr_strLit_none {env : Env} {cval : ConstVal V} {φ : Name → Nat}
    (hs : ¬ strLitSupported env = true) {d : Nat} {ρ : Nat → V} {s : String} :
    interpExpr V cval env φ d ρ (.lit (.strVal s)) = none := by
  simp [interpExpr, hs]

/-- Congruence for the string-literal value: it reads the valuations
only at the seven pinned slots (each at the displayed assignment). -/
theorem strLitVal_congr {cval₁ cval₂ : ConstVal V} {env₁ env₂ : Env}
    {φ₁ φ₂ : Name → Nat} {s : String}
    (h1 : cval₁ stringOfListName (Level.substFn φ₁ [] []) =
      cval₂ stringOfListName (Level.substFn φ₂ [] []))
    (h2 : cval₁ listNilName
        (Level.substFn φ₁ (env₁.levelParamsAt listNilName) [.zero]) =
      cval₂ listNilName
        (Level.substFn φ₂ (env₂.levelParamsAt listNilName) [.zero]))
    (h3 : cval₁ listConsName
        (Level.substFn φ₁ (env₁.levelParamsAt listConsName) [.zero]) =
      cval₂ listConsName
        (Level.substFn φ₂ (env₂.levelParamsAt listConsName) [.zero]))
    (h4 : cval₁ charName (Level.substFn φ₁ [] []) =
      cval₂ charName (Level.substFn φ₂ [] []))
    (h5 : cval₁ charOfNatName (Level.substFn φ₁ [] []) =
      cval₂ charOfNatName (Level.substFn φ₂ [] []))
    (h6 : cval₁ natZeroName (Level.substFn φ₁ [] []) =
      cval₂ natZeroName (Level.substFn φ₂ [] []))
    (h7 : cval₁ natSuccName (Level.substFn φ₁ [] []) =
      cval₂ natSuccName (Level.substFn φ₂ [] [])) :
    strLitVal V cval₁ env₁ φ₁ s = strLitVal V cval₂ env₂ φ₂ s := by
  unfold strLitVal
  rw [h1, h2, h3, h4, h5, h6, h7]

end Setlec
