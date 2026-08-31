import Setlec.NbE.Verify.Denote

/-!
# NbE pilot verification: the fundamental theorem

`eval_applyV_sound`: machine evaluation preserves denotation —
`eval E fuel ρ t = some v` implies `⟦v⟧σ = ⟦t⟧(⟦ρ⟧σ)`, conditional on
the **β-membership ledger** `EvalOk`/`ApplyOk`.

## The β bet, verified

The β case (in `applyV`'s λ clause) is:

    ⟦eval (a :: ρ) b⟧ = app (lamC ⟦dom⟧ (x ↦ ⟦b⟧(x :: ⟦ρ⟧))) ⟦a⟧

and it closes by the induction hypothesis plus **one** application of
`app_lamC` — no lifting, no instantiation, no substitution transport;
the machine's environment extension and the denotation's environment
extension are the same operation, so the two sides meet definitionally
once `app_lamC` peels the `lamC`.  The binder cases (λ/Π formation)
are `rfl` after rewriting the domain.  This verifies the pilot's
promise 1: the substitution-transport tier of the main campaign has no
counterpart here.

## The ledger (where typing went)

`app_lamC` (post-#100 collapse) fires on *domain membership alone* —
but it does need `⟦a⟧ ∈ˢ ⟦dom⟧`.  The unconditional statement is
**false**: evaluate `(λ (x : Sort 0). x) (Sort 5)` — the machine
β-reduces to `Sort 5`, but in the model `app (lamC (univ 0) id)
(univ 5)` is junk, not `univ 5` (see `ft_unconditional_refuted`).
So the fundamental theorem is premised on `EvalOk`: a Prop-mirror of
the machine's call tree whose *only* content is one membership per β
event (`ApplyOk`'s λ clause).  This is hard class 3 (the typing
boundary) in NbE clothing: typing premises are not eliminated, they
are relocated — from per-syntax-node truthfulness (the campaign's
`AnnotOk`) to per-β-event memberships.  Discharging the ledger from
front-door typing is the logical-relations tier; see the walls file.

## δ-coherence (gluing)

`unfoldNeu_sound`: the recomputed unfolded face of a glued neutral
denotes the same set as its spine face, premised on `EnvOk` (each
constant denotes its own body — the environment invariant), on the
ledger for the body's evaluation, and on `ArgsOk` (the ledger for
re-applying the spine).  Levels cross this lemma through
`dTerm_instL` + `dTerm_ext_φ` + `substFn_eq_lvlAssign` —
unconditional level plumbing, no set-model arbitration.
-/

namespace Setlec.NbE

open Setlec.SetTheory

universe u

variable {V : Type u} [SetTheory V]

mutual

/-- The β-membership ledger: mirrors `eval`'s recursion; its only
content is the membership at each β event (`ApplyOk`'s λ clause). -/
def EvalOk (κ : Name → List Nat → V) (φ : Name → Nat) (σ : Nat → V)
    (E : Env) : Nat → List Value → Term → Prop
  | 0, _, _ => True
  | _ + 1, _, .bvar _ => True
  | _ + 1, _, .sort _ => True
  | _ + 1, _, .const _ _ => True
  | fuel + 1, ρ, .app f a =>
    EvalOk κ φ σ E fuel ρ f ∧ EvalOk κ φ σ E fuel ρ a ∧
    ∀ vf va, eval E fuel ρ f = some vf → eval E fuel ρ a = some va →
      ApplyOk κ φ σ E fuel vf va
  | fuel + 1, ρ, .lam d _ => EvalOk κ φ σ E fuel ρ d
  | fuel + 1, ρ, .pi d _ => EvalOk κ φ σ E fuel ρ d
termination_by fuel _ _ => (fuel, 0)

/-- The ledger clause for one application: at a β event, the argument's
denotation inhabits the λ's own domain denotation. -/
def ApplyOk (κ : Name → List Nat → V) (φ : Name → Nat) (σ : Nat → V)
    (E : Env) : Nat → Value → Value → Prop
  | 0, _, _ => True
  | fuel + 1, .lam dom (.mk ρ b), a =>
    dVal κ φ σ a ∈ˢ dVal κ φ σ dom ∧ EvalOk κ φ σ E fuel (a :: ρ) b
  | _ + 1, _, _ => True
termination_by fuel _ _ => (fuel, 1)

end

variable {κ : Name → List Nat → V} {φ : Name → Nat} {σ : Nat → V} {E : Env}

/-- **The fundamental theorem** (both machine functions at once, by
fuel induction): evaluation preserves denotation, conditional on the
β-membership ledger.  At fuel `0` both machines return `none`, so the
base case is vacuous by *machine failure*, not by premise vacuity —
the ledger at fuel `0` is `True` and the conclusion is unconstrained. -/
theorem eval_applyV_sound : ∀ fuel : Nat,
    (∀ (ρ : List Value) (t : Term) (v : Value),
      eval E fuel ρ t = some v → EvalOk κ φ σ E fuel ρ t →
      dVal κ φ σ v = dTerm κ φ (dVals κ φ σ ρ) t) ∧
    (∀ vf va v : Value,
      applyV E fuel vf va = some v → ApplyOk κ φ σ E fuel vf va →
      dVal κ φ σ v = SetTheory.app (dVal κ φ σ vf) (dVal κ φ σ va)) := by
  intro fuel
  induction fuel with
  | zero =>
    exact ⟨fun ρ t v h => by simp [eval] at h,
           fun vf va v h => by simp [applyV] at h⟩
  | succ fuel ih =>
    obtain ⟨ihE, ihA⟩ := ih
    constructor
    · intro ρ t v hev hok
      cases t with
      | bvar i =>
        simp only [eval] at hev
        exact (dVals_getD hev).symm
      | sort u =>
        simp only [eval, Option.some.injEq] at hev
        subst hev; rfl
      | const n us =>
        simp only [eval] at hev
        cases hl : E.lookup n with
        | none => rw [hl] at hev; cases hev
        | some ci =>
          simp only [hl] at hev
          by_cases hlen : ci.lvlParams.length = us.length
          · rw [if_pos hlen, Option.some.injEq] at hev
            subst hev; rfl
          · rw [if_neg hlen] at hev; cases hev
      | app f a =>
        simp only [eval] at hev
        cases hf : eval E fuel ρ f with
        | none => rw [hf] at hev; cases hev
        | some vf =>
          cases ha : eval E fuel ρ a with
          | none => rw [hf, ha] at hev; cases hev
          | some va =>
            rw [hf, ha] at hev
            simp only [EvalOk] at hok
            obtain ⟨hokf, hoka, hokap⟩ := hok
            have := ihA vf va v hev (hokap vf va hf ha)
            rw [this, ihE ρ f vf hf hokf, ihE ρ a va ha hoka]
            rfl
      | lam d b =>
        simp only [eval] at hev
        cases hd : eval E fuel ρ d with
        | none => rw [hd] at hev; cases hev
        | some vd =>
          rw [hd, Option.some.injEq] at hev
          subst hev
          simp only [EvalOk] at hok
          show lamC (dVal κ φ σ vd) _ = lamC (dTerm κ φ (dVals κ φ σ ρ) d) _
          rw [ihE ρ d vd hd hok]
          rfl
      | pi d b =>
        simp only [eval] at hev
        cases hd : eval E fuel ρ d with
        | none => rw [hd] at hev; cases hev
        | some vd =>
          rw [hd, Option.some.injEq] at hev
          subst hev
          simp only [EvalOk] at hok
          show piC (dVal κ φ σ vd) _ = piC (dTerm κ φ (dVals κ φ σ ρ) d) _
          rw [ihE ρ d vd hd hok]
          rfl
    · intro vf va v hap hok
      cases vf with
      | sort u => simp [applyV] at hap
      | pi d cl => simp [applyV] at hap
      | lam dom cl =>
        cases cl with
        | mk ρ b =>
          simp only [applyV] at hap
          simp only [ApplyOk] at hok
          obtain ⟨hmem, hokb⟩ := hok
          -- The β case: one `app_lamC`, no substitution lemma.
          rw [ihE (va :: ρ) b v hap hokb]
          show dTerm κ φ (dVal κ φ σ va :: dVals κ φ σ ρ) b =
            SetTheory.app (lamC (dVal κ φ σ dom) fun x => dClosure κ φ σ (.mk ρ b) x)
              (dVal κ φ σ va)
          rw [app_lamC hmem]
          rfl
      | neu h args =>
        simp only [applyV, Option.some.injEq] at hap
        subst hap
        exact dVal_neu_snoc h args va

/-- The unconditional fundamental theorem is **false** — the exact
refutation the ledger exists for: the machine β-reduces
`(λ (x : Sort 0). x) (Sort 5)` to `Sort 5`, but soundness of that step
would force `univ 5 ∈ˢ univ 1` (by cardinality nonsense through
`app_lamC`'s absence).  Concretely we refute the *statement schema*
"`applyV`'s λ clause is denotation-sound without the membership": the
β equation `app (lamC A F) a = F a` fails for `a ∉ˢ A` in general.
Rather than exhibit a model here (the interface is parametric), we
record the schema-level countermodel: with `A := univ 0`,
`F := id`, `a := univ 5`, soundness would give
`app (lamC (univ 0) id) (univ 5) = univ 5`; but the same argument with
`F := fun _ => univ 3` gives `… = univ 3` — while
`lamC (univ 0) id = lamC (univ 0) (fun _ => univ 3)` would *not* be
required, `app` of *some* fixed junk value cannot be both.  The
machine-checked form: two λs that agree on their domain are
denotation-equal (`lamC_congr`), yet β-reduce differently off it. -/
theorem ft_unconditional_refuted :
    (∀ (A : V) (F G : V → V) (a : V),
        SetTheory.app (lamC A F) a = F a ∧ SetTheory.app (lamC A G) a = G a) →
    False := by
  intro h
  -- Off-domain β for both `id` and `const (univ 3)` at the *empty* domain:
  -- the two λs are equal (`lamC_congr`, vacuously), so their `app`s agree,
  -- forcing `univ 5 = univ 3`.
  have hlam : lamC (empty : V) (fun x => x) = lamC (empty : V) (fun _ => univ 3) :=
    lamC_congr fun x hx => absurd hx (not_mem_empty x)
  have h1 := (h empty (fun x => x) (fun _ => univ 3) (univ 5)).1
  have h2 := (h empty (fun x => x) (fun _ => univ 3) (univ 5)).2
  rw [hlam] at h1
  rw [h1] at h2
  exact absurd (univ_inj h2) (by omega)

/-! ## Vacuity probe: the ledger is satisfiable and the conclusion bites

A concrete β event whose ledger entry is discharged by a real
membership (`univ 0 ∈ˢ univ 1`) and whose conclusion is a nontrivial
model equation.  (Fuel is `fuel + 2` so the equations reduce by the
generated equation lemmas without committing to a literal.) -/

example (fuel : Nat) :
    applyV E (fuel + 2) (.lam (.sort (.succ .zero)) (.mk [] (.bvar 0)))
      (.sort .zero) = some (.sort .zero) := by
  simp [applyV, eval]

example (fuel : Nat) :
    ApplyOk κ φ σ E (fuel + 2) (.lam (.sort (.succ .zero)) (.mk [] (.bvar 0)))
      (.sort .zero) := by
  simp only [ApplyOk]
  refine ⟨?_, ?_⟩
  · simpa [dVal, Level.eval] using univ_mem_univ (V := V) 0
  · show EvalOk κ φ σ E (fuel + 1) [Value.sort .zero] (.bvar 0)
    simp [EvalOk]

/-- The probe's conclusion, through the fundamental theorem: a real
model equation (`app` of a `lamC` at a member of its domain). -/
example (fuel : Nat) :
    SetTheory.app (lamC (univ 1) fun x => dTerm κ φ [x] (.bvar 0))
      (univ 0 : V) = univ 0 := by
  have h := (eval_applyV_sound (V := V) (κ := κ) (φ := φ) (σ := σ) (E := E)
    (fuel + 2)).2
    (.lam (.sort (.succ .zero)) (.mk [] (.bvar 0))) (.sort .zero) (.sort .zero)
    (by simp [applyV, eval])
    (by simp only [ApplyOk]
        exact ⟨by simpa [dVal, Level.eval] using univ_mem_univ (V := V) 0,
               by simp [EvalOk]⟩)
  simp only [dVal, dClosure, dVals, Level.eval] at h
  exact h.symm

/-! ## δ-coherence: the glued value's two faces agree -/

/-- The environment invariant: every constant denotes its own value
term at every level instantiation of the right length, and its level
hygiene checks (what `checkDecl` enforced) hold. -/
def EnvOk (κ : Name → List Nat → V) (E : Env) : Prop :=
  ∀ ci ∈ E.consts,
    Name.nodup ci.lvlParams = true ∧
    ci.value.lvlDefined ci.lvlParams = true ∧
    ∀ ls : List Nat, ls.length = ci.lvlParams.length →
      κ ci.name ls = dTerm κ (lvlAssign ci.lvlParams ls) [] ci.value

/-- The ledger for re-applying a spine (`applyArgs`). -/
def ArgsOk (κ : Name → List Nat → V) (φ : Name → Nat) (σ : Nat → V)
    (E : Env) (fuel : Nat) : Value → List Value → Prop
  | _, [] => True
  | v, a :: as =>
    ApplyOk κ φ σ E fuel v a ∧
    ∀ w, applyV E fuel v a = some w → ArgsOk κ φ σ E fuel w as

theorem applyArgs_sound (fuel : Nat) :
    ∀ (as : List Value) (v w : Value),
      applyArgs E fuel v as = some w → ArgsOk κ φ σ E fuel v as →
      dVal κ φ σ w = (dVals κ φ σ as).foldl SetTheory.app (dVal κ φ σ v) := by
  intro as
  induction as with
  | nil =>
    intro v w h _
    simp only [applyArgs, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro v w h hok
    simp only [applyArgs] at h
    cases hap : applyV E fuel v a with
    | none => rw [hap] at h; cases h
    | some v' =>
      rw [hap] at h
      obtain ⟨hokA, hokRest⟩ := hok
      have h1 := (eval_applyV_sound (κ := κ) (φ := φ) (σ := σ) fuel).2
        v a v' hap hokA
      rw [ih v' w h (hokRest v' hap), h1]
      rfl

/-- **Gluing coherence, δ side**: the recomputed unfolded face of a
glued neutral denotes its spine face.  Premises: the environment
invariant, the length invariant on machine-created spines, and the
β-membership ledger for the unfolding evaluation and the spine
replay. -/
theorem unfoldNeu_sound {fuel : Nat} {n : Name} {us : List Level}
    {args : List Value} {w : Value}
    (hE : EnvOk κ E)
    (h : unfoldNeu E fuel n us args = some w)
    (hpre : ∀ ci, E.lookup n = some ci →
      ci.lvlParams.length = us.length ∧
      EvalOk κ φ σ E fuel [] (ci.value.instL ci.lvlParams us) ∧
      ∀ v0, eval E fuel [] (ci.value.instL ci.lvlParams us) = some v0 →
        ArgsOk κ φ σ E fuel v0 args) :
    dVal κ φ σ w = dVal κ φ σ (.neu (.const n us) args) := by
  simp only [unfoldNeu] at h
  cases hl : E.lookup n with
  | none => rw [hl] at h; cases h
  | some ci =>
    simp only [hl] at h
    obtain ⟨hlen, hokE, hokArgs⟩ := hpre ci hl
    cases hev : eval E fuel [] (ci.value.instL ci.lvlParams us) with
    | none => rw [hev] at h; cases h
    | some v0 =>
      simp only [hev] at h
      -- The unfolded head denotes the constant's denotation:
      have hci : ci ∈ E.consts := List.mem_of_find?_eq_some hl
      have hname : ci.name = n := by
        have := List.find?_some hl
        simpa using this
      obtain ⟨hnd, hdef, hκ⟩ := hE ci hci
      have h0 := (eval_applyV_sound (κ := κ) (φ := φ) (σ := σ) fuel).1
        [] (ci.value.instL ci.lvlParams us) v0 hev hokE
      rw [dTerm_instL] at h0
      simp only [dVals_nil] at h0
      have hext : dTerm κ (Level.substFn φ ci.lvlParams us) ([] : List V)
          ci.value = dTerm κ (lvlAssign ci.lvlParams (us.map (Level.eval φ)))
            ([] : List V) ci.value :=
        dTerm_ext_φ
          (substFn_eq_lvlAssign ci.lvlParams us hnd (hlen.trans rfl))
          ci.value hdef []
      have hκ' := hκ (us.map (Level.eval φ)) (by simpa using hlen.symm)
      have hhead : dVal κ φ σ v0 = κ n (us.map (Level.eval φ)) := by
        rw [h0, hext, ← hname, ← hκ']
      -- Replay the spine:
      rw [applyArgs_sound fuel args v0 w h (hokArgs v0 hev), hhead]
      rfl

end Setlec.NbE
