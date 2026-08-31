import Setlec.NbE.Verify.Eval

/-!
# NbE pilot verification: conversion soundness

`conv_sound`: a `some true` verdict of the untyped value conversion
implies equal denotations — conditional on `ConvOk`, the conversion
ledger.

## What the ledger carries (and why)

`ConvOk` mirrors `conv`'s match tree exactly.  Its clauses:

* **sorts**: nothing — the sort case is carried entirely by the
  campaign's `Level.isEquiv_sound` (all-assignments soundness),
  imported across regimes unchanged because values carry the same
  `Level` syntax.  No set-model arbitration of levels happens anywhere
  in this proof: hard class 2 (cross-run sort agreement) has no
  purchase on this slice, because conversion's fresh variables are
  *untyped* — there is no fvar sort for two runs to disagree about.
* **binders** (`BinderOk`): for every argument `x` in the *domain's*
  denotation, (a) the two closure applications at the shared fresh
  variable denote their closures at `x` (the fresh-variable coherence
  facts — dischargeable, see `closure_app_coherent`), and (b) the
  ledger for the sub-conversion at frontier `k+1` and `σ[k ↦ x]`.
  The `x ∈ˢ ⟦dom⟧` bound is what `piC_congr`/`lamC_congr` consume;
  nothing needs the *level* of the domain (the post-#100 collapse
  keeps β and congruence level-free).
* **glued neutrals** (`DeltaOk` and the one-sided unfold clauses): the
  δ-coherence equations of `unfoldNeu_sound` plus the sub-ledger.

## The gluing-coherence verdict

The spine-equality shortcut is proved sound *without touching the
unfolded face*: equal heads need `Level.isEquiv_sound` only; equal
spines are pairwise induction; `app` is a function, so congruence is
free.  Gluing does **not** reintroduce a coherence tier for the
shortcut itself.  The tier it does need — one equation per δ-unfold
event, `⟦unfolded⟧ = ⟦spine⟧` — is `unfoldNeu_sound`, whose premises
are the environment invariant plus the β-ledger of the unfolding.
With the pilot's recomputed unfolding this is an *event* premise, not
a value invariant; a thunk-cached implementation would strengthen it
into a "all thunks in all reachable values are pedigreed" invariant
threaded through every constructor site (the mini-tier the charter
asked about).
-/

namespace Setlec.NbE

open Setlec.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- Pointwise-equivalent level lists have equal evaluations. -/
theorem evalEqList_map_eq {φ : Name → Nat} :
    ∀ {us vs : List Level}, Level.EvalEqList φ us vs →
      us.map (Level.eval φ) = vs.map (Level.eval φ)
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h1, h2⟩ => by
    simp only [List.map_cons, h1, evalEqList_map_eq h2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

mutual

/-- The conversion ledger: mirrors `conv`'s match tree.  Sort and
mismatch clauses carry nothing; binder clauses carry the fresh-variable
coherence and the sub-ledger over the domain; glued clauses carry the
δ-coherence equations and the sub-ledger. -/
def ConvOk (κ : Name → List Nat → V) (φ : Name → Nat) (E : Env) :
    Nat → Nat → (Nat → V) → Value → Value → Prop
  | 0, _, _, _, _ => True
  | fuel + 1, k, σ, v, w =>
    match v, w with
    | .sort _, .sort _ => True
    | .pi d cl, .pi d' cl' => BinderOk κ φ E fuel k σ d cl d' cl'
    | .lam d cl, .lam d' cl' => BinderOk κ φ E fuel k σ d cl d' cl'
    | .neu (.fvar _) args, .neu (.fvar _) args' =>
      ArgsConvOk κ φ E fuel k σ args args'
    | .neu (.const n us) args, .neu (.const n' us') args' =>
      ArgsConvOk κ φ E fuel k σ args args' ∧
      DeltaOk κ φ E fuel k σ n us args n' us' args'
    | .neu (.const n us) args, w =>
      ∀ x, unfoldNeu E fuel n us args = some x →
        dVal κ φ σ x = dVal κ φ σ (.neu (.const n us) args) ∧
        ConvOk κ φ E fuel k σ x w
    | v, .neu (.const n us) args =>
      ∀ y, unfoldNeu E fuel n us args = some y →
        dVal κ φ σ y = dVal κ φ σ (.neu (.const n us) args) ∧
        ConvOk κ φ E fuel k σ v y
    | _, _ => True
termination_by fuel _ _ _ _ => (fuel, 0)

/-- Binder clause: domains' ledger, then — for each `x` in the domain's
denotation — the fresh-variable coherence equations and the
sub-ledger at the extended frontier. -/
def BinderOk (κ : Name → List Nat → V) (φ : Name → Nat) (E : Env)
    (fuel k : Nat) (σ : Nat → V) (d : Value) (cl : Closure)
    (d' : Value) (cl' : Closure) : Prop :=
  ConvOk κ φ E fuel k σ d d' ∧
  ∀ x : V, x ∈ˢ dVal κ φ σ d →
    ∀ vb vb', applyCl E fuel cl (freshV k) = some vb →
      applyCl E fuel cl' (freshV k) = some vb' →
      dVal κ φ (setAt σ k x) vb = dClosure κ φ σ cl x ∧
      dVal κ φ (setAt σ k x) vb' = dClosure κ φ σ cl' x ∧
      ConvOk κ φ E fuel (k + 1) (setAt σ k x) vb vb'
termination_by (fuel, 1)

/-- δ clause: both unfolded faces cohere with their spines, and the
sub-ledger relates them. -/
def DeltaOk (κ : Name → List Nat → V) (φ : Name → Nat) (E : Env)
    (fuel k : Nat) (σ : Nat → V) (n : Name) (us : List Level)
    (args : List Value) (n' : Name) (us' : List Level)
    (args' : List Value) : Prop :=
  ∀ x y, unfoldNeu E fuel n us args = some x →
    unfoldNeu E fuel n' us' args' = some y →
    dVal κ φ σ x = dVal κ φ σ (.neu (.const n us) args) ∧
    dVal κ φ σ y = dVal κ φ σ (.neu (.const n' us') args') ∧
    ConvOk κ φ E fuel k σ x y
termination_by (fuel, 1)

def ArgsConvOk (κ : Name → List Nat → V) (φ : Name → Nat) (E : Env) :
    Nat → Nat → (Nat → V) → List Value → List Value → Prop
  | fuel, k, σ, a :: as, b :: bs =>
    ConvOk κ φ E fuel k σ a b ∧ ArgsConvOk κ φ E fuel k σ as bs
  | _, _, _, _, _ => True
termination_by fuel _ _ as _ => (fuel, as.length + 2)

end

variable {κ : Name → List Nat → V} {φ : Name → Nat} {E : Env}

/-- Spine congruence: equal head and pointwise-equal argument
denotations give equal spine denotations (`app` is a function — no
model fact needed at all). -/
theorem foldl_app_congr {h h' : V} (hh : h = h') :
    ∀ {xs ys : List V}, xs = ys →
      xs.foldl SetTheory.app h = ys.foldl SetTheory.app h' := by
  intro xs ys hxy
  subst hxy; subst hh; rfl

section Sound

variable {σ : Nat → V}

private theorem convArgs_sound_of {fuel : Nat}
    (hconv : ∀ (k : Nat) (σ : Nat → V) (v w : Value),
      conv E fuel k v w = some true → ConvOk κ φ E fuel k σ v w →
      dVal κ φ σ v = dVal κ φ σ w) :
    ∀ (as bs : List Value) (k : Nat) (σ : Nat → V),
      convArgs E fuel k as bs = some true → ArgsConvOk κ φ E fuel k σ as bs →
      dVals κ φ σ as = dVals κ φ σ bs := by
  intro as
  induction as with
  | nil =>
    intro bs k σ hc _
    cases bs with
    | nil => rfl
    | cons b bs => simp [convArgs] at hc
  | cons a as ih =>
    intro bs k σ hc hok
    cases bs with
    | nil => simp [convArgs] at hc
    | cons b bs =>
      simp only [convArgs] at hc
      simp only [ArgsConvOk] at hok
      cases hab : conv E fuel k a b with
      | none => simp [hab] at hc
      | some r =>
        cases r with
        | false => simp [hab] at hc
        | true =>
          simp only [hab] at hc
          simp only [dVals_cons, hconv k σ a b hab hok.1,
            ih bs k σ hc hok.2]

private theorem convBinder_sound_of {fuel : Nat}
    (hconv : ∀ (k : Nat) (σ : Nat → V) (v w : Value),
      conv E fuel k v w = some true → ConvOk κ φ E fuel k σ v w →
      dVal κ φ σ v = dVal κ φ σ w)
    {k : Nat} {d : Value} {cl : Closure} {d' : Value} {cl' : Closure}
    (hc : convBinder E fuel k d cl d' cl' = some true)
    (hok : BinderOk κ φ E fuel k σ d cl d' cl') :
    dVal κ φ σ d = dVal κ φ σ d' ∧
    ∀ x : V, x ∈ˢ dVal κ φ σ d →
      dClosure κ φ σ cl x = dClosure κ φ σ cl' x := by
  simp only [BinderOk] at hok
  obtain ⟨hokd, hbody⟩ := hok
  simp only [convBinder] at hc
  cases hdd : conv E fuel k d d' with
  | none => simp [hdd] at hc
  | some r =>
    cases r with
    | false => simp [hdd] at hc
    | true =>
      simp only [hdd] at hc
      refine ⟨hconv k σ d d' hdd hokd, ?_⟩
      intro x hx
      cases hb : applyCl E fuel cl (freshV k) with
      | none => simp [hb] at hc
      | some vb =>
        cases hb' : applyCl E fuel cl' (freshV k) with
        | none => simp [hb, hb'] at hc
        | some vb' =>
          simp only [hb, hb'] at hc
          obtain ⟨hcoh, hcoh', hokb⟩ := hbody x hx vb vb' hb hb'
          rw [← hcoh, ← hcoh']
          exact hconv (k + 1) (setAt σ k x) vb vb' hc hokb

private theorem convDelta_sound_of {fuel : Nat}
    (hconv : ∀ (k : Nat) (σ : Nat → V) (v w : Value),
      conv E fuel k v w = some true → ConvOk κ φ E fuel k σ v w →
      dVal κ φ σ v = dVal κ φ σ w)
    {k : Nat} {n : Name} {us : List Level} {args : List Value}
    {n' : Name} {us' : List Level} {args' : List Value}
    (hc : convDelta E fuel k n us args n' us' args' = some true)
    (hok : DeltaOk κ φ E fuel k σ n us args n' us' args') :
    dVal κ φ σ (.neu (.const n us) args) =
      dVal κ φ σ (.neu (.const n' us') args') := by
  simp only [DeltaOk] at hok
  simp only [convDelta] at hc
  cases hx : unfoldNeu E fuel n us args with
  | none => rw [hx] at hc; cases hc
  | some x =>
    cases hy : unfoldNeu E fuel n' us' args' with
    | none => simp [hx, hy] at hc
    | some y =>
      simp only [hx, hy] at hc
      obtain ⟨hcx, hcy, hokxy⟩ := hok x y hx hy
      rw [← hcx, ← hcy]
      exact hconv k σ x y hc hokxy

/-- **Conversion soundness**: a `some true` verdict implies equal
denotations, conditional on the conversion ledger. -/
theorem conv_sound : ∀ (fuel k : Nat) (σ : Nat → V) (v w : Value),
    conv E fuel k v w = some true → ConvOk κ φ E fuel k σ v w →
    dVal κ φ σ v = dVal κ φ σ w := by
  intro fuel
  induction fuel with
  | zero => intro k σ v w hc; simp [conv] at hc
  | succ fuel ih =>
    intro k σ v w hc hok
    cases v with
    | sort u =>
      cases w with
      | sort u' =>
        simp only [conv] at hc
        simp only [dVal]
        rw [Level.isEquiv_sound hc φ]
      | pi d' cl' => simp [conv] at hc
      | lam d' cl' => simp [conv] at hc
      | neu h' args' =>
        cases h' with
        | fvar l' => simp [conv] at hc
        | const n' us' =>
          simp only [conv] at hc
          simp only [ConvOk] at hok
          cases hy : unfoldNeu E fuel n' us' args' with
          | none => simp [hy] at hc
          | some y =>
            simp only [hy] at hc
            obtain ⟨hcoh, hok'⟩ := hok y hy
            rw [← hcoh]
            exact ih k σ _ y hc hok'
    | pi d cl =>
      cases w with
      | sort u' => simp [conv] at hc
      | pi d' cl' =>
        simp only [conv] at hc
        simp only [ConvOk] at hok
        obtain ⟨hd, hcl⟩ := convBinder_sound_of ih hc hok
        simp only [dVal]
        rw [← hd]
        exact piC_congr hcl
      | lam d' cl' => simp [conv] at hc
      | neu h' args' =>
        cases h' with
        | fvar l' => simp [conv] at hc
        | const n' us' =>
          simp only [conv] at hc
          simp only [ConvOk] at hok
          cases hy : unfoldNeu E fuel n' us' args' with
          | none => simp [hy] at hc
          | some y =>
            simp only [hy] at hc
            obtain ⟨hcoh, hok'⟩ := hok y hy
            rw [← hcoh]
            exact ih k σ _ y hc hok'
    | lam d cl =>
      cases w with
      | sort u' => simp [conv] at hc
      | pi d' cl' => simp [conv] at hc
      | lam d' cl' =>
        simp only [conv] at hc
        simp only [ConvOk] at hok
        obtain ⟨hd, hcl⟩ := convBinder_sound_of ih hc hok
        simp only [dVal]
        rw [← hd]
        exact lamC_congr hcl
      | neu h' args' =>
        cases h' with
        | fvar l' => simp [conv] at hc
        | const n' us' =>
          simp only [conv] at hc
          simp only [ConvOk] at hok
          cases hy : unfoldNeu E fuel n' us' args' with
          | none => simp [hy] at hc
          | some y =>
            simp only [hy] at hc
            obtain ⟨hcoh, hok'⟩ := hok y hy
            rw [← hcoh]
            exact ih k σ _ y hc hok'
    | neu h args =>
      cases h with
      | fvar l =>
        cases w with
        | sort u' => simp [conv] at hc
        | pi d' cl' => simp [conv] at hc
        | lam d' cl' => simp [conv] at hc
        | neu h' args' =>
          cases h' with
          | fvar l' =>
            simp only [conv] at hc
            simp only [ConvOk] at hok
            by_cases hll : l = l'
            · subst hll
              rw [if_pos rfl] at hc
              simp only [dVal]
              exact foldl_app_congr rfl (convArgs_sound_of ih args args' k σ hc hok)
            · rw [if_neg hll] at hc; simp at hc
          | const n' us' =>
            simp only [conv] at hc
            simp only [ConvOk] at hok
            cases hy : unfoldNeu E fuel n' us' args' with
            | none => simp [hy] at hc
            | some y =>
              simp only [hy] at hc
              obtain ⟨hcoh, hok'⟩ := hok y hy
              rw [← hcoh]
              exact ih k σ _ y hc hok'
      | const n us =>
        cases w with
        | sort u' =>
          simp only [conv] at hc
          simp only [ConvOk] at hok
          cases hx : unfoldNeu E fuel n us args with
          | none => simp [hx] at hc
          | some x =>
            simp only [hx] at hc
            obtain ⟨hcoh, hok'⟩ := hok x hx
            rw [← hcoh]
            exact ih k σ x _ hc hok'
        | pi d' cl' =>
          simp only [conv] at hc
          simp only [ConvOk] at hok
          cases hx : unfoldNeu E fuel n us args with
          | none => simp [hx] at hc
          | some x =>
            simp only [hx] at hc
            obtain ⟨hcoh, hok'⟩ := hok x hx
            rw [← hcoh]
            exact ih k σ x _ hc hok'
        | lam d' cl' =>
          simp only [conv] at hc
          simp only [ConvOk] at hok
          cases hx : unfoldNeu E fuel n us args with
          | none => simp [hx] at hc
          | some x =>
            simp only [hx] at hc
            obtain ⟨hcoh, hok'⟩ := hok x hx
            rw [← hcoh]
            exact ih k σ x _ hc hok'
        | neu h' args' =>
          cases h' with
          | fvar l' =>
            simp only [conv] at hc
            simp only [ConvOk] at hok
            cases hx : unfoldNeu E fuel n us args with
            | none => simp [hx] at hc
            | some x =>
              simp only [hx] at hc
              obtain ⟨hcoh, hok'⟩ := hok x hx
              rw [← hcoh]
              exact ih k σ x _ hc hok'
          | const n' us' =>
            -- The glued/glued case: spine shortcut or δ.
            simp only [conv] at hc
            simp only [ConvOk] at hok
            obtain ⟨hokArgs, hokDelta⟩ := hok
            by_cases hnn : n = n'
            · subst hnn
              rw [if_pos rfl] at hc
              cases hlv : Level.isEquivList us us' with
              | none => simp [hlv] at hc
              | some r =>
                cases r with
                | false =>
                  simp only [hlv] at hc
                  exact convDelta_sound_of ih hc hokDelta
                | true =>
                  simp only [hlv] at hc
                  cases hargs : convArgs E fuel k args args' with
                  | none => simp [hargs] at hc
                  | some r' =>
                    cases r' with
                    | false =>
                      simp only [hargs] at hc
                      exact convDelta_sound_of ih hc hokDelta
                    | true =>
                      -- The spine-equality shortcut: no unfolding, no
                      -- typing; head by `isEquiv_sound`, spine by IH.
                      simp only [dVal]
                      refine foldl_app_congr ?_
                        (convArgs_sound_of ih args args' k σ hargs hokArgs)
                      simp only [dHead]
                      rw [evalEqList_map_eq (Level.isEquivList_sound hlv φ)]
            · rw [if_neg hnn] at hc
              exact convDelta_sound_of ih hc hokDelta

end Sound

/-! ## Discharging the binder coherence: the fresh-variable lemma

The `BinderOk` coherence equations are not creative content — they are
exactly what the fundamental theorem plus scoping deliver.  This lemma
is the NbE image of the campaign's scoped-call discipline, shrunk to
one statement: the machine's fresh variable at level `k` denotes `x`
under `σ[k ↦ x]`, and everything below the frontier is unaffected. -/

theorem closure_app_coherent {σ : Nat → V} {fuel k : Nat} {x : V}
    {cl : Closure} {vb : Value}
    (h : applyCl E fuel cl (freshV k) = some vb)
    (hok : EvalOk κ φ (setAt σ k x) E fuel (freshV k :: cl.env) cl.body)
    (hsc : ScopedC k cl) :
    dVal κ φ (setAt σ k x) vb = dClosure κ φ σ cl x := by
  cases cl with
  | mk ρ b =>
    have hft := (eval_applyV_sound (κ := κ) (φ := φ) (σ := setAt σ k x)
      (E := E) fuel).1 (freshV k :: ρ) b vb h hok
    rw [hft]
    simp only [dClosure, dVals_cons, dVal_freshV_setAt]
    congr 1
    congr 1
    exact dVals_ext_σ (fun l hl => setAt_lt hl x) hsc

/-! ## Scoping is preserved by the machine

(The other half of dischargeability: machine-produced values stay below
the frontier, so `dVals_ext_σ` applies where `closure_app_coherent`
needs it.) -/

theorem scopedL_getElem : ∀ {vs : List Value} {k i : Nat} {v : Value},
    ScopedL k vs → vs[i]? = some v → ScopedV k v := by
  intro vs
  induction vs with
  | nil => intro k i v _ h; simp at h
  | cons a as ih =>
    intro k i v hs h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact h ▸ hs.1
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      exact ih hs.2 h

theorem scopedL_append : ∀ {as bs : List Value} {k : Nat},
    ScopedL k as → ScopedL k bs → ScopedL k (as ++ bs) := by
  intro as
  induction as with
  | nil => intro bs k _ hb; exact hb
  | cons a as ih => intro bs k ha hb; exact ⟨ha.1, ih ha.2 hb⟩

theorem eval_applyV_scoped : ∀ fuel : Nat,
    (∀ (ρ : List Value) (t : Term) (v : Value) (k : Nat),
      eval E fuel ρ t = some v → ScopedL k ρ → ScopedV k v) ∧
    (∀ (vf va v : Value) (k : Nat),
      applyV E fuel vf va = some v → ScopedV k vf → ScopedV k va →
      ScopedV k v) := by
  intro fuel
  induction fuel with
  | zero =>
    exact ⟨fun ρ t v k h => by simp [eval] at h,
           fun vf va v k h => by simp [applyV] at h⟩
  | succ fuel ih =>
    obtain ⟨ihE, ihA⟩ := ih
    constructor
    · intro ρ t v k hev hρ
      cases t with
      | bvar i =>
        simp only [eval] at hev
        exact scopedL_getElem hρ hev
      | sort u =>
        simp only [eval, Option.some.injEq] at hev
        subst hev; trivial
      | const n us =>
        simp only [eval] at hev
        cases hl : E.lookup n with
        | none => rw [hl] at hev; cases hev
        | some ci =>
          simp only [hl] at hev
          by_cases hlen : ci.lvlParams.length = us.length
          · rw [if_pos hlen, Option.some.injEq] at hev
            subst hev; exact ⟨trivial, trivial⟩
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
            exact ihA vf va v k hev (ihE ρ f vf k hf hρ) (ihE ρ a va k ha hρ)
      | lam d b =>
        simp only [eval] at hev
        cases hd : eval E fuel ρ d with
        | none => rw [hd] at hev; cases hev
        | some vd =>
          rw [hd, Option.some.injEq] at hev
          subst hev
          exact ⟨ihE ρ d vd k hd hρ, hρ⟩
      | pi d b =>
        simp only [eval] at hev
        cases hd : eval E fuel ρ d with
        | none => rw [hd] at hev; cases hev
        | some vd =>
          rw [hd, Option.some.injEq] at hev
          subst hev
          exact ⟨ihE ρ d vd k hd hρ, hρ⟩
    · intro vf va v k hap hvf hva
      cases vf with
      | sort u => simp [applyV] at hap
      | pi d cl => simp [applyV] at hap
      | lam dom cl =>
        cases cl with
        | mk ρ b =>
          simp only [applyV] at hap
          exact ihE (va :: ρ) b v k hap ⟨hva, hvf.2⟩
      | neu h args =>
        simp only [applyV, Option.some.injEq] at hap
        subst hap
        exact ⟨hvf.1, scopedL_append hvf.2 ⟨hva, trivial⟩⟩

end Setlec.NbE
