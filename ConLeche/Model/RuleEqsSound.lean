module

public import ConLeche.Model.Denotes
import ConLeche.Verify.Denote.Shift
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Model.IndTele
public import ConLeche.Model.IndFrame
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.IndPointKit
import ConLeche.Verify.Denote.OpenRevDenote
import ConLeche.Model.Reading.Levels

public section

/-!
# The recursor rules' equations hold in the model the invariant carries

`ConLeche.Model.rule_eqs` (`ConLeche/Denotes.lean`) asks every stored recursor rule's ι equation
(`ConLeche.iotaEq`: `∀ prefix fields, @Eq (motive indices major) (rec prefix indices major)
(rhs prefix fields)`), wherever it denotes, to denote an inhabited set.  This module derives it
from the invariant's two rule facts: `RecRuleLaw` (the fired equation, at a fit of the
recursor's telescope) and `RecRuleFit` (that fit, from a fit of the prefix and the fields).

* §1 the converse substitution lemmas over `Denotes`: a lifted or instantiated term denotes
  only what its source denotes at the matching environment;
* §0 the vocabulary: `Fits`, the telescope fit over `Denotes`, and its reading
  (`teleFit_of_Fits`); the constructor levels as the fired comparands (`substFn_ctorLevels`);
* §2 telescopes over `Denotes`: an equation's `∀`-telescope denotes an inhabited truth value
  where its body does at every fit;
-/

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.SetModel ConLeche.Verify SetTheory
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule)
open ConLeche.Expr (closeN)

universe w

variable {V : Type w} [SetTheory V]

/-! ## 0. Vocabulary: telescope fits over `Denotes`, the constructor levels, the environments a
lift or an instantiation reads its source in -/

/-- `Fits cval env φ ρ T xs ρ' R`: the sets `xs` fit the leading `∀`
binders of `T` read at `ρ` — each a member of what its domain denotes,
the domain read with the earlier sets pushed — and `R` is the rest of
`T`, to be read at `ρ'`, which is `ρ` with `xs` pushed. -/
inductive Fits (cval : Name → (Name → Nat) → V) (env : Env) (φ : Name → Nat) :
    (Nat → V) → Expr → List V → (Nat → V) → Expr → Prop
  | nil {ρ : Nat → V} {T : Expr} : Fits cval env φ ρ T [] ρ T
  | cons {ρ ρ' : Nat → V} {A B R : Expr} {A' x : V} {xs : List V}
      (hA : ConLeche.Denotes cval env φ ρ A A') (hx : x ∈ˢ A')
      (h : Fits cval env φ (ConLeche.push x ρ) B xs ρ' R) :
      Fits cval env φ ρ (.forallE A B) (x :: xs) ρ' R

/-- **A fit against a stored type is a fit against its reading.** -/
theorem teleFit_of_Fits {acval : Name → (Name → Nat) → Term}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ)) {env : Env} {φ : Name → Nat} :
    ∀ (xs : List V) (d : Nat) (e : Expr) {ta : Term} {ρ ρ' : Nat → V} {R : Expr},
      denote acval env φ d e = some ta → Expr.fvarsBelow d e →
      e.looseBVarsBounded 0 = true →
      Fits (cvalOf (V := V) acval) env φ ρ (closeN d e) xs ρ' R →
      ∃ rest, TeleFit V ρ ta xs rest
  | [], _, _, _, _, _, _, _, _, _, _ => ⟨_, .nil⟩
  | x :: xs, d, e, ta, ρ, ρ', R, h, hfb, hlb, hfit => by
    cases e with
    | forallE ty body =>
      obtain ⟨tA, bA, hta, hba, rfl⟩ := denote_forallE_inv h
      have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d body := hfb
      have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
      rw [Bool.and_eq_true] at hlb'
      have hc : closeN d (.forallE ty body) = .forallE (closeN d ty 0) (closeN d body 1) := rfl
      rw [hc] at hfit
      cases hfit with
      | cons hA hx hrest =>
        have hA' := Denotes_of_denote (V := V) hcl d ty hta hfb'.1 hlb'.1 ρ
        obtain rfl := ConLeche.Denotes_functional hA hA'
        rw [← Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2, push_eq_cons] at hrest
        obtain ⟨rest, hr⟩ := teleFit_of_Fits hcl xs (d + 1) _ hba
          (Expr.fvarsBelow_instantiate1 0 hfb'.2)
          (ConLeche.looseBVarsBounded_instantiate1 body 0 hlb'.2) hrest
        exact ⟨rest, .cons hx hr⟩
    | _ => cases hfit

/-- A peeled telescope's body is scoped by the binders peeled. -/
theorem PiTeleAV.bvarsBelow_rest : ∀ {n : Nat} {T : Term} {Γ : List Term} {R : Term},
    PiTeleAV n T Γ R → ∀ {k : Nat}, Term.bvarsBelow k T → Term.bvarsBelow (k + n) R
  | _, _, _, _, .nil, _, h => h
  | _, _, _, _, @PiTeleAV.cons n _ _ _ _ h', k, h => by
    have := PiTeleAV.bvarsBelow_rest h' (k := k + 1) h.2
    rwa [show k + 1 + n = k + (n + 1) by omega] at this

/-- **A fit of a peeled telescope's body, the peeled binders' values pushed**, is a fit past
them (`TeleSkipFit`). -/
theorem teleSkipFit_of_piTele : ∀ {n : Nat} {T : Term} {Γ : List Term} {R : Term},
    PiTeleAV n T Γ R → ∀ {ps fs : List V} {ρ : Nat → V} {rest : V}, ps.length = n →
      TeleFit V (consN ps ρ) R fs rest → TeleSkipFit V ρ T ps fs rest
  | _, _, _, _, .nil, ps, _, _, _, hl, h => by
    obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero hl
    exact .fit h
  | _, _, _, _, .cons h', p :: ps, _, _, _, hl, h =>
    .skip (teleSkipFit_of_piTele h' (by simpa using hl) h)

/-- Levels read alike at `φ` give one composed assignment. -/
theorem substFn_map_subst_self (φ : Name → Nat) (lps : List Name) :
    ∀ (ks : List Name) (vs : List Level),
      Level.substFn φ ks (vs.map (Level.subst lps (lps.map Level.param)))
        = Level.substFn φ ks vs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | k :: ks, v :: vs => by
    funext q
    simp only [List.map_cons, Level.substFn]
    rw [Level.eval_subst, Level.substFn_param_self, substFn_map_subst_self φ lps ks vs]

/-- **The spec's constructor levels are the fired comparands** at the recursor's own levels. -/
theorem substFn_ctorLevels (φ : Name → Nat) (rl : RecRule) (cnP : Nat) (lps cvjLps : List Name)
    (rP : Nat) :
    Level.substFn φ cvjLps (rl.ctorLevels cvjLps)
      = Level.substFn φ cvjLps
          (ConLeche.recFireComparands rl cnP lps (lps.map Level.param) cvjLps [] rP).1 := by
  unfold RecRule.ctorLevels ConLeche.recFireComparands
  split <;> rename_i h <;> simp only [h]
  · exact (substFn_map_subst_self φ lps cvjLps _).symm
  · exact (substFn_map_subst_self φ lps cvjLps _).symm
  · rw [show cvjLps.map (fun p => Level.subst lps (lps.map Level.param) (.param p))
        = (cvjLps.map Level.param).map (Level.subst lps (lps.map Level.param)) by
      rw [List.map_map]; rfl]
    exact (substFn_map_subst_self φ lps cvjLps _).symm

/-- A list of variables read in an environment holding a list. -/
theorem map_interp_bvars (σ : Nat → V) (o : Nat) (zs : List V)
    (hσ : ∀ i (h : i < zs.length), σ (o + i) = zs[i]) :
    ((List.range zs.length).map fun i => Term.bvar (o + i)).map (interp V σ) = zs := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, interp_bvar]
  exact hσ i (by simpa using h1)

/-- The environment a lift by `k` at cutoff `c` reads its source in. -/
@[expose] def skipAt (c k : Nat) (ρ : Nat → V) : Nat → V := fun i => if i < c then ρ i else ρ (i + k)

omit [SetTheory V] in
theorem push_skipAt (x : V) (c k : Nat) (ρ : Nat → V) :
    ConLeche.push x (skipAt c k ρ) = skipAt (c + 1) k (ConLeche.push x ρ) := by
  funext i
  cases i with
  | zero => simp [skipAt, ConLeche.push]
  | succ i =>
    by_cases h : i < c
    · have h' : i + 1 < c + 1 := by omega
      simp [skipAt, ConLeche.push, h, h']
    · have h' : ¬ i + 1 < c + 1 := by omega
      simp [skipAt, ConLeche.push, h, h', show i + 1 + k = i + k + 1 by omega]

theorem strLitToConstructor_looseBVarsBounded (s : String) (c : Nat) :
    (ConLeche.strLitToConstructor s).looseBVarsBounded c = true := by
  unfold ConLeche.strLitToConstructor
  simp only [Expr.looseBVarsBounded, Bool.true_and]
  induction s.toList with
  | nil => simp [Expr.looseBVarsBounded]
  | cons a l ih => simp [Expr.looseBVarsBounded, ih]

theorem natLitToConstructor_looseBVarsBounded' (n c : Nat) :
    (ConLeche.natLitToConstructor n).looseBVarsBounded c = true := by
  cases n <;> simp [ConLeche.natLitToConstructor, Expr.looseBVarsBounded]

/-- The environment an instantiation at depth `d` reads its source in:
`ρ` below `d`, the values' denotations `Ys` next, `ρ` lowered above. -/
@[expose] def insAt (d : Nat) (Ys : List V) (ρ : Nat → V) : Nat → V := fun i =>
  if i < d then ρ i else if h : i - d < Ys.length then Ys[i - d] else ρ (i - Ys.length)

omit [SetTheory V] in
theorem push_insAt (x : V) (d : Nat) (Ys : List V) (ρ : Nat → V) :
    ConLeche.push x (insAt d Ys ρ) = insAt (d + 1) Ys (ConLeche.push x ρ) := by
  funext i
  cases i with
  | zero => simp [insAt, ConLeche.push]
  | succ i =>
    by_cases h : i < d
    · have h1 : i + 1 < d + 1 := by omega
      simp [insAt, ConLeche.push, h, h1]
    · have h1 : ¬ i + 1 < d + 1 := by omega
      have h2 : i + 1 - (d + 1) = i - d := by omega
      by_cases h' : i - d < Ys.length
      · simp [insAt, ConLeche.push, h, h1, h2, h']
      · have h3 : i + 1 - Ys.length = (i - Ys.length) + 1 := by omega
        simp [insAt, ConLeche.push, h, h1, h2, h', h3]

section Subst

variable {cval : Name → (Name → Nat) → V} {env : Env} {φ : Name → Nat}

/-! ## 1. Converse substitution over `Denotes` -/

/-- **A term reads alike in environments agreeing below its loose variables.** -/
theorem Denotes_congr_below :
    ∀ {ρ : Nat → V} {e : Expr} {X : V}, ConLeche.Denotes cval env φ ρ e X →
    ∀ {k : Nat} {ρ' : Nat → V}, e.looseBVarsBounded k = true → (∀ i, i < k → ρ i = ρ' i) →
      ConLeche.Denotes cval env φ ρ' e X := by
  intro ρ e X h
  induction h with
  | bvar =>
    rename_i ρ i
    intro k ρ' hb hag
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    rw [hag i hb]; exact .bvar
  | sort => intro _ _ _ _; exact .sort
  | const hf hl => intro _ _ _ _; exact .const hf hl
  | app _ _ ihf iha =>
    intro k ρ' hb hag
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact .app (ihf hb.1 hag) (iha hb.2 hag)
  | lam _ _ ihA ihF =>
    intro k ρ' hb hag
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact .lam (ihA hb.1 hag) fun x hx => ihF x hx hb.2 fun i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
  | pi _ _ ihA ihB =>
    intro k ρ' hb hag
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact .pi (ihA hb.1 hag) fun x hx => ihB x hx hb.2 fun i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
  | letE _ _ ihv ihb =>
    intro k ρ' hb hag
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact .letE (ihv hb.1.2 hag) (ihb hb.2 fun i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hag i (by omega))
  | proj_table ht _ ih =>
    intro k ρ' hb hag
    exact .proj_table ht (ih hb hag)
  | natLit _ ih =>
    rename_i n _ _
    intro k ρ' _ hag
    exact .natLit (ih (natLitToConstructor_looseBVarsBounded' n 0)
      fun i hi => absurd hi (Nat.not_lt_zero _))
  | strLit _ ih =>
    rename_i s _ _
    intro k ρ' _ hag
    exact .strLit (ih (strLitToConstructor_looseBVarsBounded s 0)
      fun i hi => absurd hi (Nat.not_lt_zero _))

/-- A literal reads alike in every environment. -/
theorem Denotes_lit_any {ρ ρ' : Nat → V} {l : ConLeche.Literal} {X : V}
    (h : ConLeche.Denotes cval env φ ρ (.lit l) X) : ConLeche.Denotes cval env φ ρ' (.lit l) X :=
  Denotes_congr_below h (k := 0) rfl fun _ hi => absurd hi (Nat.not_lt_zero _)

/-- **Lifting, conversely**: a lifted term denotes only what its source denotes where the lift's
`k` variables are skipped. -/
theorem Denotes_liftLooseBVars_inv {k : Nat} :
    ∀ (e : Expr) {c : Nat} {ρ : Nat → V} {X : V},
      ConLeche.Denotes cval env φ ρ (e.liftLooseBVars k c) X →
      ConLeche.Denotes cval env φ (skipAt c k ρ) e X
  | .bvar i, c, ρ, X, h => by
    by_cases hi : c ≤ i
    · simp only [Expr.liftLooseBVars, ge_iff_le, hi, ↓reduceIte] at h
      cases h
      have : skipAt c k ρ i = ρ (i + k) := by simp [skipAt, Nat.not_lt.mpr hi]
      rw [← this]; exact .bvar
    · simp only [Expr.liftLooseBVars, ge_iff_le, hi, ↓reduceIte] at h
      cases h
      have : skipAt c k ρ i = ρ i := by simp [skipAt, Nat.lt_of_not_le hi]
      rw [← this]; exact .bvar
  | .fvar _ _, _, _, _, h => by cases h
  | .sort _, _, _, _, h => by cases h; exact .sort
  | .const _ _, _, _, _, h => by cases h with | const hf hl => exact .const hf hl
  | .app f a, _, _, _, h => by
    cases h with
    | app hf ha => exact .app (Denotes_liftLooseBVars_inv f hf) (Denotes_liftLooseBVars_inv a ha)
  | .lam ty b, c, ρ, _, h => by
    cases h with
    | lam hA hF =>
      exact .lam (Denotes_liftLooseBVars_inv ty hA) fun x hx => by
        rw [push_skipAt]; exact Denotes_liftLooseBVars_inv b (hF x hx)
  | .forallE ty b, c, ρ, _, h => by
    cases h with
    | pi hA hB =>
      exact .pi (Denotes_liftLooseBVars_inv ty hA) fun x hx => by
        rw [push_skipAt]; exact Denotes_liftLooseBVars_inv b (hB x hx)
  | .letE ty v b, c, ρ, _, h => by
    cases h with
    | letE hv hb =>
      exact .letE (Denotes_liftLooseBVars_inv v hv) (by
        rw [push_skipAt]; exact Denotes_liftLooseBVars_inv b hb)
  | .lit _, _, _, _, h => Denotes_lit_any h
  | .proj _ _ e, _, _, _, h => by
    cases h with
    | proj_table ht he => exact .proj_table ht (Denotes_liftLooseBVars_inv e he)

/-- **Instantiation, conversely**: an instantiated term denotes only what its source denotes with
the values' denotations in place of the instantiated variables. -/
theorem Denotes_instantiateLift_inv {vs : List Expr} {Ys : List V} {σ : Nat → V}
    (hlen : Ys.length = vs.length)
    (hvs : ∀ j (h : j < vs.length), ConLeche.Denotes cval env φ σ vs[j] (Ys[j]'(hlen ▸ h))) :
    ∀ (e : Expr) {d : Nat} {ρ : Nat → V} {X : V}, (∀ i, ρ (i + d) = σ i) →
      ConLeche.Denotes cval env φ ρ (e.instantiateLift vs d) X →
      ConLeche.Denotes cval env φ (insAt d Ys ρ) e X
  | .bvar i, d, ρ, X, hσ, h => by
    by_cases hi : i < d
    · simp only [Expr.instantiateLift, hi, ↓reduceIte] at h
      cases h
      have : insAt d Ys ρ i = ρ i := by simp [insAt, hi]
      rw [← this]; exact .bvar
    · by_cases hj : i - d < vs.length
      · simp only [Expr.instantiateLift, hi, ↓reduceIte, hj, dite_true] at h
        have h' := Denotes_liftLooseBVars_inv (k := d) (c := 0) _ h
        have hsk : skipAt 0 d ρ = σ := by
          funext q; simp [skipAt, ← hσ q]
        rw [hsk] at h'
        obtain rfl := ConLeche.Denotes_functional h' (hvs _ hj)
        have hj' : i - d < Ys.length := by rw [hlen]; exact hj
        have : insAt d Ys ρ i = Ys[i - d] := by simp [insAt, hi, hj']
        rw [← this]; exact .bvar
      · simp only [Expr.instantiateLift, hi, ↓reduceIte, hj, dite_false] at h
        cases h
        have hj' : ¬ i - d < Ys.length := by rw [hlen]; exact hj
        have : insAt d Ys ρ i = ρ (i - vs.length) := by simp only [insAt, hi, ↓reduceIte, hlen, hj, dite_false]
        rw [← this]; exact .bvar
  | .fvar _ _, _, _, _, _, h => by cases h
  | .sort _, _, _, _, _, h => by cases h; exact .sort
  | .const _ _, _, _, _, _, h => by cases h with | const hf hl => exact .const hf hl
  | .app f a, _, _, _, hσ, h => by
    cases h with
    | app hf ha =>
      exact .app (Denotes_instantiateLift_inv hlen hvs f hσ hf)
        (Denotes_instantiateLift_inv hlen hvs a hσ ha)
  | .lam ty b, d, ρ, _, hσ, h => by
    cases h with
    | lam hA hF =>
      exact .lam (Denotes_instantiateLift_inv hlen hvs ty hσ hA) fun x hx => by
        rw [push_insAt]
        exact Denotes_instantiateLift_inv hlen hvs b
          (fun i => by rw [show i + (d + 1) = (i + d) + 1 by omega]; exact hσ i) (hF x hx)
  | .forallE ty b, d, ρ, _, hσ, h => by
    cases h with
    | pi hA hB =>
      exact .pi (Denotes_instantiateLift_inv hlen hvs ty hσ hA) fun x hx => by
        rw [push_insAt]
        exact Denotes_instantiateLift_inv hlen hvs b
          (fun i => by rw [show i + (d + 1) = (i + d) + 1 by omega]; exact hσ i) (hB x hx)
  | .letE ty v b, d, ρ, _, hσ, h => by
    cases h with
    | letE hv hb =>
      refine .letE (Denotes_instantiateLift_inv hlen hvs v hσ hv) ?_
      rw [push_insAt]
      exact Denotes_instantiateLift_inv hlen hvs b
        (fun i => by rw [show i + (d + 1) = (i + d) + 1 by omega]; exact hσ i) hb
  | .lit _, _, _, _, _, h => Denotes_lit_any h
  | .proj _ _ e, _, _, _, hσ, h => by
    cases h with
    | proj_table ht he => exact .proj_table ht (Denotes_instantiateLift_inv hlen hvs e hσ he)

/-! ## 2. Telescopes over `Denotes` -/

/-- **A `∀`-telescope over inhabited truth values is one**: where at every fit of its binders
the body denotes an inhabited truth value, so does the telescope. -/
theorem tele_inhabited_of : ∀ (ds : List Expr) {ρ : Nat → V} {body : Expr} {P : V},
    ConLeche.Denotes cval env φ ρ (ds.foldr .forallE body) P →
    (∀ (vs : List V) (ρ' : Nat → V) (Y : V), vs.length = ds.length →
      Fits cval env φ ρ (ds.foldr .forallE body) vs ρ' body →
      ConLeche.Denotes cval env φ ρ' body Y → Y ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ Y) →
    P ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ P
  | [], _, _, _, h, hY => hY [] _ _ rfl .nil h
  | d :: ds, ρ, body, _, h, hY => by
    cases h with
    | pi hA hB =>
      rename_i A B
      have hz : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ B x := fun x hx =>
        tele_inhabited_of ds (hB x hx) fun vs ρ' Y hl hf hYd =>
          hY (x :: vs) ρ' Y (by simp [hl]) (.cons hA hx hf) hYd
      refine ⟨?_, ?_⟩
      · rw [piV_eq_zero fun x hx => (hz x hx).1]; exact piR_zero_mem_univZero
      · exact (pt_mem_piV_iff fun x hx => Or.inl (hz x hx).1).mpr fun x hx => (hz x hx).2

/-- The empty fit is no fit. -/
theorem Fits.nil_inv {ρ ρ' : Nat → V} {T R : Expr}
    (h : Fits cval env φ ρ T [] ρ' R) : ρ' = ρ ∧ R = T := by
  generalize hv : ([] : List V) = vs at h
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons => exact nomatch hv

/-- **A fit of a telescope's binders**, in one statement: it splits at any point into a fit of
the leading binders and one of the rest, it does not read the body, and its environment is the
values pushed. -/
theorem Fits.foldr_aux {ρ ρ' : Nat → V} {T R : Expr} {vs : List V}
    (h : Fits cval env φ ρ T vs ρ' R) :
    ∀ (ds : List Expr) (b : Expr), T = ds.foldr .forallE b → R = b → vs.length = ds.length →
      (∀ b', Fits cval env φ ρ (ds.foldr .forallE b') vs ρ' b') ∧
      ρ' = vs.foldl (fun r x => ConLeche.push x r) ρ := by
  induction h with
  | nil =>
    intro ds b hT hR hl
    obtain rfl : ds = [] := List.eq_nil_of_length_eq_zero hl.symm
    exact ⟨fun _ => .nil, rfl⟩
  | cons hA hx _ ih =>
    intro ds b hT hR hl
    match ds, hl with
    | d :: ds, hl =>
      simp only [List.foldr_cons, Expr.forallE.injEq] at hT
      obtain ⟨rfl, rfl⟩ := hT
      obtain ⟨h1, h2⟩ := ih ds b rfl hR (by simpa using hl)
      exact ⟨fun b' => .cons hA hx (h1 b'), h2⟩

/-- A fit of a telescope's binders does not read its body. -/
theorem Fits.rebody {ds : List Expr} {ρ ρ' : Nat → V} {b b' : Expr} {vs : List V}
    (hl : vs.length = ds.length) (h : Fits cval env φ ρ (ds.foldr .forallE b) vs ρ' b) :
    Fits cval env φ ρ (ds.foldr .forallE b') vs ρ' b' :=
  (h.foldr_aux ds b rfl rfl hl).1 b'

/-- A full fit's environment is the values pushed, the last one innermost. -/
theorem Fits.env_eq {ds : List Expr} {ρ ρ' : Nat → V} {b : Expr} {vs : List V}
    (hl : vs.length = ds.length) (h : Fits cval env φ ρ (ds.foldr .forallE b) vs ρ' b) :
    ρ' = vs.foldl (fun r x => ConLeche.push x r) ρ :=
  (h.foldr_aux ds b rfl rfl hl).2

/-- Fits compose along a telescope. -/
theorem Fits.append {ρ ρ₁ ρ' : Nat → V} {T R R' : Expr} {vs ws : List V}
    (h1 : Fits cval env φ ρ T vs ρ₁ R) (h2 : Fits cval env φ ρ₁ R ws ρ' R') :
    Fits cval env φ ρ T (vs ++ ws) ρ' R' := by
  induction h1 with
  | nil => exact h2
  | cons hA hx _ ih => exact .cons hA hx (ih h2)

/-- A fit of an appended list splits at the append. -/
theorem Fits.split {ρ ρ' : Nat → V} {T R : Expr} {vs ws : List V}
    (h : Fits cval env φ ρ T (vs ++ ws) ρ' R) :
    ∃ ρ₁ R₁, Fits cval env φ ρ T vs ρ₁ R₁ ∧ Fits cval env φ ρ₁ R₁ ws ρ' R := by
  induction vs generalizing ρ T with
  | nil => exact ⟨ρ, T, .nil, h⟩
  | cons v vs ih =>
    generalize hv : (v :: vs) ++ ws = us at h
    cases h with
    | nil => exact nomatch hv
    | cons hA hx hr =>
      simp only [List.cons_append, List.cons.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      obtain ⟨ρ₁, R₁, h1, h2⟩ := ih hr
      exact ⟨ρ₁, R₁, .cons hA hx h1, h2⟩

/-- A fit's residual of a closed telescope, read: the fit at the reading, with the residual's
value (`teleFit_of_Fits` with its residual). -/
theorem teleFit_of_Fits_rest {acval : Name → (Name → Nat) → Term}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ)) {env : Env} {φ : Name → Nat} :
    ∀ (xs : List V) (d : Nat) (e : Expr) {ta : Term} {ρ ρ' : Nat → V} {R : Expr} {Y : V},
      denote acval env φ d e = some ta → Expr.fvarsBelow d e →
      e.looseBVarsBounded 0 = true →
      Fits (cvalOf (V := V) acval) env φ ρ (closeN d e) xs ρ' R →
      ConLeche.Denotes (cvalOf (V := V) acval) env φ ρ' R Y →
      TeleFit V ρ ta xs Y
  | [], d, e, ta, ρ, ρ', R, Y, h, hfb, hlb, hfit, hY => by
    obtain ⟨rfl, rfl⟩ := hfit.nil_inv
    have hD := Denotes_of_denote (V := V) hcl d e h hfb hlb ρ'

    obtain rfl := ConLeche.Denotes_functional hY hD
    exact .nil
  | x :: xs, d, e, ta, ρ, ρ', R, Y, h, hfb, hlb, hfit, hY => by
    cases e with
    | forallE ty body =>
      obtain ⟨tA, bA, hta, hba, rfl⟩ := denote_forallE_inv h
      have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d body := hfb
      have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
      rw [Bool.and_eq_true] at hlb'
      have hc : closeN d (.forallE ty body) = .forallE (closeN d ty 0) (closeN d body 1) := rfl
      rw [hc] at hfit
      cases hfit with
      | cons hA hx hrest =>
        have hA' := Denotes_of_denote (V := V) hcl d ty hta hfb'.1 hlb'.1 ρ
        obtain rfl := ConLeche.Denotes_functional hA hA'
        rw [← Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2, push_eq_cons] at hrest
        exact .cons hx (teleFit_of_Fits_rest hcl xs (d + 1) _ hba
          (Expr.fvarsBelow_instantiate1 0 hfb'.2)
          (ConLeche.looseBVarsBounded_instantiate1 body 0 hlb'.2) hrest hY)
    | _ => cases hfit

/-- Instantiating a variable keeps a term's leading binders. -/
theorem stripPis_isSome_instantiate1 : ∀ (n : Nat) (e v : Expr) (c : Nat),
    (e.stripPis n).isSome = true → ((e.instantiate1 v c).stripPis n).isSome = true
  | 0, _, _, _, _ => rfl
  | n + 1, .forallE ty b, v, c, h => by
    simp only [Expr.stripPis, Expr.instantiate1, Option.isSome_map] at h ⊢
    exact stripPis_isSome_instantiate1 n b v (c + 1) h
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _, _, _, h
  | _ + 1, .letE _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h => by
    simp [Expr.stripPis] at h

/-- **The converse**: a fit at the reading of a closed telescope is a fit of the telescope,
its residual denoting the fit's residual value. -/
theorem Fits_of_teleFit {acval : Name → (Name → Nat) → Term}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ)) {env : Env} {φ : Name → Nat} :
    ∀ (xs : List V) (d : Nat) (e : Expr) {ta : Term} {ρ : Nat → V} {Y : V},
      denote acval env φ d e = some ta → Expr.fvarsBelow d e →
      e.looseBVarsBounded 0 = true → (e.stripPis xs.length).isSome = true →
      TeleFit V ρ ta xs Y →
      ∃ ρ' R, Fits (cvalOf (V := V) acval) env φ ρ (closeN d e) xs ρ' R ∧
        ConLeche.Denotes (cvalOf (V := V) acval) env φ ρ' R Y
  | [], d, e, ta, ρ, Y, h, hfb, hlb, _, hfit => by
    obtain rfl := teleFit_nil_inv hfit
    exact ⟨ρ, _, .nil, Denotes_of_denote (V := V) hcl d e h hfb hlb ρ⟩
  | x :: xs, d, e, ta, ρ, Y, h, hfb, hlb, hs, hfit => by
    cases e with
    | forallE ty body =>
      obtain ⟨tA, bA, hta, hba, rfl⟩ := denote_forallE_inv h
      have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d body := hfb
      have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
      rw [Bool.and_eq_true] at hlb'
      cases hfit with
      | cons hx hrest =>
        have hA' := Denotes_of_denote (V := V) hcl d ty hta hfb'.1 hlb'.1 ρ
        have hs' : (body.stripPis xs.length).isSome = true := by
          simpa [Expr.stripPis, Option.isSome_map] using hs
        obtain ⟨ρ', R, hF, hR⟩ := Fits_of_teleFit hcl xs (d + 1) _ hba
          (Expr.fvarsBelow_instantiate1 0 hfb'.2)
          (ConLeche.looseBVarsBounded_instantiate1 body 0 hlb'.2)
          (stripPis_isSome_instantiate1 _ _ _ _ hs') hrest
        rw [Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2, ← push_eq_cons] at hF
        exact ⟨ρ', R, .cons hA' hx hF, hR⟩
    | _ => all_goals simp [Expr.stripPis] at hs

/-! ## 3. Syntax: telescopes and spines -/

/-- A peeled telescope is its binders over its body. -/
theorem stripPis_eq_foldr : ∀ (k : Nat) {e : Expr} {ds : List Expr} {b : Expr},
    e.stripPis k = some (ds, b) → e = ds.foldr .forallE b ∧ ds.length = k
  | 0, e, ds, b, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | k + 1, e, ds, b, h => by
    match e, h with
    | .forallE ty bo, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨ds', b'⟩, hs, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨rfl, hl⟩ := stripPis_eq_foldr k hs
      exact ⟨rfl, by simp [hl]⟩

/-- A telescope peels to its binders and body. -/
theorem stripPis_foldr : ∀ (ds : List Expr) (b : Expr),
    (ds.foldr .forallE b).stripPis ds.length = some (ds, b)
  | [], _ => rfl
  | d :: ds, b => by
    simp only [List.foldr_cons, List.length_cons, Expr.stripPis, stripPis_foldr ds b,
      Option.map_some]

/-- A telescope's body is bounded past its binders. -/
theorem looseBVarsBounded_foldr_body : ∀ (ds : List Expr) {b : Expr} {j : Nat},
    (ds.foldr .forallE b).looseBVarsBounded j = true → b.looseBVarsBounded (j + ds.length) = true
  | [], _, _, h => h
  | _ :: ds, _, j, h => by
    simp only [List.foldr_cons, Expr.looseBVarsBounded, Bool.and_eq_true] at h
    have := looseBVarsBounded_foldr_body ds h.2
    rwa [show j + 1 + ds.length = j + (ds.length + 1) by omega] at this

/-- A telescope's binders are bounded at their depth. -/
theorem looseBVarsBounded_foldr_dom : ∀ (ds : List Expr) {b : Expr} {j : Nat},
    (ds.foldr .forallE b).looseBVarsBounded j = true →
    ∀ i (h : i < ds.length), ds[i].looseBVarsBounded (j + i) = true
  | [], _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: ds, _, j, h, i, hi => by
    simp only [List.foldr_cons, Expr.looseBVarsBounded, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := looseBVarsBounded_foldr_dom ds h.2 i (by simpa using hi)
      simpa [show j + 1 + i = j + (i + 1) by omega] using this

/-- A telescope without free variables has none in its body. -/
theorem hasFvar_foldr_body : ∀ (ds : List Expr) {b : Expr},
    (ds.foldr .forallE b).hasFvar = false → b.hasFvar = false
  | [], _, h => h
  | _ :: ds, _, h => by
    simp only [List.foldr_cons, Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact hasFvar_foldr_body ds h.2

/-- A telescope's free variables bound its body's. -/
theorem fvarsBelow_foldr_body : ∀ (ds : List Expr) {b : Expr} {d : Nat},
    Expr.fvarsBelow d (ds.foldr .forallE b) → Expr.fvarsBelow d b
  | [], _, _, h => h
  | _ :: ds, _, _, h => fvarsBelow_foldr_body ds h.2

/-- Instantiation runs through a telescope, binder by binder. -/
theorem instantiateLift_foldr (vs : List Expr) : ∀ (ds : List Expr) (b : Expr) (d : Nat),
    ∃ ds' : List Expr, ds'.length = ds.length ∧
      (ds.foldr .forallE b).instantiateLift vs d
        = ds'.foldr .forallE (b.instantiateLift vs (d + ds.length)) ∧
      ∀ i (h : i < ds.length) (h' : i < ds'.length), ds'[i] = ds[i].instantiateLift vs (d + i)
  | [], _, _ => ⟨[], rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | x :: ds, b, d => by
    obtain ⟨ds', hl, he, hi⟩ := instantiateLift_foldr vs ds b (d + 1)
    refine ⟨x.instantiateLift vs d :: ds', by simp [hl], ?_, fun i h h' => ?_⟩
    · simp only [List.foldr_cons, Expr.instantiateLift, he, List.length_cons,
        show d + 1 + ds.length = d + (ds.length + 1) by omega]
    · cases i with
      | zero => rfl
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [hi i (by simpa using h) (by simpa using h'), show d + 1 + i = d + (i + 1) by omega]

/-- An application spine's arguments survive closing. -/
theorem getAppArgs_closeN (D : Nat) : ∀ (e : Expr) (c : Nat),
    (closeN D e c).getAppArgs = e.getAppArgs.map (closeN D · c)
  | .app f a, c => by
    simp only [closeN, Expr.getAppArgs, getAppArgs_closeN D f c, List.map_append, List.map_cons,
      List.map_nil]
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lam _ _, _ | .forallE _ _, _
  | .letE _ _ _, _ | .lit _, _ | .proj _ _ _, _ => rfl

/-- At a constant head, instantiation maps the spine's arguments. -/
theorem getAppArgs_instantiateLift (vs : List Expr) (d : Nat) : ∀ (e : Expr),
    (∃ n us, e.getAppFn = .const n us) →
    (e.instantiateLift vs d).getAppArgs = e.getAppArgs.map (·.instantiateLift vs d)
  | .app f a, h => by
    simp only [Expr.getAppFn] at h
    simp only [Expr.instantiateLift, Expr.getAppArgs, getAppArgs_instantiateLift vs d f h,
      List.map_append, List.map_cons, List.map_nil]
  | .const _ _, _ => rfl
  | .bvar _, ⟨_, _, h⟩ | .fvar _ _, ⟨_, _, h⟩ | .sort _, ⟨_, _, h⟩ | .lam _ _, ⟨_, _, h⟩
  | .forallE _ _, ⟨_, _, h⟩ | .letE _ _ _, ⟨_, _, h⟩ | .lit _, ⟨_, _, h⟩
  | .proj _ _ _, ⟨_, _, h⟩ => by simp [Expr.getAppFn] at h

/-- **An application spine, inverted over `Denotes`.** -/
theorem Denotes_mkAppN_inv : ∀ (as : List Expr) {f : Expr} {ρ : Nat → V} {X : V},
    ConLeche.Denotes cval env φ ρ (Expr.mkAppN f as) X →
    ∃ (F : V) (Xs : List V), ConLeche.Denotes cval env φ ρ f F ∧ Xs.length = as.length ∧
      (∀ i (h : i < as.length) (h' : i < Xs.length),
        ConLeche.Denotes cval env φ ρ as[i] Xs[i]) ∧ X = Xs.foldl app F
  | [], _, _, _, h => ⟨_, [], h, rfl, fun _ h => absurd h (Nat.not_lt_zero _), rfl⟩
  | a :: as, f, ρ, X, h => by
    obtain ⟨F, Xs, hF, hl, hXs, rfl⟩ := Denotes_mkAppN_inv as h
    cases hF with
    | app hf ha =>
      refine ⟨_, _ :: Xs, hf, by simp [hl], fun i h h' => ?_, rfl⟩
      cases i with
      | zero => exact ha
      | succ i => exact hXs i (by simpa using h) (by simpa using h')

/-! ## 4. Readings: residuals and transfers -/

/-- **A fit of a telescope's leading binders**: its residual is the rest of the telescope, its
environment the values pushed, and it does not read the body. -/
theorem Fits.foldr_prefix {ρ ρ' : Nat → V} {T R : Expr} {vs : List V}
    (h : Fits cval env φ ρ T vs ρ' R) :
    ∀ (ds : List Expr) (b : Expr), T = ds.foldr .forallE b → vs.length ≤ ds.length →
      R = (ds.drop vs.length).foldr .forallE b ∧ ρ' = consN vs ρ ∧
      ∀ b', Fits cval env φ ρ ((ds.take vs.length).foldr .forallE b') vs ρ' b' := by
  induction h with
  | nil =>
    intro ds b hT _
    exact ⟨by simpa using hT, rfl, fun _ => .nil⟩
  | cons hA hx _ ih =>
    intro ds b hT hl
    match ds, hl with
    | d :: ds, hl =>
      simp only [List.foldr_cons, Expr.forallE.injEq] at hT
      obtain ⟨rfl, rfl⟩ := hT
      obtain ⟨h1, h2, h3⟩ := ih ds b rfl (by simp at hl; omega)
      refine ⟨by simpa using h1, by rw [h2, consN_cons, push_eq_cons], fun b' => ?_⟩
      simpa using Fits.cons hA hx (h3 b')

/-- **A fit against a closed reading transfers with its residual** to any environment. -/
theorem TeleFit.transfer_rest :
    ∀ {ρ σ : Nat → V} {T : Term} {vs : List V} {rest : V} {k : Nat},
      TeleFit V ρ T vs rest → Term.bvarsBelow k T → (∀ i, i < k → ρ i = σ i) →
      TeleFit V σ T vs rest
  | ρ, σ, T, [], rest, k, h, hb, hag => by
    obtain rfl := teleFit_nil_inv h
    rw [interp_congr_below V T k ρ σ hb hag]
    exact .nil
  | ρ, σ, _, _ :: _, _, k, .cons (A := A) (B := B) hm h, hb, hag => by
    have hb' : Term.bvarsBelow k A ∧ Term.bvarsBelow (k + 1) B := hb
    rw [interp_congr_below V A k ρ σ hb'.1 hag] at hm
    exact .cons hm (TeleFit.transfer_rest h hb'.2 fun i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hag i (by omega))

/-- Instantiating one variable runs through a telescope, binder by binder. -/
theorem instantiate1_foldr (v : Expr) : ∀ (ds : List Expr) (b : Expr) (c : Nat),
    ∃ ds' : List Expr, ds'.length = ds.length ∧
      (ds.foldr .forallE b).instantiate1 v c = ds'.foldr .forallE (b.instantiate1 v (c + ds.length))
  | [], _, _ => ⟨[], rfl, rfl⟩
  | x :: ds, b, c => by
    obtain ⟨ds', hl, he⟩ := instantiate1_foldr v ds b (c + 1)
    refine ⟨x.instantiate1 v c :: ds', by simp [hl], ?_⟩
    simp only [List.foldr_cons, Expr.instantiate1, he, List.length_cons,
      show c + 1 + ds.length = c + (ds.length + 1) by omega]

/-- **A reading's telescope, peeled**: the reading of a telescope peels to a `PiTeleAV` whose
body is the reading of the opened body, which closes back to the body. -/
theorem denote_peelStrip {acval : Name → (Name → Nat) → Term} {env : Env} {φ : Name → Nat} :
    ∀ (k : Nat) {d : Nat} {e : Expr} {ta : Term} {ds : List Expr} {b : Expr},
      denote acval env φ d e = some ta → e.stripPis k = some (ds, b) →
      Expr.fvarsBelow d e → e.looseBVarsBounded 0 = true →
      ∃ Γ R b', PiTeleAV k ta Γ R ∧ denote acval env φ (d + k) b' = some R ∧
        closeN (d + k) b' = closeN d b k ∧ Expr.fvarsBelow (d + k) b' ∧
        b'.looseBVarsBounded 0 = true
  | 0, d, e, ta, ds, b, h, hs, hfb, hlb => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    exact ⟨[], ta, e, .nil, h, rfl, hfb, hlb⟩
  | k + 1, d, e, ta, ds, b, h, hs, hfb, hlb => by
    match e, hs with
    | .forallE ty body, hs =>
      obtain ⟨tA, tB, -, hB, rfl⟩ := denote_forallE_inv h
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨ds', b₀⟩, hs', heq⟩ := hs
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d body := hfb
      have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
      rw [Bool.and_eq_true] at hlb'
      obtain ⟨rfl, hl⟩ := stripPis_eq_foldr k hs'
      -- the opened body peels to the opened body's body
      obtain ⟨ds'', hl'', hinst⟩ := instantiate1_foldr (.fvar d ty) ds' b₀ 0
      have hs'' := stripPis_foldr ds'' (b₀.instantiate1 (.fvar d ty) (0 + ds'.length))
      rw [← hinst, hl'', hl] at hs''
      obtain ⟨Γ, R, b', hP, hR, hc, hfb'', hlb''⟩ := denote_peelStrip k hB hs''
        (Expr.fvarsBelow_instantiate1 0 hfb'.2)
        (ConLeche.looseBVarsBounded_instantiate1 _ 0 hlb'.2)
      have hbb : b₀.looseBVarsBounded (k + 1) = true := by
        have := looseBVarsBounded_foldr_body ds' hlb'.2
        rwa [hl, Nat.add_comm] at this
      refine ⟨Γ ++ [tA], R, b', .cons hP, by rwa [show d + (k + 1) = d + 1 + k by omega], ?_,
        by rwa [show d + (k + 1) = d + 1 + k by omega], hlb''⟩
      rw [show d + (k + 1) = d + 1 + k by omega, hc, Nat.zero_add,
        Expr.closeN_instantiate1 b₀ k hbb (fvarsBelow_foldr_body ds' hfb'.2)]

/-- **A fit of an instantiated telescope is a fit of the source**, the instantiated variables
holding the values' denotations. -/
theorem Fits_instantiateLift_inv {vs : List Expr} {Ys : List V} {σ : Nat → V}
    (hlen : Ys.length = vs.length)
    (hvs : ∀ j (h : j < vs.length), ConLeche.Denotes cval env φ σ vs[j] (Ys[j]'(hlen ▸ h))) :
    ∀ (ds : List Expr) (b : Expr) (fs : List V) (d : Nat) {ρ ρ' : Nat → V} {R : Expr},
      (∀ i, ρ (i + d) = σ i) → fs.length = ds.length →
      Fits cval env φ ρ ((ds.foldr .forallE b).instantiateLift vs d) fs ρ' R →
      Fits cval env φ (insAt d Ys ρ) (ds.foldr .forallE b) fs (insAt (d + ds.length) Ys ρ') b ∧
        ρ' = consN fs ρ ∧ R = b.instantiateLift vs (d + ds.length)
  | [], b, fs, d, ρ, ρ', R, _, hl, h => by
    obtain rfl : fs = [] := List.eq_nil_of_length_eq_zero hl
    obtain ⟨rfl, rfl⟩ := h.nil_inv
    exact ⟨.nil, rfl, rfl⟩
  | x :: ds, b, fs, d, ρ, ρ', R, hσ, hl, h => by
    match fs, hl with
    | f :: fs, hl =>
      simp only [List.foldr_cons, Expr.instantiateLift] at h
      cases h with
      | cons hA hx hr =>
        obtain ⟨h1, h2, h3⟩ := Fits_instantiateLift_inv hlen hvs ds b fs (d + 1)
          (fun i => by rw [show i + (d + 1) = (i + d) + 1 by omega]; exact hσ i)
          (by simpa using hl) hr
        refine ⟨.cons (Denotes_instantiateLift_inv hlen hvs x hσ hA) hx ?_, ?_, ?_⟩
        · rw [push_insAt]
          simpa [show d + 1 + ds.length = d + (ds.length + 1) by omega] using h1
        · rw [h2, consN_cons, push_eq_cons]
        · rw [h3]; simp [show d + 1 + ds.length = d + (ds.length + 1) by omega]

/-! ## 5. The equation's syntax -/

/-- **An ι equation, taken apart**: the records it was built from and its pieces. -/
theorem iotaEq_inv {find? : Name → Option ConstantInfo} {cv : ConstantVal} {mI rP : Nat}
    {rl : RecRule} {e : Expr} (h : ConLeche.iotaEq find? cv mI rP rl = some e) :
    ∃ (cvj : ConstantVal) (cnP cnF : Nat) (iT : Name) (pre idx pd fd : List Expr)
      (rest body ctorBody concl : Expr) (u : Level),
      find? rl.ctor = some (.ctorInfo cvj cnP cnF iT) ∧
      cv.type.stripPis rP = some (pre, rest) ∧
      rest.stripPis (mI - rP + 1) = some (idx, body) ∧
      ConLeche.motiveLevel? pre (mI - rP) body = some u ∧
      (cvj.type.instantiateLevelParams cvj.levelParams
        (rl.ctorLevels cvj.levelParams)).stripPis cnP = some (pd, ctorBody) ∧
      (ctorBody.instantiateLift (rl.iotaParams rP cnP).reverse).stripPis rl.nfields
        = some (fd, concl) ∧
      (rl.iotaParams rP cnP).length = cnP ∧ rP ≤ mI ∧
      (concl.getAppArgs.drop cnP).length = mI - rP ∧
      e = (pre ++ fd).foldr .forallE
        (.app (.app (.app (.const ConLeche.eqName [u])
          ((body.liftLooseBVars rl.nfields (mI - rP + 1)).instantiateLift
            (Expr.mkAppN (.const rl.ctor (rl.ctorLevels cvj.levelParams))
              ((rl.iotaParams rP cnP).map (·.liftLooseBVars rl.nfields 0) ++
                (List.range rl.nfields).map fun j => Expr.bvar (rl.nfields - 1 - j))
              :: (concl.getAppArgs.drop cnP).reverse)))
          (Expr.mkAppN (.const cv.name (cv.levelParams.map .param))
            ((List.range rP).map (fun i => Expr.bvar (rP + rl.nfields - 1 - i)) ++
              concl.getAppArgs.drop cnP ++
              [Expr.mkAppN (.const rl.ctor (rl.ctorLevels cvj.levelParams))
                ((rl.iotaParams rP cnP).map (·.liftLooseBVars rl.nfields 0) ++
                  (List.range rl.nfields).map fun j => Expr.bvar (rl.nfields - 1 - j))])))
          (Expr.mkAppN rl.rhs ((List.range rP).map (fun i => Expr.bvar (rP + rl.nfields - 1 - i)) ++
            (List.range rl.nfields).map fun j => Expr.bvar (rl.nfields - 1 - j)))) := by
  unfold ConLeche.iotaEq at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨ci, hc, h⟩ := h
  · cases ci with
    | ctorInfo cvj cnP cnF iT =>
      unfold ConLeche.iotaEqAt at h
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨pre, rest⟩, hpre, h⟩ := h
      obtain ⟨⟨idx, body⟩, hbody, h⟩ := h
      obtain ⟨u, hu, h⟩ := h
      obtain ⟨⟨pd, ctorBody⟩, hcb, h⟩ := h
      obtain ⟨⟨fd, concl⟩, hfd, h⟩ := h
      obtain ⟨_, hg, he⟩ := h
      simp only [guard] at hg
      split at hg
      · rename_i hg'
        exact ⟨cvj, cnP, cnF, iT, pre, idx, pd, fd, rest, body, ctorBody, concl, u, hc, hpre, hbody,
          hu, hcb, hfd, hg'.1, hg'.2.1, hg'.2.2, he.symm⟩
      · exact nomatch hg
    | _ => exact nomatch h

/-! ## 6. Environments -/

omit [SetTheory V] in
theorem consN_append : ∀ (L₁ L₂ : List V) (ρ : Nat → V),
    consN (L₁ ++ L₂) ρ = consN L₂ (consN L₁ ρ)
  | [], _, _ => rfl
  | x :: L₁, L₂, ρ => by simp only [List.cons_append, consN_cons, consN_append L₁ L₂]

omit [SetTheory V] in
theorem consN_lt (L : List V) (ρ : Nat → V) {j : Nat} (hj : j < L.length) :
    consN L ρ j = L[L.length - 1 - j] := by
  have h := consN_getElem? L ρ j hj
  rw [List.getElem?_eq_getElem (by omega)] at h
  exact (Option.some.inj h).symm

omit [SetTheory V] in
theorem consN_ge (L : List V) (ρ : Nat → V) {j : Nat} (hj : L.length ≤ j) :
    consN L ρ j = ρ (j - L.length) := by
  have := consN_shift L ρ (j - L.length)
  rwa [Nat.sub_add_cancel hj] at this

omit [SetTheory V] in
/-- Instantiating at the outermost variables is pushing the values, the last innermost. -/
theorem insAt_zero_reverse (L : List V) (ρ : Nat → V) : insAt 0 L.reverse ρ = consN L ρ := by
  funext i
  simp only [insAt, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, List.length_reverse]
  by_cases h : i < L.length
  · simp only [h, ↓reduceDIte]; rw [consN_lt L ρ h, List.getElem_reverse]
  · simp only [h, ↓reduceDIte]; rw [consN_ge L ρ (by omega)]

/-- **An application along a fit lands in its residual.** -/
theorem TeleFit.app_mem {ρ : Nat → V} {T : Term} {vs : List V} {rest : V}
    (h : TeleFit V ρ T vs rest) {f : V} (hf : f ∈ˢ interp V ρ T) : vs.foldl app f ∈ˢ rest := by
  induction h generalizing f with
  | nil => exact hf
  | cons hm _ ih =>
    rw [interp_pi] at hf
    exact ih (app_mem_piV hf hm)

/-- A telescope's peel past its binders is its body's. -/
theorem stripPis_foldr_add : ∀ (ds : List Expr) (b : Expr) (k : Nat),
    (ds.foldr .forallE b).stripPis (ds.length + k) = (b.stripPis k).map fun p => (ds ++ p.1, p.2)
  | [], b, k => by simp
  | d :: ds, b, k => by
    rw [List.length_cons, show ds.length + 1 + k = (ds.length + k) + 1 by omega]
    simp only [List.foldr_cons, Expr.stripPis, stripPis_foldr_add ds b k, Option.map_map]
    rfl

/-! ## 6b. The reverse opening -/

/-- The free variables the reverse opening puts in. -/
def openFvarList (n : Nat) : List Expr := (List.range n).map fun j => .fvar j (.sort .zero)

/-- The variables the reverse opening's closure puts back, reversed. -/
def revBVarList (n : Nat) : List Expr := (List.range n).map fun j => .bvar (n - 1 - j)

theorem instantiate1_instantiateLift_fvars (n : Nat) : ∀ (e : Expr) (c : Nat),
    (e.instantiateLift (openFvarList n) c).instantiate1 (.fvar n (.sort .zero)) c
      = e.instantiateLift (openFvarList (n + 1)) c
  | .bvar i, c => by
    simp only [Expr.instantiateLift, openFvarList, List.length_map, List.length_range]
    by_cases h1 : i < c
    · simp [h1, show i ≠ c by omega, show ¬ i > c by omega]
    · by_cases h2 : i - c < n
      · simp [h1, h2, show i - c < n + 1 by omega, Expr.liftLooseBVars]
      · by_cases h3 : i - c = n
        · simp [h1, h3, Expr.liftLooseBVars, show i - n = c by omega]
        · simp [h1, h2, show ¬ i - c < n + 1 by omega,
            show i - n ≠ c by omega, show i - n > c by omega, show i - n - 1 = i - (n + 1) by omega]
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, c => by
    simp only [Expr.instantiateLift, Expr.instantiate1, instantiate1_instantiateLift_fvars n f,
      instantiate1_instantiateLift_fvars n a]
  | .lam t b, c => by
    simp only [Expr.instantiateLift, Expr.instantiate1, instantiate1_instantiateLift_fvars n t,
      instantiate1_instantiateLift_fvars n b]
  | .forallE t b, c => by
    simp only [Expr.instantiateLift, Expr.instantiate1, instantiate1_instantiateLift_fvars n t,
      instantiate1_instantiateLift_fvars n b]
  | .letE t v b, c => by
    simp only [Expr.instantiateLift, Expr.instantiate1, instantiate1_instantiateLift_fvars n t,
      instantiate1_instantiateLift_fvars n v, instantiate1_instantiateLift_fvars n b]
  | .proj _ _ e, c => by
    simp only [Expr.instantiateLift, Expr.instantiate1, instantiate1_instantiateLift_fvars n e]

/-- **The reverse opening is an instantiation** by the free variables `0, …, n-1`. -/
theorem openRev_eq_instantiateLift : ∀ (n : Nat) (e : Expr),
    openRev 0 n e = e.instantiateLift (openFvarList n) 0
  | 0, e => by
    simp only [openRev, openFvarList, List.range_zero, List.map_nil]
    exact (Expr.instantiateLift_nil e 0).symm
  | n + 1, e => by
    rw [openRev, openRev_eq_instantiateLift n e, Nat.zero_add,
      instantiate1_instantiateLift_fvars n e 0]

/-- **Closing the reverse opening reverses the variables.** -/
theorem closeN_instantiateLift_fvars (n : Nat) : ∀ (e : Expr) (c : Nat), e.hasFvar = false →
    closeN n (e.instantiateLift (openFvarList n) c) c = e.instantiateLift (revBVarList n) c
  | .bvar i, c, _ => by
    simp only [Expr.instantiateLift, openFvarList, revBVarList, List.length_map, List.length_range]
    by_cases h1 : i < c
    · simp [h1, closeN]
    · by_cases h2 : i - c < n
      · simp [h1, h2, closeN, Expr.liftLooseBVars]; omega
      · simp [h1, h2, closeN]
  | .fvar _ _, _, h => by simp [Expr.hasFvar] at h
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, c, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiateLift, closeN, closeN_instantiateLift_fvars n f c h.1,
      closeN_instantiateLift_fvars n a c h.2]
  | .lam t b, c, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiateLift, closeN, closeN_instantiateLift_fvars n t c h.1,
      closeN_instantiateLift_fvars n b (c + 1) h.2]
  | .forallE t b, c, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiateLift, closeN, closeN_instantiateLift_fvars n t c h.1,
      closeN_instantiateLift_fvars n b (c + 1) h.2]
  | .letE t v b, c, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiateLift, closeN, closeN_instantiateLift_fvars n t c h.1.1,
      closeN_instantiateLift_fvars n v c h.1.2, closeN_instantiateLift_fvars n b (c + 1) h.2]
  | .proj _ _ e, c, h => by
    simp only [Expr.hasFvar] at h
    simp only [Expr.instantiateLift, closeN, closeN_instantiateLift_fvars n e c h]

end Subst

end ConLeche.Model

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.SetModel ConLeche.Verify SetTheory
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule)
open ConLeche.Expr (closeN)

variable {V : Type w} [SetTheory V]

/-- **A reverse-instantiation chain, read**: the chain's arguments sit at the variables, the
first at `0`. -/
theorem interp_instRevChain : ∀ (zs : List Term) (X : Term) (σ : Nat → V),
    interp V σ (Term.instRevChain zs X) = interp V (consN (zs.map (interp V σ)).reverse σ) X
  | [], _, _ => rfl
  | v :: vs, X, σ => by
    show interp V σ (Term.instRevChain vs (X.inst (v.liftN vs.length 0) 0)) = _
    rw [interp_instRevChain vs, interp_inst]
    have h1 : shiftE 0 0 (consN (vs.map (interp V σ)).reverse σ)
        = consN (vs.map (interp V σ)).reverse σ := by funext i; simp [shiftE]
    have h2 : interp V (consN (vs.map (interp V σ)).reverse σ) (v.liftN vs.length 0)
        = interp V σ v := by
      rw [interp_liftN]
      congr 1
      funext i
      simp only [shiftE, Nat.not_lt_zero, ↓reduceIte]
      have := consN_shift (vs.map (interp V σ)).reverse σ i
      simpa using this
    rw [h1, h2, List.map_cons, List.reverse_cons, consN_append]
    congr 1
    funext i
    cases i <;> simp [instE, consN, Semantics.cons]

/-- **A nested rule's pin, read through the reverse opening**: the opened reading at the prefix
values (reversed onto any environment) is what the pin denotes with the prefix values pushed. -/
theorem pin_reading_val {acval : Name → (Name → Nat) → Term}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ)) {env : Env} {φ : Name → Nat} {rP : Nat} {p : Expr}
    (hnf : p.hasFvar = false) (hb : p.looseBVarsBounded rP = true) {xs : List V}
    (hxl : xs.length = rP) {ρ : Nat → V} {X : V}
    (hX : ConLeche.Denotes (cvalOf (V := V) acval) env φ (consN xs ρ) p X) {vpa : Term}
    (hv : denote acval env φ rP (openRev 0 rP p) = some vpa) (σ : Nat → V) :
    interp V (consN xs.reverse σ) vpa = X := by
  have hfb : Expr.fvarsBelow rP (openRev 0 rP p) := by
    have := openRev_fvarsBelow (d := 0) (e := p)
      (fvarsBelow_zero_of_not_hasFvar hnf) rP
    rwa [Nat.zero_add] at this
  have hlb : (openRev 0 rP p).looseBVarsBounded 0 = true :=
    openRev_bounded rP 0 (by simpa using hb)
  have hD := Denotes_of_denote (V := V) hcl rP _ hv hfb hlb (consN xs.reverse σ)
  rw [openRev_eq_instantiateLift, closeN_instantiateLift_fvars rP p 0 hnf] at hD
  have hYl : ((List.range rP).map fun j => consN xs.reverse σ (rP - 1 - j)).length
      = (revBVarList rP).length := by simp [revBVarList]
  have hD' := Denotes_instantiateLift_inv (σ := consN xs.reverse σ) hYl
    (fun j hj => by simp only [revBVarList, List.getElem_map, List.getElem_range]; exact .bvar)
    p (d := 0) (fun i => rfl) hD
  refine ConLeche.Denotes_functional (Denotes_congr_below hD' hb fun i hi => ?_) hX
  simp only [insAt, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, List.length_map,
    List.length_range, hi, ↓reduceDIte, List.getElem_map, List.getElem_range]
  rw [consN_lt _ _ (by simp [hxl]; omega), consN_lt _ _ (by omega), List.getElem_reverse]
  congr 1; simp [hxl]; omega

/-! ## 7. The equations hold -/

theorem fvarsBelow_getAppArgs {d : Nat} : ∀ (e : Expr), Expr.fvarsBelow d e →
    ∀ x ∈ e.getAppArgs, Expr.fvarsBelow d x
  | .app f a, h, x, hx => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact fvarsBelow_getAppArgs f h.1 x hx
    · exact h.2
  | .bvar _, _, _, hx | .fvar _ _, _, _, hx | .sort _, _, _, hx | .const _ _, _, _, hx
  | .lam _ _, _, _, hx | .forallE _ _, _, _, hx | .letE _ _ _, _, _, hx | .lit _, _, _, hx
  | .proj _ _ _, _, _, hx => by simp [Expr.getAppArgs] at hx

theorem piResult_foldr : ∀ (ds : List Expr) (b : Expr),
    (ds.foldr .forallE b).piResult = b.piResult
  | [], _ => rfl
  | _ :: ds, b => by simp only [List.foldr_cons, Expr.piResult, piResult_foldr ds b]

theorem getD_of_lt {α : Type _} (L : List α) {i : Nat} {d : α} (h : i < L.length) :
    L.getD i d = L[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem Denotes_bvar_inv {cval : Name → (Name → Nat) → V} {env : Env} {φ : Name → Nat}
    {ρ : Nat → V} {i : Nat} {X : V} (h : ConLeche.Denotes cval env φ ρ (.bvar i) X) : X = ρ i := by
  cases h; rfl

theorem list_split3 {α : Type _} (L : List α) (a b : Nat) (h : L.length = a + b + 1) :
    L = L.take a ++ (L.drop a).take b ++ [L[a + b]'(by omega)] := by
  apply List.ext_getElem (by simp [List.length_take, List.length_drop]; omega)
  intro i h1 h2
  by_cases hi : i < a
  · rw [List.getElem_append_left (by simp [List.length_take, List.length_drop]; omega),
      List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]
  · by_cases hj : i < a + b
    · rw [List.getElem_append_left (by simp [List.length_take, List.length_drop]; omega),
        List.getElem_append_right (by simp [List.length_take]; omega)]
      simp only [List.getElem_take, List.getElem_drop, List.length_take]
      congr 1; omega
    · rw [List.getElem_append_right (by simp [List.length_take, List.length_drop]; omega)]
      simp only [List.getElem_singleton]
      congr 1; omega

/-- **The two sides of every stored ι equation**, at every fit of its telescope: an equation is a
telescope over `@Eq.{u} ty lhs rhs`, and wherever the three denote, `ty` is a type of the universe
`u` and `lhs` and `rhs` are one member of it.  This is what an equation holds by, whatever `Eq`
denotes (`ruleEqsHold_of` reads it through `Eq`'s law); it needs no `Eq` stored. -/
theorem ruleEq_sides {env : Env} (m : EnvModelM V env)
    (hfit : ∀ (φ : Name → Nat) (n : Name) (cv : ConstantVal) (mI rP : Nat) (isK : Bool)
      (rules : List RecRule), env.find? n = some (.recInfo cv mI rP isK rules) →
      ∀ rl ∈ rules, RecRuleFit m.base2 φ cv mI rP rl)
    {e : Expr} (he : e ∈ ConLeche.ruleEqs env) :
    ∃ (ds : List Expr) (u : Level) (ty lhs rhs : Expr),
      e = ds.foldr .forallE (.app (.app (.app (.const ConLeche.eqName [u]) ty) lhs) rhs) ∧
      ∀ (φ : Name → Nat) (ρ : Nat → V) (vs : List V) (ρ' : Nat → V), vs.length = ds.length →
        Fits (cvalOf m.base2.acval) env φ ρ
          (ds.foldr .forallE (.app (.app (.app (.const ConLeche.eqName [u]) ty) lhs) rhs)) vs ρ'
          (.app (.app (.app (.const ConLeche.eqName [u]) ty) lhs) rhs) →
        ∀ T L R : V,
          ConLeche.Denotes (cvalOf m.base2.acval) env φ ρ' ty T →
          ConLeche.Denotes (cvalOf m.base2.acval) env φ ρ' lhs L →
          ConLeche.Denotes (cvalOf m.base2.acval) env φ ρ' rhs R →
          T ∈ˢ (univ (Level.eval φ u) : V) ∧ L ∈ˢ T ∧ R ∈ˢ T ∧ L = R := by
  -- the recursor and the rule the equation was built from
  simp only [ConLeche.ruleEqs, List.mem_flatMap] at he
  obtain ⟨c, hcmem, he⟩ := he
  split at he
  rotate_left
  · exact absurd he (List.not_mem_nil)
  rename_i cv mI rP isK rules hf
  obtain ⟨rl, hrl, hiota⟩ := List.mem_filterMap.mp he
  obtain ⟨cvj, cnP, cnF, iT, pre, idx, pd, fd, rest, body, ctorBody, concl, u, hc, hpre, hbody,
    hu, hcb, hfd, hplen, hrPmI, hidx, rfl⟩ := iotaEq_inv hiota
  have hcl := m.base2.cval_closed
  have hnm : cv.name = c.name := by
    have := ConLeche.Env.find?_name hf
    simpa [ConLeche.ConstantInfo.name, ConstantInfo.toConstantVal] using this
  have hfR : env.find? cv.name = some (.recInfo cv mI rP isK rules) := by rw [hnm]; exact hf
  -- the syntax of the records
  obtain ⟨hpreEq, hprel⟩ := stripPis_eq_foldr rP hpre
  obtain ⟨hrestEq, hidxl⟩ := stripPis_eq_foldr _ hbody
  obtain ⟨hcbEq, hpdl⟩ := stripPis_eq_foldr cnP hcb
  obtain ⟨hfdEq, hfdl⟩ := stripPis_eq_foldr _ hfd
  -- names for the pieces
  clear he
  generalize hnF : rl.nfields = nF at *
  generalize hps : rl.iotaParams rP cnP = ps at *
  generalize hind : List.drop cnP concl.getAppArgs = ind at *
  generalize hfsB : (List.range nF).map (fun j => Expr.bvar (nF - 1 - j)) = fsB at *
  generalize hxsB : (List.range rP).map (fun i => Expr.bvar (rP + nF - 1 - i)) = xsB at *
  generalize hmaj : Expr.mkAppN (.const rl.ctor (rl.ctorLevels cvj.levelParams))
    (ps.map (·.liftLooseBVars nF 0) ++ fsB) = major at *
  -- the telescope
  refine ⟨pre ++ fd, u, _, _, _, rfl, fun φ ρ vs ρ' hvl hvf T L R hT hL hR => ?_⟩
  rw [List.length_append, hprel, hfdl] at hvl
  rw [← List.take_append_drop rP vs] at hvf
  obtain ⟨ρ₁, R₁, h1, h2⟩ := hvf.split
  obtain ⟨hR₁, hρ₁, hxfit⟩ := h1.foldr_prefix (pre ++ fd) _ rfl
    (by rw [List.length_take, List.length_append, hprel]; omega)
  have hxl : (vs.take rP).length = rP := by rw [List.length_take]; omega
  rw [hxl, List.drop_left' hprel] at hR₁
  rw [hxl, List.take_left' hprel] at hxfit
  subst hR₁ hρ₁
  obtain ⟨-, hρ', hffit⟩ := h2.foldr_prefix fd _ rfl (by rw [List.length_drop, hfdl]; omega)
  have hfl : (vs.drop rP).length = nF := by rw [List.length_drop]; omega
  rw [hfl, ← hfdl, List.take_length] at hffit
  generalize vs.take rP = xs at hxl hxfit hρ' hffit
  generalize vs.drop rP = fs at hfl hρ' hffit
  subst hρ'
  -- the left-hand side's values: the prefix, the indices, the major
  obtain ⟨F, Xs, hF, hXl, hXs, rfl⟩ := Denotes_mkAppN_inv _ hL
  cases hF with
  | const hfF hlenF =>
  rw [hfR] at hfF
  cases hfF
  simp only [ConstantInfo.toConstantVal, Level.substFn_param_self] at hlenF ⊢
  have hxBl : xsB.length = rP := by rw [← hxsB]; simp
  have hXl' : Xs.length = rP + (mI - rP) + 1 := by
    rw [hXl, List.length_append, List.length_append, hxBl, hidx]; rfl
  have hXsplit := list_split3 Xs rP (mI - rP) hXl'
  generalize hIs : (Xs.drop rP).take (mI - rP) = Is at hXsplit
  generalize hMaj : Xs[rP + (mI - rP)]'(by omega) = Maj at hXsplit
  have hIl : Is.length = mI - rP := by rw [← hIs]; simp [List.length_take, List.length_drop]; omega
  -- the prefix's values are the fit's
  have hxs : Xs.take rP = xs := by
    apply List.ext_getElem (by rw [List.length_take]; omega)
    intro i h1 h2
    have hD := hXs i (by rw [List.length_append, List.length_append, hxBl]; rw [List.length_take] at h1; omega)
      (by rw [List.length_take] at h1; omega)
    rw [List.getElem_append_left (by rw [List.length_append, hxBl]; rw [List.length_take] at h1; omega),
      List.getElem_append_left (by rw [hxBl]; rw [List.length_take] at h1; omega)] at hD
    simp only [← hxsB, List.getElem_map, List.getElem_range] at hD
    rw [List.getElem_take, Denotes_bvar_inv hD, consN_ge _ _ (by rw [hfl]; omega), hfl, consN_lt _ _ (by omega)]
    congr 1; omega
  rw [hxs] at hXsplit
  subst hXsplit
  have hxl' : xsB.length + ind.length = rP + (mI - rP) := by rw [hxBl, hidx]
  have hIsD : ∀ i (h : i < ind.length) (h' : i < Is.length),
      ConLeche.Denotes (cvalOf m.base2.acval) env φ (consN fs (consN xs ρ)) ind[i] Is[i] := by
    intro i h h'
    have hD := hXs (rP + i) (by simp [hxBl]; omega) (by simp [hxl, hIl]; omega)
    rw [List.getElem_append_left (by simp [hxBl]; omega),
      List.getElem_append_right (by simp [hxBl]),
      List.getElem_append_left (by simp [hxl]; omega),
      List.getElem_append_right (by simp [hxl])] at hD
    simpa [hxBl, hxl] using hD
  have hMajD : ConLeche.Denotes (cvalOf m.base2.acval) env φ (consN fs (consN xs ρ)) major Maj := by
    have hD := hXs (rP + (mI - rP)) (by simp [hxBl, hidx]) (by simp [hxl, hIl])
    rw [List.getElem_append_right (by simp [hxBl, hidx]),
      List.getElem_append_right (by simp [hxl, hIl])] at hD
    simpa [hxBl, hidx, hxl, hIl] using hD
  clear hXs
  have hMajD0 := hMajD
  -- the major's values: the constructor at its levels, the parameters, the fields
  rw [← hmaj] at hMajD
  obtain ⟨Cv, Ms, hCv, hMl, hMs, rfl⟩ := Denotes_mkAppN_inv _ hMajD
  have hfBl : fsB.length = nF := by rw [← hfsB]; simp
  have hskip : skipAt 0 nF (consN fs (consN xs ρ)) = consN xs ρ := by
    funext i; simp only [skipAt, Nat.not_lt_zero, ↓reduceIte]
    rw [consN_ge _ _ (by omega), hfl, Nat.add_sub_cancel]
  generalize hPs : Ms.take cnP = Ps
  have hPl : Ps.length = cnP := by
    rw [← hPs, List.length_take, hMl, List.length_append, List.length_map, hplen]; omega
  have hPsD : ∀ i (h : i < ps.length) (h' : i < Ps.length),
      ConLeche.Denotes (cvalOf m.base2.acval) env φ (consN xs ρ) ps[i] Ps[i] := by
    intro i h h'
    have hD := hMs i (by simp; omega) (by rw [hMl]; simp; omega)
    rw [List.getElem_append_left (by simp; omega)] at hD
    simp only [List.getElem_map] at hD
    have := Denotes_liftLooseBVars_inv _ hD
    rw [hskip] at this
    simpa [← hPs, List.getElem_take] using this
  have hMfs : Ms.drop cnP = fs := by
    apply List.ext_getElem (by rw [List.length_drop, hMl]; simp [hplen, hfBl, hfl])
    intro j h1 h2
    have hD := hMs (cnP + j) (by simp [hplen, hfBl]; rw [List.length_drop, hMl] at h1; simp [hplen, hfBl] at h1; omega)
      (by rw [List.length_drop] at h1; omega)
    rw [List.getElem_append_right (by simp [hplen])] at hD
    simp only [List.length_map, hplen, Nat.add_sub_cancel_left, ← hfsB, List.getElem_map,
      List.getElem_range] at hD
    rw [List.getElem_drop, Denotes_bvar_inv hD, consN_lt _ _ (by omega)]
    congr 1; omega
  have hMsplit : Ms = Ps ++ fs := by rw [← hPs, ← hMfs, List.take_append_drop]
  subst hMsplit
  clear hMs hMfs
  -- the right-hand side's values: the rule's right-hand side, the prefix, the fields
  obtain ⟨Rv, Rs, hRv, hRl, hRs, rfl⟩ := Denotes_mkAppN_inv _ hR
  have hRs' : Rs = xs ++ fs := by
    apply List.ext_getElem (by rw [hRl]; simp [hxBl, hfBl, hxl, hfl])
    intro j h1 h2
    have hD := hRs j (by rw [← hRl]; exact h1) h1
    have hj2 : j < rP + nF := by simpa [hxl, hfl] using h2
    by_cases hj : j < rP
    · rw [List.getElem_append_left (by simp [hxBl]; omega)] at hD
      simp only [← hxsB, List.getElem_map, List.getElem_range] at hD
      rw [Denotes_bvar_inv hD, List.getElem_append_left (by omega),
        consN_ge _ _ (by rw [hfl]; omega), hfl, consN_lt _ _ (by omega)]
      congr 1; omega
    · rw [List.getElem_append_right (by simp [hxBl]; omega)] at hD
      simp only [hxBl, ← hfsB, List.getElem_map, List.getElem_range] at hD
      rw [Denotes_bvar_inv hD, List.getElem_append_right (by omega),
        consN_lt _ _ (by rw [hfl]; omega)]
      congr 1; rw [hfl, hxl]; omega
  subst hRs'
  clear hRs hRl
  -- the constructor's value
  cases hCv with
  | const hfC hlenC =>
  rw [hc] at hfC
  cases hfC
  simp only [ConstantInfo.toConstantVal] at hlenC hMajD0 ⊢
  generalize hψc : Level.substFn φ cvj.levelParams (rl.ctorLevels cvj.levelParams) = ψc at *
  -- the records' readings
  have hmemR := ConLeche.Env.find?_mem hfR
  have hmemC := ConLeche.Env.find?_mem hc
  have hwfR := m.base2.wf.consts _ hmemR
  have hwfC := m.base2.wf.consts _ hmemC
  have hnfR : cv.type.hasFvar = false := hwfR.1
  have hlbR : cv.type.looseBVarsBounded 0 = true := hwfR.2.2.2.1
  have hwfC1 : cvj.type.hasFvar = false := hwfC.1
  have hwfC4 : cvj.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hnfC : (cvj.type.instantiateLevelParams cvj.levelParams
      (rl.ctorLevels cvj.levelParams)).hasFvar = false := by
    simpa [Expr.hasFvar_instantiateLevelParams] using hwfC1
  have hlbC : (cvj.type.instantiateLevelParams cvj.levelParams
      (rl.ctorLevels cvj.levelParams)).looseBVarsBounded 0 = true := by
    simpa [Expr.looseBVarsBounded_instantiateLevelParams] using hwfC4
  obtain ⟨TVa, hTVa⟩ := m.type_reads _ hmemR φ
  obtain ⟨TVja, hTVja⟩ := m.type_reads _ hmemC ψc
  simp only [ConstantInfo.toConstantVal] at hTVa hTVja
  have hTVa' : denote m.base2.acval env φ 0
      (cv.type.instantiateLevelParams cv.levelParams (cv.levelParams.map Level.param))
        = some TVa := by
    rw [Expr.instantiateLevelParams_self]; exact hTVa
  have hTVja' : denote m.base2.acval env φ 0
      (cvj.type.instantiateLevelParams cvj.levelParams (rl.ctorLevels cvj.levelParams))
        = some TVja := by
    rw [denotePInstLevels m.base2 φ, hψc]; exact hTVja
  have hclA := denote_closed hcl hnfR hlbR hTVa
  have hclC := denote_closed hcl hnfC hlbC hTVja'
  -- the environment holding the values, and the variables naming them
  let W : List V := xs ++ Ps ++ fs ++ Is
  let σ : Nat → V := fun i => W.getD i pt
  have hσ : ∀ (o : Nat) (L : List V), (∀ i (h : i < L.length), W[o + i]? = some L[i]) →
      ∀ i (h : i < L.length), σ (o + i) = L[i] := by
    intro o L hL i h
    simp only [σ, List.getD_eq_getElem?_getD, hL i h, Option.getD_some]
  let xsT : List Term := (List.range xs.length).map fun i => .bvar (0 + i)
  let psT : List Term := (List.range Ps.length).map fun i => .bvar (rP + i)
  let fsT : List Term := (List.range fs.length).map fun i => .bvar (rP + cnP + i)
  let isT : List Term := (List.range Is.length).map fun i => .bvar (rP + cnP + nF + i)
  have hxsI : xsT.map (interp V σ) = xs := map_interp_bvars σ 0 xs (hσ 0 xs fun i h => by
    simp only [W, Nat.zero_add, List.append_assoc]
    rw [List.getElem?_append_left h, List.getElem?_eq_getElem h])
  have hpsI : psT.map (interp V σ) = Ps := map_interp_bvars σ rP Ps (hσ rP Ps fun i h => by
    simp only [W, List.append_assoc]
    rw [List.getElem?_append_right (by omega), hxl, Nat.add_sub_cancel_left,
      List.getElem?_append_left h, List.getElem?_eq_getElem h])
  have hfsI : fsT.map (interp V σ) = fs := map_interp_bvars σ (rP + cnP) fs
    (hσ (rP + cnP) fs fun i h => by
      simp only [W, List.append_assoc]
      rw [List.getElem?_append_right (by omega), hxl,
        List.getElem?_append_right (by omega), hPl,
        show rP + cnP + i - rP - cnP = i by omega, List.getElem?_append_left h,
        List.getElem?_eq_getElem h])
  have hisI : isT.map (interp V σ) = Is := map_interp_bvars σ (rP + cnP + nF) Is
    (hσ (rP + cnP + nF) Is fun i h => by
      simp only [W, List.append_assoc]
      rw [List.getElem?_append_right (by omega), hxl,
        List.getElem?_append_right (by omega), hPl,
        List.getElem?_append_right (by omega), hfl,
        show rP + cnP + nF + i - rP - cnP - nF = i by omega, List.getElem?_eq_getElem h])
  have hbvWD : ∀ (L : List Term) (o k : Nat), L = (List.range k).map (fun i => Term.bvar (o + i)) →
      ∀ t ∈ L, WellDenoted V σ t := by
    intro L o k hL t ht
    rw [hL] at ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    simp
  let majT : Term := Term.mkAppN (m.base2.acval rl.ctor ψc) (psT ++ fsT)
  have hmajI : interp V σ majT = (Ps ++ fs).foldl app (cvalOf m.base2.acval rl.ctor ψc) := by
    show interp V σ (Term.mkAppN _ _) = _
    rw [interp_mkAppN, interp_cvalOf hcl, ← List.foldl_map, List.map_append, hpsI, hfsI]
  -- the prefix fits the recursor's reading
  have hxF : Fits (cvalOf m.base2.acval) env φ ρ (closeN 0 cv.type) xs (consN xs ρ) rest := by
    rw [Expr.closeN_of_hasFvar _ 0 0 hnfR, hpreEq]; exact hxfit rest
  obtain ⟨_, hxT⟩ := teleFit_of_Fits hcl xs 0 cv.type hTVa
    (fvarsBelow_zero_of_not_hasFvar hnfR) hlbR hxF
  have hxT' := hxT.transfer_rest (σ := σ) hclA fun _ h => absurd h (Nat.not_lt_zero _)
  rw [← hxsI] at hxT'
  obtain ⟨mid, hmid⟩ := Rules.teleFitPA_of_teleFit xsT
    (by simpa using Rules.piChain_of_teleFit hxT') hxT'
  -- the variables, read
  have hgetD : ∀ (L : List V) (o : Nat), (∀ i (h : i < L.length), W[o + i]? = some L[i]) →
      ∀ i (h : i < L.length),
        interp V σ (((List.range L.length).map fun i => Term.bvar (o + i)).getD i default)
          = L[i] := by
    intro L o hL i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
      Option.getD_some, interp_bvar]
    exact hσ o L hL i h
  have hxW : ∀ i (h : i < xs.length), W[0 + i]? = some xs[i] := fun i h => by
    simp only [W, Nat.zero_add, List.append_assoc]
    rw [List.getElem?_append_left h, List.getElem?_eq_getElem h]
  have hpW : ∀ i (h : i < Ps.length), W[rP + i]? = some Ps[i] := fun i h => by
    simp only [W, List.append_assoc]
    rw [List.getElem?_append_right (by omega), hxl, Nat.add_sub_cancel_left,
      List.getElem?_append_left h, List.getElem?_eq_getElem h]
  -- the parameters read as the rule's
  have hRPR : RuleParamsRead m.base2 φ cv rP cnP (cv.levelParams.map Level.param) rl σ xsT psT := by
    refine ⟨by simp [psT, hPl], fun i hi => ?_⟩
    have hpi : interp V σ (psT.getD i default) = Ps[i]'(by omega) :=
      hgetD Ps rP hpW i (by omega)
    have hPsi := hPsD i (by omega) (by omega)
    split
    · rename_i lvls pins hfire
      intro vpa hvpa
      rw [Expr.instantiateLevelParams_self] at hvpa
      have hpins : ps = pins := by rw [← hps]; simp [RecRule.iotaParams, hfire]
      subst hpins
      obtain ⟨-, -, -, -, hnest⟩ := hwfR.2.2.2.2.2 cv mI rP isK rules rfl rl hrl
      obtain ⟨-, -, hpw, -⟩ := hnest lvls ps hfire
      have hmem : ps.getD i default ∈ ps := by
        rw [getD_of_lt _ (by omega)]; exact List.getElem_mem _
      obtain ⟨hpf, -, -, hpb⟩ := hpw _ hmem
      rw [getD_of_lt _ (by omega)] at hvpa hpf hpb
      rw [hpi, interp_instRevChain, hxsI]
      exact (pin_reading_val hcl hpf hpb hxl hPsi hvpa σ).symm
    all_goals
      rename_i hfire
      have hpsE : ps = (List.range (min cnP rP)).map fun i => Expr.bvar (rP - 1 - i) := by
        rw [← hps]; unfold RecRule.iotaParams; split
        · rename_i h; rw [h] at hfire; exact absurd hfire (by simp)
        all_goals rfl
      have hcr : cnP ≤ rP := by
        have := hplen; rw [hpsE, List.length_map, List.length_range] at this; omega
      subst hpsE
      simp only [List.getElem_map, List.getElem_range] at hPsi
      rw [hpi, Denotes_bvar_inv hPsi, consN_lt _ _ (by omega),
        hgetD xs 0 hxW i (by omega)]
      congr 1; omega
  -- the field: its first half, the parameters' fit where the fields fit; its second, the whole fit
  have hF := (hfit φ cv.name cv mI rP isK rules hfR rl hrl).2 (cv.levelParams.map Level.param)
    (by simp) TVa hTVa' cvj cnP cnF iT hc (rl.ctorLevels cvj.levelParams) hlenC
    (substFn_ctorLevels φ rl cnP cv.levelParams cvj.levelParams rP) TVja hTVja' σ xsT psT mid
    (by simp [xsT, hxl]) (hbvWD xsT 0 _ rfl) hmid (hbvWD psT rP _ rfl) hRPR
  obtain ⟨hF1, hF2⟩ := hF
  -- the constructor's telescope: its parameters, then its fields
  obtain ⟨-, hmain, hextra, -⟩ := m.rec_rules φ cv.name cv mI rP isK rules hfR rl hrl
  have harity := ((hextra (cv.levelParams.map Level.param) (by simp) TVa hTVa').2 cvj cnP cnF iT
    hc).1
  rw [hnF] at harity
  have harity' := Expr.stripPis_instantiateLevelParams_isSome cvj.levelParams
    (rl.ctorLevels cvj.levelParams) _ harity
  rw [hcbEq, ← hpdl, stripPis_foldr_add, Option.isSome_map] at harity'
  obtain ⟨⟨fdS, conclS⟩, hS⟩ := Option.isSome_iff_exists.mp harity'
  obtain ⟨hcbS, hfdSl⟩ := stripPis_eq_foldr nF hS
  subst hcbS
  obtain ⟨fd', hfd'l, hiL, -⟩ := instantiateLift_foldr ps.reverse fdS conclS 0
  have hfdE : fd = fd' ∧ concl = conclS.instantiateLift ps.reverse nF := by
    have h1 := stripPis_foldr fd' (conclS.instantiateLift ps.reverse (0 + fdS.length))
    rw [← hiL, hfd'l, hfdSl, hfd] at h1
    simp only [Option.some.injEq, Prod.mk.injEq, Nat.zero_add] at h1
    exact ⟨h1.1, h1.2⟩
  obtain ⟨rfl, rfl⟩ := hfdE
  have hTypeEq : cvj.type.instantiateLevelParams cvj.levelParams (rl.ctorLevels cvj.levelParams)
      = (pd ++ fdS).foldr .forallE conclS := by rw [hcbEq, List.foldr_append]
  -- the fields' fit, at the source of the instantiated fields
  have hfF := hffit (conclS.instantiateLift ps.reverse (0 + fdS.length))
  rw [← hiL] at hfF
  have hlenR : Ps.reverse.length = ps.reverse.length := by simp [hPl, hplen]
  obtain ⟨hfF', -, -⟩ := Fits_instantiateLift_inv (σ := consN xs ρ) hlenR (fun j h => by
      simp only [List.length_reverse] at h
      simp only [List.getElem_reverse]
      have := hPsD (ps.length - 1 - j) (by omega) (by rw [hPl, ← hplen]; omega)
      simpa [hPl, hplen] using this) fdS conclS fs 0
    (fun i => rfl) (by rw [hfl, hfdSl]) hfF
  rw [insAt_zero_reverse, Nat.zero_add] at hfF'
  -- the fields fit past the parameters' values, so the parameters fit (the field's first half)
  have hsCB : (cvj.type.instantiateLevelParams cvj.levelParams
      (rl.ctorLevels cvj.levelParams)).stripPis cnP = some (pd, fdS.foldr .forallE conclS) := by
    rw [hTypeEq, ← hpdl, List.foldr_append, stripPis_foldr]
  obtain ⟨Γ, RB, b', hPT, hRB, hcb', hfb', hlb'⟩ := denote_peelStrip cnP hTVja' hsCB
    (fvarsBelow_zero_of_not_hasFvar hnfC) hlbC
  have hnfB : (fdS.foldr Expr.forallE conclS).hasFvar = false := by
    rw [hTypeEq, List.foldr_append] at hnfC
    exact hasFvar_foldr_body _ hnfC
  rw [Expr.closeN_of_hasFvar _ 0 cnP hnfB, Nat.zero_add] at hcb'
  rw [Nat.zero_add] at hRB hfb'
  have hfF'' := hfF'
  rw [← hcb'] at hfF''
  obtain ⟨restF, hRF⟩ := teleFit_of_Fits hcl fs cnP b' hRB hfb' hlb' hfF''
  have hRFσ : TeleFit V (consN Ps σ) RB fs restF := by
    refine hRF.transfer_rest (k := cnP)
      (by simpa using PiTeleAV.bvarsBelow_rest hPT (k := 0) hclC) fun i hi => ?_
    rw [consN_lt _ _ (by omega), consN_lt _ _ (by omega)]
  obtain ⟨r, hr⟩ := hF1 fs restF (by rw [hnF]; exact hfl) (by
    rw [hpsI]; exact teleSkipFit_of_piTele hPT hPl hRFσ)
  -- the parameters' fit, at the stored type
  have hpc : Rules.PiChain psT.length TVja := by
    simpa [psT, hPl] using Rules.piChain_of_stripPis cnP (by rw [hcb]; rfl) hTVja'
  have hrT := Rules.teleFit_of_teleFitPA hpc hr
  rw [hpsI] at hrT
  have hrT' := hrT.transfer_rest (σ := consN xs ρ) hclC fun _ h => absurd h (Nat.not_lt_zero _)
  obtain ⟨ρP, RP, hPF, -⟩ := Fits_of_teleFit hcl Ps 0 _ hTVja'
    (fvarsBelow_zero_of_not_hasFvar hnfC) hlbC (by rw [hPl, hcb]; rfl) hrT'
  rw [Expr.closeN_of_hasFvar _ 0 0 hnfC, hTypeEq, List.foldr_append] at hPF
  obtain ⟨hRP, hρP, -⟩ := hPF.foldr_prefix pd _ rfl (by omega)
  rw [hPl, ← hpdl, List.drop_length] at hRP
  simp only [List.foldr_nil] at hRP
  subst hRP hρP
  have hCF := hPF.append hfF'
  rw [← List.foldr_append, ← hTypeEq, ← Expr.closeN_of_hasFvar _ 0 0 hnfC] at hCF
  obtain ⟨_, hCT⟩ := teleFit_of_Fits hcl (Ps ++ fs) 0 _ hTVja'
    (fvarsBelow_zero_of_not_hasFvar hnfC) hlbC hCF
  have hCT' := hCT.transfer_rest (σ := σ) hclC fun _ h => absurd h (Nat.not_lt_zero _)
  rw [← hpsI, ← hfsI, ← List.map_append] at hCT'
  have hsAll : (cvj.type.instantiateLevelParams cvj.levelParams
      (rl.ctorLevels cvj.levelParams)).stripPis (cnP + nF) = some (pd ++ fdS, conclS) := by
    rw [hTypeEq, ← hpdl, ← hfdSl, ← List.length_append, stripPis_foldr]
  have hpcC : Rules.PiChain (psT ++ fsT).length TVja := by
    have := Rules.piChain_of_stripPis (cnP + nF) (by rw [hsAll]; rfl) hTVja'
    simpa [psT, fsT, hPl, hfl] using this
  obtain ⟨restC, hrestC⟩ := Rules.teleFitPA_of_teleFit _ hpcC hCT'
  -- the residual's index arguments are the equation's indices
  have hxisW : ∀ i (h : i < Is.length), W[rP + cnP + nF + i]? = some Is[i] := fun i h => by
    simp only [W, List.append_assoc]
    rw [List.getElem?_append_right (by omega), hxl,
      List.getElem?_append_right (by omega), hPl,
      List.getElem?_append_right (by omega), hfl,
      show rP + cnP + nF + i - rP - cnP - nF = i by omega, List.getElem?_eq_getElem h]
  have hpin : IotaIndexPin (V := V) σ restC cnP mI rP (xsT ++ isT) := by
    by_cases h0 : mI - rP = 0
    · exact ⟨restC, [], rfl, Or.inl (by omega), fun i hi => absurd hi (by omega)⟩
    have hnfS : conclS.hasFvar = false := by
      rw [hTypeEq] at hnfC; exact hasFvar_foldr_body _ hnfC
    have hlbS : conclS.looseBVarsBounded (cnP + nF) = true := by
      rw [hTypeEq] at hlbC
      have := looseBVarsBounded_foldr_body _ hlbC
      simpa [hpdl, hfdSl] using this
    -- the conclusion's head is a constant
    have hhead : ∃ n us, conclS.getAppFn = .const n us := by
      obtain ⟨us, hus⟩ := m.base2.wf.ctors _ hmemC cvj cnP cnF iT rfl
      have h1 : ((cvj.type.instantiateLevelParams cvj.levelParams
          (rl.ctorLevels cvj.levelParams)).piResult).getAppFn
          = (cvj.type.piResult.getAppFn).instantiateLevelParams cvj.levelParams
              (rl.ctorLevels cvj.levelParams) := by
        rw [Expr.piResult_instantiateLevelParams, Expr.getAppFn_instantiateLevelParams]
      rw [hus, hTypeEq, piResult_foldr] at h1
      simp only [Expr.instantiateLevelParams] at h1
      have hpr : conclS.piResult = conclS := by
        cases hcs : conclS with
        | forallE t b =>
          exfalso
          rw [hcs] at hind
          simp [Expr.instantiateLift, Expr.getAppArgs] at hind
          subst hind; simp at hidx; omega
        | _ => rfl
      rw [hpr] at h1
      exact ⟨iT, _, h1⟩
    -- the reading of the conclusion
    obtain ⟨Γ, Rc, b', hPT, hRc, hcl', hfb', hlb'⟩ := denote_peelStrip (cnP + nF) hTVja' hsAll
      (fvarsBelow_zero_of_not_hasFvar hnfC) hlbC
    rw [Nat.zero_add] at hfb'
    rw [Expr.closeN_of_hasFvar _ 0 _ hnfS, Nat.zero_add] at hcl'
    rw [Nat.zero_add, ← Expr.mkAppN_getApp b'] at hRc
    obtain ⟨fa, vsR, -, hsp, rfl⟩ := denote_mkAppN_inv hRc
    have hargs : b'.getAppArgs.map (closeN (cnP + nF) · 0) = conclS.getAppArgs := by
      rw [← getAppArgs_closeN, hcl']
    have hrest := teleFitPA_rest_eq (cnP + nF) hPT (by simp [psT, fsT, hPl, hfl]) hrestC
    rw [instSeqAV_mkAppN] at hrest
    have hindE : ind = (conclS.getAppArgs.map (·.instantiateLift ps.reverse nF)).drop cnP := by
      rw [← hind, getAppArgs_instantiateLift _ _ _ hhead]
    have hvl : vsR.length = conclS.getAppArgs.length := by
      rw [← hsp.length, ← hargs, List.length_map]
    have hcl0 : conclS.getAppArgs.length = cnP + (mI - rP) := by
      have := hidx; rw [hindE, List.length_drop, List.length_map] at this; omega
    refine ⟨_, _, hrest, Or.inr (by rw [List.length_map, hvl, hcl0]), fun i hi => ?_⟩
    -- the index argument's reading
    have hj : cnP + i < b'.getAppArgs.length := by
      rw [← List.length_map (f := (closeN (cnP + nF) · 0)), hargs]; omega
    have hjv : cnP + i < vsR.length := by omega
    have hws : (psT ++ fsT).map (interp V σ) = Ps ++ fs := by rw [List.map_append, hpsI, hfsI]
    have hlen1 : cnP + nF - 1 = (psT ++ fsT).length - 1 := by simp [psT, fsT, hPl, hfl]
    rw [getD_of_lt _ (by simp; omega), List.getElem_map, hlen1, interp_instSeq, chain, hws]
    have hsp' := hsp.getD default (cnP + i) hj
    rw [getD_of_lt _ hj, getD_of_lt _ hjv] at hsp'
    have hD1 := Denotes_of_denote (V := V) hcl (cnP + nF) _ hsp'
      (fvarsBelow_getAppArgs _ hfb' _ (List.getElem_mem hj))
      (looseBVarsBounded_getAppArgs hlb' _ (List.getElem_mem hj))
      (consN (Ps ++ fs) σ)
    have hcA : closeN (cnP + nF) (b'.getAppArgs[cnP + i])
        = conclS.getAppArgs[cnP + i]'(by omega) := by
      have := congrArg (fun l => l[cnP + i]?) hargs
      simp only [List.getElem?_map, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem (show cnP + i < conclS.getAppArgs.length by omega),
        Option.map_some, Option.some.injEq] at this
      exact this
    rw [hcA] at hD1
    -- the equation's index, at the source of its instantiation
    have hIi := hIsD i (by rw [hindE]; simp; omega) (by omega)
    have hIi' : ind[i]'(by rw [hindE]; simp; omega)
        = (conclS.getAppArgs[cnP + i]'(by omega)).instantiateLift ps.reverse nF := by
      simp [hindE]
    rw [hIi'] at hIi
    have hlenR : Ps.reverse.length = ps.reverse.length := by simp [hPl, hplen]
    have hIi2 := Denotes_instantiateLift_inv (σ := consN xs ρ) hlenR (fun j h => by
      simp only [List.length_reverse] at h
      simp only [List.getElem_reverse]
      have := hPsD (ps.length - 1 - j) (by omega) (by rw [hPl, ← hplen]; omega)
      simpa [hPl, hplen] using this) _ (d := nF)
      (fun j => by rw [consN_ge _ _ (by rw [hfl]; omega), hfl, Nat.add_sub_cancel]) hIi
    have hbA : (conclS.getAppArgs[cnP + i]'(by omega)).looseBVarsBounded (cnP + nF) = true :=
      looseBVarsBounded_getAppArgs hlbS _ (List.getElem_mem _)
    have hag : ∀ j, j < cnP + nF → insAt nF Ps.reverse (consN fs (consN xs ρ)) j
        = consN (Ps ++ fs) σ j := by
      intro j hj
      rw [consN_lt _ _ (by simp [hPl, hfl]; omega)]
      simp only [insAt]
      by_cases hjn : j < nF
      · simp only [hjn, ↓reduceIte]
        rw [consN_lt _ _ (by omega), List.getElem_append_right (by simp [hPl]; omega)]
        congr 1; simp [hPl, hfl]; omega
      · have hjP : j - nF < Ps.reverse.length := by simp [hPl]; omega
        simp only [hjn, ↓reduceIte, hjP, ↓reduceDIte]
        rw [List.getElem_reverse, List.getElem_append_left (by simp [hPl]; omega)]
        congr 1; simp [hPl, hfl]; omega
    have hIi3 := Denotes_congr_below hIi2 hbA hag
    have hgi : (xsT ++ isT).getD (rP + i) default = isT.getD i default := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, xsT, hxl]
    rw [ConLeche.Denotes_functional hD1 hIi3, hgi]
    exact (hgetD Is (rP + cnP + nF) hxisW i (by omega)).symm
  -- the field's second half: the whole telescope fits, the residual in the motive's sort
  obtain ⟨restR, hrestR, huniv⟩ := hF2 fsT isT restC (by simp [fsT, hfl, hnF])
    (by simp [isT, hIl]) (hbvWD fsT _ _ rfl) (hbvWD isT _ _ rfl) hrestC hpin
  rw [hψc] at hrestR
  have hTu := huniv pre idx rest body u (by rw [Expr.instantiateLevelParams_self]; exact hpre)
    hbody hu
  -- the residual is what the equation's type denotes
  have hvals : (xsT ++ isT ++ [majT]).map (interp V σ) = xs ++ Is ++ [(Ps ++ fs).foldl app
      (cvalOf m.base2.acval rl.ctor ψc)] := by
    rw [List.map_append, List.map_append, hxsI, hisI, List.map_singleton, hmajI]
  have hTyEq : cv.type = (pre ++ idx).foldr .forallE body := by
    rw [hpreEq, hrestEq, List.foldr_append]
  have hsR : (cv.type.stripPis (rP + (mI - rP + 1))).isSome = true := by
    have := stripPis_foldr (pre ++ idx) body
    rw [List.length_append, hprel, hidxl, ← hTyEq] at this
    rw [this]; rfl
  have hpcR : Rules.PiChain (xsT ++ isT ++ [majT]).length TVa := by
    have := Rules.piChain_of_stripPis _ hsR hTVa
    simpa [xsT, isT, hxl, hIl, show rP + (mI - rP + 1) = rP + (mI - rP) + 1 by omega] using this
  have hRT := Rules.teleFit_of_teleFitPA hpcR hrestR
  rw [hvals] at hRT
  have hRT' := hRT.transfer_rest (σ := ρ) hclA fun _ h => absurd h (Nat.not_lt_zero _)
  obtain ⟨ρ'', R'', hRF, hRD⟩ := Fits_of_teleFit hcl _ 0 _ hTVa
    (fvarsBelow_zero_of_not_hasFvar hnfR) hlbR
    (by simpa [hxl, hIl, show rP + (mI - rP) + 1 = rP + (mI - rP + 1) by omega] using hsR) hRT'
  rw [Expr.closeN_of_hasFvar _ 0 0 hnfR, hTyEq] at hRF
  obtain ⟨hR'', hρ'', -⟩ := hRF.foldr_prefix (pre ++ idx) body rfl (by simp [hxl, hIl, hprel, hidxl])
  rw [show (xs ++ Is ++ [(Ps ++ fs).foldl app (cvalOf m.base2.acval rl.ctor ψc)]).length
      = (pre ++ idx).length by simp [hxl, hIl, hprel, hidxl],
    List.drop_length] at hR''
  simp only [List.foldr_nil] at hR''
  rw [hR'', hρ''] at hRD
  have hlenY : ((Ps ++ fs).foldl app (cvalOf m.base2.acval rl.ctor ψc) :: Is.reverse).length
      = (major :: ind.reverse).length := by simp [hIl, hidx]
  have hT1 := Denotes_instantiateLift_inv (σ := consN fs (consN xs ρ)) hlenY (fun j hj => by
      cases j with
      | zero => exact hMajD0
      | succ j =>
        simp only [List.getElem_cons_succ, List.getElem_reverse]
        simp only [List.length_cons, List.length_reverse] at hj
        have := hIsD (mI - rP - 1 - j) (by omega) (by omega)
        simpa [hIl, hidx] using this) _ (d := 0) (fun i => rfl) hT
  have hT2 := Denotes_liftLooseBVars_inv _ hT1
  have hbB : body.looseBVarsBounded (rP + (mI - rP) + 1) = true := by
    have := looseBVarsBounded_foldr_body _ (hTyEq ▸ hlbR)
    simpa [hprel, hidxl, show rP + (mI - rP + 1) = rP + (mI - rP) + 1 by omega] using this
  have hT3 := Denotes_congr_below hT2 hbB
    (ρ' := consN (xs ++ Is ++ [(Ps ++ fs).foldl app (cvalOf m.base2.acval rl.ctor ψc)]) ρ)
    fun j hj => by
    rw [consN_lt _ _ (by simp [hxl, hIl]; omega)]
    simp only [skipAt, insAt, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, List.length_cons,
      List.length_reverse, hIl]
    by_cases hj1 : j < mI - rP + 1
    · simp only [hj1, ↓reduceIte, ↓reduceDIte]
      cases j with
      | zero => simp [hxl, hIl]
      | succ j =>
        simp only [List.getElem_cons_succ, List.getElem_reverse]
        rw [List.getElem_append_left (by simp [hxl, hIl]; omega),
          List.getElem_append_right (by simp [hxl]; omega)]
        congr 1; simp [hxl, hIl]; omega
    · simp only [hj1, ↓reduceIte, show ¬ (j + nF < mI - rP + 1) by omega, ↓reduceDIte]
      rw [consN_ge _ _ (by rw [hfl]; omega), hfl, consN_lt _ _ (by omega),
        List.getElem_append_left (by simp [hxl, hIl]; omega),
        List.getElem_append_left (by simp [hxl]; omega)]
      congr 1; simp [hxl, hIl]; omega
  obtain rfl := ConLeche.Denotes_functional hT3 hRD
  -- the left-hand side lies in it
  have hmemL := hRT.app_mem (m.mem_type _ hmemR φ TVa hTVa σ)
  rw [interp_cvalOf hcl, show (ConstantInfo.recInfo cv mI rP isK rules).name = cv.name from rfl]
    at hmemL
  -- the fired equation
  obtain ⟨Ra, hRa, -, -, hlaw⟩ := hmain (cv.levelParams.map Level.param) (by simp)
  obtain ⟨heqn, -⟩ := hlaw cvj cnP cnF iT hc (rl.ctorLevels cvj.levelParams) σ (xsT ++ isT)
    (psT ++ fsT) TVa TVja restR restC (by simp [xsT, isT, hxl, hIl]; omega)
    (by simp [psT, fsT, hPl, hfl, hnF]) hlenC
    (substFn_ctorLevels φ rl cnP cv.levelParams cvj.levelParams rP)
    (fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · exact hbvWD psT _ _ rfl y hy
      · exact hbvWD fsT _ _ rfl y hy)
    (fun _ => hpin) hTVa' hTVja' (by rw [hψc]; exact hrestR) hrestC
  rw [hψc, Level.substFn_param_self, List.take_left' (by simp [xsT, hxl]),
    List.drop_left' (by simp [psT, hPl])] at heqn
  rw [interp_mkAppN, interp_mkAppN, interp_cvalOf hcl] at heqn
  rw [Expr.instantiateLevelParams_self] at hRa
  obtain ⟨hrhsF, -, -, hrhsB, -⟩ := hwfR.2.2.2.2.2 cv mI rP isK rules rfl rl hrl
  have hRvD := Denotes_of_denote (V := V) hcl 0 rl.rhs hRa
    (fvarsBelow_zero_of_not_hasFvar hrhsF) hrhsB (consN fs (consN xs ρ))
  rw [Expr.closeN_of_hasFvar _ 0 0 hrhsF] at hRvD
  obtain rfl := ConLeche.Denotes_functional hRv hRvD
  rw [interp_closed (V := V) (denote_closed hcl hrhsF hrhsB hRa) (consN fs (consN xs ρ)) σ]
  have hLR : (xs ++ Is ++ [(Ps ++ fs).foldl app (cvalOf m.base2.acval rl.ctor ψc)]).foldl app
        (cvalOf m.base2.acval cv.name φ)
      = (xs ++ fs).foldl app (interp V σ Ra) := by
    rw [← List.foldl_map (f := interp V σ) (g := app),
      ← List.foldl_map (f := interp V σ) (g := app), hvals, List.map_append, hxsI, hfsI] at heqn
    exact heqn
  have hRm : (xs ++ fs).foldl app (interp V σ Ra) ∈ˢ interp V σ restR := hLR ▸ hmemL
  exact ⟨hTu, hmemL, hRm, hLR⟩

/-- **The ι equations hold in the model the invariant carries**, given the rule facts at every
stored rule and `Eq`'s law: at every fit the equation is `Eq`'s truth value of an equality of its
two sides (`ruleEq_sides`). -/
theorem ruleEqsHold_of {env : Env} (m : EnvModelM V env)
    (hfit : ∀ (φ : Name → Nat) (n : Name) (cv : ConstantVal) (mI rP : Nat) (isK : Bool)
      (rules : List RecRule), env.find? n = some (.recInfo cv mI rP isK rules) →
      ∀ rl ∈ rules, RecRuleFit m.base2 φ cv mI rP rl)
    (heq : ∀ (u : Level) (φ : Name → Nat) (ρ : Nat → V) (E A a b : V),
      ConLeche.Denotes (cvalOf m.base2.acval) env φ ρ (.const ConLeche.eqName [u]) E →
      A ∈ˢ (univ (Level.eval φ u) : V) → a ∈ˢ A → b ∈ˢ A →
      app (app (app E A) a) b = eqv a b) :
    ConLeche.RuleEqsHold (cvalOf (V := V) m.base2.acval) env := by
  intro e he φ ρ P hP
  obtain ⟨ds, u, ty, lhs, rhs, rfl, H⟩ := ruleEq_sides m hfit he
  refine ⟨pt, (tele_inhabited_of _ hP fun vs ρ' Y hvl hvf hY => ?_).2⟩
  cases hY with
  | @app _ _ _ Y3 R hY3 hR =>
  cases hY3 with
  | @app _ _ _ Y2 L hY2 hL =>
  cases hY2 with
  | @app _ _ _ E T hE hT =>
  obtain ⟨hTu, hLT, hRT, hLR⟩ := H φ ρ vs ρ' hvl hvf T L R hT hL hR
  rw [heq u φ _ E _ _ _ hE hTu hLT hRT, ← hLR]
  exact ⟨eqv_mem_univZero _ _, pt_mem_eqv_self _⟩

end ConLeche.Model
