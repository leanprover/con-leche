module

public import ConLeche.Model.RecRulesHold
public import ConLeche.Model.IndTele
public import ConLeche.Model.IndFrame
public import ConLeche.Model.IndPointKit

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

/-- A fit's residual is determined. -/
theorem TeleFit.rest_unique {ρ : Nat → V} {T : Term} {vs : List V} {r₁ r₂ : V}
    (h₁ : TeleFit V ρ T vs r₁) (h₂ : TeleFit V ρ T vs r₂) : r₁ = r₂ := by
  induction h₁ with
  | nil => exact (teleFit_nil_inv h₂).symm
  | cons _ _ ih =>
    cases h₂ with
    | cons _ h₂ => exact ih h₂

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
theorem denote_peel {acval : Name → (Name → Nat) → Term} {env : Env} {φ : Name → Nat} :
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
      obtain ⟨Γ, R, b', hP, hR, hc, hfb'', hlb''⟩ := denote_peel k hB hs''
        (Expr.fvarsBelow_instantiate1 0 hfb'.2)
        (ConLeche.looseBVarsBounded_instantiate1 _ 0 hlb'.2)
      have hbb : b₀.looseBVarsBounded (k + 1) = true := by
        have := looseBVarsBounded_foldr_body ds' hlb'.2
        rwa [hl, Nat.add_comm] at this
      refine ⟨Γ ++ [tA], R, b', .cons hP, by rwa [show d + (k + 1) = d + 1 + k by omega], ?_,
        by rwa [show d + (k + 1) = d + 1 + k by omega], hlb''⟩
      rw [show d + (k + 1) = d + 1 + k by omega, hc, Nat.zero_add,
        Expr.closeN_instantiate1 b₀ k hbb (fvarsBelow_foldr_body ds' hfb'.2)]

end Subst

end ConLeche.Model
