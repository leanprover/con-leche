module

public import ConLeche.Verify.Inductives.CopyTypes
public import ConLeche.Verify.Inductives.NestedFacts
import ConLeche.Verify.Mono
import ConLeche.Verify.Deep
import ConLeche.Verify.Leaves
import ConLeche.Verify.InstLevels

public section

/-!
# The copies' stored types, READ off the run (task #279 M-B′ step 3g)

`CopyTypes.lean` (task #298, K.4) proves that the auxiliary install's
annotation of a minted copy reproduces the container's stored type at
the ANNOTATED pin, binder data included, given the target's stability
under the head reader.  This module is the TELESCOPE BOOKKEEPING K.4
named as the model lane's step: it turns the run's facts — the mint
(`mkCopy`: `instPis` of the container's level-instantiated stored type
at the pin's components, closed over the block's parameter binders),
the pin check (`pinsOkAux`: the components annotated at the block's
first stored former's openers) and the install's own annotation run —
into the ALIGNMENT `copyIdxRead_of_align` consumes: the copy's stored
former, opened at the block's openers, IS `instPis` of the container's
stored former at the annotated components.

**The leaf map.**  Every step of the elimination and of the install is
an operation on free-variable LEAVES — `abstract1`/`instantiate1`
(`closeTelescope`/`openPisAtFvars`), `abstractRange`/`instantiateList`
(the pin check), `instPis` (the mint) — and none of them enters an
fvar's type annotation.  `Expr.mapFvars σ` is the one operation they
all are: replace the leaf `fvar i _` by `σ i` where `σ` is defined.
The re-opening of a closed telescope at new openers re-annotates the
leaves (`instantiate1_abstract1_mapFvars`), which is why the raw
terms of the elimination (whose leaves carry the stream's raw domains)
and the annotated ones (whose leaves carry the annotated domains) are
`mapFvars`-images of one another.

**The reader is a leaf-map congruence, directionally.**  K.4's
`SortAgree` asks a component to read EXACTLY like the parameter it
replaces at every arity; what the transport of stability needs is
weaker and directional: WHERE the container's side answers, the
component's side answers the same (`SortAgreeW`, `ProofAgreeW`), and
the readers are congruences for a leaf map whose values satisfy it at
the leaves it hits (`typeSortPW_mapFvars`, `proofPW_mapFvars`).

**Stability, fused with the relation.**  K.4's theorem takes the
relation `AnnotRel R e e'` and the stability `AnnotStable e'` of the
whole target SEPARATELY, so the target must be stable INSIDE the
annotated components too — which is neither measured nor needed (at a
component the annotation run itself is the certificate, `hRok`).
`AnnotRelS` fuses the two: the same relation with the reader's answer
recorded at every STRUCTURAL binder of the right side, and nothing
asked of the leaves.  `annotateCore_of_annotRelS` is K.4's theorem
over it (same proof), and `annotRelS_of_readerStable` PRODUCES it from
the container's stability (`ReaderStable`: the reader answers the
binder's datum at every binder — the strong reading of K.4's
`AnnotStable`, the one the kernel lane measured) by the leaf map that
substitutes the components — no second relation, no transport of a
stability predicate across a substitution: the target's stability is
built by ONE induction over the container's, carrying the map.
-/

namespace ConLeche

open Expr

/-! ## The leaf map -/

/-- **Replace free-variable leaves.**  `fvar i _` becomes `σ i` where
`σ` is defined; the annotations of the leaves `σ` does not hit are not
entered — exactly as `abstract1`, `instantiate1`, `abstractRange` and
`instantiateList` behave.  Values are meant to be bvar-closed: the map
does not shift under binders. -/
@[expose] def Expr.mapFvars (σ : Nat → Option Expr) : Expr → Expr
  | .fvar idx ty =>
    match σ idx with
    | some v => v
    | none => .fvar idx ty
  | .app f a => .app (mapFvars σ f) (mapFvars σ a)
  | .lam ty b m => .lam (mapFvars σ ty) (mapFvars σ b) m
  | .forallE ty b m => .forallE (mapFvars σ ty) (mapFvars σ b) m
  | .letE ty v b => .letE (mapFvars σ ty) (mapFvars σ v) (mapFvars σ b)
  | .proj s i e => .proj s i (mapFvars σ e)
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const n us => .const n us
  | .lit l => .lit l

/-- The one-point leaf map. -/
@[expose] def Expr.single (j : Nat) (v : Expr) : Nat → Option Expr :=
  fun i => if i = j then some v else none

theorem Expr.single_self (j : Nat) (v : Expr) : Expr.single j v j = some v := by
  simp [Expr.single]

theorem Expr.single_ne {j i : Nat} (v : Expr) (h : i ≠ j) : Expr.single j v i = none := by
  simp [Expr.single, h]

/-- A closed value's leaf map is invisible to `instantiate1`. -/
theorem mapFvars_instantiate1 {σ : Nat → Option Expr}
    (hσ : ∀ i v, σ i = some v → v.looseBVarsBounded 0 = true) :
    ∀ (e w : Expr) (k : Nat),
      (e.instantiate1 w k).mapFvars σ = (e.mapFvars σ).instantiate1 (w.mapFvars σ) k := by
  intro e
  induction e with
  | bvar i =>
    intro w k
    by_cases h1 : i = k
    · subst h1; simp [Expr.instantiate1, Expr.mapFvars]
    · by_cases h2 : i > k <;> simp [Expr.instantiate1, h1, h2, Expr.mapFvars]
  | fvar idx ty _ =>
    intro w k
    simp only [Expr.instantiate1, Expr.mapFvars]
    cases hs : σ idx with
    | none => rfl
    | some v =>
      exact (instantiate1_eq_self (looseBVarsBounded_mono (Nat.zero_le k) (hσ idx v hs))).symm
  | sort u => intro w k; rfl
  | const n us => intro w k; rfl
  | lit l => intro w k; rfl
  | app f a ihf iha => intro w k; simp [Expr.instantiate1, Expr.mapFvars, ihf, iha]
  | lam ty b m iht ihb => intro w k; simp [Expr.instantiate1, Expr.mapFvars, iht, ihb]
  | forallE ty b m iht ihb => intro w k; simp [Expr.instantiate1, Expr.mapFvars, iht, ihb]
  | letE ty v b iht ihv ihb => intro w k; simp [Expr.instantiate1, Expr.mapFvars, iht, ihv, ihb]
  | proj s i e ih => intro w k; simp [Expr.instantiate1, Expr.mapFvars, ih]

/-- A term none of whose leaves sits at `j` is fixed by `abstract1 j`. -/
theorem abstract1_eq_self_of_leaves {j : Nat} :
    ∀ (e : Expr) (k : Nat), (∀ l ∈ e.fvarLeaves, l.1 ≠ j) → e.abstract1 j k = e := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro k hl
    have : idx ≠ j := hl (idx, ty) (by simp [Expr.fvarLeaves])
    simp [Expr.abstract1, this]
  | app f a ihf iha =>
    intro k hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    simp [Expr.abstract1, ihf k (fun l h => hl l (Or.inl h)), iha k (fun l h => hl l (Or.inr h))]
  | lam ty b m iht ihb =>
    intro k hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    simp [Expr.abstract1, iht k (fun l h => hl l (Or.inl h)), ihb (k + 1) (fun l h => hl l (Or.inr h))]
  | forallE ty b m iht ihb =>
    intro k hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    simp [Expr.abstract1, iht k (fun l h => hl l (Or.inl h)), ihb (k + 1) (fun l h => hl l (Or.inr h))]
  | letE ty v b iht ihv ihb =>
    intro k hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    simp [Expr.abstract1, iht k (fun l h => hl l (Or.inl (Or.inl h))),
      ihv k (fun l h => hl l (Or.inl (Or.inr h))), ihb (k + 1) (fun l h => hl l (Or.inr h))]
  | proj s i e ih =>
    intro k hl
    simp only [Expr.fvarLeaves] at hl
    simp [Expr.abstract1, ih k hl]
  | _ => intro k _; rfl

/-- Abstraction of a leaf the map does not reach commutes with the map
(the map's values must not carry that leaf either). -/
theorem mapFvars_abstract1 {σ : Nat → Option Expr} {j : Nat} (hj : σ j = none)
    (hno : ∀ i v, σ i = some v → ∀ l ∈ v.fvarLeaves, l.1 ≠ j) :
    ∀ (e : Expr) (k : Nat), (e.abstract1 j k).mapFvars σ = (e.mapFvars σ).abstract1 j k := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro k
    by_cases hidx : idx = j
    · subst hidx
      simp [Expr.abstract1, Expr.mapFvars, hj]
    · simp only [Expr.abstract1, hidx, if_false, Expr.mapFvars]
      cases hs : σ idx with
      | none => simp [Expr.abstract1, hidx]
      | some v => exact (abstract1_eq_self_of_leaves v k (hno idx v hs)).symm
  | app f a ihf iha => intro k; simp [Expr.abstract1, Expr.mapFvars, ihf, iha]
  | lam ty b m iht ihb => intro k; simp [Expr.abstract1, Expr.mapFvars, iht, ihb]
  | forallE ty b m iht ihb => intro k; simp [Expr.abstract1, Expr.mapFvars, iht, ihb]
  | letE ty v b iht ihv ihb => intro k; simp [Expr.abstract1, Expr.mapFvars, iht, ihv, ihb]
  | proj s i e ih => intro k; simp [Expr.abstract1, Expr.mapFvars, ih]
  | _ => intro k; rfl

/-- **Re-opening is a re-annotation**: closing a bvar-bounded term over
a leaf and opening it again at a new annotation replaces every leaf at
that index by the new opener. -/
theorem instantiate1_abstract1_mapFvars {j : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.abstract1 j k).instantiate1 (.fvar j ty) k = e.mapFvars (Expr.single j (.fvar j ty)) := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    have h1 : ¬ (i = k) := by omega
    have h2 : ¬ (i > k) := by omega
    simp [Expr.abstract1, Expr.mapFvars, h1, h2]
  | fvar idx ty' _ =>
    intro k _
    by_cases hidx : idx = j
    · subst hidx; simp [Expr.abstract1, Expr.mapFvars, Expr.single]
    · simp [Expr.abstract1, Expr.mapFvars, Expr.single, hidx]
  | app f a ihf iha =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.abstract1, Expr.mapFvars, ihf k hb.1, iha k hb.2]
  | lam ty b m iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.abstract1, Expr.mapFvars, iht k hb.1, ihb (k + 1) hb.2]
  | forallE ty b m iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.abstract1, Expr.mapFvars, iht k hb.1, ihb (k + 1) hb.2]
  | letE ty v b iht ihv ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.abstract1, Expr.instantiate1, Expr.mapFvars, iht k hb.1.1, ihv k hb.1.2,
      ihb (k + 1) hb.2]
  | proj s i e ih =>
    intro k hb
    simp [Expr.abstract1, Expr.instantiate1, Expr.mapFvars, ih k hb]
  | _ => intro k _; rfl

/-- A map undefined at every leaf is the identity. -/
theorem mapFvars_eq_self {σ : Nat → Option Expr} :
    ∀ (e : Expr), (∀ l ∈ e.fvarLeaves, σ l.1 = none) → e.mapFvars σ = e := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro hl
    have := hl (idx, ty) (by simp [Expr.fvarLeaves])
    simp [Expr.mapFvars, this]
  | app f a ihf iha =>
    intro hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    simp [Expr.mapFvars, ihf (fun l h => hl l (Or.inl h)), iha (fun l h => hl l (Or.inr h))]
  | lam ty b m iht ihb =>
    intro hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    simp [Expr.mapFvars, iht (fun l h => hl l (Or.inl h)), ihb (fun l h => hl l (Or.inr h))]
  | forallE ty b m iht ihb =>
    intro hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    simp [Expr.mapFvars, iht (fun l h => hl l (Or.inl h)), ihb (fun l h => hl l (Or.inr h))]
  | letE ty v b iht ihv ihb =>
    intro hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    simp [Expr.mapFvars, iht (fun l h => hl l (Or.inl (Or.inl h))),
      ihv (fun l h => hl l (Or.inl (Or.inr h))), ihb (fun l h => hl l (Or.inr h))]
  | proj s i e ih =>
    intro hl
    simp only [Expr.fvarLeaves] at hl
    simp [Expr.mapFvars, ih hl]
  | _ => intro _; rfl

/-- A term without free variables is fixed by every leaf map. -/
theorem mapFvars_of_not_hasFvar {σ : Nat → Option Expr} {e : Expr} (h : e.hasFvar = false) :
    e.mapFvars σ = e :=
  mapFvars_eq_self e fun l hl => by
    rw [fvarLeaves_eq_nil_of_not_hasFvar h] at hl
    exact nomatch hl

/-- Two leaf maps compose to one. -/
theorem mapFvars_mapFvars (σ₁ σ₂ : Nat → Option Expr) :
    ∀ (e : Expr), (e.mapFvars σ₁).mapFvars σ₂
      = e.mapFvars (fun i => match σ₁ i with
          | some v => some (v.mapFvars σ₂)
          | none => σ₂ i) := by
  intro e
  induction e with
  | fvar idx ty _ =>
    simp only [Expr.mapFvars]
    cases σ₁ idx <;> simp [Expr.mapFvars]
  | app f a ihf iha => simp [Expr.mapFvars, ihf, iha]
  | lam ty b m iht ihb => simp [Expr.mapFvars, iht, ihb]
  | forallE ty b m iht ihb => simp [Expr.mapFvars, iht, ihb]
  | letE ty v b iht ihv ihb => simp [Expr.mapFvars, iht, ihv, ihb]
  | proj s i e ih => simp [Expr.mapFvars, ih]
  | _ => rfl

/-- The leaf map is structural on a spine. -/
theorem mapFvars_mkAppN (σ : Nat → Option Expr) :
    ∀ (args : List Expr) (f : Expr),
      (Expr.mkAppN f args).mapFvars σ = Expr.mkAppN (f.mapFvars σ) (args.map (·.mapFvars σ))
  | [], _ => rfl
  | a :: args, f => by
    show (Expr.mkAppN (.app f a) args).mapFvars σ = _
    rw [mapFvars_mkAppN σ args (.app f a)]
    rfl

/-- `instPis` at mapped arguments is the mapped residual. -/
theorem instPis_mapFvars {σ : Nat → Option Expr}
    (hσ : ∀ i v, σ i = some v → v.looseBVarsBounded 0 = true) :
    ∀ (args : List Expr) {ty rest : Expr}, Expr.instPis ty args = some rest →
      Expr.instPis (ty.mapFvars σ) (args.map (·.mapFvars σ)) = some (rest.mapFvars σ)
  | [], ty, rest, h => by
    simp only [Expr.instPis, Option.some.injEq] at h
    subst h; rfl
  | a :: args, ty, rest, h => by
    match ty, h with
    | .forallE dom body bm, h =>
      simp only [Expr.instPis] at h
      simp only [List.map_cons, Expr.mapFvars, Expr.instPis]
      rw [← mapFvars_instantiate1 hσ]
      exact instPis_mapFvars hσ args h
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => simp [Expr.instPis] at h

/-- The pin check's re-annotation IS the leaf map at the openers:
abstracting the parameter range and instantiating at the (reversed)
openers replaces each parameter leaf by its opener. -/
theorem instantiateList_abstractRange_eq_mapFvars {n : Nat} {fvs : List Expr}
    (hlen : fvs.length = n) (hfv : ∀ x ∈ fvs, ∃ i ty, x = Expr.fvar i ty) :
    ∀ (e : Expr) (c : Nat), e.looseBVarsBounded c = true →
      Expr.instantiateList (e.abstractRange 0 n c) fvs.reverse c
        = e.mapFvars (fun i => fvs[i]?) := by
  intro e
  induction e with
  | bvar i =>
    intro c hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp [Expr.abstractRange, Expr.instantiateList, Expr.mapFvars, hb]
  | fvar idx ty _ =>
    intro c _
    by_cases hidx : idx < n
    · have hc : 0 ≤ idx ∧ idx < 0 + n := ⟨Nat.zero_le _, by omega⟩
      have hidxL : idx < fvs.length := by omega
      simp only [Expr.abstractRange, hc, and_self, if_true, Expr.mapFvars]
      have hi : c + (0 + n - 1 - idx) - c = n - 1 - idx := by omega
      have hlt : n - 1 - idx < fvs.reverse.length := by
        simp only [List.length_reverse, hlen]; omega
      have hnl : ¬ (c + (0 + n - 1 - idx) < c) := by omega
      rw [Expr.instantiateList]
      simp only [hnl, if_false, hi, hlt, dite_true]
      have h3 : fvs.length - 1 - (n - 1 - idx) = idx := by omega
      have hget : fvs.reverse[n - 1 - idx]'hlt = fvs[idx]'hidxL := by
        rw [List.getElem_reverse]
        simp only [h3]
      rw [hget, List.getElem?_eq_getElem hidxL]
      obtain ⟨i', ty', hx⟩ := hfv _ (List.getElem_mem hidxL)
      rw [hx, Expr.instantiateList]
    · have h' : ¬ (0 ≤ idx ∧ idx < 0 + n) := by omega
      simp only [Expr.abstractRange, h', if_false, Expr.mapFvars,
        List.getElem?_eq_none (show fvs.length ≤ idx by omega)]
      rw [Expr.instantiateList]
  | sort u => intro c _; simp [Expr.abstractRange, Expr.instantiateList, Expr.mapFvars]
  | const n us => intro c _; simp [Expr.abstractRange, Expr.instantiateList, Expr.mapFvars]
  | lit l => intro c _; simp [Expr.abstractRange, Expr.instantiateList, Expr.mapFvars]
  | app f a ihf iha =>
    intro c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange, Expr.mapFvars]
    rw [Expr.instantiateList, ihf c hb.1, iha c hb.2]
  | lam ty b m iht ihb =>
    intro c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange, Expr.mapFvars]
    rw [Expr.instantiateList, iht c hb.1, ihb (c + 1) hb.2]
  | forallE ty b m iht ihb =>
    intro c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange, Expr.mapFvars]
    rw [Expr.instantiateList, iht c hb.1, ihb (c + 1) hb.2]
  | letE ty v b iht ihv ihb =>
    intro c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange, Expr.mapFvars]
    rw [Expr.instantiateList, iht c hb.1.1, ihv c hb.1.2, ihb (c + 1) hb.2]
  | proj s i e ih =>
    intro c hb
    simp only [Expr.abstractRange, Expr.mapFvars]
    rw [Expr.instantiateList, ih c hb]

/-- Scoping survives a scoped leaf map. -/
theorem WScoped.mapFvars {d : Nat} {σ : Nat → Option Expr}
    (hσ : ∀ i v, σ i = some v → WScoped d v) :
    ∀ {e : Expr}, WScoped d e → WScoped d (e.mapFvars σ) := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro hw
    simp only [Expr.mapFvars]
    cases hs : σ idx with
    | none => exact hw
    | some v => exact hσ idx v hs
  | app f a ihf iha => intro hw; simp only [Expr.mapFvars, WScoped] at hw ⊢; exact ⟨ihf hw.1, iha hw.2⟩
  | lam ty b m iht ihb => intro hw; simp only [Expr.mapFvars, WScoped] at hw ⊢; exact ⟨iht hw.1, ihb hw.2⟩
  | forallE ty b m iht ihb => intro hw; simp only [Expr.mapFvars, WScoped] at hw ⊢; exact ⟨iht hw.1, ihb hw.2⟩
  | letE ty v b iht ihv ihb =>
    intro hw; simp only [Expr.mapFvars, WScoped] at hw ⊢; exact ⟨iht hw.1, ihv hw.2.1, ihb hw.2.2⟩
  | proj s i e ih => intro hw; simp only [Expr.mapFvars, WScoped] at hw ⊢; exact ih hw
  | _ => intro hw; exact hw

/-- Boundedness survives a closed leaf map. -/
theorem looseBVarsBounded_mapFvars {σ : Nat → Option Expr}
    (hσ : ∀ i v, σ i = some v → v.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.mapFvars σ).looseBVarsBounded k = true := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro k _
    simp only [Expr.mapFvars]
    cases hs : σ idx with
    | none => rfl
    | some v => exact looseBVarsBounded_mono (Nat.zero_le k) (hσ idx v hs)
  | app f a ihf iha =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true, Expr.mapFvars] at hb ⊢
    exact ⟨ihf k hb.1, iha k hb.2⟩
  | lam ty b m iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true, Expr.mapFvars] at hb ⊢
    exact ⟨iht k hb.1, ihb (k + 1) hb.2⟩
  | forallE ty b m iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true, Expr.mapFvars] at hb ⊢
    exact ⟨iht k hb.1, ihb (k + 1) hb.2⟩
  | letE ty v b iht ihv ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true, Expr.mapFvars] at hb ⊢
    exact ⟨⟨iht k hb.1.1, ihv k hb.1.2⟩, ihb (k + 1) hb.2⟩
  | proj s i e ih =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Expr.mapFvars] at hb ⊢
    exact ih k hb
  | _ => intro k hb; exact hb

/-- The leaves of a mapped term are among the unmapped term's and the
values'. -/
theorem fvarLeaves_mapFvars {σ : Nat → Option Expr} :
    ∀ (e : Expr) {l}, l ∈ (e.mapFvars σ).fvarLeaves →
      l ∈ e.fvarLeaves ∨ ∃ i v, σ i = some v ∧ l ∈ v.fvarLeaves := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro l hl
    simp only [Expr.mapFvars] at hl
    cases hs : σ idx with
    | none => rw [hs] at hl; exact Or.inl hl
    | some v => rw [hs] at hl; exact Or.inr ⟨idx, v, hs, hl⟩
  | app f a ihf iha =>
    intro l hl
    simp only [Expr.mapFvars, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases ihf hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases iha hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | lam ty b m iht ihb =>
    intro l hl
    simp only [Expr.mapFvars, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases iht hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihb hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | forallE ty b m iht ihb =>
    intro l hl
    simp only [Expr.mapFvars, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases iht hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihb hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | letE ty v b iht ihv ihb =>
    intro l hl
    simp only [Expr.mapFvars, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · rcases iht hl with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
    · rcases ihv hl with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
    · rcases ihb hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | proj s i e ih =>
    intro l hl
    simp only [Expr.mapFvars, Expr.fvarLeaves] at hl ⊢
    exact ih hl
  | _ => intro l hl; exact Or.inl hl

/-! ## The head reader, directionally

K.4's `SortAgree find? A v` asks the component `v` to read EXACTLY like
a variable of the parameter's declared type `A`, at every arity.  The
transport of stability needs only the direction "where `A`'s side
answers, `v`'s side answers the same" — the container's binders are the
ones that are stable (the reader answers there), and the substituted
component must not change that answer.  Two readers are consulted:
`typeSortPW` at a `∀`-binder's codomain (through `headTypePW` at the
applied arity) and `proofPW` at a `λ`-binder's body (through
`headProofPW`). -/

/-- The reader at arity `n` on a term: unapplied, `typeSortPW`; applied
to `n` further arguments, `headTypePW` at the head. -/
@[expose] def readAt (find? : Name → Option ConstantInfo) (v : Expr) : Nat → Option PropWhen
  | 0 => typeSortPW find? v
  | n + 1 => headTypePW find? v.getAppFn (v.numArgs + (n + 1))

/-- **Where the declared type answers, the value answers the same**
(the `∀`-binder reader). -/
@[expose] def SortAgreeW (find? : Name → Option ConstantInfo) (A v : Expr) : Prop :=
  ∀ (n : Nat) (pw : PropWhen), residualPW (A.peelNeverPis n) = some pw → readAt find? v n = some pw

/-- The same for the `λ`-binder reader: a variable of type `A` is a
proof exactly when `A` is a proposition. -/
@[expose] def ProofAgreeW (find? : Name → Option ConstantInfo) (A v : Expr) : Prop :=
  ∀ pw : PropWhen, typeSortPW find? A = some pw → headProofPW find? v.getAppFn = some pw

/-- A variable reads like itself. -/
theorem SortAgreeW.fvar_refl (find? : Name → Option ConstantInfo) (i : Nat) (ty : Expr) :
    SortAgreeW find? ty (.fvar i ty) := by
  intro n pw h
  cases n with
  | zero => exact h
  | succ n =>
    show headTypePW find? (Expr.fvar i ty) (0 + (n + 1)) = some pw
    rw [Nat.zero_add]; exact h

theorem ProofAgreeW.fvar_refl (find? : Name → Option ConstantInfo) (i : Nat) (ty : Expr) :
    ProofAgreeW find? ty (.fvar i ty) := fun _ h => h

/-- A leaf map is OK on a term when every value it puts at one of the
term's leaves reads like that leaf's annotation, for both readers. -/
@[expose] def LeafOk (find? : Name → Option ConstantInfo) (σ : Nat → Option Expr) (e : Expr) : Prop :=
  ∀ (i : Nat) (ty v : Expr), (i, ty) ∈ e.fvarLeaves → σ i = some v →
    SortAgreeW find? ty v ∧ ProofAgreeW find? ty v

theorem LeafOk.mono {find? : Name → Option ConstantInfo} {σ : Nat → Option Expr} {e e' : Expr}
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) (h : LeafOk find? σ e) : LeafOk find? σ e' :=
  fun i ty v hl hs => h i ty v (hsub _ hl) hs

theorem LeafOk.app_fn {find? : Name → Option ConstantInfo} {σ : Nat → Option Expr} {f a : Expr}
    (h : LeafOk find? σ (.app f a)) : LeafOk find? σ f :=
  h.mono fun l hl => by simp [Expr.fvarLeaves, hl]

theorem LeafOk.app_arg {find? : Name → Option ConstantInfo} {σ : Nat → Option Expr} {f a : Expr}
    (h : LeafOk find? σ (.app f a)) : LeafOk find? σ a :=
  h.mono fun l hl => by simp [Expr.fvarLeaves, hl]

theorem LeafOk.binder_ty {find? : Name → Option ConstantInfo} {σ : Nat → Option Expr}
    {ty b : Expr} {m : BinderMeta} (h : LeafOk find? σ (.forallE ty b m) ∨ LeafOk find? σ (.lam ty b m)) :
    LeafOk find? σ ty := by
  rcases h with h | h
  · exact h.mono fun l hl => by simp [Expr.fvarLeaves, hl]
  · exact h.mono fun l hl => by simp [Expr.fvarLeaves, hl]

/-- A peeled residual sort survives the leaf map. -/
theorem peelNeverPis_mapFvars {σ : Nat → Option Expr} :
    ∀ (n : Nat) (ty : Expr) (u : Level), ty.peelNeverPis n = some (.sort u) →
      (ty.mapFvars σ).peelNeverPis n = some (.sort u)
  | 0, ty, u, h => by
    rw [Expr.peelNeverPis_zero_inv h]; rfl
  | n + 1, ty, u, h => by
    obtain ⟨t, b, m, rfl, hnev, hb⟩ := Expr.peelNeverPis_succ_inv h
    simp only [Expr.mapFvars, Expr.peelNeverPis, hnev, if_true]
    exact peelNeverPis_mapFvars n b u hb

theorem residualPW_mapFvars {σ : Nat → Option Expr} {n : Nat} {ty : Expr} {pw : PropWhen}
    (h : residualPW (ty.peelNeverPis n) = some pw) :
    residualPW ((ty.mapFvars σ).peelNeverPis n) = some pw := by
  obtain ⟨u, hu, rfl⟩ := residualPW_some_inv h
  rw [peelNeverPis_mapFvars n ty u hu]; rfl

/-- The applied reader is a congruence for an OK leaf map. -/
theorem headTypePW_mapFvars (find? : Name → Option ConstantInfo) {σ : Nat → Option Expr} :
    ∀ (e : Expr), LeafOk find? σ e → ∀ (n : Nat) (pw : PropWhen),
      headTypePW find? e.getAppFn (e.numArgs + (n + 1)) = some pw →
      headTypePW find? (e.mapFvars σ).getAppFn ((e.mapFvars σ).numArgs + (n + 1)) = some pw := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro hok n pw h
    have harg : ∀ m : Nat, m + 1 + (n + 1) = m + (n + 1 + 1) := fun m => by omega
    show headTypePW find? (f.mapFvars σ).getAppFn ((f.mapFvars σ).numArgs + 1 + (n + 1)) = some pw
    rw [harg]
    refine ihf hok.app_fn (n + 1) pw ?_
    have h' : headTypePW find? f.getAppFn (f.numArgs + 1 + (n + 1)) = some pw := h
    rw [harg] at h'
    exact h'
  | fvar idx ty _ =>
    intro hok n pw h
    simp only [Expr.mapFvars]
    cases hs : σ idx with
    | none => exact h
    | some v =>
      have hl : (idx, ty) ∈ (Expr.fvar idx ty).fvarLeaves := by simp [Expr.fvarLeaves]
      have hres : residualPW (ty.peelNeverPis (n + 1)) = some pw := by
        have h' : residualPW (ty.peelNeverPis (0 + (n + 1))) = some pw := h
        rwa [Nat.zero_add] at h'
      exact (hok idx ty v hl hs).1 (n + 1) pw hres
  | const c us => intro _ n pw h; exact h
  | bvar i => intro _ n pw h; exact nomatch h
  | sort u => intro _ n pw h; exact nomatch h
  | lit l => intro _ n pw h; exact nomatch h
  | lam _ _ _ _ _ => intro _ n pw h; exact nomatch h
  | forallE _ _ _ _ _ => intro _ n pw h; exact nomatch h
  | letE _ _ _ _ _ _ => intro _ n pw h; exact nomatch h
  | proj _ _ _ _ => intro _ n pw h; exact nomatch h

/-- **The `∀`-reader is a congruence for an OK leaf map.** -/
theorem typeSortPW_mapFvars (find? : Name → Option ConstantInfo) {σ : Nat → Option Expr}
    (e : Expr) (hok : LeafOk find? σ e) {pw : PropWhen} (h : typeSortPW find? e = some pw) :
    typeSortPW find? (e.mapFvars σ) = some pw := by
  cases e with
  | forallE ty b m => exact h
  | sort u => exact h
  | const c us => exact h
  | fvar idx ty =>
    simp only [Expr.mapFvars]
    cases hs : σ idx with
    | none => exact h
    | some v =>
      have hl : (idx, ty) ∈ (Expr.fvar idx ty).fvarLeaves := by simp [Expr.fvarLeaves]
      exact (hok idx ty v hl hs).1 0 pw h
  | app f a =>
    have h' : headTypePW find? f.getAppFn (f.numArgs + (0 + 1)) = some pw := h
    have := headTypePW_mapFvars find? f hok.app_fn 0 pw h'
    exact this
  | bvar i => exact nomatch h
  | lit l => exact nomatch h
  | lam _ _ _ => exact nomatch h
  | letE _ _ _ => exact nomatch h
  | proj _ _ _ => exact nomatch h

/-- The proof reader at the head is a congruence for an OK leaf map. -/
theorem headProofPW_mapFvars (find? : Name → Option ConstantInfo) {σ : Nat → Option Expr} :
    ∀ (e : Expr), LeafOk find? σ e → ∀ (pw : PropWhen),
      headProofPW find? e.getAppFn = some pw →
      headProofPW find? (e.mapFvars σ).getAppFn = some pw := by
  intro e
  induction e with
  | app f a ihf _ => intro hok pw h; exact ihf hok.app_fn pw h
  | fvar idx ty _ =>
    intro hok pw h
    simp only [Expr.mapFvars]
    cases hs : σ idx with
    | none => exact h
    | some v =>
      have hl : (idx, ty) ∈ (Expr.fvar idx ty).fvarLeaves := by simp [Expr.fvarLeaves]
      exact (hok idx ty v hl hs).2 pw h
  | const c us => intro _ pw h; exact h
  | sort u => intro _ pw h; exact h
  | forallE _ _ _ _ _ => intro _ pw h; exact h
  | lit l => intro _ pw h; exact h
  | bvar i => intro _ pw h; exact nomatch h
  | lam _ _ _ _ _ => intro _ pw h; exact nomatch h
  | letE _ _ _ _ _ _ => intro _ pw h; exact nomatch h
  | proj _ _ _ _ => intro _ pw h; exact nomatch h

/-- A head reading is a `proofPW` reading (a λ has no head reading). -/
theorem proofPW_of_headProofPW (find? : Name → Option ConstantInfo) {v : Expr} {pw : PropWhen}
    (h : headProofPW find? v.getAppFn = some pw) : proofPW find? v = some pw := by
  cases v with
  | lam _ _ _ => exact nomatch h
  | _ => exact h

/-- **The `λ`-reader is a congruence for an OK leaf map.** -/
theorem proofPW_mapFvars (find? : Name → Option ConstantInfo) {σ : Nat → Option Expr}
    (e : Expr) (hok : LeafOk find? σ e) {pw : PropWhen} (h : proofPW find? e = some pw) :
    proofPW find? (e.mapFvars σ) = some pw := by
  cases e with
  | lam ty b m => exact h
  | fvar idx ty =>
    simp only [Expr.mapFvars]
    cases hs : σ idx with
    | none => exact h
    | some v =>
      have hl : (idx, ty) ∈ (Expr.fvar idx ty).fvarLeaves := by simp [Expr.fvarLeaves]
      exact proofPW_of_headProofPW find? ((hok idx ty v hl hs).2 pw h)
  | app f a =>
    exact proofPW_of_headProofPW find? (headProofPW_mapFvars find? (.app f a) hok pw h)
  | _ => exact h

/-! ## Stability under the reader, and the fused relation -/

/-- **The reader answers every binder's datum** — the strong reading of
K.4's `AnnotStable` (no "written" escape: a written datum is not
preserved by level instantiation, the reader's answer is), and the
property the kernel lane measured of every container of the corpus. -/
inductive ReaderStable (find? : Name → Option ConstantInfo) : Nat → Expr → Prop where
  | bvar {d i} : ReaderStable find? d (.bvar i)
  | fvar {d idx ty} : ReaderStable find? d (.fvar idx ty)
  | sort {d u} : ReaderStable find? d (.sort u)
  | const {d n us} : ReaderStable find? d (.const n us)
  | lit {d l} : ReaderStable find? d (.lit l)
  | app {d f a} : ReaderStable find? d f → ReaderStable find? d a →
      ReaderStable find? d (.app f a)
  | forallE {d ty body m} :
      ReaderStable find? d ty →
      ReaderStable find? (d + 1) (body.instantiate1 (.fvar d ty)) →
      typeSortPW find? (body.instantiate1 (.fvar d ty)) = some m.pw →
      ReaderStable find? d (.forallE ty body m)
  | lam {d ty body m} :
      ReaderStable find? d ty →
      ReaderStable find? (d + 1) (body.instantiate1 (.fvar d ty)) →
      proofPW find? (body.instantiate1 (.fvar d ty)) = some m.pw →
      ReaderStable find? d (.lam ty body m)

theorem ReaderStable.toAnnotStable {find? : Name → Option ConstantInfo} :
    ∀ {d : Nat} {e : Expr}, ReaderStable find? d e → AnnotStable find? d e := by
  intro d e h
  induction h with
  | bvar => exact .bvar
  | fvar => exact .fvar
  | sort => exact .sort
  | const => exact .const
  | lit => exact .lit
  | app _ _ ihf iha => exact .app ihf iha
  | forallE _ _ hpw iht ihb => exact .forallE iht ihb (Or.inr hpw)
  | lam _ _ hpw iht ihb => exact .lam iht ihb (Or.inr hpw)

/-- **The relation and the stability, fused.**  `AnnotRelS R d e e'`:
`e` and `e'` differ only at `R`-related leaves, and at every STRUCTURAL
binder of `e'` the reader answers the binder's datum on the body opened
at the RIGHT side's domain — which is where the annotation pass opens
both sides (it opens the raw body at the annotated domain).  Nothing is
asked inside the leaves: there the annotation run is the certificate. -/
inductive AnnotRelS (R : Expr → Expr → Prop) (find? : Name → Option ConstantInfo) :
    Nat → Expr → Expr → Prop where
  | base {d a b} : R a b → AnnotRelS R find? d a b
  | bvar {d} (i : Nat) : AnnotRelS R find? d (.bvar i) (.bvar i)
  | fvar {d} (idx : Nat) (ty : Expr) : AnnotRelS R find? d (.fvar idx ty) (.fvar idx ty)
  | sort {d} (u : Level) : AnnotRelS R find? d (.sort u) (.sort u)
  | const {d} (n : Name) (us : List Level) : AnnotRelS R find? d (.const n us) (.const n us)
  | lit {d} (l : Literal) : AnnotRelS R find? d (.lit l) (.lit l)
  | app {d f f' a a'} : AnnotRelS R find? d f f' → AnnotRelS R find? d a a' →
      AnnotRelS R find? d (.app f a) (.app f' a')
  | forallE {d ty ty' b b'} (m : BinderMeta) :
      AnnotRelS R find? d ty ty' →
      AnnotRelS R find? (d + 1) (b.instantiate1 (.fvar d ty')) (b'.instantiate1 (.fvar d ty')) →
      typeSortPW find? (b'.instantiate1 (.fvar d ty')) = some m.pw →
      AnnotRelS R find? d (.forallE ty b m) (.forallE ty' b' m)
  | lam {d ty ty' b b'} (m : BinderMeta) :
      AnnotRelS R find? d ty ty' →
      AnnotRelS R find? (d + 1) (b.instantiate1 (.fvar d ty')) (b'.instantiate1 (.fvar d ty')) →
      proofPW find? (b'.instantiate1 (.fvar d ty')) = some m.pw →
      AnnotRelS R find? d (.lam ty b m) (.lam ty' b' m)

/-- The relation is monotone in `R`. -/
theorem AnnotRelS.mono {R R' : Expr → Expr → Prop} {find? : Name → Option ConstantInfo}
    (hR : ∀ a b, R a b → R' a b) :
    ∀ {d : Nat} {e e' : Expr}, AnnotRelS R find? d e e' → AnnotRelS R' find? d e e' := by
  intro d e e' h
  induction h with
  | base hab => exact .base (hR _ _ hab)
  | bvar i => exact .bvar i
  | fvar idx ty => exact .fvar idx ty
  | sort u => exact .sort u
  | const n us => exact .const n us
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | forallE m _ _ hpw iht ihb => exact .forallE m iht ihb hpw
  | lam m _ _ hpw iht ihb => exact .lam m iht ihb hpw

/-- A stable term is related to itself (at the empty relation). -/
theorem ReaderStable.toRelS {find? : Name → Option ConstantInfo} {R : Expr → Expr → Prop} :
    ∀ {d : Nat} {e : Expr}, ReaderStable find? d e → AnnotRelS R find? d e e := by
  intro d e h
  induction h with
  | bvar => exact .bvar _
  | fvar => exact .fvar _ _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit => exact .lit _
  | app _ _ ihf iha => exact .app ihf iha
  | forallE _ _ hpw iht ihb => exact .forallE _ iht ihb hpw
  | lam _ _ hpw iht ihb => exact .lam _ iht ihb hpw

/-! ## The annotation theorem over the fused relation (K.4's proof) -/

private theorem annotS_bvar {env : Env} {f d i : Nat} {r : Expr}
    (h : annotateCore mode env (f + 1) d (.bvar i) = .ok r) : r = .bvar i := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

private theorem annotS_fvar {env : Env} {f d idx : Nat} {ty r : Expr}
    (h : annotateCore mode env (f + 1) d (.fvar idx ty) = .ok r) : r = .fvar idx ty := by
  rw [annotateCore_succ] at h
  simp only [annotateBody] at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
  · simp only [throw, throwThe, MonadExceptOf.throw] at h; exact nomatch h

private theorem annotS_sort {env : Env} {f d : Nat} {u : Level} {r : Expr}
    (h : annotateCore mode env (f + 1) d (.sort u) = .ok r) : r = .sort u := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

private theorem annotS_const {env : Env} {f d : Nat} {n : Name} {us : List Level}
    {r : Expr} (h : annotateCore mode env (f + 1) d (.const n us) = .ok r) :
    r = .const n us := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

private theorem annotS_lit {env : Env} {f d : Nat} {l : Literal} {r : Expr}
    (h : annotateCore mode env (f + 1) d (.lit l) = .ok r) : r = .lit l := by
  rw [annotateCore_succ] at h
  cases l with
  | natVal n =>
    simp only [annotateBody] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
    · simp only [throw, throwThe, MonadExceptOf.throw] at h; exact nomatch h
  | strVal s =>
    simp only [annotateBody] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
    · simp only [throw, throwThe, MonadExceptOf.throw] at h; exact nomatch h

/-- **The annotation theorem over the fused relation** (K.4's
`annotateCore_of_annotRel`, with the stability of the target recorded
IN the relation, hence asked at no leaf; the leaf certificate `hRok`
is only owed from the depth the run starts at). -/
theorem annotateCore_of_annotRelS {env : Env} {R : Expr → Expr → Prop} {d₀ : Nat}
    (hRok : ∀ a b, R a b → ∀ (f d' : Nat) (x : Expr), d₀ ≤ d' →
      annotateCore mode env f d' a = .ok x → x = b) :
    ∀ (F : Nat) (e e' : Expr) (d : Nat) (r : Expr), d₀ ≤ d →
      AnnotRelS R env.find? d e e' → WScoped d e' → e'.looseBVarsBounded 0 = true →
      annotateCore mode env F d e = .ok r → r = e' := by
  intro F
  induction F with
  | zero =>
    intro e e' d r _ _ _ _ h
    rw [annotateCore_zero] at h
    simp only [throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  | succ f ih =>
    intro e e' d r hd hrel hw hb h
    cases hrel with
    | base hab => exact hRok _ _ hab _ _ _ hd h
    | bvar i => exact annotS_bvar h
    | fvar idx ty => exact annotS_fvar h
    | sort u => exact annotS_sort h
    | const n us => exact annotS_const h
    | lit l => exact annotS_lit h
    | app hrf hra =>
      obtain ⟨fA, aA, hf1, ha1, rfl⟩ := annotateCore_app_inv h
      simp only [WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      rw [ih _ _ _ _ hd hrf hw.1 hb.1 hf1, ih _ _ _ _ hd hra hw.2 hb.2 ha1]
    | forallE m hrty hrb hpw =>
      rename_i ty₀ ty' b₀ b'
      obtain ⟨tyA, bodyA, hty1, hb1, hcase⟩ := annotateCore_forallE_inv_pw h
      simp only [WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      obtain rfl : ty' = tyA := (ih _ _ _ _ hd hrty hw.1 hb.1 hty1).symm
      obtain rfl : bodyA = b'.instantiate1 (.fvar d ty') :=
        ih _ _ _ _ (Nat.le_succ_of_le hd) hrb (WScoped.instantiate1 hw.1 0 hw.2)
          (looseBVarsBounded_instantiate1 b' 0 hb.2) hb1
      have hround : (b'.instantiate1 (.fvar d ty')).abstract1 d = b' :=
        Expr.instantiate1_abstract1 b' 0 hw.2 hb.2
      rcases hcase with ⟨-, rfl⟩ | ⟨-, pw, hpwEq, rfl⟩
      · rw [hround]
      · have hval : pw = m.pw :=
          Except.ok.inj (hpwEq.symm.trans (annotPwPi_of_reader hpw))
        rw [hround, hval]
    | lam m hrty hrb hpw =>
      rename_i ty₀ ty' b₀ b'
      obtain ⟨tyA, bodyA, hty1, hb1, hcase⟩ := annotateCore_lam_inv_pw h
      simp only [WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      obtain rfl : ty' = tyA := (ih _ _ _ _ hd hrty hw.1 hb.1 hty1).symm
      obtain rfl : bodyA = b'.instantiate1 (.fvar d ty') :=
        ih _ _ _ _ (Nat.le_succ_of_le hd) hrb (WScoped.instantiate1 hw.1 0 hw.2)
          (looseBVarsBounded_instantiate1 b' 0 hb.2) hb1
      have hround : (b'.instantiate1 (.fvar d ty')).abstract1 d = b' :=
        Expr.instantiate1_abstract1 b' 0 hw.2 hb.2
      rcases hcase with ⟨-, rfl⟩ | ⟨-, pw, hpwEq, rfl⟩
      · rw [hround]
      · have hval : pw = m.pw :=
          Except.ok.inj (hpwEq.symm.trans (annotPwLam_of_reader hpw))
        rw [hround, hval]

/-! ## Stability under level instantiation

The container's stored type is stable; the mint instantiates its level
parameters at the occurrence's levels.  Both readers commute with level
instantiation through the datum's own substitution (`typeSortPW`: K.4's
`typeSortPW_at_levels`; `proofPW`: below), so stability transports —
the strong form does; the "written" escape of `AnnotStable` would not
(a written datum is collapsed by `substPW`). -/

theorem Expr.allLevelParamsDefined_getAppFn {ps : List Name} :
    ∀ (e : Expr), e.allLevelParamsDefined ps = true → e.getAppFn.allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    exact ihf h.1
  | _ => intro h; exact h

/-- A reader's answer has its level parameters within the term's. -/
theorem typeSortPW_paramsDefined (find? : Name → Option ConstantInfo)
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true)
    {ps : List Name} {T : Expr} {pw : PropWhen} (hT : T.allLevelParamsDefined ps = true)
    (h : typeSortPW find? T = some pw) : pw.paramsDefined ps = true := by
  have hhead : ∀ {hd : Expr} {k : Nat}, hd.allLevelParamsDefined ps = true →
      headTypePW find? hd k = some pw → pw.paramsDefined ps = true := by
    intro hd k hhd hk
    rcases headTypePW_some_inv find? hk with
      ⟨I, us, ci, u, rfl, hf, -, hlen, hpeel, rfl⟩ | ⟨idx, ty, u, rfl, hpeel, rfl⟩
    · have hus : ∀ v ∈ us, v.allParamsDefined ps = true := by
        simp only [Expr.allLevelParamsDefined, List.all_eq_true] at hhd
        exact hhd
      refine Level.substPW_paramsDefined hlen hus ?_
      have := Expr.allLevelParamsDefined_peelNeverPis k hpeel (hdef I ci hf)
      exact Level.zeronessOf_paramsDefined (by simpa [Expr.allLevelParamsDefined] using this)
    · have := Expr.allLevelParamsDefined_peelNeverPis k hpeel hhd
      exact Level.zeronessOf_paramsDefined (by simpa [Expr.allLevelParamsDefined] using this)
  cases T with
  | forallE ty b m =>
    obtain rfl : pw = m.pw := (Option.some.inj h).symm
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hT
    exact hT.2
  | sort u =>
    obtain rfl : pw = .never := (Option.some.inj h).symm
    simp
  | const c us => exact hhead hT h
  | fvar idx ty => exact hhead hT h
  | app f a =>
    have h' : headTypePW find? f.getAppFn (f.numArgs + 1) = some pw := h
    exact hhead (Expr.allLevelParamsDefined_getAppFn f
      (by simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hT; exact hT.1)) h'
  | bvar i => exact nomatch h
  | lit l => exact nomatch h
  | lam _ _ _ => exact nomatch h
  | letE _ _ _ => exact nomatch h
  | proj _ _ _ => exact nomatch h

/-- The proof reader at a head commutes with level instantiation. -/
theorem headProofPW_instantiateLevelParams (find? : Name → Option ConstantInfo)
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true)
    {ks : List Name} {vs : List Level} {hd : Expr} {pw : PropWhen}
    (h : headProofPW find? hd = some pw) :
    headProofPW find? (hd.instantiateLevelParams ks vs) = some (Level.substPW ks vs pw) := by
  cases hd with
  | const c us =>
    simp only [headProofPW] at h
    cases hf : find? c with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      dsimp only at h
      split at h
      · exact nomatch h
      · next hnt =>
        split at h
        · next hlen =>
          cases hts : typeSortPW find? ci.toConstantVal.type with
          | none => rw [hts] at h; exact nomatch h
          | some pw₀ =>
            rw [hts] at h
            obtain rfl : pw = Level.substPW ci.toConstantVal.levelParams us pw₀ :=
              (Option.some.inj h).symm
            show headProofPW find? (.const c (us.map (Level.subst ks vs))) = _
            simp only [headProofPW, hf, hnt, Bool.false_eq_true, if_false, List.length_map, hlen,
              if_true, hts, Option.map_some]
            exact congrArg some (Level.substPW_comp hlen
              (typeSortPW_paramsDefined find? hdef (hdef c ci hf) hts)).symm
        · exact nomatch h
  | fvar idx ty =>
    show typeSortPW find? (ty.instantiateLevelParams ks vs) = _
    exact typeSortPW_at_levels find? hdef h
  | sort u =>
    obtain rfl : pw = .never := (Option.some.inj h).symm
    rw [Level.substPW_never]; rfl
  | forallE _ _ _ =>
    obtain rfl : pw = .never := (Option.some.inj h).symm
    rw [Level.substPW_never]; rfl
  | lit l =>
    obtain rfl : pw = .never := (Option.some.inj h).symm
    rw [Level.substPW_never]; rfl
  | bvar i => exact nomatch h
  | app _ _ => exact nomatch h
  | lam _ _ _ => exact nomatch h
  | letE _ _ _ => exact nomatch h
  | proj _ _ _ => exact nomatch h

/-- **The `λ`-reader commutes with level instantiation.** -/
theorem proofPW_instantiateLevelParams (find? : Name → Option ConstantInfo)
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true)
    {ks : List Name} {vs : List Level} {e : Expr} {pw : PropWhen}
    (h : proofPW find? e = some pw) :
    proofPW find? (e.instantiateLevelParams ks vs) = some (Level.substPW ks vs pw) := by
  cases e with
  | lam ty b m =>
    obtain rfl : pw = m.pw := (Option.some.inj h).symm
    rfl
  | app f a =>
    have h' : headProofPW find? (Expr.app f a).getAppFn = some pw := h
    show headProofPW find? ((Expr.app f a).instantiateLevelParams ks vs).getAppFn = _
    rw [Expr.getAppFn_instantiateLevelParams']
    exact headProofPW_instantiateLevelParams find? hdef h'
  | bvar i =>
    have h' : headProofPW find? (Expr.bvar i).getAppFn = some pw := h
    show headProofPW find? ((Expr.bvar i).instantiateLevelParams ks vs).getAppFn = _
    rw [Expr.getAppFn_instantiateLevelParams']
    exact headProofPW_instantiateLevelParams find? hdef h'
  | fvar idx ty =>
    have h' : headProofPW find? (Expr.fvar idx ty).getAppFn = some pw := h
    show headProofPW find? ((Expr.fvar idx ty).instantiateLevelParams ks vs).getAppFn = _
    rw [Expr.getAppFn_instantiateLevelParams']
    exact headProofPW_instantiateLevelParams find? hdef h'
  | sort u =>
    have h' : headProofPW find? (Expr.sort u).getAppFn = some pw := h
    show headProofPW find? ((Expr.sort u).instantiateLevelParams ks vs).getAppFn = _
    rw [Expr.getAppFn_instantiateLevelParams']
    exact headProofPW_instantiateLevelParams find? hdef h'
  | const c us =>
    have h' : headProofPW find? (Expr.const c us).getAppFn = some pw := h
    show headProofPW find? ((Expr.const c us).instantiateLevelParams ks vs).getAppFn = _
    rw [Expr.getAppFn_instantiateLevelParams']
    exact headProofPW_instantiateLevelParams find? hdef h'
  | lit l =>
    have h' : headProofPW find? (Expr.lit l).getAppFn = some pw := h
    show headProofPW find? ((Expr.lit l).instantiateLevelParams ks vs).getAppFn = _
    rw [Expr.getAppFn_instantiateLevelParams']
    exact headProofPW_instantiateLevelParams find? hdef h'
  | forallE ty b m =>
    have h' : headProofPW find? (Expr.forallE ty b m).getAppFn = some pw := h
    show headProofPW find? ((Expr.forallE ty b m).instantiateLevelParams ks vs).getAppFn = _
    rw [Expr.getAppFn_instantiateLevelParams']
    exact headProofPW_instantiateLevelParams find? hdef h'
  | letE ty v b =>
    have h' : headProofPW find? (Expr.letE ty v b).getAppFn = some pw := h
    show headProofPW find? ((Expr.letE ty v b).instantiateLevelParams ks vs).getAppFn = _
    rw [Expr.getAppFn_instantiateLevelParams']
    exact headProofPW_instantiateLevelParams find? hdef h'
  | proj s i e =>
    have h' : headProofPW find? (Expr.proj s i e).getAppFn = some pw := h
    show headProofPW find? ((Expr.proj s i e).instantiateLevelParams ks vs).getAppFn = _
    rw [Expr.getAppFn_instantiateLevelParams']
    exact headProofPW_instantiateLevelParams find? hdef h'

/-- **Stability transports across level instantiation.** -/
theorem ReaderStable.instantiateLevelParams {find? : Name → Option ConstantInfo}
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true)
    {ks : List Name} {vs : List Level} :
    ∀ {d : Nat} {e : Expr}, ReaderStable find? d e →
      ReaderStable find? d (e.instantiateLevelParams ks vs) := by
  intro d e h
  induction h with
  | bvar => exact .bvar
  | fvar => exact .fvar
  | sort => exact .sort
  | const => exact .const
  | lit => exact .lit
  | app _ _ ihf iha => exact .app ihf iha
  | @forallE d ty body m _ _ hpw iht ihb =>
    refine .forallE iht ?_ ?_
    · rw [← instantiateLevelParams_instantiate1]; exact ihb
    · rw [← instantiateLevelParams_instantiate1]
      exact typeSortPW_at_levels find? hdef hpw
  | @lam d ty body m _ _ hpw iht ihb =>
    refine .lam iht ?_ ?_
    · rw [← instantiateLevelParams_instantiate1]; exact ihb
    · rw [← instantiateLevelParams_instantiate1]
      exact proofPW_instantiateLevelParams find? hdef hpw

/-! ## The producer: the fused relation from the container's stability

Two leaf maps with the same domain — raw and annotated values at the
same indices, `R`-related where they differ and identical variables
elsewhere — applied to a stable term give the fused relation between
the two images, PROVIDED the annotated values read like the leaves they
replace (`LeafOk`).  The induction is over the stability derivation of
the unmapped term, carrying the maps; at a binder both sides open at the
annotated domain, so the maps are extended at the fresh index by that
opener on both sides (identical), which is where `WScoped` is spent:
the body has no leaf at the fresh index. -/

/-- Two maps agreeing on a term's leaves give the same image. -/
theorem mapFvars_congr {σ σ' : Nat → Option Expr} :
    ∀ (e : Expr), (∀ l ∈ e.fvarLeaves, σ l.1 = σ' l.1) → e.mapFvars σ = e.mapFvars σ' := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro h
    have := h (idx, ty) (by simp [Expr.fvarLeaves])
    simp only [Expr.mapFvars, this]
  | app f a ihf iha =>
    intro h
    simp only [Expr.fvarLeaves, List.mem_append] at h
    simp [Expr.mapFvars, ihf (fun l hl => h l (Or.inl hl)), iha (fun l hl => h l (Or.inr hl))]
  | lam ty b m iht ihb =>
    intro h
    simp only [Expr.fvarLeaves, List.mem_append] at h
    simp [Expr.mapFvars, iht (fun l hl => h l (Or.inl hl)), ihb (fun l hl => h l (Or.inr hl))]
  | forallE ty b m iht ihb =>
    intro h
    simp only [Expr.fvarLeaves, List.mem_append] at h
    simp [Expr.mapFvars, iht (fun l hl => h l (Or.inl hl)), ihb (fun l hl => h l (Or.inr hl))]
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [Expr.fvarLeaves, List.mem_append] at h
    simp [Expr.mapFvars, iht (fun l hl => h l (Or.inl (Or.inl hl))),
      ihv (fun l hl => h l (Or.inl (Or.inr hl))), ihb (fun l hl => h l (Or.inr hl))]
  | proj s i e ih =>
    intro h
    simp only [Expr.fvarLeaves] at h
    simp [Expr.mapFvars, ih h]
  | _ => intro _; rfl

/-- The extension of a leaf map at one index. -/
@[expose] def Expr.extendMap (σ : Nat → Option Expr) (j : Nat) (v : Expr) : Nat → Option Expr :=
  fun i => if i = j then some v else σ i

theorem Expr.extendMap_self (σ : Nat → Option Expr) (j : Nat) (v : Expr) :
    Expr.extendMap σ j v j = some v := by simp [Expr.extendMap]

theorem Expr.extendMap_ne (σ : Nat → Option Expr) {j i : Nat} (v : Expr) (h : i ≠ j) :
    Expr.extendMap σ j v i = σ i := by simp [Expr.extendMap, h]

/-- **The two sides of a leaf map** (raw/annotated): the same domain,
`R`-related or identical-variable values, both bvar-closed. -/
structure MapPair (R : Expr → Expr → Prop) (σr σa : Nat → Option Expr) : Prop where
  dom : ∀ i, (σr i).isNone = (σa i).isNone
  rel : ∀ i vr va, σr i = some vr → σa i = some va →
    R vr va ∨ ∃ j t, vr = .fvar j t ∧ va = .fvar j t
  closedR : ∀ i v, σr i = some v → v.looseBVarsBounded 0 = true
  closedA : ∀ i v, σa i = some v → v.looseBVarsBounded 0 = true

theorem MapPair.extend {R : Expr → Expr → Prop} {σr σa : Nat → Option Expr}
    (h : MapPair R σr σa) (j : Nat) (vr va : Expr)
    (hrel : R vr va ∨ ∃ j' t, vr = .fvar j' t ∧ va = .fvar j' t)
    (hr : vr.looseBVarsBounded 0 = true) (ha : va.looseBVarsBounded 0 = true) :
    MapPair R (Expr.extendMap σr j vr) (Expr.extendMap σa j va) where
  dom i := by
    by_cases hi : i = j
    · subst hi; simp [Expr.extendMap]
    · simp only [Expr.extendMap, hi, if_false]; exact h.dom i
  rel i vr' va' hr' ha' := by
    by_cases hi : i = j
    · subst hi
      simp only [Expr.extendMap, if_true, Option.some.injEq] at hr' ha'
      subst hr' ha'
      exact hrel
    · simp only [Expr.extendMap, hi, if_false] at hr' ha'
      exact h.rel i vr' va' hr' ha'
  closedR i v hv := by
    by_cases hi : i = j
    · subst hi; simp only [Expr.extendMap, if_true, Option.some.injEq] at hv; subst hv; exact hr
    · simp only [Expr.extendMap, hi, if_false] at hv; exact h.closedR i v hv
  closedA i v hv := by
    by_cases hi : i = j
    · subst hi; simp only [Expr.extendMap, if_true, Option.some.injEq] at hv; subst hv; exact ha
    · simp only [Expr.extendMap, hi, if_false] at hv; exact h.closedA i v hv

/-- Opening a binder under a map: opening at the fresh index and then
mapping (with the opener's value at that index) is mapping and then
instantiating at the value — the body has no leaf at the fresh index. -/
theorem mapFvars_open {σ : Nat → Option Expr}
    (hσ : ∀ i v, σ i = some v → v.looseBVarsBounded 0 = true)
    {b : Expr} {j : Nat} (hfresh : ∀ l ∈ b.fvarLeaves, l.1 ≠ j) (ty v : Expr)
    (hv : v.looseBVarsBounded 0 = true) :
    (b.instantiate1 (.fvar j ty)).mapFvars (Expr.extendMap σ j v)
      = (b.mapFvars σ).instantiate1 v := by
  have hσ' : ∀ i v', Expr.extendMap σ j v i = some v' → v'.looseBVarsBounded 0 = true := by
    intro i v' hv'
    by_cases hi : i = j
    · subst hi
      simp only [Expr.extendMap, if_true, Option.some.injEq] at hv'
      subst hv'; exact hv
    · simp only [Expr.extendMap, hi, if_false] at hv'; exact hσ i v' hv'
  rw [mapFvars_instantiate1 hσ']
  have hb : b.mapFvars (Expr.extendMap σ j v) = b.mapFvars σ :=
    mapFvars_congr b fun l hl => Expr.extendMap_ne σ v (hfresh l hl)
  rw [hb]
  show (b.mapFvars σ).instantiate1 (match Expr.extendMap σ j v j with
    | some v' => v' | none => Expr.fvar j ty) = _
  rw [Expr.extendMap_self]

/-- The leaves of an opened body: the body's and the opener's. -/
theorem LeafOk.open {find? : Name → Option ConstantInfo} {σ : Nat → Option Expr} {b ty : Expr}
    {j : Nat} {v : Expr} (hfresh : ∀ l ∈ b.fvarLeaves, l.1 ≠ j)
    (hfreshTy : ∀ l ∈ ty.fvarLeaves, l.1 ≠ j)
    (hb : LeafOk find? σ b) (hty : LeafOk find? σ ty)
    (hv : SortAgreeW find? ty v ∧ ProofAgreeW find? ty v) :
    LeafOk find? (Expr.extendMap σ j v) (b.instantiate1 (.fvar j ty)) := by
  intro i t w hl hs
  rcases fvarLeaves_instantiate1 b 0 hl with hl' | hl'
  · have hne := hfresh _ hl'
    rw [Expr.extendMap_ne σ v hne] at hs
    exact hb i t w hl' hs
  · simp only [Expr.fvarLeaves, List.mem_cons] at hl'
    rcases hl' with hl' | hl'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hl'
      rw [Expr.extendMap_self] at hs
      obtain rfl := Option.some.inj hs
      exact hv
    · have hne := hfreshTy _ hl'
      rw [Expr.extendMap_ne σ v hne] at hs
      exact hty i t w hl' hs

/-- The mapped domain reads like the domain, for both readers (the
opener at the mapped domain). -/
theorem agree_fvar_mapped (find? : Name → Option ConstantInfo) {σ : Nat → Option Expr}
    {ty : Expr} (hty : LeafOk find? σ ty) (d : Nat) :
    SortAgreeW find? ty (.fvar d (ty.mapFvars σ)) ∧ ProofAgreeW find? ty (.fvar d (ty.mapFvars σ)) := by
  refine ⟨fun n pw h => ?_, fun pw h => ?_⟩
  · cases n with
    | zero => exact residualPW_mapFvars h
    | succ n =>
      show headTypePW find? (Expr.fvar d (ty.mapFvars σ)) (0 + (n + 1)) = some pw
      rw [Nat.zero_add]
      exact residualPW_mapFvars h
  · exact typeSortPW_mapFvars find? ty hty h

/-- A component that reads like the mapped domain reads like the domain. -/
theorem agree_of_mapped (find? : Name → Option ConstantInfo) {σ : Nat → Option Expr}
    {ty v : Expr} (hty : LeafOk find? σ ty)
    (h : SortAgreeW find? (ty.mapFvars σ) v ∧ ProofAgreeW find? (ty.mapFvars σ) v) :
    SortAgreeW find? ty v ∧ ProofAgreeW find? ty v :=
  ⟨fun n pw hn => h.1 n pw (residualPW_mapFvars hn),
    fun pw hpw => h.2 pw (typeSortPW_mapFvars find? ty hty hpw)⟩

/-- **The producer**: the fused relation between the raw and the
annotated images of a stable term. -/
theorem annotRelS_of_readerStable {find? : Name → Option ConstantInfo} {R : Expr → Expr → Prop} :
    ∀ {dA : Nat} {e : Expr}, ReaderStable find? dA e → WScoped dA e →
      ∀ (d : Nat) (σr σa : Nat → Option Expr), MapPair R σr σa → LeafOk find? σa e →
        AnnotRelS R find? d (e.mapFvars σr) (e.mapFvars σa) := by
  intro dA e h
  induction h with
  | bvar => intro _ d σr σa _ _; exact .bvar _
  | @fvar dA idx ty =>
    intro _ d σr σa hp _
    simp only [Expr.mapFvars]
    cases hr : σr idx with
    | none =>
      have ha : σa idx = none := by
        have := hp.dom idx
        rw [hr] at this
        simpa [Option.isNone_iff_eq_none] using this.symm
      rw [ha]; exact .fvar _ _
    | some vr =>
      cases ha : σa idx with
      | none =>
        have := hp.dom idx
        rw [hr, ha] at this
        exact nomatch this
      | some va =>
        rcases hp.rel idx vr va hr ha with hR | ⟨j, t, rfl, rfl⟩
        · exact .base hR
        · exact .fvar _ _
  | sort => intro _ d σr σa _ _; exact .sort _
  | const => intro _ d σr σa _ _; exact .const _ _
  | lit => intro _ d σr σa _ _; exact .lit _
  | app _ _ ihf iha =>
    intro hw d σr σa hp hok
    simp only [WScoped] at hw
    exact .app (ihf hw.1 d σr σa hp hok.app_fn) (iha hw.2 d σr σa hp hok.app_arg)
  | @forallE dA ty b m _ _ hpw iht ihb =>
    intro hw d σr σa hp hok
    simp only [WScoped] at hw
    have hokTy : LeafOk find? σa ty := LeafOk.binder_ty (Or.inl hok)
    have hokB : LeafOk find? σa b := hok.mono fun l hl => by simp [Expr.fvarLeaves, hl]
    have hfresh : ∀ l ∈ b.fvarLeaves, l.1 ≠ dA := fun l hl =>
      Nat.ne_of_lt (fvarLeaves_fst_lt hw.2 l hl)
    have hfreshTy : ∀ l ∈ ty.fvarLeaves, l.1 ≠ dA := fun l hl =>
      Nat.ne_of_lt (fvarLeaves_fst_lt hw.1 l hl)
    -- both sides open at the ANNOTATED domain
    let ty' := ty.mapFvars σa
    have hp' : MapPair R (Expr.extendMap σr dA (.fvar d ty')) (Expr.extendMap σa dA (.fvar d ty')) :=
      hp.extend dA _ _ (Or.inr ⟨d, ty', rfl, rfl⟩) rfl rfl
    have hok' : LeafOk find? (Expr.extendMap σa dA (.fvar d ty')) (b.instantiate1 (.fvar dA ty)) :=
      LeafOk.open hfresh hfreshTy hokB hokTy (agree_fvar_mapped find? hokTy d)
    have hwB : WScoped (dA + 1) (b.instantiate1 (.fvar dA ty)) := WScoped.instantiate1 hw.1 0 hw.2
    have hopenR := mapFvars_open hp.closedR hfresh ty (.fvar d ty') rfl
    have hopenA := mapFvars_open hp.closedA hfresh ty (.fvar d ty') rfl
    simp only [Expr.mapFvars]
    refine .forallE m (iht hw.1 d σr σa hp hokTy) ?_ ?_
    · have := ihb hwB (d + 1) _ _ hp' hok'
      rw [hopenR, hopenA] at this
      exact this
    · rw [← hopenA]
      exact typeSortPW_mapFvars find? _ hok' hpw
  | @lam dA ty b m _ _ hpw iht ihb =>
    intro hw d σr σa hp hok
    simp only [WScoped] at hw
    have hokTy : LeafOk find? σa ty := LeafOk.binder_ty (Or.inr hok)
    have hokB : LeafOk find? σa b := hok.mono fun l hl => by simp [Expr.fvarLeaves, hl]
    have hfresh : ∀ l ∈ b.fvarLeaves, l.1 ≠ dA := fun l hl =>
      Nat.ne_of_lt (fvarLeaves_fst_lt hw.2 l hl)
    have hfreshTy : ∀ l ∈ ty.fvarLeaves, l.1 ≠ dA := fun l hl =>
      Nat.ne_of_lt (fvarLeaves_fst_lt hw.1 l hl)
    let ty' := ty.mapFvars σa
    have hp' : MapPair R (Expr.extendMap σr dA (.fvar d ty')) (Expr.extendMap σa dA (.fvar d ty')) :=
      hp.extend dA _ _ (Or.inr ⟨d, ty', rfl, rfl⟩) rfl rfl
    have hok' : LeafOk find? (Expr.extendMap σa dA (.fvar d ty')) (b.instantiate1 (.fvar dA ty)) :=
      LeafOk.open hfresh hfreshTy hokB hokTy (agree_fvar_mapped find? hokTy d)
    have hwB : WScoped (dA + 1) (b.instantiate1 (.fvar dA ty)) := WScoped.instantiate1 hw.1 0 hw.2
    have hopenR := mapFvars_open hp.closedR hfresh ty (.fvar d ty') rfl
    have hopenA := mapFvars_open hp.closedA hfresh ty (.fvar d ty') rfl
    simp only [Expr.mapFvars]
    refine .lam m (iht hw.1 d σr σa hp hokTy) ?_ ?_
    · have := ihb hwB (d + 1) _ _ hp' hok'
      rw [hopenR, hopenA] at this
      exact this
    · rw [← hopenA]
      exact proofPW_mapFvars find? _ hok' hpw

/-! ## The chain of parameters (`instPis`)

The mint instantiates the container's parameters at the components:
each step opens one binder of the stable term at the container's fresh
index and puts the raw component on the left and the annotated one on
the right — the maps extended by an `R`-related pair.  The per-component
premise: the annotated component reads like the container's parameter
domain WITH THE EARLIER COMPONENTS SUBSTITUTED (the domains
`instPisAt` returns), for both readers. -/

/-- `stripPis` survives an opening. -/
theorem stripPis_instantiate1 :
    ∀ (n : Nat) (b v : Expr) (k : Nat) {bs : List (Expr × BinderMeta)} {r : Expr},
      b.stripPis n = some (bs, r) →
      ∃ bs' r', (b.instantiate1 v k).stripPis n = some (bs', r')
  | 0, b, v, k, bs, r, _ => ⟨[], _, rfl⟩
  | n + 1, b, v, k, bs, r, h => by
    match b, h with
    | .forallE ty body m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₀, r₀⟩, h₀, -⟩ := h
      obtain ⟨bs', r', h'⟩ := stripPis_instantiate1 n body v (k + 1) h₀
      exact ⟨(ty.instantiate1 v k, m) :: bs', r', by simp [Expr.instantiate1, Expr.stripPis, h']⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => simp [Expr.stripPis] at h

/-- **The chain**: the fused relation between the raw and the annotated
`instPis` of a stable Π-telescope at `R`-related components. -/
theorem annotRelS_instPis {find? : Name → Option ConstantInfo} {R : Expr → Expr → Prop} :
    ∀ (rawArgs annArgs : List Expr) {dA d : Nat} {e : Expr} (σr σa : Nat → Option Expr),
      ReaderStable find? dA e → WScoped dA e → MapPair R σr σa → LeafOk find? σa e →
      rawArgs.length = annArgs.length →
      (∀ (i : Nat) (vr va : Expr), rawArgs[i]? = some vr → annArgs[i]? = some va →
        R vr va ∧ vr.looseBVarsBounded 0 = true ∧ va.looseBVarsBounded 0 = true) →
      (∃ bs r, e.stripPis annArgs.length = some (bs, r)) →
      ∀ {dsA : List Expr} {restA restR : Expr},
        Expr.instPisAt annArgs (e.mapFvars σa) = some (dsA, restA) →
        Expr.instPis (e.mapFvars σr) rawArgs = some restR →
        (∀ (i : Nat) (A a : Expr), dsA[i]? = some A → annArgs[i]? = some a →
          SortAgreeW find? A a ∧ ProofAgreeW find? A a) →
        AnnotRelS R find? d restR restA
  | [], [], dA, d, e, σr, σa, hst, hw, hp, hok, _, _, _, dsA, restA, restR, hA, hR, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at hA
    simp only [Expr.instPis, Option.some.injEq] at hR
    obtain ⟨-, rfl⟩ := hA
    subst hR
    exact annotRelS_of_readerStable hst hw d σr σa hp hok
  | [], _ :: _, _, _, _, _, _, _, _, _, _, hlen, _, _, _, _, _, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, _, _, _, _, hlen, _, _, _, _, _, _, _, _ => by simp at hlen
  | ar :: rawRest, aa :: annRest, dA, d, e, σr, σa, hst, hw, hp, hok, hlen, hargs, hstrip, dsA,
    restA, restR, hA, hR, hdoms => by
    obtain ⟨bs, r, hstrip⟩ := hstrip
    match e, hst, hw, hok, hstrip with
    | .forallE ty b m, .forallE _ hstB hpw, hw, hok, hstrip =>
      rename_i hstTy
      simp only [WScoped] at hw
      simp only [Expr.mapFvars, Expr.instPisAt, Option.map_eq_some_iff] at hA
      obtain ⟨⟨ds', restA'⟩, hA', hA''⟩ := hA
      simp only [Prod.mk.injEq] at hA''
      obtain ⟨rfl, rfl⟩ := hA''
      simp only [Expr.mapFvars, Expr.instPis] at hR
      have hokTy : LeafOk find? σa ty := LeafOk.binder_ty (Or.inl hok)
      have hokB : LeafOk find? σa b := hok.mono fun l hl => by simp [Expr.fvarLeaves, hl]
      have hfresh : ∀ l ∈ b.fvarLeaves, l.1 ≠ dA := fun l hl =>
        Nat.ne_of_lt (fvarLeaves_fst_lt hw.2 l hl)
      have hfreshTy : ∀ l ∈ ty.fvarLeaves, l.1 ≠ dA := fun l hl =>
        Nat.ne_of_lt (fvarLeaves_fst_lt hw.1 l hl)
      obtain ⟨hRa, hcr, hca⟩ := hargs 0 ar aa rfl rfl
      have hp' : MapPair R (Expr.extendMap σr dA ar) (Expr.extendMap σa dA aa) :=
        hp.extend dA ar aa (Or.inl hRa) hcr hca
      have hagree : SortAgreeW find? ty aa ∧ ProofAgreeW find? ty aa :=
        agree_of_mapped find? hokTy (hdoms 0 _ aa rfl rfl)
      have hok' : LeafOk find? (Expr.extendMap σa dA aa) (b.instantiate1 (.fvar dA ty)) :=
        LeafOk.open hfresh hfreshTy hokB hokTy hagree
      have hwB : WScoped (dA + 1) (b.instantiate1 (.fvar dA ty)) := WScoped.instantiate1 hw.1 0 hw.2
      have hopenR := mapFvars_open hp.closedR hfresh ty ar hcr
      have hopenA := mapFvars_open hp.closedA hfresh ty aa hca
      rw [← hopenA] at hA'
      rw [← hopenR] at hR
      simp only [List.length_cons, Expr.stripPis, Option.map_eq_some_iff] at hstrip
      obtain ⟨⟨bs₀, r₀⟩, hstrip₀, -⟩ := hstrip
      refine annotRelS_instPis rawRest annRest _ _ hstB hwB hp' hok' (by simpa using hlen)
        (fun i vr va hr ha => hargs (i + 1) vr va hr ha)
        (by
          obtain ⟨bs', r', h'⟩ := stripPis_instantiate1 annRest.length b (.fvar dA ty) 0 hstrip₀
          exact ⟨bs', r', h'⟩)
        hA' hR (fun i A a hAi hai => hdoms (i + 1) A a hAi hai)
    | .bvar _, _, _, _, hstrip | .fvar _ _, _, _, _, hstrip | .sort _, _, _, _, hstrip
    | .const _ _, _, _, _, hstrip | .app _ _, _, _, _, hstrip | .lam _ _ _, _, _, _, hstrip
    | .lit _, _, _, _, hstrip => simp [Expr.stripPis] at hstrip

end ConLeche
