module

public import ConLeche.SetTheory.Derive.Empty

@[expose] public section

/-!
# First-order definability combinators and the replacement bridge

Defines `DefRel` and `DefFun` over `Formula` (with value parameters in
`V`), together with full closure under boolean connectives, quantifiers,
bounded quantifiers, finite iterations, re-indexing, composition,
conditionals, unique choice, and the set-theoretic primitives (`empty`,
`upair`, `sUnion`, `power`, `image`).

Provides `hasImage_of_def` (`DefFunOn a f → HasImage f a`) from
`SetTheory.replacement`, and the pure-core tactic macro `fo_def`
wrapping `solve_by_elim` with pointwise `*_apply` rules (zero
`import Lean`).
-/

namespace ConLeche.SetTheory

universe u

/-! ### Private index-renaming helpers -/

private def padLeft (k p₁ p₂ : Nat) (i : Fin (k + p₁)) : Fin (k + (p₁ + p₂)) :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.add_le_add_left (Nat.le_add_right p₁ p₂) k)⟩

private def padRight (k p₁ p₂ : Nat) (i : Fin (k + p₂)) : Fin (k + (p₁ + p₂)) :=
  if h : i.val < k then
    ⟨i.val, Nat.lt_of_lt_of_le h (Nat.le_add_right k (p₁ + p₂))⟩
  else
    ⟨k + p₁ + (i.val - k), by
      have hsub : i.val - k < p₂ :=
        Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) i.isLt
      omega⟩

private theorem fappend_padLeft {α : Sort u} {k p₁ p₂ : Nat} (env : Fin k → α)
    (ps₁ : Fin p₁ → α) (ps₂ : Fin p₂ → α) (i : Fin (k + p₁)) :
    fappend env (fappend ps₁ ps₂) (padLeft k p₁ p₂ i) = fappend env ps₁ i := by
  by_cases hi : i.val < k
  · have hi' : (padLeft k p₁ p₂ i).val < k := hi
    rw [fappend_lt env (fappend ps₁ ps₂) hi', fappend_lt env ps₁ hi]
    rfl
  · have hle : k ≤ i.val := Nat.le_of_not_lt hi
    have hle' : k ≤ (padLeft k p₁ p₂ i).val := hle
    rw [fappend_ge env (fappend ps₁ ps₂) hle', fappend_ge env ps₁ hle]
    have hsub : i.val - k < p₁ := Nat.sub_lt_left_of_lt_add hle i.isLt
    exact fappend_lt ps₁ ps₂ hsub

private theorem fappend_padRight {α : Sort u} {k p₁ p₂ : Nat} (env : Fin k → α)
    (ps₁ : Fin p₁ → α) (ps₂ : Fin p₂ → α) (i : Fin (k + p₂)) :
    fappend env (fappend ps₁ ps₂) (padRight k p₁ p₂ i) = fappend env ps₂ i := by
  by_cases hi : i.val < k
  · simp only [padRight, hi, ↓reduceDIte]
    rw [fappend_lt env (fappend ps₁ ps₂) hi, fappend_lt env ps₂ hi]
  · have hle : k ≤ i.val := Nat.le_of_not_lt hi
    simp only [padRight, hi, ↓reduceDIte]
    have hge : k ≤ k + p₁ + (i.val - k) :=
      Nat.le_trans (Nat.le_add_right k p₁) (Nat.le_add_right (k + p₁) (i.val - k))
    have hsub : i.val - k < p₂ := Nat.sub_lt_left_of_lt_add hle i.isLt
    have hlt2 : k + p₁ + (i.val - k) < k + (p₁ + p₂) := by omega
    rw [fappend_ge env (fappend ps₁ ps₂) (i := ⟨k + p₁ + (i.val - k), hlt2⟩) hge,
        fappend_ge env ps₂ hle]
    have hge2 : p₁ ≤ (⟨k + p₁ + (i.val - k) - k,
        Nat.sub_lt_left_of_lt_add hge hlt2⟩ : Fin (p₁ + p₂)).val := by
      dsimp; omega
    rw [fappend_ge ps₁ ps₂ hge2]
    congr 1
    apply Fin.ext
    dsimp
    omega

variable {V : Type u} [SetTheory V]

/-- A `k`-ary relation on `V` is first-order definable (with parameters
in `V`). -/
def DefRel (k : Nat) (R : (Fin k → V) → Prop) : Prop :=
  ∃ (p : Nat) (φ : Formula (k + p)) (params : Fin p → V),
    ∀ env, R env ↔ φ.eval (Mem (V := V)) (fappend env params)

/-- Unary definable predicate. -/
abbrev DefPred (P : V → Prop) : Prop := DefRel 1 fun v => P (v 0)

/-- Binary definable predicate. -/
abbrev DefPred2 (P : V → V → Prop) : Prop := DefRel 2 fun v => P (v 0) (v 1)

/-- A `k`-ary function on `V` is first-order definable if its graph
relation `v 0 = F (ftail v)` is `DefRel (k + 1)`. -/
def DefFun (k : Nat) (F : (Fin k → V) → V) : Prop :=
  DefRel (k + 1) fun v => v 0 = F (ftail v)

/-- 0-ary definable function (constant). -/
abbrev DefFun0 (c : V) : Prop := DefFun 0 fun _ => c

/-- Unary definable function. -/
abbrev DefFun1 (f : V → V) : Prop := DefFun 1 fun v => f (v 0)

/-- Binary definable function. -/
abbrev DefFun2 (f : V → V → V) : Prop := DefFun 2 fun v => f (v 0) (v 1)

/-- Ternary definable function. -/
abbrev DefFun3 (f : V → V → V → V) : Prop := DefFun 3 fun v => f (v 0) (v 1) (v 2)

/-- Predicate definable *on* a set `a` (agrees with a global `DefPred` on `a`). -/
def DefPredOn (a : V) (P : V → Prop) : Prop :=
  ∃ Q : V → Prop, DefPred Q ∧ ∀ x, x ∈ˢ a → (P x ↔ Q x)

/-- Function definable *on* a set `a` (agrees with a global `DefFun1` on `a`). -/
def DefFunOn (a : V) (F : V → V) : Prop :=
  ∃ G : V → V, DefFun 1 (fun v => G (v 0)) ∧ ∀ x, x ∈ˢ a → F x = G x

theorem DefPredOn.of_defPred {a : V} {P : V → Prop} (hP : DefPred P) :
    DefPredOn a P :=
  ⟨P, hP, fun _ _ => Iff.rfl⟩

theorem DefPredOn.congr {a : V} {P Q : V → Prop}
    (h : ∀ x, x ∈ˢ a → (P x ↔ Q x)) (hP : DefPredOn a P) : DefPredOn a Q := by
  obtain ⟨R, hR, hPR⟩ := hP
  exact ⟨R, hR, fun x hx => (h x hx).symm.trans (hPR x hx)⟩

theorem DefFunOn.of_defFun1 {a : V} {F : V → V}
    (hF : DefFun 1 (fun v => F (v 0))) : DefFunOn a F :=
  ⟨F, hF, fun _ _ => rfl⟩

theorem DefFunOn.congr {a : V} {F G : V → V}
    (h : ∀ x, x ∈ˢ a → F x = G x) (hF : DefFunOn a F) : DefFunOn a G := by
  obtain ⟨H, hH, hFH⟩ := hF
  exact ⟨H, hH, fun x hx => (h x hx).symm.trans (hFH x hx)⟩

/-! ### `DefRel` closure combinators -/

namespace DefRel

theorem congr {k : Nat} {R S : (Fin k → V) → Prop} (hR : DefRel k R)
    (h : ∀ env, R env ↔ S env) : DefRel k S := by
  obtain ⟨p, φ, params, hφ⟩ := hR
  exact ⟨p, φ, params, fun env => (h env).symm.trans (hφ env)⟩

theorem true {k : Nat} : DefRel (V := V) k fun _ => True :=
  ⟨0, Formula.truth, Fin.elim0, fun env =>
    ⟨fun _ => (Formula.eval_truth (Mem (V := V)) (fappend env Fin.elim0)).mpr trivial,
     fun _ => trivial⟩⟩

theorem false {k : Nat} : DefRel (V := V) k fun _ => False :=
  ⟨0, Formula.falsity, Fin.elim0, fun env =>
    ⟨fun h => False.elim h,
     fun h => (Formula.eval_falsity (Mem (V := V)) (fappend env Fin.elim0)).mp h⟩⟩

theorem constProp {k : Nat} (P : Prop) : DefRel (V := V) k fun _ => P := by
  by_cases hP : P
  · exact (DefRel.true (V := V)).congr fun _ => ⟨fun _ => hP, fun _ => trivial⟩
  · exact (DefRel.false (V := V)).congr fun _ => ⟨False.elim, fun h => absurd h hP⟩

theorem reIndex {m n : Nat} {R : (Fin m → V) → Prop} (hR : DefRel m R)
    (f : Fin m → Fin n) : DefRel n fun env => R (fun i => env (f i)) := by
  obtain ⟨p, φ, params, hφ⟩ := hR
  let f' : Fin (m + p) → Fin (n + p) := fun i =>
    if h : i.val < m then
      ⟨(f ⟨i.val, h⟩).val, Nat.lt_of_lt_of_le (f ⟨i.val, h⟩).isLt (Nat.le_add_right n p)⟩
    else
      ⟨n + (i.val - m), by
        have hsub : i.val - m < p :=
          Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) i.isLt
        exact Nat.add_lt_add_left hsub n⟩
  refine ⟨p, φ.rename f', params, fun env => ?_⟩
  rw [Formula.eval_rename]
  refine (hφ (fun i => env (f i))).trans ?_
  have heqv : (fun i => fappend env params (f' i)) =
      fappend (fun i => env (f i)) params := by
    funext i
    by_cases hi : i.val < m
    · simp only [f', hi, ↓reduceDIte]
      rw [fappend_lt env params (f ⟨i.val, hi⟩).isLt, fappend_lt (fun i => env (f i)) params hi]
    · have hle : m ≤ i.val := Nat.le_of_not_lt hi
      simp only [f', hi, ↓reduceDIte]
      have hge : n ≤ n + (i.val - m) := Nat.le_add_right n (i.val - m)
      rw [fappend_ge env params hge, fappend_ge (fun i => env (f i)) params hle]
      congr 1
      apply Fin.ext
      dsimp
      omega
  rw [heqv]

theorem weaken {k : Nat} {R : (Fin k → V) → Prop} (hR : DefRel k R) :
    DefRel (k + 1) fun env => R (ftail env) :=
  hR.reIndex Fin.succ

theorem fixParam {k : Nat} {R : (Fin (k + 1) → V) → Prop}
    (hR : DefRel (k + 1) R) (c : V) : DefRel k fun env => R (fcons c env) := by
  obtain ⟨p, φ, params, hφ⟩ := hR
  let f' : Fin ((k + 1) + p) → Fin (k + (p + 1)) := fun i =>
    if h0 : i.val = 0 then ⟨k, Nat.lt_add_of_pos_right (Nat.zero_lt_succ p)⟩
    else if hk : i.val < k + 1 then
      ⟨i.val - 1, by omega⟩
    else
      ⟨i.val, by omega⟩
  refine ⟨p + 1, φ.rename f', fcons c params, fun env => ?_⟩
  rw [Formula.eval_rename]
  refine (hφ (fcons c env)).trans ?_
  have heqv : (fun i => fappend env (fcons c params) (f' i)) =
      fappend (fcons c env) params := by
    funext i
    by_cases h0 : i.val = 0
    · simp only [f', h0, ↓reduceDIte]
      rw [fappend_ge env (fcons c params) (Nat.le_refl k)]
      have hilt : i.val < k + 1 := by omega
      rw [fappend_lt (fcons c env) params hilt]
      have hk0 : (⟨k - k, Nat.sub_lt_left_of_lt_add (Nat.le_refl k)
          (Nat.lt_add_of_pos_right (Nat.zero_lt_succ p))⟩ : Fin (p + 1)) = 0 :=
        Fin.ext (Nat.sub_self k)
      have hi0 : (⟨i.val, hilt⟩ : Fin (k + 1)) = 0 := Fin.ext h0
      rw [hk0, hi0]
      rfl
    · by_cases hk : i.val < k + 1
      · simp only [f', h0, hk, ↓reduceDIte]
        rw [fappend_lt env (fcons c params) (by dsimp; omega),
            fappend_lt (fcons c env) params hk]
        rcases i with ⟨v, hv⟩
        cases v with
        | zero => exact absurd rfl h0
        | succ v => rfl
      · simp only [f', h0, hk, ↓reduceDIte]
        have hle : k + 1 ≤ i.val := Nat.le_of_not_lt hk
        have hlek : k ≤ i.val := Nat.le_trans (Nat.le_succ k) hle
        rw [fappend_ge env (fcons c params) hlek, fappend_ge (fcons c env) params hle]
        have hfin : (⟨i.val - k, Nat.sub_lt_left_of_lt_add hlek (by omega)⟩ : Fin (p + 1)) =
            (⟨i.val - (k + 1), Nat.sub_lt_left_of_lt_add hle i.isLt⟩ : Fin p).succ := by
          apply Fin.ext
          dsimp
          omega
        rw [hfin, fcons_succ]
  rw [heqv]

theorem not {k : Nat} {R : (Fin k → V) → Prop} (hR : DefRel k R) :
    DefRel k fun env => ¬ R env := by
  obtain ⟨p, φ, params, hφ⟩ := hR
  exact ⟨p, .not φ, params, fun env => not_congr (hφ env)⟩

theorem and {k : Nat} {R S : (Fin k → V) → Prop}
    (hR : DefRel k R) (hS : DefRel k S) :
    DefRel k fun env => R env ∧ S env := by
  obtain ⟨p₁, φ₁, params₁, hφ₁⟩ := hR
  obtain ⟨p₂, φ₂, params₂, hφ₂⟩ := hS
  refine ⟨p₁ + p₂, .and (φ₁.rename (padLeft k p₁ p₂)) (φ₂.rename (padRight k p₁ p₂)),
    fappend params₁ params₂, fun env => ?_⟩
  simp only [Formula.eval_and, Formula.eval_rename]
  have e₁ : (fun i => fappend env (fappend params₁ params₂) (padLeft k p₁ p₂ i)) =
      fappend env params₁ := funext (fappend_padLeft env params₁ params₂)
  have e₂ : (fun i => fappend env (fappend params₁ params₂) (padRight k p₁ p₂ i)) =
      fappend env params₂ := funext (fappend_padRight env params₁ params₂)
  rw [e₁, e₂]
  exact and_congr (hφ₁ env) (hφ₂ env)

theorem or {k : Nat} {R S : (Fin k → V) → Prop}
    (hR : DefRel k R) (hS : DefRel k S) :
    DefRel k fun env => R env ∨ S env :=
  ((not hR).and (not hS)).not.congr fun env => by
    constructor
    · intro h
      by_cases hr : R env
      · exact Or.inl hr
      · by_cases hs : S env
        · exact Or.inr hs
        · exact absurd ⟨hr, hs⟩ h
    · rintro (hr | hs) ⟨hnr, hns⟩
      · exact hnr hr
      · exact hns hs

theorem imp {k : Nat} {R S : (Fin k → V) → Prop}
    (hR : DefRel k R) (hS : DefRel k S) :
    DefRel k fun env => R env → S env :=
  (hR.and (not hS)).not.congr fun env => by
    constructor
    · intro h hr
      exact Classical.byContradiction fun hns => h ⟨hr, hns⟩
    · intro hrs ⟨hr, hns⟩
      exact hns (hrs hr)

theorem iff {k : Nat} {R S : (Fin k → V) → Prop}
    (hR : DefRel k R) (hS : DefRel k S) :
    DefRel k fun env => R env ↔ S env :=
  ((hR.imp hS).and (hS.imp hR)).congr fun _ =>
    ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem exists_ {k : Nat} {R : (Fin (k + 1) → V) → Prop}
    (hR : DefRel (k + 1) R) : DefRel k fun env => ∃ x, R (fcons x env) := by
  obtain ⟨p, φ, params, hφ⟩ := hR
  let cast : Fin ((k + 1) + p) → Fin ((k + p) + 1) :=
    fun i => ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add k p)⟩
  refine ⟨p, .exists_ (φ.rename cast), params, fun env => ?_⟩
  simp only [Formula.eval_exists, Formula.eval_rename]
  refine exists_congr fun x => ?_
  refine (hφ (fcons x env)).trans ?_
  have heqv : (fun i => fcons x (fappend env params) (cast i)) =
      fappend (fcons x env) params := by
    funext i
    rw [fcons_fappend x env params (cast i)]
  rw [heqv]

theorem exists_curry {k : Nat} {R : V → (Fin k → V) → Prop}
    (hR : DefRel (k + 1) fun v => R (v 0) (ftail v)) :
    DefRel k fun env => ∃ x, R x env :=
  hR.exists_

theorem forall_ {k : Nat} {R : (Fin (k + 1) → V) → Prop}
    (hR : DefRel (k + 1) R) : DefRel k fun env => ∀ x, R (fcons x env) :=
  (exists_ (not hR)).not.congr fun env => by
    constructor
    · intro h x
      exact Classical.byContradiction fun hnx => h ⟨x, hnx⟩
    · intro h ⟨x, hnx⟩
      exact hnx (h x)

theorem forall_curry {k : Nat} {R : V → (Fin k → V) → Prop}
    (hR : DefRel (k + 1) fun v => R (v 0) (ftail v)) :
    DefRel k fun env => ∀ x, R x env :=
  hR.forall_

theorem finForall {n k : Nat} {R : Fin n → (Fin k → V) → Prop}
    (hR : ∀ i : Fin n, DefRel k (R i)) :
    DefRel k fun env => ∀ i : Fin n, R i env := by
  induction n with
  | zero => exact (DefRel.true (V := V)).congr fun _ => ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩
  | succ n ih =>
    have ih' := ih (fun i => hR i.castSucc)
    have hn := hR ⟨n, Nat.lt_succ_self n⟩
    exact (ih'.and hn).congr fun env =>
      ⟨fun ⟨h1, h2⟩ ⟨i, hi⟩ => by
         rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
         · exact h1 ⟨i, h⟩
         · exact h2,
       fun h => ⟨fun i => h i.castSucc, h ⟨n, Nat.lt_succ_self n⟩⟩⟩

theorem finExists {n k : Nat} {R : Fin n → (Fin k → V) → Prop}
    (hR : ∀ i : Fin n, DefRel k (R i)) :
    DefRel k fun env => ∃ i : Fin n, R i env := by
  induction n with
  | zero => exact (DefRel.false (V := V)).congr fun _ => ⟨False.elim, fun ⟨i, _⟩ => Fin.elim0 i⟩
  | succ n ih =>
    have ih' := ih (fun i => hR i.castSucc)
    have hn := hR ⟨n, Nat.lt_succ_self n⟩
    exact (ih'.or hn).congr fun env =>
      ⟨by rintro (⟨i, hi⟩ | hn)
          · exact ⟨i.castSucc, hi⟩
          · exact ⟨⟨n, Nat.lt_succ_self n⟩, hn⟩,
       by rintro ⟨⟨i, hi⟩, hri⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
          · exact Or.inl ⟨⟨i, h⟩, hri⟩
          · exact Or.inr hri⟩

theorem finForall_lt {n k : Nat} {R : Nat → (Fin k → V) → Prop}
    (hR : ∀ i, i < n → DefRel k (R i)) :
    DefRel k fun env => ∀ i, i < n → R i env := by
  have h := finForall (fun i : Fin n => hR i.val i.isLt)
  exact h.congr fun env =>
    ⟨fun hf i hi => hf ⟨i, hi⟩, fun hf ⟨i, hi⟩ => hf i hi⟩

theorem finExists_lt {n k : Nat} {R : Nat → (Fin k → V) → Prop}
    (hR : ∀ i, i < n → DefRel k (R i)) :
    DefRel k fun env => ∃ i, i < n ∧ R i env := by
  have h := finExists (fun i : Fin n => hR i.val i.isLt)
  exact h.congr fun env =>
    ⟨fun ⟨i, hi⟩ => ⟨i.val, i.isLt, hi⟩, fun ⟨i, hi, hri⟩ => ⟨⟨i, hi⟩, hri⟩⟩

end DefRel

/-! ### `DefFun` core combinators and composition -/

namespace DefFun

theorem congr {k : Nat} {F G : (Fin k → V) → V} (hF : DefFun k F)
    (h : ∀ env, F env = G env) : DefFun k G :=
  DefRel.congr hF fun v => by rw [h (ftail v)]

theorem proj {k : Nat} (i : Fin k) : DefFun (V := V) k fun env => env i :=
  ⟨0, Formula.eq 0 i.succ, Fin.elim0, fun _ => by simp⟩

theorem reIndex {m n : Nat} {F : (Fin m → V) → V} (hF : DefFun m F)
    (f : Fin m → Fin n) : DefFun n fun env => F (fun i => env (f i)) :=
  DefRel.congr (DefRel.reIndex hF (Formula.liftFin f)) fun _ => Iff.rfl

theorem weaken {k : Nat} {F : (Fin k → V) → V} (hF : DefFun k F) :
    DefFun (k + 1) fun env => F (ftail env) :=
  hF.reIndex Fin.succ

end DefFun

private theorem defRel_comp_aux :
    ∀ (m : Nat) {r k : Nat} {R : (Fin (r + m) → V) → Prop}
      {Gs : Fin m → (Fin k → V) → V} {idx : Fin r → Fin k},
      DefRel (r + m) R →
      (∀ i, DefFun k (Gs i)) →
      DefRel k fun env => R (fappend (fun j => env (idx j)) (fun i => Gs i env))
  | 0, r, k, R, Gs, idx, hR, _ => by
    have h := DefRel.reIndex hR idx
    refine DefRel.congr h fun env => ?_
    have heqv : (fun j : Fin (r + 0) => env (idx j)) =
        fappend (fun j => env (idx j)) (fun i => Gs i env) := by
      funext j
      exact (fappend_lt (fun j => env (idx j)) (fun i => Gs i env) j.isLt).symm
    rw [heqv]
  | m + 1, r, k, R, Gs, idx, hR, hGs => by
    let idx' : Fin (r + 1) → Fin (k + 1) := fun j =>
      if hlt : j.val < r then (idx ⟨j.val, hlt⟩).succ
      else 0
    let R' : (Fin ((r + 1) + m) → V) → Prop := fun w =>
      R fun i => w ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add r m).symm⟩
    have hR' : DefRel ((r + 1) + m) R' :=
      DefRel.reIndex hR fun i => ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add r m).symm⟩
    have hGs' : ∀ i : Fin m, DefFun (k + 1) fun w => Gs i.succ (ftail w) :=
      fun i => DefFun.weaken (hGs i.succ)
    have hIH := defRel_comp_aux m (r := r + 1) (k := k + 1) (R := R')
      (Gs := fun i w => Gs i.succ (ftail w)) (idx := idx') hR' hGs'
    have hstep := DefRel.exists_ ((hGs 0).and hIH)
    refine DefRel.congr hstep fun env => ?_
    have heqv : ∀ (y : V) (hy : y = Gs 0 env),
        (fun i : Fin (r + (m + 1)) =>
          (fappend (fun j => fcons y env (idx' j))
            (fun l => Gs l.succ env))
            ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add r m).symm⟩) =
        fappend (fun j => env (idx j)) (fun i => Gs i env) := by
      intro y hy
      funext i
      by_cases hlt : i.val < r
      · have hlt' : (⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add r m).symm⟩ :
            Fin ((r + 1) + m)).val < r + 1 := by dsimp; omega
        rw [fappend_lt (fun j => fcons y env (idx' j)) (fun l => Gs l.succ env) hlt']
        rw [fappend_lt (fun j => env (idx j)) (fun i => Gs i env) hlt]
        simp only [idx', hlt, ↓reduceDIte, fcons_succ]
      · have hle : r ≤ i.val := Nat.le_of_not_lt hlt
        rw [fappend_ge (fun j => env (idx j)) (fun i => Gs i env) hle]
        by_cases heq : i.val = r
        · have hlt' : (⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add r m).symm⟩ :
              Fin ((r + 1) + m)).val < r + 1 := by dsimp; omega
          rw [fappend_lt (fun j => fcons y env (idx' j)) (fun l => Gs l.succ env) hlt']
          have h0 : (⟨i.val - r, Nat.sub_lt_left_of_lt_add hle i.isLt⟩ : Fin (m + 1)) = 0 := by
            apply Fin.ext; dsimp; omega
          rw [h0]
          simp only [idx', heq, Nat.lt_irrefl, ↓reduceDIte, fcons_zero]
          exact hy
        · have hle' : r + 1 ≤ (⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add r m).symm⟩ :
              Fin ((r + 1) + m)).val := by dsimp; omega
          rw [fappend_ge (fun j => fcons y env (idx' j)) (fun l => Gs l.succ env) hle']
          have hsub : (⟨i.val - r, Nat.sub_lt_left_of_lt_add hle i.isLt⟩ : Fin (m + 1)) =
              (⟨i.val - (r + 1), Nat.sub_lt_left_of_lt_add hle'
                (Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add r m).symm)⟩ : Fin m).succ := by
            apply Fin.ext
            dsimp
            omega
          rw [hsub]
    constructor
    · rintro ⟨y, hy, hRy⟩
      change R (fun i =>
        (fappend (fun j => fcons y env (idx' j)) (fun l => Gs l.succ env))
          ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add r m).symm⟩) at hRy
      rwa [heqv y hy] at hRy
    · intro h
      refine ⟨Gs 0 env, rfl, ?_⟩
      change R (fun i =>
        (fappend (fun j => fcons (Gs 0 env) env (idx' j)) (fun l => Gs l.succ env))
          ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add r m).symm⟩)
      rwa [heqv (Gs 0 env) rfl]

namespace DefRel

theorem comp {m k : Nat} {R : (Fin m → V) → Prop}
    {Gs : Fin m → (Fin k → V) → V} (hR : DefRel m R)
    (hGs : ∀ i, DefFun k (Gs i)) :
    DefRel k fun env => R (fun i => Gs i env) := by
  have h := defRel_comp_aux m (r := 0) (k := k)
    (R := fun w : Fin (0 + m) → V => R fun i => w ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add m).symm⟩)
    (Gs := Gs) (idx := Fin.elim0)
    (reIndex hR fun i => ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add m).symm⟩) hGs
  refine h.congr fun env => ?_
  have heqv : (fun i : Fin m =>
      (fappend (fun j : Fin 0 => env (Fin.elim0 j)) (fun i => Gs i env))
        ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add m).symm⟩) =
      fun i => Gs i env := by
    funext i
    have hge : 0 ≤ (⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add m).symm⟩ : Fin (0 + m)).val :=
      Nat.zero_le _
    rw [fappend_ge (fun j : Fin 0 => env (Fin.elim0 j)) (fun i => Gs i env) hge]
    congr 1
  rw [heqv]

end DefRel

namespace DefFun

theorem comp {m k : Nat} {F : (Fin m → V) → V}
    {Gs : Fin m → (Fin k → V) → V} (hF : DefFun m F)
    (hGs : ∀ i, DefFun k (Gs i)) :
    DefFun k fun env => F (fun i => Gs i env) := by
  let Hs : Fin (m + 1) → (Fin (k + 1) → V) → V
    | ⟨0, _⟩ => fun w => w 0
    | ⟨i + 1, h⟩ => fun w => Gs ⟨i, Nat.lt_of_succ_lt_succ h⟩ (ftail w)
  have hHs : ∀ j : Fin (m + 1), DefFun (k + 1) (Hs j) := by
    rintro ⟨j, hj⟩
    cases j with
    | zero => exact proj 0
    | succ j => exact weaken (hGs ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
  have h := DefRel.comp hF hHs
  refine DefRel.congr h fun w => ?_
  have hft : (fun i : Fin m => Hs i.succ w) = fun i => Gs i (ftail w) := rfl
  change (Hs 0 w = F (fun i => Hs i.succ w)) ↔ (w 0 = F (fun i => Gs i (ftail w)))
  rw [hft]
  rfl

theorem comp1 {k : Nat} {f : V → V} {A : (Fin k → V) → V}
    (hf : DefFun 1 fun v => f (v 0)) (hA : DefFun k A) :
    DefFun k fun env => f (A env) :=
  (hf.comp (fun _ => hA)).congr fun _ => rfl

theorem comp2 {k : Nat} {f : V → V → V} {A B : (Fin k → V) → V}
    (hf : DefFun 2 fun v => f (v 0) (v 1)) (hA : DefFun k A) (hB : DefFun k B) :
    DefFun k fun env => f (A env) (B env) := by
  let Gs : Fin 2 → (Fin k → V) → V
    | ⟨0, _⟩ => A
    | ⟨1, _⟩ => B
  have hGs : ∀ i : Fin 2, DefFun k (Gs i) := by
    rintro ⟨i, hi⟩
    match i with
    | 0 => exact hA
    | 1 => exact hB
  exact (hf.comp hGs).congr fun _ => rfl

theorem comp3 {k : Nat} {f : V → V → V → V} {A B C : (Fin k → V) → V}
    (hf : DefFun 3 fun v => f (v 0) (v 1) (v 2))
    (hA : DefFun k A) (hB : DefFun k B) (hC : DefFun k C) :
    DefFun k fun env => f (A env) (B env) (C env) := by
  let Gs : Fin 3 → (Fin k → V) → V
    | ⟨0, _⟩ => A
    | ⟨1, _⟩ => B
    | ⟨2, _⟩ => C
  have hGs : ∀ i : Fin 3, DefFun k (Gs i) := by
    rintro ⟨i, hi⟩
    match i with
    | 0 => exact hA
    | 1 => exact hB
    | 2 => exact hC
  exact (hf.comp hGs).congr fun _ => rfl

theorem const {k : Nat} (c : V) : DefFun k fun _ => c := by
  refine ⟨1, Formula.eq 0 ⟨k + 1, Nat.lt_succ_self (k + 1)⟩, fun _ => c, fun env => ?_⟩
  simp only [Formula.eval_eq]
  have h0 : fappend env (fun _ : Fin 1 => c) 0 = env 0 := by
    rw [fappend_lt env (fun _ : Fin 1 => c) (Nat.zero_lt_succ k)]
    rfl
  have h1 : fappend env (fun _ : Fin 1 => c) ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ = c :=
    fappend_right env (fun _ : Fin 1 => c) 0
  rw [h0, h1]

open Classical in
theorem ite {k : Nat} {P : (Fin k → V) → Prop} {F G : (Fin k → V) → V}
    (hP : DefRel k P) (hF : DefFun k F) (hG : DefFun k G) :
    DefFun k fun env => if P env then F env else G env := by
  have hPw := hP.weaken
  have h1 := hPw.and hF
  have h2 := hPw.not.and hG
  refine (h1.or h2).congr fun v => ?_
  by_cases hp : P (ftail v)
  · simp [hp]
  · simp [hp]

theorem empty {k : Nat} : DefFun k fun _ => (SetTheory.empty (V := V)) :=
  const (SetTheory.empty (V := V))

end DefFun

/-! ### Atomic relations (`=`, `∈ˢ`, `⊆ˢ`) and primitive `DefFun`s -/

namespace DefRel

private theorem mem_base : DefRel (V := V) 2 fun v => v 0 ∈ˢ v 1 :=
  ⟨0, Formula.mem 0 1, Fin.elim0, fun _ => by simp⟩

private theorem eq_base : DefRel (V := V) 2 fun v => v 0 = v 1 :=
  ⟨0, Formula.eq 0 1, Fin.elim0, fun _ => by simp⟩

theorem mem_apply {k : Nat} {A B : (Fin k → V) → V}
    (hA : DefFun k A) (hB : DefFun k B) :
    DefRel k fun env => A env ∈ˢ B env := by
  let Gs : Fin 2 → (Fin k → V) → V
    | ⟨0, _⟩ => A
    | ⟨1, _⟩ => B
  have hGs : ∀ i : Fin 2, DefFun k (Gs i) := by
    rintro ⟨i, hi⟩
    match i with
    | 0 => exact hA
    | 1 => exact hB
  exact ((mem_base (V := V)).comp hGs).congr fun _ => Iff.rfl

theorem eq_apply {k : Nat} {A B : (Fin k → V) → V}
    (hA : DefFun k A) (hB : DefFun k B) :
    DefRel k fun env => A env = B env := by
  let Gs : Fin 2 → (Fin k → V) → V
    | ⟨0, _⟩ => A
    | ⟨1, _⟩ => B
  have hGs : ∀ i : Fin 2, DefFun k (Gs i) := by
    rintro ⟨i, hi⟩
    match i with
    | 0 => exact hA
    | 1 => exact hB
  exact ((eq_base (V := V)).comp hGs).congr fun _ => Iff.rfl

theorem ne_apply {k : Nat} {A B : (Fin k → V) → V}
    (hA : DefFun k A) (hB : DefFun k B) :
    DefRel k fun env => A env ≠ B env :=
  (eq_apply hA hB).not

theorem subset_apply {k : Nat} {A B : (Fin k → V) → V}
    (hA : DefFun k A) (hB : DefFun k B) :
    DefRel k fun env => A env ⊆ˢ B env :=
  forall_curry
    ((mem_apply (DefFun.proj 0) hA.weaken).imp (mem_apply (DefFun.proj 0) hB.weaken))

theorem bExists {k : Nat} {A : (Fin k → V) → V} {R : (Fin (k + 1) → V) → Prop}
    (hA : DefFun k A) (hR : DefRel (k + 1) R) :
    DefRel k fun env => ∃ x, x ∈ˢ A env ∧ R (fcons x env) :=
  (exists_ ((mem_apply (DefFun.proj 0) hA.weaken).and hR)).congr fun _ => Iff.rfl

theorem bExists_curry {k : Nat} {A : (Fin k → V) → V} {R : V → (Fin k → V) → Prop}
    (hA : DefFun k A) (hR : DefRel (k + 1) fun v => R (v 0) (ftail v)) :
    DefRel k fun env => ∃ x, x ∈ˢ A env ∧ R x env :=
  bExists hA hR

theorem bForall {k : Nat} {A : (Fin k → V) → V} {R : (Fin (k + 1) → V) → Prop}
    (hA : DefFun k A) (hR : DefRel (k + 1) R) :
    DefRel k fun env => ∀ x, x ∈ˢ A env → R (fcons x env) :=
  (forall_ ((mem_apply (DefFun.proj 0) hA.weaken).imp hR)).congr fun _ => Iff.rfl

theorem bForall_curry {k : Nat} {A : (Fin k → V) → V} {R : V → (Fin k → V) → Prop}
    (hA : DefFun k A) (hR : DefRel (k + 1) fun v => R (v 0) (ftail v)) :
    DefRel k fun env => ∀ x, x ∈ˢ A env → R x env :=
  bForall hA hR

theorem existsUnique {k : Nat} {R : (Fin (k + 1) → V) → Prop}
    (hR : DefRel (k + 1) R) :
    DefRel k fun env => ExistsUnique fun x => R (fcons x env) := by
  have hsub : DefRel (k + 2) fun v => R (fcons (v 0) (ftail (ftail v))) → v 0 = ftail v 0 := by
    have hre := hR.reIndex (fcons 0 (Fin.succ.comp Fin.succ))
    have hre' : DefRel (k + 2) fun v => R (fcons (v 0) (ftail (ftail v))) :=
      hre.congr fun v => by
        have heqv : (fun i => v (fcons 0 (Fin.succ.comp Fin.succ) i)) =
            fcons (v 0) (ftail (ftail v)) := by
          funext ⟨j, hj⟩
          cases j with
          | zero => rfl
          | succ j => rfl
        rw [heqv]
    exact hre'.imp (eq_apply (DefFun.proj 0) (DefFun.proj 1))
  have h1 : DefRel (k + 1) fun v =>
      R v ∧ ∀ y, R (fcons y (ftail v)) → y = v 0 :=
    hR.and (forall_curry hsub)
  exact (exists_ h1).congr fun env => Iff.rfl

theorem existsUnique_curry {k : Nat} {R : V → (Fin k → V) → Prop}
    (hR : DefRel (k + 1) fun v => R (v 0) (ftail v)) :
    DefRel k fun env => ExistsUnique fun x => R x env :=
  existsUnique hR

end DefRel

namespace DefFun

open Classical in
theorem uniqueChoice {k : Nat} {R : (Fin (k + 1) → V) → Prop}
    (hR : DefRel (k + 1) R) :
    DefFun k fun env =>
      if h : ExistsUnique fun y => R (fcons y env) then Classical.choose h else SetTheory.empty := by
  have hex := (DefRel.existsUnique hR).weaken
  have hpos := hex.and hR
  have hneg := hex.not.and (DefRel.eq_apply (proj 0) (DefFun.empty (V := V) (k := k + 1)))
  refine (hpos.or hneg).congr fun v => ?_
  dsimp only
  constructor
  · rintro (⟨he, hv⟩ | ⟨he, hv⟩)
    · rw [dite_eq_left he]
      exact (Classical.choose_spec he).2 (v 0) (by dsimp only; rwa [fcons_zero_ftail])
    · rw [dite_eq_right he]
      exact hv
  · intro hv
    by_cases he : ExistsUnique fun y => R (fcons y (ftail v))
    · rw [dite_eq_left he] at hv
      refine Or.inl ⟨he, ?_⟩
      have hspec := (Classical.choose_spec he).1
      rw [← hv, fcons_zero_ftail] at hspec
      exact hspec
    · rw [dite_eq_right he] at hv
      exact Or.inr ⟨he, hv⟩

open Classical in
theorem uniqueChoice_curry {k : Nat} {R : V → (Fin k → V) → Prop}
    (hR : DefRel (k + 1) fun v => R (v 0) (ftail v)) :
    DefFun k fun env =>
      if h : ExistsUnique fun y => R y env then Classical.choose h else SetTheory.empty :=
  uniqueChoice hR

private theorem upair_base : DefFun (V := V) 2 fun v => upair (v 0) (v 1) := by
  have h : DefRel (V := V) 3 fun v =>
      ∀ z, z ∈ˢ v 0 ↔ z = v 1 ∨ z = v 2 :=
    DefRel.forall_curry
      ((DefRel.mem_apply (proj 0) (proj 1)).iff
        ((DefRel.eq_apply (proj 0) (proj 2)).or (DefRel.eq_apply (proj 0) (proj 3))))
  refine h.congr fun v => ?_
  exact ⟨fun hz => ext fun z => (hz z).trans mem_upair.symm,
    fun heq z => by rw [heq, mem_upair]; rfl⟩

theorem upair_apply {k : Nat} {A B : (Fin k → V) → V}
    (hA : DefFun k A) (hB : DefFun k B) :
    DefFun k fun env => upair (A env) (B env) :=
  comp2 (upair_base (V := V)) hA hB

private theorem sUnion_base : DefFun (V := V) 1 fun v => sUnion (v 0) := by
  have h : DefRel (V := V) 2 fun v =>
      ∀ z, z ∈ˢ v 0 ↔ ∃ y, y ∈ˢ v 1 ∧ z ∈ˢ y :=
    DefRel.forall_curry
      ((DefRel.mem_apply (proj 0) (proj 1)).iff
        (DefRel.bExists_curry (proj 2) (DefRel.mem_apply (proj 1) (proj 0))))
  refine h.congr fun v => ?_
  exact ⟨fun hz => ext fun z => (hz z).trans mem_sUnion.symm,
    fun heq z => by rw [heq, mem_sUnion]; rfl⟩

theorem sUnion_apply {k : Nat} {A : (Fin k → V) → V} (hA : DefFun k A) :
    DefFun k fun env => sUnion (A env) :=
  comp1 (sUnion_base (V := V)) hA

private theorem power_base : DefFun (V := V) 1 fun v => power (v 0) := by
  have h : DefRel (V := V) 2 fun v =>
      ∀ z, z ∈ˢ v 0 ↔ z ⊆ˢ v 1 :=
    DefRel.forall_curry
      ((DefRel.mem_apply (proj 0) (proj 1)).iff
        (DefRel.subset_apply (proj 0) (proj 2)))
  refine h.congr fun v => ?_
  exact ⟨fun hz => ext fun z => (hz z).trans mem_power.symm,
    fun heq z => by rw [heq, mem_power]; rfl⟩

theorem power_apply {k : Nat} {A : (Fin k → V) → V} (hA : DefFun k A) :
    DefFun k fun env => power (A env) :=
  comp1 (power_base (V := V)) hA

theorem image_apply {k : Nat} {F : (Fin (k + 1) → V) → V} {A : (Fin k → V) → V}
    {h : ∀ env, HasImage (fun x => F (fcons x env)) (A env)}
    (hF : DefFun (k + 1) F) (hA : DefFun k A) :
    DefFun k fun env => image (fun x => F (fcons x env)) (A env) (h env) := by
  let reF : Fin (k + 1) → Fin (k + 3)
    | ⟨0, _⟩ => 0
    | ⟨i + 1, hi⟩ => ⟨i + 3, by omega⟩
  have hF' : DefFun (k + 3) fun w => F (fcons (w 0) (ftail (ftail (ftail w)))) :=
    (hF.reIndex reF).congr fun w => by
      congr 1
      funext ⟨j, hj⟩
      cases j with
      | zero => rfl
      | succ j => rfl
  have hrel : DefRel (k + 1) fun v =>
      ∀ z, z ∈ˢ v 0 ↔ ∃ x, x ∈ˢ A (ftail v) ∧ z = F (fcons x (ftail v)) :=
    DefRel.forall_curry
      ((DefRel.mem_apply (proj 0) (proj 1)).iff
        (DefRel.bExists_curry hA.weaken.weaken
          (DefRel.eq_apply (proj 1) hF')))
  refine hrel.congr fun v => ?_
  exact ⟨fun hz => ext fun z => (hz z).trans mem_image.symm,
    fun heq z => by rw [heq, mem_image]⟩

theorem image_apply_curry {k : Nat} {F : V → (Fin k → V) → V} {A : (Fin k → V) → V}
    {h : ∀ env, HasImage (fun x => F x env) (A env)}
    (hF : DefFun (k + 1) fun v => F (v 0) (ftail v)) (hA : DefFun k A) :
    DefFun k fun env => image (fun x => F x env) (A env) (h env) :=
  image_apply (F := fun v => F (v 0) (ftail v)) hF hA

end DefFun

/-! ### Replacement bridge: `DefFunOn` → `HasImage` -/

/-- Any globally `DefFun1` function has a replacement image on every set `a`. -/
theorem hasImage_of_defFun1 {f : V → V}
    (hf : DefFun 1 fun v => f (v 0)) (a : V) : HasImage f a := by
  obtain ⟨p, φ, params, hφ⟩ := hf
  have huniq : ∀ x, x ∈ˢ a →
      ExistsUnique fun y =>
        φ.eval (Mem (V := V)) (fappend (fcons y (fcons x Fin.elim0)) params) := by
    intro x _
    refine ⟨f x, (hφ (fcons (f x) (fcons x Fin.elim0))).mp rfl, fun y hy => ?_⟩
    exact (hφ (fcons y (fcons x Fin.elim0))).mpr hy
  obtain ⟨b, hb⟩ := SetTheory.replacement φ params a huniq
  refine ⟨b, fun z => (hb z).trans ?_⟩
  exact exists_congr fun x => and_congr_right fun _ => (hφ (fcons z (fcons x Fin.elim0))).symm

/-- Any function definable *on* `a` has a replacement image on `a`. -/
theorem hasImage_of_def {a : V} {f : V → V} (hf : DefFunOn a f) : HasImage f a := by
  obtain ⟨g, hg, heq⟩ := hf
  exact (hasImage_of_defFun1 hg a).congr fun x hx => (heq x hx).symm

/-! ### Lightweight first-order definability tactic (`fo_def`) -/

/-- Pure-core tactic macro (zero `import Lean`) discharging `DefRel`,
`DefFun`, `DefPredOn`, `DefFunOn`, and `HasImage` obligations by
backward chaining over the pointwise combinators.  Extra domain-specific
lemmas may be passed as `fo_def [lemma1, lemma2]`. -/
syntax "fo_def" (" [" Lean.Parser.Tactic.SolveByElim.arg,* "]")? : tactic

macro_rules
  | `(tactic| fo_def) =>
    `(tactic|
      solve_by_elim -exfalso (maxDepth := 24) (transparency := .reducible)
        [ hasImage_empty
        , hasImage_of_defFun1
        , hasImage_of_def
        , DefFunOn.of_defFun1
        , DefPredOn.of_defPred
        , DefRel.true
        , DefRel.false
        , DefRel.not
        , DefRel.and
        , DefRel.or
        , DefRel.imp
        , DefRel.iff
        , DefRel.bExists_curry
        , DefRel.bForall_curry
        , DefRel.exists_curry
        , DefRel.forall_curry
        , DefRel.existsUnique_curry
        , DefRel.mem_apply
        , DefRel.eq_apply
        , DefRel.ne_apply
        , DefRel.subset_apply
        , DefFun.proj
        , DefFun.empty
        , DefFun.const
        , DefFun.ite
        , DefFun.uniqueChoice_curry
        , DefFun.upair_apply
        , DefFun.sUnion_apply
        , DefFun.power_apply
        , DefFun.image_apply_curry
        , DefRel.constProp
        ])
  | `(tactic| fo_def [$rs,*]) => do
    let base ← `(Lean.Parser.Tactic.SolveByElim.args|
      [ hasImage_empty
      , hasImage_of_defFun1
      , hasImage_of_def
      , DefFunOn.of_defFun1
      , DefPredOn.of_defPred
      , DefRel.true
      , DefRel.false
      , DefRel.not
      , DefRel.and
      , DefRel.or
      , DefRel.imp
      , DefRel.iff
      , DefRel.bExists_curry
      , DefRel.bForall_curry
      , DefRel.exists_curry
      , DefRel.forall_curry
      , DefRel.existsUnique_curry
      , DefRel.mem_apply
      , DefRel.eq_apply
      , DefRel.ne_apply
      , DefRel.subset_apply
      , DefFun.proj
      , DefFun.empty
      , DefFun.const
      , DefFun.ite
      , DefFun.uniqueChoice_curry
      , DefFun.upair_apply
      , DefFun.sUnion_apply
      , DefFun.power_apply
      , DefFun.image_apply_curry
      , DefRel.constProp
      ])
    let baseElems := match base with
      | `(Lean.Parser.Tactic.SolveByElim.args| [$as,*]) => as.getElems
      | _ => #[]
    let all := Lean.Syntax.TSepArray.ofElems (rs.getElems ++ baseElems)
    `(tactic| solve_by_elim -exfalso (maxDepth := 24) (transparency := .reducible) [$all,*])

end ConLeche.SetTheory
