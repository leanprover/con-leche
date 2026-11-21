module

public import ConLeche.Model.Env.Laws
public import ConLeche.Verify.Denote.Install

public section

/-!
# Leaves alike in the interpretation

Two valuations of the constants whose leaves interpret alike, at every assignment and every
environment of the bound variables (`LeavesAlike`), read every expression alike: where one
denotation succeeds the other does too, and the two terms interpret alike
(`denote_leavesAlike`).  `denote` never looks inside a leaf, and `interp` is compositional.

The laws a model's leaves are held to at the stored-term reading (`NatOps`, `DivMod`,
`ReduceOps`) are statements about interpretations, so they pass from one valuation to an alike
one (`NatOps.of_alike`, `DivMod.of_alike`, `ReduceOps.of_alike`).  The install step uses this
where a constant whose type reads as a truth value takes the canonical proof as its leaf in
place of its value's reading, which interprets as the point too.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]

variable (V) in
/-- **Two valuations whose leaves interpret alike.** -/
@[expose] def LeavesAlike (a a' : Name → (Name → Nat) → Term) : Prop :=
  ∀ n ψ (ρ : Nat → V), interp V ρ (a n ψ) = interp V ρ (a' n ψ)

theorem natLitT_alike {z z' s s' : Term} (hz : ∀ ρ : Nat → V, interp V ρ z = interp V ρ z')
    (hs : ∀ ρ : Nat → V, interp V ρ s = interp V ρ s') :
    ∀ (k : Nat) (ρ : Nat → V), interp V ρ (natLitT z s k) = interp V ρ (natLitT z' s' k)
  | 0, ρ => hz ρ
  | k + 1, ρ => by simp only [natLitT, interp_app, hs ρ, natLitT_alike hz hs k ρ]

theorem charListT_alike {nl nl' cs cs' on on' z z' s s' : Term}
    (hnl : ∀ ρ : Nat → V, interp V ρ nl = interp V ρ nl')
    (hcs : ∀ ρ : Nat → V, interp V ρ cs = interp V ρ cs')
    (hon : ∀ ρ : Nat → V, interp V ρ on = interp V ρ on')
    (hz : ∀ ρ : Nat → V, interp V ρ z = interp V ρ z')
    (hs : ∀ ρ : Nat → V, interp V ρ s = interp V ρ s') :
    ∀ (l : List Char) (ρ : Nat → V),
      interp V ρ (charListT nl cs on z s l) = interp V ρ (charListT nl' cs' on' z' s' l)
  | [], ρ => hnl ρ
  | c :: l, ρ => by
    simp only [charListT, interp_app, hcs ρ, hon ρ, natLitT_alike hz hs _ ρ,
      charListT_alike hnl hcs hon hz hs l ρ]

theorem projNV_alike : ∀ (i : Nat) {e e' : Term} (_ : ∀ ρ : Nat → V, interp V ρ e = interp V ρ e')
    (ρ : Nat → V), interp V ρ (projNV i e) = interp V ρ (projNV i e')
  | 0, _, _, h, ρ => by simp only [projNV, interp_fst, h ρ]
  | i + 1, _, _, h, ρ => projNV_alike i (fun ρ => by simp only [interp_snd, h ρ]) ρ

/-- **Alike leaves read every expression alike.** -/
theorem denote_leavesAlike {a a' : Name → (Name → Nat) → Term} (h : LeavesAlike V a a')
    (env : Env) (φ : Name → Nat) (d : Nat) (e : Expr) {t : Term}
    (ht : denote a env φ d e = some t) :
    ∃ t', denote a' env φ d e = some t' ∧ ∀ ρ : Nat → V, interp V ρ t = interp V ρ t' := by
  induction d, e using denote.induct env generalizing t with
  | case1 d u =>
    simp only [denote] at ht ⊢
    exact ⟨t, ht, fun _ => rfl⟩
  | case2 d idx ty =>
    simp only [denote] at ht ⊢
    exact ⟨t, ht, fun _ => rfl⟩
  | case3 d n us ci hci hl =>
    simp only [denote, hci, hl, ↓reduceIte] at ht ⊢
    obtain rfl := Option.some.inj ht
    exact ⟨_, rfl, fun ρ => h _ _ ρ⟩
  | case4 d n us ci hci hl =>
    simp only [denote, hci, hl, ↓reduceIte] at ht
    exact nomatch ht
  | case5 d n us hci =>
    simp only [denote, hci] at ht
    exact nomatch ht
  | case6 d ty body ih1 ih2 =>
    simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ht ⊢
    obtain ⟨A, hA, B, hB, rfl⟩ := ht
    obtain ⟨A', hA', eA⟩ := ih1 hA
    obtain ⟨B', hB', eB⟩ := ih2 hB
    exact ⟨_, ⟨A', hA', B', hB', rfl⟩, fun ρ => by
      simp only [interp_pi, eA ρ]
      exact congrArg _ (funext fun x => eB _)⟩
  | case7 d ty body ih1 ih2 =>
    simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ht ⊢
    obtain ⟨A, hA, B, hB, rfl⟩ := ht
    obtain ⟨A', hA', eA⟩ := ih1 hA
    obtain ⟨B', hB', eB⟩ := ih2 hB
    exact ⟨_, ⟨A', hA', B', hB', rfl⟩, fun ρ => by
      simp only [interp_lam, eA ρ]
      exact congrArg _ (funext fun x => eB _)⟩
  | case8 d f x ih1 ih2 =>
    simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ht ⊢
    obtain ⟨F, hF, X, hX, rfl⟩ := ht
    obtain ⟨F', hF', eF⟩ := ih1 hF
    obtain ⟨X', hX', eX⟩ := ih2 hX
    exact ⟨_, ⟨F', hF', X', hX', rfl⟩, fun ρ => by simp only [interp_app, eF ρ, eX ρ]⟩
  | case9 d ty v b ih1 ih2 ih3 =>
    simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ht ⊢
    obtain ⟨T, hT, W, hW, B, hB, rfl⟩ := ht
    obtain ⟨T', hT', -⟩ := ih1 hT
    obtain ⟨W', hW', eW⟩ := ih2 hW
    obtain ⟨B', hB', eB⟩ := ih3 hB
    exact ⟨_, ⟨T', hT', W', hW', B', hB', rfl⟩, fun ρ => by
      simp only [interp_letE, eW ρ]
      exact eB _⟩
  | case10 d sn i x ih =>
    simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at ht ⊢
    obtain ⟨X, hX, hp⟩ := ht
    obtain ⟨X', hX', eX⟩ := ih hX
    split at hp
    · next hf =>
      obtain rfl := Option.some.inj hp
      exact ⟨_, ⟨X', hX', rfl⟩, projNV_alike _ eX⟩
    · exact nomatch hp
  | case11 d k hs =>
    simp only [denote, hs, ↓reduceIte] at ht ⊢
    obtain rfl := Option.some.inj ht
    exact ⟨_, rfl, natLitT_alike (h _ _) (h _ _) _⟩
  | case12 d k hs =>
    simp only [denote, hs] at ht
    exact nomatch ht
  | case13 d str hs =>
    simp only [denote, hs, ↓reduceIte] at ht ⊢
    obtain rfl := Option.some.inj ht
    refine ⟨_, rfl, fun ρ => ?_⟩
    simp only [interp_app, h _ _ ρ]
    exact congrArg _ (charListT_alike (fun ρ => by simp only [interp_app, h _ _ ρ])
      (fun ρ => by simp only [interp_app, h _ _ ρ]) (h _ _) (h _ _) (h _ _) _ ρ)
  | case14 d str hs =>
    simp only [denote, hs] at ht
    exact nomatch ht
  | case15 d x h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    cases x with
    | lit l => cases l <;> simp_all
    | _ => first
      | (exfalso; simp_all)
      | (simp only [denote] at ht; exact nomatch ht)

/-- One leaf replaced by one that interprets alike. -/
theorem leavesAlike_acvalWith {a : Name → (Name → Nat) → Term} {n : Name}
    {A B : (Name → Nat) → Term} (h : ∀ ψ (ρ : Nat → V), interp V ρ (A ψ) = interp V ρ (B ψ)) :
    LeavesAlike V (acvalWith a n A) (acvalWith a n B) := by
  intro c ψ ρ
  unfold acvalWith
  split
  · exact h ψ ρ
  · rfl

/-! ## The laws, across alike valuations -/

section Laws
variable {env : Env} {m m' : EnvModel V env}

theorem NatOps.of_alike (h : LeavesAlike V m.acval m'.acval) {φ : Name → Nat}
    (H : NatOps m φ) : NatOps m' φ := by
  intro c hc ci hf
  obtain ⟨hg, hd, heqs⟩ := H c hc ci hf
  refine ⟨hg, hd, fun eq heq => ?_⟩
  obtain ⟨L, R, hL, hR, hLR⟩ := heqs eq heq
  obtain ⟨L', hL', eL⟩ := denote_leavesAlike h env φ 2 eq.1 hL
  obtain ⟨R', hR', eR⟩ := denote_leavesAlike h env φ 2 eq.2 hR
  refine ⟨L', R', hL', hR', fun ρ x y hx hy => ?_⟩
  rw [← h] at hx hy
  rw [← eL, ← eR]
  exact hLR ρ x y hx hy

theorem DivMod.of_alike (h : LeavesAlike V m.acval m'.acval) {φ : Name → Nat}
    (H : DivMod m φ) : DivMod m' φ := by
  intro c hc ci hf
  obtain ⟨hg, hd, hcl⟩ := H c hc ci hf
  refine ⟨hg, hd, fun ρ x y hx hy => ?_⟩
  rw [← h] at hx hy
  have he : (fun n => interp V ρ (m'.acval n φ)) = fun n => interp V ρ (m.acval n φ) :=
    funext fun n => (h n φ ρ).symm
  rw [he]
  exact hcl ρ x y hx hy

theorem ReduceOps.of_alike (h : LeavesAlike V m.acval m'.acval) (H : ReduceOps m) :
    ReduceOps m' := by
  intro c hc cv hf hp
  obtain ⟨hs, hid⟩ := H c hc cv hf hp
  refine ⟨hs, fun ψ ρ x hx => ?_⟩
  rw [← h] at hx ⊢
  exact hid ψ ρ x hx

end Laws

end ConLeche.Model
