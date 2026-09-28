module

public import ConLeche.Model.Inductives.HoleKit
import ConLeche.Model.Inductives.ErasureKit
public import ConLeche.Semantics.Inductives.HoleAcc
import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Verify.Denote.Shift

public section

/-!
# The hole kit for accessibility

The prog-free vocabulary of the closure witness (W): the non-hole
positions an output mentions (`MentNH`, `MentP`) and that a hole-free
domain reads only those (`noBVar_not_mentNH`); congruence of the
admissible-item predicate (`RichOn.congrQ`, `AccOn.congrQ`); a domain
carries its values to a larger related frame (`transfer_of_constOn`,
`transfer_of_accOn`); a telescope's values are small (`TeleSmall`).
Nothing here mentions a derivation, a frame program or a node: the class
check's accessibility facts (`ClassFieldAcc`) and the old positivity
proof (`NestPosAcc`) both build on it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestKey NestHole)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The positions an output mentions -/

/-- **The non-hole positions an output mentions** at depth `d`: position
`i` is the variable `d - 1 - i`, mentioned by `nf`, and not a hole. -/
@[expose] def MentNH (lo hi d : Nat) (nf : Expr) : Nat → Prop :=
  fun i => i < d ∧ nf.nestOcc [] (d - 1 - i) (d - i) = true ∧ ¬ holeP d lo hi i

omit [SetTheory V] in
theorem noBVar_exists' {α : Type} :
    ∀ {e : AnnotTerm} {P : α → Nat → Prop}, (∀ a, NoBVar (P a) e) →
      NoBVar (fun i => ∃ a, P a i) e := by
  intro e
  induction e with
  | bvar i => intro P h; exact fun ⟨a, ha⟩ => h a ha
  | sort u => intros; trivial
  | const c us => intros; trivial
  | prf => intros; trivial
  | app f a ihf iha => intro P h; exact ⟨ihf fun a => (h a).1, iha fun a => (h a).2⟩
  | eqE a b iha ihb => intro P h; exact ⟨iha fun a => (h a).1, ihb fun a => (h a).2⟩
  | fst e ihe => intro P h; exact ihe fun a => h a
  | snd e ihe => intro P h; exact ihe fun a => h a
  | lam v A b ihA ihb =>
    intro P h
    refine ⟨ihA fun a => (h a).1, NoBVar.mono (fun i hi => ?_)
      (ihb (P := fun a => shiftP (P a)) fun a => (h a).2)⟩
    cases i with
    | zero => exact hi.elim
    | succ i => exact hi
  | pi u v A B ihA ihB =>
    intro P h
    refine ⟨ihA fun a => (h a).1, NoBVar.mono (fun i hi => ?_)
      (ihB (P := fun a => shiftP (P a)) fun a => (h a).2)⟩
    cases i with
    | zero => exact hi.elim
    | succ i => exact hi

/-- **A hole-free domain inside the output reads only mentioned non-hole
positions.** -/
theorem noBVar_not_mentNH {lo hi d : Nat} {a nf : Expr} {ta : AnnotTerm}
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hholes : NoBVar (holeP d lo hi) ta)
    (hsub : ∀ s, s < d → nf.nestOcc [] s (s + 1) = false → a.nestOcc [] s (s + 1) = false)
    (hta : denoteMeta m.acval env φ d a = some ta) :
    NoBVar (fun i => ¬ MentNH lo hi d nf i) ta := by
  have hbb := denote_bvarsBelow m.cval_closedL d a hws hb (denoteMeta_erase m.acval_erase d a hta)
  have hbelow : NoBVar (fun i => d ≤ i) ta := NoBVar_of_bvarsBelow hbb fun _ h => h
  have hnone : NoBVar (fun _ => False) ta := NoBVar_of_bvarsBelow hbb fun _ h => h.elim
  have hun : NoBVar (fun i => ∃ s, s < d ∧ nf.nestOcc [] s (s + 1) = false ∧ holeP d s (s + 1) i)
      ta := by
    refine noBVar_exists' (P := fun s i => s < d ∧ nf.nestOcc [] s (s + 1) = false ∧
      holeP d s (s + 1) i) fun s => ?_
    by_cases hs : s < d ∧ nf.nestOcc [] s (s + 1) = false
    · exact NoBVar.mono (fun i hn => hn.2.2)
        (denoteMeta_noBVar_of_nestOcc (m := m) (names := []) (lo := s) (hi := s + 1) d a hws
          (by omega) (hsub s hs.1 hs.2) hta)
    · exact NoBVar.mono (fun i hn => absurd ⟨hn.1, hn.2.1⟩ hs) hnone
  have hall := noBVar_exists' (α := Fin 3) (P := fun k i => match k with
    | 0 => d ≤ i
    | 1 => ∃ s, s < d ∧ nf.nestOcc [] s (s + 1) = false ∧ holeP d s (s + 1) i
    | 2 => holeP d lo hi i) (e := ta) fun k => by
      match k with
      | 0 => exact hbelow
      | 1 => exact hun
      | 2 => exact hholes
  refine NoBVar.mono (fun i hn => ?_) hall
  by_cases hid : i < d
  · by_cases hh : holeP d lo hi i
    · exact ⟨2, hh⟩
    · refine ⟨1, d - 1 - i, by omega, ?_, ⟨hid, by omega, by omega⟩⟩
      cases hm : nf.nestOcc [] (d - 1 - i) (d - 1 - i + 1)
      · rfl
      · exact absurd ⟨hid, by rw [show d - i = d - 1 - i + 1 by omega]; exact hm, hh⟩ hn
  · exact ⟨0, by omega⟩

/-- The body's output, one binder down, mentions no more than the Π's. -/
theorem mentNH_body {lo hi dep : Nat} {a nb : Expr} {bm : ConLeche.BinderMeta} :
    ∀ i, MentNH lo hi (dep + 1) nb i → liftM (MentNH lo hi dep (.forallE a (nb.abstract1 dep 0) bm)) i
  | 0, _ => trivial
  | i + 1, ⟨hlt, hm, hh⟩ => by
    refine ⟨by omega, ?_, fun h => hh (holeP_succ (i + 1) h)⟩
    simp only [ConLeche.Expr.nestOcc, Bool.or_eq_true]
    refine Or.inr ?_
    rw [nestOcc_abstract1 (by omega) nb 0]
    rw [show dep + 1 - 1 - (i + 1) = dep - 1 - i by omega,
      show dep + 1 - (i + 1) = dep - i by omega] at hm
    exact hm

/-- **The positions a bound may read**: the non-hole positions the output
mentions, or a PARAMETER position (a container's
bound reads the enclosing parameters through its key's parameters, which
may be mentioned only inside an annotation). -/
@[expose] def MentP (lo hi d : Nat) (nf : Expr) : Nat → Prop :=
  fun i => MentNH lo hi d nf i ∨ (i < d ∧ d - 1 - i < lo)

theorem mentP_body {lo hi dep : Nat} {a nb : Expr} {bm : ConLeche.BinderMeta} :
    ∀ i, MentP lo hi (dep + 1) nb i → liftM (MentP lo hi dep (.forallE a (nb.abstract1 dep 0) bm)) i
  | 0, _ => trivial
  | i + 1, Or.inl h => Or.inl (mentNH_body (i + 1) h)
  | i + 1, Or.inr ⟨hlt, hp⟩ => Or.inr ⟨by omega, by omega⟩

omit [SetTheory V] in
theorem InvOn.mono {M M' : Nat → Prop} {A : (Nat → V) → V} (h : InvOn M A) (hM : ∀ i, M i → M' i) :
    InvOn M' A :=
  fun ρ ρ' hag => h ρ ρ' fun i hi => hag i (hM i hi)

theorem holdsLe_congrQ {Q Q' : Nat → Nat → Prop} (hQ : ∀ i n, Q i n ↔ Q' i n) {ρ ρ' : Nat → V}
    (h : HoldsLe Q ρ ρ') : HoldsLe Q' ρ ρ' :=
  fun o ho => h o ((hQ _ _).mpr ho)

theorem RichOn.congrQ {Q Q' : Nat → Nat → Prop} (hQ : ∀ i n, Q i n ↔ Q' i n) {R : FrameRel V}
    (h : RichOn Q R) : RichOn Q' R := by
  intro ρ ρ₀ hR i vs hq hpt
  obtain ⟨ρ'', hR'', hle, hz⟩ := h ρ ρ₀ hR i vs ((hQ _ _).mpr hq) hpt
  exact ⟨ρ'', hR'', holdsLe_congrQ hQ hle, hz⟩

theorem AccOn.congrQ {w : Nat} {Q Q' : Nat → Nat → Prop} (hQ : ∀ i n, Q i n ↔ Q' i n)
    {R : FrameRel V} {A : (Nat → V) → V} {a : AnnotTerm} (h : AccOn w Q R A a) :
    AccOn w Q' R A a := by
  intro ρ ρ₀ hR x hxw hx
  obtain ⟨B, g, hB, hg, hs⟩ := h ρ ρ₀ hR x hxw hx
  exact ⟨B, g, hB, fun b hb => ⟨(hQ _ _).mp (hg b hb).1, (hg b hb).2⟩, hs⟩

/-- A hole-free domain carries its values. -/
theorem transfer_of_constOn {R : FrameRel V} {Q : Nat → Nat → Prop} {ta : AnnotTerm}
    (hA : ConstOn R ta) :
    ∀ ρ ρ₀ ρ'', R ρ ρ₀ → R ρ ρ'' → HoldsLe Q ρ ρ'' →
      ∀ x, x ∈ˢ interp V ρ ta → x ∈ˢ interp V ρ₀ ta → x ∈ˢ interp V ρ'' ta :=
  fun ρ _ ρ'' _ hR'' _ _ hx _ => hA ρ ρ'' hR'' ▸ hx

/-- An accessible domain carries its small values. -/
theorem transfer_of_accOn {w : Nat} {R : FrameRel V} {Q : Nat → Nat → Prop} {ta : AnnotTerm}
    {Af : (Nat → V) → V} (hA : AccOn w Q R Af ta)
    (hsm : ∀ ρ ρ₀, R ρ ρ₀ → ∀ x, x ∈ˢ interp V ρ ta → x ∈ˢ (univ w : V)) :
    ∀ ρ ρ₀ ρ'', R ρ ρ₀ → R ρ ρ'' → HoldsLe Q ρ ρ'' →
      ∀ x, x ∈ˢ interp V ρ ta → x ∈ˢ interp V ρ₀ ta → x ∈ˢ interp V ρ'' ta :=
  fun ρ ρ₀ _ hR₀ hR'' hle x hx _ => hA.transfer hR₀ hR'' hle (hsm ρ ρ₀ hR₀ x hx) hx

/-- **The first `n` Π-domains' values are small** at every frame of the
relation, each under the earlier ones. -/
@[expose] def TeleSmall (w : Nat) : Nat → FrameRel V → AnnotTerm → Prop
  | 0, _, _ => True
  | n + 1, R, .pi _ _ A B =>
    (∀ ρ ρ₀, R ρ ρ₀ → ∀ x, x ∈ˢ interp V ρ A → x ∈ˢ (univ w : V)) ∧
      TeleSmall w n (R.underBoth A) B
  | _ + 1, _, _ => True

end ConLeche.Model
