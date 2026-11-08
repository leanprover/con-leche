module

public import InLeanProof.CertArm
/- `ConstantInfo.name`/`levelParams`/`type` are read as projections of `toConstantVal`. -/
import all Lean.Declaration
/- `FEnv.push` (core's private add, behind `InLean/Push.lean`) is read to find the pushed definition. -/
import all InLean.Push

/-!
# CertArm: the pin-certified `Nat` operations (task #451, lane CertArm)

InLean's `checkDivModPin` (`InLean/CheckerC.lean`: `checkDivModPinLoop`,
`checkDivModPinAt`, `checkTypePins`, `checkDivModCerts`) against master's
(`ConLeche/Kernel/Checker.lean`), at `loadedPins`.

* **Resolution** (`constsResolve_tr`): InLean's `constsResolve` is master's
  `Expr.constsResolve` on the reading.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-! ## Resolution -/

/-- The constants' pick of `EO.usedConstants`. -/
@[expose] def cPick : Expr → Option Name
  | .const n _ => some n
  | _ => none

/-- The unresolved-node test of `InLean.constsResolve`. -/
@[expose] def unresI (fe : InLean.FEnv) : Expr → Bool
  | .proj s _ _ => (fe.find? s).isNone
  | .lit (.natVal _) => !natLitStoredF fe
  | .lit (.strVal _) => !strLitStoredF fe
  | _ => false

theorem cPick_compound : ∀ x, EO.isCompound x = true → cPick x = none := by
  intro x hx; cases x <;> first | rfl | simp [EO.isCompound] at hx

section dedup
attribute [local instance 3000] instBEqExprExact

/-- The deduplicating fold keeps every name it reads. -/
theorem dedup_mem (l : List Name) :
    ∀ (s : Std.HashSet Name) (acc : Array Name), (∀ x, s.contains x = true → x ∈ acc) →
      (∀ x, x ∈ acc → x ∈ (l.foldl (fun (sa : Std.HashSet Name × Array Name) n => match sa with
        | (s, acc) => if s.contains n = true then (s, acc) else (s.insert n, acc.push n)) (s, acc)).2) ∧
      (∀ x, x ∈ l → x ∈ (l.foldl (fun (sa : Std.HashSet Name × Array Name) n => match sa with
        | (s, acc) => if s.contains n = true then (s, acc) else (s.insert n, acc.push n)) (s, acc)).2) := by
  induction l with
  | nil => intro s acc _; exact ⟨fun _ h => h, fun _ h => nomatch h⟩
  | cons n rest ih =>
    intro s acc hs
    simp only [List.foldl_cons]
    split
    · rename_i hc
      obtain ⟨i1, i2⟩ := ih s acc hs
      refine ⟨i1, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact i1 _ (hs _ hc)
      · exact i2 x hx
    · have hs' : ∀ x, (s.insert n).contains x = true → x ∈ acc.push n := by
        intro x hx
        rw [Std.HashSet.contains_insert] at hx
        rcases Bool.or_eq_true_iff.1 hx with hx | hx
        · rw [show x = n from (eq_of_beq hx).symm]; exact Array.mem_push_self
        · exact Array.mem_push_of_mem _ (hs x hx)
      obtain ⟨i1, i2⟩ := ih (s.insert n) (acc.push n) hs'
      refine ⟨fun x hx => i1 x (Array.mem_push_of_mem _ hx), fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact i1 _ Array.mem_push_self
      · exact i2 x hx

theorem usedConstants_complete {e : Expr} {n : Name} (h : OccS (fun _ => false) cPick n e) :
    n ∈ EO.usedConstants e := by
  have hc : n ∈ EO.collect (fun _ => false) cPick e := collect_complete cPick_compound e h
  unfold EO.usedConstants
  dsimp only
  rw [← Array.foldl_toList]
  exact (dedup_mem _ {} #[] (fun x hx => by simp at hx)).2 n (Array.mem_toList_iff.2 hc)

end dedup

theorem any_eq_anySpec (p : Expr → Bool) (e : Expr) :
    EO.any p e = anySpec (fun x _ => if p x then some true else none) e 0 := by
  unfold EO.any; rw [anyNode_fresh]

theorem natLit_cr {L : ConLeche.Env} (h : ConLeche.natLitStored L = true) (n : Nat) :
    (ConLeche.Expr.lit (.natVal n)).constsResolve L = true := by
  simpa [ConLeche.Expr.constsResolve, ConLeche.natLitStored, Bool.and_assoc] using h

theorem strLit_cr {L : ConLeche.Env} (h : ConLeche.strLitStored L = true) (s : String) :
    (ConLeche.Expr.lit (.strVal s)).constsResolve L = true := by
  simpa [ConLeche.Expr.constsResolve, ConLeche.strLitStored, ConLeche.natLitStored,
    Bool.and_assoc] using h

/-- **Resolution on the reading**, generic in the free variables' reading. -/
theorem constsResolve_trE {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (fv : FVarId → Option ConLeche.Expr)
    (hfv : ∀ id, okE fv (.fvar id) = true → (trE fv (.fvar id)).constsResolve L = true) :
    ∀ (e : Expr) (k : Nat), okE fv e = true →
      (∀ n, OccS (fun _ => false) cPick n e → (fe.find? n).isSome = true) →
      anySpec (fun x _ => if unresI fe x then some true else none) e k = false →
      (trE fv e).constsResolve L = true := by
  have hdom := envDomI_of hP
  intro e
  induction e with
  | bvar => intro _ _ _ _; rfl
  | sort => intro _ _ _ _; rfl
  | fvar id => intro _ h _ _; exact hfv id h
  | mvar => intro _ h _ _; simp [okE] at h
  | const n us =>
    intro _ _ hc _
    have := find_isSome_of_pres hP (hc n ⟨rfl, rfl⟩)
    simpa [trE, ConLeche.Expr.constsResolve] using this
  | lit l =>
    intro k _ _ ha
    cases l with
    | natVal m =>
      cases hn : natLitStoredF fe
      · simp [anySpec, unresI, hn] at ha
      · exact natLit_cr (by rw [← natLitStoredF_I hdom]; exact hn) m
    | strVal m =>
      cases hn : strLitStoredF fe
      · simp [anySpec, unresI, hn] at ha
      · exact strLit_cr (by rw [← strLitStoredF_I hdom]; exact hn) m
  | app f a ihf iha =>
    intro k hok hc ha
    simp only [okE, Bool.and_eq_true] at hok
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨ihf k hok.1 (fun n h => hc n ⟨rfl, .inl h⟩) ha.1,
      iha k hok.2 (fun n h => hc n ⟨rfl, .inr h⟩) ha.2⟩
  | lam nm t b bi iht ihb =>
    intro k hok hc ha
    simp only [okE, Bool.and_eq_true] at hok
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨iht k hok.1 (fun n h => hc n ⟨rfl, .inl h⟩) ha.1,
      ihb (k + 1) hok.2 (fun n h => hc n ⟨rfl, .inr h⟩) ha.2⟩
  | forallE nm t b bi iht ihb =>
    intro k hok hc ha
    simp only [okE, Bool.and_eq_true] at hok
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨iht k hok.1 (fun n h => hc n ⟨rfl, .inl h⟩) ha.1,
      ihb (k + 1) hok.2 (fun n h => hc n ⟨rfl, .inr h⟩) ha.2⟩
  | letE nm t v b nd iht ihv ihb =>
    intro k hok hc ha
    simp only [okE, Bool.and_eq_true] at hok
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨⟨iht k hok.1.1 (fun n h => hc n ⟨rfl, .inl h⟩) ha.1.1,
      ihv k hok.1.2 (fun n h => hc n ⟨rfl, .inr (.inl h)⟩) ha.1.2⟩,
      ihb (k + 1) hok.2 (fun n h => hc n ⟨rfl, .inr (.inr h)⟩) ha.2⟩
  | mdata m x ih =>
    intro k hok hc ha
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none] at ha
    exact ih k hok (fun n h => hc n ⟨rfl, h⟩) ha
  | proj s i x ih =>
    intro k hok hc ha
    cases hs : (fe.find? s).isSome
    · have hn : fe.find? s = none := by simpa using hs
      simp [anySpec, unresI, hn] at ha
    · have hn : fe.find? s ≠ none := by simpa [← Option.isSome_iff_ne_none] using hs
      have ha' : anySpec (fun x _ => if unresI fe x then some true else none) x k = false := by
        simpa [anySpec, unresI, hn] using ha
      simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
      exact ⟨find_isSome_of_pres hP hs, ih k hok (fun n h => hc n ⟨rfl, h⟩) ha'⟩

/-- **InLean's resolution is master's** on a reading with free variables
resolving. -/
theorem constsResolve_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (fv : FVarId → Option ConLeche.Expr)
    (hfv : ∀ id, okE fv (.fvar id) = true → (trE fv (.fvar id)).constsResolve L = true)
    {e : Expr} (hok : okE fv e = true) (h : InLean.constsResolve fe e = true) :
    (trE fv e).constsResolve L = true := by
  unfold InLean.constsResolve at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  rw [any_eq_anySpec] at h2
  refine constsResolve_trE hP fv hfv e 0 hok (fun n hn => ?_) ?_
  · exact List.all_eq_true.1 (by simpa [← Array.all_toList] using h1) n
      (Array.mem_toList_iff.2 (usedConstants_complete hn))
  · have : (fun x (_ : Nat) => if (match x with
        | .proj s _ _ => (fe.find? s).isNone
        | .lit (.natVal _) => !natLitStoredF fe
        | .lit (.strVal _) => !strLitStoredF fe
        | _ => false) = true then some true else none) =
        (fun x _ => if unresI fe x then some true else none) := by
      funext x k; cases x <;> rfl
    rw [← this]; exact h2

/-- Closed terms. -/
theorem constsResolve_trC {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {e : Expr}
    (hok : okC e = true) (h : InLean.constsResolve fe e = true) : (trC e).constsResolve L = true :=
  constsResolve_tr hP _ (fun _ h => by simp [okE] at h) hok h

end InLeanProof
