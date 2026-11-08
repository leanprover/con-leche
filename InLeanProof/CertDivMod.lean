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

/-- The unresolved-node test of `InLean.constsResolve`. -/
@[expose] def unresI (fe : InLean.FEnv) : Expr → Bool
  | .const c _ => (fe.find? c).isNone
  | .proj s _ _ => (fe.find? s).isNone
  | .lit (.natVal _) => !natLitStoredF fe
  | .lit (.strVal _) => !strLitStoredF fe
  | _ => false


theorem any_eq_anySpec (p : Expr → Bool) (e : Expr) :
    EO.any p e = anySpec (fun x _ => if p x then some true else none) e 0 := by
  unfold EO.any; rw [anyNode_spec]

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
      anySpec (fun x _ => if unresI fe x then some true else none) e k = false →
      (trE fv e).constsResolve L = true := by
  have hdom := envDomI_of hP
  intro e
  induction e with
  | bvar => intro _ _ _; rfl
  | sort => intro _ _ _; rfl
  | fvar id => intro _ h _; exact hfv id h
  | mvar => intro _ h _; simp [okE] at h
  | const n us =>
    intro _ _ ha
    cases hs : (fe.find? n).isSome
    · have hn : fe.find? n = none := by simpa using hs
      simp [anySpec, unresI, hn] at ha
    · simpa [trE, ConLeche.Expr.constsResolve] using find_isSome_of_pres hP hs
  | lit l =>
    intro k _ ha
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
    intro k hok ha
    simp only [okE, Bool.and_eq_true] at hok
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨ihf k hok.1 ha.1,
      iha k hok.2 ha.2⟩
  | lam nm t b bi iht ihb =>
    intro k hok ha
    simp only [okE, Bool.and_eq_true] at hok
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨iht k hok.1 ha.1,
      ihb (k + 1) hok.2 ha.2⟩
  | forallE nm t b bi iht ihb =>
    intro k hok ha
    simp only [okE, Bool.and_eq_true] at hok
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨iht k hok.1 ha.1,
      ihb (k + 1) hok.2 ha.2⟩
  | letE nm t v b nd iht ihv ihb =>
    intro k hok ha
    simp only [okE, Bool.and_eq_true] at hok
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Bool.or_eq_false_iff] at ha
    simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
    exact ⟨⟨iht k hok.1.1 ha.1.1,
      ihv k hok.1.2 ha.1.2⟩,
      ihb (k + 1) hok.2 ha.2⟩
  | mdata m x ih =>
    intro k hok ha
    simp only [anySpec, unresI, Bool.false_eq_true, ↓reduceIte, Option.getD_none] at ha
    exact ih k hok ha
  | proj s i x ih =>
    intro k hok ha
    cases hs : (fe.find? s).isSome
    · have hn : fe.find? s = none := by simpa using hs
      simp [anySpec, unresI, hn] at ha
    · have hn : fe.find? s ≠ none := by simpa [← Option.isSome_iff_ne_none] using hs
      have ha' : anySpec (fun x _ => if unresI fe x then some true else none) x k = false := by
        simpa [anySpec, unresI, hn] using ha
      simp only [trE, ConLeche.Expr.constsResolve, Bool.and_eq_true]
      exact ⟨find_isSome_of_pres hP hs, ih k hok ha'⟩

/-- **InLean's resolution is master's** on a reading with free variables
resolving. -/
theorem constsResolve_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (fv : FVarId → Option ConLeche.Expr)
    (hfv : ∀ id, okE fv (.fvar id) = true → (trE fv (.fvar id)).constsResolve L = true)
    {e : Expr} (hok : okE fv e = true) (h : InLean.constsResolve fe e = true) :
    (trE fv e).constsResolve L = true := by
  unfold InLean.constsResolve at h
  simp only [Bool.not_eq_true'] at h
  rw [any_eq_anySpec] at h
  refine constsResolve_trE hP fv hfv e 0 hok ?_
  have : (fun x (_ : Nat) => if (match x with
      | .const c _ => (fe.find? c).isNone
      | .proj s _ _ => (fe.find? s).isNone
      | .lit (.natVal _) => !natLitStoredF fe
      | .lit (.strVal _) => !strLitStoredF fe
      | _ => false) = true then some true else none) =
      (fun x _ => if unresI fe x then some true else none) := by
    funext x k; cases x <;> rfl
  rw [← this]; exact h

/-- Closed terms. -/
theorem constsResolve_trC {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {e : Expr}
    (hok : okC e = true) (h : InLean.constsResolve fe e = true) : (trC e).constsResolve L = true :=
  constsResolve_tr hP _ (fun _ h => by simp [okE] at h) hok h

/-! ## The decoded pin variants are in range -/

/-- **Every term InLean decodes is in range**: the decoder refuses a dump
with a term out of range (`PinSet.inRange`). -/
theorem loadPinSets_range {sets : Array InLean.PinSet} (h : InLean.loadPinSets () = .ok sets) :
    ∀ ps ∈ sets, ∀ op ∈ ps.ops, (Expr.RangeOk op.pin ∧ emvarS op.pin = false) ∧
      (∀ p ∈ op.proofs, Expr.RangeOk p ∧ emvarS p = false) ∧
      ∀ t ∈ op.typePins, Expr.RangeOk t.2 ∧ emvarS t.2 = false := by
  unfold InLean.loadPinSets at h
  obtain ⟨sets', h1, h2⟩ := except_bind_ok h
  split at h2
  · rename_i hall
    simp only [pure, Except.pure, Except.ok.injEq] at h2
    subst h2
    intro ps hps op hop
    have h3 := Array.all_eq_true_iff_forall_mem.1 (by simpa using hall) ps hps
    have h4 := Array.all_eq_true_iff_forall_mem.1 h3 op hop
    simp only [InLean.PinOp.inRange, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h4
    exact ⟨RangeOk_of_inRange h4.1.1, fun p hp => RangeOk_of_inRange (h4.1.2 p hp),
      fun t ht => RangeOk_of_inRange (h4.2 t ht)⟩
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h2

end InLeanProof
