module

public import ConLeche.Model.Inductives.NestPosMono

public section

/-!
# N2 read semantically: a container instance's index telescope is hole-free (lane CONTSEM)

`nestInstType` (`Kernel/Inductives/Positivity.lean`) checks, for a key
`C.{us} ds` at the walk's hole bound `hi`, that the instantiated type
`instPisWith ds (C's type at us)` is a syntactic Π-telescope ending in a
sort whose binder domains mention no hole (N2, official's "unknown
constant").  Read: every domain of the instantiated type's reading
mentions no hole position (`noBVarTele_of_piDomsFree`), so two valuations
agreeing off the holes read the same index telescope — the container's
index sets, and its hole values applied to the key's parameters, are the
same at both sides of a hole relation.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The syntactic side -/

/-- A Π-telescope ending in a sort whose domains mention no hole. -/
@[expose] def PiDomsFree (names : List Name) (lo hi : Nat) : Expr → Prop
  | .forallE ty b _ => ty.nestOcc names lo hi = false ∧ PiDomsFree names lo hi b
  | .sort _ => True
  | _ => False

/-- The number of leading `∀` binders. -/
@[expose] def piCount : Expr → Nat
  | .forallE _ b _ => piCount b + 1
  | _ => 0

theorem piDomsFree_of_binders {names : List Name} {lo hi : Nat} :
    ∀ (e : Expr) {s : Level}, e.piBinders.2 = .sort s →
      (e.piBinders.1.any fun b => b.1.nestOcc names lo hi) = false → PiDomsFree names lo hi e := by
  intro e
  induction e with
  | forallE ty b mb _ ihb =>
    intro s hs hany
    simp only [ConLeche.Expr.piBinders, List.any_cons, Bool.or_eq_false_iff] at hs hany
    exact ⟨hany.1, ihb hs hany.2⟩
  | sort u => intro _ _ _; trivial
  | bvar => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | fvar => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | const => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | app => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | lam => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | letE => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | lit => intro s hs; simp [ConLeche.Expr.piBinders] at hs
  | proj => intro s hs; simp [ConLeche.Expr.piBinders] at hs

theorem PiDomsFree.instantiate1 {names : List Name} {lo hi d : Nat} (hd : ¬ (lo ≤ d ∧ d < hi))
    (ty : Expr) : ∀ (e : Expr) (k : Nat), PiDomsFree names lo hi e →
      PiDomsFree names lo hi (e.instantiate1 (.fvar d ty) k) := by
  intro e
  induction e with
  | forallE t b mb _ ihb =>
    intro k h
    obtain ⟨h1, h2⟩ := h
    exact ⟨by rw [nestOcc_instantiate1_fvar hd ty t k]; exact h1, ihb (k + 1) h2⟩
  | sort u => intro _ _; trivial
  | bvar => intro _ h; exact h.elim
  | fvar => intro _ h; exact h.elim
  | const => intro _ h; exact h.elim
  | app => intro _ h; exact h.elim
  | lam => intro _ h; exact h.elim
  | letE => intro _ h; exact h.elim
  | lit => intro _ h; exact h.elim
  | proj => intro _ h; exact h.elim

theorem piCount_instantiate1_fvar {d : Nat} (ty : Expr) :
    ∀ (e : Expr) (k : Nat), piCount (e.instantiate1 (.fvar d ty) k) = piCount e := by
  intro e
  induction e with
  | forallE t b mb _ ihb => intro k; simp only [ConLeche.Expr.instantiate1, piCount, ihb]
  | bvar i =>
    intro k
    simp only [ConLeche.Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | _ => intro k; rfl

/-! ## The reading -/

theorem NoBVarTele.mono :
    ∀ {Fs : List AnnotTerm} {P Q : Nat → Prop}, (∀ i, Q i → P i) → NoBVarTele P Fs →
      NoBVarTele Q Fs
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, h, ⟨h1, h2⟩ => ⟨NoBVar.mono h h1, NoBVarTele.mono (shiftP_mono h) h2⟩

/-- **A hole-free telescope reads hole-free**: the reading of a
Π-telescope ending in a sort whose domains mention no hole is a Π-tower
ending in a sort whose every domain mentions no hole position. -/
theorem noBVarTele_of_piDomsFree {names : List Name} {lo hi : Nat} :
    ∀ (n : Nat) (e : Expr) {d : Nat} {ea : AnnotTerm}, piCount e = n →
      PiDomsFree names lo hi e → Expr.WScoped d e → hi ≤ d →
      denoteMeta m.acval env φ d e = some ea →
      ∃ (ab : List (Nat × Nat × AnnotTerm)) (u : Nat), ea = mkPisAV ab (.sort u) ∧
        NoBVarTele (holeP d lo hi) (ab.map (·.2.2)) := by
  intro n
  induction n with
  | zero =>
    intro e d ea hn hf _ _ h
    match e, hn, hf, h with
    | .sort s, _, _, h =>
      rw [denoteMeta_sort] at h
      exact ⟨[], _, (Option.some.inj h).symm, trivial⟩
  | succ n ih =>
    intro e d ea hn hf hws hd h
    match e, hn, hf, hws, h with
    | .forallE ty b mb, hn, hf, hws, h =>
      obtain ⟨hty, hb⟩ := hf
      simp only [piCount, Nat.add_right_cancel_iff] at hn
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
      simp only [Expr.WScoped] at hws
      have hA : NoBVar (holeP d lo hi) ta := denoteMeta_noBVar_of_nestOcc d ty hws.1 hd hty hta
      have hnot : ¬ (lo ≤ d ∧ d < hi) := by omega
      obtain ⟨ab, u, rfl, hab⟩ := ih (b.instantiate1 (.fvar d ty))
        (by rw [piCount_instantiate1_fvar]; exact hn)
        (PiDomsFree.instantiate1 hnot ty b 0 hb)
        (Expr.WScoped.instantiate1 hws.1 0 hws.2) (by omega) hba
      exact ⟨(_, _, ta) :: ab, u, rfl, hA, NoBVarTele.mono holeP_succ hab⟩

end ConLeche.Model
