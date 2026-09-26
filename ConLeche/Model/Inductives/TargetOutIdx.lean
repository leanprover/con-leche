module

public import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Inductives.BlockRecRule

public section

/-!
# An outside major's index count is its container's

At an outside major `I.{us} D⃗ i⃗` the target check counts the indices
syntactically: `targetOutsideInst` instantiates `I`'s type at the levels
and the parameters `D⃗` and requires the rest to be a Π-telescope ending
in a sort, whose binders it counts (`M.nIdx`).  The recursor model reads
the major's domain through `I`'s recorded clause, whose index telescope
`D.ids` has the length of the READING of `I`'s type past its parameters
(`LfpReads`).  The two agree (`tgtOutIdx_len`), without any recorded
fact: a reading that is a Π-tower ending in a sort forces the type's
syntactic Π-tail to be neither a variable (`tailOk_of_read`) — so
instantiating the parameters opens no new binder — and once the
instantiated tail is a sort, the original tail is a sort and the
reading counts exactly the syntactic binders (`read_of_sortTail`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- The syntactic Π-tail of a term (`Expr.piBinders`' second part). -/
@[expose] def piTail : Expr → Expr
  | .forallE _ b _ => piTail b
  | e => e

theorem piBinders_snd_eq : ∀ e : Expr, e.piBinders.2 = piTail e := by
  intro e
  induction e with
  | forallE t b mb _ ihb => simp [ConLeche.Expr.piBinders, piTail, ihb]
  | _ => simp [ConLeche.Expr.piBinders, piTail]

/-- The tail is no variable (bound or free). -/
@[expose] def TailOk (e : Expr) : Prop :=
  match piTail e with
  | .bvar _ => False
  | .fvar _ _ => False
  | _ => True

/-- The tail is a sort. -/
@[expose] def SortTail (e : Expr) : Prop :=
  match piTail e with
  | .sort _ => True
  | _ => False

theorem tailOk_of_sortTail {e : Expr} (h : SortTail e) : TailOk e := by
  unfold SortTail at h; unfold TailOk
  split at h <;> simp_all

/-- **Instantiation keeps a variable-free tail**: the Π-count, the tail's
being a sort, and its freedom from variables are unchanged. -/
theorem tail_instantiate1 (v : Expr) :
    ∀ (e : Expr) (k : Nat), TailOk e →
      piCount (e.instantiate1 v k) = piCount e ∧ (SortTail (e.instantiate1 v k) ↔ SortTail e) ∧
        TailOk (e.instantiate1 v k) := by
  intro e
  induction e with
  | forallE t b mb _ ihb =>
    intro k h
    have h' : TailOk b := h
    obtain ⟨h1, h2, h3⟩ := ihb (k + 1) h'
    exact ⟨by simp only [ConLeche.Expr.instantiate1, piCount, h1], h2, h3⟩
  | bvar i => intro _ h; exact h.elim
  | fvar => intro _ h; exact h.elim
  | sort => intro _ _; exact ⟨rfl, Iff.rfl, trivial⟩
  | const => intro _ _; exact ⟨rfl, Iff.rfl, trivial⟩
  | lit => intro _ _; exact ⟨rfl, Iff.rfl, trivial⟩
  | app => intro _ _; exact ⟨rfl, ⟨fun h => h.elim, fun h => h.elim⟩, trivial⟩
  | lam => intro _ _; exact ⟨rfl, ⟨fun h => h.elim, fun h => h.elim⟩, trivial⟩
  | letE => intro _ _; exact ⟨rfl, ⟨fun h => h.elim, fun h => h.elim⟩, trivial⟩
  | proj => intro _ _; exact ⟨rfl, ⟨fun h => h.elim, fun h => h.elim⟩, trivial⟩

/-- **Opening a binder at a free variable reveals no tail**: if the
opened body's tail is no variable, neither is the body's. -/
theorem tailOk_of_instantiate1_fvar (d : Nat) (ty : Expr) :
    ∀ (e : Expr) (k : Nat), TailOk (e.instantiate1 (.fvar d ty) k) → TailOk e := by
  intro e
  induction e with
  | forallE t b mb _ ihb => intro k h; exact ihb (k + 1) h
  | bvar i =>
    intro k h
    simp only [ConLeche.Expr.instantiate1] at h
    split at h
    · exact h.elim
    · split at h <;> exact h.elim
  | fvar => intro _ h; exact h.elim
  | sort => intro _ _; trivial
  | const => intro _ _; trivial
  | lit => intro _ _; trivial
  | app => intro _ _; trivial
  | lam => intro _ _; trivial
  | letE => intro _ _; trivial
  | proj => intro _ _; trivial

/-- **Level instantiation keeps the tail**: the Π-count, the tail's being
a sort, and its freedom from variables. -/
theorem tail_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ e : Expr, piCount (e.instantiateLevelParams ks us) = piCount e ∧
      (SortTail (e.instantiateLevelParams ks us) ↔ SortTail e) ∧
      (TailOk (e.instantiateLevelParams ks us) ↔ TailOk e) := by
  intro e
  induction e with
  | forallE t b mb _ ihb =>
    obtain ⟨h1, h2, h3⟩ := ihb
    exact ⟨by simp only [ConLeche.Expr.instantiateLevelParams, piCount, h1], h2, h3⟩
  | bvar => exact ⟨rfl, Iff.rfl, Iff.rfl⟩
  | fvar => exact ⟨rfl, Iff.rfl, Iff.rfl⟩
  | sort => exact ⟨rfl, ⟨fun _ => trivial, fun _ => trivial⟩, ⟨fun _ => trivial, fun _ => trivial⟩⟩
  | const => exact ⟨rfl, Iff.rfl, ⟨fun _ => trivial, fun _ => trivial⟩⟩
  | lit => exact ⟨rfl, Iff.rfl, ⟨fun _ => trivial, fun _ => trivial⟩⟩
  | app => exact ⟨rfl, Iff.rfl, ⟨fun _ => trivial, fun _ => trivial⟩⟩
  | lam => exact ⟨rfl, Iff.rfl, ⟨fun _ => trivial, fun _ => trivial⟩⟩
  | letE => exact ⟨rfl, Iff.rfl, ⟨fun _ => trivial, fun _ => trivial⟩⟩
  | proj => exact ⟨rfl, Iff.rfl, ⟨fun _ => trivial, fun _ => trivial⟩⟩

/-- **Instantiating the parameters at a variable-free tail** consumes as
many syntactic binders as there are arguments, and keeps the tail. -/
theorem tail_instPisWith :
    ∀ (ds : List Expr) {e ty : Expr}, TailOk e → ConLeche.instPisWith ds e = some ty →
      piCount e = ds.length + piCount ty ∧ (SortTail ty ↔ SortTail e) := by
  intro ds
  induction ds with
  | nil =>
    intro e ty _ h
    simp only [ConLeche.instPisWith, Option.some.injEq] at h
    subst h; exact ⟨by simp, Iff.rfl⟩
  | cons x ds ih =>
    intro e ty he h
    match e, he, h with
    | .forallE t b mb, he, h =>
      simp only [ConLeche.instPisWith] at h
      have hb : TailOk b := he
      obtain ⟨h1, h2, h3⟩ := tail_instantiate1 x b 0 hb
      obtain ⟨k1, k2⟩ := ih h3 h
      refine ⟨?_, k2.trans h2⟩
      simp only [piCount, List.length_cons]
      omega

/-- **A reading that is a Π-tower ending in a sort** comes from a term
whose syntactic tail is no variable. -/
theorem tailOk_of_read {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (n : Nat) (e : Expr) {d : Nat} {ab : List (Nat × Nat × AnnotTerm)} {u : Nat},
      piCount e = n → denoteMeta acval env φ d e = some (mkPisAV ab (.sort u)) → TailOk e := by
  intro n
  induction n with
  | zero =>
    intro e d ab u hn h
    match e, hn, h with
    | .bvar _, _, h => rw [denoteMeta_bvar] at h; exact nomatch h
    | .fvar idx ty, _, h =>
      rw [denoteMeta_fvar] at h
      cases ab with
      | nil => simp [mkPisAV] at h
      | cons => simp [mkPisAV] at h
    | .sort _, _, _ => trivial
    | .const _ _, _, _ => trivial
    | .lit _, _, _ => trivial
    | .app _ _, _, _ => trivial
    | .lam _ _ _, _, _ => trivial
    | .letE _ _ _, _, _ => trivial
    | .proj _ _ _, _, _ => trivial
  | succ n ih =>
    intro e d ab u hn h
    match e, hn, h with
    | .forallE ty b mb, hn, h =>
      simp only [piCount, Nat.add_right_cancel_iff] at hn
      obtain ⟨ta, ba, -, hba, heq⟩ := denoteMeta_forallE_inv h
      cases ab with
      | nil => simp [mkPisAV] at heq
      | cons a ab =>
        simp only [mkPisAV, AnnotTerm.pi.injEq] at heq
        obtain ⟨-, -, -, rfl⟩ := heq
        exact tailOk_of_instantiate1_fvar d ty b 0
          (ih _ (by rw [piCount_instantiate1_fvar]; exact hn) hba)

/-- **A sort tail reads as a Π-tower ending in a sort, one binder per
syntactic binder.** -/
theorem read_of_sortTail {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (n : Nat) (e : Expr) {d : Nat} {ea : AnnotTerm}, piCount e = n → SortTail e →
      denoteMeta acval env φ d e = some ea →
      ∃ (ab : List (Nat × Nat × AnnotTerm)) (u : Nat), ea = mkPisAV ab (.sort u) ∧
        ab.length = n := by
  intro n
  induction n with
  | zero =>
    intro e d ea hn hs h
    match e, hn, hs, h with
    | .sort s, _, _, h =>
      rw [denoteMeta_sort] at h
      exact ⟨[], _, (Option.some.inj h).symm, rfl⟩
  | succ n ih =>
    intro e d ea hn hs h
    match e, hn, hs, h with
    | .forallE ty b mb, hn, hs, h =>
      simp only [piCount, Nat.add_right_cancel_iff] at hn
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv h
      have hsb : SortTail b := hs
      obtain ⟨h1, h2, -⟩ := tail_instantiate1 (.fvar d ty) b 0 (tailOk_of_sortTail hsb)
      obtain ⟨ab, u, rfl, hlen⟩ := ih _ (by rw [h1]; exact hn) (h2.mpr hsb) hba
      exact ⟨(_, _, ta) :: ab, u, rfl, by simp [hlen]⟩

/-- **The kernel's index count at an instantiation is the reading's**:
a type reading as a Π-tower `ab` ending in a sort, whose level- and
parameter-instantiation `ty` has a sort as its syntactic tail, has
`ds.length + |ty.piBinders.1| = |ab|`. -/
theorem instPis_count_of_read {acval : Name → (Name → Nat) → AnnotTerm} {e : Expr} {d : Nat}
    {ab : List (Nat × Nat × AnnotTerm)} {u : Nat}
    (hread : denoteMeta acval env φ d e = some (mkPisAV ab (.sort u)))
    (ks : List Name) (us : List Level) {ds : List Expr} {ty : Expr} {s : Level}
    (hty : ConLeche.instPisWith ds (e.instantiateLevelParams ks us) = some ty)
    (hs : ty.piBinders.2 = .sort s) :
    ds.length + ty.piBinders.1.length = ab.length := by
  have hok := tailOk_of_read _ e rfl hread
  obtain ⟨l1, l2, l3⟩ := tail_instantiateLevelParams ks us e
  obtain ⟨k1, k2⟩ := tail_instPisWith ds (l3.mpr hok) hty
  have hsty : SortTail ty := by
    unfold SortTail; rw [← piBinders_snd_eq, hs]; trivial
  have hse : SortTail e := l2.mp (k2.mp hsty)
  obtain ⟨ab', u', heq, hlen⟩ := read_of_sortTail _ e rfl hse hread
  obtain ⟨rfl, -⟩ := mkPisAV_sort_eq heq
  rw [hlen, ← l1, k1, piCount_eq_length]

/-! ## The tail's LEVEL (`huniq` at an outside class) -/

omit [SetTheory V] in
/-- Instantiating a bound variable keeps a sort tail. -/
theorem piTail_instantiate1_sort (v : Expr) {l : Level} :
    ∀ (e : Expr) (k : Nat), piTail e = .sort l → piTail (e.instantiate1 v k) = .sort l := by
  intro e
  induction e with
  | forallE t b mb _ ihb => intro k h; exact ihb (k + 1) h
  | sort u => intro _ h; exact h
  | bvar => intro _ h; simp [piTail] at h
  | fvar => intro _ h; simp [piTail] at h
  | const => intro _ h; simp [piTail] at h
  | lit => intro _ h; simp [piTail] at h
  | app => intro _ h; simp [piTail] at h
  | lam => intro _ h; simp [piTail] at h
  | letE => intro _ h; simp [piTail] at h
  | proj => intro _ h; simp [piTail] at h

omit [SetTheory V] in
/-- Level instantiation substitutes a sort tail's level. -/
theorem piTail_instantiateLevelParams_sort (ks : List Name) (us : List Level) {l : Level} :
    ∀ e : Expr, piTail e = .sort l →
      piTail (e.instantiateLevelParams ks us) = .sort (Level.subst ks us l) := by
  intro e
  induction e with
  | forallE t b mb _ ihb => intro h; exact ihb h
  | sort u => intro h; simp only [piTail, Expr.sort.injEq] at h; subst h; rfl
  | bvar => intro h; simp [piTail] at h
  | fvar => intro h; simp [piTail] at h
  | const => intro h; simp [piTail] at h
  | lit => intro h; simp [piTail] at h
  | app => intro h; simp [piTail] at h
  | lam => intro h; simp [piTail] at h
  | letE => intro h; simp [piTail] at h
  | proj => intro h; simp [piTail] at h

omit [SetTheory V] in
/-- Instantiating the parameters keeps a sort tail. -/
theorem piTail_instPisWith_sort {l : Level} :
    ∀ (ds : List Expr) {e ty : Expr}, piTail e = .sort l → ConLeche.instPisWith ds e = some ty →
      piTail ty = .sort l := by
  intro ds
  induction ds with
  | nil =>
    intro e ty he h
    simp only [ConLeche.instPisWith, Option.some.injEq] at h
    subst h; exact he
  | cons x ds ih =>
    intro e ty he h
    match e, he, h with
    | .forallE t b mb, he, h =>
      simp only [ConLeche.instPisWith] at h
      exact ih (piTail_instantiate1_sort x b 0 he) h

/-- **A sort tail's reading is its level's value**: a term whose
syntactic tail is `Sort l` and which reads as a Π-tower ending in
`Sort u` has `u = l`'s value. -/
theorem read_sortTail_eval {acval : Name → (Name → Nat) → AnnotTerm} {l : Level} :
    ∀ (n : Nat) (e : Expr) {d : Nat} {ab : List (Nat × Nat × AnnotTerm)} {u : Nat},
      piCount e = n → piTail e = .sort l →
      denoteMeta acval env φ d e = some (mkPisAV ab (.sort u)) → u = Level.eval φ l := by
  intro n
  induction n with
  | zero =>
    intro e d ab u hn ht h
    match e, hn, ht, h with
    | .sort s, _, ht, h =>
      simp only [piTail, Expr.sort.injEq] at ht
      subst ht
      rw [denoteMeta_sort] at h
      cases ab with
      | nil => simpa [mkPisAV] using (Option.some.inj h).symm
      | cons => simp [mkPisAV] at h
  | succ n ih =>
    intro e d ab u hn ht h
    match e, hn, ht, h with
    | .forallE ty b mb, hn, ht, h =>
      simp only [piCount, Nat.add_right_cancel_iff] at hn
      obtain ⟨ta, ba, -, hba, heq⟩ := denoteMeta_forallE_inv h
      cases ab with
      | nil => simp [mkPisAV] at heq
      | cons a ab =>
        simp only [mkPisAV, AnnotTerm.pi.injEq] at heq
        obtain ⟨-, -, -, rfl⟩ := heq
        exact ih _ (by rw [piCount_instantiate1_fvar]; exact hn)
          (piTail_instantiate1_sort _ b 0 ht) hba

/-- **The kernel's sort at an instantiation is the reading's**: a type
reading as a Π-tower ending in `Sort u`, whose level- and
parameter-instantiation `ty` has the syntactic tail `Sort s`, has
`u = s`'s value at the instantiated levels. -/
theorem instPis_sort_of_read {acval : Name → (Name → Nat) → AnnotTerm} {e : Expr} {d : Nat}
    {ab : List (Nat × Nat × AnnotTerm)} {u : Nat} (ks : List Name) (us : List Level)
    (hread : denoteMeta acval env (Level.substFn φ ks us) d e = some (mkPisAV ab (.sort u)))
    {ds : List Expr} {ty : Expr} {s : Level}
    (hty : ConLeche.instPisWith ds (e.instantiateLevelParams ks us) = some ty)
    (hs : ty.piBinders.2 = .sort s) :
    u = Level.eval φ s := by
  have hok := tailOk_of_read _ e rfl hread
  obtain ⟨-, l2, l3⟩ := tail_instantiateLevelParams ks us e
  obtain ⟨-, k2⟩ := tail_instPisWith ds (l3.mpr hok) hty
  have hsty : SortTail ty := by
    unfold SortTail; rw [← piBinders_snd_eq, hs]; trivial
  have hse : SortTail e := l2.mp (k2.mp hsty)
  obtain ⟨l, hl⟩ : ∃ l, piTail e = .sort l := by
    unfold SortTail at hse
    split at hse
    · next l h => exact ⟨l, h⟩
    · exact hse.elim
  have hty' := piTail_instPisWith_sort ds (piTail_instantiateLevelParams_sort ks us e hl) hty
  rw [← piBinders_snd_eq, hs] at hty'
  obtain rfl : s = Level.subst ks us l := by simpa using hty'
  rw [ConLeche.Level.eval_subst]
  exact read_sortTail_eval _ e rfl hl hread

end ConLeche.Model
