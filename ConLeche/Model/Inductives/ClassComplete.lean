module

public import ConLeche.Model.Inductives.ClassStageF
public import ConLeche.Model.Inductives.HoleAccKit

public section

/-!
# The coherent completion of a valuation (P2d, DESIGN CLASSCHECK / P2D4)

The identification of a class's crest with its container's recorded
clause (`classCrest_spineFit_recorded`) holds at every valuation that is
LOCALLY COHERENT for the class's stage holes `F` (`StageCohF`): every
class outside `F` reads as its key with the classes of `F` abstracted.
A class fact's valuation is coherent only where the fact reads — the
crest's classes; the rest of the hole context is arbitrary.  The
COMPLETION of a valuation (`completeF`) replaces every hole of a class
outside `F` by that class's `F`-key read at the valuation: the `F`-keys
read no hole outside `F` (their holes are `F`'s, their parameters below
the class holes), so the completion is coherent (`stageCohF_completeF`),
and it agrees with the valuation off the completed holes — in
particular at every term mentioning only coherent holes, the valuation
and its completion read alike (`interp_congr_unmentioned`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ClassInfo)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## A reading ignores the variables its term does not mention -/

omit [SetTheory V] in
/-- Nothing is excluded. -/
theorem noBVar_empty : ∀ (e : AnnotTerm) {P : Nat → Prop}, (∀ i, ¬ P i) → NoBVar P e := by
  intro e
  induction e with
  | bvar i => intro P h; exact h i
  | app f a ihf iha => intro P h; exact ⟨ihf h, iha h⟩
  | lam _ A b ihA ihb => intro P h; exact ⟨ihA h, ihb fun i => by cases i <;> simp [shiftP, h]⟩
  | pi _ _ A B ihA ihB => intro P h; exact ⟨ihA h, ihB fun i => by cases i <;> simp [shiftP, h]⟩
  | eqE a b iha ihb => intro P h; exact ⟨iha h, ihb h⟩
  | fst e ih => intro P h; exact ih h
  | snd e ih => intro P h; exact ih h
  | sort _ | const _ _ | prf => intros; trivial

/-- **A reading does not read the positions of the free variables its
term does not mention**: two frames agreeing at the mentioned variables'
positions and above the context read it alike. -/
theorem interp_congr_unmentioned (m : EnvModel V env) {d : Nat} {e : Expr} {ea : AnnotTerm}
    (hws : Expr.fvarsBelow d e) (h : denoteMeta m.acval env φ d e = some ea)
    {σ σ' : Nat → V}
    (hag : ∀ i, i < d → e.nestOcc [] i (i + 1) = true → σ (d - 1 - i) = σ' (d - 1 - i))
    (hbig : ∀ j, d ≤ j → σ j = σ' j) : interp V σ ea = interp V σ' ea := by
  classical
  have hnb : NoBVar (fun j => ∃ i, (i < d ∧ e.nestOcc [] i (i + 1) = false) ∧ holeP d i (i + 1) j)
      ea := by
    refine noBVar_exists' (P := fun i j => (i < d ∧ e.nestOcc [] i (i + 1) = false) ∧
      holeP d i (i + 1) j) fun i => ?_
    by_cases hc : i < d ∧ e.nestOcc [] i (i + 1) = false
    · exact NoBVar.mono (fun j hj => hj.2)
        (denoteMeta_noBVar_of_nestOcc' (m := m) (φ := φ) d e hws (by omega) hc.2 h)
    · exact NoBVar.mono (fun j hj => absurd hj.1 hc) (noBVar_empty ea (P := fun _ => False) fun _ h => h)
  refine interp_congr_noBVar ea hnb fun j hj => ?_
  by_cases hjd : d ≤ j
  · exact hbig j hjd
  · have hi : d - 1 - j < d := by omega
    cases hocc : e.nestOcc [] (d - 1 - j) (d - 1 - j + 1) with
    | true =>
      have := hag (d - 1 - j) hi hocc
      rwa [show d - 1 - (d - 1 - j) = j by omega] at this
    | false =>
      exact absurd ⟨d - 1 - j, ⟨hi, hocc⟩, by unfold holeP; omega⟩ hj

/-! ## The variables the restricted abstraction mentions -/

theorem nestOcc_mkAppN_nil {i : Nat} :
    ∀ (as : List Expr) (f : Expr),
      (Expr.mkAppN f as).nestOcc [] i (i + 1) = (f.nestOcc [] i (i + 1) || as.any (·.nestOcc [] i (i + 1)))
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    rw [Expr.mkAppN, nestOcc_mkAppN_nil as (.app f a)]
    simp only [ConLeche.Expr.nestOcc, List.any_cons, Bool.or_assoc]

/-- **The class abstraction mentions a variable only if its term does or
a recognised hole is it.** -/
theorem nestOcc_classAbsSpec (occ : Expr → Option (Expr × Nat)) {i : Nat} :
    ∀ (e : Expr) (m : Option (Expr × Nat)),
      (ConLeche.classAbsSpec occ m e).nestOcc [] i (i + 1) = true →
      e.nestOcc [] i (i + 1) = true ∨
        (∃ x h n, occ x = some (h, n) ∧ h.nestOcc [] i (i + 1) = true) ∨
        (∃ h n, m = some (h, n) ∧ h.nestOcc [] i (i + 1) = true) := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro m hn
    rcases m with _ | ⟨h, _ | n⟩
    · unfold ConLeche.classAbsSpec at hn
      split at hn
      · rename_i h hx
        exact Or.inr (Or.inl ⟨_, h, 0, hx, hn⟩)
      · rename_i h n hx
        simp only [ConLeche.Expr.nestOcc, Bool.or_eq_true] at hn
        rcases hn with hn | hn
        · rcases ihf _ hn with h1 | h1 | ⟨h', n', he, h2⟩
          · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
          · exact Or.inr (Or.inl h1)
          · cases he; exact Or.inr (Or.inl ⟨_, h, n + 1, hx, h2⟩)
        · rcases iha _ hn with h1 | h1 | ⟨h', n', he, h2⟩
          · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
          · exact Or.inr (Or.inl h1)
          · cases he
      · simp only [ConLeche.Expr.nestOcc, Bool.or_eq_true] at hn
        rcases hn with hn | hn
        · rcases ihf _ hn with h1 | h1 | ⟨h', n', he, h2⟩
          · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
          · exact Or.inr (Or.inl h1)
          · cases he
        · rcases iha _ hn with h1 | h1 | ⟨h', n', he, h2⟩
          · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
          · exact Or.inr (Or.inl h1)
          · cases he
    · exact Or.inr (Or.inr ⟨h, 0, rfl, hn⟩)
    · simp only [ConLeche.classAbsSpec, ConLeche.Expr.nestOcc, Bool.or_eq_true] at hn
      rcases hn with hn | hn
      · rcases ihf _ hn with h1 | h1 | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl h1)
        · cases he; exact Or.inr (Or.inr ⟨h, n + 1, rfl, h2⟩)
      · rcases iha _ hn with h1 | h1 | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl h1)
        · cases he
  | lam t b bm iht ihb | forallE t b bm iht ihb =>
    intro m hn
    rcases m with _ | ⟨h, _ | n⟩
    · simp only [ConLeche.classAbsSpec, ConLeche.Expr.nestOcc, Bool.or_eq_true] at hn
      rcases hn with hn | hn
      · rcases iht _ hn with h1 | h1 | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl h1)
        · cases he
      · rcases ihb _ hn with h1 | h1 | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl h1)
        · cases he
    · exact Or.inr (Or.inr ⟨h, 0, rfl, hn⟩)
    · exact Or.inl hn
  | letE t v b iht ihv ihb =>
    intro m hn
    rcases m with _ | ⟨h, _ | n⟩
    · simp only [ConLeche.classAbsSpec, ConLeche.Expr.nestOcc, Bool.or_eq_true] at hn
      rcases hn with (hn | hn) | hn
      · rcases iht _ hn with h1 | h1 | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl h1)
        · cases he
      · rcases ihv _ hn with h1 | h1 | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl h1)
        · cases he
      · rcases ihb _ hn with h1 | h1 | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl h1)
        · cases he
    · exact Or.inr (Or.inr ⟨h, 0, rfl, hn⟩)
    · exact Or.inl hn
  | proj sn si y ihy =>
    intro m hn
    rcases m with _ | ⟨h, _ | n⟩
    · simp only [ConLeche.classAbsSpec, ConLeche.Expr.nestOcc] at hn
      rcases ihy _ hn with h1 | h1 | ⟨h', n', he, h2⟩
      · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
      · exact Or.inr (Or.inl h1)
      · cases he
    · exact Or.inr (Or.inr ⟨h, 0, rfl, hn⟩)
    · exact Or.inl hn
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro m hn
    rcases m with _ | ⟨h, _ | n⟩
    · exact Or.inl (by simpa [ConLeche.classAbsSpec] using hn)
    · exact Or.inr (Or.inr ⟨h, 0, rfl, hn⟩)
    · exact Or.inl (by simpa [ConLeche.classAbsSpec] using hn)

/-! ## The completion -/

section Complete

/-- **A hole's key value at `τ`**: a class outside `F` holds its hole at
the position `p`, and its `F`-key reads there as `v`. -/
@[expose] def KeyValAt (V : Type w) [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (cls : List ClassInfo) (F : Expr → Bool) (H : Nat)
    (τ : Nat → V) (p : Nat) (v : V) : Prop :=
  ∃ c ∈ cls, ∃ i ty a, c.hole = some (.fvar i ty) ∧ i < H ∧ p = H - 1 - i ∧
    F (.fvar i ty) = false ∧ denoteMeta acval env φ H (classKeyF cls F c) = some a ∧
    v = interp V τ a

open Classical in
/-- **The completion** of `τ`: every hole of a class outside `F` at its
`F`-key's value at `τ`. -/
@[expose] noncomputable def completeF (V : Type w) [SetTheory V]
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat) (cls : List ClassInfo)
    (F : Expr → Bool) (H : Nat) (τ : Nat → V) : Nat → V := fun p =>
  if h : ∃ v, KeyValAt V acval env φ cls F H τ p v then Classical.choose h else τ p

/-- **A hole index names one class.** -/
@[expose] def HoleIdxUniq (cls : List ClassInfo) : Prop :=
  ∀ c ∈ cls, ∀ c' ∈ cls, ∀ i ty ty', c.hole = some (.fvar i ty) → c'.hole = some (.fvar i ty') →
    c = c'

variable {acval : Name → (Name → Nat) → AnnotTerm} {cls : List ClassInfo} {F : Expr → Bool}
  {H : Nat}

theorem keyValAt_unique (hu : HoleIdxUniq cls) {τ : Nat → V} {p : Nat} {v v' : V}
    (h : KeyValAt V acval env φ cls F H τ p v) (h' : KeyValAt V acval env φ cls F H τ p v') :
    v = v' := by
  obtain ⟨c, hc, i, ty, a, hch, hi, rfl, -, ha, rfl⟩ := h
  obtain ⟨c', hc', i', ty', a', hch', hi', hp, -, ha', rfl⟩ := h'
  obtain rfl : i = i' := by omega
  obtain rfl := hu c hc c' hc' i ty ty' hch hch'
  rw [ha] at ha'
  cases ha'
  rfl

theorem completeF_eq_of (hu : HoleIdxUniq cls) {τ : Nat → V} {p : Nat} {v : V}
    (h : KeyValAt V acval env φ cls F H τ p v) : completeF V acval env φ cls F H τ p = v := by
  unfold completeF
  rw [dif_pos ⟨v, h⟩]
  exact keyValAt_unique hu (Classical.choose_spec (⟨v, h⟩ : ∃ v, _)) h

theorem completeF_eq_self {τ : Nat → V} {p : Nat}
    (h : ¬ ∃ v, KeyValAt V acval env φ cls F H τ p v) :
    completeF V acval env φ cls F H τ p = τ p := by
  unfold completeF
  rw [dif_neg h]

/-- **The completion keeps every position but the holes of the classes
outside `F`.** -/
theorem completeF_keep {τ : Nat → V} {p : Nat}
    (hp : ∀ c ∈ cls, ∀ i ty, c.hole = some (.fvar i ty) → i < H → p = H - 1 - i →
      F (.fvar i ty) = true) :
    completeF V acval env φ cls F H τ p = τ p := by
  refine completeF_eq_self fun ⟨v, c, hc, i, ty, a, hch, hi, hpe, hF, _⟩ => ?_
  rw [hp c hc i ty hch hi hpe] at hF
  exact Bool.noConfusion hF

/-- The completion keeps the positions of `F`'s holes, of the variables
below `lo`, and above the context. -/
theorem completeF_keep_of (hu : HoleIdxUniq cls) {lo : Nat}
    (hhole : ∀ c ∈ cls, ∀ h, c.hole = some h → ∃ i ty, h = .fvar i ty ∧ lo ≤ i ∧ i < H)
    {τ : Nat → V} {i : Nat}
    (hcase : i < lo ∨ ∃ c' ∈ cls, ∃ ty, c'.hole = some (.fvar i ty) ∧ F (.fvar i ty) = true) :
    completeF V acval env φ cls F H τ (H - 1 - i) = τ (H - 1 - i) := by
  refine completeF_keep fun c hc j ty hch hj hpe => ?_
  obtain rfl : j = i := by
    by_cases hiH : i < H
    · omega
    · rcases hcase with hlt | ⟨c', hc', ty', hch', -⟩
      · obtain ⟨i', ty'', he, hlo', -⟩ := hhole c hc _ hch
        cases he; omega
      · obtain ⟨i', ty'', he, -, hi'⟩ := hhole c' hc' _ hch'
        cases he; omega
  rcases hcase with hlt | ⟨c', hc', ty', hch', hF'⟩
  · obtain ⟨i', ty'', he, hlo', -⟩ := hhole c hc _ hch
    cases he; omega
  · obtain rfl := hu c hc c' hc' j ty ty' hch hch'
    rw [hch] at hch'
    cases hch'
    exact hF'

/-- **The completion is locally coherent** (`StageCohF`): given the
classes' `F`-keys scoped and read (`KeysFOk`), mentioning only variables
below `lo` (the parameters and members) and `F`'s holes, one class per
hole index, `F` closed under same keys, and the classes of `F` the same
up to spelling at one value. -/
theorem stageCohF_completeF (m : EnvModel V env) (hu : HoleIdxUniq cls) {lo : Nat}
    (hhole : ∀ c ∈ cls, ∀ h, c.hole = some h → ∃ i ty, h = .fvar i ty ∧ lo ≤ i ∧ i < H)
    (hkf : KeysFOk m.acval env φ cls F H) (hFc : FClosed cls F)
    (hkeyF : ∀ c ∈ cls, c.hole.isSome → F (c.hole.getD default) = false → ∀ i,
      (classKeyF cls F c).nestOcc [] i (i + 1) = true →
      i < lo ∨ ∃ c' ∈ cls, ∃ ty, c'.hole = some (.fvar i ty) ∧ F (.fvar i ty) = true)
    {τ : Nat → V} (hsame : SameF V cls F H τ) :
    StageCohF V m.acval env φ cls F H (completeF V m.acval env φ cls F H τ) := by
  refine ⟨fun c hc i ty hch hF a ha => ?_, fun c hc c' hc' i ty i' ty' hch hch' hF hs => ?_⟩
  · obtain ⟨i0, ty0, he, hlo0, hi⟩ := hhole c hc _ hch
    cases he
    have hval : completeF V m.acval env φ cls F H τ (H - 1 - i) = interp V τ a :=
      completeF_eq_of hu ⟨c, hc, i, ty, a, hch, hi, rfl, hF, ha, rfl⟩
    rw [hval]
    have hchs : c.hole.isSome := by rw [hch]; rfl
    have hF' : F (c.hole.getD default) = false := by rw [hch]; exact hF
    exact interp_congr_unmentioned m (hkf c hc hchs hF').1 ha
      (fun j _ hocc => (completeF_keep_of hu hhole (hkeyF c hc hchs hF' j hocc)).symm)
      (fun j hj => by
        refine (completeF_keep fun c2 _ i2 _ _ hi2 hpe => ?_).symm
        omega)
  · have hF' : F (.fvar i' ty') = true := by rw [← hFc c hc c' hc' _ _ hch hch' hs]; exact hF
    rw [completeF_keep_of hu hhole (Or.inr ⟨c, hc, ty, hch, hF⟩),
      completeF_keep_of hu hhole (Or.inr ⟨c', hc', ty', hch', hF'⟩)]
    exact hsame c hc c' hc' i ty i' ty' hch hch' hF hs

end Complete

end ConLeche.Model
