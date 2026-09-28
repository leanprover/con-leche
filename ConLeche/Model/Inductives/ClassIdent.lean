module

public import ConLeche.Model.Inductives.ClassStageF
public import ConLeche.Model.Annot.BitSubstFvars

public section

/-!
# The identification: a class's crest reads as its container's recorded clause (P2d, I2)

The class check's commutation equation (`classCommutes`,
DESIGN CLASSCHECK / P2D3) says two SUBSTITUTION INSTANCES are equal up to
the free variables' annotations: the crest with its stage classes
abstracted, its group holes written back as placeholder members applied
to the key's free-hole form `dsF`; and the container's canonical text
(what the recorded clause reads), its parameters `dsF`, its members the
placeholders.  Read, both sides are substitutions of their readings
(`denoteMeta_replaceFVars`), so the crest reads as the recorded text at
the valuation holding the key's free-hole form and, at each member slot,
the value the group hole holds applied back — no induction over terms.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ClassInfo)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## 1. A replacement of free variables, read -/

/-- **A replacement of free variables reads as the parallel substitution
of its readings**: `e` scoped below `b`, every replaced variable's term
(an unreplaced one standing for itself) scoped at `D`, closed, and read. -/
theorem denoteMeta_replaceFVars (m : EnvModel V env) {b D : Nat} {g : Nat → Option Expr}
    {x : Nat → AnnotTerm}
    (hg : ∀ i, i < b → Expr.fvarsBelow D ((g i).getD (.fvar i (.sort .zero))) ∧
      ((g i).getD (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ D ((g i).getD (.fvar i (.sort .zero))) = some (x i))
    {e : Expr} (he : Expr.fvarsBelow b e) :
    denoteMeta m.acval env φ D (e.replaceFVars g)
      = (denoteMeta m.acval env φ b e).map (AnnotTerm.substAV (substTau b D x) · 0) := by
  let s : Nat → Expr := fun i => ((g i).getD (.fvar i (.sort .zero))).eraseFVarTys
  have hE : Expr.ErasedEq (e.replaceFVars g) (Expr.substFvars b D s e) := by
    refine Expr.replaceFVars_erasedEq_substFvars (fun v hv ty => ?_) e he
    cases hgv : g v with
    | none =>
      simp only [Option.getD_none, s, hgv, Expr.eraseFVarTys, Expr.replaceFVars, Option.getD_some]
      exact rfl
    | some t =>
      simp only [Option.getD_some, s, hgv]
      exact Expr.erasedEq_eraseFVarTys t
  rw [denoteMeta_semEq (Expr.semEq_of_erasedEq hE)]
  have hs : ∀ i, i < b → Expr.WScoped D (s i) ∧ (s i).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ D (s i) = some (x i) := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hg i hi
    have hsem : Expr.SemEq ((g i).getD (.fvar i (.sort .zero))) (s i) :=
      Expr.semEq_of_erasedEq (Expr.erasedEq_eraseFVarTys _)
    refine ⟨Expr.wscoped_eraseFVarTys h1, ?_, ?_⟩
    · rw [← Expr.SemEq.looseBVarsBounded hsem 0]; exact h2
    · rw [← denoteMeta_semEq hsem]; exact h3
  have := denoteMeta_substFvars (φ := φ) m hs e 0 (by simpa using he)
  simpa using this

/-! ## 2. The commutation equation, read -/

/-- **Two substitution instances equal up to annotations read as equal
substitutions of their readings** — the commutation equation's reading:
`L` (the crest, stage classes abstracted) below `H` and `A` (the canonical
text) below `b`, each replaced into depth `D`. -/
theorem substRead_eq (m : EnvModel V env) {H b D : Nat} {L A : Expr} {gL gR : Nat → Option Expr}
    {xL xR : Nat → AnnotTerm}
    (hgL : ∀ i, i < H → Expr.fvarsBelow D ((gL i).getD (.fvar i (.sort .zero))) ∧
      ((gL i).getD (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ D ((gL i).getD (.fvar i (.sort .zero))) = some (xL i))
    (hgR : ∀ i, i < b → Expr.fvarsBelow D ((gR i).getD (.fvar i (.sort .zero))) ∧
      ((gR i).getD (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ D ((gR i).getD (.fvar i (.sort .zero))) = some (xR i))
    (hL : Expr.fvarsBelow H L) (hA : Expr.fvarsBelow b A)
    (heq : (L.replaceFVars gL).eraseFVarTys = (A.replaceFVars gR).eraseFVarTys)
    {aL aA : AnnotTerm} (haL : denoteMeta m.acval env φ H L = some aL)
    (haA : denoteMeta m.acval env φ b A = some aA) :
    AnnotTerm.substAV (substTau H D xL) aL 0 = AnnotTerm.substAV (substTau b D xR) aA 0 := by
  have h1 := denoteMeta_replaceFVars (φ := φ) m hgL hL
  have h2 := denoteMeta_replaceFVars (φ := φ) m hgR hA
  rw [haL, Option.map_some] at h1
  rw [haA, Option.map_some] at h2
  have hsem : Expr.SemEq (L.replaceFVars gL) (A.replaceFVars gR) :=
    Expr.semEq_of_erasedEq ((Expr.erasedEq_of_eraseFVarTys heq))
  rw [denoteMeta_semEq hsem, h2] at h1
  exact (Option.some.inj h1).symm

/-! ## 3. Agreement of Π-towers, field by field -/

section Tele

variable {acval : Name → (Name → Nat) → AnnotTerm}

theorem obind2 {α β γ : Type} {x : Option α} {y : Option β} {f : α → β → γ} {c : γ}
    (h : (do let a ← x; let b ← y; some (f a b)) = some c) :
    ∃ a b, x = some a ∧ y = some b ∧ f a b = c := by
  cases x <;> cases y <;> simp_all

set_option maxHeartbeats 1600000 in
/-- **Two transforms of a Π-tower that agree on every opened subterm fit
the same spines**: `f`, `g` commute with `Π` and create none; if every
term's `f`- and `g`-images read alike at every admissible valuation (any
number of opened locals), the readings' telescopes fit the same spines
there. -/
theorem teleAgree_spineFit {H : Nat} {Good : (Nat → V) → Prop} {f g : Expr → Expr}
    (hf : ∀ t b m, f (.forallE t b m) = .forallE (f t) (f b) m)
    (hg : ∀ t b m, g (.forallE t b m) = .forallE (g t) (g b) m)
    (hfn : ∀ X, (∀ t b m, X ≠ .forallE t b m) → ∀ d as, LocList H d as →
      ∀ a, denoteMeta acval env φ (H + d) ((f X).instantiateList as 0) = some a →
        ∀ n bm A B, a ≠ .pi n bm A B)
    (hag : ∀ (e : Expr) (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
      OptAgree (ValAgree V Good d)
        (denoteMeta acval env φ (H + d) ((f e).instantiateList as2 0))
        (denoteMeta acval env φ (H + d) ((g e).instantiateList as1 0))) :
    ∀ (ab1 : List (Nat × Nat × AnnotTerm)) (X : Expr) (d : Nat) (as2 as1 : List Expr),
      LocList H d as2 → LocList H d as1 → ∀ (ab2 : List (Nat × Nat × AnnotTerm)) (r1 r2 : AnnotTerm),
      denoteMeta acval env φ (H + d) ((f X).instantiateList as2 0) = some (mkPisAV ab1 r1) →
      denoteMeta acval env φ (H + d) ((g X).instantiateList as1 0) = some (mkPisAV ab2 r2) →
      ab1.length = ab2.length → ∀ τ, Good τ → ∀ vals : List V, vals.length = d →
      ∀ fs : List V, SpineFit (consList vals τ) (ab1.map (·.2.2)) fs ↔
        SpineFit (consList vals τ) (ab2.map (·.2.2)) fs
  | [], _, _, _, _, _, _, ab2, _, _, _, _, hl, _, _, _, _, fs => by
    cases ab2 with
    | nil => exact Iff.rfl
    | cons _ _ => simp at hl
  | e1 :: ab1, X, d, as2, as1, h2, h1, ab2, r1, r2, hX1, hX2, hl, τ, hτ, vals, hvl, fs => by
    cases ab2 with
    | nil => simp at hl
    | cons e2 ab2 =>
    by_cases hXp : ∃ t b m, X = .forallE t b m
    · obtain ⟨t, b, m, rfl⟩ := hXp
      rw [hf] at hX1
      rw [hg] at hX2
      simp only [Expr.instantiateList] at hX1 hX2
      rw [denoteMeta_forallE] at hX1 hX2
      obtain ⟨ta1, ba1, hta1, hba1, hP1⟩ := obind2 hX1
      obtain ⟨ta2, ba2, hta2, hba2, hP2⟩ := obind2 hX2
      have hT := hag t d as2 as1 h2 h1
      rw [hta1, hta2] at hT
      rw [← Expr.instantiateList_cons] at hba1 hba2
      simp only [mkPisAV] at hP1 hP2
      injection hP1 with _ _ hta1' hba1'
      injection hP2 with _ _ hta2' hba2'
      subst hta1' hta2'
      simp only [List.map_cons]
      cases fs with
      | nil => simp [SpineFit]
      | cons x fs =>
        simp only [SpineFit]
        rw [hT vals τ hvl hτ]
        refine and_congr_right fun _ => ?_
        have hrec := teleAgree_spineFit hf hg hfn hag ab1 b (d + 1) _ _
          (h2.cons ((f t).instantiateList as2 0)) (h1.cons ((g t).instantiateList as1 0)) ab2 r1 r2
          (by rw [show H + (d + 1) = H + d + 1 by omega, hba1, hba1'])
          (by rw [show H + (d + 1) = H + d + 1 by omega, hba2, hba2'])
          (by simpa using hl) τ hτ (vals ++ [x]) (by simp [hvl]) fs
        simpa [consList_append] using hrec
    · exfalso
      have hXn : ∀ t b m, X ≠ .forallE t b m := fun t b m h => hXp ⟨t, b, m, h⟩
      exact hfn X hXn d as2 h2 _ hX1 _ _ _ _ rfl

end Tele

end ConLeche.Model
