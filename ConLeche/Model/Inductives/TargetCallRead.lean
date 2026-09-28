module

public import ConLeche.Model.Inductives.TargetNodeRead
public import ConLeche.Model.Annot.BitSubstFvars
public import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Inductives.PosFieldLeaf
import ConLeche.Verify.Shift
import ConLeche.Verify.Subst

public section

/-!
# A call's readings through the walk's substitution

The call's tie (`callTie`, `TargetCallTie.lean`) says, syntactically, that
the callee's telescope and major are the walk's field telescope and leaf
under ONE parallel substitution of the walk's variables (`substFvars`).
This file reads that at the rule's frame: the call's telescope, read at the
rule's depth (`teleDoms`), is the walk's read at the walk's depth and
substituted (`teleDoms_substFvars`), and a spine fits the first at a
valuation exactly when it fits the second at the substituted valuation
(`spineFit_substAt`).  Hole-free readings do not see the holes' values
(`interp_holeFree`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A list substituted at rising cut-offs -/

/-- Entry `l` substituted at the cut `k + l` — a telescope's domains
through a parallel substitution. -/
@[expose] def substAt (τ : Nat → AnnotTerm) : Nat → List AnnotTerm → List AnnotTerm
  | _, [] => []
  | k, a :: as => AnnotTerm.substAV τ a k :: substAt τ (k + 1) as

/-- **A spine fits substituted domains exactly when it fits the domains at
the substituted valuation.** -/
theorem spineFit_substAt (τ : Nat → AnnotTerm) :
    ∀ (as : List AnnotTerm) (k : Nat) (σ : Nat → V) (bs : List V),
      SpineFit σ (substAt τ k as) bs ↔ SpineFit (substE V τ k σ) as bs
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | a :: as, k, σ, b :: bs => by
    simp only [substAt, SpineFit, interp_substAV]
    rw [cons_substE]
    exact and_congr Iff.rfl (spineFit_substAt τ as (k + 1) (cons b σ) bs)

/-! ## `fvarsBelow` through an opening -/

theorem fvarsBelow_instantiateList {D : Nat} :
    ∀ (os : List Expr), (∀ x ∈ os, Expr.fvarsBelow D x) →
      ∀ (e : Expr) (k : Nat), Expr.fvarsBelow D e → Expr.fvarsBelow D (e.instantiateList os k)
  | [], _, e, k, h => by rw [Expr.instantiateList_nil]; exact h
  | v :: vs, hos, e, k, h => by
    rw [Expr.instantiateList_cons]
    exact Expr.fvarsBelow_instantiate1_gen (hos v List.mem_cons_self) k
      (fvarsBelow_instantiateList vs (fun x hx => hos x (List.mem_cons_of_mem _ hx)) e (k + 1) h)

theorem LocList.fvarsBelow {B q : Nat} {os : List Expr} (h : LocList B q os) :
    ∀ x ∈ os, Expr.fvarsBelow (B + q) x := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨ty, hty⟩ := h.2 j (by rw [← h.1]; exact hj)
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hty
  rw [hty]
  show B + q - 1 - j < B + q
  have := h.1; omega

/-! ## A telescope read through a parallel substitution -/

variable {env : Env} {φ : Name → Nat}

/-- **A telescope erasure-equal to a substituted one reads as the
substituted reading**: opened at the rule's variables above `B`, entry
`l` reads as the walk's entry, opened at the walk's variables above `b`,
substituted at the cut `q + l`. -/
theorem teleDoms_substFvars (m : EnvModel V env) {b B : Nat} {s : Nat → Expr}
    {x : Nat → AnnotTerm}
    (hs : ∀ i, i < b → Expr.WScoped B (s i) ∧ (s i).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ B (s i) = some (x i)) :
    ∀ (tysR tysW : List Expr) (q : Nat) (osR osW : List Expr), LocList B q osR → LocList b q osW →
      tysR.length = tysW.length →
      (∀ (l : Nat) (tR tW : Expr), tysR[l]? = some tR → tysW[l]? = some tW →
        Expr.ErasedEq tR (Expr.substFvars b B s tW)) →
      (∀ tW ∈ tysW, Expr.fvarsBelow b tW) →
      teleDoms m.acval env φ B osR tysR
        = (teleDoms m.acval env φ b osW tysW).map (substAt (substTau b B x) q)
  | [], [], _, _, _, _, _, _, _, _ => by simp [teleDoms, substAt]
  | [], _ :: _, _, _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, hl, _, _ => by simp at hl
  | tR :: tysR, tW :: tysW, q, osR, osW, hR, hW, hl, hE, hfb => by
    have hq1 : osR.length = q := hR.1
    have hq2 : osW.length = q := hW.1
    have hsb : ∀ v, v < b → (s v).looseBVarsBounded 0 = true := fun v hv => (hs v hv).2.1
    -- the head entry
    have hE0 : Expr.ErasedEq (tR.instantiateList osR 0)
        (Expr.substFvars b B s (tW.instantiateList osW 0)) :=
      (erasedEq_instantiateList osR 0 (hE 0 tR tW rfl rfl)).trans
        (Expr.substFvars_instantiateList hsb q osW osR hq2 hq1
          (fun j hj => by
            obtain ⟨ty, h1⟩ := hW.2 j hj
            obtain ⟨ty', h2⟩ := hR.2 j hj
            exact ⟨ty, ty', h1, h2⟩) tW 0)
    have hfbW : Expr.fvarsBelow (b + q) (tW.instantiateList osW 0) :=
      fvarsBelow_instantiateList osW (by simpa using hW.fvarsBelow) tW 0
        (Expr.fvarsBelow_mono (Nat.le_add_right b q) (hfb tW List.mem_cons_self))
    have hread : denoteMeta m.acval env φ (B + q) (tR.instantiateList osR 0)
        = (denoteMeta m.acval env φ (b + q) (tW.instantiateList osW 0)).map
            (AnnotTerm.substAV (substTau b B x) · q) := by
      rw [denoteMeta_erasedEq hE0]
      exact denoteMeta_substFvars m hs _ q hfbW
    -- the rest, one binder down
    have ih := teleDoms_substFvars m hs tysR tysW (q + 1)
      (.fvar (B + q) (tR.instantiateList osR 0) :: osR)
      (.fvar (b + q) (tW.instantiateList osW 0) :: osW) (hR.cons _) (hW.cons _)
      (by simpa using hl) (fun l t1 t2 h1 h2 => hE (l + 1) t1 t2 (by simpa using h1)
        (by simpa using h2)) (fun t ht => hfb t (List.mem_cons_of_mem _ ht))
    simp only [teleDoms, hq1, hq2]
    rw [hread, ih]
    cases denoteMeta m.acval env φ (b + q) (tW.instantiateList osW 0) with
    | none => rfl
    | some a =>
      cases teleDoms m.acval env φ b (.fvar (b + q) (tW.instantiateList osW 0) :: osW) tysW with
      | none => rfl
      | some r => rfl

/-! ## Hole-free readings, at `fvarsBelow` scoping -/

section HoleFree

variable {m : EnvModel V env}

/-- Opening at variables that are no holes changes no occurrence. -/
theorem nestOcc_instantiateList_locList {names : List Name} {lo hi D : Nat} (hD : hi ≤ D) :
    ∀ (q : Nat) (os : List Expr), LocList D q os → ∀ (e : Expr) (k : Nat),
      (e.instantiateList os k).nestOcc names lo hi = e.nestOcc names lo hi
  | 0, os, h, e, k => by
    obtain rfl : os = [] := List.length_eq_zero_iff.mp h.1
    rw [Expr.instantiateList_nil]
  | q + 1, os, h, e, k => by
    obtain ⟨o, os', rfl⟩ : ∃ o os', os = o :: os' := by
      cases os with
      | nil => exact absurd h.1 (by simp)
      | cons o os' => exact ⟨o, os', rfl⟩
    obtain ⟨ty, hty⟩ := h.2 0 (by omega)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hty
    subst hty
    have h' : LocList D q os' := by
      refine ⟨by have := h.1; simp at this; omega, fun j hj => ?_⟩
      obtain ⟨ty', hty'⟩ := h.2 (j + 1) (by omega)
      refine ⟨ty', ?_⟩
      simp only [List.getElem?_cons_succ] at hty'
      rw [hty']
      congr 2
      omega
    rw [Expr.instantiateList_cons, nestOcc_instantiate1_fvar (by omega),
      nestOcc_instantiateList_locList hD q os' h' e (k + 1)]

/-- **A hole-free term reads alike at two valuations agreeing off the
holes**, opened at non-hole variables. -/
theorem interp_holeFree {names : List Name} {lo hi : Nat} {d : Nat} {e : Expr} {ea : AnnotTerm}
    (hfb : Expr.fvarsBelow d e) (hd : hi ≤ d) (hocc : e.nestOcc names lo hi = false)
    (hea : denoteMeta m.acval env φ d e = some ea) {σ σ' : Nat → V}
    (hag : AgreeOff (holeP d lo hi) σ σ') : interp V σ ea = interp V σ' ea :=
  interp_congr_noBVar ea (denoteMeta_noBVar_of_nestOcc' d e hfb hd hocc hea) hag

omit [SetTheory V] in
theorem agreeOff_holeP_cons {d lo hi : Nat} {σ σ' : Nat → V} (h : AgreeOff (holeP d lo hi) σ σ')
    (x : V) : AgreeOff (holeP (d + 1) lo hi) (cons x σ) (cons x σ') :=
  fun i hi' => agreeOff_cons h x i fun hs => hi' (holeP_succ i hs)

omit [SetTheory V] in
theorem agreeOff_holeP_consList {lo hi : Nat} :
    ∀ (as : List V) {d : Nat} {σ σ' : Nat → V}, AgreeOff (holeP d lo hi) σ σ' →
      AgreeOff (holeP (d + as.length) lo hi) (consList as σ) (consList as σ')
  | [], _, _, _, h => h
  | a :: as, d, _, _, h => by
    rw [consList_cons, consList_cons, List.length_cons, show d + (as.length + 1)
      = (d + 1) + as.length by omega]
    exact agreeOff_holeP_consList as (agreeOff_holeP_cons h a)

/-- **A hole-free telescope fits the same spines at two valuations
agreeing off the holes.** -/
theorem spineFit_teleDoms_holeFree {names : List Name} {lo hi D : Nat} (hD : hi ≤ D) :
    ∀ (tys : List Expr) (q : Nat) (os : List Expr) (ds : List AnnotTerm),
      LocList D q os → teleDoms m.acval env φ D os tys = some ds →
      (∀ t ∈ tys, t.nestOcc names lo hi = false ∧ Expr.fvarsBelow D t) →
      ∀ {σ σ' : Nat → V}, AgreeOff (holeP (D + q) lo hi) σ σ' →
      ∀ bs : List V, SpineFit σ ds bs ↔ SpineFit σ' ds bs
  | [], q, os, ds, _, h, _, _, _, _, bs => by
    simp only [teleDoms, Option.some.injEq] at h; subst h
    cases bs <;> exact Iff.rfl
  | t :: tys, q, os, ds, hos, h, hall, σ, σ', hag, bs => by
    have hq : os.length = q := hos.1
    simp only [teleDoms, hq] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure, Option.some.injEq] at h
    subst h
    obtain ⟨hocc, hfb⟩ := hall t List.mem_cons_self
    have hfbO : Expr.fvarsBelow (D + q) (t.instantiateList os 0) :=
      fvarsBelow_instantiateList os (by simpa using hos.fvarsBelow) t 0
        (Expr.fvarsBelow_mono (Nat.le_add_right D q) hfb)
    have hoccO : (t.instantiateList os 0).nestOcc names lo hi = false := by
      rw [nestOcc_instantiateList_locList hD q os hos t 0]; exact hocc
    have heq := interp_holeFree hfbO (by omega) hoccO ha hag
    cases bs with
    | nil => exact Iff.rfl
    | cons b bs =>
      simp only [SpineFit]
      rw [heq]
      exact and_congr Iff.rfl (spineFit_teleDoms_holeFree hD tys (q + 1) _ r (hos.cons _) hr
        (fun t' ht' => hall t' (List.mem_cons_of_mem _ ht'))
        (by rw [show D + (q + 1) = D + q + 1 by omega]; exact agreeOff_holeP_cons hag b) bs)

end HoleFree

end ConLeche.Model
