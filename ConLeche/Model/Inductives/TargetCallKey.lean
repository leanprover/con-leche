module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.TargetCallGen
import ConLeche.Model.Inductives.TargetResidue
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Annot.BitClosed
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Model.Inductives.BlockRecOpenerRead
import ConLeche.Verify.InferLeaves
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.WellDenotedTransport
import ConLeche.Semantics.Kit

public section

/-!
# One `ih` key of a target rule, read

What the graph kit's two `ih` rows read at the target data, per key
`r` of the `(c, j)`-th rule: the callee is a position of the family
sharing the rule's prefix; the key's telescope carries the family's
elimination bit; and the `ih` variable's domain (its `ih` type's
reading) is the Π-tower over the key's telescope whose body reads, at
every spine of it, the callee's conclusion at the call's spine (the
prefix, the index readings and the applied field) — the `ih` type is
the callee's stored type peeled at the call's arguments (`targetIhTy`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **A λ-tower over binder data is a λ reading**: the semantic tower at
one frame and the reading of `mkLamsAV` at another agree when the bits'
zeroness is the tower's, the domains agree at every partial spine, and
the bodies agree at every fitting spine. -/
theorem lamTowerA_eq_mkLamsAV {m : Nat} {g : List V → (Nat → V) → V} {b : AnnotTerm} :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (ds : List (Nat × AnnotTerm)) (ρ1 ρ2 : Nat → V)
      (acc : List V), tl.length = ds.length → (∀ d ∈ ds, (m = 0 ↔ d.1 = 0)) →
      (∀ bs : List V, bs.length < tl.length →
        interp V (consList bs ρ1) (tl.getD bs.length default).2.2
          = interp V (consList bs ρ2) (ds.getD bs.length default).2) →
      (∀ bs : List V, SpineFit ρ1 (tl.map (·.2.2)) bs →
        g (acc ++ bs) (consList bs ρ1) = interp V (consList bs ρ2) b) →
      lamTowerA m ρ1 acc tl g = interp V ρ2 (mkLamsAV ds b)
  | [], [], ρ1, ρ2, acc, _, _, _, hbody => by
    have := hbody [] trivial
    simpa [lamTowerA, mkLamsAV] using this
  | [], _ :: _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _, _, _ => by simp at hl
  | d :: tl, e :: ds, ρ1, ρ2, acc, hl, hz, hdom, hbody => by
    have hd0 : interp V ρ1 d.2.2 = interp V ρ2 e.2 := by simpa using hdom [] (by simp)
    show lamR m (interp V ρ1 d.2.2) (fun a => lamTowerA m (cons a ρ1) (acc ++ [a]) tl g)
      = interp V ρ2 (.lam e.1 e.2 (mkLamsAV ds b))
    rw [interp_lam, hd0]
    refine lamR_zero_agree (hz e List.mem_cons_self) fun a ha => ?_
    refine lamTowerA_eq_mkLamsAV tl ds (cons a ρ1) (cons a ρ2) (acc ++ [a]) (by simpa using hl)
      (fun d' hd' => hz d' (List.mem_cons_of_mem _ hd')) (fun bs hbs => ?_) (fun bs hbs => ?_)
    · have := hdom (a :: bs) (by simp; omega)
      simpa using this
    · have := hbody (a :: bs) ⟨by rw [← hd0] at ha; exact ha, hbs⟩
      simpa [List.append_assoc] using this

omit [SetTheory V] in
theorem liftAt_getD (n : Nat) :
    ∀ (k : Nat) (ds : List AnnotTerm) (i : Nat), i < ds.length →
      (liftAt n k ds).getD i default = (ds.getD i default).liftN n (k + i)
  | _, [], _, h => absurd h (by simp)
  | k, t :: ts, 0, _ => by simp [liftAt]
  | k, t :: ts, i + 1, h => by
    simp only [liftAt, List.getD_cons_succ]
    rw [liftAt_getD n (k + 1) ts i (by simpa using h), show k + 1 + i = k + (i + 1) by omega]

omit [SetTheory V] in
theorem liftAt_length (n : Nat) : ∀ (k : Nat) (ds : List AnnotTerm), (liftAt n k ds).length = ds.length
  | _, [] => rfl
  | k, _ :: ts => by simp [liftAt, liftAt_length n (k + 1) ts]

section Key

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {envI : Env}

omit [SetTheory V] in
theorem locOpen_eq_openFvars (B m : Nat) : locOpen B m = (openFvars B m).reverse := by
  apply List.ext_getElem? 
  intro j
  rcases Nat.lt_or_ge j m with hj | hj
  · rw [List.getElem?_reverse (by simpa using hj), openFvars_length,
      openFvars_getElem? (by omega)]
    simp [locOpen, List.getElem?_range hj]
    omega
  · rw [List.getElem?_eq_none (by simp [locOpen]; omega),
      List.getElem?_eq_none (by simp; omega)]

omit [SetTheory V] in
theorem mkPisOf_fvarLeaves_body :
    ∀ (bs : List (Expr × ConLeche.BinderMeta)) (X : Expr), ∀ l ∈ X.fvarLeaves,
      l ∈ (Expr.mkPisOf bs X).fvarLeaves
  | [], _, _, hl => hl
  | (ty, mt) :: bs, X, l, hl => by
    simp only [Expr.mkPisOf, Expr.fvarLeaves, List.mem_append]
    exact Or.inr (mkPisOf_fvarLeaves_body bs X l hl)

omit [SetTheory V] in
theorem mem_locOpen {B m : Nat} {x : Expr} (hx : x ∈ locOpen B m) :
    ∃ j, j < m ∧ x = Expr.fvar (B + m - 1 - j) (.sort .zero) := by
  simp only [locOpen, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact ⟨j, hj, rfl⟩

omit [SetTheory V] in
/-- Subjects that read make a read spine. -/
theorem denoteMetaSpine_of_reads {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {D : Nat} :
    ∀ (es : List Expr), (∀ e ∈ es, ∃ a, denoteMeta acval env φ D e = some a) →
      ∃ vs, DenoteMetaSpine acval env φ D es vs
  | [], _ => ⟨[], .nil⟩
  | e :: es, h => by
    obtain ⟨a, ha⟩ := h e List.mem_cons_self
    obtain ⟨vs, hvs⟩ := denoteMetaSpine_of_reads es fun e' he' => h e' (List.mem_cons_of_mem _ he')
    exact ⟨a :: vs, .cons ha hvs⟩

end Key

end ConLeche.Model
