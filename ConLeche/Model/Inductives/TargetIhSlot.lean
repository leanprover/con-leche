module

import ConLeche.Verify.Leaves
import ConLeche.Verify.InferLeaves
public import ConLeche.Verify.Inductives.RecCheckRun
public import ConLeche.Model.Inductives.TargetRecRead
import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.Rules.Bridge

public section

/-!
# The `ih` slots of the residue's context

The residue of a target-checked rule is typed in a context whose last
`ihs.size` slots are the `ih` variables, at their `ih` types
`∀ a⃗ : A⃗, c x⃗ e⃗ (f a⃗)` (`targetIhTy`).  The model reads that context at
the rule's frame extended by the `ih` VALUES — the readings of the calls'
λs (`targetCallE`), at the callees' values — so each slot owes two facts:

* its type's reading is GRADED at every valuation of the frame, and
* the call's value LIES in it.

Both are the kernel's (`targetCallOk`, K1 + K3): the `ih` type was
inferred at the frame (`TargetCallRun.hihTy`: `InferClaim` grades its
reading), the call's λ was inferred one slot deeper, the callee a variable
of its stored type (`hcall`: the value lies in the inferred type), and the
two types were compared (`hcallEq`: `DefEqClaim` equates their readings).
No field classification and no syntactic computation of the λ's type.

`targetCall_ihSlot` states them at a frame whose context is a `WalkCtx`;
`walkCtx_consLifted` is the one-slot step of the residue context's entry
(`targetRuleBodyEq`'s `hW`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal CheckMode)

universe uv

variable {V : Type uv} [SetTheory V] {μ : CheckMode}

/-! ## The residue's context, slot by slot -/

/-- A leaf of a frame-listed term lies below the frame. -/
theorem leaf_lt_of_mem {B : Nat} {L : List Expr} (hL : FvarList B L) {ty : Expr}
    (hlT : ∀ l ∈ ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ L) : ∀ l ∈ ty.fvarLeaves, l.1 < B := by
  intro l hl
  have h := hL.2.2 _ (hlT l hl)
  simp only [Expr.WScoped] at h
  exact h.1

/-- **One slot on top of `n` earlier ones**: a type whose leaves are the
frame's, read at the frame to a reading graded under the frame's context,
opens a slot at depth `B + n` whose domain is that reading lifted past the
`n` earlier slots, and a value of the frame-level reading fills it. -/
theorem walkCtx_consLifted {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    {B n : Nat} {Li L : List Expr} (hL : FvarList B L) {Δi Δ : List AnnotTerm} {vs : List V}
    {ρ : Nat → V}
    (hW : WalkCtx V mT φ (B + n) (consList vs ρ) (Δi ++ Δ) (Li ++ L))
    (hn : Δi.length = n) (hvs : vs.length = n)
    {ty : Expr} (hlT : ∀ l ∈ ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    (hbT : ty.looseBVarsBounded 0 = true) (hcbT : ConstsBound envT ty)
    {T : AnnotTerm} (hT : denoteMeta mT.acval envT φ B ty = some T)
    (hGT : ∀ σ : Nat → V, Sat V Δ σ → WellDenotedV V σ T)
    {v : V} (hv : v ∈ˢ interp V ρ T) :
    WalkCtx V mT φ (B + n + 1) (cons v (consList vs ρ)) (T.liftN n 0 :: (Δi ++ Δ))
      (Expr.fvar (B + n) ty :: (Li ++ L)) := by
  have hta : denoteMeta mT.acval envT φ (B + n) ty = some (T.liftN n 0) := by
    have hd := denoteMeta_open_deepen (acval := mT.acval) (env := envT) (φ := φ) hacl n B
      ty 0 [] [] (leaf_lt_of_mem hL hlT) (LocList.nil B) (LocList.nil (B + n))
    simp only [ConLeche.Expr.instantiateList_nil, Nat.add_zero] at hd
    rw [hd, hT]; rfl
  refine hW.cons hta hbT hcbT (fun l hl => List.mem_append_right _ (hlT l hl)) ?_ ?_
  · intro σ hσ
    rw [WellDenotedV_liftN, shiftE_zero]
    have h := Sat_drop hσ n
    rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
      List.nil_append] at h
    exact hGT _ h
  · rw [← hvs, interp_liftN_consList]
    exact hv

/-- The `ih` slots' domains: entry `r`'s frame-level reading, lifted past
the `r` slots before it. -/
@[expose] def ihDomsLifted (Ts : List AnnotTerm) : List AnnotTerm :=
  (List.range Ts.length).map fun r => (Ts.getD r default).liftN r 0

/-- The `ih` variables: entry `r` at `B + r`. -/
@[expose] def ihFvarsAt (B : Nat) (tys : List Expr) : List Expr :=
  (List.range tys.length).map fun r => Expr.fvar (B + r) (tys.getD r default)

/-- **The residue's context at the rule's entry**: the frame's context
with every `ih` slot on top — each `ih` type read at the frame, graded
there, and filled by its value. -/
theorem walkCtx_ihs {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    {B : Nat} {L : List Expr} (hL : FvarList B L) {Δ : List AnnotTerm} {ρ : Nat → V}
    (hW : WalkCtx V mT φ B ρ Δ L)
    (tys : List Expr) (Ts : List AnnotTerm) (vals : List V)
    (hlen1 : tys.length = Ts.length) (hlen2 : vals.length = Ts.length)
    (hslot : ∀ r, r < Ts.length →
      (∀ l ∈ (tys.getD r default).fvarLeaves, Expr.fvar l.1 l.2 ∈ L) ∧
      (tys.getD r default).looseBVarsBounded 0 = true ∧
      ConstsBound envT (tys.getD r default) ∧
      denoteMeta mT.acval envT φ B (tys.getD r default) = some (Ts.getD r default) ∧
      (∀ σ : Nat → V, Sat V Δ σ → WellDenotedV V σ (Ts.getD r default)) ∧
      vals.getD r pt ∈ˢ interp V ρ (Ts.getD r default)) :
    WalkCtx V mT φ (B + Ts.length) (consList vals ρ) ((ihDomsLifted Ts).reverse ++ Δ)
      ((ihFvarsAt B tys).reverse ++ L) := by
  suffices key : ∀ n, n ≤ Ts.length →
      WalkCtx V mT φ (B + n) (consList (vals.take n) ρ)
        (((List.range n).map fun r => (Ts.getD r default).liftN r 0).reverse ++ Δ)
        (((List.range n).map fun r => Expr.fvar (B + r) (tys.getD r default)).reverse ++ L) by
    have h := key Ts.length (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega), show (List.range Ts.length).map
      (fun r => Expr.fvar (B + r) (tys.getD r default)) = ihFvarsAt B tys by
        rw [ihFvarsAt, hlen1]] at h
  intro n
  induction n with
  | zero => intro _; simpa using hW
  | succ n ih =>
    intro hn
    have hW' := ih (by omega)
    obtain ⟨hlT, hbT, hcbT, hT, hGT, hv⟩ := hslot n (by omega)
    have hlenΔ : ((List.range n).map fun r => (Ts.getD r default).liftN r 0).reverse.length = n := by
      simp
    have hlenV : (vals.take n).length = n := by rw [List.length_take]; omega
    have h := walkCtx_consLifted hacl hL hW' hlenΔ hlenV hlT hbT hcbT hT hGT hv
    have hvals : vals.take (n + 1) = vals.take n ++ [vals.getD n pt] := by
      rw [List.take_add_one, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show n < vals.length by omega)]
      rfl
    rw [hvals, consList_append]
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append] at h ⊢
    rw [show B + (n + 1) = B + n + 1 from by omega]
    exact h

/-! ## The residue's context at a target rule's entry -/

/-! ## The `ih` types' and the calls' scoping, from the run -/

/-- An opened sub-term's constants are the term's. -/
theorem constsBound_of_instantiate1 {env₀ : Env} {v : Expr} :
    ∀ (e : Expr) (k : Nat), ConstsBound env₀ (e.instantiate1 v k) → ConstsBound env₀ e := by
  intro e
  induction e with
  | bvar i => intro _ _; simp
  | fvar i ty _ => intro k h; simpa [Expr.instantiate1] using h
  | sort u => intro _ _; simp
  | lit l => intro _ _; simp
  | const n us => intro k h; simpa [Expr.instantiate1] using h
  | app f a ihf iha =>
    intro k h; simp only [Expr.instantiate1, constsBound_app] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b m iht ihb =>
    intro k h; simp only [Expr.instantiate1, constsBound_lam] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m iht ihb =>
    intro k h; simp only [Expr.instantiate1, constsBound_forallE] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v' b iht ihv ihb =>
    intro k h; simp only [Expr.instantiate1, constsBound_letE] at h ⊢
    exact ⟨iht k h.1, ihv k h.2.1, ihb (k + 1) h.2.2⟩
  | proj s i x ih =>
    intro k h; simp only [Expr.instantiate1, constsBound_proj] at h ⊢
    exact ih k h

/-- **A term inferred at the certified grade names only stored
constants**, once its free variables' annotations do. -/
theorem infer_constsBound_of_full {env : Env} :
    ∀ {g : Rules.Grade} {d : Nat} {e t : Expr}, Rules.Infer env g d e t → g = .full →
      (∀ l ∈ e.fvarLeaves, ConstsBound env l.2) → ConstsBound env e
  | _, _, _, _, .sort, _, _ => by simp
  | _, _, _, _, @Rules.Infer.fvar _ _ _ idx ty _, _, hl => by
    simp only [constsBound_fvar]
    exact hl (idx, ty) (by simp [Expr.fvarLeaves])
  | _, _, _, _, .const hf _ _, _, _ => by simp [hf]
  | _, _, _, _, .natLit _, _, _ => by simp
  | _, _, _, _, .strLit _, _, _ => by simp
  | _, _, _, _, .forallE hs _ hbs _ _, hg, hl => by
    have hty := infer_constsBound_of_full hs hg (fun l h => hl l (by simp [Expr.fvarLeaves, h]))
    simp only [constsBound_forallE]
    refine ⟨hty, constsBound_of_instantiate1 _ 0 (infer_constsBound_of_full hbs hg ?_)⟩
    intro l h
    rcases ConLeche.Expr.fvarLeaves_instantiate1 _ 0 h with h' | h'
    · exact hl l (by simp [Expr.fvarLeaves, h'])
    · simp only [Expr.fvarLeaves, List.mem_cons] at h'
      rcases h' with rfl | h'
      · exact hty
      · exact hl l (by simp [Expr.fvarLeaves, h'])
  | _, _, _, _, .lam hs _ hbt _ _ _ _, hg, hl => by
    have hty := infer_constsBound_of_full (hs hg) rfl
      (fun l h => hl l (by simp [Expr.fvarLeaves, h]))
    simp only [constsBound_lam]
    refine ⟨hty, constsBound_of_instantiate1 _ 0 (infer_constsBound_of_full hbt hg ?_)⟩
    intro l h
    rcases ConLeche.Expr.fvarLeaves_instantiate1 _ 0 h with h' | h'
    · exact hl l (by simp [Expr.fvarLeaves, h'])
    · simp only [Expr.fvarLeaves, List.mem_cons] at h'
      rcases h' with rfl | h'
      · exact hty
      · exact hl l (by simp [Expr.fvarLeaves, h'])
  | _, _, _, _, .app hf _ ha _, hg, hl => by
    simp only [constsBound_app]
    exact ⟨infer_constsBound_of_full hf hg (fun l h => hl l (by simp [Expr.fvarLeaves, h])),
      infer_constsBound_of_full ha hg (fun l h => hl l (by simp [Expr.fvarLeaves, h]))⟩
  | _, _, _, _, .appSkip .., hg, _ => nomatch hg
  | _, _, _, _, .proj hp .., hg, hl => by
    simp only [constsBound_proj]
    exact infer_constsBound_of_full hp hg (fun l h => hl l (by simpa [Expr.fvarLeaves] using h))

/-- An entry of an opener list is a free variable. -/
theorem FvarList.mem_fvar {E : Nat} {xs : List Expr} (h : FvarList E xs) {x : Expr}
    (hx : x ∈ xs) : ∃ i ty, x = Expr.fvar i ty := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
  have hjl : j < E := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    rw [h.1] at this; exact this
  obtain ⟨ty, hty⟩ := h.2.1 j hjl
  rw [hj] at hty
  exact ⟨_, _, Option.some.inj hty⟩

theorem fvarLeaves_default : (default : Expr).fvarLeaves = [] := by
  have h : (default : Expr) = .bvar default := rfl
  rw [h]; simp [Expr.fvarLeaves]

end ConLeche.Model
