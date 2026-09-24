module

public import ConLeche.Verify.Inductives.RecCheckRun
public import ConLeche.Model.Inductives.TargetRecRead
import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.Leaves
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Rules.Bridge

public section

/-!
# The `ih` slots of the residue's context (lane RECLIB, B3 (b))

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
`walkCtx_consIh` is the one-slot step of the residue context's entry
(`targetRuleBodyEq`'s `hW`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal CheckMode TargetIh TargetFamily)

universe uv

variable {V : Type uv} [SetTheory V] {μ : CheckMode}

/-- The call's λ as `targetCallOk` infers it, at the run's own frame
data (`TargetCallRun.hcall`'s subject). -/
@[expose] def targetCallLam (fam : TargetFamily) (fvsPref fvsF : List Expr)
    (teles : List (List (Expr × ConLeche.BinderMeta))) (B : Nat) (pw : ConLeche.PropWhen)
    (ih : TargetIh) : Expr :=
  Expr.mkLamsOf ((teles.getD ih.field []).map fun b => (b.1, ⟨pw⟩))
    (Expr.mkAppN (.fvar B (fam.recTys.getD ih.callee (.sort .zero)))
      (fvsPref ++ ih.idx ++
        [Expr.mkAppN (fvsF.getD ih.field default)
          (ConLeche.structTeleVars (teles.getD ih.field []).length)]))

set_option maxHeartbeats 1000000 in
/-- **One `ih` slot, from the call's typing run.**  At a frame of width
`B` whose context the walk carries (`hW`), and a value `x` of the
callee's stored type: the `ih` type reads at the frame, its reading is
graded, the call's λ reads one slot deeper (the callee's), and the λ's
value at `x` lies in the `ih` type's reading. -/
theorem targetCall_ihSlot (hμ : μ.verifiedChecks = true) {envT : Env} {mT : EnvModel V envT}
    {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F B k : Nat} {fam : TargetFamily} {fvsPref fvsF fnorm : List Expr}
    {teles : List (List (Expr × ConLeche.BinderMeta))} {absM : Expr → Expr}
    {pw : ConLeche.PropWhen} {ih : TargetIh}
    (C : ConLeche.TargetCallRun μ F envT fam fvsPref fvsF fnorm teles absM B k pw ih)
    {L : List Expr} (hL : FvarList B L) {ρ : Nat → V} {Δ : List AnnotTerm}
    (hW : WalkCtx V mT φ B ρ Δ L)
    -- the `ih` type and the call's λ: their leaves are the frame's (and the callee's)
    (hlT : ∀ l ∈ ih.ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    (hbT : ih.ty.looseBVarsBounded 0 = true)
    (hlE : ∀ l ∈ (targetCallLam fam fvsPref fvsF teles B pw ih).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ Expr.fvar B (fam.recTys.getD ih.callee (.sort .zero)) :: L)
    (hbE : (targetCallLam fam fvsPref fvsF teles B pw ih).looseBVarsBounded 0 = true)
    -- the callee's stored type: closed, bounded, read and graded
    (hRf : (fam.recTys.getD ih.callee (.sort .zero)).hasFvar = false)
    (hRb : (fam.recTys.getD ih.callee (.sort .zero)).looseBVarsBounded 0 = true)
    (hRcb : ConstsBound envT (fam.recTys.getD ih.callee (.sort .zero)))
    {RTa : AnnotTerm}
    (hRT : denoteMeta mT.acval envT φ B (fam.recTys.getD ih.callee (.sort .zero)) = some RTa)
    (hRG : ∀ σ : Nat → V, WellDenotedV V σ RTa)
    {x : V} (hx : x ∈ˢ interp V ρ RTa) :
    ∃ T Lr : AnnotTerm,
      denoteMeta mT.acval envT φ B ih.ty = some T ∧
      (∀ σ : Nat → V, Sat V Δ σ → WellDenotedV V σ T) ∧
      denoteMeta mT.acval envT φ (B + 1) (targetCallLam fam fvsPref fvsF teles B pw ih)
        = some Lr ∧
      interp V (cons x ρ) Lr ∈ˢ interp V ρ T ∧
      WellDenotedV V (cons x ρ) Lr := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  -- the `ih` type, at the frame: it reads and is graded (`InferClaim`)
  have hFrT : Rules.Frame B ih.ty :=
    ⟨wscoped_of_leaves_mem hL _ hlT, hbT, fun l hl => hW.2.2.2.2.1 _ (hlT l hl)⟩
  have hCT := hW.ctxOk hacl1 hL hlT
  obtain ⟨T, hT⟩ := acceptedReads_of mT φ C.hihTy hFrT.1 hFrT.2.1 hFrT.2.2
  obtain ⟨-, -, -, -, hGT, -, -⟩ :=
    Rules.infer_sound hin (Rules.inferTypeCore_bridge C.hihTy) hFrT hCT hT
  -- the callee's slot
  have hwsR : Expr.WScoped B (fam.recTys.getD ih.callee (.sort .zero)) :=
    Expr.WScoped.of_not_hasFvar hRf
  have hL1 : FvarList (B + 1) (Expr.fvar B (fam.recTys.getD ih.callee (.sort .zero)) :: L) :=
    hL.cons _ hwsR
  have hW1 := hW.cons hRT hRb hRcb
    (by intro l hl; rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hRf] at hl; exact nomatch hl)
    (fun σ _ => hRG σ) hx
  -- the call's λ, one slot deeper: it reads and lies in its inferred type
  have hFrE : Rules.Frame (B + 1) (targetCallLam fam fvsPref fvsF teles B pw ih) :=
    ⟨wscoped_of_leaves_mem hL1 _ hlE, hbE, fun l hl => hW1.2.2.2.2.1 _ (hlE l hl)⟩
  have hCE := hW1.ctxOk hacl1 hL1 hlE
  obtain ⟨Lr, hLr⟩ := acceptedReads_of mT φ C.hcall hFrE.1 hFrE.2.1 hFrE.2.2
  obtain ⟨hFrC, hLsub, Cr, hCr, hGL, hGC, hmem⟩ :=
    Rules.infer_sound hin (Rules.inferTypeCore_bridge C.hcall) hFrE hCE hLr
  -- the `ih` type one slot deeper: its reading lifted
  have hT1 : denoteMeta mT.acval envT φ (B + 1) ih.ty = some (T.liftN 1 0) := by
    have hd := denoteMeta_open_deepen (acval := mT.acval) (env := envT) (φ := φ) hacl 1 B
      ih.ty 0 [] []
      (fun l hl => by
        have h := hL.2.2 _ (hlT l hl)
        simp only [Expr.WScoped] at h
        exact h.1) (LocList.nil B) (LocList.nil (B + 1))
    simp only [ConLeche.Expr.instantiateList_nil, Nat.add_zero] at hd
    rw [hd, hT]; rfl
  have hshift : shiftE 1 0 (cons x ρ) = ρ := by
    funext i; simp [shiftE, cons]
  have hFrT1 : Rules.Frame (B + 1) ih.ty :=
    ⟨wscoped_of_leaves_mem hL1 _ (fun l hl => List.mem_cons_of_mem _ (hlT l hl)), hbT, hFrT.2.2⟩
  have hCT1 := hW1.ctxOk hacl1 hL1 (fun l hl => List.mem_cons_of_mem _ (hlT l hl))
  have hCC := hW1.ctxOk hacl1 hL1 (fun l hl => hlE l (hLsub l hl))
  have hGT1 : Rules.Graded V (RTa :: Δ) (T.liftN 1 0) := by
    intro σ hσ
    rw [WellDenotedV_liftN]
    have hs : shiftE 1 0 σ = fun j => σ (j + 1) := by funext i; simp [shiftE]
    rw [hs]
    exact hGT _ (Sat_tail hσ)
  -- the two types are one (`DefEqClaim`)
  have heq := Rules.defeq_sound hin (Rules.isDefEqCore_bridge C.hcallEq) hFrC hFrT1 hCC hCT1
    hCr hT1 hGC hGT1 (cons x ρ) hW1.2.1
  refine ⟨T, Lr, hT, hGT, hLr, ?_, hGL (cons x ρ) hW1.2.1⟩
  have h := hmem (cons x ρ) hW1.2.1
  rw [heq, interp_liftN, hshift] at h
  exact h

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

/-- Entry `r`'s `ih` type's reading at the frame (the run's). -/
@[expose] def ihTyReads (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat)
    (B : Nat) (ihs : List TargetIh) : List AnnotTerm :=
  ihs.map fun ih => (denoteMeta acval env φ B ih.ty).getD default

/-- The calls' λ-readings one slot past the frame (the run's). -/
@[expose] def ihLamReads (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat)
    (fam : TargetFamily) (fvsPref fvsF : List Expr)
    (teles : List (List (Expr × ConLeche.BinderMeta))) (B : Nat) (pw : ConLeche.PropWhen)
    (ihs : List TargetIh) : List AnnotTerm :=
  ihs.map fun ih =>
    (denoteMeta acval env φ (B + 1) (targetCallLam fam fvsPref fvsF teles B pw ih)).getD default

/-- The `ih` VALUES: each call's λ at its callee's value `R c`. -/
@[expose] noncomputable def ihValsAt (R : Nat → V) (ρ : Nat → V) (ihs : List TargetIh) (Lrs : List AnnotTerm) :
    List V :=
  (List.range ihs.length).map fun r =>
    interp V (cons (R (ihs.getD r default).callee) ρ) (Lrs.getD r default)

set_option maxHeartbeats 1000000 in
/-- **The residue's context at a target rule's entry** (B3 (a)): the
frame's context (`hW`: the prefix and the fields) with the `ih`
variables on top, each at its `ih` type's reading lifted past the slots
before it, filled by the call's value at the callee's value `R c` — from
the calls' typing runs (`targetCall_ihSlot`), the accumulator's shape
(`TargetIhWF`: entry `r` is `fvar (B + r)` at its `ih` type), and the
callees' values lying in their stored types. -/
theorem walkCtx_targetEntry (hμ : μ.verifiedChecks = true) {envT : Env} {mT : EnvModel V envT}
    {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F B k : Nat} {fam : TargetFamily} {fvsPref fvsF fnorm : List Expr}
    {teles : List (List (Expr × ConLeche.BinderMeta))} {absM : Expr → Expr}
    {pw : ConLeche.PropWhen} {fr : ConLeche.TargetFrame} {ihs : Array TargetIh}
    (hcalls : ∀ ih ∈ ihs.toList,
      Nonempty (ConLeche.TargetCallRun μ F envT fam fvsPref fvsF fnorm teles absM B k pw ih))
    (hwf : TargetIhWF fr B ihs)
    {L : List Expr} (hL : FvarList B L) {ρ : Nat → V} {Δ : List AnnotTerm}
    (hW : WalkCtx V mT φ B ρ Δ L)
    -- every `ih` type's and every call's scoping
    (hscope : ∀ ih ∈ ihs.toList,
      (∀ l ∈ ih.ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ L) ∧ ih.ty.looseBVarsBounded 0 = true ∧
      ConstsBound envT ih.ty ∧
      (∀ l ∈ (targetCallLam fam fvsPref fvsF teles B pw ih).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ Expr.fvar B (fam.recTys.getD ih.callee (.sort .zero)) :: L) ∧
      (targetCallLam fam fvsPref fvsF teles B pw ih).looseBVarsBounded 0 = true)
    -- the callees' stored types, and their values
    (hRT : ∀ ih ∈ ihs.toList,
      (fam.recTys.getD ih.callee (.sort .zero)).hasFvar = false ∧
      (fam.recTys.getD ih.callee (.sort .zero)).looseBVarsBounded 0 = true ∧
      ConstsBound envT (fam.recTys.getD ih.callee (.sort .zero)) ∧
      ∃ RTa : AnnotTerm,
        denoteMeta mT.acval envT φ B (fam.recTys.getD ih.callee (.sort .zero)) = some RTa ∧
        (∀ σ : Nat → V, WellDenotedV V σ RTa))
    (R : Nat → V)
    (hR : ∀ ih ∈ ihs.toList, ∀ RTa : AnnotTerm,
      denoteMeta mT.acval envT φ B (fam.recTys.getD ih.callee (.sort .zero)) = some RTa →
      R ih.callee ∈ˢ interp V ρ RTa) :
    (∀ ih ∈ ihs.toList,
      ∃ T Lr : AnnotTerm, denoteMeta mT.acval envT φ B ih.ty = some T ∧
        denoteMeta mT.acval envT φ (B + 1) (targetCallLam fam fvsPref fvsF teles B pw ih)
          = some Lr) ∧
    WalkCtx V mT φ (B + ihs.size)
      (consList (ihValsAt R ρ ihs.toList
        (ihLamReads mT.acval envT φ fam fvsPref fvsF teles B pw ihs.toList)) ρ)
      ((ihDomsLifted (ihTyReads mT.acval envT φ B ihs.toList)).reverse ++ Δ)
      ((ihs.toList.map (·.fv)).reverse ++ L) := by
  -- each call's slot facts
  have hslot : ∀ ih ∈ ihs.toList, ∃ T Lr : AnnotTerm,
      denoteMeta mT.acval envT φ B ih.ty = some T ∧
      (∀ σ : Nat → V, Sat V Δ σ → WellDenotedV V σ T) ∧
      denoteMeta mT.acval envT φ (B + 1) (targetCallLam fam fvsPref fvsF teles B pw ih)
        = some Lr ∧
      interp V (cons (R ih.callee) ρ) Lr ∈ˢ interp V ρ T := by
    intro ih hih
    obtain ⟨C⟩ := hcalls ih hih
    obtain ⟨hlT, hbT, -, hlE, hbE⟩ := hscope ih hih
    obtain ⟨hRf, hRb, hRcb, RTa, hRTa, hRG⟩ := hRT ih hih
    obtain ⟨T, Lr, h1, h2, h3, h4, -⟩ :=
      targetCall_ihSlot hμ hacl hin C hL hW hlT hbT hlE hbE hRf hRb hRcb hRTa hRG
        (hR ih hih RTa hRTa)
    exact ⟨T, Lr, h1, h2, h3, h4⟩
  refine ⟨fun ih hih => ?_, ?_⟩
  · obtain ⟨T, Lr, hT, -, hLr, -⟩ := hslot ih hih
    exact ⟨T, Lr, hT, hLr⟩
  -- the `ih` variables are `fvar (B + r)` at their types
  have hfv : ihs.toList.map (·.fv) = ihFvarsAt B (ihs.toList.map (·.ty)) := by
    apply List.ext_getElem (by simp [ihFvarsAt])
    intro r h1 h2
    simp only [List.getElem_map, ihFvarsAt, List.getElem_range, List.length_map] at h1 ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
      Array.getElem?_eq_getElem (by simpa using h1)]
    simpa using (hwf r (by simpa using h1)).1
  have hlenT : (ihTyReads mT.acval envT φ B ihs.toList).length = ihs.size := by
    simp [ihTyReads]
  rw [hfv, ← hlenT]
  refine walkCtx_ihs hacl hL hW _ _ _ (by simp [ihTyReads]) (by simp [ihValsAt, ihTyReads]) ?_
  intro r hr
  rw [hlenT] at hr
  have hmem : ihs[r] ∈ ihs.toList := Array.getElem_mem_toList hr
  obtain ⟨T, Lr, hT, hGT, hLr, hv⟩ := hslot _ hmem
  obtain ⟨hlT, hbT, hcbT, -, -⟩ := hscope _ hmem
  have eTy : (ihs.toList.map (·.ty)).getD r default = ihs[r].ty := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
      Array.getElem?_eq_getElem hr]; rfl
  have eT : (ihTyReads mT.acval envT φ B ihs.toList).getD r default = T := by
    rw [ihTyReads, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
      Array.getElem?_eq_getElem hr]
    simp [hT]
  have eV : (ihValsAt R ρ ihs.toList
      (ihLamReads mT.acval envT φ fam fvsPref fvsF teles B pw ihs.toList)).getD r pt
      = interp V (cons (R ihs[r].callee) ρ) Lr := by
    rw [ihValsAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by simpa using hr)]
    simp only [Option.map_some, Option.getD_some]
    have e1 : (ihs.toList.getD r default) = ihs[r] := by
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getElem?_eq_getElem hr]; rfl
    have e2 : (ihLamReads mT.acval envT φ fam fvsPref fvsF teles B pw ihs.toList).getD r default
        = Lr := by
      rw [ihLamReads, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
        Array.getElem?_eq_getElem hr]
      simp [hLr]
    rw [e1, e2]
  rw [eTy, eT, eV]
  exact ⟨hlT, hbT, hcbT, hT, hGT, hv⟩

/-! ## The `ih` types' and the calls' scoping, from the run -/

/-- **The walk's new entries** carry index arguments that are sub-terms
of the walked term: their leaves are its leaves. -/
theorem targetAbstract_entries {fr : ConLeche.TargetFrame} {B : Nat}
    (hle : ∀ c, fr.rPs.getD c 0 ≤ fr.mIs.getD c 0) :
    ∀ (d : Nat) (e : Expr) (acc : Array TargetIh) (e' : Expr) (acc' : Array TargetIh),
      ConLeche.targetAbstract fr B d e acc = some (e', acc') →
      ∀ ih ∈ acc'.toList, ih ∈ acc.toList ∨ ∀ x ∈ ih.idx, ∀ l ∈ x.fvarLeaves, l ∈ e.fvarLeaves
  | _, .bvar _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
  | _, .sort _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
  | _, .lit _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
  | _, .fvar _ _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
  | _, .const n us, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
  | d, .lam ty b bi, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro ih hih
    rcases targetAbstract_entries hle (d + 1) b acc1 b' acc2 h2 ih hih with hA | hA
    · rcases targetAbstract_entries hle d ty acc ty' acc1 h1 ih hA with hB | hB
      · exact Or.inl hB
      · exact Or.inr fun x hx l hl => by simp [Expr.fvarLeaves, hB x hx l hl]
    · exact Or.inr fun x hx l hl => by simp [Expr.fvarLeaves, hA x hx l hl]
  | d, .forallE ty b bi, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro ih hih
    rcases targetAbstract_entries hle (d + 1) b acc1 b' acc2 h2 ih hih with hA | hA
    · rcases targetAbstract_entries hle d ty acc ty' acc1 h1 ih hA with hB | hB
      · exact Or.inl hB
      · exact Or.inr fun x hx l hl => by simp [Expr.fvarLeaves, hB x hx l hl]
    · exact Or.inr fun x hx l hl => by simp [Expr.fvarLeaves, hA x hx l hl]
  | d, .letE ty v b, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨v', acc2⟩, h2, ⟨b', acc3⟩, h3, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro ih hih
    rcases targetAbstract_entries hle (d + 1) b acc2 b' acc3 h3 ih hih with hA | hA
    · rcases targetAbstract_entries hle d v acc1 v' acc2 h2 ih hA with hB | hB
      · rcases targetAbstract_entries hle d ty acc ty' acc1 h1 ih hB with hC | hC
        · exact Or.inl hC
        · exact Or.inr fun x hx l hl => by simp [Expr.fvarLeaves, hC x hx l hl]
      · exact Or.inr fun x hx l hl => by simp [Expr.fvarLeaves, hB x hx l hl]
    · exact Or.inr fun x hx l hl => by simp [Expr.fvarLeaves, hA x hx l hl]
  | d, .proj sn i x, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨x', acc1⟩, h1, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro ih hih
      rcases targetAbstract_entries hle d x acc x' acc1 h1 ih hih with hA | hA
      · exact Or.inl hA
      · exact Or.inr fun y hy l hl => by simpa [Expr.fvarLeaves] using hA y hy l hl
  | d, .app f a, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · next i c m idx hc =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ty, hty, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact fun ih h => Or.inl h
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        intro ih hih
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hih
        rcases hih with hih | rfl
        · exact Or.inl hih
        · refine Or.inr fun x hx l hl => ?_
          obtain ⟨rn, he, -⟩ := targetCall?_inv hc hle
          rw [he]
          exact mem_fvarLeaves_mkAppN_arg _ _ x
            (List.mem_append_left _ (List.mem_append_right _ hx)) l hl
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨f', acc1⟩, h1, ⟨a', acc2⟩, h2, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro ih hih
      rcases targetAbstract_entries hle d a acc1 a' acc2 h2 ih hih with hA | hA
      · rcases targetAbstract_entries hle d f acc f' acc1 h1 ih hA with hB | hB
        · exact Or.inl hB
        · exact Or.inr fun x hx l hl => by simp [Expr.fvarLeaves, hB x hx l hl]
      · exact Or.inr fun x hx l hl => by simp [Expr.fvarLeaves, hA x hx l hl]

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

set_option maxHeartbeats 2000000 in
/-- **Every `ih` type and every call's λ is scoped by the rule's frame**:
their leaves are the frame's entries (the λ's also the callee's slot),
they have no loose bound variable, and the `ih` type names only stored
constants — from the rule's run (`TargetRuleRun`: the walk's entries,
the fields' whnf-telescopes, the calls' typing runs) and the frame's own
hereditary facts. -/
theorem targetIh_scope (hμ : μ.verifiedChecks = true)
    {F : Nat} {feR feT : ConLeche.FEnv} {p : ConLeche.BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} {cvR : ConstantVal} {rP : Nat} {recTy : Expr} {M : ConLeche.TargetMajor}
    {c : ConstantVal × Nat} {rhs out : Expr}
    (R : ConLeche.TargetRuleRun μ F feR feT p formerTys fam cvR rP recTy M c rhs out)
    (henv : ConLeche.EnvWF feT.env)
    (hle : ∀ c', fam.rPs.getD c' 0 ≤ fam.mIs.getD c' 0)
    (hbf : R.body.hasFvar = false)
    (hFr : FvarList (rP + c.2) (R.fvsPref ++ R.fvsF).reverse)
    (hher : ∀ x ∈ R.fvsPref ++ R.fvsF, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ R.fvsPref ++ R.fvsF)
    (hcbF : ∀ x ∈ R.fvsPref ++ R.fvsF, ConstsBound feT.env x)
    (hformer : ∀ t ∈ formerTys, t.hasFvar = false)
    (hRf : ∀ c', (fam.recTys.getD c' (.sort .zero)).hasFvar = false)
    {ih : TargetIh} (hih : ih ∈ R.ihs.toList) :
    (∀ l ∈ ih.ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ (R.fvsPref ++ R.fvsF).reverse) ∧
    ih.ty.looseBVarsBounded 0 = true ∧ ConstsBound feT.env ih.ty ∧
    (∀ l ∈ (targetCallLam fam R.fvsPref R.fvsF (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
        (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ Expr.fvar (rP + c.2) (fam.recTys.getD ih.callee (.sort .zero))
        :: (R.fvsPref ++ R.fvsF).reverse) ∧
    (targetCallLam fam R.fvsPref R.fvsF (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
        (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih).looseBVarsBounded 0
      = true ∧
    (∀ b ∈ (R.fnorm.map fun t => t.piBinders.1).getD ih.field [],
      ∀ l ∈ b.1.fvarLeaves, Expr.fvar l.1 l.2 ∈ R.fvsPref ++ R.fvsF) := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  obtain ⟨C⟩ := R.call hih
  -- the frame's entries' leaves are the frame's
  have hframeL : ∀ x ∈ R.fvsPref ++ R.fvsF, ∀ l ∈ x.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ R.fvsPref ++ R.fvsF := by
    intro x hx l hl
    obtain ⟨i, ty, rfl⟩ := hFr.mem_fvar (List.mem_reverse.mpr hx)
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hx
    · exact hher _ hx l hl
  -- the walk's entry: its `ih` type
  have hwf : TargetIhWF (ConLeche.targetFrameOf fam rP R.fvsPref R.fvsF R.fnorm
      (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large))) (rP + c.2) R.ihs :=
    (targetAbstract_acc 0 _ #[] _ _ R.habs).2 (fun r hr => absurd hr (by simp))
  obtain ⟨r, hr, hget⟩ := List.getElem_of_mem hih
  have hr' : r < R.ihs.size := by simpa using hr
  obtain ⟨-, htyW⟩ := hwf r hr'
  have hget' : R.ihs[r] = ih := by simpa using hget
  rw [hget'] at htyW
  unfold ConLeche.targetIhTy at htyW
  obtain ⟨X, hX, hXeq⟩ := Option.map_eq_some_iff.mp htyW
  simp only [ConLeche.targetFrameOf] at hX hXeq
  -- the index arguments: sub-terms of the opened body
  have hidx : ∀ x ∈ ih.idx, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ R.fvsPref ++ R.fvsF := by
    rcases targetAbstract_entries (fr := ConLeche.targetFrameOf fam rP R.fvsPref R.fvsF R.fnorm
        (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large))) (B := rP + c.2) hle
        0 _ #[] _ _ R.habs ih hih with h0 | h0
    · simp at h0
    · intro x hx l hl
      obtain ⟨y, hy, hly⟩ := fvarLeaves_instantiateList hFr R.body hbf 0 l (h0 x hx l hl)
      exact hframeL y (List.mem_reverse.mp hy) l hly
  -- the field
  have hfld : ∀ l ∈ (R.fvsF.getD ih.field default).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ R.fvsPref ++ R.fvsF := by
    intro l hl
    rcases Nat.lt_or_ge ih.field R.fvsF.length with hi | hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hl
      exact hframeL _ (List.mem_append_right _ (List.getElem_mem hi)) l hl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none,
        fvarLeaves_default] at hl
      exact nomatch hl
  -- the arguments of the call
  have hargs : ∀ a ∈ R.fvsPref ++ ih.idx ++
      [Expr.mkAppN (R.fvsF.getD ih.field default)
        (ConLeche.structTeleVars ((R.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)],
      ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ R.fvsPref ++ R.fvsF := by
    intro a ha l hl
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact hframeL a (List.mem_append_left _ ha) l hl
    · exact hidx a ha l hl
    · rcases ConLeche.fvarLeaves_mkAppN hl with h1 | ⟨y, hy, h1⟩
      · exact hfld l h1
      · rw [structTeleVars_fvarLeaves _ y hy] at h1; exact nomatch h1
  -- the field's telescope: its domains' leaves are the field type's
  have htele : ∀ b ∈ (R.fnorm.map fun t => t.piBinders.1).getD ih.field [],
      ∀ l ∈ b.1.fvarLeaves, Expr.fvar l.1 l.2 ∈ R.fvsPref ++ R.fvsF := by
    intro b hb l hl
    obtain ⟨hlenN, hallN⟩ := ConLeche.targetFieldNorms_run R.hfnorm
    rcases Nat.lt_or_ge ih.field R.fvsF.length with hi | hi
    · obtain ⟨t, ht, hrun⟩ := hallN ih.field _ (List.getElem?_eq_getElem hi)
      have hbt : b ∈ t.piBinders.1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, ht] at hb; simpa using hb
      have hlt := piBinders_dom_fvarLeaves t b hbt l hl
      -- the field's own type is scoped by the frame
      have hfmem : R.fvsF[ih.field] ∈ R.fvsPref ++ R.fvsF :=
        List.mem_append_right _ (List.getElem_mem hi)
      obtain ⟨i0, ty0, hf0⟩ := hFr.mem_fvar (List.mem_reverse.mpr hfmem)
      have hws0 : Expr.WScoped (rP + c.2) ty0 := by
        have h := hFr.2.2 _ (List.mem_reverse.mpr hfmem)
        rw [hf0] at h
        unfold Expr.WScoped at h
        exact h.2.mono (by omega)
      have hholes : ∀ h ∈ ConLeche.targetHoles formerTys (rP + c.2),
          Expr.WScoped (rP + c.2 + formerTys.length) h := by
        intro h hh
        simp only [ConLeche.targetHoles, List.mem_map, List.mem_range] at hh
        obtain ⟨t', ht', rfl⟩ := hh
        unfold Expr.WScoped
        refine ⟨by omega, Expr.WScoped.of_not_hasFvar (hformer _ ?_)⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]
        exact List.getElem_mem ht'
      have hwsA := ConLeche.targetAbs_WScoped (names := p.memberNames) (lvls := p.lps.map .param)
        hholes ty0 (hws0.mono (by omega))
      have hfT : (R.fvsF[ih.field]).fvarTypeD = ty0 := by rw [hf0]; rfl
      rw [hfT] at hrun
      obtain ⟨-, hlw⟩ := ConLeche.targetWhnfPis_scope henv 1024 _ _ t hrun hwsA
      rcases ConLeche.targetAbs_fvarLeaves ty0 l (hlw l hlt) with h1 | ⟨h, hh, h1⟩
      · have := hher _ hfmem l
        rw [hfT] at this
        exact this h1
      · -- a hole's leaf is excluded by the hole-free check
        exfalso
        simp only [ConLeche.targetHoles, List.mem_map, List.mem_range] at hh
        obtain ⟨t', ht', rfl⟩ := hh
        have hcl : (formerTys.getD t' default).hasFvar = false := by
          apply hformer
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]
          exact List.getElem_mem ht'
        simp only [Expr.fvarLeaves, List.mem_cons,
          ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl, List.not_mem_nil, or_false] at h1
        have hfree := C.htele b hb
        simp only [ConLeche.targetHoleFree, List.all_eq_true, List.mem_range] at hfree
        have := hfree t' ht'
        simp only [ConLeche.Expr.mentionsFvar, Bool.not_eq_true', List.any_eq_false] at this
        exact this l hl (by rw [h1]; simp)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa [hlenN] using hi),
        Option.getD_none] at hb
      exact nomatch hb
  -- the `ih` type's leaves
  have hlT : ∀ l ∈ ih.ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ R.fvsPref ++ R.fvsF := by
    intro l hl
    rw [← hXeq] at hl
    rcases ConLeche.mkPisOf_fvarLeaves _ X l hl with ⟨b, hb, h1⟩ | h1
    · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
      exact htele b0 hb0 l h1
    · rcases ConLeche.instPisAtLift_fvarLeaves _ _ hX l h1 with h2 | ⟨a, ha, h2⟩
      · rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar (hRf _)] at h2; exact nomatch h2
      · exact hargs a ha l h2
  refine ⟨fun l hl => List.mem_reverse.mpr (hlT l hl),
    ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge C.hihTy),
    infer_constsBound_of_full (Rules.inferTypeCore_bridge C.hihTy) rfl
      (fun l hl => by
        have := hcbF _ (hlT l hl)
        simpa using this),
    ?_, ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge C.hcall), htele⟩
  -- the call's λ's leaves
  intro l hl
  rcases ConLeche.mkLamsOf_fvarLeaves _ _ l hl with ⟨b, hb, h1⟩ | h1
  · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
    exact List.mem_cons_of_mem _ (List.mem_reverse.mpr (htele b0 hb0 l h1))
  · rcases ConLeche.fvarLeaves_mkAppN h1 with h2 | ⟨a, ha, h2⟩
    · simp only [Expr.fvarLeaves, List.mem_cons,
        ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar (hRf _), List.not_mem_nil,
        or_false] at h2
      subst h2
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_reverse.mpr (hargs a ha l h2))

/-- **The residue's leaves** are the walked term's, or an `ih` variable's. -/
theorem targetAbstract_out_leaves {fr : ConLeche.TargetFrame} {B : Nat} :
    ∀ (d : Nat) (e : Expr) (acc : Array TargetIh) (e' : Expr) (acc' : Array TargetIh),
      ConLeche.targetAbstract fr B d e acc = some (e', acc') →
      ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves ∨ ∃ ih ∈ acc'.toList, l ∈ ih.fv.fvarLeaves
  | _, .bvar _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; exact fun l hl => Or.inl hl
  | _, .sort _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; exact fun l hl => Or.inl hl
  | _, .lit _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; exact fun l hl => Or.inl hl
  | _, .fvar _ _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; exact fun l hl => Or.inl hl
  | _, .const n us, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; exact fun l hl => Or.inl hl
  | d, .lam ty b bi, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have p2 := (targetAbstract_acc (d + 1) b acc1 b' acc2 h2).1
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · rcases targetAbstract_out_leaves d ty acc ty' acc1 h1 l hl with hA | ⟨ih, hih, hA⟩
      · exact Or.inl (by simp [Expr.fvarLeaves, hA])
      · exact Or.inr ⟨ih, p2.subset hih, hA⟩
    · rcases targetAbstract_out_leaves (d + 1) b acc1 b' acc2 h2 l hl with hA | hA
      · exact Or.inl (by simp [Expr.fvarLeaves, hA])
      · exact Or.inr hA
  | d, .forallE ty b bi, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have p2 := (targetAbstract_acc (d + 1) b acc1 b' acc2 h2).1
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · rcases targetAbstract_out_leaves d ty acc ty' acc1 h1 l hl with hA | ⟨ih, hih, hA⟩
      · exact Or.inl (by simp [Expr.fvarLeaves, hA])
      · exact Or.inr ⟨ih, p2.subset hih, hA⟩
    · rcases targetAbstract_out_leaves (d + 1) b acc1 b' acc2 h2 l hl with hA | hA
      · exact Or.inl (by simp [Expr.fvarLeaves, hA])
      · exact Or.inr hA
  | d, .letE ty v b, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨v', acc2⟩, h2, ⟨b', acc3⟩, h3, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have p2 := (targetAbstract_acc d v acc1 v' acc2 h2).1
    have p3 := (targetAbstract_acc (d + 1) b acc2 b' acc3 h3).1
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · rcases targetAbstract_out_leaves d ty acc ty' acc1 h1 l hl with hA | ⟨ih, hih, hA⟩
      · exact Or.inl (by simp [Expr.fvarLeaves, hA])
      · exact Or.inr ⟨ih, p3.subset (p2.subset hih), hA⟩
    · rcases targetAbstract_out_leaves d v acc1 v' acc2 h2 l hl with hA | ⟨ih, hih, hA⟩
      · exact Or.inl (by simp [Expr.fvarLeaves, hA])
      · exact Or.inr ⟨ih, p3.subset hih, hA⟩
    · rcases targetAbstract_out_leaves (d + 1) b acc2 b' acc3 h3 l hl with hA | hA
      · exact Or.inl (by simp [Expr.fvarLeaves, hA])
      · exact Or.inr hA
  | d, .proj sn i x, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨x', acc1⟩, h1, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro l hl
      simp only [Expr.fvarLeaves] at hl
      rcases targetAbstract_out_leaves d x acc x' acc1 h1 l hl with hA | hA
      · exact Or.inl (by simpa [Expr.fvarLeaves] using hA)
      · exact Or.inr hA
  | d, .app f a, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · next i c m idx hc =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ty, hty, h⟩ := h
      split at h
      · next r hr =>
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro l hl
        rcases ConLeche.fvarLeaves_mkAppN hl with h1 | ⟨y, hy, h1⟩
        · refine Or.inr ?_
          simp only [Array.getD] at h1
          split at h1
          · next hlt => exact ⟨_, Array.getElem_mem_toList hlt, h1⟩
          · exfalso
            have : (default : TargetIh).fv = default := rfl
            rw [this, fvarLeaves_default] at h1
            exact nomatch h1
        · rw [ConLeche.structTeleVars_fvarLeaves _ y hy] at h1; exact nomatch h1
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro l hl
        rcases ConLeche.fvarLeaves_mkAppN hl with h1 | ⟨y, hy, h1⟩
        · refine Or.inr ⟨⟨i, c, idx, ty, .fvar (B + acc.size) ty⟩, ?_, h1⟩
          rw [Array.toList_push]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [ConLeche.structTeleVars_fvarLeaves _ y hy] at h1; exact nomatch h1
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨f', acc1⟩, h1, ⟨a', acc2⟩, h2, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have p2 := (targetAbstract_acc d a acc1 a' acc2 h2).1
      intro l hl
      simp only [Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · rcases targetAbstract_out_leaves d f acc f' acc1 h1 l hl with hA | ⟨ih, hih, hA⟩
        · exact Or.inl (by simp [Expr.fvarLeaves, hA])
        · exact Or.inr ⟨ih, p2.subset hih, hA⟩
      · rcases targetAbstract_out_leaves d a acc1 a' acc2 h2 l hl with hA | hA
        · exact Or.inl (by simp [Expr.fvarLeaves, hA])
        · exact Or.inr hA

end ConLeche.Model
