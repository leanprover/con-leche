module

public import ConLeche.Model.Inductives.TargetRuleData
import ConLeche.Model.Rules.Sound
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
      interp V (cons x ρ) Lr ∈ˢ interp V ρ T := by
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
  obtain ⟨hFrC, hLsub, Cr, hCr, -, hGC, hmem⟩ :=
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
  refine ⟨T, Lr, hT, hGT, hLr, ?_⟩
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
    exact targetCall_ihSlot hμ hacl hin C hL hW hlT hbT hlE hbE hRf hRb hRcb hRTa hRG
      (hR ih hih RTa hRTa)
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

end ConLeche.Model
