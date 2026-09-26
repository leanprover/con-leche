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
import ConLeche.Model.Inductives.StructBits
import ConLeche.Model.WellDenotedTransport
import ConLeche.Semantics.Kit

public section

/-!
# One `ih` key of a target rule, read (lane RECLIB, B3 (e))

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

set_option maxHeartbeats 4000000 in
/-- **A target rule's call arguments** (`p⃗ ++ e⃗ ++ [f a⃗]` of one `ih`
key `r`): their leaves are the frame's, they are bounded by the key's
telescope, and — read along any locals list `n` slots above the frame
and evaluated at a telescope spine `bs` past `n` extra values — they are
the rule's prefix, the key's index readings and its applied field. -/
theorem tgtCallArgs_run (mT : EnvModel V fe.env) (ψ : Name → Nat) {c j : Nat}
    {r0 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} {rc : ConLeche.RecShape}
    {cA : ConstantVal × Nat} {M : TargetMajor} {rhs0 rhs : Expr}
    {Q : ConLeche.TargetRuleRun μ F
      (ConLeche.consBlockRecsBareF pp.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) fe) fe pp.toBlockShape
      (cvTas.map (·.type)) (tgtFam pp.toBlockShape (tgtRs out)) r0.1 rc.rP r0.1.type M cA rhs0 rhs}
    (hle : ∀ c', (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD c' 0
      ≤ (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD c' 0)
    (hbf : Q.body.hasFvar = false)
    (hFr : FvarList (rc.rP + cA.2) (Q.fvsPref ++ Q.fvsF).reverse)
    (hher : ∀ x ∈ Q.fvsPref ++ Q.fvsF, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF)
    (hB : tgtB pp.toBlockShape out c j = rc.rP + cA.2)
    (hFrEq : tgtFrame μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j
      = ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
          Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)))
    {r : Nat} {ih : ConLeche.TargetIh} (hihMem : ih ∈ Q.ihs.toList)
    (hih : (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r default
      = ih)
    {m : Nat} (hm : ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length = m) :
    (∀ a ∈ Q.fvsPref ++ ih.idx ++
      [Expr.mkAppN (Q.fvsF.getD ih.field default) (ConLeche.structTeleVars m)],
      ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF) ∧
    (∀ a ∈ Q.fvsPref ++ ih.idx ++
      [Expr.mkAppN (Q.fvsF.getD ih.field default) (ConLeche.structTeleVars m)],
      a.looseBVarsBounded m = true) ∧
    ∀ (n : Nat) (ex xs fs bs : List V) (ρ : Nat → V) (osL : List Expr) (ws : List AnnotTerm),
      ex.length = n → bs.length = m → xs.length = rc.rP → fs.length = cA.2 →
      LocList (rc.rP + cA.2 + n) m osL →
      DenoteMetaSpine mT.acval fe.env ψ (rc.rP + cA.2 + n + m)
        ((Q.fvsPref ++ ih.idx ++
          [Expr.mkAppN (Q.fvsF.getD ih.field default) (ConLeche.structTeleVars m)]).map
            (·.instantiateList osL 0)) ws →
      ws.map (interp V (consList bs (consList ex (consList (xs ++ fs) ρ))))
        = xs ++ ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mT.acval
              fe.env ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ)))
          ++ [interp V (consList bs (consList (xs ++ fs) ρ))
            (tgtFapA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mT.acval fe.env
              ψ c j r)]) := by
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mT.acval n ψ').liftN m k = mT.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mT.cval_closedL n ψ') k m
  obtain ⟨C⟩ := Q.call hihMem
  have hlp : Q.fvsPref.length = rc.rP := openPisAtFvars_length _ Q.hpref
  have hlf : Q.fvsF.length = cA.2 := openPisAtFvars_length _ Q.hfld
  have hframeL : ∀ x ∈ Q.fvsPref ++ Q.fvsF, ∀ l ∈ x.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := frame_leaves_mem hFr hher
  have hidxL : ∀ x ∈ ih.idx, ∀ l ∈ x.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := by
    rcases targetAbstract_entries (fr := ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out))
        rc.rP Q.fvsPref Q.fvsF Q.fnorm
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)))
        (B := rc.rP + cA.2) hle 0 _ #[] _ _ Q.habs _ hihMem with h0 | h0
    · simp at h0
    · intro x hx l hl
      obtain ⟨y, hy, hly⟩ := fvarLeaves_instantiateList hFr Q.body hbf 0 l (h0 x hx l hl)
      exact hframeL y (List.mem_reverse.mp hy) l hly
  obtain ⟨-, -, hidxB⟩ : ih.idx.length + rc.rP
        = (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD ih.callee 0 ∧
      (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD ih.callee 0 = rc.rP ∧
      ∀ x ∈ ih.idx, x.looseBVarsBounded
        ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length = true := by
    rcases targetAbstract_callShape (fr := ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out))
        rc.rP Q.fvsPref Q.fvsF Q.fnorm
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)))
        (B := rc.rP + cA.2) hle 0 _ #[] _ _ Q.habs _ hihMem with h0 | h0
    · simp at h0
    · exact h0
  rw [hm] at hidxB
  -- the field
  have hfi : ih.field < cA.2 := by
    refine Nat.lt_of_not_le fun hge => ?_
    have hg : Q.fvsF.getD ih.field default = .bvar 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have h0 := C.hfld
    rw [hg] at h0
    exact inferTypeCore_bvar_absurd' h0
  have hfvF : ∃ ty, Q.fvsF.getD ih.field default = Expr.fvar (rc.rP + ih.field) ty := by
    have hlt : rc.rP + ih.field < (Q.fvsPref ++ Q.fvsF).length := by simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hFr.reverse_idx (rc.rP + ih.field) _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    refine ⟨ty, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [List.getElem_append_right (by omega)] at hty
    simpa [hlp] using hty
  obtain ⟨fty, hfty⟩ := hfvF
  have hfmem : Q.fvsF.getD ih.field default ∈ Q.fvsPref ++ Q.fvsF := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.mem_append_right _ (List.getElem_mem _)
  -- (i) the leaves
  have hargsL : ∀ a ∈ Q.fvsPref ++ ih.idx ++
      [Expr.mkAppN (Q.fvsF.getD ih.field default) (ConLeche.structTeleVars m)],
      ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := by
    intro a ha l hl
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact hframeL a (List.mem_append_left _ ha) l hl
    · exact hidxL a ha l hl
    · rcases ConLeche.fvarLeaves_mkAppN hl with h1 | ⟨y, hy, h1⟩
      · exact hframeL _ hfmem l h1
      · rw [ConLeche.structTeleVars_fvarLeaves _ y hy] at h1; exact nomatch h1
  refine ⟨hargsL, ?_, ?_⟩
  -- (ii) the bound
  · intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · obtain ⟨i, ty, rfl⟩ := hFr.mem_fvar (List.mem_reverse.mpr (List.mem_append_left _ ha)); rfl
    · exact hidxB a ha
    · refine ConLeche.looseBVarsBounded_mkAppN (by rw [hfty]; rfl) fun x hx => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
      have := List.mem_range.mp hk
      omega
  -- (iii) the values
  intro n ex xs fs bs ρ osL ws hexl hbl hxl hfsl hosL hwsL
  have hargsLt : ∀ a ∈ Q.fvsPref ++ ih.idx ++
      [Expr.mkAppN (Q.fvsF.getD ih.field default) (ConLeche.structTeleVars m)],
      ∀ l ∈ a.fvarLeaves, l.1 < rc.rP + cA.2 := fun a ha =>
    leaf_lt_of_mem hFr (fun l hl => List.mem_reverse.mpr (hargsL a ha l hl))
  have hfvPref : ∀ i, i < rc.rP → ∃ ty, Q.fvsPref[i]? = some (Expr.fvar i ty) := by
    intro i hi
    have hlt : i < (Q.fvsPref ++ Q.fvsF).length := by simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hFr.reverse_idx i _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    refine ⟨ty, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), ← hty, List.getElem_append_left]
  have hlenS : (xs ++ fs).length = rc.rP + cA.2 := by rw [List.length_append, hxl, hfsl]
  have hTel : (tgtFrame μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).teles
      = Q.fnorm.map fun t => t.piBinders.1 := by rw [hFrEq]; rfl
  have hFF' : (tgtFrame μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).fields
      = Q.fvsF := congrArg (·.fields) hFrEq
  -- one opened argument has one value at both depths
  have hre : ∀ t ∈ Q.fvsPref ++ ih.idx ++
      [Expr.mkAppN (Q.fvsF.getD ih.field default) (ConLeche.structTeleVars m)],
      interp V (consList bs (consList ex (consList (xs ++ fs) ρ)))
          ((denoteMeta mT.acval fe.env ψ (rc.rP + cA.2 + n + m)
            (t.instantiateList osL 0)).getD default)
        = interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mT.acval fe.env ψ (rc.rP + cA.2 + m)
            (t.instantiateList (locOpen (rc.rP + cA.2) m) 0)).getD default) := by
    intro t ht
    obtain ⟨v1, hv1⟩ := spine_reads (mT := mT) hwsL _ (List.mem_map_of_mem ht)
    have hd := denoteMeta_open_deepen (acval := mT.acval) (env := fe.env) (φ := ψ)
      hacl n (rc.rP + cA.2) t m (locOpen (rc.rP + cA.2) m) osL (hargsLt t ht)
      (locOpen_locList _ _) hosL
    rw [hv1] at hd
    cases h0 : denoteMeta mT.acval fe.env ψ (rc.rP + cA.2 + m)
        (t.instantiateList (locOpen (rc.rP + cA.2) m) 0) with
    | none => rw [h0] at hd; exact nomatch hd
    | some A0 =>
      rw [hv1, Option.getD_some, Option.getD_some]
      have := interp_open_indep (V := V) (acval := mT.acval) (env := fe.env) (φ := ψ)
        hacl (hargsLt t ht) hosL (show LocList (rc.rP + cA.2 + 0) m (locOpen (rc.rP + cA.2) m)
          from locOpen_locList _ _) hbl (ex1 := ex) (ex2 := []) hexl rfl
        (ρ' := consList (xs ++ fs) ρ) hv1 h0
      simpa using this
  rw [spine_map_getD (mT := mT) hwsL]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, List.append_assoc]
  symm
  congr 1
  · apply List.ext_getElem (by simp [hlp, hxl])
    intro i h1 h2
    obtain ⟨ty, hty⟩ := hfvPref i (by omega)
    symm
    rw [List.getElem_map]
    rw [List.getElem?_eq_getElem (by rw [hlp]; omega)] at hty
    rw [Option.some.inj hty]
    simp only [Function.comp, Expr.instantiateList, denoteMeta_fvar, Option.getD_some]
    rw [← consList_append,
      show rc.rP + cA.2 + n + m - 1 - i = rc.rP + cA.2 + (ex ++ bs).length - 1 - i from by
        simp [hbl, hexl]; omega,
      interp_frame_fvar hlenS rfl (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega),
      Option.getD_some]
  · congr 1
    · simp only [tgtEisA, tgtTeleTys]
      rw [hih, hTel, hB, List.length_map, hm, List.map_map]
      apply List.map_congr_left
      intro x hx
      exact (hre x (by simp [hx])).symm
    · simp only [tgtFapA, tgtTeleTys]
      rw [hih, hTel, hB, hFF', List.length_map, hm]
      exact congrArg (·::[]) (hre _ (by simp)).symm

set_option maxHeartbeats 8000000 in
/-- **One `ih` key of a target rule, read — at ANY major** (lane NESTIND,
session 9): at the rule's frame facts (the
target run `Q`, the major's parameters scoped at the prefix, the
constructor at the major's instantiation scoped), whichever major's
class supplies them — a member's record or an outside container's
entry (`tgtFrame_cls`). -/
theorem tgtIhKey_core (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F fe.env pp cvTas ctorsAs (tgtRs out) memR)
    (hformerF : ∀ t ∈ cvTas.map (·.type), t.hasFvar = false)
    (ψ : Name → Nat) (ρ : Nat → V) {c j : Nat}
    {r0 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    {rc : ConLeche.RecShape} {M : TargetMajor}
    {cA : ConstantVal × Nat} {rhs0 rhs : Expr}
    (Q : ConLeche.TargetRuleRun μ F
      (ConLeche.consBlockRecsBareF pp.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) fe) fe pp.toBlockShape
      (cvTas.map (·.type)) (tgtFam pp.toBlockShape (tgtRs out)) r0.1 rc.rP r0.1.type M cA rhs0 rhs)
    (hrP : rc.rP = pp.toBlockShape.rulePrefixAt c)
    (hdsOk : TgtDsOk fe.env rc.rP Q.fvsPref M.ds)
    (hCf : (ConLeche.targetCtorAt M cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt M cA.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound fe.env (ConLeche.targetCtorAt M cA.1))
    (hbf : Q.body.hasFvar = false)
    (hTf : r0.1.type.hasFvar = false) (hTb : r0.1.type.looseBVarsBounded 0 = true)
    (hTc : ConstsBound fe.env r0.1.type)
    (hle : ∀ c', (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD c' 0
      ≤ (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD c' 0)
    (hRT3 : ∀ c',
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).hasFvar = false ∧
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).looseBVarsBounded 0
        = true ∧
      ConstsBound fe.env ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)))
    (hB : tgtB pp.toBlockShape out c j = rc.rP + cA.2)
    (hFrEq : tgtFrame μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j
      = ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
          Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)))
    (hAbs : (Q.bodyO, Q.ihs) = tgtAbs μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j)
    {xs fs : List V} (hxs : xs.length = pp.toBlockShape.rulePrefixAt c)
    (hfsl : fs.length = cA.2)
    {r : Nat}
    (hr : r < (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).length) :
    ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r default).callee < (tgtRs out).length ∧
    pp.toBlockShape.rulePrefixAt ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r default).callee = pp.toBlockShape.rulePrefixAt c ∧
    (∀ dd ∈ (tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ c j r), dd.2.1 = pwBit ψ (Level.zeronessOf
      (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))) ∧
    ∃ Xr : AnnotTerm,
      (∀ σ' : Nat → V, interp V σ' ((ihTyReads mpC.base2.acval fe.env ψ
          (tgtB pp.toBlockShape out c j)
          (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j)).getD r default)
        = interp V σ' (mkPisAV (tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ c j r) Xr)) ∧
      ∀ bs : List V, SpineFit (consList (xs ++ fs) ρ) ((tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ c j r).map (·.2.2)) bs →
        interp V (consList bs (consList (xs ++ fs) ρ)) Xr
          = interp V (consList (xs ++ ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ)))
              ++ [interp V (consList bs (consList (xs ++ fs) ρ)) (tgtFapA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ c j r)])) ρ)
            (blockRecConclAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r default).callee) := by
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  have hIhL : tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j = Q.ihs.toList := by
    rw [tgtIhL, ← hAbs]
  have hrl : r < Q.ihs.toList.length := by rw [← hIhL]; exact hr
  have hihGet : (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r default
      = Q.ihs.toList[r] := by
    rw [hIhL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl]; rfl
  generalize hih : (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
    default = ih at *
  have hihMem : ih ∈ Q.ihs.toList := by rw [hihGet]; exact List.getElem_mem hrl
  obtain ⟨C⟩ := Q.call hihMem
  -- the frame
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts Q.hpref Q.hcrest hdsOk Q.hfld hTf hTb hTc
    hCf hCb hCc
  have hlp : Q.fvsPref.length = rc.rP := openPisAtFvars_length _ Q.hpref
  have hlf : Q.fvsF.length = cA.2 := openPisAtFvars_length _ Q.hfld
  have hscope := targetIh_scope hμ Q mpC.base2.wf hle hbf hFr hher hcbF hformerF
    (fun c' => (hRT3 c').1) hihMem
  obtain ⟨hidxLen, hrPc, -⟩ : ih.idx.length + rc.rP
        = (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD ih.callee 0 ∧
      (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD ih.callee 0 = rc.rP ∧
      ∀ x ∈ ih.idx, x.looseBVarsBounded
        ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length = true := by
    rcases targetAbstract_callShape (fr := ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out))
        rc.rP Q.fvsPref Q.fvsF Q.fnorm
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)))
        (B := rc.rP + cA.2) hle 0 _ #[] _ _ Q.habs _ hihMem with h0 | h0
    · simp at h0
    · exact h0
  -- the callee
  have hcal : ih.callee < (tgtRs out).length := by
    simpa [tgtFam] using targetCall_callee_lt C
  obtain ⟨r1, hr1⟩ : ∃ r1, (tgtRs out)[ih.callee]? = some r1 :=
    ⟨_, List.getElem?_eq_getElem hcal⟩
  obtain ⟨-, hlenR, -⟩ := recStageG_recNames h
  have hcalR : ih.callee < pp.recs.length := by omega
  have hmIc : (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD ih.callee 0
      = pp.toBlockShape.majorIdxAt ih.callee := by
    simp only [tgtFam, ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, List.getElem?_eq_getElem hcalR]; rfl
  have hrPc' : pp.toBlockShape.rulePrefixAt ih.callee = rc.rP := by
    rw [← hrPc]
    simp only [tgtFam, ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, List.getElem?_eq_getElem hcalR]; rfl
  have hrecTy : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD ih.callee (.sort .zero)
      = r1.1.type := by
    simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hr1]; rfl
  refine ⟨hcal, by rw [hrPc', hrP], ?_, ?_⟩
  · intro dd hdd
    simp only [tgtTlA, List.mem_map] at hdd
    obtain ⟨t, -, rfl⟩ := hdd
    rfl
  -- the entry's `ih` type: the callee's type peeled at the call, under the telescope
  have hwf : TargetIhWF (ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP
      Q.fvsPref Q.fvsF Q.fnorm
      (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)))
      (rc.rP + cA.2) Q.ihs :=
    (targetAbstract_acc 0 _ #[] _ _ Q.habs).2 (fun r hr => absurd hr (by simp))
  have hrs : r < Q.ihs.size := by simpa using hrl
  obtain ⟨-, htyW⟩ := hwf r hrs
  have hQr : Q.ihs[r] = ih := by rw [hihGet]; simp
  rw [hQr] at htyW
  unfold ConLeche.targetIhTy at htyW
  obtain ⟨X, hX, hXeq⟩ := Option.map_eq_some_iff.mp htyW
  simp only [ConLeche.targetFrameOf] at hX hXeq
  obtain ⟨hlT, hbT, -⟩ := hscope
  obtain ⟨T, hT⟩ := acceptedReads_of mpC.base2 ψ C.hihTy (wscoped_of_leaves_mem hFr _ hlT) hbT
    (fun l hl => by
      exact hlbF _ (List.mem_reverse.mp (hlT l hl)))
  have hTget : (ihTyReads mpC.base2.acval fe.env ψ (tgtB pp.toBlockShape out c j)
      (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j)).getD r default = T := by
    rw [hB, hIhL, ihTyReads, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hrl, ← hihGet]
    simp [hT]
  rw [← hXeq, ← ConLeche.Expr.instantiateList_nil (Expr.mkPisOf _ _) 0,
    show rc.rP + cA.2 = rc.rP + cA.2 + 0 from rfl] at hT
  obtain ⟨ds, Xr, os', rfl, hdoms, hbits, hos', hXr⟩ :=
    denoteMeta_mkPisOf (acval := mpC.base2.acval) (env := fe.env) (φ := ψ) (D := rc.rP + cA.2)
      _ X 0 [] _ (LocList.nil _) hT
  have hTel : (tgtFrame μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
      out c j).teles = Q.fnorm.map fun t => t.piBinders.1 := congrArg (·.teles) hFrEq
  have hTL : tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ
        c j r
      = (ds.map (·.2.2)).map fun t => (0, pwBit ψ (Level.zeronessOf
          (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)), t) := by
    simp only [tgtTlA, tgtTeleTys]
    rw [hih, hTel, hB]
    simp only [List.map_map] at hdoms
    rw [show (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1))
      = ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map
          ((·.1) ∘ fun b => (b.1, (⟨Level.zeronessOf (ConLeche.structElimLevel
            pp.toBlockShape.elim pp.toBlockShape.large)⟩ : ConLeche.BinderMeta))) from rfl, hdoms,
      Option.getD_some]
  have hsnd : ds.map (·.2) = (tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) out
      mpC.base2.acval fe.env ψ c j r).map (·.2) := by
    rw [hTL, List.map_map]
    have hdl : ds.length = ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length := by
      have := congrArg List.length hbits; simpa using this
    apply List.ext_getElem (by simp)
    intro q h1 h2
    have hb := congrArg (fun l => l[q]?) hbits
    simp only [List.getElem?_map] at hb
    simp only [List.getElem_map, Function.comp]
    ext
    · have hq : q < ds.length := by simpa using h1
      rw [List.getElem?_eq_getElem hq] at hb
      have hq' : q < ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length := by
        omega
      rw [List.getElem?_eq_getElem hq'] at hb
      simpa using hb
    · rfl
  refine ⟨Xr, fun σ' => by rw [hTget, interp_mkPisAV_congr hsnd], ?_⟩
  intro bs hbs
  -- names
  generalize hmdef : ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length = m at *
  have hmT : (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map fun b =>
      (b.1, (⟨Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
        pp.toBlockShape.large)⟩ : ConLeche.BinderMeta))).length = m := by
    rw [List.length_map, hmdef]
  rw [hmT, Nat.zero_add] at hos' hXr
  have hxl : xs.length = rc.rP := by rw [hxs, hrP]
  have hlenS : (xs ++ fs).length = rc.rP + cA.2 := by rw [List.length_append, hxl, hfsl]
  have hbl : bs.length = m := by
    have hdl : ds.length = m := by
      have := congrArg List.length hbits
      rw [List.length_map, List.length_map, hmT] at this
      exact this
    rw [hbs.length_eq, hTL, List.length_map, List.length_map, List.length_map, hdl]
  -- the call's arguments
  obtain ⟨hargsL, hargsB', hvalsAt⟩ :=
    tgtCallArgs_run mpC.base2 ψ hle hbf hFr hher hB hFrEq hihMem hih hmdef
  have hargsLt : ∀ a ∈ Q.fvsPref ++ ih.idx ++
      [Expr.mkAppN (Q.fvsF.getD ih.field default) (ConLeche.structTeleVars m)],
      ∀ l ∈ a.fvarLeaves, l.1 < rc.rP + cA.2 := fun a ha =>
    leaf_lt_of_mem hFr (fun l hl => List.mem_reverse.mpr (hargsL a ha l hl))
  have hargsB : ∀ a ∈ Q.fvsPref ++ ih.idx ++
      [Expr.mkAppN (Q.fvsF.getD ih.field default) (ConLeche.structTeleVars m)],
      a.looseBVarsBounded (locOpen (rc.rP + cA.2) m).length = true := by
    rw [show (locOpen (rc.rP + cA.2) m).length = m by simp [locOpen]]
    exact hargsB'
  have hlocAll : AllFvars (locOpen (rc.rP + cA.2) m) := (locOpen_locList _ _).allFvars
  have hloccl : ∀ o ∈ locOpen (rc.rP + cA.2) m, o.looseBVarsBounded 0 = true := by
    intro o ho; obtain ⟨i, ty, rfl⟩ := hlocAll o ho; rfl
  have hXleaves : ∀ l ∈ X.fvarLeaves, l.1 < rc.rP + cA.2 := by
    intro l hl
    have hl' : l ∈ ih.ty.fvarLeaves := by
      rw [← hXeq]
      exact mkPisOf_fvarLeaves_body _ X l hl
    exact leaf_lt_of_mem hFr hlT l hl'
  -- (a) the body, read at the canonical openers
  have hXl : denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + m)
      (X.instantiateList (locOpen (rc.rP + cA.2) m) 0) = some Xr := by
    have hd := denoteMeta_open_deepen (acval := mpC.base2.acval) (env := fe.env) (φ := ψ) hacl 0
      (rc.rP + cA.2) X m (locOpen (rc.rP + cA.2) m) os' hXleaves (locOpen_locList _ _)
      (by simpa using hos')
    rw [Nat.add_zero, hXr] at hd
    cases h0 : denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + m)
        (X.instantiateList (locOpen (rc.rP + cA.2) m) 0) with
    | none => rw [h0] at hd; exact nomatch hd
    | some A0 =>
      rw [h0, Option.map_some] at hd
      rw [Option.some.inj hd, ConLeche.Semantics.AnnotTerm.liftN_zero]
  -- (b) the peel, at the opened arguments
  have hins := instPisAtLift_instantiateList hloccl _ hargsB (hRT3 ih.callee).2.1 hX
  rw [hrecTy] at hins
  -- (c) the arguments read
  obtain ⟨-, hlam, -, -, -⟩ := targetRule_reads hμ mpC.base2 ψ Q hle hbf hdsOk hTf hTb hTc hCf hCb hCc
    (fun t ht => hformerF t ht) (fun c' => hRT3 c')
  obtain ⟨Lr, hLr, -, -⟩ := hlam r ih (by rw [← hQr]; simp)
  have hLr' := hLr
  unfold targetCallLam at hLr'
  rw [← ConLeche.Expr.instantiateList_nil (Expr.mkLamsOf _ _) 0,
    show rc.rP + cA.2 + 1 = rc.rP + cA.2 + 1 + 0 from rfl] at hLr'
  obtain ⟨dsL, bodyL, osL, -, -, -, hosL, hbodyL⟩ :=
    denoteMeta_mkLamsOf (acval := mpC.base2.acval) (env := fe.env) (φ := ψ)
      (D := rc.rP + cA.2 + 1) _ _ 0 [] _ (LocList.nil _) hLr'
  have hmL : (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map fun b =>
      (b.1, (⟨Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
        pp.toBlockShape.large)⟩ : ConLeche.BinderMeta))).length = m := hmT
  rw [hmL, Nat.zero_add] at hosL hbodyL
  rw [instantiateList_mkAppN] at hbodyL
  simp only [Expr.instantiateList] at hbodyL
  rw [hmdef] at hbodyL
  obtain ⟨-, wsL, -, hwsL, -⟩ := denoteMeta_mkAppN_inv hbodyL
  have hreads : ∀ a ∈ (Q.fvsPref ++ ih.idx ++
      [Expr.mkAppN (Q.fvsF.getD ih.field default) (ConLeche.structTeleVars m)]).map
        (·.instantiateList (locOpen (rc.rP + cA.2) m) 0),
      ∃ v, denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + m) a = some v := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v1, hv1⟩ := spine_reads hwsL _ (List.mem_map_of_mem hb)
    have hd := denoteMeta_open_deepen (acval := mpC.base2.acval) (env := fe.env) (φ := ψ) hacl 1
      (rc.rP + cA.2) b m (locOpen (rc.rP + cA.2) m) osL (hargsLt b hb) (locOpen_locList _ _) hosL
    rw [show rc.rP + cA.2 + 1 + m = rc.rP + cA.2 + 1 + m from rfl, hv1] at hd
    cases h0 : denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + m)
        (b.instantiateList (locOpen (rc.rP + cA.2) m) 0) with
    | none => rw [h0] at hd; exact nomatch hd
    | some A0 => exact ⟨A0, rfl⟩
  obtain ⟨vs, hvs⟩ := denoteMetaSpine_of_reads _ hreads
  -- (e) the callee's type, read, and its peel
  obtain ⟨hTf1, -, -, -, -⟩ := ConLeche.recStage_facts h r1 (List.mem_of_getElem? hr1)
  obtain ⟨-, -, -, hread0, hTyE, hlenRds, -, -, -, -⟩ := recStage_tyPis hμ mpC h hr1 ψ
  have hcl1 := closed_blockRecTyAV hμ mpC h hr1 ψ
  have hRTd := denoteMeta_depth_of_closed mpC.base2.acval_closed hTf1
    (fun k => liftN_eq_self_of_closed hcl1 k 1) hread0 (rc.rP + cA.2 + m)
  have hLx : FvarList (rc.rP + cA.2 + m)
      (locOpen (rc.rP + cA.2) m ++ (Q.fvsPref ++ Q.fvsF).reverse) := by
    rw [locOpen_eq_openFvars]; exact FvarList.openExtend hFr m
  have hwsA : ∀ a ∈ (Q.fvsPref ++ ih.idx ++
      [Expr.mkAppN (Q.fvsF.getD ih.field default) (ConLeche.structTeleVars m)]).map
        (·.instantiateList (locOpen (rc.rP + cA.2) m) 0),
      Expr.WScoped (rc.rP + cA.2 + m) a ∧ a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    refine ⟨wscoped_of_leaves_mem hLx _ fun l hl => ?_, ?_⟩
    · rcases fvarLeaves_instantiateList_allFvars hlocAll b 0 l hl with h1 | ⟨x, hx, h1⟩
      · exact List.mem_append_right _ (List.mem_reverse.mpr (hargsL b hb l h1))
      · obtain ⟨j', -, rfl⟩ := mem_locOpen hx
        simp only [Expr.fvarLeaves, List.mem_cons, List.not_mem_nil, or_false] at h1
        subst h1
        exact List.mem_append_left _ hx
    · exact looseBVarsBounded_instantiateList_allFvars hlocAll b 0
        (by rw [Nat.zero_add]; exact hargsB b hb)
  obtain ⟨restA, hrest, hpeel⟩ := denoteMeta_instPisAtLift_peel mpC.base2.acval_closed
    (acval_inst_self mpC.base2) _ hins (Expr.WScoped.of_not_hasFvar hTf1) hwsA hRTd hvs
  obtain rfl : Xr = restA := Option.some.inj (hXl.symm.trans hrest)
  rw [hTyE] at hpeel
  have hvsl : vs.length = (blockRecRdsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ
      ih.callee).length := by
    rw [← hvs.length, hlenRds, List.length_map, List.length_append, List.length_append, hlp,
      List.length_singleton, ← hmIc]
    omega
  rw [interp_peelPis_mkPisAV hvsl hpeel]
  -- (g) the spine's values: the prefix, the index readings and the applied field
  have hvals : vs.map (interp V (consList bs (consList (xs ++ fs) ρ)))
      = xs ++ ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
          out mpC.base2.acval fe.env ψ c j r).map
            (interp V (consList bs (consList (xs ++ fs) ρ)))
        ++ [interp V (consList bs (consList (xs ++ fs) ρ))
          (tgtFapA μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
            out mpC.base2.acval fe.env ψ c j r)]) :=
    hvalsAt 0 [] xs fs bs ρ _ vs rfl hbl hxl hfsl (locOpen_locList _ _) hvs
  -- (h) the conclusion reads below the spine
  rw [hvals]
  have hconclB := (recStage_tyBounds hμ mpC h hr1 ψ).2
  have hLlen : (xs ++ ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
          out mpC.base2.acval fe.env ψ c j r).map
            (interp V (consList bs (consList (xs ++ fs) ρ)))
        ++ [interp V (consList bs (consList (xs ++ fs) ρ))
          (tgtFapA μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
            out mpC.base2.acval fe.env ψ c j r)])).length
      = (blockRecRdsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ ih.callee).length := by
    rw [← hvals, List.length_map, hvsl]
  exact interp_congr_below V _ _ _ _ hconclB fun i hi =>
    consList_below_indep _ _ _ i (by rw [hLlen]; exact hi)

end Key

end ConLeche.Model
