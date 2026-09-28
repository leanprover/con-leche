module

public import ConLeche.Model.Inductives.TargetNodeRead
public import ConLeche.Verify.Inductives.RecCheckRun

public section

/-!
# The target check's rule data, as functions of the run

The model's rule data (`ihs`, `Rb0`, …) are functions of the level
valuation and of the (recursor, constructor) position alone.  This file
RECOMPUTES every intermediate value of `targetRule` from the stored
data and pins them: at a `targetRecCheck` run, the `(j, i)`-th rule's run
record (`TargetRuleRun`) has exactly these witnesses.

The stored family, in the model's format, is `tgtRs out`: the checked
recursor, its annotated rules, the major's index count and its
constructors — the stage record's `rs`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo FEnv BlockShape TargetMajor
  TargetIh TargetFamily TargetFrame)

/-- The family's shared data, from the stored recursors. -/
@[expose] def tgtFam (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) :
    TargetFamily :=
  { recNames := p.recs.map (·.cvR.name),
    rlvls := (p.recs.head?.map fun rc => rc.cvR.levelParams.map Level.param).getD [],
    recTys := (tgtRs out).map (·.1.type),
    mIs := p.recs.map (·.mI),
    rPs := p.recs.map (·.rP),
    majs := out.map (·.2.1) }

section Defs

variable (mode : ConLeche.CheckMode) (F : Nat) (fe : FEnv) (p : BlockShape)
  (formerTys : List Expr)
  (out : List (ConstantVal × TargetMajor × List Expr))

/-- The `j`-th stored recursor's type. -/
@[expose] def tgtRecTy (j : Nat) : Expr := (out.getD j default).1.type
/-- The `j`-th recursor's major (a member, or an outside container at its
instantiation). -/
@[expose] def tgtMajor (j : Nat) : TargetMajor := (out.getD j default).2.1
/-- The `j`-th recursor's rule prefix and major index (its record's). -/
@[expose] def tgtRP (j : Nat) : Nat := (p.recs.getD j default).rP
/-- The `i`-th constructor of the `j`-th recursor's major. -/
@[expose] def tgtCtorOf (j i : Nat) : ConstantVal × Nat := (tgtMajor out j).ctors.getD i default
/-- The `(j, i)`-th stored rule. -/
@[expose] def tgtRhsOf (j i : Nat) : Expr := ((out.getD j default).2.2).getD i default
/-- The rule's width `rP + nF`. -/
@[expose] def tgtB (j i : Nat) : Nat := tgtRP p j + (tgtCtorOf out j i).2

/-- The rule's prefix openers. -/
@[expose] def tgtPrefFvs (j : Nat) : List Expr :=
  ((ConLeche.openPisAtFvars (tgtRP p j) (tgtRecTy out j) 0).map (·.1)).getD []
/-- The constructor at the major's instantiation (`targetCtorAt`: a
member's stored at the block's levels, an outside container's
instantiated at the major's) and parameters (a member's: the recursor
type's first `nP` openers). -/
@[expose] def tgtCrest (j i : Nat) : Expr :=
  (ConLeche.instPisWith (tgtMajor out j).ds
    (ConLeche.targetCtorAt (tgtMajor out j) (tgtCtorOf out j i).1)).getD default
/-- The rule's field openers. -/
@[expose] def tgtFieldFvs (j i : Nat) : List Expr :=
  ((ConLeche.openPisAtFvars (tgtCtorOf out j i).2 (tgtCrest out j i) (tgtRP p j)).map (·.1)).getD []
/-- The constructor's conclusion at the rule's field openers (its index
expressions are `getAppArgs.drop nPc`, the major's parameter count). -/
@[expose] def tgtCbody (j i : Nat) : Expr :=
  ((ConLeche.openPisAtFvars (tgtCtorOf out j i).2 (tgtCrest out j i) (tgtRP p j)).map (·.2)).getD
    default
/-- **The recursor's conclusion at the constructor, AT THE MAJOR** (the
target check's `concl`, `targetRule`): the recursor type at the prefix,
the constructor's index expressions and the fired constructor
`C.{M.lvls} M.ds f⃗`. -/
@[expose] def tgtConclExpr (j i : Nat) : Expr :=
  (ConLeche.Expr.instPisAtLift
    (tgtPrefFvs p out j ++ (tgtCbody p out j i).getAppArgs.drop (tgtMajor out j).nPc
      ++ [Expr.mkAppN (.const (tgtCtorOf out j i).1.name (tgtMajor out j).lvls)
          ((tgtMajor out j).ds ++ tgtFieldFvs p out j i)])
    (tgtRecTy out j)).getD default
/-- The rule's body (below its `rP + nF` λ-binders). -/
@[expose] def tgtBody (j i : Nat) : Expr :=
  (((tgtRhsOf out j i).stripLams (tgtB p out j i)).map (·.2)).getD default
/-- The member abstraction at the rule's holes. -/
@[expose] def tgtAbsM (j i : Nat) : Expr → Expr :=
  ConLeche.targetAbs p.memberNames (p.lps.map .param)
    (ConLeche.targetHoles formerTys (tgtB p out j i))
/-- The fields' abstract whnf-telescopes. -/
@[expose] def tgtFnorm (j i : Nat) : List Expr :=
  match ConLeche.targetFieldNorms (ConLeche.fueledOps mode F) fe.env
      (tgtB p out j i + formerTys.length) (tgtAbsM p formerTys out j i) (tgtFieldFvs p out j i) with
  | .ok l => l
  | .error _ => []
/-- The rule's frame. -/
@[expose] def tgtFrame (j i : Nat) : TargetFrame :=
  ConLeche.targetFrameOf (tgtFam p out) (tgtRP p j) (tgtPrefFvs p out j) (tgtFieldFvs p out j i)
    (tgtFnorm mode F fe p formerTys out j i)
    (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large))
/-- The abstraction: the residue and the `ih` variables. -/
@[expose] def tgtAbs (j i : Nat) : Expr × Array TargetIh :=
  (ConLeche.targetAbstract (tgtFrame mode F fe p formerTys out j i) (tgtB p out j i) 0
    ((tgtBody p out j i).instantiateList (tgtPrefFvs p out j ++ tgtFieldFvs p out j i).reverse 0)
    #[]).getD (default, #[])

variable (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)

/-- **`ihs`, PINNED**: the `ih` term of each call is the reading of the
call's λ (`targetCallE`), its callee variable instantiated at the
family's chain variable (below the frame). -/
@[expose] def tgtIhsAV (ψ : Name → Nat) (j i : Nat) : List AnnotTerm :=
  (tgtAbs mode F fe p formerTys out j i).2.toList.map fun ih =>
    ((denoteMeta acval env ψ (tgtB p out j i + 1)
        (targetCallE (tgtFrame mode F fe p formerTys out j i) (tgtB p out j i)
          (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih)).getD default).inst
      (.bvar (tgtB p out j i + ((tgtRs out).length - 1 - ih.callee)))

/-- **`Rb0`, PINNED**: the residue, read at the frame and the `ih`
variables. -/
@[expose] def tgtRbAV (ψ : Name → Nat) (j i : Nat) : AnnotTerm :=
  (denoteMeta acval env ψ (tgtB p out j i + (tgtAbs mode F fe p formerTys out j i).2.size)
    (tgtAbs mode F fe p formerTys out j i).1).getD default

end Defs

end ConLeche.Model

namespace ConLeche.Model

open ConLeche (FEnv BlockShape TargetMajor TargetIh RecShape CheckMode)

/-! ## The pinning -/

section Pin

variable {mode : CheckMode} {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
  {block : List ConstantInfo} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

/-- The recomputed constructor at a stored rule is the stored one. -/
theorem tgtCtorOf_at {out : List (ConstantVal × TargetMajor × List Expr)} {j : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) : tgtCtorOf out j i = cA := by
  simp only [tgtRs, List.getElem?_map] at hr
  cases ho : out[j]? with
  | none => rw [ho] at hr; exact nomatch hr
  | some t =>
    rw [ho] at hr
    obtain rfl := Option.some.inj hr
    simp only [tgtCtorOf, tgtMajor, List.getD_eq_getElem?_getD, ho, Option.getD_some]
    simp only at hcA
    rw [hcA, Option.getD_some]

/-- The stored recursors are stage (b)'s, at every position. -/
theorem targetRecRun_fam_eq
    (R : ConLeche.TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    ConLeche.targetFamilyOf p R.tys = tgtFam p out := by
  have h0 := targetRecRun_out_fst R
  have h1 : out.map (fun t => t.1.type) = R.tys.map (fun t => t.1.type) := by
    have := congrArg (List.map fun q : ConstantVal × TargetMajor => q.1.type) h0
    simpa [List.map_map, Function.comp_def] using this
  have h2 : out.map (fun t => t.2.1) = R.tys.map (fun t => t.2.1) := by
    have := congrArg (List.map fun q : ConstantVal × TargetMajor => q.2) h0
    simpa [List.map_map, Function.comp_def] using this
  simp only [ConLeche.targetFamilyOf, tgtFam, tgtRs, List.map_map, Function.comp_def]
  rw [h1, h2]

/-- **The `(j, i)`-th rule's RUN, pinned, at ANY major**: at a
`targetRecCheck` run, the stored rule
`rhs` of the `j`-th recursor at its major's `i`-th constructor is a
`targetRule` run at the recursor's major `M = tgtMajor out j`, whose
witnesses are the recomputed ones — the prefix and field openers (the
constructor at the MAJOR's instantiation, `tgtCrest`), the body, the
fields' abstract telescopes and the abstraction; and the recursor's
type-stage record. -/
theorem targetRuleAtG
    (R : ConLeche.TargetRecRun mode F fe p nested block cvTas ctorsAs out)
    {j i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) :
    ∃ (rc : RecShape) (rhs0 : Expr) (M : TargetMajor) (u : Level)
      (Q : ConLeche.TargetRuleRun mode F
        (ConLeche.consBlockRecsBareF p 0 ((tgtRs out).map fun r => (r.1, r.2.2.1)) fe) fe p
        (cvTas.map (·.type)) (tgtFam p out) r.1 rc.rP r.1.type M cA rhs0 rhs),
      p.recs[j]? = some rc ∧ M = tgtMajor out j ∧
      Nonempty (ConLeche.TargetTyEntry mode F fe p nested cvTas ctorsAs rc r.1 M u) ∧
      Q.fvsPref = tgtPrefFvs p out j ∧
      Q.crest = tgtCrest out j i ∧
      Q.fvsF = tgtFieldFvs p out j i ∧
      Q.body = tgtBody p out j i ∧
      Q.fnorm = tgtFnorm mode F fe p (cvTas.map (·.type)) out j i ∧
      (Q.bodyO, Q.ihs) = tgtAbs mode F fe p (cvTas.map (·.type)) out j i := by
  obtain ⟨hlenT, hallT⟩ := ConLeche.targetRecTys_run R.htys
  obtain ⟨hlenO, hallO⟩ := ConLeche.targetRecsRules_run R.rules
  -- the stored entry is the run's
  obtain ⟨t', ht', rfl⟩ : ∃ t', out[j]? = some t' ∧ r = (t'.1, t'.2.2, t'.2.1.nIdx, t'.2.1.ctors) := by
    simp only [tgtRs, List.getElem?_map] at hr
    cases ho : out[j]? with
    | none => rw [ho] at hr; exact nomatch hr
    | some t' => rw [ho] at hr; exact ⟨t', rfl, (Option.some.inj hr).symm⟩
  have hj : j < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp ht').1
    rw [hlenO] at this; omega
  obtain ⟨rc, hrc⟩ : ∃ rc, p.recs[j]? = some rc := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨t, ht⟩ : ∃ t, R.tys[j]? = some t :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenT]; exact hj)⟩
  obtain ⟨rhssA, ho, hlenR, RR⟩ := hallO j rc t hrc ht
  obtain rfl : t' = (t.1, t.2.1, rhssA) := Option.some.inj (ht'.symm.trans ho)
  obtain ⟨cvRi, M, u⟩ := t
  obtain ⟨cvRi', M', u', ht2, ⟨E⟩⟩ := hallT j rc hrc
  obtain ⟨e1, e2, e3⟩ : cvRi = cvRi' ∧ M = M' ∧ u = u' := by
    have := ht.symm.trans ht2; simpa using this
  subst e1; subst e2; subst e3
  -- the rule's run
  simp only at hcA hrhs
  obtain ⟨rhs0, hrhs0⟩ : ∃ rhs0, rc.rhss[i]? = some rhs0 :=
    ⟨_, List.getElem?_eq_getElem (by
      rw [hlenR]; exact (List.getElem?_eq_some_iff.mp hcA).1)⟩
  obtain ⟨o, hoi, hrun⟩ := RR.rule i cA rhs0 hcA hrhs0
  obtain rfl : rhs = o := Option.some.inj (hrhs.symm.trans hoi)
  obtain ⟨Q⟩ := ConLeche.targetRule_run hrun
  rw [targetRecRun_fam_eq R, targetRecRun_bare_eq R] at Q
  -- the recomputed data at `(j, i)`
  have hgetO : out.getD j default = (cvRi, M, rhssA) := by
    rw [List.getD_eq_getElem?_getD, ht', Option.getD_some]
  have hMaj : tgtMajor out j = M := by rw [tgtMajor, hgetO]
  have hRP : tgtRP p j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hTy : tgtRecTy out j = cvRi.type := by rw [tgtRecTy, hgetO]
  have hCt : tgtCtorOf out j i = cA := by
    rw [tgtCtorOf, hMaj, List.getD_eq_getElem?_getD, hcA, Option.getD_some]
  have hRhs : tgtRhsOf out j i = rhs := by
    rw [tgtRhsOf, hgetO, List.getD_eq_getElem?_getD, hrhs, Option.getD_some]
  have hBB : tgtB p out j i = rc.rP + cA.2 := by rw [tgtB, hRP, hCt]
  have hPref : Q.fvsPref = tgtPrefFvs p out j := by
    rw [tgtPrefFvs, hRP, hTy, Q.hpref, Option.map_some, Option.getD_some]
  have hCrest : Q.crest = tgtCrest out j i := by
    rw [tgtCrest, hMaj, hCt, Q.hcrest, Option.getD_some]
  have hFld : Q.fvsF = tgtFieldFvs p out j i := by
    rw [tgtFieldFvs, hCt, ← hCrest, hRP, Q.hfld, Option.map_some, Option.getD_some]
  have hBody : Q.body = tgtBody p out j i := by
    rw [tgtBody, hRhs, hBB, Q.hstrip, Option.map_some, Option.getD_some]
  have hFn : Q.fnorm = tgtFnorm mode F fe p (cvTas.map (·.type)) out j i := by
    rw [tgtFnorm, tgtAbsM, hBB, ← hFld, Q.hfnorm]
  refine ⟨rc, rhs0, M, u, Q, hrc, hMaj.symm, ⟨E⟩, hPref, hCrest, hFld, hBody, hFn, ?_⟩
  rw [tgtAbs, tgtFrame, ← hPref, ← hFld, ← hFn, hRP, hBB, ← hBody, Q.habs, Option.getD_some]

/-- **The `(j, i)`-th rule's RUN, pinned, at a MEMBER major** (the member
bit `hm`) — `targetRuleAtG`
with the member major's parameters, count and levels. -/
theorem targetRuleAtM
    (R : ConLeche.TargetRecRun mode F fe p nested block cvTas ctorsAs out)
    {j i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) (hm : (tgtMajor out j).member.isSome = true) :
    ∃ (rc : RecShape) (rhs0 : Expr) (M : TargetMajor)
      (Q : ConLeche.TargetRuleRun mode F
        (ConLeche.consBlockRecsBareF p 0 ((tgtRs out).map fun r => (r.1, r.2.2.1)) fe) fe p
        (cvTas.map (·.type)) (tgtFam p out) r.1 rc.rP r.1.type M cA rhs0 rhs),
      p.recs[j]? = some rc ∧ M.member.isSome ∧ M.ds = Q.fvsPref.take p.nP ∧
      Q.fvsPref = tgtPrefFvs p out j ∧
      Q.fvsF = tgtFieldFvs p out j i ∧
      Q.body = tgtBody p out j i ∧
      Q.fnorm = tgtFnorm mode F fe p (cvTas.map (·.type)) out j i ∧
      (Q.bodyO, Q.ihs) = tgtAbs mode F fe p (cvTas.map (·.type)) out j i ∧
      M.nPc = p.nP ∧ M.lvls = p.lps.map .param := by
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, ⟨E⟩, hPref, -, hFld, hBody, hFn, hAbs⟩ :=
    targetRuleAtG R hr hcA hrhs
  subst hMaj
  obtain ⟨hnPc, hlvls⟩ := targetTyEntry_major_of E hm
  have hds : (tgtMajor out j).ds = Q.fvsPref.take p.nP := by
    rw [E.ds_eq_of hm]
    obtain ⟨o', ho'⟩ := ConLeche.openPisAtFvars_prefix rc.rP (rc.mI + 1) _ 0
      (by have := E.hle; omega) E.hopen
    rw [Q.hpref] at ho'
    rw [(Prod.mk.inj (Option.some.inj ho')).1, List.take_take, Nat.min_eq_left E.hroom]
  exact ⟨rc, rhs0, _, Q, hrc, hm, hds, hPref, hFld, hBody, hFn, hAbs, hnPc, hlvls⟩

end Pin

end ConLeche.Model
