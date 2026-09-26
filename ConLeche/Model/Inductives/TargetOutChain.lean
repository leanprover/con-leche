module

public import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutConv
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.StructFrameKit

public section

/-!
# The rule rows at an OUTSIDE class, at the CHAIN frame (lane NESTIND, session 6)

The graph producer (`graphRecPre_core`) reads the rule rows `hrule` and
`hdec` at the chain frame `chainFrame K a ρ`, where the rule data are
the base-frame forms lifted past the `K` chain binders at their own
depths (`liftDomsK`, `liftN`; the member rows' `blockRecFdomsK` etc.).
At an outside class the base-frame forms are the target check's field
domains and fired spine (`tgtFdomsAV`, `tgtMkAV`) and the class's
index expressions (`tgtOutEs`, the substituted recorded result indices).

* `chainFit_base` — the chain move, once: a spine fitting the lifted
  prefix-and-field data at the chain frame fits the base data at the
  base frame (the prefix domains are closed, `blockRecPdomsK_run`);
* `tgtOutDecK` — `hdec` at an outside class;
* `tgtOutRuleK` — `hrule` at an outside class: the prefix, the class's
  index values (which fit the container's index telescope, so the
  recursor's index binders by O13, `tgtOutIdxConv`) and the fired
  spine (the injection, in the carrier at that tuple, which is the
  major's domain there, `tgtOutMajor`) fit the recursor's binder data.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- The target field domains, lifted past `K` chain binders. -/
@[expose] def tgtFdomsK (K : Nat) (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat)
    (c i : Nat) : List AnnotTerm :=
  liftDomsK K (blockRulePdomsAV acval envC p (tgtRs out) ψ c).length
    (tgtFdomsAV p out acval envC ψ c i)

/-- The target fired spine, lifted past `K` chain binders. -/
@[expose] def tgtMkK (K : Nat) (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat)
    (c i : Nat) : AnnotTerm :=
  (tgtMkAV p out acval envC ψ c i).liftN K
    ((blockRulePdomsAV acval envC p (tgtRs out) ψ c).length
      + (tgtFdomsAV p out acval envC ψ c i).length)

/-- An index-expression list, lifted past `K` chain binders at depth `n`. -/
@[expose] def liftEsK (K n : Nat) (es : List AnnotTerm) : List AnnotTerm :=
  es.map fun e => e.liftN K n

/-- **The chain move**: a spine fitting the lifted prefix-and-field data
at the chain frame fits the base data at the base frame, when the prefix
domains are unchanged by the lift. -/
theorem chainFit_base {K : Nat} {a ρ : Nat → V} {pd fd : List AnnotTerm}
    (hpK : liftDomsK K 0 pd = pd) {xs fs : List V} (hxl : xs.length = pd.length)
    (h : SpineFit (chainFrame K a ρ) (pd ++ liftDomsK K pd.length fd) (xs ++ fs)) :
    SpineFit ρ (pd ++ fd) (xs ++ fs) := by
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv h
  have hl₁ : as₁.length = xs.length := by rw [h1.length_eq, hxl]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm hl₁
  rw [← hpK] at h1
  have h1' := (spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) pd [] as₁).mp h1
  rw [← hxl] at h2
  have h2' := (spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) fd as₁ as₂).mp h2
  exact SpineFit.append h1' h2'

section Rows

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {nested : Bool} {block : List ConstantInfo}

variable (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI)

include hμ hcov h R hr hcA hrhs hMo hcl in
/-- **Row `hdec` at an outside class, at the chain frame.** -/
theorem tgtOutDecK (ψ : Name → Nat) (K : Nat) (a ρ : Nat → V)
    {xs fs : List V}
    (hxl : xs.length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length)
    (hsp : SpineFit (chainFrame K a ρ)
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
        ++ tgtFdomsK K mpC.base2.acval envC pp.toBlockShape out ψ j i) (xs ++ fs)) :
    D.HFits (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
        (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList xs ρ))
        (D.carrier (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
          (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
            (tgtRP pp.toBlockShape j) (consList xs ρ)))
        (tupW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
          ((liftEsK K ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length)
            (tgtOutEs mpC D mm cvI.levelParams (tgtMajor out j) (tgtRP pp.toBlockShape j) ψ i)).map
            (interp V (consList (xs ++ fs) (chainFrame K a ρ)))))
        mm i fs ∧
      interp V (consList (xs ++ fs) (chainFrame K a ρ))
          (tgtMkK K mpC.base2.acval envC pp.toBlockShape out ψ j i)
        = D.inj (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) mm i fs ∧
      SpineFit (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList xs ρ))
        (D.ids mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
        ((liftEsK K ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length)
            (tgtOutEs mpC D mm cvI.levelParams (tgtMajor out j) (tgtRP pp.toBlockShape j) ψ i)).map
            (interp V (consList (xs ++ fs) (chainFrame K a ρ)))) := by
  have hpK : liftDomsK K 0 (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
      = blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j :=
    blockRecPdomsK_run (V := V) hμ mpC h hr ψ K
  have hbase := chainFit_base hpK hxl hsp
  have hlen : (xs ++ fs).length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
        + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length := by
    rw [hbase.length_eq, List.length_append]
  have hmapE : ∀ es : List AnnotTerm,
      (liftEsK K ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
          + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length) es).map
        (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
      = es.map (interp V (consList (xs ++ fs) ρ)) := by
    intro es
    rw [liftEsK, List.map_map, ← hlen]
    exact List.map_congr_left fun e _ => interp_liftN_chainFrame (xs ++ fs) e
  have hmk : interp V (consList (xs ++ fs) (chainFrame K a ρ))
        (tgtMkK K mpC.base2.acval envC pp.toBlockShape out ψ j i)
      = interp V (consList (xs ++ fs) ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i) := by
    rw [tgtMkK, ← hlen]; exact interp_liftN_chainFrame (xs ++ fs) _
  rw [hmapE, hmk]
  exact tgtOutDec hμ hcov h R hr hcA hrhs hMo hcl ψ ρ hxl hbase

omit [SetTheory V] in
/-- The recursor's binder data split into the prefix, the index binders
and the major. -/
theorem rds_split3 {L : List AnnotTerm} {rP nI : Nat} (hlen : L.length = rP + nI + 1) :
    L = (L.take rP ++ (L.drop rP).take nI) ++ [L.getD (rP + nI) default] := by
  rw [← List.take_add]
  have hd : L.drop (rP + nI) = [L.getD (rP + nI) default] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  rw [← hd, List.take_append_drop]

include hμ hcov h R hr hcA hrhs hMo hcl in
set_option maxHeartbeats 1000000 in
/-- **Row `hrule` at an outside class, at the chain frame**: the
prefix, the class's index values and the fired spine fit the recursor's
binder data. -/
theorem tgtOutRuleK (ψ : Name → Nat) (K : Nat) (a ρ : Nat → V)
    {xs fs : List V}
    (hxl : xs.length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length)
    (hsp : SpineFit (chainFrame K a ρ)
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
        ++ tgtFdomsK K mpC.base2.acval envC pp.toBlockShape out ψ j i) (xs ++ fs)) :
    SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2))
      (xs ++ ((liftEsK K ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length)
            (tgtOutEs mpC D mm cvI.levelParams (tgtMajor out j) (tgtRP pp.toBlockShape j) ψ i)).map
            (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
        ++ [interp V (consList (xs ++ fs) (chainFrame K a ρ))
            (tgtMkK K mpC.base2.acval envC pp.toBlockShape out ψ j i)])) := by
  obtain ⟨hHF, hmk, hids⟩ := tgtOutDecK hμ hcov h R hr hcA hrhs hMo hcl ψ K a ρ hxl hsp
  have hpK : liftDomsK K 0 (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
      = blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j :=
    blockRecPdomsK_run (V := V) hμ mpC h hr ψ K
  have hbase := chainFit_base hpK hxl hsp
  obtain ⟨xs', fs', heq, hpref, -⟩ := spineFit_append_inv hbase
  have hl₁ : xs'.length = xs.length := by rw [hpref.length_eq, hxl]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm hl₁
  generalize hES : (liftEsK K ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out)
      ψ j).length + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length)
      (tgtOutEs mpC D mm cvI.levelParams (tgtMajor out j) (tgtRP pp.toBlockShape j) ψ i)).map
      (interp V (consList (xs' ++ fs') (chainFrame K a ρ))) = is at hHF hids ⊢
  rw [hmk]
  -- the index values fit the recursor's index binders (O13)
  have hconv := tgtOutIdxConv hμ hcov h R hr hMo hcl ψ ρ xs' is hpref hids
  have hmaj := tgtOutMajor hμ hcov h R hr hMo hcl ψ ρ xs' is hpref hconv
  -- the injection lies in the carrier at the tuple
  obtain ⟨dsa, hdsa, -, -, -, hsatF⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  have hsat := hsatF ρ xs' hpref
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok D hcl.hD
  have hmN : mm < D.N := Nat.lt_of_lt_of_le hcl.hmm hC.kN
  have ht : tupW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)) is
      ∈ˢ D.idx (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
        (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList xs' ρ)) mm := tupW_mem hids
  have hin : D.inj (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) mm i fs'
      ∈ˢ app (D.carrier (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
        (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList xs' ρ)) mm)
        (tupW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)) is) := by
    rw [← hC.carrier_eq hsat hmN]
    exact (hC.fibre _ _ hsat _ (lfpTuple_mem _ _ _ _) mm hmN _ ht _).mpr ⟨i, fs', hHF, rfl⟩
  -- assemble the spine
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hMI : pp.toBlockShape.majorIdxAt j = rc.mI := by
    rw [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hPdE : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
      = ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2)).take
          rc.rP := by
    rw [blockRulePdomsAV, ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc,
      Option.getD_some, List.map_take]
  obtain ⟨-, -, -, -, -, hlenRds, -, -, -, -⟩ := recStage_tyPis (V := V) hμ mpC h hr ψ
  rw [hMI] at hlenRds hmaj
  rw [hRP] at hconv hmaj
  rw [hPdE] at hpref
  have hmI := E.hmI
  have hsplitL := rds_split3 (L := (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out)
    ψ j).map (·.2.2)) (rP := rc.rP) (nI := (tgtMajor out j).nIdx)
    (by rw [List.length_map, hlenRds, hmI])
  rw [← hmI] at hsplitL
  rw [hsplitL, ← List.append_assoc]
  refine SpineFit.append (SpineFit.append hpref hconv) ⟨?_, trivial⟩
  rw [hmaj, ← hRP]; exact hin

include hμ hcov h R hr hcA hrhs hMo hcl in
/-- **The target field domains are bounded at their own depths** at an
outside class: entry `l` is the reading of the `l`-th field opener's
annotation at depth `rP + l`, which is scoped there (the instantiated
constructor is scoped at the prefix, `hds`) and bvar-closed. -/
theorem tgtOutFdoms_bounded (ψ : Name → Nat) :
    ∀ l, l < (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length →
      Term.bvarsBelow (tgtRP pp.toBlockShape j + l)
        (((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default).erase) := by
  obtain ⟨dsa, hdsa, hul, hds, hlenP, -⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfdR, -⟩ :=
    tgtOutOpen R hr hcA hrhs hMo hcl hul hds ψ hdsa hlenP
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, -, -, -, hFld, -⟩ := targetRuleAtG R hr hcA hrhs
  subst hMaj
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  -- the constructor, stored
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by
    rw [← tgtRs_ctors hr]; exact hcA
  have hiL : i < (tgtMajor out j).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
  have hcAi : (tgtMajor out j).ctors[i] = cA := (List.getElem?_eq_some_iff.mp hcAM).2
  have hfc0 := hcl.hctor i hiL
  rw [hcAi] at hfc0
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfc0)
  have hct : ConLeche.targetCtorAt (tgtMajor out j) cA.1
      = cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls := by
    simp [ConLeche.targetCtorAt, hMo]
  have hCf' : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).hasFvar = false := by
    rw [hct, Expr.hasFvar_instantiateLevelParams]; exact hwfC.1
  have hCb' : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).looseBVarsBounded 0 = true := by
    rw [hct, Expr.looseBVarsBounded_instantiateLevelParams]; exact hwfC.2.2.2.1
  -- the instantiated constructor: scoped at the prefix, bvar-closed
  have hcr := Q.hcrest
  rw [ConLeche.instPisWith_eq_instPisAt] at hcr
  obtain ⟨⟨doms, crest'⟩, hinstC, hcr'⟩ := Option.map_eq_some_iff.mp hcr
  obtain rfl : crest' = Q.crest := hcr'
  have hw₂ : Expr.WScoped rc.rP Q.crest :=
    (instPisAt_WScoped (d := rc.rP) _ _ hinstC (Expr.WScoped.of_not_hasFvar hCf')
      (fun a ha => by rw [← hRP]; exact (hds a ha).1)).2
  have hb₂ : Q.crest.looseBVarsBounded 0 = true :=
    (ConLeche.Verify.instPisAt_bounded _ hinstC hCb' (fun a ha => (hds a ha).2)).2
  obtain ⟨-, hlb⟩ := ConLeche.Verify.openPisAtFvars_bounded cA.2 Q.hfld hb₂
  intro l hl
  have hlF : l < Q.fvsF.length := by
    rw [hFld]; rw [tgtFdomsAV, readOpenedDoms_length_eq] at hl; exact hl
  obtain ⟨x, hx⟩ : ∃ x, Q.fvsF[l]? = some x := ⟨_, List.getElem?_eq_getElem hlF⟩
  have hw := openPisAtFvars_typeWScoped _ Q.hfld hw₂ l x hx
  have hrd := hfdR l x (by rw [← hFld]; exact hx)
  rw [hRP] at hrd ⊢
  exact bvarsBelow_of_reading (m := mpC.base2) hw (hlb x (List.mem_of_getElem? hx)) hrd

include hμ hcov h R hr hcA hrhs hMo hcl in
/-- **The chain lift of the target field domains is the identity** at an
outside class (`tgtOutFdoms_bounded`). -/
theorem tgtOutFdomsK_eq (ψ : Name → Nat) (K : Nat) :
    tgtFdomsK K mpC.base2.acval envC pp.toBlockShape out ψ j i
      = tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i := by
  rw [tgtFdomsK, blockRulePdomsAV_length hμ mpC h hr ψ]
  exact liftDomsK_eq_self_of_bounded _ _
    (tgtOutFdoms_bounded hμ hcov h R hr hcA hrhs hMo hcl ψ)

end Rows

end ConLeche.Model
