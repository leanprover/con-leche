module

public import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.ContInst
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.ContInstRule
import ConLeche.Model.Inductives.StructRecSpine
import ConLeche.Model.Inductives.StructBits
import ConLeche.Model.NatEqs
import ConLeche.Verify.BridgeWfImp
import ConLeche.Model.Annot.BitInst

public section

/-!
# The rule rows at an OUTSIDE class (lane NESTIND, item 3′)

At a recursor whose major is an outside container `C.{us} ds` the rule
data are the target check's at the major (`tgtFdomsAV`, `tgtMkAV`,
`TargetIhData.lean`), and the class is the recorded block `D` holding
`C` (`TgtOutCls`).  O12 (`instCtor_open`, `instCtor_decode`) reads the
rule's opened constructor through `D`'s clause; this file pins that
reading to the target check's rule run (`targetRuleAtG`):

* `tgtOutEs` — the class's index expressions: the recorded result
  indices substituted by `instTau` (no spine-arity fact identifies the
  kernel's `getAppArgs.drop nPc` with them, so an outside class DEFINES
  its `es` as the values the decoding reads);
* `tgtOutDec_core` — **the decoding row**: a spine fitting the rule's
  field domains at a prefix whose key frame satisfies the container's
  parameter telescope hole-fits the recorded constructor at the carrier,
  at the index tuple the class's index expressions read to (F5,
  `LfpClause.resIdxFit`), and the fired spine (`tgtMkAV`) reads to the
  clause's injection.

The satisfaction of the container's parameter telescope at the key frame
(F2-extended, NESTKERN-2) is the row's premise `hsat`: the kernel types
the major's parameters at the rule prefix (F2, `TargetTyEntry.pinTys_of`)
but does not yet compare their types with the container's parameter
telescope.
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

/-- **A read spine read deeper**: its readings lifted past the extra
binders (`denoteMeta_lift`, argument by argument). -/
theorem denoteMetaSpine_liftD {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      (∀ x ∈ as, Expr.WScoped d x) → ∀ k : Nat,
      DenoteMetaSpine acval env φ (d + k) as (vs.map (AnnotTerm.liftN k · 0))
  | _, _, .nil, _, _ => .nil
  | a :: _, _, .cons ha hs, hw, k => by
    refine .cons ?_ (denoteMetaSpine_liftD hacl hs (fun x hx => hw x (List.mem_cons_of_mem _ hx)) k)
    rw [denoteMeta_lift hacl (hw a List.mem_cons_self) _ (Nat.le_add_right _ _), ha,
      Nat.add_sub_cancel_left]
    rfl

/-- The member-format family's constructors at `j` are the major's. -/
theorem tgtRs_ctors {out : List (ConstantVal × TargetMajor × List Expr)} {j : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) : r.2.2.2 = (tgtMajor out j).ctors := by
  simp only [tgtRs, List.getElem?_map] at hr
  cases ho : out[j]? with
  | none => rw [ho] at hr; exact nomatch hr
  | some t =>
    rw [ho] at hr
    obtain rfl := Option.some.inj hr
    simp only [tgtMajor, List.getD_eq_getElem?_getD, ho, Option.getD_some]

/-- **An outside class's index expressions** at the `(j, i)`-th rule:
the recorded result indices of `D`'s member `mm`'s constructor `i`,
substituted by the instantiation's `instTau` (below the rule's `nF`
field binders). -/
@[expose] noncomputable def tgtOutEs {env : Env} (mp : EnvModelM V μ env) (D : LfpDatum V)
    (mm : Nat) (lps : List Name) (M : TargetMajor) (rP : Nat) (ψ : Name → Nat) (i : Nat) :
    List AnnotTerm :=
  (D.resIdx (Level.substFn ψ lps M.lvls) mm i).map fun e =>
    AnnotTerm.substAV (instTau mp ψ D M.lvls rP M.ds) e (M.ctors.getD i default).2

/-- **The decoding row at an outside class** (lane NESTIND, item 3′):
the `(j, i)`-th rule of a recursor whose major is outside, at a prefix
`xs` (the recursor's `rP` parameters) whose key frame satisfies the
container's parameter telescope (`hsat`, F2-extended) and a field spine
`fs` fitting the rule's field domains: `fs` hole-fits `D`'s constructor
at the carrier of the key frame, at the index tuple of the class's index
expressions, and the fired spine reads to the injection. -/
theorem tgtOutDec_core {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {p : BlockShape}
    {outside nested : Bool} {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) p outside nested block cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI)
    -- the class's reading: its levels and parameters at the rule prefix
    (hul : (tgtMajor out j).lvls.length = cvI.levelParams.length)
    (hds : ∀ x ∈ (tgtMajor out j).ds, Expr.WScoped (tgtRP p j) x ∧ x.looseBVarsBounded 0 = true)
    (ψ : Name → Nat) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mpC.base2.acval envC ψ (tgtRP p j) (tgtMajor out j).ds dsa)
    (hlenP : (D.params (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)).length
      = (tgtMajor out j).ds.length)
    {ρ : Nat → V} {xs fs : List V} (hxl : xs.length = tgtRP p j)
    (hsat : Sat V (D.params (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)).reverse
      (keyFrame dsa (tgtRP p j) (consList xs ρ)))
    (hfit : SpineFit (consList xs ρ) (tgtFdomsAV p out mpC.base2.acval envC ψ j i) fs) :
    D.HFits (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
        (keyFrame dsa (tgtRP p j) (consList xs ρ))
        (D.carrier (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
          (keyFrame dsa (tgtRP p j) (consList xs ρ)))
        (tupW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
          ((tgtOutEs mpC D mm cvI.levelParams (tgtMajor out j) (tgtRP p j) ψ i).map
            (interp V (consList (xs ++ fs) ρ))))
        mm i fs ∧
      interp V (consList (xs ++ fs) ρ) (tgtMkAV p out mpC.base2.acval envC ψ j i)
        = D.inj (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) mm i fs ∧
      SpineFit (keyFrame dsa (tgtRP p j) (consList xs ρ))
        (D.ids mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
        ((tgtOutEs mpC D mm cvI.levelParams (tgtMajor out j) (tgtRP p j) ψ i).map
          (interp V (consList (xs ++ fs) ρ))) := by
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, ⟨E⟩, _, _, hFld, _, _, _⟩ :=
    targetRuleAtG R hr hcA hrhs
  subst hMaj
  have hnd := hcl.hnd
  obtain ⟨-, -, -, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hMo
  have hct' : tgtCtorOf out j i = cA := tgtCtorOf_at hr hcA
  -- the fired constructor is the major's `i`-th
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by
    rw [← tgtRs_ctors hr]; exact hcA
  have hiL : i < (tgtMajor out j).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
  have hcAi : (tgtMajor out j).ctors[i] = cA := (List.getElem?_eq_some_iff.mp hcAM).2
  have hiD : i < D.nctors mm := by rw [← hcl.hlen]; exact hiL
  have hfc0 := hcl.hctor i hiL
  rw [hcAi] at hfc0
  have hname : cA.1.name = D.ctorName mm i := Env.find?_name hfc0
  -- the block's members share the constructor's level parameters
  obtain ⟨hclause, -, -, hcrd⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cv', nPc', nF', hf', -, hlpsC, -⟩ := hcrd.2 mm hcl.hmm i hiD
  rw [hfc0] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv' ∧ (tgtMajor out j).nPc = nPc' ∧ cA.2 = nF' := by
    injection hf' with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hlpsI : cvI.levelParams = cA.1.levelParams := by
    obtain ⟨caps, hfI⟩ := hcl.hfind
    obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC mm hcl.hmm
    rw [hcl.hmem, hfI] at hfm
    injection hfm with h; injection h with h1 _
    rw [h1, hlm]
  rw [hlpsI] at hnd hul hlenP hsat ⊢
  have hlps : ∀ mm', mm' < D.k → ∃ cv caps, envC.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = cA.1.levelParams := hlpsC
  -- the constructor's entry at the major's parameter count
  have hfc : envC.find? (D.ctorName mm i)
      = some (.ctorInfo cA.1 (tgtMajor out j).ds.length cA.2) := by
    rw [hdsLen]; exact hfc0
  -- the run's opening of the instantiated constructor
  have hcr : ConLeche.instPisWith (tgtMajor out j).ds
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls) = some Q.crest := by
    have h := Q.hcrest
    simpa [ConLeche.targetCtorAt, hMo] using h
  have hRP : tgtRP p j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hfld : ConLeche.openPisAtFvars cA.2 Q.crest (tgtRP p j) = some (Q.fvsF, Q.cbody) := by
    rw [hRP]; exact Q.hfld
  obtain ⟨-, ab, ⟨Tys, hlT, hTys, hEq⟩, hlab, hrdF, -, -⟩ :=
    instCtor_open mpC hcl.hD hcl.hnN hcl.hkN hlps hnd hul hds hdsa hlenP hcl.hmm hiD hfc hcr hfld
  -- the rule's field domains are the substituted recorded fields
  have hfdoms : tgtFdomsAV p out mpC.base2.acval envC ψ j i
      = (AnnotTerm.substTele (instTau mpC ψ D (tgtMajor out j).lvls (tgtRP p j)
          (tgtMajor out j).ds) 0 ab).map (·.2.2) := by
    rw [tgtFdomsAV, ← hFld, hrdF]
  rw [hfdoms] at hfit
  obtain ⟨hIdsF, hHF, hleaf⟩ := instCtor_decode mpC hcl.hD hcl.hnN hcl.hkN hlps hnd hul hds hdsa hlenP
    hcl.hmm hiD hlT hTys hEq hlab hsat hfit
  have hfl : fs.length = cA.2 := by
    rw [hfit.length_eq, List.length_map, substTele_length, hlab]
  have hES : (tgtOutEs mpC D mm cA.1.levelParams (tgtMajor out j) (tgtRP p j) ψ i).map
        (interp V (consList (xs ++ fs) ρ))
      = (D.resIdx (Level.substFn ψ cA.1.levelParams (tgtMajor out j).lvls) mm i).map fun e =>
          interp V (consList fs (consList xs ρ))
            (AnnotTerm.substAV (instTau mpC ψ D (tgtMajor out j).lvls (tgtRP p j)
              (tgtMajor out j).ds) e cA.2) := by
    rw [tgtOutEs, List.map_map, consList_append, List.getD_eq_getElem?_getD, hcAM,
      Option.getD_some]
    rfl
  refine ⟨by rw [hES]; exact hHF, ?_, by rw [hES]; exact hIdsF⟩
  -- the fired spine: the constant at the major's levels, the parameters, the fields
  have hconst : denoteMeta mpC.base2.acval envC ψ (tgtB p out j i)
      (.const cA.1.name (tgtMajor out j).lvls)
      = some (mpC.base2.acval cA.1.name
          (Level.substFn ψ cA.1.levelParams (tgtMajor out j).lvls)) := by
    rw [hname]
    exact denoteMeta_const (ci := .ctorInfo cA.1 _ cA.2) hfc (by rw [hul]; rfl)
  have hB : tgtB p out j i = tgtRP p j + cA.2 := by rw [tgtB, hct']
  have hdsaL : DenoteMetaSpine mpC.base2.acval envC ψ (tgtB p out j i) (tgtMajor out j).ds
      (dsa.map (AnnotTerm.liftN cA.2 · 0)) := by
    rw [hB]
    exact denoteMetaSpine_liftD mpC.base2.acval_closed hdsa (fun x hx => (hds x hx).1) cA.2
  have hidxF := ConLeche.openPisAtFvars_index _ _ _ hfld
  have hspF := denoteMetaSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    (tgtB p out j i) Q.fvsF (tgtRP p j) hidxF
  rw [openPisAtFvars_length _ hfld] at hspF
  rw [tgtMkAV, hct', ← hFld, denoteMeta_mkAppN_of _ hconst (DenoteMetaSpine.append hdsaL hspF),
    Option.getD_some, interp_mkAppN, foldl_app_map, List.map_append, hB,
    map_fieldBvars hxl hfl, List.map_map]
  have hmapD : dsa.map (interp V (consList (xs ++ fs) ρ) ∘ fun x => AnnotTerm.liftN cA.2 x 0)
      = dsa.map (interp V (consList xs ρ)) := by
    refine List.map_congr_left fun x _ => ?_
    show interp V (consList (xs ++ fs) ρ) (x.liftN cA.2 0) = _
    rw [consList_append, ← hfl, interp_liftN_consList]
  rw [hmapD, acval_interp_closedC mpC.base2 _ _ _ (consList xs ρ), hname]
  exact hleaf

end ConLeche.Model
