module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRuleRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Model.Inductives.BlockRuleParams
import ConLeche.Model.Capstone
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRuleCertsRun
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Inductives.BlockKitIhRun
import ConLeche.Model.Inductives.BlockRecGraph
import ConLeche.Model.Inductives.BlockModelRecords

public section

/-!
# `declBlock` at the run — the composition (task #315)

`declBlock` (`DeclBlock.lean`) takes the recursor stage as ONE
hypothesis, `hrec`; `blockRecStaged_data` (`BlockRecData.lean` §A.18)
turns it into the stage's remaining obligations at one environment and
one valuation; the dispatch (`BlockRecPreHpre.lean`) and the rule
contract (`BlockRuleFit.lean`) produce the two largest of them.  This
file is where they meet.

## 1. The `ℓ = 0` arm's LEFT side

The endpoint's `ℓ = 0` arm (`blockRuleRhsOk_base`) asks for two facts:
the stored rule reads as the point (`blockRuleRaZ_seam`, §1b) and the
recursor's TYPE is a truth value.  The second is
here, because it needs the elimination-level package
(`blockRecElimLevel_run`) and the level PIN (`blockRecElimPin_run`),
both downstream of the endpoint's file: the type's binder bits follow
its conclusion's inferred sort, the pin equates that sort with the
checked elimination level `structElimLevel p.elim p.large`, and a
Π-tower whose head bit is `0` is a truth value. -/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section TyZero

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **THE `ℓ = 0` ARM'S LEFT SIDE**: at a valuation where the checked
elimination level is zero, every recursor's type reads as a truth
value — so the recursor's value is the point, and so is every
application of it.  `FixRecLaw.lean`'s `hRpt`, at the block route. -/
theorem blockRecTyZ_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs) :
    ∀ j, j < rs.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0 →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ j) ∈ˢ (univZero : V) := by
  intro j hj ψ ρ hℓ
  obtain ⟨uOf, hbits, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hu : (uOf j).eval ψ = 0 := by
    have := blockRecElimPin_run h hruns ψ hj
    rw [hℓ] at this
    exact this
  obtain ⟨-, -, -, -, heq, hlen, -⟩ :=
    recStage_tyPis (V := V) hμ mpC h (List.getElem?_eq_getElem hj) ψ
  rw [heq]
  cases hrds : blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ j with
  | nil => rw [hrds] at hlen; exact absurd hlen (by simp)
  | cons d rest =>
    have hd : d.2.1 = 0 :=
      (hbits ψ j hj d (by rw [hrds]; exact List.mem_cons_self)).mpr hu
    show interp V ρ (.pi d.1 d.2.1 d.2.2 _) ∈ˢ _
    rw [interp_pi, hd]
    exact piR_zero_mem_univZero

end TyZero

/-! ## 1b. `BlockMembersRun` at the seam

The recursor model and the recursor type's split take the block's
members' run facts as ONE record, `BlockMembersRun`
(`BlockRecTyShapeRun.lean`).  At the run's own
block data (`blockDataOf`, which the seam hands) it is the
constructors' three records read member by member: the names and the
count off `BlockNamesOk`, the former's storage, reading and leaf off
`BlockCtorsCore`, the leaf's λ-shape and the parameter agreement off
`BlockCtorsStage`, the former's closedness off the environment's
well-formedness. -/

section MembersRun

variable {envC envI : Env} {pp : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {mpC : EnvModelM V μ envC} {F : Nat}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
 
  {env₀ : Env} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}

/-- **`BlockMembersRun` from the constructors' three records**, at the
run's own block data. -/
theorem blockMembersRun_seam
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k) :
    BlockMembersRun mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.toBlockShape
      cvTas := by
  obtain ⟨hname, -, -, hlen⟩ := hN
  refine ⟨rfl, rfl, hlen, ?_, ?_, ?_, ?_⟩
  · intro m cvTb hcv
    have hm : m < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hcv).1
    obtain ⟨hfind, -, -, hFD⟩ := hcore.1 m cvTb hcv
    have hwf := mpC.base2.wf _ (List.mem_of_find?_eq_some hfind)
    exact ⟨hname m cvTb hcv, hS.lpsT m cvTb hm hcv, ⟨_, hfind⟩, hwf.1, hwf.2.2.2.1, hFD⟩
  · intro m ms hms
    have hm : m < pp.toBlockShape.members.length := (List.getElem?_eq_some_iff.mp hms).1
    have hg : pp.toBlockShape.members.getD m default = ms := by
      rw [List.getD_eq_getElem?_getD, hms]; rfl
    refine ⟨?_, ?_⟩
    · show (pp.toBlockShape.members.map (·.cvT.name)).getD m .anonymous = ms.cvT.name
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hms]; rfl
    · show pp.toBlockShape.nIdxs.getD m 0 = ms.nIdx
      rw [blockNIdxs_getD hm, hg]
  · intro m ψ hm
    obtain ⟨cvTb, hcv⟩ : ∃ cvTb, cvTas[m]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hm)⟩
    obtain ⟨-, -, hleaf, -⟩ := hcore.1 m cvTb hcv
    rw [hname m cvTb hcv, hleaf ψ, hS.leaf m ψ]
    exact ⟨_, rfl⟩
  · intro m hm ψ ρ
    have h0 : 0 < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) hm
    exact ⟨fun h => hS.paramsOf m hm ψ ρ h 0 h0, fun h => hS.paramsOf 0 h0 ψ ρ h m hm⟩

/-- **The block's representation at the seam** — `blockModelAt_of_records`
with its four identifications `rfl` at the run's own block data, and
`0 < k` off the counting pass's first clause. -/
theorem blockModelAt_seam
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.RecStageOk μ F envC pp cvTas ctorsAs rs)
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    (hlfp : (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).toLfp
      ∈ mpC.lfpBlocks) :
    BlockModelAt mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).memberNames
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) := by
  obtain ⟨R⟩ := id h
  -- the operator's monotonicity is the recorded clause's (lane HOLE2: the
  -- install derived it from positivity when it recorded the clause)
  exact blockModelAt_of_records hN hS hcore rfl R.fam.k_pos (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun ψ ρp hs => ((mpC.lfpClause_of_mem hlfp).functor ψ ρp hs).1)
    (mpC.lfpClause_of_mem hlfp).fitsMono

/-- **The seam's canonical constructor-type reading**: the stored type
of recursor `j`'s `i`-th constructor, read at the constructors'
environment.  `blockRecCtor_seam` shows the reading is never the
default for a constructor a recursor carries. -/
noncomputable def blockRecCtorTy (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) (j i : Nat)
    (ψ : Name → Nat) : AnnotTerm :=
  (denoteMeta acval envC ψ 0 ((rs.getD j default).2.2.2.getD i default).1.type).getD default

/-- **`hctor` at the seam** — every constructor a recursor carries is
STORED with the block's parameter count and its type reads, off the
constructors' core record at the member the recursor's list is. -/
theorem blockRecCtor_seam
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.RecStageOk μ F envC pp cvTas ctorsAs rs)
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) cvTas)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM c)) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 pp.nP cA.2) ∧
        ConstsBound envC cA.1.type ∧
        ∀ ψ : Name → Nat,
          denoteMeta mpC.base2.acval envC ψ 0 cA.1.type
            = some (blockRecCtorTy mpC.base2.acval envC rs j i ψ) := by
  intro j r hr i cA hcA
  obtain ⟨c, hc⟩ := recStage_ctorsIdx h r (List.mem_of_getElem? hr)
  have hcl : c < ctorsAs.length := (List.getElem?_eq_some_iff.mp hc).1
  have heq : r.2.2.2
      = (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM c :=
    Option.some.inj (hc.symm.trans (hctorsAs c hcl))
  rw [heq] at hcA
  have hck : c < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k := by
    rw [← hN.2.2.2]; exact hN.2.2.1 c i cA hcA
  obtain ⟨hfind, -, -⟩ := hcore.2.2.2 c hck i cA hcA
  obtain ⟨hres, -, hdat⟩ := hcore.2.2.1 c i cA hcA
  have hread := hdat.read
  have hrd : rs.getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
  have hsel : ((rs.getD j default).2.2.2.getD i default) = cA := by
    rw [hrd, heq, List.getD_eq_getElem?_getD, hcA]; rfl
  refine ⟨hfind, constsBound_of_constsResolve _ hres, fun ψ => ?_⟩
  rw [blockRecCtorTy, hsel, hread ψ]
  rfl

omit [SetTheory V] in
/-- A field chain whose entries are bounded one by one is bounded. -/
theorem fieldsBelow_of_getD :
    ∀ {m : Nat} {Fs : List AnnotTerm},
      (∀ q, q < Fs.length → Term.bvarsBelow (m + q) (Fs.getD q default).erase) →
      FieldsBelow m Fs
  | _, [], _ => trivial
  | m, _ :: Fs, h => by
    refine ⟨by simpa using h 0 (by simp), fieldsBelow_of_getD (m := m + 1) (Fs := Fs)
      fun q hq => ?_⟩
    have := h (q + 1) (by simpa using hq)
    simpa [show m + (q + 1) = m + 1 + q from by omega] using this

/-- **`heqB` at the run** — the equation list at the PINNED `ihs`/`Rb0`
is bounded below the chain: `bvarsBelow_blockIotaEqsAV`, each of its six
component bounds paid at the run (the prefix by `blockRulePdomsAV_bounded`,
the fields and indices by the constructor's record lifted past the rule
prefix, the fired spine by its own shape, `ihs` by
`blockRuleIhsRunAV_below`, `Rb0` by `blockRuleRbAV_below`).  The kinds'
coverage (`hkLen`) is what gives every constructor its rule. -/
theorem blockRecEqs_below_gen (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.RecStageOk μ F envC pp cvTas ctorsAs rs)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    -- the two rows the rule stage's abstraction supplies, at every stored rule
    (hihB : ∀ (ψ : Name → Nat) (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs →
      ∀ v ∈ ihs ψ c j,
        Term.bvarsBelow (rs.length + pp.toBlockShape.rulePrefixAt c + cA.2) v.erase)
    (hRbB : ∀ (ψ : Name → Nat) (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs →
      Term.bvarsBelow (pp.toBlockShape.rulePrefixAt c + cA.2 + (ihs ψ c j).length)
        (Rb0 ψ c j).erase) :
    ∀ ψ : Name → Nat,
      ∀ e ∈ blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          ihs
          (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          Rb0 ψ,
        Term.bvarsBelow rs.length e.erase := by
  intro ψ
  -- every (recursor, constructor) pair of the list has its rule
  have hpair : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∃ (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) (cA : ConstantVal × Nat)
        (rhs : Expr), rs[c]? = some r ∧ r.2.2.2[j]? = some cA ∧ r.2.1[j]? = some rhs := by
    intro c hc j hj
    have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
    have hjl : j < rs[c].2.2.2.length := by
      rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
    have hlen := recStage_rulesLen h hr
    exact ⟨rs[c], rs[c].2.2.2[j], rs[c].2.1[j]'(by omega), hr, List.getElem?_eq_getElem hjl,
      List.getElem?_eq_getElem _⟩
  -- the record's facts at a pair
  have hrec : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat), r.2.2.2[j]? = some cA →
      ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
          (pp.toBlockShape.recTgtAt c))[j]? = some cA ∧
        pp.toBlockShape.recTgtAt c
          < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k := by
    intro c r hr j cA hcA
    obtain ⟨ms, hms, hctA, -⟩ := recStage_ctorsAt h hr
    refine ⟨?_, (List.getElem?_eq_some_iff.mp hms).1⟩
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  show ∀ e ∈ blockIotaEqsAV rs.length (blockRecNCt rs) _ _ _ _ _ _, _
  refine bvarsBelow_blockIotaEqsAV (fun c hc => ?_) (fun c hc j hj => ?_) (fun c hc j hj => ?_)
    (fun c hc j hj => ?_) (fun c hc j hj => ?_) (fun c hc j hj => ?_)
  · -- the prefix
    have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
    exact fieldsBelow_of_getD fun q hq => by
      rw [Nat.zero_add]; exact blockRulePdomsAV_bounded hμ mpC h hr ψ q hq
  all_goals
    dsimp only
    obtain ⟨r, cA, rhs, hr, hcA, hrhs⟩ := hpair c hc j hj
    obtain ⟨hcj, hmemk⟩ := hrec c r hr j cA hcA
    obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
    have hcd := blockCtorData_of_core hcore hcj
    have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
    have hCf : cA.1.type.hasFvar = false := hwfC.1
    have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
    have hcbC : ConstsBound envC cA.1.type := constsBound_of_constsResolve _ hwfC.2.2.1
    obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
    have hnP := TE.nP_le
    have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
    have hks : (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ksF
        (pp.toBlockShape.recTgtAt c) j = (blockRuleKsOf pp c j).map ConLeche.BlockFieldKind.toRec := by
      rw [blockDataOf_ksF]; rfl
    have hfd := (blockRuleFdomsAV_eq h hr hcA hrhs hcd hCf hnP ψ)
    have hfl : (blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 := by
      rw [blockRuleFdomsAV, readOpenedDoms_length_eq]
      obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, -, -, h₂, -, -, -, -, -⟩ :=
        blockRuleData_run h hr hcA hrhs
      exact openPisAtFvars_length _ h₂
  · -- the fields
    rw [hpl, hfd.1]
    have hd := ConLeche.Model.DomsBelow.drop pp.nP (hcd.below ψ)
    rw [Nat.zero_add] at hd
    have := fieldsBelow_liftDomsK_at (pp.toBlockShape.rulePrefixAt c - pp.nP) (k := 0) hd.fields
    rwa [show pp.nP + (pp.toBlockShape.rulePrefixAt c - pp.nP)
      = pp.toBlockShape.rulePrefixAt c from by omega] at this
  · -- the index expressions
    intro e he
    rw [blockRuleEsAV_eq h hr hcA hrhs hcd hCf hnP ψ] at he
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp he
    rw [hpl, hfl]
    have hE' : Term.bvarsBelow (pp.nP + cA.2) E.erase := hcd.belowE ψ E hE
    exact bvarsBelow_liftN_add hE' (by omega) _
  · -- the fired spine
    rw [hpl, hfl, blockRuleMkAV_eq h hr hcA hrhs hfindC hlpsC hnP ψ, AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN ?_ ?_
    · rw [mpC.base2.acval_erase]
      exact Term.bvarsBelow.mono (Nat.zero_le _) (mpC.base2.cval_closed _ _)
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
        have := List.mem_range.mp hk
        show _ < _
        omega
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
        have := List.mem_range.mp hk
        show _ < _
        omega
  · -- the `ih` terms
    intro v hv
    rw [hpl, hfl]
    exact hihB ψ c r hr j cA rhs hcA hrhs v hv
  · -- the residue
    rw [hpl, hfl]
    exact hRbB ψ c r hr j cA rhs hcA hrhs

/-- **`heqP`'s equation half at the run** — the equation list at the
PINNED `ihs`/`Rb0` reads alike at two level valuations agreeing on ANY
recursor's parameters (the block's recursors share them,
`recStage_lps`): every component is ψ-congruent there
(`BlockRuleParams.lean` §3) — the prefix through the recursor type's
reading, the fields, indices and `ih` terms through the constructors'
record (`params`, `tssParams`, `eissParams`; the constructor's
parameters are the block's, a sub-list of the recursor's), the fired
spine through the leaf's `acval_params`, and the residue through its
footprint (`lpDefF`).  The kinds' coverage (`hkLen`) gives every
constructor its rule. -/
theorem blockRecEqs_params_gen (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.RecStageOk μ F envC pp cvTas ctorsAs rs)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    -- the two rows the rule stage's abstraction supplies, at every stored rule
    (hihP : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → ihs ψ₁ c j = ihs ψ₂ c j)
    (hRbP : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → Rb0 ψ₁ c j = Rb0 ψ₂ c j) :
    ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        blockRecEqs (blockRecNCt rs) rs
            (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            ihs
            (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            Rb0 ψ₁
          = blockRecEqs (blockRecNCt rs) rs
            (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            ihs
            (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            Rb0 ψ₂ := by
  intro i₀ r₀ hr₀ ψ₁ ψ₂ hq₀
  -- every (recursor, constructor) pair of the list has its rule
  have hpair : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∃ (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) (cA : ConstantVal × Nat)
        (rhs : Expr), rs[c]? = some r ∧ r.2.2.2[j]? = some cA ∧ r.2.1[j]? = some rhs := by
    intro c hc j hj
    have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
    have hjl : j < rs[c].2.2.2.length := by
      rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
    have hlen := recStage_rulesLen h hr
    exact ⟨rs[c], rs[c].2.2.2[j], rs[c].2.1[j]'(by omega), hr, List.getElem?_eq_getElem hjl,
      List.getElem?_eq_getElem _⟩
  show blockIotaEqsAV rs.length (blockRecNCt rs) _ _ _ _ _ _
    = blockIotaEqsAV rs.length (blockRecNCt rs) _ _ _ _ _ _
  refine blockIotaEqsAV_congr (fun c hc => blockRulePdomsAV_params hμ mpC h hr₀ hq₀ hc)
    (fun c hc j hj => ?_)
  obtain ⟨r, cA, rhs, hr, hcA, hrhs⟩ := hpair c hc j hj
  have hq : ∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q := by
    rw [recStage_lps h hr hr₀]; exact hq₀
  obtain ⟨ms, hms, hctA, -⟩ := recStage_ctorsAt h hr
  have hmemk : pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms).1
  have hcj : ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  have hcd := blockCtorData_of_core hcore hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
  have hnP := TE.nP_le
  have hks : (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ksF
      (pp.toBlockShape.recTgtAt c) j = (blockRuleKsOf pp c j).map ConLeche.BlockFieldKind.toRec := by
    rw [blockDataOf_ksF]; rfl
  have hqL : ∀ q ∈ pp.lps, ψ₁ q = ψ₂ q := fun q hq' => hq q (recStage_lps_sub h hr q hq')
  have hqC : ∀ q ∈ cA.1.levelParams, ψ₁ q = ψ₂ q := by rw [hlpsC]; exact hqL
  exact ⟨blockRuleFdomsAV_params h hr hcA hrhs hcd hCf hnP hqC,
    blockRuleEsAV_params h hr hcA hrhs hcd hCf hnP hqC,
    hihP c r hr j cA rhs hcA hrhs ψ₁ ψ₂ hq,
    blockRuleMkAV_params h hr hcA hrhs hfindC hlpsC hnP hqL,
    hRbP c r hr j cA rhs hcA hrhs ψ₁ ψ₂ hq⟩

/-- **The constructor's index readings are bit-valid at the rule's
frame** — off the constructor's own stored type: its reading is graded
at every valuation (`CtorDataI.okTy`), so at a spine fitting its binder
data its conclusion — the member at the parameters and the index
readings — is valid, and so is each reading.  The rule frame's values
fit that binder data: the parameters through the family's parameter
agreement (`blockRuleParamFit_run`, the stage's `frames`), the fields
through the lifting past the prefix's extra binders
(`spineFit_liftDomsK_insert`). -/
theorem blockRuleEsAV_valid_seam (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.RecStageOk μ F envC pp cvTas ctorsAs rs)
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {j : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[j]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[j]? = some rhs) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c
        ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j) ys →
      ∀ e ∈ blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j,
        AnnotValid V (consList ys ρ) e := by
  intro ys hys e he
  -- the member link and the constructor's record
  obtain ⟨ms, hms, hctA, -⟩ := recStage_ctorsAt h hr
  have hmemk : pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms).1
  have hcj : ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  have hcd := blockCtorData_of_core hcore hcj
  have hCf : cA.1.type.hasFvar = false := (mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)).1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
  have hnP := TE.nP_le
  rw [blockRuleEsAV_eq h hr hcA hrhs hcd hCf hnP ψ] at he
  obtain ⟨E, hE, rfl⟩ := List.mem_map.mp he
  -- the frame's two segments
  have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
  obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, -, -, h₂, -⟩ := blockRuleData_run h hr hcA hrhs
  have hflen : (blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 := by
    rw [blockRuleFdomsAV, readOpenedDoms_length_eq, openPisAtFvars_length _ h₂]
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_inv hys
  have hxl : xs.length = pp.toBlockShape.rulePrefixAt c := by rw [hxs.length_eq, hpl]
  have hfl : fs.length = cA.2 := by rw [hfs.length_eq, hflen]
  have hod : (xs.drop pp.nP).length = pp.toBlockShape.rulePrefixAt c - pp.nP := by
    rw [List.length_drop, hxl]
  -- the index reading, back at the constructor's own frame
  rw [AnnotValid_liftN, consList_append, ← hfl, shiftE_consList_len,
    shiftE_drop_consList xs pp.nP hod ρ]
  -- the rule frame's values fit the constructor's binder data
  have hMR := blockMembersRun_seam hN hS hcore
  have hcvl : pp.toBlockShape.recTgtAt c < cvTas.length := by rw [hMR.2.2.1]; exact hmemk
  obtain ⟨-, -, ⟨caps, hfT⟩, -, -, hFD⟩ :=
    hMR.2.2.2.1 _ cvTas[pp.toBlockShape.recTgtAt c] (List.getElem?_eq_getElem hcvl)
  have hps := blockRuleParamFit_run hμ mpC h hr ψ (List.getElem?_eq_getElem hcvl) hfT hFD
    (by rw [hMR.1]; exact Nat.le_add_right _ _) (hcd.len ψ) (fun ρ' => (hS.frames _ hmemk j cA hcj).1 ψ ρ')
    (spineFit_take_any hxs pp.nP)
  have hfs' : SpineFit (consList (xs.take pp.nP) ρ)
      ((((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).dsF
        (pp.toBlockShape.recTgtAt c) j ψ).drop pp.nP).map (·.2.2)) fs := by
    have hq := (spineFit_liftDomsK_insert (us := xs.drop pp.nP) (ρ := consList (xs.take pp.nP) ρ)
      ((((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).dsF
        (pp.toBlockShape.recTgtAt c) j ψ).drop pp.nP).map (·.2.2)) [] fs)
    rw [List.length_nil, hod, consList_nil, consList_nil, ← consList_append,
      List.take_append_drop, ← (blockRuleFdomsAV_eq h hr hcA hrhs hcd hCf hnP ψ).1] at hq
    exact hq.mp hfs
  have hfit : SpineFit ρ (((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).dsF
      (pp.toBlockShape.recTgtAt c) j ψ).map (·.2.2)) (xs.take pp.nP ++ fs) := by
    rw [← List.take_append_drop pp.nP ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk
      uOfD ppsOf).dsF (pp.toBlockShape.recTgtAt c) j ψ), List.map_append]
    exact SpineFit.append hps hfs'
  -- the constructor's conclusion is valid there, and so is each index reading
  obtain ⟨-, hB⟩ := AnnotValid_mkPisAV_inv (hcd.okTy ψ ρ).2
  have hb := hB _ hfit
  rw [ctorBodyAVI, consList_append] at hb
  exact (AnnotValid.mkAppN_inv hb).2 E (List.mem_append_right _ hE)

/-- **`heqV` at the run, through the grading** — the equation list at
the PINNED `ihs`/`Rb0` is bit-valid at every typed tuple:
`annotValid_blockIotaEqsAV` with

* the frame's validity off the GRADING (`hokA`, `blockRuleHokA_of_run`'s
  conclusion — the spelling `blockRuleGrading_run` produces), through `fieldsValid_of_grading`;
* the fired spine's validity FREE (a leaf applied to bound variables,
  `acval_validV`);
* the residue's validity off its own TYPING at the frame
  (`blockRuleRbAV_wdV_run`: the stage's `inferTypeCore` run, the
  openers' readings and the same grading), at the `ih` values the owed
  row fits;
* the `ih` terms' validity off the grading's FIELD segment
  (`blockRuleIhsRunAV_valid_run`: a field's domain is the Π-tower over
  its telescope of the target former at the field's index readings);
* the index readings' validity off the constructor's stored type
  (`blockRuleEsAV_valid_seam`);
* the typed tuple's `ih` fit OWED (`BlockIhFitTypedOwed`). -/
theorem blockRecEqs_valid_gen (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.RecStageOk μ F envC pp cvTas ctorsAs rs)
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    -- the frame's grading at the prefix and the fields
    (hokPF : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      ∀ ψ : Name → Nat,
      ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j
            ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j
            ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i).getD l default))
    {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    -- the two rows the rule stage's abstraction supplies, at every typed tuple
    (hihV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c
        ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j) ys →
      ∀ v ∈ ihs ψ c j, AnnotValid V (consList ys (consList tup ρ)) v)
    (hRbV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c
        ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j) ys →
      AnnotValid V (consList ((ihs ψ c j).map (interp V (consList ys (consList tup ρ))))
        (consList ys ρ)) (Rb0 ψ c j)) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ e ∈ blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          ihs
          (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          Rb0 ψ,
        AnnotValid V (consList tup ρ) e := by
  intro ψ ρ tup hlen htyp
  have hcf := consList_eq_chainFrame hlen ρ
  -- every (recursor, constructor) pair of the list has its rule, and its record
  have hpair : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∃ (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) (cA : ConstantVal × Nat)
        (rhs : Expr), rs[c]? = some r ∧ r.2.2.2[j]? = some cA ∧ r.2.1[j]? = some rhs := by
    intro c hc j hj
    have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
    have hjl : j < rs[c].2.2.2.length := by
      rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
    have hlen := recStage_rulesLen h hr
    exact ⟨rs[c], rs[c].2.2.2[j], rs[c].2.1[j]'(by omega), hr, List.getElem?_eq_getElem hjl,
      List.getElem?_eq_getElem _⟩
  have hfl : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs →
      (blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 := by
    intro c r hr j cA rhs hcA hrhs
    rw [blockRuleFdomsAV, readOpenedDoms_length_eq]
    obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, -, -, h₂, -⟩ := blockRuleData_run h hr hcA hrhs
    exact openPisAtFvars_length _ h₂
  rw [hcf]
  refine annotValid_blockIotaEqsAV (a := fun c => tup.getD c pt) (ρ := ρ)
    (fun c hc j hj => ?_) (fun c hc j hj ys hys => ?_)
  · -- the frame, off the grading
    dsimp only
    obtain ⟨r, cA, rhs, hr, hcA, hrhs⟩ := hpair c hc j hj
    have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
    have hfl' := hfl c r hr j cA rhs hcA hrhs
    refine fieldsValid_of_grading _ (fun l hl ys hys => ?_)
    have hl' : l < pp.toBlockShape.rulePrefixAt c + cA.2 := by
      rw [List.length_append, hpl, hfl'] at hl; exact hl
    exact (hokPF c r hr j cA hcA ψ l hl' ρ ys hys).2
  · dsimp only at hys ⊢
    obtain ⟨r, cA, rhs, hr, hcA, hrhs⟩ := hpair c hc j hj
    -- the constructor's record
    obtain ⟨ms, hms, hctA, -⟩ := recStage_ctorsAt h hr
    have hmemk : pp.toBlockShape.recTgtAt c
        < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
      (List.getElem?_eq_some_iff.mp hms).1
    have hcj : ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
        (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
      show (ctorsAs.getD _ [])[j]? = _
      rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
    obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
    have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
    obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
    have hnP := TE.nP_le
    have hks : (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ksF
        (pp.toBlockShape.recTgtAt c) j
        = (blockRuleKsOf pp c j).map ConLeche.BlockFieldKind.toRec := by
      rw [blockDataOf_ksF]; rfl
    refine ⟨blockRuleEsAV_valid_seam hμ h hN hS hcore hr hcA hrhs ψ ρ ys hys, ?_,
      by rw [← hcf]; exact hihV ψ ρ tup hlen htyp c r hr j cA rhs hcA hrhs ys hys, ?_⟩
    · -- the fired spine: a leaf applied to bound variables
      rw [blockRuleMkAV_eq h hr hcA hrhs hfindC hlpsC hnP ψ]
      refine annotValid_mkAppN (mpC.acval_validV _ _ _) (fun a ha => ?_)
      rcases List.mem_append.mp ha with ha | ha
      · simp only [paramBvarsAt, List.mem_map] at ha
        obtain ⟨k, -, rfl⟩ := ha
        trivial
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
        trivial
    · -- the residue
      rw [← hcf]
      exact hRbV ψ ρ tup hlen htyp c r hr j cA rhs hcA hrhs ys hys

/-- **THE RULE CONTRACT AT THE SEAM, its residue conjunct a premise**
(lane RECLIB): `blockRuleDataB_seam` at any `ihs`/`Rb0` whose residue
conjunct follows from the rule's reading and the contract's first
conjunct. -/
theorem blockRuleDataB_seam_gen (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.RecStageOk μ F envC pp cvTas ctorsAs rs)
    (hndM : pp.toBlockShape.memberNames.Nodup)
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    (hlfp : (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).toLfp
      ∈ mpC.lfpBlocks)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM c))
    {s : (Name → Nat) → Nat} {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (heqB : ∀ ψ : Name → Nat,
      ∀ e ∈ blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          ihs (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ') Rb0 ψ,
        Term.bvarsBelow rs.length e.erase)
    (heqV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ e ∈ blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          ihs (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ') Rb0 ψ,
        AnnotValid V (consList tup ρ) e)
    (heqP : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂ ∧
          blockRecEqs (blockRecNCt rs) rs
              (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
              (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
              (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
              ihs (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ') Rb0 ψ₁
            = blockRecEqs (blockRecNCt rs) rs
              (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
              (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
              (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
              ihs (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ') Rb0 ψ₂)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          ihs (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ') Rb0 ψ) ρ)
    -- the residue conjunct, given the rule's reading and the contract's first conjunct
    (hres : ∀ m₃ : EnvModel V (consBlockRecs envC.find? pp.toBlockShape pp.nP 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s
        (blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          ihs (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ') Rb0) →
      ∀ (φ : Name → Nat) (j : Nat)
        (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      (∀ us : List Level, us.length = r.1.levelParams.length →
        denoteMeta m₃.acval (consBlockRecs envC.find? pp.toBlockShape pp.nP 0 rs envC)
            (Level.substFn φ r.1.levelParams us) 0 rhs
          = some (blockRuleRaOf m₃.acval
              (consBlockRecs envC.find? pp.toBlockShape pp.nP 0 rs envC) rhs
              (Level.substFn φ r.1.levelParams us))) →
      (∀ us : List Level, us.length = r.1.levelParams.length →
        Level.eval (Level.substFn φ r.1.levelParams us)
          (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0 →
        ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
          xs.length = pp.toBlockShape.majorIdxAt j → ys.length = pp.nP + cA.2 →
          usj.length = cA.1.levelParams.length →
          Level.substFn φ cA.1.levelParams usj
            = Level.substFn φ cA.1.levelParams
                (ConLeche.recFireComparands
                  (ConLeche.recRuleBits envC.find? r.1.name
                    { ctor := cA.1.name, nfields := cA.2, ctorParams := pp.nP,
                      fire := .plain, rhs := rhs, paramsBlind := true })
                  r.1.levelParams us cA.1.levelParams [] (pp.toBlockShape.rulePrefixAt j)).1 →
          IotaIndexPin (V := V) ρ restC pp.nP
            (pp.toBlockShape.majorIdxAt j) (pp.toBlockShape.rulePrefixAt j) xs →
          TeleFitPA V ρ
            (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j)
            (xs ++ [AnnotTerm.mkAppN
              (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
          TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC rs j i
            (Level.substFn φ cA.1.levelParams usj)) ys restC →
          SpineFit ρ
            (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs
                (Level.substFn φ r.1.levelParams us) j
              ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC
                  (Level.substFn φ r.1.levelParams us) j i)
            ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
              ++ (ys.drop pp.nP).map (interp V ρ))) →
      BlockRuleResidueB (V := V) mpC pp rs s (blockRecNCt rs)
        (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
        (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
        (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
        ihs (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ') Rb0
        (blockRecCtorTy mpC.base2.acval envC rs j i) φ j i r cA
        (ConLeche.recRuleBits envC.find? r.1.name
          { ctor := cA.1.name, nfields := cA.2, ctorParams := pp.nP,
            fire := .plain, rhs := rhs, paramsBlind := true }) rhs) :
    ∀ m₃ : EnvModel V (consBlockRecs envC.find? pp.toBlockShape pp.nP 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s
        (blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          ihs (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ') Rb0) →
    ∀ (φ : Name → Nat) (j : Nat)
        (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        BlockRuleDataB (V := V) mpC pp rs s (blockRecNCt rs)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          ihs (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ') Rb0
          (blockRecCtorTy mpC.base2.acval envC rs j i) φ j i r cA
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := pp.nP,
              fire := .plain, rhs := rhs, paramsBlind := true }) rhs := by
  intro m₃ hac φ j r hr i cA rhs hcA hrhs
  have hj : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  have hM := blockModelAt_seam h hN hS hcore hlfp
  have hmr := blockMembersRun_seam hN hS hcore
  -- the member link and the constructor's facts
  obtain ⟨ms, hms, hctA, hlenms⟩ := recStage_ctorsAt h hr
  have hmemk : pp.toBlockShape.recTgtAt j
      < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms).1
  have hctM : (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt j) = r.2.2.2 := by
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hcj : ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt j))[i]? = some cA := by rw [hctM]; exact hcA
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk i cA hcj
  obtain ⟨-, -, hcd⟩ := hcore.2.2.1 _ i cA hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
  have hcvTa := TE.hcvTa
  have hnP := TE.nP_le
  -- the elimination level package, and the pin
  obtain ⟨uOf, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hk0 : 0 < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hmemk
  -- the rule's reading, off the leaf's facts
  obtain ⟨hreadR, hokR⟩ :=
    blockRuleRhs_read_run hμ mpC h hndM
      (blockRecLeafAV_closed hμ mpC h heqB) (blockRecLeafAV_liftN hμ mpC h heqB)
      (blockRecLeafAV_par_run hμ mpC h heqP) (fun ψ _ hi ρ => blockRecLeafAV_wd hpre ψ hi ρ)
      (blockRecLeafAV_valid hμ mpC h heqV) hpre m₃ hac r (List.mem_of_getElem? hr) rhs
      (List.mem_of_getElem? hrhs)
  have hreadM : ∀ us : List Level, us.length = r.1.levelParams.length →
      denoteMeta m₃.acval (consBlockRecs envC.find? pp.toBlockShape pp.nP 0 rs envC)
          (Level.substFn φ r.1.levelParams us) 0 rhs
        = some (blockRuleRaOf m₃.acval
            (consBlockRecs envC.find? pp.toBlockShape pp.nP 0 rs envC) rhs
            (Level.substFn φ r.1.levelParams us)) := by
    intro us _
    rw [← denoteMeta_instLevels (acvalParamsAt_of_core m₃) (ks := r.1.levelParams) (us := us) φ]
    exact hreadR φ us
  refine blockRuleDataB_run_gen (mem := pp.toBlockShape.recTgtAt) (jc := i)
    (K := rs.length) hM hμ h rfl rfl rfl rfl hr hcA hrhs rfl hcj ⟨hfindC, hlpsC, hcd⟩ hlpsC rfl
    hnP hmemk hj ((blockRecCtor_seam h hN hcore hctorsAs j r hr i cA hcA).2.2)
    (fun us _ => blockRuleFdomsAV_datum h hr hcA hrhs hcore hmemk hcj hnP rfl _)
    ?hes ?hlenP ?hparamsC
    (fun us _ ρ => blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl _ ρ))
    ?hlarge ?hct1 ?hread ?hokRa hCf hCb
    (fun us _ => (blockRuleFdomsAV_eq h hr hcA hrhs hcd hCf hnP _).2)
    ?hokF (hres m₃ hac φ j r hr i cA rhs hcA hrhs hreadM)
  case hes =>
    intro us _
    rw [blockRuleEsAV_eq h hr hcA hrhs hcd hCf hnP _]
    exact congrArg (List.map _) (essOfR_fixCtorDataList_getD hcj).symm
  case hlenP =>
    intro us _
    have hl := hS.lenPps 0 (Level.substFn φ r.1.levelParams us) hk0
    show (((ppsOf 0 _).take pp.toBlockShape.nP).map (·.2.2)).length = pp.toBlockShape.nP
    rw [List.length_map, List.length_take]
    exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hl.symm))
  case hparamsC =>
    intro us _ σ
    exact ⟨fun hσ => ((hS.frames _ hmemk i cA hcj).1 _ σ).mp (hS.paramsOf 0 hk0 _ σ hσ _ hmemk),
      fun hσ => hS.paramsOf _ hmemk _ σ (((hS.frames _ hmemk i cA hcj).1 _ σ).mpr hσ) 0 hk0⟩
  case hlarge =>
    intro us _ hne _
    refine blockRecLarge_run h hruns (Level.substFn φ r.1.levelParams us) hj ?_
    rw [blockRecElimPin_run h hruns _ hj]
    exact hne
  case hct1 =>
    intro us _ hne hw0
    obtain ⟨-, -, -, -, hc⟩ := blockRecCounting_run h hruns _ hne hw0
    rw [hctM, hlenms]
    exact Nat.le_trans (numCtorsOf_ge_of_mem (List.mem_of_getElem? hms)) hc
  case hread =>
    intro us _
    rw [← hac, ← denoteMeta_instLevels (acvalParamsAt_of_core m₃) (ks := r.1.levelParams)
      (us := us) φ]
    exact hreadR φ us
  case hokRa =>
    intro us _ ρ
    rw [← hac]
    exact hokR _ ρ
  case hokF =>
    intro us _
    obtain ⟨hfT, -, -, hFD⟩ := hcore.1 _ TE.cvTa hcvTa
    exact blockRuleHokF_of_run hμ mpC h hr hcA hrhs hcvTa hfT hFD
      (Nat.le_add_right _ _) hcd hCf _ (fun ρ => hcd.okTy _ ρ)
      ((hS.frames _ hmemk i cA hcj).1 _) (o := pp.toBlockShape.rulePrefixAt j - pp.nP)
      (by omega)


end MembersRun

/-! ## 1b. The `ℓ = 0` arm's RIGHT side

The stored rule reads as the point at a valuation where the checked
elimination level is zero.  A rule that binds a variable carries the
elimination datum on its head binder (`blockRuleRaZ_run`).  A rule that
binds NONE — the zero-motive recursor `T.rec : (t : T) → True`,
`T.rec T.c ↦ True.intro`, which the kernel accepts since the
motive-count floor was removed (lane FLOOR) — is its own residue: no
field means no guarded call, so the abstraction is the identity on the
closed right-hand side, and the family's ι law at the empty spine says
that residue equals the recursor's value, which is the point
(`blockRecTyZ_run`).  No λ-head bit and no typing of the right-hand side
is needed: the graph producer's ι law already carries it. -/


/-! ## 2. The composition

`declBlock_run` is `declBlock_data` at the route's component choices —
`nCt := blockRecNCt`, the four syntactic components
`blockRulePdomsAV`/`blockRuleFdomsAV`/`blockRuleEsAV`/`blockRuleMkAV` —
with every seam conjunct DISCHARGED from the run. -/

section Compose

/-- The seam's `nCt` bound: a recursor carries `blockRecNCt` rules. -/
theorem blockRecNCt_ge {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) : r.2.2.2.length ≤ blockRecNCt rs j := by
  rw [blockRecNCt, List.getD_eq_getElem?_getD, hr]
  exact Nat.le_refl _

end Compose

end ConLeche.Model
