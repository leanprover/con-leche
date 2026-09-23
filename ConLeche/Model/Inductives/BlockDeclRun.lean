module

public import ConLeche.Model.Inductives.BlockRecPreHpre
public import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Model.Inductives.BlockRuleParams
import ConLeche.Model.Capstone
import ConLeche.Model.Inductives.BlockRecRead

public section

/-!
# `declBlock` at the run — the composition (task #315, lane RM49)

`declBlock` (`DeclBlock.lean`) takes the recursor stage as ONE
hypothesis, `hrec`; `blockRecStaged_data` (`BlockRecData.lean` §A.18)
turns it into the stage's remaining obligations at one environment and
one valuation; the dispatch (`BlockRecPreHpre.lean`) and the rule
contract (`BlockRuleFit.lean`) produce the two largest of them.  This
file is where they meet.

## 1. The `ℓ = 0` arm's LEFT side

The endpoint's `ℓ = 0` arm (`blockRuleRhsOk_base`) asks for two facts:
the stored rule reads as the point (`blockRuleRaZ_run`, off the fourth
kernel guard) and the recursor's TYPE is a truth value.  The second is
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
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∀ j, j < rs.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0 →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ j) ∈ˢ (univZero : V) := by
  intro j hj ψ ρ hℓ
  obtain ⟨_, uOf, -, -, hbits, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hu : (uOf j).eval ψ = 0 := by
    have := blockRecElimPin_run h hruns ψ hj
    rw [hℓ] at this
    exact this
  obtain ⟨-, -, -, -, heq, hlen, -⟩ :=
    checkBlockRecK_tyPis (V := V) hμ mpC h (List.getElem?_eq_getElem hj) ψ
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

All three regimes and the recursor type's split take the block's
members' run facts as ONE record, `BlockMembersRun`
(`BlockRecTyShapeRun.lean`), and nothing produced it.  At the run's own
block data (`blockDataOf`, which the seam now hands) it is the
constructors' three records read member by member: the names and the
count off `BlockNamesOk`, the former's storage, reading and leaf off
`BlockCtorsCore`, the leaf's λ-shape and the parameter agreement off
`BlockCtorsStage`, the former's closedness off the environment's
well-formedness. -/

section MembersRun

variable {envC envI : Env} {pp : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {mpC : EnvModelM V μ envC} {F : Nat}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)}
  {env₀ : Env} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}

/-- **`BlockMembersRun` from the constructors' three records**, at the
run's own block data. -/
theorem blockMembersRun_seam
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A fssZ envI pp.ctorNamesAt)
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
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC pp cvTas ctorsAs = .ok rs)
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A fssZ envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k) :
    BlockModelAt mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).memberNames
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) := by
  obtain ⟨-, cvRus, -, hsmall, -⟩ := checkBlockRecK_count h
  obtain ⟨hk0, -⟩ := ConLeche.checkBlockRecSmallElim_inv hsmall
  exact blockModelAt_of_records hN hS hcore rfl hk0 (fun _ _ => rfl) (fun _ _ _ _ => rfl)

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
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC pp cvTas ctorsAs = .ok rs)
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
  obtain ⟨c, hc⟩ := checkBlockRecK_ctorsIdx h r (List.mem_of_getElem? hr)
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
theorem blockRecEqs_below_seam (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC pp cvTas ctorsAs = .ok rs)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length) :
    ∀ ψ : Name → Nat,
      ∀ e ∈ blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleIhsRunAV pp rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleRbAV pp rs mpC.base2.acval envC ψ') ψ,
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
    have hlen := checkBlockRecK_rulesLen h hkLen hr
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
    obtain ⟨ms, hms, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
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
    obtain ⟨_, _, _, _, _, _, _, -, -, hnP, -⟩ := checkBlockRecK_tyMajor h hr
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
  · -- the `ih` openers
    intro v hv
    rw [hpl, hfl, Nat.add_assoc, ← Nat.add_assoc rs.length]
    exact blockRuleIhsRunAV_below h hr hcA hcore hcj rfl hks ψ v hv
  · -- the residue
    rw [hpl, hfl, blockRuleIhsRunAV, blockRuleIhsAV_length]
    exact blockRuleRbAV_below h hr hcA hrhs hcore hcj rfl hks hCf hCb hcbC ψ

/-- **`heqP`'s equation half at the run** — the equation list at the
PINNED `ihs`/`Rb0` reads alike at two level valuations agreeing on ANY
recursor's parameters (the block's recursors share them,
`checkBlockRecK_lps`): every component is ψ-congruent there
(`BlockRuleParams.lean` §3) — the prefix through the recursor type's
reading, the fields, indices and `ih` terms through the constructors'
record (`params`, `tssParams`, `eissParams`; the constructor's
parameters are the block's, a sub-list of the recursor's), the fired
spine through the leaf's `acval_params`, and the residue through its
footprint (`lpDefF`).  The kinds' coverage (`hkLen`) gives every
constructor its rule. -/
theorem blockRecEqs_params_seam (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC pp cvTas ctorsAs = .ok rs)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length) :
    ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        blockRecEqs (blockRecNCt rs) rs
            (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            (fun ψ' => blockRuleIhsRunAV pp rs mpC.base2.acval envC ψ')
            (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            (fun ψ' => blockRuleRbAV pp rs mpC.base2.acval envC ψ') ψ₁
          = blockRecEqs (blockRecNCt rs) rs
            (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            (fun ψ' => blockRuleIhsRunAV pp rs mpC.base2.acval envC ψ')
            (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ')
            (fun ψ' => blockRuleRbAV pp rs mpC.base2.acval envC ψ') ψ₂ := by
  intro i₀ r₀ hr₀ ψ₁ ψ₂ hq₀
  -- every (recursor, constructor) pair of the list has its rule
  have hpair : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∃ (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) (cA : ConstantVal × Nat)
        (rhs : Expr), rs[c]? = some r ∧ r.2.2.2[j]? = some cA ∧ r.2.1[j]? = some rhs := by
    intro c hc j hj
    have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
    have hjl : j < rs[c].2.2.2.length := by
      rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
    have hlen := checkBlockRecK_rulesLen h hkLen hr
    exact ⟨rs[c], rs[c].2.2.2[j], rs[c].2.1[j]'(by omega), hr, List.getElem?_eq_getElem hjl,
      List.getElem?_eq_getElem _⟩
  show blockIotaEqsAV rs.length (blockRecNCt rs) _ _ _ _ _ _
    = blockIotaEqsAV rs.length (blockRecNCt rs) _ _ _ _ _ _
  refine blockIotaEqsAV_congr (fun c hc => blockRulePdomsAV_params hμ mpC h hr₀ hq₀ hc)
    (fun c hc j hj => ?_)
  obtain ⟨r, cA, rhs, hr, hcA, hrhs⟩ := hpair c hc j hj
  have hq : ∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q := by
    rw [checkBlockRecK_lps h hr hr₀]; exact hq₀
  obtain ⟨ms, hms, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
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
  obtain ⟨_, _, _, _, _, _, _, -, -, hnP, -⟩ := checkBlockRecK_tyMajor h hr
  have hks : (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ksF
      (pp.toBlockShape.recTgtAt c) j = (blockRuleKsOf pp c j).map ConLeche.BlockFieldKind.toRec := by
    rw [blockDataOf_ksF]; rfl
  have hqL : ∀ q ∈ pp.lps, ψ₁ q = ψ₂ q := fun q hq' => hq q (checkBlockRecK_lps_sub h hr q hq')
  have hqC : ∀ q ∈ cA.1.levelParams, ψ₁ q = ψ₂ q := by rw [hlpsC]; exact hqL
  exact ⟨blockRuleFdomsAV_params h hr hcA hrhs hcd hCf hnP hqC,
    blockRuleEsAV_params h hr hcA hrhs hcd hCf hnP hqC,
    blockRuleIhsRunAV_params h hr hcA hcore hcj rfl hks hq hqC,
    blockRuleMkAV_params h hr hcA hrhs hfindC hlpsC hnP hqL,
    blockRuleRbAV_params mpC h hr hcA hrhs hq⟩

/-- **What `heqV` owes past the grading** — at every tuple typed at the
recursor types, every rule's frame (the prefix and the fields, at the
base frame `ρ`) carries:

* the constructor's INDEX readings, bit-valid;
* the pinned `ih` terms' VALUES (at the chain frame: the tuple under
  the rule's frame) fitting the pinned `ih` openers' domains
  `ihdoms` — the typed tuple's recursive calls land in the callee's
  conclusion.  The residue's validity is read at those values, and it
  is what makes the residue's own reading (typed at the frame,
  `blockRuleRbAV_wdV_run`) applicable.

Everything else `heqV` needs — the frame's validity, the fired spine,
the `ih` terms, the residue — is paid from the run and the grading
(`blockRecEqs_valid_seam`). -/
def BlockEqsValidOwed (mpC : EnvModelM V μ envC) (pp : ConLeche.BlockParts)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (ρ : Nat → V) (tup : List V) : Prop :=
  ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c → ∀ ys : List V,
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c
      ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j) ys →
    (∀ e ∈ blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j,
      AnnotValid V (consList ys ρ) e) ∧
    SpineFit (consList ys ρ) (blockRuleIhdomsAV pp rs mpC.base2.acval envC ψ c j)
      ((blockRuleIhsRunAV pp rs mpC.base2.acval envC ψ c j).map
        (interp V (consList ys (consList tup ρ))))

/-- `BlockEqsValidOwed` UNFOLDED, for its producer in another module. -/
theorem blockEqsValidOwed_iff (mpC : EnvModelM V μ envC) (pp : ConLeche.BlockParts)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (ρ : Nat → V) (tup : List V) :
    BlockEqsValidOwed mpC pp rs ψ ρ tup ↔
  ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c → ∀ ys : List V,
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c
      ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j) ys →
    (∀ e ∈ blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j,
      AnnotValid V (consList ys ρ) e) ∧
    SpineFit (consList ys ρ) (blockRuleIhdomsAV pp rs mpC.base2.acval envC ψ c j)
      ((blockRuleIhsRunAV pp rs mpC.base2.acval envC ψ c j).map
        (interp V (consList ys (consList tup ρ)))) := Iff.rfl

/-- A tuple of the family's length IS the chain frame's block. -/
theorem consList_eq_chainFrame {K : Nat} {tup : List V} (hlen : tup.length = K) (ρ : Nat → V) :
    consList tup ρ = chainFrame K (fun c => tup.getD c pt) ρ := by
  have hmap : (List.range K).map (fun c => tup.getD c pt) = tup := by
    refine List.ext_getElem? fun n => ?_
    rw [List.getElem?_map]
    by_cases hn : n < K
    · rw [List.getElem?_range hn, List.getElem?_eq_getElem (by omega : n < tup.length)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : n < tup.length)]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
      rfl
  rw [chainFrame, hmap]

/-- **`heqV` at the run, through the grading** — the equation list at
the PINNED `ihs`/`Rb0` is bit-valid at every typed tuple:
`annotValid_blockIotaEqsAV` with

* the frame's validity off the GRADING (`hokA`, the certificate lane's
  `blockRuleHokA_of_run` conclusion — the spelling `declBlock_run`'s
  `howed` already owes), through `fieldsValid_of_grading`;
* the fired spine's validity FREE (a leaf applied to bound variables,
  `acval_validV`);
* the residue's validity off its own TYPING at the frame
  (`blockRuleRbAV_wdV_run`: the stage's `inferTypeCore` run, the
  openers' readings and the same grading), at the `ih` values the owed
  row fits;
* the `ih` terms' validity off the grading's FIELD segment
  (`blockRuleIhsRunAV_valid_run`: a field's domain is the Π-tower over
  its telescope of the target former at the field's index readings);
* the index readings and the `ih` fit OWED (`BlockEqsValidOwed`). -/
theorem blockRecEqs_valid_seam (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC pp cvTas ctorsAs = .ok rs)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length)
    (hokA : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      ∀ ψ : Name → Nat,
      ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt pp rs j i).nR →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j
            ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV pp rs mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j
            ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV pp rs mpC.base2.acval envC ψ j i).getD l default))
    (hval : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      BlockEqsValidOwed mpC pp rs ψ ρ tup) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ e ∈ blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleIhsRunAV pp rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleRbAV pp rs mpC.base2.acval envC ψ') ψ,
        AnnotValid V (consList tup ρ) e := by
  intro ψ ρ tup hlen htyp
  have hv := hval ψ ρ tup hlen htyp
  have hcf := consList_eq_chainFrame hlen ρ
  -- every (recursor, constructor) pair of the list has its rule, and its record
  have hpair : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∃ (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) (cA : ConstantVal × Nat)
        (rhs : Expr), rs[c]? = some r ∧ r.2.2.2[j]? = some cA ∧ r.2.1[j]? = some rhs := by
    intro c hc j hj
    have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
    have hjl : j < rs[c].2.2.2.length := by
      rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
    have hlen := checkBlockRecK_rulesLen h hkLen hr
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
    have htk : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c
          ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j
          ++ blockRuleIhdomsAV pp rs mpC.base2.acval envC ψ c j).take l
        = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c
          ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j).take l :=
      List.take_append_of_le_length (by omega)
    have hgd : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c
          ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j
          ++ blockRuleIhdomsAV pp rs mpC.base2.acval envC ψ c j).getD l default
        = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c
          ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j).getD l default := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hl]
    have hq := hokA c r hr j cA hcA ψ l (by omega) ρ ys (by rw [htk]; exact hys)
    rw [hgd] at hq
    exact hq.2
  · dsimp only at hys ⊢
    obtain ⟨r, cA, rhs, hr, hcA, hrhs⟩ := hpair c hc j hj
    obtain ⟨hes, hfit⟩ := hv c hc j hj ys hys
    -- the constructor's record
    obtain ⟨ms, hms, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    have hmemk : pp.toBlockShape.recTgtAt c
        < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
      (List.getElem?_eq_some_iff.mp hms).1
    have hcj : ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
        (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
      show (ctorsAs.getD _ [])[j]? = _
      rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
    obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
    have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
    obtain ⟨_, _, _, _, _, _, _, -, -, hnP, -⟩ := checkBlockRecK_tyMajor h hr
    have hks : (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ksF
        (pp.toBlockShape.recTgtAt c) j
        = (blockRuleKsOf pp c j).map ConLeche.BlockFieldKind.toRec := by
      rw [blockDataOf_ksF]; rfl
    refine ⟨hes, ?_, blockRuleIhsRunAV_valid_run hμ h hr hcA hrhs hcore hcj rfl hks hwfC.1 ψ
      (hokA c r hr j cA hcA ψ) _ ys
      (spineFit_chainFrame_of_bounded (blockRuleDoms_bounded_at hμ h hcore ψ c r hr j cA rhs hcA hrhs)
        hys), ?_⟩
    · -- the fired spine: a leaf applied to bound variables
      rw [blockRuleMkAV_eq h hr hcA hrhs hfindC hlpsC hnP ψ]
      refine annotValid_mkAppN (mpC.acval_validV _ _ _) (fun a ha => ?_)
      rcases List.mem_append.mp ha with ha | ha
      · simp only [paramBvarsAt, List.mem_map] at ha
        obtain ⟨k, -, rfl⟩ := ha
        trivial
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
        trivial
    · -- the residue, off its typing at the frame
      rw [← hcf]
      have hsat1 : Sat V (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ c
          ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j).reverse
          (consList ys ρ) := by
        simpa using sat_of_spineFit (Sat_nil V ρ) hys
      exact (blockRuleRbAV_wdV_run hμ h hr hcA hrhs hcore hcj rfl hks hwfC.1 hwfC.2.2.2.1
        (constsBound_of_constsResolve _ hwfC.2.2.1) ψ (hokA c r hr j cA hcA ψ) _
        (sat_of_spineFit hsat1 hfit)).2

/-- **THE RULE CONTRACT AT THE SEAM** — `blockRuleDataB_run` at every
(recursor, constructor) pair, with everything the run pays discharged:
the representation, the member link (`checkBlockRecK_ctorsAt`), the
constructor's facts off the core record, the prefix and field
readings, the recursor type's split, the counting guard's two facts at
the checked elimination level, the rule's reading and grading
(`blockRuleRhs_read_run`, off the leaf's facts), the environment's
closedness, the rules' inputs, the level parameters and the rule
domains' own bounds (`blockRuleDoms_bounded_seam`).

`ihs`/`Rb0` are the run's own (`hihsE`/`hRbE`, `BlockRuleRun.lean`),
and the rule stage's peel obligation is `blockRuleBodyOwed_run` CALLED
here.  What is left of it is two facts that are not the rule stage's:
the frame's grading `hokA` (the certificate lane's,
`blockRuleHokA_of_run`'s conclusion) and the `ih` openers' fit
`hihFit` (the regime's, `BlockRuleIhFitOwed`).  The equation list's
facts (`heqB`/`heqP`/`heqV`) and the regime (`hpre`) enter only
through the leaf, and are the seam's own conjuncts. -/
theorem blockRuleDataB_seam (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC pp cvTas ctorsAs = .ok rs)
    (hndM : pp.toBlockShape.memberNames.Nodup)
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A fssZ envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
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
    -- `ihs`/`Rb0` are the RUN'S OWN (`BlockRuleRun.lean` §2, `BlockRecData.lean` §A.9b)
    (hihsE : ihs = fun ψ' => blockRuleIhsRunAV pp rs mpC.base2.acval envC ψ')
    (hRbE : Rb0 = fun ψ' => blockRuleRbAV pp rs mpC.base2.acval envC ψ')
    -- the rule frame's GRADING (the certificate lane's: `blockRuleHokA_of_run`)
    (hokA : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      ∀ ψ : Name → Nat,
      ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt pp rs j i).nR →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j
            ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV pp rs mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j
            ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV pp rs mpC.base2.acval envC ψ j i).getD l default))
    -- the `ih` openers' FIT (the regime's)
    (hihFit : ∀ (φ : Name → Nat) (j : Nat)
        (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        BlockRuleIhFitOwed (V := V) mpC pp rs s (blockRecNCt rs)
          (fun ψ' => blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ')
          (blockRecCtorTy mpC.base2.acval envC rs j i) φ j i r cA
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := pp.nP,
              fire := .plain, rhs := rhs, paramsBlind := true })) :
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
  have hM := blockModelAt_seam h hN hS hcore
  have hmr := blockMembersRun_seam hN hS hcore
  -- the member link and the constructor's facts
  obtain ⟨ms, hms, hctA, hlenms⟩ := checkBlockRecK_ctorsAt h hr
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
  obtain ⟨_, cvTa, _, _, _, _, _, -, hcvTa, hnP, -⟩ := checkBlockRecK_tyMajor h hr
  -- the elimination level package, and the pin
  obtain ⟨usP, uOf, helim, hmemU, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hk0 : 0 < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hmemk
  -- the rule's reading, off the leaf's facts
  obtain ⟨hreadR, hokR⟩ :=
    blockRuleRhs_read_run hμ mpC h hndM
      (blockRecLeafAV_closed hμ mpC h heqB) (blockRecLeafAV_liftN hμ mpC h heqB)
      (blockRecLeafAV_par_run hμ mpC h heqP) (fun ψ _ hi ρ => blockRecLeafAV_wd hpre ψ hi ρ)
      (blockRecLeafAV_valid hμ mpC h heqV) hpre m₃ hac r (List.mem_of_getElem? hr) rhs
      (List.mem_of_getElem? hrhs)
  refine blockRuleDataB_run (mem := pp.toBlockShape.recTgtAt) (jc := i)
    (K := rs.length) hM hμ h rfl rfl rfl rfl hr hcA hrhs rfl hcj ⟨hfindC, hlpsC, hcd⟩ hlpsC rfl
    hnP hmemk ?htgt hj ((blockRecCtor_seam h hN hcore hctorsAs j r hr i cA hcA).2.2)
    (fun us _ => blockRuleFdomsAV_datum h hr hcA hrhs hcore hmemk hcj hnP rfl _)
    ?hes ?hlenP ?hparamsC
    (fun us _ ρ => blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl _ ρ))
    ?hlarge ?hct1 ?hread ?hokRa hCf hCb
    (fun us _ => (blockRuleFdomsAV_eq h hr hcA hrhs hcd hCf hnP _).2)
    ?hokF hndM hac (blockRecLeafAV_closed hμ mpC h heqB)
    (fun r₀ h0 => checkBlockRecK_lps h h0 hr)
    (fun us _ => Rules.RulesInputs.ofSem mpC _)
    (blockRuleDoms_bounded_seam hμ h hcore φ j r hr i cA rhs hcA hrhs)
    (by
      subst hihsE hRbE
      exact blockRuleBodyOwed_run hμ h hr hcA hrhs hcore hcj rfl
        (by rw [blockDataOf_ksF]; rfl) hCf hCb (constsBound_of_constsResolve _ hwfC.2.2.1)
        (hokA j r hr i cA hcA) (hihFit φ j r hr i cA rhs hcA hrhs))
  case htgt =>
    intro l _
    rw [← hN.2.2.2]
    exact hN.2.1 _ i l
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
    have hpos : 0 < rs.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
    have hℓ : (usP.headD .zero).eval (Level.substFn φ r.1.levelParams us) ≠ 0 := by
      rw [← blockRecElimAgree_eval helim _ (uOf 0) (hmemU 0 hpos),
        blockRecElimPin_run h hruns _ hpos]
      exact hne
    obtain ⟨-, -, -, -, -, hc⟩ := blockRecCounting_run h helim hmemU hruns _ hℓ hw0
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
    obtain ⟨hfT, -, -, hFD⟩ := hcore.1 _ cvTa hcvTa
    exact blockRuleHokF_of_run hμ mpC h hr hcA hrhs hcvTa hfT hFD
      (Nat.le_add_right _ _) hcd hCf _ (fun ρ => hcd.okTy _ ρ)
      ((hS.frames _ hmemk i cA hcj).1 _) (o := pp.toBlockShape.rulePrefixAt j - pp.nP)
      (by omega)

end MembersRun

/-! ## 2. The composition

`declBlock_run` is `declBlock_data` at the lane's component choices —
`nCt := blockRecNCt`, the four syntactic components
`blockRulePdomsAV`/`blockRuleFdomsAV`/`blockRuleEsAV`/`blockRuleMkAV` —
with every seam conjunct that the run already pays DISCHARGED and the
rest named in ONE premise, `howed`, quantified over exactly what the
seam hands (the recursor stage's run and the constructors' records,
and — lane RM49's widening — that the block data IS the run's
`blockDataOf`).  `howed`'s conjuncts are the honest list of what the
composition still needs; each carries its owner in the comment above
it. -/

section Compose

/-- The seam's `nCt` bound: a recursor carries `blockRecNCt` rules. -/
theorem blockRecNCt_ge {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) : r.2.2.2.length ≤ blockRecNCt rs j := by
  rw [blockRecNCt, List.getD_eq_getElem?_getD, hr]
  exact Nat.le_refl _

/-- **`declBlock` at the run** — the uniform install's carrier, with
the recursor stage's obligation discharged down to `howed`.

Discharged here, at the seam: the rule count (`blockRecNCt_ge`), the
prefix length (`blockRulePdomsAV_length`), every carried constructor's
storage and reading (`blockRecCtor_seam`, at the canonical
`blockRecCtorTy`), the `ℓ = 0` arm's type fact (`blockRecTyZ_run`),
and the whole per-pair RULE CONTRACT but one premise
(`blockRuleDataB_seam`).

The rules' `ih` openers and residue readings are PINNED
(`blockRuleIhsRunAV`/`blockRuleRbAV`, functions of the run through
§A.9b's definitions), so `howed` chooses only the family's level `s`,
and owes at that choice:
* of the equation list's three facts, only what `heqV` needs past the
  grading — `BlockEqsValidOwed` (the index readings' validity and the
  typed tuple's `ih` fit); the rest of `heqV`
  is `blockRecEqs_valid_seam`, its bound `heqB` is
  `blockRecEqs_below_seam` and its parametricity `heqP` is
  `blockRecEqs_params_seam`, all paid here — and the level's own
  parametricity (`heqP`'s `s` half, whoever fixes `s`);
* the family's regime is PRODUCED (`blockRecPre_seam`, lane RM51) and
  what is owed of it is its ROWS: the family level's typing at `s`
  (`blockRecTy_univ_run` pays it at `s := maxLevelEval us`), the
  grading bundle `BlockGradeOwed`, and one bundle per regime
  (`BlockIndOwed`, `BlockWfOwed`, `BlockSqOwed`) at the checked
  elimination level;
* of the rule stage's peel obligation (`blockRuleBodyOwed_run`, called
  in `blockRuleDataB_seam`), the two conjuncts that are not the rule
  stage's: the frame's GRADING (the certificate lane's) and the `ih`
  openers' FIT `BlockRuleIhFitOwed` (the regime's).

The `ℓ = 0` arm's non-empty rule telescope is the kernel's rule-prefix
floor `nP + k ≤ rP` (`checkBlockRecK_rulePos`). -/
theorem declBlock_run (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : ConLeche.BlockParts}
    (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env p₀ env₂)
    (hgate : ConLeche.blockRecCheckOn = true)
    (howed : ∀ (envC envI : Env) (pp : ConLeche.BlockParts) (cvTasR : List ConstantVal)
        (ctorsAsR : List (List (ConstantVal × Nat)))
        (rsR : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
        (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
        (A : Nat → (Name → Nat) → AnnotTerm)
        (fssZ : (Name → Nat) → Nat → List (List AnnotTerm)),
        ConLeche.checkBlockRecK (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envC pp cvTasR
          ctorsAsR = .ok rsR →
        pp.toBlockShape.memberNames.Nodup →
        BlockNamesOk (V := V) dR cvTasR →
        BlockCtorsStage (V := V) μ F dR pp.lps cvTasR pp.toBlockShape isRecR A fssZ envI
          pp.ctorNamesAt →
        BlockCtorsCore mpC.base2 dR pp.lps cvTasR pp.toBlockShape isRecR A dR.k →
        (∀ c, c < ctorsAsR.length → ctorsAsR[c]? = some (dR.ctorsM c)) →
        (∀ r ∈ rsR, ∀ cA ∈ r.2.2.2,
          ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF)) →
        (∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
            (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
          dR = blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) →
        (∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAsR[c]? = some ctorsA →
          (pp.kinds.getD c []).length = ctorsA.length) →
        ∃ s : (Name → Nat) → Nat,
      -- the equation list's validity past the grading (`blockRecEqs_valid_seam` pays
      -- the rest; its bound is `blockRecEqs_below_seam`, its parametricity
      -- `blockRecEqs_params_seam`)
      (∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rsR.length →
      (∀ mm, mm < rsR.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rsR ψ mm)) →
        BlockEqsValidOwed mpC pp rsR ψ ρ tup) ∧
      -- the level's parameter-invariance (the equation list's is
      -- `blockRecEqs_params_seam`)
      (∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rsR[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂)
      ∧
      -- the family's regime, OWED as rows (`blockRecPre_seam` produces
      -- `hpre` from them): the level's typing at `s`, the grading, and
      -- one bundle per regime at the checked elimination level
      (∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rsR.length →
        interp V ρ (blockRecTyAV mpC.base2.acval envC rsR ψ c) ∈ˢ (univ (s ψ) : V) ∧
          WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rsR ψ c)) ∧
      BlockGradeOwed mpC F pp rsR (fun ψ' => blockRuleIhsRunAV pp rsR mpC.base2.acval envC ψ')
        (fun ψ' => blockRuleRbAV pp rsR mpC.base2.acval envC ψ') ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0 →
        BlockIndOwed mpC F pp rsR dR ψ ρ (blockRuleIhsRunAV pp rsR mpC.base2.acval envC ψ)
          (blockRuleRbAV pp rsR mpC.base2.acval envC ψ)) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0 →
        dR.w ψ ≠ 0 →
        BlockWfOwed mpC F pp rsR dR ψ ρ
          (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
          (blockRuleIhsRunAV pp rsR mpC.base2.acval envC ψ)
          (blockRuleRbAV pp rsR mpC.base2.acval envC ψ)) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0 →
        dR.w ψ = 0 →
        BlockSqOwed mpC F pp rsR dR ψ ρ
          (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
          (blockRuleIhsRunAV pp rsR mpC.base2.acval envC ψ)
          (blockRuleRbAV pp rsR mpC.base2.acval envC ψ))
      ∧
      -- the rule frame's GRADING (the certificate lane's: `blockRuleHokA_of_run`)
      (∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
        rsR[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        ∀ ψ : Name → Nat,
        ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt pp rsR j i).nR →
        ∀ (σ' : Nat → V) (ys : List V),
          SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rsR ψ j
              ++ blockRuleFdomsAV pp.toBlockShape rsR mpC.base2.acval envC ψ j i
              ++ blockRuleIhdomsAV pp rsR mpC.base2.acval envC ψ j i).take l) ys →
          WellDenotedV V (consList ys σ')
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rsR ψ j
              ++ blockRuleFdomsAV pp.toBlockShape rsR mpC.base2.acval envC ψ j i
              ++ blockRuleIhdomsAV pp rsR mpC.base2.acval envC ψ j i).getD l default))
      ∧
      -- the `ih` openers' FIT (the regime's)
      (∀ (φ : Name → Nat) (j : Nat)
          (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rsR[j]? = some r →
        ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
          r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
          BlockRuleIhFitOwed (V := V) mpC pp rsR s (blockRecNCt rsR)
            (fun ψ' => blockRuleEsAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
            (fun ψ' => blockRuleMkAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
            (blockRecCtorTy mpC.base2.acval envC rsR j i) φ j i r cA
            (ConLeche.recRuleBits envC.find? r.1.name
              { ctor := cA.1.name, nfields := cA.2, ctorParams := pp.nP,
                fire := .plain, rhs := rhs, paramsBlind := true }))) :
    Nonempty (EnvModelM V μ env₂) :=
  declBlock_data hμ mp hE hdp hrun hgate
    fun envC envI pp cvTasR ctorsAsR rsR mpC dR isRecR A fssZ hrec hnd hnames hstage hcore
        hctorsAs hctorsIn hdR hkLen => by
      obtain ⟨s, hval, hsP, hTy, hG, hI, hW, hSq, hokA, hihFit⟩ :=
        howed envC envI pp cvTasR ctorsAsR rsR mpC dR isRecR A fssZ hrec hnd hnames hstage
          hcore hctorsAs hctorsIn hdR hkLen
      obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
      have heqB := blockRecEqs_below_seam hμ hrec hcore hkLen
      have heqV := blockRecEqs_valid_seam hμ hrec hcore hkLen hokA hval
      have heqP := fun i r hr ψ₁ ψ₂ hq =>
        And.intro (hsP i r hr ψ₁ ψ₂ hq) (blockRecEqs_params_seam hμ hrec hcore hkLen i r hr ψ₁ ψ₂ hq)
      have hpre := blockRecPre_seam hμ hrec ⟨env₀, pk, uOfD, ppsOf, rfl⟩ hnames hstage hcore
        (blockMembersRun_seam hnames hstage hcore) (blockModelAt_seam hrec hnames hstage hcore)
        hTy hG hI hW hSq
      exact ⟨s, blockRecNCt rsR,
        fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rsR ψ',
        fun ψ' => blockRuleFdomsAV pp.toBlockShape rsR mpC.base2.acval envC ψ',
        fun ψ' => blockRuleEsAV pp.toBlockShape rsR mpC.base2.acval envC ψ',
        fun ψ' => blockRuleIhsRunAV pp rsR mpC.base2.acval envC ψ',
        fun ψ' => blockRuleMkAV pp.toBlockShape rsR mpC.base2.acval envC ψ',
        fun ψ' => blockRuleRbAV pp rsR mpC.base2.acval envC ψ',
        blockRecCtorTy mpC.base2.acval envC rsR,
        heqB, heqV, heqP, hpre,
        fun j r hr => blockRecNCt_ge hr,
        fun ψ j r hr => blockRulePdomsAV_length hμ mpC hrec hr ψ,
        blockRecCtor_seam hrec hnames hcore hctorsAs,
        blockRuleDataB_seam hμ hrec hnd hnames hstage hcore hctorsAs heqB heqV heqP hpre
          rfl rfl hokA hihFit,
        blockRecTyZ_run hμ mpC hrec,
        ConLeche.checkBlockRecK_rulePos hrec⟩

end Compose

end ConLeche.Model
