module

public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecPreHpre
public import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Verify.Inductives.BlockRecInv
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
/-- A bounded field chain stays bounded, `K` higher, under `liftDomsK` at ANY
cutoff (`fieldsBelow_liftDomsK` is the cutoff-equals-bound case). -/
theorem fieldsBelow_liftDomsK_at (K : Nat) :
    ∀ {m k : Nat} {Fs : List AnnotTerm}, FieldsBelow m Fs → FieldsBelow (m + K) (liftDomsK K k Fs)
  | _, _, [], _ => trivial
  | m, k, _ :: Fs, h =>
    ⟨bvarsBelow_liftN_add h.1 (Nat.le_refl _) k, by
      have := fieldsBelow_liftDomsK_at K (m := m + 1) (k := k + 1) (Fs := Fs) h.2
      rwa [show m + 1 + K = m + K + 1 from by omega] at this⟩

omit [SetTheory V] in
/-- A bounded field chain's entries, one by one. -/
theorem fieldsBelow_getD :
    ∀ {m : Nat} {Fs : List AnnotTerm}, FieldsBelow m Fs → ∀ q, q < Fs.length →
      Term.bvarsBelow (m + q) (Fs.getD q default).erase
  | _, [], _, _, hq => absurd hq (Nat.not_lt_zero _)
  | m, _ :: _, h, 0, _ => by simpa using h.1
  | m, _ :: Fs, h, q + 1, hq => by
    simp only [List.getD_cons_succ]
    have := fieldsBelow_getD (m := m + 1) (Fs := Fs) h.2 q (by simpa using hq)
    rwa [show m + 1 + q = m + (q + 1) from by omega] at this

omit [SetTheory V] in
/-- A member's constructors are among the block's. -/
theorem numCtorsOf_ge {ms : ConLeche.MemberShape} :
    ∀ {l : List ConLeche.MemberShape}, ms ∈ l → ms.ctors.length ≤ ConLeche.numCtorsOf l
  | _ :: _, .head _ => by simp only [ConLeche.numCtorsOf]; omega
  | _ :: _, .tail _ h => by simp only [ConLeche.numCtorsOf]; have := numCtorsOf_ge h; omega

/-- **The rule domains' own bounds, at the seam** — the residue
producer's `hbdd`: the prefix half is `blockRulePdomsAV_bounded`, the
field half is the constructor's field domains (`CtorDataI.below`,
dropped past the parameters) lifted past the rule prefix's non-parameter
stretch (`blockRuleFdomsAV_eq`). -/
theorem blockRuleDoms_bounded_seam (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC pp cvTas ctorsAs = .ok rs)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k) :
    ∀ (φ : Name → Nat) (j : Nat)
        (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr), r.2.2.2[i]? = some cA →
      r.2.1[i]? = some rhs →
      ∀ us : List Level, us.length = r.1.levelParams.length →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs
            (Level.substFn φ r.1.levelParams us) j
          ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i).length →
        Term.bvarsBelow l (((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs
            (Level.substFn φ r.1.levelParams us) j
          ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i).getD l default).erase) := by
  intro φ j r hr i cA rhs hcA hrhs us _ l hl
  -- the member link and the constructor's data
  obtain ⟨ms, hms, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
  have hmemk : pp.toBlockShape.recTgtAt j
      < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms).1
  have hcj : ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt j))[i]? = some cA := by
    show (ctorsAs.getD _ [])[i]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmemk i cA hcj
  obtain ⟨-, -, hcd⟩ := hcore.2.2.1 _ i cA hcj
  have hCf : cA.1.type.hasFvar = false := (mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)).1
  obtain ⟨_, _, _, _, _, _, _, -, -, hnP, -⟩ := checkBlockRecK_tyMajor h hr
  generalize Level.substFn φ r.1.levelParams us = ψ at hl ⊢
  have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
  -- the two halves' bounds
  have hfd := (blockRuleFdomsAV_eq h hr hcA hrhs hcd hCf hnP ψ).1
  have hfB : FieldsBelow (pp.toBlockShape.rulePrefixAt j)
      (blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i) := by
    rw [hfd]
    have hd := ConLeche.Model.DomsBelow.drop pp.nP (hcd.below ψ)
    rw [Nat.zero_add] at hd
    have := fieldsBelow_liftDomsK_at (pp.toBlockShape.rulePrefixAt j - pp.nP) (k := 0) hd.fields
    rwa [show pp.nP + (pp.toBlockShape.rulePrefixAt j - pp.nP)
      = pp.toBlockShape.rulePrefixAt j from by omega] at this
  rcases Nat.lt_or_ge l (pp.toBlockShape.rulePrefixAt j) with hlt | hge
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hpl]; exact hlt),
      ← List.getD_eq_getElem?_getD]
    exact blockRulePdomsAV_bounded hμ mpC h hr ψ l (by rw [hpl]; exact hlt)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hpl]; exact hge),
      ← List.getD_eq_getElem?_getD, hpl]
    have hq : l - pp.toBlockShape.rulePrefixAt j
        < (blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i).length := by
      rw [List.length_append, hpl] at hl; omega
    have := fieldsBelow_getD hfB _ hq
    rwa [show pp.toBlockShape.rulePrefixAt j + (l - pp.toBlockShape.rulePrefixAt j) = l
      from by omega] at this

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
    exact Nat.le_trans (numCtorsOf_ge (List.mem_of_getElem? hms)) hc
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
* the equation list's three facts `heqB`/`heqV`/`heqP` (the rule
  lanes'; `§A.3` reduces the first two to per-component facts);
* the family's regime `hpre` (the dispatch lane's
  `blockRecPre_dispatch_run` concludes it, but its WF/SQ arms relay
  premises quantified over EVERY `D : RecFamData` whose conclusions read
  `D.tupOf`/`D.kit` — `hihChain`, and the SQ arm has no case for a
  zero-constructor `Prop` block with large elimination — so relaying
  them here would make this premise set uninhabitable);
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
      -- the equation list: bounded, valid, level-parametric
      (∀ ψ : Name → Nat,
      ∀ e ∈ blockRecEqs (blockRecNCt rsR) rsR
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rsR ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleIhsRunAV pp rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleRbAV pp rsR mpC.base2.acval envC ψ') ψ,
        Term.bvarsBelow rsR.length e.erase) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rsR.length →
      (∀ mm, mm < rsR.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rsR ψ mm)) →
      ∀ e ∈ blockRecEqs (blockRecNCt rsR) rsR
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rsR ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleIhsRunAV pp rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleRbAV pp rsR mpC.base2.acval envC ψ') ψ,
        AnnotValid V (consList tup ρ) e) ∧
      (∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rsR[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂ ∧
          blockRecEqs (blockRecNCt rsR) rsR
              (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rsR ψ')
              (fun ψ' => blockRuleFdomsAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
              (fun ψ' => blockRuleEsAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
              (fun ψ' => blockRuleIhsRunAV pp rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleRbAV pp rsR mpC.base2.acval envC ψ') ψ₁
            = blockRecEqs (blockRecNCt rsR) rsR
              (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rsR ψ')
              (fun ψ' => blockRuleFdomsAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
              (fun ψ' => blockRuleEsAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
              (fun ψ' => blockRuleIhsRunAV pp rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleRbAV pp rsR mpC.base2.acval envC ψ') ψ₂)
      ∧
      -- the family's regime (`blockRecPre_dispatch_run`'s conclusion)
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rsR.length
        (blockRecTyAV mpC.base2.acval envC rsR ψ)
        (blockRecEqs (blockRecNCt rsR) rsR
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rsR ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleIhsRunAV pp rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape rsR mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleRbAV pp rsR mpC.base2.acval envC ψ') ψ) ρ)
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
      obtain ⟨s, heqB, heqV, heqP, hpre, hokA, hihFit⟩ :=
        howed envC envI pp cvTasR ctorsAsR rsR mpC dR isRecR A fssZ hrec hnd hnames hstage
          hcore hctorsAs hctorsIn hdR hkLen
      obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
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
