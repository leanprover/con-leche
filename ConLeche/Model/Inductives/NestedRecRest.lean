module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Cached.PushChain
import ConLeche.Model.Inductives.BlockRecAssembly
import Std.Data.String.ToNat
public import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.TargetIhData
public import ConLeche.Model.Inductives.TargetFrame
public import ConLeche.Model.Inductives.TargetClass
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.IndTowerRead
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Verify.InstLevels
import ConLeche.Verify.CheckerF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Model.Inductives.BlockRuleParams
import ConLeche.Model.Inductives.TargetOutCerts
import ConLeche.Model.Inductives.TargetOutConcl
import ConLeche.Model.Inductives.TargetOutCa
import ConLeche.Model.Inductives.TargetOutChain
import ConLeche.Model.Inductives.StructFrames
import ConLeche.Model.Inductives.SumData
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves

public section

/-!
# The nested recursors' stage: the facts beside the class induction (lane RECREST)

The facts the recursors' stage (`nestedRecStage`, `DeclBlockStep.lean`)
reads beside the class induction, one producer each, at the target
check's run (`TargetRecRun`).
-/

namespace ConLeche

/-! ## `hnd`: the family's names are distinct

The member-major records carry the names `{T_m.rec}` as a set (the
name-set check), the others `{T_0.rec_1 … T_0.rec_n}` as a set
(`targetRecPins`' auxiliary check, `RecPinsF.auxNames`).  Each set is
pinned at its own length, and the generated names are distinct
(`Nat.repr` is injective), so each half is `Nodup` by the pigeonhole;
the halves are disjoint because `"rec" ≠ "rec_" ++ n`. -/

/-- The generated auxiliary names' last components are distinct. -/
theorem auxRecStr_inj {i j : Nat} (h : s!"rec_{i + 1}" = s!"rec_{j + 1}") : i = j := by
  have h2 : toString (i + 1) = toString (j + 1) := by simpa using h
  have := Nat.repr_injective h2
  omega

/-- A member's recursor name is never an auxiliary one's last component. -/
theorem rec_ne_auxRecStr (i : Nat) : "rec" ≠ s!"rec_{i + 1}" := by
  intro h
  have := congrArg String.length h
  simp only [String.length_append] at this
  have h3 : "rec".length = 3 := by decide
  have h4 : (toString "rec_").length = 4 := by decide
  simp only [h3, h4] at this
  omega

/-- The generated auxiliary names are distinct. -/
theorem recAuxWant_nodup (q : BlockShape) : (recAuxWant q).Nodup := by
  unfold recAuxWant
  exact List.Pairwise.map _ (fun i j hij h => hij (auxRecStr_inj (Name.str.inj h).2))
    List.nodup_range

/-- **The target check's pins make the family's names distinct**, given
the members' own. -/
theorem RecPinsF.nodup {q : BlockShape} (h : RecPinsF q)
    (hndM : q.memberNames.Nodup) : (q.recs.map (·.cvR.name)).Nodup := by
  -- the member-major half
  have hown : ((q.recs.filter fun rc => decide (rc.tgt < q.k)).map (·.cvR.name)).Nodup :=
    Cached.blockRecNameSetOk_nodup (p := { q with recs := q.recs.filter fun rc => rc.tgt < q.k })
      h.nameSet hndM
  -- the auxiliary half
  have hA := h.auxNames
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at hA
  obtain ⟨⟨hlenA, hwant⟩, hgot⟩ := hA
  have haux : (recAuxGot q).Nodup :=
    Cached.nodup_of_covering (recAuxWant_nodup q) hwant (Nat.le_of_eq hlenA)
  -- the halves are disjoint
  have hdisj : ∀ a ∈ (q.recs.filter fun rc => decide (rc.tgt < q.k)).map (·.cvR.name),
      a ∉ recAuxGot q := by
    intro a ha hb
    have hsetO := h.nameSet
    unfold blockRecNameSetOk at hsetO
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hsetO
    obtain ⟨ms, -, hms⟩ := List.mem_map.mp (hsetO.2 a ha)
    obtain ⟨i, -, hi⟩ := List.mem_map.mp (hgot a hb)
    rw [← hms] at hi
    exact rec_ne_auxRecStr i (Name.str.inj hi).2.symm
  have hperm : ((q.recs.filter fun rc => decide (rc.tgt < q.k)).map (·.cvR.name) ++
      recAuxGot q).Perm (q.recs.map (·.cvR.name)) := by
    unfold recAuxGot
    rw [← List.map_append]
    exact (List.filter_append_perm _ q.recs).map _
  exact hperm.nodup_iff.mp (List.nodup_append.mpr ⟨hown, haux, fun a ha b hb hab =>
    hdisj a ha (hab ▸ hb)⟩)

/-- **`hnd` at any majors**: the stored family's names are distinct —
positionally the records' (`recStageG_recNames`), which the pins make
distinct (`RecPinsF.nodup`). -/
theorem recStageG_nodup {mode : CheckMode} {F : Nat} {env : Env} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {mem : Nat → Prop}
    (h : RecStageG mode F env p cvTas ctorsAs rs mem)
    (hndM : p.toBlockShape.memberNames.Nodup) : (rs.map (·.1.name)).Nodup := by
  obtain ⟨hpins, hlenR, hall⟩ := recStageG_recNames h
  have hmap : rs.map (·.1.name) = p.recs.map (·.cvR.name) := by
    refine List.ext_getElem? (fun i => ?_)
    by_cases hi : i < p.recs.length
    · obtain ⟨rc, r, hrc, hr, hname, -, -, -⟩ := hall i hi
      simp only [List.getElem?_map, hrc, hr, Option.map_some]
      rw [hname]
    · rw [List.getElem?_eq_none (by simp only [List.length_map, hlenR]; omega),
        List.getElem?_eq_none (by simp only [List.length_map]; omega)]
  rw [hmap]
  exact hpins.nodup hndM

/-! ## `pinsNoProj`: a `.nested` firing's pins mention no empty slot

The pins are the major domain's parameter arguments (lowered), read off
the STORED recursor type, which is annotated and so mentions no empty
projection slot (`recStage_cvFacts`). -/

namespace Expr

variable {T : Name} {i : Nat}

/-- Lifting the loose variables creates no `.proj` node. -/
theorem NoProjAt.of_liftLooseBVars {k : Nat} :
    ∀ {e : Expr} {c : Nat}, NoProjAt T i (e.liftLooseBVars k c) → NoProjAt T i e := by
  intro e
  induction e with
  | bvar j => intro _ _; simp
  | fvar idx ty ih => intro c h; simpa [Expr.liftLooseBVars] using h
  | sort u => intro _ _; simp
  | const n us => intro _ _; simp
  | lit l => intro _ _; simp
  | app f a ihf iha =>
    intro c h
    simp only [Expr.liftLooseBVars, noProjAt_app] at h
    exact noProjAt_app.mpr ⟨ihf h.1, iha h.2⟩
  | lam ty b m ihty ihb =>
    intro c h
    simp only [Expr.liftLooseBVars, noProjAt_lam] at h
    exact noProjAt_lam.mpr ⟨ihty h.1, ihb h.2⟩
  | forallE ty b m ihty ihb =>
    intro c h
    simp only [Expr.liftLooseBVars, noProjAt_forallE] at h
    exact noProjAt_forallE.mpr ⟨ihty h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro c h
    simp only [Expr.liftLooseBVars, noProjAt_letE] at h
    exact noProjAt_letE.mpr ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s j e ih =>
    intro c h
    simp only [Expr.liftLooseBVars, noProjAt_proj] at h
    exact noProjAt_proj.mpr ⟨h.1, ih h.2⟩

/-- An application's arguments are subterms. -/
theorem NoProjAt.getAppArgs :
    ∀ {e : Expr}, NoProjAt T i e → ∀ a ∈ e.getAppArgs, NoProjAt T i a := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h x hx
    rw [noProjAt_app] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ihf h.1 x hx
    · exact h.2
  | _ => intro _ x hx; simp [Expr.getAppArgs] at hx

/-- A stripped telescope's body is a subterm. -/
theorem NoProjAt.stripPis :
    ∀ (k : Nat) {e b : Expr} {bs : List (Expr × BinderMeta)}, e.stripPis k = some (bs, b) →
      NoProjAt T i e → NoProjAt T i b
  | 0, e, b, bs, h, he => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact he
  | k + 1, e, b, bs, h, he => by
    cases e with
    | forallE ty body m =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', b'⟩, h', hh⟩ := h
      simp only [Prod.mk.injEq] at hh
      rw [← hh.2]
      exact NoProjAt.stripPis k h' (noProjAt_forallE.mp he).2
    | _ => simp [Expr.stripPis] at h

end Expr

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## `ctorsIn`, `ctor`: the carried constructors are stored at the major's parameter count

At a member major, the constructors' core record (`BlockCtorsCore`); at
an outside major, the carrier's coverage of the container's block
(`tgtOutCls_of`: the recorded constructors ARE the ones the target
check read off the environment). -/

omit [SetTheory V] in
/-- A lookup finds a constant under its own name. -/
theorem find?_some_name {env : Env} {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci) :
    ci.name = n := by
  have := List.find?_some h
  simpa using this

section Ctors

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {isRec : Bool}
  {A : Nat → (Name → Nat) → AnnotTerm}

/-- **Every constructor a checked recursor carries is stored, at its
major's parameter count** — a member's by the constructors' core record,
a container's by the carrier's coverage. -/
theorem tgtRecCtor_find
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    (hN : BlockNamesOk (V := V) (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM c))
    (hcov : LfpCover mpC []) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name
          = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2) := by
  intro j r hr i cA hcA
  obtain ⟨rc, cvRi, M, u, rhssA, -, -, ho, rfl, -, -, ⟨E⟩⟩ := ConLeche.targetRecRun_at R hr
  have hMj : ConLeche.tgtMajorsOf out j = M := by
    simp [ConLeche.tgtMajorsOf, List.getD_eq_getElem?_getD, ho]
  rw [hMj]
  simp only at hcA
  cases hm : M.member with
  | some t =>
    obtain ⟨ms, -, -, -, hnPc, hctors, -⟩ := E.member_facts_of (by simp [hm])
    have hcl : rc.tgt < ctorsAs.length := (List.getElem?_eq_some_iff.mp hctors).1
    have heq : M.ctors = (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM rc.tgt :=
      Option.some.inj (hctors.symm.trans (hctorsAs _ hcl))
    rw [heq] at hcA
    have hck : rc.tgt < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k := by
      rw [← hN.2.2]; exact hN.2.1 _ i cA hcA
    obtain ⟨hfind, -, -⟩ := hcore.2.2.2 _ hck i cA hcA
    rw [hnPc]
    exact hfind
  | none =>
    obtain ⟨D, mm, cvI, hD⟩ := tgtOutCls_of hcov E hm
    have hi : i < M.ctors.length := (List.getElem?_eq_some_iff.mp hcA).1
    have hc := hD.hctor i hi
    have hcA' : M.ctors[i] = cA := (List.getElem?_eq_some_iff.mp hcA).2
    rw [hcA'] at hc
    have hname := find?_some_name hc
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    rw [hname]
    exact hc

/-- **`ctorsIn`**: every constructor a checked recursor carries is stored. -/
theorem tgtRecCtor_in
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    (hN : BlockNamesOk (V := V) (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM c))
    (hcov : LfpCover mpC []) :
    ∀ r ∈ tgtRs out, ∀ cA ∈ r.2.2.2,
      ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF) := by
  intro r hr cA hcA
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hcA
  exact ⟨_, _, _, tgtRecCtor_find R hN hcore hctorsAs hcov j r hj i cA hi⟩

/-- **`ctor`**: the carried constructors, stored at the MAJOR's parameter
count, their types bound (the environment's well-formedness) and read
(`EnvModelM.type_reads`). -/
theorem tgtRecCtor_seam
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    (hN : BlockNamesOk (V := V) (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM c))
    (hcov : LfpCover mpC []) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2) ∧
        ConstsBound envC cA.1.type ∧
        ∀ ψ : Name → Nat,
          denoteMeta mpC.base2.acval envC ψ 0 cA.1.type
            = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) := by
  intro j r hr i cA hcA
  have hfind := tgtRecCtor_find R hN hcore hctorsAs hcov j r hr i cA hcA
  have hmem := List.mem_of_find?_eq_some hfind
  have hwfC := mpC.base2.wf _ hmem
  have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
  have hsel : (((tgtRs out).getD j default).2.2.2.getD i default) = cA := by
    rw [hrd, List.getD_eq_getElem?_getD, hcA]; rfl
  refine ⟨hfind, constsBound_of_constsResolve _ hwfC.2.2.1, fun ψ => ?_⟩
  obtain ⟨ta, hta⟩ := mpC.type_reads _ hmem ψ
  change denoteMeta mpC.base2.acval envC ψ 0 cA.1.type = some ta at hta
  rw [blockRecCtorTy, hsel, hta]
  rfl

end Ctors

section Pins

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {mem : Nat → Prop}

omit [SetTheory V] in
/-- **`pinsNoProj`**: a `.nested` firing's pins mention no empty
projection slot — they are subterms of the stored (annotated) recursor
type, lowered. -/
theorem tgtFire_pinsNoProj (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs rs mem)
    {resolves : Expr → Bool} {Ms : Nat → TargetMajor} :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ lvls pins,
        ConLeche.tgtFireOf resolves pp.toBlockShape Ms j r = .nested lvls pins →
        ∀ pin ∈ pins, ∀ (T : Name) (i : Nat), envC.findProj? T i = none →
          Expr.NoProjAt T i pin := by
  intro j r hr lvls pins hf pin hpin T i hT
  obtain ⟨-, -, -, pre, dom, body, bm, D, hs, -, hargs⟩ := ConLeche.tgtFireOf_nested hf
  have hty := (ConLeche.recStage_cvFacts h r (List.mem_of_getElem? hr)).2.2.2 T i hT
  have hb := Expr.NoProjAt.stripPis _ hs hty
  have hdom := (Expr.noProjAt_forallE.mp hb).1
  have hmem : pin.liftLooseBVars (pp.toBlockShape.majorIdxAt j - pp.toBlockShape.rulePrefixAt j) 0
      ∈ dom.getAppArgs := by
    rw [hargs]
    exact List.mem_append_left _ (List.mem_map_of_mem hpin)
  exact Expr.NoProjAt.of_liftLooseBVars (Expr.NoProjAt.getAppArgs hdom _ hmem)

end Pins

/-! ## `tower`: every stored rule reads as a λ-tower over its prefix and fields

At ANY major: the target rule run opens the stored rule's λ-tower at the
prefix and field openers (`TargetRuleRun.hlams`), which are the fvars
`0 … rP + nF − 1` (`blockRuleOpeners_index`), so a reading of the rule is
a λ-telescope of that length (`instLamsAt_denotePTele`). -/

section Tower

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}

omit [SetTheory V] in
/-- **`tower`** (at every major, fired or not). -/
theorem tgtRuleTower_run
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      ∀ (acv : Name → (Name → Nat) → AnnotTerm) (env₃ : Env) (ψ : Name → Nat) (Ra : AnnotTerm),
        denoteMeta acv env₃ ψ 0 rhs = some Ra →
        ∃ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A ∧
          lds.length = pp.toBlockShape.rulePrefixAt j + cA.2 := by
  intro j r hr i cA rhs hcA hrhs acv env₃ ψ Ra hread
  obtain ⟨rc, cvRi, M, u, rhssA, hrc, -, -, rfl, hlenR, RR, -⟩ := ConLeche.targetRecRun_at R hr
  obtain ⟨-, -, hR⟩ := ConLeche.recShape_at (q := pp.toBlockShape) hrc
  simp only at hcA hrhs
  obtain ⟨rhs0, hrhs0⟩ : ∃ rhs0, rc.rhss[i]? = some rhs0 :=
    ⟨_, List.getElem?_eq_getElem (by
      rw [hlenR]; exact (List.getElem?_eq_some_iff.mp hcA).1)⟩
  obtain ⟨o, hoi, hrun⟩ := RR.rule i cA rhs0 hcA hrhs0
  obtain rfl : rhs = o := Option.some.inj (hrhs.symm.trans hoi)
  obtain ⟨Q⟩ := ConLeche.targetRule_run hrun
  have hlenP : Q.fvsPref.length = rc.rP := openPisAtFvars_length _ Q.hpref
  have hlenF : Q.fvsF.length = cA.2 := openPisAtFvars_length _ Q.hfld
  obtain ⟨Γ, C, htele, hΓlen, -, -⟩ :=
    instLamsAt_denotePTele (acval := acv) (env := env₃) (φ := ψ) _ Q.hlams
      (blockRuleOpeners_index Q.hpref Q.hfld) hread
  obtain ⟨lds, hmap, hT⟩ := lamTele_mkLamsAV htele
  refine ⟨lds, C, hT, ?_⟩
  have hq : (lds.map (·.2)).length = Γ.reverse.length := by rw [hmap]
  simp only [List.length_map, List.length_reverse] at hq
  rw [hq, hΓlen, List.length_append, hlenP, hlenF, hR]

end Tower


/-! ## The target field domains' length -/

omit [SetTheory V] in
/-- The target field domains at a stored pair are as many as the
constructor's fields (the rule run opens them, `TargetRuleRun.hfld`). -/
theorem tgtFdomsAV_length {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool}
    {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F fe.env pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) :
    ∀ (ψ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      (tgtFdomsAV pp.toBlockShape out acval env ψ j i).length = cA.2 := by
  intro ψ j r hr i cA hcA
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[i]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by
      rw [recStage_rulesLen h hr]; exact (List.getElem?_eq_some_iff.mp hcA).1)⟩
  obtain ⟨rc, rhs0, M, Q, -, -, hFld, -, -, -, -⟩ := tgtRuleAt_factsG h R hr hcA hrhs
  rw [tgtFdomsAV, readOpenedDoms_length_eq, ← hFld]
  exact openPisAtFvars_length _ Q.hfld

/-! ## `eqP`: the target rule data read alike at valuations agreeing on the recursor's parameters

At ANY major, by the reading's level footprint (`lpDefF`,
`denoteMeta_params_extF`): the major's levels and parameters are read
off the recursor type's major domain (the checked type names only the
recursor's level parameters), the fired constructor's type names only
its own (a member's are the block's, a container's are instantiated at
the major's levels, as many as the container's own), and opening at
fvars keeps the footprint. -/

section Params

omit [SetTheory V] in
/-- Opening a telescope at fvars keeps the footprint, in the openers'
types and in the body. -/
theorem lpDefF_openPisAtFvars {ps : List Name} :
    ∀ (n : Nat) (e : Expr) (i : Nat) {fvs : List Expr} {body : Expr},
      ConLeche.openPisAtFvars n e i = some (fvs, body) → lpDefF ps e = true →
      (∀ x ∈ fvs, lpDefF ps x.fvarTypeD = true) ∧ lpDefF ps body = true
  | 0, e, i, fvs, body, h, he => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun x hx => (nomatch hx), he⟩
  | n + 1, e, i, fvs, body, h, he => by
    cases e with
    | forallE dom b m =>
      simp only [ConLeche.openPisAtFvars] at h
      split at h
      · next fvs' e' hrec =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [lpDefF, Bool.and_eq_true] at he
        obtain ⟨h1, h2⟩ := lpDefF_openPisAtFvars n _ (i + 1) hrec
          (lpDefF_instantiate1 (v := .fvar i dom) rfl _ _ he.1.2)
        refine ⟨fun x hx => ?_, h2⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he.1.1
        · exact h1 x hx
      · exact nomatch h
    | _ => simp [ConLeche.openPisAtFvars] at h

omit [SetTheory V] in
/-- Instantiating a telescope at footprint-bounded arguments keeps the
footprint. -/
theorem lpDefF_instPisWith {ps : List Name} :
    ∀ (ds : List Expr) (e : Expr) {r : Expr}, (∀ d ∈ ds, lpDefF ps d = true) →
      lpDefF ps e = true → ConLeche.instPisWith ds e = some r → lpDefF ps r = true
  | [], e, r, _, he, h => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h
    exact h ▸ he
  | a :: as, e, r, hds, he, h => by
    cases e with
    | forallE dom b m =>
      simp only [ConLeche.instPisWith] at h
      simp only [lpDefF, Bool.and_eq_true] at he
      exact lpDefF_instPisWith as _ (fun d hd => hds d (List.mem_cons_of_mem _ hd))
        (lpDefF_instantiate1 (hds a List.mem_cons_self) _ _ he.1.2) h
    | _ => simp [ConLeche.instPisWith] at h

omit [SetTheory V] in
/-- Instantiating ALL of a term's level parameters at bounded levels
bounds its footprint. -/
theorem lpDefF_instantiateLevelParams {ps ks : List Name} {us : List Level}
    (hl : us.length = ks.length) (hus : ∀ u ∈ us, u.allParamsDefined ps = true) :
    ∀ e : Expr, e.allLevelParamsDefined ks = true →
      lpDefF ps (e.instantiateLevelParams ks us) = true := by
  intro e
  induction e with
  | bvar => intro _; rfl
  | fvar => intro _; rfl
  | lit => intro _; rfl
  | sort u =>
    intro h
    exact ConLeche.Level.allParamsDefined_subst hl hus h
  | const n vs =>
    intro h
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Expr.instantiateLevelParams, lpDefF, List.all_eq_true, List.mem_map]
    rintro _ ⟨v, hv, rfl⟩
    exact ConLeche.Level.allParamsDefined_subst hl hus (h v hv)
  | app f a ihf iha =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, lpDefF, ihf h.1, iha h.2, Bool.and_self]
  | lam t b m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, lpDefF, iht h.1.1, ihb h.1.2,
      ConLeche.Level.substPW_paramsDefined hl hus h.2, Bool.and_self]
  | forallE t b m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, lpDefF, iht h.1.1, ihb h.1.2,
      ConLeche.Level.substPW_paramsDefined hl hus h.2, Bool.and_self]
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, lpDefF, iht h.1.1, ihv h.1.2, ihb h.2,
      Bool.and_self]
  | proj s i e ih =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, lpDefF, ih h]

/-- The opened domains read alike at valuations agreeing on their
footprint. -/
theorem readOpenedDoms_params {env : Env} (m : EnvModel V env) {ps : List Name}
    {ψ₁ ψ₂ : Name → Nat} (hq : ∀ q ∈ ps, ψ₁ q = ψ₂ q) :
    ∀ (d : Nat) (fvs : List Expr), (∀ x ∈ fvs, lpDefF ps x.fvarTypeD = true) →
      readOpenedDoms m.acval env ψ₁ d fvs = readOpenedDoms m.acval env ψ₂ d fvs
  | _, [], _ => rfl
  | d, x :: xs, h => by
    simp only [readOpenedDoms]
    rw [denoteMeta_params_extF m hq _ _ (h x List.mem_cons_self),
      readOpenedDoms_params m hq (d + 1) xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

omit [SetTheory V] in
/-- A term naming only parameters of `ks` names only parameters of any
`ps ⊇ ks`. -/
theorem lpDefF_of_sub {ps ks : List Name} (hsub : ∀ q ∈ ks, q ∈ ps) {e : Expr}
    (h : e.allLevelParamsDefined ks = true) : lpDefF ps e = true := by
  have := lpDefF_instantiateLevelParams (ps := ps) (us := ks.map Level.param)
    (by rw [List.length_map]) (fun u hu => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
      simp [Level.allParamsDefined, hsub q hq]) e h
  rwa [Expr.instantiateLevelParams_self] at this

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}

omit [SetTheory V] in
/-- **The major's levels and parameters name only the recursor's level
parameters** — they are read off the checked recursor type's major
domain (a member's parameters are its openers). -/
theorem tgtMaj_lp
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) :
    (∀ u ∈ (tgtMajor out j).lvls, u.allParamsDefined r.1.levelParams = true) ∧
      ∀ d ∈ (tgtMajor out j).ds, lpDefF r.1.levelParams d = true := by
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hcv : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) envC rc.cvR = .ok r.1 := by
    rw [← ConLeche.checkConstantValF_eq]; exact E.hcv
  obtain ⟨-, -, -, -, -, -, type, -, -, -, hlpT, -, -, -, hcv'⟩ :=
    ConLeche.checkConstantVal_inv hcv
  have hty : r.1.type.allLevelParamsDefined r.1.levelParams = true := by
    rw [hcv']; exact hlpT
  have hmajT : lpDefF r.1.levelParams E.maj.fvarTypeD = true :=
    (lpDefF_openPisAtFvars _ _ _ E.hopen (lpDefF_of_allLevelParamsDefined _ hty)).1 _
      (List.mem_of_getElem? E.hmaj)
  have hsplit := lpDefF_mkAppN_args E.maj.fvarTypeD.getAppArgs
    (f := E.maj.fvarTypeD.getAppFn) (by rw [Expr.mkAppN_getApp]; exact hmajT)
  cases hm : (tgtMajor out j).member with
  | none =>
    obtain ⟨-, hfn, -, -, -, hds, -⟩ := E.outside_of hm
    rw [hfn] at hsplit
    refine ⟨fun v hv => ?_, fun d hd => ?_⟩
    · have := hsplit.1
      simp only [lpDefF, List.all_eq_true] at this
      exact this v hv
    · rw [hds] at hd; exact hsplit.2 d (List.mem_of_mem_take hd)
  | some t =>
    have hMs : (tgtMajor out j).member.isSome = true := by simp [hm]
    obtain ⟨-, hlvls⟩ := ConLeche.targetTyEntry_major_of E hMs
    refine ⟨fun v hv => ?_, fun d hd => ?_⟩
    · rw [hlvls] at hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      simp [Level.allParamsDefined, recStage_lps_sub h hr q hq]
    · rw [E.ds_eq_of hMs] at hd
      obtain ⟨n, t, rfl⟩ := openPisAtFvars_mem_fvar E.hopen d (List.mem_of_mem_take hd)
      rfl

/-- **The fired constructor's type, at the major's instantiation, names
only the recursor's level parameters** — a member's constructor is the
block's (its parameters the block's, `BlockCtorsCore`), a container's is
instantiated at the major's levels, as many as its own
(`tgtOutSat`, `tgtOutOpen`). -/
theorem tgtCtorAt_lp (hμ : μ.verifiedChecks = true)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    {mpC : EnvModelM V μ envC} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    (hN : BlockNamesOk (V := V) (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM c))
    (hcov : LfpCover mpC [])
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) :
    lpDefF r.1.levelParams (ConLeche.targetCtorAt (tgtMajor out j) cA.1) = true := by
  have hfind := tgtRecCtor_find R hN hcore hctorsAs hcov j r hr i cA hcA
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfind)
  have hlpC : cA.1.type.allLevelParamsDefined cA.1.levelParams = true := hwfC.2.1
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  cases hm : (tgtMajor out j).member with
  | some t =>
    simp only [ConLeche.targetCtorAt, hm]
    -- a member's constructor: its level parameters are the block's
    obtain ⟨ms, -, -, -, -, hctors, -⟩ := E.member_facts_of (by simp [hm])
    have hcA' : (tgtMajor out j).ctors[i]? = some cA := by rw [← tgtRs_ctors hr]; exact hcA
    have hcl : rc.tgt < ctorsAs.length := (List.getElem?_eq_some_iff.mp hctors).1
    have heq : (tgtMajor out j).ctors
        = (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM rc.tgt :=
      Option.some.inj (hctors.symm.trans (hctorsAs _ hcl))
    rw [heq] at hcA'
    have hck : rc.tgt < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k := by
      rw [← hN.2.2]; exact hN.2.1 _ i cA hcA'
    obtain ⟨-, hlps, -⟩ := hcore.2.2.2 _ hck i cA hcA'
    exact lpDefF_of_sub (fun q hq => recStage_lps_sub h hr q (hlps ▸ hq)) hlpC
  | none =>
    simp only [ConLeche.targetCtorAt, hm]
    obtain ⟨D, mm, cvI, hcl⟩ := tgtOutCls_of hcov E hm
    obtain ⟨dsa, hdsa, hul, hds, hlenP, -⟩ := tgtOutSat hμ mpC hcov h R hr hm hcl (fun _ => 0)
    obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[i]? = some rhs :=
      ⟨_, List.getElem?_eq_getElem (by
        rw [recStage_rulesLen h hr]; exact (List.getElem?_eq_some_iff.mp hcA).1)⟩
    obtain ⟨-, hlpsI, -⟩ := tgtOutOpen (mpC := mpC) R hr hcA hrhs hm hcl hul hds (fun _ => 0)
      hdsa hlenP
    exact lpDefF_instantiateLevelParams (by rw [hul, hlpsI]) (tgtMaj_lp R h hr).1 _ hlpC

/-- **`eqP`'s row at ANY major**: the rule's field domains, index
expressions and fired spine read alike at valuations agreeing on the
recursor's level parameters. -/
theorem tgtRow_params (hμ : μ.verifiedChecks = true)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    {mpC : EnvModelM V μ envC} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    (hN : BlockNamesOk (V := V) (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM c))
    (hcov : LfpCover mpC [])
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {ψ₁ ψ₂ : Name → Nat} (hq : ∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) :
    tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
        = tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i ∧
      tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
        = tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i ∧
      tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
        = tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i := by
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, -, -, hCrest, hFld, -, -, -⟩ :=
    targetRuleAtG R hr hcA hrhs
  subst hMaj
  obtain ⟨hlv, hds⟩ := tgtMaj_lp R h hr
  have hct := tgtCtorAt_lp hμ R hN hcore hctorsAs hcov h hr hcA
  have hcr : lpDefF r.1.levelParams Q.crest = true := lpDefF_instPisWith _ _ hds hct Q.hcrest
  obtain ⟨hfT, hcb⟩ := lpDefF_openPisAtFvars _ _ _ Q.hfld hcr
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hcbE : tgtCbody pp.toBlockShape out j i = Q.cbody := by
    rw [tgtCbody, tgtCtorOf_at hr hcA, ← hCrest, hRP, Q.hfld]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [tgtFdomsAV, tgtFdomsAV, ← hFld]
    exact readOpenedDoms_params mpC.base2 hq _ _ hfT
  · rw [tgtEsAV, tgtEsAV, hcbE]
    have hargs := (lpDefF_mkAppN_args Q.cbody.getAppArgs (f := Q.cbody.getAppFn)
      (by rw [Expr.mkAppN_getApp]; exact hcb)).2
    refine List.map_congr_left fun e he => ?_
    rw [denoteMeta_params_extF mpC.base2 hq _ _ (hargs e (List.mem_of_mem_drop he))]
  · rw [tgtMkAV, tgtMkAV]
    refine congrArg (·.getD default) (denoteMeta_params_extF mpC.base2 hq _ _ ?_)
    refine lpDefF_mkAppN _ ?_ (fun a ha => ?_)
    · simp only [lpDefF, List.all_eq_true]; exact hlv
    · rcases List.mem_append.mp ha with ha | ha
      · exact hds a ha
      · rw [← hFld] at ha
        obtain ⟨n, t, rfl⟩ := openPisAtFvars_mem_fvar Q.hfld a ha
        rfl

end Params

/-! ## `eqB`: the target rule data are bound by their frames, at every major

The rows of `blockRecEqs_below_rows`: at a member major the block's own
(`blockRule_rowB_member` through `tgt…_eq_block`); at an outside major
the field domains by `tgtOutFdoms_bounded`, the index expressions and the
fired spine by their readings (the instantiated constructor is scoped at
the prefix); the `ih` terms and the residue at ANY major by
`tgtRule_belowG`, the major's parameters scoped (`tgtDsOk_any`) and the
fired constructor closed (`tgtCtorAt_closed`). -/

section RowsB

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {isRec : Bool}
  {A : Nat → (Name → Nat) → AnnotTerm}

/-- **The fired constructor's type at ANY major is closed and bound**: a
member's is stored; a container's is its stored one at the major's
levels. -/
theorem tgtCtorAt_closed
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    (hN : BlockNamesOk (V := V) (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM c))
    (hcov : LfpCover mpC [])
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) :
    (ConLeche.targetCtorAt (tgtMajor out j) cA.1).hasFvar = false ∧
      (ConLeche.targetCtorAt (tgtMajor out j) cA.1).looseBVarsBounded 0 = true ∧
      ConstsBound envC (ConLeche.targetCtorAt (tgtMajor out j) cA.1) := by
  have hfind := tgtRecCtor_find R hN hcore hctorsAs hcov j r hr i cA hcA
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfind)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hCr : cA.1.type.constsResolve envC = true := hwfC.2.2.1
  cases hm : (tgtMajor out j).member with
  | some t =>
    simp only [ConLeche.targetCtorAt, hm]
    exact ⟨hCf, hCb, constsBound_of_constsResolve _ hCr⟩
  | none =>
    simp only [ConLeche.targetCtorAt, hm]
    refine ⟨by rw [Expr.hasFvar_instantiateLevelParams]; exact hCf,
      by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hCb,
      constsBound_of_constsResolve _ ?_⟩
    rw [ConLeche.Expr.constsResolve_instantiateLevelParams]; exact hCr

omit [SetTheory V] in
/-- **The major's parameters are scoped at the prefix, at ANY major**
(`TgtDsOk`): a member's are its prefix openers, a container's the
arguments of the recursor type's major domain. -/
theorem tgtDsOk_any
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) :
    TgtDsOk envC (tgtRP pp.toBlockShape j) (tgtPrefFvs pp.toBlockShape out j)
      (tgtMajor out j).ds := by
  cases hm : (tgtMajor out j).member with
  | some t => exact tgtDsOk_member (fe := ConLeche.mkFEnv envC) h R hr (by simp [hm])
  | none => exact tgtOutDsOk h R hr hm

omit [SetTheory V] in
/-- **The rule's conclusion and field openers are scoped at the rule's
width** (at ANY major): the instantiated constructor is scoped at the
prefix, its opening at the fields. -/
theorem tgtCbody_scoped
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hDs : TgtDsOk envC (tgtRP pp.toBlockShape j) (tgtPrefFvs pp.toBlockShape out j)
      (tgtMajor out j).ds)
    (hCf : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).looseBVarsBounded 0 = true) :
    Expr.WScoped (tgtB pp.toBlockShape out j i) (tgtCbody pp.toBlockShape out j i) ∧
      (tgtCbody pp.toBlockShape out j i).looseBVarsBounded 0 = true ∧
      ∀ x ∈ tgtFieldFvs pp.toBlockShape out j i,
        Expr.WScoped (tgtB pp.toBlockShape out j i) x ∧ x.looseBVarsBounded 0 = true := by
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, -, -, hCrest, hFld, -, -, -⟩ :=
    targetRuleAtG R hr hcA hrhs
  subst hMaj
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hB : tgtB pp.toBlockShape out j i = rc.rP + cA.2 := by
    rw [tgtB_at hr hcA]; exact congrArg (· + cA.2) hRP
  have hcr := Q.hcrest
  rw [ConLeche.instPisWith_eq_instPisAt] at hcr
  obtain ⟨⟨doms, crest'⟩, hinstC, hcr'⟩ := Option.map_eq_some_iff.mp hcr
  obtain rfl : crest' = Q.crest := hcr'
  have hw₂ : Expr.WScoped rc.rP Q.crest :=
    (instPisAt_WScoped (d := rc.rP) _ _ hinstC (Expr.WScoped.of_not_hasFvar hCf)
      (fun a ha => by rw [← hRP]; exact (hDs a ha).1)).2
  have hb₂ : Q.crest.looseBVarsBounded 0 = true :=
    (ConLeche.Verify.instPisAt_bounded _ hinstC hCb (fun a ha => (hDs a ha).2.1)).2
  obtain ⟨hwF, hwB⟩ := openPisAtFvars_WScoped cA.2 Q.crest rc.rP Q.hfld hw₂
  obtain ⟨hbB, -⟩ := ConLeche.Verify.openPisAtFvars_bounded cA.2 Q.hfld hb₂
  have hcbE : tgtCbody pp.toBlockShape out j i = Q.cbody := by
    rw [tgtCbody, tgtCtorOf_at hr hcA, ← hCrest, hRP, Q.hfld]; rfl
  rw [hB, hcbE, ← hFld]
  exact ⟨hwB, hbB, fun x hx => ⟨hwF x hx, openPisAtFvars_fvars_closed Q.hfld x hx⟩⟩

omit [SetTheory V] in
/-- A member of a read spine reads as a member of the reading. -/
theorem DenoteMetaSpine.mem_val {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) :
    ∀ x ∈ as, ∃ v ∈ vs, denoteMeta acval env φ d x = some v := by
  induction h with
  | nil => intro x hx; exact nomatch hx
  | cons ha _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, List.mem_cons_self, ha⟩
    · obtain ⟨v, hv, hr⟩ := ih x hx'
      exact ⟨v, List.mem_cons_of_mem _ hv, hr⟩

/-- **The index expressions at an outside major are bound by the rule's
width** — they are arguments of the rule's conclusion, which reads
(`tgtOutCbody`) and is scoped there. -/
theorem tgtOutEs_below (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI)
    (hDs : TgtDsOk envC (tgtRP pp.toBlockShape j) (tgtPrefFvs pp.toBlockShape out j)
      (tgtMajor out j).ds)
    (hCf : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).looseBVarsBounded 0 = true)
    (ψ : Name → Nat) :
    ∀ e ∈ tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ j i,
      Term.bvarsBelow (tgtB pp.toBlockShape out j i) e.erase := by
  obtain ⟨cargs, hcE, -, hrd⟩ := tgtOutCbody hμ hcov h R hr hcA hrhs hMo hcl ψ
  obtain ⟨hwC, hbC, -⟩ := tgtCbody_scoped R hr hcA hrhs hDs hCf hCb
  rw [hcE] at hrd hwC hbC
  have hX := bvarsBelow_of_reading (m := mpC.base2) hwC hbC hrd
  obtain ⟨fa, vs, -, hvs, heq⟩ := denoteMeta_mkAppN_inv hrd
  rw [heq, AnnotTerm.erase_mkAppN] at hX
  obtain ⟨-, hall⟩ := bvarsBelow_mkAppN_inv hX
  intro e he
  rw [tgtEsAV, hcE, Expr.getAppArgs_mkAppN] at he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  have ha' : a ∈ cargs := by
    have := List.mem_of_mem_drop ha
    simpa [Expr.getAppArgs] using this
  obtain ⟨v, hv, hrv⟩ := DenoteMetaSpine.mem_val hvs a ha'
  rw [hrv, Option.getD_some]
  exact hall v.erase (List.mem_map_of_mem hv)

/-- **The fired spine at an outside major is bound by the rule's width**
— it reads (`tgtOutMkAV_eq`) and is scoped there. -/
theorem tgtOutMk_below (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI)
    (hDs : TgtDsOk envC (tgtRP pp.toBlockShape j) (tgtPrefFvs pp.toBlockShape out j)
      (tgtMajor out j).ds)
    (hCf : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).looseBVarsBounded 0 = true)
    (ψ : Name → Nat) :
    Term.bvarsBelow (tgtB pp.toBlockShape out j i)
      (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i).erase := by
  obtain ⟨hrd, -⟩ := tgtOutMkAV_eq hμ hcov h R hr hcA hrhs hMo hcl ψ
  obtain ⟨-, -, hF⟩ := tgtCbody_scoped R hr hcA hrhs hDs hCf hCb
  have hle : tgtRP pp.toBlockShape j ≤ tgtB pp.toBlockShape out j i := by
    rw [tgtB]; exact Nat.le_add_right _ _
  refine bvarsBelow_of_reading (m := mpC.base2)
    (Expr.WScoped.mkAppN (by simp [Expr.WScoped]) fun x hx => ?_)
    (looseBVarsBounded_mkAppN rfl fun x hx => ?_) hrd
  · rcases List.mem_append.mp hx with hx | hx
    · exact (hDs x hx).1.mono hle
    · exact (hF x hx).1
  · rcases List.mem_append.mp hx with hx | hx
    · exact (hDs x hx).2.1
    · exact (hF x hx).2

/-- **`eqB`'s rows at every major** (`blockRecEqs_below_rows`' premise at
the target data). -/
theorem tgtRowB (hμ : μ.verifiedChecks = true)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    (hN : BlockNamesOk (V := V) (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM c))
    (hcov : LfpCover mpC []) (hformer : ∀ cv ∈ cvTas, cv.type.hasFvar = false)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (hmem : ∀ c, (tgtMajor out c).member.isSome = true → memR c) :
    ∀ (ψ : Name → Nat) (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs →
        FieldsBelow (pp.toBlockShape.rulePrefixAt c)
          (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ∧
        (∀ e ∈ tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j, Term.bvarsBelow
          (pp.toBlockShape.rulePrefixAt c
            + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length) e.erase) ∧
        Term.bvarsBelow (pp.toBlockShape.rulePrefixAt c
            + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
          (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j).erase ∧
        (∀ v ∈ tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ c j, Term.bvarsBelow
          ((tgtRs out).length + pp.toBlockShape.rulePrefixAt c
            + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length) v.erase) ∧
        Term.bvarsBelow (pp.toBlockShape.rulePrefixAt c
            + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length
            + (tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval envC ψ c j).length)
          (tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ c j).erase := by
  intro ψ c r hr j cA rhs hcA hrhs
  rw [tgtFdomsAV_length (fe := ConLeche.mkFEnv envC) h R mpC.base2.acval envC ψ c r hr j cA hcA]
  have hDs := tgtDsOk_any R h hr
  obtain ⟨hCf, hCb, hCc⟩ := tgtCtorAt_closed R hN hcore hctorsAs hcov hr hcA
  obtain ⟨hI, hRb⟩ := tgtRule_belowG (fe := ConLeche.mkFEnv envC) hμ mpC.base2 h R hformer ψ hr
    hcA hrhs hDs hCf hCb hCc
  have hB : tgtB pp.toBlockShape out c j = pp.toBlockShape.rulePrefixAt c + cA.2 := tgtB_at hr hcA
  cases hm : (tgtMajor out c).member with
  | some t =>
    have hms : (tgtMajor out c).member.isSome = true := by simp [hm]
    obtain ⟨hF, -, hE, hM⟩ := blockRule_rowB_member h hcore (hmem c hms) hr hcA hrhs ψ
    rw [tgtFdomsAV_eq_block R hr hcA hrhs hms, tgtEsAV_eq_block R hr hcA hrhs hms,
      tgtMkAV_eq_block R hr hcA hrhs hms]
    exact ⟨hF, hE, hM, hI, hRb⟩
  | none =>
    obtain ⟨rc', u', -, ⟨E⟩⟩ := targetEntryAt R hr
    obtain ⟨D, mm, cvI, hcl⟩ := tgtOutCls_of hcov E hm
    refine ⟨fieldsBelow_of_getD fun q hq =>
      tgtOutFdoms_bounded hμ hcov h R hr hcA hrhs hm hcl ψ q hq, ?_, ?_, hI, hRb⟩
    · rw [← hB]
      exact tgtOutEs_below hμ hcov h R hr hcA hrhs hm hcl hDs hCf hCb ψ
    · rw [← hB]
      exact tgtOutMk_below hμ hcov h R hr hcA hrhs hm hcl hDs hCf hCb ψ

end RowsB

end ConLeche.Model
