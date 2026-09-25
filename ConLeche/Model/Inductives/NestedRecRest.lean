module

public import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Cached.PushChain
import ConLeche.Model.Inductives.BlockRecAssembly
import Std.Data.String.ToNat
public import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.TargetClass
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.IndTowerRead

public section

/-!
# The nested recursors' stage: the facts beside the class induction (lane RECREST)

`NestedRecRest`'s fields (`NestedRecStage.lean`), one producer each, at
the target check's run (`TargetRecRun … true …`, the route switch on).
Each field discharged here is consumed by `nestedRecStageOwed_of` and
dropped from the owed bundle.
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
    Model.nodup_of_subset_length (recAuxWant_nodup q) hwant (Nat.le_of_eq hlenA)
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
  {ctorsAs : List (List (ConstantVal × Nat))} {outside nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {isRec : Bool}
  {A : Nat → (Name → Nat) → AnnotTerm}

/-- **Every constructor a checked recursor carries is stored, at its
major's parameter count** — a member's by the constructors' core record,
a container's by the carrier's coverage. -/
theorem tgtRecCtor_find
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
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
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
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
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
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
  {ctorsAs : List (List (ConstantVal × Nat))} {outside nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}

omit [SetTheory V] in
/-- **`tower`** (at every major, fired or not). -/
theorem tgtRuleTower_run
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
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

end ConLeche.Model
