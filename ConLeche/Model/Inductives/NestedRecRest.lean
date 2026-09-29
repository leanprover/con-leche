module

import ConLeche.Verify.Cached.PushChain
import Std.Data.String.ToNat
public import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Verify.InstLevels

public section

/-!
# The nested recursors' stage: the facts beside the class induction

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

/-! ## A `.nested` firing's pins mention no empty slot

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

section Ctors

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {isRec : Bool}
  {A : Nat → (Name → Nat) → AnnotTerm}

/-- **`ctor` from the constructors' storage**: carried constructors
stored at the major's parameter count have their types bound (the
environment's well-formedness) and read (`EnvModelM.type_reads`).  Any
recursor stage whose carried constructors are stored has `ctor`. -/
theorem tgtRecCtor_seam_of_find {envC : Env} {mpC : EnvModelM V μ envC}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (hfind0 : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name
          = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2)) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2) ∧
        ConstsBound envC cA.1.type ∧
        ∀ ψ : Name → Nat,
          denoteMeta mpC.base2.acval envC ψ 0 cA.1.type
            = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) := by
  intro j r hr i cA hcA
  have hfind := hfind0 j r hr i cA hcA
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
/-- **A `.nested` firing's pins mention no empty
projection slot** — they are subterms of the stored (annotated) recursor
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

end Tower


/-! ## The target field domains' length -/

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

end RowsB

end ConLeche.Model
