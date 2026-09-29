module

public import ConLeche.Model.Inductives.GenRecAssembly
public import ConLeche.Model.Inductives.GenRecStage
public import ConLeche.Model.Inductives.TargetNodeList
public import ConLeche.Model.Inductives.TargetNodeSem
public import ConLeche.Model.Inductives.TargetNodeCover
import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Verify.EnvBound
public import ConLeche.Model.Inductives.PosDerivNodes
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Inductives.LfpCover
import ConLeche.Verify.Inductives.PosAnn
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.EnvWF
import ConLeche.Model.Cover
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Inductives.TargetClass
import ConLeche.Verify.Inductives.PosNodes

public section

/-!
# The generated stage's classes, and the node list (lane GENREC-B2)

* the run's classes per recursor (`genOut_cls`): a stored recursor's
  major is its class's checked major (`classMajors`) with its table
  entries (`classesNfs`);
* `genOutsideClass_reachedNode` — `outsideClass_reachedNode` at the
  generated stage's seeds (`classSeeds`): every outside class is a seed,
  so a node of the walk;
* `genRecCtx_nodes` — `nestedRecCtx_nodes` at the generated stage's
  context: the node list over the table `R.st.ctorNfs`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassKey ClassSlot ClassMajorRun NestCtx
  NestCtorNf NestFieldKind PosTree PosD NestState fueledOps mkFEnv)

universe w

/-! ## The pre-pass's classes -/

theorem motiveSlot_lt_classes {slots : List ClassSlot} {c s : Nat}
    (h : ClassRead.motiveSlot ⟨slots, []⟩ c = some s) :
    c < (ClassRead.classes ⟨slots, []⟩).length := by
  have hlt : c < ((List.range slots.length).filter fun s =>
      match slots[s]? with | some (.motive _) => true | _ => false).length :=
    (List.getElem?_eq_some_iff.mp h).1
  suffices e : ((List.range slots.length).filter fun s =>
      match slots[s]? with | some (.motive _) => true | _ => false).length
      = (ClassRead.classes ⟨slots, []⟩).length by omega
  simp only [ClassRead.classes]
  clear h hlt
  generalize hn : slots.length = n
  induction n generalizing slots with
  | zero => rw [List.length_eq_zero_iff.mp hn]; rfl
  | succ n ih =>
    obtain ⟨l, a, rfl⟩ : ∃ l a, slots = l ++ [a] := by
      refine ⟨slots.dropLast, slots.getLast (List.ne_nil_of_length_pos (by omega)), ?_⟩
      exact (List.dropLast_concat_getLast _).symm
    have hl : l.length = n := by simpa using hn
    rw [List.range_succ, List.filter_append, List.length_append, List.filterMap_append,
      List.length_append]
    have hl' : ((List.range n).filter fun s =>
        match (l ++ [a])[s]? with | some (.motive _) => true | _ => false)
        = (List.range n).filter fun s =>
          match l[s]? with | some (.motive _) => true | _ => false := by
      refine List.filter_congr fun s hs => ?_
      rw [List.getElem?_append_left (by rw [hl]; exact List.mem_range.mp hs)]
    rw [hl', ih hl]
    congr 1
    simp only [List.filter_cons, List.filter_nil]
    rw [List.getElem?_append_right (by omega), show n - l.length = 0 by omega]
    cases a <;> rfl


/-! ## The seeds -/

theorem mem_classSeeds' {ctx : NestCtx} {holes : List Expr} {Ms : List TargetMajor}
    {s : ConLeche.NestKey × Nat} (h : s ∈ ConLeche.classSeeds ctx holes Ms) :
    ∃ M ∈ Ms, M.member = none ∧ s = ConLeche.nestSeedOf ctx holes M.ind M.lvls M.ds M.nPc := by
  simp only [ConLeche.classSeeds, List.mem_filterMap] at h
  obtain ⟨M, hM, hs⟩ := h
  split at hs
  · rename_i hn
    exact ⟨M, hM, Option.isNone_iff_eq_none.mp hn, (Option.some.inj hs).symm⟩
  · exact nomatch hs

theorem classSeeds_mem' {ctx : NestCtx} {holes : List Expr} {Ms : List TargetMajor}
    {M : TargetMajor} (hM : M ∈ Ms) (hMo : M.member = none) :
    ConLeche.nestSeedOf ctx holes M.ind M.lvls M.ds M.nPc ∈ ConLeche.classSeeds ctx holes Ms := by
  simp only [ConLeche.classSeeds, List.mem_filterMap]
  exact ⟨M, hM, by simp [hMo]⟩

/-- **An outside class, checked as a major**: `TargetMajorRun`'s outside
arm (`TargetTyEntry.outside_of`'s shape). -/
theorem _root_.ConLeche.ClassMajorRun.outside_of {mode : CheckMode} {F : Nat} {fe : FEnv} {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs : List Expr} {key : ClassKey}
    {M : TargetMajor} (C : ClassMajorRun mode F fe p ctorsAs pfvs key M)
    (hM : M.member = none) :
    ∃ sI, p.memberNames.findIdx? (· == M.ind) = none ∧ M.ind ≠ ConLeche.quotName ∧
      ConLeche.targetCtorsOf fe M.ind = some (M.nPc, M.ctors) ∧ M.ds.length = M.nPc ∧
      (∀ x ∈ M.ds, x.bvarB = 0 ∧ x.fvarB ≤ p.nP) ∧
      ConLeche.targetOutsideInst (m := ConLeche.CheckM) fe M.ind M.lvls M.ds = .ok (M.nIdx, sI) ∧
      M.pfvs = pfvs := by
  obtain ⟨major, -⟩ := C
  cases major with
  | member => exact nomatch hM
  | outside I us nPc nIdx ctors sI hfn ht hnq hct hl hsc _ hinst hs =>
    exact ⟨sI, ht, hnq, hct, hl, hsc, hinst, rfl⟩

/-- A class's parameter openers are the run's canonical parameters. -/
theorem _root_.ConLeche.ClassMajorRun.pfvs_eq {mode : CheckMode} {F : Nat} {fe : FEnv} {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs : List Expr} {key : ClassKey}
    {M : TargetMajor} (C : ClassMajorRun mode F fe p ctorsAs pfvs key M) : M.pfvs = pfvs := by
  obtain ⟨major, -⟩ := C
  cases major <;> rfl

section Run

variable {μ : CheckMode} {F : Nat} {env₁ envC : Env} {p : BlockParts} {nestedBit : Bool}
  {pos : NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- A stored recursor's class has a motive: it indexes the run's classes. -/
theorem genRecCls_lt
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) {i c : Nat} (hc : R.rd.recCls[i]? = some c) :
    c < R.Ms.length ∧ R.Ms.length = R.Ms₀.length ∧ R.Ms₀.length = R.rd.classes.length := by
  obtain ⟨s, hs⟩ := ConLeche.classRead_recCls_motive R.hrd c (List.mem_of_getElem? hc)
  have h1 := motiveSlot_lt_classes hs
  have hl0 := (R.majors).1
  rw [R.keys_length] at hl0
  have hl1 := (ConLeche.classesNfs_run R.hMs).1
  have e : (ClassRead.classes ⟨R.rd.slots, []⟩) = R.rd.classes := rfl
  rw [e] at h1
  exact ⟨by omega, hl1, hl0⟩

/-- **A stored recursor's major is its class's** (`genRecRun_at`), the
class a checked major with its table entries. -/
theorem genOut_cls
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) {i : Nat} (hi : i < out.length) :
    ∃ rc cls cvG rhss M₀ nfs, p.recs[i]? = some rc ∧ R.rd.recCls[i]? = some cls ∧
      cls < R.Ms.length ∧ R.Ms₀[cls]? = some M₀ ∧
      R.Ms[cls]? = some { M₀ with nfs := nfs } ∧
      out[i]? = some (cvG, { M₀ with nfs := nfs }, rhss) ∧
      Nonempty (ConLeche.ClassRecTyRun μ F (mkFEnv envC) R.g p.k rc cls cvG) ∧
      Nonempty (ClassMajorRun μ F (mkFEnv envC) p.toBlockShape ctorsAs R.ctx.params
        (R.keys.getD cls default) M₀) ∧
      ConLeche.targetMajorNfs (fueledOps μ F) envC p.toBlockShape (cvTas.map (·.type))
        M₀.pfvs M₀.lvls M₀.ds M₀.ctors R.st.ctorNfs.toList = .ok nfs := by
  have hlenO := (ConLeche.classRecsRulesOk_run R.hrules).1
  have hlenG := (ConLeche.classRecTysOk_run R.hcvGs).1
  have hir : i < p.toBlockShape.recs.length := by omega
  obtain ⟨rc, hrc⟩ : ∃ rc, p.recs[i]? = some rc := ⟨_, List.getElem?_eq_getElem hir⟩
  obtain ⟨cls, cvG, rhss, hc, -, T, ho, -, -⟩ := genRecRun_at R hrc
  obtain ⟨hlt, hl1, hl0⟩ := genRecCls_lt R hc
  obtain ⟨-, hallM⟩ := R.majors
  obtain ⟨-, hallN⟩ := ConLeche.classesNfs_run R.hMs
  have hk : R.keys[cls]?
      = some (R.keys.getD cls default) := by
    have hkl := R.keys_length
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  obtain ⟨M₀, hM₀, hMR⟩ := hallM cls _ hk
  obtain ⟨nfs, hMs, hnfs⟩ := hallN cls M₀ hM₀
  have hgd : R.Ms.getD cls default = { M₀ with nfs := nfs } := by
    rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]
  rw [hgd] at ho
  refine ⟨rc, cls, cvG, rhss, M₀, nfs, hrc, hc, hlt, hM₀, hMs, ho, T, hMR, ?_⟩
  exact hnfs

/-- The same, at `tgtMajor`. -/
theorem genTgtMajor
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) {i : Nat} (hi : i < (ConLeche.tgtRs out).length) :
    ∃ cls M₀ nfs, R.rd.recCls[i]? = some cls ∧ cls < R.Ms.length ∧ R.Ms₀[cls]? = some M₀ ∧
      R.Ms[cls]? = some { M₀ with nfs := nfs } ∧
      tgtMajor out i = { M₀ with nfs := nfs } ∧
      Nonempty (ClassMajorRun μ F (mkFEnv envC) p.toBlockShape ctorsAs R.ctx.params
        (R.keys.getD cls default) M₀) ∧
      ConLeche.targetMajorNfs (fueledOps μ F) envC p.toBlockShape (cvTas.map (·.type))
        M₀.pfvs M₀.lvls M₀.ds M₀.ctors R.st.ctorNfs.toList = .ok nfs := by
  have hi' : i < out.length := by simpa [ConLeche.tgtRs] using hi
  obtain ⟨-, cls, cvG, rhss, M₀, nfs, -, hc, hlt, hM₀, hMs, ho, -, hMR, hnfs⟩ := genOut_cls R hi'
  refine ⟨cls, M₀, nfs, hc, hlt, hM₀, hMs, ?_, hMR, hnfs⟩
  simp [tgtMajor, List.getD_eq_getElem?_getD, ho]


/-- **A class checked as a MEMBER major**: `TargetMajorRun`'s member arm. -/
theorem _root_.ConLeche.ClassMajorRun.member_of {mode : CheckMode} {F : Nat} {fe : FEnv}
    {p : BlockShape} {ctorsAs : List (List (ConstantVal × Nat))} {pfvs : List Expr}
    {key : ClassKey} {M : TargetMajor} (C : ClassMajorRun mode F fe p ctorsAs pfvs key M)
    {m : Nat} (hM : M.member = some m) :
    p.memberNames.findIdx? (· == M.ind) = some m ∧ ctorsAs[m]? = some M.ctors ∧
      M.lvls = p.lps.map .param ∧ M.ds = pfvs.take p.nP ∧ M.nPc = p.nP ∧ M.pfvs = pfvs ∧
      (∃ ms, p.members[m]? = some ms ∧ M.nIdx = ms.nIdx) := by
  obtain ⟨major, -⟩ := C
  cases major with
  | member I t ms ctorsA hfn ht hms hctors hpar nfs =>
    obtain rfl : t = m := Option.some.inj hM
    exact ⟨ht, hctors, rfl, rfl, rfl, rfl, ms, hms, rfl⟩
  | outside => exact nomatch hM

/-- **A stored recursor's prefix, target and member class** at the
generated run. -/
theorem genRec_at
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ConLeche.ClassGenScoped R.g) {c : Nat}
    (hc : c < (ConLeche.tgtRs out).length) :
    tgtRP p.toBlockShape c = R.pre.length ∧ p.toBlockShape.rulePrefixAt c = R.pre.length ∧
      R.pre.length = p.nP + R.rd.slots.length ∧
      ∀ m, (tgtMajor out c).member = some m →
        p.toBlockShape.recTgtAt c = m ∧ ctorsAs[m]? = some (tgtMajor out c).ctors ∧
        p.toBlockShape.memberNames.findIdx? (· == (tgtMajor out c).ind) = some m ∧
        (tgtMajor out c).lvls = p.lps.map .param ∧
        (tgtMajor out c).ds = R.ctx.params.take p.nP ∧ (tgtMajor out c).nPc = p.nP := by
  have hi' : c < out.length := by simpa [ConLeche.tgtRs] using hc
  obtain ⟨rc, cls, cvG, rhss, M₀, nfs, hrc, hcl, hlt, hM₀, hMs, ho, ⟨T⟩, ⟨C⟩, -⟩ :=
    genOut_cls R hi'
  have hMeq : tgtMajor out c = { M₀ with nfs := nfs } := by
    simp [tgtMajor, List.getD_eq_getElem?_getD, ho]
  have hpl : R.pre.length = p.nP + R.rd.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  have hrP : rc.rP = R.pre.length := by rw [T.hrP, hpl]; rfl
  have hgc : R.g.cls.getD cls default = { M₀ with nfs := nfs } := by
    show R.Ms.getD cls default = _
    rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]
  have hrcd : p.toBlockShape.recs.getD c default = rc := by
    rw [List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  refine ⟨by rw [tgtRP, hrcd, hrP], by rw [ConLeche.BlockShape.rulePrefixAt, hrcd, hrP], hpl,
    fun m hm => ?_⟩
  rw [hMeq] at hm ⊢
  have hm' : M₀.member = some m := hm
  obtain ⟨hfi, hct, hlv, hds, hnpc, -, -⟩ := C.member_of hm'
  refine ⟨?_, hct, hfi, hlv, hds, hnpc⟩
  rw [ConLeche.BlockShape.recTgtAt, hrcd, T.htgt, hgc]
  show (M₀.member).getD _ = m
  rw [hm']; rfl


/-- Every class's parameter openers are at most the block's parameters. -/
theorem genMs_pfvs_len
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ConLeche.ClassGenScoped R.g) (t : Nat) :
    (R.Ms.getD t default).pfvs.length ≤ p.nP := by
  rw [List.getD_eq_getElem?_getD]
  cases hMt : R.Ms[t]? with
  | none => exact Nat.zero_le _
  | some M =>
    simp only [Option.getD_some]
    obtain ⟨hl1, hallN⟩ := ConLeche.classesNfs_run R.hMs
    obtain ⟨hl0, hallM⟩ := R.majors
    have ht : t < R.Ms₀.length := by rw [← hl1]; exact (List.getElem?_eq_some_iff.mp hMt).1
    obtain ⟨M₀, hM₀⟩ : ∃ M₀, R.Ms₀[t]? = some M₀ := ⟨_, List.getElem?_eq_getElem ht⟩
    obtain ⟨nfs, hMs, -⟩ := hallN t M₀ hM₀
    rw [hMs] at hMt
    obtain rfl := Option.some.inj hMt
    have hk : t < R.keys.length := by
      rw [← hl0]; exact ht
    obtain ⟨M₀', hM₀', ⟨C⟩⟩ := hallM t _ (List.getElem?_eq_getElem hk)
    rw [hM₀] at hM₀'
    obtain rfl := Option.some.inj hM₀'
    show M₀.pfvs.length ≤ p.nP
    rw [C.pfvs_eq]
    exact Nat.le_of_eq hg.params_len

end Run


/-! ## Every outside class is a reached node -/

open ConLeche (NestKey quotName targetCtorsOf nestSeedOf NestCtxOk NestArityOk SeedOk TreeRec
  MemberCtorD instPisWith nestAbstract nestHoles openPisAtFvars) in
/-- **`outsideClass_reachedNode` at the generated stage**: the seeds are
the outside classes (`classSeeds`), walked from the positivity run's state;
every stored recursor's OUTSIDE class is a seed, so its node is reached,
and it matches the seed's key read back. -/
theorem genOutsideClass_reachedNode {envC envI : Env} (hwf : ConLeche.EnvWF envI) {F : Nat}
    {pp : BlockParts} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {pos : NestState}
    {nested : Bool} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (hpos : ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (fueledOps .verified F) envI
      envI.find? pp cvTas ctorsAs = .ok (kinds, nfs, pos))
    (R : GenRecRun .verified F (mkFEnv envI) envI (mkFEnv envC) pp.toBlockShape nested pos cvTas
      block ctorsAs out)
    (henvC : envC = ConLeche.consBlockCtors pp.nP ctorsAs envI)
    (hheads : ∀ c ∈ ctorsAs.flatten, envI.find? c.1.name = none ∧
      ∀ C, (ctorEntry C (.ctorInfo c.1 pp.nP c.2)).isSome = true →
        C ∈ pp.toBlockShape.memberNames)
    (hT0 : ∀ cvTa0, cvTas.head? = some cvTa0 → cvTa0.type.hasFvar = false)
    (hcl : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false)
    (hAr : ∀ fvsP, NestArityOk (pp.nestCtx fvsP envI.find?))
    (hlpsC : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ cA ∈ cs, cA.1.levelParams = pp.lps) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars pp.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (pp.nestCtx fvsP envI.find?) = some holes ∧
      R.ctx = pp.nestCtx fvsP envI.find? ∧
      (∀ e ∈ pos.ctorNfs.toList, e ∈ R.st.ctorNfs.toList) ∧
      ∀ c, c < out.length → (tgtMajor out c).member = none →
        ∃ ts : List PosTree,
          ((∃ (m : Nat) (cs : List (ConstantVal × Nat)) (j : Nat) (cA : ConstantVal × Nat)
            (crest : Expr) (ks : List NestFieldKind),
            ctorsAs[m]? = some cs ∧ cs[j]? = some cA ∧
            instPisWith fvsP (nestAbstract (pp.nestCtx fvsP envI.find?) holes
              cA.1.type) = some crest ∧
            MemberCtorD (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find?)
              cA.2 crest ks ((nfs.getD m []).getD j default) ts) ∨
           ∃ key, PosD (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find?)
             (.seed key) ts) ∧
          TreeRec (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find?)
            R.st.ctorNfs.toList ts ∧
          ∃ t, PosTree.Reached ts t ∧
            ConLeche.PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find?) t ∧
            NodeMajor F envC pp.toBlockShape (cvTas.map (·.type))
              (pp.nestCtx fvsP envI.find?) (tgtMajor out c) t := by
  have hwsc : ∀ dep e w, (fueledOps .verified F).whnf envI dep e = .ok w → Expr.WScoped dep e →
      Expr.WScoped dep w := fun dep e w hw hws => ConLeche.whnf_WScoped hwf F hw hws
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, hder⟩ :=
    ConLeche.checkBlockPositivity_deriv hwsc hpos
  have hctx : NestCtxOk (pp.nestCtx fvsP envI.find?) :=
    fun n ci hf => (hwf ci (List.mem_of_find?_eq_some hf)).1
  have hparIdx : ∀ i, i < pp.nP → ∃ ty, fvsP[i]? = some (.fvar i ty) := by
    intro i hi
    have hl := ConLeche.Verify.openPisAtFvars_length _ h2
    obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ h2 i _
      (List.getElem?_eq_getElem (by omega))
    exact ⟨ty, by rw [List.getElem?_eq_getElem (by omega), hty]; simp⟩
  have hpar : ∀ x ∈ fvsP, Expr.WScoped ((pp.nestCtx fvsP envI.find?).hiAt 0) x := by
    intro x hx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    have hw := (ConLeche.openPisAtFvars_WScoped pp.nP cvTa0.type 0 h2
      (Expr.WScoped.of_not_hasFvar (hT0 _ h1))).1 x hx
    obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ h2 i _ hi
    have hilt : i < pp.nP := by
      rw [← ConLeche.Verify.openPisAtFvars_length _ h2]; exact (List.getElem?_eq_some_iff.mp hi).1
    simp only [Expr.WScoped] at hw ⊢
    exact ⟨by simp only [ConLeche.NestCtx.hiAt, BlockParts.nestCtx]; omega, hw.2⟩
  have hIpos := (hder hctx (hAr fvsP) hpar hcl hlpsC).2.2
  -- the run's context is the positivity run's
  obtain ⟨cvTa0', fvsP', rest', hcv', hop', hctxR, hholesR⟩ := ConLeche.blockNestCtx_inv R.hctx
  rw [show (mkFEnv envI).find? = envI.find? from funext (ConLeche.mkFEnv_find? envI)] at hctxR
  rw [h1] at hcv'
  obtain rfl := Option.some.inj hcv'
  rw [h2] at hop'
  obtain ⟨rfl, rfl⟩ : fvsP = fvsP' ∧ rest = rest' := by simpa using hop'
  have hctxEq : pp.toBlockShape.nestCtx fvsP envI.find?
      = pp.nestCtx fvsP envI.find? := rfl
  rw [hctxEq] at hctxR
  rw [hctxR, h3] at hholesR
  obtain rfl := Option.some.inj hholesR
  have hst := R.hst
  rw [hctxR] at hst
  refine ⟨cvTa0, fvsP, rest, R.holes, h1, h2, h3, hctxR, ?_⟩
  generalize hctxE : pp.nestCtx fvsP envI.find? = ctx at *
  have hholes := ConLeche.nestHoles_ok hctx h3
  have hlenP : ctx.params.length = ctx.nP := by
    rw [← hctxE]; exact ConLeche.Verify.openPisAtFvars_length _ h2
  have hnP : ctx.nP = pp.nP := by rw [← hctxE]; rfl
  have hnames : ctx.names = pp.toBlockShape.memberNames := by rw [← hctxE]; rfl
  have hparams : ctx.params = fvsP := by rw [← hctxE]; rfl
  -- the classes as majors
  obtain ⟨hlenM₀, hallM₀⟩ := R.majors
  have hMR : ∀ M ∈ R.Ms₀, ∃ key, Nonempty (ClassMajorRun .verified F (mkFEnv envC)
      pp.toBlockShape ctorsAs R.ctx.params key M) := by
    intro M hM
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hM
    have hil : i < R.keys.length := by
      rw [← hlenM₀]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨M', hM', hC⟩ := hallM₀ i _ (List.getElem?_eq_getElem hil)
    rw [hi] at hM'
    obtain rfl := Option.some.inj hM'
    exact ⟨_, hC⟩
  -- every seed is well formed
  have hok : ∀ s ∈ ConLeche.classSeeds ctx R.holes R.Ms₀, SeedOk ctx s := by
    intro s hs
    obtain ⟨M, hM, hMo, rfl⟩ := mem_classSeeds' hs
    obtain ⟨key, ⟨C⟩⟩ := hMR M hM
    obtain ⟨sI, hfi, hnq, hct, hdsLen, hsc, hinst, -⟩ := C.outside_of hMo
    have hnm : M.ind ∉ pp.toBlockShape.memberNames := by
      intro hmem
      have := List.findIdx?_eq_none_iff.mp hfi _ hmem
      simp at this
    obtain ⟨cvI, capsI, hfI⟩ := ConLeche.Model.targetOutsideInst_find hinst
    rw [ConLeche.mkFEnv_find?] at hfI
    rw [targetCtorsOf_mkFEnv, henvC, nestContainer_consBlockCtors hheads hnm (by rw [← henvC]; exact hfI),
      ← nestContainer_ctx (ctx := ctx) (fun n => by rw [← hctxE]; rfl)]
      at hct
    have hds : ∀ x ∈ M.ds, x.fvarsBelow ctx.nP := fun x hx => by
      rw [hnP]; exact ConLeche.Expr.fvarB_le (hsc x hx).2
    have hw := ConLeche.nestSeedOf_ds (I := M.ind) (us := M.lvls) (nPc := M.nPc)
      h3 hlenP hds
    have hW : ∀ x ∈ (nestSeedOf ctx R.holes M.ind M.lvls M.ds M.nPc).1.ds,
        Expr.WScoped (ctx.hiAt 0) x := fun x hx => (hw x hx).2 (fun y hy => (hholes y hy).1)
          (fun y hy => hpar y (by rw [← hctxE] at hy; exact hy))
    have hB := ConLeche.nestSeedOf_closed (I := M.ind) (us := M.lvls) (nPc := M.nPc)
      h3 (fun a ha => by
        rw [← hctxE] at ha
        obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
        obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ h2 i _ hi
        exact ⟨_, ty, rfl⟩)
      (fun x hx => ConLeche.Expr.bvarB_le (Nat.le_of_eq (hsc x hx).1))
    refine ⟨by simp only [nestSeedOf]; rw [hnames]; simpa using hnm, hnq, ⟨_, hct⟩,
      by simp [nestSeedOf, hdsLen],
      fun x hx => ⟨fun hs' hh' l hl => ?_, hW x hx⟩, fun x hx => ⟨?_, ?_⟩⟩
    · rw [h3] at hh'
      obtain rfl := Option.some.inj hh'
      exact (hw x hx).1 l hl
    · have := ConLeche.Expr.looseBVarsBounded_iff.mp (hB x hx)
      rw [ConLeche.Expr.bvarB_eq]; omega
    · rw [ConLeche.Expr.fvarB_eq]
      exact ConLeche.Expr.fvarsBelow_iff.mp (ConLeche.Expr.WScoped.fvarsBelow (hW x hx))
  obtain ⟨-, hall, ⟨l, hl⟩⟩ := ConLeche.nestSeeds_deriv hctx
    (ConLeche.nestRootOk_of_open (ctx := ctx) (by rw [← hctxE]; exact h2)
      (by rw [← hctxE]; exact hAr fvsP)) hwsc _ _ _ hst hok hIpos
  refine ⟨fun e he => by rw [hl]; exact List.mem_append_left _ he, fun c hc hM => ?_⟩
  -- the class's checked major, and its seed
  obtain ⟨-, cls, cvG, rhss, M₀, nfs', -, -, hlt, hM₀, -, ho, -, ⟨C⟩, -⟩ := genOut_cls R hc
  have hMeq : tgtMajor out c = { M₀ with nfs := nfs' } := by
    simp [tgtMajor, List.getD_eq_getElem?_getD, ho]
  have hM₀o : M₀.member = none := by rw [hMeq] at hM; exact hM
  obtain ⟨grp, tsF, hD, hgrp, htr⟩ := hall _ (classSeeds_mem' (List.mem_of_getElem? hM₀) hM₀o)
  obtain ⟨-, -, -, -, -, hsc, -, hpfv⟩ := C.outside_of hM₀o
  have hpl : M₀.pfvs.length = pp.nP := by
    rw [hpfv, hctxR, hparams]; exact ConLeche.Verify.openPisAtFvars_length _ h2
  have hds : ∀ x ∈ M₀.ds, x.fvarsBelow ctx.nP := fun x hx => by
    rw [hnP]; exact ConLeche.Expr.fvarB_le (hsc x hx).2
  have hroot : PosTree.node [] [] (nestSeedOf ctx R.holes M₀.ind M₀.lvls M₀.ds
      M₀.nPc).1 grp tsF ∈ PosTree.forest [PosTree.node [] [] (nestSeedOf ctx R.holes M₀.ind
        M₀.lvls M₀.ds M₀.nPc).1 grp tsF] :=
    PosTree.mem_forest_iff.mpr ⟨_, List.mem_cons_self, PosTree.mem_nodes.mpr (Or.inl rfl)⟩
  refine ⟨_, Or.inr ⟨_, hD⟩, htr, _, .root List.mem_cons_self,
    ConLeche.posD_nodes hD _ hroot, ?_⟩
  rw [hMeq]
  refine ⟨hM₀o, hgrp, ?_⟩
  unfold ClassMatches
  exact ConLeche.targetClassMatch_self
    (fun a ha => ⟨(hsc a ha).1, by rw [hpl]; exact (hsc a ha).2⟩)
    (seed_readback h3 (fun i hi => by rw [← hctxE]; exact hparIdx i (hnP ▸ hi))
      hlenP hds)


/-! ## The node list -/

section Nodes

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **`nestedRecCtx_nodes` at the generated stage's context**: the node
list over the generated run's table `R.st.ctorNfs` (the seeds' walk). -/
theorem genRecCtx_nodes (hμ : μ.verifiedChecks = true) {F : Nat} {block : List ConstantInfo}
    {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState} {nested : Bool}
    (hctx : RecCtxBase V μ F envC envI pp cvTasR ctorsAsR mpC dR isRecR A kindsR nfsR posR)
    (R : GenRecRun μ F (mkFEnv envI) envI (mkFEnv envC) pp.toBlockShape nested posR cvTasR
      block ctorsAsR out)
    (mk : EnvModelM V μ envI) (hmkC : LfpCover mk pp.toBlockShape.memberNames)
    (hcoreK : BlockHoleCtxFacts mk.base2 dR pp.lps cvTasR pp.toBlockShape isRecR) :
    ∃ (fvsP : List Expr) (ns : List PosTree),
      R.ctx = pp.nestCtx fvsP envI.find? ∧
      (∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find?) t) ∧
      (∀ t ∈ ns, NodeOwned (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find?) t) ∧
      (∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns) ∧
      (∀ t ∈ ns, t.occ ≠ [] → ∃ p ∈ ns, t ∈ p.kids) ∧
      (∀ t ∈ ns, ∀ ψ, NodeSemAt mk.base2 ψ (pp.nestCtx fvsP envI.find?)
        (dR.holeCtx ψ).reverse t) ∧
      (∀ t ∈ ns, ConLeche.FrameRec (fueledOps .verified F) envI
        (pp.nestCtx fvsP envI.find?) R.st.ctorNfs.toList t.anc t.key.lvls t.key.ds t.grp) ∧
      MemberForests F envI pp cvTasR ctorsAsR nfsR fvsP R.st.ctorNfs.toList ns ∧
      (∃ par, ParentPtrs ns par) ∧
      ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
        ∃ t ∈ ns, NodeMajor F envC pp.toBlockShape (cvTasR.map (·.type))
          (pp.nestCtx fvsP envI.find?) (tgtMajor out c) t := by
  classical
  obtain ⟨hPos, henvC, -, -, hN, -, hcore, hctorsAs, hdR, -, -, -, -, hheads⟩ := hctx
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  -- the formers' and the constructors' types are closed
  have hT0 : ∀ cvTa0, cvTasR.head? = some cvTa0 → cvTa0.type.hasFvar = false := by
    intro cvTa0 h0
    have h0' : cvTasR[0]? = some cvTa0 := by
      rw [List.head?_eq_getElem?] at h0; exact h0
    obtain ⟨hf, -⟩ := hcore.1 0 cvTa0 h0'
    exact (mpC.base2.wf _ (List.mem_of_find?_eq_some hf)).1
  have hcl2 : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAsR[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
      (dR.ctorsM c)[j]? = some cA ∧
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true := by
    intro c cs hcs j cA hcA
    have hc : c < ctorsAsR.length := (List.getElem?_eq_some_iff.mp hcs).1
    rw [hctorsAs c hc] at hcs
    obtain rfl := Option.some.inj hcs
    have hck : c < dR.k := hN.2.2 ▸ hN.2.1 c j cA hcA
    obtain ⟨hf, -⟩ := hcore.2.2.2 c hck j cA hcA
    have hw := mpC.base2.wf _ (List.mem_of_find?_eq_some hf)
    exact ⟨hcA, hw.1, hw.2.2.2.1⟩
  have hcl : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAsR[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false :=
    fun c cs hcs j cA hcA => (hcl2 c cs hcs j cA hcA).2.1
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  have hkD : (blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).k
      = (blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).memberNames.length := by
    simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
      ConLeche.BlockShape.memberNames]
  have hAr : ∀ fvsP, ConLeche.NestArityOk (pp.nestCtx fvsP envI.find?) :=
    hcoreK.nestArity hN rfl rfl rfl hkD
  have hlpsC : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAsR[c]? = some cs →
      ∀ cA ∈ cs, cA.1.levelParams = pp.lps := by
    intro c cs hcs cA hcA
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    exact hcoreK.2.2 c j cA (hcl2 c cs hcs j cA hj).1
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, hctxR, hposT, hall⟩ :=
    genOutsideClass_reachedNode mk.base2.wf hPos R henvC hheads hT0 hcl hAr hlpsC
  obtain ⟨cvTa0', fvsP', rest', holes', h1', h2', h3', hder, hrootRec⟩ :=
    checkBlockPositivity_derivM mk.base2.wf hPos hT0 hcl hAr hlpsC
  rw [h1] at h1'
  obtain rfl := Option.some.inj h1'
  rw [h2] at h2'
  obtain ⟨rfl, rfl⟩ : fvsP = fvsP' ∧ rest = rest' := by simpa using h2'
  rw [h3] at h3'
  obtain rfl := Option.some.inj h3'
  have hrootOk : ConLeche.NestRootOk (pp.nestCtx fvsP envI.find?) :=
    ConLeche.nestRootOk_of_open (ctx := pp.nestCtx fvsP envI.find?) h2 (hAr fvsP)
  generalize hctxE : pp.nestCtx fvsP envI.find? = ctx at *
  have hcov : ContCover mk ctx := by
    rw [← hctxE]; exact contCover_of hmkC (fun _ => rfl)
  -- every chosen constructor's forest is read
  have hsem : ∀ (m : Nat) (cs : List (ConstantVal × Nat)) (j : Nat) (cA : ConstantVal × Nat)
      (crest : Expr) (ks : List ConLeche.NestFieldKind) (tyN : Expr) (ts : List PosTree),
      ctorsAsR[m]? = some cs → cs[j]? = some cA →
      instPisWith fvsP (nestAbstract ctx holes cA.1.type) = some crest →
      ConLeche.MemberCtorD (fueledOps .verified F) envI ctx cA.2 crest ks tyN ts →
      ∀ ψ, NodesSem mk.base2 ψ ctx
        ((blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).holeCtx ψ).reverse ts := by
    intro m cs j cA crest ks tyN ts hcs hj hcr hd ψ
    obtain ⟨hcj, hCf, hCb⟩ := hcl2 m cs hcs j cA hj
    obtain ⟨crest', -, -, hcr', -, -, ⟨ty, hty⟩, -⟩ := hder m cs hcs j cA hj
    rw [hcr] at hcr'
    obtain rfl := Option.some.inj hcr'
    subst hctxE
    exact memberCtor_nodesSem mk hN hcoreK rfl rfl rfl rfl
      (by simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
        ConLeche.BlockShape.memberNames]) h1 h2 h3 hcov hcj hCf hCb hcr hty hd ψ
  -- the chosen forests: one per outside class
  -- a forest's facts, member constructor's or seed's
  have hsrcD : ∀ ts : List PosTree,
      ((∃ (m : Nat) (cs : List (ConstantVal × Nat)) (j : Nat) (cA : ConstantVal × Nat)
        (crest : Expr) (ks : List ConLeche.NestFieldKind),
        ctorsAsR[m]? = some cs ∧ cs[j]? = some cA ∧
        instPisWith fvsP (nestAbstract ctx holes cA.1.type) = some crest ∧
        ConLeche.MemberCtorD (fueledOps .verified F) envI ctx cA.2 crest ks
          ((nfsR.getD m []).getD j default) ts) ∨
       ∃ key, ConLeche.PosD (fueledOps .verified F) envI ctx (.seed key) ts) →
      (∀ r ∈ ts, r.occ = []) ∧ (∀ u ∈ PosTree.forest ts, PosNodeOk (fueledOps .verified F) envI ctx u) ∧
      ∀ ψ, NodesSem mk.base2 ψ ctx
        ((blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).holeCtx ψ).reverse ts := by
    intro ts hts
    rcases hts with ⟨m, cs, j, cA, crest, ks, hcs, hj, hcr, hd⟩ | ⟨key, hd⟩
    · obtain ⟨hocc0, hfor⟩ := ConLeche.memberCtorD_nodes hd
      exact ⟨hocc0, hfor, hsem m cs j cA crest ks _ _ hcs hj hcr hd⟩
    · obtain ⟨hocc0, hfor⟩ := ConLeche.seedD_nodes hd
      refine ⟨hocc0, hfor, fun ψ => ?_⟩
      subst hctxE
      exact seed_nodesSem mk hN hcoreK rfl rfl rfl rfl
        (by simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
          ConLeche.BlockShape.memberNames]) h1 h2 h3 hcov hd ψ
  have hex : ∀ c, ∃ ts : List PosTree,
      (¬ (c < out.length ∧ (tgtMajor out c).member = none) → ts = []) ∧
      (c < out.length → (tgtMajor out c).member = none →
        ((∃ (m : Nat) (cs : List (ConstantVal × Nat)) (j : Nat) (cA : ConstantVal × Nat)
          (crest : Expr) (ks : List ConLeche.NestFieldKind),
          ctorsAsR[m]? = some cs ∧ cs[j]? = some cA ∧
          instPisWith fvsP (nestAbstract ctx holes cA.1.type) = some crest ∧
          ConLeche.MemberCtorD (fueledOps .verified F) envI ctx cA.2 crest ks
            ((nfsR.getD m []).getD j default) ts) ∨
         ∃ key, ConLeche.PosD (fueledOps .verified F) envI ctx (.seed key) ts) ∧
        ConLeche.TreeRec (fueledOps .verified F) envI ctx R.st.ctorNfs.toList ts ∧
        ∃ t, PosTree.Reached ts t ∧
          NodeMajor F envC pp.toBlockShape (cvTasR.map (·.type)) ctx (tgtMajor out c) t) := by
    intro c
    by_cases h : c < out.length ∧ (tgtMajor out c).member = none
    · obtain ⟨ts, hS, htr, t, hR, -, hNM⟩ := hall c h.1 h.2
      exact ⟨ts, fun h' => absurd h h', fun _ _ => ⟨hS, htr, t, hR, hNM⟩⟩
    · exact ⟨[], fun _ => rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  obtain ⟨tsOf, htsOf⟩ := Classical.axiomOfChoice hex
  -- one derivation per member constructor
  have hexM : ∀ q : Nat × Nat, ∃ ts : List PosTree,
      ∀ (cs : List (ConstantVal × Nat)) (cA : ConstantVal × Nat), ctorsAsR[q.1]? = some cs →
        cs[q.2]? = some cA → ∃ crest ks,
          instPisWith fvsP (nestAbstract ctx holes cA.1.type) = some crest ∧
          ConLeche.MemberCtorD (fueledOps .verified F) envI ctx cA.2 crest ks
            ((nfsR.getD q.1 []).getD q.2 default) ts ∧
          (∃ ty, ConLeche.inferTypeCore .verified envI F (ctx.hiAt 0) crest = .ok ty) ∧
          ConLeche.TreeRec (fueledOps .verified F) envI ctx R.st.ctorNfs.toList ts := by
    intro q
    by_cases h : ∃ cs cA, ctorsAsR[q.1]? = some cs ∧ cs[q.2]? = some cA
    · obtain ⟨cs, cA, hcs, hj⟩ := h
      obtain ⟨crest, ks, ts, hcr, hd, -, hty, -, -, -, htr⟩ := hder q.1 cs hcs q.2 cA hj
      refine ⟨ts, fun cs' cA' hcs' hj' => ?_⟩
      rw [hcs] at hcs'
      obtain rfl := Option.some.inj hcs'
      rw [hj] at hj'
      obtain rfl := Option.some.inj hj'
      exact ⟨crest, ks, hcr, hd, hty, htr.mono hposT⟩
    · exact ⟨[], fun cs cA hcs hj => absurd ⟨cs, cA, hcs, hj⟩ h⟩
  obtain ⟨tsM, htsM⟩ := Classical.axiomOfChoice hexM
  let rtC : List PosTree := (List.range out.length).flatMap fun c => tsOf c
  let rtM : List PosTree := (List.range ctorsAsR.length).flatMap fun m =>
    (List.range (ctorsAsR.getD m []).length).flatMap fun j => tsM (m, j)
  let L := PosTree.annF 0 0 (rtC ++ rtM)
  let ns : List PosTree := L.map (·.1)
  have hns : ns = PosTree.forest (rtC ++ rtM) := (PosTree.annF_spec _).1
  have hinR : ∀ ts : List PosTree, (∀ r ∈ ts, r ∈ rtC ++ rtM) → ∀ t ∈ PosTree.forest ts, t ∈ ns := by
    intro ts hts t ht
    rw [hns]
    obtain ⟨k, hk, htk⟩ := PosTree.mem_forest_iff.mp ht
    exact PosTree.mem_forest_iff.mpr ⟨k, hts k hk, htk⟩
  have hinC : ∀ c, c < out.length → ∀ t ∈ PosTree.forest (tsOf c), t ∈ ns :=
    fun c hc => hinR _ fun r hr =>
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, hr⟩)
  have hinM : ∀ (m : Nat) (cs : List (ConstantVal × Nat)), ctorsAsR[m]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
      ∀ t ∈ PosTree.forest (tsM (m, j)), t ∈ ns := by
    intro m cs hcs j cA hj
    have hm : m < ctorsAsR.length := (List.getElem?_eq_some_iff.mp hcs).1
    have hgd : ctorsAsR.getD m [] = cs := by rw [List.getD_eq_getElem?_getD, hcs]; rfl
    have hjl : j < cs.length := (List.getElem?_eq_some_iff.mp hj).1
    refine hinR _ fun r hr => List.mem_append_right _ (List.mem_flatMap.mpr ⟨m,
      List.mem_range.mpr hm, List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (by rw [hgd]; exact hjl),
        hr⟩⟩)
  -- per listed node: its derivation
  have hsrc : ∀ t ∈ ns, ∃ ts : List PosTree, t ∈ PosTree.forest ts ∧
      (∀ r ∈ ts, PosNodeOk (fueledOps .verified F) envI ctx r) ∧
      (∀ r ∈ ts, r.occ = []) ∧
      (∀ u ∈ PosTree.forest ts, PosNodeOk (fueledOps .verified F) envI ctx u) ∧
      (∀ ψ, NodesSem mk.base2 ψ ctx
        ((blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).holeCtx ψ).reverse ts) ∧
      ConLeche.TreeRec (fueledOps .verified F) envI ctx R.st.ctorNfs.toList ts ∧
      ∀ u ∈ PosTree.forest ts, u ∈ ns := by
    intro t ht
    rw [hns] at ht
    obtain ⟨r0, hr0, htr0⟩ := PosTree.mem_forest_iff.mp ht
    have htr0' : t ∈ PosTree.forest [r0] := PosTree.mem_forest_iff.mpr ⟨r0, List.mem_singleton_self _, htr0⟩
    rcases List.mem_append.mp hr0 with hr0 | hr0
    · obtain ⟨c, hc, hrc⟩ := List.mem_flatMap.mp hr0
      have htc : t ∈ PosTree.forest (tsOf c) := PosTree.mem_forest_iff.mpr ⟨r0, hrc, htr0⟩
      have hc' := List.mem_range.mp hc
      by_cases hM : (tgtMajor out c).member = none
      · obtain ⟨hS, htr, -⟩ := (htsOf c).2 hc' hM
        obtain ⟨hocc0, hfor, hS'⟩ := hsrcD _ hS
        exact ⟨tsOf c, htc, fun r hr => hfor r (PosTree.mem_forest_of_mem hr), hocc0, hfor,
          hS', htr, hinC c hc'⟩
      · rw [(htsOf c).1 fun h => hM h.2] at htc
        exact nomatch htc
    · obtain ⟨m, hm, htm⟩ := List.mem_flatMap.mp hr0
      obtain ⟨j, hj, hrj⟩ := List.mem_flatMap.mp htm
      have htj : t ∈ PosTree.forest (tsM (m, j)) := PosTree.mem_forest_iff.mpr ⟨r0, hrj, htr0⟩
      have hm' := List.mem_range.mp hm
      have hj' := List.mem_range.mp hj
      obtain ⟨cs, hcs⟩ : ∃ cs, ctorsAsR[m]? = some cs := ⟨_, List.getElem?_eq_getElem hm'⟩
      have hgd : ctorsAsR.getD m [] = cs := by rw [List.getD_eq_getElem?_getD, hcs]; rfl
      rw [hgd] at hj'
      obtain ⟨cA, hcA⟩ : ∃ cA, cs[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj'⟩
      obtain ⟨crest, ks, hcr, hd, -, htr⟩ := htsM (m, j) cs cA hcs hcA
      obtain ⟨hocc0, hfor⟩ := ConLeche.memberCtorD_nodes hd
      exact ⟨tsM (m, j), htj, fun r hr => hfor r (PosTree.mem_forest_of_mem hr), hocc0, hfor,
        hsem m cs j cA crest ks _ _ hcs hcA hcr hd, htr, hinM m cs hcs j cA hcA⟩
  -- every root occurs at no frame
  have hroot0 : ∀ r ∈ rtC ++ rtM, r.occ = [] := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨c, hc, hrc⟩ := List.mem_flatMap.mp hr
      have hc' := List.mem_range.mp hc
      by_cases hM : (tgtMajor out c).member = none
      · obtain ⟨hS, -, -⟩ := (htsOf c).2 hc' hM
        exact (hsrcD _ hS).1 r hrc
      · rw [(htsOf c).1 fun h => hM h.2] at hrc
        exact nomatch hrc
    · obtain ⟨m, hm, htm⟩ := List.mem_flatMap.mp hr
      obtain ⟨j, hj, hrj⟩ := List.mem_flatMap.mp htm
      have hm' := List.mem_range.mp hm
      have hj' := List.mem_range.mp hj
      obtain ⟨cs, hcs⟩ : ∃ cs, ctorsAsR[m]? = some cs := ⟨_, List.getElem?_eq_getElem hm'⟩
      have hgd : ctorsAsR.getD m [] = cs := by rw [List.getD_eq_getElem?_getD, hcs]; rfl
      rw [hgd] at hj'
      obtain ⟨cA, hcA⟩ : ∃ cA, cs[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj'⟩
      obtain ⟨crest, ks, hcr, hd, -, -⟩ := htsM (m, j) cs cA hcs hcA
      exact (ConLeche.memberCtorD_nodes hd).1 r hrj
  -- the parent pointers
  have hPP : ParentPtrs ns (fun b => (L.getD (b - 1) default).2) := by
    obtain ⟨-, hP, hK⟩ := PosTree.annF_spec (rtC ++ rtM)
    have hlen : ns.length = L.length := List.length_map _
    have hget : ∀ b, 0 < b → b ≤ ns.length → L[b - 1]? = some (ns.getD (b - 1) default,
        (L.getD (b - 1) default).2) := by
      intro b hb0 hbl
      have hl : b - 1 < L.length := by omega
      rw [List.getElem?_eq_getElem hl, List.getD_eq_getElem?_getD (l := L), List.getElem?_eq_getElem hl,
        Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl,
        Option.map_some, Option.getD_some]
    refine ⟨fun b hb0 hbl hocc => ?_, fun b hb0 hbl k hk => ?_⟩
    · rcases hP (b - 1) _ _ (hget b hb0 hbl) with ⟨h1, h2⟩ | ⟨h1, h2, e, he, h4⟩
      · exact absurd (hroot0 _ h2) hocc
      · dsimp only
        refine ⟨by omega, by omega, ?_⟩
        have hel := (List.getElem?_eq_some_iff.mp he).1
        have hge := hget ((L.getD (b - 1) default).2) (by omega) (by omega)
        rw [Nat.sub_zero] at he
        rw [he] at hge
        rw [← (Prod.mk.inj (Option.some.inj hge)).1]
        exact h4
    · obtain ⟨q', hq'⟩ := hK (b - 1) _ _ (hget b hb0 hbl) k hk
      have hq'l : q' < L.length := (List.getElem?_eq_some_iff.mp hq').1
      refine ⟨q' + 1, by omega, by omega, ?_, ?_⟩
      · rw [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_map, hq']; rfl
      · show (L.getD (q' + 1 - 1) default).2 = b
        rw [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, hq', Option.getD_some]
        simp only; omega
  refine ⟨fvsP, ns, by rw [hctxR, hctxE], fun t ht => ?_, fun t ht => ?_, fun t ht k hk => ?_, fun t ht hne => ?_,
    fun t ht ψ => ?_, fun t ht => ?_, ?_, ⟨_, hPP⟩, fun c hc hM => ?_⟩
  · obtain ⟨ts, htc, -, -, hfor, -⟩ := hsrc t ht
    rw [hctxE]; exact hfor t htc
  · obtain ⟨ts, htc, hroots, hocc0, -, -⟩ := hsrc t ht
    intro hk hkm
    obtain ⟨u, -, hu, -, hmemu⟩ :=
      (PosTree.Reached.of_forest htc).occ_owners hroots hocc0 hk hkm
    rw [hctxE]
    exact ⟨u, hu, hmemu⟩
  · obtain ⟨ts, htc, -, -, -, -, -, hin⟩ := hsrc t ht
    exact hin k (PosTree.mem_forest_kid htc hk)
  · obtain ⟨ts, htc, -, hocc0, -, -, -, hin⟩ := hsrc t ht
    rcases PosTree.forest_parent htc with hr | ⟨p, hp, htp⟩
    · exact absurd (hocc0 t hr) hne
    · exact ⟨p, hin p hp, htp⟩
  · obtain ⟨ts, htc, -, -, -, hS, -⟩ := hsrc t ht
    rw [hctxE]; exact hS ψ t htc
  · obtain ⟨ts, htc, -, -, -, -, htr, -⟩ := hsrc t ht
    rw [hctxE]; exact htr t htc
  · refine ⟨cvTa0, rest, holes, h1, h2, by rw [hctxE]; exact h3, fun m cs hcs j cA hj => ?_⟩
    obtain ⟨crest, ks, hcr, hd, hty, -⟩ := htsM (m, j) cs cA hcs hj
    have hent := ConLeche.rootEntry_mem hrootOk hrootRec hcs (List.mem_of_getElem? hj)
      (by rw [← hctxE]; exact hlpsC m cs hcs cA (List.mem_of_getElem? hj))
      (by rw [show ctx.params = fvsP by rw [← hctxE]; rfl]; exact hcr) hd
    refine ⟨crest, ks, tsM (m, j), by rw [hctxE]; exact hcr, by rw [hctxE]; exact hd,
      by rw [hctxE]; exact hty, hinM m cs hcs j cA hj, ?_⟩
    rw [hctxE]
    exact hposT _ hent
  · have hc' : c < out.length := by simpa [tgtRs] using hc
    obtain ⟨-, -, t, hR, hNM⟩ := (htsOf c).2 hc' hM
    refine ⟨t, hinC c hc' t (PosTree.mem_forest_of_reached hR), ?_⟩
    rw [hctxE]; exact hNM

end Nodes

end ConLeche.Model
