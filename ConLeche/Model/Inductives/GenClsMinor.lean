module

public import ConLeche.Model.Inductives.GenClsSem
public import ConLeche.Model.Inductives.GenRecRules
public import ConLeche.Verify.Inductives.GenDepth
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.ClassGenMinor
import ConLeche.Model.Inductives.GenRuleSyn
import ConLeche.Model.Inductives.GenRuleFree
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Verify.Subst
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Annot.Valid
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Model.Inductives.GenCallKit

public section

/-!
# The minor premise at the rule frame (lane GENREC-CLS)

`GenPreSem.minor`: the minor premise's typing at the rule frame.  The
minor premise of recursor `c`'s `j`-th constructor sits in the shared
prefix at its slot `mp = nP + s`, its type the generator's
`ClassGen.minorTy` built at `mp`.  That term does not depend on the depth
it is built at (`ClassGen.minorTy_depth`), so it IS the one built at the
rule prefix `rP`, whose pieces are the rule frame's: the constructor's
declared fields opened at `rP` (`tgtFieldFvs`), one inductive hypothesis
type per recursive field (the same term at every depth,
`ClassGen.ihTy_depth`, so the one the generated rule's `ih` is built
over), and the conclusion `motive_c e⃗ (C ds f⃗)` over the declared
result (`tgtCbody`).  Read at `rP` (a lift of its reading at `mp`) it is
the Π-tower of the rule frame's field domains, the `ih` domains
`genIhDomAV`, and the motive at `tgtEsAV`/`tgtMkAV`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassGenScoped RecShape NestState BinderMeta
  closeTelescope)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## A closed telescope, read -/

/-- **A closed telescope, read at its own depth**: a Π-tower whose binder
data are the pieces' readings (each at its own depth, the bit its binder
datum's) over the body's reading. -/
theorem denoteMeta_closeTelescope_read {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} :
    ∀ (nds : List (Expr × BinderMeta)) (d : Nat) (body Y : Expr) {A : AnnotTerm},
      (∀ p ∈ nds, p.1.looseBVarsBounded 0 = true) → body.looseBVarsBounded 0 = true →
      Expr.ErasedEq Y (closeTelescope nds d body) →
      denoteMeta acval env φ d Y = some A →
      ∃ (bs : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm), A = mkPisAV bs b ∧
        bs.length = nds.length ∧
        (∀ (k : Nat) (nd : Expr × BinderMeta), nds[k]? = some nd → ∃ a,
          bs[k]? = some (0, pwBit φ nd.2.pw, a) ∧ denoteMeta acval env φ (d + k) nd.1 = some a) ∧
        denoteMeta acval env φ (d + nds.length) body = some b
  | [], d, body, Y, A, _, _, hY, hA => by
    refine ⟨[], A, rfl, rfl, fun k nd h => by simp at h, ?_⟩
    rw [← hA, List.length_nil, Nat.add_zero, denoteMeta_erasedEq hY]
    rfl
  | (dom, bm) :: nds, d, body, Y, A, hcl, hb, hY, hA => by
    cases Y with
    | forallE a b bm' =>
      simp only [closeTelescope] at hY
      obtain ⟨hbm, ha, hbE⟩ := hY
      have hcl' : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true :=
        fun p hp => hcl p (List.mem_cons_of_mem _ hp)
      have hC := closeTelescope_bounded nds (d + 1) body hcl' hb
      have hE : Expr.ErasedEq (b.instantiate1 (.fvar d a)) (closeTelescope nds (d + 1) body) :=
        Expr.ErasedEq.trans (Expr.ErasedEq.instantiate1 hbE (v' := .fvar d dom) rfl)
          (erasedEq_abstract1_instantiate1 _ 0 hC)
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hA
      obtain ⟨bs, b0, rfl, hbl, hbs, hb0⟩ :=
        denoteMeta_closeTelescope_read nds (d + 1) body _ hcl' hb hE hba
      refine ⟨(0, pwBit φ bm'.pw, ta) :: bs, b0, rfl, by simp [hbl], fun k nd hk => ?_, ?_⟩
      · cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          refine ⟨ta, by rw [hbm]; rfl, ?_⟩
          rw [Nat.add_zero, ← denoteMeta_erasedEq ha]; exact hta
        | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          obtain ⟨a', ha', hr⟩ := hbs k nd hk
          exact ⟨a', by simpa using ha', by rw [show d + (k + 1) = d + 1 + k by omega]; exact hr⟩
      · rw [List.length_cons, show d + (nds.length + 1) = d + 1 + nds.length by omega]
        exact hb0
    | _ => simp [closeTelescope, Expr.ErasedEq] at hY

/-! ## The minor premise of `(c, j)`, syntactically -/

section Setup

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

set_option maxHeartbeats 4000000 in
/-- **The minor premise of recursor `c`'s `j`-th constructor, at the rule
prefix**: its slot `s`, the shared prefix's entry there (`T`, scoped at
the slot), and `T` spelled out as built AT THE RULE PREFIX — the rule
frame's declared fields `tgtFieldFvs`, one `ih` type per recursive field,
the conclusion over the declared result `tgtCbody`. -/
theorem genMinorSetup
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    {c j : Nat} (hc : c < (tgtRs out).length) (hj : j < blockRecNCt (tgtRs out) c) :
    ∃ (cls s : Nat) (x : ClassCtor) (T res : Expr) (ws : List Expr)
      (ihs : List (Expr × BinderMeta)),
      genClsOf R.rd c = cls ∧ genCtorAt R.g R.rd c j = x ∧ genMinorSlot R.g R.rd c j = s ∧
      x ∈ R.g.ctors.getD cls [] ∧ tgtMajor out c = R.g.cls.getD cls default ∧
      (∃ ihs0, R.g.slots[s]? = some (.minor cls x.cv.name ihs0)) ∧
      R.g.pre[R.g.nP + s]? = some (T, R.g.bm) ∧ ConLeche.ScB (R.g.nP + s) T ∧
      pp.toBlockShape.rulePrefixAt c = R.g.pre.length ∧
      ConLeche.openPisAtFvars x.nF x.tyD R.g.pre.length
        = some (tgtFieldFvs pp.toBlockShape out c j, res) ∧
      tgtCbody pp.toBlockShape out c j = res ∧ (tgtCtorOf out c j).2 = x.nF ∧
      (tgtCtorOf out c j).1 = x.cv ∧
      ConLeche.targetPiDomsWith (tgtFieldFvs pp.toBlockShape out c j) x.tyN = some ws ∧
      ihs.length = x.recs.length ∧
      (∀ (l i t tele : Nat), x.recs[l]? = some (i, t, tele) →
        (∃ ty, R.g.ihTy t tele (ws.getD i default)
          ((tgtFieldFvs pp.toBlockShape out c j).getD i default)
          (R.g.pre.length + x.nF + l) = some ty ∧ ihs[l]? = some (ty, R.g.bm)) ∧
        (∃ n, ConLeche.classRecOf R.rd.recCls R.cvGs t = some n) ∧
        (∃ xs idx, R.g.ihParts t tele (ws.getD i default) (R.g.pre.length + x.nF)
          = some (xs, idx)) ∧
        ∃ st, ConLeche.ClassRead.motiveSlot ⟨R.g.slots, []⟩ t = some st ∧ st < s) ∧
      (∃ sc, ConLeche.ClassRead.motiveSlot ⟨R.g.slots, []⟩ cls = some sc ∧ sc < s) ∧
      T = closeTelescope ((tgtFieldFvs pp.toBlockShape out c j).map R.g.binder ++ ihs)
        R.g.pre.length
        (Expr.mkAppN (R.g.motVar cls) (res.getAppArgs.drop (R.g.cls.getD cls default).nPc ++
          [Expr.mkAppN (.const x.cv.name (R.g.cls.getD cls default).lvls)
            ((R.g.cls.getD cls default).ds ++ tgtFieldFvs pp.toBlockShape out c j)])) := by
  have hr : (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := List.getElem?_eq_getElem hc
  obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
  obtain ⟨rc, cls2, x2, gen, -, hc2, -, -, hctors, hclsM, hx2, ⟨CR⟩, -, -, hxcv, hgen, -⟩ :=
    genRuleAt R hr hcA hrhs
  obtain ⟨cls, x, fvsR, resR, hcls, hrP, -, hMaj, hCt, -, hopR, hFF, hCB, -, hgx, hnF, hxmem,
    -, -, -, -, -⟩ := genFrameAt R hg hr hcA hrhs
  have hcc : cls2 = cls := Option.some.inj (hc2.symm.trans hcls)
  subst cls2
  have hgc : genClsOf R.rd c = cls := by simp [genClsOf, List.getD_eq_getElem?_getD, hcls]
  have hxx : x2 = x := by
    rw [← hgx, genCtorAt, hgc, List.getD_eq_getElem?_getD, hx2]; rfl
  subst x2
  obtain ⟨s, fvsG, resG, wsG, ihsG, hslot, hsl, hopG, hwsG, -, -, hihsG⟩ :=
    ConLeche.Model.classGenRule_spec hgen
  have hms : genMinorSlot R.g R.rd c j = s := by
    unfold genMinorSlot
    rw [hgc, hgx]
    unfold genSlotOf at hslot
    have hs2 : (List.range R.g.slots.length).find? (fun s => match R.g.slots.getD s default with
        | .minor c' C _ => c' == cls && C == x.cv.name
        | _ => false) = some s := hslot
    exact congrArg (fun o => Option.getD o 0) hs2
  -- the slot, and the constructor its prefix entry is built for
  have hsS : R.g.slots[s]? = some (.minor cls x.cv.name
      (match R.g.slots.getD s default with | .minor _ _ ihs0 => ihs0 | _ => [])) := by
    unfold genSlotOf at hslot
    have hpr := List.find?_some hslot
    rw [List.getElem?_eq_getElem hsl]
    have hgd : R.g.slots.getD s default = R.g.slots[s] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsl]; rfl
    rw [hgd] at hpr ⊢
    revert hpr
    cases R.g.slots[s] with
    | minor c' C' ihs0 =>
      intro hpr
      simp only [Bool.and_eq_true, beq_iff_eq] at hpr
      obtain ⟨rfl, rfl⟩ := hpr
      rfl
    | motive _ => intro hpr; exact nomatch hpr
  obtain ⟨x', T, hfx, hmin, hpreT⟩ := ConLeche.ClassGen.prefixBinders_minor hg hsS
  have hx'x : x' = x := by
    have hmem := List.mem_of_find?_eq_some hfx
    have hname : x'.cv.name = x.cv.name := by simpa using List.find?_some hfx
    obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨cA', hcA', ⟨CR'⟩⟩ := genClassCtorAt R hclsM (List.getElem?_eq_getElem hi')
    have hcA'r : ((tgtRs out)[c]'hc).2.2.2[i']? = some cA' := by
      rw [hctors]; exact hcA'
    have hf1 := hfind c _ hr i' cA' hcA'r
    have hf2 := hfind c _ hr j cA hcA
    have hn1 : cA'.1.name = cA.1.name := by
      have h1 := congrArg (fun y => y.cv.name) CR'.hx
      simp only at h1
      rw [← h1, hname, hxcv]
    rw [hn1, hf2] at hf1
    have hinj := Option.some.inj hf1
    injection hinj with h1 h2 h3
    have hcAeq : cA' = cA := Prod.ext h1.symm h3.symm
    subst hcAeq
    exact ConLeche.Model.classCtorRun_unique CR' CR
  subst x'
  have hxC : x.cv.name = x.cv.name := rfl
  have hTs : ConLeche.ScB (R.g.nP + s) T := ConLeche.ClassGen.minorTy_scoped hg hsS hxmem hxC hmin
  -- the same term at the rule prefix
  obtain ⟨⟨sc, hsc, hmc⟩, hmt⟩ := hg.order s cls x.cv.name _ hsS
  have hpl : R.g.pre.length = R.g.nP + R.g.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  have hminR : R.g.minorTy cls x R.g.pre.length = some T := by
    have hd := ConLeche.ClassGen.minorTy_depth (d₀ := R.g.nP + s)
      (ConLeche.Expr.fvarsBelow_mono (by omega) (hg.tyD cls x hxmem).1.fvarsBelow)
      (ConLeche.Expr.fvarsBelow_mono (by omega) (hg.tyN cls x hxmem).1.fvarsBelow)
      (fun e he => ConLeche.Expr.fvarsBelow_mono (by omega) (hg.ds cls e he).1.fvarsBelow)
      (fun t ht => by
        rcases ht with rfl | ⟨i, tele, hmem⟩
        · rw [hmc]; simp only [Option.getD_some]; omega
        · obtain ⟨hi, hk⟩ := ConLeche.ClassGen.recs_mem hmem
          obtain ⟨st, hst, hmt'⟩ := hmt x hxmem rfl t tele (ConLeche.ClassField.mem_of_getD hk)
          rw [hmt']; simp only [Option.getD_some]; omega)
      hTs.1.fvarsBelow hmin (R.g.pre.length - (R.g.nP + s))
    rwa [show R.g.nP + s + (R.g.pre.length - (R.g.nP + s)) = R.g.pre.length by omega] at hd
  obtain ⟨fvs', res', ws', ihs', hop', hws', hihl', hih', hTE⟩ := ConLeche.ClassGen.minorTy_unfold hminR
  rw [← hnF] at hopR
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop'.symm.trans hopR))
  refine ⟨cls, s, x, T, res', ws', ihs', hgc, hgx, hms, hxmem, hMaj, ⟨_, hsS⟩, hpreT, hTs, hrP,
    by rw [hFF]; exact hop', hCB, by rw [hCt]; exact hnF.symm, by rw [hCt]; exact hxcv.symm,
    by rw [hFF]; exact hws', hihl', fun l i t tele hq => ⟨?_, ?_, ?_, ?_⟩, ⟨sc, hmc, hsc⟩,
    by rw [hFF]; exact hTE⟩
  · rw [hFF]; exact hih' l i t tele hq
  · obtain ⟨xs, idx, n, ih, -, -, hrec, -⟩ := hihsG l (i, t, tele) hq
    exact ⟨n, hrec⟩
  · obtain ⟨xs, idx, n, ih, -, hparts, -, -⟩ := hihsG l (i, t, tele) hq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopG.symm.trans hop'))
    have hwq : wsG = ws' := Option.some.inj (hwsG.symm.trans hws')
    subst hwq
    exact ⟨xs, idx, hparts⟩
  · obtain ⟨hi, hk⟩ := ConLeche.ClassGen.recs_mem (List.mem_of_getElem? hq)
    obtain ⟨st, hst, hmt'⟩ := hmt x hxmem rfl t tele (ConLeche.ClassField.mem_of_getD hk)
    exact ⟨st, hmt', hst⟩

end Setup

/-- An inductive hypothesis type over scoped inputs is scoped. -/
theorem genIhTy_scb {g : ClassGen} {t tele st : Nat} {w f : Expr} {d : Nat} {ty : Expr}
    (hst : ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ t = some st) (hlt : g.nP + st < d)
    (hw : ConLeche.ScB d w) (hf : ConLeche.ScB d f)
    (h : g.ihTy t tele w f d = some ty) : ConLeche.ScB d ty := by
  unfold ClassGen.ihTy at h
  obtain ⟨⟨xs, idx⟩, hip, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  obtain ⟨hxl, hxs, hidx⟩ := ConLeche.ClassGen.ihParts_scoped hw (Nat.le_refl _) hip
  rw [ConLeche.ClassGen.motVar_eq hst]
  refine ConLeche.ScB.of_closeTelescope (fun k nd hk => ?_) ?_
  · rw [List.getElem?_map] at hk
    cases hxk : xs[k]? with
    | none => rw [hxk] at hk; exact nomatch hk
    | some xk =>
      rw [hxk] at hk
      obtain rfl := (Option.some.inj hk).symm
      obtain ⟨ty', hxe, hty'⟩ := hxs k xk hxk
      exact ConLeche.ScB.binder g hxe hty'
  · rw [List.length_map, hxl]
    refine ConLeche.ScB.mkAppN (ConLeche.ScB.fvar (by omega) (ConLeche.ScB.sort _ _)) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · exact hidx a ha
    · simp only [List.mem_singleton] at ha
      subst ha
      refine ConLeche.ScB.mkAppN (hf.mono (by omega)) fun b hb => ?_
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
      obtain ⟨ty', hxe, hty'⟩ := hxs k _ (List.getElem?_eq_getElem hk)
      rw [hxe]
      exact ConLeche.ScB.fvar (by omega) hty'

/-! ## An inductive hypothesis type, read -/

/-- **An inductive hypothesis's type, read at its depth `D`**: the
`genIhDomAV` of the `ih` data read off its pieces (the walked telescope's
domains with the family's bit, the leaf's indices and the applied field) —
the data `genIhdAV` reads. -/
theorem genIhTy_read {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {ψ : Name → Nat}
    {g : ClassGen} {t tele st : Nat} {w f : Expr} {D : Nat} {xs idx : List Expr} {ty0 : Expr}
    {a : AnnotTerm} (hst : ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ t = some st)
    (hw : ConLeche.ScB D w) (hfb : f.looseBVarsBounded 0 = true)
    (hip : g.ihParts t tele w D = some (xs, idx))
    (hty : g.ihTy t tele w f D = some ty0) (r : Nat)
    (hread : denoteMeta acval env ψ D ty0 = some a) :
    a = genIhDomAV D (g.nP + st)
      (r, (readOpenedDoms acval env ψ D xs).map fun b => (pwBit ψ g.bm.pw, b),
        idx.map fun e => (denoteMeta acval env ψ (D + xs.length) e).getD default,
        (denoteMeta acval env ψ (D + xs.length) (Expr.mkAppN f xs)).getD default) := by
  unfold ClassGen.ihTy at hty
  obtain ⟨⟨xs', idx'⟩, hip', hty⟩ := Option.bind_eq_some_iff.mp hty
  rw [hip] at hip'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hip')
  simp only [Option.pure_def, Option.some.injEq] at hty
  subst hty
  obtain ⟨hxl, hxs, hidx⟩ := ConLeche.ClassGen.ihParts_scoped hw (Nat.le_refl _) hip
  rw [ConLeche.ClassGen.motVar_eq hst] at hread
  have hcl : ∀ p ∈ xs.map g.binder, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    obtain ⟨ty, hxe, hty'⟩ := hxs k _ (List.getElem?_eq_getElem hk)
    rw [hxe]; exact hty'.2
  have hbb : (Expr.mkAppN (.fvar (g.nP + st) (.sort .zero))
      (idx ++ [Expr.mkAppN f xs])).looseBVarsBounded 0 = true := by
    refine ConLeche.looseBVarsBounded_mkAppN (by simp [Expr.looseBVarsBounded]) fun e he => ?_
    rcases List.mem_append.mp he with he | he
    · exact (hidx e he).2
    · simp only [List.mem_singleton] at he
      subst he
      refine ConLeche.looseBVarsBounded_mkAppN hfb fun y hy => ?_
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
      obtain ⟨ty, hxe, -⟩ := hxs k _ (List.getElem?_eq_getElem hk)
      rw [hxe]; simp [Expr.looseBVarsBounded]
  obtain ⟨bs, b, rfl, hbl, hbs, hb⟩ :=
    denoteMeta_closeTelescope_read _ D _ _ hcl hbb (Expr.ErasedEq.rfl _) hread
  rw [List.length_map] at hb hbl
  obtain ⟨fa, vs, hfa, hvs, rfl⟩ := denoteMeta_mkAppN_inv hb
  rw [denoteMeta_fvar] at hfa
  obtain rfl := Option.some.inj hfa
  have hvsE := denoteMetaSpine_eq_map hvs
  unfold genIhDomAV
  simp only [List.length_map, readOpenedDoms_length_eq]
  congr 1
  · refine List.ext_getElem (by simp [hbl]) fun k h1 h2 => ?_
    have hkx : k < xs.length := by rw [← hbl]; exact h1
    obtain ⟨a', ha', hr⟩ := hbs k (g.binder xs[k]) (by simp [hkx])
    rw [List.getElem?_eq_getElem h1] at ha'
    rw [Option.some.inj ha']
    simp only [List.getElem_map, readOpenedDoms_getElem D xs k hkx]
    simp only [ClassGen.binder] at hr
    rw [hr]
    rfl
  · rw [hvsE, List.map_append, List.map_cons, List.map_nil]

/-- **The generated `ih` data at a recursive field**, spelled out. -/
theorem genIhdAV_getElem {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {g : ClassGen}
    {rd : ClassRead} {bit : Nat} {ψ : Name → Nat} {c j l i t tele : Nat} {fvs : List Expr}
    {res : Expr} {ws xs idx : List Expr}
    (hq : (genCtorAt g rd c j).recs[l]? = some (i, t, tele))
    (hop : ConLeche.openPisAtFvars (genCtorAt g rd c j).nF (genCtorAt g rd c j).tyD g.pre.length
      = some (fvs, res))
    (hws : ConLeche.targetPiDomsWith fvs (genCtorAt g rd c j).tyN = some ws)
    (hip : g.ihParts t tele (ws.getD i default) (g.pre.length + (genCtorAt g rd c j).nF)
      = some (xs, idx)) :
    (genIhdAV acval env g rd bit ψ c j)[l]? = some (genRecIdx rd t,
      (readOpenedDoms acval env ψ (g.pre.length + (genCtorAt g rd c j).nF) xs).map
        fun b => (bit, b),
      idx.map fun e => (denoteMeta acval env ψ
        (g.pre.length + (genCtorAt g rd c j).nF + xs.length) e).getD default,
      (denoteMeta acval env ψ (g.pre.length + (genCtorAt g rd c j).nF + xs.length)
        (Expr.mkAppN (fvs.getD i default) xs)).getD default) := by
  unfold genIhdAV
  simp only [List.getElem?_map, hq, hop, hws, Option.map_some, Option.getD_some, hip]

/-- **The `l`-th inductive hypothesis type of the minor premise, read at
its position `rP + nF + l`**: the generated `ih` binder type of the
`l`-th `ih` datum, lifted past the `l` earlier `ih` binders. -/
theorem genIhEntry_read {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    (m : EnvModel V env) (hac : m.acval = acval) {ψ : Name → Nat}
    {g : ClassGen} {rd : ClassRead} {c j l i t tele st : Nat} {fvs : List Expr} {res : Expr}
    {ws : List Expr} {ty : Expr} {a : AnnotTerm}
    (hq : (genCtorAt g rd c j).recs[l]? = some (i, t, tele))
    (hop : ConLeche.openPisAtFvars (genCtorAt g rd c j).nF (genCtorAt g rd c j).tyD g.pre.length
      = some (fvs, res))
    (hfvs : ∀ (k : Nat) (y : Expr), fvs[k]? = some y →
      ∃ ty, y = .fvar (g.pre.length + k) ty ∧ ConLeche.ScB (g.pre.length + k) ty)
    (hws : ConLeche.targetPiDomsWith fvs (genCtorAt g rd c j).tyN = some ws)
    (hwsS : ConLeche.ScB (g.pre.length + (genCtorAt g rd c j).nF) (ws.getD i default))
    (hparts : ∃ xs idx, g.ihParts t tele (ws.getD i default)
      (g.pre.length + (genCtorAt g rd c j).nF) = some (xs, idx))
    (hst : ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ t = some st)
    (hstl : g.nP + st < g.pre.length)
    (hty : g.ihTy t tele (ws.getD i default) (fvs.getD i default)
      (g.pre.length + (genCtorAt g rd c j).nF + l) = some ty)
    (hread : denoteMeta acval env ψ (g.pre.length + (genCtorAt g rd c j).nF + l) ty = some a)
    {bit : Nat} (hbit : bit = pwBit ψ g.bm.pw) :
    ∃ q, (genIhdAV acval env g rd bit ψ c j)[l]? = some q ∧ q.1 = genRecIdx rd t ∧
      a = (genIhDomAV (g.pre.length + (genCtorAt g rd c j).nF) (g.nP + st) q).liftN l 0 := by
  subst hac
  obtain ⟨xs, idx, hip⟩ := hparts
  generalize hD : g.pre.length + (genCtorAt g rd c j).nF = D at hwsS hip hty hread
  have hiF : i < (genCtorAt g rd c j).nF :=
    (ConLeche.ClassGen.recs_mem (List.mem_of_getElem? hq)).1
  have hi : i < fvs.length := by
    rw [ConLeche.Verify.openPisAtFvars_length _ hop]; exact hiF
  have hfS : ConLeche.ScB D (fvs.getD i default) := by
    obtain ⟨ty', hxe, hty'⟩ := hfvs i _ (List.getElem?_eq_getElem hi)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hxe]
    exact ConLeche.ScB.fvar (by omega) hty'
  -- the type at `D`
  have hty0 : g.ihTy t tele (ws.getD i default) (fvs.getD i default) D
      = some (closeTelescope (xs.map g.binder) D
          (Expr.mkAppN (g.motVar t) (idx ++ [Expr.mkAppN (fvs.getD i default) xs]))) := by
    unfold ClassGen.ihTy; rw [hip]; rfl
  have hS0 := genIhTy_scb hst (by omega) hwsS hfS hty0
  have hd := ConLeche.ClassGen.ihTy_depth hwsS.1.fvarsBelow hfS.1.fvarsBelow
    (by rw [hst]; simp only [Option.getD_some]; omega) hS0.1.fvarsBelow hty0 l
  rw [hd] at hty
  obtain rfl := Option.some.inj hty
  have hlift := denoteMeta_lift (env := env) (φ := ψ) m.acval_closed hS0.1 (D + l)
    (Nat.le_add_right _ _)
  rw [hread, show D + l - D = l by omega] at hlift
  obtain ⟨a0, ha0, rfl⟩ : ∃ a0, denoteMeta m.acval env ψ D (closeTelescope (xs.map g.binder) D
      (Expr.mkAppN (g.motVar t) (idx ++ [Expr.mkAppN (fvs.getD i default) xs]))) = some a0 ∧
      a = a0.liftN l 0 := by
    cases h0 : denoteMeta m.acval env ψ D (closeTelescope (xs.map g.binder) D
      (Expr.mkAppN (g.motVar t) (idx ++ [Expr.mkAppN (fvs.getD i default) xs]))) with
    | none => rw [h0] at hlift; exact nomatch hlift
    | some a0 => rw [h0] at hlift; exact ⟨a0, rfl, Option.some.inj hlift⟩
  have hE := genIhTy_read (acval := m.acval) (env := env) (ψ := ψ) hst hwsS hfS.2 hip hty0
    (genRecIdx rd t) ha0
  subst hD hbit
  exact ⟨_, genIhdAV_getElem hq hop hws hip, rfl, by rw [hE]⟩

/-! ## `GenPreSem.minor` -/

section Minor

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

set_option maxHeartbeats 8000000 in
/-- **`GenPreSem.minor` from the run**: the minor premise of recursor
`c`'s `j`-th constructor, at a prefix spine, fields fitting the rule
frame's declared field domains and `ih` values of the generated `ih`
binder types, lands in the motive at the declared result's indices and
the constructor applied.  The prefix's entry is the minor premise's type
built at the slot, which IS the one built at the rule prefix
(`genMinorSetup`); read at the rule prefix it is the Π-tower of exactly
the rule frame's pieces. -/
theorem genCls_minor (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ xs,
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs →
    ∀ fs, SpineFit (consList xs ρ) (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) fs →
    ∀ hs : List V, hs.length = (genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j).length →
    (∀ (l : Nat) (q : IhDatum) (hv : V),
      (genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j)[l]? = some q → hs[l]? = some hv →
      hv ∈ˢ interp V (consList (xs ++ fs) ρ)
        (genIhDomAV ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
          (classMotPos R.g (genClsOf R.rd q.1)) q)) →
    (fs ++ hs).foldl SetTheory.app (xs.getD (R.g.nP + genMinorSlot R.g R.rd c j) pt)
      ∈ˢ ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ))
          ++ [interp V (consList (xs ++ fs) ρ)
            (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j)]).foldl SetTheory.app
          (xs.getD (classMotPos R.g (genClsOf R.rd c)) pt) := by
  intro c hc j hj xs hxs fs hfs hs hhl hhs
  obtain ⟨cls, s, x, T, res, ws, ihs, hgc, hgx, hms, hxmem, hMaj, ⟨ihs0, hsS⟩, hpreT, hTs, hrP,
    hopR, hCB, hnF, hcv, hwsR, hihl, hih, ⟨sc, hmc, hscl⟩, hTE⟩ := genMinorSetup R hg h hfind hc hj
  rw [hms, hgc]
  have hr : (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := List.getElem?_eq_getElem hc
  have hpl : R.g.pre.length = R.g.nP + R.g.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  have hsl : s < R.g.slots.length := (List.getElem?_eq_some_iff.mp hsS).1
  have hmp : R.g.nP + s < R.g.pre.length := by omega
  -- the stored type's entry at the minor's slot
  obtain ⟨cls', ty', ifs', body', -, -, -, -, -, -, -, -, -, -, fvs0, o0, hop0, hE⟩ :=
    genRun_binders hμ R hg h mpC ψ hc
  obtain ⟨fvs1, concl1, hop1, -, hTyE, hlenRds, -, hdomsR, -, hwdTy⟩ :=
    recStage_tyPis (V := V) hμ mpC h hr ψ
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop1.symm.trans hop0))
  have hle := blockRecHrPle (p := pp) h hc
  have hlenF : fvs1.length = pp.toBlockShape.majorIdxAt c + 1 :=
    ConLeche.Verify.openPisAtFvars_length _ hop1
  obtain ⟨y, hy⟩ : ∃ y, fvs1[R.g.nP + s]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hyE := hE _ y T hy (by
    rw [List.append_assoc, List.getElem?_append_left (by omega), hpreT]; rfl)
  obtain ⟨pd, hpd, -, hrd⟩ := hdomsR _ y hy
  rw [denoteMeta_erasedEq hyE] at hrd
  -- the prefix's entry: the minor's value, valid there
  have hlenPd := blockRulePdomsAV_length (V := V) hμ mpC h hr ψ
  have hPdget : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).getD
      (R.g.nP + s) default = pd.2.2 := by
    rw [blockRulePdomsAV, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
      ite_eq_left (by omega), hpd]; rfl
  have hmem := FixKI.spineFit_getD_mem' hxs (l := R.g.nP + s) (by rw [hlenPd]; omega)
  rw [hPdget] at hmem
  have hv := (hwdTy ρ).2
  rw [hTyE, ← List.take_append_drop (pp.toBlockShape.rulePrefixAt c)
    (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c), mkPisAV_append'] at hv
  have hvA := annotValid_piDom_at hv hxs (R.g.nP + s) (by
    rw [List.length_take, hlenRds]; omega)
  rw [show ((List.take (pp.toBlockShape.rulePrefixAt c)
      (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)).map (·.2.2)).getD
      (R.g.nP + s) default = pd.2.2 from hPdget] at hvA
  -- read at the rule prefix
  have hlift := denoteMeta_lift (env := envC) (φ := ψ) mpC.base2.acval_closed hTs.1 R.g.pre.length
    (by omega)
  rw [hrd, Option.map_some] at hlift
  -- the pieces are bounded
  obtain ⟨hfl, hfvsS, hresS⟩ := ConLeche.ScB.openPis hopR
    ((hg.tyD cls x hxmem).mono (by omega))
  have hwsS : ∀ i, i < x.nF → ConLeche.ScB (R.g.pre.length + x.nF) (ws.getD i default) :=
    fun i hi => ConLeche.ScB.targetPiDomsWith_getD hwsR
      ((hg.tyN cls x hxmem).mono (by omega)) (fun a ha => by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
        obtain ⟨ty, hxe, hty⟩ := hfvsS k _ (List.getElem?_eq_getElem hk)
        rw [hxe]; exact ConLeche.ScB.fvar (by omega) hty) (by omega)
  have hihS : ∀ l ty bm', ihs[l]? = some (ty, bm') →
      ConLeche.ScB (R.g.pre.length + x.nF + l) ty := by
    intro l ty bm' hl
    have hl' : l < x.recs.length := by
      rw [← hihl]; exact (List.getElem?_eq_some_iff.mp hl).1
    obtain ⟨⟨i, t, tele⟩, hq⟩ : ∃ q, x.recs[l]? = some q :=
      ⟨_, List.getElem?_eq_getElem hl'⟩
    obtain ⟨⟨ty', hty', hl2⟩, -, -, st, hst, hstl⟩ := hih l i t tele hq
    rw [hl] at hl2
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl2)
    obtain ⟨hiF, -⟩ := ConLeche.ClassGen.recs_mem (List.mem_of_getElem? hq)
    have hi : i < (tgtFieldFvs pp.toBlockShape out c j).length := by rw [hfl]; exact hiF
    obtain ⟨tyf, hxe, htyf⟩ := hfvsS i _ (List.getElem?_eq_getElem hi)
    refine genIhTy_scb hst (by omega) ((hwsS i hiF).mono (by omega)) ?_ hty'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hxe]
    exact ConLeche.ScB.fvar (by omega) (htyf.mono (by omega))
  have hcl : ∀ p ∈ (tgtFieldFvs pp.toBlockShape out c j).map R.g.binder ++ ihs,
      p.1.looseBVarsBounded 0 = true := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hp
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy'
      obtain ⟨ty, hxe, hty⟩ := hfvsS k _ (List.getElem?_eq_getElem hk)
      rw [hxe]; exact hty.2
    · obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hp
      exact (hihS l _ _ (List.getElem?_eq_getElem hl)).2
  have hbbS : ConLeche.ScB (R.g.pre.length + x.nF)
      (Expr.mkAppN (R.g.motVar cls) (res.getAppArgs.drop (R.g.cls.getD cls default).nPc ++
        [Expr.mkAppN (.const x.cv.name (R.g.cls.getD cls default).lvls)
          ((R.g.cls.getD cls default).ds ++ tgtFieldFvs pp.toBlockShape out c j)])) := by
    rw [ConLeche.ClassGen.motVar_eq hmc]
    refine ConLeche.ScB.mkAppN (ConLeche.ScB.fvar (by omega) (ConLeche.ScB.sort _ _))
      fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · exact ConLeche.ScB.getAppArgs hresS a (List.mem_of_mem_drop ha)
    · simp only [List.mem_singleton] at ha
      subst ha
      refine ConLeche.ScB.mkAppN (ConLeche.ScB.const _ _ _) fun b hb => ?_
      rcases List.mem_append.mp hb with hb | hb
      · exact (hg.ds cls b hb).mono (by omega)
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
        obtain ⟨ty, hxe, hty⟩ := hfvsS k _ (List.getElem?_eq_getElem hk)
        rw [hxe]; exact ConLeche.ScB.fvar (by omega) (hty.mono (by omega))
  obtain ⟨bs, b, hBE, hbl, hbs, hb⟩ :=
    denoteMeta_closeTelescope_read _ _ _ T hcl hbbS.2 (by rw [← hTE]; exact Expr.ErasedEq.rfl _)
      hlift
  -- the frames
  have hlenPd' : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      = R.g.pre.length := hlenPd.trans hrP
  have hxl : xs.length = R.g.pre.length := hxs.length_eq.trans hlenPd'
  have hsh : shiftE (R.g.pre.length - (R.g.nP + s)) 0 (consList xs ρ)
      = consList (xs.take (R.g.nP + s)) ρ := by
    have := shiftE_consList (V := V) (ys := ([] : List V)) (zs := xs) (ρ := ρ)
      (n := R.g.pre.length - (R.g.nP + s)) (k := 0) rfl (by omega)
    rw [show xs.length - (R.g.pre.length - (R.g.nP + s)) = R.g.nP + s by omega] at this
    exact this
  have hmemB : xs.getD (R.g.nP + s) pt ∈ˢ interp V (consList xs ρ) (mkPisAV bs b) := by
    rw [← hBE, interp_liftN, hsh]; exact hmem
  have hvB : AnnotValid V (consList xs ρ) (mkPisAV bs b) := by
    rw [← hBE, AnnotValid_liftN, hsh]; exact hvA
  -- the rule frame's field domains are the fields' binder data
  have hRP : tgtRP pp.toBlockShape c = R.g.pre.length := hrP
  have hfdL : (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length = x.nF := by
    rw [tgtFdomsAV, readOpenedDoms_length_eq, hfl]
  have hfsl : fs.length = x.nF := hfs.length_eq.trans hfdL
  have hihdL : (genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j).length
      = x.recs.length := by simp [genIhdAV, hgx]
  have hhsl : hs.length = x.recs.length := hhl.trans hihdL
  have hbsl : bs.length = x.nF + x.recs.length := by rw [hbl]; simp [hfl, hihl]
  have hfit : SpineFit (consList xs ρ) (bs.map (·.2.2)) (fs ++ hs) := by
    refine spineFit_of_getD (by simp [hfsl, hhsl, hbsl]) fun r hr => ?_
    rw [List.length_map] at hr
    rcases Nat.lt_or_ge r x.nF with hrF | hrF
    · -- a field
      have hrf : r < (tgtFieldFvs pp.toBlockShape out c j).length := by rw [hfl]; exact hrF
      obtain ⟨a, ha, hra⟩ := hbs r (R.g.binder (tgtFieldFvs pp.toBlockShape out c j)[r])
        (by rw [List.getElem?_append_left (by simpa using hrf)]; simp [hrf])
      have hgetB : (bs.map (·.2.2)).getD r default = a := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, ha]; rfl
      have hgetF : (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).getD r default
          = a := by
        rw [List.getD_eq_getElem?_getD, tgtFdomsAV, hRP, List.getElem?_eq_getElem (by simpa using hrf),
          Option.getD_some, readOpenedDoms_getElem _ _ r hrf]
        simp only [ClassGen.binder] at hra
        rw [hra]; rfl
      have hm := FixKI.spineFit_getD_mem' hfs (l := r) (by rw [hfdL]; exact hrF)
      rw [hgetF] at hm
      rw [hgetB, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD, take_append_of_le (by omega)]
      exact hm
    · -- an inductive hypothesis
      obtain ⟨l, rfl⟩ : ∃ l, r = x.nF + l := ⟨r - x.nF, by omega⟩
      have hl : l < x.recs.length := by omega
      obtain ⟨⟨i, t, tele⟩, hq⟩ : ∃ q, x.recs[l]? = some q := ⟨_, List.getElem?_eq_getElem hl⟩
      obtain ⟨⟨ty, hty, hihq⟩, ⟨n, hrec⟩, hparts, st, hst, hstl⟩ := hih l i t tele hq
      obtain ⟨a, ha, hra⟩ := hbs (x.nF + l) (ty, R.g.bm)
        (by rw [List.getElem?_append_right (by simp [hfl]), List.length_map, hfl,
          Nat.add_sub_cancel_left]; exact hihq)
      have hgetB : (bs.map (·.2.2)).getD (x.nF + l) default = a := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, ha]; rfl
      rw [show R.g.pre.length + (x.nF + l) = R.g.pre.length + x.nF + l by omega] at hra
      have hq' : (genCtorAt R.g R.rd c j).recs[l]? = some (i, t, tele) := by rw [hgx]; exact hq
      have hop' : ConLeche.openPisAtFvars (genCtorAt R.g R.rd c j).nF (genCtorAt R.g R.rd c j).tyD
          R.g.pre.length = some (tgtFieldFvs pp.toBlockShape out c j, res) := by rw [hgx]; exact hopR
      obtain ⟨hiF, -⟩ := ConLeche.ClassGen.recs_mem (List.mem_of_getElem? hq)
      obtain ⟨qd, hqd, hq1, hae⟩ := genIhEntry_read (acval := mpC.base2.acval) mpC.base2 rfl
        (ψ := ψ) hq' hop' (by simpa [hgx] using hfvsS)
        (by rw [hgx]; exact hwsR) (by rw [hgx]; exact hwsS i hiF)
        (by rw [hgx]; exact hparts) hst (by omega) (by rw [hgx]; exact hty)
        (by rw [hgx]; exact hra) (bit := genBit pp ψ) rfl
      obtain ⟨hv, hhv⟩ : ∃ hv, hs[l]? = some hv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hmI := hhs l qd hv hqd hhv
      have hcal := (genRecIdx_spec (rd := R.rd) (cvGs := R.cvGs) hrec (by
        have := genRun_recCls_length R
        have h2 := (genRun_lengths R).2
        omega)).1
      have hmt : classMotPos R.g (genClsOf R.rd qd.1) = R.g.nP + st := by
        rw [hq1, genClsOf, List.getD_eq_getElem?_getD, hcal, Option.getD_some, classMotPos, hst]
        rfl
      rw [hmt, hlenPd', hfdL, ← hgx] at hmI
      rw [hgetB, hae, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hfsl,
        Nat.add_sub_cancel_left, hhv, Option.getD_some, List.take_append, List.take_of_length_le
        (by omega), hfsl, Nat.add_sub_cancel_left, consList_append, interp_liftN,
        shiftE_zero_consList (by simp; omega), ← consList_append]
      exact hmI
  have happ := foldl_app_mem_mkPisAV hvB hfit hmemB
  -- the conclusion: the motive at the declared result's indices and the constructor
  have hbl' : ((tgtFieldFvs pp.toBlockShape out c j).map R.g.binder ++ ihs).length
      = x.nF + x.recs.length := by simp [hfl, hihl]
  rw [hbl'] at hb
  have hlift2 := denoteMeta_lift (env := envC) (φ := ψ) mpC.base2.acval_closed hbbS.1
    (R.g.pre.length + (x.nF + x.recs.length)) (by omega)
  rw [hb, show R.g.pre.length + (x.nF + x.recs.length) - (R.g.pre.length + x.nF)
    = x.recs.length by omega] at hlift2
  obtain ⟨b0, hb0, rfl⟩ : ∃ b0, denoteMeta mpC.base2.acval envC ψ (R.g.pre.length + x.nF)
      (Expr.mkAppN (R.g.motVar cls) (res.getAppArgs.drop (R.g.cls.getD cls default).nPc ++
        [Expr.mkAppN (.const x.cv.name (R.g.cls.getD cls default).lvls)
          ((R.g.cls.getD cls default).ds ++ tgtFieldFvs pp.toBlockShape out c j)])) = some b0 ∧
      b = b0.liftN x.recs.length 0 := by
    cases h0 : denoteMeta mpC.base2.acval envC ψ (R.g.pre.length + x.nF)
      (Expr.mkAppN (R.g.motVar cls) (res.getAppArgs.drop (R.g.cls.getD cls default).nPc ++
        [Expr.mkAppN (.const x.cv.name (R.g.cls.getD cls default).lvls)
          ((R.g.cls.getD cls default).ds ++ tgtFieldFvs pp.toBlockShape out c j)])) with
    | none => rw [h0] at hlift2; exact nomatch hlift2
    | some b0 => rw [h0] at hlift2; exact ⟨b0, rfl, Option.some.inj hlift2⟩
  rw [ConLeche.ClassGen.motVar_eq hmc] at hb0
  obtain ⟨fa, vs, hfa, hvs, rfl⟩ := denoteMeta_mkAppN_inv hb0
  rw [denoteMeta_fvar] at hfa
  obtain rfl := Option.some.inj hfa
  have hvsE := denoteMetaSpine_eq_map hvs
  have hB : tgtB pp.toBlockShape out c j = R.g.pre.length + x.nF := by
    rw [tgtB, hRP, hnF]
  have hEs : tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j
      = (res.getAppArgs.drop (R.g.cls.getD cls default).nPc).map
          fun e => (denoteMeta mpC.base2.acval envC ψ (R.g.pre.length + x.nF) e).getD default := by
    rw [tgtEsAV, hCB, hMaj, hB]
  have hMk : tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j
      = (denoteMeta mpC.base2.acval envC ψ (R.g.pre.length + x.nF)
          (Expr.mkAppN (.const x.cv.name (R.g.cls.getD cls default).lvls)
            ((R.g.cls.getD cls default).ds ++ tgtFieldFvs pp.toBlockShape out c j))).getD default := by
    rw [tgtMkAV, hB, hcv, hMaj]
  rw [interp_liftN, consList_append, shiftE_zero_consList hhsl, interp_mkAppN,
    ← List.foldl_map (f := interp V (consList fs (consList xs ρ))) (g := SetTheory.app)] at happ
  have hhd : interp V (consList fs (consList xs ρ))
      (.bvar (R.g.pre.length + x.nF - 1 - (R.g.nP + sc))) = xs.getD (classMotPos R.g cls) pt := by
    show consList fs (consList xs ρ) _ = _
    rw [← consList_append, show R.g.pre.length + x.nF - 1 - (R.g.nP + sc)
      = fs.length + xs.length - 1 - (R.g.nP + sc) by omega,
      consList_prefix_getD (by omega)]
    simp [classMotPos, hmc]
  rw [hhd, hvsE] at happ
  rw [hEs, hMk, consList_append]
  simpa only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def]
    using happ

end Minor

end ConLeche.Model
