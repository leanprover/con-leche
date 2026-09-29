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

theorem list_find?_congr {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      list_find?_congr l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

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
    hopR, hCB, hnF, hcv, hwsR, hihl, hih, hTE⟩ := genMinorSetup R hg h hfind hc hj
  rw [hms, hgc]
  have hr : (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := List.getElem?_eq_getElem hc
  have hpl : R.g.pre.length = R.g.nP + R.g.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  have hsl : s < R.g.slots.length := (List.getElem?_eq_some_iff.mp hsS).1
  generalize hrPd : R.g.pre.length = rP at hopR hTE hrP hpl hih
  generalize hmpd : R.g.nP + s = mp at hpreT hTs
  have hmp : mp < rP := by omega
  -- the stored type's entry at the minor's slot
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, fvs0, o0, hop0, hE⟩ :=
    genRun_binders hμ R hg h mpC ψ hc
  obtain ⟨fvs1, concl1, hop1, hta, hTyE, hlenRds, -, hdomsR, -, hwdTy⟩ :=
    recStage_tyPis (V := V) hμ mpC h hr ψ
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop1.symm.trans hop0))
  sorry

end Minor

end ConLeche.Model
