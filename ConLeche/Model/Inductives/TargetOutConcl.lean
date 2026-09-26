module

public import ConLeche.Model.Inductives.TargetOutRow
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.ContInstRule
import ConLeche.Model.Inductives.ContSubst
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Subst
import ConLeche.Verify.InstLevels

public section

/-!
# An outside rule's conclusion, syntactically and read

The target check reads an outside rule's index expressions off the
instantiated constructor's conclusion, `cbody.getAppArgs.drop M.nPc`
(`tgtEsAV`).  The recursor model's index values at an outside class are
the recorded result indices substituted at the instantiation
(`tgtOutEs`, `instCtor_decode`'s).  They agree once the conclusion's
spine arity is known — which no reading gives (a leaf may be an
application), and which the carrier records (`LfpOwn.ctorConcl`: a
recorded constructor concludes in its member at
its own levels, applied to `nPc + |ids|` arguments):

* `PiConcl` — "past `n` syntactic binders, the constant `I` at `us`
  applied to `m` arguments", kept by instantiation (`instantiate1`,
  levels, `instPisWith`) and by opening (`openPisAtFvars`);
* `AnnotTerm.mkAppN_inj_head` — two applications of the same head are
  equal only at equal argument lists;
* **`tgtEsAV_outside`** — at an outside class the target check's index
  expressions read as the class's (`tgtEsAV = tgtOutEs`), so the rule
  data are the target check's at every class.
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

/-! ## The conclusion's shape, syntactically -/

/-- Past `n` syntactic binders, the constant `I` at the levels `us`
applied to `m` arguments. -/
@[expose] def PiConcl (I : Name) (us : List Level) (m : Nat) : Nat → Expr → Prop
  | 0, e => ∃ args, e = Expr.mkAppN (.const I us) args ∧ args.length = m
  | n + 1, .forallE _ b _ => PiConcl I us m n b
  | _ + 1, _ => False

theorem piConcl_of_stripPis {I : Name} {us : List Level} {m : Nat} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × ConLeche.BinderMeta)} {args : List Expr},
      e.stripPis n = some (bs, Expr.mkAppN (.const I us) args) → args.length = m →
      PiConcl I us m n e
  | 0, e, bs, args, h, hl => by
    simp only [ConLeche.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨args, h.2, hl⟩
  | n + 1, .forallE t b mb, bs, args, h, hl => by
    simp only [ConLeche.Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs', b'⟩, hs, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact piConcl_of_stripPis n hs hl
  | _ + 1, .bvar _, _, _, h, _ | _ + 1, .fvar _ _, _, _, h, _ | _ + 1, .sort _, _, _, h, _
  | _ + 1, .const _ _, _, _, h, _ | _ + 1, .app _ _, _, _, h, _
  | _ + 1, .lam _ _ _, _, _, h, _ | _ + 1, .letE _ _ _, _, _, h, _ | _ + 1, .lit _, _, _, h, _
  | _ + 1, .proj _ _ _, _, _, h, _ => by simp [ConLeche.Expr.stripPis] at h

theorem piConcl_instantiate1 {I : Name} {us : List Level} {m : Nat} (v : Expr) :
    ∀ (n : Nat) (e : Expr) (k : Nat), PiConcl I us m n e → PiConcl I us m n (e.instantiate1 v k)
  | 0, e, k, ⟨args, he, hl⟩ => by
    subst he
    refine ⟨args.map (·.instantiate1 v k), ?_, by rw [List.length_map, hl]⟩
    rw [Expr.mkAppN_instantiate1]; rfl
  | n + 1, .forallE t b mb, k, h => piConcl_instantiate1 v n b (k + 1) h
  | _ + 1, .bvar _, _, h | _ + 1, .fvar _ _, _, h | _ + 1, .sort _, _, h
  | _ + 1, .const _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .lam _ _ _, _, h
  | _ + 1, .letE _ _ _, _, h | _ + 1, .lit _, _, h | _ + 1, .proj _ _ _, _, h => h.elim

theorem piConcl_instantiateLevelParams {I : Name} {us : List Level} {m : Nat}
    (ks : List Name) (vs : List Level) :
    ∀ (n : Nat) (e : Expr), PiConcl I us m n e →
      PiConcl I (us.map (Level.subst ks vs)) m n (e.instantiateLevelParams ks vs)
  | 0, e, ⟨args, he, hl⟩ => by
    subst he
    refine ⟨args.map (·.instantiateLevelParams ks vs), ?_, by rw [List.length_map, hl]⟩
    rw [instantiateLevelParams_mkAppN]; rfl
  | n + 1, .forallE t b mb, h => piConcl_instantiateLevelParams ks vs n b h
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h
  | _ + 1, .const _ _, h | _ + 1, .app _ _, h | _ + 1, .lam _ _ _, h
  | _ + 1, .letE _ _ _, h | _ + 1, .lit _, h | _ + 1, .proj _ _ _, h => h.elim

theorem piConcl_instPisWith {I : Name} {us : List Level} {m n : Nat} :
    ∀ (ds : List Expr) {e e' : Expr}, PiConcl I us m (ds.length + n) e →
      ConLeche.instPisWith ds e = some e' → PiConcl I us m n e'
  | [], e, e', h, hi => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at hi
    subst hi; simpa using h
  | a :: ds, .forallE t b mb, e', h, hi => by
    have hi' : ConLeche.instPisWith ds (b.instantiate1 a) = some e' := hi
    have hb : PiConcl I us m (ds.length + n) b := by
      simp only [List.length_cons, show ds.length + 1 + n = (ds.length + n) + 1 by omega] at h
      exact h
    exact piConcl_instPisWith ds (piConcl_instantiate1 a _ b 0 hb) hi'
  | _ :: _, .bvar _, _, _, hi | _ :: _, .fvar _ _, _, _, hi | _ :: _, .sort _, _, _, hi
  | _ :: _, .const _ _, _, _, hi | _ :: _, .app _ _, _, _, hi | _ :: _, .lam _ _ _, _, _, hi
  | _ :: _, .letE _ _ _, _, _, hi | _ :: _, .lit _, _, _, hi
  | _ :: _, .proj _ _ _, _, _, hi => by simp [ConLeche.instPisWith] at hi

theorem piConcl_open {I : Name} {us : List Level} {m : Nat} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {cb : Expr}, PiConcl I us m n e →
      ConLeche.openPisAtFvars n e d = some (fvs, cb) → PiConcl I us m 0 cb
  | 0, e, d, fvs, cb, h, ho => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨-, rfl⟩ := ho
    exact h
  | n + 1, .forallE t b mb, d, fvs, cb, h, ho => by
    simp only [ConLeche.openPisAtFvars] at ho
    split at ho
    · next fvs' cb' hrec =>
      simp only [Option.some.injEq, Prod.mk.injEq] at ho
      obtain ⟨-, rfl⟩ := ho
      exact piConcl_open n (piConcl_instantiate1 _ n b 0 h) hrec
    · exact nomatch ho
  | _ + 1, .bvar _, _, _, _, _, ho | _ + 1, .fvar _ _, _, _, _, _, ho
  | _ + 1, .sort _, _, _, _, _, ho | _ + 1, .const _ _, _, _, _, _, ho
  | _ + 1, .app _ _, _, _, _, _, ho | _ + 1, .lam _ _ _, _, _, _, _, ho
  | _ + 1, .letE _ _ _, _, _, _, _, ho | _ + 1, .lit _, _, _, _, _, ho
  | _ + 1, .proj _ _ _, _, _, _, _, ho => by simp [ConLeche.openPisAtFvars] at ho

/-! ## Applications of one head -/

omit [SetTheory V] in
theorem sizeOf_le_mkAppN : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    sizeOf f ≤ sizeOf (AnnotTerm.mkAppN f as)
  | [], _ => Nat.le_refl _
  | a :: as, f => by
    rw [AnnotTerm.mkAppN_cons]
    refine Nat.le_trans ?_ (sizeOf_le_mkAppN as (.app f a))
    show sizeOf f ≤ 1 + sizeOf f + sizeOf a
    omega

omit [SetTheory V] in
/-- **Two applications of the same head are equal only at equal
argument lists.** -/
theorem AnnotTerm.mkAppN_inj_head {f : AnnotTerm} :
    ∀ {as bs : List AnnotTerm}, AnnotTerm.mkAppN f as = AnnotTerm.mkAppN f bs → as = bs := by
  intro as bs h
  rcases Nat.lt_trichotomy as.length bs.length with hlt | heq | hgt
  · exfalso
    obtain ⟨b₁, b₂, rfl, hl⟩ : ∃ b₁ b₂, bs = b₁ ++ b₂ ∧ b₂.length = as.length :=
      ⟨bs.take (bs.length - as.length), bs.drop (bs.length - as.length), by simp,
        by rw [List.length_drop]; omega⟩
    rw [annotMkAppN_append] at h
    obtain ⟨hf, -⟩ := AnnotTerm.mkAppN_inj h hl.symm
    have hne : b₁ ≠ [] := by
      intro h0; subst h0; rw [List.nil_append] at hlt; omega
    obtain ⟨b, b₁', rfl⟩ := List.exists_cons_of_ne_nil hne
    have := sizeOf_le_mkAppN b₁' (.app f b)
    rw [← AnnotTerm.mkAppN_cons, ← hf] at this
    have h2 : sizeOf f < sizeOf (AnnotTerm.app f b) := by
      show sizeOf f < 1 + sizeOf f + sizeOf b; omega
    omega
  · exact (AnnotTerm.mkAppN_inj h heq).2
  · exfalso
    obtain ⟨a₁, a₂, rfl, hl⟩ : ∃ a₁ a₂, as = a₁ ++ a₂ ∧ a₂.length = bs.length :=
      ⟨as.take (as.length - bs.length), as.drop (as.length - bs.length), by simp,
        by rw [List.length_drop]; omega⟩
    rw [annotMkAppN_append] at h
    obtain ⟨hf, -⟩ := AnnotTerm.mkAppN_inj h hl
    have hne : a₁ ≠ [] := by
      intro h0; subst h0; rw [List.nil_append] at hgt; omega
    obtain ⟨a, a₁', rfl⟩ := List.exists_cons_of_ne_nil hne
    have := sizeOf_le_mkAppN a₁' (.app f a)
    rw [← AnnotTerm.mkAppN_cons, hf] at this
    have h2 : sizeOf f < sizeOf (AnnotTerm.app f a) := by
      show sizeOf f < 1 + sizeOf f + sizeOf a; omega
    omega

/-! ## The outside rule's conclusion -/

section Concl

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {nested : Bool} {block : List ConstantInfo}

variable (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI)

include hμ hcov h R hr hcA hrhs hMo hcl in
set_option maxHeartbeats 1000000 in
/-- **An outside rule's conclusion, syntactically and read**: the
instantiated constructor's opened conclusion is the major's inductive at
the major's levels applied to `nPc + |ids|` arguments, and it reads as
the recorded result, substituted by `instTau`. -/
theorem tgtOutCbody (ψ : Name → Nat) :
    ∃ cargs, tgtCbody pp.toBlockShape out j i
        = Expr.mkAppN (.const (tgtMajor out j).ind (tgtMajor out j).lvls) cargs ∧
      cargs.length = (tgtMajor out j).nPc
        + (D.ids mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)).length ∧
      denoteMeta mpC.base2.acval envC ψ (tgtB pp.toBlockShape out j i) (tgtCbody pp.toBlockShape out j i)
        = some (AnnotTerm.substAV (instTau mpC ψ D (tgtMajor out j).lvls (tgtRP pp.toBlockShape j)
              (tgtMajor out j).ds)
            (AnnotTerm.mkAppN (.bvar (cA.2 + (D.k - 1 - mm)))
              ((List.range (tgtMajor out j).ds.length).map
                  (fun q => AnnotTerm.bvar ((tgtMajor out j).ds.length + D.k + cA.2 - 1 - q))
                ++ D.resIdx (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) mm i)) cA.2) := by
  obtain ⟨dsa, hdsa, hul, hds, hlenP, -⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, ⟨E⟩, -, hQcr, hQfF, -, -, -⟩ := targetRuleAtG R hr hcA hrhs
  subst hMaj
  obtain ⟨-, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hMo
  have hct' : tgtCtorOf out j i = cA := tgtCtorOf_at hr hcA
  obtain ⟨hiD, hfc0, hlpsI, hlps⟩ := hcl.ctor_at (by rw [← tgtRs_ctors hr]; exact hcA)
  have hnd := hcl.hnd
  rw [hlpsI] at hnd hul hlenP ⊢
  have hfc : envC.find? (D.ctorName mm i)
      = some (.ctorInfo cA.1 (tgtMajor out j).ds.length cA.2) := by
    rw [hdsLen]; exact hfc0
  have hcr : ConLeche.instPisWith (tgtMajor out j).ds
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls) = some Q.crest := by
    have h0 := Q.hcrest
    simpa [ConLeche.targetCtorAt, hMo] using h0
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hfld : ConLeche.openPisAtFvars cA.2 Q.crest (tgtRP pp.toBlockShape j)
      = some (Q.fvsF, Q.cbody) := by
    rw [hRP]; exact Q.hfld
  have hcb : tgtCbody pp.toBlockShape out j i = Q.cbody := by
    rw [tgtCbody, ← hQcr, hct', hfld]; rfl
  have hB : tgtB pp.toBlockShape out j i = tgtRP pp.toBlockShape j + cA.2 := by
    rw [tgtB, hct']
  -- the reading, off the recorded constructor
  obtain ⟨-, -, -, -, -, -, hrdC, -⟩ :=
    instCtor_open mpC hcl.hD hcl.hnN hcl.hkN hlps hnd hul hds hdsa hlenP hcl.hmm hiD hfc hcr hfld
  -- the syntax, off `LfpOwn.ctorConcl`
  obtain ⟨cv₈, nPc₈, nF₈, hf₈, bs, args, hstrip, hlen⟩ :=
    (hcov.own D hcl.hD).ctorConcl mm hcl.hmm i hiD
  rw [hfc0] at hf₈
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv₈ ∧ (tgtMajor out j).nPc = nPc₈ ∧ cA.2 = nF₈ := by
    injection hf₈ with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hP0 := piConcl_of_stripPis _ hstrip rfl
  have hP1 := piConcl_instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls _ _ hP0
  rw [map_param_subst hnd hul] at hP1
  rw [← hdsLen] at hP1
  have hP2 := piConcl_instPisWith (tgtMajor out j).ds hP1 hcr
  obtain ⟨cargs, hcE, hcl'⟩ := piConcl_open _ hP2 hfld
  refine ⟨cargs, by rw [hcb, hcE, hcl.hmem], ?_, ?_⟩
  · rw [hcl', hlen, ← hlpsI]
  · rw [hcb, hB]; exact hrdC

include hμ hcov h R hr hcA hrhs hMo hcl in
set_option maxHeartbeats 1000000 in
/-- **At an outside class the target check's index expressions read as
the class's**: `tgtEsAV = tgtOutEs`. -/
theorem tgtEsAV_outside (ψ : Name → Nat) :
    tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ j i
      = tgtOutEs mpC D mm cvI.levelParams (tgtMajor out j) (tgtRP pp.toBlockShape j) ψ i := by
  obtain ⟨cargs, hcE, -, hrd⟩ := tgtOutCbody hμ hcov h R hr hcA hrhs hMo hcl ψ
  obtain ⟨-, -, hul, -, -, -⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  obtain ⟨caps, hfI⟩ := hcl.hfind
  rw [hcE] at hrd
  obtain ⟨fa, vs, hfa, hvs, heq⟩ := denoteMeta_mkAppN_inv hrd
  rw [denoteMeta_const (ci := .indInfo cvI caps) hfI hul] at hfa
  obtain rfl := Option.some.inj hfa
  -- the recorded head is the major's inductive, read
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by
    rw [← tgtRs_ctors hr]; exact hcA
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok D hcl.hD
  have hmmk : D.k - 1 - mm < (tgtMajor out j).ds.length + D.k := by have := hcl.hmm; omega
  have hhead : AnnotTerm.substAV (instTau mpC ψ D (tgtMajor out j).lvls (tgtRP pp.toBlockShape j)
        (tgtMajor out j).ds) (.bvar (cA.2 + (D.k - 1 - mm))) cA.2
      = mpC.base2.acval (tgtMajor out j).ind
          (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) := by
    rw [AnnotTerm.substAV_bvar_ge _ (by omega), show cA.2 + (D.k - 1 - mm) - cA.2 = D.k - 1 - mm
      by omega, instTau, substTau, if_pos hmmk, grpX, grpS,
      if_neg (by have := hcl.hmm; omega), show (tgtMajor out j).ds.length + D.k - 1 - (D.k - 1 - mm)
        - (tgtMajor out j).ds.length = mm by have := hcl.hmm; omega,
      grpSub_none (by simp), Option.getD_none, hcl.hmem,
      denoteMeta_const (ci := .indInfo cvI caps) hfI hul, Option.getD_some]
    exact liftN_eq_self_of_closed (mpC.base2.cval_closedL _ _) 0 _
  rw [AnnotTerm.substAV_mkAppN, hhead] at heq
  have hvsE := AnnotTerm.mkAppN_inj_head heq.symm
  have hvsM := denoteMetaSpine_eq_map hvs
  rw [tgtEsAV, hcE, Expr.getAppArgs_mkAppN]
  simp only [show (Expr.const (tgtMajor out j).ind (tgtMajor out j).lvls).getAppArgs = [] from rfl,
    List.nil_append]
  obtain ⟨rc, u, -, ⟨E⟩⟩ := targetEntryAt R hr
  obtain ⟨-, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hMo
  rw [List.map_drop, ← hvsM, hvsE, List.map_append, List.drop_left'
    (by rw [List.length_map, List.length_map, List.length_range, hdsLen]), tgtOutEs,
    List.getD_eq_getElem?_getD, hcAM, Option.getD_some]

end Concl

end ConLeche.Model
