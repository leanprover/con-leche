module

public import ConLeche.Verify.Inductives.GenRecRun
public import ConLeche.Verify.Inductives.ClassGenScope
public import ConLeche.Verify.Inductives.NestNfScope
public import ConLeche.Verify.CheckerF
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Cached.GenRecC

public section

/-!
# The generated stage's generator inputs are scoped (`ClassGenScoped`)

`genScoped_of_run`: the generated recursor stage's run (`GenRecRun`)
builds its generator `R.g` from inputs scoped the way `ClassGenScoped`
asks — what `recStage_of_gen` and the family premise take as their
hypothesis `hg`.  Field by field, each from the run's own binds:

* `params` — the canonical parameters are the first former's opened
  telescope (`blockNestCtx`): a closed former opened at `0` gives
  `fvar i` typed over the earlier ones;
* `ds` — a class's parameters: a member's are the canonical parameters,
  an outside class's are its key's (the pre-pass's reading off CHECKED,
  hence closed, stream recursor types, `classRead_keys_scoped`, moved to
  the canonical parameters, `classKeyCanon`) under `targetMajorOf`'s guard
  (no loose bound variable, free variables below `nP`);
* `former` — a member's former is a (closed) stream former, an outside
  class's the stored inductive's type at levels (`EnvWF`);
* `tyN` — the datum entry of the positivity check's table, whose entries
  are scoped over the parameters (`NfStScoped`, `Verify/Inductives/NestNfScope.lean`),
  from the positivity stage's state through the seeds;
* `tyD` — a stored constructor's type (closed: a stream constructor's or a
  stored one's at levels) instantiated at the class's parameters;
* `order` — the pre-pass reads a minor premise's class and its inductive
  hypotheses' classes as ordinals of the motives read BEFORE it
  (`classOfMotiveVar` over `classReadSlots`' `motPos`), and the generator's
  recursive kinds are exactly those hypotheses' classes (`classFieldsOf`);
* `pre` — the prefix is computed with `pre := []`, which `prefixBinders`
  does not read.

The caller's hypotheses: the two environments well formed, the stream's
formers and constructors closed, one former per member, and the
positivity stage's final state scoped (`checkBlockPositivity_nfScoped`).
-/

namespace ConLeche

open Expr

/-! ## Small list facts -/

theorem except_mapM_getElem? {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' →
      l'.length = l.length ∧ ∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, l'[i]? = some b ∧ f a = .ok b
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun _ _ h => nomatch h⟩
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    obtain ⟨bs, hbs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hall⟩ := except_mapM_getElem? hbs
    refine ⟨by simp [hl], fun i a' hi => ?_⟩
    cases i with
    | zero =>
      obtain rfl : a = a' := by simpa using hi
      exact ⟨b, rfl, hb⟩
    | succ i => simpa using hall i a' (by simpa using hi)

/-- `targetMajorNfs` keeps entries of its table only. -/
theorem targetMajorNfs_sub {ops : CheckerOps CheckM} {env : Env} {p : BlockShape}
    {formerTys pfvs : List Expr} {us : List Level} {ds : List Expr}
    {ctors : List (ConstantVal × Nat)} :
    ∀ {tbl nfs : List NestCtorNf},
      targetMajorNfs ops env p formerTys pfvs us ds ctors tbl = .ok nfs → ∀ e ∈ nfs, e ∈ tbl
  | [], nfs, h => by
    simp only [targetMajorNfs, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro e he; exact nomatch he
  | e₀ :: tbl, nfs, h => by
    unfold targetMajorNfs at h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    have ih := targetMajorNfs_sub hrest
    intro e he
    split at h
    · obtain ⟨b, -, h⟩ := exceptBind_ok h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp he with rfl | he
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih e he)
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact List.mem_cons_of_mem _ (ih e he)
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact List.mem_cons_of_mem _ (ih e he)

/-! ## The run's pieces -/

section Run

variable {mode : CheckMode} {F : Nat} {env₁ envC : Env} {p : BlockShape} {nestedBit : Bool}
  {pos : NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- The run's walk context: the first former opened, the environment's
lookups. -/
theorem genRun_ctx
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out) :
    ∃ cvTa0 rest, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (R.ctx.params, rest) ∧
      R.ctx = p.nestCtx R.ctx.params env₁.find? env₁.consts ∧ nestHoles R.ctx = some R.holes := by
  obtain ⟨cvTa0, fvsP, rest, h0, hop, hctx, hh⟩ := blockNestCtx_inv R.hctx
  rw [mkFEnv_find?_fun] at hctx
  refine ⟨cvTa0, rest, h0, ?_, ?_, hh⟩
  · rw [hctx]; exact hop
  · rw [hctx]; rfl

/-- **The canonical parameters**: `fvar i`, typed over the earlier ones. -/
theorem genRun_params
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    (hT : ∀ cv ∈ cvTas, ScB 0 cv.type) :
    R.ctx.params.length = p.nP ∧
      ∀ (i : Nat) (x : Expr), R.ctx.params[i]? = some x → ∃ ty, x = .fvar i ty ∧ ScB i ty := by
  obtain ⟨cvTa0, rest, h0, hop, -, -⟩ := genRun_ctx R
  obtain ⟨hl, hfvs, -⟩ := ScB.openPis hop (hT cvTa0 (List.mem_of_mem_head? h0))
  exact ⟨hl, fun i x hx => by simpa using hfvs i x hx⟩

theorem genRun_params_scb
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    (hT : ∀ cv ∈ cvTas, ScB 0 cv.type) : ∀ x ∈ R.ctx.params, ScB p.nP x := by
  obtain ⟨hl, hP⟩ := genRun_params R hT
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨ty, hxe, hty⟩ := hP i _ (List.getElem?_eq_getElem hi)
  rw [hxe]
  exact ScB.fvar (by omega) hty

/-- The stream's recursor types the pre-pass reads are closed. -/
theorem genRun_cvRis_closed
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out) :
    ∀ cv ∈ R.cvRis, WScoped 0 cv.type := by
  obtain ⟨hlen, hall⟩ := classStreamRecs_run R.hcvRis
  intro cv hcv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcv
  obtain ⟨rc, hrc⟩ : ∃ rc, p.recs[i]? = some rc :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨cv', hcv', hchk⟩ := hall i rc hrc
  rw [List.getElem?_eq_getElem hi] at hcv'
  obtain rfl := Option.some.inj hcv'
  rw [checkConstantValF_eq] at hchk
  exact WScoped.of_not_hasFvar (checkConstantVal_typeWF hchk).1

/-- **Every class checked as a major**, scoped: its parameters scoped over
the canonical parameters (an outside class's below them), its
constructors closed, a member's index a member. -/
theorem genRun_Ms₀
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    (henvC : EnvWF envC) (hT : ∀ cv ∈ cvTas, ScB 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, ScB 0 c.1.type) :
    ∀ M ∈ R.Ms₀, (∀ x ∈ M.ds, ScB p.nP x) ∧ (M.member = none → ∀ x ∈ M.ds, x.fvarB ≤ p.nP) ∧
      (∀ cA ∈ M.ctors, ScB 0 (targetCtorAt M cA.1)) ∧
      (∀ t, M.member = some t → t < p.memberNames.length) ∧
      (M.member = none → ∃ cv caps, envC.find? M.ind = some (.indInfo cv caps)) := by
  have hpar := genRun_params_scb R hT
  obtain ⟨hlP, -⟩ := genRun_params R hT
  obtain ⟨hlen, hall⟩ := classMajors_run R.hMs₀
  -- the pre-pass's keys, scoped, moved to the canonical parameters
  have hkeys₀ : ∀ key ∈ R.rd.classes, ∀ x ∈ key.ds, ∃ D, WScoped D x := by
    refine Cached.classRead_keys_scoped (fun rc hrc => ?_) R.hrd
    obtain ⟨⟨rc', cv⟩, hmem, rfl⟩ := List.mem_map.mp hrc
    exact genRun_cvRis_closed R cv (List.of_mem_zip hmem).2
  intro M hM
  obtain ⟨i, hi, hMi⟩ := List.getElem_of_mem hM
  have hik : i < (R.rd.classes.map (classKeyCanon R.ctx.params)).length := by omega
  obtain ⟨M', hM', ⟨C⟩⟩ := hall i _ (List.getElem?_eq_getElem hik)
  rw [List.getElem?_eq_getElem hi, hMi] at hM'
  obtain rfl := Option.some.inj hM'
  have hkey : (R.rd.classes.map (classKeyCanon R.ctx.params))[i] ∈
      R.rd.classes.map (classKeyCanon R.ctx.params) := List.getElem_mem _
  generalize (R.rd.classes.map (classKeyCanon R.ctx.params))[i] = key at hkey C
  cases C.major with
  | member I t ms ctorsA hfn ht hms hctors hpar' nfs =>
    dsimp only
    refine ⟨fun x hx => hpar x (List.mem_of_mem_take hx), fun h => by simp at h,
      fun cA hcA => hct ctorsA (List.mem_of_getElem? hctors) cA hcA, fun t' ht' => ?_,
      fun h => by simp at h⟩
    obtain rfl : t = t' := Option.some.inj ht'
    exact (List.findIdx?_eq_some_iff_getElem.mp ht).1
  | outside I us nPc nIdx ctors sI hfn ht hnq hctors hdsLen hdsSc hment hinst hsort nfs =>
    dsimp only
    refine ⟨fun x hx => ?_, fun _ x hx => (hdsSc x hx).2, fun cA hcA => ?_, fun _ h => by simp at h,
      fun _ => ?_⟩
    · have hxa := List.mem_of_mem_take hx
      rw [Expr.getAppArgs_mkAppN] at hxa
      simp only [Expr.getAppArgs, List.nil_append] at hxa
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hkey
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxa
      obtain ⟨D, hD⟩ := hkeys₀ k0 hk0 y hy
      have hw : WScoped (max D p.nP) (targetCanonParams R.ctx.params y) :=
        replaceFVars_WScoped (fun j r hr => (hpar r (List.mem_of_getElem? hr)).1.mono
          (Nat.le_max_right _ _)) _ (WScoped.mono (Nat.le_max_left _ _) hD)
      exact ⟨WScoped.of_fvarsBelow hw (Expr.fvarB_le (hdsSc _ hx).2),
        Expr.bvarB_le (by rw [(hdsSc _ hx).1]; exact Nat.le_refl 0)⟩
    · have hc : NestCtxOk (⟨[], [], 0, [], [], .zero, (mkFEnv envC).find?,
          (mkFEnv envC).env.consts⟩ : NestCtx) ∧
          NestCtxB (⟨[], [], 0, [], [], .zero, (mkFEnv envC).find?,
            (mkFEnv envC).env.consts⟩ : NestCtx) := by
        rw [mkFEnv_find?_fun, mkFEnv_env]
        exact ⟨⟨fun ci hci => (henvC ci hci).1,
            fun _ ci hf => (henvC ci (List.mem_of_find?_eq_some hf)).1⟩,
          ⟨fun ci hci => (henvC ci hci).2.2.2.1,
            fun _ ci hf => (henvC ci (List.mem_of_find?_eq_some hf)).2.2.2.1⟩⟩
      have h0 := nestContainer_scb hc.1 hc.2 hctors cA hcA
      simp only [targetCtorAt]
      refine ScB.of_closed ?_ ?_ 0
      · rw [Expr.hasFvar_instantiateLevelParams]; exact (ScB.closed h0).1
      · rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact h0.2
    · unfold targetCtorsOf nestContainer at hctors
      dsimp only at hctors
      split at hctors
      · rename_i cv caps hf
        rw [mkFEnv_find?_fun] at hf
        exact ⟨cv, caps, hf⟩
      · exact nomatch hctors

/-- **Every class with its table entries**: the class checked as a major,
its entries among the table's. -/
theorem genRun_Ms
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out) :
    R.Ms.length = R.Ms₀.length ∧ ∀ (c : Nat) (M : TargetMajor), R.Ms[c]? = some M →
      ∃ M₀, R.Ms₀[c]? = some M₀ ∧ M = { M₀ with nfs := M.nfs } ∧
        ∀ e ∈ M.nfs, e ∈ R.st.ctorNfs.toList := by
  obtain ⟨hlen, hall⟩ := classesNfs_run R.hMs
  refine ⟨hlen, fun c M hM => ?_⟩
  have hc : c < R.Ms₀.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hM).1
  obtain ⟨nfs, hMs, hnfs⟩ := hall c _ (List.getElem?_eq_getElem hc)
  rw [hM] at hMs
  obtain rfl := Option.some.inj hMs
  exact ⟨_, List.getElem?_eq_getElem hc, rfl, targetMajorNfs_sub hnfs⟩

/-- **The positivity check's table after the seeds is scoped** over the
parameters: every entry the generated stage reads a datum off
(`ClassCtor.tyN`) — lane B2's fact. -/
theorem genRun_tbl_scoped
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    (henv₁ : EnvWF env₁) (henvC : EnvWF envC) (hT : ∀ cv ∈ cvTas, ScB 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, ScB 0 c.1.type) (hpos : NfStScoped p.nP pos) :
    ∀ e ∈ R.st.ctorNfs.toList, ScB p.nP e.ty := by
  obtain ⟨cvTa0, rest, h0, hop, hctx, hh⟩ := genRun_ctx R
  obtain ⟨hlP, -⟩ := genRun_params R hT
  have hMs₀ := genRun_Ms₀ R henvC hT hct
  have hcb : NestCtxOk R.ctx ∧ NestCtxB R.ctx := by
    rw [hctx]; exact nestCtx_ok_of_envWF henv₁ p R.ctx.params
  have hnP : R.ctx.nP = p.nP := by rw [hctx]; rfl
  have hparH : ∀ x ∈ R.ctx.params, ScB (R.ctx.hiAt 0) x := by
    intro x hx
    have := genRun_params_scb R hT x hx
    exact this.mono (by rw [← hnP]; simp [NestCtx.hiAt])
  have hholes := nestHoles_ok hcb.1 hh
  have hseeds : ∀ s ∈ classSeeds R.ctx R.holes R.Ms₀, ∀ x ∈ s.1.ds, ScB (R.ctx.hiAt 0) x := by
    intro s hs x hx
    obtain ⟨M, hM, hMn, rfl⟩ := Cached.mem_classSeeds hs
    obtain ⟨hds, hfb, -⟩ := hMs₀ M hM
    refine ⟨(nestSeedOf_ds hh (by rw [hlP, hnP]) (fun y hy => Expr.fvarB_le (by
        rw [hnP]; exact hfb hMn y hy)) x hx).2 (fun y hy => (hholes y hy).1)
        (fun y hy => (hparH y hy).1), ?_⟩
    refine nestSeedOf_closed hh (fun a ha => ?_) (fun y hy => (hds y hy).2) x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨ty, hxe, -⟩ := (genRun_params R hT).2 i _ (List.getElem?_eq_getElem hi)
    exact ⟨i, ty, hxe⟩
  have hst := nestSeeds_nfScoped hcb.1 hcb.2 (fun d e w hw he => whnf_WScoped henv₁ F hw he)
    (fun d e w hw he => whnf_looseBVars henv₁ F hw he) _ pos R.st R.hst hseeds
    (by rw [hnP]; exact hpos)
  rw [hnP] at hst
  exact hst.2

/-- A generated constructor of class `c`, as its run. -/
theorem genRun_ctor
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    {c : Nat} {x : ClassCtor} (hx : x ∈ R.ctors.getD c []) :
    ∃ M cA, R.Ms[c]? = some M ∧ cA ∈ M.ctors ∧
      Nonempty (ClassCtorRun mode F (mkFEnv envC).env p (cvTas.map (·.type)) R.rd R.Ms c cA x) := by
  obtain ⟨hlen, hall⟩ := classesCtors_run R.hctors
  by_cases hc : c < R.Ms.length
  · obtain ⟨xs, hxs, hrun⟩ := hall c _ (List.getElem?_eq_getElem hc)
    rw [List.getD_eq_getElem?_getD, hxs, Option.getD_some] at hx
    rw [Nat.zero_add] at hrun
    obtain ⟨hl, hall'⟩ := classCtorsOf_run hrun
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨x', hx', hR⟩ := hall' j _ (List.getElem?_eq_getElem (show j < R.Ms[c].ctors.length by
      omega))
    rw [List.getElem?_eq_getElem hj] at hx'
    obtain rfl := Option.some.inj hx'
    exact ⟨_, _, List.getElem?_eq_getElem hc, List.getElem_mem _, hR⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hx
    exact nomatch hx

end Run

end ConLeche
