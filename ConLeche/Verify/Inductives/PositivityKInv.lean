module

public import ConLeche.Verify.Inductives.PositivityInv
public import ConLeche.Kernel.Inductives.BlockPositivityK
public import ConLeche.Verify.Inductives.UseOkKRun
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.DirectInv

public section

/-!
# The key-named positivity stage, inverted (PRIMREC / NESTKN-M5)

`checkBlockPositivityK` (`Kernel/Inductives/BlockInstall.lean`, UNWIRED) read
back as `checkBlockPositivity` is (`PositivityInv.lean`): the canonical
parameters, the holes, the key-named walk `nestBlockCtorsK` and U2.

* `checkBlockPositivityK_split` — the stage split into its runs;
* `checkBlockPositivityK_inv_gen` — `checkBlockPositivity_inv_gen`'s
  statement VERBATIM at the key-named stage (any `ops`): the crest, the normal
  form the run's entry, U2, M2′ (`nestNoMemberConst`);
* `checkBlockPositivityK_derivU` — every member constructor's derivation at
  the use hook (`nestBlockCtorsK_derivU`) at the stage's context, the one
  hypothesis (`CtxTysClosed`) discharged from `EnvWF`.

At the switch `checkBlockPositivity` becomes this function, and the two
`_inv_gen`s have one statement: its consumers (`canonOcc_of_positivity`)
swap the lemma's name only.
-/

namespace ConLeche

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {holes : List Expr}

/-- **M2′ at one member's constructors of the key-named walk**: the walk
checked each member-abstracted constructor type for a member constant. -/
theorem nestMemberCtorsK_occ :
    ∀ {cs : List (ConstantVal × Nat)} {st : NestStK} {kss : List (List NestFieldKind)}
      {nss : List Expr} {st' : NestStK},
      nestMemberCtorsK (m := CheckM) ops env ctx holes cs st = .ok (kss, nss, st') →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        (nestAbstract ctx holes cA.1.type).nestOcc ctx.names 0 0 = false
  | [], _, _, _, _, _, j, cA, hj => by simp at hj
  | c :: cs, st, kss, nss, st', h, j, cA, hj => by
    simp only [nestMemberCtorsK, bind, Except.bind] at h
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i u hnm
    have hnm' : (nestAbstract ctx holes c.1.type).nestOcc ctx.names 0 0 = false := by
      unfold nestNoMemberConst at hnm
      split at hnm
      · simp [throw, throwThe, MonadExceptOf.throw] at hnm
      · rename_i hn; simpa using hn
    split at h
    · simp at h
    rename_i r₂ hr₂
    obtain ⟨kss₂, nss₂, st₂⟩ := r₂
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact hnm'
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      exact nestMemberCtorsK_occ hr₂ j cA hj

/-- **M2′ at every member's constructors of the key-named walk.** -/
theorem nestBlockCtorsGoK_occ :
    ∀ {css : List (List (ConstantVal × Nat))} {st : NestStK}
      {ksss : List (List (List NestFieldKind))} {nsss : List (List Expr)} {st' : NestStK},
      nestBlockCtorsGoK (m := CheckM) ops env ctx holes css st = .ok (ksss, nsss, st') →
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
          (nestAbstract ctx holes cA.1.type).nestOcc ctx.names 0 0 = false
  | [], _, _, _, _, _, c, cs, hc => by simp at hc
  | cs₀ :: css, st, ksss, nsss, st', h, c, cs, hc => by
    simp only [nestBlockCtorsGoK, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i r₁ hr₁
    obtain ⟨kss, nss, st₁⟩ := r₁
    simp only at h
    split at h
    · simp at h
    rename_i r₂ hr₂
    obtain ⟨ksss₂, nsss₂, st₂⟩ := r₂
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact nestMemberCtorsK_occ hr₁
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc
      exact nestBlockCtorsGoK_occ hr₂ c cs hc

/-- **M2′ of the key-named walk**, at the whole block. -/
theorem nestBlockCtorsK_occ {css : List (List (ConstantVal × Nat))}
    {ksss : List (List (List NestFieldKind))} {nsss : List (List Expr)} {base : NestState}
    (h : nestBlockCtorsK (m := CheckM) ops env ctx holes css = .ok (ksss, nsss, base))
    (c : Nat) (cs : List (ConstantVal × Nat)) (hc : css[c]? = some cs)
    (j : Nat) (cA : ConstantVal × Nat) (hj : cs[j]? = some cA) :
    (nestAbstract ctx holes cA.1.type).nestOcc ctx.names 0 0 = false := by
  simp only [nestBlockCtorsK, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨ksss₁, nsss₁, st⟩ := r
  exact nestBlockCtorsGoK_occ hr c cs hc j cA hj

/-- **The key-named positivity stage, split into its runs**: the
canonical parameters, the holes, the key-named walk and U2. -/
theorem checkBlockPositivityK_split {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nodes : NestNodes}
    (h : checkBlockPositivityK ops env₁ find? consts p cvTas ctorsAs = .ok (kinds, nfs, nodes)) :
    ∃ cvTa0 fvsP rest holes st, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find? consts) = some holes ∧
      nestBlockCtorsK ops env₁ (p.nestCtx fvsP find? consts) holes ctorsAs = .ok (kinds, nfs, st) ∧
      checkAbsCtorTysAll ops env₁ (p.nestCtx fvsP find? consts) holes ctorsAs nfs = .ok () ∧
      nodes = ⟨st.nodes.toList, nestMemberNfs (p.nestCtx fvsP find? consts) ctorsAs nfs ++
        st.ctorNfs.toList⟩ := by
  unfold checkBlockPositivityK at h
  obtain ⟨cvTa0, h0, h⟩ := exceptBind_ok h
  obtain ⟨pq, h1, h⟩ := exceptBind_ok h
  obtain ⟨holes, h2, h⟩ := exceptBind_ok h
  obtain ⟨⟨kinds', nfs', st⟩, h3, h⟩ := exceptBind_ok h
  obtain ⟨u, h4, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨cvTa0, pq.1, pq.2, holes, st, unwrapOr_ok h0, unwrapOr_ok h1, unwrapOr_ok h2,
    h3, h4, rfl⟩

/-- **The key-named positivity stage, constructor by constructor**:
`checkBlockPositivity_inv_gen`'s statement at `checkBlockPositivityK`. -/
theorem checkBlockPositivityK_inv_gen {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nodes : NestNodes}
    (h : checkBlockPositivityK ops env₁ find? consts p cvTas ctorsAs = .ok (kinds, nfs, nodes)) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find? consts) = some holes ∧
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ crest tyN, instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type)
            = some crest ∧
          (nfs.getD c []).getD j default = tyN ∧
          (∃ ty, ops.inferType env₁ ((p.nestCtx fvsP find? consts).hiAt 0) crest = .ok ty) ∧
          tyN.allLevelParamsDefined p.lps = true ∧
          (∃ xq sorts, openPisAtFvars cA.2 tyN ((p.nestCtx fvsP find? consts).hiAt 0) = some xq ∧
            checkStructFieldSortsI ops env₁ (Level.isEquiv p.resSort .zero == some true) false
              p.resSort ((p.nestCtx fvsP find? consts).hiAt 0) xq.1 [] cA.2 = .ok sorts) ∧
          (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type).nestOcc
            (p.nestCtx fvsP find? consts).names 0 0 = false := by
  obtain ⟨cvTa0, fvsP, rest, holes, st, hcv', hpq', hh, hr, hA, rfl⟩ :=
    checkBlockPositivityK_split h
  refine ⟨cvTa0, fvsP, rest, holes, hcv', hpq', hh, fun c cs hc j cA hj => ?_⟩
  obtain ⟨-, -, -, hall⟩ := nestBlockCtorsK_deriv (hookOkK_triv (ops := ops) (env := env₁)
    (ctx := p.nestCtx fvsP find? consts)) hr
  obtain ⟨crest, ks, tyN, hcrest, -, hnj, -⟩ := hall c cs hc j cA hj
  have hocc := nestBlockCtorsK_occ hr c cs hc j cA hj
  have hcl : c < nfs.length := by
    rcases Nat.lt_or_ge c nfs.length with h' | h'
    · exact h'
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h'] at hnj
      simp at hnj
  have hn : nfs[c]? = some (nfs.getD c []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl]; rfl
  obtain ⟨crest', ty, hcrest', hty, hlp, xq, sorts, hxq, hsorts⟩ :=
    checkAbsCtorTys_inv (checkAbsCtorTysAll_inv hA c cs _ hc hn) j cA tyN hj hnj
  have hcr : instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type)
      = some crest := hcrest
  have hcrest'' : instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type)
      = some crest' := hcrest'
  rw [hcr] at hcrest''
  obtain rfl := Option.some.inj hcrest''
  refine ⟨crest, tyN, hcr, ?_, ⟨ty, hty⟩, hlp, ⟨xq, sorts, hxq, hsorts⟩, hocc⟩
  rw [List.getD_eq_getElem?_getD, hnj]; rfl

/-- **The key-named stage's walk, derived at the use hook** at the
stage's own context, from the environment's well-formedness. -/
theorem checkBlockPositivityK_derivU {env₁ : Env} (hwf : EnvWF env₁) {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nodes : NestNodes}
    (h : checkBlockPositivityK ops env₁ env₁.find? env₁.consts p cvTas ctorsAs
      = .ok (kinds, nfs, nodes)) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP env₁.find? env₁.consts) = some holes ∧
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ crest ks, instPisWith fvsP
            (nestAbstract (p.nestCtx fvsP env₁.find? env₁.consts) holes cA.1.type) = some crest ∧
          (kinds.getD c [])[j]? = some ks ∧
          MemberCtorDKH ops env₁ (p.nestCtx fvsP env₁.find? env₁.consts)
            (UseOkK ops env₁ (p.nestCtx fvsP env₁.find? env₁.consts)) cA.2 crest (ks.map (·.erase))
            ((nfs.getD c []).getD j default) := by
  obtain ⟨cvTa0, fvsP, rest, holes, st, hcv', hpq', hh, hr, -, -⟩ :=
    checkBlockPositivityK_split h
  have hcl : CtxTysClosed (p.nestCtx fvsP env₁.find? env₁.consts) :=
    ctxTysClosed_of_envWF hwf rfl
  exact ⟨cvTa0, fvsP, rest, holes, hcv', hpq', hh, fun c cs hc j cA hj =>
    nestBlockCtorsK_posPremise hcl hr hc hj⟩

end ConLeche
