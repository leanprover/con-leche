module

public import ConLeche.Kernel.Inductives.FieldNf
public import ConLeche.Verify.Inductives.PosDerivFun

public section

/-!
# The walk's recorded normal forms are a decision-free function

`posD_nfOk`: every field and telescope judgment of the positivity
derivation `PosD` has, as its normal-form output, what `nestNf` /
`nestTeleNf` (`ConLeche/Kernel/Inductives/FieldNf.lean`) compute on its
input, at the judgment's own hole range `[nP, hiAt prog.length)` and at
every fuel above a bound.  So the walk's record of a node's constructor
(`NestCtorNf`, K.53′: `nestCtorNf` of the derivation's telescope, which
`FrameRec` says is recorded) is `nestCtorNf` of `nestTeleNf` at the
constructor's instantiated type (`FrameRec.entry_nestTeleNf`).

This is the determinism half of the frame lemma at a frame walked at the
EMPTY stack (DESIGN "PRIMREC / FRAME"): a reader that rebuilds the
walk's input for a class — the walk's layout, the class head's group
abstracted, the block's members as holes — and runs `nestTeleNf`
computes the walk's record, by this theorem; the env gap between the
walk's `env₁` and the reader's is the env-extension lemma's.
-/

namespace ConLeche

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

/-- What `posD_nfOk` states per judgment: a field's normal form and a
telescope's normal forms and result are `nestNf`'s / `nestTeleNf`'s at
the judgment's hole range, at every fuel above some bound. -/
@[expose] def PosJ.NfOk (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) : PosJ → Prop
  | .field prog dep _ e _ nf => ∃ F, ∀ fuel, F ≤ fuel →
      nestNf ops env ctx.names ctx.nP (ctx.hiAt prog.length) fuel dep e = .ok nf
  | .tele prog base nF j cur _ nds res => ∃ F, ∀ fuel, F ≤ fuel →
      nestTeleNf ops env ctx.names ctx.nP (ctx.hiAt prog.length) fuel base nF j cur = .ok (nds, res)
  | _ => True

/-- `nestNf` one step in, at a known reduct. -/
private theorem nestNf_succ {names : List Name} {nP hi fuel dep : Nat} {e w : Expr}
    (hw : ops.whnf env dep e = .ok w) :
    nestNf ops env names nP hi (fuel + 1) dep e =
      nestNfAt names nP hi (nestNf ops env names nP hi fuel) dep e w := by
  show ops.whnf env dep e >>= _ = _
  rw [hw]
  rfl

/-- A reduct whose head is a variable or a constant is no `Π`: the
container and hole cases return it. -/
private theorem nestNf_rigid {names : List Name} {nP hi fuel dep : Nat} {e w : Expr}
    (hw : ops.whnf env dep e = .ok w) (hocc : w.nestOcc names nP hi = true)
    (hnp : ∀ a b bm, w ≠ .forallE a b bm) :
    nestNf ops env names nP hi (fuel + 1) dep e = .ok w := by
  rw [nestNf_succ hw]
  unfold nestNfAt
  rw [hocc]
  cases w with
  | forallE a b bm => exact absurd rfl (hnp a b bm)
  | _ => rfl

private theorem getAppFn_fvar_ne_pi {w : Expr} {i : Nat} {ty : Expr}
    (h : w.getAppFn = .fvar i ty) : ∀ a b bm, w ≠ .forallE a b bm := by
  intro a b bm he; subst he; simp [Expr.getAppFn] at h

private theorem getAppFn_const_ne_pi {w : Expr} {n : Name} {us : List Level}
    (h : w.getAppFn = .const n us) : ∀ a b bm, w ≠ .forallE a b bm := by
  intro a b bm he; subst he; simp [Expr.getAppFn] at h

/-- **The walk's normal forms are `nestNf`'s** (see the module docstring). -/
theorem posD_nfOk : ∀ {j : PosJ} {ts : List PosTree}, PosD ops env ctx j ts →
    PosJ.NfOk ops env ctx j := by
  intro j ts h
  induction h with
  | @const prog dep kb e w hw hocc =>
    refine ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [nestNf_succ hw]
    unfold nestNfAt
    rw [hocc]
    rfl
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ih =>
    obtain ⟨F, hF⟩ := ih
    refine ⟨F + 1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [nestNf_succ hw]
    unfold nestNfAt
    rw [hocc]
    show (do
      let nb ← nestNf ops env ctx.names ctx.nP (ctx.hiAt prog.length) f (dep + 1)
        (b.instantiate1 (.fvar dep a))
      pure (Expr.forallE a (nb.abstract1 dep) bm) : CheckM Expr) = _
    rw [hF f (by omega)]
    rfl
  | @hole prog dep kb e w i ty hw hocc hfn =>
    refine ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact nestNf_rigid hw hocc (getAppFn_fvar_ne_pi hfn)
  | @frameHole prog dep kb e w i ty h hw hocc hfn =>
    refine ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact nestNf_rigid hw hocc (getAppFn_fvar_ne_pi hfn)
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn =>
    refine ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact nestNf_rigid hw hocc (getAppFn_const_ne_pi hfn)
  | @contHit prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn =>
    refine ⟨1, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact nestNf_rigid hw hocc (getAppFn_const_ne_pi hfn)
  | frame => trivial
  | ctorsNil => trivial
  | ctorsCons => trivial
  | teleNil => exact ⟨0, fun _ _ => rfl⟩
  | @teleCons prog base nF j a b bm k nd ks nds res ts tss ts' ha hs hb iha ihs ihb =>
    obtain ⟨F₁, hF₁⟩ := iha
    obtain ⟨F₂, hF₂⟩ := ihb
    refine ⟨max F₁ F₂, fun fuel hf => ?_⟩
    simp only [nestTeleNf]
    show (do
      let nd ← nestNf ops env ctx.names ctx.nP (ctx.hiAt prog.length) fuel (base + j) a
      let (nds, res) ← nestTeleNf ops env ctx.names ctx.nP (ctx.hiAt prog.length) fuel base nF
        (j + 1) (b.instantiate1 (.fvar (base + j) a))
      pure ((nd, bm) :: nds, res) : CheckM _) = _
    rw [hF₁ fuel (by omega), hF₂ fuel (by omega)]
    rfl
  | synNil => trivial
  | synNew => trivial
  | synHit => trivial

/-- A field judgment's normal form is `nestNf`'s. -/
theorem PosD.field_nestNf {prog : List NestHole} {dep kb : Nat} {e nf : Expr} {k : PosKind}
    {ts : List PosTree} (h : PosD ops env ctx (.field prog dep kb e k nf) ts) :
    ∃ F, ∀ fuel, F ≤ fuel →
      nestNf ops env ctx.names ctx.nP (ctx.hiAt prog.length) fuel dep e = .ok nf :=
  posD_nfOk h

/-- A telescope judgment's normal forms and result are `nestTeleNf`'s. -/
theorem PosD.tele_nestTeleNf {prog : List NestHole} {base nF j : Nat} {cur res : Expr}
    {ks : List PosKind} {nds : List (Expr × BinderMeta)} {ts : List PosTree}
    (h : PosD ops env ctx (.tele prog base nF j cur ks nds res) ts) :
    ∃ F, ∀ fuel, F ≤ fuel →
      nestTeleNf ops env ctx.names ctx.nP (ctx.hiAt prog.length) fuel base nF j cur
        = .ok (nds, res) :=
  posD_nfOk h

/-- **A recorded frame constructor is `nestTeleNf`'s, read back**: the
entry `FrameRec` records for a derived constructor telescope is
`nestCtorNf` of what `nestTeleNf` computes on the constructor's
instantiated type (the frame's walk input), at the frame's hole range. -/
theorem FrameRec.entry_nestTeleNf {tbl : List NestCtorNf} {prog : List NestHole}
    {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    (h : FrameRec ops env ctx tbl prog us ds grp)
    {ctors : List (ConstantVal × Nat)} (hc : groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    {x : ConstantVal × Nat} (hx : x ∈ ctors) {crest : Expr} {ks : List PosKind}
    {nds : List (Expr × BinderMeta)} {cur : Expr} {ts' : List PosTree}
    (hcr : instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts
      (grpSub us (ctx.hiAt prog.length) grp)) = some crest)
    (hd : PosD ops env ctx (.tele ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
      (ctx.hiAt prog.length + grp.length) x.2 0 crest ks nds cur) ts') :
    ∃ F, ∀ fuel, F ≤ fuel →
      (∃ nds' cur', nestTeleNf ops env ctx.names ctx.nP
          (ctx.hiAt ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog).length)
          fuel (ctx.hiAt prog.length + grp.length) x.2 0 crest = .ok (nds', cur') ∧
        nestCtorNf ctx ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
          (ctx.hiAt prog.length + grp.length) us ds x.1 nds' cur' ∈ tbl) := by
  obtain ⟨F, hF⟩ := hd.tele_nestTeleNf
  exact ⟨F, fun fuel hf => ⟨nds, cur, hF fuel hf, h.entry hc hx hcr hd⟩⟩

end ConLeche
