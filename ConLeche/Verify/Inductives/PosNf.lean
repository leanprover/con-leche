module

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

/-! ## Rebuilding the walk's input from a class key

A reader holding a class key in the recursor's representation (the
walk's record read back: member holes to the members' constants,
`nestHoleConst ctx []`) rebuilds the walk's representation with the
walk's own member abstraction (`nestAbstract`).  On a key the walk
built — no member constant anywhere (M2′, fvar annotations included) and
every member-hole variable the walk's hole — this is the identity. -/

/-- Every member-hole variable of `x` (outside fvar annotations) is the
walk's hole for its member. -/
@[expose] def HolesCanonical (ctx : NestCtx) (holes : List Expr) : Expr → Prop
  | .fvar i ty => ctx.nP ≤ i → i < ctx.hiAt 0 → holes[i - ctx.nP]? = some (.fvar i ty)
  | .app f a => HolesCanonical ctx holes f ∧ HolesCanonical ctx holes a
  | .lam ty b _ | .forallE ty b _ => HolesCanonical ctx holes ty ∧ HolesCanonical ctx holes b
  | .letE ty v b =>
    HolesCanonical ctx holes ty ∧ HolesCanonical ctx holes v ∧ HolesCanonical ctx holes b
  | .proj _ _ e => HolesCanonical ctx holes e
  | _ => True

/-- `replaceConsts` leaves a term alone when its map answers `none` at
every constant name the term mentions (fvar annotations included). -/
theorem replaceConsts_eq_self_of_not_mentions {f : Name → List Level → Option Expr}
    {names : List Name} (hf : ∀ n us, names.contains n = false → f n us = none) :
    ∀ (e : Expr), e.mentionsAnyConst names = false → e.replaceConsts f = e := by
  intro e
  induction e with
  | bvar => intro _; rfl
  | sort => intro _; rfl
  | lit => intro _; rfl
  | const n us =>
    intro h
    simp only [Expr.mentionsAnyConst] at h
    simp [Expr.replaceConsts, hf n us h]
  | fvar i ty ih =>
    intro h
    simp only [Expr.mentionsAnyConst] at h
    simp [Expr.replaceConsts, ih h]
  | app a b iha ihb =>
    intro h
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp [Expr.replaceConsts, iha h.1, ihb h.2]
  | lam ty b m iht ihb =>
    intro h
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp [Expr.replaceConsts, iht h.1, ihb h.2]
  | forallE ty b m iht ihb =>
    intro h
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp [Expr.replaceConsts, iht h.1, ihb h.2]
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp [Expr.replaceConsts, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj s i e ih =>
    intro h
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp [Expr.replaceConsts, ih h.2]

/-- A name the list does not contain has no index. -/
theorem findIdx?_beq_none {names : List Name} {n : Name} (hn : names.contains n = false) :
    names.findIdx? (· == n) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  simp only [List.contains_eq_mem, decide_eq_false_iff_not] at hn
  rw [beq_eq_false_iff_ne]
  intro heq
  exact hn (heq ▸ hx)

/-- In a duplicate-free list, the `i`-th entry's index is `i`. -/
theorem findIdx?_beq_getElem : ∀ {names : List Name} (_ : names.Nodup) {i : Nat}
    (hi : i < names.length), names.findIdx? (· == names[i]) = some i
  | [], _, i, hi => by simp at hi
  | x :: xs, hnd, i, hi => by
    rw [List.nodup_cons] at hnd
    cases i with
    | zero =>
      rw [List.findIdx?_cons]
      simp
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      have hne : (x == xs[i]) = false := by
        simp only [beq_eq_false_iff_ne]
        intro heq
        exact hnd.1 (heq ▸ List.getElem_mem hi')
      rw [List.findIdx?_cons]
      simp only [List.getElem_cons_succ, hne]
      rw [findIdx?_beq_getElem hnd.2 hi']
      rfl

/-- **The walk's key, read back and re-abstracted, is the walk's key.** -/
theorem nestAbstract_readback {holes : List Expr} (hnd : ctx.names.Nodup) :
    ∀ (x : Expr), x.mentionsAnyConst ctx.names = false → HolesCanonical ctx holes x →
      nestAbstract ctx holes (x.replaceFVars (nestHoleConst ctx [])) = x := by
  intro x
  induction x with
  | bvar => intro _ _; rfl
  | sort => intro _ _; rfl
  | lit => intro _ _; rfl
  | const n us =>
    intro h _
    simp only [Expr.mentionsAnyConst] at h
    simp only [Expr.replaceFVars, nestAbstract, Expr.replaceConsts, findIdx?_beq_none h]
    split <;> rfl
  | fvar i ty _ =>
    intro h hc
    simp only [Expr.mentionsAnyConst] at h
    simp only [HolesCanonical] at hc
    by_cases hr : ctx.nP ≤ i ∧ i < ctx.hiAt 0
    · have hhole := hc hr.1 hr.2
      have hm : i - ctx.nP < ctx.names.length := by
        simp only [NestCtx.hiAt] at hr; omega
      have hget : ctx.names.getD (i - ctx.nP) .anonymous = ctx.names[i - ctx.nP] := by
        simp [List.getD, hm]
      simp only [Expr.replaceFVars, nestHoleConst, hr, and_self, if_true, Option.getD_some,
        nestAbstract, Expr.replaceConsts, hget, findIdx?_beq_getElem hnd hm, beq_self_eq_true,
        hhole]
    · have hnh : nestHoleConst ctx [] i = none := by
        simp only [nestHoleConst, hr, if_false, List.length_nil]
        simp
      simp only [Expr.replaceFVars, hnh, Option.getD_none, nestAbstract, Expr.replaceConsts]
      rw [replaceConsts_eq_self_of_not_mentions (names := ctx.names) ?_ ty h]
      intro n us hn
      simp only [findIdx?_beq_none hn]
      split <;> rfl
  | app a b iha ihb =>
    intro h hc
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [nestAbstract] at iha ihb ⊢
    simp only [Expr.replaceFVars, Expr.replaceConsts, iha h.1 hc.1, ihb h.2 hc.2]
  | lam ty b m iht ihb =>
    intro h hc
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [nestAbstract] at iht ihb ⊢
    simp only [Expr.replaceFVars, Expr.replaceConsts, iht h.1 hc.1, ihb h.2 hc.2]
  | forallE ty b m iht ihb =>
    intro h hc
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [nestAbstract] at iht ihb ⊢
    simp only [Expr.replaceFVars, Expr.replaceConsts, iht h.1 hc.1, ihb h.2 hc.2]
  | letE ty v b iht ihv ihb =>
    intro h hc
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [nestAbstract] at iht ihv ihb ⊢
    simp only [Expr.replaceFVars, Expr.replaceConsts, iht h.1.1 hc.1, ihv h.1.2 hc.2.1,
      ihb h.2 hc.2.2]
  | proj s i e ih =>
    intro h hc
    simp only [Expr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [nestAbstract] at ih ⊢
    simp only [Expr.replaceFVars, Expr.replaceConsts, ih h.2 hc]

end ConLeche
