module

public import ConLeche.Verify.Inductives.ClassGenScope
public import ConLeche.Verify.Inductives.NestScope
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Abstract
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Cached.NestPosC
import ConLeche.Verify.Cached.Erase

public section

/-!
# The positivity check's recorded normal forms are scoped over the parameters

Every entry the positivity check records (K.53′, `NestState.ctorNfs`,
pushed by `nestCtors` as `nestCtorNf`) is a walked constructor telescope
closed over its fields and READ BACK — every hole replaced by the
application it stands for (`nestHoleImg`) — so only the block's parameter
variables `0 ..< nP` stay free, and no bound variable is loose (`ScB nP`).  The generated recursor
stage reads a constructor's WALKED telescope off such an entry
(`ClassCtor.tyN`), so the generator's closedness (`ClassGenScoped.tyN`)
rests on it.

This is a state invariant of the FUELED walk (`NfStScoped`): every
recorded entry is scoped.  It is kept by every stage of the walk
(`nestPos_nfScoped`, `nestRoot_nfScoped`, `nestSeeds_nfScoped`) under any
`ops` whose whnf keeps terms scoped and bvar-closed, at a context whose
stored constants are closed (`NestCtxOk`, `NestCtxB`).  At the install:
the positivity stage's final state (`checkBlockPositivity_nfScoped`).
-/

namespace ConLeche

open Expr

/-! ## The invariant -/

/-- The context's stored constants have no loose bound variable (the
bvar half of `NestCtxOk`). -/
@[expose] def NestCtxB (ctx : NestCtx) : Prop :=
  ∀ n ci, ctx.find? n = some ci → ci.toConstantVal.type.looseBVarsBounded 0 = true

/-- **The walk's state, scoped**: every recorded constructor normal form
(K.53′) is scoped over the `nP` parameters. -/
@[expose] def NfStScoped (nP : Nat) (st : NestState) : Prop :=
  ∀ e ∈ st.ctorNfs.toList, ScB nP e.ty

theorem nfStScoped_empty (nP : Nat) : NfStScoped nP {} :=
  fun _ h => by simp at h

/-- **The frames are scoped**: every frame's parameters are scoped at the
depth of the frames outside it. -/
@[expose] def ProgScB (ctx : NestCtx) : List NestHole → Prop
  | [] => True
  | h :: prog => (∀ x ∈ h.key.ds, ScB (ctx.hiAt prog.length) x) ∧ ProgScB ctx prog

/-- A walk step's contract: at a scoped input, scoped frames and a scoped
state, the state stays scoped and the normal form is scoped where the
input is. -/
@[expose] def RecNf (ctx : NestCtx)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)) :
    Prop :=
  ∀ (prog : List NestHole) (dep kb : Nat) (e : Expr) (st : NestState) (k : NestFieldKind)
    (nf : Expr) (st' : NestState),
    rec prog dep kb e st = .ok (k, nf, st') → ScB dep e → ProgScB ctx prog →
    NfStScoped ctx.nP st → NfStScoped ctx.nP st' ∧ ScB dep nf

/-- Frames pushed at one key scoped at the current depth keep the frames
scoped. -/
theorem ProgScB.push {ctx : NestCtx} {prog : List NestHole} (hp : ProgScB ctx prog)
    {ds : List Expr} (hds : ∀ x ∈ ds, ScB (ctx.hiAt prog.length) x) :
    ∀ l : List NestHole, (∀ h ∈ l, h.key.ds = ds) → ProgScB ctx (l ++ prog)
  | [], _ => hp
  | h :: l, hl => by
    refine ⟨fun x hx => ?_, ProgScB.push hp hds l fun h' hh' => hl h' (List.mem_cons_of_mem _ hh')⟩
    rw [hl h List.mem_cons_self] at hx
    exact (hds x hx).mono (by simp [NestCtx.hiAt])

/-! ## Closed pieces -/

theorem ScB.of_closed {e : Expr} (hf : e.hasFvar = false) (hb : e.looseBVarsBounded 0 = true)
    (d : Nat) : ScB d e :=
  ⟨WScoped.of_not_hasFvar hf, hb⟩

section Ctx

variable {ctx : NestCtx}

theorem nestContainer_scb (hc : NestCtxOk ctx) (hb : NestCtxB ctx) {C : Name}
    {q : Nat × List (ConstantVal × Nat)} (h : nestContainer ctx C = some q) :
    ∀ x ∈ q.2, ScB 0 x.1.type := by
  obtain ⟨nP, L⟩ := q
  intro x hx
  obtain ⟨n, nPc, hf⟩ := nestContainer_mem h x hx
  exact ScB.of_closed (hc _ _ hf) (hb _ _ hf) 0

/-- The container's type former at the key (its hole's type) is scoped
where the key's parameters are. -/
theorem nestInstType_scb (hc : NestCtxOk ctx) (hb : NestCtxB ctx) {hi d : Nat} {key : NestKey}
    {nI : Nat} {cty : Expr} (h : nestInstType (m := CheckM) ctx hi key = .ok (nI, cty))
    (hds : ∀ x ∈ key.ds, ScB d x) : ScB d cty := by
  obtain ⟨cvC, caps, hf, -, hcty, -⟩ := nestInstType_inv h
  refine ScB.of_instPisWith hcty (ScB.of_closed ?_ ?_ d) hds
  · rw [Expr.hasFvar_instantiateLevelParams]; exact hc _ _ hf
  · rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb _ _ hf

theorem nestGrowGroup_scb (hc : NestCtxOk ctx) (hb : NestCtxB ctx) {hi d : Nat}
    {us : List Level} {ds : List Expr} {cs : List Name} {grp grp' : List (Name × Expr)}
    (h : nestGrowGroup (m := CheckM) ctx hi us ds cs grp = .ok grp')
    (hds : ∀ x ∈ ds, ScB d x)
    (hg : ∀ x ∈ grp, ScB d x.2) : ∀ x ∈ grp', ScB d x.2 := by
  obtain ⟨ext, rfl, -, hext⟩ := nestGrowGroup_inv' (ctx := ctx) cs grp grp' h
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hg x hx
  · obtain ⟨nI, hnI⟩ := hext x hx
    exact nestInstType_scb hc hb hnI hds

theorem nestGroupCtors_scb (hc : NestCtxOk ctx) (hb : NestCtxB ctx) {nPc : Nat} :
    ∀ (cs : List Name) (ctors : List (ConstantVal × Nat)),
      nestGroupCtors (m := CheckM) ctx nPc cs = .ok ctors → ∀ x ∈ ctors, ScB 0 x.1.type
  | [], ctors, h => by
    simp only [nestGroupCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact fun _ h => nomatch h
  | c :: cs, ctors, h => by
    simp only [nestGroupCtors, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i q hq
    have hq' := unwrapOr_ok hq
    obtain ⟨nP', L⟩ := q
    dsimp only at h
    split at h
    · split at h
      · simp at h
      rename_i rest hr
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hrest := nestGroupCtors_scb hc hb cs rest hr
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact nestContainer_scb hc hb hq' x hx
      · exact hrest x hx
    · simp [throw, throwThe, MonadExceptOf.throw] at h

end Ctx

/-! ## The recorded entry, read back -/

/-- Replacing every variable in `[n, D)` by a term scoped at `n`, and
none below `n`, moves a term scoped at `D` to `n`. -/
theorem WScoped.replaceFVars_lower {g : Nat → Option Expr} {D n : Nat}
    (hlo : ∀ i, i < n → g i = none)
    (hhi : ∀ i, n ≤ i → i < D → ∃ r, g i = some r ∧ WScoped n r) :
    ∀ (e : Expr), WScoped D e → WScoped n (e.replaceFVars g) := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro hw
    simp only [WScoped] at hw
    simp only [Expr.replaceFVars]
    by_cases hin : i < n
    · rw [hlo i hin]; simp only [Option.getD_none, WScoped]; exact ⟨hin, hw.2⟩
    · obtain ⟨r, hr, hwr⟩ := hhi i (by omega) hw.1
      rw [hr]; exact hwr
  | app a b iha ihb =>
    intro hw; unfold WScoped at hw; simp only [Expr.replaceFVars]; unfold WScoped
    exact ⟨iha hw.1, ihb hw.2⟩
  | lam ty b m iht ihb =>
    intro hw; unfold WScoped at hw; simp only [Expr.replaceFVars]; unfold WScoped
    exact ⟨iht hw.1, ihb hw.2⟩
  | forallE ty b m iht ihb =>
    intro hw; unfold WScoped at hw; simp only [Expr.replaceFVars]; unfold WScoped
    exact ⟨iht hw.1, ihb hw.2⟩
  | letE ty v b iht ihv ihb =>
    intro hw; unfold WScoped at hw; simp only [Expr.replaceFVars]; unfold WScoped
    exact ⟨iht hw.1, ihv hw.2.1, ihb hw.2.2⟩
  | proj s i sub ih =>
    intro hw; unfold WScoped at hw; simp only [Expr.replaceFVars]; unfold WScoped; exact ih hw
  | _ => intro _; simp [Expr.replaceFVars, WScoped]

/-- Below the frames' top, every hole has a read-back. -/
theorem nestHoleImg_isSome {ctx : NestCtx} {i : Nat} (hlo : ctx.nP ≤ i) :
    ∀ prog : List NestHole, i < ctx.hiAt prog.length → ∃ r, nestHoleImg ctx prog i = some r
  | [], hhi => by
    simp only [nestHoleImg]; rw [if_pos ⟨hlo, hhi⟩]; exact ⟨_, rfl⟩
  | h :: prog, hhi => by
    simp only [nestHoleImg]
    split
    · exact ⟨_, rfl⟩
    · rename_i hne
      exact nestHoleImg_isSome hlo prog (by
        simp only [NestCtx.hiAt, List.length_cons] at hhi hne ⊢; omega)

/-- **A read-back is scoped over the parameters**, and so is every term
scoped at the frames' depth once its holes are read back. -/
theorem nestHoleImg_scb {ctx : NestCtx} (hpar : ∀ x ∈ ctx.params, ScB ctx.nP x) :
    ∀ prog : List NestHole, ProgScB ctx prog →
      (∀ i r, nestHoleImg ctx prog i = some r → ScB ctx.nP r) ∧
      ∀ t, ScB (ctx.hiAt prog.length) t → ScB ctx.nP (t.replaceFVars (nestHoleImg ctx prog))
  | prog, hp => by
    have himg : ∀ i r, nestHoleImg ctx prog i = some r → ScB ctx.nP r := by
      cases prog with
      | nil =>
        intro i r h
        simp only [nestHoleImg] at h
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact ScB.mkAppN ⟨by simp [WScoped], rfl⟩ hpar
        · exact nomatch h
      | cons hd prog =>
        obtain ⟨hds, hp'⟩ := hp
        have ih := nestHoleImg_scb hpar prog hp'
        intro i r h
        simp only [nestHoleImg] at h
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          refine ScB.mkAppN ⟨by simp [WScoped], rfl⟩ fun x hx => ?_
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          exact ih.2 y (hds y hy)
        · exact ih.1 i r h
    refine ⟨himg, fun t ht => ⟨WScoped.replaceFVars_lower (D := ctx.hiAt prog.length)
      (fun i hi => nestHoleImg_lt_nP (prog := prog) hi) (fun i hlo hhi => ?_) t ht.1,
      looseBVarsBounded_replaceFVars (fun i r hr => (himg i r hr).2) t 0 ht.2⟩⟩
    obtain ⟨r, hr⟩ := nestHoleImg_isSome hlo prog hhi
    exact ⟨r, hr, (himg i r hr).1⟩
termination_by prog => prog.length

/-- **A frame's crest is scoped** where its key's parameters and its
holes are (a closed stored constructor type). -/
theorem ScB.of_nestCrest {names : List Name} {us : List Level} {ds holes : List Expr}
    {d : Nat} {cty crest : Expr} (hcty : ScB 0 cty) (hlen : names.length ≤ holes.length)
    (hds : ∀ x ∈ ds ++ holes, ScB d x) (h : nestCrest names us ds holes cty = some crest) :
    ScB d crest := by
  refine ⟨WScoped_nestCrest (ScB.closed hcty).1 hlen (fun x hx => (hds x hx).1) h, ?_⟩
  unfold nestCrest at h
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp h
  unfold nestCanonCrest at hA
  obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp hA
  have hBb : B.looseBVarsBounded 0 = true :=
    (ScB.of_instPisWith (d := ds.length) hB (hcty.mono (Nat.zero_le _)) (fun a ha => by
      simp only [nestPhs, List.mem_map, List.mem_range] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact ScB.fvar hi ⟨by simp [WScoped], rfl⟩)).2
  refine looseBVarsBounded_replaceFVars (fun i r hr => ?_) _ 0
    (looseBVarsBounded_replaceApps (fun c v r hr => ?_) _ 0 hBb)
  · unfold nestKeyMap at hr
    split at hr
    · exact (hds r (List.mem_append_left _ (List.mem_of_getElem? hr))).2
    · exact (hds r (List.mem_append_right _ (List.mem_of_getElem? hr))).2
  · obtain ⟨m, -, -, -, rfl⟩ := nestCanonSub_some hr
    rfl

/-! ## The walk -/

section Walk

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

theorem nestFields_nfScoped
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    (hrec : RecNf ctx rec) (prog : List NestHole) (hp : ProgScB ctx prog) (base : Nat)
    (err : CheckError) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) (ks : List NestFieldKind)
      (nds : List (Expr × BinderMeta)) (res : Expr) (st' : NestState),
      nestFields rec prog base err nF j cur st = .ok (ks, nds, res, st') →
      ScB (base + j) cur → NfStScoped ctx.nP st →
      NfStScoped ctx.nP st' ∧
        (∀ (i : Nat) (nd : Expr × BinderMeta), nds[i]? = some nd → ScB (base + j + i) nd.1) ∧
        ScB (base + j + nds.length) res := by
  intro nF
  induction nF with
  | zero =>
    intro j cur st ks nds res st' h hws hst
    simp only [nestFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨hst, fun _ _ h => by simp at h, by simpa using hws⟩
  | succ nF ih =>
    intro j cur st ks nds res st' h hws hst
    unfold nestFields at h
    split at h
    · rename_i a b bm
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      rename_i r₁ hr₁
      obtain ⟨k₁, nd₁, st₁⟩ := r₁
      simp only at h
      obtain ⟨hw, hbd⟩ := hws
      simp only [WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbd
      obtain ⟨hst₁, hnd₁⟩ := hrec prog (base + j) 0 a st k₁ nd₁ st₁ hr₁ ⟨hw.1, hbd.1⟩ hp hst
      split at h
      · simp at h
      rename_i r₂ hr₂
      obtain ⟨ks₂, nds₂, res₂, st₂⟩ := r₂
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hws' : ScB (base + (j + 1)) (b.instantiate1 (.fvar (base + j) a)) := by
        rw [show base + (j + 1) = base + j + 1 by omega]
        exact ⟨WScoped.instantiate1 hw.1 0 hw.2,
          looseBVarsBounded_instantiate1 (d := base + j) (ty := a) b 0 hbd.2⟩
      obtain ⟨hst₂, hnds, hres⟩ := ih (j + 1) _ st₁ ks₂ nds₂ res₂ st₂ hr₂ hws' hst₁
      refine ⟨hst₂, fun i x hx => ?_, by
        simp only [List.length_cons]
        rw [show base + j + (nds₂.length + 1) = base + (j + 1) + nds₂.length by omega]
        exact hres⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx; simpa using hnd₁
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        have := hnds i x hx
        rwa [show base + (j + 1) + i = base + j + (i + 1) by omega] at this
    · simp at h

/-- **A frame's constructors keep the state scoped**, and record scoped
entries: at the walk's depth `hi = hiAt |prog|`, at scoped parameters
and a scoped substitution. -/
theorem nestCtors_nfScoped
    {recC : Expr → List NestHole → Nat → Nat → Expr → NestState →
      CheckM (NestFieldKind × Expr × NestState)}
    (hrec : ∀ x, RecNf ctx (recC x)) {prog : List NestHole} {hi : Nat} {us : List Level}
    {ds : List Expr} {names : List Name} {holes : List Expr}
    (hpar : ∀ x ∈ ctx.params, ScB ctx.nP x) (hp : ProgScB ctx prog)
    (hhi : hi = ctx.hiAt prog.length) (hds : ∀ x ∈ ds, ScB hi x)
    (hholes : ∀ x ∈ holes, ScB hi x) (hlen : names.length ≤ holes.length) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState) (os : List (List NestFieldKind × Expr))
      (st' : NestState),
      nestCtors ctx ops env recC prog hi us ds names holes cs st = .ok (os, st') →
      (∀ x ∈ cs, ScB 0 x.1.type) → NfStScoped ctx.nP st →
      NfStScoped ctx.nP st' ∧ ∀ o ∈ os, ScB hi o.2 := by
  intro cs
  induction cs with
  | nil =>
    intro st os st' h _ hst
    simp only [nestCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hst, fun _ h => nomatch h⟩
  | cons x cs ih =>
    intro st os st' h hcl hst
    obtain ⟨cv, nF⟩ := x
    simp only [nestCtors, bind, Except.bind] at h
    have hnd : Name.nodup cv.levelParams = true := by
      rcases hb : Name.nodup cv.levelParams
      · simp [hb, throw, throwThe, MonadExceptOf.throw] at h
      · rfl
    rw [if_pos hnd] at h
    split at h
    · simp at h
    rename_i crest hcrest
    have hcrest' := unwrapOr_ok hcrest
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨ks, nds, cur, st₁⟩ := r
    have hcv : ScB 0 cv.type := hcl _ List.mem_cons_self
    have hws : ScB (hi + 0) crest := by
      rw [Nat.add_zero]
      refine ScB.of_nestCrest ⟨WScoped.of_not_hasFvar ?_, ?_⟩ hlen
        (fun x hx => (List.mem_append.mp hx).elim (hds x) (hholes x)) hcrest'
      · rw [Expr.hasFvar_instantiateLevelParams]; exact (ScB.closed hcv).1
      · rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hcv.2
    obtain ⟨hst₁, hnds, hcur⟩ := nestFields_nfScoped (hrec crest) prog hp hi _ nF 0 crest st ks
      nds cur st₁ hr hws hst
    have hN : ScB hi (closeTelescope nds hi cur) :=
      ScB.of_closeTelescope (fun k nd hk => by simpa using hnds k nd hk) (by simpa using hcur)
    dsimp only at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · split at h
      · simp at h
      rename_i r₂ hr₂
      obtain ⟨os₂, st₂⟩ := r₂
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hst₁' : NfStScoped ctx.nP
          { st₁ with ctorNfs := st₁.ctorNfs.push (nestCtorNf ctx prog hi us ds cv nds cur) } := by
        intro e he
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hst₁ e he
        · subst hhi
          exact (nestHoleImg_scb hpar prog hp).2 _ hN
      obtain ⟨hst₂, hos⟩ := ih _ os₂ st₂ hr₂ (fun x hx => hcl x (List.mem_cons_of_mem _ hx))
        hst₁'
      refine ⟨hst₂, fun o ho => ?_⟩
      rcases List.mem_cons.mp ho with rfl | ho
      · exact hN
      · exact hos o ho
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem frameHole_scb {grp : List (Name × Expr)} {hi : Nat} (hg : ∀ x ∈ grp, ScB hi x.2) :
    ∀ e ∈ (grp.mapIdx fun i (x : Name × Expr) => Expr.fvar (hi + i) x.2),
      ScB (hi + grp.length) e := by
  intro e hm
  obtain ⟨i, hi', heq⟩ := List.mem_mapIdx.mp hm
  subst heq
  exact ScB.fvar (by omega) ((hg _ (List.getElem_mem hi')).mono (by omega))

variable {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}

theorem nestFrame_nfScoped (hc : NestCtxOk ctx) (hb : NestCtxB ctx) (hrec : RecNf ctx rec)
    (hpar : ∀ x ∈ ctx.params, ScB ctx.nP x)
    {prog : List NestHole} (hp : ProgScB ctx prog) {hi : Nat} {us : List Level} {ds : List Expr}
    {nPc : Nat} (hhi : hi = ctx.hiAt prog.length) (hds : ∀ x ∈ ds, ScB hi x)
    {grp : List (Name × Expr)} (hg : ∀ x ∈ grp, ScB hi x.2) {st st' : NestState}
    (h : nestFrame ctx ops env rec prog hi us ds nPc grp st = .ok st')
    (hst : NfStScoped ctx.nP st) : NfStScoped ctx.nP st' := by
  simp only [nestFrame, bind, Except.bind] at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i ctors hgc
  have hcl := nestGroupCtors_scb hc hb _ ctors hgc
  split at h
  · simp at h
  rename_i v' hv'
  obtain ⟨os, st₂⟩ := v'
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hp' : ProgScB ctx ((grp.mapIdx fun _ (c, _) =>
      ({ key := ⟨c, us, ds⟩, base := hi } : NestHole)).reverse ++ prog) :=
    ProgScB.push hp (by subst hhi; exact hds) _ (fun h hh => by
      rw [List.mem_reverse] at hh
      obtain ⟨i, hi', rfl⟩ := List.mem_mapIdx.mp hh
      rfl)
  refine (nestCtors_nfScoped (fun _ => hrec) hpar hp' ?_ (fun x hx => (hds x hx).mono (by omega))
    (frameHole_scb hg) (by simp) ctors st os st₂ hv' hcl hst).1
  subst hhi; simp [NestCtx.hiAt]; omega

theorem nestContNew_nfScoped (hc : NestCtxOk ctx) (hb : NestCtxB ctx) (hrec : RecNf ctx rec)
    (hpar : ∀ x ∈ ctx.params, ScB ctx.nP x)
    {prog : List NestHole} (hp : ProgScB ctx prog) {kb : Nat} {n : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat}
    (hds : ∀ x ∈ ds, ScB (ctx.hiAt prog.length) x) {cty : Expr}
    (hcty : ∀ d, (∀ x ∈ ds, ScB d x) → ScB d cty)
    {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestContNew ctx ops env rec prog kb n us ds nPc cty st = .ok (k, st'))
    (hst : NfStScoped ctx.nP st) : NfStScoped ctx.nP st' := by
  have hdsw : ∀ x ∈ ds, ScB (ctx.hiAt (nestWalkStack ctx prog ds).length) x := by
    unfold nestWalkStack; split
    · rename_i hfree
      intro x hx
      exact ⟨WScoped.of_fvarsBelow (hds x hx).1
        (Expr.fvarB_le (by simpa using List.all_eq_true.mp hfree x hx)), (hds x hx).2⟩
    · exact hds
  simp only [nestContNew, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i grp hgrow
  have hg := nestGrowGroup_scb hc hb hgrow hdsw (fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact hcty _ hdsw)
  have hpw : ProgScB ctx (nestWalkStack ctx prog ds) := by
    unfold nestWalkStack; split
    · trivial
    · exact hp
  split at h
  · simp at h
  rename_i st₁ hfr
  have hst₁ := nestFrame_nfScoped hc hb hrec hpar hpw rfl hdsw hg hfr hst
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact hst₁

theorem nestContKey_nfScoped (hc : NestCtxOk ctx) (hb : NestCtxB ctx) (hrec : RecNf ctx rec)
    (hpar : ∀ x ∈ ctx.params, ScB ctx.nP x)
    {prog : List NestHole} (hp : ProgScB ctx prog) {kb : Nat} {n : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat}
    (hds : ∀ x ∈ ds, ScB (ctx.hiAt prog.length) x) {cty : Expr}
    (hcty : ∀ d, (∀ x ∈ ds, ScB d x) → ScB d cty)
    {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestContKey ctx ops env rec prog kb n us ds nPc cty st = .ok (k, st'))
    (hst : NfStScoped ctx.nP st) : NfStScoped ctx.nP st' := by
  unfold nestContKey at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact hst
    · exact nestContNew_nfScoped hc hb hrec hpar hp hds hcty h hst

theorem nestCont_nfScoped (hc : NestCtxOk ctx) (hb : NestCtxB ctx) (hrec : RecNf ctx rec)
    (hpar : ∀ x ∈ ctx.params, ScB ctx.nP x)
    {prog : List NestHole} (hp : ProgScB ctx prog) {kb : Nat} {n : Name} {us : List Level}
    {args : List Expr} {dep : Nat}
    (hargs : ∀ a ∈ args, ScB dep a) {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestCont ctx ops env rec prog kb n us args st = .ok (k, st'))
    (hst : NfStScoped ctx.nP st) : NfStScoped ctx.nP st' := by
  obtain ⟨nPc, L, -, -, -, -, hdsok, nI, cty, hnI, -, hkey⟩ := nestCont_inv h
  have hdsok' : ∀ x ∈ args.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length := by
    simpa using hdsok
  exact nestContKey_nfScoped hc hb hrec hpar hp
    (fun x hx => ⟨WScoped.of_fvarsBelow (hargs x (List.mem_of_mem_take hx)).1
      (Expr.fvarB_le (hdsok' x hx).2), (hargs x (List.mem_of_mem_take hx)).2⟩)
    (fun _ hd => nestInstType_scb hc hb hnI hd) hkey hst

/-- **The walk keeps the state scoped** and its normal form scoped where
its input is — at any fuel, under any `ops` whose whnf keeps terms scoped
and bvar-closed. -/
theorem nestPos_nfScoped (hc : NestCtxOk ctx) (hb : NestCtxB ctx)
    (hpar : ∀ x ∈ ctx.params, ScB ctx.nP x)
    (hwW : ∀ d e w, ops.whnf env d e = .ok w → WScoped d e → WScoped d w)
    (hwB : ∀ d e w, ops.whnf env d e = .ok w → e.looseBVarsBounded 0 = true →
      w.looseBVarsBounded 0 = true) :
    ∀ fuel, RecNf ctx (nestPos ops env ctx fuel)
  | 0 => by
    intro prog dep kb e st k nf st' hrun
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at hrun
  | fuel + 1 => by
    have ih := nestPos_nfScoped hc hb hpar hwW hwB fuel
    intro prog dep kb e st k nf st' hrun hws hp hst
    rw [nestPos] at hrun
    cases hw : ops.whnf env dep e with
    | error err => simp [hw, bind, Except.bind] at hrun
    | ok w =>
      simp only [hw, bind, Except.bind] at hrun
      have hwsw : ScB dep w := ⟨hwW dep e w hw hws.1, hwB dep e w hw hws.2⟩
      by_cases hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false
      · rw [if_pos (by simpa using hocc)] at hrun
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        exact ⟨hst, by split <;> assumption⟩
      rw [if_neg (by simpa using hocc)] at hrun
      split at hrun
      · -- `pi`
        rename_i a b bm
        by_cases ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true
        · rw [if_pos ha] at hrun
          simp [throw, throwThe, MonadExceptOf.throw] at hrun
        rw [if_neg ha] at hrun
        split at hrun
        · simp at hrun
        rename_i v hv
        obtain ⟨k₁, nb, st₁⟩ := v
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        obtain ⟨hW, hB⟩ := hwsw
        simp only [WScoped] at hW
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hB
        obtain ⟨hst₁, hnb⟩ := ih prog (dep + 1) (kb + 1) _ st k₁ nb _ hv
          ⟨WScoped.instantiate1 hW.1 0 hW.2,
            looseBVarsBounded_instantiate1 (d := dep) (ty := a) b 0 hB.2⟩ hp hst
        refine ⟨hst₁, ?_, ?_⟩
        · simp only [WScoped]; exact ⟨hW.1, WScoped.abstract1 0 hnb.1⟩
        · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
          exact ⟨hB.1, looseBVarsBounded_abstract1 _ 0 hnb.2⟩
      · -- a head applied to arguments
        split at hrun
        · -- a variable head
          split at hrun
          · split at hrun
            · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl, rfl⟩ := hrun
              exact ⟨hst, hwsw⟩
            · simp [throw, throwThe, MonadExceptOf.throw] at hrun
          · simp [throw, throwThe, MonadExceptOf.throw] at hrun
        · -- `contApp`
          split at hrun
          · simp [throw, throwThe, MonadExceptOf.throw] at hrun
          split at hrun
          · simp at hrun
          rename_i v hv
          obtain ⟨k₁, st₁⟩ := v
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl, rfl⟩ := hrun
          exact ⟨nestCont_nfScoped hc hb ih hpar hp (fun a ha => ScB.getAppArgs hwsw a ha) hv hst,
            hwsw⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun

/-- **The root frame keeps the state scoped.** -/
theorem nestRoot_nfScoped (hc : NestCtxOk ctx) (hb : NestCtxB ctx)
    (hwW : ∀ d e w, ops.whnf env d e = .ok w → WScoped d e → WScoped d w)
    (hwB : ∀ d e w, ops.whnf env d e = .ok w → e.looseBVarsBounded 0 = true →
      w.looseBVarsBounded 0 = true)
    {holes : List Expr} (hh : nestHoles ctx = some holes)
    (hpar : ∀ x ∈ ctx.params, ScB ctx.nP x) :
    ∀ (css : List (List (ConstantVal × Nat))) (st : NestState)
      (outs : List (List (List NestFieldKind × Expr))) (st' : NestState),
      nestRoot ops env ctx holes css st = .ok (outs, st') →
      (∀ cs ∈ css, ∀ x ∈ cs, ScB 0 x.1.type) → NfStScoped ctx.nP st →
      NfStScoped ctx.nP st'
  | [], st, outs, st', h, _, hst => by
    simp only [nestRoot, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hst
  | cs₀ :: css, st, outs, st', h, hcl, hst => by
    simp only [nestRoot, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i r₁ hr₁
    obtain ⟨o, st₁⟩ := r₁
    simp only at h
    split at h
    · simp at h
    rename_i r₂ hr₂
    obtain ⟨os₂, st₂⟩ := r₂
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have hholes : ∀ x ∈ holes, ScB (ctx.hiAt 0) x := by
      intro x hx
      obtain ⟨hw, i, ty, rfl⟩ := nestHoles_ok hc (fun y hy => (hpar y hy).1) hh x hx
      exact ⟨hw, rfl⟩
    obtain ⟨hst₁, -⟩ := nestCtors_nfScoped
      (fun x => nestPos_nfScoped hc hb hpar hwW hwB (whnfWalkFuel x))
      (prog := []) hpar trivial rfl (fun x hx => (hpar x hx).mono (by simp [NestCtx.hiAt]))
      hholes (by rw [nestHoles_length hh]; exact Nat.le_refl _) cs₀ st o st₁ hr₁
      (hcl cs₀ List.mem_cons_self) hst
    exact nestRoot_nfScoped hc hb hwW hwB hh hpar css st₁ os₂ st₂ hr₂
      (fun cs hcs => hcl cs (List.mem_cons_of_mem _ hcs)) hst₁

/-- **The seeds keep the state scoped**, at seeds whose parameters are
scoped at the walk's root depth. -/
theorem nestSeeds_nfScoped (hc : NestCtxOk ctx) (hb : NestCtxB ctx)
    (hpar : ∀ x ∈ ctx.params, ScB ctx.nP x)
    (hwW : ∀ d e w, ops.whnf env d e = .ok w → WScoped d e → WScoped d w)
    (hwB : ∀ d e w, ops.whnf env d e = .ok w → e.looseBVarsBounded 0 = true →
      w.looseBVarsBounded 0 = true) :
    ∀ (ks : List (NestKey × Nat)) (st st' : NestState), nestSeeds ops env ctx ks st = .ok st' →
      (∀ s ∈ ks, ∀ x ∈ s.1.ds, ScB (ctx.hiAt 0) x) → NfStScoped ctx.nP st →
      NfStScoped ctx.nP st'
  | [], st, st', h, _, hst => by
    simp only [nestSeeds, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hst
  | (key, nPc) :: ks, st, st', h, hks, hst => by
    simp only [nestSeeds, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i ni hni
    obtain ⟨nI, cty⟩ := ni
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨k₁, st₁⟩ := r
    have hst₁ := nestContKey_nfScoped (prog := []) hc hb (nestPos_nfScoped hc hb hpar hwW hwB _)
      hpar trivial (fun x hx => hks _ List.mem_cons_self x hx)
      (fun _ hd => nestInstType_scb hc hb hni hd) hr hst
    exact nestSeeds_nfScoped hc hb hpar hwW hwB ks st₁ st' h
      (fun s hs => hks s (List.mem_cons_of_mem _ hs)) hst₁

end Walk

/-! ## At the install -/

/-- A block's walk context at a well-formed environment's lookups is
closed and bvar-closed. -/
theorem nestCtx_ok_of_envWF {env : Env} (henv : EnvWF env) (p : BlockShape) (fvsP : List Expr) :
    NestCtxOk (p.nestCtx fvsP env.find?) ∧
      NestCtxB (p.nestCtx fvsP env.find?) :=
  ⟨fun _ ci hf => (henv ci (List.mem_of_find?_eq_some hf)).1,
    fun _ ci hf => (henv ci (List.mem_of_find?_eq_some hf)).2.2.2.1⟩

/-- The canonical parameters (a closed former's opened telescope) are
scoped over the parameters. -/
theorem nestCtx_params_scb {p : BlockShape} {T rest : Expr} {fvsP : List Expr}
    {find? : Name → Option ConstantInfo}
    (hT : ScB 0 T) (hop : openPisAtFvars p.nP T 0 = some (fvsP, rest)) :
    ∀ x ∈ (p.nestCtx fvsP find?).params,
      ScB (p.nestCtx fvsP find?).nP x := by
  intro x hx
  obtain ⟨hl, hfvs, -⟩ := ScB.openPis hop hT
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨ty, hxe, hty⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
  rw [hxe]
  have : k < p.nP := by
    have : k < fvsP.length := hk
    omega
  exact ScB.fvar (by simp [BlockShape.nestCtx]; omega) (by simpa using hty)

/-- **The positivity stage's final state is scoped**: every constructor
normal form the install's positivity check records is scoped over the
block's parameters. -/
theorem checkBlockPositivity_nfScoped {mode : CheckMode} {F : Nat} {env₁ : Env}
    (henv : EnvWF env₁) {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {pos : NestState}
    (hT : ∀ cv ∈ cvTas, ScB 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, ScB 0 c.1.type)
    (h : checkBlockPositivity (fueledOps mode F) env₁ env₁.find? pp cvTas ctorsAs
      = .ok (kinds, nfs, pos)) :
    NfStScoped pp.nP pos := by
  obtain ⟨cvTa0, fvsP, rest, holes, outs, h0, hop, hh, -, hroot, -⟩ := checkBlockPositivity_inv h
  obtain ⟨hc, hb⟩ := nestCtx_ok_of_envWF henv pp.toBlockShape fvsP
  exact nestRoot_nfScoped hc hb (fun d e w hw he => whnf_WScoped henv F hw he)
    (fun d e w hw he => whnf_looseBVars henv F hw he) hh
    (nestCtx_params_scb (hT cvTa0 (List.mem_of_mem_head? h0)) hop) ctorsAs {} outs pos hroot
    hct (nfStScoped_empty _)

end ConLeche
