module

public import ConLeche.Model.Inductives.ContSem
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Verify.Cached.Erase
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Semantics.Frame
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.InferSoundKit

public section

/-!
# The positivity derivation is monotone in the holes (lane POSDERIV)

Charter items 2–4, via the maintainer's ruling "use the positivity run,
via a declarative derivation" (2026-09-25): the operator's monotonicity
is proved by INDUCTION ON THE DERIVATION `PosD`
(`Verify/Inductives/PosDeriv.lean`), never on the run.  The run is read
once, by `nestPos_deriv`.

The motive `MonoJ` reads each judgment:

* `field` — the term's reading grows along every hole relation (the
  whnf step by `red_sound`; `const`, `pi`, `hole`, `frameHole` as the
  hole-monotonicity kit's case lemmas; a container instance by its
  frame's conclusion at the key's frames, `monoOn_of_famLe`);
* `tele` — every field grows under the earlier ones, the result read at
  the relation (`PiPosThen`);
* `ctors` — every constructor of the frame's group walked (`CtorWalked`);
* `frame` — the reached group's carriers grow between the key frames of
  each related pair, with the per-constructor hole-fit transfer
  (`frameIter`).

The container rules are the only place the coverage premise
(`ContCover`) is read: a field of a FLAT kind never meets one, so the
switch-off route needs no coverage.  A cache hit (`contHit`) reads its
frame's conclusion under the frames of its first walk, extended by
empty ones and seen at the block's own depth.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestKey NestHole NestState
  NestFieldKind CheckError instPisWith fueledOps PosD PosJ PosKind ProgScoped KeyD grpNews grpSub
  groupCtors)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Syntactic facts of the derivation -/

/-- The level parameters of every derived frame constructor are distinct. -/
theorem posD_ctors_nodup {ops : ConLeche.CheckerOps CheckM} {ctx : NestCtx} :
    ∀ {j : PosJ} {ts : List ConLeche.PosTree}, PosD ops env ctx j ts → match j with
      | .ctors _ _ _ _ _ cs => ∀ x ∈ cs, ConLeche.Name.nodup x.1.levelParams = true
      | _ => True := by
  intro j ts h
  induction h with
  | ctorsNil => intro x hx; exact nomatch hx
  | ctorsCons hnd _ _ _ _ _ _ _ _ _ ihr =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hnd
    · exact ihr x hx
  | _ => trivial

/-! ## The motive -/

section Motive

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat) (ctx : NestCtx) (F : Nat)

/-- **A frame's conclusion** (`frameIter`'s, and the group's well
formedness), at every recorded block holding the frame's head. -/
@[expose] def FrameMono (prog : List NestHole) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  ContCover mp ctx →
  ∀ {D : LfpDatum V}, D ∈ mp.lfpBlocks → ∀ {mm : Nat}, mm < D.k →
    D.member mm = (grp.headD default).1 →
  ∀ {lps : List Name},
    (∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = lps) →
    us.length = lps.length →
    (∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x ∧ x.looseBVarsBounded 0 = true) →
    ∀ {dsa : List AnnotTerm}, DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt prog.length) ds dsa →
    (D.params (Level.substFn φ lps us)).length = ds.length →
    ((∃ nP' L, ConLeche.nestContainer ctx (D.member mm) = some (nP', L) ∧ L ≠ []) ∨ lps.Nodup) →
    ∀ {Δh : List AnnotTerm} {R₀ : FrameRel V},
    HoleRel mp.base2 φ ctx prog (ctx.hiAt prog.length) Δh R₀ → Δh.length = ctx.hiAt prog.length →
    (∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt prog.length) Δh x) →
    (∀ x ∈ ds, Expr.LeavesBounded x) →
    (∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa (ctx.hiAt prog.length) ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa (ctx.hiAt prog.length) ρ')) →
    lps.Nodup ∧ GrpOk ctx D (ctx.hiAt prog.length) us ds grp ∧
    (∀ ρ ρ', R₀ ρ ρ' → ∀ c, InGrp D grp c →
      FamLe (D.idx (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ) c)
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ) c)
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ') c)) ∧
    ∀ ρ ρ', R₀ ρ ρ' → ∀ g, InGrp D grp g → ∀ t j fs,
      D.HFits (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ)
        (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa (ctx.hiAt prog.length) ρ)
          (keyFrame dsa (ctx.hiAt prog.length) ρ')) t g j fs →
      D.HFits (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ')
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ')) t g j fs

/-- **What a derivation proves** of its judgment's reading (see the
module docstring). -/
@[expose] def MonoJ : PosJ → Prop
  | .field prog dep _ e k _ =>
    (k.flat = false → ContCover mp ctx) →
    ctx.hiAt prog.length ≤ dep → Frame dep e →
    ∀ {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ dep Δa e → denoteMeta mp.base2.acval env φ dep e = some ea →
      Graded V Δa ea → HoleRel mp.base2 φ ctx prog dep Δa R → MonoOn R ea
  | .tele prog base nF j cur ks _ res =>
    ((∃ k ∈ ks, k.flat = false) → ContCover mp ctx) →
    ctx.hiAt prog.length ≤ base + j → Frame (base + j) cur →
    ∀ {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ (base + j) Δa cur → denoteMeta mp.base2.acval env φ (base + j) cur = some ca →
      Graded V Δa ca → HoleRel mp.base2 φ ctx prog (base + j) Δa R →
      PiPosThen (ResultAt mp.base2 φ ctx.nP (ctx.hiAt prog.length) (base + j + nF) res) nF R ca
  | .ctors prog hi us ds sub cs =>
    ContCover mp ctx → ctx.hiAt prog.length = hi →
    ∀ {Δ : List AnnotTerm} {R : FrameRel V}, HoleRel mp.base2 φ ctx prog hi Δ R →
    ∀ (Q : ConstantVal × Nat → Prop),
    (∀ (x : ConstantVal × Nat) (crest : Expr), Q x →
      instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
        = some crest →
      (∃ ty, ConLeche.inferTypeCore .verified env F hi crest = .ok ty) →
      ∃ ca, Frame hi crest ∧ CtxOkP mp.base2 φ hi Δ crest ∧
        denoteMeta mp.base2.acval env φ hi crest = some ca ∧ Graded V Δ ca) →
    (∀ x ∈ cs, Q x) → ∀ x ∈ cs, CtorWalked mp.base2 φ ctx hi us ds ds.length sub R x
  | .frame prog us ds grp => FrameMono mp φ ctx prog us ds grp
  | .syn _ _ => True

end Motive

variable {φ : Name → Nat}

/-! ## The container case's pieces -/

/-- An inductive the context finds has a constructor listing. -/
theorem nestContainer_of_find {ctx : NestCtx} {C : Name} {cv : ConstantVal} {caps : IndCaps}
    (h : ctx.find? C = some (.indInfo cv caps)) :
    ∃ nP L, ConLeche.nestContainer ctx C = some (nP, L) := by
  unfold ConLeche.nestContainer
  rw [h]
  dsimp only
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- **A recorded block's level parameters and parameter count**, read at
one of its members: off the member's first constructor's record, or — a
member WITHOUT constructors (lane RESTRICT-FIX) — off the recorded former
(`ContBlockOk.noCtors`). -/
theorem contBlock_facts {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx}
    (hcov : ContCover mp ctx) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k)
    {cv : ConstantVal} {caps : IndCaps} (hfc : env.find? (D.member mm) = some (.indInfo cv caps))
    {nPc : Nat} {L : List (ConstantVal × Nat)}
    (hq : ConLeche.nestContainer ctx (D.member mm) = some (nPc, L)) :
    ∃ lps : List Name,
      (∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
        cv.levelParams = lps) ∧
      (∀ ψ, (D.params ψ).length = nPc) ∧ cv.levelParams = lps ∧
      ((∃ L', ConLeche.nestContainer ctx (D.member mm) = some (nPc, L') ∧ L' ≠ []) ∨ lps.Nodup) := by
  have hblk := hcov.block D hD
  obtain ⟨nP', L', hL', hlenL', hfL'⟩ := hblk.ctors mm hmm
  rw [hq] at hL'
  obtain ⟨rfl, rfl⟩ : nPc = nP' ∧ L = L' := by simpa using hL'
  by_cases hLne : L = []
  · subst hLne
    obtain ⟨cv', caps', hf', hnd', hlen', hlps'⟩ := hblk.noCtors mm hmm nPc hq
    rw [hfc] at hf'
    obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
    exact ⟨cv.levelParams, hlps', hlen', rfl, Or.inr hnd'⟩
  · have h0 : 0 < L.length := by
      cases L with
      | nil => exact absurd rfl hLne
      | cons => simp
    obtain ⟨-, -, -, -, hrdC⟩ := mp.lfp_ok D hD
    obtain ⟨cv0, nPc0, nF0, hf0, -, hlpsC, -, -, _A, -, hread0⟩ :=
      hrdC mm hmm 0 (by rw [← hlenL']; exact h0)
    rw [hfL' 0 h0] at hf0
    obtain ⟨rfl, rfl, rfl⟩ : L[0].1 = cv0 ∧ nPc = nPc0 ∧ L[0].2 = nF0 := by
      simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at hf0
      exact ⟨hf0.1, hf0.2.1, hf0.2.2⟩
    have hcvl : cv.levelParams = L[0].1.levelParams := by
      obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC mm hmm
      rw [hfc] at hfm
      obtain ⟨rfl, rfl⟩ : cv = cvm ∧ caps = capsm := by simpa using hfm
      exact hlm
    exact ⟨L[0].1.levelParams, hlpsC, fun ψ => (hread0 ψ).1, hcvl, Or.inl ⟨L, hq, hLne⟩⟩


/-- The frame judgment's premises, read back. -/
theorem posD_frame_inv {ops : ConLeche.CheckerOps CheckM} {ctx : NestCtx} :
    ∀ {j : PosJ} {ts : List ConLeche.PosTree}, PosD ops env ctx j ts → match j with
      | .frame prog us ds grp => grp ≠ [] ∧
          (ctx.names.contains (grp.headD default).1 = false ∧
            (grp.headD default).1 ≠ ConLeche.quotName) ∧
          (∃ L, ConLeche.nestContainer ctx (grp.headD default).1 = some (ds.length, L)) ∧
          (∀ p ∈ grp, ∃ nI, ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
            ⟨p.1, us, ds⟩ = .ok (nI, p.2)) ∧
          ∀ p ∈ grp.tail, (ConLeche.nestBlockOf ctx (grp.headD default).1).contains p.1 = true
      | _ => True := by
  intro j ts h
  cases h with
  | frame hne hhd hhdC _ hinst hblk _ _ _ => exact ⟨hne, hhd, hhdC, hinst, hblk⟩
  | _ => trivial

/-- **The whnf step** of every field rule: the reduct reads as the term,
so it is enough to prove the reduct's reading monotone. -/
theorem mono_of_whnf {μ : ConLeche.CheckMode} {mp : EnvModelM V μ env}
    (hin : RulesInputs V mp.base2 φ) {F dep : Nat} {e w : Expr}
    (hw : (fueledOps .verified F).whnf env dep e = .ok w) (hfr : Frame dep e)
    {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa e) (hea : denoteMeta mp.base2.acval env φ dep e = some ea)
    (hgr : Graded V Δa ea) (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ')
    (k : Frame dep w → CtxOkP mp.base2 φ dep Δa w → ∀ wa,
      denoteMeta mp.base2.acval env φ dep w = some wa → Graded V Δa wa → MonoOn R wa) :
    MonoOn R ea := by
  have hw' : ConLeche.whnf .verified env F dep e = .ok w := hw
  obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ :=
    red_sound hin (ConLeche.Rules.whnf_bridge hw') hfr hC.toCtxOk hea hgr
  exact MonoOn.of_eqOn (Q := Sat V Δa) hdom (fun ρ hρ => heq ρ hρ)
    (k hfrw (hC.of_subset hsub) wa hwa hgw)

/-- The frame's constructors, listed and their level parameters distinct. -/
theorem posD_frame_ctors {ops : ConLeche.CheckerOps CheckM} {ctx : NestCtx} :
    ∀ {j : PosJ} {ts : List ConLeche.PosTree}, PosD ops env ctx j ts → match j with
      | .frame _ _ ds grp => ∃ ctors, groupCtors ctx ds.length (grp.map (·.1)) = some ctors ∧
          ∀ x ∈ ctors, ConLeche.Name.nodup x.1.levelParams = true
      | _ => True := by
  intro j ts h
  cases h with
  | frame _ _ _ _ _ _ _ hctors _ hwalk => exact ⟨_, hctors, posD_ctors_nodup hwalk⟩
  | _ => trivial

/-- **The level parameters of a frame's block are distinct**: the head's
first constructor's check (a derived frame constructor), or — a head
without constructors — the caller's. -/
theorem frame_lps_nodup {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx}
    (hcov : ContCover mp ctx) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat}
    (hmm : mm < D.k) {lps : List Name}
    (hlps : ∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
    {nPc : Nat} {grp : List (Name × Expr)} (hhead : D.member mm ∈ grp.map (·.1))
    {ctors : List (ConstantVal × Nat)} (hctors : groupCtors ctx nPc (grp.map (·.1)) = some ctors)
    (hnodup : ∀ x ∈ ctors, ConLeche.Name.nodup x.1.levelParams = true)
    (hnL : (∃ nP' L, ConLeche.nestContainer ctx (D.member mm) = some (nP', L) ∧ L ≠ []) ∨
      lps.Nodup) : lps.Nodup := by
  rcases hnL with ⟨nP', L, hL, hLne⟩ | hnd0
  · have hblkD := hcov.block D hD
    obtain ⟨-, hctorsAll⟩ := ConLeche.groupCtors_spec hctors
    obtain ⟨nP'', L', hL', -, hsub⟩ := hctorsAll (D.member mm) hhead
    rw [hL] at hL'
    obtain ⟨rfl, rfl⟩ : nP' = nP'' ∧ L = L' := by simpa using hL'
    obtain ⟨nP₃, L₃, hL₃, hlen₃, hfL₃⟩ := hblkD.ctors mm hmm
    rw [hL] at hL₃
    obtain ⟨rfl, rfl⟩ : nP' = nP₃ ∧ L = L₃ := by simpa using hL₃
    have h0 : 0 < L.length := by
      cases L with
      | nil => exact absurd rfl hLne
      | cons => simp
    have hndx := nodup_of_nameNodup (hnodup _ (hsub _ (List.getElem_mem h0)))
    rw [ctor_lps mp hD hlps hmm (by rw [← hlen₃]; exact h0) (hfL₃ 0 h0)] at hndx
    exact hndx
  · exact hnd0

/-! ## The frame -/

/-- **A frame's conclusion from its derivation**: the group well formed
(the head in the block, the rest in the head's recorded block), the
level parameters distinct (the head's first constructor's check, or its
recorded former), and `frameIter` along the walked constructors. -/
theorem frame_mono {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} {F : Nat} {prog : List NestHole}
    {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    {ctors : List (ConstantVal × Nat)} (hne : grp ≠ []) (hnd : (grp.map (·.1)).Nodup)
    (hinst : ∀ p ∈ grp, ∃ nI, ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
      ⟨p.1, us, ds⟩ = .ok (nI, p.2))
    (hblk : ∀ p ∈ grp.tail, (ConLeche.nestBlockOf ctx (grp.headD default).1).contains p.1 = true)
    (hctors : groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    {ts : List ConLeche.PosTree}
    (hwalkD : PosD (fueledOps .verified F) env ctx
      (.ctors ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
        (ctx.hiAt prog.length + grp.length) us ds (grpSub us (ctx.hiAt prog.length) grp) ctors) ts)
    (ih : MonoJ mp φ ctx F
      (.ctors ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
        (ctx.hiAt prog.length + grp.length) us ds (grpSub us (ctx.hiAt prog.length) grp) ctors)) :
    FrameMono mp φ ctx prog us ds grp := by
  intro hcov D hD mm hmm hhead lps hlps hul hds dsa hdsa hlenP hnL Δh R₀ hR₀ hΔ hCds hLds hfit
  have hblkD := hcov.block D hD
  have hkN := lfp_namesLen mp hD
  obtain ⟨p₀, ps₀, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.headD_cons] at hhead hblk
  -- the group is well formed
  have hg : GrpOk ctx D (ctx.hiAt prog.length) us ds (p₀ :: ps₀) := by
    refine ⟨hne, hnd, fun p hp => ⟨?_, hinst p hp⟩⟩
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨mm, hmm, hhead.symm⟩
    · have hin' := hblk p (by simpa using hp')
      obtain ⟨cv₀, caps₀, hf₀, -⟩ := hlps mm hmm
      have hblkOf : ConLeche.nestBlockOf ctx p₀.1 = D.names := by
        unfold ConLeche.nestBlockOf
        rw [← hhead, hcov.find, hf₀]
        exact hblkD.all mm hmm cv₀ caps₀ hf₀
      rw [hblkOf, List.contains_iff_mem] at hin'
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hin'
      refine ⟨i, by omega, ?_⟩
      unfold LfpDatum.member
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hpi]
  -- the level parameters are distinct: the head's first constructor's
  -- check, or — a container without constructors — the caller's
  have hndl : lps.Nodup := frame_lps_nodup mp hcov hD hmm hlps (by rw [hhead]; simp) hctors
    (posD_ctors_nodup hwalkD) hnL
  have hle := frameIter mp hD hblkD.nodup hkN hcov.find hlps hndl hul hds hdsa hlenP hg.2 hin
    hblkD.ctors rfl hR₀ hΔ hCds hLds hfit hctors
    (fun hR Q hprem hQ => ih hcov (by simp [grpNews, ConLeche.NestCtx.hiAt]; omega) hR Q hprem hQ)
  exact ⟨hndl, hg, hle.1, hle.2⟩

/-! ## The container instance -/

/-- **A container instance whose frame is derived HERE** (`contNew`): the
frame's conclusion at the enclosing relation seen at the key's depth makes
the instance grow (its leaf, `monoOn_of_famLe`). -/
theorem contNew_mono {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx}
    (hcov : ContCover mp ctx) {prog : List NestHole} {dep : Nat}
    (hhid : ctx.hiAt prog.length ≤ dep) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat}
    (hmm : mm < D.k) {lps : List Name}
    (hlps : ∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
    {us : List Level} (hul : us.length = lps.length) {ds is : List Expr}
    (hdsw : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x ∧ x.looseBVarsBounded 0 = true)
    (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    (hlenP : ∀ ψ, (D.params ψ).length = ds.length)
    (hnL : (∃ L', ConLeche.nestContainer ctx (D.member mm) = some (ds.length, L') ∧ L' ≠ []) ∨
      lps.Nodup)
    {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) = some wa)
    {Δa : List AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)))
    (hgr : Graded V Δa wa) (hR : HoleRel mp.base2 φ ctx prog dep Δa R)
    (hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
    {nI : Nat} {cty : Expr}
    (hnI : ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨D.member mm, us, ds⟩
      = .ok (nI, cty))
    (hisl : is.length = nI) {grp : List (Name × Expr)} (hhead : D.member mm = (grp.headD default).1)
    (ihf : FrameMono mp φ ctx prog us ds grp) : MonoOn R wa := by
  obtain ⟨cv, caps, hf, hcvl⟩ := hlps mm hmm
  -- the key's parameters read at the key's depth
  obtain ⟨fa, vs, -, hsp, -⟩ := denoteMeta_mkAppN_inv hwa
  obtain ⟨vs₁, vs₂, -, hsp₁, -⟩ := DenoteMetaSpine.split _ hsp
  obtain ⟨dsa, hdsa, -⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) hhid
    (fun x hx => (hdsw x hx).1) hsp₁
  -- the relation at the key's depth
  have hR₀ := hR.drop (Nat.le_refl _) hhid
  have hΔ : (Δa.drop (dep - ctx.hiAt prog.length)).length = ctx.hiAt prog.length := by
    rw [List.length_drop, hC.1]; omega
  have hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt prog.length)
      (Δa.drop (dep - ctx.hiAt prog.length)) x := fun x hx =>
    hC.drop hhid fun l hl => ⟨leaves_mkAppN_arg (List.mem_append_left _ hx) hl,
      ConLeche.Expr.fvarLeaves_lt_of_wscoped (hdsw x hx).1 l hl⟩
  have hfit : ∀ σ σ', R.drop (dep - ctx.hiAt prog.length) σ σ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa (ctx.hiAt prog.length) σ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa (ctx.hiAt prog.length) σ') := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    have k1 := keyParamsFit mp hD hmm hf hhid hwa (by rw [hcvl, hlenP]) (fun x hx => (hdsw x hx).1)
      hdsa ρ (hgr ρ h1)
    have k2 := keyParamsFit mp hD hmm hf hhid hwa (by rw [hcvl, hlenP]) (fun x hx => (hdsw x hx).1)
      hdsa ρ' (hgr ρ' h2)
    rw [hcvl] at k1 k2
    exact ⟨k1, k2⟩
  obtain ⟨hnd, hg', hle, -⟩ := ihf hcov hD hmm hhead hlps hul hdsw hdsa (hlenP _)
    (hnL.imp (fun ⟨L, hL, hLne⟩ => ⟨_, L, hL, hLne⟩) id) hR₀ hΔ hCds hLds hfit
  have hheadmem : (D.member mm, (grp.headD default).2) ∈ grp := by
    obtain ⟨p₀, ps₀, hp₀⟩ := List.exists_cons_of_ne_nil hg'.1
    rw [hp₀] at hhead ⊢
    simp only [List.headD_cons] at hhead ⊢
    rw [hhead]
    exact List.mem_cons_self
  obtain ⟨-, hids, -⟩ := n2_link mp hD hmm hcov.find hnI hf (by rw [hcvl]; exact hnd)
    (by rw [hcvl]; exact hul) (by rw [hcvl, hlenP]) hdsw hdsa
  refine monoOn_of_famLe mp hD hmm hf hhid hwa (by rw [hcvl, hlenP]) (by rw [hids, hisl])
    (fun x hx => (hdsw x hx).1) hdsa hR.dom hgr hisC fun ρ ρ' hr => ?_
  have := hle _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ mm ⟨hmm, by
    rw [List.contains_iff_mem, List.mem_map]; exact ⟨_, hheadmem, rfl⟩⟩
  rw [hcvl]
  exact this

/-! ## A derived key, at the block's own depth -/

/-- **A key's frame, read at the block's own depth** (the cache hit's
content; lane NESTIND's `trans` at `w = 0`, route A): for a recorded block
holding the key's container, along every frameless hole relation whose
pairs satisfy the container's parameter telescope at the key frames, the
container's carrier grows between them, and every member of the frame's
group transfers its hole fits to the carrier (`frameIter`). -/
@[expose] def KeyPos {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat)
    (ctx : NestCtx) (key : NestKey) : Prop :=
  ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = key.cname ∧
    ∀ cv caps, env.find? key.cname = some (.indInfo cv caps) →
      key.lvls.length = cv.levelParams.length →
      cv.levelParams.Nodup ∧
      (D.params (Level.substFn φ cv.levelParams key.lvls)).length = key.ds.length ∧
      ∀ (Δ0 : List AnnotTerm) (R00 : FrameRel V), HoleRel mp.base2 φ ctx [] (ctx.hiAt 0) Δ0 R00 →
        Δ0.length = ctx.hiAt 0 → (∀ x ∈ key.ds, CtxOkP mp.base2 φ (ctx.hiAt 0) Δ0 x) →
        ∀ dsa, DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt 0) key.ds dsa →
        (∀ ρ ρ', R00 ρ ρ' →
          Sat V (D.params (Level.substFn φ cv.levelParams key.lvls)).reverse
              (keyFrame dsa (ctx.hiAt 0) ρ) ∧
          Sat V (D.params (Level.substFn φ cv.levelParams key.lvls)).reverse
              (keyFrame dsa (ctx.hiAt 0) ρ')) →
        ∀ ρ ρ', R00 ρ ρ' →
          FamLe (D.idx (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ) mm)
            (D.carrier (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ) mm)
            (D.carrier (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ') mm)
          ∧ ∃ grp : List (Name × Expr), InGrp D grp mm ∧ ∀ g, InGrp D grp g → ∀ t j fs,
            D.HFits (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ)
              (grpTuple D (Level.substFn φ cv.levelParams key.lvls) grp
                (keyFrame dsa (ctx.hiAt 0) ρ) (keyFrame dsa (ctx.hiAt 0) ρ')) t g j fs →
            D.HFits (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ')
              (D.carrier (Level.substFn φ cv.levelParams key.lvls)
                (keyFrame dsa (ctx.hiAt 0) ρ')) t g j fs

/-- **A key whose frame is derived is positive at the block's own depth**:
its frame, derived under a well-scoped frame stack, read along the
frameless relation extended by EMPTY frames for that stack, and back
through the empty frames (`keyFrame_lift`). -/
theorem keyPos_of_frame {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx}
    {F : Nat} (hcov : ContCover mp ctx) {key : NestKey} {prog' : List NestHole}
    {grp : List (Name × Expr)} (hsc : ProgScoped ctx prog') (hmem : key.cname ∈ grp.map (·.1))
    {ts : List ConLeche.PosTree}
    (hfrD : PosD (fueledOps .verified F) env ctx (.frame prog' key.lvls key.ds grp) ts)
    (ihf : FrameMono mp φ ctx prog' key.lvls key.ds grp)
    (hds : ∀ x ∈ key.ds, Expr.WScoped (ctx.hiAt 0) x ∧ x.looseBVarsBounded 0 = true)
    (hLds : ∀ x ∈ key.ds, Expr.LeavesBounded x) : KeyPos mp φ ctx key := by
  obtain ⟨hne, hhd, ⟨Lh, hqh⟩, hinst, hblk⟩ := posD_frame_inv hfrD
  obtain ⟨ctors, hctors, hnodup⟩ := posD_frame_ctors hfrD
  obtain ⟨p₀, ps₀, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.headD_cons] at hhd hblk hqh
  -- the head's recorded block
  obtain ⟨nI₀, hnI₀⟩ := hinst p₀ List.mem_cons_self
  obtain ⟨cv₀, caps₀, hf₀c, -⟩ := ConLeche.nestInstType_inv hnI₀
  have hf₀ : env.find? p₀.1 = some (.indInfo cv₀ caps₀) := by rw [← hcov.find]; exact hf₀c
  obtain ⟨D, hD, mm₀, hmm₀, hn₀⟩ := hcov.cover p₀.1 cv₀ caps₀ hf₀ hhd.1 hhd.2
  have hblkD := hcov.block D hD
  -- the key's container is a member of it
  obtain ⟨mm, hmm, hn⟩ : ∃ mm, mm < D.k ∧ D.member mm = key.cname := by
    simp only [List.map_cons, List.mem_cons] at hmem
    rcases hmem with h | hmem
    · exact ⟨mm₀, hmm₀, hn₀.trans h.symm⟩
    · obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hmem
      have hin' := hblk p (by simpa using hp)
      have hblkOf : ConLeche.nestBlockOf ctx p₀.1 = D.names := by
        unfold ConLeche.nestBlockOf
        rw [hf₀c]
        exact hblkD.all mm₀ hmm₀ cv₀ caps₀ (by rw [hn₀]; exact hf₀)
      rw [hblkOf, List.contains_iff_mem] at hin'
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hin'
      refine ⟨i, by rw [lfp_namesLen mp hD] at hi; exact hi, ?_⟩
      unfold LfpDatum.member
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hpi, hpk]
  refine ⟨D, hD, mm, hmm, hn, fun cv caps hf hul => ?_⟩
  rw [← hn₀] at hqh
  obtain ⟨lps, hlps, hlenP, -, hnLh⟩ :=
    contBlock_facts mp hcov hD hmm₀ (by rw [hn₀]; exact hf₀) hqh
  have hcvl : cv.levelParams = lps := by
    obtain ⟨cv', caps', hf', h'⟩ := hlps mm hmm
    rw [hn, hf] at hf'
    obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
    exact h'
  have hnd : lps.Nodup := frame_lps_nodup mp hcov hD hmm₀ hlps (by rw [hn₀]; simp) hctors hnodup
    (hnLh.imp (fun ⟨L, hL, hLne⟩ => ⟨_, L, hL, hLne⟩) id)
  rw [hcvl] at hul ⊢
  refine ⟨hnd, hlenP _, fun Δ0 R00 hR00 hΔ0 hC0 dsa0 hdsa0 hfit00 ρ ρ' hr => ?_⟩
  -- the first walk's frames, empty
  have hle0' : ctx.hiAt 0 ≤ ctx.hiAt prog'.length := by simp only [ConLeche.NestCtx.hiAt]; omega
  have hlenR : (List.replicate prog'.length (empty : V)).length = prog'.length := by simp
  have hhiEq : ctx.hiAt prog'.length = ctx.hiAt 0 + prog'.length := by
    simp only [ConLeche.NestCtx.hiAt]; omega
  have hR₀ := HoleRel.extendEmpty hR00 prog' hsc
  have hdsaL := DenoteMetaSpine.lift (m := mp.base2) (φ := φ) hle0' (fun x hx => (hds x hx).1) hdsa0
  rw [show ctx.hiAt prog'.length - ctx.hiAt 0 = prog'.length by rw [hhiEq]; omega] at hdsaL
  have e := keyFrame_lift dsa0 (ctx.hiAt 0) (List.replicate prog'.length (empty : V))
  rw [hlenR, ← hhiEq] at e
  have hfit' : ∀ σ σ', (fun σ σ' => ∃ ρ ρ', R00 ρ ρ' ∧
        σ = consList (List.replicate prog'.length empty) ρ ∧
        σ' = consList (List.replicate prog'.length empty) ρ') σ σ' →
      Sat V (D.params (Level.substFn φ lps key.lvls)).reverse
          (keyFrame (dsa0.map (AnnotTerm.liftN prog'.length · 0)) (ctx.hiAt prog'.length) σ) ∧
      Sat V (D.params (Level.substFn φ lps key.lvls)).reverse
          (keyFrame (dsa0.map (AnnotTerm.liftN prog'.length · 0)) (ctx.hiAt prog'.length) σ') := by
    rintro _ _ ⟨ρ₁, ρ₁', hr₁, rfl, rfl⟩
    rw [e, e]
    exact hfit00 ρ₁ ρ₁' hr₁
  have hCds : ∀ x ∈ key.ds, CtxOkP mp.base2 φ (ctx.hiAt prog'.length)
      (List.replicate prog'.length (.sort 0) ++ Δ0) x := by
    intro x hx
    have := CtxOkP.extend (h := ctx.hiAt 0) (g := prog'.length)
      (Ts := List.replicate prog'.length (.sort 0)) (by simp) hΔ0
      (fun l hl => Or.inl ((hC0 x hx).2 l hl))
    rwa [← hhiEq] at this
  obtain ⟨-, -, hle, htr⟩ := ihf hcov hD hmm₀ hn₀ hlps hul
    (fun x hx => ⟨Expr.WScoped.mono hle0' (hds x hx).1, (hds x hx).2⟩) hdsaL (hlenP _)
    (hnLh.imp (fun ⟨L, hL, hLne⟩ => ⟨_, L, hL, hLne⟩) id) hR₀
    (by rw [List.length_append, List.length_replicate, hΔ0, hhiEq]; omega) hCds hLds hfit'
  have hmmG : InGrp D (p₀ :: ps₀) mm := ⟨hmm, by
    rw [List.contains_iff_mem, hn]; exact hmem⟩
  have hle' := hle _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ mm hmmG
  have htr' := htr _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
  rw [e, e] at hle' htr'
  exact ⟨hle', _, hmmG, htr'⟩

/-- **A container instance whose frame was derived under other frames**
(`contHit`, a cache hit): its parameters lie below every frame hole, so
the key is positive at the block's own depth (`keyPos_of_keyD`), read at
the enclosing relation seen at that depth; its leaf makes the instance
grow. -/
theorem contHit_mono {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx} {F : Nat}
    (hcov : ContCover mp ctx) {prog prog' : List NestHole} {dep : Nat}
    (hhid : ctx.hiAt prog.length ≤ dep) {n : Name} {us : List Level} {ds is : List Expr}
    {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep (Expr.mkAppN (.const n us) (ds ++ is)) = some wa)
    {Δa : List AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa (Expr.mkAppN (.const n us) (ds ++ is)))
    (hgr : Graded V Δa wa) (hR : HoleRel mp.base2 φ ctx prog dep Δa R)
    (hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
    (hdsw : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x ∧ x.looseBVarsBounded 0 = true)
    (hfree : ∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    {nI : Nat} {cty : Expr}
    (hnI : ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩
      = .ok (nI, cty))
    (hisl : is.length = nI) {grp : List (Name × Expr)}
    (hsc : ProgScoped ctx prog') (hmem : n ∈ grp.map (·.1))
    {ts : List ConLeche.PosTree}
    (hfrD : PosD (fueledOps .verified F) env ctx (.frame prog' us ds grp) ts)
    (ihf : FrameMono mp φ ctx prog' us ds grp) : MonoOn R wa := by
  have hds0 : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt 0) x := fun x hx =>
    ConLeche.WScoped.of_fvarsBelow (hdsw x hx).1 (ConLeche.Expr.fvarB_le (hfree x hx))
  obtain ⟨D, hD, mm, hmm, hn, hk⟩ := keyPos_of_frame mp hcov (key := ⟨n, us, ds⟩) hsc hmem hfrD
    ihf (fun x hx => ⟨hds0 x hx, (hdsw x hx).2⟩) hLds
  change D.member mm = n at hn
  subst hn
  obtain ⟨cv, caps, hf⟩ := (mp.lfp_ok D hD).2.1.1 mm hmm
  have hle0 : ctx.hiAt 0 ≤ ctx.hiAt prog.length := by simp only [ConLeche.NestCtx.hiAt]; omega
  have hle0d : ctx.hiAt 0 ≤ dep := Nat.le_trans hle0 hhid
  -- the parameters' readings at the two depths
  obtain ⟨fa, vs, hfa, hsp, -⟩ := denoteMeta_mkAppN_inv hwa
  obtain ⟨hul, -⟩ := Rules.denoteMeta_const_arityK hf hfa
  change us.length = cv.levelParams.length at hul
  obtain ⟨hnd, hlenP, hpos⟩ := hk cv caps hf hul
  obtain ⟨vs₁, vs₂, -, hsp₁, -⟩ := DenoteMetaSpine.split _ hsp
  obtain ⟨dsa0, hdsa0, -⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) hle0d hds0 hsp₁
  obtain ⟨dsa, hdsa, -⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) hhid
    (fun x hx => (hdsw x hx).1) hsp₁
  -- the index count
  obtain ⟨-, hids, -⟩ := n2_link mp hD hmm hcov.find hnI hf hnd hul hlenP hdsw hdsa
  -- the key's positivity at the enclosing relation seen at the block's depth
  have hR00 := hR.dropBase hhid
  have hC0 : ∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt 0) (Δa.drop (dep - ctx.hiAt 0)) x :=
    fun x hx => hC.drop hle0d fun l hl =>
      ⟨leaves_mkAppN_arg (List.mem_append_left _ hx) hl,
        ConLeche.Expr.fvarLeaves_lt_of_wscoped (hds0 x hx) l hl⟩
  have hfit00 : ∀ σ σ', R.drop (dep - ctx.hiAt 0) σ σ' →
      Sat V (D.params (Level.substFn φ cv.levelParams us)).reverse
          (keyFrame dsa0 (ctx.hiAt 0) σ) ∧
      Sat V (D.params (Level.substFn φ cv.levelParams us)).reverse
          (keyFrame dsa0 (ctx.hiAt 0) σ') := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨keyParamsFit mp hD hmm hf hle0d hwa hlenP.symm hds0 hdsa0 ρ (hgr ρ h1),
      keyParamsFit mp hD hmm hf hle0d hwa hlenP.symm hds0 hdsa0 ρ' (hgr ρ' h2)⟩
  refine monoOn_of_famLe mp hD hmm hf hle0d hwa hlenP.symm (by rw [hids, hisl]) hds0 hdsa0
    hR.dom hgr hisC fun ρ ρ' hr => ?_
  exact (hpos _ _ hR00 (by rw [List.length_drop, hC.1]; omega) hC0 dsa0 hdsa0 hfit00 _ _
    ⟨ρ, ρ', hr, rfl, rfl⟩).1

/-! ## THE INDUCTION -/

/-- **THE DERIVATION IS MONOTONE** (charter items 2–4): every judgment of
a positivity derivation reads monotonically in the holes, by induction
on the derivation (see the module docstring). -/
theorem posD_mono {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} {F : Nat} :
    ∀ {j : PosJ} {ts : List ConLeche.PosTree}, PosD (fueledOps .verified F) env ctx j ts →
      MonoJ mp φ ctx F j := by
  intro j ts h
  induction h with
  | @const prog dep kb e w hw hocc =>
    intro _ hhi hfr Δa ea R hC hea hgr hR
    exact mono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw _ wa hwa _ =>
      (ConstOn.of_noBVar hR.agree (denoteMeta_noBVar_of_nestOcc dep w hfrw.1 hhi hocc hwa)).monoOn
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ihb =>
    intro hcov hhi hfr Δa ea R hC hea hgr hR
    refine mono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hwa
    obtain ⟨hws, hbb, hLb⟩ := hfrw
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hA : ConstOn R ta := ConstOn.of_noBVar hR.agree
      (denoteMeta_noBVar_of_nestOcc dep a hws.1 hhi ha hta)
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
    have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
    exact MonoOn.pi 0 _ hA (ihb hcov (by omega) (frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd)
      hCop hba hgB (hR.under hhi hA.monoOn))
  | @hole prog dep kb e w i ty hw hocc hfn hlo hhi' hlen hpar hfree =>
    intro _ hhi hfr Δa ea R hC hea hgr hR
    refine mono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    have hspine := Expr.mkAppN_getApp w
    rw [hfn] at hspine
    rw [← hspine] at hwa
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
    rw [denoteMeta_fvar] at hfa
    cases hfa
    have hwsargs : ∀ a ∈ w.getAppArgs, Expr.WScoped dep a := by
      have h0 := hfrw.1
      rw [← hspine] at h0
      exact (wScoped_mkAppN _ h0).2
    have hlenv := DenoteMetaSpine.length_eq hsp
    have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
    have ht : i - ctx.nP < ctx.names.length := by
      simp only [ConLeche.NestCtx.hiAt] at hhi'; omega
    have hh := hR.member (i - ctx.nP) ht
    rw [show dep - 1 - (ctx.nP + (i - ctx.nP)) = dep - 1 - i by omega, ← hlen, hlenv] at hh
    exact MonoOn.holeApp hh hvs
  | @frameHole prog dep kb e w i ty h hw hocc hfn hlo hhi' hk hle hpar hfree har =>
    intro _ hhi hfr Δa ea R hC hea hgr hR
    refine mono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    have hspine := Expr.mkAppN_getApp w
    rw [hfn] at hspine
    rw [← hspine] at hwa
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
    rw [denoteMeta_fvar] at hfa
    cases hfa
    have hwsargs : ∀ a ∈ w.getAppArgs, Expr.WScoped dep a := by
      have h0 := hfrw.1
      rw [← hspine] at h0
      exact (wScoped_mkAppN _ h0).2
    rw [← List.take_append_drop h.key.ds.length w.getAppArgs] at hsp
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
    have hvs₂ := constOn_spine hR.agree hhi hsp₂ fun a ha =>
      ⟨hwsargs a (List.mem_of_mem_drop ha), hfree a ha⟩
    have hsp₁' : DenoteMetaSpine mp.base2.acval env φ dep h.key.ds vs₁ := by
      rw [← hpar]; exact hsp₁
    have hh := hR.frame (i - ctx.hiAt 0) h hk vs₁ hsp₁' vs₂.length (by
      have h2 := DenoteMetaSpine.length_eq hsp₂
      rw [List.length_drop] at h2
      omega)
    rw [show dep - 1 - (ctx.hiAt 0 + (i - ctx.hiAt 0)) = dep - 1 - i by omega] at hh
    exact MonoOn.holeAppArgs hh hvs₂
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds _ hnI
      hhead _ hfrD ihf =>
    intro hcovk hhid hfr Δa ea R hC hea hgr hR
    have hcov := hcovk rfl
    refine mono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    obtain ⟨cv, caps, hfc⟩ := nestContainer_find hq
    rw [hcov.find] at hfc
    obtain ⟨D, hD, mm, hmm, hn⟩ := hcov.cover n cv caps hfc hnm hquot
    subst hn
    obtain ⟨lps, hlps, hlenP0, hcvl, hnL0⟩ := contBlock_facts mp hcov hD hmm hfc hq
    have hspine := Expr.mkAppN_getApp w
    rw [hfn] at hspine
    generalize hargs : w.getAppArgs = args at hspine hlen hidx hds hnI hfrD ihf
    subst hspine
    rw [← List.take_append_drop nPc args] at hwa hCw
    have hdl : (args.take nPc).length = nPc := by rw [List.length_take]; omega
    have hwsargs := (wScoped_mkAppN _ hfrw.1).2
    have hdsw : ∀ x ∈ args.take nPc, Expr.WScoped (ctx.hiAt prog.length) x ∧
        x.looseBVarsBounded 0 = true := fun x hx =>
      ⟨ConLeche.WScoped.of_fvarsBelow (hwsargs x (List.mem_of_mem_take hx))
        (ConLeche.Expr.fvarB_le (hds x hx).2), ConLeche.Expr.bvarB_le (Nat.le_of_eq (hds x hx).1)⟩
    have hLds : ∀ x ∈ args.take nPc, Expr.LeavesBounded x := fun x hx l hl =>
      hfrw.2.2 l (leaves_mkAppN_arg (List.mem_of_mem_take hx) hl)
    have hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep (args.drop nPc) isa →
        ∀ v ∈ isa, ConstOn R v := fun isa hisa =>
      constOn_spine hR.agree hhid hisa fun a ha => ⟨hwsargs a (List.mem_of_mem_drop ha), hidx a ha⟩
    have hisl : (args.drop nPc).length = nI := by rw [List.length_drop]; omega
    obtain ⟨fa, vs, hfa, -, -⟩ := denoteMeta_mkAppN_inv hwa
    obtain ⟨hul, -⟩ := Rules.denoteMeta_const_arityK hfc hfa
    change us.length = cv.levelParams.length at hul
    rw [hcvl] at hul
    have hhead' : D.member mm = (grp.headD default).1 := by
      cases grp with
      | nil => simp at hhead
      | cons p ps =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        rw [List.headD_cons, hhead]
    exact contNew_mono mp hcov hhid hD hmm hlps hul hdsw hLds
      (fun ψ => by rw [hdl]; exact hlenP0 ψ) (by rw [hdl]; exact hnL0) hwa hCw hgw hR hisC hnI
      hisl hhead' ihf
  | @contHit prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds
      _ hnI hmem hfrD ihf =>
    intro hcovk hhid hfr Δa ea R hC hea hgr hR
    have hcov := hcovk rfl
    refine mono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    have hspine := Expr.mkAppN_getApp w
    rw [hfn] at hspine
    generalize hargs : w.getAppArgs = args at hspine hlen hidx hds hnI hfrD ihf
    subst hspine
    rw [← List.take_append_drop nPc args] at hwa hCw
    have hdl : (args.take nPc).length = nPc := by rw [List.length_take]; omega
    have hwsargs := (wScoped_mkAppN _ hfrw.1).2
    have hle0 : ctx.hiAt 0 ≤ ctx.hiAt prog.length := by simp only [ConLeche.NestCtx.hiAt]; omega
    have hdsw : ∀ x ∈ args.take nPc, Expr.WScoped (ctx.hiAt prog.length) x ∧
        x.looseBVarsBounded 0 = true := fun x hx =>
      ⟨ConLeche.WScoped.of_fvarsBelow (hwsargs x (List.mem_of_mem_take hx))
        (ConLeche.Expr.fvarB_le (Nat.le_trans (hds x hx).2 hle0)),
        ConLeche.Expr.bvarB_le (Nat.le_of_eq (hds x hx).1)⟩
    have hLds : ∀ x ∈ args.take nPc, Expr.LeavesBounded x := fun x hx l hl =>
      hfrw.2.2 l (leaves_mkAppN_arg (List.mem_of_mem_take hx) hl)
    have hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep (args.drop nPc) isa →
        ∀ v ∈ isa, ConstOn R v := fun isa hisa =>
      constOn_spine hR.agree hhid hisa fun a ha => ⟨hwsargs a (List.mem_of_mem_drop ha), hidx a ha⟩
    have hisl : (args.drop nPc).length = nI := by rw [List.length_drop]; omega
    exact contHit_mono mp hcov hhid hwa hCw hgw hR hisC hdsw (fun x hx => (hds x hx).2) hLds hnI
      hisl (ConLeche.ProgScoped.nil' (ctx := ctx)) hmem hfrD ihf
  | @frame prog us ds grp ctors ts hne hhd hhdC hnd hinst hblk _ hctors _ hwalk ih =>
    exact frame_mono mp hin hne hnd hinst hblk hctors hwalk ih
  | ctorsNil =>
    intro _ _ Δ R _ Q _ _ x hx
    exact nomatch hx
  | @ctorsCons prog hi us ds sub cv nF cs crest ty sv ks nds cur ts ts' hnd hcrest hty hsort htele
      hu4 hres hidx hrest ihtele ihrest =>
    intro hcov hhi Δ R hR Q hprem hQ x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨ca, hfr, hC, hca, hgr⟩ :=
        hprem (cv, nF) crest (hQ _ List.mem_cons_self) hcrest ⟨ty, hty⟩
      refine ⟨nodup_of_nameNodup hnd, crest, ca, cur, hcrest, hca, hres, hidx, ?_⟩
      have := ihtele (fun _ => hcov) (by omega) hfr hC hca hgr hR
      rw [hhi] at this
      simpa using this
    · exact ihrest hcov hhi hR Q hprem (fun y hy => hQ y (List.mem_cons_of_mem _ hy)) x hx
  | teleNil =>
    intro _ _ hfr Δa ca R _ hca _ hR
    exact ⟨hR.agree, hca, hfr.1⟩
  | @teleCons prog base nF j a b bm k nd ks nds res ts tss ts' ha hs hb iha _ ihb =>
    intro hcovk hhi hfr Δa ca R hC hca hgr hR
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hca
    obtain ⟨hws, hbb, hLb⟩ := hfr
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgr
    have hA := iha (fun hk => hcovk ⟨k, List.mem_cons_self, hk⟩) hhi ⟨hws.1, hbb.1, hLa⟩
      hC.forallE_ty hta hgA hR
    have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgA
    have hfr' := frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd
    rw [show base + j + 1 = base + (j + 1) by omega] at hCop hfr' hba
    have hrest := ihb (fun ⟨k', hk', hkf⟩ => hcovk ⟨k', List.mem_cons_of_mem _ hk', hkf⟩)
      (by omega) hfr' hCop hba hgB
      (by rw [show base + (j + 1) = base + j + 1 by omega]; exact hR.under hhi hA)
    rw [show base + j + (nF + 1) = base + (j + 1) + nF by omega]
    exact ⟨hA, hrest⟩
  | synNil => trivial
  | synNew => trivial
  | synHit => trivial


/-! ## The member constructor -/

/-- **The result's reading, its indices constant** along the relation: a
member-hole head with hole-free indices (the member constructor's result
check), read at a depth above the block's own. -/
theorem resultIdxConst_of_resultAt {m : EnvModel V env} {ctx : NestCtx} {D : Nat} {res : Expr}
    (hD : ctx.hiAt 0 ≤ D) (hhead : ConLeche.nestResHead res = true)
    (hok : (res.getAppArgs.drop ctx.nP).all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0))
      = true)
    {R : FrameRel V} {r : AnnotTerm} (hres : ResultAt m φ ctx.nP (ctx.hiAt 0) D res R r) :
    ResultIdxConst ctx.nP R r := by
  obtain ⟨hag, hrd, hws⟩ := hres
  have hspine := Expr.mkAppN_getApp res
  rw [← hspine] at hrd hws
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hrd
  have hfa' : ∃ i, fa = .bvar i := by
    unfold ConLeche.nestResHead at hhead
    split at hhead
    · rename_i heq
      rw [heq, denoteMeta] at hfa
      exact ⟨_, (Option.some.inj hfa).symm⟩
    · exact nomatch hhead
  obtain ⟨i, rfl⟩ := hfa'
  rw [← List.take_append_drop ctx.nP res.getAppArgs] at hsp
  obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
  refine ⟨i, vs₁ ++ vs₂, rfl, ?_⟩
  have hl₁ : vs₁.length ≤ ctx.nP := by
    rw [← DenoteMetaSpine.length_eq hsp₁, List.length_take]; omega
  intro v hv
  simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hok
  have hdrop : (vs₁ ++ vs₂).drop ctx.nP ⊆ vs₂ := by
    intro x hx
    rw [List.drop_append] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.drop_eq_nil_of_le hl₁] at hx; exact nomatch hx
    · exact List.mem_of_mem_drop hx
  have hwsargs := (wScoped_mkAppN _ hws).2
  refine constOn_spine hag hD hsp₂ (fun a ha => ⟨?_, hok a ha⟩) v (hdrop hv)
  exact hwsargs a (List.mem_of_mem_drop ha)

/-- **A derived member constructor is positive** (the consumer's
premise; `CtorPos` of `Model/Annot/BlockLfpMono.lean` in the
constructor type's own Π-form): every field's reading monotone under the
earlier ones along the hole relation, the result's indices hole-free —
coverage needed only when some field's kind is not flat. -/
theorem memberCtorD_mono {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} {F nF : Nat} {crest : Expr}
    {ks : List PosKind} {tyN : Expr} {ts : List ConLeche.PosTree}
    (hd : ConLeche.MemberCtorD (fueledOps .verified F) env ctx nF crest ks tyN ts)
    (hcov : (∃ k ∈ ks, k.flat = false) → ContCover mp ctx)
    (hfr : Frame (ctx.hiAt 0) crest)
    {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta mp.base2.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca)
    (hR : HoleRel mp.base2 φ ctx [] (ctx.hiAt 0) Δa R) :
    PiPosThen (ResultIdxConst ctx.nP) nF R ca := by
  obtain ⟨nds, res, htele, -, -, hhead, hok, -⟩ := hd
  exact PiPosThen.mono (fun _ _ h => resultIdxConst_of_resultAt (by simp) hhead hok h) nF R ca
    (posD_mono mp hin htele hcov (by simp) hfr hC hca hgr hR)

end ConLeche.Model
