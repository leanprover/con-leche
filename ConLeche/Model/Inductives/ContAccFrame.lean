module

public import ConLeche.Model.Inductives.ContAccRel
public import ConLeche.Model.Inductives.BlockAccRun
import ConLeche.Model.Inductives.StoredShapes
import ConLeche.Verify.Denote.Shift
import ConLeche.Verify.Cached.NestPosC
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Inductives.ContCtor
import ConLeche.Model.Annot.LfpFormer

public section

/-!
# A container frame's constructors are accessible (lane ACCMODEL, session 3)

The accessibility twin of `frameIter`/`frame_sem` (`ContWalk.lean`), over
the frame relation `frameRelA` (`ContAccRel.lean`).

* `walkTele_acc`: a walked telescope (any frames, any base depth) is
  accessible along its relation over its NORMAL FORM's readings (the walk's
  outputs, `OutTele`), with bounds and ordinary readings reading only the
  ordinary slots and the parameter positions (`TAgrM`, `ParamPos`) — the
  input fields may mention a non-ordinary field or a hole inside a redex
  whnf drops (`corner_nestw_u4frame_beta`), the outputs may not (U4).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestHole NestState NestFieldKind CheckError CheckM
  ConstantVal BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The parameter positions -/

/-- **The parameter positions at depth `b`**: position `p` is a variable
below the depth, one of the `nP` parameters. -/
@[expose] def ParamPos (b nP : Nat) : Nat → Prop := fun p => p < b ∧ b - 1 - p < nP

/-- Hereditary sizes move along fields reading alike. -/
theorem FieldsBound.of_eqOn {w : Nat} :
    ∀ {Δ As Bs : List AnnotTerm} {ρ : Nat → V}, FieldsEqOn V Δ As Bs → Sat V Δ ρ →
      FieldsBound w ρ As → FieldsBound w ρ Bs
  | _, [], [], _, _, _, _ => trivial
  | Δ, A :: As, B :: Bs, ρ, hE, hs, hb => by
    obtain ⟨h0, hrest⟩ := hE
    obtain ⟨hA, hAs⟩ := hb
    rw [h0 ρ hs] at hA hAs
    refine ⟨hA, fun a ha => ?_⟩
    exact FieldsBound.of_eqOn hrest (Sat_cons V hs (by rw [h0 ρ hs]; exact ha)) (hAs a ha)
  | _, [], _ :: _, _, hE, _, _ => hE.elim
  | _, _ :: _, [], _, hE, _, _ => hE.elim

/-- **The walked outputs' readings, as a telescope** (`OutTele`): a list
reading like the walked input fields, each entry the reading of its
field's output. -/
theorem outTele_list {ctx : NestCtx} {prog : List NestHole} :
    ∀ (ks : List NestFieldKind) (nds : List Expr) (d : Nat) (Δ : List AnnotTerm)
      (abD : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      abD.length = nds.length →
      OutTele m φ ctx prog ks nds d Δ (mkPisAV abD B) →
      ∃ N : List AnnotTerm, N.length = nds.length ∧ FieldsEqOn V Δ (abD.map (·.2.2)) N ∧
        ∀ (i : Nat) (nd : Expr), nds[i]? = some nd → ∃ na, N[i]? = some na ∧
          denoteMeta m.acval env φ (d + i) nd = some na ∧ nd.looseBVarsBounded 0 = true ∧
          Expr.WScoped (d + i) nd ∧
          (ks.getD i .ordinary = .ordinary →
            nd.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
  | [], [], _, _, [], _, _, _ => ⟨[], rfl, trivial, fun _ _ h => by simp at h⟩
  | k :: ks, nd :: nds, d, Δ, x :: abD, B, hl, hO => by
    obtain ⟨⟨hcl, hws, hord, na, hna, hr⟩, hrest⟩ := hO
    obtain ⟨N, hNl, hE, hN⟩ := outTele_list ks nds (d + 1) (x.2.2 :: Δ) abD B
      (by simpa using hl) hrest
    refine ⟨na :: N, by simp [hNl], ⟨fun ρ hρ => (hr ρ hρ).symm, hE⟩, fun i nd' hi => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨na, rfl, by simpa using hna, hcl, by simpa using hws, fun h => hord (by simpa using h)⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨na', h1, h2, h3, h4, h5⟩ := hN i nd' hi
      refine ⟨na', by simpa using h1, by rw [show d + (i + 1) = d + 1 + i by omega]; exact h2, h3,
        by rw [show d + (i + 1) = d + 1 + i by omega]; exact h4, fun h => h5 (by simpa using h)⟩
  | [], _ :: _, _, _, _, _, _, hO => hO.elim
  | _ :: _, [], _, _, _, _, _, hO => by cases hO
  | [], [], _, _, _ :: _, _, hl, _ => by simp at hl
  | _ :: _, _ :: _, _, _, [], _, hl, _ => by simp at hl

/-! ## A walked telescope, over its normal form -/

set_option maxHeartbeats 800000 in
/-- **A walked telescope is accessible over its normal form** (see the
module docstring): any walk `rec` at any frames `prog`, the base depth the
walk's hole bound `b`. -/
theorem walkTele_acc {w : Nat} (hw : w ≠ 0) {ctx : NestCtx} {prog : List NestHole} {b : Nat}
    (hb : ctx.hiAt prog.length = b)
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {err : CheckError} {nF : Nat} {cur res : Expr}
    {st₀ st₁ : NestState} {ks : List NestFieldKind} {nds : List (Expr × BinderMeta)}
    (hf : ConLeche.nestFields rec prog b err nF 0 cur st₀ = .ok (ks, nds, res, st₁))
    (hr : st₁.restart = none) (hcl : cur.looseBVarsBounded 0 = true)
    (hU4 : ∀ i, i < nF → ks.getD i .ordinary ≠ .ordinary →
      ConLeche.structUsedLater (ConLeche.closeTelescope nds b res) 0 i = false)
    {Δ : List AnnotTerm} {R : FrameRel V} {abD : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm}
    (hlen : abD.length = nF)
    (hdom : ∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀)
    (hbd : ∀ ρ ρ₀, R ρ ρ₀ → FieldsBound w ρ (abD.map (·.2.2)))
    (hP : PiAccThen w ctx prog (ResultAt m φ ctx.nP b (b + nF) res) nF b (nds.map (·.1)) R
      (mkPisAV abD B))
    (hO : OutTele m φ ctx prog ks (nds.map (·.1)) b Δ (mkPisAV abD B)) :
    ∃ (Af : Nat → (Nat → V) → V) (N : List AnnotTerm),
      FieldsEqOn V Δ (abD.map (·.2.2)) N ∧
      TeleAccP w Af 0 (HoleQ ctx prog b) R N ∧
      (∀ l τ τ', TAgrM 0 (ParamPos b ctx.nP) (fun l => ks.getD l .ordinary == .ordinary) l τ τ' →
        Af l τ = Af l τ') ∧
      (∀ (i : Nat) (G : AnnotTerm), N[i]? = some G → (ks.getD i .ordinary == .ordinary) = true →
        ∀ τ τ', TAgrM 0 (ParamPos b ctx.nP) (fun l => ks.getD l .ordinary == .ordinary) i τ τ' →
          interp V τ G = interp V τ' G) ∧
      ResultAt m φ ctx.nP b (b + nF) res (R.underBothTele N) B := by
  classical
  obtain ⟨-, -, hkl, hnl, -⟩ := nestFields_inv_nr nF 0 cur st₀ ks nds res st₁ hf hr
  have hnl' : (nds.map (·.1)).length = nF := by rw [List.length_map, hnl]
  obtain ⟨N, hNl, hE, hN⟩ := outTele_list ks (nds.map (·.1)) b Δ abD B
    (by rw [hnl', hlen]) hO
  have hndcl : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨na, -, -, h3, -⟩ := hN i nds[i].1 (by simp [List.getElem?_eq_getElem hi])
    exact h3
  obtain ⟨xs, rest, hop, -, -, hxs⟩ := fields_open hcl hf hr hndcl
  let abN : List (Nat × Nat × AnnotTerm) := N.map fun a => (0, 0, a)
  have habN : abN.map (·.2.2) = N := by simp only [abN, List.map_map]; exact List.map_id N
  rw [← hlen] at hP
  obtain ⟨Af, htele, hinv, hQf⟩ := teleAccP_of_piAccThen hw abD abN B b 0 (nds.map (·.1)) Δ R
    (HoleQ ctx prog b) (by rw [habN]; exact hE) hdom
    (fun ρ ρ₀ h => by rw [habN]; exact FieldsBound.of_eqOn hE (hdom ρ ρ₀ h).1 (hbd ρ ρ₀ h))
    (fun _ _ => Iff.rfl) (by omega) hP
  rw [habN] at htele hQf
  rw [hlen] at hQf
  have hNn : N.length = nF := hNl.trans hnl'
  -- the closed normal form is scoped at the base
  have hW : Expr.WScoped b (ConLeche.closeTelescope nds b res) := by
    refine ConLeche.Cached.closeTelescope_wscoped nds b res (fun k nd hk => ?_) ?_
    · obtain ⟨na, -, -, -, h4, -⟩ := hN k nd.1 (by simp [hk])
      exact h4
    · rw [hnl]; exact hQf.2.2
  let ord : Nat → Bool := fun l => ks.getD l .ordinary == .ordinary
  -- U4: a later output mentions no non-ordinary field
  have hu4 : ∀ l j x, j < l → xs[l]? = some x → ord j = false →
      x.fvarTypeD.nestOcc [] (b + j) (b + j + 1) = false := by
    intro l j x hjl hx hoj
    have hlx : l < nF := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [ConLeche.Verify.openPisAtFvars_length nF hop] at this; exact this
    have hne : ks.getD j .ordinary ≠ .ordinary := by simpa [ord] using hoj
    exact u4_nestOccAt hop hW (hU4 j (by omega) hne) (by omega) hjl hx
  refine ⟨fun l => if l < nF then Af l else fun _ => empty, N, hE, ?_, ?_, ?_, hQf⟩
  · refine TeleAccP.congr _ 0 _ _ (fun l' _ hl' => ?_) htele
    have : l' < nF := by simp at hl'; omega
    simp only [if_pos this]
  · -- the bounds read the ordinary slots and the parameters
    intro l τ τ' hag
    by_cases hl : l < nF
    · simp only [if_pos hl]
      obtain ⟨x, hx⟩ : ∃ x, xs[l]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [ConLeche.Verify.openPisAtFvars_length nF hop]; exact hl)⟩
      obtain ⟨nd, hnd, hEx⟩ := hxs l x hx
      have hinvl := hinv l nd (by rw [hlen]; exact hl) (by rw [List.getElem?_map]; exact hnd)
      rw [Nat.zero_add, hb] at hinvl
      refine hinvl τ τ' fun i hi => ?_
      by_cases hil : i < l
      · by_cases hoj : ord (l - 1 - i) = true
        · exact (hag i).1 hil hoj
        · exfalso
          rcases hi with ⟨hlt, hocc, -⟩ | ⟨hlt, hpar⟩
          · have hfree := hu4 l (l - 1 - i) x (by omega) hx (by simpa using hoj)
            rw [erasedEq_nestOcc _ _ hEx] at hfree
            rw [show b + l - 1 - i = b + (l - 1 - i) by omega,
              show b + l - i = b + (l - 1 - i) + 1 by omega, hfree] at hocc
            exact Bool.false_ne_true hocc
          · have : ctx.nP ≤ b := by rw [← hb]; simp only [NestCtx.hiAt]; omega
            omega
      · refine (hag i).2 (by omega) ?_
        have : ctx.nP ≤ b := by rw [← hb]; simp only [NestCtx.hiAt]; omega
        rcases hi with ⟨hlt, -, hnh⟩ | ⟨hlt, hpar⟩
        · refine ⟨by omega, Nat.lt_of_not_le fun hge => hnh ⟨hlt, ?_, ?_⟩⟩ <;> omega
        · exact ⟨by omega, by omega⟩
    · simp only [if_neg hl]
  · -- the ordinary readings read the ordinary slots and the parameters
    intro i G hGi hoi τ τ' hag
    have hi : i < nF := by
      have := (List.getElem?_eq_some_iff.mp hGi).1
      rw [hNl, hnl'] at this; exact this
    obtain ⟨p, hp⟩ : ∃ p, nds[i]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨na, hna, hden, hcln, hws, hord⟩ := hN i p.1 (by simp [hp])
    rw [hGi] at hna
    obtain rfl := Option.some.inj hna
    have hkord : ks.getD i .ordinary = .ordinary := by simpa using hoi
    have hholes : NoBVar (holeP (b + i) ctx.nP b) G := by
      have h := hord hkord
      rw [hb] at h
      exact denoteMeta_noBVar_of_nestOcc (m := m) (names := ctx.names) _ _ hws (by omega) h hden
    obtain ⟨x, hx⟩ : ∃ x, xs[i]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [ConLeche.Verify.openPisAtFvars_length nF hop]; exact hi)⟩
    obtain ⟨nd, hnd, hEx⟩ := hxs i x hx
    have hndp : nd = p.1 := by rw [hp] at hnd; simpa using hnd.symm
    subst hndp
    have hxread : denoteMeta m.acval env φ (b + i) x.fvarTypeD = some G := by
      rw [denoteMeta_erasedEq hEx]; exact hden
    have hslots : NoBVar (fun q => ∃ jj, jj < i ∧ ord jj = false ∧ LfpDatum.fieldSlot jj i q) G := by
      refine noBVar_exists' (P := fun jj q => jj < i ∧ ord jj = false ∧ LfpDatum.fieldSlot jj i q)
        fun jj => ?_
      by_cases hjj : jj < i ∧ ord jj = false
      · have hne : ks.getD jj .ordinary ≠ .ordinary := by simpa [ord] using hjj.2
        exact NoBVar.mono (fun q hq => hq.2.2)
          (u4_fieldSlotAt (m := m) hop hW (hU4 jj (by omega) hne) (by omega) hjj.1 hx hxread)
      · exact NoBVar.mono (fun q hq => absurd ⟨hq.1, hq.2.1⟩ hjj) hholes
    have hbeyond : NoBVar (fun q => b + i ≤ q) G :=
      NoBVar_of_bvarsBelow (denote_bvarsBelow m.cval_closedL (b + i) _ hws hcln
        (denoteMeta_erase m.acval_erase (b + i) _ hden)) fun _ h => h
    refine interp_congr_noBVar _ (noBVar_or (noBVar_or hholes hslots) hbeyond) fun q hq => ?_
    have : ctx.nP ≤ b := by rw [← hb]; simp only [NestCtx.hiAt]; omega
    by_cases hqi : q < i
    · refine (hag q).1 hqi (Classical.byContradiction fun hqo => ?_)
      exact hq (Or.inl (Or.inr ⟨i - 1 - q, by omega, Bool.eq_false_iff.mpr hqo, by
        simp only [LfpDatum.fieldSlot]; omega⟩))
    · refine (hag q).2 (by omega) ⟨?_, ?_⟩
      · exact Nat.lt_of_not_le fun hge => hq (Or.inr (by omega))
      · refine Nat.lt_of_not_le fun hge => hq (Or.inl (Or.inl ⟨?_, ?_, ?_⟩))
        · exact Nat.lt_of_not_le fun hge' => hq (Or.inr hge')
        · omega
        · omega

/-! ## A frame's constructors, walked -/

/-- What a successful frame walk leaves of one constructor, for
accessibility: its level parameters distinct, its instantiated abstracted
type read, the telescope run itself (no restart pending), U4 on its normal
form, its result the hole applied with hole-free indices, the walked
fields accessible along the frame relation and their outputs read like the
inputs. -/
@[expose] def CtorWalkedA (m : EnvModel V env) (φ : Name → Nat) (w : Nat) (ctx : NestCtx)
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (sub : Name → List Level → Option Expr)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState))
    (Δ : List AnnotTerm) (R : FrameRel V) (x : ConstantVal × Nat) : Prop :=
  x.1.levelParams.Nodup ∧ ∃ crest ca err st ks nds cur st₁,
    ConLeche.instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
      = some crest ∧
    crest.looseBVarsBounded 0 = true ∧
    denoteMeta m.acval env φ hi crest = some ca ∧
    ConLeche.nestFields rec prog hi err x.2 0 crest st = .ok (ks, nds, cur, st₁) ∧
    st₁.restart = none ∧
    (∀ i, i < x.2 → ks.getD i .ordinary ≠ .ordinary →
      ConLeche.structUsedLater (ConLeche.closeTelescope nds hi cur) 0 i = false) ∧
    ConLeche.nestResHead cur = true ∧
    (cur.getAppArgs.drop nPc).all (fun a => !a.nestOcc ctx.names ctx.nP hi) = true ∧
    PiAccThen w ctx prog (ResultAt m φ ctx.nP hi (hi + x.2) cur) x.2 hi (nds.map (·.1)) R ca ∧
    OutTele m φ ctx prog ks (nds.map (·.1)) hi Δ ca

/-- **A frame's constructors, walked, accessible** (twin of
`nestCtors_sem`): the state invariant is kept, and when no restart is
pending every constructor was walked (`CtorWalkedA`). -/
theorem nestCtors_acc {w : Nat} {ctx : NestCtx} {F : Nat} {I : NestState → Prop}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    (hrec : NestPosAcc m φ w ctx (fun _ => True) I rec)
    {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr} {nPc : Nat}
    {sub : Name → List Level → Option Expr} (hhi : ctx.hiAt prog.length = hi)
    {Δ : List AnnotTerm} {R : FrameRel V} (hR : HoleRelA m φ ctx prog hi Δ R)
    {Q : ConstantVal × Nat → Prop}
    (hprem : ∀ (x : ConstantVal × Nat) (crest : Expr), Q x →
      ConLeche.instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
        = some crest →
      (∃ ty, ConLeche.inferTypeCore .verified env F hi crest = .ok ty) →
      ∃ ca, Frame hi crest ∧ CtxOkP m φ hi Δ crest ∧
        denoteMeta m.acval env φ hi crest = some ca ∧ Graded V Δ ca ∧ TeleSmall w x.2 R ca) :
    ∀ (ctors : List (ConstantVal × Nat)) (st st' : NestState), (∀ x ∈ ctors, Q x) →
      ConLeche.nestCtors ctx (ConLeche.fueledOps .verified F) env rec prog hi us ds nPc sub ctors st
        = .ok st' → I st →
      I st' ∧ (st'.restart = none → ∀ x ∈ ctors,
        CtorWalkedA m φ w ctx prog hi us ds nPc sub rec Δ R x) := by
  intro ctors
  induction ctors with
  | nil =>
    intro st st' _ h hI
    simp only [ConLeche.nestCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, fun _ x hx => nomatch hx⟩
  | cons x cs ih =>
    intro st st' hQ h hI
    obtain ⟨cv, nF⟩ := x
    simp only [ConLeche.nestCtors, bind, Except.bind] at h
    have hnd : ConLeche.Name.nodup cv.levelParams = true := by
      rcases hb : ConLeche.Name.nodup cv.levelParams
      · simp [hb, throw, throwThe, MonadExceptOf.throw] at h
      · rfl
    rw [if_pos hnd] at h
    have hnd' : cv.levelParams.Nodup := nodup_of_nameNodup hnd
    split at h
    · simp at h
    rename_i crest hcrest
    have hcrest' := unwrapOr_ok hcrest
    split at h
    · simp at h
    rename_i ty hty
    split at h
    · simp at h
    rename_i sv hsv
    obtain ⟨ca, hfr, hC, hca, hgr, hsm⟩ := hprem (cv, nF) crest (hQ _ List.mem_cons_self) hcrest'
      ⟨ty, hty⟩
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨ks, nds, cur, st₁⟩ := r
    obtain ⟨hI₁, hpos⟩ := nestFields_acc (P := fun _ => True) hrec nF 0 crest st ks nds cur st₁
      (hi + nF) hr (fun _ _ => trivial) (by omega) (by rw [hhi]; omega) hfr hI hC hca hgr
      (by simpa using hR) (by simpa using hsm)
    dsimp only at h
    by_cases hrs : st₁.restart.isSome = true
    · rw [if_pos hrs] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨hI₁, fun hc => ?_⟩
      rw [hc] at hrs; exact nomatch hrs
    rw [if_neg hrs] at h
    have hc₁ : st₁.restart = none := by simpa using hrs
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hu4
    split at h
    · rename_i hok
      obtain ⟨hI', hrest⟩ := ih st₁ st' (fun x hx => hQ x (List.mem_cons_of_mem _ hx)) h hI₁
      refine ⟨hI', fun hc x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [Bool.and_eq_true] at hok
        obtain ⟨hPi, -, hO⟩ := hpos hc₁
        refine ⟨hnd', crest, ca, _, st, ks, nds, cur, st₁, hcrest', hfr.2.1, hca, hr, hc₁,
          fun i hil hne => ?_, hok.1, hok.2, by rw [hhi] at hPi; simpa using hPi, by simpa using hO⟩
        have := hu4
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
          not_exists, not_and] at this
        cases hU : ConLeche.structUsedLater (ConLeche.closeTelescope nds hi cur) 0 i
        · rfl
        · exact absurd hU (this i hil hne)
      · exact hrest hc x hx
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Sizes through the frame's readings -/

/-- Hereditary sizes move back along fields reading alike. -/
theorem FieldsBound.of_eqOn' {w : Nat} :
    ∀ {Δ As Bs : List AnnotTerm} {ρ : Nat → V}, FieldsEqOn V Δ As Bs → Sat V Δ ρ →
      FieldsBound w ρ Bs → FieldsBound w ρ As
  | _, [], [], _, _, _, _ => trivial
  | Δ, A :: As, B :: Bs, ρ, hE, hs, hb => by
    obtain ⟨h0, hrest⟩ := hE
    obtain ⟨hB, hBs⟩ := hb
    refine ⟨by rw [h0 ρ hs]; exact hB, fun a ha => ?_⟩
    exact FieldsBound.of_eqOn' hrest (Sat_cons V hs ha) (hBs a (by rw [← h0 ρ hs]; exact ha))
  | _, [], _ :: _, _, hE, _, _ => hE.elim
  | _, _ :: _, [], _, hE, _, _ => hE.elim

/-- Hereditary sizes cross frames related at the applied holes. -/
theorem fieldsBound_congr_holeApp {k nP w : Nat} :
    ∀ (Fs : List AnnotTerm) {lo : Nat}, (∀ l F, Fs[l]? = some F → HoleApp k nP (lo + l) F) →
      ∀ {σ σ' : Nat → V}, HoleAgree k nP lo σ σ' → FieldsBound w σ Fs → FieldsBound w σ' Fs
  | [], _, _, _, _, _, _ => trivial
  | F :: Fs, lo, hF, σ, σ', h, hok => by
    have h0 : HoleApp k nP lo F := by simpa using hF 0 F rfl
    have ht : ∀ l F', Fs[l]? = some F' → HoleApp k nP (lo + 1 + l) F' := by
      intro l F' hl
      have := hF (l + 1) F' (by simpa using hl)
      rwa [show lo + (l + 1) = lo + 1 + l by omega] at this
    have he := interp_congr_holeApp h0 h
    refine ⟨he ▸ hok.1, fun a ha => ?_⟩
    exact fieldsBound_congr_holeApp Fs ht (h.cons a) (hok.2 a (he ▸ ha))

/-- Hereditary sizes through a substitution. -/
theorem fieldsBound_substTele {w : Nat} (τ : Nat → AnnotTerm) :
    ∀ (ab : List (Nat × Nat × AnnotTerm)) (k : Nat) (ρ : Nat → V),
      FieldsBound w (substE V τ k ρ) (ab.map (·.2.2)) →
      FieldsBound w ρ ((AnnotTerm.substTele τ k ab).map (·.2.2))
  | [], _, _, _ => trivial
  | d :: ab, k, ρ, ⟨h1, h2⟩ => by
    refine ⟨?_, fun a ha => ?_⟩
    · show interp V ρ (AnnotTerm.substAV τ d.2.2 k) ∈ˢ _
      rw [interp_substAV]; exact h1
    · have ha' : a ∈ˢ interp V (substE V τ k ρ) d.2.2 := by
        have := ha
        simp only [interp_substAV] at this
        exact this
      have := h2 a ha'
      rw [cons_substE] at this
      exact fieldsBound_substTele τ ab (k + 1) (cons a ρ) this

/-! ## The hole fit through a frame's normal form -/

/-- **A hole fit of a recorded constructor is a fit of the walked normal
form** at a frame whose substituted valuation agrees with the hole frame
at the applied holes. -/
theorem spineFitN_of_hfits {D : LfpDatum V} {ψ : Name → Nat} {c j : Nat}
    {ab : List (Nat × Nat × AnnotTerm)} {Δ Δ' : List AnnotTerm} {N : List AnnotTerm}
    (hEq : FieldsEqOn V Δ (ab.map (·.2.2)) (D.fields ψ c j)) {τ : Nat → AnnotTerm}
    (hEN : FieldsEqOn V Δ' ((AnnotTerm.substTele τ 0 ab).map (·.2.2)) N)
    (hha : D.HolesApplied ψ c j)
    {σ ρp X : Nat → V} {vs : List V} (hv : substE V τ 0 σ = consList vs ρp)
    (hag : HoleAgree D.k (D.params ψ).length 0 (D.frame ψ ρp X) (consList vs ρp))
    (hsat : Sat V Δ (consList vs ρp)) (hsat' : Sat V Δ' σ) {t : V} {fs : List V}
    (hf : D.HFits ψ ρp X t c j fs) : SpineFit σ N fs := by
  obtain ⟨-, hsp, -⟩ := (LfpDatum.hfits_iff_of_holeAgree hha hag).mp hf
  refine (hEN.spineFit_iff hsat' fs).mp ((spineFit_substTele V τ ab 0 σ fs).mpr ?_)
  rw [hv]; exact (hEq.spineFit_iff hsat fs).mpr hsp

/-- **The hole fit moves along the walk's relation** once the normal form
fits at the target (the result's indices are hole-free along the relation
under the normal form). -/
theorem hfits_of_spineFitN {D : LfpDatum V} {ψ : Name → Nat} {c j nF nPc : Nat}
    {ctx : NestCtx} {hi' : Nat} {cur : Expr}
    {ab : List (Nat × Nat × AnnotTerm)} {Δ Δ' : List AnnotTerm} {N : List AnnotTerm}
    (hEq : FieldsEqOn V Δ (ab.map (·.2.2)) (D.fields ψ c j))
    (hlen : ab.length = nF) (hnP : (D.params ψ).length = nPc)
    {τ : Nat → AnnotTerm} {p : Nat} (hhead : (τ (D.k - 1 - c)).liftN nF 0 = .bvar p)
    (hEN : FieldsEqOn V Δ' ((AnnotTerm.substTele τ 0 ab).map (·.2.2)) N)
    {R' : FrameRel V}
    (hresAt : ResultAt m φ ctx.nP hi' (hi' + nF) cur (R'.underBothTele N)
      (AnnotTerm.substAV τ (AnnotTerm.mkAppN (.bvar (nF + (D.k - 1 - c)))
          ((List.range nPc).map (fun i => AnnotTerm.bvar (nPc + D.k + nF - 1 - i))
            ++ D.resIdx ψ c j)) ab.length))
    (hres : ConLeche.nestResHead cur = true)
    (hidx : (cur.getAppArgs.drop nPc).all (fun x => !x.nestOcc ctx.names ctx.nP hi') = true)
    (hha : D.HolesApplied ψ c j)
    {σS σL ρpS ρpL XS XL : Nat → V} {vsS vsL : List V} (hR : R' σS σL)
    (hvS : substE V τ 0 σS = consList vsS ρpS) (hvL : substE V τ 0 σL = consList vsL ρpL)
    (hagS : HoleAgree D.k nPc 0 (D.frame ψ ρpS XS) (consList vsS ρpS))
    (hagL : HoleAgree D.k nPc 0 (D.frame ψ ρpL XL) (consList vsL ρpL))
    (hsatS : Sat V Δ (consList vsS ρpS)) (hsatL : Sat V Δ (consList vsL ρpL))
    (hsatS' : Sat V Δ' σS) (hsatL' : Sat V Δ' σL)
    {t : V} {fs : List V} (hf : D.HFits ψ ρpS XS t c j fs) (hL : SpineFit σL N fs) :
    D.HFits ψ ρpL XL t c j fs := by
  rw [← hnP] at hagS hagL
  obtain ⟨hjS, -, hresS⟩ := (LfpDatum.hfits_iff_of_holeAgree hha hagS).mp hf
  have hS : SpineFit σS N fs := spineFitN_of_hfits hEq hEN hha hvS hagS hsatS hsatS' hf
  have hlenS : (AnnotTerm.substTele τ 0 ab).length = nF := by
    rw [substTele_length, hlen]
  have hspL : SpineFit (consList vsL ρpL) (D.fields ψ c j) fs := by
    refine (hEq.spineFit_iff hsatL fs).mp ?_
    rw [← hvL]
    exact (spineFit_substTele V τ ab 0 σL fs).mp ((hEN.spineFit_iff hsatL' fs).mpr hL)
  refine (LfpDatum.hfits_iff_of_holeAgree hha hagL).mpr ⟨hjS, hspL, fun l hl => ?_⟩
  obtain ⟨e, he, heq⟩ := hresS l hl
  refine ⟨e, he, ?_⟩
  rw [← heq]
  obtain ⟨hag, hrd, hws⟩ := hresAt
  have hfl : fs.length = nF := by
    rw [hS.length_eq, ← hEN.length_eq, List.length_map, hlenS]
  rw [hlen, AnnotTerm.substAV_mkAppN, AnnotTerm.substAV_bvar_ge τ (by omega),
    show nF + (D.k - 1 - c) - nF = D.k - 1 - c by omega, hhead] at hrd
  have hspine := Expr.mkAppN_getApp cur
  obtain ⟨i, ty, hfn⟩ : ∃ i ty, cur.getAppFn = .fvar i ty := by
    unfold ConLeche.nestResHead at hres
    split at hres
    · rename_i i ty heq; exact ⟨i, ty, heq⟩
    · exact nomatch hres
  rw [← hspine, hfn] at hrd hws
  obtain ⟨fa, vs, hfa, hsp, hvs⟩ := denoteMeta_mkAppN_inv hrd
  rw [denoteMeta_fvar] at hfa
  cases hfa
  obtain ⟨-, hvs⟩ := mkAppN_bvar_inj hvs
  rw [List.map_append] at hvs
  have hwsargs := (wScoped_mkAppN _ hws).2
  have hlv := DenoteMetaSpine.length_eq hsp
  rw [← List.take_append_drop nPc cur.getAppArgs] at hsp
  obtain ⟨vs₁, vs₂, hv12, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
  have hl₁ : vs₁.length = nPc := by
    rw [← DenoteMetaSpine.length_eq hsp₁, List.length_take]
    have : cur.getAppArgs.length = nPc + (D.resIdx ψ c j).length := by
      rw [hlv, ← hvs]; simp
    omega
  rw [hv12] at hvs
  have hvs₂ : vs₂ = (D.resIdx ψ c j).map (AnnotTerm.substAV τ · nF) := by
    have := congrArg (List.drop nPc) hvs
    rw [List.drop_left' hl₁, List.drop_left' (by simp)] at this
    rw [this]
  have hconst := constOn_spine (m := m) (φ := φ) (names := ctx.names) hag (by omega) hsp₂
    (fun a ha => ⟨hwsargs a (List.mem_of_mem_drop ha), by
      simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hidx
      exact hidx a ha⟩)
  have hce := hconst (AnnotTerm.substAV τ e nF)
    (by rw [hvs₂]; exact List.mem_map_of_mem (List.mem_of_getElem? he))
    _ _ (FrameRel.underBothTele_consList _ fs hR hS hL)
  rw [interp_substAV, interp_substAV, ← hfl, ← Nat.zero_add fs.length, substE_consList,
    substE_consList, hvS, hvL] at hce
  exact hce.symm

/-! ## One frame constructor -/

section Frame

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
  (hfind : ∀ n, ctx.find? n = env.find? n) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List AnnotTerm}
  (hdsa : DenoteMetaSpine mp.base2.acval env φ hi ds dsa)
  (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)
  {grp : List (Name × Expr)} (hg : GrpWf ctx D hi us ds grp)

include hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg

omit hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg in
open Classical in
theorem mixT_grp_eq (Y C : Nat → V) :
    (fun c => if decide (InGrp D grp c) = true then Y c else C c) = mixT (InGrp D grp) C Y := by
  funext c
  unfold mixT
  by_cases h : InGrp D grp c <;> simp [h]

/-- **The frame's walk valuation** at an enclosing frame and a tuple. -/
@[expose] noncomputable def frameVal (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr))
    (dsa : List AnnotTerm) (hi : Nat) (ρ Y : Nat → V) : Nat → V :=
  consList (grpVals D ψ grp (keyFrame dsa hi ρ) Y) ρ

set_option maxHeartbeats 1600000 in
/-- **One constructor of a frame's group is accessible** (the accessibility
twin of `frameIter`'s per-constructor transfer): a bound of the level
reading only the parameter positions, and for every fit of the recorded
constructor at a group tuple mixed into the carrier, a support of the
frame's walk valuation carrying the fit to any related frame and tuple. -/
theorem frameCtor_acc {w : Nat} (hw : w ≠ 0) (hwD : D.w (Level.substFn φ lps us) = w)
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi)
    {Δh : List AnnotTerm} {R₀ : FrameRel V} (hR₀ : HoleRelA mp.base2 φ ctx prog hi Δh R₀)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ'))
    {g j : Nat} (hG : InGrp D grp g) (hj : j < D.nctors g) {cv : ConstantVal} {nF : Nat}
    (hfc : env.find? (D.ctorName g j) = some (.ctorInfo cv ds.length nF))
    (hwk : CtorWalkedA mp.base2 φ w ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)
      us ds ds.length (grpSub us hi grp) rec ((grpTys mp.base2 φ grp).reverse ++ Δh)
      (frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi) (cv, nF)) :
    ∃ TB : (Nat → V) → V, (∀ σ, TB σ ∈ˢ (univ w : V)) ∧
      (∀ σ σ', (∀ q, ParamPos (hi + grp.length) ctx.nP q → σ q = σ' q) → TB σ = TB σ') ∧
      ∀ ρ ρ₀ Y, R₀ ρ ρ₀ →
        InTupleSpace (D.w (Level.substFn φ lps us)) D.N
          (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y →
        ∀ t fs, D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ)
            (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y) t g j fs →
          ∃ (B : V) (gi : V → Occ V), B ⊆ˢ TB (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) ∧
            (∀ b, b ∈ˢ B → Adm (HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog)
                (hi + grp.length)) (gi b) ∧
              Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) (gi b)) ∧
            ∀ ρ' Y', R₀ ρ ρ' →
              InTupleSpace (D.w (Level.substFn φ lps us)) D.N
                (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ')) Y' →
              (∀ b, b ∈ˢ B → Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') (gi b)) →
              D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ')
                (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ')) Y')
                t g j fs := by
  classical
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  have hkNN := h.kN
  have hw' : D.w (Level.substFn φ lps us) ≠ 0 := by rw [hwD]; exact hw
  obtain ⟨-, crest, ca, err, st, ks, nds, cur, st₁, hcr, hcrcl, hca, hfields, hr, hU4, hres, hidx,
    hPi, hO⟩ := hwk
  obtain ⟨-, crest', ab, hcr', ⟨Tys, hlT, hTys, hEqF⟩, hlen, hrd⟩ :=
    crest_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hG.1 hj hfc
  rw [hcr] at hcr'
  obtain rfl := Option.some.inj hcr'
  rw [hca] at hrd
  obtain rfl := Option.some.inj hrd
  have hRA := frameRelA_holeRelA mp hD hnN hkN hfind hlps hnd hul hds hdsa
    hlenP hg hhi hR₀ hfit hw' (grp_arity mp hD hnN hkN hfind hg _)
  have hha := h.holeApp (Level.substFn φ lps us) g (Nat.lt_of_lt_of_le hG.1 hkNN) j hj
  -- the substituted valuation and the hole agreement at a frame and a tuple
  have hvals : ∀ ρ Y, Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) →
      InTupleSpace (D.w (Level.substFn φ lps us)) D.N (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y →
      ∃ vs : List V, substE V (substTau (ds.length + D.k) (hi + grp.length)
          (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0
          (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) = consList vs (keyFrame dsa hi ρ) ∧
        HoleAgree D.k ds.length 0
          (D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ) (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y))
          (consList vs (keyFrame dsa hi ρ)) ∧
        Sat V (D.params (Level.substFn φ lps us) ++ Tys).reverse (consList vs (keyFrame dsa hi ρ)) := by
    intro ρ Y hs hY
    have hS := substE_grp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg
      (keyFrame dsa hi ρ) Y ρ
    refine ⟨_, hS, ?_, ?_⟩
    · have hagS := holeAgree_instance mp hD hs ρ (fun mm => decide (InGrp D grp mm)) Y
        (vs := (List.range D.k).map fun mm =>
          if decide (InGrp D grp mm) = true then D.holeVal (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y mm
          else interp V ρ (mp.base2.acval (D.member mm) (Level.substFn φ lps us)))
        (by simp) (fun m hm => by simp)
      rw [mixT_grp_eq, hlenP] at hagS
      exact hagS
    · exact frameVals_sat mp hD hs hlT hTys (fun mm => decide (InGrp D grp mm)) Y hY ρ
  -- the walked fields are small at every related frame
  have hbd : ∀ σ σ₀, frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi σ σ₀ →
      FieldsBound w σ ((AnnotTerm.substTele (substTau (ds.length + D.k) (hi + grp.length)
        (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0 ab).map (·.2.2)) := by
    rintro _ _ ⟨ρ, ρ', Y, Y', hR, hY, -, rfl, -⟩
    obtain ⟨vs, hS, hag, hsat⟩ := hvals ρ Y (hfit ρ ρ' hR).1 hY
    have hok := (mp.lfp_ok D hD).1.fieldsOk (Level.substFn φ lps us) (keyFrame dsa hi ρ) (hfit ρ ρ' hR).1 hw'
      (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y)
      (mixT_mem (G := InGrp D grp) (lfpTuple_mem _ _ _ _) hY) g (Nat.lt_of_lt_of_le hG.1 hkNN) j hj
    have hb := hok.toBound hw'
    rw [hwD] at hb
    have hb' := fieldsBound_congr_holeApp (D.fields (Level.substFn φ lps us) g j) (lo := 0)
      (fun l F hl => by simpa using hha.1 l F hl) (by rw [hlenP]; exact hag) hb
    refine fieldsBound_substTele _ ab 0 _ ?_
    unfold frameVal at hS
    rw [hS]
    exact FieldsBound.of_eqOn' hEqF hsat hb'
  have hlenW : (AnnotTerm.substTele (substTau (ds.length + D.k) (hi + grp.length)
      (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0 ab).length = nF := by
    rw [substTele_length, hlen]
  have hb : ctx.hiAt ((grpNews us ds hi grp).reverse ++ prog).length = hi + grp.length := by
    rw [List.length_append, List.length_reverse, grpNews_length, ← hhi]
    simp only [NestCtx.hiAt]; omega
  obtain ⟨Af, N, hEN, htele, hAf, hF, hRes⟩ := walkTele_acc (m := mp.base2) (φ := φ) hw hb
    hfields hr hcrcl hU4 hlenW hRA.dom hbd hPi hO
  let ord : Nat → Bool := fun l => ks.getD l .ordinary == .ordinary
  -- the substituted result head is the member's hole
  have hhead : ∃ p, ((substTau (ds.length + D.k) (hi + grp.length)
      (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) (D.k - 1 - g)).liftN nF 0
        = .bvar p := by
    have hgk := hG.1
    simp only [substTau, if_pos (show D.k - 1 - g < ds.length + D.k by omega)]
    rw [show ds.length + D.k - 1 - (D.k - 1 - g) = ds.length + g by omega]
    have hr' := (grpS_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg (ds.length + g)
      (by omega)).2.2
    unfold grpS at hr'
    rw [if_neg (by omega), show ds.length + g - ds.length = g by omega] at hr'
    obtain ⟨i, hi', hgi⟩ : ∃ i, ∃ hi' : i < grp.length, grp[i].1 = D.member g := by
      obtain ⟨i, hi', h'⟩ := List.getElem_of_mem (List.contains_iff_mem.mp hG.2)
      exact ⟨i, by simpa using hi', by simpa using h'⟩
    rw [← hgi, grpSub_mem hg.1 hi', Option.getD_some, denoteMeta_fvar] at hr'
    rw [← Option.some.inj hr']
    exact ⟨hi + grp.length - 1 - (hi + i) + nF, by simp⟩
  obtain ⟨p, hp⟩ := hhead
  refine ⟨teleBound w ord Af 0 N, fun σ => teleBound_mem hw _ _ _ _ _, fun σ σ' hq => ?_, ?_⟩
  · refine teleBound_agrM (k := 0) (M0 := ParamPos (hi + grp.length) ctx.nP) hAf N 0
      (fun i G hG' ho τ τ' hτ => hF i G (by simpa using hG') (by simpa using ho) τ τ'
        (by simpa using hτ)) σ σ' fun i => ⟨fun h => absurd h (Nat.not_lt_zero _),
          fun _ hm => hq i (by simpa using hm)⟩
  intro ρ ρ₀ Y hR hY t fs hf
  have hRσ : frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y)
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) :=
    ⟨ρ, ρ, Y, Y, hR₀.lrefl ρ ρ₀ hR, hY, hY, rfl, rfl⟩
  obtain ⟨vs, hS, hag, hsat⟩ := hvals ρ Y (hfit ρ ρ₀ hR).1 hY
  have hspN := spineFitN_of_hfits hEqF hEN hha hS (by rw [hlenP]; exact hag) hsat
    (hRA.dom _ _ hRσ).1 hf
  obtain ⟨B, gi, hB, hgi, hs⟩ := teleBound_support hw (k := 0) (ord := ord)
    (fun l τ τ' hτ => hAf l τ τ' (hτ.toM _)) N 0 _ _
    (fun i G hG' ho τ τ' hτ => hF i G (by simpa using hG') (by rw [Nat.zero_add] at ho; exact ho)
      τ τ' (by rw [Nat.zero_add] at hτ; exact hτ.toM _))
    htele _ hRσ fs hspN
  refine ⟨B, gi, hB, hgi, fun ρ' Y' hR' hY' hheld => ?_⟩
  have hRσL : frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y)
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') := ⟨ρ, ρ', Y, Y', hR', hY, hY', rfl, rfl⟩
  have hL := hs _ hRσL hheld
  obtain ⟨vsL, hSL, hagL, hsatL⟩ := hvals ρ' Y' (hfit ρ ρ' hR').2 hY'
  exact hfits_of_spineFitN hEqF hlen hlenP hp hEN hRes hres hidx hha hRσL hS hSL hag hagL hsat hsatL
    (hRA.dom _ _ hRσL).1 (hRA.dom _ _ hRσL).2 hf hL

end Frame

end ConLeche.Model
