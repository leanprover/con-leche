module

import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Denote.IndFrame
public import ConLeche.Model.Inductives.ContAccRel
public import ConLeche.Model.Inductives.BlockAccRun
import ConLeche.Model.Inductives.DeclaredShapes
import ConLeche.Model.Inductives.PosDerivShape
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Denote.Shift
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Inductives.ContCtor
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Inductives.TypeStep
import ConLeche.SetModel.Access
import ConLeche.SetTheory.Derive.Natrec

public section

/-!
# A container frame's constructors are accessible

The accessibility twin of `frameIter` (`ContWalk.lean`), over
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

open ConLeche (Env Expr Name Level NestCtx NestHole NestState NestFieldKind CheckError CheckM
  ConstantVal)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The parameter positions -/

/-- **The parameter positions at depth `b`**: position `p` is a variable
below the depth, one of the `nP` parameters. -/
@[expose] def ParamPos (b nP : Nat) : Nat → Prop := fun p => p < b ∧ b - 1 - p < nP

/-- Hereditary sizes move along fields reading alike. -/
theorem FieldsBound.of_eqOn {w : Nat} :
    ∀ {Δ As Bs : List Term} {ρ : Nat → V}, FieldsEqOn V Δ As Bs → Sat V Δ ρ →
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
    ∀ (ks : List ConLeche.NestFieldKind) (nds : List Expr) (d : Nat) (Δ : List Term)
      (abD : List Term) (B : Term),
      abD.length = nds.length →
      OutTele m φ ctx prog ks nds d Δ (mkPisAV abD B) →
      ∃ N : List Term, N.length = nds.length ∧ FieldsEqOn V Δ (abD) N ∧
        ∀ (i : Nat) (nd : Expr), nds[i]? = some nd → ∃ na, N[i]? = some na ∧
          denote m.acval env φ (d + i) nd = some na ∧ nd.looseBVarsBounded 0 = true ∧
          Expr.WScoped (d + i) nd ∧
          (ks.getD i .ordinary = .ordinary →
            nd.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
  | [], [], _, _, [], _, _, _ => ⟨[], rfl, trivial, fun _ _ h => by simp at h⟩
  | k :: ks, nd :: nds, d, Δ, x :: abD, B, hl, hO => by
    obtain ⟨⟨hcl, hws, hord, na, hna, hr⟩, hrest⟩ := hO
    obtain ⟨N, hNl, hE, hN⟩ := outTele_list ks nds (d + 1) (x :: Δ) abD B
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

private theorem shiftQ_congr_caf {Q Q' : Nat → Nat → Prop} (h : ∀ i n, Q i n ↔ Q' i n) :
    ∀ i n, shiftQ Q i n ↔ shiftQ Q' i n
  | 0, _ => Iff.rfl
  | i + 1, n => h i n

private theorem teleAccP_of_piAccThen_def {w : Nat} {ctx : NestCtx} {prog : List NestHole}
    {Qf : FrameRel V → Term → Prop} :
    ∀ (abD abN : List Term) (B : Term) (d l : Nat) (nds : List Expr)
      (Δ : List Term) (R : FrameRel V) (Q : Nat → Nat → Prop),
      FieldsEqOn V Δ abD abN →
      (∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀) →
      (∀ ρ ρ₀, R ρ ρ₀ → w ≠ 0 → FieldsBound w ρ abN) →
      (∀ i n, HoleQ ctx prog d i n ↔ Q i n) → ctx.hiAt prog.length ≤ d →
      PiAccThen w ctx prog Qf abD.length d nds R (mkPisAV abD B) →
      ∃ Af : Nat → (Nat → V) → V, TeleAccP w Af l Q R abN ∧
        (∀ (i : Nat) (nd : Expr), i < abD.length → nds[i]? = some nd →
          InvOn (MentP ctx.nP (ctx.hiAt prog.length) (d + i) nd) (Af (l + i))) ∧
        (∀ l', l ≤ l' → l' < l + abD.length → DefBound (d + (l' - l)) (Af l')) ∧
        Qf (R.underBothTele abN) B
  | [], [], B, _, _, _, _, R, _, _, _, _, _, _, hP =>
    ⟨fun _ _ => empty, trivial, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ hl1 hl2 => absurd hl2 (by simp at hl2 ⊢; omega), hP⟩
  | x :: abD, y :: abN, B, d, l, nds, Δ, R, Q, hE, hdom, hok, hQ, hd, hP => by
    obtain ⟨h0, hrest⟩ := hE
    match nds, hP with
    | [], hP => exact hP.elim
    | nd :: nds', ⟨⟨Af0, hacc0, hsz0, hinv0, hdef0⟩, hP'⟩ =>
      have hUE : R.underBoth x = R.underBoth y := underBoth_eq_of_eqOn h0 hdom
      have hok' : ∀ σ σ₀, R.underBoth x σ σ₀ → w ≠ 0 →
          FieldsBound w σ abN := by
        rintro _ _ ⟨a, ρ, ρ₀, rfl, rfl, hR, ha, -⟩ hw
        have hok0 := hok ρ ρ₀ hR hw
        exact hok0.2 a (h0 ρ (hdom ρ ρ₀ hR).1 ▸ ha)
      have hQ' : ∀ i n, HoleQ ctx prog (d + 1) i n ↔ shiftQ Q i n := by
        intro i n
        rw [← shiftQ_holeQ hd i n]
        exact shiftQ_congr_caf hQ i n
      obtain ⟨Af', htele', hinv', hdef', hQf⟩ :=
        teleAccP_of_piAccThen_def abD abN B (d + 1) (l + 1) nds' (x :: Δ) (R.underBoth x)
          (shiftQ Q) hrest (underBoth_dom hdom) hok' hQ' (by omega) hP'
      classical
      refine ⟨fun l' => if l' = l then Af0 else Af' l', ?_, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_, fun ρ ρ₀ hR => ?_, ?_⟩
        · simp only
          exact AccOn.of_eqOn (P := Sat V Δ) hdom (fun ρ hρ => (h0 ρ hρ).symm)
            (AccOn.congrQ hQ hacc0)
        · simp only
          exact hsz0
        · intro hw
          have hok0 := hok ρ ρ₀ hR hw
          exact mem_tg_of_mem_univ hok0.1
        · rw [← hUE]
          exact TeleAccP.congr _ (l + 1) (shiftQ Q) _
            (fun l' hl' _ => by simp only [ite_eq_right (show l' ≠ l by omega)]) htele'
      · intro i nd' hi hnd
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hnd
          subst hnd
          simp only [Nat.add_zero]
          exact hinv0
        | succ i =>
          simp only [List.getElem?_cons_succ] at hnd
          simp only [ite_eq_right (show l + (i + 1) ≠ l by omega)]
          have := hinv' i nd' (by simpa using hi) hnd
          rwa [show d + 1 + i = d + (i + 1) by omega, show l + 1 + i = l + (i + 1) by omega]
            at this
      · intro l' hl1 hl2
        by_cases hll : l' = l
        · subst hll
          simp only [↓reduceIte, Nat.sub_self, Nat.add_zero]
          exact hdef0
        · simp only [ite_eq_right hll]
          have hd' := hdef' l' (by omega) (by simp only [List.length_cons] at hl2; omega)
          rwa [show d + 1 + (l' - (l + 1)) = d + (l' - l) by omega] at hd'
      · show Qf ((R.underBoth y).underBothTele abN) B
        rw [← hUE]
        exact hQf
  | [], _ :: _, _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim
  | _ :: _, [], _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim

set_option maxHeartbeats 800000 in
/-- **A walked telescope is accessible over its normal form** (see the
module docstring): at any frames `prog`, the base depth the walk's hole
bound `b`; the telescope's shape (one output per field, its result
bvar-closed) and U4 on its normal form. -/
theorem walkTele_acc {w : Nat} {ctx : NestCtx} {prog : List NestHole} {b : Nat}
    (hb : ctx.hiAt prog.length = b) {nF : Nat} {res : Expr}
    {ks : List ConLeche.NestFieldKind} {nds : List Expr}
    (hnl : nds.length = nF) (hrescl : res.looseBVarsBounded 0 = true)
    (hU4 : ∀ i, i < nF → ks.getD i .ordinary ≠ .ordinary →
      ConLeche.structUsedLater (ConLeche.closeTelescope nds b res) 0 i = false)
    {Δ : List Term} {R : FrameRel V} {abD : List Term} {B : Term}
    (hlen : abD.length = nF)
    (hdom : ∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀)
    (hbd : ∀ ρ ρ₀, R ρ ρ₀ → w ≠ 0 → FieldsBound w ρ abD)
    (hP : PiAccThen w ctx prog (ResultAt m φ ctx.nP b (b + nF) res) nF b nds R
      (mkPisAV abD B))
    (hO : OutTele m φ ctx prog ks nds b Δ (mkPisAV abD B)) :
    ∃ (Af : Nat → (Nat → V) → V) (N : List Term),
      FieldsEqOn V Δ (abD) N ∧
      TeleAccP w Af 0 (HoleQ ctx prog b) R N ∧
      (∀ l τ τ', TAgrM 0 (ParamPos b ctx.nP) (fun l => ks.getD l .ordinary == .ordinary) l τ τ' →
        Af l τ = Af l τ') ∧
      (∀ l, DefBound (b + l) (Af l)) ∧
      (∀ (i : Nat) (G : Term), N[i]? = some G → (ks.getD i .ordinary == .ordinary) = true →
        ∀ τ τ', TAgrM 0 (ParamPos b ctx.nP) (fun l => ks.getD l .ordinary == .ordinary) i τ τ' →
          interp V τ G = interp V τ' G) ∧
      ResultAt m φ ctx.nP b (b + nF) res (R.underBothTele N) B := by
  classical
  have hnl' : nds.length = nF := hnl
  obtain ⟨N, hNl, hE, hN⟩ := outTele_list ks nds b Δ abD B
    (by rw [hnl', hlen]) hO
  have hndcl : ∀ p ∈ nds, p.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨na, -, -, h3, -⟩ := hN i nds[i] (by simp [List.getElem?_eq_getElem hi])
    exact h3
  obtain ⟨xs, rest, hop, hxs⟩ := fields_open hrescl hnl hndcl
  let abN : List Term := N
  have habN : abN = N := rfl
  rw [← hlen] at hP
  obtain ⟨Af, htele, hinv, hdef, hQf⟩ := teleAccP_of_piAccThen_def abD abN B b 0 nds Δ R
    (HoleQ ctx prog b) (by rw [habN]; exact hE) hdom
    (fun ρ ρ₀ h hw => by rw [habN]; exact FieldsBound.of_eqOn hE (hdom ρ ρ₀ h).1 (hbd ρ ρ₀ h hw))
    (fun _ _ => Iff.rfl) (by omega) hP
  rw [habN] at htele hQf
  rw [hlen] at hQf
  have hNn : N.length = nF := hNl.trans hnl'
  -- the closed normal form is scoped at the base
  have hW : Expr.WScoped b (ConLeche.closeTelescope nds b res) := by
    refine ConLeche.closeTelescope_wscoped nds b res (fun k nd hk => ?_) ?_
    · obtain ⟨na, -, -, -, h4, -⟩ := hN k nd (by simp [hk])
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
  refine ⟨fun l => if l < nF then Af l else fun _ => empty, N, hE, ?_, ?_, ?_, ?_, hQf⟩
  · refine TeleAccP.congr _ 0 _ _ (fun l' _ hl' => ?_) htele
    have : l' < nF := by simp at hl'; omega
    simp only [ite_eq_left this]
  · -- the bounds read the ordinary slots and the parameters
    intro l τ τ' hag
    by_cases hl : l < nF
    · simp only [ite_eq_left hl]
      obtain ⟨x, hx⟩ : ∃ x, xs[l]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [ConLeche.Verify.openPisAtFvars_length nF hop]; exact hl)⟩
      obtain ⟨nd, hnd, hEx⟩ := hxs l x hx
      have hinvl := hinv l nd (by rw [hlen]; exact hl) hnd
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
    · simp only [ite_eq_right hl]
  · -- definability of the bounds
    intro l'
    by_cases hl : l' < nF
    · simp only [ite_eq_left hl]
      have hd := hdef l' (Nat.zero_le _) (by rw [Nat.zero_add, hlen]; exact hl)
      simpa only [Nat.sub_zero] using hd
    · simp only [ite_eq_right hl]
      exact DefBound.const (b + l') empty
  · -- the ordinary readings read the ordinary slots and the parameters
    intro i G hGi hoi τ τ' hag
    have hi : i < nF := by
      have := (List.getElem?_eq_some_iff.mp hGi).1
      rw [hNl, hnl'] at this; exact this
    obtain ⟨p, hp⟩ : ∃ p, nds[i]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨na, hna, hden, hcln, hws, hord⟩ := hN i p (by simp [hp])
    rw [hGi] at hna
    obtain rfl := Option.some.inj hna
    have hkord : ks.getD i .ordinary = .ordinary := by simpa using hoi
    have hholes : NoBVar (holeP (b + i) ctx.nP b) G := by
      have h := hord hkord
      rw [hb] at h
      exact denote_noBVar_of_nestOcc (m := m) (names := ctx.names) _ _ hws (by omega) h hden
    obtain ⟨x, hx⟩ : ∃ x, xs[i]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [ConLeche.Verify.openPisAtFvars_length nF hop]; exact hi)⟩
    obtain ⟨nd, hnd, hEx⟩ := hxs i x hx
    have hndp : nd = p := by rw [hp] at hnd; simpa using hnd.symm
    subst hndp
    have hxread : denote m.acval env φ (b + i) x.fvarTypeD = some G := by
      rw [denote_erasedEq hEx]; exact hden
    have hslots : NoBVar (fun q => ∃ jj, jj < i ∧ ord jj = false ∧ LfpDatum.fieldSlot jj i q) G := by
      refine noBVar_exists' (P := fun jj q => jj < i ∧ ord jj = false ∧ LfpDatum.fieldSlot jj i q)
        fun jj => ?_
      by_cases hjj : jj < i ∧ ord jj = false
      · have hne : ks.getD jj .ordinary ≠ .ordinary := by simpa [ord] using hjj.2
        exact NoBVar.mono (fun q hq => hq.2.2)
          (u4_fieldSlotAt (m := m) hop hW (hU4 jj (by omega) hne) (by omega) hjj.1 hx hxread)
      · exact NoBVar.mono (fun q hq => absurd ⟨hq.1, hq.2.1⟩ hjj) hholes
    have hbeyond : NoBVar (fun q => b + i ≤ q) G :=
      NoBVar_of_bvarsBelow (denote_bvarsBelow m.cval_closed (b + i) _ hws hcln
        hden) fun _ h => h
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

/-- What a frame's derivation leaves of one constructor, for
accessibility: its level parameters distinct, its instantiated abstracted
type read, its telescope's shape (one output per field, the result
bvar-closed), U4 on its normal form, its result the hole applied
with hole-free indices, the walked fields accessible along the frame
relation and their outputs read like the inputs. -/
@[expose] def CtorWalkedA (m : EnvModel V env) (φ : Name → Nat) (w : Nat) (ctx : NestCtx)
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (names : List Name)
    (holes : List Expr) (Δ : List Term) (R : FrameRel V) (x : ConstantVal × Nat) : Prop :=
  x.1.levelParams.Nodup ∧ ∃ crest ca, ∃ ks : List ConLeche.NestFieldKind, ∃ nds cur,
    ConLeche.nestCrest names us ds holes (x.1.type.instantiateLevelParams x.1.levelParams us)
      = some crest ∧
    crest.looseBVarsBounded 0 = true ∧
    denote m.acval env φ hi crest = some ca ∧
    nds.length = x.2 ∧ cur.looseBVarsBounded 0 = true ∧
    (∀ i, i < x.2 → ks.getD i .ordinary ≠ .ordinary →
      ConLeche.structUsedLater (ConLeche.closeTelescope nds hi cur) 0 i = false) ∧
    ConLeche.nestResHead cur = true ∧
    cur.getAppArgs.all (fun a => !a.nestOcc ctx.names ctx.nP hi) = true ∧
    PiAccThen w ctx prog (ResultAt m φ ctx.nP hi (hi + x.2) cur) x.2 hi nds R ca ∧
    OutTele m φ ctx prog ks nds hi Δ ca

/-! ## Sizes through the frame's readings -/

/-- Hereditary sizes move back along fields reading alike. -/
theorem FieldsBound.of_eqOn' {w : Nat} :
    ∀ {Δ As Bs : List Term} {ρ : Nat → V}, FieldsEqOn V Δ As Bs → Sat V Δ ρ →
      FieldsBound w ρ Bs → FieldsBound w ρ As
  | _, [], [], _, _, _, _ => trivial
  | Δ, A :: As, B :: Bs, ρ, hE, hs, hb => by
    obtain ⟨h0, hrest⟩ := hE
    obtain ⟨hB, hBs⟩ := hb
    refine ⟨by rw [h0 ρ hs]; exact hB, fun a ha => ?_⟩
    exact FieldsBound.of_eqOn' hrest (Sat_cons V hs ha) (hBs a (by rw [← h0 ρ hs]; exact ha))
  | _, [], _ :: _, _, hE, _, _ => hE.elim
  | _, _ :: _, [], _, hE, _, _ => hE.elim

/-- Hereditary sizes through a substitution. -/
theorem fieldsBound_substTele {w : Nat} (τ : Nat → Term) :
    ∀ (ab : List Term) (k : Nat) (ρ : Nat → V),
      FieldsBound w (substE V τ k ρ) (ab) →
      FieldsBound w ρ (Term.substTele τ k ab)
  | [], _, _, _ => trivial
  | d :: ab, k, ρ, ⟨h1, h2⟩ => by
    refine ⟨?_, fun a ha => ?_⟩
    · show interp V ρ (Term.substAV τ d k) ∈ˢ _
      rw [interp_substAV]; exact h1
    · have ha' : a ∈ˢ interp V (substE V τ k ρ) d := by
        have := ha
        simp only [interp_substAV] at this
        exact this
      have := h2 a ha'
      rw [cons_substE] at this
      exact fieldsBound_substTele τ ab (k + 1) (cons a ρ) this

/-! ## The hole fit through a frame's normal form -/

/-- **A hole fit of a recorded constructor is a fit of the walked normal
form** at a frame whose substituted valuation IS the hole frame. -/
theorem spineFitN_of_hfits {D : LfpDatum V} {ψ : Name → Nat} {c j : Nat}
    {ab : List Term} {Δ Δ' : List Term} {N : List Term}
    (hEq : FieldsEqOn V Δ (ab) (D.fields ψ c j)) {τ : Nat → Term}
    (hEN : FieldsEqOn V Δ' (Term.substTele τ 0 ab) N)
    {σ ρp X : Nat → V} (hv : substE V τ 0 σ = D.frame ψ ρp X)
    (hsat : Sat V Δ (D.frame ψ ρp X)) (hsat' : Sat V Δ' σ) {t : V} {fs : List V}
    (hf : D.HFits ψ ρp X t c j fs) : SpineFit σ N fs := by
  obtain ⟨-, hsp, -⟩ := hf
  refine (hEN.spineFit_iff hsat' fs).mp ((spineFit_substTele V τ ab 0 σ fs).mpr ?_)
  rw [hv]; exact (hEq.spineFit_iff hsat fs).mpr hsp

/-- **The hole fit moves along the walk's relation** once the normal form
fits at the target (the result's indices are hole-free along the relation
under the normal form). -/
theorem hfits_of_spineFitN {D : LfpDatum V} {ψ : Name → Nat} {c j nF : Nat}
    {ctx : NestCtx} {hi' : Nat} {cur : Expr}
    {ab : List Term} {Δ Δ' : List Term} {N : List Term}
    (hEq : FieldsEqOn V Δ (ab) (D.fields ψ c j))
    (hlen : ab.length = nF)
    {τ : Nat → Term} {p : Nat} (hhead : (τ (D.k - 1 - c)).liftN nF 0 = .bvar p)
    (hEN : FieldsEqOn V Δ' (Term.substTele τ 0 ab) N)
    {R' : FrameRel V}
    (hresAt : ResultAt m φ ctx.nP hi' (hi' + nF) cur (R'.underBothTele N)
      (Term.substAV τ (Term.mkAppN (.bvar (nF + (D.k - 1 - c))) (D.resIdx ψ c j))
        ab.length))
    (hres : ConLeche.nestResHead cur = true)
    (hidx : cur.getAppArgs.all (fun x => !x.nestOcc ctx.names ctx.nP hi') = true)
    {σS σL ρpS ρpL XS XL : Nat → V} (hR : R' σS σL)
    (hvS : substE V τ 0 σS = D.frame ψ ρpS XS) (hvL : substE V τ 0 σL = D.frame ψ ρpL XL)
    (hsatS : Sat V Δ (D.frame ψ ρpS XS)) (hsatL : Sat V Δ (D.frame ψ ρpL XL))
    (hsatS' : Sat V Δ' σS) (hsatL' : Sat V Δ' σL)
    {t : V} {fs : List V} (hf : D.HFits ψ ρpS XS t c j fs) (hL : SpineFit σL N fs) :
    D.HFits ψ ρpL XL t c j fs := by
  have hS : SpineFit σS N fs := spineFitN_of_hfits hEq hEN hvS hsatS hsatS' hf
  obtain ⟨hjS, -, hresS⟩ := hf
  have hlenS : (Term.substTele τ 0 ab).length = nF := by
    rw [substTele_length, hlen]
  have hspL : SpineFit (D.frame ψ ρpL XL) (D.fields ψ c j) fs := by
    refine (hEq.spineFit_iff hsatL fs).mp ?_
    rw [← hvL]
    exact (spineFit_substTele V τ ab 0 σL fs).mp ((hEN.spineFit_iff hsatL' fs).mpr hL)
  refine ⟨hjS, hspL, fun l hl => ?_⟩
  obtain ⟨e, he, heq⟩ := hresS l hl
  refine ⟨e, he, ?_⟩
  rw [← heq]
  have hfl : fs.length = nF := by
    rw [hS.length_eq, ← hEN.length_eq, hlenS]
  rw [hlen] at hresAt
  have hce := resIdx_constOn hhead hresAt hres hidx e (List.mem_of_getElem? he)
    _ _ (FrameRel.underBothTele_consList _ fs hR hS hL)
  rw [interp_substAV, interp_substAV, ← hfl, ← Nat.zero_add fs.length, substE_consList,
    substE_consList, hvS, hvL] at hce
  exact hce.symm

/-! ## The frame's items as the group tuple's occurrences -/

/-- **The frame's walk valuation** at an enclosing frame and a tuple. -/
@[expose] noncomputable def frameVal (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr))
    (dsa : List Term) (hi : Nat) (ρ Y : Nat → V) : Nat → V :=
  consList (grpVals D ψ grp (keyFrame dsa hi ρ) Y) ρ

/-- **A frame item's occurrence**: the member of the group entry at the
item's position, the index tuple of the spine's indices, the value. -/
@[expose] noncomputable def frameOcc (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr))
    (o : Occ V) : Nat × V × V :=
  (D.names.idxOf (grp.getD (grp.length - 1 - o.1) default).1,
    tupW (D.u (D.names.idxOf (grp.getD (grp.length - 1 - o.1) default).1) ψ) o.2.1, o.2.2)

theorem frameVal_lt {D : LfpDatum V} {ψ : Name → Nat} {grp : List (Name × Expr)}
    {dsa : List Term} {hi : Nat} (ρ Y : Nat → V) {i : Nat} (hi' : i < grp.length) :
    frameVal D ψ grp dsa hi ρ Y i
      = D.holeVal ψ (keyFrame dsa hi ρ) Y
          (D.names.idxOf (grp.getD (grp.length - 1 - i) default).1) := by
  unfold frameVal
  have hl := grpVals_length D ψ grp (keyFrame dsa hi ρ) Y
  have := consList_getElem_pos (ρ := ρ) hl (p := grp.length - 1 - i) (by omega)
  rw [show grp.length - 1 - (grp.length - 1 - i) = i by omega] at this
  rw [this]
  simp only [grpVals, List.getElem_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem frameVal_ge {D : LfpDatum V} {ψ : Name → Nat} {grp : List (Name × Expr)}
    {dsa : List Term} {hi : Nat} (ρ Y : Nat → V) (i : Nat) :
    frameVal D ψ grp dsa hi ρ Y (i + grp.length) = ρ i := by
  unfold frameVal
  have := consList_apply_add (grpVals D ψ grp (keyFrame dsa hi ρ) Y) ρ i
  rwa [grpVals_length] at this

/-- An outer item seen through the frame. -/
theorem holds_frameVal_ge {D : LfpDatum V} {ψ : Name → Nat} {grp : List (Name × Expr)}
    {dsa : List Term} {hi : Nat} {ρ Y : Nat → V} {o : Occ V} (h : grp.length ≤ o.1) :
    Holds (frameVal D ψ grp dsa hi ρ Y) o ↔ Holds ρ (o.1 - grp.length, o.2) := by
  obtain ⟨i, vs, y⟩ := o
  unfold Holds
  simp only at h ⊢
  rw [show i = (i - grp.length) + grp.length by omega, frameVal_ge,
    show i - grp.length + grp.length - grp.length = i - grp.length by omega]

/-- **What one constructor of a frame's group gives** (`frameCtor_acc`): a
definable bound of the level reading only the parameter positions of the
frame's depth `b`, and set-level support graphs of the frame's walk
valuation carrying a fit at a tuple mixed into the carrier to any
related frame and tuple. -/
@[expose] def FrameCtorAcc (w b nP : Nat) (Q' : Nat → Nat → Prop) (R₀ : FrameRel V)
    (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr)) (dsa : List Term) (hi : Nat)
    (g j : Nat) : Prop :=
  ∃ TB : (Nat → V) → V, (∀ σ, w ≠ 0 → TB σ ∈ˢ (tg w : V)) ∧
    (∀ σ σ', (∀ q, ParamPos b nP q → σ q = σ' q) → TB σ = TB σ') ∧
    DefBound b TB ∧
    ∀ ρ ρ₀ Y, R₀ ρ ρ₀ → InTupleSpace (D.w ψ) D.N (D.idx ψ (keyFrame dsa hi ρ)) Y →
      ∀ t fs, D.HFits ψ (keyFrame dsa hi ρ) (mixT (InGrp D grp) (D.carrier ψ (keyFrame dsa hi ρ)) Y)
          t g j fs →
        ∃ (B g' : V), B ⊆ˢ TB (frameVal D ψ grp dsa hi ρ Y) ∧
          (∃ U : V, g' ∈ˢ piSet B (fun _ => U) (hasSigmaPairs_const _ _)) ∧
          (∀ b, b ∈ˢ B → AdmItem Q' (app g' b) ∧ HoldsNonPt (frameVal D ψ grp dsa hi ρ Y) (app g' b)) ∧
          ∀ ρ' Y', R₀ ρ ρ' → InTupleSpace (D.w ψ) D.N (D.idx ψ (keyFrame dsa hi ρ')) Y' →
            (∀ b, b ∈ˢ B → HoldsItem (frameVal D ψ grp dsa hi ρ' Y') (app g' b)) →
            D.HFits ψ (keyFrame dsa hi ρ') (mixT (InGrp D grp) (D.carrier ψ (keyFrame dsa hi ρ')) Y')
              t g j fs

/-- **A frame's accessibility**: a definable bound of the
level reading only the parameter positions at the key's depth, and every
group member's carrier at the key frame accessible along the enclosing
relation with set-level support graphs of admissible enclosing items. -/
@[expose] def FrameAccOut (w : Nat) (ctx : NestCtx) (prog : List NestHole) (hi : Nat)
    (R₀ : FrameRel V) (D : LfpDatum V) (ψ : Name → Nat) (dsa : List Term) (G : Nat → Prop) :
    Prop :=
  ∃ A : (Nat → V) → V, (∀ ρ, w ≠ 0 → A ρ ∈ˢ (tg w : V)) ∧ InvOn (ParamPos hi ctx.nP) A ∧
    DefBound hi A ∧
    ∀ c, G c → ∀ ρ ρ₀, R₀ ρ ρ₀ → ∀ i, i ∈ˢ D.idx ψ (keyFrame dsa hi ρ) c →
      ∀ x, x ∈ˢ app (D.carrier ψ (keyFrame dsa hi ρ) c) i →
        ∃ (B g : V), B ⊆ˢ A ρ ∧
          (∃ U : V, g ∈ˢ piSet B (fun _ => U) (hasSigmaPairs_const _ _)) ∧
          (∀ b, b ∈ˢ B → AdmItem (HoleQ ctx prog hi) (app g b) ∧ HoldsNonPt ρ (app g b)) ∧
          ∀ ρ', R₀ ρ ρ' → (∀ b, b ∈ˢ B → HoldsItem ρ' (app g b)) →
            x ∈ˢ app (D.carrier ψ (keyFrame dsa hi ρ') c) i

private noncomputable def mkTowerEnc (s : V) : Nat → V
  | 0 => empty
  | n + 1 => spair (sfst s) (mkTowerEnc (ssnd s) n)

private theorem mkTowerEnc_encSpineY :
    ∀ {vs : List V} {y : V}, mkTowerEnc (encSpineY vs y) vs.length = Tower.mkTower vs
  | [], _ => rfl
  | _ :: _, _ => by
    rw [List.length_cons, mkTowerEnc, encSpineY, Tower.mkTower, sfst_kpair, ssnd_kpair,
      mkTowerEnc_encSpineY]

private theorem defFun_mkTowerEnc_apply {k : Nat} :
    ∀ (n : Nat) {S : (Fin k → V) → V}, DefFun k S →
      DefFun k fun env => mkTowerEnc (S env) n
  | 0, _, _ => DefFun.empty
  | n + 1, _, hS =>
    DefFun.spair_apply (DefFun.sfst_apply hS) (defFun_mkTowerEnc_apply n (DefFun.ssnd_apply hS))

private noncomputable def tupWEnc (u n : Nat) (s : V) : V :=
  if u = 0 then pt else mkTowerEnc s n

private theorem tupWEnc_encSpineY (u : Nat) {vs : List V} {y : V} :
    tupWEnc u vs.length (encSpineY vs y) = tupW u vs := by
  unfold tupWEnc
  by_cases hu : u = 0
  · subst hu; rw [ite_eq_left rfl, tupW_zero]
  · rw [ite_eq_right hu, tupW_pos hu, mkTowerEnc_encSpineY]

private theorem defFun_tupWEnc_apply {k : Nat} (u n : Nat) {S : (Fin k → V) → V}
    (hS : DefFun k S) : DefFun k fun env => tupWEnc u n (S env) := by
  unfold tupWEnc
  by_cases hu : u = 0
  · subst hu; exact DefFun.pt.congr fun _ => by simp
  · exact (defFun_mkTowerEnc_apply n hS).congr fun _ => by simp [hu]

private noncomputable def downOccN : Nat → V → V
  | 0, o => o
  | n + 1, o => downOccN n (downOcc o)

private theorem downOccN_occEncItem :
    ∀ (n i : Nat) {vs : List V} {y : V}, n ≤ i →
      downOccN n (occEncItem i vs y) = occEncItem (i - n) vs y
  | 0, i, _, _, _ => by simp [downOccN]
  | n + 1, i, vs, y, hle => by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    rw [downOccN, downOcc_occEncItem, downOccN_occEncItem n m (by omega)]
    congr 1; omega

private theorem defFun_downOccN {k : Nat} :
    ∀ (n : Nat) {O : (Fin k → V) → V}, DefFun k O →
      DefFun k fun env => downOccN n (O env)
  | 0, _, hO => hO
  | n + 1, _, hO => defFun_downOccN n (DefFun.downOcc_apply hO)

private noncomputable def frameOccEnc (D : LfpDatum V) (ψ : Name → Nat)
    (grp : List (Name × Expr)) : Nat → V → V
  | 0, _ => empty
  | j + 1, o =>
      open Classical in
      if sfst o = vnat (grp.length - 1 - j) then
        let mm := D.names.idxOf (grp.getD j default).1
        kpair pt (occEnc mm (tupWEnc (D.u mm ψ) (D.ids mm ψ).length (ssnd (ssnd o)))
          (lastVal (ssnd (ssnd o)) (D.ids mm ψ).length))
      else frameOccEnc D ψ grp j o

private theorem defFun_frameOccEnc (D : LfpDatum V) (ψ : Name → Nat)
    (grp : List (Name × Expr)) :
    ∀ k' : Nat, DefFun 1 fun v => frameOccEnc D ψ grp k' (v 0)
  | 0 => DefFun.empty
  | j + 1 => by
    unfold frameOccEnc
    refine DefFun.ite
      (DefRel.eq_apply (DefFun.sfst_apply (DefFun.proj 0))
        (DefFun.const (vnat (grp.length - 1 - j))))
      ?_ (defFun_frameOccEnc D ψ grp j)
    let mm := D.names.idxOf (grp.getD j default).1
    exact DefFun.kpair_apply DefFun.pt
      (DefFun.occEnc_apply mm
        (defFun_tupWEnc_apply (D.u mm ψ) (D.ids mm ψ).length
          (DefFun.ssnd_apply (DefFun.ssnd_apply (DefFun.proj 0))))
        (DefFun.lastVal_apply (D.ids mm ψ).length
          (DefFun.ssnd_apply (DefFun.ssnd_apply (DefFun.proj 0)))))

private theorem frameOccEnc_eq (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr)) :
    ∀ (k' : Nat), k' ≤ grp.length → ∀ {j : Nat} (_hjk : j < k') (_hjg : j < grp.length)
      {vs : List V} {y : V},
      vs.length = (D.ids (D.names.idxOf (grp.getD j default).1) ψ).length →
      frameOccEnc D ψ grp k' (occEncItem (grp.length - 1 - j) vs y) =
        kpair pt (occEnc (D.names.idxOf (grp.getD j default).1)
          (tupW (D.u (D.names.idxOf (grp.getD j default).1) ψ) vs) y)
  | 0, _, _, hjk, _, _, _, _ => absurd hjk (Nat.not_lt_zero _)
  | j' + 1, hk', j, hjk, hjg, vs, y, hlen => by
    unfold frameOccEnc
    by_cases heq : j = j'
    · subst heq
      rw [ite_eq_left (by unfold occEncItem; rw [sfst_kpair])]
      unfold occEncItem
      rw [ssnd_kpair, ssnd_kpair]
      dsimp only
      rw [← hlen, tupWEnc_encSpineY, lastVal_encSpineY]
    · have hne : sfst (occEncItem (grp.length - 1 - j) vs y) ≠
          vnat (grp.length - 1 - j') := by
        unfold occEncItem
        rw [sfst_kpair]
        intro hv
        have := vnat_inj hv
        omega
      rw [ite_eq_right hne]
      exact frameOccEnc_eq D ψ grp j' (by omega) (by omega) hjg hlen

private noncomputable def frameItemMap (D : LfpDatum V) (ψ : Name → Nat)
    (grp : List (Name × Expr)) (o : V) : V :=
  open Classical in
  if ∃ i : Fin grp.length, sfst o = vnat i.val
  then frameOccEnc D ψ grp grp.length o
  else kpair empty (downOccN grp.length o)

private theorem defFun_frameItemMap (D : LfpDatum V) (ψ : Name → Nat)
    (grp : List (Name × Expr)) :
    DefFun 1 fun v => frameItemMap D ψ grp (v 0) := by
  unfold frameItemMap
  refine (DefFun.ite (DefRel.finExists fun i : Fin grp.length =>
      DefRel.eq_apply (DefFun.sfst_apply (DefFun.proj 0)) (DefFun.const (vnat i.val)))
    (defFun_frameOccEnc D ψ grp grp.length)
    (DefFun.kpair_apply DefFun.empty (defFun_downOccN grp.length (DefFun.proj 0)))).congr fun v => by
    by_cases h : ∃ i : Fin grp.length, sfst (v 0) = vnat i.val <;> simp [h]

private theorem frameItemMap_lt (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr))
    {i : Nat} (hi : i < grp.length) {vs : List V} {y : V}
    (hlen : vs.length = (D.ids (D.names.idxOf (grp.getD (grp.length - 1 - i) default).1) ψ).length) :
    frameItemMap D ψ grp (occEncItem i vs y) =
      kpair pt (occEnc (D.names.idxOf (grp.getD (grp.length - 1 - i) default).1)
        (tupW (D.u (D.names.idxOf (grp.getD (grp.length - 1 - i) default).1) ψ) vs) y) := by
  unfold frameItemMap
  have hex : ∃ i' : Fin grp.length, sfst (occEncItem i vs y) = vnat i'.val :=
    ⟨⟨i, hi⟩, by unfold occEncItem; rw [sfst_kpair]⟩
  rw [ite_eq_left hex]
  let j := grp.length - 1 - i
  have hj : j < grp.length := by omega
  have hji : grp.length - 1 - j = i := by dsimp [j]; omega
  have hlen' : vs.length = (D.ids (D.names.idxOf (grp.getD j default).1) ψ).length := by
    simpa [j] using hlen
  have h1 := frameOccEnc_eq D ψ grp grp.length (Nat.le_refl _) hj hj (y := y) hlen'
  rw [hji] at h1
  simpa [j] using h1

private theorem frameItemMap_ge (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr))
    {i : Nat} (hi : grp.length ≤ i) {vs : List V} {y : V} :
    frameItemMap D ψ grp (occEncItem i vs y) =
      kpair empty (occEncItem (i - grp.length) vs y) := by
  unfold frameItemMap
  have hne : ¬ ∃ i' : Fin grp.length, sfst (occEncItem i vs y) = vnat i'.val := by
    rintro ⟨i', heq⟩
    unfold occEncItem at heq
    rw [sfst_kpair] at heq
    have := vnat_inj heq
    omega
  rw [ite_eq_right hne, downOccN_occEncItem _ _ hi]

private theorem defHoleFn_cons_list_caf {r n : Nat} {g : List V → V} (hg : DefHoleFn (r + n) g) :
    ∀ (as : List V), as.length = r → DefHoleFn n fun vs => g (as ++ vs) := by
  induction r generalizing g with
  | zero =>
    intro as hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    rw [Nat.zero_add] at hg
    simpa only [List.nil_append] using hg
  | succ r ih =>
    intro as hlen
    cases as with
    | nil => simp at hlen
    | cons a as =>
      rw [Nat.succ_add] at hg
      exact ih (hg.cons a) as (by simpa using hlen)

private theorem defFun_mkTower_ofFn_caf {k : Nat} :
    ∀ {r : Nat} (As : Fin r → (Fin k → V) → V), (∀ i, DefFun k (As i)) →
      DefFun k fun env => Tower.mkTower (List.ofFn fun i => As i env)
  | 0, _, _ => DefFun.empty.congr fun _ => by simp [Tower.mkTower]
  | r + 1, As, hAs => by
    have hrest := defFun_mkTower_ofFn_caf (fun i : Fin r => As i.succ) (fun i => hAs i.succ)
    exact (DefFun.spair_apply (hAs 0) hrest).congr fun env => by
      simp [List.ofFn_succ, Tower.mkTower]

private theorem defFun_tupW_ofFn_caf (u : Nat) {k r : Nat}
    (As : Fin r → (Fin k → V) → V) (hAs : ∀ i, DefFun k (As i)) :
    DefFun k fun env => tupW u (List.ofFn fun i => As i env) := by
  by_cases hu : u = 0
  · subst hu
    exact DefFun.pt.congr fun _ => (tupW_zero _).symm
  · exact (defFun_mkTower_ofFn_caf As hAs).congr fun _ => (tupW_pos hu _).symm

private theorem holeFam_congr_caf {Fs : List Term} {ρ ρ' : Nat → V} {g g' : List V → V}
    {hg : DefHoleFn Fs.length g} {hg' : DefHoleFn Fs.length g'}
    (hρ : ρ = ρ') (hg_eq : g = g') :
    holeFam ρ Fs g hg = holeFam ρ' Fs g' hg' := by
  subst hρ hg_eq
  rfl

private theorem defFun_holeFam_app_ofFn_caf (u : Nat) (tail : Nat → V) :
    ∀ (Fs : List Term) {k m r : Nat}
      (Xs : Fin m → (Fin k → V) → V) (_ : ∀ i, DefFun k (Xs i))
      (Y : (Fin k → V) → V) (_ : DefFun k Y)
      (As : Fin r → (Fin k → V) → V) (_ : ∀ i, DefFun k (As i)),
      DefFun k fun env =>
        holeFam (Semantics.prepend (fun i => Xs i env) tail) Fs
          (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ vs)))
          (defHoleFn_cons_list_caf (DefHoleFn.of_app_tupW (Y env) u (r + Fs.length))
            (List.ofFn fun i => As i env) List.length_ofFn)
  | [], k, m, r, Xs, hXs, Y, hY, As, hAs =>
    (DefFun.app_apply hY (defFun_tupW_ofFn_caf u As hAs)).congr fun env => by
      rw [holeFam_nil, List.append_nil]
  | F :: Fs, k, m, r, Xs, hXs, Y, hY, As, hAs => by
    have hF : DefFun k fun env => interp V (Semantics.prepend (fun i => Xs i env) tail) F :=
      (interp_defFun_prepend tail m F).comp hXs
    let Xs' : Fin (m + 1) → (Fin (k + 1) → V) → V := fun i w =>
      if h0 : i.val = 0 then w 0 else Xs ⟨i.val - 1, by omega⟩ (ftail w)
    have hXs' : ∀ i, DefFun (k + 1) (Xs' i) := fun ⟨i, hi⟩ => by
      dsimp only [Xs']
      split
      · exact DefFun.proj 0
      · exact (hXs _).weaken
    let Y' : (Fin (k + 1) → V) → V := fun w => Y (ftail w)
    have hY' : DefFun (k + 1) Y' := hY.weaken
    let As' : Fin (r + 1) → (Fin (k + 1) → V) → V := fun i w =>
      if hi : i.val < r then As ⟨i.val, hi⟩ (ftail w) else w 0
    have hAs' : ∀ i, DefFun (k + 1) (As' i) := fun ⟨i, hi⟩ => by
      dsimp only [As']
      split
      · exact (hAs _).weaken
      · exact DefFun.proj 0
    have hrec := defFun_holeFam_app_ofFn_caf u tail Fs Xs' hXs' Y' hY' As' hAs'
    let hg_all : ∀ env, DefHoleFn (F :: Fs).length
        (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ vs))) := fun env =>
      defHoleFn_cons_list_caf (DefHoleFn.of_app_tupW (Y env) u (r + (F :: Fs).length))
        (List.ofFn fun i => As i env) List.length_ofFn
    let F_lam : V → (Fin k → V) → V := fun x env =>
      holeFam (cons x (Semantics.prepend (fun i => Xs i env) tail)) Fs
        (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ x :: vs)))
        ((hg_all env).cons x)
    have hrec' : DefFun (k + 1) fun w => F_lam (w 0) (ftail w) := by
      refine hrec.congr fun w => ?_
      have hρ : Semantics.prepend (fun i => Xs' i w) tail =
          cons (w 0) (Semantics.prepend (fun i => Xs i (ftail w)) tail) := by
        funext j
        cases j with
        | zero => simp [Semantics.prepend, Xs']
        | succ j =>
          by_cases hj : j < m
          · have hj1 : j + 1 < m + 1 := by omega
            simp [Semantics.prepend, hj, hj1, Xs', cons]
          · have hj1 : ¬ (j + 1 < m + 1) := by omega
            simp only [Semantics.prepend, hj, hj1, ↓reduceDIte, cons]
            congr 1; omega
      have hA_eq : List.ofFn (fun i => As' i w) =
          List.ofFn (fun i => As i (ftail w)) ++ [w 0] := by
        apply List.ext_getElem (by simp)
        intro j h1 h2
        simp only [List.length_ofFn] at h1
        simp only [List.getElem_ofFn, As']
        by_cases hj : j < r
        · simp [hj, List.getElem_append_left]
        · have hjr : j = r := by omega
          subst hjr
          simp [List.getElem_append_right]
      have h_fn : (fun vs => app (Y' w) (tupW u (List.ofFn (fun i => As' i w) ++ vs))) =
          (fun vs => app (Y (ftail w)) (tupW u (List.ofFn (fun i => As i (ftail w)) ++ w 0 :: vs))) := by
        funext vs
        change app (Y (ftail w)) (tupW u (List.ofFn (fun i => As' i w) ++ vs)) = _
        rw [hA_eq, List.append_assoc, List.singleton_append]
      exact holeFam_congr_caf hρ h_fn
    have hGraph : ∀ env, HasGraph (interp V (Semantics.prepend (fun i => Xs i env) tail) F)
        (fun x => F_lam x env) := fun env =>
      holeFam_hasGraph (Semantics.prepend (fun i => Xs i env) tail) F Fs _ (hg_all env)
    refine (DefFun.lamV_apply_curry (F := F_lam) (h := hGraph) hrec' hF).congr fun env => ?_
    exact (holeFam_cons (Semantics.prepend (fun i => Xs i env) tail) F Fs _ (hg_all env)).symm

private noncomputable def finUnion_caf (f : Nat → V) : Nat → V
  | 0 => empty
  | n + 1 => binUnion (finUnion_caf f n) (f n)

private theorem subset_finUnion_caf {f : Nat → V} :
    ∀ {n i : Nat}, i < n → f i ⊆ˢ finUnion_caf f n
  | 0, _, h => absurd h (by omega)
  | n + 1, i, h => by
    intro x hx
    show x ∈ˢ binUnion (finUnion_caf f n) (f n)
    by_cases hin : i = n
    · subst hin; exact mem_binUnion.mpr (Or.inr hx)
    · exact mem_binUnion.mpr (Or.inl (subset_finUnion_caf (by omega) x hx))

private theorem finUnion_mem_caf {w' : Nat} (hw : w' ≠ 0) {f : Nat → V} :
    ∀ {n : Nat}, (∀ i, i < n → f i ∈ˢ (tg w' : V)) → finUnion_caf f n ∈ˢ (tg w' : V)
  | 0, _ => empty_mem_tg w'
  | n + 1, h => (tg_isGrothendieck hw).binUnion_mem
      (finUnion_mem_caf hw fun i hi => h i (by omega)) (h n (by omega))

private theorem defFun_finUnion_caf {p : Nat} :
    ∀ (n : Nat) {f : Nat → (Fin p → V) → V}, (∀ i, i < n → DefFun p (f i)) →
      DefFun p fun env => finUnion_caf (fun i => f i env) n
  | 0, _, _ => DefFun.empty
  | n + 1, f, hf =>
    DefFun.binUnion_apply (defFun_finUnion_caf n fun i hi => hf i (by omega)) (hf n (by omega))

private theorem defFun_accPaths_apply {p : Nat} {A : (Fin p → V) → V} (hA : DefFun p A) :
    DefFun p fun env => accPaths (A env) := by
  have hN : DefFun (p + 1) fun w => accPathsN (A (ftail w)) (w 0) := by
    unfold accPathsN
    have hS : DefFun (((p + 1) + 2) + 2) fun w =>
        accPathsStep (A (ftail (ftail (ftail (ftail (ftail w)))))) (w 0) (w 1) := by
      unfold accPathsStep
      exact DefFun.sigmaPairs_apply_curry hA.weaken.weaken.weaken.weaken.weaken (DefFun.proj 2)
    have hAtt := defRel_isAttempt_param
      (Z := fun _ : Fin ((p + 1) + 2) → V => (unitSet : V))
      (S := fun w => accPathsStep (A (ftail (ftail (ftail (ftail (ftail w)))))) (w 0) (w 1))
      (N := fun w : Fin ((p + 1) + 2) → V => w 2)
      (G := fun w : Fin ((p + 1) + 2) → V => w 0)
      DefFun.unitSet hS (DefFun.proj 2) (DefFun.proj 0)
    have hAtt' : DefRel ((p + 1) + 2) fun w =>
        IsAttempt unitSet (accPathsStep (A (ftail (ftail (ftail w))))) (w 2) (w 0) :=
      hAtt.congr fun _ => by simp only [fcons_zero]; exact Iff.rfl
    have hR : DefRel ((p + 1) + 1) fun v =>
        ∃ g, IsAttempt unitSet (accPathsStep (A (ftail (ftail v)))) (v 1) g ∧ kpair (v 1) (v 0) ∈ˢ g :=
      DefRel.exists_curry (DefRel.and hAtt'
        (DefRel.mem_apply (DefFun.kpair_apply (DefFun.proj 2) (DefFun.proj 1)) (DefFun.proj 0)))
    exact (DefFun.uniqueChoice_curry hR).congr fun _ => rfl
  exact DefFun.omegaUnion_apply_curry hN

private theorem keyFrame_prepend_eq_caf {dsa : List Term} {hi : Nat} (tail : Nat → V)
    (xs : Fin hi → V) :
    keyFrame dsa hi (Semantics.prepend xs tail) =
      Semantics.prepend (fun j : Fin dsa.length =>
        interp V (Semantics.prepend xs tail) (dsa[dsa.length - 1 - j.val]'(by omega))) tail := by
  funext k
  unfold keyFrame
  have htail : (fun j => Semantics.prepend xs tail (j + hi)) = tail := by
    funext j
    have hge : ¬ (j + hi < hi) := by omega
    simp only [Semantics.prepend, hge, ↓reduceDIte]
    congr 1; omega
  rw [htail]
  by_cases hk : k < dsa.length
  · simp only [Semantics.prepend, hk, ↓reduceDIte]
    have hk' : dsa.length - 1 - k < dsa.length := by omega
    have hpos := consList_getElem_pos (ρ := tail)
      (by simp : (List.map (interp V (Semantics.prepend xs tail)) dsa).length = dsa.length) hk'
    rw [show dsa.length - 1 - (dsa.length - 1 - k) = k by omega] at hpos
    rw [hpos]
    simp [List.getElem_map]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + dsa.length := ⟨k - dsa.length, by omega⟩
    have hm_not : ¬ (m + dsa.length < dsa.length) := by omega
    simp only [Semantics.prepend, hm_not, ↓reduceDIte, Nat.add_sub_cancel]
    have hlen : m + dsa.length = m + (List.map (interp V (Semantics.prepend xs tail)) dsa).length := by simp
    rw [hlen, consList_apply_add]

private theorem defRel_holdsQ_prepend {qs : List (Nat × Nat)} {d : Nat} (tail : Nat → V) :
    DefRel (d + 1) fun v => HoldsQ (Semantics.prepend (ftail v) tail) qs (v 0) := by
  induction qs with
  | nil => exact DefRel.false
  | cons p qs ih =>
    unfold HoldsQ
    refine DefRel.or ?_ ih
    by_cases hp : p.1 < d
    · exact (DefRel.holdsAt_apply p.1 p.2
        (DefFun.proj (k := d + 1) ⟨p.1 + 1, by omega⟩) (DefFun.proj 0)).congr fun v => by
        simp [Semantics.prepend, ftail, hp]
    · exact (DefRel.holdsAt_apply p.1 p.2
        (DefFun.const (tail (p.1 - d))) (DefFun.proj 0)).congr fun v => by
        simp [Semantics.prepend, hp]

private theorem defRel_exists_spineFit_prepend {d : Nat} (tail : Nat → V) :
    ∀ (Ts : List Term) {m : Nat} (Xs : Fin m → (Fin d → V) → V), (∀ i, DefFun d (Xs i)) →
      DefRel d fun v => ∃ is : List V, SpineFit (Semantics.prepend (fun i => Xs i v) tail) Ts is
  | [], _, _, _ => DefRel.true.congr fun _ => ⟨fun _ => ⟨[], trivial⟩, fun _ => trivial⟩
  | F :: Ts, m, Xs, hXs => by
    let Xs' : Fin (m + 1) → (Fin (d + 1) → V) → V := fun i w =>
      if h0 : i.val = 0 then w 0 else Xs ⟨i.val - 1, by omega⟩ (ftail w)
    have hXs' : ∀ i, DefFun (d + 1) (Xs' i) := fun ⟨i, hi⟩ => by
      dsimp only [Xs']
      split
      · exact DefFun.proj 0
      · exact (hXs _).weaken
    have ih := defRel_exists_spineFit_prepend tail Ts Xs' hXs'
    have hF : DefFun (d + 1) fun w =>
        interp V (Semantics.prepend (fun i => Xs i (ftail w)) tail) F :=
      ((interp_defFun_prepend tail m F).comp hXs).weaken
    let R_body : V → (Fin d → V) → Prop := fun a v =>
      a ∈ˢ interp V (Semantics.prepend (fun i => Xs i v) tail) F ∧
        ∃ is : List V, SpineFit (Semantics.prepend (fun i => Xs' i (fcons a v)) tail) Ts is
    have hBody : DefRel (d + 1) fun w => R_body (w 0) (ftail w) := by
      refine (DefRel.and (DefRel.mem_apply (DefFun.proj 0) hF) ih).congr fun w => ?_
      dsimp only [R_body]
      have hfw : fcons (w 0) (ftail w) = w := by
        funext i; cases i using Fin.cases with | zero => rfl | succ i => rfl
      rw [hfw]
    refine (DefRel.exists_curry (R := R_body) hBody).congr fun v => ?_
    constructor
    · rintro ⟨a, ha, vs, hvs⟩
      refine ⟨a :: vs, ha, ?_⟩
      have hp : Semantics.prepend (fun i => Xs' i (fcons a v)) tail =
          cons a (Semantics.prepend (fun i => Xs i v) tail) := by
        funext j
        cases j with
        | zero => simp [Semantics.prepend, Xs', fcons_zero]
        | succ j =>
          by_cases hj : j < m
          · have hj1 : j + 1 < m + 1 := by omega
            simp [Semantics.prepend, hj, hj1, Xs', cons]
          · have hj1 : ¬ (j + 1 < m + 1) := by omega
            simp only [Semantics.prepend, hj, hj1, ↓reduceDIte, cons]
            congr 1; omega
      rwa [← hp]
    · rintro ⟨(_ | ⟨a, vs⟩), hsp⟩
      · exact hsp.elim
      · refine ⟨a, hsp.1, vs, ?_⟩
        have hp : Semantics.prepend (fun i => Xs' i (fcons a v)) tail =
            cons a (Semantics.prepend (fun i => Xs i v) tail) := by
          funext j
          cases j with
          | zero => simp [Semantics.prepend, Xs', fcons_zero]
          | succ j =>
            by_cases hj : j < m
            · have hj1 : j + 1 < m + 1 := by omega
              simp [Semantics.prepend, hj, hj1, Xs', cons]
            · have hj1 : ¬ (j + 1 < m + 1) := by omega
              simp only [Semantics.prepend, hj, hj1, ↓reduceDIte, cons]
              congr 1; omega
        rw [hp]
        exact hsp.2

private theorem defRel_sat_prepend {d m : Nat} (tail : Nat → V)
    (Xs : Fin m → (Fin d → V) → V) (hXs : ∀ i, DefFun d (Xs i))
    (Δ : List Term) :
    DefRel d fun v => Sat V Δ (Semantics.prepend (fun i => Xs i v) tail) := by
  refine (DefRel.finForall (R := fun (idx : Fin Δ.length) (v : Fin d → V) =>
      Semantics.prepend (fun i => Xs i v) tail idx.val ∈ˢ
        interp V (fun j => Semantics.prepend (fun i => Xs i v) tail (j + idx.val + 1)) Δ[idx.val])
    fun idx => ?_).congr fun v => ?_
  · have hhead : DefFun d fun v => Semantics.prepend (fun i => Xs i v) tail idx.val := by
      by_cases hi : idx.val < m
      · exact (hXs ⟨idx.val, hi⟩).congr fun v => by simp [Semantics.prepend, hi]
      · exact (DefFun.const (tail (idx.val - m))).congr fun v => by simp [Semantics.prepend, hi]
    let m' := m - (idx.val + 1)
    let tail' : Nat → V := fun j =>
      if h : idx.val + 1 ≤ m then tail j else tail (j + (idx.val + 1 - m))
    let Xs' : Fin m' → (Fin d → V) → V := fun k v =>
      Xs ⟨k.val + idx.val + 1, by dsimp [m'] at k; omega⟩ v
    have hXs' : ∀ k, DefFun d (Xs' k) := fun k => hXs _
    have harg : DefFun d fun v =>
        interp V (fun j => Semantics.prepend (fun i => Xs i v) tail (j + idx.val + 1)) Δ[idx.val] := by
      refine ((interp_defFun_prepend tail' m' Δ[idx.val]).comp hXs').congr fun v => ?_
      congr 1
      funext j
      by_cases hm : idx.val + 1 ≤ m
      · by_cases hj : j < m'
        · have hj' : j + idx.val + 1 < m := by dsimp [m'] at hj; omega
          simp only [Semantics.prepend, hj, hj', ↓reduceDIte, Xs']
        · have hj' : ¬ (j + idx.val + 1 < m) := by dsimp [m'] at hj; omega
          simp only [Semantics.prepend, hj, hj', ↓reduceDIte, tail', hm]
          congr 1; dsimp [m']; omega
      · have hj1 : ¬ (j < m') := by dsimp [m']; omega
        have hj2 : ¬ (j + idx.val + 1 < m) := by omega
        simp only [Semantics.prepend, hj1, hj2, ↓reduceDIte, tail', hm]
        congr 1; dsimp [m']; omega
    exact DefRel.mem_apply hhead harg
  · unfold Sat
    constructor
    · intro h i Aa hi
      have hil : i < Δ.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [List.getElem?_eq_getElem hil, Option.some.injEq] at hi
      subst hi
      exact h ⟨i, hil⟩
    · intro h idx
      exact h idx.val _ (List.getElem?_eq_getElem idx.isLt)

/-! ## One frame constructor -/

section Frame

variable (mp : EnvModelM V env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
  (hfind : ∀ n, ctx.find? n = env.find? n) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List Term}
  (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa)
  (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)
  {grp : List (Name × Expr)} (hg : GrpWf env ctx D hi us ds grp)

include hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg

omit hD hnN hfind hlps hnd hul hds hdsa hlenP in
/-- **The hole frame reads a tuple mixed into another on the group as the
tuple** (every member is in the group). -/
theorem frame_mixT_grp (ψ : Name → Nat) (ρp C Y : Nat → V) :
    D.frame ψ ρp (mixT (InGrp D grp) C Y) = D.frame ψ ρp Y := by
  unfold LfpDatum.frame
  congr 1
  refine List.map_congr_left fun c hc => ?_
  have hc' : c < D.k := List.mem_range.mp hc
  have hm : mixT (InGrp D grp) C Y c = Y c := by
    unfold mixT; rw [ite_eq_left (inGrp_of_lt hg.2.1 hkN hc')]
  unfold LfpDatum.holeVal
  simp only [hm]

omit hD hnN hfind hlps hnd hul hds hdsa hlenP in
/-- The hole fit at a tuple mixed into another on the group is the fit
at the tuple. -/
theorem hfits_mixT_grp {ψ : Name → Nat} {ρp C Y : Nat → V} {t : V} {c j : Nat} {fs : List V} :
    D.HFits ψ ρp (mixT (InGrp D grp) C Y) t c j fs ↔ D.HFits ψ ρp Y t c j fs := by
  unfold LfpDatum.HFits
  rw [frame_mixT_grp hkN hg]

set_option maxHeartbeats 1600000 in
/-- **One constructor of a frame's group is accessible** (the accessibility
twin of `frameIter`'s per-constructor transfer): a bound of the level
reading only the parameter positions, and for every fit of the recorded
constructor at a group tuple mixed into the carrier, a support of the
frame's walk valuation carrying the fit to any related frame and tuple. -/
theorem frameCtor_acc (hin : RulesInputs V mp.base2 φ) {w : Nat}
    {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi)
    {Δh : List Term} {R₀ : FrameRel V} (hR₀ : HoleRelA mp.base2 φ w ctx prog hi Δh R₀)
    (hΔ : Δh.length = hi) (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x)
    (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    (hkf : ∀ ρ ρ', R₀ ρ ρ' → KeyFit D (Level.substFn φ lps us) dsa hi ρ ∧ KeyFit D (Level.substFn φ lps us) dsa hi ρ')
    (hwD : ∀ ρ ρ', R₀ ρ ρ' → D.w (Level.substFn φ lps us) = w)
    {g j : Nat} (hG : InGrp D grp g) (hj : j < D.nctors g) {cv : ConstantVal} {nF : Nat} {iT : Name}
    (hfc : env.find? (D.ctorName g j) = some (.ctorInfo cv ds.length nF iT))
    (hwk : CtorWalkedA mp.base2 φ w ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)
      us ds (grp.map (·.1)) (grpHoles hi grp) ((grpTys mp.base2 φ hi grp).reverse ++ Δh)
      (frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi) (cv, nF)) :
    FrameCtorAcc w (hi + grp.length) ctx.nP
      (HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)) R₀ D
      (Level.substFn φ lps us) grp dsa hi g j := by
  classical
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  have hkNN := h.kN
  obtain ⟨-, crest, ca, ks, nds, cur, hcr, -, hca, hnl, hcurcl, hU4, hres, hidx, hPi, hO⟩ :=
    hwk
  obtain ⟨-, crest', ab, hcr', hEqF, hlen, hrd⟩ :=
    crest_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hG.1 hj hfc
  rw [hcr] at hcr'
  obtain rfl := Option.some.inj hcr'
  rw [hca] at hrd
  obtain rfl := Option.some.inj hrd
  have hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ') := fun ρ ρ' hr =>
    ⟨(hkf ρ ρ' hr).1.1, (hkf ρ ρ' hr).2.1⟩
  have hRA := frameRelA_holeRelA mp hD hnN hkN hfind hlps hnd hul hds hdsa
    hlenP hg hhi hR₀ hin hΔ hCds hLds hkf hwD (grp_arity mp hD hnN hkN hfind hg _)
  -- the substituted valuation IS the hole frame at a frame and a tuple
  have hvals : ∀ ρ Y, Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) →
      InTupleSpace (D.w (Level.substFn φ lps us)) D.N
        (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y →
      substE V (substTau (ds.length + D.k) (hi + grp.length)
          (grpX mp.base2 φ D hi grp ds (hi + grp.length))) 0
          (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y)
        = D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y ∧
      Sat V (D.params (Level.substFn φ lps us) ++ D.holeTys (Level.substFn φ lps us)).reverse
        (D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y) := fun ρ Y hs hY =>
    ⟨substE_grp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg Y ρ,
      frameVals_sat mp hD hs Y hY⟩
  -- the walked fields are small at every related frame
  have hbd : ∀ σ σ₀, frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi σ σ₀ → w ≠ 0 →
      FieldsBound w σ ((Term.substTele (substTau (ds.length + D.k) (hi + grp.length)
        (grpX mp.base2 φ D hi grp ds (hi + grp.length))) 0 ab)) := by
    rintro _ _ ⟨ρ, ρ', Y, Y', hR, hY, -, rfl, -⟩ hw
    have hw' : D.w (Level.substFn φ lps us) ≠ 0 := by rw [hwD ρ ρ' hR]; exact hw
    obtain ⟨hS, hsat⟩ := hvals ρ Y (hfit ρ ρ' hR).1 hY
    have hok := h.fieldsOk (Level.substFn φ lps us) (keyFrame dsa hi ρ) (hfit ρ ρ' hR).1 hw'
      Y hY g (Nat.lt_of_lt_of_le hG.1 hkNN) j hj
    have hb := hok.toBound hw'
    rw [hwD ρ ρ' hR] at hb
    refine fieldsBound_substTele _ ab 0 _ ?_
    unfold frameVal at hS
    rw [hS]
    exact FieldsBound.of_eqOn' hEqF hsat hb
  have hlenW : (Term.substTele (substTau (ds.length + D.k) (hi + grp.length)
      (grpX mp.base2 φ D hi grp ds (hi + grp.length))) 0 ab).length = nF := by
    rw [substTele_length, hlen]
  have hb : ctx.hiAt ((grpNews us ds hi grp).reverse ++ prog).length = hi + grp.length := by
    rw [List.length_append, List.length_reverse, grpNews_length, ← hhi]
    simp only [NestCtx.hiAt]; omega
  obtain ⟨Af, N, hEN, htele, hAf, hAfDef, hF, hRes⟩ := walkTele_acc (m := mp.base2) (φ := φ) hb
    hnl hcurcl hU4 hlenW hRA.dom hbd hPi hO
  let ord : Nat → Bool := fun l => ks.getD l .ordinary == .ordinary
  -- the substituted result head is the member's hole
  have hhead : ∃ p, ((substTau (ds.length + D.k) (hi + grp.length)
      (grpX mp.base2 φ D hi grp ds (hi + grp.length))) (D.k - 1 - g)).liftN nF 0
        = .bvar p := by
    have hgk := hG.1
    simp only [substTau, ite_eq_left (show D.k - 1 - g < ds.length + D.k by omega)]
    rw [show ds.length + D.k - 1 - (D.k - 1 - g) = ds.length + g by omega]
    have hr' := (grpS_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg (ds.length + g)
      (by omega)).2.2
    unfold grpS at hr'
    rw [ite_eq_right (by omega), show ds.length + g - ds.length = g by omega] at hr'
    obtain ⟨i, hi', -, hidx', hget⟩ := grpHoles_member (hi := hi) hg.2.1 hkN hgk
    rw [hidx', hget, denote_fvar] at hr'
    rw [← Option.some.inj hr']
    exact ⟨hi + grp.length - 1 - (hi + i) + nF, by simp⟩
  obtain ⟨p, hp⟩ := hhead
  refine ⟨teleBound w ord Af 0 N, fun σ hw => teleBound_mem hw _ _ _ _ _, fun σ σ' hq => ?_,
    DefBound.teleBound w ord (hi + grp.length) N 0 (fun l' _ _ => hAfDef l'), ?_⟩
  · refine teleBound_agrM (k := 0) (M0 := ParamPos (hi + grp.length) ctx.nP) hAf N 0
      (fun i G hG' ho τ τ' hτ => hF i G (by simpa using hG') (by simpa using ho) τ τ'
        (by simpa using hτ)) σ σ' fun i => ⟨fun h => absurd h (Nat.not_lt_zero _),
          fun _ hm => hq i (by simpa using hm)⟩
  intro ρ ρ₀ Y hR hY t fs hf
  rw [hfits_mixT_grp hkN hg] at hf
  have hRσ : frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y)
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) :=
    ⟨ρ, ρ, Y, Y, hR₀.lrefl ρ ρ₀ hR, hY, hY, rfl, rfl⟩
  obtain ⟨hS, hsat⟩ := hvals ρ Y (hfit ρ ρ₀ hR).1 hY
  have hspN := spineFitN_of_hfits hEqF hEN hS hsat (hRA.dom _ _ hRσ).1 hf
  obtain ⟨B, g', hB, hg', hitems, hs⟩ := teleBound_support (k := 0) (ord := ord)
    (fun l τ τ' hτ => hAf l τ τ' (hτ.toM _)) (fun l' _ => hAfDef l') N 0 _ _
    (fun i G hG' ho τ τ' hτ => hF i G (by simpa using hG') (by rw [Nat.zero_add] at ho; exact ho)
      τ τ' (by rw [Nat.zero_add] at hτ; exact hτ.toM _))
    htele _ hRσ fs hspN
  refine ⟨B, g', hB, hg', hitems, fun ρ' Y' hR' hY' hheld => ?_⟩
  rw [hfits_mixT_grp hkN hg]
  have hRσL : frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y)
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') := ⟨ρ, ρ', Y, Y', hR', hY, hY', rfl, rfl⟩
  have hL := hs _ hRσL hheld
  obtain ⟨hSL, hsatL⟩ := hvals ρ' Y' (hfit ρ ρ' hR').2 hY'
  exact hfits_of_spineFitN hEqF hlen hp hEN hRes hres hidx hRσL hS hSL hsat hsatL
    (hRA.dom _ _ hRσL).1 (hRA.dom _ _ hRσL).2 hf hL

omit hnd hul in
/-- **A frame item is a group occurrence or an enclosing item.** -/
theorem frame_item_fwd (hin : RulesInputs V mp.base2 φ) {Δh : List Term} (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi) {ρ Y : Nat → V}
    (hs : Sat V Δh ρ) (hkF : KeyFit D (Level.substFn φ lps us) dsa hi ρ)
    {o : Occ V} (hQ : Adm (HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)) o)
    (hH : Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) o) :
    (o.1 < grp.length ∧ InGrp D grp (frameOcc D (Level.substFn φ lps us) grp o).1 ∧
      InTup D.N (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y
        (occEnc (frameOcc D (Level.substFn φ lps us) grp o).1
          (frameOcc D (Level.substFn φ lps us) grp o).2.1
          (frameOcc D (Level.substFn φ lps us) grp o).2.2) ∧
      ∀ ρ', AgreeOff (holeP hi ctx.nP hi) ρ ρ' → Sat V Δh ρ' → KeyFit D (Level.substFn φ lps us) dsa hi ρ' →
        SpineFit (keyFrame dsa hi ρ')
          (D.ids (frameOcc D (Level.substFn φ lps us) grp o).1 (Level.substFn φ lps us)) o.2.1) ∨
    (grp.length ≤ o.1 ∧ Adm (HoleQ ctx prog hi) (o.1 - grp.length, o.2) ∧
      Holds ρ (o.1 - grp.length, o.2)) ∨
    (o.1 < grp.length ∧
      o.2.1.length = (D.ids (frameOcc D (Level.substFn φ lps us) grp o).1
        (Level.substFn φ lps us)).length ∧
      ¬ SpineFit (keyFrame dsa hi ρ)
        (D.ids (frameOcc D (Level.substFn φ lps us) grp o).1 (Level.substFn φ lps us)) o.2.1) := by
  obtain ⟨i, vs, y⟩ := o
  have hnl := grpNews_length us ds hi grp
  have hQ' : HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog)
      (ctx.hiAt prog.length + (grpNews us ds hi grp).length) i vs.length := by
    rw [hnl, hhi]; exact hQ
  rcases holeQ_frame_iff.mp hQ' with ⟨j, hk, hj, rfl, hn⟩ | ⟨hle, hQo⟩
  · -- a new hole
    rw [hnl]
    rw [hnl] at hH
    have hjl : j < grp.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1; rwa [grpNews_length] at this
    have hjk : (grp.getD (grp.length - 1 - (grp.length - 1 - j)) default) = grp[j] := by
      rw [show grp.length - 1 - (grp.length - 1 - j) = j by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
    have hkey : hk.nIdx = grp[j].2.piBinders.1.length := by
      simp only [grpNews, List.getElem?_map, List.getElem?_eq_getElem hjl, Option.map_some,
        Option.some.injEq] at hj
      rw [← hj]
    have hmem : grp[j] ∈ grp := List.getElem_mem hjl
    obtain ⟨mm, hmm, -, hidx, -, hte⟩ :=
      grp_n2 mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hΔ hCds hLds hmem
    have har := grp_arity mp hD hnN hkN hfind hg (Level.substFn φ lps us) _ hmem
    rw [hkey] at hn
    rw [hidx, parsLen_dsa mp hD hdsa hlenP hmm, ← DenoteSpine.length_eq hdsa] at har
    unfold Holds at hH
    simp only at hH
    rw [frameVal_lt ρ Y (by omega), hjk, hidx] at hH
    unfold frameOcc
    simp only
    rw [hjk, hidx]
    rcases grp_hole_full (D := D) (lps := lps) (us := us) (φ := φ) (mm := mm) (keyFrame dsa hi ρ) Y
        (vs := vs) (by omega) with ⟨hfit, he⟩ | ⟨hnf, he⟩
    · refine Or.inl ⟨by omega, ?_, ?_⟩
      · have := grp_inGrp mp hD hnN hkN hfind hlps hg hmem
        rwa [hidx] at this
      rw [he] at hH
      exact ⟨occEnc_mem_occSpace.mpr ⟨Nat.lt_of_lt_of_le hmm (mp.lfp_ok D hD).1.kN, tupW_mem hfit, hH⟩,
        fun ρ' hag hs' hk' =>
          ((spineFit_iff_of_mkPisAV_eq rfl (hte ρ ρ' hag hs hs' hkF hk') vs).1).mp hfit⟩
    · exact Or.inr (Or.inr ⟨by omega, by omega, hnf⟩)
  · exact Or.inr (Or.inl ⟨by rw [hnl] at hle; exact hle,
      by show HoleQ ctx prog hi (i - grp.length) vs.length; rw [hnl, hhi] at hQo; exact hQo,
      (holds_frameVal_ge (by rw [hnl] at hle; exact hle)).mp hH⟩)

omit hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg in
/-- **A group occurrence held by another tuple holds the item at its frame**
(the spine fits the member's index telescope at the key frame). -/
theorem frame_item_bwd {ρ' Y' : Nat → V} {o : Occ V} (hlt : o.1 < grp.length)
    (hfit : SpineFit (keyFrame dsa hi ρ')
      (D.ids (frameOcc D (Level.substFn φ lps us) grp o).1 (Level.substFn φ lps us)) o.2.1)
    (hin : InTup D.N (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ')) Y'
      (occEnc (frameOcc D (Level.substFn φ lps us) grp o).1
        (frameOcc D (Level.substFn φ lps us) grp o).2.1
        (frameOcc D (Level.substFn φ lps us) grp o).2.2)) :
    Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') o := by
  obtain ⟨i, vs, y⟩ := o
  have h2 := LfpDatum.holeVal_app (X := Y') hfit
  unfold frameOcc at h2 hin
  unfold Holds
  simp only at hlt h2 hin ⊢
  rw [frameVal_lt ρ' Y' hlt, h2]
  exact (occEnc_mem_occSpace.mp hin).2.2

omit hnd hul in
/-- **A new-hole item off its fit is held alike at every related frame**:
the hole's value there reads neither the enclosing frame off the holes
(N2's `TeleEq`) nor the tuple (`holeFam_foldl_nofit`; the tuples'
fibres are strict sets or truth values, never the point). -/
theorem frame_item_nofit (hin : RulesInputs V mp.base2 φ) {Δh : List Term} (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    {ρ ρ' Y Y' : Nat → V} {o : Occ V} (hlt : o.1 < grp.length)
    (hag : AgreeOff (holeP hi ctx.nP hi) ρ ρ') (hs : Sat V Δh ρ) (hs' : Sat V Δh ρ')
    (hk : KeyFit D (Level.substFn φ lps us) dsa hi ρ) (hk' : KeyFit D (Level.substFn φ lps us) dsa hi ρ')
    (hY : InTupleSpace (D.w (Level.substFn φ lps us)) D.N
      (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y)
    (hY' : InTupleSpace (D.w (Level.substFn φ lps us)) D.N
      (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ')) Y')
    (hlen : o.2.1.length = (D.ids (frameOcc D (Level.substFn φ lps us) grp o).1
      (Level.substFn φ lps us)).length)
    (hn : ¬ SpineFit (keyFrame dsa hi ρ)
      (D.ids (frameOcc D (Level.substFn φ lps us) grp o).1 (Level.substFn φ lps us)) o.2.1)
    (hH : Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) o) :
    Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') o := by
  obtain ⟨i, vs, y⟩ := o
  simp only at hlt hn hlen
  have hmemG : grp.getD (grp.length - 1 - i) default ∈ grp := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  obtain ⟨mm, hmm, -, hidx, -, hte⟩ :=
    grp_n2 mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hΔ hCds hLds hmemG
  unfold frameOcc at hn hlen
  simp only [hidx] at hn hlen
  unfold Holds at hH ⊢
  simp only at hH ⊢
  rw [frameVal_lt ρ Y hlt, hidx] at hH
  rw [frameVal_lt ρ' Y' hlt, hidx]
  have hmmN : mm < D.N := Nat.lt_of_lt_of_le hmm (mp.lfp_ok D hD).1.kN
  have hT := hte ρ ρ' hag hs hs' hk hk'
  have hne : ∀ ws, SpineFit (keyFrame dsa hi ρ) (D.ids mm (Level.substFn φ lps us)) ws →
      app (Y mm) (tupW (D.u mm (Level.substFn φ lps us)) ws) ≠ pt := fun ws hws =>
    (IsTy_of_mem_strictU (famSpace_app (hY mm hmmN) (tupW_mem hws))).ne_pt
  have hne' : ∀ ws, SpineFit (keyFrame dsa hi ρ) (D.ids mm (Level.substFn φ lps us)) ws →
      app (Y' mm) (tupW (D.u mm (Level.substFn φ lps us)) ws) ≠ pt := fun ws hws =>
    (IsTy_of_mem_strictU (famSpace_app (hY' mm hmmN)
      (tupW_mem (((spineFit_iff_of_mkPisAV_eq rfl hT ws).1).mp hws)))).ne_pt
  unfold LfpDatum.holeVal at hH ⊢
  rw [← holeFam_of_mkPisAV_eq (hg := DefHoleFn.of_app_tupW (Y' mm)
    (D.u mm (Level.substFn φ lps us)) (D.ids mm (Level.substFn φ lps us)).length) rfl hT,
    holeFam_foldl_nofit hne' hne hlen hn]
  exact hH

omit hnd hul in
set_option maxHeartbeats 1600000 in
/-- **The frame's accessibility from its constructors'** (`FrameAccOut`):
the group operator mixed into the carrier (`mixT`) is jointly accessible
in the enclosing frame and the group's own components (`AccJointG`), so
its least tuple — the carrier on the group (`lfpTuple_mixT`) — is
accessible in the enclosing frame (`lfpP_acc_group`).  The stored
container's own facts used are its clause's accessibility (`acc`, at
its `Type`-valued level `w`: the sections' accessibility and
monotonicity) and (W). -/
theorem frameAccOut_of (hin : RulesInputs V mp.base2 φ) {w : Nat}
    {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi)
    {Δh : List Term} {R₀ : FrameRel V} (hR₀ : HoleRelA mp.base2 φ w ctx prog hi Δh R₀)
    (hΔ : Δh.length = hi) (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x)
    (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    (hkf : ∀ ρ ρ', R₀ ρ ρ' → KeyFit D (Level.substFn φ lps us) dsa hi ρ ∧ KeyFit D (Level.substFn φ lps us) dsa hi ρ')
    (hper : ∀ g j, InGrp D grp g → j < D.nctors g →
      FrameCtorAcc w (hi + grp.length) ctx.nP
        (HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)) R₀ D
        (Level.substFn φ lps us) grp dsa hi g j) :
    FrameAccOut w ctx prog hi R₀ D (Level.substFn φ lps us) dsa (InGrp D grp) := by
  classical
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  have hkNN := h.kN
  have hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ') := fun ρ ρ' hr =>
    ⟨(hkf ρ ρ' hr).1.1, (hkf ρ ρ' hr).2.1⟩
  have hnP : ctx.nP ≤ hi := by rw [← hhi]; simp only [NestCtx.hiAt]; omega
  -- the constructors' bounds, as functions
  let TBt : Nat → Nat → (Nat → V) → V := fun g j =>
    if hgj : InGrp D grp g ∧ j < D.nctors g then Classical.choose (hper g j hgj.1 hgj.2)
    else fun _ => empty
  have hTB : ∀ g j (hG : InGrp D grp g) (hj : j < D.nctors g),
      (∀ σ, w ≠ 0 → TBt g j σ ∈ˢ (tg w : V)) ∧
      (∀ σ σ', (∀ q, ParamPos (hi + grp.length) ctx.nP q → σ q = σ' q) → TBt g j σ = TBt g j σ') ∧
      DefBound (hi + grp.length) (TBt g j) ∧
      ∀ ρ ρ₀ Y, R₀ ρ ρ₀ → InTupleSpace (D.w (Level.substFn φ lps us)) D.N
          (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y →
        ∀ t fs, D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ)
            (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y) t g j fs →
          ∃ (B g' : V),
            B ⊆ˢ TBt g j (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) ∧
            (∃ U : V, g' ∈ˢ piSet B (fun _ => U) (hasSigmaPairs_const _ _)) ∧
            (∀ b, b ∈ˢ B → AdmItem (HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog)
                (hi + grp.length)) (app g' b) ∧
              HoldsNonPt (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) (app g' b)) ∧
            ∀ ρ' Y', R₀ ρ ρ' → InTupleSpace (D.w (Level.substFn φ lps us)) D.N
                (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ')) Y' →
              (∀ b, b ∈ˢ B → HoldsItem (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') (app g' b)) →
              D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ')
                (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ')) Y')
                t g j fs := by
    intro g j hG hj
    have e : TBt g j = Classical.choose (hper g j hG hj) := by
      simp only [TBt, dite_eq_left (show InGrp D grp g ∧ j < D.nctors g from ⟨hG, hj⟩)]
    rw [e]
    exact Classical.choose_spec (hper g j hG hj)
  have hTBsz : ∀ g j σ, w ≠ 0 → TBt g j σ ∈ˢ (tg w : V) := by
    intro g j σ hw
    by_cases hgj : InGrp D grp g ∧ j < D.nctors g
    · exact (hTB g j hgj.1 hgj.2).1 σ hw
    · simp only [TBt, dite_eq_right hgj]; exact empty_mem_tg w
  have hTBdef : ∀ g j, DefBound (hi + grp.length) (TBt g j) := by
    intro g j
    by_cases hgj : InGrp D grp g ∧ j < D.nctors g
    · exact (hTB g j hgj.1 hgj.2).2.2.1
    · intro _; exact DefFun.empty.congr fun _ => by simp only [TBt, dite_eq_right hgj]
  -- the frame valuations of two frames agreeing at the parameters agree at the parameters
  have hpar : ∀ (ρ ρ' Y Y' : Nat → V), (∀ q, ParamPos hi ctx.nP q → ρ q = ρ' q) →
      ∀ q, ParamPos (hi + grp.length) ctx.nP q →
        frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y q
          = frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y' q := by
    intro ρ ρ' Y Y' hag q hq
    obtain ⟨hq1, hq2⟩ := hq
    obtain ⟨r, rfl⟩ : ∃ r, q = r + grp.length := ⟨q - grp.length, by omega⟩
    rw [frameVal_ge, frameVal_ge]
    exact hag r ⟨by omega, by omega⟩
  have hTBeq : ∀ g j (ρ ρ' Y Y' : Nat → V), (∀ q, ParamPos hi ctx.nP q → ρ q = ρ' q) →
      TBt g j (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y)
        = TBt g j (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') := by
    intro g j ρ ρ' Y Y' hag
    by_cases hgj : InGrp D grp g ∧ j < D.nctors g
    · exact (hTB g j hgj.1 hgj.2).2.1 _ _ (hpar ρ ρ' Y Y' hag)
    · simp only [TBt, dite_eq_right hgj]
  -- the bound
  let A0 : (Nat → V) → V := fun ρ =>
    finUnion_caf (fun c => finUnion_caf (fun j => TBt c j (frameVal D (Level.substFn φ lps us) grp dsa hi ρ
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)))) (D.nctors c)) D.N
  have hA0 : ∀ ρ, w ≠ 0 → A0 ρ ∈ˢ (tg w : V) := fun ρ hw =>
    finUnion_mem_caf hw fun c _ => finUnion_mem_caf hw fun j _ => hTBsz c j _ hw
  have hA0_def : DefBound hi fun ρ => accPaths (A0 ρ) := fun tail => by
    let ψ := Level.substFn φ lps us
    let Xs_kf : Fin dsa.length → (Fin hi → V) → V := fun l ps =>
      interp V (Semantics.prepend ps tail) (dsa[dsa.length - 1 - l.val]'(by omega))
    have hXs_kf : ∀ l, DefFun hi (Xs_kf l) := fun l =>
      interp_defFun_prepend tail hi (dsa[dsa.length - 1 - l.val]'(by omega))
    have hslot_def : ∀ q : Fin (hi + grp.length), DefFun hi fun ps : Fin hi → V =>
        frameVal D ψ grp dsa hi (Semantics.prepend ps tail)
          (D.carrier ψ (keyFrame dsa hi (Semantics.prepend ps tail))) q.val := by
      intro ⟨q, hq⟩
      by_cases hqg : q < grp.length
      · let j := grp.length - 1 - q
        have hj : j < grp.length := by dsimp [j]; omega
        obtain ⟨mm, hmm, -, hidx, -⟩ := grpMember mp hD hnN hkN hfind hlps hg (List.getElem_mem hj)
        have hmmN : mm < D.N := Nat.lt_of_lt_of_le hmm hkNN
        have hcarr_def : DefFun hi fun ps : Fin hi → V =>
            D.carrier ψ (keyFrame dsa hi (Semantics.prepend ps tail)) mm := by
          refine ((D.defFun_carrier ψ tail dsa.length mm hmmN).comp hXs_kf).congr fun ps => ?_
          rw [keyFrame_prepend_eq_caf]
        have hhole_def : DefFun hi fun ps : Fin hi → V =>
            D.holeVal ψ (keyFrame dsa hi (Semantics.prepend ps tail))
              (D.carrier ψ (keyFrame dsa hi (Semantics.prepend ps tail))) mm := by
          refine (defFun_holeFam_app_ofFn_caf (D.u mm ψ) tail (D.ids mm ψ)
            Xs_kf hXs_kf _ hcarr_def Fin.elim0 (fun i => Fin.elim0 i)).congr fun ps => ?_
          unfold LfpDatum.holeVal
          rw [keyFrame_prepend_eq_caf]
          refine holeFam_congr_caf rfl (funext fun vs => by simp)
        refine hhole_def.congr fun ps => ?_
        rw [frameVal_lt _ _ hqg, show grp.length - 1 - q = j by omega,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hidx]
      · have hge : grp.length ≤ q := by omega
        exact (DefFun.proj (k := hi) ⟨q - grp.length, by omega⟩).congr fun ps => by
          have hqv : (⟨q, hq⟩ : Fin (hi + grp.length)).val = (q - grp.length) + grp.length := by
            dsimp; omega
          rw [hqv, frameVal_ge]
          simp [Semantics.prepend, show q - grp.length < hi by omega]
    have hA0_inner : DefFun hi fun ps => A0 (Semantics.prepend ps tail) := by
      dsimp only [A0]
      refine defFun_finUnion_caf D.N fun c _ => defFun_finUnion_caf (D.nctors c) fun j _ => ?_
      refine ((hTBdef c j tail).comp hslot_def).congr fun ps => ?_
      dsimp only [ψ]
      congr 1
      funext k
      by_cases hk : k < hi + grp.length
      · simp [Semantics.prepend, hk]
      · obtain ⟨m', rfl⟩ : ∃ m', k = m' + (hi + grp.length) := ⟨k - (hi + grp.length), by omega⟩
        have hm' : ¬ (m' + (hi + grp.length) < hi + grp.length) := by omega
        have hm'' : ¬ (m' + hi < hi) := by omega
        simp only [Semantics.prepend, hm', ↓reduceDIte]
        rw [show m' + (hi + grp.length) = (m' + hi) + grp.length by omega, frameVal_ge]
        simp only [Semantics.prepend, hm'', ↓reduceDIte]
        congr 1; omega
    exact defFun_accPaths_apply hA0_inner
  -- the relation's tails and index sets
  have hagree : ∀ ρ ρ', R₀ ρ ρ' → AgreeOff (holeP hi ctx.nP hi) ρ ρ' := by
    intro ρ ρ' hr; have := hR₀.agree ρ ρ' hr; rwa [hhi] at this
  have hIs : ∀ p p', R₀ p p' → ∀ m, InGrp D grp m →
      D.idx (Level.substFn φ lps us) (keyFrame dsa hi p) m
        = D.idx (Level.substFn φ lps us) (keyFrame dsa hi p') m :=
    fun p p' hr m hm => grp_idx_eq mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hΔ hCds hLds hm
      (hagree p p' hr) (hR₀.dom p p' hr).1 (hR₀.dom p p' hr).2 (hkf p p' hr).1 (hkf p p' hr).2
  -- the stored container's accessibility at the key frame, and its monotonicity
  have hDacc : ∀ p p₀, R₀ p p₀ → ∃ A', AccTuple (D.w (Level.substFn φ lps us)) D.N
      (D.idx (Level.substFn φ lps us) (keyFrame dsa hi p)) D.N
      (D.idx (Level.substFn φ lps us) (keyFrame dsa hi p))
      (D.Φ (Level.substFn φ lps us) (keyFrame dsa hi p)) A' :=
    fun p p₀ hp => (h.acc _ _ (hfit p p₀ hp).1).elim fun A hA => ⟨A, hA.2⟩
  have hDmono : ∀ p p₀, R₀ p p₀ → MonoTuple (D.w (Level.substFn φ lps us)) D.N
      (D.idx (Level.substFn φ lps us) (keyFrame dsa hi p))
      (D.Φ (Level.substFn φ lps us) (keyFrame dsa hi p)) :=
    fun p p₀ hp => (hDacc p p₀ hp).elim fun _ hA => hA.monoTuple
  have hDmaps : ∀ p p₀, R₀ p p₀ → MapsTuple (D.w (Level.substFn φ lps us)) D.N
      (D.idx (Level.substFn φ lps us) (keyFrame dsa hi p))
      (D.Φ (Level.substFn φ lps us) (keyFrame dsa hi p)) :=
    fun p p₀ hp => h.maps _ _ (hfit p p₀ hp).1
  obtain ⟨qs, hqs⟩ := finQ_holeQ ctx prog hi
  refine ⟨fun ρ => accPaths (A0 ρ), fun ρ hw => accPaths_mem hw (hA0 ρ hw), fun ρ ρ' hag => ?_, hA0_def, ?_⟩
  · show accPaths (A0 ρ) = accPaths (A0 ρ')
    have : A0 ρ = A0 ρ' := by
      show finUnion_caf _ _ = finUnion_caf _ _
      congr 1; funext c; congr 1; funext j
      exact hTBeq c j ρ ρ' _ _ hag
    rw [this]
  · intro c hc ρ ρ₀ hr i hiI x hx
    let ψ := Level.substFn φ lps us
    let tail : Nat → V := fun j => ρ₀ (j + hi)
    let IsY : (Fin hi → V) → Nat → V := fun p m =>
      D.idx ψ (keyFrame dsa hi (Semantics.prepend p tail)) m
    let Sp : (Fin hi → V) → Prop := fun p =>
      R₀ (Semantics.prepend p tail) (Semantics.prepend p tail)
    let Rp : (Fin hi → V) → (Fin hi → V) → Prop := fun p p' =>
      R₀ (Semantics.prepend p tail) (Semantics.prepend p' tail)
    let HasP : (Fin hi → V) → V → Prop := fun p o =>
      HoldsQ (Semantics.prepend p tail) qs o
    let Θ : (Fin hi → V) → (Nat → V) → Nat → V := fun p Y =>
      D.Φ ψ (keyFrame dsa hi (Semantics.prepend p tail))
        (mixT (InGrp D grp) (D.carrier ψ (keyFrame dsa hi (Semantics.prepend p tail))) Y)
    let A : (Fin hi → V) → V := fun p => A0 (Semantics.prepend p tail)
    let O_sp : (Fin hi → V) → V := fun p => occSpaceQ (Semantics.prepend p tail) qs
    have hSp : DefRel hi Sp := by
      let Gs : Fin (hi + hi) → (Fin hi → V) → V := fun j v =>
        if hj : j.val < hi then v ⟨j.val, hj⟩ else v ⟨j.val - hi, by omega⟩
      have hGs : ∀ j : Fin (hi + hi), DefFun hi (Gs j) := fun j => by
        dsimp only [Gs]; split
        · exact DefFun.proj _
        · exact DefFun.proj _
      refine ((hR₀.defRel.2 tail).comp hGs).congr fun v => ?_
      have e1 : ftake (fun j => Gs j v) = v := by funext ⟨j, hj⟩; simp [ftake, Gs, hj]
      have e2 : fdrop (fun j => Gs j v) = v := by
        funext ⟨j, hj⟩
        have hge : ¬ (hi + j < hi) := by omega
        simp [fdrop, Gs, hge]
      rw [e1, e2]
    have hRp : DefRel (hi + hi) fun v => Rp (ftake v) (fdrop v) :=
      (hR₀.defRel.2 tail).congr fun _ => Iff.rfl
    have hHasP : DefRel (hi + 1) fun v => HasP (ftail v) (v 0) :=
      defRel_holdsQ_prepend tail
    let Xs_kf : Fin dsa.length → (Fin hi → V) → V := fun l ps =>
      interp V (Semantics.prepend ps tail) (dsa[dsa.length - 1 - l.val]'(by omega))
    have hXs_kf : ∀ l, DefFun hi (Xs_kf l) := fun l =>
      interp_defFun_prepend tail hi (dsa[dsa.length - 1 - l.val]'(by omega))
    have hIsY_def : ∀ m, m < D.N → DefFun hi fun p => IsY p m := fun m _ => by
      refine ((D.defFun_idx ψ tail dsa.length m).comp hXs_kf).congr fun p => ?_
      dsimp only [IsY]
      rw [keyFrame_prepend_eq_caf]
    have hΘ : ∀ p, DefTupleOp D.N (Θ p) := fun p =>
      mixT_defTupleOp (InGrp D grp) (D.carrier ψ (keyFrame dsa hi (Semantics.prepend p tail)))
        (D.hΦ ψ (keyFrame dsa hi (Semantics.prepend p tail)))
    have hΘ_def : ∀ m, m < D.N → DefFun (D.N + hi) fun v => Θ (fdrop v) (padTuple (ftake v)) m :=
      fun m hm => by
        refine (D.hΦ_param ψ tail (G := InGrp D grp) hXs_kf hm).congr fun v => ?_
        dsimp only [Θ]
        rw [keyFrame_prepend_eq_caf]
    have hIs' : ∀ p p', Rp p p' → ∀ m, InGrp D grp m → IsY p m = IsY p' m :=
      fun p p' hr' m hm => hIs _ _ hr' m hm
    have hcl : ∀ p, Sp p → ∃ L, IsClosedTuple (D.w ψ) D.N (IsY p) (Θ p) L :=
      fun p hp => ⟨_, mixT_isClosed (G := InGrp D grp)
        (h.closed (hfit _ _ hp).1) (hDmono _ _ hp) (hDmaps _ _ hp)⟩
    have hmaps : ∀ p, Sp p → MapsTuple (D.w ψ) D.N (IsY p) (Θ p) :=
      fun p hp => mixT_mapsTuple (hDmaps _ _ hp) (lfpTuple_mem _ _ _ _ (D.hΦ _ _))
    have hsacc : ∀ p, Sp p → ∃ A', AccTuple (D.w ψ) D.N (IsY p) D.N (IsY p) (Θ p) A' :=
      fun p hp => (hDacc _ _ hp).elim fun A' hA' =>
        ⟨A', accTuple_mixT (G := InGrp D grp) hA' (lfpTuple_mem _ _ _ _ (D.hΦ _ _))⟩
    have hlen_of_holeQ : ∀ {qi n : Nat}, qi < grp.length →
        HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length) qi n →
        n = (D.ids (D.names.idxOf (grp.getD (grp.length - 1 - qi) default).1) ψ).length := by
      intro qi n hlt hQ_q
      have hQ' : HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog)
          (ctx.hiAt prog.length + (grpNews us ds hi grp).length) qi n := by
        rw [grpNews_length, hhi]; exact hQ_q
      rcases holeQ_frame_iff.mp hQ' with ⟨jj, hk, hjj, hqi, hn⟩ | ⟨hle, -⟩
      · have hjl : jj < grp.length := by
          have := (List.getElem?_eq_some_iff.mp hjj).1; rwa [grpNews_length] at this
        have har := grp_arity mp hD hnN hkN hfind hg ψ grp[jj] (List.getElem_mem hjl)
        have hkey : hk.nIdx = grp[jj].2.piBinders.1.length := by
          simp only [grpNews, List.getElem?_map, List.getElem?_eq_getElem hjl, Option.map_some,
            Option.some.injEq] at hjj
          rw [← hjj]
        rw [grpNews_length] at hqi
        rw [hn, hkey]
        obtain ⟨mm', hmm', -, hidx', -⟩ := grpMember mp hD hnN hkN hfind hlps hg (List.getElem_mem hjl)
        rw [show grp.length - 1 - qi = jj by omega, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hjl, Option.getD_some]
        rw [hidx'] at har ⊢
        rw [parsLen_dsa mp hD hdsa hlenP hmm', ← DenoteSpine.length_eq hdsa] at har
        omega
      · rw [grpNews_length] at hle; omega
    have hacc : AccJointG (D.w ψ) D.N IsY Sp Rp HasP (InGrp D grp) Θ A O_sp := by
      rintro p Y hp hY m hm hGm j hjI z hz
      have hs := (hfit _ _ hp).1
      have hmixS := mixT_mem (G := InGrp D grp)
        (C := D.carrier ψ (keyFrame dsa hi (Semantics.prepend p tail)))
        (lfpTuple_mem _ _ _ _ (D.hΦ _ _)) hY
      obtain ⟨j', fs, hf, rfl⟩ := (h.fibre _ _ hs _ hmixS m hm j hjI z).mp hz
      have hj' := hf.1
      obtain ⟨-, -, -, hsup⟩ := hTB m j' hGm hj'
      obtain ⟨B, g0, hB, ⟨U0, hg0⟩, hitems, htr⟩ := hsup _ _ Y hp hY j fs hf
      let Good : V → Prop := fun o => ∀ q : Fin grp.length,
        sfst o = vnat q.val →
        evalSpineY
          (D.holeVal ψ (keyFrame dsa hi (Semantics.prepend p tail)) Y
            (D.names.idxOf (grp.getD (grp.length - 1 - q.val) default).1))
          (ssnd (ssnd o))
          (D.ids (D.names.idxOf (grp.getD (grp.length - 1 - q.val) default).1) ψ).length ≠ pt
      have hGood_def : DefPred fun b => Good (app g0 b) := by
        refine DefRel.finForall fun q : Fin grp.length => DefRel.imp
          (DefRel.eq_apply (DefFun.sfst_apply (DefFun.app_apply (DefFun.const g0) (DefFun.proj 0)))
            (DefFun.const (vnat q.val)))
          (DefRel.ne_apply
            (DefFun.evalSpineY_apply
              (D.ids (D.names.idxOf (grp.getD (grp.length - 1 - q.val) default).1) ψ).length
              (DefFun.const _)
              (DefFun.ssnd_apply (DefFun.ssnd_apply (DefFun.app_apply (DefFun.const g0) (DefFun.proj 0)))))
            DefFun.pt)
      let B_good : V := sep B (fun b => Good (app g0 b)) (hasSep_of_defPred hGood_def)
      let g : V := graph (fun b => frameItemMap D ψ grp (app g0 b)) B_good
        (hasGraph_of_defFun1 ((defFun_frameItemMap D ψ grp).comp1
          (DefFun.app_apply (DefFun.const g0) (DefFun.proj 0))))
      refine ⟨B_good, g, ?_, ?_, ?_, ?_⟩
      · intro b hb
        have hb' := hB b (sep_subset b hb)
        rw [hTBeq m j' _ _ Y (D.carrier ψ (keyFrame dsa hi (Semantics.prepend p tail)))
          fun _ _ => rfl] at hb'
        exact subset_finUnion_caf (f := fun c' => finUnion_caf (fun j'' => TBt c' j''
          (frameVal D ψ grp dsa hi (Semantics.prepend p tail)
            (D.carrier ψ (keyFrame dsa hi (Semantics.prepend p tail))))) (D.nctors c')) hm b
          (subset_finUnion_caf (f := fun j'' => TBt m j''
            (frameVal D ψ grp dsa hi (Semantics.prepend p tail)
              (D.carrier ψ (keyFrame dsa hi (Semantics.prepend p tail))))) hj' b hb')
      · refine graph_mem_piSet fun b hb => ?_
        obtain ⟨hbB, hGd⟩ := mem_sep.mp hb
        obtain ⟨hQ, hH⟩ := hitems b hbB
        have hg_app : frameItemMap D ψ grp (app g0 b) = _ := rfl
        rw [hg_app]
        obtain ⟨qi, vs, y, heq, hnp, hy⟩ := hH
        have hQ_adm : Adm (HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)) (qi, vs, y) := by
          obtain ⟨q1, vs1, y1, hE1, hQ1⟩ := hQ
          rw [heq] at hE1
          obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj hE1
          exact hQ1
        have hH_occ : Holds (frameVal D ψ grp dsa hi (Semantics.prepend p tail) Y) (qi, vs, y) := by
          unfold Holds; exact hy
        rcases frame_item_fwd mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hΔ hCds hLds hhi
            (hR₀.dom _ _ hp).1 (hkf _ _ hp).1 hQ_adm hH_occ with
          ⟨hlt, hGc, hin', -⟩ | ⟨hge, hQo, hHo⟩ | ⟨hlt, hlen, hnf⟩
        · have hlen' := hlen_of_holeQ hlt hQ_adm
          rw [heq, frameItemMap_lt D ψ grp hlt hlen']
          refine mem_binUnion.mpr (Or.inr (mem_image.mpr ⟨_, ?_, rfl⟩))
          exact hin'
        · rw [heq, frameItemMap_ge D ψ grp hge]
          refine mem_binUnion.mpr (Or.inl (mem_image.mpr ⟨_, ?_, rfl⟩))
          have hA_down : AdmItem (HoleQ ctx prog hi) (occEncItem (qi - grp.length) vs y) :=
            ⟨qi - grp.length, vs, y, rfl, hQo⟩
          have hH_down : HoldsNonPt (Semantics.prepend p tail) (occEncItem (qi - grp.length) vs y) := by
            refine ⟨qi - grp.length, vs, y, rfl, ?_, hHo⟩
            have hnp' := hnp
            rw [show qi = (qi - grp.length) + grp.length by omega, frameVal_ge] at hnp'
            exact hnp'
          exact occEncItem_mem_occSpaceQ hqs hA_down hH_down
        · exfalso
          have hsf : sfst (app g0 b) = vnat qi := by rw [heq]; unfold occEncItem; rw [sfst_kpair]
          have hne_gd := hGd ⟨qi, hlt⟩ hsf
          rw [heq] at hne_gd
          unfold occEncItem at hne_gd
          rw [ssnd_kpair, ssnd_kpair] at hne_gd
          unfold frameOcc at hlen
          simp only at hlen
          rw [← hlen, evalSpineY_encSpineY] at hne_gd
          rcases grp_hole_full (D := D) (lps := lps) (us := us) (φ := φ)
              (keyFrame dsa hi (Semantics.prepend p tail)) Y (vs := vs) hlen with
            ⟨hfit', -⟩ | ⟨-, he | he⟩
          · exact hnf hfit'
          · unfold Holds at hH_occ; simp only at hH_occ
            rw [frameVal_lt _ _ hlt] at hH_occ
            rw [he] at hH_occ
            exact not_mem_empty _ hH_occ
          · exact hne_gd he
      · intro b hb
        have hg_app : app g b = frameItemMap D ψ grp (app g0 b) :=
          app_graph hb
        rw [hg_app]
        obtain ⟨hbB, hGd⟩ := mem_sep.mp hb
        obtain ⟨hQ, qi, vs, y, heq, hnp, hy⟩ := hitems b hbB
        have hQ_adm : Adm (HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)) (qi, vs, y) := by
          obtain ⟨q1, vs1, y1, hE1, hQ1⟩ := hQ
          rw [heq] at hE1
          obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj hE1
          exact hQ1
        have hH_occ : Holds (frameVal D ψ grp dsa hi (Semantics.prepend p tail) Y) (qi, vs, y) := by
          unfold Holds; exact hy
        rcases frame_item_fwd mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hΔ hCds hLds hhi
            (hR₀.dom _ _ hp).1 (hkf _ _ hp).1 hQ_adm hH_occ with
          ⟨hlt, hGc, hin', -⟩ | ⟨hge, hQo, hHo⟩ | ⟨hlt, hlen, hnf⟩
        · have hlen' := hlen_of_holeQ hlt hQ_adm
          rw [heq, frameItemMap_lt D ψ grp hlt hlen']
          obtain ⟨-, hi_in, hy_in⟩ := occEnc_mem_occSpace.mp hin'
          exact Or.inr ⟨(frameOcc D ψ grp (qi, vs, y)).1, Nat.lt_of_lt_of_le hGc.1 hkNN, hGc,
            (tupW (D.u (frameOcc D ψ grp (qi, vs, y)).1 ψ) vs), y, hi_in, hy_in, rfl⟩
        · rw [heq, frameItemMap_ge D ψ grp hge]
          refine Or.inl ⟨occEncItem (qi - grp.length) vs y, rfl, ?_⟩
          exact holdsQ_iff.mpr ⟨⟨qi - grp.length, vs, y, rfl, (hqs _ _).mp hQo⟩,
            ⟨qi - grp.length, vs, y, rfl, hHo⟩⟩
        · exfalso
          have hsf : sfst (app g0 b) = vnat qi := by rw [heq]; unfold occEncItem; rw [sfst_kpair]
          have hne_gd := hGd ⟨qi, hlt⟩ hsf
          rw [heq] at hne_gd
          unfold occEncItem at hne_gd
          rw [ssnd_kpair, ssnd_kpair] at hne_gd
          unfold frameOcc at hlen
          simp only at hlen
          rw [← hlen, evalSpineY_encSpineY] at hne_gd
          rcases grp_hole_full (D := D) (lps := lps) (us := us) (φ := φ)
              (keyFrame dsa hi (Semantics.prepend p tail)) Y (vs := vs) hlen with
            ⟨hfit', -⟩ | ⟨-, he | he⟩
          · exact hnf hfit'
          · unfold Holds at hH_occ; simp only at hH_occ
            rw [frameVal_lt _ _ hlt] at hH_occ
            rw [he] at hH_occ
            exact not_mem_empty _ hH_occ
          · exact hne_gd he
      · rintro p' Y' hR' hp' hY' hitems'
        have hs' := (hfit _ _ hR').2
        have hf' := htr _ Y' hR' hY' fun b hb => by
          obtain ⟨hQ, qi, vs, y, heq, -, hy⟩ := hitems b hb
          have hQ_adm : Adm (HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)) (qi, vs, y) := by
            obtain ⟨q1, vs1, y1, hE1, hQ1⟩ := hQ
            rw [heq] at hE1
            obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj hE1
            exact hQ1
          have hH_occ : Holds (frameVal D ψ grp dsa hi (Semantics.prepend p tail) Y) (qi, vs, y) := by
            unfold Holds; exact hy
          by_cases hGd : Good (app g0 b)
          · have hb' : b ∈ˢ B_good := mem_sep.mpr ⟨hb, hGd⟩
            have hg_app : app g b = frameItemMap D ψ grp (app g0 b) :=
              app_graph hb'
            have hib := hitems' b hb'
            rw [hg_app] at hib
            rcases frame_item_fwd mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hΔ hCds hLds hhi
                (hR₀.dom _ _ hp).1 (hkf _ _ hp).1 hQ_adm hH_occ with
              ⟨hlt, -, -, hfit0⟩ | ⟨hge, -, -⟩ | ⟨hlt, hlen, hnf⟩
            · have hlen' := hlen_of_holeQ hlt hQ_adm
              rw [heq, frameItemMap_lt D ψ grp hlt hlen'] at hib
              rcases hib with ⟨o', ho', -⟩ | ⟨mm', hm', -, i', y', -, hy', ho'⟩
              · exfalso
                obtain ⟨hpt, -⟩ := kpair_inj ho'
                exact pt_ne_empty hpt
              · obtain ⟨-, hocc⟩ := kpair_inj ho'
                obtain ⟨rmm, rtup, ry⟩ := occEnc_inj hocc
                subst rmm ry
                have hfit1 := hfit0 _ (hagree _ _ hR') (hR₀.dom _ _ hR').2 (hkf _ _ hR').2
                have hbw := frame_item_bwd hlt hfit1 (occEnc_mem_occSpace.mpr ⟨hm',
                  by dsimp only [frameOcc]; exact tupW_mem hfit1,
                  by dsimp only [frameOcc]; rw [rtup]; exact hy'⟩)
                exact ⟨qi, vs, y, heq, hbw⟩
            · rw [heq, frameItemMap_ge D ψ grp hge] at hib
              rcases hib with ⟨o', ho', hHas'⟩ | ⟨_, _, _, _, _, _, _, ho'⟩
              · obtain ⟨-, rfl⟩ := kpair_inj ho'
                obtain ⟨qi', vs', y', heq', hy'⟩ := (holdsQ_iff.mp hHas').2
                obtain ⟨rqi, rvs, ry⟩ := occEncItem_inj heq'
                have rqi' : qi' = qi - grp.length := rqi.symm
                rw [rqi', ← rvs, ← ry] at hy'
                exact ⟨qi, vs, y, heq, (holds_frameVal_ge hge).mpr hy'⟩
              · exfalso
                obtain ⟨hpt, -⟩ := kpair_inj ho'
                exact pt_ne_empty hpt.symm
            · exfalso
              have hsf : sfst (app g0 b) = vnat qi := by rw [heq]; unfold occEncItem; rw [sfst_kpair]
              have hne_gd := hGd ⟨qi, hlt⟩ hsf
              rw [heq] at hne_gd
              unfold occEncItem at hne_gd
              rw [ssnd_kpair, ssnd_kpair] at hne_gd
              unfold frameOcc at hlen
              simp only at hlen
              rw [← hlen, evalSpineY_encSpineY] at hne_gd
              rcases grp_hole_full (D := D) (lps := lps) (us := us) (φ := φ)
                  (keyFrame dsa hi (Semantics.prepend p tail)) Y (vs := vs) hlen with
                ⟨hfit', -⟩ | ⟨-, he | he⟩
              · exact hnf hfit'
              · unfold Holds at hH_occ; simp only at hH_occ
                rw [frameVal_lt _ _ hlt] at hH_occ
                rw [he] at hH_occ
                exact not_mem_empty _ hH_occ
              · exact hne_gd he
          · have hnot : ∃ q : Fin grp.length, sfst (app g0 b) = vnat q.val ∧
                evalSpineY (D.holeVal ψ (keyFrame dsa hi (Semantics.prepend p tail)) Y
                  (D.names.idxOf (grp.getD (grp.length - 1 - q.val) default).1))
                  (ssnd (ssnd (app g0 b)))
                  (D.ids (D.names.idxOf (grp.getD (grp.length - 1 - q.val) default).1) ψ).length = pt :=
              Classical.byContradiction fun hn' =>
                hGd fun q hsf heq_pt => hn' ⟨q, hsf, heq_pt⟩
            obtain ⟨q, hsf, heq_pt⟩ := hnot
            rw [heq] at hsf
            unfold occEncItem at hsf
            rw [sfst_kpair] at hsf
            have hqi : qi = q.val := vnat_inj hsf
            have hlt : qi < grp.length := hqi ▸ q.isLt
            rcases frame_item_fwd mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hΔ hCds hLds hhi
                (hR₀.dom _ _ hp).1 (hkf _ _ hp).1 hQ_adm hH_occ with
              ⟨hlt', hGc, hin', hfit0⟩ | ⟨hge, -, -⟩ | ⟨hlt', hlen, hnf⟩
            · exfalso
              rw [heq] at heq_pt
              unfold occEncItem at heq_pt
              rw [ssnd_kpair, ssnd_kpair] at heq_pt
              have hlen_eq : vs.length = (D.ids (D.names.idxOf (grp.getD (grp.length - 1 - q.val) default).1) ψ).length := by
                rw [← hqi]; exact hlen_of_holeQ hlt hQ_adm
              rw [← hlen_eq, evalSpineY_encSpineY, ← hqi] at heq_pt
              have hsp_fit := hfit0 _ (fun _ _ => rfl) (hR₀.dom _ _ hp).1 (hkf _ _ hp).1
              unfold frameOcc at hsp_fit
              simp only at hsp_fit
              obtain ⟨-, hi_in, -⟩ := occEnc_mem_occSpace.mp hin'
              unfold frameOcc at hi_in
              simp only at hi_in
              have hlt_sub : grp.length - 1 - qi < grp.length := by omega
              have hmm_in := grpMember mp hD hnN hkN hfind hlps hg (List.getElem_mem hlt_sub)
              obtain ⟨mm', hmm', -, hidx', -⟩ := hmm_in
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_sub, Option.getD_some] at hsp_fit hi_in heq_pt
              rw [hidx'] at hsp_fit heq_pt
              have hne_pt := (IsTy_of_mem_strictU (famSpace_app (hY _ (Nat.lt_of_lt_of_le hmm' hkNN))
                (by rw [← hidx']; exact hi_in))).ne_pt
              rw [hidx'] at hne_pt
              exact hne_pt (by
                rw [← LfpDatum.holeVal_app (X := Y) hsp_fit]
                exact heq_pt)
            · exact absurd hlt (by omega)
            · have h_nf := frame_item_nofit mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hΔ hCds hLds
                hlt' (hagree _ _ hR') (hR₀.dom _ _ hR').1 (hR₀.dom _ _ hR').2
                (hkf _ _ hR').1 (hkf _ _ hR').2 hY hY' hlen hnf hH_occ
              exact ⟨qi, vs, y, heq, h_nf⟩
        have hmixS' := mixT_mem (G := InGrp D grp)
          (C := D.carrier ψ (keyFrame dsa hi (Semantics.prepend p' tail)))
          (lfpTuple_mem _ _ _ _ (D.hΦ _ _)) hY'
        exact (h.fibre _ _ hs' _ hmixS' m hm j (by change j ∈ˢ IsY p' m; rw [← hIs' p p' hR' m hGm]; exact hjI)
          (D.inj (Level.substFn φ lps us) m j' fs)).mpr ⟨j', fs, hf', rfl⟩
    have hmain := lfpP_acc_group hSp hRp hHasP hIsY_def hΘ hΘ_def hIs' hcl hmaps hsacc hacc
    -- the carrier on the group is the mixed operator's least tuple
    have hcarr : ∀ ρ₁ ρ₂, R₀ ρ₁ ρ₂ → ∀ c', InGrp D grp c' →
        lfpTuple (D.w ψ) D.N (D.idx ψ (keyFrame dsa hi ρ₁))
            (fun Y => D.Φ ψ (keyFrame dsa hi ρ₁)
              (mixT (InGrp D grp) (D.carrier ψ (keyFrame dsa hi ρ₁)) Y))
            (mixT_defTupleOp (InGrp D grp) (D.carrier ψ (keyFrame dsa hi ρ₁))
              (D.hΦ ψ (keyFrame dsa hi ρ₁))) c'
          = D.carrier ψ (keyFrame dsa hi ρ₁) c' := by
      intro ρ₁ ρ₂ hr' c' hc'
      exact lfpTuple_mixT (hΦ := D.hΦ ψ (keyFrame dsa hi ρ₁))
        (h.closed (hfit ρ₁ ρ₂ hr').1) (hDmono ρ₁ ρ₂ hr') (hDmaps ρ₁ ρ₂ hr') c'
        (Nat.lt_of_lt_of_le hc'.1 hkNN) hc'
    let p : Fin hi → V := fun q => ρ q.val
    have hp_eq : Semantics.prepend p tail = ρ := by
      funext k
      by_cases hk : k < hi
      · simp [Semantics.prepend, hk, p]
      · simp only [Semantics.prepend, hk, ↓reduceDIte, tail]
        rw [show k - hi + hi = k by omega]
        exact (hagree ρ ρ₀ hr k (fun hpar => by exact absurd hpar.1 hk)).symm
    have hp_sp : Sp p := by dsimp [Sp]; rw [hp_eq]; exact hR₀.lrefl ρ ρ₀ hr
    rw [← hp_eq] at hiI hx
    rw [← hcarr (Semantics.prepend p tail) (Semantics.prepend p tail) (by dsimp [Sp] at hp_sp; exact hp_sp) c hc] at hx
    obtain ⟨B, g, hB, hg', hitems, htr⟩ := hmain p hp_sp c (Nat.lt_of_lt_of_le hc.1 hkNN) hc i hiI x hx
    dsimp only [A] at hB
    rw [hp_eq] at hB
    let B' : V := sep B (fun b => app g b ∈ˢ occSpaceQ ρ qs)
      (hasSep_of_defPred (DefRel.mem_apply (DefFun.app_apply (DefFun.const g) (DefFun.proj 0))
        (DefFun.const (occSpaceQ ρ qs))))
    let g' : V := graph (fun b => app g b) B'
      (hasGraph_of_defFun1 (DefFun.app_apply (DefFun.const g) (DefFun.proj 0)))
    refine ⟨B', g', fun b hb => hB b (sep_subset b hb),
      ⟨O_sp p, graph_mem_piSet fun b hb => app_mem_of_mem_piSet hg' (sep_subset b hb)⟩,
      fun b hb => ?_, fun ρ' hr' hheld => ?_⟩
    · have hb' := mem_sep.mp hb
      have h_app : app g' b = app g b := app_graph hb
      rw [h_app]
      obtain ⟨hA_item, -⟩ := holdsQ_iff.mp (hitems b hb'.1)
      refine ⟨(admItem_congrQ hqs).mpr hA_item, ?_⟩
      obtain ⟨⟨qj, qn⟩, -, ho_mem⟩ := mem_occSpaceQ_iff.mp hb'.2
      obtain ⟨vs, y, -, heq, hnp, hy⟩ := mem_graphOccs_iff.mp ho_mem
      exact ⟨qj, vs, y, heq, hnp, hy⟩
    · have hpt_eq : Semantics.prepend (fun q : Fin hi => ρ' q.val) tail = ρ' := by
        funext k
        by_cases hk : k < hi
        · simp [Semantics.prepend, hk]
        · simp only [Semantics.prepend, hk, ↓reduceDIte, tail]
          rw [show k - hi + hi = k by omega]
          have h1 := hagree ρ ρ₀ hr k (fun hpar => absurd hpar.1 hk)
          have h2 := hagree ρ ρ' hr' k (fun hpar => absurd hpar.1 hk)
          exact h1.symm.trans h2
      let p' : Fin hi → V := fun q => ρ' q.val
      have hp'_rp : Rp p p' := by dsimp [Rp]; rw [hp_eq, hpt_eq]; exact hr'
      have hp'_sp : Sp p' := by
        dsimp [Sp]; rw [hpt_eq]; exact hR₀.lrefl ρ' ρ (hR₀.symm ρ ρ' hr')
      have hsub : ∀ b, b ∈ˢ B → HasP p' (app g b) := by
        intro b hb
        have h_src := hitems b hb
        dsimp only [HasP] at h_src
        rw [hp_eq] at h_src
        obtain ⟨hA_src, qi, vs, y, heq, hy⟩ := holdsQ_iff.mp h_src
        have hQ_src : HoleQ ctx prog hi qi vs.length := by
          obtain ⟨qi', vs', y', heq', hqin⟩ := hA_src
          rw [heq] at heq'
          obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj heq'
          exact (hqs _ _).mpr hqin
        by_cases hb_occ : app g b ∈ˢ occSpaceQ ρ qs
        · have hb' : b ∈ˢ B' := mem_sep.mpr ⟨hb, hb_occ⟩
          have h_tgt := hheld b hb'
          rw [app_graph hb'] at h_tgt
          dsimp [HasP]; rw [hpt_eq]
          exact holdsQ_iff.mpr ⟨hA_src, h_tgt⟩
        · have hnp : ¬ NoPtPrefix (ρ qi) vs := by
            intro hnp'
            exact hb_occ (heq ▸ occEncItem_mem_occSpaceQ hqs ⟨qi, vs, y, rfl, hQ_src⟩
              ⟨qi, vs, y, rfl, hnp', hy⟩)
          have hpt_sub := hR₀.ptHit ρ ρ' hr' qi vs (hhi ▸ hQ_src) hnp
          have hy_pt : y ∈ˢ (pt : V) := by
            rwa [← foldlApp_eq_pt_of_not_noPtPrefix hnp]
          dsimp [HasP]; rw [hpt_eq]
          exact holdsQ_iff.mpr ⟨hA_src, qi, vs, y, heq, hpt_sub y hy_pt⟩
      have hx' := htr p' hp'_rp hp'_sp hsub
      have h_lfp_congr : ∀ {Is₁ Is₂ : Nat → V} {Φ₁ Φ₂ : (Nat → V) → Nat → V}
          {h₁ : DefTupleOp D.N Φ₁} {h₂ : DefTupleOp D.N Φ₂},
          Is₁ = Is₂ → Φ₁ = Φ₂ → lfpTuple (D.w ψ) D.N Is₁ Φ₁ h₁ = lfpTuple (D.w ψ) D.N Is₂ Φ₂ h₂ := by
        rintro _ _ _ _ _ _ rfl rfl; rfl
      have h_lfp_eq := h_lfp_congr
        (Is₁ := IsY p') (Is₂ := D.idx ψ (keyFrame dsa hi ρ'))
        (h₁ := hΘ p')
        (h₂ := mixT_defTupleOp (InGrp D grp) (D.carrier ψ (keyFrame dsa hi ρ'))
          (D.hΦ ψ (keyFrame dsa hi ρ')))
        (by dsimp only [IsY]; rw [hpt_eq])
        (by dsimp only [Θ]; rw [hpt_eq])
      rw [h_lfp_eq] at hx'
      rw [← hcarr ρ' ρ (hR₀.symm ρ ρ' hr') c hc]
      exact hx'

set_option maxHeartbeats 1600000 in
/-- **A frame's constructors make it accessible** (the accessibility
twin of `frameIter`): the constructors of the reached group, instantiated
at the key and walked along the frame relation (`hwalk`, the frame
derivation's), make the group's carriers accessible in the enclosing
frame (`FrameAccOut`) at the pairs whose key frames fit the block (`fitRel`), where the block lives
at the walk context's level (`grp_sort`). -/
theorem frameIterAcc (hin : RulesInputs V mp.base2 φ) {w : Nat}
    (hwS : ctx.sort.eval φ = w) {F : Nat}
    (hcov : ∀ c, c < D.k → ∃ nP' L, ConLeche.nestContainer ctx (D.member c) = some (nP', L) ∧
      L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
        ∃ iT, env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2 iT))
    {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi) {Δh : List Term}
    {R₀ : FrameRel V} (hR₀ : HoleRelA mp.base2 φ w ctx prog hi Δh R₀) (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    {ctors : List (ConstantVal × Nat)}
    (hgc : ConLeche.groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    (hwalk : ∀ {Δ : List Term} {R : FrameRel V},
      HoleRelA mp.base2 φ w ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length) Δ R →
      ∀ (Q : ConstantVal × Nat → Prop),
      (∀ (x : ConstantVal × Nat) (crest : Expr), Q x →
        ConLeche.nestCrest (grp.map (·.1)) us ds (grpHoles hi grp)
          (x.1.type.instantiateLevelParams x.1.levelParams us) = some crest →
        (∃ ty u, ConLeche.inferTypeCore .verified false env F (hi + grp.length) crest = .ok ty ∧
          ConLeche.ensureSortCore .verified false env F (hi + grp.length) ty = .ok u) →
        ∃ ca, Frame (hi + grp.length) crest ∧ CtxOkP mp.base2 φ (hi + grp.length) Δ crest ∧
          denote mp.base2.acval env φ (hi + grp.length) crest = some ca ∧ GradedTy V Δ ca) →
      (∀ x ∈ ctors, Q x) →
      ∀ x ∈ ctors, CtorWalkedA mp.base2 φ w ctx ((grpNews us ds hi grp).reverse ++ prog)
        (hi + grp.length) us ds (grp.map (·.1)) (grpHoles hi grp) Δ R x) :
    FrameAccOut w ctx prog hi (fitRel R₀ D (Level.substFn φ lps us) dsa hi) D
      (Level.substFn φ lps us) dsa (InGrp D grp) := by
  have hQ := grpCtors_found hg hcov hgc
  have hR₁ := hR₀.restrict (KeyFit D (Level.substFn φ lps us) dsa hi) fun tail => by
    let ψ := Level.substFn φ lps us
    let Xs_kf : Fin dsa.length → (Fin hi → V) → V := fun l ps =>
      interp V (Semantics.prepend ps tail) (dsa[dsa.length - 1 - l.val]'(by omega))
    have hXs_kf : ∀ l, DefFun hi (Xs_kf l) := fun l =>
      interp_defFun_prepend tail hi (dsa[dsa.length - 1 - l.val]'(by omega))
    have h1 := defRel_sat_prepend tail Xs_kf hXs_kf (D.params ψ).reverse
    have h2 : DefRel hi fun v => ∃ mm, mm < D.k ∧ ∃ is,
        SpineFit (Semantics.prepend (fun l => Xs_kf l v) tail) (D.ids mm ψ) is :=
      DefRel.finExists_lt fun mm _ => defRel_exists_spineFit_prepend tail (D.ids mm ψ) Xs_kf hXs_kf
    refine (DefRel.and h1 h2).congr fun v => ?_
    change (_ ∧ _) ↔ D.FrFit ψ (keyFrame dsa hi (Semantics.prepend v tail))
    unfold LfpDatum.FrFit
    rw [keyFrame_prepend_eq_caf]
  have hkf : ∀ ρ ρ', fitRel R₀ D (Level.substFn φ lps us) dsa hi ρ ρ' →
      KeyFit D (Level.substFn φ lps us) dsa hi ρ ∧ KeyFit D (Level.substFn φ lps us) dsa hi ρ' :=
    fun _ _ hr => hr.2
  have hwD : ∀ ρ ρ', fitRel R₀ D (Level.substFn φ lps us) dsa hi ρ ρ' →
      D.w (Level.substFn φ lps us) = w := fun ρ ρ' hr =>
    (grp_sort mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hΔ hCds hLds
      (hR₀.dom ρ ρ' hr.1).1 hr.2.1).trans hwS
  have hR' := frameRelA_holeRelA mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hhi hR₁ hin
    hΔ hCds hLds hkf hwD (grp_arity mp hD hnN hkN hfind hg _)
  have hwalked := hwalk hR'
    (fun x => ∃ c j, InGrp D grp c ∧ j < D.nctors c ∧
      ∃ iT, env.find? (D.ctorName c j) = some (.ctorInfo x.1 ds.length x.2 iT))
    (fun x crest hQx hcr hinf => by
      obtain ⟨c, j, hGc, hj, _, hfc⟩ := hQx
      have hwf := mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfc)
      have hcl : (x.1.type.instantiateLevelParams x.1.levelParams us).hasFvar = false := by
        rw [Expr.hasFvar_instantiateLevelParams]; exact hwf.1
      have hbb : (x.1.type.instantiateLevelParams x.1.levelParams us).looseBVarsBounded 0 = true := by
        rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
      obtain ⟨hfr, hC⟩ := crest_frame mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hin hΔ
        hCds hLds hcl hbb hcr
      obtain ⟨-, crest', ab, hcr', hEqF, hlen, hrd⟩ :=
        crest_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hGc.1 hj hfc
      rw [hcr] at hcr'
      obtain rfl := Option.some.inj hcr'
      obtain ⟨ty, u, hty, hsort⟩ := hinf
      exact ⟨_, hfr, hC, hrd, gradedTy_of_sort hin hty hsort hfr hC.toCtxOk hrd⟩)
    hQ
  refine frameAccOut_of mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hhi hR₁ hΔ hCds hLds
    hkf fun g j hG hj => ?_
  obtain ⟨x, hxmem, _, hfc⟩ := grpCtor_found hcov hgc hG hj
  exact frameCtor_acc mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hin hhi hR₁ hΔ hCds hLds
    hkf hwD hG hj hfc (hwalked _ hxmem)

end Frame

end ConLeche.Model
