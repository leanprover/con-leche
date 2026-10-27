module

public import ConLeche.Model.Inductives.ContAccRel
public import ConLeche.Model.Inductives.BlockAccRun
import ConLeche.Model.Inductives.StoredShapes
import ConLeche.Model.Inductives.PosDerivShape
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Denote.Shift
import ConLeche.Verify.Cached.NestPosC
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Inductives.ContCtor
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Inductives.TypeStep
import ConLeche.Verify.Denote.IndFrame

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
  obtain ⟨Af, htele, hinv, hQf⟩ := teleAccP_of_piAccThen abD abN B b 0 nds Δ R
    (HoleQ ctx prog b) (by rw [habN]; exact hE) hdom
    (fun ρ ρ₀ h hw => by rw [habN]; exact FieldsBound.of_eqOn hE (hdom ρ ρ₀ h).1 (hbd ρ ρ₀ h hw))
    (fun _ _ => Iff.rfl) (by omega) hP
  rw [habN] at htele hQf
  rw [hlen] at hQf
  have hNn : N.length = nF := hNl.trans hnl'
  -- the closed normal form is scoped at the base
  have hW : Expr.WScoped b (ConLeche.closeTelescope nds b res) := by
    refine ConLeche.Cached.closeTelescope_wscoped nds b res (fun k nd hk => ?_) ?_
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
  refine ⟨fun l => if l < nF then Af l else fun _ => empty, N, hE, ?_, ?_, ?_, hQf⟩
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
bound of the level reading only the parameter positions of the frame's
depth `b`, and supports of the frame's walk valuation carrying a fit at a
tuple mixed into the carrier to any related frame and tuple. -/
@[expose] def FrameCtorAcc (w b nP : Nat) (Q' : Nat → Nat → Prop) (R₀ : FrameRel V)
    (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr)) (dsa : List Term) (hi : Nat)
    (g j : Nat) : Prop :=
  ∃ TB : (Nat → V) → V, (∀ σ, w ≠ 0 → TB σ ∈ˢ (tg w : V)) ∧
    (∀ σ σ', (∀ q, ParamPos b nP q → σ q = σ' q) → TB σ = TB σ') ∧
    ∀ ρ ρ₀ Y, R₀ ρ ρ₀ → InTupleSpace (D.w ψ) D.N (D.idx ψ (keyFrame dsa hi ρ)) Y →
      ∀ t fs, D.HFits ψ (keyFrame dsa hi ρ) (mixT (InGrp D grp) (D.carrier ψ (keyFrame dsa hi ρ)) Y)
          t g j fs →
        ∃ (B : V) (gi : V → Occ V), B ⊆ˢ TB (frameVal D ψ grp dsa hi ρ Y) ∧
          (∀ b, b ∈ˢ B → Adm Q' (gi b) ∧ Holds (frameVal D ψ grp dsa hi ρ Y) (gi b)) ∧
          ∀ ρ' Y', R₀ ρ ρ' → InTupleSpace (D.w ψ) D.N (D.idx ψ (keyFrame dsa hi ρ')) Y' →
            (∀ b, b ∈ˢ B → Holds (frameVal D ψ grp dsa hi ρ' Y') (gi b)) →
            D.HFits ψ (keyFrame dsa hi ρ') (mixT (InGrp D grp) (D.carrier ψ (keyFrame dsa hi ρ')) Y')
              t g j fs

/-- **A frame's accessibility**: a bound of the
level reading only the parameter positions at the key's depth, and every
group member's carrier at the key frame accessible along the enclosing
relation with admissible enclosing items. -/
@[expose] def FrameAccOut (w : Nat) (ctx : NestCtx) (prog : List NestHole) (hi : Nat)
    (R₀ : FrameRel V) (D : LfpDatum V) (ψ : Name → Nat) (dsa : List Term) (G : Nat → Prop) :
    Prop :=
  ∃ A : (Nat → V) → V, (∀ ρ, w ≠ 0 → A ρ ∈ˢ (tg w : V)) ∧ InvOn (ParamPos hi ctx.nP) A ∧
    ∀ c, G c → ∀ ρ ρ₀, R₀ ρ ρ₀ → ∀ i, i ∈ˢ D.idx ψ (keyFrame dsa hi ρ) c →
      ∀ x, x ∈ˢ app (D.carrier ψ (keyFrame dsa hi ρ) c) i →
        ∃ (B : V) (g : V → Occ V), B ⊆ˢ A ρ ∧
          (∀ b, b ∈ˢ B → Adm (HoleQ ctx prog hi) (g b) ∧ Holds ρ (g b)) ∧
          ∀ ρ', R₀ ρ ρ' → (∀ b, b ∈ˢ B → Holds ρ' (g b)) →
            x ∈ˢ app (D.carrier ψ (keyFrame dsa hi ρ') c) i

/-! ## One frame constructor -/

section Frame

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
  (hfind : ∀ n, ctx.find? n = env.find? n) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List Term}
  (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa)
  (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)
  {grp : List (Name × Expr)} (hg : GrpWf ctx D hi us ds grp)

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
theorem frameCtor_acc {w : Nat} (hwD : D.w (Level.substFn φ lps us) = w)
    {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi)
    {Δh : List Term} {R₀ : FrameRel V} (hR₀ : HoleRelA mp.base2 φ w ctx prog hi Δh R₀)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ'))
    {g j : Nat} (hG : InGrp D grp g) (hj : j < D.nctors g) {cv : ConstantVal} {nF : Nat}
    (hfc : env.find? (D.ctorName g j) = some (.ctorInfo cv ds.length nF))
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
  obtain ⟨-, crest', ab, hcr', ⟨Tys, hlT, hTys, hEqF⟩, hlen, hrd⟩ :=
    crest_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hG.1 hj hfc
  rw [hcr] at hcr'
  obtain rfl := Option.some.inj hcr'
  rw [hca] at hrd
  obtain rfl := Option.some.inj hrd
  have hRA := frameRelA_holeRelA mp hD hnN hkN hfind hlps hnd hul hds hdsa
    hlenP hg hhi hR₀ hwD (grp_arity mp hD hnN hkN hfind hg _)
  -- the substituted valuation IS the hole frame at a frame and a tuple
  have hvals : ∀ ρ Y, Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) →
      InTupleSpace (D.w (Level.substFn φ lps us)) D.N
        (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y →
      substE V (substTau (ds.length + D.k) (hi + grp.length)
          (grpX mp.base2 φ D hi grp ds (hi + grp.length))) 0
          (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y)
        = D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y ∧
      Sat V (D.params (Level.substFn φ lps us) ++ Tys).reverse
        (D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y) := fun ρ Y hs hY =>
    ⟨substE_grp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg Y ρ,
      frameVals_sat mp hD hs hlenP hlT hTys Y hY⟩
  -- the walked fields are small at every related frame
  have hbd : ∀ σ σ₀, frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi σ σ₀ → w ≠ 0 →
      FieldsBound w σ ((Term.substTele (substTau (ds.length + D.k) (hi + grp.length)
        (grpX mp.base2 φ D hi grp ds (hi + grp.length))) 0 ab)) := by
    rintro _ _ ⟨ρ, ρ', Y, Y', hR, hY, -, rfl, -⟩ hw
    have hw' : D.w (Level.substFn φ lps us) ≠ 0 := by rw [hwD]; exact hw
    obtain ⟨hS, hsat⟩ := hvals ρ Y (hfit ρ ρ' hR).1 hY
    have hok := h.fieldsOk (Level.substFn φ lps us) (keyFrame dsa hi ρ) (hfit ρ ρ' hR).1 hw'
      Y hY g (Nat.lt_of_lt_of_le hG.1 hkNN) j hj
    have hb := hok.toBound hw'
    rw [hwD] at hb
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
  obtain ⟨Af, N, hEN, htele, hAf, hF, hRes⟩ := walkTele_acc (m := mp.base2) (φ := φ) hb
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
  refine ⟨teleBound w ord Af 0 N, fun σ hw => teleBound_mem hw _ _ _ _ _, fun σ σ' hq => ?_, ?_⟩
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
  obtain ⟨B, gi, hB, hgi, hs⟩ := teleBound_support (k := 0) (ord := ord)
    (fun l τ τ' hτ => hAf l τ τ' (hτ.toM _)) N 0 _ _
    (fun i G hG' ho τ τ' hτ => hF i G (by simpa using hG') (by rw [Nat.zero_add] at ho; exact ho)
      τ τ' (by rw [Nat.zero_add] at hτ; exact hτ.toM _))
    htele _ hRσ fs hspN
  refine ⟨B, gi, hB, hgi, fun ρ' Y' hR' hY' hheld => ?_⟩
  rw [hfits_mixT_grp hkN hg]
  have hRσL : frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y)
      (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') := ⟨ρ, ρ', Y, Y', hR', hY, hY', rfl, rfl⟩
  have hL := hs _ hRσL hheld
  obtain ⟨hSL, hsatL⟩ := hvals ρ' Y' (hfit ρ ρ' hR').2 hY'
  exact hfits_of_spineFitN hEqF hlen hp hEN hRes hres hidx hRσL hS hSL hsat hsatL
    (hRA.dom _ _ hRσL).1 (hRA.dom _ _ hRσL).2 hf hL

/-- **A frame item is a group occurrence or an enclosing item.** -/
theorem frame_item_fwd {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi) {ρ Y : Nat → V}
    {o : Occ V} (hQ : Adm (HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)) o)
    (hH : Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) o) :
    (o.1 < grp.length ∧ InGrp D grp (frameOcc D (Level.substFn φ lps us) grp o).1 ∧
      InTup D.N (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y
        (frameOcc D (Level.substFn φ lps us) grp o) ∧
      ∀ ρ', AgreeOff (holeP hi ctx.nP hi) ρ ρ' →
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
    have hkey : hk.key.cname = grp[j].1 ∧ hk.key.ds = ds := by
      simp only [grpNews, List.getElem?_map, List.getElem?_eq_getElem hjl, Option.map_some,
        Option.some.injEq] at hj
      rw [← hj]
      exact ⟨rfl, rfl⟩
    have hmem : grp[j] ∈ grp := List.getElem_mem hjl
    obtain ⟨mm, hmm, -, hidx, -, -, -, -, -, -, hte⟩ :=
      grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hmem
    have har := grp_arity mp hD hnN hkN hfind hg (Level.substFn φ lps us) _ hmem
    rw [hkey.1, hkey.2] at hn
    rw [hidx, parsLen_dsa mp hD hdsa hlenP hmm, ← DenoteSpine.length_eq hdsa] at har
    unfold Holds at hH
    simp only at hH
    rw [frameVal_lt ρ Y (by omega), hjk, hidx] at hH
    unfold frameOcc
    simp only
    rw [hjk, hidx]
    rcases grp_hole_full (D := D) (lps := lps) (us := us) (φ := φ) (mm := mm) (keyFrame dsa hi ρ) Y
        (vs := vs) (by rw [har] at hn; omega) with ⟨hfit, he⟩ | ⟨hnf, he⟩
    · refine Or.inl ⟨by omega, ?_, ?_⟩
      · have := grp_inGrp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hmem
        rwa [hidx] at this
      rw [he] at hH
      exact ⟨⟨Nat.lt_of_lt_of_le hmm (mp.lfp_ok D hD).1.kN, tupW_mem hfit, hH⟩,
        fun ρ' hag => ((hte ρ ρ' hag).spineFit vs).mp hfit⟩
    · exact Or.inr (Or.inr ⟨by omega, by rw [har] at hn; omega, hnf⟩)
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
      (frameOcc D (Level.substFn φ lps us) grp o)) :
    Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') o := by
  obtain ⟨i, vs, y⟩ := o
  have h2 := LfpDatum.holeVal_app (X := Y') hfit
  unfold frameOcc at h2 hin
  unfold Holds
  simp only at hlt h2 hin ⊢
  rw [frameVal_lt ρ' Y' hlt, h2]
  exact hin.2.2

/-- **A new-hole item off its fit is held alike at every related frame**:
the hole's value there reads neither the enclosing frame off the holes
(N2's `TeleEq`) nor the tuple (`holeFam_foldl_nofit`; the tuples'
fibres are strict sets or truth values, never the point). -/
theorem frame_item_nofit {ρ ρ' Y Y' : Nat → V} {o : Occ V} (hlt : o.1 < grp.length)
    (hag : AgreeOff (holeP hi ctx.nP hi) ρ ρ')
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
  obtain ⟨mm, hmm, -, hidx, -, -, -, -, -, -, hte⟩ :=
    grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hmemG
  unfold frameOcc at hn hlen
  simp only [hidx] at hn hlen
  unfold Holds at hH ⊢
  simp only at hH ⊢
  rw [frameVal_lt ρ Y hlt, hidx] at hH
  rw [frameVal_lt ρ' Y' hlt, hidx]
  have hmmN : mm < D.N := Nat.lt_of_lt_of_le hmm (mp.lfp_ok D hD).1.kN
  have hT := hte ρ ρ' hag
  have hne : ∀ ws, SpineFit (keyFrame dsa hi ρ) (D.ids mm (Level.substFn φ lps us)) ws →
      app (Y mm) (tupW (D.u mm (Level.substFn φ lps us)) ws) ≠ pt := fun ws hws =>
    (IsTy_of_mem_strictU (famSpace_app (hY mm hmmN) (tupW_mem hws))).ne_pt
  have hne' : ∀ ws, SpineFit (keyFrame dsa hi ρ) (D.ids mm (Level.substFn φ lps us)) ws →
      app (Y' mm) (tupW (D.u mm (Level.substFn φ lps us)) ws) ≠ pt := fun ws hws =>
    (IsTy_of_mem_strictU (famSpace_app (hY' mm hmmN)
      (tupW_mem ((hT.spineFit ws).mp hws)))).ne_pt
  unfold LfpDatum.holeVal at hH ⊢
  rw [← hT.holeFam, holeFam_foldl_nofit hne' hne hlen hn]
  exact hH

set_option maxHeartbeats 1600000 in
/-- **The frame's accessibility from its constructors'** (`FrameAccOut`):
the group operator mixed into the carrier (`mixT`) is jointly accessible
in the enclosing frame and the group's own components (`AccJointG`), so
its least tuple — the carrier on the group (`lfpTuple_mixT`) — is
accessible in the enclosing frame (`lfpP_acc_group`).  The stored
container's own facts used are its clause's accessibility (`acc`, at
its `Type`-valued level `w`: the sections' accessibility and
monotonicity) and (W). -/
theorem frameAccOut_of {w : Nat}
    {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi)
    {Δh : List Term} {R₀ : FrameRel V} (hR₀ : HoleRelA mp.base2 φ w ctx prog hi Δh R₀)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ'))
    (hper : ∀ g j, InGrp D grp g → j < D.nctors g →
      FrameCtorAcc w (hi + grp.length) ctx.nP
        (HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)) R₀ D
        (Level.substFn φ lps us) grp dsa hi g j) :
    FrameAccOut w ctx prog hi R₀ D (Level.substFn φ lps us) dsa (InGrp D grp) := by
  classical
  haveI : Nonempty (Occ V) := ⟨(0, [], empty)⟩
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  have hkNN := h.kN
  have hnP : ctx.nP ≤ hi := by rw [← hhi]; simp only [NestCtx.hiAt]; omega
  -- the constructors' bounds, as functions
  let TBt : Nat → Nat → (Nat → V) → V := fun g j =>
    if hgj : InGrp D grp g ∧ j < D.nctors g then Classical.choose (hper g j hgj.1 hgj.2)
    else fun _ => empty
  have hTB : ∀ g j (hG : InGrp D grp g) (hj : j < D.nctors g),
      (∀ σ, w ≠ 0 → TBt g j σ ∈ˢ (tg w : V)) ∧
      (∀ σ σ', (∀ q, ParamPos (hi + grp.length) ctx.nP q → σ q = σ' q) → TBt g j σ = TBt g j σ') ∧
      ∀ ρ ρ₀ Y, R₀ ρ ρ₀ → InTupleSpace (D.w (Level.substFn φ lps us)) D.N
          (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y →
        ∀ t fs, D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ)
            (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y) t g j fs →
          ∃ (B : V) (gi : V → Occ V),
            B ⊆ˢ TBt g j (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) ∧
            (∀ b, b ∈ˢ B → Adm (HoleQ ctx ((grpNews us ds hi grp).reverse ++ prog)
                (hi + grp.length)) (gi b) ∧
              Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ Y) (gi b)) ∧
            ∀ ρ' Y', R₀ ρ ρ' → InTupleSpace (D.w (Level.substFn φ lps us)) D.N
                (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ')) Y' →
              (∀ b, b ∈ˢ B → Holds (frameVal D (Level.substFn φ lps us) grp dsa hi ρ' Y') (gi b)) →
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
    LfpDatum.finUnion (fun c => LfpDatum.finUnion (fun j => TBt c j (frameVal D (Level.substFn φ lps us) grp dsa hi ρ
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)))) (D.nctors c)) D.N
  have hA0 : ∀ ρ, w ≠ 0 → A0 ρ ∈ˢ (tg w : V) := fun ρ hw =>
    LfpDatum.finUnion_mem hw fun c _ => LfpDatum.finUnion_mem hw fun j _ => hTBsz c j _ hw
  -- the relation's tails and index sets
  have hagree : ∀ ρ ρ', R₀ ρ ρ' → AgreeOff (holeP hi ctx.nP hi) ρ ρ' := by
    intro ρ ρ' hr; have := hR₀.agree ρ ρ' hr; rwa [hhi] at this
  have htail : ∀ ρ ρ', R₀ ρ ρ' → (fun j => ρ (j + hi)) = (fun j => ρ' (j + hi)) := by
    intro ρ ρ' hr; funext j
    exact hagree ρ ρ' hr (j + hi) fun hp => by have := hp.1; omega
  have hIs : ∀ p p', R₀ p p' → ∀ m, InGrp D grp m →
      D.idx (Level.substFn φ lps us) (keyFrame dsa hi p) m
        = D.idx (Level.substFn φ lps us) (keyFrame dsa hi p') m :=
    fun p p' hr m hm => grp_idx_eq mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hm
      (hagree p p' hr)
  -- the joint accessibility
  have hacc : AccJointG (D.w (Level.substFn φ lps us)) D.N
      (fun p => D.idx (Level.substFn φ lps us) (keyFrame dsa hi p)) (fun p => ∃ p₀, R₀ p p₀) R₀
      (fun p o => Adm (HoleQ ctx prog hi) o ∧ Holds p o) (InGrp D grp)
      (fun p Y => D.Φ (Level.substFn φ lps us) (keyFrame dsa hi p)
        (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p)) Y)) A0 := by
    rintro p Y ⟨p₀, hp⟩ hY m hm hGm i hiI x hx
    have hs := (hfit p p₀ hp).1
    have hmixS := mixT_mem (G := InGrp D grp)
      (C := D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p)) (lfpTuple_mem _ _ _ _) hY
    obtain ⟨j, fs, hf, rfl⟩ := (h.fibre _ _ hs _ hmixS m hm i hiI x).mp hx
    have hj := hf.1
    obtain ⟨-, -, hsup⟩ := hTB m j hGm hj
    obtain ⟨B, gi, hB, hgi, htr⟩ := hsup p p₀ Y hp hY i fs hf
    let item : V → Occ V ⊕ (Nat × V × V) := fun b =>
      if (gi b).1 < grp.length then .inr (frameOcc D (Level.substFn φ lps us) grp (gi b))
      else .inl ((gi b).1 - grp.length, (gi b).2)
    -- a new-hole item off its fit is no occurrence, but it is held alike at
    -- every related frame (`frame_item_nofit`): the support drops it
    let NF : V → Prop := fun b => (gi b).1 < grp.length ∧ ¬ SpineFit (keyFrame dsa hi p)
      (D.ids (frameOcc D (Level.substFn φ lps us) grp (gi b)).1 (Level.substFn φ lps us))
      (gi b).2.1
    refine ⟨sep B fun b => ¬ NF b, item, fun b hb => ?_, fun b hb => ?_, ?_⟩
    · have hb' := hB b (sep_subset b hb)
      rw [hTBeq m j p p Y (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p))
        fun _ _ => rfl] at hb'
      exact LfpDatum.subset_finUnion (f := fun c => LfpDatum.finUnion (fun j => TBt c j
        (frameVal D (Level.substFn φ lps us) grp dsa hi p
          (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p)))) (D.nctors c)) hm _
        (LfpDatum.subset_finUnion (f := fun j => TBt m j (frameVal D (Level.substFn φ lps us) grp dsa hi p
          (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p)))) hj _ hb')
    · obtain ⟨hbB, hNF⟩ := mem_sep.mp hb
      obtain ⟨hQ, hH⟩ := hgi b hbB
      rcases frame_item_fwd mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hhi hQ hH with
        ⟨hlt, hGc, hin, -⟩ | ⟨hge, hQo, hHo⟩ | ⟨hlt, -, hnf⟩
      · simp only [item, ite_eq_left hlt]; exact ⟨hGc, hin⟩
      · simp only [item, ite_eq_right (show ¬ (gi b).1 < grp.length by omega)]; exact ⟨hQo, hHo⟩
      · exact absurd ⟨hlt, hnf⟩ hNF
    · rintro p' Y' hR' ⟨p₀', hp'⟩ hY' hitems
      have hs' := (hfit p' p₀' hp').1
      have hf' := htr p' Y' hR' hY' fun b hb => by
        obtain ⟨hQ, hH⟩ := hgi b hb
        by_cases hNF : NF b
        · exact frame_item_nofit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hNF.1
            (hagree p p' hR') hY hY'
            (by
              rcases frame_item_fwd mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hhi hQ hH
                with ⟨-, -, -, hfit0⟩ | ⟨hge, -⟩ | ⟨-, hl, -⟩
              · exact absurd (hfit0 p (fun _ _ => rfl)) hNF.2
              · exact absurd hNF.1 (by omega)
              · exact hl)
            hNF.2 hH
        have hib := hitems b (mem_sep.mpr ⟨hb, hNF⟩)
        rcases frame_item_fwd mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hhi hQ hH with
          ⟨hlt, -, -, hfit0⟩ | ⟨hge, -, -⟩ | ⟨hlt, -, hnf⟩
        · simp only [item, ite_eq_left hlt] at hib
          exact frame_item_bwd hlt (hfit0 p' (hagree p p' hR')) hib.2
        · simp only [item, ite_eq_right (show ¬ (gi b).1 < grp.length by omega)] at hib
          exact (holds_frameVal_ge hge).mpr hib.2
        · exact absurd ⟨hlt, hnf⟩ hNF
      have hmixS' := mixT_mem (G := InGrp D grp)
        (C := D.carrier (Level.substFn φ lps us) (keyFrame dsa hi p')) (lfpTuple_mem _ _ _ _) hY'
      exact (h.fibre _ _ hs' _ hmixS' m hm i (by rw [← hIs p p' hR' m hGm]; exact hiI) _).mpr
        ⟨j, fs, hf', rfl⟩
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
  have hmain := lfpP_acc_group (O := Occ V) hIs
    (fun p ⟨p₀, hp⟩ => ⟨_, mixT_isClosed (G := InGrp D grp)
      (h.closed (hfit p p₀ hp).1) (hDmono p p₀ hp) (hDmaps p p₀ hp)⟩)
    (fun p ⟨p₀, hp⟩ => mixT_mapsTuple (hDmaps p p₀ hp) (lfpTuple_mem _ _ _ _))
    (fun p ⟨p₀, hp⟩ => (hDacc p p₀ hp).elim fun A' hA' =>
      ⟨A', accTuple_mixT (G := InGrp D grp) hA' (lfpTuple_mem _ _ _ _)⟩) hacc
  -- the carrier on the group is the mixed operator's least tuple
  have hcarr : ∀ ρ ρ₀, R₀ ρ ρ₀ → ∀ c, InGrp D grp c →
      lfpTuple (D.w (Level.substFn φ lps us)) D.N
          (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ))
          (fun Y => D.Φ (Level.substFn φ lps us) (keyFrame dsa hi ρ)
            (mixT (InGrp D grp) (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y)) c
        = D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ) c := by
    intro ρ ρ₀ hr c hc
    exact lfpTuple_mixT (h.closed (hfit ρ ρ₀ hr).1) (hDmono ρ ρ₀ hr) (hDmaps ρ ρ₀ hr) c
      (Nat.lt_of_lt_of_le hc.1 hkNN) hc
  refine ⟨fun ρ => accPaths (A0 ρ), fun ρ hw => accPaths_mem hw (hA0 ρ hw), fun ρ ρ' hag => ?_, ?_⟩
  · show accPaths (A0 ρ) = accPaths (A0 ρ')
    have : A0 ρ = A0 ρ' := by
      show LfpDatum.finUnion _ _ = LfpDatum.finUnion _ _
      congr 1; funext c; congr 1; funext j
      exact hTBeq c j ρ ρ' _ _ hag
    rw [this]
  · intro c hc ρ ρ₀ hr i hiI x hx
    rw [← hcarr ρ ρ₀ hr c hc] at hx
    obtain ⟨B, g, hB, hg', htr⟩ := hmain ρ ⟨ρ₀, hr⟩ c (Nat.lt_of_lt_of_le hc.1 hkNN) hc i hiI x hx
    refine ⟨B, g, hB, hg', fun ρ' hr' hheld => ?_⟩
    have hx' := htr ρ' hr' ⟨ρ, hR₀.symm ρ ρ' hr'⟩ fun b hb => ⟨(hg' b hb).1, hheld b hb⟩
    rwa [hcarr ρ' ρ (hR₀.symm ρ ρ' hr') c hc] at hx'

set_option maxHeartbeats 1600000 in
/-- **A frame's constructors make it accessible** (the accessibility
twin of `frameIter`): the constructors of the reached group, instantiated
at the key and walked along the frame relation (`hwalk`, the frame
derivation's), make the group's carriers accessible in the enclosing
frame (`FrameAccOut`). -/
theorem frameIterAcc (hin : RulesInputs V mp.base2 φ) {w : Nat}
    (hwD : D.w (Level.substFn φ lps us) = w) {F : Nat}
    (hcov : ∀ c, c < D.k → ∃ nP' L, ConLeche.nestContainer ctx (D.member c) = some (nP', L) ∧
      L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
        env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2))
    {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi) {Δh : List Term}
    {R₀ : FrameRel V} (hR₀ : HoleRelA mp.base2 φ w ctx prog hi Δh R₀) (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    (hkey : ∀ ρ, Sat V Δh ρ →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      ∀ a ∈ dsa, WellDenoted V ρ a)
    {ctors : List (ConstantVal × Nat)}
    (hgc : ConLeche.groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    (hwalk : ∀ {Δ : List Term} {R : FrameRel V},
      HoleRelA mp.base2 φ w ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length) Δ R →
      ∀ (Q : ConstantVal × Nat → Prop),
      (∀ (x : ConstantVal × Nat) (crest : Expr), Q x →
        ConLeche.nestCrest (grp.map (·.1)) us ds (grpHoles hi grp)
          (x.1.type.instantiateLevelParams x.1.levelParams us) = some crest →
        (∃ ty u, ConLeche.inferTypeCore .verified env F (hi + grp.length) crest = .ok ty ∧
          ConLeche.ensureSortCore .verified env F (hi + grp.length) ty = .ok u) →
        ∃ ca, Frame (hi + grp.length) crest ∧ CtxOkP mp.base2 φ (hi + grp.length) Δ crest ∧
          denote mp.base2.acval env φ (hi + grp.length) crest = some ca ∧ GradedTy V Δ ca) →
      (∀ x ∈ ctors, Q x) →
      ∀ x ∈ ctors, CtorWalkedA mp.base2 φ w ctx ((grpNews us ds hi grp).reverse ++ prog)
        (hi + grp.length) us ds (grp.map (·.1)) (grpHoles hi grp) Δ R x) :
    FrameAccOut w ctx prog hi R₀ D (Level.substFn φ lps us) dsa (InGrp D grp) := by
  have hQ := grpCtors_found hg hcov hgc
  have hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ') := fun ρ ρ' hr =>
    ⟨(hkey ρ (hR₀.dom ρ ρ' hr).1).1, (hkey ρ' (hR₀.dom ρ ρ' hr).2).1⟩
  have hR' := frameRelA_holeRelA mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hhi hR₀ hwD
    (grp_arity mp hD hnN hkN hfind hg _)
  have hwalked := hwalk hR'
    (fun x => ∃ c j, InGrp D grp c ∧ j < D.nctors c ∧
      env.find? (D.ctorName c j) = some (.ctorInfo x.1 ds.length x.2))
    (fun x crest hQx hcr hinf => by
      obtain ⟨c, j, hGc, hj, hfc⟩ := hQx
      have hwf := mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfc)
      have hcl : (x.1.type.instantiateLevelParams x.1.levelParams us).hasFvar = false := by
        rw [Expr.hasFvar_instantiateLevelParams]; exact hwf.1
      have hbb : (x.1.type.instantiateLevelParams x.1.levelParams us).looseBVarsBounded 0 = true := by
        rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
      obtain ⟨hfr, hC⟩ := crest_frame mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hΔ hCds hLds
        hkey hcl hbb hcr
      obtain ⟨-, crest', ab, hcr', ⟨Tys, hlT, hTys, hEqF⟩, hlen, hrd⟩ :=
        crest_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hGc.1 hj hfc
      rw [hcr] at hcr'
      obtain rfl := Option.some.inj hcr'
      obtain ⟨ty, u, hty, hsort⟩ := hinf
      exact ⟨_, hfr, hC, hrd, gradedTy_of_sort hin hty hsort hfr hC.toCtxOk hrd⟩)
    hQ
  refine frameAccOut_of mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hhi hR₀ hfit
    fun g j hG hj => ?_
  obtain ⟨x, hxmem, hfc⟩ := grpCtor_found hcov hgc hG hj
  exact frameCtor_acc mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hwD hhi hR₀ hfit hG hj
    hfc (hwalked _ hxmem)

end Frame

end ConLeche.Model
