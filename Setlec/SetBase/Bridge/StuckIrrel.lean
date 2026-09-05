import Setlec.SetBase.Bridge.Certs

/-!
# `stuckIrrel`'s cascade (task #148, T3, batch d)

`stuckIrrel` (`Core.lean:1044-1051`) is six attempts in order:
`pairEtaCert` both ways, `structEtaCert` both ways, `structUnitCert`,
then `proofIrrel`.  The design's note that "the `stuckIrrel` cascade is
not a rule — it is the *bridge's* dispatch order" is discharged here:
this module is that dispatch, and each arm lands on D12/D10/D11/D8-D9,
with the two "wrong way round" arms composed by D2 `symm`.

`structUnitCert` (D11) is proved here; the two eta certificates are
named obligations, discharged in `Bridge/StructEta.lean` and
`Bridge/PairEta.lean`, and `proofIrrel` is already proved
(`Bridge/Irrel.lean`).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env}

/-- `pairEtaCert`'s verdict yields an equation (D12). -/
def PairEtaCertStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
    pairEtaCertP mode env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR mode m.cval env φ d Δ a → CtxOkR mode m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → DefEq mode env m.cval φ Δ va vb

/-- `structEtaCert`'s verdict yields an equation (D10). -/
def StructEtaCertStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
    structEtaCertP mode env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR mode m.cval env φ d Δ a → CtxOkR mode m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → DefEq mode env m.cval φ Δ va vb

/-! ## D11: `structUnitCert`

A stored unit-like family collapses all its inhabitants.  The rule's
shape is the certificate's own: both sides' types, the equation between
them, and the type-former's telescope certificate — the last through
`certs_teleR`, which is the first consumer of that walk. -/

/-- **`StructUnitCertStepR`, proved.** -/
theorem structUnitCert_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (hg : mode.betaGate = false)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {a b : Expr}
    (h : structUnitCertP mode env fuel d a b = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b)
    (hCa : CtxOkR mode m.cval env φ d Δ a)
    (hCb : CtxOkR mode m.cval env φ d Δ b)
    {va vb : VExpr} (hva : denote m.cval env φ d a = some va)
    (hvb : denote m.cval env φ d b = some vb) :
    DefEq mode env m.cval φ Δ va vb := by
  obtain ⟨ta, wta, T, us', cvT, caps, tb, wtb, hta, hwta, hfn, hfind, hunit,
    hres, hlenArgs, hlenUs, hstrip, htb, hwtb, hdeq, hcerts⟩ :=
    structUnitCert_inv h
  rw [Setlec.inferTypeIO_off hg] at hta htb
  -- both sides' types, at the `whnf`'d shapes
  obtain ⟨va', WA, hva', hWA, TA, hAI, hAD⟩ :=
    inferShapeR m φ ihw ihi hta hwta hwa hba hLa hCa
  obtain rfl : va' = va := by rw [hva'] at hva; exact Option.some.inj hva
  obtain ⟨vb', WB, hvb', hWB, TB, hBI, hBD⟩ :=
    inferShapeR m φ ihw ihi htb hwtb hwb hbb hLb hCb
  obtain rfl : vb' = vb := by rw [hvb'] at hvb; exact Option.some.inj hvb
  -- the frame conditions of the two reducts (for the equation between them)
  obtain ⟨htaw, htab, htaL, htaC⟩ := frame_inferR m.wf hta hwa hba hLa hCa
  obtain ⟨htbw, htbb, htbL, htbC⟩ := frame_inferR m.wf htb hwb hbb hLb hCb
  obtain ⟨hwtaw, hwtab, hwtaL, hwtaC⟩ := by
    exact (⟨whnf_WScoped m.wf fuel hwta htaw, whnf_looseBVars m.wf fuel hwta htab,
      fun l hl => htaL l (whnf_fvarLeaves m.wf fuel hwta l hl),
      CtxOkR.of_subset (whnf_fvarLeaves m.wf fuel hwta) htaC⟩ :
      Expr.WScoped d wta ∧ wta.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded wta ∧ CtxOkR mode m.cval env φ d Δ wta)
  obtain ⟨hwtbw, hwtbb, hwtbL, hwtbC⟩ := by
    exact (⟨whnf_WScoped m.wf fuel hwtb htbw, whnf_looseBVars m.wf fuel hwtb htbb,
      fun l hl => htbL l (whnf_fvarLeaves m.wf fuel hwtb l hl),
      CtxOkR.of_subset (whnf_fvarLeaves m.wf fuel hwtb) htbC⟩ :
      Expr.WScoped d wtb ∧ wtb.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded wtb ∧ CtxOkR mode m.cval env φ d Δ wtb)
  have hWAB : DefEq mode env m.cval φ Δ WA WB :=
    ihd hdeq hwtaw hwtab hwtaL hwtbw hwtbb hwtbL hwtaC hwtbC hWA hWB
  -- the left type's shape: the family applied to its parameters
  have hea : wta = Expr.mkAppN (.const T us') wta.getAppArgs := by
    rw [← hfn, Expr.mkAppN_getApp]
  rw [hea] at hWA
  obtain ⟨vhead, ts, hvhead, hspa, rfl⟩ := denote_mkAppN_inv hWA
  rw [denote_const, hfind] at hvhead
  dsimp only at hvhead
  split at hvhead
  · next hlen =>
    obtain rfl : vhead
        = m.cval T (Level.substFn φ cvT.levelParams us') :=
      (Option.some.inj hvhead).symm
    -- the type-former's telescope certificate
    obtain ⟨TFv, hTFv0, hTFvC, hTFvd⟩ :=
      denote_declTypeR m φ hcl hfind us' d
    obtain ⟨hTw, hTb, hTL, hTC⟩ :=
      frame_declTypeR (cval := m.cval) (φ := φ) (mode := mode) m.wf hfind us' d
        hCa.1
    obtain ⟨ts', rest, hsp', htele⟩ :=
      certs_teleR m φ hg hcl ihd ihi _ wta.getAppArgs TFv hcerts hTw hTb hTL hTC
        hTFvd (frame_spineR hwtaw hwtab hwtaL hwtaC)
    obtain rfl : ts' = ts := DenoteSpine.det hsp' hspa
    exact DefEq.structUnit hfind hunit hres
      (by rw [hspa.length, hlenArgs]) hlenUs hstrip hTFv0 hTFvC
      hAI hAD hBI hBD hWAB htele
  · exact nomatch hvhead

/-! ## The cascade -/

/-- `stuckIrrel`'s verdict yields an equation: the bridge's dispatch
order, arm for arm. -/
def StuckIrrelStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
    stuckIrrelP mode env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR mode m.cval env φ d Δ a → CtxOkR mode m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → DefEq mode env m.cval φ Δ va vb

/-- **`StuckIrrelStepR`**, modulo the two eta certificates.  The two
reversed arms are `DefEq.symm` (D2) — which is exactly what the design
says D2 is there for. -/
theorem stuckIrrel_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hg : mode.betaGate = false)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel)
    (hpair : PairEtaCertStepR (mode := mode) m φ fuel)
    (hseta : StructEtaCertStepR (mode := mode) m φ fuel) :
    StuckIrrelStepR (mode := mode) m φ fuel := by
  intro d Δ a b h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  simp only [stuckIrrelP, stuckIrrel, Bind.bind, Except.bind,
    pairEtaCert_fold, structEtaCert_fold, structUnitCert_fold,
    proofIrrel_fold] at h
  cases h1 : pairEtaCertP mode env fuel d a b with
  | error err => rw [h1] at h; exact nomatch h
  | ok r1 =>
  rw [h1] at h
  dsimp only at h
  cases r1 with
  | true => exact hpair h1 hwa hba hLa hwb hbb hLb hCa hCb hva hvb
  | false =>
  cases h2 : pairEtaCertP mode env fuel d b a with
  | error err => rw [h2] at h; exact nomatch h
  | ok r2 =>
  rw [h2] at h
  dsimp only at h
  cases r2 with
  | true => exact (hpair h2 hwb hbb hLb hwa hba hLa hCb hCa hvb hva).symm
  | false =>
  cases h3 : structEtaCertP mode env fuel d a b with
  | error err => rw [h3] at h; exact nomatch h
  | ok r3 =>
  rw [h3] at h
  dsimp only at h
  cases r3 with
  | true => exact hseta h3 hwa hba hLa hwb hbb hLb hCa hCb hva hvb
  | false =>
  cases h4 : structEtaCertP mode env fuel d b a with
  | error err => rw [h4] at h; exact nomatch h
  | ok r4 =>
  rw [h4] at h
  dsimp only at h
  cases r4 with
  | true => exact (hseta h4 hwb hbb hLb hwa hba hLa hCb hCa hvb hva).symm
  | false =>
  cases h5 : structUnitCertP mode env fuel d a b with
  | error err => rw [h5] at h; exact nomatch h
  | ok r5 =>
  rw [h5] at h
  dsimp only at h
  cases r5 with
  | true =>
    exact structUnitCert_stepR m φ hg hcl ihw ihd ihi h5 hwa hba hLa hwb hbb
      hLb hCa hCb hva hvb
  | false =>
    exact proofIrrel_stepR hg m φ ihw ihi h hwa hba hLa hwb hbb hLb hCa hCb
      hva hvb

end Setlec.SetR
