module

public import ConLeche.Verify.Rules.Defs
public import ConLeche.Verify.Knot
import ConLeche.Rules.Derived
import ConLeche.Verify.InferLemmas

public section

/-!
# The certificate bridges (task #305, lane B1)

The helpers of `Core.lean` that several bodies call — the telescope
certificate, the list walk, the two proof-irrelevance tests, the three
structure certificates, η, the stuck cascade, the same-head
short-circuit, the `Bool.true` shortcut — each bridged at `fuel` from
the entry-point bridges at `fuel` (the helpers run the record
`pureFns .verified eager env fuel`, whose fields ARE the entry points at
`fuel`: `whnf_def`, `defeq_def`, `inferTypeIO_def`).

Each theorem's proof is the site's `Verify` inversion lemma
(`iotaCertsFull_step_inv`, `defEqList_step_inv`, `proofIrrel_inv`,
`propIrrel_inv`, `structEtaCertWith_inv`, `structEtaCert_inv`,
`structUnitCert_inv`, `etaCert_inv`,
`defeqSpine_inv`; `stuckIrrel` and `boolTrueShortcut` have none yet
and are inverted by hand) followed by the one rule.
-/

namespace ConLeche.Rules

variable {μ : CheckMode} {eager : Bool} {env : Env} {fuel : Nat}

/-- `iotaCertsFull` ⇒ `CertsF` (`iotaCertsFull_step_inv`; every slot
through `hi` and `hd`; task #342 L10). -/
theorem iotaCertsFull_bridge (hd : DefEqBridge μ eager env fuel) (hi : InferBridge μ eager env
    fuel) :
    ∀ {d : Nat} {ty : Expr} {args : List Expr},
      iotaCertsFullFueled μ eager env fuel d ty args = .ok true →
      CertsF env d ty args := by
  intro d ty args
  induction args generalizing ty with
  | nil => intro _; exact .nil
  | cons arg rest ih =>
    match ty with
    | .forallE ty₀ body =>
      intro h
      obtain ⟨ta, hta, hde, hrest⟩ := iotaCertsFull_step_inv h
      exact .cert (hi hta) (hd hde) (ih hrest)
    | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _
    | .letE _ _ _ | .lit _ | .proj _ _ _ =>
      intro h
      simp [iotaCertsFullFueled, iotaCertsFull, pure, Except.pure] at h

/-- `defEqList` ⇒ `DefEqList` (`defEqList_step_inv`). -/
theorem defEqList_bridge (hd : DefEqBridge μ eager env fuel) :
    ∀ {d : Nat} {as bs : List Expr},
      defEqListFueled μ eager env fuel d as bs = .ok true →
      DefEqList env d as bs := by
  intro d as
  induction as with
  | nil =>
    intro bs h
    match bs with
    | [] => exact .nil
    | _ :: _ =>
      simp [defEqListFueled, defEqList, pure, Except.pure] at h
  | cons a as ih =>
    intro bs h
    match bs with
    | [] =>
      simp [defEqListFueled, defEqList, pure, Except.pure] at h
    | b :: bs =>
      obtain ⟨hab, hrest⟩ := defEqList_step_inv h
      exact .cons (hd hab) (ih hrest)

/-- `proofIrrel` ⇒ `DefEq.proofIrrel` (`proofIrrel_inv`). -/
theorem proofIrrel_bridge (hw : WhnfBridge μ eager env fuel) (hio : InferIOBridge μ eager env fuel)
    {d : Nat} {a b : Expr}
    (h : proofIrrelFueled μ eager env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨ta, sta, uT, tb, stb, vT, hta, hsta, hwsta, huT, htb, hstb, hwstb, hvT⟩ :=
    proofIrrel_inv h
  exact .proofIrrel (inferTypeIO_bridge hio hta)
    (inferTypeIO_bridge hio hsta) (hw hwsta) huT
    (inferTypeIO_bridge hio htb) (inferTypeIO_bridge hio hstb)
    (hw hwstb) hvT

/-- `propIrrel` ⇒ `DefEq.proofFast` or `DefEq.proofIrrel`
(`propIrrel_inv`). -/
theorem propIrrel_bridge (hw : WhnfBridge μ eager env fuel) (hio : InferIOBridge μ eager env fuel)
    {d : Nat} {a b : Expr}
    (h : propIrrelFueled μ eager env fuel d a b = .ok true) :
    DefEq env d a b := by
  rcases propIrrel_inv h with ⟨hfa, hfb⟩ |
    ⟨ta, sta, uT, tb, stb, vT, hta, hsta, hwsta, huT, htb, hstb, hwstb, hvT⟩
  · exact .proofFast hfa hfb
  · exact .proofIrrel (inferTypeIO_bridge hio hta)
      (inferTypeIO_bridge hio hsta) (hw hwsta) huT
      (inferTypeIO_bridge hio htb) (inferTypeIO_bridge hio hstb)
      (hw hwstb) hvT

/-- `structEtaCertWith` at a given head-normal type ⇒ `DefEq.structEta`
(`structEtaCertWith_inv`).  The two runs that produced `wtb` are
`structEtaCert`'s, so they are hypotheses here. -/
theorem structEtaCertWith_bridge (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hio : InferIOBridge μ eager env fuel)
    {d : Nat} {a b tb wtb : Expr}
    (htb : inferTypeIO μ eager env fuel d b = .ok tb)
    (hwtb : whnf μ eager env fuel d tb = .ok wtb)
    (h : structEtaCertWithFueled μ eager env fuel d a b wtb = .ok true) :
    DefEq env d a b := by
  obtain ⟨c, us, cvc, cnP, cnF, T, us', cvT, caps,
    hfn, hfc, hlen, hwfn, hfT, heta, hctor, hresT, hresc, hplen, hulen,
    hlps, hslots, hus, hpar, hfields⟩ :=
    structEtaCertWith_inv h
  exact .structEta (inferTypeIO_bridge hio htb) (hw hwtb) hfn hfc hlen hwfn hfT
    heta hctor hresT hresc hplen hulen hlps hslots hus
    (defEqList_bridge hd hpar) (defEqList_bridge hd hfields)

/-- `structEtaCert` ⇒ `DefEq.structEta` (`structEtaCert_inv`, then
`structEtaCertWith_bridge`). -/
theorem structEtaCert_bridge (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hio : InferIOBridge μ eager env fuel)
    {d : Nat} {a b : Expr}
    (h : structEtaCertFueled μ eager env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨tb, wtb, htb, hwtb, h'⟩ := structEtaCert_inv h
  exact structEtaCertWith_bridge hw hd hio htb hwtb h'

/-- `structUnitCert` ⇒ `DefEq.structUnit` (`structUnitCert_inv`). -/
theorem structUnitCert_bridge (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hio : InferIOBridge μ eager env fuel)
    {d : Nat} {a b : Expr}
    (h : structUnitCertFueled μ eager env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨ta, wta, T, us', cvT, caps, tb, wtb,
    hta, hwta, hwfn, hfT, hunit, hres, hplen, hulen, htb, hwtb, hF, hde⟩ :=
    structUnitCert_inv h
  exact .structUnit (inferTypeIO_bridge hio hta) (hw hwta) hwfn hfT hunit
    hres hplen hulen (inferTypeIO_bridge hio htb) (hw hwtb) hF (hd hde)

/-- `etaCert` ⇒ `DefEq.eta` (`etaCert_inv`): the λ's opened body's
full-grade type against the ∀'s body is the checker's η check. -/
theorem etaCert_bridge (hμ : μ.verifiedChecks = true) (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hi : InferBridge μ eager env fuel) (hio : InferIOBridge μ
        eager env fuel)
    {d : Nat} {ty body b : Expr}
    (h : etaCertFueled μ eager env fuel d ty body b = .ok true) :
    DefEq env d (.lam ty body) b := by
  obtain ⟨hneu, tb, ty₂, fb, htb, hwtb, hdty, hdbody, hT2⟩ := etaCert_inv h
  obtain ⟨t₁, ht₁, hdt⟩ := hT2 hμ
  exact .eta hneu (inferTypeIO_bridge hio htb) (hw hwtb) (hd hdty) (hd hdbody)
    (hi ht₁) (hd hdt)

/-- `stuckIrrel` ⇒ one of its four arms (`structEtaCert_bridge` twice —
the second through `DefEq.structEtaR` —, `structUnitCert_bridge`,
`proofIrrel_bridge`).  No inversion lemma exists for `stuckIrrel`
today; it is four `exceptBind_ok`s. -/
theorem stuckIrrel_bridge (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hio : InferIOBridge μ eager env fuel)
    {d : Nat} {a b : Expr}
    (h : stuckIrrelFueled μ eager env fuel d a b = .ok true) :
    DefEq env d a b := by
  dsimp only [stuckIrrelFueled] at h
  simp only [stuckIrrel, Bind.bind, Except.bind, structEtaCert_fold,
    structUnitCert_fold, proofIrrel_fold] at h
  cases h3 : structEtaCertFueled μ eager env fuel d a b with
  | error err => rw [h3] at h; exact nomatch h
  | ok r3 =>
  rw [h3] at h
  dsimp only at h
  cases r3 with
  | true => exact structEtaCert_bridge hw hd hio h3
  | false =>
  cases h4 : structEtaCertFueled μ eager env fuel d b a with
  | error err => rw [h4] at h; exact nomatch h
  | ok r4 =>
  rw [h4] at h
  dsimp only at h
  cases r4 with
  | true => exact .structEtaR (structEtaCert_bridge hw hd hio h4)
  | false =>
  cases h5 : structUnitCertFueled μ eager env fuel d a b with
  | error err => rw [h5] at h; exact nomatch h
  | ok r5 =>
  rw [h5] at h
  dsimp only at h
  cases r5 with
  | true => exact structUnitCert_bridge hw hd hio h5
  | false => exact proofIrrel_bridge hw hio h

/-- `defeqSpine` ⇒ `DefEq.constSpine` (`defeqSpine_inv`). -/
theorem defeqSpine_bridge (hd : DefEqBridge μ eager env fuel)
    {d : Nat} {a b : Expr}
    (h : defeqSpineFueled μ eager env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨n, us, us', ha, hb, -, hus, hl⟩ := defeqSpine_inv h
  have hr := (defEqList_bridge hd hl).reverse
  rw [List.reverse_reverse, List.reverse_reverse] at hr
  exact .constSpine ha hb hus hr

/-- `boolTrueShortcut` ⇒ `DefEq.boolTrue`. -/
theorem boolTrueShortcut_bridge (hw : WhnfBridge μ eager env fuel)
    {d : Nat} {a : Expr}
    (h : boolTrueShortcutFueled μ eager env fuel d a = .ok true) :
    DefEq env d a (.const boolTrueName []) := by
  dsimp only [boolTrueShortcutFueled] at h
  simp only [boolTrueShortcut, Bind.bind, Except.bind, whnf_def] at h
  cases hwh : whnf μ eager env fuel d a with
  | error err => rw [hwh] at h; exact nomatch h
  | ok w =>
  rw [hwh] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact .boolTrue (hw hwh) h

end ConLeche.Rules
