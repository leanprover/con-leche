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

/-- `structEtaFull` ⇒ `DefEq.structEta` (`structEtaFull_inv`, then
`structEtaCertWith_bridge`). -/
theorem structEtaFull_bridge (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hio : InferIOBridge μ eager env fuel)
    {d : Nat} {a b : Expr}
    (h : structEtaFullFueled μ eager env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨tb, wtb, htb, hwtb, h'⟩ := structEtaFull_inv h
  exact structEtaCertWith_bridge hw hd hio htb hwtb h'

/-- `structEtaExpand` ⇒ `DefEqExpand`: one `step` per binder, `done`
by `structEtaFull_bridge`. -/
theorem structEtaExpand_bridge (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hio : InferIOBridge μ eager env fuel) :
    ∀ (k d : Nat) {a b t : Expr},
      structEtaExpandFueled μ eager env fuel k d a b t = .ok true →
      DefEqExpand env d a b t
  | 0, d, a, b, t, h => .done (structEtaFull_bridge hw hd hio (by
      dsimp only [structEtaExpandFueled] at h; rw [structEtaExpand] at h; exact h))
  | k + 1, d, a, b, t, h => by
    obtain ⟨dom, body, rfl, h'⟩ := structEtaExpand_succ_inv h
    exact .step (structEtaExpand_bridge hw hd hio k (d + 1) h')

/-- `structEtaCert` ⇒ `DefEq.structEta` (fully applied) or
`DefEq.etaExpand` (partially applied) (`structEtaCert_inv`). -/
theorem structEtaCert_bridge (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hio : InferIOBridge μ eager env fuel)
    {d : Nat} {a b : Expr}
    (h : structEtaCertFueled μ eager env fuel d a b = .ok true) :
    DefEq env d a b := by
  rcases structEtaCert_inv h with h' | ⟨k, ta, tb, hna, hnb, hta, htb, hde, hex⟩
  · exact structEtaFull_bridge hw hd hio h'
  · exact .etaExpand hna hnb (inferTypeIO_bridge hio hta) (inferTypeIO_bridge hio htb)
      (hd hde) (structEtaExpand_bridge hw hd hio k d hex)

/-- `isPropType` ⇒ the proposition premises (`isPropType_inv`). -/
theorem isPropType_bridge (hw : WhnfBridge μ eager env fuel)
    (hio : InferIOBridge μ eager env fuel) {d : Nat} {T : Expr}
    (h : isPropTypeFueled μ eager env fuel d T = .ok true) :
    ∃ tt u, Infer env .io d T tt ∧ Red env d tt (.sort u) ∧
      Level.isEquiv u .zero = some true := by
  obtain ⟨tt, u, htt, hwt, hu⟩ := isPropType_inv h
  exact ⟨tt, u, inferTypeIO_bridge hio htt, hw hwt, hu⟩

/-- `unitLikeFields` ⇒ `UnitFields`, given the field test's bridge. -/
theorem unitLikeFields_bridge (hw : WhnfBridge μ eager env fuel)
    (hio : InferIOBridge μ eager env fuel) {ul : Nat → Expr → CheckM Bool}
    (hul : ∀ {d : Nat} {e : Expr}, ul d e = .ok true → UnitLike env d e) :
    ∀ (n d : Nat) {t : Expr},
      unitLikeFields (pureFns μ eager env fuel) ul n d t = .ok true →
      UnitFields env d t n
  | 0, _, _, _ => .nil
  | n + 1, d, t, h => by
    obtain ⟨dom, body, rfl, hok, hrest⟩ := unitLikeFields_succ_inv h
    have ih := unitLikeFields_bridge hw hio hul n (d + 1) hrest
    rcases hok with hp | hu
    · obtain ⟨tt, u, htt, hr, hz⟩ := isPropType_bridge hw hio hp
      exact .prop htt hr hz ih
    · exact .unit (hul hu) ih

/-- `unitLikeStruct` ⇒ the `unit` or `struct` rule (`unitLikeStruct_inv`),
given the reduction to `w`. -/
theorem unitLikeStruct_bridge (hw : WhnfBridge μ eager env fuel)
    (hio : InferIOBridge μ eager env fuel) {ul : Nat → Expr → CheckM Bool}
    (hul : ∀ {d : Nat} {e : Expr}, ul d e = .ok true → UnitLike env d e)
    {d : Nat} {T w : Expr} (hr : Red env d T w)
    (h : unitLikeStruct (pureFns μ eager env fuel) ul env d w = .ok true) :
    UnitLike env d T := by
  rcases unitLikeStruct_inv h with hsh | ⟨tele, n, hsh, hf⟩
  · exact .unit hr hsh
  · exact .struct hr hsh (unitLikeFields_bridge hw hio hul n d hf)

/-- `unitLikeLoop` ⇒ `UnitLike` (`unitLikeLoop_succ_inv`, by induction on
the budget). -/
theorem unitLikeLoop_bridge (hw : WhnfBridge μ eager env fuel)
    (hio : InferIOBridge μ eager env fuel) :
    ∀ (f : Nat) {d : Nat} {T : Expr},
      unitLikeLoopFueled μ eager env fuel f d T = .ok true → UnitLike env d T
  | 0, d, T, h => by
    simp [unitLikeLoopFueled, unitLikeLoop, pure, Except.pure] at h
  | f + 1, d, T, h => by
    obtain ⟨w, hwh, hpi | hs⟩ := unitLikeLoop_succ_inv h
    · obtain ⟨dom, body, rfl, h'⟩ := hpi
      exact .pi (hw hwh) (unitLikeLoop_bridge hw hio f h')
    · exact unitLikeStruct_bridge hw hio (fun h => unitLikeLoop_bridge hw hio f h) (hw hwh) hs

/-- `structUnitCert` ⇒ `DefEq.unitLike` (`structUnitCert_inv`). -/
theorem structUnitCert_bridge (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hio : InferIOBridge μ eager env fuel)
    {d : Nat} {a b : Expr}
    (h : structUnitCertFueled μ eager env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨ta, wta, tb, wtb, hta, hwta, hnA, hul, htb, hwtb, hnB, hde⟩ :=
    structUnitCert_inv h
  exact .unitLike (inferTypeIO_bridge hio hta) (hw hwta) hnA
    (unitLikeLoop_bridge hw hio _ hul) (inferTypeIO_bridge hio htb) (hw hwtb) hnB (hd hde)

/-- `etaCert` ⇒ `DefEq.eta` (`etaCert_inv`): the λ's opened body's
full-grade type against the ∀'s body is the checker's η check. -/
theorem etaCert_bridge (hw : WhnfBridge .verified eager env fuel)
    (hd : DefEqBridge .verified eager env fuel) (hi : InferBridge .verified eager env fuel) (hio : InferIOBridge .verified
        eager env fuel)
    {d : Nat} {ty body b : Expr}
    (h : etaCertFueled .verified eager env fuel d ty body b = .ok true) :
    DefEq env d (.lam ty body) b := by
  obtain ⟨hneu, tb, ty₂, fb, htb, hwtb, hdty, hdbody, hT2⟩ := etaCert_inv h
  obtain ⟨t₁, ht₁, hdt⟩ := hT2 rfl
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
