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
`pureFns .verified env fuel`, whose fields ARE the entry points at
`fuel`: `whnf_def`, `defeq_def`, `inferTypeIO_def`).

Each theorem's proof is the site's `Verify` inversion lemma
(`iotaCerts_step_inv_gate`, `defEqList_step_inv`, `proofIrrel_inv`,
`propIrrel_inv`, `structEtaCertWith_inv`, `structEtaCert_inv`,
`structUnitCert_inv`, `etaCert_inv`, `structEtaProjCerts_inv`,
`defeqSpine_inv`; `stuckIrrel` and `boolTrueShortcut` have none yet
and are inverted by hand as `Model/Steps/Stuck.lean`'s
`stuckIrrelFueled_of_claims` does) followed by the one rule.
-/

namespace ConLeche.Rules

variable {env : Env} {fuel : Nat}

/-- `iotaCerts` ⇒ `Certs` (`iotaCerts_step_inv_gate`; a licensed
`.never` slot lands on `Certs.skip`, a certified one on `Certs.cert`
through `inferTypeIO_bridge` and `hd`). -/
theorem iotaCerts_bridge (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel) :
    ∀ {d : Nat} {lic : Bool} {ty : Expr} {args : List Expr},
      iotaCertsFueled .verified env fuel d lic ty args = .ok true →
      Certs env d lic ty args := by
  sorry

/-- `defEqList` ⇒ `DefEqList` (`defEqList_step_inv`). -/
theorem defEqList_bridge (hd : DefEqBridge env fuel) :
    ∀ {d : Nat} {as bs : List Expr},
      defEqListFueled .verified env fuel d as bs = .ok true →
      DefEqList env d as bs := by
  sorry

/-- `structEtaProjCerts` ⇒ `EtaProjCerts` (`structEtaProjCerts_inv`,
one `iotaCerts_bridge` per field). -/
theorem structEtaProjCerts_bridge (hd : DefEqBridge env fuel)
    (hio : InferIOBridge env fuel) :
    ∀ {d : Nat} {T : Name} {us' : List Level} {targs : List Expr} {b : Expr}
      {lpsT : List Name} {idxs : List Nat},
      structEtaProjCertsFueled .verified env fuel d T us' targs b lpsT idxs
        = .ok true →
      EtaProjCerts env d T us' targs b lpsT idxs := by
  sorry

/-- `proofIrrel` ⇒ `DefEq.unitLike` or `DefEq.proofIrrel`
(`proofIrrel_inv`). -/
theorem proofIrrel_bridge (hw : WhnfBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : proofIrrelFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  sorry

/-- `propIrrel` ⇒ `DefEq.proofFast` or `DefEq.proofIrrel`
(`propIrrel_inv`). -/
theorem propIrrel_bridge (hw : WhnfBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : propIrrelFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  sorry

/-- `structEtaCertWith` at a given head-normal type ⇒ `DefEq.structEta`
(`structEtaCertWith_inv`).  The two runs that produced `wtb` are the
caller's (`structEtaCert`'s own, or the η rescue's `tm`/`tmaj`), so
they are hypotheses here. -/
theorem structEtaCertWith_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b tb wtb : Expr}
    (htb : inferTypeIO .verified env fuel d b = .ok tb)
    (hwtb : whnf .verified env fuel d tb = .ok wtb)
    (h : structEtaCertWithFueled .verified env fuel d a b wtb = .ok true) :
    DefEq env d a b := by
  sorry

/-- `structEtaCert` ⇒ `DefEq.structEta` (`structEtaCert_inv`, then
`structEtaCertWith_bridge`). -/
theorem structEtaCert_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : structEtaCertFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨tb, wtb, htb, hwtb, h'⟩ := structEtaCert_inv h
  exact structEtaCertWith_bridge hw hd hio htb hwtb h'

/-- `structUnitCert` ⇒ `DefEq.structUnit` (`structUnitCert_inv`). -/
theorem structUnitCert_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : structUnitCertFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  sorry

/-- `etaCert` ⇒ `DefEq.eta` (`etaCert_inv`; the annotation agreement is
the inversion's `verifiedChecks = true →` conjunct at `rfl`). -/
theorem etaCert_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {ty body b : Expr} {mb : BinderMeta}
    (h : etaCertFueled .verified env fuel d ty body mb b = .ok true) :
    DefEq env d (.lam ty body mb) b := by
  sorry

/-- `stuckIrrel` ⇒ one of its four arms (`structEtaCert_bridge` twice —
the second through `DefEq.structEtaR` —, `structUnitCert_bridge`,
`proofIrrel_bridge`).  No inversion lemma exists for `stuckIrrel`
today; it is four `exceptBind_ok`s. -/
theorem stuckIrrel_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : stuckIrrelFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  sorry

/-- `defeqSpine` ⇒ `DefEq.constSpine` (`defeqSpine_inv`). -/
theorem defeqSpine_bridge (hd : DefEqBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : defeqSpineFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨n, us, us', ha, hb, -, hus, hl⟩ := defeqSpine_inv h
  exact .constSpine ha hb hus (defEqList_bridge hd hl)

/-- `boolTrueShortcut` ⇒ `DefEq.boolTrue`. -/
theorem boolTrueShortcut_bridge (hw : WhnfBridge env fuel)
    {d : Nat} {a : Expr}
    (h : boolTrueShortcutFueled .verified env fuel d a = .ok true) :
    DefEq env d a (.const boolTrueName []) := by
  sorry

end ConLeche.Rules
