module

public import ConLeche.Verify.Rules.Defs
public import ConLeche.Verify.Knot
import ConLeche.Verify.Rules.Certs
import ConLeche.Rules.Derived
import ConLeche.Verify.InferLemmas

public section

/-!
# The reduction bridges (task #305, lane B2)

`whnfCore` and `whnf` at `fuel + 1` from the five bridges at `fuel`,
through the reduction helpers: literal acceleration, the literal
expansions, the projection certificate, the stuck-major rescues, the
major's preparation, ι, and the two loops.

Inversions: `whnf_app_inv` (the `.app` clause: β gated/certified, ι,
stuck), `whnf_proj_inv` (the `.proj` clause), `whnfCore_leaf_*`
(`Semantics/WhnfCoreLeaf.lean`), `whnfCore_letE_inv`, `whnfStep_inv`,
`whnfLoopFuel_succ`, `reduceNat`'s branches (no inversion lemma:
`Model/Steps/Nat.lean`'s `natLeaf_unary`/`natLeaf_binary` do the
case analysis), `litMajorToCtorFueled_inv`, `projLitToCtorFueled_inv`,
`projCertAtFueled_verified` + `projCert_inv`, `majorToCtor_inv`,
`prepareMajorFueled_ind`, `iotaRec_inv`, `iotaIndexOk_inv`.
-/

namespace ConLeche.Rules

variable {env : Env} {fuel : Nat}

/-- `reduceNat` ⇒ `Red.natSucc` / `Red.natOp` (the two accelerated
shapes; the WF-names safety net throws or answers `none`). -/
theorem reduceNat_bridge (hw : WhnfBridge env fuel)
    {d : Nat} {e e₂ : Expr}
    (h : reduceNatFueled .verified env fuel d e = .ok (some e₂)) :
    Red env d e e₂ := by
  match e, h with
  | .app (.const c []) a, h =>
    simp only [reduceNatFueled, reduceNat, Bind.bind, Except.bind, whnf_def] at h
    split at h
    · next hcond =>
      obtain ⟨rfl, hnat⟩ := hcond
      cases hwa : whnf .verified env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hra : rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n =>
        rw [hra] at h
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        subst h
        exact .natSucc hnat (hw hwa) hra
    · simp [pure, Except.pure] at h
  | .app (.app (.const c []) a) b, h =>
    simp only [reduceNatFueled, reduceNat, Bind.bind, Except.bind, whnf_def] at h
    split at h
    · next hcond =>
      obtain ⟨hnames, hstored⟩ := hcond
      have hmem : c ∈ natBinOpNames := by
        rcases hnames with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      cases hwa : whnf .verified env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hra : rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n₁ =>
      rw [hra] at h
      dsimp only at h
      cases hwb : whnf .verified env fuel d b with
      | error err => rw [hwb] at h; exact nomatch h
      | ok b0 =>
      rw [hwb] at h
      dsimp only at h
      cases hrb : rawNatLit? b0 with
      | none => rw [hrb] at h; simp [pure, Except.pure] at h
      | some n₂ =>
        rw [hrb] at h
        dsimp only at h
        cases hres : natOpResult c n₁ n₂ with
        | none => rw [hres] at h; simp [pure, Except.pure] at h
        | some r =>
          rw [hres] at h
          simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          subst h
          exact .natOp hmem hstored (hw hwa) hra (hw hwb) hrb hres
    · split at h
      · cases hwa : whnf .verified env fuel d a with
        | error err => rw [hwa] at h; exact nomatch h
        | ok a0 =>
        rw [hwa] at h
        dsimp only at h
        cases hra : rawNatLit? a0 with
        | none => rw [hra] at h; simp [pure, Except.pure] at h
        | some n₁ =>
        rw [hra] at h
        dsimp only at h
        cases hwb : whnf .verified env fuel d b with
        | error err => rw [hwb] at h; exact nomatch h
        | ok b0 =>
        rw [hwb] at h
        dsimp only at h
        cases hrb : rawNatLit? b0 with
        | none => rw [hrb] at h; simp [pure, Except.pure] at h
        | some n₂ =>
          rw [hrb] at h
          simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [pure, Except.pure] at h
  | .bvar _, h | .fvar _ _, h | .sort _, h | .lam _ _ _, h
  | .forallE _ _ _, h | .letE _ _ _, h | .lit _, h
  | .proj _ _ _, h | .const _ _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _, h | .app (.fvar _ _) _, h
  | .app (.sort _) _, h | .app (.lam _ _ _) _, h
  | .app (.forallE _ _ _) _, h | .app (.letE _ _ _) _, h
  | .app (.lit _) _, h | .app (.proj _ _ _) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _, h | .app (.app (.fvar _ _) _) _, h
  | .app (.app (.sort _) _) _, h | .app (.app (.app _ _) _) _, h
  | .app (.app (.lam _ _ _) _) _, h
  | .app (.app (.forallE _ _ _) _) _, h
  | .app (.app (.letE _ _ _) _) _, h
  | .app (.app (.lit _) _) _, h
  | .app (.app (.proj _ _ _) _) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h

/-- `litMajorToCtor` ⇒ `Red.litToCtorIfNat` or `Red.strLitWhnf`
(`litMajorToCtorFueled_inv`). -/
theorem litMajorToCtor_bridge (hw : WhnfBridge env fuel)
    {d : Nat} {e e₁ : Expr}
    (h : litMajorToCtorFueled .verified env fuel d e = .ok e₁) :
    Red env d e e₁ := by
  rcases litMajorToCtorFueled_inv h with rfl | ⟨s, rfl, hsup, hwh⟩
  · exact .litToCtorIfNat e
  · exact .strLitWhnf hsup (hw hwh)

/-- `projLitToCtor` ⇒ `Red.refl` or `Red.strLitWhnf`
(`projLitToCtorFueled_inv`). -/
theorem projLitToCtor_bridge (hw : WhnfBridge env fuel)
    {d : Nat} {e e₁ : Expr}
    (h : projLitToCtorFueled .verified env fuel d e = .ok e₁) :
    Red env d e e₁ := by
  rcases projLitToCtorFueled_inv h with rfl | ⟨s, rfl, hsup, hwh⟩
  · exact .refl
  · exact .strLitWhnf hsup (hw hwh)

/-- `projCertAt` at `.verified` ⇒ the constructor's stored type and a
licensed `Certs` walk (`projCertAtFueled_verified`, `projCert_inv`,
`iotaCerts_bridge`). -/
theorem projCertAt_bridge (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {c : Name} {us : List Level} {args : List Expr}
    (h : projCertAtFueled .verified env fuel d true true c us args = .ok true) :
    ∃ cvC nP nF, env.find? c = some (.ctorInfo cvC nP nF) ∧
      Certs env d true (cvC.type.instantiateLevelParams cvC.levelParams us) args := by
  obtain ⟨cvC, nP, nF, hc, hcerts⟩ :=
    projCert_inv (projCertAtFueled_verified (mode := .verified) rfl h)
  exact ⟨cvC, nP, nF, hc, iotaCerts_bridge hd hio hcerts⟩

/-- `majorToCtor` ⇒ `Red.refl` or one of the three rescues
(`majorToCtor_inv`; the rescue's proof-irrelevance / structure-η
certificate becomes the `DefEq fab major` premise through
`proofIrrel_bridge` / `structEtaCertWith_bridge`). -/
theorem majorToCtor_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {recName : Name} {rules : List RecRule} {major major' : Expr}
    (h : majorToCtorFueled .verified env fuel d recName rules major = .ok major') :
    Red env d major major' := by
  sorry

/-- `prepareMajor` ⇒ a `Red` chain (`prepareMajorFueled_ind` with the
motive `Red env d a ·`: each of the three steps is a `Red.trans`). -/
theorem prepareMajor_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {recName : Name} {rules : List RecRule} {a m : Expr}
    (h : prepareMajorFueled .verified env fuel d recName rules a = .ok m) :
    Red env d a m :=
  prepareMajorFueled_ind h (Red env d a)
    (fun hwh hp => .trans hp (hw hwh))
    (fun hl hp => .trans hp (litMajorToCtor_bridge hw hl))
    (fun hm hp => .trans hp (majorToCtor_bridge hw hd hio hm))
    .refl

/-- `iotaRec` ⇒ `Red.iota` (`iotaRec_inv`, `prepareMajor_bridge`,
`defEqList_bridge`, `iotaCerts_bridge` twice, `iotaIndexOk_inv`). -/
theorem iotaRec_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {e e'' : Expr}
    (h : iotaRecFueled .verified env fuel d e = .ok (some e'')) :
    Red env d e e'' := by
  sorry

/-- **`whnfCore` at `fuel + 1`**: the eleven shapes (`whnf_app_inv`,
`whnf_proj_inv`, the six leaves, `whnfCore_letE_inv`, the `.bvar`
throw). -/
theorem whnfCore_bridge_succ (hwc : WhnfCoreBridge env fuel)
    (hw : WhnfBridge env fuel) (hd : DefEqBridge env fuel)
    (hio : InferIOBridge env fuel) :
    WhnfCoreBridge env (fuel + 1) := by
  sorry

/-- One `whnfStep` under a bridged continuation is a `Red` chain
(`whnfStep_inv`: `whnfCore`, then acceleration or δ into `k`, or the
fixpoint). -/
theorem whnfStep_bridge (hwc : WhnfCoreBridge env fuel) (hw : WhnfBridge env fuel)
    {d : Nat} {k : Expr → CheckM Expr}
    (hk : ∀ {e e' : Expr}, k e = .ok e' → Red env d e e')
    {e e' : Expr}
    (h : whnfStep (pureFns .verified env fuel) env d k e = .ok e') :
    Red env d e e' := by
  obtain ⟨e₁, hwc₁, hrest⟩ := whnfStep_inv h
  have h₁ : Red env d e e₁ := hwc hwc₁
  rcases hrest with ⟨e₂, hnat, hk₂⟩ | ⟨-, e₂, hδ, hk₂⟩ | ⟨-, -, rfl⟩
  · exact .trans h₁ (.trans (reduceNat_bridge hw hnat) (hk hk₂))
  · exact .trans h₁ (.trans (.delta hδ) (hk hk₂))
  · exact h₁

/-- The loop at every budget. -/
theorem whnfLoop_bridge (hwc : WhnfCoreBridge env fuel) (hw : WhnfBridge env fuel)
    {d : Nat} : ∀ (n : Nat) {e e' : Expr},
      whnfLoop (pureFns .verified env fuel) env d n e = .ok e' →
      Red env d e e'
  | 0, _, _, h => by
    simp [whnfLoop, throw, throwThe, MonadExceptOf.throw] at h
  | n + 1, _, _, h => whnfStep_bridge hwc hw (whnfLoop_bridge hwc hw n) h

/-- **`whnf` at `fuel + 1`**: the loop at its budget. -/
theorem whnf_bridge_succ (hwc : WhnfCoreBridge env fuel) (hw : WhnfBridge env fuel) :
    WhnfBridge env (fuel + 1) := by
  intro d e e' h
  rw [whnf_succ] at h
  exact whnfLoop_bridge hwc hw _ h

end ConLeche.Rules
