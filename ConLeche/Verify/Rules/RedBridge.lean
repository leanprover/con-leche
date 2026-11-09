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

Inversions: `whnf_app_inv` (the `.app` clause: β, ι,
stuck), `whnf_proj_inv` (the `.proj` clause), `whnfCore_letE_inv`, `whnfStep_inv`,
`whnfLoopFuel_succ`, `reduceNat`'s branches (no inversion lemma:
split inline), `litMajorToCtorFueled_inv`, `projLitToCtorFueled_inv`,
`projCertAt_verified_inv`, `majorToCtor_inv`,
`prepareMajorFueled_ind`, `iotaRec_inv`, `iotaIndexOk_inv`.
-/

namespace ConLeche.Rules

variable {μ : CheckMode} {eager : Bool} {env : Env} {fuel : Nat}

/-- `reduceNat` ⇒ `Red.natSucc` / `Red.natOp` (the two accelerated
shapes; the WF-names safety net throws or answers `none`). -/
theorem reduceNat_bridge (hw : WhnfBridge μ eager env fuel)
    {d : Nat} {e e₂ : Expr}
    (h : reduceNatFueled μ eager env fuel d e = .ok (some e₂)) :
    Red env d e e₂ := by
  match e, h with
  | .app (.const c []) a, h =>
    simp only [reduceNatFueled, reduceNat, Bind.bind, Except.bind, whnf_def] at h
    split at h
    · next hcond =>
      obtain ⟨rfl, hnat⟩ := hcond
      cases hwa : whnf μ eager env fuel d a with
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
    · next hnames =>
      have hmem : c ∈ natBinOpNames := by
        rcases hnames with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      cases hwa : whnf μ eager env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hra : rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n₁ =>
      rw [hra] at h
      dsimp only at h
      cases hwb : whnf μ eager env fuel d b with
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
          exact .natOp hmem (hw hwa) hra (hw hwb) hrb hres
    · split at h
      · cases hwa : whnf μ eager env fuel d a with
        | error err => rw [hwa] at h; exact nomatch h
        | ok a0 =>
        rw [hwa] at h
        dsimp only at h
        cases hra : rawNatLit? a0 with
        | none => rw [hra] at h; simp [pure, Except.pure] at h
        | some n₁ =>
        rw [hra] at h
        dsimp only at h
        cases hwb : whnf μ eager env fuel d b with
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
  | .bvar _, h | .fvar _ _, h | .sort _, h | .lam _ _, h
  | .forallE _ _, h | .letE _ _ _, h | .lit _, h
  | .proj _ _ _, h | .const _ _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _, h | .app (.fvar _ _) _, h
  | .app (.sort _) _, h | .app (.lam _ _) _, h
  | .app (.forallE _ _) _, h | .app (.letE _ _ _) _, h
  | .app (.lit _) _, h | .app (.proj _ _ _) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _, h | .app (.app (.fvar _ _) _) _, h
  | .app (.app (.sort _) _) _, h | .app (.app (.app _ _) _) _, h
  | .app (.app (.lam _ _) _) _, h
  | .app (.app (.forallE _ _) _) _, h
  | .app (.app (.letE _ _ _) _) _, h
  | .app (.app (.lit _) _) _, h
  | .app (.app (.proj _ _ _) _) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h

/-- `litMajorToCtor` ⇒ `Red.litToCtorIfNat` or `Red.strLitWhnf`
(`litMajorToCtorFueled_inv`). -/
theorem litMajorToCtor_bridge (hw : WhnfBridge μ eager env fuel)
    {d : Nat} {e e₁ : Expr}
    (h : litMajorToCtorFueled μ eager env fuel d e = .ok e₁) :
    Red env d e e₁ := by
  rcases litMajorToCtorFueled_inv h with rfl | ⟨s, rfl, hsup, hwh⟩
  · exact .litToCtorIfNat e
  · exact .strLitWhnf hsup (hw hwh)

/-- `projLitToCtor` ⇒ `Red.refl` or `Red.strLitWhnf`
(`projLitToCtorFueled_inv`). -/
theorem projLitToCtor_bridge (hw : WhnfBridge μ eager env fuel)
    {d : Nat} {e e₁ : Expr}
    (h : projLitToCtorFueled μ eager env fuel d e = .ok e₁) :
    Red env d e e₁ := by
  rcases projLitToCtorFueled_inv h with rfl | ⟨s, rfl, hsup, hwh⟩
  · exact .refl
  · exact .strLitWhnf hsup (hw hwh)

/-- `majorToCtor` ⇒ `Red.refl` or one of the three rescues
(`majorToCtor_inv`; the K and `And` rescues' proof-irrelevance
certificate becomes the `DefEq fab major` premise through
`proofIrrel_bridge`).

**`hrec`**: the three `Red.rescue*` rules open with `env.find? recName
= some (.recInfo cv mI rP isK [rl])` — the rule bit `isK` is
honest only at a stored recursor, which is what the soundness lane
reads them from.  `majorToCtor` itself ignores its `_recName` argument
(`Core.lean:556`), so the inversion cannot supply the fact and the
caller must: `iotaRec_inv` hands it over at the one site that runs the
chain (through `prepareMajor_bridge`, which passes it through). -/
theorem majorToCtor_bridge (hw : WhnfBridge .verified eager env fuel)
    (hd : DefEqBridge .verified eager env fuel) (hio : InferIOBridge .verified eager env fuel)
    {d : Nat} {recName : Name} {isK : Bool} {rules : List RecRule} {major major' : Expr}
    (hrec : ∃ cv mI rP, env.find? recName = some (.recInfo cv mI rP isK rules))
    (h : majorToCtorFueled .verified eager env fuel d recName isK rules major = .ok major') :
    Red env d major major' := by
  obtain ⟨cv, mI, rP, hfr⟩ := hrec
  rcases majorToCtor_inv h with rfl | ⟨hsc1, hsc2, hsc3, rl, cvj, cnP, cnF,
    tmaj₀, tmaj, T, us₀, ust, cvT, caps, rfl, hfj, hpi, hfT, hinf, hwh, hfn, harm⟩
  · exact .refl
  rcases harm with ⟨hk, hlps, hle, rfl, ⟨tf, htf, hdq⟩, hpirr⟩ |
    ⟨tbl, heta, hlen, hlps, rfl⟩ |
    ⟨rfl, hlen, hlps, hslots, rfl, ⟨tf, htf, hdq⟩, hpirr⟩
  · -- the major's half of the `proofIrrel (fab, major)` run: a proof
    obtain ⟨-, -, -, tb, stb, vT, -, -, -, -, htb, hstb, hwstb, hvT⟩ :=
      proofIrrel_inv (hpirr rfl)
    exact .rescueK hfr hk hfj hpi hfT (inferTypeIO_bridge hio hinf) (hw hwh) hfn
      hlps hle rfl hsc1 hsc2 hsc3
      (inferTypeIO_bridge hio htf) (hd hdq) (inferTypeIO_bridge hio htb)
      (inferTypeIO_bridge hio hstb) (hw hwstb) hvT
  · exact .rescueEta hfr hfj hpi hfT heta (inferTypeIO_bridge hio hinf) (hw hwh)
      hfn hlen hlps rfl hsc1 hsc2 hsc3
  · obtain ⟨-, -, -, tb, stb, vT, -, -, -, -, htb, hstb, hwstb, hvT⟩ :=
      proofIrrel_inv (hpirr rfl)
    exact .rescueAnd hfr hfj hpi hfT (inferTypeIO_bridge hio hinf) (hw hwh) hfn
      hlen hlps hslots rfl hsc1 hsc2 hsc3
      (inferTypeIO_bridge hio htf) (hd hdq) (inferTypeIO_bridge hio htb)
      (inferTypeIO_bridge hio hstb) (hw hwstb) hvT

/-- `prepareMajor` ⇒ a `Red` chain (`prepareMajorFueled_ind` with the
motive `Red env d a ·`: each of the three steps is a `Red.trans`).
`hrec` is `majorToCtor_bridge`'s, passed through. -/
theorem prepareMajor_bridge (hw : WhnfBridge .verified eager env fuel)
    (hd : DefEqBridge .verified eager env fuel) (hio : InferIOBridge .verified eager env fuel)
    {d : Nat} {recName : Name} {isK : Bool} {rules : List RecRule} {a m : Expr}
    (hrec : ∃ cv mI rP, env.find? recName = some (.recInfo cv mI rP isK rules))
    (h : prepareMajorFueled .verified eager env fuel d recName isK rules a = .ok m) :
    Red env d a m :=
  prepareMajorFueled_ind h (Red env d a)
    (fun hwh hp => .trans hp (hw hwh))
    (fun hl hp => .trans hp (litMajorToCtor_bridge hw hl))
    (fun hm hp => .trans hp (majorToCtor_bridge hw hd hio hrec hm))
    .refl

/-- Level instantiation keeps a telescope's syntactic arity. -/
theorem peelPis_isSome_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (k : Nat) {e : Expr}, (Expr.peelPis k e).isSome = true →
      (Expr.peelPis k (e.instantiateLevelParams ks us)).isSome = true
  | 0, _, _ => rfl
  | k + 1, .forallE _ b, h => by
    simp only [Expr.instantiateLevelParams, Expr.peelPis] at h ⊢
    exact peelPis_isSome_instantiateLevelParams ks us k h
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h
  | _ + 1, .const _ _, h | _ + 1, .app _ _, h | _ + 1, .lam _ _, h
  | _ + 1, .letE _ _ _, h | _ + 1, .lit _, h | _ + 1, .proj _ _ _, h => by
    simp [Expr.peelPis] at h

/-- The walk to a family's sort is `FormerSort`. -/
theorem formerSortLoop_bridge (hw : WhnfBridge .verified eager env fuel) :
    ∀ {n d : Nat} {e : Expr} {s : Level},
      formerSortLoop (pureFns .verified eager env fuel).whnf d n e = .ok (some s) →
      FormerSort env d n e s
  | 0, d, e, s, h => by
    unfold formerSortLoop at h
    cases hr : (pureFns .verified eager env fuel).whnf d e with
    | error err => rw [hr] at h; exact nomatch h
    | ok w =>
      rw [hr] at h
      cases w with
      | sort s' =>
        cases Option.some.inj (Except.ok.inj h)
        exact .sort (hw hr)
      | _ => exact nomatch h
  | n + 1, d, e, s, h => by
    unfold formerSortLoop at h
    cases hr : (pureFns .verified eager env fuel).whnf d e with
    | error err => rw [hr] at h; exact nomatch h
    | ok w =>
      rw [hr] at h
      cases w with
      | forallE dom b => exact .pi (hw hr) (formerSortLoop_bridge hw h)
      | _ => exact nomatch h

/-- A family's sort reached at a use: never zero, by the type's shape or by the
walk. -/
theorem formerNeverZeroAt_bridge (hw : WhnfBridge .verified eager env fuel)
    {cvT : ConstantVal} {caps : IndCaps} {us : List Level}
    (h : formerNeverZeroAt (pureFns .verified eager env fuel).whnf cvT caps us = .ok true) :
    formerNeverZero cvT us = true ∨
      formerResSort cvT.type = none ∧ ∃ s, FormerSort env 0 (caps.nparams + caps.nIdx)
          (cvT.type.instantiateLevelParams cvT.levelParams us) s ∧
        (Level.zeronessOf s).isNever = true := by
  unfold formerNeverZeroAt at h
  split at h
  · exact .inl (Except.ok.inj h)
  · next hnone =>
    cases hr : formerSortLoop (pureFns .verified eager env fuel).whnf 0
        (caps.nparams + caps.nIdx) (cvT.type.instantiateLevelParams cvT.levelParams us) with
    | error err => rw [hr] at h; exact nomatch h
    | ok o =>
      rw [hr] at h
      cases o with
      | none => exact nomatch h
      | some s => exact .inr ⟨hnone, s, formerSortLoop_bridge hw hr, Except.ok.inj h⟩

/-- The ι case split's verdict is `IotaCase`. -/
theorem iotaCase3At_bridge (hw : WhnfBridge .verified eager env fuel)
    {isK : Bool} {cvj : ConstantVal} {us : List Level} {c3 : Bool}
    (h : iotaCase3At (pureFns .verified eager env fuel).whnf env.find? isK cvj us = .ok c3) :
    IotaCase env isK cvj us c3 := by
  cases c3 with
  | true => exact .three
  | false =>
    unfold iotaCase3At at h
    split at h
    · next hk => rw [show isK = true from hk]; exact .k
    · next hk =>
      rw [show isK = false by simpa using hk]
      split at h
      · next cvT caps hfam =>
        split at h
        · next hlen =>
          cases hr : formerNeverZeroAt (pureFns .verified eager env fuel).whnf cvT caps us with
          | error err => rw [hr] at h; exact nomatch h
          | ok nz =>
            rw [hr] at h
            have hnz : nz = true := by
              cases nz with
              | true => rfl
              | false => exact nomatch h
            subst hnz
            have hlen' : cvT.levelParams.length = us.length := by simpa using hlen
            rcases formerNeverZeroAt_bridge hw hr with h' | ⟨hnone, s, hs, hn⟩
            · exact .never hfam hlen' h'
            · exact .walk hfam hlen' hnone hs hn
        · exact nomatch h
      · exact nomatch h

/-- `iotaRec` ⇒ `Red.iota` (`iotaRec_inv`, `prepareMajor_bridge`,
`defEqList_bridge`, the arity-checked recursor spine, and at a case-3 redex
`iotaCertsFull_bridge` and `iotaIndexOk_inv`). -/
theorem iotaRec_bridge (hw : WhnfBridge .verified eager env fuel)
    (hd : DefEqBridge .verified eager env fuel) (hi : InferBridge .verified eager env fuel)
    (hio : InferIOBridge .verified eager env fuel)
    {d : Nat} {e e'' : Expr}
    (h : iotaRecFueled .verified eager env fuel d e = .ok (some e'')) :
    Red env d e e'' := by
  obtain ⟨c, us, cv, mI, rP, isK, rules, major, cj, usj, cvj, cnP, cnF, rl,
    hfn, hfc, hlen, hlvl, hprep, hmfn, hfj, hrule, hml, h3, rfl⟩ := iotaRec_inv h
  have hmaj : Red env d (e.getAppArgs.getD mI (.bvar 0)) major :=
    prepareMajor_bridge hw hd hio ⟨cv, mI, rP, hfc⟩ hprep
  -- the arity-checked recursor spine's arity: the checker's test on the
  -- stored type (task #342 L18)
  have harity : (Expr.peelPis e.getAppArgs.length
      (cv.type.instantiateLevelParams cv.levelParams us)).isSome = true := by
    rw [hlen]
    exact peelPis_isSome_instantiateLevelParams _ _ _ (iotaRec_arity h hfn hfc)
  obtain ⟨c3, hrun, h3⟩ := h3 rfl
  have hcase := iotaCase3At_bridge hw hrun
  cases c3 with
  | true =>
    obtain ⟨hlev, hpeq, hcerts, hidx⟩ := h3 rfl
    by_cases hne : mI = rP
    · exact .iota (residual := .bvar 0) hfn hfc hlen hlvl hmaj hmfn hfj hrule hml hcase
        (fun _ => hlev) (fun _ => defEqList_bridge hd hpeq)
        harity
        (fun _ => iotaCertsFull_bridge hd hi hcerts)
        (fun _ hc => absurd hne hc) (fun _ hc => absurd hne hc)
    · obtain ⟨residual, hres, hdl⟩ := iotaIndexOk_inv hidx hne
      exact .iota hfn hfc hlen hlvl hmaj hmfn hfj hrule hml hcase
        (fun _ => hlev) (fun _ => defEqList_bridge hd hpeq)
        harity
        (fun _ => iotaCertsFull_bridge hd hi hcerts)
        (fun _ _ => hres) (fun _ _ => defEqList_bridge hd hdl)
  | false =>
    exact .iota (residual := .bvar 0) hfn hfc hlen hlvl hmaj hmfn hfj hrule hml hcase
      (fun hc => nomatch hc) (fun hc => nomatch hc)
      harity
      (fun hc => nomatch hc)
      (fun hc => nomatch hc) (fun hc => nomatch hc)

/-- A firing projection rule (`reduceProjCore`) is a `Red` chain: the
string-literal expansion, then `Red.proj` under its certificate. -/
theorem reduceProjCore_bridge (hw : WhnfBridge .verified eager env fuel)
    {d : Nat} {sn : Name} {i : Nat} {c m : Expr}
    (h : reduceProjCoreFueled .verified eager env fuel d sn i c = .ok (some m)) :
    Red env d (.proj sn i c) m := by
  obtain ⟨e₃, us, entry, hlit, hfn, hfp, hi, hlen, hus, rfl, hcert⟩ :=
    reduceProjCore_inv h
  obtain ⟨cvC, nP, nF, hc, harity⟩ := projCertAt_verified_inv hcert
  exact .trans (.projArg (projLitToCtor_bridge hw hlit))
    (.proj hfp hfn hi hlen hus hc
      (peelPis_isSome_instantiateLevelParams _ _ _ harity))

/-- **`whnfCore` at `fuel + 1`**: the eleven shapes (`whnf_app_inv`,
`whnf_proj_inv`, the six leaves, `whnfCore_letE_inv`, the `.bvar`
throw). -/
theorem whnfCore_bridge_succ (hwc : WhnfCoreBridge .verified eager env fuel)
    (hw : WhnfBridge .verified eager env fuel) (hd : DefEqBridge .verified eager env fuel)
    (hi : InferBridge .verified eager env fuel) (hio : InferIOBridge .verified eager env fuel) :
    WhnfCoreBridge .verified eager env (fuel + 1) := by
  intro c d e e' h
  match e, h with
  | .sort _, h | .fvar _ _, h | .forallE _ _, h | .lam _ _, h
  | .const _ _, h | .lit _, h =>
    cases Except.ok.inj h; exact .refl
  | .bvar _, h =>
    rw [whnfCore_succ] at h
    simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
  | .letE _ _ _, h => exact .trans .zeta (hwc (whnfCore_letE_inv h))
  | .app f a, h =>
    obtain ⟨f', hf, hcase⟩ := whnf_app_inv h
    have hRf : Red env d (.app f a) (.app f' a) := .appFn (hwc hf)
    rcases hcase with ⟨ty, body, rfl, hbody⟩ | ⟨e'', hiota, hcont⟩ | rfl
    · refine .trans hRf (.trans ?_ (hwc hbody))
      exact .beta
    · exact .trans hRf (.trans (iotaRec_bridge hw hd hi hio hiota) (hwc hcont))
    · exact hRf
  | .proj sn i pe, h =>
    obtain ⟨e₂, hst, hcase⟩ := whnf_proj_inv h
    have hR : Red env d (.proj sn i pe) (.proj sn i e₂) := by
      rcases hst with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact .projArg (hwc h2)
      · exact .projArg (hw h2)
    rcases hcase with rfl | ⟨m, hr, hcont⟩
    · exact .refl
    · exact .trans hR (.trans (reduceProjCore_bridge hw hr) (hwc hcont))

/-- One `whnfStep` under a bridged continuation is a `Red` chain
(`whnfStep_inv`: `whnfCore`, then acceleration or δ into `k`, or the
fixpoint). -/
theorem whnfStep_bridge (hwc : WhnfCoreBridge μ eager env fuel) (hw : WhnfBridge μ eager env fuel)
    {d : Nat} {k : Expr → CheckM Expr}
    (hk : ∀ {e e' : Expr}, k e = .ok e' → Red env d e e')
    {e e' : Expr}
    (h : whnfStep (pureFns μ eager env fuel) env d k e = .ok e') :
    Red env d e e' := by
  obtain ⟨e₁, hwc₁, hrest⟩ := whnfStep_inv h
  have h₁ : Red env d e e₁ := hwc hwc₁
  rcases hrest with ⟨e₂, hnat, hk₂⟩ | ⟨-, e₂, hδ, hk₂⟩ | ⟨-, -, rfl⟩
  · exact .trans h₁ (.trans (reduceNat_bridge hw hnat) (hk hk₂))
  · exact .trans h₁ (.trans (.delta hδ) (hk hk₂))
  · exact h₁

/-- The loop at every budget. -/
theorem whnfLoop_bridge (hwc : WhnfCoreBridge μ eager env fuel) (hw : WhnfBridge μ eager env fuel)
    {d : Nat} : ∀ (n : Nat) {e e' : Expr},
      whnfLoop (pureFns μ eager env fuel) env d n e = .ok e' →
      Red env d e e'
  | 0, _, _, h => by
    simp [whnfLoop, throw, throwThe, MonadExceptOf.throw] at h
  | n + 1, _, _, h => whnfStep_bridge hwc hw (whnfLoop_bridge hwc hw n) h

/-- **`whnf` at `fuel + 1`**: the loop at its budget. -/
theorem whnf_bridge_succ (hwc : WhnfCoreBridge μ eager env fuel) (hw : WhnfBridge μ eager env fuel)
    :
    WhnfBridge μ eager env (fuel + 1) := by
  intro d e e' h
  rw [whnf_succ] at h
  exact whnfLoop_bridge hwc hw _ h

end ConLeche.Rules
