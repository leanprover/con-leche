module

public import ConLeche.Verify.Cached.BridgeCSDecl
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Inductives.FixRec
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Cached.WalkersC
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Inductives.SumInv
import ConLeche.Verify.Inductives.SumWF
import ConLeche.Verify.Cached.NestPosC

public section

/-!
# The cached uniform install at k members, bridged (lane FLIP1)

`checkBlockKS` (`ConLeche/Cached/CheckerC.lean`), the cached mirror of
the uniform installer at any number of members, is reproduced by the
pure fueled `checkBlock`.  This file holds the pass (`checkBlockPassS_run`),
the stages' simulations and the `SimG` kit; the recursor stage — the
target check — its install and the `.indDecl` dispatch
(`checkBlockTailS_run`, `checkBlockKS_run`, `checkModeledOrNativeSF_run`)
are in `ConLeche/Verify/Cached/TargetRecC.lean` (lane RECLIB, B1).  The
old stage's simulation (§4, `checkBlockRecKS_run`) is no longer on the
fold's path.

The file follows `BridgeCSDecl.lean`'s layout:

1. the index mirrors at `mkFEnv` ARE the pure stages (`*_eqC`);
2. the scoping facts every cached operation's simulation needs
   (`SimC`, `ConLeche/Verify/Cached/SimC.lean`, is stated at well-scoped
   inputs) — the rule stage's residue is the one that needs work: it is
   built by the primitive-recursion abstraction, which is fvar-free by
   construction (`abstractIh_hasFvar`, `blockIhPis_hasFvar`);
3. the single-environment stages as `SimC`s;
4. the rule stage, whose one rule alternates between the rule-less
   recursors' environment and the constructors' (`sharedOpsRuleR`'s
   flushes are what make that a chain of `SimC`s);
5. the assembly, and the dispatch.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## 1. The index mirrors at `mkFEnv` are the pure stages -/

section Mirrors

variable (ops : CheckerOps CheckCM)

theorem checkBlockTeleF_eqC (env : Env) (nP : Nat) (ms : MemberShape) :
    checkBlockTeleF ops (mkFEnv env) nP ms = checkBlockTele ops env nP ms := by
  unfold checkBlockTeleF checkBlockTele
  simp only [checkConstantValF_eq, checkSumTeleF_pushC]

theorem checkBlockTelesF_eqC (env : Env) (nP : Nat) :
    ∀ mss : List MemberShape,
      checkBlockTelesF ops (mkFEnv env) nP mss = checkBlockTeles ops env nP mss
  | [] => rfl
  | ms :: rest => by
    simp only [checkBlockTelesF, checkBlockTeles, checkBlockTeleF_eqC,
      checkBlockTelesF_eqC env nP rest]

theorem checkBlockDomsAtF_eqC (env : Env) (off : Nat) (fvs doms : List Expr) :
    ∀ j : Nat, checkBlockDomsAtF ops (mkFEnv env) off fvs doms j
      = checkBlockDomsAt ops env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkBlockDomsAtF, checkBlockDomsAt, mkFEnv_env,
      checkBlockDomsAtF_eqC env off fvs doms j]

theorem checkBlockAgreeF_eqC (env : Env) (nP : Nat) (cvTa0 : ConstantVal) (s0 : Level) :
    ∀ cvs : List (ConstantVal × Level),
      checkBlockAgreeF ops (mkFEnv env) nP cvTa0 s0 cvs
        = checkBlockAgree ops env nP cvTa0 s0 cvs
  | [] => rfl
  | (cvTa, s) :: rest => by
    simp only [checkBlockAgreeF, checkBlockAgree, checkBlockDomsAtF_eqC,
      checkBlockAgreeF_eqC env nP cvTa0 s0 rest]

theorem consBlockIndsF_mkFEnv (p₁ : BlockShape) (isRec : Bool) :
    ∀ (cvTas : List ConstantVal) (i : Nat) (env : Env),
      consBlockIndsF p₁ isRec cvTas i (mkFEnv env) = mkFEnv (consBlockInds p₁ isRec cvTas i env)
  | [], _, _ => rfl
  | cvTa :: rest, i, env => by
    simp only [consBlockIndsF, consBlockInds, push_mkFEnv]
    exact consBlockIndsF_mkFEnv p₁ isRec rest (i + 1) _

theorem checkBlockIndsF_eqC (env : Env) (p : BlockParts) (isRec : Bool) :
    checkBlockIndsF ops (mkFEnv env) p isRec
      = checkBlockInds ops env p isRec >>= fun r => pure (mkFEnv r.1, r.2) := by
  unfold checkBlockIndsF checkBlockInds
  rcases hm : p.members with _ | ⟨ms0, rest⟩
  · rfl
  · simp only [checkBlockTeleF_eqC, checkBlockTelesF_eqC, checkBlockAgreeF_eqC, bind_assoc,
      pure_bind, consBlockIndsF_mkFEnv]

theorem checkBlockCtorsF_eqC (env₀ env : Env) (p : BlockShape) :
    ∀ l : List (MemberShape × ConstantVal),
      checkBlockCtorsF ops (mkFEnv env₀) (mkFEnv env) p l = checkBlockCtors ops env₀ env p l
  | [] => rfl
  | (ms, cvTa) :: rest => by
    simp only [checkBlockCtorsF, checkBlockCtors, checkSumCtorsF_eq,
      checkBlockCtorsF_eqC env₀ env p rest]

theorem checkBlockIdxSortsF_eqC (env : Env) (p : BlockShape) :
    ∀ l : List (MemberShape × ConstantVal),
      checkBlockIdxSortsF ops (mkFEnv env) p l = checkBlockIdxSorts ops env p l
  | [] => rfl
  | (ms, cvTa) :: rest => by
    simp only [checkBlockIdxSortsF, checkBlockIdxSorts, checkStructFieldSortsIF_eq,
      checkBlockIdxSortsF_eqC env p rest]

end Mirrors

theorem consBlockCtorsF_mkFEnv (nP : Nat) :
    ∀ (ctorsAs : List (List (ConstantVal × Nat))) (env : Env),
      consBlockCtorsF nP ctorsAs (mkFEnv env) = mkFEnv (consBlockCtors nP ctorsAs env)
  | [], _ => rfl
  | ctorsA :: rest, env => by
    simp only [consBlockCtorsF, consBlockCtors, consSumCtorsF_mkFEnv]
    exact consBlockCtorsF_mkFEnv nP rest _

theorem consBlockRecsF_mkFEnv (find? : Name → Option ConstantInfo) (p : BlockShape)
    (nP : Nat) :
    ∀ (m : Nat) (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
      (env : Env),
      consBlockRecsF find? p nP m rs (mkFEnv env) = mkFEnv (consBlockRecs find? p nP m rs env)
  | _, [], _ => rfl
  | m, (cvRa, rhss, nIdx, ctorsA) :: rest, env => by
    simp only [consBlockRecsF, consBlockRecs, push_mkFEnv]
    exact consBlockRecsF_mkFEnv find? p nP (m + 1) rest _

theorem blockOpenedOkF_eqC (env₀ : Env) (names lps : List Name) (nP : Nat) (nIdxs : List Nat)
    (cty : Expr) (nF : Nat) (ks : List BlockFieldKind) :
    blockOpenedOkF .plain (mkFEnv env₀) names lps nP nIdxs cty nF ks
      = blockOpenedOk env₀ names lps nP nIdxs cty nF ks := by
  simp only [blockOpenedOkF, blockOpenedOk, StructWalkers.plain, constsResolveF_eq] <;> rfl

theorem blockFieldsOkF_eqC (env₀ : Env) (names lps : List Name) (nP : Nat) (nIdxs : List Nat)
    (ctorsAs : List (List (ConstantVal × Nat))) (kinds : List (List (List BlockFieldKind))) :
    blockFieldsOkF .plain (mkFEnv env₀) names lps nP nIdxs ctorsAs kinds
      = blockFieldsOk env₀ names lps nP nIdxs ctorsAs kinds := by
  simp only [blockFieldsOkF, blockFieldsOk, blockMemberFieldsOkF, blockMemberFieldsOk,
    blockOpenedOkF_eqC] <;> rfl

theorem checkBlockTablesF_eqC (p : BlockShape) :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) (env : Env),
      checkBlockTablesF (m := CheckCM) .plain p l (mkFEnv env)
        = checkBlockTables (m := CheckCM) p l env >>= fun e => pure (mkFEnv e)
  | [], _ => by simp only [checkBlockTablesF, checkBlockTables, pure_bind]
  | (ms, ctorsA, sortss) :: rest, env => by
    unfold checkBlockTablesF checkBlockTables
    split
    · split
      · simp only [checkStructProjTableF_pushC, bind_assoc, pure_bind,
          checkBlockTablesF_eqC p rest]
      · simp only [pure_bind, checkBlockTablesF_eqC p rest]
    · simp only [pure_bind, checkBlockTablesF_eqC p rest]

/-! ## 2. Scoping

Every cached operation's simulation is stated at a well-scoped input
(`WScoped`).  Most of the rule stage's inputs are OPENED telescopes of
checked (fvar-free) constants, and the Verify tier's opening lemmas
cover them; the residue is the exception — it is the primitive-
recursion abstraction of the rule body, wrapped in a GENERATED `ih`
telescope — and the two facts it needs are here: the abstraction never
produces a free variable (`abstractIh_hasFvar`), and neither does the
generated telescope over fvar-free pieces (`blockIhPis_ws0`).
"fvar-free" is stated as `WScoped 0`, which is the same thing
(`ws0_iff`) and composes with the opening lemmas. -/

theorem ws0_hasFvar {e : Expr} (h : WScoped 0 e) : e.hasFvar = false :=
  not_hasFvar_of_fvarsBelow_zero (WScoped.fvarsBelow h)

theorem ws_of_ws0 {d : Nat} {e : Expr} (h : WScoped 0 e) : WScoped d e :=
  WScoped.of_not_hasFvar (ws0_hasFvar h)

theorem WScoped.liftLooseBVars' {d n : Nat} :
    ∀ {e : Expr} {c : Nat}, WScoped d e → WScoped d (e.liftLooseBVars n c) := by
  intro e
  induction e with
  | bvar i => intro c _; simp only [Expr.liftLooseBVars]; split <;> simp [WScoped]
  | fvar idx ty _ => intro c hw; simpa [Expr.liftLooseBVars] using hw
  | app f a ihf iha =>
    intro c hw
    simp only [WScoped] at hw
    simp only [Expr.liftLooseBVars, WScoped]
    exact ⟨ihf hw.1, iha hw.2⟩
  | lam ty b bi ih1 ih2 =>
    intro c hw
    simp only [WScoped] at hw
    simp only [Expr.liftLooseBVars, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2⟩
  | forallE ty b bi ih1 ih2 =>
    intro c hw
    simp only [WScoped] at hw
    simp only [Expr.liftLooseBVars, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2⟩
  | letE ty v b ih1 ih2 ih3 =>
    intro c hw
    simp only [WScoped] at hw
    simp only [Expr.liftLooseBVars, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2.1, ih3 hw.2.2⟩
  | proj s i e ih =>
    intro c hw
    simp only [WScoped] at hw
    simp only [Expr.liftLooseBVars, WScoped]
    exact ih hw
  | _ => intro c _; simp [Expr.liftLooseBVars, WScoped]

theorem WScoped.instantiate1Lift' {d : Nat} {v : Expr} (hv : WScoped d v) :
    ∀ {e : Expr} {k : Nat}, WScoped d e → WScoped d (e.instantiate1Lift v k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1Lift]
    split
    · exact WScoped.liftLooseBVars' hv
    · split <;> simp [WScoped]
  | fvar idx ty _ => intro k hw; simpa [Expr.instantiate1Lift] using hw
  | app f a ihf iha =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1Lift, WScoped]
    exact ⟨ihf hw.1, iha hw.2⟩
  | lam ty b bi ih1 ih2 =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1Lift, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2⟩
  | forallE ty b bi ih1 ih2 =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1Lift, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2⟩
  | letE ty v' b ih1 ih2 ih3 =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1Lift, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2.1, ih3 hw.2.2⟩
  | proj s i e ih =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1Lift, WScoped]
    exact ih hw
  | _ => intro k _; simp [Expr.instantiate1Lift, WScoped]

theorem instPisAtLift_WScoped {d : Nat} :
    ∀ {as : List Expr} {t r : Expr}, Expr.instPisAtLift as t = some r → WScoped d t →
      (∀ a ∈ as, WScoped d a) → WScoped d r
  | [], t, r, h, ht, _ => by
    simp only [Expr.instPisAtLift, Option.some.injEq] at h
    exact h ▸ ht
  | a :: as, t, r, h, ht, ha => by
    cases t with
    | forallE dom body bi =>
      simp only [Expr.instPisAtLift] at h
      simp only [WScoped] at ht
      exact instPisAtLift_WScoped h (WScoped.instantiate1Lift' (ha a List.mem_cons_self) ht.2)
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
    | _ => simp [Expr.instPisAtLift] at h

theorem mkPisOf_WScoped {d : Nat} :
    ∀ {bs : List (Expr × BinderMeta)} {body : Expr}, (∀ b ∈ bs, WScoped d b.1) →
      WScoped d body → WScoped d (Expr.mkPisOf bs body)
  | [], _, _, hb => hb
  | (ty, mt) :: bs, body, hbs, hb => by
    simp only [Expr.mkPisOf, WScoped]
    exact ⟨hbs _ List.mem_cons_self,
      mkPisOf_WScoped (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb⟩

theorem structTeleVars_WScoped {d m : Nat} : ∀ x ∈ structTeleVars m, WScoped d x := by
  intro x hx
  simp only [structTeleVars, List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  simp [WScoped]

/-- `instantiateList` at well-scoped values keeps a scoped term scoped. -/
theorem instantiateList_WScoped {d : Nat} {vs : List Expr} {e : Expr}
    (hvs : ∀ v ∈ vs, WScoped d v) (he : WScoped d e) : WScoped d (e.instantiateList vs 0) := by
  by_cases hne : vs = []
  · subst hne; rw [Expr.instantiateList_nil]; exact he
  · rw [instantiateList_eq_instSeq hne]
    exact Expr.instSeq_WScoped _ _ (fun a ha => hvs a (List.mem_reverse.mp ha)) he

/-- An opened telescope's variables carry types scoped at their own
frame. -/
theorem openers_typeD_WScoped {n off : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e off = some (fvs, body)) (he : WScoped off e) :
    ∀ (i : Nat) (x : Expr), fvs[i]? = some x → WScoped (off + i) x.fvarTypeD := by
  intro i x hx
  obtain ⟨ty, rfl⟩ := openPisAtFvars_index n e off h i x hx
  have hw := (openPisAtFvars_WScoped n e off h he).1 _ (List.mem_of_getElem? hx)
  simp only [WScoped] at hw
  exact hw.2

/-- The same, read at a common frame. -/
theorem openers_typeD_WScoped' {n off d : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e off = some (fvs, body)) (he : WScoped off e) (hd : off + n ≤ d) :
    ∀ x ∈ fvs, WScoped d x.fvarTypeD := by
  intro x hx
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  have hil : i < fvs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlen : fvs.length = n := ConLeche.Verify.openPisAtFvars_length n h
  exact (openers_typeD_WScoped h he i x hi).mono (by omega)

/-! ## 3. The single-environment stages, simulated -/

section Sims

variable {env : Env}

theorem checkBlockTeleS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {nP : Nat}
    {ms : MemberShape} {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 (Prod.fst v).type)
      (checkBlockTele (sharedOpsC mode (mkFEnv env)) env nP ms)
      (checkBlockTele (fueledOpsM mode) env nP ms) := by
  unfold checkBlockTele
  refine SimC.bind (checkConstantValS_sim hμ henv hs) (fun s₁ c c' hs₁ hP => ?_)
  obtain ⟨rfl, hw⟩ := hP
  refine SimC.bind (checkSumTeleS_sim hμ henv hs₁ hw) (fun s₂ r r' hs₂ hR => ?_)
  obtain ⟨rfl, hw'⟩ := hR
  obtain ⟨cvTa, sx⟩ := r
  dsimp only
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ q q' hs₃ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨tbs, tbody⟩ := q
  dsimp only
  by_cases h1 : (tbody == Expr.sort sx) = true
  case neg => simp only [h1]; exact SimC.throw_bind
  simp only [h1, if_true]
  exact SimC.pure hs₃ ⟨rfl, hw'⟩

theorem checkBlockTelesS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {nP : Nat} :
    ∀ {mss : List MemberShape} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ r ∈ v, WScoped 0 (Prod.fst r).type)
        (checkBlockTeles (sharedOpsC mode (mkFEnv env)) env nP mss)
        (checkBlockTeles (fueledOpsM mode) env nP mss)
  | [], s₀, hs => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | ms :: rest, s₀, hs => by
    unfold checkBlockTeles
    refine SimC.bind (checkBlockTeleS_sim hμ henv hs) (fun s₁ r r' hs₁ hP => ?_)
    obtain ⟨rfl, hw⟩ := hP
    refine SimC.bind (checkBlockTelesS_sim hμ henv hs₁) (fun s₂ rs rs' hs₂ hR => ?_)
    obtain ⟨rfl, hws⟩ := hR
    refine SimC.pure hs₂ ⟨rfl, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hw
    · exact hws x hx

theorem checkBlockDomsAtS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {off : Nat}
    {fvs doms : List Expr}
    (hc : ∀ (i : Nat) (x : Expr), fvs[i]? = some x → WScoped (off + i) (Expr.fvarTypeD x))
    (ht : ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (off + i) x) :
    ∀ {j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockDomsAt (sharedOpsC mode (mkFEnv env)) env off fvs doms j)
        (checkBlockDomsAt (fueledOpsM mode) env off fvs doms j)
  | 0, s₀, hs => SimC.pure hs rfl
  | j + 1, s₀, hs => by
    unfold checkBlockDomsAt
    dsimp only [sharedOpsC]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ a a' hs₁ hP => ?_)
    obtain ⟨rfl, hae⟩ := hP
    refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ b b' hs₂ hQ => ?_)
    obtain ⟨rfl, hbe⟩ := hQ
    refine SimC.bind (opB_sim hμ henv hs₂ (hc j a hae) (ht j b hbe))
      (fun s₃ c c' hs₃ hC => ?_)
    obtain rfl : c = c' := hC
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkBlockDomsAtS_sim hμ henv hc ht hs₃

theorem checkBlockAgreeS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {nP : Nat}
    {cvTa0 : ConstantVal} {s0 : Level} (h0 : WScoped 0 cvTa0.type) :
    ∀ {cvs : List (ConstantVal × Level)} {s₀ : CState},
      (∀ r ∈ cvs, WScoped 0 r.1.type) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockAgree (sharedOpsC mode (mkFEnv env)) env nP cvTa0 s0 cvs)
        (checkBlockAgree (fueledOpsM mode) env nP cvTa0 s0 cvs)
  | [], s₀, _, hs => SimC.pure hs rfl
  | (cvTa, s) :: rest, s₀, hcvs, hs => by
    unfold checkBlockAgree
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ tq0 tq0' hs₁ hP => ?_)
    obtain ⟨rfl, htq0⟩ := hP
    refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ tq tq' hs₂ hQ => ?_)
    obtain ⟨rfl, htq⟩ := hQ
    have hw : WScoped 0 cvTa.type := hcvs _ List.mem_cons_self
    by_cases hl : (tq.1.length == tq0.1.length) = true
    case neg => simp only [hl]; exact SimC.throw_bind
    simp only [hl, if_true]
    refine SimC.bind (checkBlockDomsAtS_sim hμ henv ?_ ?_ hs₂) (fun s₄ _ _ hs₄ _ => ?_)
    · intro i x hx
      exact openers_typeD_WScoped htq hw i x hx
    · intro i x hx
      rw [List.getElem?_map] at hx
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
      exact openers_typeD_WScoped htq0 h0 i y hy
    by_cases he : (Level.isEquiv s s0 == some true) = true
    case neg => simp only [he]; exact SimC.throw_bind
    simp only [he, if_true]
    exact checkBlockAgreeS_sim hμ henv h0 (fun r hr => hcvs r (List.mem_cons_of_mem _ hr)) hs₄

theorem checkBlockIndsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockParts}
    {isRec : Bool} {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ ∀ cv ∈ v.2.1, WScoped 0 cv.type)
      (checkBlockInds (sharedOpsC mode (mkFEnv env)) env p isRec)
      (checkBlockInds (fueledOpsM mode) env p isRec) := by
  unfold checkBlockInds
  split
  · exact SimC.throw
  · refine SimC.bind (checkBlockTeleS_sim hμ henv hs) (fun s₁ r r' hs₁ hP => ?_)
    obtain ⟨rfl, hw0⟩ := hP
    obtain ⟨cvTa0, s0⟩ := r
    dsimp only
    refine SimC.bind (checkBlockTelesS_sim hμ henv hs₁) (fun s₂ cvs cvs' hs₂ hQ => ?_)
    obtain ⟨rfl, hws⟩ := hQ
    refine SimC.bind (checkBlockAgreeS_sim hμ henv hw0 hws hs₂) (fun s₃ _ _ hs₃ _ => ?_)
    refine SimC.pure hs₃ ⟨rfl, ?_⟩
    intro cv hcv
    rcases List.mem_cons.mp hcv with rfl | hcv
    · exact hw0
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hcv
      exact hws r hr

theorem checkBlockCtorsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env₀ : Env}
    {p : BlockShape} :
    ∀ {l : List (MemberShape × ConstantVal)} {s₀ : CState},
      (∀ x ∈ l, x.2.type.hasFvar = false) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockCtors (sharedOpsC mode (mkFEnv env)) env₀ env p l)
        (checkBlockCtors (fueledOpsM mode) env₀ env p l)
  | [], s₀, _, hs => SimC.pure hs rfl
  | (ms, cvTa) :: rest, s₀, hl, hs => by
    unfold checkBlockCtors
    refine SimC.bind (checkSumCtorsS_sim hμ henv (hl _ List.mem_cons_self) hs)
      (fun s₁ q q' hs₁ hP => ?_)
    obtain rfl : q = q' := hP
    obtain ⟨ctorsA, sortss⟩ := q
    dsimp only
    refine SimC.bind (checkBlockCtorsS_sim hμ henv (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      hs₁) (fun s₂ r r' hs₂ hR => ?_)
    obtain rfl : r = r' := hR
    exact SimC.pure hs₂ rfl

theorem checkBlockIdxSortsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} :
    ∀ {l : List (MemberShape × ConstantVal)} {s₀ : CState},
      (∀ x ∈ l, WScoped 0 x.2.type) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockIdxSorts (sharedOpsC mode (mkFEnv env)) env p l)
        (checkBlockIdxSorts (fueledOpsM mode) env p l)
  | [], s₀, _, hs => SimC.pure hs rfl
  | (ms, cvTa) :: rest, s₀, hl, hs => by
    unfold checkBlockIdxSorts
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ tq tq' hs₁ hP => ?_)
    obtain ⟨rfl, htq⟩ := hP
    have hw : WScoped 0 cvTa.type := hl _ List.mem_cons_self
    have hxPos : ∀ (i : Nat) (x : Expr), (tq.1.drop p.nP)[i]? = some x →
        WScoped (p.nP + i) (Expr.fvarTypeD x) := by
      intro i x hx
      rw [List.getElem?_drop] at hx
      have := openers_typeD_WScoped htq hw (p.nP + i) x hx
      simpa using this
    refine SimC.bind (checkStructFieldSortsIS_sim hμ henv hxPos hs₁) (fun s₂ is is' hs₂ hI => ?_)
    obtain rfl : is = is' := hI
    refine SimC.bind (checkBlockIdxSortsS_sim hμ henv (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      hs₂) (fun s₃ r r' hs₃ hR => ?_)
    obtain rfl : r = r' := hR
    exact SimC.pure hs₃ rfl

/-- `checkBlockDefEqList`, at pairwise-scoped inputs: only the pairs
the walk actually compares need to be scoped. -/
theorem checkBlockDefEqListS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {depth : Nat} {what : String} :
    ∀ {as bs : List Expr},
      (∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b →
        WScoped depth a ∧ WScoped depth b) →
      ∀ {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockDefEqList (sharedOpsC mode (mkFEnv env)) env depth what as bs)
        (checkBlockDefEqList (fueledOpsM mode) env depth what as bs)
  | [], [], _, s₀, hs => SimC.pure hs rfl
  | [], _ :: _, _, s₀, hs => SimC.throw
  | _ :: _, [], _, s₀, hs => SimC.throw
  | a :: as, b :: bs, hab, s₀, hs => by
    unfold checkBlockDefEqList
    dsimp only [sharedOpsC]
    obtain ⟨ha, hb⟩ := hab 0 a b rfl rfl
    refine SimC.bind (opB_sim hμ henv hs ha hb) (fun s₁ c c' hs₁ hP => ?_)
    obtain rfl : c = c' := hP
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkBlockDefEqListS_sim hμ henv (fun i a b ha hb => hab (i + 1) a b ha hb) hs₁

end Sims


section Sims3

variable {env : Env}

/-- The member's parameter-and-index telescope at the recursor's own
numbering: the index openers carry types scoped at their own frame,
provided the parameters come first. -/
theorem openPisParamsIdx_typeD_WScoped {nP nIdx rP : Nat} {ty : Expr} {tfvs : List Expr}
    {rest : Expr} (h : openPisParamsIdx nP nIdx rP ty = some (tfvs, rest))
    (hw : WScoped 0 ty) (hle : nP ≤ rP) :
    ∀ (i : Nat) (x : Expr), (tfvs.drop nP)[i]? = some x →
      i < nIdx ∧ WScoped (rP + i) x.fvarTypeD := by
  unfold openPisParamsIdx at h
  split at h
  · exact nomatch h
  · next pfvs body hp =>
    split at h
    · exact nomatch h
    · next ifvs rest' hi =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have hpl : pfvs.length = nP := ConLeche.Verify.openPisAtFvars_length _ hp
      have hil : ifvs.length = nIdx := ConLeche.Verify.openPisAtFvars_length _ hi
      have hbody : WScoped rP body :=
        ((openPisAtFvars_WScoped _ _ 0 hp hw).2).mono (by omega)
      intro i x hx
      rw [List.drop_left' hpl] at hx
      exact ⟨by have := (List.getElem?_eq_some_iff.mp hx).1; omega,
        openers_typeD_WScoped hi hbody i x hx⟩

theorem checkBlockRecPrefixAtS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {rP0 : Nat} {doms0 : List Expr} (hd : ∀ x ∈ doms0, WScoped rP0 x) :
    ∀ {l : List ConstantVal} {ri : Nat} {s₀ : CState},
      (∀ cv ∈ l, WScoped 0 cv.type) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockRecPrefixAt (sharedOpsC mode (mkFEnv env)) env p rP0 doms0 l ri)
        (checkBlockRecPrefixAt (fueledOpsM mode) env p rP0 doms0 l ri)
  | [], _, s₀, _, hs => SimC.pure hs rfl
  | cv :: rest, ri, s₀, hl, hs => by
    unfold checkBlockRecPrefixAt
    by_cases h1 : (p.rulePrefixAt ri == rP0) = true
    case neg => simp only [h1]; exact SimC.throw_bind
    simp only [h1, if_true]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ x x' hs₁ hX => ?_)
    obtain ⟨rfl, hx⟩ := hX
    obtain ⟨fvs, body⟩ := x
    dsimp only
    refine SimC.bind (checkBlockDefEqListS_sim hμ henv ?_ hs₁) (fun s₂ _ _ hs₂ _ => ?_)
    · intro i a b ha hb
      rw [List.getElem?_map] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨hd a (List.mem_of_getElem? ha),
        openers_typeD_WScoped' hx (hl cv List.mem_cons_self) (by omega) b'
          (List.mem_of_getElem? hb')⟩
    exact checkBlockRecPrefixAtS_sim hμ henv hd (fun c hc => hl c (List.mem_cons_of_mem _ hc)) hs₂

theorem checkBlockRecPrefixAgreeS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {cvRs : List ConstantVal} {s₀ : CState}
    (hl : ∀ cv ∈ cvRs, WScoped 0 cv.type) (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkBlockRecPrefixAgree (sharedOpsC mode (mkFEnv env)) env p cvRs)
      (checkBlockRecPrefixAgree (fueledOpsM mode) env p cvRs) := by
  unfold checkBlockRecPrefixAgree
  split
  · exact SimC.pure hs rfl
  · next cv0 rest =>
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ x x' hs₁ hX => ?_)
    obtain ⟨rfl, hx⟩ := hX
    obtain ⟨fvs0, body0⟩ := x
    dsimp only
    refine checkBlockRecPrefixAtS_sim hμ henv ?_ (fun c hc => hl c (List.mem_cons_of_mem _ hc)) hs₁
    intro y hy
    obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hy
    exact openers_typeD_WScoped' hx (hl cv0 List.mem_cons_self) (by omega) x hx'

theorem checkBlockRecSmallElimS_sim {p : BlockShape} {nested : Bool} {us : List Level}
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (checkBlockRecSmallElim (m := CheckCM) p nested us)
      (checkBlockRecSmallElim (m := FueledM) p nested us) := by
  unfold checkBlockRecSmallElim
  by_cases h1 : 0 < p.k
  case neg => simp only [h1]; exact SimC.throw_bind
  simp only [h1, if_true]
  split
  · exact SimC.pure hs rfl
  · exact SimC.throw

theorem checkBlockRecElimPinS_sim {p : BlockShape} {us : List Level} {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (checkBlockRecElimPin (m := CheckCM) p us)
      (checkBlockRecElimPin (m := FueledM) p us) := by
  unfold checkBlockRecElimPin
  split
  · exact SimC.pure hs rfl
  · exact SimC.throw

end Sims3

/-- The kinds' classification is operation-free: in the cached monad
it leaves the state alone and computes what the pure one does. -/
theorem classifyMemberKindsC_ok {names lps : List Name} {nP : Nat} {nIdxs : List Nat}
    {ctorsA : List (ConstantVal × Nat)} {s₀ s' : CState} {kinds : List (List BlockFieldKind)}
    (h : classifyMemberKinds (m := CheckCM) names lps nP nIdxs ctorsA s₀ = .ok (kinds, s')) :
    s' = s₀ ∧ classifyMemberKinds (m := CheckM) names lps nP nIdxs ctorsA = .ok kinds := by
  unfold classifyMemberKinds at h ⊢
  obtain ⟨ks, s₁, hu, h⟩ := bindC_ok h
  cases hk : ctorsA.mapM (blockCtorKinds names lps nP nIdxs) with
  | none => rw [hk] at hu; exact nomatch hu
  | some ks' =>
  rw [hk] at hu
  simp only [unwrapOr] at hu
  obtain ⟨rfl, rfl⟩ := pureC_ok hu
  simp only [unwrapOr, hk]
  try dsimp only at h
  split at h
  · exact absurd h throwC_bind_ok
  · try dsimp only at h
    split at h
    · exact absurd h throwC_bind_ok
    · obtain ⟨rfl, rfl⟩ := pureC_ok h
      simp only [*, bind, Except.bind, ↓reduceIte, pure, Except.pure]
      exact ⟨trivial, rfl⟩

theorem classifyBlockKindsC_ok {names lps : List Name} {nP : Nat} {nIdxs : List Nat} :
    ∀ {l : List (List (ConstantVal × Nat))} {s₀ s' : CState}
      {kinds : List (List (List BlockFieldKind))},
      classifyBlockKinds (m := CheckCM) names lps nP nIdxs l s₀ = .ok (kinds, s') →
      s' = s₀ ∧ classifyBlockKinds (m := CheckM) names lps nP nIdxs l = .ok kinds
  | [], s₀, s', kinds, h => by
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨rfl, rfl⟩
  | ctorsA :: rest, s₀, s', kinds, h => by
    unfold classifyBlockKinds at h
    obtain ⟨kss, s₁, h1, h⟩ := bindC_ok h
    obtain ⟨e1, hk1⟩ := classifyMemberKindsC_ok h1
    obtain ⟨rest', s₂, h2, h⟩ := bindC_ok h
    obtain ⟨e2, hk2⟩ := classifyBlockKindsC_ok h2
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    refine ⟨by rw [e2, e1], ?_⟩
    simp only [classifyBlockKinds, hk1, hk2, bind, Except.bind, pure, Except.pure]

/-! ## 4. The rule stage: two environments, one state

One rule runs its first two operations at the rule-less recursors'
environment and the rest at the constructors'; `sharedOpsRuleR`
flushes entering the first and leaving the second.  `SimG` is `SimC`
with the state invariant at entry and at exit left free, so that a
chain of operations can change environment where a flush lets it. -/

/-- `SimC` across environment transitions: `Pre` of the entry state,
`Post` of the exit state. -/
@[expose] def SimG (Pre Post : CState → Prop) {β α : Type} (P : β → α → Prop) (c : CheckCM β)
    (p : FueledM α) : Prop :=
  ∀ s₀, Pre s₀ → ∀ v' s', c s₀ = .ok (v', s') → Post s' ∧ ∃ v, P v' v ∧ ∃ F, p.val F = .ok v

namespace SimG

variable {A B C : CState → Prop}

theorem ofC {env : Env} {β α : Type} {P : β → α → Prop} {c : CheckCM β} {p : FueledM α}
    (h : ∀ s₀, CSOK mode env s₀ → SimC mode env s₀ P c p) :
    SimG (CSOK mode env) (CSOK mode env) P c p :=
  fun s₀ hs v' s' hr => h s₀ hs v' s' hr

theorem pure {β α : Type} {P : β → α → Prop} {b : β} {a : α} (hAB : ∀ s, A s → B s)
    (h : P b a) : SimG A B P (Pure.pure b) (Pure.pure a) := by
  intro s₀ hs v' s' hr
  simp only [Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hAB _ hs, a, h, 0, rfl⟩

theorem throw_bind {β β' α : Type} {P : β' → α → Prop} {er : CheckError}
    {k : β → CheckCM β'} {p : FueledM α} :
    SimG A B P ((throw er : CheckCM β) >>= k) p := by
  intro s₀ _ v' s' hr
  exact nomatch hr

theorem throw {β α : Type} {P : β → α → Prop} {er : CheckError} {p : FueledM α} :
    SimG A B P (throw er : CheckCM β) p := by
  intro s₀ _ v' s' hr
  exact nomatch hr

theorem bind {β β' α α' : Type} {P : β → α → Prop} {Q : β' → α' → Prop}
    {c : CheckCM β} {k : β → CheckCM β'} {p : FueledM α} {q : α → FueledM α'}
    (hx : SimG A B P c p) (hf : ∀ b a, P b a → SimG B C Q (k b) (q a)) :
    SimG A C Q (c >>= k) (p >>= q) := by
  intro s₀ hs v' s' hr
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e => rw [hc] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, a, hP, F₁, hp₁⟩ := hx s₀ hs b s₁ hc
    obtain ⟨hs', a', hQ, F₂, hp₂⟩ := hf b a hP s₁ hs₁ v' s' hr
    refine ⟨hs', a', hQ, max F₁ F₂, ?_⟩
    rw [FueledM.atF_bind]
    simp only [Bind.bind]
    rw [p.property (Nat.le_max_left F₁ F₂) hp₁]
    dsimp only [Except.bind]
    exact (q a).property (Nat.le_max_right F₁ F₂) hp₂

theorem unwrapOr {α : Type} {o : Option α} {err : CheckError} (hAB : ∀ s, A s → B s) :
    SimG A B (fun v w => v = w ∧ o = some v)
      (ConLeche.unwrapOr o err : CheckCM α) (ConLeche.unwrapOr o err : FueledM α) := by
  cases o with
  | none => exact SimG.throw
  | some a => exact SimG.pure hAB ⟨rfl, rfl⟩

theorem mono {β α : Type} {P : β → α → Prop} {c : CheckCM β} {p : FueledM α}
    {A' B' : CState → Prop} (h : SimG A B P c p) (hA : ∀ s, A' s → A s)
    (hB : ∀ s, B s → B' s) : SimG A' B' P c p :=
  fun s₀ hs v' s' hr =>
    let ⟨h1, h2⟩ := h s₀ (hA s₀ hs) v' s' hr
    ⟨hB s' h1, h2⟩

end SimG

/-- The rule stage's `annotate` at the rule-less recursors'
environment: it flushes first, so it simulates from any residue. -/
theorem ruleR_annotate_simG (hμ : mode.verifiedChecks = true) {envR : Env} (henvR : EnvWF envR)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    SimG CSOKF (CSOK mode envR) (RelW d)
      ((sharedOpsRuleR mode (mkFEnv envR)).annotate envR d e)
      ((fueledOpsM mode).annotate envR d e) := by
  intro s₀ hs v' s' hr
  simp only [sharedOpsRuleR] at hr
  obtain ⟨u, s₁, hfl, hr⟩ := bindC_ok hr
  rw [flushC_run] at hfl
  injection hfl with hfl
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hfl
  exact opE_annotate_sim hμ henvR (flushC_csok hs) hw v' s' hr

/-- The rule stage's `inferType` at the rule-less recursors'
environment: it flushes last, so it hands on a state that is an
invariant state of ANY environment. -/
theorem ruleR_infer_simG (hμ : mode.verifiedChecks = true) {envR : Env} (henvR : EnvWF envR)
    (envT : Env) {d : Nat} {e : Expr} (hw : WScoped d e) :
    SimG (CSOK mode envR) (CSOK mode envT) (RelW d)
      ((sharedOpsRuleR mode (mkFEnv envR)).inferType envR d e)
      ((fueledOpsM mode).inferType envR d e) := by
  intro s₀ hs v' s' hr
  simp only [sharedOpsRuleR] at hr
  obtain ⟨t, s₁, hinf, hr⟩ := bindC_ok hr
  obtain ⟨hs₁, w, hrel, F, hF⟩ := opE_infer_sim hμ henvR hs hw t s₁ hinf
  obtain ⟨u, s₂, hfl, hr⟩ := bindC_ok hr
  rw [flushC_run] at hfl
  injection hfl with hfl
  obtain rfl : s₁.flushed = s₂ := congrArg Prod.snd hfl
  obtain ⟨rfl, rfl⟩ := pureC_ok hr
  exact ⟨flushC_csok hs₁.residue, w, hrel, F, hF⟩

/-! ## 5. The assembly -/

/-- The rule-less recursors' cons is a `consBlockRecs` with no rules. -/
theorem consBlockRecsBare_eq_consBlockRecs (find? : Name → Option ConstantInfo) (q : BlockShape)
    (nP : Nat) :
    ∀ (m : Nat) (cvRas : List (ConstantVal × Nat)) (env : Env),
      consBlockRecsBare q m cvRas env
        = consBlockRecs find? q nP m
            (cvRas.map fun c => (c.1, ([] : List Expr), c.2, ([] : List (ConstantVal × Nat))))
            env
  | _, [], _ => rfl
  | m, (cv, n) :: rest, env => by
    simp only [consBlockRecsBare, consBlockRecs, List.map_cons, sumRules]
    exact consBlockRecsBare_eq_consBlockRecs find? q nP (m + 1) rest _

/-- **The rule-less recursors' environment is well-formed** when their
checked types are. -/
theorem envWF_consBlockRecsBare {q : BlockShape} {cvRas : List (ConstantVal × Nat)} {env : Env}
    (henv : EnvWF env)
    (hall : ∀ c ∈ cvRas, c.1.type.hasFvar = false ∧
      c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
      c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true) :
    EnvWF (consBlockRecsBare q 0 cvRas env) := by
  rw [consBlockRecsBare_eq_consBlockRecs env.find? q 0]
  refine envWF_consBlockRecs henv ?_
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  obtain ⟨h1, h2, h3, h4⟩ := hall c hc
  exact ⟨h1, h2, h3, h4, fun _ h => nomatch h⟩

/-- The projection tables at the cached driver: operation-free, the
state unchanged, the environment the pure stage's. -/
theorem checkBlockTablesS_run (p : BlockShape) :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) (env : Env)
      {s₀ : CState} {fe' : FEnv} {s' : CState}, EnvWF env → CSOKF s₀ →
      checkBlockTablesF (m := CheckCM) .plain p l (mkFEnv env) s₀ = .ok (fe', s') →
      CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
        checkBlockTables (m := CheckM) p l env = .ok fe'.env
  | [], env, s₀, fe', s', henv, hwf, h => by
    simp only [checkBlockTablesF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, rfl⟩
  | (ms, ctorsA, sortss) :: rest, env, s₀, fe', s', henv, hwf, h => by
    match ctorsA, sortss with
    | [cA], [sorts] =>
      simp only [checkBlockTablesF] at h
      by_cases hi : (ms.nIdx == 0) = true
      · rw [if_pos hi] at h
        obtain ⟨fe₁, s₁, h1, h⟩ := bindC_ok h
        obtain ⟨hwf₁, hfe₁, henv₁, F₁, hF₁⟩ := checkStructProjTableS_run env henv hwf h1
        rw [hfe₁] at h
        obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest fe₁.env henv₁ hwf₁ h
        refine ⟨hwf', hfe', henv', ?_⟩
        rw [checkStructProjTable_datF] at hF₁
        simp only [checkBlockTables, if_pos hi, Bind.bind, Except.bind]
        rw [hF₁]
        exact hrest
      · rw [if_neg hi] at h
        simp only [pure_bind] at h
        obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
        refine ⟨hwf', hfe', henv', ?_⟩
        simp only [checkBlockTables, if_neg hi, pure_bind]
        exact hrest
    | [], _ =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩
    | _ :: _ :: _, _ =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩
    | [_], [] =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩
    | [_], _ :: _ :: _ =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩

/-- The constructors' stage stores fvar-free constructor types. -/
theorem checkBlockCtors_types {env₀ env : Env} {q : BlockShape} {F : Nat}
    {l : List (MemberShape × ConstantVal)} {ctorsAs : List (List (ConstantVal × Nat))}
    {sortsss : List (List (List Level))}
    (h : checkBlockCtors (fueledOps mode F) env₀ env q l = .ok (ctorsAs, sortsss)) :
    ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type := by
  obtain ⟨hlen, -, hall⟩ := checkBlockCtors_inv h
  intro ctorsA hcA c hc
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hcA
  have hil : i < l.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨ctorsA', sortss, hcA', -, hcs⟩ := hall i l[i] (List.getElem?_eq_getElem hil)
  obtain rfl := Option.some.inj (hi.symm.trans hcA')
  obtain ⟨hlenC, -, hallc⟩ := checkSumCtors_inv hcs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  have hjl : j < l[i].1.ctors.length := by
    rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨-, sorts, -, hrun⟩ := hallc j (l[i].1.ctors[j]) c (List.getElem?_eq_getElem hjl) hj
  exact WScoped.of_not_hasFvar (direct_sum_ctor_typeWF hrun).1

/-- **One pass at k members, at the cached driver**, is reproduced by
the pure fueled `checkBlockPass`: the formers' environment is the index
over the pure one, the memo state is an invariant state of it, and the
formers' and the constructors' types are fvar-free. -/
theorem checkBlockPassS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {p₀ : BlockParts} {isRec : Bool} {s₀ : CState} (hs : CSOK mode env s₀)
    {q : BlockPass FEnv} {b : Bool} {s' : CState}
    (h : checkBlockPassS mode (mkFEnv env) p₀ isRec s₀ = .ok ((q, b), s')) :
    ∃ env₁ : Env, q.env₁ = mkFEnv env₁ ∧ CSOK mode env₁ s' ∧ EnvWF env₁ ∧
      (∀ cv ∈ q.cvTas, WScoped 0 cv.type) ∧
      (∀ ctorsA ∈ q.ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type) ∧
      EnvWF (consBlockCtors q.p.nP q.ctorsAs env₁) ∧
      ∃ F, (checkBlockPass (fueledOpsM mode) env p₀ isRec).val F
        = .ok (⟨env₁, q.cvTas, q.p, q.ctorsAs, q.sortsss⟩, b) := by
  unfold checkBlockPassS at h
  rw [checkBlockIndsF_eqC] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨r₁, s₁, hind, h⟩ := bindC_ok h
  obtain ⟨hs₁, r₁', hP1, F₁, hF₁⟩ := checkBlockIndsS_sim hμ henv hs r₁ s₁ hind
  obtain ⟨rfl, hwT⟩ := hP1
  obtain ⟨env₁, cvTas, p₁⟩ := r₁
  have hF₁p : checkBlockInds (fueledOps mode F₁) env p₀ isRec = .ok (env₁, cvTas, p₁) := by
    rw [← checkBlockInds_datF]; exact hF₁
  obtain ⟨henv₁, hTf⟩ := direct_block_inds_wf henv hF₁p
  try simp only at h
  obtain ⟨uB, sB, hflB, h⟩ := bindC_ok h
  rw [flushC_run] at hflB
  injection hflB with hflB
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hflB
  rw [checkBlockCtorsF_eqC] at h
  obtain ⟨q2, s₂, hct, h⟩ := bindC_ok h
  have hzT : ∀ x ∈ (p₀.complete p₁).members.zip cvTas, x.2.type.hasFvar = false :=
    fun x hx => hTf x.2 (List.of_mem_zip hx).2
  obtain ⟨hs₂, q2', hP2, F₂, hF₂⟩ :=
    checkBlockCtorsS_sim hμ henv₁ hzT (flushC_csok hs₁.residue) q2 s₂ hct
  obtain rfl : q2 = q2' := hP2
  obtain ⟨ctorsAs, sortsss⟩ := q2
  have hF₂p : checkBlockCtors (fueledOps mode F₂) env₁ env₁ (p₀.complete p₁).toBlockShape
      ((p₀.complete p₁).members.zip cvTas) = .ok (ctorsAs, sortsss) := by
    rw [← checkBlockCtors_datF]; exact hF₂
  try simp only at h
  obtain ⟨kinds, sK, hK, h⟩ := bindC_ok h
  obtain ⟨hsK, hKp⟩ := classifyBlockKindsC_ok hK
  obtain ⟨hq, rfl⟩ := pureC_ok h
  subst hsK
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  refine ⟨env₁, rfl, hs₂, henv₁, hwT, checkBlockCtors_types hF₂p,
    direct_block_ctors_wf henv₁ hF₂p, max F₁ F₂, ?_⟩
  have g₁ : checkBlockInds (fueledOps mode (max F₁ F₂)) env p₀ isRec = .ok (env₁, cvTas, p₁) := by
    rw [← checkBlockInds_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
  have g₂ : checkBlockCtors (fueledOps mode (max F₁ F₂)) env₁ env₁ (p₀.complete p₁).toBlockShape
      ((p₀.complete p₁).members.zip cvTas) = .ok (ctorsAs, sortsss) := by
    rw [← checkBlockCtors_datF]; exact FueledM.up (Nat.le_max_right _ _) hF₂
  rw [checkBlockPass_datF]
  unfold checkBlockPass
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind]
  rw [g₂]
  simp only [Except.bind]
  rw [hKp]

/-- **The reject-only conformance check (lane CONF1) at the cached
driver** is reproduced by the pure fueled one.  It opens with its own
`flushC`, so it starts from any residue: the rule stage before it ends
at the constructors' index (the `feR` half of every rule is closed by
`sharedOpsRuleR`'s trailing flush), and this flush only drops what that
stage cached there — no invariant is carried across it. -/
theorem checkBlockRecConformS_run (hμ : mode.verifiedChecks = true) {env₂ : Env}
    (henv₂ : EnvWF env₂) {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {s₀ : CState} (hwf : CSOKF s₀)
    {u : Unit} {s' : CState}
    (h : (flushC *> checkBlockRecConformF (sharedOpsC mode (mkFEnv env₂)) structWalkersC
      (mkFEnv env₂) none p cvTas ctorsAs) s₀ = .ok (u, s')) :
    CSOKF s' ∧ ∃ F, checkBlockRecConform (fueledOps mode F) env₂ p cvTas ctorsAs = .ok () := by
  simp only [SeqRight.seqRight, bind_pure_comp] at h
  obtain ⟨u0, s₁, hfl, h⟩ := bindC_ok h
  rw [flushC_run] at hfl
  injection hfl with hfl
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hfl
  have hs₁ : CSOK mode env₂ s₀.flushed := flushC_csok hwf
  rw [structWalkersC_eq_plain] at h
  by_cases hone : ∃ ms rc cvTa ctorsA, p.members = [ms] ∧ p.recs = [rc] ∧
      cvTas = [cvTa] ∧ ctorsAs = [ctorsA]
  · obtain ⟨ms, rc, cvTa, ctorsA, hm, hr, hc, hct⟩ := hone
    unfold checkBlockRecConformF at h
    unfold checkBlockRecConform
    simp only [hm, hr, hc, hct] at h ⊢
    by_cases hok : nativeRulesOk p.toNative.cvR.name (p.toNative.cvR.levelParams.map .param)
        .never p.toNative.nP p.toNative.ctors.length ctorsA p.toNative.kinds p.toNative.rhss
        p.toNative.cvR.type = true
    case neg =>
      simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h throwC_bind_ok
    simp only [hok, ↓reduceIte] at h ⊢
    simp only [discard, Functor.discard, Functor.mapConst, Function.comp_def] at h
    rw [checkNativeRecF_eq] at h
    cases hrc : checkNativeRec (sharedOpsC mode (mkFEnv env₂)) env₂ p.toNative cvTa ctorsA
        s₀.flushed with
    | error e =>
      simp only [StateT.map, hrc, bind, Except.bind] at h
      exact nomatch h
    | ok r =>
    obtain ⟨q, s₂⟩ := r
    have hs' : s₂ = s' := by
      simp only [StateT.map, hrc, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      exact h.2
    subst hs'
    obtain ⟨hs₂, q', hP, F, hF⟩ := checkNativeRecS_sim hμ henv₂ hs₁ q s₂ hrc
    obtain rfl : q = q' := hP
    refine ⟨hs₂.residue, F, ?_⟩
    have hF' : checkNativeRec (fueledOps mode F) env₂ p.toNative cvTa ctorsA = .ok q := by
      rw [← checkNativeRec_datF]; exact hF
    simp only [discard, Functor.discard, Functor.mapConst, Function.comp_def]
    rw [hF']
    rfl
  · have eF : checkBlockRecConformF (sharedOpsC mode (mkFEnv env₂)) StructWalkers.plain
        (mkFEnv env₂) none p cvTas ctorsAs = pure () := by
      unfold checkBlockRecConformF
      split
      · exfalso; exact hone ⟨_, _, _, _, by assumption, by assumption, rfl, rfl⟩
      · rfl
    rw [eF] at h
    obtain ⟨-, rfl⟩ := pureC_ok h
    refine ⟨hs₁.residue, 0, ?_⟩
    unfold checkBlockRecConform
    split
    · exfalso; exact hone ⟨_, _, _, _, by assumption, by assumption, rfl, rfl⟩
    · rfl

end ConLeche.Cached
