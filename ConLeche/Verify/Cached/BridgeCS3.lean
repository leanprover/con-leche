module

public import ConLeche.Verify.Cached.BridgeCS2
import ConLeche.Verify.Cached.NestPosC
public import ConLeche.Verify.Inductives.NestScope

public section

/-!
# Cached shared-state walks, part 3: the direct simple-structure install

Port of `ConLeche/Verify/BridgeS3.lean` for the cached tier.  The
single-environment functions of the direct-install path
(`checkStructFieldSorts`, `checkStructDomsAt`, `checkStructInd`,
`checkStructCtor`, `checkStructRec`,
`checkStructProj`), as `SimC`s between the `sharedOpsC` and
`(fueledOpsM mode)` instantiations.  The per-site scoping facts mirror
`ConLeche/Verify/BridgeWfImp.lean`'s `_wfimp` walks one for one; the
`FEnv`-to-`Env` step is `ConLeche/Verify/CheckerF.lean`'s `_eq`/`_push`
family and happens in `ConLeche/Verify/Cached/BridgeCS4.lean`, so
everything here is stated over the generic functions.

The *subjects* are the very same `Expr`-level checker functions as in
the interned original — only the operations record differs — so the
walks transpose by the recipe's substitutions alone (`SimAt → SimC`,
`ISOK → CSOK`, no `Ext` binder, state-free value relations).  The pure
comparand side of every statement is byte-identical to the interned
original's.
-/

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr
open Expr

variable {mode : CheckMode}

section Walks3

variable {env : Env} {s₀ : CState}

/-- The per-frame binder-domain pins at the shared operations. -/
theorem checkStructDomsAtS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {off : Nat}
    {fvs doms : List Expr}
    (hc : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      WScoped (off + i) (Expr.fvarTypeD x))
    (ht : ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (off + i) x) :
    ∀ {j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkStructDomsAt (sharedOpsC mode (mkFEnv env)) env off fvs doms j)
        (checkStructDomsAt (fueledOpsM mode) env off fvs doms j)
  | 0, s₀, hs => SimC.pure hs rfl
  | j + 1, s₀, hs => by
    unfold checkStructDomsAt
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
      exact checkStructDomsAtS_sim hμ henv hc ht hs₃

/-! ## The direct sum install (task #175 sum-types, indexed)

The same three stages over a constructor *list*: the former, one
constructor stage per constructor — all at the environment holding the
type former alone — and the recursor, generated and compared, whose
rules loop runs `inferType` on closed generated right-hand sides.
Task #175 indexed: the stages carry `nIdx` and the field-sort walk is
`checkStructFieldSortsI` (`checkStructFieldSortsIS_sim`, `NestPosC.lean`: U2 runs it
too). -/

/-- Official's telescope loop (task #195) at the shared operations:
every `whnf` is the shared one, on a well-scoped input at its depth
(the opened body is well-scoped one deeper). -/
theorem whnfTelescopeS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) :
    ∀ {i n : Nat} {e : Expr} {s₀ : CState}, CSOK mode env s₀ → WScoped i e →
      SimC mode env s₀ RelVC
        (whnfTelescope (sharedOpsC mode (mkFEnv env)) env i n e)
        (whnfTelescope (fueledOpsM mode) env i n e)
  | i, 0, e, s₀, hs, hw => by
    unfold whnfTelescope
    dsimp only [sharedOpsC]
    refine SimC.bind (opE_whnf_sim hμ henv hs hw) (fun s₁ e' e'' hs₁ hR => ?_)
    obtain ⟨rfl, -⟩ := hR
    split
    · exact SimC.pure hs₁ rfl
    · exact SimC.throw
  | i, n + 1, e, s₀, hs, hw => by
    unfold whnfTelescope
    dsimp only [sharedOpsC]
    refine SimC.bind (opE_whnf_sim hμ henv hs hw) (fun s₁ e' e'' hs₁ hR => ?_)
    obtain ⟨rfl, hw'⟩ := hR
    split
    · next nm dom body bm =>
      simp only [WScoped] at hw'
      refine SimC.bind (whnfTelescopeS_sim hμ henv hs₁ (WScoped.instantiate1 hw'.1 0 hw'.2))
        (fun s₂ q q' hs₂ hQ => ?_)
      obtain rfl : q = q' := hQ
      exact SimC.pure hs₂ rfl
    · exact SimC.throw

/-- The former's telescope stage (task #195) at the shared operations:
the checked constant's type is well-scoped either way. -/
theorem checkSumTeleS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {cv : ConstantVal} {n : Nat} {cvTa₀ : ConstantVal}
    (hs : CSOK mode env s₀) (hTw : WScoped 0 cvTa₀.type) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 (Prod.fst v).type)
      (checkSumTele (sharedOpsC mode (mkFEnv env)) env cv n cvTa₀)
      (checkSumTele (fueledOpsM mode) env cv n cvTa₀) := by
  unfold checkSumTele
  split
  · exact SimC.pure hs ⟨rfl, hTw⟩
  · refine SimC.bind (whnfTelescopeS_sim hμ henv hs hTw) (fun s₁ q q' hs₁ hQ => ?_)
    obtain rfl : q = q' := hQ
    refine SimC.bind (checkConstantValS_sim hμ henv hs₁) (fun s₂ cvTa cvTa' hs₂ hP => ?_)
    obtain ⟨rfl, hTw'⟩ := hP
    exact SimC.pure hs₂ ⟨rfl, hTw'⟩

/-- Stage 2 (one constructor, the constructor and its field count
explicit) at the shared operations. -/
theorem checkSumCtorS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env₀ : Env} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC : ConstantVal} {nF : Nat} {cvTa : ConstantVal}
    (hTf : cvTa.type.hasFvar = false) (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkSumCtor (sharedOpsC mode (mkFEnv env)) env₀ env T lps nP
        nIdx resSort isProp large cvC nF cvTa)
      (checkSumCtor (fueledOpsM mode) env₀ env T lps nP nIdx resSort isProp large
        cvC nF cvTa) := by
  unfold checkSumCtor
  dsimp only [sharedOpsC]
  refine SimC.bind (checkConstantValS_sim hμ henv hs)
    (fun s₁ cvCa cvCa' hs₁ hP => ?_)
  obtain ⟨rfl, hCw⟩ := hP
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ q q' hs₂ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨cbs, cbody⟩ := q
  dsimp only
  by_cases h1 : structCtorResidOk T lps nP nF nIdx cbody = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ cq cq' hs₃ hR => ?_)
  obtain ⟨rfl, hop⟩ := hR
  obtain ⟨fvsP, crest⟩ := cq
  dsimp only
  obtain ⟨hfvsW0, hcrW0⟩ := openPisAtFvars_WScoped nP cvCa.type 0 hop hCw
  have hcrW : WScoped nP crest := by rwa [Nat.zero_add] at hcrW0
  refine SimC.bind (SimC.unwrapOr' hs₃) (fun s₄ tq tq' hs₄ hS => ?_)
  obtain ⟨rfl, hci⟩ := hS
  obtain ⟨tfvs, trest⟩ := tq
  dsimp only
  obtain ⟨htfvsW0, -⟩ := openPisAtFvars_WScoped nP cvTa.type 0 hci
    (WScoped.of_not_hasFvar hTf)
  refine SimC.bind (checkStructDomsAtS_sim hμ (off := 0) henv
      (fun i x hx => by
        obtain ⟨ty, rfl⟩ := openPisAtFvars_index nP cvCa.type 0 hop i x hx
        have hw := hfvsW0 _ (List.mem_of_getElem? hx)
        simp only [WScoped] at hw
        exact hw.2)
      (fun i x hx => by
        rw [List.getElem?_map] at hx
        obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
        obtain ⟨ty, rfl⟩ := openPisAtFvars_index nP cvTa.type 0 hci i y hy
        have hw := htfvsW0 _ (List.mem_of_getElem? hy)
        simp only [WScoped] at hw
        exact hw.2)
      hs₄)
    (fun s₅ u1 u1' hs₅ hU1 => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₅) (fun s₆ xq xq' hs₆ hT => ?_)
  obtain ⟨rfl, hox⟩ := hT
  obtain ⟨xFvs, cresid⟩ := xq
  dsimp only
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped nF crest nP hox hcrW
  have hxPos : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x →
      WScoped (nP + i) (Expr.fvarTypeD x) := by
    intro i x hx
    obtain ⟨ty, rfl⟩ := openPisAtFvars_index nF crest nP hox i x hx
    have hw := hxW _ (List.mem_of_getElem? hx)
    simp only [WScoped] at hw
    exact hw.2
  by_cases h2 : (cresid.getAppFn == Expr.const T (lps.map .param) &&
      cresid.getAppArgs.take nP == fvsP && cresid.getAppArgs.length == nP + nIdx) = true
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  by_cases h3 : (xFvs.all fun x => Expr.constsResolve env₀ x.fvarTypeD) = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  by_cases h4 : ((cresid.getAppArgs.drop nP).all fun e => Expr.constsResolve env₀ e) = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  refine SimC.bind (checkStructFieldSortsIS_sim hμ henv hxPos hs₆)
    (fun s₇ sorts sorts' hs₇ hS => ?_)
  obtain rfl : sorts = sorts' := hS
  exact SimC.pure hs₇ rfl

/-- Stage 2, the whole constructor list: every constructor is checked
at the *same* environment (the one holding the type former alone), so
the walk is a plain induction on the list. -/
theorem checkSumCtorsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env₀ : Env} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvTa : ConstantVal} (hTf : cvTa.type.hasFvar = false) :
    ∀ {cs : List (ConstantVal × Nat)} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkSumCtors (sharedOpsC mode (mkFEnv env)) env₀ env T lps
          nP nIdx resSort isProp large cvTa cs)
        (checkSumCtors (fueledOpsM mode) env₀ env T lps nP nIdx resSort isProp
          large cvTa cs)
  | [], s₀, hs => SimC.pure hs rfl
  | c :: cs, s₀, hs => by
    unfold checkSumCtors
    dsimp only [sharedOpsC]
    refine SimC.bind (checkSumCtorS_sim hμ henv hTf hs)
      (fun s₁ q q' hs₁ hP => ?_)
    obtain rfl : q = q' := hP
    obtain ⟨cvCa, sorts⟩ := q
    dsimp only
    refine SimC.bind (checkSumCtorsS_sim hμ henv hTf hs₁)
      (fun s₂ rest rest' hs₂ hR => ?_)
    obtain rfl : rest = rest' := hR
    obtain ⟨rest, srest⟩ := rest
    exact SimC.pure hs₂ rfl

/-! ### The direct recursive install (task #188) -/

/-- The generated rules loop of the recursive route: no operation is
called (a rule mentions the recursor and is not inferred), so the walk
is the identity on a pure program. -/
theorem checkNativeRulesS_sim {envR : Env} {rlps : List Name} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nIdx : Nat} {tty : Expr}
    {ctors : List (Name × Nat × Expr × List Nat)} {recC : Name} {rlvls : List Level} :
    ∀ {k j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkNativeRules (m := CheckCM) envR rlps T lps elim large nP nIdx tty ctors
          recC rlvls k j)
        (checkNativeRules (m := FueledM) envR rlps T lps elim large nP nIdx tty ctors
          recC rlvls k j)
  | 0, _, s₀, hs => SimC.pure hs rfl
  | k + 1, j, s₀, hs => by
    unfold checkNativeRules
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ rhs rhs' hs₁ hP => ?_)
    obtain ⟨rfl, -⟩ := hP
    by_cases h1 : (Expr.allLevelParamsDefined rlps rhs &&
        Expr.constsResolve envR rhs && Expr.looseBVarsBounded 0 rhs &&
        !rhs.hasFvar) = true
    case neg => simp only [if_neg h1]; exact SimC.throw_bind
    simp only [if_pos h1]
    refine SimC.bind (checkNativeRulesS_sim hs₁)
      (fun s₂ rest rest' hs₂ hR => ?_)
    obtain rfl : rest = rest' := hR
    exact SimC.pure hs₂ rfl

/-- Stage 3 (the recursor with the inductive hypotheses, generated and
compared) of the recursive route at the shared operations. -/
theorem checkNativeRecS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : NativeParts} {cvTa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkNativeRec (sharedOpsC mode (mkFEnv env)) env p cvTa ctorsA)
      (checkNativeRec (fueledOpsM mode) env p cvTa ctorsA) := by
  unfold checkNativeRec
  dsimp only [sharedOpsC]
  -- the recursor pin (task #220): both sides throw at the same guard
  by_cases hn : (p.cvR.name == p.cvT.name.str "rec") = true
  case neg => simp only [if_neg hn]; intro v' s' hr; exact nomatch hr
  simp only [if_pos hn]
  by_cases hlp : nativeRecLpsOk p.toInductiveShape = true
  case neg => simp only [if_neg hlp]; intro v' s' hr; exact nomatch hr
  simp only [if_pos hlp]
  by_cases hpin : p.recPinned = true
  case neg => simp only [if_neg hpin]; intro v' s' hr; exact nomatch hr
  simp only [if_pos hpin]
  refine SimC.bind (checkConstantValS_sim hμ henv hs) (fun s₁ cvRi cvRi' hs₁ hP => ?_)
  obtain ⟨rfl, hwI⟩ := hP
  try dsimp only
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ recTy recTy' hs₂ hR => ?_)
  obtain ⟨rfl, -⟩ := hR
  by_cases h1 : (Expr.allLevelParamsDefined p.cvR.levelParams recTy &&
      Expr.constsResolve env recTy && Expr.looseBVarsBounded 0 recTy &&
      !recTy.hasFvar) = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  have hRf : recTy.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact h1.2
  have hwR : WScoped 0 recTy := WScoped.of_not_hasFvar hRf
  refine SimC.bind (opE_infer_sim hμ henv hs₂ hwR) (fun s₃ sty sty' hs₃ hS => ?_)
  obtain ⟨rfl, hwsty⟩ := hS
  refine SimC.bind (opS_sim hμ henv hs₃ hwsty) (fun s₄ u u' hs₄ hU => ?_)
  refine SimC.bind (opB_sim hμ henv hs₄ hwI hwR) (fun s₅ b b' hs₅ hB => ?_)
  obtain rfl : b = b' := hB
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  refine SimC.bind (checkNativeRulesS_sim hs₅)
    (fun s₆ rhss rhss' hs₆ hRs => ?_)
  obtain rfl : rhss = rhss' := hRs
  exact SimC.pure hs₆ rfl

end Walks3

end ConLeche.Cached
