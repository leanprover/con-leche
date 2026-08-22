import Setlec.Verify.BridgeS1

/-!
# Shared-state walks, part 2: the inductive-install checker functions

The single-environment functions of the modeled-inductive install path
(`checkMemberVal`, the iota-theorem checks, the projection stages), as
`SimAt`s between the `sharedOps` and `fueledOpsM` instantiations.  The
per-site scoping facts mirror `Setlec/Verify/BridgeWfImp.lean`'s
`_wfimp` walks; the operation environment is the `SimAt`'s `env` (for
the iota checks that is `envSelf` — the pure model lookups run at the
separately passed `env'`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open Expr

section Walks2

variable {env : Env} {s₀ : IState}

/-- `unwrapOr` as a `SimAt`, remembering the unwrapped value. -/
protected theorem SimAt.unwrapOr' {α : Type} {o : Option α}
    {err : CheckError} (hs : ISOK env s₀) :
    SimAt env s₀ (fun _ v w => v = w ∧ o = some v)
      (unwrapOr o err : CheckIM α) (unwrapOr o err : FueledM α) := by
  cases o with
  | none => exact SimAt.throw
  | some a => exact SimAt.pure hs ⟨rfl, rfl⟩

/-- `checkDefEqList` at the shared operations. -/
theorem checkDefEqListS_sim (henv : EnvWF env) {depth : Nat} :
    ∀ {as bs : List Expr},
      (∀ a ∈ as, WScoped depth a) → (∀ b ∈ bs, WScoped depth b) →
      ∀ {s₀ : IState}, ISOK env s₀ →
      SimAt env s₀ RelV
        (checkDefEqList (sharedOps (mkFEnv env)) env depth as bs)
        (checkDefEqList fueledOpsM env depth as bs)
  | [], [], _, _, s₀, hs => SimAt.pure hs rfl
  | [], _ :: _, _, _, s₀, hs => SimAt.throw
  | _ :: _, [], _, _, s₀, hs => SimAt.throw
  | a :: as, b :: bs, ha, hb, s₀, hs => by
    unfold checkDefEqList
    dsimp only [sharedOps]
    refine SimAt.bind (opB_sim henv hs (ha a List.mem_cons_self)
        (hb b List.mem_cons_self))
      (fun s₁ c c' hs₁ hext₁ hP => ?_)
    obtain rfl : c = c' := hP
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimAt.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkDefEqListS_sim henv
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun y hy => hb y (List.mem_cons_of_mem _ hy)) hs₁

set_option maxHeartbeats 6400000 in
/-- The iota-theorem check at the shared operations (the operation
environment is `env` = the provisioned `envSelf`; `env'` only feeds
the pure model lookups). -/
theorem checkIotaThmS_sim {env' : Env} (henv' : EnvWF env')
    (henv : EnvWF env) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr}
    (htyA : tyA.hasFvar = false) (hctor : cvj.type.hasFvar = false)
    (hrhsA : rhsA.hasFvar = false) (hs : ISOK env s₀) :
    SimAt env s₀ RelV
      (checkIotaThm (sharedOps (mkFEnv env)) env' env f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA)
      (checkIotaThm fueledOpsM env' env f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA) := by
  unfold checkIotaThm
  dsimp only [sharedOps]
  refine SimAt.bind (SimAt.unwrapOr' hs) (fun s₁ cvt p' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hthm⟩ := hP
  try dsimp only
  have hcvtF : cvt.type.hasFvar = false := by
    obtain ⟨ci, hci, hcvt⟩ := findCV?_ok hthm
    exact hcvt ▸ (henv' _ (find?_mem hci)).1
  by_cases h1 : cvt.levelParams = lps
  case neg => simp only [if_neg h1]; exact SimAt.throw_bind
  simp only [if_pos h1]
  refine SimAt.bind (SimAt.unwrapOr' hs₁) (fun s₂ q q' hs₂ hext₂ hQ => ?_)
  obtain ⟨rfl, hopen⟩ := hQ
  obtain ⟨fvs, tbody⟩ := q
  dsimp only
  have hopenW := openPisAtFvars_WScoped (rP + cnF) cvt.type 0
    hopen (WScoped.of_not_hasFvar hcvtF)
  rw [Nat.zero_add] at hopenW
  obtain ⟨hfvsW, htbodyW⟩ := hopenW
  have htargsW : ∀ x ∈ tbody.getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs htbodyW
  have hlhsW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 1 (.bvar 0)) := WScoped_getD' htargsW 1
  have hrhsSW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0)) := WScoped_getD' htargsW 2
  have hlargsW : ∀ x ∈ (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs hlhsW
  by_cases h2 : isEqHead tbody.getAppFn = true
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  by_cases h3 : tbody.getAppArgs.length = 3
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  try dsimp only
  by_cases h4 : ((tbody.getAppArgs.getD 1 (.bvar 0)).getAppFn ==
      Expr.const (f cvName) (lps.map .param)) = true
  case neg => simp only [if_neg h4]; exact SimAt.throw_bind
  simp only [if_pos h4]
  by_cases h5 : (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs.length =
      mI + 1
  case neg => simp only [if_neg h5]; exact SimAt.throw_bind
  simp only [if_pos h5]
  by_cases h6 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.take rP == fvs.take rP) = true
  case neg => simp only [if_neg h6]; exact SimAt.throw_bind
  simp only [if_pos h6]
  by_cases h7 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.getLastD (.bvar 0) ==
      Expr.mkAppN (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP)) = true
  case neg => simp only [if_neg h7]; exact SimAt.throw_bind
  simp only [if_pos h7]
  by_cases h8 : (cvj.type.stripPis (cnP + cnF)).isSome = true
  case neg => simp only [if_neg h8]; exact SimAt.throw_bind
  simp only [if_pos h8]
  refine SimAt.bind (SimAt.unwrapOr' hs₂) (fun s₃ q2 q2' hs₃ hext₃ hQ2 => ?_)
  obtain ⟨rfl, hcinst⟩ := hQ2
  obtain ⟨cdoms, cres⟩ := q2
  dsimp only
  have hcargW : ∀ a ∈ fvs.take cnP ++ fvs.drop rP,
      WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact hfvsW a (List.mem_of_mem_take hax)
    · exact hfvsW a (List.mem_of_mem_drop hax)
  have hcinstW := instPisAt_WScoped _ _ hcinst
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact hctor)) hcargW
  obtain ⟨hcdomsW, hcresW⟩ := hcinstW
  by_cases h9 : cres.getAppArgs.length = cnP + (mI - rP)
  case neg => simp only [if_neg h9]; exact SimAt.throw_bind
  simp only [if_pos h9]
  refine SimAt.bind (checkDefEqListS_sim henv
      (fun a ha => hlargsW a
        (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
      (fun b hb => Expr.WScoped.getAppArgs hcresW b
        (List.mem_of_mem_drop hb)) hs₃)
    (fun s₄ u1 u1' hs₄ hext₄ hU1 => ?_)
  refine SimAt.bind (checkDefEqListS_sim henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_drop hx)))
      (fun b hb => hcdomsW b (List.mem_of_mem_drop hb)) hs₄)
    (fun s₅ u2 u2' hs₅ hext₅ hU2 => ?_)
  refine SimAt.bind (SimAt.unwrapOr' hs₅) (fun s₆ q3 q3' hs₆ hext₆ hQ3 => ?_)
  obtain ⟨rfl, hrinst⟩ := hQ3
  obtain ⟨rdoms, rrest⟩ := q3
  dsimp only
  have hrinstW := instPisAt_WScoped _ _ hrinst
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact htyA))
    (fun a ha => hfvsW a (List.mem_of_mem_take ha))
  obtain ⟨hrdomsW, -⟩ := hrinstW
  refine SimAt.bind (checkDefEqListS_sim henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_take hx)))
      (fun b hb => hrdomsW b hb) hs₆)
    (fun s₇ u3 u3' hs₇ hext₇ hU3 => ?_)
  refine SimAt.bind (SimAt.unwrapOr' hs₇) (fun s₈ q4 q4' hs₈ hext₈ hQ4 => ?_)
  obtain ⟨rfl, hopenP⟩ := hQ4
  obtain ⟨fvsP, restP⟩ := q4
  dsimp only
  have hopenPW := openPisAtFvars_WScoped rP tyA 0 hopenP
    (WScoped.of_not_hasFvar htyA)
  rw [Nat.zero_add] at hopenPW
  obtain ⟨hfvsPW, -⟩ := hopenPW
  refine SimAt.bind (SimAt.unwrapOr' hs₈) (fun s₉ q5 q5' hs₉ hext₉ hQ5 => ?_)
  obtain ⟨rfl, hcinstP⟩ := hQ5
  obtain ⟨cdomsP, crestP⟩ := q5
  dsimp only
  have hcinstPW := instPisAt_WScoped (d := rP) _ _ hcinstP
    (WScoped.of_not_hasFvar hctor)
    (fun a ha => hfvsPW a (List.mem_of_mem_take ha))
  obtain ⟨-, hcrestPW⟩ := hcinstPW
  refine SimAt.bind (SimAt.unwrapOr' hs₉) (fun s10 q6 q6' hs10 hext10 hQ6 => ?_)
  obtain ⟨rfl, hopenX⟩ := hQ6
  obtain ⟨xFvsP, crest2⟩ := q6
  dsimp only
  have hopenXW := openPisAtFvars_WScoped cnF crestP rP hopenX hcrestPW
  obtain ⟨hxFvsPW, -⟩ := hopenXW
  have hfvsPW' : ∀ a ∈ fvsP ++ xFvsP, WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact WScoped.mono (by omega) (hfvsPW a hax)
    · exact hxFvsPW a hax
  refine SimAt.bind (SimAt.unwrapOr' hs10) (fun s11 q7 q7' hs11 hext11 hQ7 => ?_)
  obtain ⟨rfl, hlinst⟩ := hQ7
  obtain ⟨ldoms, lrest⟩ := q7
  dsimp only
  have hlinstW := instLamsAt_WScoped _ _ hlinst
    (WScoped.of_not_hasFvar hrhsA) hfvsPW'
  obtain ⟨hldomsW, -⟩ := hlinstW
  refine SimAt.bind (checkDefEqListS_sim henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsPW' x hx))
      (fun b hb => hldomsW b hb) hs11)
    (fun s12 u4 u4' hs12 hext12 hU4 => ?_)
  refine SimAt.bind (opB_sim henv hs12 hrhsSW
      (Expr.WScoped.mkAppN
        (WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact hrhsA))
        (fun x hx => hfvsW x hx)))
    (fun s13 c c' hs13 hext13 hC => ?_)
  obtain rfl : c = c' := hC
  cases c with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw
  | true =>
    simp only [↓reduceIte]
    exact SimAt.pure hs13 rfl

set_option maxHeartbeats 6400000 in
/-- The nested-auxiliary iota-theorem check at the shared operations. -/
theorem checkIotaThmNS_sim {env' : Env} (henv' : EnvWF env')
    (henv : EnvWF env) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr}
    (htyA : tyA.hasFvar = false) (hctor : cvj.type.hasFvar = false)
    (hrhsA : rhsA.hasFvar = false) (hs : ISOK env s₀) :
    SimAt env s₀ RelV
      (checkIotaThmN (sharedOps (mkFEnv env)) env' env f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA)
      (checkIotaThmN fueledOpsM env' env f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA) := by
  unfold checkIotaThmN
  dsimp only [sharedOps]
  match hshape : nestedRuleShape env' env cvName lps tyA mI rP cnP j with
  | none => exact SimAt.pure hs rfl
  | some (lvls, pins) =>
  dsimp only
  have hpinsF : ∀ p ∈ pins, p.hasFvar = false :=
    nestedRuleShape_pins hshape
  refine SimAt.bind (SimAt.unwrapOr' hs) (fun s₁ cvt p' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hthm⟩ := hP
  try dsimp only
  have hcvtF : cvt.type.hasFvar = false := by
    obtain ⟨ci, hci, hcvt⟩ := findCV?_ok hthm
    exact hcvt ▸ (henv' _ (find?_mem hci)).1
  by_cases h1 : cvt.levelParams = lps
  case neg => simp only [if_neg h1]; exact SimAt.throw_bind
  simp only [if_pos h1]
  refine SimAt.bind (SimAt.unwrapOr' hs₁) (fun s₂ q q' hs₂ hext₂ hQ => ?_)
  obtain ⟨rfl, hopen⟩ := hQ
  obtain ⟨fvs, tbody⟩ := q
  dsimp only
  have hopenW := openPisAtFvars_WScoped (rP + cnF) cvt.type 0
    hopen (WScoped.of_not_hasFvar hcvtF)
  rw [Nat.zero_add] at hopenW
  obtain ⟨hfvsW, htbodyW⟩ := hopenW
  have htargsW : ∀ x ∈ tbody.getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs htbodyW
  have hlhsW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 1 (.bvar 0)) := WScoped_getD' htargsW 1
  have hrhsSW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0)) := WScoped_getD' htargsW 2
  have hlargsW : ∀ x ∈ (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs hlhsW
  by_cases h2 : isEqHead tbody.getAppFn = true
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  by_cases h3 : tbody.getAppArgs.length = 3
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  try dsimp only
  by_cases h4 : ((tbody.getAppArgs.getD 1 (.bvar 0)).getAppFn ==
      Expr.const (f cvName) (lps.map .param)) = true
  case neg => simp only [if_neg h4]; exact SimAt.throw_bind
  simp only [if_pos h4]
  by_cases h5 : (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs.length =
      mI + 1
  case neg => simp only [if_neg h5]; exact SimAt.throw_bind
  simp only [if_pos h5]
  by_cases h6 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.take rP == fvs.take rP) = true
  case neg => simp only [if_neg h6]; exact SimAt.throw_bind
  simp only [if_pos h6]
  by_cases h7 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.getLastD (.bvar 0) ==
      Expr.mkAppN (.const (f r.ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP)) = true
  case neg => simp only [if_neg h7]; exact SimAt.throw_bind
  simp only [if_pos h7]
  by_cases h8 : (cvj.type.stripPis (cnP + cnF)).isSome = true
  case neg => simp only [if_neg h8]; exact SimAt.throw_bind
  simp only [if_pos h8]
  refine SimAt.bind (SimAt.unwrapOr' hs₂) (fun s₃ q2 q2' hs₃ hext₃ hQ2 => ?_)
  obtain ⟨rfl, hcinst⟩ := hQ2
  obtain ⟨cdoms, cres⟩ := q2
  dsimp only
  have hcargW : ∀ a ∈ pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)) ++
      fvs.drop rP, WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hax
      exact instSpine_WScoped (rP - 1)
        (WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact hpinsF x hx))
        (fun a' ha' => hfvsW a' (List.mem_of_mem_take ha'))
    · exact hfvsW a (List.mem_of_mem_drop hax)
  have hcinstW := instPisAt_WScoped _ _ hcinst
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts, hasFvar_instantiateLevelParams]
      exact hctor)) hcargW
  obtain ⟨hcdomsW, hcresW⟩ := hcinstW
  by_cases h9 : cres.getAppArgs.length = cnP + (mI - rP)
  case neg => simp only [if_neg h9]; exact SimAt.throw_bind
  simp only [if_pos h9]
  refine SimAt.bind (checkDefEqListS_sim henv
      (fun a ha => hlargsW a
        (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
      (fun b hb => Expr.WScoped.getAppArgs hcresW b
        (List.mem_of_mem_drop hb)) hs₃)
    (fun s₄ u1 u1' hs₄ hext₄ hU1 => ?_)
  refine SimAt.bind (checkDefEqListS_sim henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_drop hx)))
      (fun b hb => hcdomsW b (List.mem_of_mem_drop hb)) hs₄)
    (fun s₅ u2 u2' hs₅ hext₅ hU2 => ?_)
  refine SimAt.bind (SimAt.unwrapOr' hs₅) (fun s₆ q3 q3' hs₆ hext₆ hQ3 => ?_)
  obtain ⟨rfl, hrinst⟩ := hQ3
  obtain ⟨rdoms, rrest⟩ := q3
  dsimp only
  have hrinstW := instPisAt_WScoped _ _ hrinst
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact htyA))
    (fun a ha => hfvsW a (List.mem_of_mem_take ha))
  obtain ⟨hrdomsW, -⟩ := hrinstW
  refine SimAt.bind (checkDefEqListS_sim henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_take hx)))
      (fun b hb => hrdomsW b hb) hs₆)
    (fun s₇ u3 u3' hs₇ hext₇ hU3 => ?_)
  refine SimAt.bind (SimAt.unwrapOr' hs₇) (fun s₈ q4 q4' hs₈ hext₈ hQ4 => ?_)
  obtain ⟨rfl, hopenP⟩ := hQ4
  obtain ⟨fvsP, restP⟩ := q4
  dsimp only
  have hopenPW := openPisAtFvars_WScoped rP tyA 0 hopenP
    (WScoped.of_not_hasFvar htyA)
  rw [Nat.zero_add] at hopenPW
  obtain ⟨hfvsPW, -⟩ := hopenPW
  refine SimAt.bind (SimAt.unwrapOr' hs₈) (fun s₉ q5 q5' hs₉ hext₉ hQ5 => ?_)
  obtain ⟨rfl, hcinstP⟩ := hQ5
  obtain ⟨cdomsP, crestP⟩ := q5
  dsimp only
  have hcinstPW := instPisAt_WScoped (d := rP) _ _ hcinstP
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_instantiateLevelParams]
      exact hctor))
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact instSpine_WScoped (rP - 1)
        (WScoped.of_not_hasFvar (hpinsF x hx))
        (fun a' ha' => hfvsPW a' (List.mem_of_mem_take ha')))
  obtain ⟨-, hcrestPW⟩ := hcinstPW
  refine SimAt.bind (SimAt.unwrapOr' hs₉) (fun s10 q6 q6' hs10 hext10 hQ6 => ?_)
  obtain ⟨rfl, hopenX⟩ := hQ6
  obtain ⟨xFvsP, crest2⟩ := q6
  dsimp only
  have hopenXW := openPisAtFvars_WScoped cnF crestP rP hopenX hcrestPW
  obtain ⟨hxFvsPW, -⟩ := hopenXW
  have hfvsPW' : ∀ a ∈ fvsP ++ xFvsP, WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact WScoped.mono (by omega) (hfvsPW a hax)
    · exact hxFvsPW a hax
  refine SimAt.bind (SimAt.unwrapOr' hs10) (fun s11 q7 q7' hs11 hext11 hQ7 => ?_)
  obtain ⟨rfl, hlinst⟩ := hQ7
  obtain ⟨ldoms, lrest⟩ := q7
  dsimp only
  have hlinstW := instLamsAt_WScoped _ _ hlinst
    (WScoped.of_not_hasFvar hrhsA) hfvsPW'
  obtain ⟨hldomsW, -⟩ := hlinstW
  refine SimAt.bind (checkDefEqListS_sim henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsPW' x hx))
      (fun b hb => hldomsW b hb) hs11)
    (fun s12 u4 u4' hs12 hext12 hU4 => ?_)
  refine SimAt.bind (opB_sim henv hs12 hrhsSW
      (Expr.WScoped.mkAppN
        (WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact hrhsA))
        (fun x hx => hfvsW x hx)))
    (fun s13 c c' hs13 hext13 hC => ?_)
  obtain rfl : c = c' := hC
  cases c with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
    simp only [↓reduceIte]
    exact SimAt.pure hs13 rfl

/-- One modeled recursor rule at the shared operations. -/
theorem checkIotaRuleS_sim {env' : Env} (henv' : EnvWF env')
    (henv : EnvWF env) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    (htyA : tyA.hasFvar = false) (hs : ISOK env s₀) :
    SimAt env s₀ RelV
      (checkIotaRule (sharedOps (mkFEnv env)) env' env f cvName lps tyA
        mI rP j r)
      (checkIotaRule fueledOpsM env' env f cvName lps tyA mI rP j r) := by
  unfold checkIotaRule
  dsimp only [sharedOps]
  match hf : env'.find? r.ctor with
  | none => exact SimAt.throw
  | some (.axiomInfo _) => exact SimAt.throw
  | some (.projInfo _) => exact SimAt.throw
  | some (.defnInfo _ _ _) => exact SimAt.throw
  | some (.thmInfo _ _) => exact SimAt.throw
  | some (.indInfo _ _) => exact SimAt.throw
  | some (.recInfo _ _ _ _) => exact SimAt.throw
  | some (.ctorInfo cvj cnP cnF) =>
  dsimp only
  by_cases h2 : r.nfields = cnF
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  by_cases h3 : Expr.looseBVarsBounded 0 (RecRule.rhs r) = true
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  by_cases h4 : (RecRule.rhs r).hasFvar = true
  · simp only [if_pos h4]; exact SimAt.throw_bind
  simp only [if_neg h4]
  refine SimAt.bind (opE_annotate_sim henv hs
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h4)))
    (fun s₁ rhsA rhsA' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hwrhsA⟩ := hP
  have hrhsAF : rhsA.hasFvar = false :=
    not_hasFvar_of_fvarsBelow_zero hwrhsA.fvarsBelow
  by_cases h5 : Expr.allLevelParamsDefined lps rhsA = true
  case neg => simp only [if_neg h5]; exact SimAt.throw_bind
  simp only [if_pos h5]
  by_cases h6 : Expr.constsResolve env rhsA = true
  case neg => simp only [if_neg h6]; exact SimAt.throw_bind
  simp only [if_pos h6]
  by_cases h7 : (rhsA.stripLams (rP + cnF)).isSome = true
  case neg => simp only [if_neg h7]; exact SimAt.throw_bind
  simp only [if_pos h7]
  refine SimAt.bind (opE_infer_sim henv hs₁ hwrhsA)
    (fun s₂ rhsTy rhsTy' hs₂ hext₂ hP₂ => ?_)
  have hctorF : cvj.type.hasFvar = false := (henv' _ (find?_mem hf)).1
  by_cases h8 : Expr.recRulePlain tyA mI rP cnP = true
  case neg =>
    simp only [if_neg h8]
    refine SimAt.bind (checkIotaThmNS_sim henv' henv htyA hctorF
        hrhsAF hs₂)
      (fun s₃ fire fire' hs₃ hext₃ hP₃ => ?_)
    obtain rfl : fire = fire' := hP₃
    exact SimAt.pure hs₃ rfl
  simp only [if_pos h8]
  refine SimAt.bind (checkIotaThmS_sim henv' henv htyA hctorF hrhsAF hs₂)
    (fun s₃ u u' hs₃ hext₃ hP₃ => ?_)
  first
  | exact SimAt.pure hs₃ rfl
  | exact SimAt.bind_pure_left (SimAt.bind_pure_right (SimAt.pure hs₃ rfl))

/-- The rule fold at the shared operations. -/
theorem checkIotaRulesS_sim {env' : Env} (henv' : EnvWF env')
    (henv : EnvWF env) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP : Nat}
    (htyA : tyA.hasFvar = false) :
    ∀ {j : Nat} {rules : List RecRule} {s₀ : IState}, ISOK env s₀ →
      SimAt env s₀ RelV
        (checkIotaRules (sharedOps (mkFEnv env)) env' env f cvName lps
          tyA mI rP j rules)
        (checkIotaRules fueledOpsM env' env f cvName lps tyA
          mI rP j rules)
  | _, [], s₀, hs => SimAt.pure hs rfl
  | j, r :: rest, s₀, hs => by
    unfold checkIotaRules
    refine SimAt.bind (checkIotaRuleS_sim henv' henv htyA hs)
      (fun s₁ r' r'' hs₁ hext₁ hP => ?_)
    obtain rfl : r' = r'' := hP
    refine SimAt.bind (checkIotaRulesS_sim henv' henv htyA hs₁)
      (fun s₂ rest' rest'' hs₂ hext₂ hP₂ => ?_)
    obtain rfl : rest' = rest'' := hP₂
    exact SimAt.pure hs₂ rfl

/-- The member-against-model check at the shared operations; the
returned constant's type is well-scoped. -/
theorem checkMemberValS_sim (henv : EnvWF env) {blockNames : List Name}
    {cv : ConstantVal} (hs : ISOK env s₀) :
    SimAt env s₀ (fun _ v w => v = w ∧ WScoped 0 v.type)
      (checkMemberVal (sharedOps (mkFEnv env)) blockNames env cv)
      (checkMemberVal fueledOpsM blockNames env cv) := by
  unfold checkMemberVal
  refine SimAt.bind (checkConstantValS_sim henv hs)
    (fun s₁ cvA cvA' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hwty⟩ := hP
  by_cases h1 : cvA.name.isModelSuffix = true
  · simp only [if_pos h1]; exact SimAt.throw_bind
  simp only [if_neg h1]
  match hm : env.find? (cvA.name.str "_model") with
  | none => exact SimAt.throw
  | some (.axiomInfo _) => exact SimAt.throw
  | some (.projInfo _) => exact SimAt.throw
  | some (.thmInfo _ _) => exact SimAt.throw
  | some (.indInfo _ _) => exact SimAt.throw
  | some (.ctorInfo _ _ _) => exact SimAt.throw
  | some (.recInfo _ _ _ _) => exact SimAt.throw
  | some (.defnInfo cvm mval mhint) =>
  dsimp only
  by_cases h2 : cvm.levelParams = cvA.levelParams
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  by_cases h3 : Expr.eqUpToNames (cvA.type.renameConsts
      (fun n => if blockNames.contains n then n.str "_model" else n))
      cvm.type = true
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  exact SimAt.pure hs₁ ⟨rfl, hwty⟩

/-- The projection-rule stage at the shared operations. -/
theorem checkProjRuleS_sim (henv : EnvWF env) {cvj : ConstantVal}
    {lps : List Name} {nP nF i : Nat} (hs : ISOK env s₀) :
    SimAt env s₀ RelV
      (checkProjRule (sharedOps (mkFEnv env)) env cvj lps nP nF i)
      (checkProjRule fueledOpsM env cvj lps nP nF i) := by
  unfold checkProjRule
  dsimp only [sharedOps]
  match hrhs : Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i)) with
  | none => exact SimAt.throw
  | some rhs =>
  dsimp only
  by_cases h1 : (!rhs.hasFvar && Expr.looseBVarsBounded 0 rhs) = true
  case neg => simp only [if_neg h1]; exact SimAt.throw_bind
  simp only [if_pos h1]
  have hrf : rhs.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact h1.1
  refine SimAt.bind (opE_annotate_sim henv hs
      (WScoped.of_not_hasFvar hrf))
    (fun s₁ rhsA rhsA' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hwrhsA⟩ := hP
  by_cases h2 : (Expr.allLevelParamsDefined lps rhsA &&
      Expr.constsResolve env rhsA && Expr.looseBVarsBounded 0 rhsA &&
      !rhsA.hasFvar) = true
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  match hstrip : rhsA.stripLams (nP + nF) with
  | none => exact SimAt.throw
  | some (rbinders, rrbody) =>
  dsimp only
  by_cases h3 : (rrbody == Expr.bvar (nF - 1 - i)) = true
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  match hstripC : cvj.type.stripPis (nP + nF) with
  | none => exact SimAt.throw
  | some (cbindersR, cbodyR) =>
  dsimp only
  by_cases h4 : domsMatchAux (fun _ e => e) rbinders cbindersR 0 0
      (nP + nF) = true
  case neg => simp only [if_neg h4]; exact SimAt.throw_bind
  simp only [if_pos h4]
  exact SimAt.pure hs₁ rfl

/-- `checkProjLookups` (operation-free) as a `SimAt`. -/
theorem checkProjLookupsS_sim {env' : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat} (hs : ISOK env s₀) :
    SimAt env s₀ RelV
      (checkProjLookups env' T ctorName lps nP nF i : CheckIM _)
      (checkProjLookups env' T ctorName lps nP nF i : FueledM _) := by
  unfold checkProjLookups
  match h1 : env'.find? ctorName with
  | none => exact SimAt.throw
  | some (.axiomInfo _) => exact SimAt.throw
  | some (.projInfo _) => exact SimAt.throw
  | some (.thmInfo _ _) => exact SimAt.throw
  | some (.indInfo _ _) => exact SimAt.throw
  | some (.defnInfo _ _ _) => exact SimAt.throw
  | some (.recInfo _ _ _ _) => exact SimAt.throw
  | some (.ctorInfo cvj cnP cnF) =>
  dsimp only
  by_cases h2 : cnP = nP ∧ cnF = nF
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  match h3 : env'.find? (projModelName T i) with
  | none => exact SimAt.throw
  | some (.axiomInfo _) => exact SimAt.throw
  | some (.projInfo _) => exact SimAt.throw
  | some (.thmInfo _ _) => exact SimAt.throw
  | some (.indInfo _ _) => exact SimAt.throw
  | some (.ctorInfo _ _ _) => exact SimAt.throw
  | some (.recInfo _ _ _ _) => exact SimAt.throw
  | some (.defnInfo mcv _ _) =>
  dsimp only
  by_cases h4 : mcv.levelParams = lps
  case neg => simp only [if_neg h4]; exact SimAt.throw_bind
  simp only [if_pos h4]
  by_cases h5 : (env'.find? (projFnName T i)).isNone = true
  case neg => simp only [if_neg h5]; exact SimAt.throw_bind
  simp only [if_pos h5]
  by_cases h6 : (env'.find? T).isSome = true
  case neg => simp only [if_neg h6]; exact SimAt.throw_bind
  simp only [if_pos h6]
  by_cases h7 : env'.find? eqName = some eqA
  case neg => simp only [if_neg h7]; exact SimAt.throw_bind
  simp only [if_pos h7]
  exact SimAt.pure hs rfl

/-- `checkProjTy` (operation-free) as a `SimAt`. -/
theorem checkProjTyS_sim {env' : Env} {T ctorName : Name}
    {lps : List Name} {mty : Expr} {nP nF : Nat} (hs : ISOK env s₀) :
    SimAt env s₀ RelV
      (checkProjTy env' T ctorName lps mty nP nF : CheckIM _)
      (checkProjTy env' T ctorName lps mty nP nF : FueledM _) := by
  unfold checkProjTy
  dsimp only
  by_cases h1 : ((mty.renameConsts (projBack T ctorName nF)).renameConsts
      (projFwd T ctorName nF) == mty) = true
  case neg => simp only [if_neg h1]; exact SimAt.throw_bind
  simp only [if_pos h1]
  by_cases h2 : Expr.constsResolve env'
      (mty.renameConsts (projBack T ctorName nF)) = true
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  by_cases h3 : (Expr.looseBVarsBounded 0
      (mty.renameConsts (projBack T ctorName nF)) &&
      !(mty.renameConsts (projBack T ctorName nF)).hasFvar &&
      Expr.allLevelParamsDefined lps
        (mty.renameConsts (projBack T ctorName nF))) = true
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  by_cases h4 : ((mty.renameConsts
      (projBack T ctorName nF)).stripPis (nP + 1)).isSome = true
  case neg => simp only [if_neg h4]; exact SimAt.throw_bind
  simp only [if_pos h4]
  exact SimAt.pure hs rfl

/-- `checkProjIota` (operation-free) as a `SimAt`. -/
theorem checkProjIotaS_sim {env' : Env} {T ctorName : Name}
    {lps : List Name} {cvj : ConstantVal} {nP nF i : Nat}
    (hs : ISOK env s₀) :
    SimAt env s₀ RelV
      (checkProjIota env' T ctorName lps cvj nP nF i : CheckIM _)
      (checkProjIota env' T ctorName lps cvj nP nF i : FueledM _) := by
  unfold checkProjIota
  match h1 : env'.find? ((projModelName T i).str "iota") with
  | none => exact SimAt.throw
  | some (.axiomInfo _) => exact SimAt.throw
  | some (.projInfo _) => exact SimAt.throw
  | some (.defnInfo _ _ _) => exact SimAt.throw
  | some (.indInfo _ _) => exact SimAt.throw
  | some (.ctorInfo _ _ _) => exact SimAt.throw
  | some (.recInfo _ _ _ _) => exact SimAt.throw
  | some (.thmInfo tcv _) =>
  dsimp only
  by_cases h2 : tcv.levelParams = lps
  case neg => simp only [if_neg h2]; exact SimAt.throw_bind
  simp only [if_pos h2]
  match h3 : tcv.type.stripPis (nP + nF) with
  | none => exact SimAt.throw
  | some (sbinders, sbody) =>
  dsimp only
  match h4 : cvj.type.stripPis (nP + nF) with
  | none => exact SimAt.throw
  | some (cbindersR, _) =>
  dsimp only
  by_cases h5 : domsMatchAux
      (fun _ e => e.renameConsts (projFwd T ctorName nF))
      sbinders cbindersR 0 0 (nP + nF) = true
  case neg => simp only [if_neg h5]; exact SimAt.throw_bind
  simp only [if_pos h5]
  cases sbody with
  | app f3 rhsC =>
    cases f3 with
    | app f2 lhsC =>
      cases f2 with
      | app f1 tySlot =>
        cases f1 with
        | const c ls =>
          cases ls with
          | nil => exact SimAt.throw
          | cons ℓ ls' =>
            cases ls' with
            | cons _ _ => exact SimAt.throw
            | nil =>
              dsimp only
              by_cases h6 : c = eqName
              case neg => simp only [if_neg h6]; exact SimAt.throw_bind
              simp only [if_pos h6]
              by_cases h7 : (lhsC == Expr.mkAppN
                  (.const (projModelName T i) (lps.map .param))
                  (((List.range nP).map fun k =>
                    Expr.bvar (nP + nF - 1 - k)) ++
                   [Expr.mkAppN (.const (ctorName.str "_model")
                     (cvj.levelParams.map .param))
                     ((((List.range nP).map fun k =>
                       Expr.bvar (nP + nF - 1 - k)) ++
                      (List.range nF).map fun k =>
                        Expr.bvar (nF - 1 - k)))])) = true
              case neg => simp only [if_neg h7]; exact SimAt.throw_bind
              simp only [if_pos h7]
              by_cases h8 : (rhsC == Expr.bvar (nF - 1 - i)) = true
              case neg => simp only [if_neg h8]; exact SimAt.throw
              simp only [if_pos h8]
              exact SimAt.pure hs rfl
        | _ => exact SimAt.throw
      | _ => exact SimAt.throw
    | _ => exact SimAt.throw
  | _ => exact SimAt.throw

end Walks2

end Setlec
