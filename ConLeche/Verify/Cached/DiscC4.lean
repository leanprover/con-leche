module

public import ConLeche.Verify.Cached.BinderLoopC
import ConLeche.Verify.BetaSpine
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.LooseBVar
public import ConLeche.Verify.ProjGuard

public section

/-!
# Cached body walks, part 4: head normalization and the whnf loop

Simulation walks (task #163) for the cached `reduceProjCoreI`,
`whnfAppI`/`betaPeelI`, `whnfCoreStepI`/`whnfCoreLoopI`/`whnfCoreBodyI`,
`whnfLoopI`/`whnfBodyI`, `inferSpineI`/`inferSpineIOI` and
`inferBodyI`/`inferBodyIOI` (`ConLeche/Cached/CoreC.lean`) against the
pure fueled comparands.  Every walk is a `Std.WP` triple proved by
`vcgen` and `grind` (`ConLeche/Verify/Cached/Grind.lean`); the bodies
are stated as `BodySpec`s, which the knot (`KnotC.lean`) consumes.

The loops are unfolded by their own `eq_def` in the `vcgen` list (the
generated per-arm equations of their inner `match` are conditional, which
`vcgen` skips); the pure mirrors' own equation lemmas go into the `sym`
list.  The bodies' `Expr` dispatch is one level deep, so the pure
bodies are unfolded as they are (one equation per constructor); where the
cached body walks a loop the chained specification does not
(`whnfCoreBody`'s head-normalization loop, `inferBody`'s spine), a
guarded `Runs` bridge (`Runs.whnfCore_of_cont`, `Runs.inferBody_app`,
`Runs.inferBodyIO_app`) carries the loop's answer to the body's.

In `inferBodyI` the binder-telescope peel fuel is the constant
`peelFuelM`, opaque to the binder-loop tails, which quantify over the
fuel.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool}

section Walks

variable {env : Env} {f : Nat}

/-- The spine length the arity pre-check computes is the length of the
argument list the ι step builds. -/
private theorem iotaNumArgs_getAppArgsAcc (e : Expr) :
    ∀ acc : List Expr,
      iotaNumArgs e acc.length = (Expr.getAppArgsAccC e acc).length := by
  induction e with
  | app g a ihg _ =>
    intro acc
    rw [iotaNumArgs, Expr.getAppArgsAccC, ← ihg (a :: acc)]
    rfl
  | _ => intro acc; rfl

private theorem iotaNumArgs_zero (e : Expr) :
    iotaNumArgs e 0 = (Expr.getAppArgsC e).length :=
  iotaNumArgs_getAppArgsAcc e []

/-- Where the arity pre-check fails, the ι step has nothing to do: its
own guard returns `none` on exactly the same three grounds (the head is
not a constant, it is not a stored recursor, or the spine has the wrong
number of arguments or of levels). -/
private theorem iotaRecI_of_arityOk_false {mi : CheckMode} {fe : FEnv} {lv : Nat}
    {d : Nat} {e : Expr} (h : iotaArityOk fe e = false) :
    iotaRecI mi fe eager lv d e = pure none := by
  unfold iotaArityOk at h
  rw [iotaRecI.eq_def]
  cases hg : Expr.getAppFn e with
  | const c us =>
    rw [hg] at h
    dsimp only at h
    simp only [pure_bind]
    cases hf : fe.find? c with
    | none => rfl
    | some ci =>
      rw [hf] at h
      cases ci with
      | recInfo cv mI rP isK rules =>
        dsimp only at h ⊢
        rw [ite_eq_right]
        rintro ⟨hlen, hlvl, -⟩
        rw [iotaNumArgs_zero, hlen, hlvl] at h
        simp at h
      | _ => rfl
  | _ => rfl

/-- The pre-check in the spine loop changes no verdict. -/
private theorem iotaArityOk_guard {mi : CheckMode} {fe : FEnv} {lv : Nat}
    {d : Nat} {e : Expr} :
    (if iotaArityOk fe e then iotaRecI mi fe eager lv d e else pure none)
      = iotaRecI mi fe eager lv d e := by
  by_cases h : iotaArityOk fe e = true
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, iotaRecI_of_arityOk_false (Bool.not_eq_true _ |>.mp h)]

/-! ### The stuck spine

`whnfStuckI` answers a spine whose head is its own head normal form (`isStuckHeadC`) with
the ι step at the one prefix where it can fire, and otherwise with the input.  The bulk-beta
loop `whnfAppI`, which the specification mirror follows, tries ι at every prefix and
rebuilds the spine; `whnfStuckI_eq` identifies the two, prefix by prefix: everywhere but at
the ι target the arity pre-check fails, and `iotaRecI` answers `none`
(`iotaRecI_of_arityOk_false`). -/

private theorem iotaNumArgs_add (e : Expr) : ∀ n, iotaNumArgs e n = iotaNumArgs e 0 + n := by
  induction e with
  | app g a ihg _ =>
    intro n
    rw [iotaNumArgs, iotaNumArgs, ihg (n + 1), ihg 1]
    omega
  | _ => intro n; simp [iotaNumArgs]

private theorem iotaNumArgs_mkAppN (v : Expr) :
    ∀ xs : List Expr, iotaNumArgs (Expr.mkAppN v xs) 0 = iotaNumArgs v 0 + xs.length
  | [] => rfl
  | a :: xs => by
    rw [show Expr.mkAppN v (a :: xs) = Expr.mkAppN (.app v a) xs from rfl,
      iotaNumArgs_mkAppN (.app v a) xs, iotaNumArgs, iotaNumArgs_add v 1]
    simp only [List.length_cons]; omega

/-- The arity pre-check is the ι target read off the spine's head. -/
private theorem iotaArityOk_eq_target (fe : FEnv) (x : Expr) :
    iotaArityOk fe x = true ↔ iotaTargetF fe x.getAppFn = some (iotaNumArgs x 0) := by
  unfold iotaArityOk iotaTargetF
  cases x.getAppFn with
  | const c us =>
    dsimp only
    cases fe.find? c with
    | none => simp
    | some ci =>
      cases ci with
      | recInfo cv mI _ _ _ =>
        dsimp only
        by_cases hl : us.length = cv.levelParams.length
        · simp only [hl, beq_self_eq_true, Bool.and_true, beq_iff_eq, ite_true,
            Option.some.injEq]
          constructor <;> intro h <;> omega
        · simp [hl]
      | _ => simp
  | _ => simp

private theorem iotaTargetF_pos {fe : FEnv} {h : Expr} {k : Nat}
    (hk : iotaTargetF fe h = some k) : 0 < k := by
  unfold iotaTargetF at hk
  split at hk
  · split at hk
    · split at hk
      · cases hk; omega
      · cases hk
    · cases hk
  · cases hk

private theorem isStuckHeadC_getAppFn {h : Expr} (hh : isStuckHeadC h = true) :
    h.getAppFn = h := by
  cases h <;> first | rfl | exact nomatch hh

private theorem isStuckHeadC_iotaNumArgs {h : Expr} (hh : isStuckHeadC h = true) :
    iotaNumArgs h 0 = 0 := by
  cases h <;> first | rfl | exact nomatch hh

private theorem isStuckHeadC_getAppArgs {h : Expr} (hh : isStuckHeadC h = true) :
    h.getAppArgs = [] := by
  cases h <;> first | rfl | exact nomatch hh

/-- `whnfAppI`'s step at a head that is not a lambda. -/
private theorem whnfAppI_cons_ne_lam {mi : CheckMode} {fe : FEnv} {lv : Nat} {d : Nat}
    {v : Expr} (hv : ∀ ty b, v ≠ .lam ty b) (a : Expr) (rest : List Expr) :
    whnfAppI mi fe eager lv d v (a :: rest) =
      ((if iotaArityOk fe (.app v a) then iotaRecI mi fe eager lv d (.app v a) else pure none) >>=
        fun o => match o with
          | some e'' => do
            let e' ← mkAppNM e'' rest
            pure (.cont e')
          | none => whnfAppI mi fe eager lv d (.app v a) rest) := by
  rw [whnfAppI.eq_def]
  cases v with
  | lam ty b => exact absurd rfl (hv ty b)
  | _ => rfl

private theorem ne_lam_of_getAppFn {v h : Expr} (hv : v.getAppFn = h)
    (hh : isStuckHeadC h = true) : ∀ ty b, v ≠ .lam ty b := by
  rintro ty b rfl
  simp [Expr.getAppFn] at hv
  subst hv
  exact nomatch hh

/-- Away from the ι target the spine loop only rebuilds the spine. -/
private theorem whnfAppI_noIota {mi : CheckMode} {fe : FEnv} {lv : Nat} {d : Nat}
    {h : Expr} (hh : isStuckHeadC h = true) :
    ∀ (args : List Expr) (v : Expr), v.getAppFn = h →
      (∀ k, iotaTargetF fe h = some k →
        k ≤ iotaNumArgs v 0 ∨ iotaNumArgs v 0 + args.length < k) →
      whnfAppI mi fe eager lv d v args = pure (.done (Expr.mkAppN v args))
  | [], v, _, _ => by rw [whnfAppI.eq_def]; rfl
  | a :: rest, v, hv, hk => by
    have hoff : iotaArityOk fe (.app v a) = false := by
      cases ho : iotaArityOk fe (.app v a) with
      | false => rfl
      | true =>
        rw [iotaArityOk_eq_target] at ho
        rw [show (Expr.app v a).getAppFn = v.getAppFn from rfl, hv, iotaNumArgs,
          iotaNumArgs_add v 1] at ho
        rcases hk _ ho with h₁ | h₁ <;> (try simp only [List.length_cons] at h₁) <;> omega
    rw [whnfAppI_cons_ne_lam (ne_lam_of_getAppFn hv hh), hoff]
    simp only [Bool.false_eq_true, ite_false, pure_bind]
    refine whnfAppI_noIota hh rest (.app v a) hv ?_
    intro k hk'
    rw [iotaNumArgs, iotaNumArgs_add v 1]
    rcases hk k hk' with h₁ | h₁
    · left; omega
    · right; simp only [List.length_cons] at h₁; omega

/-- Up to the ι target the spine loop tries ι there once, and then only rebuilds. -/
private theorem whnfAppI_iota {mi : CheckMode} {fe : FEnv} {lv : Nat} {d : Nat}
    {h : Expr} (hh : isStuckHeadC h = true) {k : Nat} (htk : iotaTargetF fe h = some k) :
    ∀ (args : List Expr) (v : Expr), v.getAppFn = h →
      iotaNumArgs v 0 < k → k ≤ iotaNumArgs v 0 + args.length →
      whnfAppI mi fe eager lv d v args =
        (iotaRecI mi fe eager lv d (Expr.mkAppN v (args.take (k - iotaNumArgs v 0))) >>=
          fun o => match o with
            | some e'' => do
              let e' ← mkAppNM e'' (args.drop (k - iotaNumArgs v 0))
              pure (.cont e')
            | none => pure (.done (Expr.mkAppN v args)))
  | [], v, _, h₁, h₂ => by simp only [List.length_nil] at h₂; omega
  | a :: rest, v, hv, h₁, h₂ => by
    have hnum : iotaNumArgs (.app v a) 0 = iotaNumArgs v 0 + 1 := by
      rw [iotaNumArgs, iotaNumArgs_add v 1]
    rw [whnfAppI_cons_ne_lam (ne_lam_of_getAppFn hv hh)]
    by_cases hat : k = iotaNumArgs v 0 + 1
    · have hon : iotaArityOk fe (.app v a) = true := by
        rw [iotaArityOk_eq_target, show (Expr.app v a).getAppFn = v.getAppFn from rfl, hv,
          hnum, htk, hat]
      rw [hon, ite_eq_left rfl]
      have hkm : k - iotaNumArgs v 0 = 1 := by omega
      rw [hkm]
      simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
      congr 1
      funext o
      cases o with
      | some e'' => rfl
      | none =>
        refine whnfAppI_noIota hh rest (.app v a) hv ?_
        intro k' hk'
        rw [htk] at hk'; cases hk'
        left; omega
    · have hoff : iotaArityOk fe (.app v a) = false := by
        cases ho : iotaArityOk fe (.app v a) with
        | false => rfl
        | true =>
          rw [iotaArityOk_eq_target, show (Expr.app v a).getAppFn = v.getAppFn from rfl, hv,
            hnum, htk] at ho
          cases ho; omega
      rw [hoff]
      simp only [Bool.false_eq_true, ite_false, pure_bind]
      have hkm : k - iotaNumArgs v 0 = (k - iotaNumArgs (.app v a) 0) + 1 := by
        rw [hnum]; omega
      rw [whnfAppI_iota hh htk rest (.app v a) hv (by omega) (by simp only [List.length_cons] at h₂; omega), hkm]
      rfl

/-- The stuck arm is the spine loop at its own head. -/
theorem whnfStuckI_mkAppN {mi : CheckMode} {fe : FEnv} {lv : Nat} {d : Nat}
    {h : Expr} (hh : isStuckHeadC h = true) (args : List Expr) :
    whnfStuckI mi fe eager lv d h (Expr.mkAppN h args) = whnfAppI mi fe eager lv d h args := by
  have h0 := isStuckHeadC_iotaNumArgs hh
  have hfn := isStuckHeadC_getAppFn hh
  rw [whnfStuckI.eq_def]
  cases htk : iotaTargetF fe h with
  | none =>
    dsimp only
    refine (whnfAppI_noIota hh args h hfn ?_).symm
    intro k hk; rw [htk] at hk; cases hk
  | some k =>
    dsimp only
    rw [iotaNumArgs_mkAppN, h0]
    by_cases hkn : k ≤ 0 + args.length
    · rw [ite_eq_left hkn, getAppArgsC_spec, Expr.getAppArgs_mkAppN, isStuckHeadC_getAppArgs hh,
        List.nil_append, whnfAppI_iota hh htk args h hfn (by rw [h0]; exact iotaTargetF_pos htk)
          (by rw [h0]; exact hkn), h0, Nat.sub_zero]
      rfl
    · rw [ite_eq_right hkn]
      refine (whnfAppI_noIota hh args h hfn ?_).symm
      intro k' hk'; rw [htk] at hk'; cases hk'
      right; omega

/-- The stuck arm at a spine's own head is the spine loop on its arguments. -/
theorem whnfStuckI_eq {mi : CheckMode} {fe : FEnv} {lv : Nat} {d : Nat}
    {e : Expr} (hh : isStuckHeadC e.getAppFn = true) :
    whnfStuckI mi fe eager lv d e.getAppFn e = whnfAppI mi fe eager lv d e.getAppFn (Expr.getAppArgsC e) := by
  have := whnfStuckI_mkAppN (eager := eager) (mi := mi) (fe := fe) (lv := lv) (d := d) hh e.getAppArgs
  rwa [Expr.mkAppN_getApp, ← getAppArgsC_spec] at this

/-- The projection rule simulates its specification. -/
theorem reduceProjCoreC_spec (ih : SSimC mode eager env f) {d : Nat} {sn : Name} {ip : Nat}
    {i : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄
      reduceProjCoreI mode (mkFEnv env) eager f d sn ip i
    ⦃fun o s' => CSOK mode eager env s' ∧
      Runs (reduceProjCore mode (fueledFns mode eager env) env d sn ip i) o ∧ OptWS d o; ⊤⦄ := by
  sym only [conleche_grind, reduceProjCore, mkFEnv_findProj?, projCertAtF_mkFEnv] =>
    vcgen [reduceProjCoreI.eq_def, projLitToCtorC_spec ih] <;> finish

/-! ### The argument loop, by `vcgen` and `grind`

Each walk below is `sym only [conleche_grind, …] => vcgen […] <;> finish`
(`ConLeche/Verify/Cached/Grind.lean`).  The cached loops match their
head on `.lam`, and the equation compiler states their `a :: rest` step
as one equation per arm, the fall-through one conditional, which `vcgen`
skips; the unconditional `eq_def` unfolds them instead (`whnfAppI`'s by
`rw` before `sym`, so that `iotaArityOk_guard` can discharge the ι arity
guard: `vcgen` splits an `ite` before it tries an equation about it).
`vcgen` splits the `match`
and hands each arm its fall-through hypothesis; the pure mirrors'
own equation lemmas (`betaPeelW.eq_*`, `whnfAppW.eq_*`, the fall-through
one included) go into the `sym` list, and `grind` discharges the
fall-through premise from the arm's hypothesis. -/

/-- The peel step's scope: a binder peeled off a well-scoped
instantiated lambda, instantiated with one more well-scoped argument. -/
theorem wscoped_peel {d : Nat} {ty body a : Expr} {acc : List Expr}
    (hw : Expr.WScoped d ((Expr.lam ty body).instantiateList acc)) (ha : Expr.WScoped d a) :
    Expr.WScoped d (body.instantiateList (a :: acc)) := by
  rw [instList_lam, Expr.WScoped] at hw
  rw [Expr.instantiateList_cons]
  exact Expr.WScoped.instantiate1_gen ha 0 hw.2
grind_pattern [conleche_grind] wscoped_peel =>
  Expr.WScoped d ((Expr.lam ty body).instantiateList acc), body.instantiateList (a :: acc)

/-- The peel loop simulates its pure mirror. -/
theorem betaPeelC_spec (lv : Nat) {d : Nat} :
    ∀ {args : List Expr} {t : Expr} {acc : List Expr} {s₀ : CState}, CSOK mode eager env s₀ →
      Expr.WScoped d (t.instantiateList acc) → AllWS d args →
      ⦃fun s => s = s₀⦄ betaPeelI mode (mkFEnv env) eager lv d t acc args
      ⦃fun v s' => CSOK mode eager env s' ∧
          Runs (betaPeelW mode (fueledFns mode eager env) env d t acc args) v ∧ StepWS d v; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ hs _ _
    sym only [conleche_grind, betaPeelW.eq_1] =>
      vcgen [betaPeelI.eq_def, instListM_spec hs] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ hs _ _
    sym only [conleche_grind, betaPeelW.eq_2, betaPeelW.eq_3] =>
      vcgen [betaPeelI.eq_def, mkAppNM, instListM_spec hs, ihr] <;> finish

/-- The bulk-beta argument loop simulates its pure mirror. -/
theorem whnfAppC_spec (ih : SSimC .verified eager env f)
    (henv : EnvWF env) {d : Nat} :
    ∀ {args : List Expr} {v : Expr} {s₀ : CState}, CSOK .verified eager env s₀ →
      Expr.WScoped d v → AllWS d args →
      ⦃fun s => s = s₀⦄ whnfAppI .verified (mkFEnv env) eager f d v args
      ⦃fun w s' => CSOK .verified eager env s' ∧
          Runs (whnfAppW .verified (fueledFns .verified eager env) env d v args) w ∧ StepWS d w; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ _ _
    sym only [conleche_grind, whnfAppW.eq_1] =>
      vcgen [whnfAppI.eq_def] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ _ _
    rw [whnfAppI.eq_def]; simp only [iotaArityOk_guard]
    sym only [conleche_grind, whnfAppW.eq_2, whnfAppW.eq_3] =>
      vcgen [mkAppNM, iotaRecC_spec ih henv,
        betaPeelC_spec (mode := .verified) f, ihr] <;> finish

/-- A stuck head is its own head normal form. -/
theorem Runs.whnfCore_stuckHead {c : Bool} {d : Nat} {h : Expr} (hh : isStuckHeadC h = true) :
    Runs ((fueledFns .verified eager env).whnfCore c d h) h :=
  ⟨1, by cases h <;> first | rfl | exact nomatch hh⟩

/-- The stuck arm simulates the mirror's application step: the head is its own head
normal form, and the stuck arm is the spine loop (`whnfStuckI_eq`). -/
theorem whnfStuckC_spec (ih : SSimC .verified eager env f)
    (henv : EnvWF env) {c : Bool} {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK .verified eager env s₀) (hw : Expr.WScoped d i)
    (hh : isStuckHeadC i.getAppFn = true) :
    ⦃fun s => s = s₀⦄
      whnfStuckI .verified (mkFEnv env) eager f d
        i.getAppFn i
    ⦃fun v s' => CSOK .verified eager env s' ∧
      Runs ((fueledFns .verified eager env).whnfCore c d i.getAppFn >>= fun v =>
        whnfAppW .verified (fueledFns .verified eager env) env d v i.getAppArgs) v ∧
      StepWS d v; ⊤⦄ := by
  rw [whnfStuckI_eq hh]
  sym only [conleche_grind, Runs.whnfCore_stuckHead (eager := eager) (env := env) (c := c)
      (d := d) hh] =>
    vcgen [whnfAppC_spec ih henv] <;> finish

/-- One head-normalization step simulates its pure mirror. -/
theorem whnfCoreStepC_spec (ih : SSimC .verified eager env f)
    (henv : EnvWF env) {c : Bool} {d : Nat} {i : Expr} {s₀ : CState} (hs : CSOK .verified eager env s₀)
    (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄
      whnfCoreStepI .verified (mkFEnv env) eager f c d i.getAppFn i
    ⦃fun v s' => CSOK .verified eager env s' ∧
      Runs (whnfCoreStepW .verified (fueledFns .verified eager env) env c d i) v ∧ StepWS d v; ⊤⦄ := by
  sym only [conleche_grind, whnfCoreStepW] =>
    vcgen [whnfCoreStepI.eq_def, inst1M_spec hs, ih.whnfCore_spec, ih.whnf_spec,
      reduceProjCoreC_spec ih, whnfAppC_spec ih henv, whnfStuckC_spec (c := c) ih henv] <;> finish

/-! ### The head-normalization loop and its memo policy

The cached loop (`whnfCoreLoopI`) looks every key up and stores the
keys of a chain at its end.  Its answer is stated against the chained
`whnfCore` directly: a hit is the backed `CSOK` clause, an answering
step is `whnfCore_of_stepW_done` and a continuing one
`whnfCore_of_stepW_cont`.  The keys waiting for the answer satisfy
`PendOK`: each answers what the current term answers. -/

/-- An easy case is its own whnfCore answer (`whnfCoreBody`'s value arms). -/
theorem Runs.whnfCore_easy {c : Bool} {d : Nat} {i : Expr} (h : whnfCoreEasy i = true) :
    Runs ((fueledFns mode eager env).whnfCore c d i) i :=
  ⟨1, by cases i <;> first | rfl | exact nomatch h⟩
grind_pattern [conleche_grind] Runs.whnfCore_easy =>
  Runs ((fueledFns mode eager env).whnfCore c d i) i

/-- A full whnfCore memo hit answers the fueled whnfCore, well scoped. -/
theorem CSOK.whnfCore_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hl : s.whnfCoreC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode eager env).whnfCore false d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.whnfCoreC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, whnfCore_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.whnfCore_hit =>
  CSOK mode eager env s, s.whnfCoreC[i]?, Runs ((fueledFns mode eager env).whnfCore false d i) r

/-- A cheap whnfCore memo hit answers the fueled cheap whnfCore. -/
theorem CSOK.whnfCoreCheap_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hl : s.whnfCoreCheapC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode eager env).whnfCore true d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.whnfCoreCheapC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, whnfCore_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.whnfCoreCheap_hit =>
  CSOK mode eager env s, s.whnfCoreCheapC[i]?, Runs ((fueledFns mode eager env).whnfCore true d i) r

/-- A continuing step: the term answers what its continuation answers. -/
theorem Runs.whnfCore_of_cont {c : Bool} {d : Nat} {e e' v : Expr}
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e'))
    (hk : Runs ((fueledFns mode eager env).whnfCore c d e') v) :
    Runs ((fueledFns mode eager env).whnfCore c d e) v := by
  obtain ⟨F, hF⟩ := hs
  obtain ⟨G, hG⟩ := hk
  exact whnfCore_of_stepW_cont hF hG
grind_pattern [conleche_grind] Runs.whnfCore_of_cont =>
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e'),
  Runs ((fueledFns mode eager env).whnfCore c d e') v

/-- An answering step: its answer is the term's. -/
theorem Runs.whnfCore_of_done {c : Bool} {d : Nat} {e v : Expr}
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v)) :
    Runs ((fueledFns mode eager env).whnfCore c d e) v := by
  obtain ⟨F, hF⟩ := hs
  exact whnfCore_of_stepW_done hF
grind_pattern [conleche_grind] Runs.whnfCore_of_done =>
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v),
  (fueledFns mode eager env).whnfCore c d e

/-- A lambda or a stuck head is its own head normal form in both modes. -/
private theorem whnfCore_cheapHead {c : Bool} {d : Nat} {h : Expr}
    (hh : (match h with | .lam .. => true | h => isStuckHeadC h) = true) :
    (fueledFns mode eager env).whnfCore true d h = (fueledFns mode eager env).whnfCore c d h := by
  apply Subtype.ext; funext F
  cases F with
  | zero => rfl
  | succ F => cases h <;> first | rfl | exact nomatch hh

/-- A step the two modes take alike (`whnfCoreCheapSafeC`) is the same step
in the cheap mode. -/
theorem whnfCoreStepW_cheap {c : Bool} {d : Nat} {e : Expr}
    (h : whnfCoreCheapSafeC e.getAppFn e = true) :
    whnfCoreStepW mode (fueledFns mode eager env) env true d e
      = whnfCoreStepW mode (fueledFns mode eager env) env c d e := by
  cases e with
  | app f a =>
    simp only [whnfCoreStepW]
    rw [whnfCore_cheapHead (c := c) h]
  | letE _ _ _ => rfl
  | _ => exact nomatch h

/-- The keys pending in the loop: each, well scoped, answers what `e`
answers (in the mode `c`). -/
@[expose] def PendOK (mode : CheckMode) (eager : Bool) (env : Env) (c : Bool) (d : Nat)
    (pend : List Expr) (e : Expr) : Prop :=
  ∀ k ∈ pend, Expr.WScoped d k ∧ ∀ v, Runs ((fueledFns mode eager env).whnfCore c d e) v →
    Runs ((fueledFns mode eager env).whnfCore c d k) v

@[conleche_grind] theorem PendOK.nil {c : Bool} {d : Nat} {e : Expr} :
    PendOK mode eager env c d [] e := by
  intro k hk; exact nomatch hk

/-- The term itself joins its pending keys. -/
theorem PendOK.self {c : Bool} {d : Nat} {pend : List Expr} {e : Expr}
    (hp : PendOK mode eager env c d pend e) (hw : Expr.WScoped d e) :
    PendOK mode eager env c d (e :: pend) e := by
  intro k hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact ⟨hw, fun _ h => h⟩
  · exact hp k hk
grind_pattern [conleche_grind] PendOK.self =>
  PendOK mode eager env c d pend e, PendOK mode eager env c d (e :: pend) e

/-- Past a continuing step, the pending keys answer what the
continuation answers. -/
theorem PendOK.cont {c : Bool} {d : Nat} {pend : List Expr} {e e' : Expr}
    (hp : PendOK mode eager env c d pend e)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')) :
    PendOK mode eager env c d pend e' :=
  fun k hk => ⟨(hp k hk).1, fun _ h => (hp k hk).2 _ (Runs.whnfCore_of_cont hs h)⟩
grind_pattern [conleche_grind] PendOK.cont =>
  PendOK mode eager env c d pend e,
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e'),
  PendOK mode eager env c d pend e'

/-- The cheap-mode keys past a step the two modes take alike. -/
theorem PendOK.contCheap {c : Bool} {d : Nat} {pend : List Expr} {e e' : Expr}
    (hp : PendOK mode eager env true d pend e) (hsafe : whnfCoreCheapSafeC e.getAppFn e = true)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')) :
    PendOK mode eager env true d pend e' := by
  rw [← whnfCoreStepW_cheap hsafe] at hs
  exact PendOK.cont hp hs
grind_pattern [conleche_grind] PendOK.contCheap =>
  PendOK mode eager env true d pend e,
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e'),
  PendOK mode eager env true d pend e'

/-- An answering step the two modes take alike answers the cheap mode too. -/
theorem Runs.whnfCore_of_doneCheap {c : Bool} {d : Nat} {e v : Expr}
    (hsafe : whnfCoreCheapSafeC e.getAppFn e = true)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v)) :
    Runs ((fueledFns mode eager env).whnfCore true d e) v := by
  rw [← whnfCoreStepW_cheap hsafe] at hs
  exact Runs.whnfCore_of_done hs
grind_pattern [conleche_grind] Runs.whnfCore_of_doneCheap =>
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v),
  (fueledFns mode eager env).whnfCore true d e

/-- A memo whose entries are backed keeps them so under inserting
backed keys, one answer for all. -/
private theorem foldl_insert_backed {P : Expr → Expr → Prop} {v : Expr} :
    ∀ {pend : List Expr} {m : Std.HashMap Expr Expr}, (∀ k w, m[k]? = some w → P k w) →
      (∀ k ∈ pend, P k v) →
      ∀ k w, (pend.foldl (fun m k => m.insert k v) m)[k]? = some w → P k w
  | [], _, hm, _ => hm
  | k :: rest, _, hm, hp =>
    foldl_insert_backed (pend := rest) (HashMap.insert_backed hm (hp k (.head _)))
      (fun k' hk' => hp k' (.tail _ hk'))

/-- A pending key, answered by `v` at `e`, is a backed memo entry. -/
private theorem PendOK.backed (henv : EnvWF env) {c : Bool} {d : Nat} {pend : List Expr}
    {e v : Expr} (hp : PendOK mode eager env c d pend e)
    (hv : Runs ((fueledFns mode eager env).whnfCore c d e) v) :
    ∀ k ∈ pend, ∃ F, ∀ d', (Expr.wscopedB d' k) = true →
      whnfCore mode eager env F d' k c = .ok v := by
  intro k hk
  obtain ⟨hw, hrun⟩ := hp k hk
  obtain ⟨F, hF⟩ := hrun v hv
  exact ⟨F, fun d' hd' => by rw [whnfCore_depth_inv henv F hd' hw.to_wscopedB]; exact hF⟩

/-- A finished chain's store keeps the invariant: its full keys answer
`v` in the full mode, its cheap keys in the cheap mode. -/
theorem CSOK.chainStored (henv : EnvWF env) {s : CState} {d : Nat} {pend pendC : List Expr}
    {e v : Expr} (hs : CSOK mode eager env s)
    (hp : PendOK mode eager env false d pend e)
    (hv : Runs ((fueledFns mode eager env).whnfCore false d e) v)
    (hpc : PendOK mode eager env true d pendC e)
    (hvc : Runs ((fueledFns mode eager env).whnfCore true d e) v) :
    CSOK mode eager env (storeChain s pend pendC v) :=
  { hs with
    whnfCoreC := foldl_insert_backed hs.whnfCoreC (hp.backed henv hv)
    whnfCoreCheapC := foldl_insert_backed hs.whnfCoreCheapC (hpc.backed henv hvc) }
grind_pattern [conleche_grind] CSOK.chainStored =>
  CSOK mode eager env s, PendOK mode eager env false d pend e,
  PendOK mode eager env true d pendC e, storeChain s pend pendC v

/-- A store with no cheap keys (the chain took a step the modes take
differently, or ended at a hit). -/
theorem CSOK.chainStored_nil (henv : EnvWF env) {s : CState} {d : Nat} {pend : List Expr}
    {e v : Expr} (hs : CSOK mode eager env s)
    (hp : PendOK mode eager env false d pend e)
    (hv : Runs ((fueledFns mode eager env).whnfCore false d e) v) :
    CSOK mode eager env (storeChain s pend [] v) :=
  { hs with
    whnfCoreC := foldl_insert_backed hs.whnfCoreC (hp.backed henv hv)
    whnfCoreCheapC := hs.whnfCoreCheapC }
grind_pattern [conleche_grind] CSOK.chainStored_nil =>
  CSOK mode eager env s, PendOK mode eager env false d pend e, storeChain s pend [] v

/-- The loop's continuing arm: the keys it passes on, the term joining
them where it is stored, answer what the continuation answers. -/
theorem PendOK.push {b : Bool} {c : Bool} {d : Nat} {pend : List Expr}
    {e e' : Expr} (hp : PendOK mode eager env c d pend e) (hw : Expr.WScoped d e)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')) :
    PendOK mode eager env c d (pushKey b e pend) e' := by
  unfold pushKey
  split
  · exact PendOK.cont (hp.self hw) hs
  · exact PendOK.cont hp hs
grind_pattern [conleche_grind] PendOK.push =>
  PendOK mode eager env c d (pushKey b e pend) e',
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')

/-- The loop's continuing arm, cheap keys: kept past a step the two
modes take alike, dropped past any other. -/
theorem PendOK.pushCheap {b : Bool} {c : Bool} {d : Nat} {pend : List Expr}
    {e e' : Expr} (hp : PendOK mode eager env true d pend e) (hw : Expr.WScoped d e)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')) :
    PendOK mode eager env true d (pushCheapKey (whnfCoreCheapSafeC e.getAppFn e) b e pend) e' := by
  unfold pushCheapKey pushKey
  split
  · rename_i hsafe
    split
    · exact PendOK.contCheap (hp.self hw) hsafe hs
    · exact PendOK.contCheap hp hsafe hs
  · exact PendOK.nil
grind_pattern [conleche_grind] PendOK.pushCheap =>
  PendOK mode eager env true d (pushCheapKey (whnfCoreCheapSafeC e.getAppFn e) b e pend) e',
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')

/-- The loop's answering arm in the full mode: the chain's keys, the term
joining them where it is stored, stored with the answer. -/
theorem CSOK.chainStoredDone (henv : EnvWF env) {b c : Bool} {s : CState}
    {d : Nat} {pend pendC : List Expr} {e v : Expr} (hs : CSOK mode eager env s)
    (hc : c = false)
    (hp : PendOK mode eager env c d pend e) (hpc : PendOK mode eager env true d pendC e)
    (hw : Expr.WScoped d e)
    (hst : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v)) :
    CSOK mode eager env (storeChain s (pushKey b e pend) (pushCheapKey (whnfCoreCheapSafeC e.getAppFn e) b e pendC) v) := by
  subst hc
  have hv := Runs.whnfCore_of_done hst
  have hp' : PendOK mode eager env false d (pushKey b e pend) e := by
    unfold pushKey
    split
    · exact hp.self hw
    · exact hp
  unfold pushCheapKey
  split
  · rename_i hsafe
    have hvc := Runs.whnfCore_of_doneCheap hsafe hst
    refine CSOK.chainStored henv hs hp' hv ?_ hvc
    unfold pushKey
    split
    · exact hpc.self hw
    · exact hpc
  · exact CSOK.chainStored_nil henv hs hp' hv
grind_pattern [conleche_grind] CSOK.chainStoredDone =>
  storeChain s (pushKey b e pend) (pushCheapKey (whnfCoreCheapSafeC e.getAppFn e) b e pendC) v,
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v)

/-- The head-normalization *loop* answers the chained `whnfCore` of its
term, by induction on the shared step budget (task #106); a step's
outcome is the same on both sides, a continuation re-enters the loop
(task #342 R2), and the memo is looked up at every key and written with
the chain's keys at its end. -/
theorem whnfCoreLoopC_spec (ih : SSimC .verified eager env f)
    (henv : EnvWF env) {c : Bool} {d : Nat} (n : Nat) :
    ∀ {pend pendC : List Expr} {i : Expr} {s₀ : CState}, CSOK .verified eager env s₀ →
      Expr.WScoped d i → PendOK .verified eager env c d pend i →
      PendOK .verified eager env true d pendC i →
      ⦃fun s => s = s₀⦄
        whnfCoreLoopI .verified (mkFEnv env) eager f c d n pend pendC i
      ⦃fun v s' => CSOK .verified eager env s' ∧
        Runs ((fueledFns .verified eager env).whnfCore c d i) v ∧
        Expr.WScoped d v; ⊤⦄ := by
  induction n with
  | zero =>
    intro pend pendC i s₀ hs hw hp hpc
    sym only [conleche_grind] => vcgen [whnfCoreLoopI.eq_def] <;> finish
  | succ n ihn =>
    intro pend pendC i s₀ hs hw hp hpc
    sym only [conleche_grind, CSOK.chainStored henv, CSOK.chainStored_nil henv,
        CSOK.chainStoredDone henv, CSOK.whnfCore_hit henv, CSOK.whnfCoreCheap_hit henv] =>
      vcgen [whnfCoreLoopI.eq_def, storeChainI, whnfCoreLookupI,
        whnfCoreStepC_spec ih henv, ihn] <;> finish

/-- The cached head-normalization body answers the chained `whnfCore`:
the loop with no key pending. -/
theorem whnfCoreBodyC_spec (ih : SSimC .verified eager env f)
    (henv : EnvWF env) (c : Bool) :
    BodySpec .verified eager env (whnfCoreBodyI .verified (mkFEnv env) eager f c)
      (fun d i => (fueledFns .verified eager env).whnfCore c d i) := by
  intro s₀ d i hs hw
  sym only [conleche_grind] =>
    vcgen [whnfCoreBodyI.eq_def, whnfCoreLoopC_spec ih henv] <;> finish

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- The reduction loop simulates its specification, by induction on the
shared step budget (task #106). -/
theorem whnfLoopC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} (n : Nat) :
    ∀ {i : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d i →
      ⦃fun s => s = s₀⦄ whnfLoopI mode (mkFEnv env) eager f d n i
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (whnfLoop (fueledFns mode eager env) env d n i) v ∧ Expr.WScoped d v; ⊤⦄ := by
  induction n with
  | zero =>
    intro i s₀ hs hw
    sym only [conleche_grind] => vcgen [whnfLoopI.eq_def] <;> finish
  | succ n ihn =>
    intro i s₀ hs hw
    sym only [conleche_grind, whnfLoop, whnfStep, unfoldDefinition_WScoped henv] =>
      vcgen [whnfLoopI.eq_def, ih.whnfCore_spec, reduceNatC_spec ih,
        unfoldDefinitionC_spec (mode := mode) (eager := eager) (env := env), ihn] <;> finish

theorem whnfBodyC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) :
    BodySpec mode eager env (whnfBodyI mode (mkFEnv env) eager f)
      (whnfBody (fueledFns mode eager env) env) := by
  intro s₀ d i hs hw
  sym only [conleche_grind, whnfBody] =>
    vcgen [whnfBodyI.eq_def, whnfLoopC_spec ih henv] <;> finish

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-! ### The io view's entry points

The io-grade walks call the knot's io entry point (`inferI … true`); their
pure side runs on `CoreFns.ioView` of the fueled family, read through
`CoreFns.ioView_*`, so the specs whose pure side is at the view are
restated here. -/

theorem ensureSortIOC_spec (ih : SSimC mode eager env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ ensureSortI mode (mkFEnv env) eager f d i
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (ensureSort (CoreFns.ioView (fueledFns mode eager env)) env d i) v; ⊤⦄ :=
  ensureSortC_spec ih hs hw

theorem CoreFns.ioView_whnf {m : Type → Type} (r : CoreFns m) (d : Nat) (e : Expr) :
    (CoreFns.ioView r).whnf d e = r.whnf d e := rfl

theorem CoreFns.ioView_infer {m : Type → Type} (r : CoreFns m) (d : Nat) (e : Expr) :
    (CoreFns.ioView r).infer d e = r.inferIO d e := rfl

/-! ### The inference spine loops

As for the argument loop: the cached loops by their `eq_def`, the pure
mirrors' own equation lemmas in the `sym` list. -/

/-- The application-inference spine loop simulates its pure mirror. -/
theorem inferSpineC_spec (ih : SSimC mode eager env f) {d : Nat} :
    ∀ {args : List Expr} {ty : Expr} {acc : Array Expr} {s₀ : CState}, CSOK mode eager env s₀ →
      Expr.WScoped d (ty.instantiateList acc.toList.reverse) → AllWS d args →
      ⦃fun s => s = s₀⦄ inferSpineI mode (mkFEnv env) eager f false d ty acc args
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (inferSpine (fueledFns mode eager env) d ty acc.toList.reverse args) v ∧
        Expr.WScoped d v; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ hs _ _
    sym only [conleche_grind, inferSpine.eq_1] =>
      vcgen [inferSpineI.eq_def, instListRevM_spec hs] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ _ _ _
    sym only [conleche_grind, inferSpine.eq_2, inferSpine.eq_3, toListRev_singleton] =>
      vcgen [inferSpineI.eq_def, instListRevM_spec (mode := mode) (eager := eager) (env := env),
          ih.infer_spec,
        ih.whnf_spec, defeqArgC_spec ih, ihr] <;> finish

/-- The io-grade spine loop simulates its pure mirror. -/
theorem inferSpineIOC_spec (ih : SSimC mode eager env f) {d : Nat} :
    ∀ {args : List Expr} {ty : Expr} {acc : Array Expr} {s₀ : CState}, CSOK mode eager env s₀ →
      Expr.WScoped d (ty.instantiateList acc.toList.reverse) → AllWS d args →
      ⦃fun s => s = s₀⦄
        inferSpineIOI mode (mkFEnv env) eager f d ty acc
            args
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (inferSpineIO (fueledFns mode eager env) d ty acc.toList.reverse args) v ∧
        Expr.WScoped d v; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ hs _ _
    sym only [conleche_grind, inferSpineIO.eq_1] =>
      vcgen [inferSpineIOI.eq_def, instListRevM_spec hs] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ _ _ _
    sym only [conleche_grind, inferSpineIO.eq_2, inferSpineIO.eq_3, toListRev_singleton] =>
      vcgen [inferSpineIOI.eq_def, instListRevM_spec (mode := mode) (eager := eager) (env := env),
        ih.whnf_spec, ihr] <;> finish

/-! ### The inference bodies -/

/-- A free variable's type is scoped at the variable's depth, so at any
depth above it. -/
theorem wscoped_fvar_ty {d idx : Nat} {ty : Expr} (h : Expr.WScoped d (.fvar idx ty)) :
    Expr.WScoped d ty := by
  rw [Expr.WScoped] at h
  exact Expr.WScoped.mono (Nat.le_of_lt h.1) h.2
grind_pattern [conleche_grind] wscoped_fvar_ty => Expr.WScoped d (.fvar idx ty)

/-- A stored constant's type is closed. -/
theorem EnvWF.constTy_closed (henv : EnvWF env) {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.toConstantVal.type.hasFvar = false :=
  (henv.consts _ (Env.find?_mem h)).1

/-- A projection's type is well scoped at its subject's scope. -/
theorem wscoped_typeAt (henv : EnvWF env) {T : Name} {i : Nat} {entry : ProjEntry}
    (hf : env.findProj? T i = some entry) (us : List Level) {d : Nat} {targs : List Expr}
    (hlen : targs.length = entry.numParams) {pe : Expr} (hargs : AllWS d targs)
    (hpe : Expr.WScoped d pe) : Expr.WScoped d (entry.typeAt us targs pe) :=
  projEntry_typeAt_WScoped henv hf us hlen hargs hpe

/-- The cached spine walk's answer is the chained application clause's
(`inferSpine_sound_body`). -/
theorem Runs.inferBody_app {d : Nat} {g a tf v : Expr}
    (h₁ : Runs ((fueledFns mode eager env).infer d (Expr.app g a).getAppFn) tf)
    (h₂ : Runs (inferSpine (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) v) :
    Runs (inferBody (fueledFns mode eager env) env d (.app g a)) v := by
  obtain ⟨F, hF⟩ := Runs.bind (f := fun tf =>
    inferSpine (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) h₁ h₂
  exact inferSpine_sound_body d g a v F hF
grind_pattern [conleche_grind] Runs.inferBody_app =>
  Runs (inferSpine (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) v,
  inferBody (fueledFns mode eager env) env d (.app g a)

/-- The ∀-telescope loop against `inferBody`'s ∀ tail, as a triple. -/
theorem inferPisC_tail_spec (ih : SSimC mode eager env f) {d fuel : Nat} {b ty : Expr} {u : Level}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hwty : Expr.WScoped d ty)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ inferPisI mode (mkFEnv env) eager f false d fuel b 1 #[.fvar d ty] [u]
    ⦃fun r s' => CSOK mode eager env s' ∧
      Runs (do
        let v ← ensureSort (fueledFns mode eager env) env (d + 1)
          (← (fueledFns mode eager env).infer (d + 1) (b.instantiate1 (.fvar d ty)))
        pure (Expr.sort (.imax u v))) r ∧ Expr.WScoped d r; ⊤⦄ :=
  (inferPisC_tail_sim ih hs rfl rfl rfl hwty hwb).triple relEC_inv

/-- The λ-telescope loop against `inferBody`'s λ tail, as a triple. -/
theorem inferLamsC_tail_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d fuel : Nat}
    {b ty : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀) (hwty : Expr.WScoped d ty)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ inferLamsI mode (mkFEnv env) eager f false d fuel b 1 #[.fvar d ty] [ty]
    ⦃fun r s' => CSOK mode eager env s' ∧
      Runs (do
        let bt ← (fueledFns mode eager env).infer (d + 1) (b.instantiate1 (.fvar d ty))
        pure (Expr.forallE ty (bt.abstract1 d))) r ∧ Expr.WScoped d r; ⊤⦄ :=
  (inferLamsC_tail_sim ih henv hs rfl rfl rfl hwty hwb).triple relEC_inv

/-- The rows of a projection's guard simulate their fueled original. -/
theorem checkGuardRowsC_spec (ih : SSimC mode eager env f) (guardSort : Level) :
    ∀ {rows : List (Nat × Expr)} {s₀ : CState}, CSOK mode eager env s₀ → GuardRowsWS rows →
      ⦃fun s => s = s₀⦄ checkGuardRowsI mode (mkFEnv env) eager f
        guardSort rows
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (checkGuardRows (fueledFns mode eager env).inferIO
          (fueledFns mode eager env).whnf guardSort rows) v; ⊤⦄ := by
  intro rows
  induction rows with
  | nil =>
    intro _ _ _
    sym only [conleche_grind, checkGuardRows] =>
      vcgen [checkGuardRowsI.eq_def] <;> finish
  | cons p rest ihr =>
    obtain ⟨d, dom⟩ := p
    intro s₀ hs hw
    have hd := hw.head
    have hr := hw.tail
    sym only [conleche_grind, checkGuardRows] =>
      vcgen [checkGuardRowsI.eq_def, ih.inferIO_spec, ih.whnf_spec, ihr] <;> finish

/-- What a projection's rows lie under simulates its fueled original. -/
theorem projGuardSortC_spec (ih : SSimC mode eager env f) {cvT : ConstantVal} {caps : IndCaps}
    {us : List Level} {s₀ : CState} (hcl : cvT.type.hasFvar = false)
    (hs : CSOK mode eager env s₀) :
    ⦃fun s => s = s₀⦄ projGuardSortI mode (mkFEnv env) eager f cvT caps us
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (projGuardSort (fueledFns mode eager env).whnf cvT caps us) v; ⊤⦄ := by
  have hw : Expr.WScoped 0 (cvT.type.instantiateLevelParams cvT.levelParams us) :=
    Expr.WScoped.of_not_hasFvar (by rw [hasFvar_instantiateLevelParams]; exact hcl)
  sym only [conleche_grind, projGuardSort] =>
    vcgen [projGuardSortI.eq_def, instLevelParamsM, formerSortLoopC_spec ih] <;> finish

/-- The cached guard rows are the kernel's (task #497). -/
theorem projGuardRowsGoC_eq :
    ∀ (k d : Nat) (e : Expr), projGuardRowsGoC k d e = projGuardRowsGo k d e
  | 0, _, .forallE .. => rfl
  | k + 1, d, .forallE dom body => by
    simp only [projGuardRowsGoC, projGuardRowsGo, hasLooseBVarBC_spec,
      Expr.instantiate1C_spec, projGuardRowsGoC_eq k (d + 1)]
    split <;> rfl
  | 0, _, .bvar _ | 0, _, .fvar .. | 0, _, .sort _ | 0, _, .const .. | 0, _, .app ..
  | 0, _, .lam .. | 0, _, .letE .. | 0, _, .lit _ | 0, _, .proj .. => rfl
  | _ + 1, _, .bvar _ | _ + 1, _, .fvar .. | _ + 1, _, .sort _ | _ + 1, _, .const ..
  | _ + 1, _, .app .. | _ + 1, _, .lam .. | _ + 1, _, .letE .. | _ + 1, _, .lit _
  | _ + 1, _, .proj .. => rfl

/-! ### The guard's fast case (task #498, L7)

`projGuardRowsC` reads the raw field telescope through `projGuardFastC`
before it rebuilds it.  Where the fast case answers, no field before the
projected one is mentioned after it, so the specification's loop steps
over every one of them and its one row is the projected field's domain
(`projGuardFastC_rows`). -/

/-- A window the reference answers `false` for holds no loose variable. -/
theorem Expr.hasLooseBVarInP_false :
    ∀ (e : Expr) {w d i : Nat}, Expr.hasLooseBVarInP w e d = false → d ≤ i → i < d + w →
      e.hasLooseBVar i = false := by
  have cut : ∀ (e : Expr) {d i : Nat}, e.bvarB ≤ d → d ≤ i → e.hasLooseBVar i = false :=
    fun e d i h hi => Expr.hasLooseBVar_eq_false_of_bound e i (by rw [← Expr.bvarB_eq]; omega)
  intro e
  induction e with
  | bvar k =>
    intro w d i h hd hw
    by_cases hc : (Expr.bvar k).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
      simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne]
      omega
  | fvar _ _ _ => intro _ _ _ _ _ _; rfl
  | sort _ => intro _ _ _ _ _ _; rfl
  | const _ _ => intro _ _ _ _ _ _; rfl
  | lit _ => intro _ _ _ _ _ _; rfl
  | app f a ihf iha =>
    intro w d i h hd hw
    by_cases hc : (Expr.app f a).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false, Bool.or_eq_false_iff] at h
      simp only [Expr.hasLooseBVar, ihf h.1 hd hw, iha h.2 hd hw, Bool.or_false]
  | lam ty b iht ihb =>
    intro w d i h hd hw
    by_cases hc : (Expr.lam ty b).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false, Bool.or_eq_false_iff] at h
      simp only [Expr.hasLooseBVar, iht h.1 hd hw, ihb (i := i + 1) h.2 (by omega) (by omega), Bool.or_false]
  | forallE ty b iht ihb =>
    intro w d i h hd hw
    by_cases hc : (Expr.forallE ty b).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false, Bool.or_eq_false_iff] at h
      simp only [Expr.hasLooseBVar, iht h.1 hd hw, ihb (i := i + 1) h.2 (by omega) (by omega), Bool.or_false]
  | letE t v b iht ihv ihb =>
    intro w d i h hd hw
    by_cases hc : (Expr.letE t v b).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false, Bool.or_eq_false_iff] at h
      simp only [Expr.hasLooseBVar, iht h.1.1 hd hw, ihv h.1.2 hd hw,
        ihb (i := i + 1) h.2 (by omega) (by omega), Bool.or_false]
  | proj sn ix s ih =>
    intro w d i h hd hw
    by_cases hc : (Expr.proj sn ix s).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false] at h
      simp only [Expr.hasLooseBVar, ih h hd hw]

/-- The empty window holds nothing. -/
theorem Expr.hasLooseBVarInP_zero : ∀ (e : Expr) (d : Nat), Expr.hasLooseBVarInP 0 e d = false := by
  intro e
  induction e with
  | bvar k =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]
    split
    · rfl
    · simp only [Nat.add_zero, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split <;> rfl
  | app f a ihf iha =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split
    · rfl
    · simp only [ihf, iha, Bool.or_false]
  | lam ty b iht ihb =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split
    · rfl
    · simp only [iht, ihb, Bool.or_false]
  | forallE ty b iht ihb =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split
    · rfl
    · simp only [iht, ihb, Bool.or_false]
  | letE t v b iht ihv ihb =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split
    · rfl
    · simp only [iht, ihv, ihb, Bool.or_false]
  | proj _ _ s ih =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split
    · rfl
    · simp only [ih]

/-- The cached window query is its reference. -/
theorem Expr.hasLooseBVarInC_spec {d w : Nat} {e : Expr} :
    Expr.hasLooseBVarInC d w e = Expr.hasLooseBVarInP w e d := by
  unfold Expr.hasLooseBVarInC
  split
  · next hw => subst hw; exact (Expr.hasLooseBVarInP_zero e d).symm
  · split
    · next h => exact (Expr.hasLooseBVarInP_cut h).symm
    · rw [Expr.resBool_eq]

/-- Substituting free variables at and above `off` leaves an index below
it occurring as it did. -/
theorem Expr.hasLooseBVar_instantiateList_fvars_lt :
    ∀ (acc : List Expr), (∀ a ∈ acc, ∃ k t, a = .fvar k t) →
      ∀ (e : Expr) {off i : Nat}, i < off →
        (e.instantiateList acc off).hasLooseBVar i = e.hasLooseBVar i
  | [], _, e, off, _, _ => by rw [Expr.instantiateList_nil]
  | v :: vs, hacc, e, off, i, hi => by
    obtain ⟨k, t, rfl⟩ := hacc v (List.mem_cons_self ..)
    rw [Expr.instantiateList_cons,
      Expr.hasLooseBVar_instantiate1_lt (v := .fvar k t) rfl _ hi,
      Expr.hasLooseBVar_instantiateList_fvars_lt vs
        (fun a ha => hacc a (List.mem_cons_of_mem _ ha)) e (by omega)]

/-- Where the fast case answers, the telescope mentions no field before
the window's top. -/
theorem projGuardFastC_below :
    ∀ (k j : Nat) (e : Expr) {dom : Expr}, projGuardFastC k j e = some dom →
      ∀ i, i < j → e.hasLooseBVar i = false
  | 0, j, .forallE dom' b, dom, h, i, hi => by
    simp only [projGuardFastC] at h
    split at h
    · exact nomatch h
    · next hc =>
      rw [Bool.not_eq_true, Expr.hasLooseBVarInC_spec] at hc
      exact Expr.hasLooseBVarInP_false _ hc (Nat.zero_le i) (by omega)
  | k + 1, j, .forallE dom0 body, dom, h, i, hi => by
    simp only [projGuardFastC] at h
    split at h
    · exact nomatch h
    · next hc =>
      rw [Bool.not_eq_true, Expr.hasLooseBVarInC_spec] at hc
      simp only [Expr.hasLooseBVar,
        Expr.hasLooseBVarInP_false _ hc (Nat.zero_le i) (by omega),
        projGuardFastC_below k (j + 1) body h (i + 1) (by omega), Bool.or_false]
  | 0, _, .bvar _, _, h, _, _ | 0, _, .fvar .., _, h, _, _ | 0, _, .sort _, _, h, _, _
  | 0, _, .const .., _, h, _, _ | 0, _, .app .., _, h, _, _ | 0, _, .lam .., _, h, _, _
  | 0, _, .letE .., _, h, _, _ | 0, _, .lit _, _, h, _, _ | 0, _, .proj .., _, h, _, _
  | _ + 1, _, .bvar _, _, h, _, _ | _ + 1, _, .fvar .., _, h, _, _
  | _ + 1, _, .sort _, _, h, _, _ | _ + 1, _, .const .., _, h, _, _
  | _ + 1, _, .app .., _, h, _, _ | _ + 1, _, .lam .., _, h, _, _
  | _ + 1, _, .letE .., _, h, _, _ | _ + 1, _, .lit _, _, h, _, _
  | _ + 1, _, .proj .., _, h, _, _ => by simp [projGuardFastC] at h

/-- **The fast case is the loop's answer**: over the telescope with the
parameters substituted, the specification steps over every field before
the projected one and returns its domain as the one row. -/
theorem projGuardFastC_rows {acc : List Expr} (hacc : ∀ a ∈ acc, ∃ k t, a = .fvar k t) :
    ∀ (k j d : Nat) (e : Expr) {dom : Expr}, projGuardFastC k j e = some dom →
      projGuardRowsGo k d (e.instantiateList acc j)
        = some [(d + k, dom.instantiateList acc (j + k))]
  | 0, j, d, .forallE dom' b, dom, h => by
    have hd : dom' = dom := by
      simp only [projGuardFastC] at h
      split at h
      · exact nomatch h
      · exact Option.some.inj h
    subst hd
    rw [Expr.instantiateList]
    rfl
  | k + 1, j, d, .forallE dom0 body, dom, h => by
    have hb : projGuardFastC k (j + 1) body = some dom := by
      simp only [projGuardFastC] at h
      split at h
      · exact nomatch h
      · exact h
    have hu : (body.instantiateList acc (j + 1)).hasLooseBVarB 0 = false := by
      rw [Expr.hasLooseBVarB_eq,
        Expr.hasLooseBVar_instantiateList_fvars_lt acc hacc body (by omega)]
      exact projGuardFastC_below k (j + 1) body hb 0 (by omega)
    rw [Expr.instantiateList]
    have e1 : d + 1 + k = d + (k + 1) := by omega
    have e2 : j + 1 + k = j + (k + 1) := by omega
    simp only [projGuardRowsGo, hu, Bool.false_eq_true, ite_false,
      projGuardFastC_rows hacc k (j + 1) (d + 1) body hb, e1, e2]
  | 0, _, _, .bvar _, _, h | 0, _, _, .fvar .., _, h | 0, _, _, .sort _, _, h
  | 0, _, _, .const .., _, h | 0, _, _, .app .., _, h | 0, _, _, .lam .., _, h
  | 0, _, _, .letE .., _, h | 0, _, _, .lit _, _, h | 0, _, _, .proj .., _, h
  | _ + 1, _, _, .bvar _, _, h | _ + 1, _, _, .fvar .., _, h
  | _ + 1, _, _, .sort _, _, h | _ + 1, _, _, .const .., _, h
  | _ + 1, _, _, .app .., _, h | _ + 1, _, _, .lam .., _, h
  | _ + 1, _, _, .letE .., _, h | _ + 1, _, _, .lit _, _, h
  | _ + 1, _, _, .proj .., _, h => by simp [projGuardFastC] at h

/-- The cached rows where the parameters do not open: none. -/
theorem projGuardRowsC_none {nP idx : Nat} {cty : Expr}
    (h : openPisAtFvars nP cty 0 = none) : projGuardRowsC nP idx cty = none := by
  unfold projGuardRowsC
  cases hraw : openPisRawGoC [] nP cty 0 with
  | none => rfl
  | some p =>
    obtain ⟨fvs, acc, r⟩ := p
    have ho := openPisAtFvarsC_eq nP cty 0
    simp only [openPisAtFvarsC, openPisAtFvarsGoC, hraw, h] at ho
    exact nomatch ho

/-- The cached rows where the parameters open: the loop over the opened
residual. -/
theorem projGuardRowsC_some {nP idx : Nat} {cty r : Expr} {fvs : List Expr}
    (h : openPisAtFvars nP cty 0 = some (fvs, r)) :
    projGuardRowsC nP idx cty = projGuardRowsGo idx nP r := by
  unfold projGuardRowsC
  cases hraw : openPisRawGoC [] nP cty 0 with
  | none =>
    have ho := openPisAtFvarsC_eq nP cty 0
    simp only [openPisAtFvarsC, openPisAtFvarsGoC, hraw, h] at ho
    exact nomatch ho
  | some p =>
    obtain ⟨fvs', acc, R⟩ := p
    have ho := openPisAtFvarsC_eq nP cty 0
    simp only [openPisAtFvarsC, openPisAtFvarsGoC, hraw, h, Expr.instantiateListC_spec,
      Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨-, rfl⟩ := ho
    have hacc := openPisRawGoC_fvars [] nP cty 0 (by simp) hraw
    simp only
    split
    · next dom hf =>
      rw [Expr.instantiateListC_spec, projGuardFastC_rows hacc idx 0 nP R hf, Nat.zero_add]
    · rw [Expr.instantiateListC_spec, projGuardRowsGoC_eq]

/-- The rows at a guardSort simulate their fueled original. -/
theorem projRowsC_spec (ih : SSimC mode eager env f) (henv : EnvWF env)
    {entry : ProjEntry} {us : List Level} {guardSort : Level} {s₀ : CState}
    (hs : CSOK mode eager env s₀) :
    ⦃fun s => s = s₀⦄ checkProjRowsI mode (mkFEnv env) eager f
      entry us guardSort
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (match projGuardRows env.find? entry us with
        | some rows => checkGuardRows (fueledFns mode eager env).inferIO
            (fueledFns mode eager env).whnf guardSort rows
        | none => throw (.invalid "projection from a propositional structure must be a proposition"))
        v; ⊤⦄ := by
  cases hc : env.find? entry.ctor with
  | none =>
    have hp : projGuardRows env.find? entry us = none := by
      simp only [projGuardRows, hc]
    sym only [conleche_grind, constTyOf, Option.isSome_some] =>
      vcgen [checkProjRowsI.eq_def, constTyAtM_spec (mode := mode) (eager := eager) (env := env),
        checkGuardRowsC_spec ih] <;> finish
  | some ci =>
    cases ho : openPisAtFvars entry.numParams
        (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) 0 with
    | none =>
      have hp : projGuardRows env.find? entry us = none := by
        simp only [projGuardRows, hc, ho]
      have hr := projGuardRowsC_none (idx := entry.idx) ho
      sym only [conleche_grind, constTyOf, Option.isSome_some] =>
        vcgen [checkProjRowsI.eq_def, constTyAtM_spec (mode := mode) (eager := eager) (env := env),
          checkGuardRowsC_spec ih] <;> finish
    | some p =>
      obtain ⟨fvsP, r⟩ := p
      have hr := projGuardRowsC_some (idx := entry.idx) ho
      cases hg : projGuardRowsGo entry.idx entry.numParams r with
      | none =>
        have hp : projGuardRows env.find? entry us = none := by
          simp only [projGuardRows, hc, ho, hg]
        sym only [conleche_grind, constTyOf, Option.isSome_some] =>
          vcgen [checkProjRowsI.eq_def, constTyAtM_spec (mode := mode) (eager := eager) (env := env),
            checkGuardRowsC_spec ih] <;> finish
      | some rows =>
        have hp : projGuardRows env.find? entry us = some rows := by
          simp only [projGuardRows, hc, ho, hg]
        have hws : GuardRowsWS rows :=
          projGuardRows_ws (fun ci' hc' => (henv.consts _ (Env.find?_mem hc')).1) hp
        sym only [conleche_grind, constTyOf, Option.isSome_some] =>
          vcgen [checkProjRowsI.eq_def, constTyAtM_spec (mode := mode) (eager := eager) (env := env),
            checkGuardRowsC_spec ih] <;> finish

/-- A projection's guard simulates its fueled original. -/
theorem checkProjGuardC_spec (ih : SSimC mode eager env f) (henv : EnvWF env)
    {entry : ProjEntry} {us : List Level} {s₀ : CState} (hs : CSOK mode eager env s₀) :
    ⦃fun s => s = s₀⦄ checkProjGuardI mode (mkFEnv env) eager f
      entry us
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (checkProjGuard (fueledFns mode eager env).inferIO
        (fueledFns mode eager env).whnf env entry us) v; ⊤⦄ := by
  unfold checkProjGuardI checkProjGuard
  simp only [mkFEnv_find_fun]
  split
  · next cvT caps hT =>
    have hcl : cvT.type.hasFvar = false := (henv.consts _ (Env.find?_mem hT)).1
    sym only [conleche_grind] =>
      vcgen [projGuardSortC_spec ih hcl, projRowsC_spec ih henv] <;> finish
  · sym only [conleche_grind] => vcgen <;> finish

/-- `checkProjGuardC_spec` at the io views the io body runs it at. -/
theorem checkProjGuardC_specIO (ih : SSimC mode eager env f) (henv : EnvWF env)
    {entry : ProjEntry} {us : List Level} {s₀ : CState} (hs : CSOK mode eager env s₀) :
    ⦃fun s => s = s₀⦄ checkProjGuardI mode (mkFEnv env) eager f
      entry us
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (checkProjGuard (CoreFns.ioView (fueledFns mode eager env)).infer
        (CoreFns.ioView (fueledFns mode eager env)).whnf env entry us) v; ⊤⦄ :=
  checkProjGuardC_spec ih henv hs

/-- The cached inference body simulates the specification body; the
application clause through the spine walk and `inferSpine_sound_body`. -/
theorem inferBodyC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) :
    BodySpec mode eager env (inferBodyI mode (mkFEnv env) eager f false)
      (inferBody (fueledFns mode eager env) env) := by
  intro s₀ d i hs hw
  sym only [conleche_grind, inferBody, natLitStoredF_eq, strLitStoredF_eq,
      mkFEnv_findProj?, constTyOf, ProjEntry.typeAtI_eq,
      toListRev_empty, Option.isSome_some, EnvWF.constTy_closed henv, wscoped_typeAt henv] =>
    vcgen [inferBodyI.eq_def, peelFuelM, maxNatSizeM, inst1M_spec (mode := mode) (eager := eager) (env := env),
        ih.infer_spec, ih.whnf_spec, ih.defeq_spec,
      ensureSortC_spec ih, constTyAtM_spec (mode := mode) (eager := eager) (env := env),
      inferSpineC_spec ih, inferPisC_tail_spec ih, inferLamsC_tail_spec ih henv,
      checkProjGuardC_spec ih henv] <;> finish

/-- Abstracting away the top variable lowers the scope bound. -/
theorem wscoped_abstract1 {d : Nat} {e : Expr} (k : Nat) (h : Expr.WScoped (d + 1) e) :
    Expr.WScoped d (e.abstract1 d k) :=
  ConLeche.WScoped.abstract1 k h
grind_pattern [conleche_grind] wscoped_abstract1 => Expr.WScoped (d + 1) e, e.abstract1 d k

/-- The cached io spine walk's answer is the io application clause's
(`inferSpineIO_sound_body`). -/
theorem Runs.inferBodyIO_app {d : Nat} {g a tf v : Expr}
    (h₁ : Runs ((fueledFns mode eager env).inferIO d (Expr.app g a).getAppFn) tf)
    (h₂ : Runs (inferSpineIO (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) v) :
    Runs (inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env d (.app g a)) v := by
  obtain ⟨F, hF⟩ := Runs.bind (f := fun tf =>
    inferSpineIO (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) h₁ h₂
  exact inferSpineIO_sound_body d g a v F hF
grind_pattern [conleche_grind] Runs.inferBodyIO_app =>
  Runs (inferSpineIO (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) v,
  inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env d (.app g a)

/-- The io inference body's walk (task #172 B4).  The leaf and `proj`
arms are `inferBodyI`'s at the io view; the binder and `letE` arms are
the io lane's own chained clauses; the application arm is the io spine
walk (`inferSpineIOI`, no argument check) with
`inferSpineIO_sound_body`. -/
theorem inferBodyIOC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) :
    BodySpec mode eager env
      (inferBodyIOI mode (mkFEnv env) eager f)
      (inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env) := by
  intro s₀ d i hs hw
  sym only [conleche_grind, inferBodyIO, CoreFns.ioView_infer, CoreFns.ioView_whnf,
      natLitStoredF_eq, strLitStoredF_eq, mkFEnv_findProj?, constTyOf,
      ProjEntry.typeAtI_eq, toListRev_empty, Option.isSome_some,
      abstract1C_spec, EnvWF.constTy_closed henv, wscoped_typeAt henv] =>
    vcgen [inferBodyIOI.eq_def, inferBodyI.eq_def, maxNatSizeM, abstract1M, ensureSortIOC_spec ih,
      inst1M_spec (mode := mode) (eager := eager) (env := env), ih.inferIO_spec, ih.whnf_spec,
      constTyAtM_spec (mode := mode) (eager := eager) (env := env), inferSpineIOC_spec ih,
      checkProjGuardC_specIO ih henv] <;>
          finish

end Walks3

end ConLeche.Cached
