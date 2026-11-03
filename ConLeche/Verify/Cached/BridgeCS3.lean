module

public import ConLeche.Verify.Cached.BridgeCS1
import ConLeche.Verify.Cached.NestPosC

public section

/-!
# Cached shared-state walks, part 3: the per-member install stages

The single-environment stages of the inductive install
(`checkStructDomsAt`, the telescope loop, `checkSumCtors`) and the
recursor conformance check's generator (`checkNativeRec`), as triples
between the `sharedOpsC` and `(fueledOpsM mode)` instantiations.  The per-site scoping facts mirror
`ConLeche/Verify/BridgeWfImp.lean`'s `_wfimp` walks one for one; the
`FEnv`-to-`Env` step is `ConLeche/Verify/CheckerF.lean`'s `_eq`/`_push`
family and happens in `ConLeche/Verify/Cached/BridgeCS4.lean`, so
everything here is stated over the generic functions.

The walks are `Std.WP` triples proved by `vcgen` and `grind`
(`ConLeche/Verify/Cached/Grind.lean`, `SimCS.lean`'s shared operations'
triples).
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr
open Expr
open Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

/-! ## Opened telescopes are scoped

Keyed by the opening's own equation, so that `grind` reads the scope of
a variable or of the body off the telescope it came from. -/

/-- An opened telescope's variables carry types scoped at their own
frame. -/
theorem openers_fvarTypeD_WScoped {n off : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e off = some (fvs, body)) (he : WScoped off e) {i : Nat} {x : Expr}
    (hx : fvs[i]? = some x) : WScoped (off + i) x.fvarTypeD := by
  obtain ⟨ty, rfl⟩ := openPisAtFvars_index n e off h i x hx
  have hw := (openPisAtFvars_WScoped n e off h he).1 _ (List.mem_of_getElem? hx)
  simp only [WScoped] at hw
  exact hw.2
grind_pattern [conleche_grind] openers_fvarTypeD_WScoped =>
  openPisAtFvars n e off, some (fvs, body), fvs[i]?, x.fvarTypeD where
  guard openPisAtFvars n e off = some (fvs, body)
  guard fvs[i]? = some x

/-- The same, read through the domains' list. -/
theorem openers_doms_WScoped {n off : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e off = some (fvs, body)) (he : WScoped off e) {i : Nat} {x : Expr}
    (hx : (fvs.map Expr.fvarTypeD)[i]? = some x) {d : Nat} (hd : d = off + i) :
    WScoped d x := by
  subst hd
  rw [List.getElem?_map] at hx
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
  exact openers_fvarTypeD_WScoped h he hy
grind_pattern [conleche_grind] openers_doms_WScoped =>
  openPisAtFvars n e off, some (fvs, body), (fvs.map Expr.fvarTypeD)[i]?, WScoped d x where
  guard openPisAtFvars n e off = some (fvs, body)
  guard (fvs.map Expr.fvarTypeD)[i]? = some x

/-- An opened telescope's body is scoped past the telescope. -/
theorem openers_body_WScoped {n off : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e off = some (fvs, body)) (he : WScoped off e) :
    WScoped (off + n) body :=
  (openPisAtFvars_WScoped n e off h he).2
grind_pattern [conleche_grind] openers_body_WScoped =>
  openPisAtFvars n e off, some (fvs, body) where
  guard openPisAtFvars n e off = some (fvs, body)

section Walks3

variable {env : Env} {s₀ : CState}

/-- The per-frame binder-domain pins at the shared operations. -/
theorem checkStructDomsAtS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {off : Nat}
    {fvs doms : List Expr}
    (hc : ∀ (i : Nat) (x : Expr), fvs[i]? = some x → WScoped (off + i) (Expr.fvarTypeD x))
    (ht : ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (off + i) x) :
    ∀ {j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      ⦃fun s => s = s₀⦄ checkStructDomsAt (sharedOpsC mode (mkFEnv env)) env off fvs doms j
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (checkStructDomsAt (fueledOpsM mode) env off fvs doms j) v; ⊤⦄ := by
  intro j
  induction j with
  | zero =>
    intro _ _
    sym only [conleche_grind, checkStructDomsAt.eq_1] => vcgen [checkStructDomsAt] <;> finish
  | succ j ih =>
    intro _ _
    sym only [conleche_grind, checkStructDomsAt.eq_2, unwrapOr] =>
      vcgen [checkStructDomsAt, unwrapOr, defeqS_spec hμ henv, ih] <;> finish

/-- Official's telescope loop (task #195) at the shared operations:
every `whnf` is the shared one, on a well-scoped input at its depth
(the opened body is well-scoped one deeper). -/
theorem whnfTelescopeS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) :
    ∀ {i n : Nat} {e : Expr} {s₀ : CState}, CSOK mode env s₀ → WScoped i e →
      ⦃fun s => s = s₀⦄ whnfTelescope (sharedOpsC mode (mkFEnv env)) env i n e
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (whnfTelescope (fueledOpsM mode) env i n e) v; ⊤⦄ := by
  intro i n
  induction n generalizing i with
  | zero =>
    intro _ _ _ _
    sym only [conleche_grind, whnfTelescope.eq_1] =>
      vcgen [whnfTelescope, whnfS_spec hμ henv] <;> finish
  | succ n ih =>
    intro _ _ _ _
    sym only [conleche_grind, whnfTelescope.eq_2] =>
      vcgen [whnfTelescope, whnfS_spec hμ henv, ih] <;>
        finish

/-- The former's telescope stage (task #195) at the shared operations:
the checked constant's type is well-scoped either way. -/
theorem checkSumTeleS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {cv : ConstantVal} {n : Nat} {cvTa₀ : ConstantVal}
    (hs : CSOK mode env s₀) (hTw : WScoped 0 cvTa₀.type) :
    ⦃fun s => s = s₀⦄ checkSumTele (sharedOpsC mode (mkFEnv env)) env cv n cvTa₀
    ⦃fun v s' => CSOK mode env s' ∧ Runs (checkSumTele (fueledOpsM mode) env cv n cvTa₀) v ∧
      WScoped 0 v.1.type; ⊤⦄ := by
  sym only [conleche_grind, checkSumTele.eq_1] =>
    vcgen [checkSumTele, whnfTelescopeS_spec hμ henv, checkConstantValS_spec hμ henv] <;>
      finish

/-- Stage 2 (one constructor, the constructor and its field count
explicit) at the shared operations. -/
theorem checkSumCtorS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env₀ : Env}
    {T : Name} {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC : ConstantVal} {nF : Nat} {cvTa : ConstantVal}
    (hTf : cvTa.type.hasFvar = false) (hs : CSOK mode env s₀) :
    ⦃fun s => s = s₀⦄ checkSumCtor (sharedOpsC mode (mkFEnv env)) env₀ env T lps nP
        nIdx resSort isProp large cvC nF cvTa
    ⦃fun v s' => CSOK mode env s' ∧ Runs (checkSumCtor (fueledOpsM mode) env₀ env T lps nP
        nIdx resSort isProp large cvC nF cvTa) v; ⊤⦄ := by
  -- `gen := 13` (the default 8 fails): the fueled side is a chain of ten binds, each one
  -- E-matching generation deeper than the last
  sym only [conleche_grind, checkSumCtor.eq_1, unwrapOr, FvsWS,
      wscoped_of_hasFvar_false (d := 0) hTf] =>
    vcgen [checkSumCtor, unwrapOr, checkConstantValS_spec hμ henv hs,
      checkStructDomsAtS_spec hμ henv, checkStructFieldSortsIS_spec hμ henv] <;>
      finish (gen := 13)

/-- Stage 2, the whole constructor list: every constructor is checked
at the *same* environment (the one holding the type former alone), so
the walk is a plain induction on the list. -/
theorem checkSumCtorsS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env₀ : Env}
    {T : Name} {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvTa : ConstantVal} (hTf : cvTa.type.hasFvar = false) :
    ∀ {cs : List (ConstantVal × Nat)} {s₀ : CState}, CSOK mode env s₀ →
      ⦃fun s => s = s₀⦄ checkSumCtors (sharedOpsC mode (mkFEnv env)) env₀ env T lps
          nP nIdx resSort isProp large cvTa cs
      ⦃fun v s' => CSOK mode env s' ∧ Runs (checkSumCtors (fueledOpsM mode) env₀ env T lps
          nP nIdx resSort isProp large cvTa cs) v; ⊤⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro _ _
    sym only [conleche_grind, checkSumCtors.eq_1] => vcgen [checkSumCtors] <;> finish
  | cons _ cs ih =>
    intro _ _
    sym only [conleche_grind, checkSumCtors.eq_2] =>
      vcgen [checkSumCtors, checkSumCtorS_spec hμ henv hTf, ih] <;> finish

/-! ### The recursor conformance check's generator (#188) -/

end Walks3

end ConLeche.Cached
