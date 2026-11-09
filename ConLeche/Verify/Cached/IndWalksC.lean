module

public import ConLeche.Cached.ExprOpsC
import ConLeche.Verify.Cached.OpsC
public import ConLeche.Kernel.Inductives.GenRec
import ConLeche.Verify.AbstractRange

public section

/-!
# The inductive check's cached walks are the specification's (task #498)

The walks and loops of `ConLeche/Cached/ExprOpsC.lean` that the cached
twin of the inductive check runs, each equal to its `Kernel/Inductives/*`
specification at the same arguments: the occurrence queries
(`nestOccC`, `mentionsAnyConstC`, `piDomsMentionAnyC`), the free-variable
replacement (`replaceFVarsC`), and the telescope closers
(`closeTelescopeC`, `closeLamsC`, `abstractPrefixC`), which abstract
each domain and the body once by `abstractRangeC` where the
specification folds `abstract1` binder by binder (`abstractRange_succ`
is the step).  As in `OpsC.lean`, the walks verify themselves against
their plain descents (`*P`); this file proves the descents.
-/

namespace ConLeche.Expr

/-! ## Free-variable replacement -/

/-- A term without a free variable is left alone by `replaceFVars`
(the walk's cutoff). -/
theorem replaceFVars_of_fvarRange_zero {f : Nat → Option Expr} :
    ∀ {e : Expr}, e.fvarRange = 0 → e.replaceFVars f = e := by
  intro e
  induction e <;> intro h <;>
    simp_all [Expr.fvarRange, Expr.replaceFVars, Nat.max_eq_zero_iff]

/-- **The plain descent computes `Expr.replaceFVars`**: the reference of
`replaceFVarsXP`. -/
theorem replaceFVarsP_spec {f : Nat → Option Expr} :
    ∀ e : Expr, replaceFVarsP f e = e.replaceFVars f := by
  intro e
  induction e with
  | _ =>
    rw [replaceFVarsP.eq_def]
    split
    · rename_i hcut
      exact (replaceFVars_of_fvarRange_zero (by rwa [← fvarB_eq])).symm
    · simp_all [Expr.replaceFVars]

/-- **The cached replacement computes `Expr.replaceFVars`.** -/
theorem replaceFVarsC_spec {f : Nat → Option Expr} {e : Expr} :
    replaceFVarsC f e = e.replaceFVars f := by
  rw [replaceFVarsC]
  split
  · rename_i hcut
    exact (replaceFVars_of_fvarRange_zero (by rwa [← fvarB_eq])).symm
  · rw [resTerm_eq]; exact replaceFVarsP_spec e

/-! ## Occurrence queries -/

/-- **The plain descent computes `Expr.nestOcc`.** -/
theorem nestOccP_spec {names : List Name} {lo hi : Nat} :
    ∀ e : Expr, nestOccP names lo hi e = e.nestOcc names lo hi := by
  intro e
  induction e <;> simp_all [nestOccP, Expr.nestOcc]

/-- **The cached occurrence test computes `Expr.nestOcc`.** -/
theorem nestOccC_spec {names : List Name} {lo hi : Nat} {e : Expr} :
    nestOccC names lo hi e = e.nestOcc names lo hi := by
  rw [nestOccC, resBool_eq, nestOccP_spec]

/-- **The plain descent computes `Expr.mentionsAnyConst`.** -/
theorem mentionsAnyConstP_spec {names : List Name} :
    ∀ e : Expr, mentionsAnyConstP names e = e.mentionsAnyConst names := by
  intro e
  induction e <;> simp_all [mentionsAnyConstP, Expr.mentionsAnyConst]

/-- **The cached mention test computes `Expr.mentionsAnyConst`.** -/
theorem mentionsAnyConstC_spec {names : List Name} {e : Expr} :
    mentionsAnyConstC names e = e.mentionsAnyConst names := by
  rw [mentionsAnyConstC, resBool_eq, mentionsAnyConstP_spec]

/-- **The cached domain scan computes `Expr.piDomsMentionAny`.** -/
theorem piDomsMentionAnyC_spec {names : List Name} :
    ∀ e : Expr, piDomsMentionAnyC names e = e.piDomsMentionAny names := by
  intro e
  induction e <;> simp_all [piDomsMentionAnyC, Expr.piDomsMentionAny, mentionsAnyConstC_spec]

/-! ## Closing telescopes -/

/-- The closer after `k` binders: the specification's closing of the
rest, abstracted over the free variables of those `k` binders. -/
theorem closeTelescopeGoC_eq (i : Nat) : ∀ (k : Nat) (bs : List Expr) (body : Expr),
    closeTelescopeGoC i k bs body = (closeTelescope bs (i + k) body).abstractRange i k
  | k, [], body => by rw [closeTelescopeGoC, abstractRangeC_spec, closeTelescope]
  | k, dom :: bs, body => by
    rw [closeTelescopeGoC, closeTelescopeGoC_eq i (k + 1) bs body, abstractRangeC_spec,
      closeTelescope, ← Nat.add_assoc, abstractRange_succ, mkForallE_eq]
    rfl

/-- **The cached closer is `closeTelescope`.** -/
theorem closeTelescopeC_eq (bs : List Expr) (i : Nat) (body : Expr) :
    closeTelescopeC bs i body = closeTelescope bs i body := by
  rw [closeTelescopeC, closeTelescopeGoC_eq, Nat.add_zero, ConLeche.abstractRange_zero]

/-- `closeTelescopeGoC_eq` with `λ` binders. -/
theorem closeLamsGoC_eq (i : Nat) : ∀ (k : Nat) (bs : List Expr) (body : Expr),
    closeLamsGoC i k bs body = (closeLams bs (i + k) body).abstractRange i k
  | k, [], body => by rw [closeLamsGoC, abstractRangeC_spec, closeLams]
  | k, dom :: bs, body => by
    rw [closeLamsGoC, closeLamsGoC_eq i (k + 1) bs body, abstractRangeC_spec,
      closeLams, ← Nat.add_assoc, abstractRange_succ, mkLam_eq]
    rfl

/-- **The cached `λ` closer is `closeLams`.** -/
theorem closeLamsC_eq (bs : List Expr) (i : Nat) (body : Expr) :
    closeLamsC bs i body = closeLams bs i body := by
  rw [closeLamsC, closeLamsGoC_eq, Nat.add_zero, ConLeche.abstractRange_zero]

/-- **The cached prefix abstraction is `Expr.abstractPrefix`.** -/
theorem abstractPrefixC_eq : ∀ (k c : Nat) (e : Expr),
    abstractPrefixC k c e = Expr.abstractPrefix k c e
  | 0, c, e => by
    rw [abstractPrefixC, abstractRangeC_spec, ConLeche.abstractRange_zero, abstractPrefix]
  | k + 1, c, e => by
    rw [abstractPrefix, ← abstractPrefixC_eq k (c + 1), abstractPrefixC, abstractPrefixC,
      abstractRangeC_spec, abstractRangeC_spec, abstractRange_succ, Nat.zero_add]

/-! ## The member abstraction -/

/-- **The plain descent computes `targetAbs`.** -/
theorem targetAbsP_spec {names : List Name} {lvls : List Level} {holes : List Expr} :
    ∀ e : Expr, targetAbsP names lvls holes e = targetAbs names lvls holes e := by
  intro e
  induction e with
  | const n us =>
    simp only [targetAbsP, targetAbs, targetAbsConst]
    cases List.findIdx? (· == n) names <;> rfl
  | _ => simp_all [targetAbsP, targetAbs]

/-- **The cached member abstraction computes `targetAbs`.** -/
theorem targetAbsC_spec {names : List Name} {lvls : List Level} {holes : List Expr} {e : Expr} :
    targetAbsC names lvls holes e = targetAbs names lvls holes e := by
  rw [targetAbsC, resTerm_eq, targetAbsP_spec]

/-! ## Opening telescopes at given arguments -/

/-- **The cached `instPisWith` is `instPisWith`.** -/
theorem instPisWithC_eq : ∀ (as : List Expr) (e : Expr), instPisWithC as e = instPisWith as e
  | [], _ => rfl
  | a :: as, .forallE _ body => by
    rw [instPisWithC, instPisWith, instantiate1C_spec, instPisWithC_eq as]
  | _ :: _, .bvar _ => rfl
  | _ :: _, .fvar .. => rfl
  | _ :: _, .sort _ => rfl
  | _ :: _, .const .. => rfl
  | _ :: _, .app .. => rfl
  | _ :: _, .lam .. => rfl
  | _ :: _, .letE .. => rfl
  | _ :: _, .lit _ => rfl
  | _ :: _, .proj .. => rfl

/-- **The cached `targetPiDomsWith` is `targetPiDomsWith`.** -/
theorem targetPiDomsWithC_eq :
    ∀ (xs : List Expr) (e : Expr), targetPiDomsWithC xs e = targetPiDomsWith xs e
  | [], _ => rfl
  | x :: xs, .forallE _ body => by
    rw [targetPiDomsWithC, targetPiDomsWith, instantiate1C_spec, targetPiDomsWithC_eq xs]
  | _ :: _, .bvar _ => rfl
  | _ :: _, .fvar .. => rfl
  | _ :: _, .sort _ => rfl
  | _ :: _, .const .. => rfl
  | _ :: _, .app .. => rfl
  | _ :: _, .lam .. => rfl
  | _ :: _, .letE .. => rfl
  | _ :: _, .lit _ => rfl
  | _ :: _, .proj .. => rfl

end ConLeche.Expr
