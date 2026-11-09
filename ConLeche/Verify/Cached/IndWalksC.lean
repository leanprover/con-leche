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

/-! ## Depth and parameter instantiation -/

/-- **The plain descent computes `Expr.depth`.** -/
theorem depthP_spec : ∀ e : Expr, depthP e = e.depth := by
  intro e
  induction e <;> simp_all [depthP, Expr.depth]

/-- **The cached depth computes `Expr.depth`.** -/
theorem depthC_spec {e : Expr} : depthC e = e.depth := by
  rw [depthC, resNat_eq, depthP_spec]

/-- **The cached parameter instantiation is `instPisWith`.** -/
theorem _root_.ConLeche.instPisWithC_eq : ∀ (args : List Expr) (e : Expr),
    instPisWithC args e = instPisWith args e
  | [], _ => rfl
  | a :: as, e => by
    cases e <;> simp only [instPisWithC, instPisWith, instantiate1C_spec,
      ConLeche.instPisWithC_eq as]

end ConLeche.Expr

namespace ConLeche.Cached

open ConLeche

/-- The cached occurrence test is `Expr.hasLooseBVarB` (task #497). -/
theorem hasLooseBVarBC_spec {i : Nat} {e : Expr} :
    Expr.hasLooseBVarBC i e = Expr.hasLooseBVarB i e := by
  unfold Expr.hasLooseBVarBC
  split
  · next h => exact (Expr.hasLooseBVarBP_cut h).symm
  · rw [Expr.resBool_eq]; rfl

/-- The cached opening loop is the kernel's. -/
theorem openPisAtFvarsGoC_eq :
    ∀ (acc : List Expr) (n : Nat) (e : Expr) (i : Nat),
      openPisAtFvarsGoC acc n e i = openPisAtFvarsFGo acc n e i
  | _, 0, _, _ => by simp only [openPisAtFvarsGoC, openPisAtFvarsFGo, Expr.instantiateListC_spec]
  | acc, n + 1, .forallE dom body, i => by
    simp only [openPisAtFvarsGoC, openPisAtFvarsFGo, Expr.instantiateListC_spec,
      openPisAtFvarsGoC_eq _ n body (i + 1)]
    cases openPisAtFvarsFGo (.fvar i (dom.instantiateList acc) :: acc) n body (i + 1) <;> rfl
  | _, _ + 1, .bvar _, _ => rfl
  | _, _ + 1, .fvar .., _ => rfl
  | _, _ + 1, .sort _, _ => rfl
  | _, _ + 1, .const .., _ => rfl
  | _, _ + 1, .app .., _ => rfl
  | _, _ + 1, .lam .., _ => rfl
  | _, _ + 1, .letE .., _ => rfl
  | _, _ + 1, .lit _, _ => rfl
  | _, _ + 1, .proj .., _ => rfl

/-- **The one pass misses no binder**: instantiating at free variables
never makes a `∀` appear, so where `openPisAtFvarsFGo` finds none, the
sequential opening of the instantiated term finds none either. -/
theorem openPisAtFvarsFGo_none :
    ∀ (n : Nat) (e : Expr) (i : Nat) (acc : List Expr),
      (∀ a ∈ acc, ∃ k t, a = .fvar k t) → openPisAtFvarsFGo acc n e i = none →
      openPisAtFvars n (e.instantiateList acc) i = none
  | 0, _, _, _, _, h => by simp [openPisAtFvarsFGo] at h
  | n + 1, .forallE dom body, i, acc, hacc, h => by
    simp only [openPisAtFvarsFGo] at h
    split at h
    case _ => exact nomatch h
    case _ hgo =>
      have ih := openPisAtFvarsFGo_none n body (i + 1)
        (Expr.fvar i (dom.instantiateList acc) :: acc)
        (fun a ha => by
          rcases List.mem_cons.mp ha with rfl | ha
          · exact ⟨_, _, rfl⟩
          · exact hacc a ha) hgo
      rw [Expr.instantiateList_cons] at ih
      simp only [Expr.instantiateList, openPisAtFvars, ih]
  | n + 1, .bvar j, i, acc, hacc, _ => by
    rw [Expr.instantiateList]
    split
    · rfl
    · split
      · rename_i hj
        obtain ⟨k, t, hk⟩ := hacc _ (List.getElem_mem hj)
        rw [hk, Expr.instantiateList]
        rfl
      · rfl
  | _ + 1, .fvar .., _, _, _, _ => by rw [Expr.instantiateList]; rfl
  | _ + 1, .sort _, _, _, _, _ => by rw [Expr.instantiateList]; rfl
  | _ + 1, .const .., _, _, _, _ => by rw [Expr.instantiateList]; rfl
  | _ + 1, .app .., _, _, _, _ => by rw [Expr.instantiateList]; rfl
  | _ + 1, .lam .., _, _, _, _ => by rw [Expr.instantiateList]; rfl
  | _ + 1, .letE .., _, _, _, _ => by rw [Expr.instantiateList]; rfl
  | _ + 1, .lit _, _, _, _, _ => by rw [Expr.instantiateList]; rfl
  | _ + 1, .proj .., _, _, _, _ => by rw [Expr.instantiateList]; rfl

/-- The cached one-pass telescope opening is `openPisAtFvars`. -/
theorem openPisAtFvarsC_eq (n : Nat) (e : Expr) (i : Nat) :
    openPisAtFvarsC n e i = openPisAtFvars n e i := by
  unfold openPisAtFvarsC
  rw [openPisAtFvarsGoC_eq]
  match h : openPisAtFvarsFGo [] n e i with
  | some r =>
    have := openPisAtFvarsFGo_sound n e i [] h
    rw [Expr.instantiateList_nil] at this
    exact this.symm
  | none =>
    have := openPisAtFvarsFGo_none n e i [] (by simp) h
    rw [Expr.instantiateList_nil] at this
    exact this.symm

end ConLeche.Cached
