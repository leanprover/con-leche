import Setlec.TTVerify.NatOpPin
import Setlec.Verify.DivModInv

/-!
# The `Nat.div`/`Nat.mod` characterization pin

`DivModPinTT`, the second obligation `DeclDefnTT` left behind.

`checkDivModCerts` checks each vendored certificate exactly like a
theorem declaration over an *opened* four-variable telescope
(`x`, `y`, and one `fvar` per `ble`-guard hypothesis), in the
**pre-insertion** environment with the operation's self-references
replaced by its stored value.  So the bridge's job is:

1. turn a successful run into a derivation in the closed four-entry
   context `[H₂, H₁, Nat, Nat]` — `InferClaimsTT` at depth `4`, then
   `DefEqClaimsTT` against the pinned equation, then `EnvTT.eq_law` to
   read the resulting `Eq` spine as the layer's `eqE`;
2. move that derivation to the caller's arbitrary context and
   arguments.

Step 2 takes the **object-level route** the substitution file asks for:
four `lam`s close the derivation, `weakenTail` puts it in the caller's
context, and four `app`s instantiate it — the `app` rule's own
`B.inst a` performs every substitution in the type.  `HasType.instN`
is never used here.

> **The inert type slot pays for the guards.**  A clause's hypothesis
> is handed to us as `Deq Δ (ble y x) true`, but the certificate wants
> an *inhabitant* of the stored `Eq` spine.  `Deq.toHasType` retypes a
> derivation at **any** type slot, so the guard converts with no
> unique-typing argument anywhere: pick the slot the law wants.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The fragment's constants, denoted -/

/-- A constant of the certificate fragment denotes to the install's
valuation — the operation itself through its substituted stored value,
every other constant through the environment. -/
def DMDen {env : Env} (m : EnvTT env) (c : Name) (value' : Expr)
    (φ : Name → Nat) (n : Name) : Prop :=
  ∀ d, denote m.cval env φ d (Expr.substConst0 c value' (.const n []))
    = some (cvalAt m.cval env c value' n φ)

/-- The operation's own constant. -/
theorem DMDen.self {env : Env} {m : EnvTT env} {c : Name} {value' : Expr}
    {φ : Name → Nat} {V : VExpr}
    (hv : denoteClosed m.cval env φ value' = some V)
    (hvf : value'.hasFvar = false)
    (hvb : value'.looseBVarsBounded 0 = true) :
    DMDen m c value' φ c := by
  intro d
  rw [show Expr.substConst0 c value' (.const c []) = value' from by
    rw [Expr.substConst0, if_pos ⟨rfl, rfl⟩]]
  rw [denote_depth_closed m.cval_closed hvf hvb d, hv, cvalAt_self hv]

/-- Any other stored constant. -/
theorem DMDen.other {env : Env} {m : EnvTT env} {c : Name} {value' : Expr}
    {φ : Name → Nat} {n : Name} {ci : ConstantInfo} (hne : n ≠ c)
    (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = []) :
    DMDen m c value' φ n := by
  intro d
  rw [show Expr.substConst0 c value' (.const n []) = .const n [] from by
    rw [Expr.substConst0, if_neg (fun hh => hne hh.1)]]
  rw [denote_const_nolevels m φ hf hlp d, cvalAt_ne hne]

/-! ## The four-fold instantiation, in two -/

/-- The two-variable instantiation of a depth-`2` denotation: `bvar 1`
is `x`, `bvar 0` is `y` (the certificate frame's own order). -/
def at2 (e x y : VExpr) : VExpr := (e.inst x 1).inst y 0

theorem inst_bvar_lt {j k : Nat} (h : j < k) (a : VExpr) :
    (VExpr.bvar j).inst a k = .bvar j := by
  simp only [VExpr.inst, if_pos h]

theorem inst_bvar_eq (k : Nat) (a : VExpr) :
    (VExpr.bvar k).inst a k = a.liftN k := by
  simp [VExpr.inst]

theorem inst_bvar_gt {j k : Nat} (h : k < j) (a : VExpr) :
    (VExpr.bvar j).inst a k = .bvar (j - 1) := by
  simp only [VExpr.inst, if_neg (show ¬ j < k by omega),
    if_neg (show ¬ j = k by omega)]

/-- Absorbing a lift into an instantiation at the base cut. -/
theorem inst_liftN_succ (e a : VExpr) (m : Nat) :
    (VExpr.liftN (m + 1) e 0).inst a m = VExpr.liftN m e 0 :=
  VExpr.inst_liftN_absorb e (Nat.zero_le _) (by omega) a

/-- **The certificate's four applications collapse to two.**  The
statement is denoted at depth `4`, so its two `Nat` variables sit two
lifts up; instantiating the four telescope binders — the two variables
and the two *proof* binders the equation never mentions — is the plain
two-variable instantiation of the depth-`2` denotation.

This is the whole of the frame bookkeeping, and it holds at every cut,
so binders inside the statement would cost nothing extra. -/
theorem inst4_at2 : ∀ (e x y : VExpr) (k : Nat),
    ((((VExpr.liftN 2 e k).inst x (k + 3)).inst y (k + 2)).inst
        VExpr.prf (k + 1)).inst VExpr.prf k
      = (e.inst x (k + 1)).inst y k := by
  intro e
  induction e with
  | bvar i =>
    intro x y k
    simp only [VExpr.liftN_bvar]
    by_cases h1 : i < k
    · rw [if_pos h1, inst_bvar_lt (by omega), inst_bvar_lt (by omega),
        inst_bvar_lt (by omega), inst_bvar_lt h1, inst_bvar_lt (by omega),
        inst_bvar_lt h1]
    · rw [if_neg h1]
      by_cases h2 : i = k
      · subst h2
        rw [inst_bvar_lt (show i + 2 < i + 3 by omega), inst_bvar_eq,
          show i + 2 = (i + 1) + 1 from rfl, inst_liftN_succ,
          inst_liftN_succ, inst_bvar_lt (show i < i + 1 by omega),
          inst_bvar_eq]
      · by_cases h3 : i = k + 1
        · subst h3
          rw [show k + 1 + 2 = k + 3 by omega, inst_bvar_eq,
            show k + 3 = (k + 2) + 1 from rfl, inst_liftN_succ,
            inst_liftN_succ, inst_liftN_succ, inst_bvar_eq,
            show k + 1 = k + 1 from rfl, inst_liftN_succ]
        · rw [inst_bvar_gt (show k + 3 < i + 2 by omega),
            inst_bvar_gt (show k + 2 < i + 2 - 1 by omega),
            inst_bvar_gt (show k + 1 < i + 2 - 1 - 1 by omega),
            inst_bvar_gt (show k < i + 2 - 1 - 1 - 1 by omega),
            inst_bvar_gt (show k + 1 < i by omega),
            inst_bvar_gt (show k < i - 1 by omega)]
          exact congrArg VExpr.bvar (by omega)
  | sort u => intro x y k; rfl
  | const n us => intro x y k; rfl
  | prf => intro x y k; rfl
  | app f a ihf iha =>
    intro x y k
    simp only [VExpr.liftN, VExpr.inst, ihf, iha]
  | proj i e ih =>
    intro x y k
    simp only [VExpr.liftN, VExpr.inst, ih]
  | eqE T a b ihT iha ihb =>
    intro x y k
    simp only [VExpr.liftN, VExpr.inst, ihT, iha, ihb]
  | lam A b ihA ihb =>
    intro x y k
    simp only [VExpr.liftN, VExpr.inst, ihA]
    exact congrArg _ (ihb x y (k + 1))
  | pi A B ihA ihB =>
    intro x y k
    simp only [VExpr.liftN, VExpr.inst, ihA]
    exact congrArg _ (ihB x y (k + 1))
  | letE T v b ihT ihv ihb =>
    intro x y k
    simp only [VExpr.liftN, VExpr.inst, ihT, ihv]
    exact congrArg _ (ihb x y (k + 1))

/-! ## The pinned operations, typed

`natOpStoredOk` pins each dependency's type to `Nat → Nat → Nat` or
`Nat → Nat → Bool` (`Nat → Nat` for the unary pair).  The guard checks
that shape so the *reduction* rules may assume it; the bridge reads the
same shape as the typing that lets a clause's spines be formed at all.
-/

/-- The pinned codomain of an operation, as a term. -/
def dmCodV {env : Env} (m : EnvTT env) (φ : Name → Nat) (n : Name) : VExpr :=
  if n = natBeqName ∨ n = natBleName then m.cval boolName φ
  else m.cval natName φ

/-- The pinned codomain is a bare constant, so no instantiation ever
enters it. -/
theorem natOpCod_shape {env : Env} {n : Name} {e : Expr}
    (h : natOpCod env n e = true) : ∃ bn, e = .const bn [] := by
  unfold natOpCod at h
  by_cases hb : (decide (n = natBeqName) || decide (n = natBleName)) = true
  · rw [if_pos hb] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨boolName, h.1⟩
  · rw [if_neg hb] at h
    simp only [beq_iff_eq] at h
    exact ⟨natName, h⟩

/-- `natOpCod`, denoted. -/
theorem denote_natOpCod {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {n : Name} {e : Expr} (h : natOpCod env n e = true)
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) (d : Nat) :
    denote m.cval env φ d e = some (dmCodV m φ n) := by
  unfold natOpCod at h
  by_cases hb : (decide (n = natBeqName) || decide (n = natBleName)) = true
  · rw [if_pos hb] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hbool⟩ := h
    rw [dmCodV, if_pos (by simpa using hb)]
    revert hbool
    split
    · next ci hf =>
      intro hbool
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hbool
      exact denote_const_nolevels m φ hf hbool.1 d
    · intro hbool; exact nomatch hbool
  · rw [if_neg hb] at h
    simp only [beq_iff_eq] at h
    subst h
    rw [dmCodV, if_neg (by simpa using hb)]
    exact denote_const_nolevels m φ hfN hlpN d

/-- A pinned binary operation's type, denoted. -/
theorem denote_natOpTy2 {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {n : Name} {ty : Expr}
    (hnot : ¬ ((decide (n = natPredName) || decide (n = natLog2Name)) = true))
    (h : natOpTyPinned env n ty = true)
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) :
    denote m.cval env φ 0 ty
      = some (.pi (m.cval natName φ)
        (.pi (m.cval natName φ) (dmCodV m φ n))) := by
  unfold natOpTyPinned at h
  rw [if_neg hnot] at h
  revert h
  match ty with
  | .forallE nm dom (.forallE nm2 dom2 body mb2) mb => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _
  | .forallE _ _ (.bvar _) _ | .forallE _ _ (.fvar _ _ _) _
  | .forallE _ _ (.sort _) _ | .forallE _ _ (.const _ _) _
  | .forallE _ _ (.app _ _) _ | .forallE _ _ (.lam _ _ _ _) _
  | .forallE _ _ (.letE _ _ _ _) _ | .forallE _ _ (.lit _) _
  | .forallE _ _ (.proj _ _ _) _ =>
    intro h; exact nomatch h
  intro h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, hcod⟩ := h
  obtain ⟨bn, rfl⟩ := natOpCod_shape hcod
  have hN : ∀ d, denote m.cval env φ d (.const natName [])
      = some (m.cval natName φ) := fun d =>
    denote_const_nolevels m φ hfN hlpN d
  simp only [denote_forallE, hN, Expr.instantiate1,
    denote_natOpCod m φ hcod hfN hlpN]

/-- A pinned unary operation's type, denoted. -/
theorem denote_natOpTy1 {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {n : Name} {ty : Expr}
    (hnot : (decide (n = natPredName) || decide (n = natLog2Name)) = true)
    (h : natOpTyPinned env n ty = true)
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) :
    denote m.cval env φ 0 ty
      = some (.pi (m.cval natName φ) (dmCodV m φ n)) := by
  unfold natOpTyPinned at h
  rw [if_pos hnot] at h
  revert h
  match ty with
  | .forallE nm dom body mb => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, hcod⟩ := h
  obtain ⟨bn, rfl⟩ := natOpCod_shape hcod
  have hN : ∀ d, denote m.cval env φ d (.const natName [])
      = some (m.cval natName φ) := fun d =>
    denote_const_nolevels m φ hfN hlpN d
  simp only [denote_forallE, hN, Expr.instantiate1,
    denote_natOpCod m φ hcod hfN hlpN]

end Setlec.TTVerify
