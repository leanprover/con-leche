import Setlec.TTVerify.WhnfCoreStep
import Setlec.TTVerify.Weaken

/-!
# The `Nat` fast path's obligation

`ReduceNatStepTT` (`Setlec/TTVerify/WhnfCoreStep.lean`): `reduceNat`
replaces an operation applied to literals by the literal of its value,
and the equation that justifies it comes from `EnvTT.nat_ops` /
`EnvTT.div_mod` closed at numerals.

Three pieces do the whole job, and all three are already built:

* `natLitT_eq_numeral` — a literal's denotation **is** the layer's
  numeral (§5);
* `Deq.close2` / `Deq.close1` — an open equation holds at closed
  arguments (§5's recipe);
* `Setlec/TT/Nat/{Ops,WfOps}.lean` — the meta-induction families, which
  take exactly the closed recurrences the previous two produce.

What is left is *shape* work: computing the denotation of each stored
equation side into the form the meta-induction lemmas state their
hypotheses at.  This module does that, one primitive at a time, so
that each operation's clause is a rewrite rather than a proof.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The primitives a `Nat` equation is built from

`natOpEquations` uses four shapes: the two free variables, `Nat.zero`,
`Nat.succ` applied to something, and an operation constant applied to
one or two arguments.  Each denotes to the obvious thing, and the
guards supply every side condition (§8.4). -/

/-- The equations' first variable, at the depth the field states them
at.  `.fvar 0` sits at de Bruijn index `2 - 1 - 0 = 1`. -/
theorem denote_natOp_x {cval : TConstVal} {env : Env} {φ : Name → Nat}
    (n : Name) (ty : Expr) :
    denote cval env φ 2 (.fvar 0 n ty) = some (.bvar 1) := by
  rw [denote_fvar]

/-- The equations' second variable: `.fvar 1` sits at index
`2 - 1 - 1 = 0`. -/
theorem denote_natOp_y {cval : TConstVal} {env : Env} {φ : Name → Nat}
    (n : Name) (ty : Expr) :
    denote cval env φ 2 (.fvar 1 n ty) = some (.bvar 0) := by
  rw [denote_fvar]

/-- A stored constant with no level parameters denotes to its valuation
at the ambient assignment. -/
theorem denote_const_nolevels {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {c : Name} {ci : ConstantInfo} (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (d : Nat) :
    denote m.cval env φ d (.const c []) = some (m.cval c φ) := by
  rw [denote_const, hf]
  simp only [hlp, List.length_nil, if_true]
  refine congrArg _ (congrArg _ ?_)
  funext q
  rfl

/-- `Nat.zero` denotes to the layer's `Nat.zero`. -/
theorem denote_natZeroT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : natLitSupported env = true) (d : Nat) :
    denote m.cval env φ d (.const natZeroName []) = some natZeroT := by
  simp only [natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, h2⟩, -⟩ := hg
  cases hf : env.find? natZeroName with
  | none => rw [hf] at h2; exact nomatch h2
  | some ci =>
    rw [hf] at h2
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv a b =>
        simp only [natZeroOk, Bool.and_eq_true] at h2
        have := h2.1
        simpa [ConstantInfo.toConstantVal, List.isEmpty_iff] using this
      | _ => simp [natZeroOk] at h2
    rw [denote_const_nolevels m φ hf hlp d]
    exact congrArg _ (cval_pinned m (by decide) (by rw [hf]; rfl) φ
      (by
        simp only [pinnedDirectT]
        rw [if_neg (by decide : ¬ (natZeroName = natName))]
        simp [natZeroT]))

/-- `Nat.succ` applied to a denoting argument denotes to `natSuccT`. -/
theorem denote_natSuccT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : natLitSupported env = true) {d : Nat} {e : Expr} {ve : VExpr}
    (h : denote m.cval env φ d e = some ve) :
    denote m.cval env φ d (.app (.const natSuccName []) e)
      = some (natSuccT ve) := by
  simp only [natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, -⟩, h3⟩ := hg
  cases hf : env.find? natSuccName with
  | none => rw [hf] at h3; exact nomatch h3
  | some ci =>
    rw [hf] at h3
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv a b =>
        simp only [natSuccOk, Bool.and_eq_true] at h3
        have := h3.1
        simpa [ConstantInfo.toConstantVal, List.isEmpty_iff] using this
      | _ => simp [natSuccOk] at h3
    have hpin : m.cval natSuccName φ = .const .natSucc [] :=
      cval_pinned m (by decide) (by rw [hf]; rfl) φ
        (by
          simp only [pinnedDirectT]
          rw [if_neg (by decide : ¬ (natSuccName = natName)),
            if_neg (by decide : ¬ (natSuccName = natZeroName))]
          simp)
    rw [denote_app, denote_const_nolevels m φ hf hlp d, h, hpin, natSuccT]

/-- `Nat` itself denotes to the layer's `Nat`.  Needed because the
meta-induction lemmas type their numerals at `natT` while the
environment law's context is `[cval natName φ, cval natName φ]`. -/
theorem cval_natT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : natLitSupported env = true) : m.cval natName φ = natT := by
  simp only [natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨h1, -⟩, -⟩ := hg
  refine cval_pinned m (by decide)
    (by revert h1; cases env.find? natName <;> simp [natIndOk]) φ ?_
  simp [pinnedDirectT, natT]

/-- Every numeral is closed. -/
theorem numeral_closed : ∀ n : Nat, VExpr.Closed (numeral n)
  | 0 => by simp [numeral, natZeroT, VExpr.Closed, VExpr.bvarsBelow]
  | n + 1 => by
    have := numeral_closed n
    simp only [numeral, natSuccT, VExpr.Closed, VExpr.bvarsBelow] at *
    exact ⟨trivial, this⟩

/-! ## An operation's recurrences, closed at numerals

The template, worked once and then repeated.  `natOpEquations 0 c`
states an operation's defining equations over `.fvar 0` and `.fvar 1`;
`EnvTT.nat_ops` denotes them at depth 2 and asserts a `Deq` in context
`[Nat, Nat]`; `Deq.close2` moves that to any two numerals.  What each
operation's clause has to do beyond that is *compute* — read the
denotation of its own equation sides into the shape
`Setlec/TT/Nat/Ops.lean` states its hypotheses at.

**`Nat.add` is written out in full below as the template.**  The other
six structural operations differ only in which primitives appear on
the right-hand side; nothing about the argument is `add`-specific. -/

/-- The `Nat.add` recurrences, closed at numerals: exactly
`numeral_add`'s two hypotheses. -/
theorem natOps_add {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hf : env.find? natAddName = some (.defnInfo cv value hint))
    {Γ : List VExpr} :
    (∀ a : Nat, Deq Γ (ap2 (m.cval natAddName φ) (numeral a) natZeroT)
        (numeral a)) ∧
      (∀ a b : Nat,
        Deq Γ (ap2 (m.cval natAddName φ) (numeral a)
            (natSuccT (numeral b)))
          (natSuccT (ap2 (m.cval natAddName φ) (numeral a)
            (numeral b)))) := by
  obtain ⟨hguard, hlaw⟩ := m.nat_ops natAddName (by decide) cv value hint hf
  -- the guard pins `Nat`, its constructors, and the operation itself
  have hnat : natLitSupported env = true := by
    simp only [natOpGuard, Bool.and_eq_true] at hguard
    exact hguard.1.1
  have hlpc : cv.levelParams = [] := by
    simp only [natOpGuard, Bool.and_eq_true] at hguard
    have hd := hguard.1.2
    rw [List.all_eq_true] at hd
    have := hd natAddName (by decide)
    rw [hf] at this
    simpa [ConstantInfo.toConstantVal, List.isEmpty_iff] using this
  have hcv : denote m.cval env φ 2 (.const natAddName []) =
      some (m.cval natAddName φ) :=
    denote_const_nolevels m φ hf (by simpa [ConstantInfo.toConstantVal]
      using hlpc) 2
  have hA : VExpr.Closed (m.cval natAddName φ) := m.cval_closed _ _
  have hnT : VExpr.Closed (m.cval natName φ) := m.cval_closed _ _
  refine ⟨?_, ?_⟩
  · -- `add x 0 = x`
    intro a
    obtain ⟨L, R, hL, hR, ⟨T, hD⟩⟩ :=
      hlaw (natOpEquations 0 natAddName)[0]! (by decide) φ
    rw [show ((natOpEquations 0 natAddName)[0]!).1 =
      .app (.app (.const natAddName []) (.fvar 0 (.str .anonymous "x")
        (.const natName []))) (.const natZeroName []) from by decide] at hL
    rw [show ((natOpEquations 0 natAddName)[0]!).2 =
      .fvar 0 (.str .anonymous "x") (.const natName []) from by decide] at hR
    rw [denote_app, denote_app, hcv, denote_natOp_x,
      denote_natZeroT m φ hnat] at hL
    rw [denote_natOp_x] at hR
    obtain rfl : L = ap2 (m.cval natAddName φ) (.bvar 1) natZeroT :=
      (Option.some.inj hL).symm
    obtain rfl : R = .bvar 1 := (Option.some.inj hR).symm
    have hc := Deq.close2 (A := m.cval natName φ) hnT hD
      (Γ := Γ) (a := numeral a) (b := numeral a)
      (by rw [cval_natT m φ hnat]; exact hasType_numeral a)
      (by rw [cval_natT m φ hnat]; exact hasType_numeral a)
    simpa [ap2, VExpr.inst, natZeroT,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed hA] using hc
  · -- `add x (succ y) = succ (add x y)`
    intro a b
    obtain ⟨L, R, hL, hR, ⟨T, hD⟩⟩ :=
      hlaw (natOpEquations 0 natAddName)[1]! (by decide) φ
    rw [show ((natOpEquations 0 natAddName)[1]!).1 =
      .app (.app (.const natAddName []) (.fvar 0 (.str .anonymous "x")
        (.const natName [])))
        (.app (.const natSuccName []) (.fvar 1 (.str .anonymous "y")
          (.const natName []))) from by decide] at hL
    rw [show ((natOpEquations 0 natAddName)[1]!).2 =
      .app (.const natSuccName [])
        (.app (.app (.const natAddName []) (.fvar 0 (.str .anonymous "x")
          (.const natName []))) (.fvar 1 (.str .anonymous "y")
            (.const natName []))) from by decide] at hR
    rw [denote_app, denote_app, hcv, denote_natOp_x,
      denote_natSuccT m φ hnat (denote_natOp_y _ _)] at hL
    rw [denote_natSuccT m φ hnat
      (by rw [denote_app, denote_app, hcv, denote_natOp_x,
        denote_natOp_y]), natSuccT] at hR
    obtain rfl : L = ap2 (m.cval natAddName φ) (.bvar 1)
        (natSuccT (.bvar 0)) := (Option.some.inj hL).symm
    obtain rfl : R = natSuccT (ap2 (m.cval natAddName φ) (.bvar 1)
        (.bvar 0)) := (Option.some.inj hR).symm
    have hc := Deq.close2 (A := m.cval natName φ) hnT hD
      (Γ := Γ) (a := numeral a) (b := numeral b)
      (by rw [cval_natT m φ hnat]; exact hasType_numeral a)
      (by rw [cval_natT m φ hnat]; exact hasType_numeral b)
    simpa [ap2, VExpr.inst, natSuccT,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.liftN_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed hA] using hc

/-- **The `Nat.add` fast path is sound**, in the form `reduceNat`'s
clause needs it: the operation applied to two numerals is `Deq` to the
numeral of their sum.

This is the whole chain in three lines — the environment's stored
recurrences, closed at numerals by `Deq.close2`, handed to the layer's
meta-induction.  **No derivation proportional to the literals is
constructed anywhere**, which is the requirement this design was
chosen to meet: `numeral_add`'s recursion is at the *meta* level, on
Lean's own `Nat`, and produces a `Deq` whose proof term is `prf`. -/
theorem natOps_add_closed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hf : env.find? natAddName = some (.defnInfo cv value hint))
    {Γ : List VExpr} : ∀ a b : Nat,
      Deq Γ (ap2 (m.cval natAddName φ) (numeral a) (numeral b))
        (numeral (a + b)) :=
  numeral_add (natOps_add m φ hf).1 (natOps_add m φ hf).2

end Setlec.TTVerify
