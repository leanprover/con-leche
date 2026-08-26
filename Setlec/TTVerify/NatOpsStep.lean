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

/-- **The template's engine**, factored so that each operation's clause
is shape work only.  Given a stored equation of `c` whose two sides
denote, the equation holds at any two numerals.

Everything an operation shares lives here: the guard's consequences,
the `Nat` pin, the numerals' typing and closedness, and `Deq.close2`. -/
theorem natOp_closed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {c : Name} (hc : c ∈ natOpNames) {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv value hint))
    {eq : Expr × Expr} (hmem : eq ∈ natOpEquations 0 c)
    {L R : VExpr}
    (hL : denote m.cval env φ 2 eq.1 = some L)
    (hR : denote m.cval env φ 2 eq.2 = some R)
    {Γ : List VExpr} (a b : Nat) :
    Deq Γ ((L.inst (numeral a) 1).inst (numeral b))
      ((R.inst (numeral a) 1).inst (numeral b)) := by
  obtain ⟨hguard, hlaw⟩ := m.nat_ops c hc cv value hint hf
  have hnat : natLitSupported env = true := by
    simp only [natOpGuard, Bool.and_eq_true] at hguard
    exact hguard.1.1
  obtain ⟨L', R', hL', hR', ⟨T, hD⟩⟩ := hlaw eq hmem φ
  obtain rfl : L' = L := by rw [hL'] at hL; exact Option.some.inj hL
  obtain rfl : R' = R := by rw [hR'] at hR; exact Option.some.inj hR
  exact Deq.close2 (m.cval_closed _ _) hD
    (by rw [cval_natT m φ hnat]; exact hasType_numeral a)
    (by rw [cval_natT m φ hnat]; exact hasType_numeral b)

/-- The guard's own consequences, in the form every operation clause
reads them: the literal support, and that the operation and each of its
dependencies is stored with no level parameters. -/
theorem natOpGuard_deps {env : Env} {c : Name}
    (hguard : natOpGuard env c = true) :
    natLitSupported env = true ∧
      ∀ n ∈ natOpDeps c, ∃ cv v hh, env.find? n = some (.defnInfo cv v hh) ∧
        cv.levelParams = [] := by
  simp only [natOpGuard, Bool.and_eq_true] at hguard
  refine ⟨hguard.1.1, ?_⟩
  intro n hn
  have hd := hguard.1.2
  rw [List.all_eq_true] at hd
  have h := hd n (by simpa using hn)
  cases hx : env.find? n with
  | none => rw [hx] at h; exact nomatch h
  | some ci =>
    rw [hx] at h
    cases ci with
    | defnInfo cv v hh =>
      exact ⟨cv, v, hh, rfl, by simpa [List.isEmpty_iff] using h⟩
    | _ => simp at h

/-- The `Bool` constructors are pinned by the guard of any operation
whose recurrences mention them. -/
theorem natOpGuard_bools {env : Env} {c : Name}
    (hguard : natOpGuard env c = true)
    (hc : c = natBeqName ∨ c = natBleName ∨ natDivModNames.contains c = true) :
    (∃ ci, env.find? boolTrueName = some ci ∧
        ci.toConstantVal.levelParams = []) ∧
      (∃ ci, env.find? boolFalseName = some ci ∧
        ci.toConstantVal.levelParams = []) := by
  simp only [natOpGuard, Bool.and_eq_true] at hguard
  have hb := hguard.2
  rw [show (decide (c = natBeqName) || decide (c = natBleName) ||
      natDivModNames.contains c) = true from by
    rcases hc with rfl | rfl | h
    · simp
    · simp
    · rw [h]; simp] at hb
  simp only [if_true, Bool.and_eq_true] at hb
  obtain ⟨hT, hF⟩ := hb
  constructor
  · cases hx : env.find? boolTrueName with
    | none => rw [hx] at hT; exact nomatch hT
    | some ci => rw [hx] at hT; exact ⟨ci, rfl,
      by simpa [List.isEmpty_iff] using hT⟩
  · cases hx : env.find? boolFalseName with
    | none => rw [hx] at hF; exact nomatch hF
    | some ci => rw [hx] at hF; exact ⟨ci, rfl,
      by simpa [List.isEmpty_iff] using hF⟩

/-- A dependency of a guarded operation denotes to its valuation. -/
theorem denote_dep {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {c n : Name} (hguard : natOpGuard env c = true)
    (hn : n ∈ natOpDeps c) (d : Nat) :
    denote m.cval env φ d (.const n []) = some (m.cval n φ) := by
  obtain ⟨-, hdeps⟩ := natOpGuard_deps hguard
  obtain ⟨cv, v, hh, hf, hlp⟩ := hdeps n hn
  exact denote_const_nolevels m φ hf (by simpa [ConstantInfo.toConstantVal]
    using hlp) d

/-- The guard of a stored operation. -/
theorem natOp_guard {env : Env} (m : EnvTT env) {c : Name}
    (hc : c ∈ natOpNames) {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv value hint)) :
    natOpGuard env c = true :=
  (m.nat_ops c hc cv value hint hf).1

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

/-! ## The remaining structural operations

Each is the template applied: name the two (or three, or four) stored
equations, compute both sides' denotations from the primitives, and
hand the results to the matching `Setlec/TT/Nat/Ops.lean` family.  The
`by decide` extraction keeps each clause independent of where its
equation sits in `natOpEquations`' list. -/

/-- `Nat.pred`, closed at numerals. -/
theorem natOps_pred_closed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hf : env.find? natPredName = some (.defnInfo cv value hint))
    {Γ : List VExpr} : ∀ a : Nat,
      Deq Γ (.app (m.cval natPredName φ) (numeral a)) (numeral (a - 1)) := by
  have hg := natOp_guard m (by decide) hf
  have hnat : natLitSupported env = true := (natOpGuard_deps hg).1
  have hcv := denote_dep m φ (c := natPredName) (n := natPredName) hg
    (by decide) 2
  refine numeral_pred (Γ := Γ) (p := m.cval natPredName φ) ?_ ?_
  · have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natPredName)[0]!) (by decide)
      (L := .app (m.cval natPredName φ) natZeroT) (R := natZeroT)
      (by rw [show ((natOpEquations 0 natPredName)[0]!).1 =
            .app (.const natPredName []) (.const natZeroName []) from by decide,
          denote_app, hcv, denote_natZeroT m φ hnat])
      (by rw [show ((natOpEquations 0 natPredName)[0]!).2 =
            .const natZeroName [] from by decide, denote_natZeroT m φ hnat])
      0 0
    simpa [natZeroT, VExpr.inst,
      VExpr.inst_eq_self_of_closed (m.cval_closed natPredName φ)] using h
  · intro a
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natPredName)[1]!) (by decide)
      (L := .app (m.cval natPredName φ) (natSuccT (.bvar 1)))
      (R := .bvar 1)
      (by rw [show ((natOpEquations 0 natPredName)[1]!).1 =
            .app (.const natPredName [])
              (.app (.const natSuccName [])
                (.fvar 0 (.str .anonymous "x") (.const natName [])))
            from by decide,
          denote_app, hcv, denote_natSuccT m φ hnat (denote_natOp_x _ _)])
      (by rw [show ((natOpEquations 0 natPredName)[1]!).2 =
            .fvar 0 (.str .anonymous "x") (.const natName []) from by decide,
          denote_natOp_x])
      a 0
    simpa [natSuccT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (m.cval_closed natPredName φ)] using h

/-- `Nat.sub`, closed at numerals. -/
theorem natOps_sub_closed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hf : env.find? natSubName = some (.defnInfo cv value hint))
    {Γ : List VExpr} : ∀ a b : Nat,
      Deq Γ (ap2 (m.cval natSubName φ) (numeral a) (numeral b))
        (numeral (a - b)) := by
  have hg := natOp_guard m (by decide) hf
  have hnat := (natOpGuard_deps hg).1
  obtain ⟨cvP, vP, hhP, hfP, -⟩ :=
    (natOpGuard_deps hg).2 natPredName (by decide)
  have hcv := denote_dep m φ (c := natSubName) (n := natSubName) hg
    (by decide) 2
  have hcp := denote_dep m φ (c := natSubName) (n := natPredName) hg
    (by decide) 2
  refine numeral_sub (p := m.cval natPredName φ)
    (natOps_pred_closed m φ hfP) ?_ ?_
  · intro a
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natSubName)[0]!) (by decide)
      (L := .app (.app (m.cval natSubName φ) (.bvar 1)) natZeroT)
      (R := .bvar 1)
      (by rw [show ((natOpEquations 0 natSubName)[0]!).1 =
            .app (.app (.const natSubName [])
              (.fvar 0 (.str .anonymous "x") (.const natName [])))
              (.const natZeroName []) from by decide,
          denote_app, denote_app, hcv, denote_natOp_x,
          denote_natZeroT m φ hnat])
      (by rw [show ((natOpEquations 0 natSubName)[0]!).2 =
            .fvar 0 (.str .anonymous "x") (.const natName []) from by decide,
          denote_natOp_x])
      a 0
    simpa [ap2, natZeroT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (m.cval_closed natSubName φ)] using h
  · intro a b
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natSubName)[1]!) (by decide)
      (L := .app (.app (m.cval natSubName φ) (.bvar 1))
        (natSuccT (.bvar 0)))
      (R := .app (m.cval natPredName φ)
        (.app (.app (m.cval natSubName φ) (.bvar 1)) (.bvar 0)))
      (by rw [show ((natOpEquations 0 natSubName)[1]!).1 =
            .app (.app (.const natSubName [])
              (.fvar 0 (.str .anonymous "x") (.const natName [])))
              (.app (.const natSuccName [])
                (.fvar 1 (.str .anonymous "y") (.const natName [])))
            from by decide,
          denote_app, denote_app, hcv, denote_natOp_x,
          denote_natSuccT m φ hnat (denote_natOp_y _ _)])
      (by rw [show ((natOpEquations 0 natSubName)[1]!).2 =
            .app (.const natPredName [])
              (.app (.app (.const natSubName [])
                (.fvar 0 (.str .anonymous "x") (.const natName [])))
                (.fvar 1 (.str .anonymous "y") (.const natName [])))
            from by decide,
          denote_app, denote_app, denote_app, hcp, hcv, denote_natOp_x,
          denote_natOp_y])
      a b
    simpa [ap2, natSuccT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.liftN_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (m.cval_closed natSubName φ),
      VExpr.inst_eq_self_of_closed (m.cval_closed natPredName φ)] using h

/-- `Nat.mul`, closed at numerals. -/
theorem natOps_mul_closed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hf : env.find? natMulName = some (.defnInfo cv value hint))
    {Γ : List VExpr} : ∀ a b : Nat,
      Deq Γ (ap2 (m.cval natMulName φ) (numeral a) (numeral b))
        (numeral (a * b)) := by
  have hg := natOp_guard m (by decide) hf
  have hnat := (natOpGuard_deps hg).1
  obtain ⟨cvA, vA, hhA, hfA, -⟩ :=
    (natOpGuard_deps hg).2 natAddName (by decide)
  have hcv := denote_dep m φ (c := natMulName) (n := natMulName) hg
    (by decide) 2
  have hca := denote_dep m φ (c := natMulName) (n := natAddName) hg
    (by decide) 2
  refine numeral_mul (g := m.cval natAddName φ)
    (natOps_add_closed m φ hfA) ?_ ?_
  · intro a
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natMulName)[0]!) (by decide)
      (L := .app (.app (m.cval natMulName φ) (.bvar 1)) natZeroT)
      (R := natZeroT)
      (by rw [show ((natOpEquations 0 natMulName)[0]!).1 =
            .app (.app (.const natMulName []) (.fvar 0 (.str .anonymous "x")
              (.const natName []))) (.const natZeroName []) from by decide,
          denote_app, denote_app, hcv, denote_natOp_x,
          denote_natZeroT m φ hnat])
      (by rw [show ((natOpEquations 0 natMulName)[0]!).2 = .const natZeroName []
            from by decide, denote_natZeroT m φ hnat])
      a 0
    simpa [ap2, natZeroT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (m.cval_closed natMulName φ)] using h
  · intro a b
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natMulName)[1]!) (by decide)
      (L := .app (.app (m.cval natMulName φ) (.bvar 1))
        (natSuccT (.bvar 0)))
      (R := .app (.app (m.cval natAddName φ)
        (.app (.app (m.cval natMulName φ) (.bvar 1)) (.bvar 0))) (.bvar 1))
      (by rw [show ((natOpEquations 0 natMulName)[1]!).1 =
            .app (.app (.const natMulName []) (.fvar 0 (.str .anonymous "x")
              (.const natName []))) (.app (.const natSuccName [])
              (.fvar 1 (.str .anonymous "y") (.const natName [])))
            from by decide,
          denote_app, denote_app, hcv, denote_natOp_x,
          denote_natSuccT m φ hnat (denote_natOp_y _ _)])
      (by rw [show ((natOpEquations 0 natMulName)[1]!).2 =
            .app (.app (.const natAddName [])
              (.app (.app (.const natMulName [])
                (.fvar 0 (.str .anonymous "x") (.const natName [])))
                (.fvar 1 (.str .anonymous "y") (.const natName []))))
                (.fvar 0 (.str .anonymous "x") (.const natName []))
            from by decide,
          denote_app, denote_app, denote_app, denote_app, hca, hcv,
          denote_natOp_x, denote_natOp_y])
      a b
    simpa [ap2, natSuccT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.liftN_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (m.cval_closed natMulName φ),
      VExpr.inst_eq_self_of_closed (m.cval_closed natAddName φ)] using h

/-- `Nat.pow`, closed at numerals. -/
theorem natOps_pow_closed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hf : env.find? natPowName = some (.defnInfo cv value hint))
    {Γ : List VExpr} : ∀ a b : Nat,
      Deq Γ (ap2 (m.cval natPowName φ) (numeral a) (numeral b))
        (numeral (a ^ b)) := by
  have hg := natOp_guard m (by decide) hf
  have hnat := (natOpGuard_deps hg).1
  obtain ⟨cvM, vM, hhM, hfM, -⟩ :=
    (natOpGuard_deps hg).2 natMulName (by decide)
  have hcv := denote_dep m φ (c := natPowName) (n := natPowName) hg
    (by decide) 2
  have hcm := denote_dep m φ (c := natPowName) (n := natMulName) hg
    (by decide) 2
  refine numeral_pow (g := m.cval natMulName φ)
    (natOps_mul_closed m φ hfM) ?_ ?_
  · intro a
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natPowName)[0]!) (by decide)
      (L := .app (.app (m.cval natPowName φ) (.bvar 1)) natZeroT)
      (R := natSuccT natZeroT)
      (by rw [show ((natOpEquations 0 natPowName)[0]!).1 =
            .app (.app (.const natPowName []) (.fvar 0 (.str .anonymous "x")
              (.const natName []))) (.const natZeroName []) from by decide,
          denote_app, denote_app, hcv, denote_natOp_x,
          denote_natZeroT m φ hnat])
      (by rw [show ((natOpEquations 0 natPowName)[0]!).2 = .app
        (.const natSuccName []) (.const natZeroName [])
            from by decide,
          denote_natSuccT m φ hnat (denote_natZeroT m φ hnat 2)])
      a 0
    simpa [ap2, natZeroT, natSuccT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (m.cval_closed natPowName φ)] using h
  · intro a b
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natPowName)[1]!) (by decide)
      (L := .app (.app (m.cval natPowName φ) (.bvar 1))
        (natSuccT (.bvar 0)))
      (R := .app (.app (m.cval natMulName φ)
        (.app (.app (m.cval natPowName φ) (.bvar 1)) (.bvar 0))) (.bvar 1))
      (by rw [show ((natOpEquations 0 natPowName)[1]!).1 =
            .app (.app (.const natPowName []) (.fvar 0 (.str .anonymous "x")
              (.const natName []))) (.app (.const natSuccName [])
              (.fvar 1 (.str .anonymous "y") (.const natName [])))
            from by decide,
          denote_app, denote_app, hcv, denote_natOp_x,
          denote_natSuccT m φ hnat (denote_natOp_y _ _)])
      (by rw [show ((natOpEquations 0 natPowName)[1]!).2 =
            .app (.app (.const natMulName [])
              (.app (.app (.const natPowName [])
                (.fvar 0 (.str .anonymous "x") (.const natName [])))
                (.fvar 1 (.str .anonymous "y") (.const natName []))))
                (.fvar 0 (.str .anonymous "x") (.const natName []))
            from by decide,
          denote_app, denote_app, denote_app, denote_app, hcm, hcv,
          denote_natOp_x, denote_natOp_y])
      a b
    simpa [ap2, natSuccT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.liftN_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (m.cval_closed natPowName φ),
      VExpr.inst_eq_self_of_closed (m.cval_closed natMulName φ)] using h

/-! ### The two comparisons

`Nat.beq` and `Nat.ble` return `Bool`, so their clauses additionally
need the two constructor terms; the guard pins those for exactly the
operations whose recurrences mention them (`natOpGuard_bools`). -/

/-- `Nat.beq`, closed at numerals. -/
theorem natOps_beq_closed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hf : env.find? natBeqName = some (.defnInfo cv value hint))
    {Γ : List VExpr} : ∀ a b : Nat,
      Deq Γ (ap2 (m.cval natBeqName φ) (numeral a) (numeral b))
        (if a = b then m.cval boolTrueName φ else m.cval boolFalseName φ) := by
  have hg := natOp_guard m (by decide) hf
  have hnat := (natOpGuard_deps hg).1
  obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ :=
    natOpGuard_bools hg (Or.inl rfl)
  have hcv := denote_dep m φ (c := natBeqName) (n := natBeqName) hg
    (by decide) 2
  have hbT := denote_const_nolevels m φ hfT hlpT 2
  have hbF := denote_const_nolevels m φ hfF hlpF 2
  refine numeral_beq (f := m.cval natBeqName φ) ?_ ?_ ?_ ?_
  · have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natBeqName)[0]!) (by decide)
      (L := .app (.app (m.cval natBeqName φ) natZeroT) natZeroT)
      (R := m.cval boolTrueName φ)
      (by rw [show ((natOpEquations 0 natBeqName)[0]!).1 =
            .app (.app (.const natBeqName []) (.const natZeroName []))
              (.const natZeroName []) from by decide,
          denote_app, denote_app, hcv, denote_natZeroT m φ hnat])
      (by rw [show ((natOpEquations 0 natBeqName)[0]!).2 =
            .const boolTrueName [] from by decide, hbT])
      0 0
    simpa [ap2, natZeroT, VExpr.inst,
      VExpr.inst_eq_self_of_closed (m.cval_closed natBeqName φ),
      VExpr.inst_eq_self_of_closed (m.cval_closed boolTrueName φ)] using h
  · intro b
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natBeqName)[1]!) (by decide)
      (L := .app (.app (m.cval natBeqName φ) natZeroT) (natSuccT (.bvar 0)))
      (R := m.cval boolFalseName φ)
      (by rw [show ((natOpEquations 0 natBeqName)[1]!).1 =
            .app (.app (.const natBeqName []) (.const natZeroName []))
              (.app (.const natSuccName []) (.fvar 1 (.str .anonymous "y")
              (.const natName []))) from by decide,
          denote_app, denote_app, hcv, denote_natZeroT m φ hnat,
          denote_natSuccT m φ hnat (denote_natOp_y _ _)])
      (by rw [show ((natOpEquations 0 natBeqName)[1]!).2 =
            .const boolFalseName [] from by decide, hbF])
      0 b
    simpa [ap2, natZeroT, natSuccT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (m.cval_closed natBeqName φ),
      VExpr.inst_eq_self_of_closed (m.cval_closed boolFalseName φ)] using h
  · intro a
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natBeqName)[2]!) (by decide)
      (L := .app (.app (m.cval natBeqName φ) (natSuccT (.bvar 1))) natZeroT)
      (R := m.cval boolFalseName φ)
      (by rw [show ((natOpEquations 0 natBeqName)[2]!).1 =
            .app (.app (.const natBeqName []) (.app (.const natSuccName [])
              (.fvar 0 (.str .anonymous "x") (.const natName []))))
              (.const natZeroName []) from by decide,
          denote_app, denote_app, hcv,
          denote_natSuccT m φ hnat (denote_natOp_x _ _),
          denote_natZeroT m φ hnat])
      (by rw [show ((natOpEquations 0 natBeqName)[2]!).2 =
            .const boolFalseName [] from by decide, hbF])
      a 0
    simpa [ap2, natZeroT, natSuccT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (m.cval_closed natBeqName φ),
      VExpr.inst_eq_self_of_closed (m.cval_closed boolFalseName φ)] using h
  · intro a b
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natBeqName)[3]!) (by decide)
      (L := .app (.app (m.cval natBeqName φ) (natSuccT (.bvar 1)))
        (natSuccT (.bvar 0)))
      (R := .app (.app (m.cval natBeqName φ) (.bvar 1)) (.bvar 0))
      (by rw [show ((natOpEquations 0 natBeqName)[3]!).1 =
            .app (.app (.const natBeqName []) (.app (.const natSuccName [])
              (.fvar 0 (.str .anonymous "x") (.const natName []))))
              (.app (.const natSuccName []) (.fvar 1 (.str .anonymous "y")
              (.const natName [])))
            from by decide,
          denote_app, denote_app, hcv,
          denote_natSuccT m φ hnat (denote_natOp_x _ _),
          denote_natSuccT m φ hnat (denote_natOp_y _ _)])
      (by rw [show ((natOpEquations 0 natBeqName)[3]!).2 =
            .app (.app (.const natBeqName []) (.fvar 0 (.str .anonymous "x")
              (.const natName []))) (.fvar 1 (.str .anonymous "y")
              (.const natName [])) from by decide,
          denote_app, denote_app, hcv, denote_natOp_x, denote_natOp_y])
      a b
    simpa [ap2, natSuccT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.liftN_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (m.cval_closed natBeqName φ)] using h

/-- `Nat.ble`, closed at numerals.  This is the one the WF-recursive
operations' guarded recurrences are stated with. -/
theorem natOps_ble_closed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hf : env.find? natBleName = some (.defnInfo cv value hint))
    {Γ : List VExpr} : ∀ a b : Nat,
      Deq Γ (ap2 (m.cval natBleName φ) (numeral a) (numeral b))
        (if a ≤ b then m.cval boolTrueName φ else m.cval boolFalseName φ) := by
  have hg := natOp_guard m (by decide) hf
  have hnat := (natOpGuard_deps hg).1
  obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ :=
    natOpGuard_bools hg (Or.inr (Or.inl rfl))
  have hcv := denote_dep m φ (c := natBleName) (n := natBleName) hg
    (by decide) 2
  have hbT := denote_const_nolevels m φ hfT hlpT 2
  have hbF := denote_const_nolevels m φ hfF hlpF 2
  refine numeral_ble (f := m.cval natBleName φ) ?_ ?_ ?_
  · intro b
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natBleName)[0]!) (by decide)
      (L := .app (.app (m.cval natBleName φ) natZeroT) (.bvar 0))
      (R := m.cval boolTrueName φ)
      (by rw [show ((natOpEquations 0 natBleName)[0]!).1 =
            .app (.app (.const natBleName []) (.const natZeroName []))
              (.fvar 1 (.str .anonymous "y")
              (.const natName [])) from by decide,
          denote_app, denote_app, hcv, denote_natZeroT m φ hnat,
          denote_natOp_y])
      (by rw [show ((natOpEquations 0 natBleName)[0]!).2 =
            .const boolTrueName [] from by decide, hbT])
      0 b
    simpa [ap2, natZeroT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (m.cval_closed natBleName φ),
      VExpr.inst_eq_self_of_closed (m.cval_closed boolTrueName φ)] using h
  · intro a
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natBleName)[1]!) (by decide)
      (L := .app (.app (m.cval natBleName φ) (natSuccT (.bvar 1))) natZeroT)
      (R := m.cval boolFalseName φ)
      (by rw [show ((natOpEquations 0 natBleName)[1]!).1 =
            .app (.app (.const natBleName []) (.app (.const natSuccName [])
              (.fvar 0 (.str .anonymous "x") (.const natName []))))
              (.const natZeroName []) from by decide,
          denote_app, denote_app, hcv,
          denote_natSuccT m φ hnat (denote_natOp_x _ _),
          denote_natZeroT m φ hnat])
      (by rw [show ((natOpEquations 0 natBleName)[1]!).2 =
            .const boolFalseName [] from by decide, hbF])
      a 0
    simpa [ap2, natZeroT, natSuccT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (m.cval_closed natBleName φ),
      VExpr.inst_eq_self_of_closed (m.cval_closed boolFalseName φ)] using h
  · intro a b
    have h := natOp_closed m φ (by decide) hf (Γ := Γ)
      (eq := (natOpEquations 0 natBleName)[2]!) (by decide)
      (L := .app (.app (m.cval natBleName φ) (natSuccT (.bvar 1)))
        (natSuccT (.bvar 0)))
      (R := .app (.app (m.cval natBleName φ) (.bvar 1)) (.bvar 0))
      (by rw [show ((natOpEquations 0 natBleName)[2]!).1 =
            .app (.app (.const natBleName []) (.app (.const natSuccName [])
              (.fvar 0 (.str .anonymous "x") (.const natName []))))
              (.app (.const natSuccName []) (.fvar 1 (.str .anonymous "y")
              (.const natName [])))
            from by decide,
          denote_app, denote_app, hcv,
          denote_natSuccT m φ hnat (denote_natOp_x _ _),
          denote_natSuccT m φ hnat (denote_natOp_y _ _)])
      (by rw [show ((natOpEquations 0 natBleName)[2]!).2 =
            .app (.app (.const natBleName []) (.fvar 0 (.str .anonymous "x")
              (.const natName []))) (.fvar 1 (.str .anonymous "y")
              (.const natName [])) from by decide,
          denote_app, denote_app, hcv, denote_natOp_x, denote_natOp_y])
      a b
    simpa [ap2, natSuccT, VExpr.inst,
      VExpr.liftN_eq_self_of_closed (numeral_closed a),
      VExpr.liftN_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (numeral_closed a),
      VExpr.inst_eq_self_of_closed (numeral_closed b),
      VExpr.inst_eq_self_of_closed (m.cval_closed natBleName φ)] using h

end Setlec.TTVerify
