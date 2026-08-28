import Setlec.SetR.Sound.Lit

/-!
# Soundness — the structural `Nat` operations' value recurrences
(task #148, T4, batch f2, part 1)

The `Model/NatOps.lean` re-hang, part 1: the equation-reading plumbing
(`natEq_value` — the certificate equations of `EnvSHyp.nat_ops`,
computed at the concrete denotations and read at value environments)
and the seven structural operations' literal meta-inductions
(`natOpV_pred` … `natOpV_ble`), stated over `interp`-values of the
`natLitV` numerals.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

section Cases

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- The `succV` head is a valuation leaf (definitional unfolding, for
rewrites against the rules' spelling). -/
theorem succV_eq :
    succV cval φ = cval natSuccName (Level.substFn φ [] []) := rfl

/-- The zero numeral is the zero valuation leaf (definitional). -/
theorem natLitV_zero :
    natLitV cval φ 0 = cval natZeroName (Level.substFn φ [] []) := rfl

/-- The denotation of a stored level-monomorphic constant. -/
theorem denote_const_mono {c : Name} {ci : ConstantInfo}
    (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (D : Nat) :
    denote cval env φ D (.const c [])
      = some (cval c (Level.substFn φ [] [])) := by
  rw [denote_const, hf]
  simp [hlp]

/-- Closed terms interpret the same under the two-slot extension. -/
theorem interp_cons2 {ρ : Nat → V} {x y : V} {e : VExpr}
    (he : VExpr.Closed e) :
    interp V (cons V y (cons V x ρ)) e = interp V ρ e :=
  interp_closed V he _ ρ

/-- Numerals interpret the same under the two-slot extension. -/
theorem interp_cons2_natLit (henv : EnvSHyp V env cval φ)
    (ρ : Nat → V) (x y : V) (n : Nat) :
    interp V (cons V y (cons V x ρ)) (natLitV cval φ n)
      = interp V ρ (natLitV cval φ n) := by
  induction n with
  | zero => exact interp_cons2 (henv.cval_closed _ _)
  | succ n ih =>
    show interp V _ (.app (succV cval φ) (natLitV cval φ n))
      = interp V ρ (.app (succV cval φ) (natLitV cval φ n))
    rw [interp_app, interp_app, ih, succV_eq,
      interp_cons2 (henv.cval_closed natSuccName _)]

/-- Read one certified recurrence equation at a value environment:
the two sides' *computed* denotations interpret equally whenever the
two slots are valued in the stored `Nat`'s interpretation. -/
theorem natEq_value (henv : EnvSHyp V env cval φ) {c : Name}
    (hc : c ∈ natOpNames) {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv v hint))
    {eq : Expr × Expr} (heq : eq ∈ natOpEquations 0 c)
    {L R : VExpr}
    (hdL : denote cval env φ 2 eq.1 = some L)
    (hdR : denote cval env φ 2 eq.2 = some R)
    {ρ : Nat → V} {x y : V}
    (hx : x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])))
    (hy : y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] []))) :
    interp V (cons V y (cons V x ρ)) L
      = interp V (cons V y (cons V x ρ)) R := by
  obtain ⟨L', R', hdL', hdR', hval⟩ :=
    (henv.nat_ops c hc cv v hint hf).2 eq heq
  obtain rfl : L' = L := Option.some.inj (hdL'.symm.trans hdL)
  obtain rfl : R' = R := Option.some.inj (hdR'.symm.trans hdR)
  exact hval ρ x y hx hy

/-! ### The per-operation value recurrences

Each operation's block: the guard's dependency facts name the stored
heads, the concrete equations denote by computation, `natEq_value`
reads them at value slots, and a literal meta-induction assembles the
closed-form (`natLit_*`'s content, inlined over the `interp`-values —
the model's `natLitVal` indirection is not needed because
`⟦natLitV (n+1)⟧ = app ⟦succ⟧ ⟦natLitV n⟧` is syntactic). -/

section PerOp

/-- `Nat.pred` on literal values. -/
theorem natOpV_pred (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natPredName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a : Nat,
      SetTheory.app (interp V ρ (cval natPredName (Level.substFn φ [] [])))
        (interp V ρ (natLitV cval φ a))
      = interp V ρ (natLitV cval φ (a - 1)) := by
  obtain ⟨hg, -⟩ := henv.nat_ops natPredName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvp, vp, hp, hfp, hlpp⟩ := hdeps natPredName (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := natLitSupported_inv hs
  have hKp := denote_const_mono (cval := cval) (φ := φ) hfp hlpp
  have hKz := denote_const_mono (cval := cval) (φ := φ) hfZ hlpZ
  have hKs := denote_const_mono (cval := cval) (φ := φ) hfS hlpS
  have hzm := (natLit_facts henv hs ρ 0).2
  -- base clause
  have h0 : SetTheory.app
      (interp V ρ (cval natPredName (Level.substFn φ [] [])))
      (interp V ρ (cval natZeroName (Level.substFn φ [] [])))
      = interp V ρ (cval natZeroName (Level.substFn φ [] [])) := by
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.const natPredName []) (.const natZeroName []),
        .const natZeroName []))
      (by decide)
      (L := .app (cval natPredName (Level.substFn φ [] []))
        (cval natZeroName (Level.substFn φ [] [])))
      (R := cval natZeroName (Level.substFn φ [] []))
      (by rw [denote_app, hKp 2, hKz 2]) (hKz 2) hzm hzm
    simp only [interp_app,
      interp_cons2 (henv.cval_closed natPredName _),
      interp_cons2 (henv.cval_closed natZeroName _)] at h
    exact h
  -- successor clause
  have hS : ∀ x : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app
        (interp V ρ (cval natPredName (Level.substFn φ [] [])))
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) x)
      = x := by
    intro x hx
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.const natPredName [])
          (.app (.const natSuccName [])
            (.fvar 0 (.str .anonymous "x") (.const natName []))),
        .fvar 0 (.str .anonymous "x") (.const natName [])))
      (by decide)
      (L := .app (cval natPredName (Level.substFn φ [] []))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 1)))
      (R := .bvar 1)
      (by rw [denote_app, hKp 2, denote_app, hKs 2, denote_fvar])
      (by rw [denote_fvar]) hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natPredName _),
      interp_cons2 (henv.cval_closed natSuccName _)] at h
    exact h
  intro a
  match a with
  | 0 => exact h0
  | a + 1 =>
    have h := hS (interp V ρ (natLitV cval φ a))
      (natLit_facts henv hs ρ a).2
    show SetTheory.app _
      (interp V ρ (.app (succV cval φ) (natLitV cval φ a))) = _
    rw [interp_app, succV_eq]
    simpa using h

/-- The common shape of the six binary structural recurrences: a base
clause at `y = 0` and a successor clause, assembled by induction on
the second literal.  `res` is the closed-form. -/
theorem natOpV_bin_of_clauses
    {opv : V} {ρ : Nat → V} (res : Nat → Nat → Nat)
    (h0 : ∀ a : Nat,
      SetTheory.app (SetTheory.app opv (interp V ρ (natLitV cval φ a)))
        (interp V ρ (cval natZeroName (Level.substFn φ [] [])))
      = interp V ρ (natLitV cval φ (res a 0)))
    (hSb : ∀ (a b : Nat),
      SetTheory.app (SetTheory.app opv (interp V ρ (natLitV cval φ a)))
          (interp V ρ (natLitV cval φ b))
        = interp V ρ (natLitV cval φ (res a b)) →
      SetTheory.app (SetTheory.app opv (interp V ρ (natLitV cval φ a)))
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
          (interp V ρ (natLitV cval φ b)))
      = interp V ρ (natLitV cval φ (res a (b + 1)))) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app opv (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b))
      = interp V ρ (natLitV cval φ (res a b)) := by
  intro a b
  induction b with
  | zero => exact h0 a
  | succ b ih =>
    show SetTheory.app _
      (interp V ρ (.app (succV cval φ) (natLitV cval φ b))) = _
    rw [interp_app, succV_eq]
    exact hSb a b ih

/-- The two clauses of a binary structural recurrence whose equations
are `(op x 0 = base x, op x (succ y) = step (op x y))`-shaped, read at
values.  `hbase`/`hstep` are the two equations' computed value
readings. -/
theorem natOpV_bin_clauses (henv : EnvSHyp V env cval φ) {c : Name}
    (hc : c ∈ natOpNames) {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv v hint))
    {L₁ R₁ L₂ R₂ : VExpr} {e₁ e₂ f₁ f₂ : Expr}
    (heq₁ : (e₁, f₁) ∈ natOpEquations 0 c)
    (heq₂ : (e₂, f₂) ∈ natOpEquations 0 c)
    (hdL₁ : denote cval env φ 2 e₁ = some L₁)
    (hdR₁ : denote cval env φ 2 f₁ = some R₁)
    (hdL₂ : denote cval env φ 2 e₂ = some L₂)
    (hdR₂ : denote cval env φ 2 f₂ = some R₂)
    {ρ : Nat → V} {x y : V}
    (hx : x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])))
    (hy : y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] []))) :
    interp V (cons V y (cons V x ρ)) L₁
        = interp V (cons V y (cons V x ρ)) R₁ ∧
    interp V (cons V y (cons V x ρ)) L₂
        = interp V (cons V y (cons V x ρ)) R₂ :=
  ⟨natEq_value henv hc hf heq₁ hdL₁ hdR₁ hx hy,
   natEq_value henv hc hf heq₂ hdL₂ hdR₂ hx hy⟩

/-- `Nat.add` on literal values. -/
theorem natOpV_add (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natAddName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natAddName (Level.substFn φ [] [])))
          (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b))
      = interp V ρ (natLitV cval φ (a + b)) := by
  obtain ⟨hg, -⟩ := henv.nat_ops natAddName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps natAddName (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := natLitSupported_inv hs
  have hKc := denote_const_mono (cval := cval) (φ := φ) hfc hlpc
  have hKz := denote_const_mono (cval := cval) (φ := φ) hfZ hlpZ
  have hKs := denote_const_mono (cval := cval) (φ := φ) hfS hlpS
  have hzm := (natLit_facts henv hs ρ 0).2
  have h0 : ∀ x : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natAddName (Level.substFn φ [] []))) x)
        (interp V ρ (cval natZeroName (Level.substFn φ [] [])))
      = x := by
    intro x hx
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natAddName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.const natZeroName []),
        .fvar 0 (.str .anonymous "x") (.const natName [])))
      (by decide)
      (L := .app (.app (cval natAddName (Level.substFn φ [] []))
          (.bvar 1)) (cval natZeroName (Level.substFn φ [] [])))
      (R := .bvar 1)
      (by rw [denote_app, denote_app, hKc 2, denote_fvar, hKz 2])
      (by rw [denote_fvar]) hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natAddName _),
      interp_cons2 (henv.cval_closed natZeroName _)] at h
    exact h
  have hSb : ∀ x y : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natAddName (Level.substFn φ [] []))) x)
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) y)
      = SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
          (SetTheory.app (SetTheory.app
            (interp V ρ (cval natAddName (Level.substFn φ [] []))) x)
            y) := by
    intro x y hx hy
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natAddName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.app (.const natSuccName [])
            (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.const natSuccName [])
          (.app (.app (.const natAddName [])
            (.fvar 0 (.str .anonymous "x") (.const natName [])))
            (.fvar 1 (.str .anonymous "y") (.const natName [])))))
      (by decide)
      (L := .app (.app (cval natAddName (Level.substFn φ [] []))
          (.bvar 1))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 0)))
      (R := .app (cval natSuccName (Level.substFn φ [] []))
        (.app (.app (cval natAddName (Level.substFn φ [] []))
          (.bvar 1)) (.bvar 0)))
      (by rw [denote_app, denote_app, hKc 2, denote_fvar, denote_app,
        hKs 2, denote_fvar])
      (by rw [denote_app, hKs 2, denote_app, denote_app, hKc 2,
        denote_fvar, denote_fvar]) hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natAddName _),
      interp_cons2 (henv.cval_closed natSuccName _)] at h
    exact h
  refine natOpV_bin_of_clauses (fun a b => a + b) ?_ ?_
  · intro a
    exact h0 _ (natLit_facts henv hs ρ a).2
  · intro a b ih
    rw [hSb _ _ (natLit_facts henv hs ρ a).2
      (natLit_facts henv hs ρ b).2, ih]
    rfl

/-- `Nat.sub` on literal values. -/
theorem natOpV_sub (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natSubName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natSubName (Level.substFn φ [] [])))
          (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b))
      = interp V ρ (natLitV cval φ (a - b)) := by
  obtain ⟨hg, -⟩ := henv.nat_ops natSubName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps natSubName (by decide)
  obtain ⟨cvp, vp, hpnt, hfp, hlpp⟩ := hdeps natPredName (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := natLitSupported_inv hs
  have hKc := denote_const_mono (cval := cval) (φ := φ) hfc hlpc
  have hKp := denote_const_mono (cval := cval) (φ := φ) hfp hlpp
  have hKz := denote_const_mono (cval := cval) (φ := φ) hfZ hlpZ
  have hKs := denote_const_mono (cval := cval) (φ := φ) hfS hlpS
  have hzm := (natLit_facts henv hs ρ 0).2
  have h0 : ∀ x : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natSubName (Level.substFn φ [] []))) x)
        (interp V ρ (cval natZeroName (Level.substFn φ [] [])))
      = x := by
    intro x hx
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natSubName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.const natZeroName []),
        .fvar 0 (.str .anonymous "x") (.const natName [])))
      (by decide)
      (L := .app (.app (cval natSubName (Level.substFn φ [] []))
          (.bvar 1)) (cval natZeroName (Level.substFn φ [] [])))
      (R := .bvar 1)
      (by rw [denote_app, denote_app, hKc 2, denote_fvar, hKz 2])
      (by rw [denote_fvar]) hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natSubName _),
      interp_cons2 (henv.cval_closed natZeroName _)] at h
    exact h
  have hSb : ∀ x y : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natSubName (Level.substFn φ [] []))) x)
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) y)
      = SetTheory.app
          (interp V ρ (cval natPredName (Level.substFn φ [] [])))
          (SetTheory.app (SetTheory.app
            (interp V ρ (cval natSubName (Level.substFn φ [] []))) x)
            y) := by
    intro x y hx hy
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natSubName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.app (.const natSuccName [])
            (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.const natPredName [])
          (.app (.app (.const natSubName [])
            (.fvar 0 (.str .anonymous "x") (.const natName [])))
            (.fvar 1 (.str .anonymous "y") (.const natName [])))))
      (by decide)
      (L := .app (.app (cval natSubName (Level.substFn φ [] []))
          (.bvar 1))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 0)))
      (R := .app (cval natPredName (Level.substFn φ [] []))
        (.app (.app (cval natSubName (Level.substFn φ [] []))
          (.bvar 1)) (.bvar 0)))
      (by rw [denote_app, denote_app, hKc 2, denote_fvar, denote_app,
        hKs 2, denote_fvar])
      (by rw [denote_app, hKp 2, denote_app, denote_app, hKc 2,
        denote_fvar, denote_fvar]) hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natSubName _),
      interp_cons2 (henv.cval_closed natSuccName _),
      interp_cons2 (henv.cval_closed natPredName _)] at h
    exact h
  refine natOpV_bin_of_clauses (fun a b => a - b) ?_ ?_
  · intro a
    exact h0 _ (natLit_facts henv hs ρ a).2
  · intro a b ih
    rw [hSb _ _ (natLit_facts henv hs ρ a).2
      (natLit_facts henv hs ρ b).2, ih,
      natOpV_pred henv hfp ρ (a - b)]
    rfl

/-- `Nat.mul` on literal values. -/
theorem natOpV_mul (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natMulName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natMulName (Level.substFn φ [] [])))
          (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b))
      = interp V ρ (natLitV cval φ (a * b)) := by
  obtain ⟨hg, -⟩ := henv.nat_ops natMulName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps natMulName (by decide)
  obtain ⟨cva, va, hant, hfa, hlpa⟩ := hdeps natAddName (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := natLitSupported_inv hs
  have hKc := denote_const_mono (cval := cval) (φ := φ) hfc hlpc
  have hKa := denote_const_mono (cval := cval) (φ := φ) hfa hlpa
  have hKz := denote_const_mono (cval := cval) (φ := φ) hfZ hlpZ
  have hKs := denote_const_mono (cval := cval) (φ := φ) hfS hlpS
  have hzm := (natLit_facts henv hs ρ 0).2
  have h0 : ∀ x : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natMulName (Level.substFn φ [] []))) x)
        (interp V ρ (cval natZeroName (Level.substFn φ [] [])))
      = interp V ρ (cval natZeroName (Level.substFn φ [] [])) := by
    intro x hx
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natMulName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.const natZeroName []),
        .const natZeroName []))
      (by decide)
      (L := .app (.app (cval natMulName (Level.substFn φ [] []))
          (.bvar 1)) (cval natZeroName (Level.substFn φ [] [])))
      (R := cval natZeroName (Level.substFn φ [] []))
      (by rw [denote_app, denote_app, hKc 2, denote_fvar, hKz 2])
      (hKz 2) hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natMulName _),
      interp_cons2 (henv.cval_closed natZeroName _)] at h
    exact h
  have hSb : ∀ x y : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natMulName (Level.substFn φ [] []))) x)
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) y)
      = SetTheory.app (SetTheory.app
          (interp V ρ (cval natAddName (Level.substFn φ [] [])))
          (SetTheory.app (SetTheory.app
            (interp V ρ (cval natMulName (Level.substFn φ [] []))) x)
            y)) x := by
    intro x y hx hy
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natMulName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.app (.const natSuccName [])
            (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.app (.const natAddName [])
          (.app (.app (.const natMulName [])
            (.fvar 0 (.str .anonymous "x") (.const natName [])))
            (.fvar 1 (.str .anonymous "y") (.const natName []))))
          (.fvar 0 (.str .anonymous "x") (.const natName []))))
      (by decide)
      (L := .app (.app (cval natMulName (Level.substFn φ [] []))
          (.bvar 1))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 0)))
      (R := .app (.app (cval natAddName (Level.substFn φ [] []))
        (.app (.app (cval natMulName (Level.substFn φ [] []))
          (.bvar 1)) (.bvar 0))) (.bvar 1))
      (by rw [denote_app, denote_app, hKc 2, denote_fvar, denote_app,
        hKs 2, denote_fvar])
      (by simp only [denote_app, hKa 2, hKc 2, denote_fvar]) hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natMulName _),
      interp_cons2 (henv.cval_closed natSuccName _),
      interp_cons2 (henv.cval_closed natAddName _)] at h
    exact h
  refine natOpV_bin_of_clauses (fun a b => a * b) ?_ ?_
  · intro a
    exact h0 _ (natLit_facts henv hs ρ a).2
  · intro a b ih
    rw [hSb _ _ (natLit_facts henv hs ρ a).2
      (natLit_facts henv hs ρ b).2, ih,
      natOpV_add henv hfa ρ (a * b) a]
    rfl

/-- `Nat.pow` on literal values. -/
theorem natOpV_pow (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natPowName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natPowName (Level.substFn φ [] [])))
          (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b))
      = interp V ρ (natLitV cval φ (a ^ b)) := by
  obtain ⟨hg, -⟩ := henv.nat_ops natPowName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps natPowName (by decide)
  obtain ⟨cvm, vm, hmnt, hfm, hlpm⟩ := hdeps natMulName (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := natLitSupported_inv hs
  have hKc := denote_const_mono (cval := cval) (φ := φ) hfc hlpc
  have hKm := denote_const_mono (cval := cval) (φ := φ) hfm hlpm
  have hKz := denote_const_mono (cval := cval) (φ := φ) hfZ hlpZ
  have hKs := denote_const_mono (cval := cval) (φ := φ) hfS hlpS
  have hzm := (natLit_facts henv hs ρ 0).2
  have h0 : ∀ x : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natPowName (Level.substFn φ [] []))) x)
        (interp V ρ (cval natZeroName (Level.substFn φ [] [])))
      = SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
          (interp V ρ (cval natZeroName (Level.substFn φ [] []))) := by
    intro x hx
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natPowName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.const natZeroName []),
        .app (.const natSuccName []) (.const natZeroName [])))
      (by decide)
      (L := .app (.app (cval natPowName (Level.substFn φ [] []))
          (.bvar 1)) (cval natZeroName (Level.substFn φ [] [])))
      (R := .app (cval natSuccName (Level.substFn φ [] []))
        (cval natZeroName (Level.substFn φ [] [])))
      (by rw [denote_app, denote_app, hKc 2, denote_fvar, hKz 2])
      (by rw [denote_app, hKs 2, hKz 2]) hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natPowName _),
      interp_cons2 (henv.cval_closed natZeroName _),
      interp_cons2 (henv.cval_closed natSuccName _)] at h
    exact h
  have hSb : ∀ x y : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natPowName (Level.substFn φ [] []))) x)
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) y)
      = SetTheory.app (SetTheory.app
          (interp V ρ (cval natMulName (Level.substFn φ [] [])))
          (SetTheory.app (SetTheory.app
            (interp V ρ (cval natPowName (Level.substFn φ [] []))) x)
            y)) x := by
    intro x y hx hy
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natPowName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.app (.const natSuccName [])
            (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.app (.const natMulName [])
          (.app (.app (.const natPowName [])
            (.fvar 0 (.str .anonymous "x") (.const natName [])))
            (.fvar 1 (.str .anonymous "y") (.const natName []))))
          (.fvar 0 (.str .anonymous "x") (.const natName []))))
      (by decide)
      (L := .app (.app (cval natPowName (Level.substFn φ [] []))
          (.bvar 1))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 0)))
      (R := .app (.app (cval natMulName (Level.substFn φ [] []))
        (.app (.app (cval natPowName (Level.substFn φ [] []))
          (.bvar 1)) (.bvar 0))) (.bvar 1))
      (by rw [denote_app, denote_app, hKc 2, denote_fvar, denote_app,
        hKs 2, denote_fvar])
      (by simp only [denote_app, hKm 2, hKc 2, denote_fvar]) hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natPowName _),
      interp_cons2 (henv.cval_closed natSuccName _),
      interp_cons2 (henv.cval_closed natMulName _)] at h
    exact h
  refine natOpV_bin_of_clauses (fun a b => a ^ b) ?_ ?_
  · intro a
    exact h0 _ (natLit_facts henv hs ρ a).2
  · intro a b ih
    rw [hSb _ _ (natLit_facts henv hs ρ a).2
      (natLit_facts henv hs ρ b).2, ih,
      natOpV_mul henv hfm ρ (a ^ b) a]
    rfl

/-- `Nat.beq` on literal values. -/
theorem natOpV_beq (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natBeqName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natBeqName (Level.substFn φ [] [])))
          (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b))
      = interp V ρ (cval (if a = b then boolTrueName else boolFalseName)
          (Level.substFn φ [] [])) := by
  obtain ⟨hg, -⟩ := henv.nat_ops natBeqName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
  obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ := hbool (Or.inl rfl)
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps natBeqName (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := natLitSupported_inv hs
  have hKc := denote_const_mono (cval := cval) (φ := φ) hfc hlpc
  have hKz := denote_const_mono (cval := cval) (φ := φ) hfZ hlpZ
  have hKs := denote_const_mono (cval := cval) (φ := φ) hfS hlpS
  have hKT := denote_const_mono (cval := cval) (φ := φ) hfT hlpT
  have hKF := denote_const_mono (cval := cval) (φ := φ) hfF hlpF
  have hzm := (natLit_facts henv hs ρ 0).2
  -- the four clauses at values
  have h00 : SetTheory.app (SetTheory.app
      (interp V ρ (cval natBeqName (Level.substFn φ [] [])))
      (interp V ρ (cval natZeroName (Level.substFn φ [] []))))
      (interp V ρ (cval natZeroName (Level.substFn φ [] [])))
      = interp V ρ (cval boolTrueName (Level.substFn φ [] [])) := by
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natBeqName []) (.const natZeroName []))
        (.const natZeroName []), .const boolTrueName []))
      (by decide)
      (L := .app (.app (cval natBeqName (Level.substFn φ [] []))
        (cval natZeroName (Level.substFn φ [] [])))
        (cval natZeroName (Level.substFn φ [] [])))
      (R := cval boolTrueName (Level.substFn φ [] []))
      (by rw [denote_app, denote_app, hKc 2, hKz 2]) (hKT 2) hzm hzm
    simp only [interp_app,
      interp_cons2 (henv.cval_closed natBeqName _),
      interp_cons2 (henv.cval_closed natZeroName _),
      interp_cons2 (henv.cval_closed boolTrueName _)] at h
    exact h
  have h0S : ∀ y : V,
      y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
        (interp V ρ (cval natBeqName (Level.substFn φ [] [])))
        (interp V ρ (cval natZeroName (Level.substFn φ [] []))))
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) y)
      = interp V ρ (cval boolFalseName (Level.substFn φ [] [])) := by
    intro y hy
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natBeqName []) (.const natZeroName []))
        (.app (.const natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .const boolFalseName []))
      (by decide)
      (L := .app (.app (cval natBeqName (Level.substFn φ [] []))
        (cval natZeroName (Level.substFn φ [] [])))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 0)))
      (R := cval boolFalseName (Level.substFn φ [] []))
      (by rw [denote_app, denote_app, hKc 2, hKz 2, denote_app, hKs 2,
        denote_fvar]) (hKF 2) hzm hy
    simp only [interp_app, interp_bvar, cons_zero,
      interp_cons2 (henv.cval_closed natBeqName _),
      interp_cons2 (henv.cval_closed natZeroName _),
      interp_cons2 (henv.cval_closed natSuccName _),
      interp_cons2 (henv.cval_closed boolFalseName _)] at h
    exact h
  have hS0 : ∀ x : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
        (interp V ρ (cval natBeqName (Level.substFn φ [] [])))
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) x))
        (interp V ρ (cval natZeroName (Level.substFn φ [] [])))
      = interp V ρ (cval boolFalseName (Level.substFn φ [] [])) := by
    intro x hx
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natBeqName [])
        (.app (.const natSuccName [])
          (.fvar 0 (.str .anonymous "x") (.const natName []))))
        (.const natZeroName []),
        .const boolFalseName []))
      (by decide)
      (L := .app (.app (cval natBeqName (Level.substFn φ [] []))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 1)))
        (cval natZeroName (Level.substFn φ [] [])))
      (R := cval boolFalseName (Level.substFn φ [] []))
      (by rw [denote_app, denote_app, hKc 2, denote_app, hKs 2,
        denote_fvar, hKz 2]) (hKF 2) hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natBeqName _),
      interp_cons2 (henv.cval_closed natZeroName _),
      interp_cons2 (henv.cval_closed natSuccName _),
      interp_cons2 (henv.cval_closed boolFalseName _)] at h
    exact h
  have hSS : ∀ x y : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
        (interp V ρ (cval natBeqName (Level.substFn φ [] [])))
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) x))
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) y)
      = SetTheory.app (SetTheory.app
          (interp V ρ (cval natBeqName (Level.substFn φ [] []))) x)
          y := by
    intro x y hx hy
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natBeqName [])
        (.app (.const natSuccName [])
          (.fvar 0 (.str .anonymous "x") (.const natName []))))
        (.app (.const natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.app (.const natBeqName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.fvar 1 (.str .anonymous "y") (.const natName []))))
      (by decide)
      (L := .app (.app (cval natBeqName (Level.substFn φ [] []))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 1)))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 0)))
      (R := .app (.app (cval natBeqName (Level.substFn φ [] []))
        (.bvar 1)) (.bvar 0))
      (by rw [denote_app, denote_app, hKc 2, denote_app, hKs 2,
        denote_fvar, denote_app, hKs 2, denote_fvar])
      (by rw [denote_app, denote_app, hKc 2, denote_fvar, denote_fvar])
      hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natBeqName _),
      interp_cons2 (henv.cval_closed natSuccName _)] at h
    exact h
  intro a
  induction a with
  | zero =>
    intro b
    match b with
    | 0 => rw [natLitV_zero]; exact h00
    | b + 1 =>
      show SetTheory.app _
        (interp V ρ (.app (succV cval φ) (natLitV cval φ b))) = _
      rw [natLitV_zero, interp_app, succV_eq,
        h0S _ (natLit_facts henv hs ρ b).2, if_neg (by omega)]
  | succ a ih =>
    intro b
    match b with
    | 0 =>
      show SetTheory.app (SetTheory.app _
        (interp V ρ (.app (succV cval φ) (natLitV cval φ a)))) _ = _
      rw [natLitV_zero, interp_app, succV_eq,
        hS0 _ (natLit_facts henv hs ρ a).2, if_neg (by omega)]
    | b + 1 =>
      show SetTheory.app (SetTheory.app _
        (interp V ρ (.app (succV cval φ) (natLitV cval φ a))))
        (interp V ρ (.app (succV cval φ) (natLitV cval φ b))) = _
      rw [interp_app, interp_app, succV_eq,
        hSS _ _ (natLit_facts henv hs ρ a).2 (natLit_facts henv hs ρ b).2,
        ih b]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos (by omega)]
      · rw [if_neg hab, if_neg (by omega)]

/-- `Nat.ble` on literal values. -/
theorem natOpV_ble (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natBleName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (cval natBleName (Level.substFn φ [] [])))
          (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b))
      = interp V ρ (cval (if a ≤ b then boolTrueName else boolFalseName)
          (Level.substFn φ [] [])) := by
  obtain ⟨hg, -⟩ := henv.nat_ops natBleName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
  obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ := hbool (Or.inr (Or.inl rfl))
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps natBleName (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := natLitSupported_inv hs
  have hKc := denote_const_mono (cval := cval) (φ := φ) hfc hlpc
  have hKz := denote_const_mono (cval := cval) (φ := φ) hfZ hlpZ
  have hKs := denote_const_mono (cval := cval) (φ := φ) hfS hlpS
  have hKT := denote_const_mono (cval := cval) (φ := φ) hfT hlpT
  have hKF := denote_const_mono (cval := cval) (φ := φ) hfF hlpF
  have hzm := (natLit_facts henv hs ρ 0).2
  have h0y : ∀ y : V,
      y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
        (interp V ρ (cval natBleName (Level.substFn φ [] [])))
        (interp V ρ (cval natZeroName (Level.substFn φ [] [])))) y
      = interp V ρ (cval boolTrueName (Level.substFn φ [] [])) := by
    intro y hy
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natBleName []) (.const natZeroName []))
        (.fvar 1 (.str .anonymous "y") (.const natName [])),
        .const boolTrueName []))
      (by decide)
      (L := .app (.app (cval natBleName (Level.substFn φ [] []))
        (cval natZeroName (Level.substFn φ [] []))) (.bvar 0))
      (R := cval boolTrueName (Level.substFn φ [] []))
      (by rw [denote_app, denote_app, hKc 2, hKz 2, denote_fvar])
      (hKT 2) hzm hy
    simp only [interp_app, interp_bvar, cons_zero,
      interp_cons2 (henv.cval_closed natBleName _),
      interp_cons2 (henv.cval_closed natZeroName _),
      interp_cons2 (henv.cval_closed boolTrueName _)] at h
    exact h
  have hS0 : ∀ x : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
        (interp V ρ (cval natBleName (Level.substFn φ [] [])))
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) x))
        (interp V ρ (cval natZeroName (Level.substFn φ [] [])))
      = interp V ρ (cval boolFalseName (Level.substFn φ [] [])) := by
    intro x hx
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natBleName [])
        (.app (.const natSuccName [])
          (.fvar 0 (.str .anonymous "x") (.const natName []))))
        (.const natZeroName []),
        .const boolFalseName []))
      (by decide)
      (L := .app (.app (cval natBleName (Level.substFn φ [] []))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 1)))
        (cval natZeroName (Level.substFn φ [] [])))
      (R := cval boolFalseName (Level.substFn φ [] []))
      (by rw [denote_app, denote_app, hKc 2, denote_app, hKs 2,
        denote_fvar, hKz 2]) (hKF 2) hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natBleName _),
      interp_cons2 (henv.cval_closed natZeroName _),
      interp_cons2 (henv.cval_closed natSuccName _),
      interp_cons2 (henv.cval_closed boolFalseName _)] at h
    exact h
  have hSS : ∀ x y : V,
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      SetTheory.app (SetTheory.app
        (interp V ρ (cval natBleName (Level.substFn φ [] [])))
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) x))
        (SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] []))) y)
      = SetTheory.app (SetTheory.app
          (interp V ρ (cval natBleName (Level.substFn φ [] []))) x)
          y := by
    intro x y hx hy
    have h := natEq_value henv (by decide) hf
      (eq := (.app (.app (.const natBleName [])
        (.app (.const natSuccName [])
          (.fvar 0 (.str .anonymous "x") (.const natName []))))
        (.app (.const natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.app (.const natBleName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.fvar 1 (.str .anonymous "y") (.const natName []))))
      (by decide)
      (L := .app (.app (cval natBleName (Level.substFn φ [] []))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 1)))
        (.app (cval natSuccName (Level.substFn φ [] [])) (.bvar 0)))
      (R := .app (.app (cval natBleName (Level.substFn φ [] []))
        (.bvar 1)) (.bvar 0))
      (by rw [denote_app, denote_app, hKc 2, denote_app, hKs 2,
        denote_fvar, denote_app, hKs 2, denote_fvar])
      (by rw [denote_app, denote_app, hKc 2, denote_fvar, denote_fvar])
      hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      interp_cons2 (henv.cval_closed natBleName _),
      interp_cons2 (henv.cval_closed natSuccName _)] at h
    exact h
  intro a
  induction a with
  | zero =>
    intro b
    rw [natLitV_zero, h0y _ (natLit_facts henv hs ρ b).2,
      if_pos (Nat.zero_le b)]
  | succ a ih =>
    intro b
    match b with
    | 0 =>
      show SetTheory.app (SetTheory.app _
        (interp V ρ (.app (succV cval φ) (natLitV cval φ a)))) _ = _
      rw [natLitV_zero, interp_app, succV_eq,
        hS0 _ (natLit_facts henv hs ρ a).2, if_neg (by omega)]
    | b + 1 =>
      show SetTheory.app (SetTheory.app _
        (interp V ρ (.app (succV cval φ) (natLitV cval φ a))))
        (interp V ρ (.app (succV cval φ) (natLitV cval φ b))) = _
      rw [interp_app, interp_app, succV_eq,
        hSS _ _ (natLit_facts henv hs ρ a).2 (natLit_facts henv hs ρ b).2,
        ih b]
      by_cases hab : a ≤ b
      · rw [if_pos hab, if_pos (by omega)]
      · rw [if_neg hab, if_neg (by omega)]

end PerOp

end Cases

end Setlec.SetR
