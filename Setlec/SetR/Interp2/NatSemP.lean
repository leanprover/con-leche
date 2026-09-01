import Setlec.SetR.Interp2.NatEqsP

/-!
# The numeral transports at `interp2` (task #161, literal tier)

`Sound/NatOps.lean`'s literal meta-inductions, re-proved at the
validated-annotation currency: the stored structural operations'
closed forms on `denoteP`'s own numeral spine, standing on the
`EnvS2PM.nat_ops` recurrence law (the run-certificate product of
`NatEqsP.lean`) instead of the collapse-lane `EnvSHyp.nat_ops`.

The value environment plumbing is one degree simpler than v1's: every
head leaf is closed, so the two-slot extension collapses through
`acval_interp2_closedC`, and the numeral spine is `denoteP`'s literal
clause verbatim (`natLitP` below **is** `denoteP_natLit`'s output).

Worked example: `natOpV2_add` (the lead-proved species).  The other
six structural operations follow the same recipe: read the two
recurrence clauses at values (`natEq_valueP` at computed `denoteP`
readings), close by the literal meta-induction
(`natOpV2_bin_of_clauses` for the binary `(op x 0, op x (succ y))`
shape).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}

/-! ## The numeral spine, and its facts -/

/-- The numeral spine at an environment's `Nat` heads — exactly
`denoteP`'s `.lit (.natVal n)` clause. -/
def natLitP {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (n : Nat) : AVExpr :=
  natLitT2 (m.acval Setlec.natZeroName φ)
    (m.acval Setlec.natSuccName φ) n

/-- The literal clause reads to the spine. -/
theorem denoteP_natLitP (m : EnvS2Core V env)
    (hs : natLitSupported env = true) (d n : Nat) :
    denoteP m.acval env φ d (.lit (.natVal n))
      = some (natLitP m φ n) := by
  rw [denoteP_natLit hs, substFn_nil]
  rfl

/-- The successor unfolding is syntactic. -/
theorem natLitP_succ (m : EnvS2Core V env) (n : Nat) :
    natLitP m φ (n + 1)
      = .app (m.acval Setlec.natSuccName φ) (natLitP m φ n) := rfl

/-- The zero numeral is the zero leaf (definitional). -/
theorem natLitP_zero (m : EnvS2Core V env) :
    natLitP m φ 0 = m.acval Setlec.natZeroName φ := rfl

/-- Numerals inhabit the stored `Nat` and are graded
(`natLit_facts2` at the environment's heads). -/
theorem natLitP_facts (m : EnvS2Core V env) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m) (hs : natLitSupported env = true)
    (ρ : Nat → V) (n : Nat) :
    AnnotOkP V ρ (natLitP m φ n) ∧
      interp2 V ρ (natLitP m φ n)
        ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) := by
  obtain ⟨hz, hsucc⟩ := hnh hs ρ
  rw [substFn_nil] at hz hsucc
  have h := natLit_facts2 (V := V)
    (za := m.acval Setlec.natZeroName φ)
    (sa := m.acval Setlec.natSuccName φ)
    (natA := m.acval Setlec.natName φ)
    (m.acval_ok2 _ _ ρ) (m.acval_ok2 _ _ ρ) hz hsucc n
  exact ⟨⟨h.1, AnnotValidV_natLitT2 (hval _ _ ρ) (hval _ _ ρ) n⟩, h.2⟩

/-- Numeral membership alone (the induction's staple). -/
theorem natLitP_mem (m : EnvS2Core V env) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m) (hs : natLitSupported env = true)
    (ρ : Nat → V) (n : Nat) :
    interp2 V ρ (natLitP m φ n)
      ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) :=
  (natLitP_facts m hnh hval hs ρ n).2

/-- The spine's interpretation ignores the two-slot extension: its
leaves are closed. -/
theorem interp2_cons2_natLitP (m : EnvS2Core V env)
    (ρ : Nat → V) (x y : V) (n : Nat) :
    interp2 V (cons y (cons x ρ)) (natLitP m φ n)
      = interp2 V ρ (natLitP m φ n) := by
  induction n with
  | zero => exact acval_interp2_closedC m _ _ _ ρ
  | succ n ih =>
    simp only [natLitP_succ, interp2_app]
    rw [ih, acval_interp2_closedC m Setlec.natSuccName _ _ ρ]

/-! ## Reading one recurrence at values -/

/-- One certified recurrence equation, read at value slots
(`natEq_value`'s mirror over `NatOpsP`). -/
theorem natEq_valueP (m : EnvS2Core V env) (hops : NatOpsP m φ)
    {c : Name} (hc : c ∈ Setlec.natOpNames) {cv : ConstantVal}
    {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv v hint))
    {eq : Expr × Expr} (heq : eq ∈ Setlec.natOpEquations 0 c)
    {L R : AVExpr}
    (hdL : denoteP m.acval env φ 2 eq.1 = some L)
    (hdR : denoteP m.acval env φ 2 eq.2 = some R)
    {ρ : Nat → V} {x y : V}
    (hx : x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ))
    (hy : y ∈ˢ interp2 V ρ (m.acval Setlec.natName φ)) :
    interp2 V (cons y (cons x ρ)) L
      = interp2 V (cons y (cons x ρ)) R := by
  obtain ⟨L', R', hdL', hdR', hval⟩ :=
    (hops c hc cv v hint hf).2 eq heq
  obtain rfl : L' = L := Option.some.inj (hdL'.symm.trans hdL)
  obtain rfl : R' = R := Option.some.inj (hdR'.symm.trans hdR)
  exact hval ρ x y hx hy

/-! ## The binary meta-induction -/

/-- The common shape of the binary structural recurrences: a base
clause at `y = 0` and a successor clause, assembled by induction on
the second literal (`natOpV_bin_of_clauses`, transposed). -/
theorem natOpV2_bin_of_clauses (m : EnvS2Core V env)
    {opv : V} {ρ : Nat → V} (res : Nat → Nat → Nat)
    (h0 : ∀ a : Nat,
      SetTheory.app (SetTheory.app opv
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (m.acval Setlec.natZeroName φ))
      = interp2 V ρ (natLitP m φ (res a 0)))
    (hSb : ∀ (a b : Nat),
      SetTheory.app (SetTheory.app opv
          (interp2 V ρ (natLitP m φ a)))
          (interp2 V ρ (natLitP m φ b))
        = interp2 V ρ (natLitP m φ (res a b)) →
      SetTheory.app (SetTheory.app opv
          (interp2 V ρ (natLitP m φ a)))
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ))
          (interp2 V ρ (natLitP m φ b)))
      = interp2 V ρ (natLitP m φ (res a (b + 1)))) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app opv
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (res a b)) := by
  intro a b
  induction b with
  | zero => exact h0 a
  | succ b ih =>
    rw [natLitP_succ, interp2_app]
    exact hSb a b ih

/-! ## `Nat.add`, the worked example -/

/-- `Nat.add` on literal values (`natOpV_add`'s mirror). -/
theorem natOpV2_add (m : EnvS2Core V env) (hops : NatOpsP m φ)
    (hnh : NatHeadsP m φ) (hval : AcvalValidP m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Setlec.natAddName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natAddName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (a + b)) := by
  obtain ⟨hg, -⟩ := hops Setlec.natAddName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Setlec.natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps Setlec.natAddName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natAddName [])
      = some (m.acval Setlec.natAddName φ) :=
    fun d => denoteP_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKz : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natZeroName [])
      = some (m.acval Setlec.natZeroName φ) :=
    fun d => denoteP_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natSuccName [])
      = some (m.acval Setlec.natSuccName φ) :=
    fun d => denoteP_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hzm := natLitP_mem m hnh hval hs ρ 0
  -- base clause, read at values
  have h0 : ∀ x : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natAddName φ)) x)
        (interp2 V ρ (m.acval Setlec.natZeroName φ))
      = x := by
    intro x hx
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natAddName [])
          (.fvar 0 (.str .anonymous "x")
            (.const Setlec.natName [])))
        (.const Setlec.natZeroName []),
        .fvar 0 (.str .anonymous "x") (.const Setlec.natName [])))
      (by decide)
      (L := .app (.app (m.acval Setlec.natAddName φ) (.bvar 1))
        (m.acval Setlec.natZeroName φ))
      (R := .bvar 1)
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_fvar, hKz 2]
          rfl)
      (by rw [denoteP_fvar])
      hx hzm
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natAddName φ _ ρ,
      acval_interp2_closedC m Setlec.natZeroName φ _ ρ] at h
    exact h
  -- successor clause, read at values
  have hS : ∀ x y : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      y ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natAddName φ)) x)
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) y)
      = SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ))
          (SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Setlec.natAddName φ)) x) y) := by
    intro x y hx hy
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natAddName [])
          (.fvar 0 (.str .anonymous "x")
            (.const Setlec.natName [])))
        (.app (.const Setlec.natSuccName [])
          (.fvar 1 (.str .anonymous "y")
            (.const Setlec.natName []))),
        .app (.const Setlec.natSuccName [])
          (.app (.app (.const Setlec.natAddName [])
            (.fvar 0 (.str .anonymous "x")
              (.const Setlec.natName [])))
            (.fvar 1 (.str .anonymous "y")
              (.const Setlec.natName [])))))
      (by decide)
      (L := .app (.app (m.acval Setlec.natAddName φ) (.bvar 1))
        (.app (m.acval Setlec.natSuccName φ) (.bvar 0)))
      (R := .app (m.acval Setlec.natSuccName φ)
        (.app (.app (m.acval Setlec.natAddName φ) (.bvar 1))
          (.bvar 0)))
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_fvar,
            denoteP_app, hKs 2, denoteP_fvar]
          rfl)
      (by rw [denoteP_app, hKs 2, denoteP_app, denoteP_app, hKc 2,
            denoteP_fvar, denoteP_fvar]
          rfl)
      hx hy
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natAddName φ _ ρ,
      acval_interp2_closedC m Setlec.natSuccName φ _ ρ] at h
    exact h
  refine natOpV2_bin_of_clauses m (fun a b => a + b) (fun a => ?_)
    (fun a b ih => ?_)
  · exact h0 (interp2 V ρ (natLitP m φ a))
      (natLitP_mem m hnh hval hs ρ a)
  · rw [hS (interp2 V ρ (natLitP m φ a))
        (interp2 V ρ (natLitP m φ b))
        (natLitP_mem m hnh hval hs ρ a)
        (natLitP_mem m hnh hval hs ρ b), ih]
    rw [Nat.add_succ, natLitP_succ, interp2_app]

/-! ## The remaining structural operations

Mechanical mirrors of `Sound/NatOps.lean`'s `natOpV_*`, at the
currencies the module docstring lists.  `sub` reads `pred`'s closed
form, `mul` reads `add`'s, `pow` reads `mul`'s — each dependency's
`find?` comes from `natOpGuard_inv`'s `hdeps`. -/

/-- `Nat.pred` on literal values (`natOpV_pred`'s mirror). -/
theorem natOpV2_pred (m : EnvS2Core V env) (hops : NatOpsP m φ)
    (hnh : NatHeadsP m φ) (hval : AcvalValidP m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Setlec.natPredName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a : Nat,
      SetTheory.app (interp2 V ρ (m.acval Setlec.natPredName φ))
        (interp2 V ρ (natLitP m φ a))
      = interp2 V ρ (natLitP m φ (a - 1)) := by
  obtain ⟨hg, -⟩ := hops Setlec.natPredName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Setlec.natOpGuard_inv hg
  obtain ⟨cvp, vp, hp, hfp, hlpp⟩ := hdeps Setlec.natPredName (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  have hKp : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natPredName [])
      = some (m.acval Setlec.natPredName φ) :=
    fun d => denoteP_levelless_const hfp
      (show (ConstantInfo.defnInfo cvp vp hp).toConstantVal.levelParams
        = [] from hlpp)
  have hKz : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natZeroName [])
      = some (m.acval Setlec.natZeroName φ) :=
    fun d => denoteP_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natSuccName [])
      = some (m.acval Setlec.natSuccName φ) :=
    fun d => denoteP_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hzm := natLitP_mem m hnh hval hs ρ 0
  -- base clause, read at values
  have h0 : SetTheory.app
      (interp2 V ρ (m.acval Setlec.natPredName φ))
      (interp2 V ρ (m.acval Setlec.natZeroName φ))
      = interp2 V ρ (m.acval Setlec.natZeroName φ) := by
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.const Setlec.natPredName [])
          (.const Setlec.natZeroName []),
        .const Setlec.natZeroName []))
      (by decide)
      (L := .app (m.acval Setlec.natPredName φ)
        (m.acval Setlec.natZeroName φ))
      (R := m.acval Setlec.natZeroName φ)
      (by rw [denoteP_app, hKp 2, hKz 2]; rfl) (hKz 2) hzm hzm
    simp only [interp2_app,
      acval_interp2_closedC m Setlec.natPredName φ _ ρ,
      acval_interp2_closedC m Setlec.natZeroName φ _ ρ] at h
    exact h
  -- successor clause, read at values
  have hS : ∀ x : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (interp2 V ρ (m.acval Setlec.natPredName φ))
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) x)
      = x := by
    intro x hx
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.const Setlec.natPredName [])
          (.app (.const Setlec.natSuccName [])
            (.fvar 0 (.str .anonymous "x")
              (.const Setlec.natName []))),
        .fvar 0 (.str .anonymous "x") (.const Setlec.natName [])))
      (by decide)
      (L := .app (m.acval Setlec.natPredName φ)
        (.app (m.acval Setlec.natSuccName φ) (.bvar 1)))
      (R := .bvar 1)
      (by rw [denoteP_app, hKp 2, denoteP_app, hKs 2, denoteP_fvar]
          rfl)
      (by rw [denoteP_fvar])
      hx hzm
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natPredName φ _ ρ,
      acval_interp2_closedC m Setlec.natSuccName φ _ ρ] at h
    exact h
  intro a
  match a with
  | 0 => exact h0
  | a + 1 =>
    rw [natLitP_succ, interp2_app,
      hS _ (natLitP_mem m hnh hval hs ρ a)]
    rfl

/-- `Nat.sub` on literal values (`natOpV_sub`'s mirror). -/
theorem natOpV2_sub (m : EnvS2Core V env) (hops : NatOpsP m φ)
    (hnh : NatHeadsP m φ) (hval : AcvalValidP m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Setlec.natSubName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSubName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (a - b)) := by
  obtain ⟨hg, -⟩ := hops Setlec.natSubName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Setlec.natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps Setlec.natSubName
    (by decide)
  obtain ⟨cvp, vp, hpnt, hfp, hlpp⟩ := hdeps Setlec.natPredName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natSubName [])
      = some (m.acval Setlec.natSubName φ) :=
    fun d => denoteP_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKp : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natPredName [])
      = some (m.acval Setlec.natPredName φ) :=
    fun d => denoteP_levelless_const hfp
      (show (ConstantInfo.defnInfo cvp vp hpnt).toConstantVal.levelParams
        = [] from hlpp)
  have hKz : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natZeroName [])
      = some (m.acval Setlec.natZeroName φ) :=
    fun d => denoteP_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natSuccName [])
      = some (m.acval Setlec.natSuccName φ) :=
    fun d => denoteP_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hzm := natLitP_mem m hnh hval hs ρ 0
  have h0 : ∀ x : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSubName φ)) x)
        (interp2 V ρ (m.acval Setlec.natZeroName φ))
      = x := by
    intro x hx
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natSubName [])
          (.fvar 0 (.str .anonymous "x")
            (.const Setlec.natName [])))
        (.const Setlec.natZeroName []),
        .fvar 0 (.str .anonymous "x") (.const Setlec.natName [])))
      (by decide)
      (L := .app (.app (m.acval Setlec.natSubName φ) (.bvar 1))
        (m.acval Setlec.natZeroName φ))
      (R := .bvar 1)
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_fvar, hKz 2]
          rfl)
      (by rw [denoteP_fvar])
      hx hzm
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natSubName φ _ ρ,
      acval_interp2_closedC m Setlec.natZeroName φ _ ρ] at h
    exact h
  have hS : ∀ x y : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      y ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSubName φ)) x)
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) y)
      = SetTheory.app
          (interp2 V ρ (m.acval Setlec.natPredName φ))
          (SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Setlec.natSubName φ)) x) y) := by
    intro x y hx hy
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natSubName [])
          (.fvar 0 (.str .anonymous "x")
            (.const Setlec.natName [])))
        (.app (.const Setlec.natSuccName [])
          (.fvar 1 (.str .anonymous "y")
            (.const Setlec.natName []))),
        .app (.const Setlec.natPredName [])
          (.app (.app (.const Setlec.natSubName [])
            (.fvar 0 (.str .anonymous "x")
              (.const Setlec.natName [])))
            (.fvar 1 (.str .anonymous "y")
              (.const Setlec.natName [])))))
      (by decide)
      (L := .app (.app (m.acval Setlec.natSubName φ) (.bvar 1))
        (.app (m.acval Setlec.natSuccName φ) (.bvar 0)))
      (R := .app (m.acval Setlec.natPredName φ)
        (.app (.app (m.acval Setlec.natSubName φ) (.bvar 1))
          (.bvar 0)))
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_fvar,
            denoteP_app, hKs 2, denoteP_fvar]
          rfl)
      (by rw [denoteP_app, hKp 2, denoteP_app, denoteP_app, hKc 2,
            denoteP_fvar, denoteP_fvar]
          rfl)
      hx hy
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natSubName φ _ ρ,
      acval_interp2_closedC m Setlec.natSuccName φ _ ρ,
      acval_interp2_closedC m Setlec.natPredName φ _ ρ] at h
    exact h
  refine natOpV2_bin_of_clauses m (fun a b => a - b) (fun a => ?_)
    (fun a b ih => ?_)
  · exact h0 _ (natLitP_mem m hnh hval hs ρ a)
  · rw [hS _ _ (natLitP_mem m hnh hval hs ρ a)
        (natLitP_mem m hnh hval hs ρ b), ih,
      natOpV2_pred m hops hnh hval hfp ρ (a - b)]
    rfl

/-- `Nat.mul` on literal values (`natOpV_mul`'s mirror). -/
theorem natOpV2_mul (m : EnvS2Core V env) (hops : NatOpsP m φ)
    (hnh : NatHeadsP m φ) (hval : AcvalValidP m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Setlec.natMulName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natMulName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (a * b)) := by
  obtain ⟨hg, -⟩ := hops Setlec.natMulName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Setlec.natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps Setlec.natMulName
    (by decide)
  obtain ⟨cva, va, hant, hfa, hlpa⟩ := hdeps Setlec.natAddName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natMulName [])
      = some (m.acval Setlec.natMulName φ) :=
    fun d => denoteP_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKa : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natAddName [])
      = some (m.acval Setlec.natAddName φ) :=
    fun d => denoteP_levelless_const hfa
      (show (ConstantInfo.defnInfo cva va hant).toConstantVal.levelParams
        = [] from hlpa)
  have hKz : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natZeroName [])
      = some (m.acval Setlec.natZeroName φ) :=
    fun d => denoteP_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natSuccName [])
      = some (m.acval Setlec.natSuccName φ) :=
    fun d => denoteP_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hzm := natLitP_mem m hnh hval hs ρ 0
  have h0 : ∀ x : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natMulName φ)) x)
        (interp2 V ρ (m.acval Setlec.natZeroName φ))
      = interp2 V ρ (m.acval Setlec.natZeroName φ) := by
    intro x hx
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natMulName [])
          (.fvar 0 (.str .anonymous "x")
            (.const Setlec.natName [])))
        (.const Setlec.natZeroName []),
        .const Setlec.natZeroName []))
      (by decide)
      (L := .app (.app (m.acval Setlec.natMulName φ) (.bvar 1))
        (m.acval Setlec.natZeroName φ))
      (R := m.acval Setlec.natZeroName φ)
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_fvar, hKz 2]
          rfl)
      (hKz 2)
      hx hzm
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natMulName φ _ ρ,
      acval_interp2_closedC m Setlec.natZeroName φ _ ρ] at h
    exact h
  have hS : ∀ x y : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      y ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natMulName φ)) x)
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) y)
      = SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natAddName φ))
          (SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Setlec.natMulName φ)) x) y)) x := by
    intro x y hx hy
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natMulName [])
          (.fvar 0 (.str .anonymous "x")
            (.const Setlec.natName [])))
        (.app (.const Setlec.natSuccName [])
          (.fvar 1 (.str .anonymous "y")
            (.const Setlec.natName []))),
        .app (.app (.const Setlec.natAddName [])
          (.app (.app (.const Setlec.natMulName [])
            (.fvar 0 (.str .anonymous "x")
              (.const Setlec.natName [])))
            (.fvar 1 (.str .anonymous "y")
              (.const Setlec.natName []))))
          (.fvar 0 (.str .anonymous "x")
            (.const Setlec.natName []))))
      (by decide)
      (L := .app (.app (m.acval Setlec.natMulName φ) (.bvar 1))
        (.app (m.acval Setlec.natSuccName φ) (.bvar 0)))
      (R := .app (.app (m.acval Setlec.natAddName φ)
        (.app (.app (m.acval Setlec.natMulName φ) (.bvar 1))
          (.bvar 0))) (.bvar 1))
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_fvar,
            denoteP_app, hKs 2, denoteP_fvar]
          rfl)
      (by simp only [denoteP_app, hKa 2, hKc 2, denoteP_fvar]; rfl)
      hx hy
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natMulName φ _ ρ,
      acval_interp2_closedC m Setlec.natSuccName φ _ ρ,
      acval_interp2_closedC m Setlec.natAddName φ _ ρ] at h
    exact h
  refine natOpV2_bin_of_clauses m (fun a b => a * b) (fun a => ?_)
    (fun a b ih => ?_)
  · exact h0 _ (natLitP_mem m hnh hval hs ρ a)
  · rw [hS _ _ (natLitP_mem m hnh hval hs ρ a)
        (natLitP_mem m hnh hval hs ρ b), ih,
      natOpV2_add m hops hnh hval hfa ρ (a * b) a]
    rfl

/-- `Nat.pow` on literal values (`natOpV_pow`'s mirror). -/
theorem natOpV2_pow (m : EnvS2Core V env) (hops : NatOpsP m φ)
    (hnh : NatHeadsP m φ) (hval : AcvalValidP m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Setlec.natPowName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natPowName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (a ^ b)) := by
  obtain ⟨hg, -⟩ := hops Setlec.natPowName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Setlec.natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps Setlec.natPowName
    (by decide)
  obtain ⟨cvm, vm, hmnt, hfm, hlpm⟩ := hdeps Setlec.natMulName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natPowName [])
      = some (m.acval Setlec.natPowName φ) :=
    fun d => denoteP_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKm : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natMulName [])
      = some (m.acval Setlec.natMulName φ) :=
    fun d => denoteP_levelless_const hfm
      (show (ConstantInfo.defnInfo cvm vm hmnt).toConstantVal.levelParams
        = [] from hlpm)
  have hKz : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natZeroName [])
      = some (m.acval Setlec.natZeroName φ) :=
    fun d => denoteP_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natSuccName [])
      = some (m.acval Setlec.natSuccName φ) :=
    fun d => denoteP_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hzm := natLitP_mem m hnh hval hs ρ 0
  have h0 : ∀ x : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natPowName φ)) x)
        (interp2 V ρ (m.acval Setlec.natZeroName φ))
      = SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ))
          (interp2 V ρ (m.acval Setlec.natZeroName φ)) := by
    intro x hx
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natPowName [])
          (.fvar 0 (.str .anonymous "x")
            (.const Setlec.natName [])))
        (.const Setlec.natZeroName []),
        .app (.const Setlec.natSuccName [])
          (.const Setlec.natZeroName [])))
      (by decide)
      (L := .app (.app (m.acval Setlec.natPowName φ) (.bvar 1))
        (m.acval Setlec.natZeroName φ))
      (R := .app (m.acval Setlec.natSuccName φ)
        (m.acval Setlec.natZeroName φ))
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_fvar, hKz 2]
          rfl)
      (by rw [denoteP_app, hKs 2, hKz 2]; rfl)
      hx hzm
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natPowName φ _ ρ,
      acval_interp2_closedC m Setlec.natZeroName φ _ ρ,
      acval_interp2_closedC m Setlec.natSuccName φ _ ρ] at h
    exact h
  have hS : ∀ x y : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      y ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natPowName φ)) x)
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) y)
      = SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natMulName φ))
          (SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Setlec.natPowName φ)) x) y)) x := by
    intro x y hx hy
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natPowName [])
          (.fvar 0 (.str .anonymous "x")
            (.const Setlec.natName [])))
        (.app (.const Setlec.natSuccName [])
          (.fvar 1 (.str .anonymous "y")
            (.const Setlec.natName []))),
        .app (.app (.const Setlec.natMulName [])
          (.app (.app (.const Setlec.natPowName [])
            (.fvar 0 (.str .anonymous "x")
              (.const Setlec.natName [])))
            (.fvar 1 (.str .anonymous "y")
              (.const Setlec.natName []))))
          (.fvar 0 (.str .anonymous "x")
            (.const Setlec.natName []))))
      (by decide)
      (L := .app (.app (m.acval Setlec.natPowName φ) (.bvar 1))
        (.app (m.acval Setlec.natSuccName φ) (.bvar 0)))
      (R := .app (.app (m.acval Setlec.natMulName φ)
        (.app (.app (m.acval Setlec.natPowName φ) (.bvar 1))
          (.bvar 0))) (.bvar 1))
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_fvar,
            denoteP_app, hKs 2, denoteP_fvar]
          rfl)
      (by simp only [denoteP_app, hKm 2, hKc 2, denoteP_fvar]; rfl)
      hx hy
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natPowName φ _ ρ,
      acval_interp2_closedC m Setlec.natSuccName φ _ ρ,
      acval_interp2_closedC m Setlec.natMulName φ _ ρ] at h
    exact h
  refine natOpV2_bin_of_clauses m (fun a b => a ^ b) (fun a => ?_)
    (fun a b ih => ?_)
  · exact h0 _ (natLitP_mem m hnh hval hs ρ a)
  · rw [hS _ _ (natLitP_mem m hnh hval hs ρ a)
        (natLitP_mem m hnh hval hs ρ b), ih,
      natOpV2_mul m hops hnh hval hfm ρ (a ^ b) a]
    rfl

/-- `Nat.beq` on literal values (`natOpV_beq`'s mirror). -/
theorem natOpV2_beq (m : EnvS2Core V env) (hops : NatOpsP m φ)
    (hnh : NatHeadsP m φ) (hval : AcvalValidP m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Setlec.natBeqName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natBeqName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (m.acval
          (if a = b then Setlec.boolTrueName else Setlec.boolFalseName)
          φ) := by
  obtain ⟨hg, -⟩ := hops Setlec.natBeqName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, hbool⟩ := Setlec.natOpGuard_inv hg
  obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ := hbool (Or.inl rfl)
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps Setlec.natBeqName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natBeqName [])
      = some (m.acval Setlec.natBeqName φ) :=
    fun d => denoteP_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKz : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natZeroName [])
      = some (m.acval Setlec.natZeroName φ) :=
    fun d => denoteP_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natSuccName [])
      = some (m.acval Setlec.natSuccName φ) :=
    fun d => denoteP_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hKT : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.boolTrueName [])
      = some (m.acval Setlec.boolTrueName φ) :=
    fun d => denoteP_levelless_const hfT hlpT
  have hKF : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.boolFalseName [])
      = some (m.acval Setlec.boolFalseName φ) :=
    fun d => denoteP_levelless_const hfF hlpF
  have hzm := natLitP_mem m hnh hval hs ρ 0
  -- the four clauses at values
  have h00 : SetTheory.app (SetTheory.app
      (interp2 V ρ (m.acval Setlec.natBeqName φ))
      (interp2 V ρ (m.acval Setlec.natZeroName φ)))
      (interp2 V ρ (m.acval Setlec.natZeroName φ))
      = interp2 V ρ (m.acval Setlec.boolTrueName φ) := by
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natBeqName [])
          (.const Setlec.natZeroName []))
        (.const Setlec.natZeroName []),
        .const Setlec.boolTrueName []))
      (by decide)
      (L := .app (.app (m.acval Setlec.natBeqName φ)
        (m.acval Setlec.natZeroName φ))
        (m.acval Setlec.natZeroName φ))
      (R := m.acval Setlec.boolTrueName φ)
      (by rw [denoteP_app, denoteP_app, hKc 2, hKz 2]; rfl)
      (hKT 2) hzm hzm
    simp only [interp2_app,
      acval_interp2_closedC m Setlec.natBeqName φ _ ρ,
      acval_interp2_closedC m Setlec.natZeroName φ _ ρ,
      acval_interp2_closedC m Setlec.boolTrueName φ _ ρ] at h
    exact h
  have h0S : ∀ y : V,
      y ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Setlec.natBeqName φ))
        (interp2 V ρ (m.acval Setlec.natZeroName φ)))
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) y)
      = interp2 V ρ (m.acval Setlec.boolFalseName φ) := by
    intro y hy
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natBeqName [])
          (.const Setlec.natZeroName []))
        (.app (.const Setlec.natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const Setlec.natName []))),
        .const Setlec.boolFalseName []))
      (by decide)
      (L := .app (.app (m.acval Setlec.natBeqName φ)
        (m.acval Setlec.natZeroName φ))
        (.app (m.acval Setlec.natSuccName φ) (.bvar 0)))
      (R := m.acval Setlec.boolFalseName φ)
      (by rw [denoteP_app, denoteP_app, hKc 2, hKz 2, denoteP_app,
            hKs 2, denoteP_fvar]
          rfl)
      (hKF 2) hzm hy
    simp only [interp2_app, interp2_bvar, cons_zero,
      acval_interp2_closedC m Setlec.natBeqName φ _ ρ,
      acval_interp2_closedC m Setlec.natZeroName φ _ ρ,
      acval_interp2_closedC m Setlec.natSuccName φ _ ρ,
      acval_interp2_closedC m Setlec.boolFalseName φ _ ρ] at h
    exact h
  have hS0 : ∀ x : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Setlec.natBeqName φ))
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) x))
        (interp2 V ρ (m.acval Setlec.natZeroName φ))
      = interp2 V ρ (m.acval Setlec.boolFalseName φ) := by
    intro x hx
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natBeqName [])
          (.app (.const Setlec.natSuccName [])
            (.fvar 0 (.str .anonymous "x")
              (.const Setlec.natName []))))
        (.const Setlec.natZeroName []),
        .const Setlec.boolFalseName []))
      (by decide)
      (L := .app (.app (m.acval Setlec.natBeqName φ)
        (.app (m.acval Setlec.natSuccName φ) (.bvar 1)))
        (m.acval Setlec.natZeroName φ))
      (R := m.acval Setlec.boolFalseName φ)
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_app, hKs 2,
            denoteP_fvar, hKz 2]
          rfl)
      (hKF 2) hx hzm
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natBeqName φ _ ρ,
      acval_interp2_closedC m Setlec.natZeroName φ _ ρ,
      acval_interp2_closedC m Setlec.natSuccName φ _ ρ,
      acval_interp2_closedC m Setlec.boolFalseName φ _ ρ] at h
    exact h
  have hSS : ∀ x y : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      y ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Setlec.natBeqName φ))
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) x))
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) y)
      = SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natBeqName φ)) x) y := by
    intro x y hx hy
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natBeqName [])
          (.app (.const Setlec.natSuccName [])
            (.fvar 0 (.str .anonymous "x")
              (.const Setlec.natName []))))
        (.app (.const Setlec.natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const Setlec.natName []))),
        .app (.app (.const Setlec.natBeqName [])
          (.fvar 0 (.str .anonymous "x") (.const Setlec.natName [])))
          (.fvar 1 (.str .anonymous "y") (.const Setlec.natName []))))
      (by decide)
      (L := .app (.app (m.acval Setlec.natBeqName φ)
        (.app (m.acval Setlec.natSuccName φ) (.bvar 1)))
        (.app (m.acval Setlec.natSuccName φ) (.bvar 0)))
      (R := .app (.app (m.acval Setlec.natBeqName φ) (.bvar 1))
        (.bvar 0))
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_app, hKs 2,
            denoteP_fvar, denoteP_app, hKs 2, denoteP_fvar]
          rfl)
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_fvar,
            denoteP_fvar]
          rfl)
      hx hy
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natBeqName φ _ ρ,
      acval_interp2_closedC m Setlec.natSuccName φ _ ρ] at h
    exact h
  intro a
  induction a with
  | zero =>
    intro b
    match b with
    | 0 => rw [natLitP_zero]; exact h00
    | b + 1 =>
      rw [natLitP_zero, natLitP_succ, interp2_app,
        h0S _ (natLitP_mem m hnh hval hs ρ b), if_neg (by omega)]
  | succ a ih =>
    intro b
    match b with
    | 0 =>
      rw [natLitP_zero, natLitP_succ, interp2_app,
        hS0 _ (natLitP_mem m hnh hval hs ρ a), if_neg (by omega)]
    | b + 1 =>
      rw [natLitP_succ, natLitP_succ, interp2_app, interp2_app,
        hSS _ _ (natLitP_mem m hnh hval hs ρ a)
          (natLitP_mem m hnh hval hs ρ b), ih b]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos (by omega)]
      · rw [if_neg hab, if_neg (by omega)]

/-- `Nat.ble` on literal values (`natOpV_ble`'s mirror). -/
theorem natOpV2_ble (m : EnvS2Core V env) (hops : NatOpsP m φ)
    (hnh : NatHeadsP m φ) (hval : AcvalValidP m)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Setlec.natBleName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natBleName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (m.acval
          (if a ≤ b then Setlec.boolTrueName else Setlec.boolFalseName)
          φ) := by
  obtain ⟨hg, -⟩ := hops Setlec.natBleName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, hbool⟩ := Setlec.natOpGuard_inv hg
  obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ :=
    hbool (Or.inr (Or.inl rfl))
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps Setlec.natBleName
    (by decide)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natBleName [])
      = some (m.acval Setlec.natBleName φ) :=
    fun d => denoteP_levelless_const hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKz : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natZeroName [])
      = some (m.acval Setlec.natZeroName φ) :=
    fun d => denoteP_levelless_const hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.natSuccName [])
      = some (m.acval Setlec.natSuccName φ) :=
    fun d => denoteP_levelless_const hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hKT : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.boolTrueName [])
      = some (m.acval Setlec.boolTrueName φ) :=
    fun d => denoteP_levelless_const hfT hlpT
  have hKF : ∀ d : Nat, denoteP m.acval env φ d
      (.const Setlec.boolFalseName [])
      = some (m.acval Setlec.boolFalseName φ) :=
    fun d => denoteP_levelless_const hfF hlpF
  have hzm := natLitP_mem m hnh hval hs ρ 0
  have h0y : ∀ y : V,
      y ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Setlec.natBleName φ))
        (interp2 V ρ (m.acval Setlec.natZeroName φ))) y
      = interp2 V ρ (m.acval Setlec.boolTrueName φ) := by
    intro y hy
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natBleName [])
          (.const Setlec.natZeroName []))
        (.fvar 1 (.str .anonymous "y") (.const Setlec.natName [])),
        .const Setlec.boolTrueName []))
      (by decide)
      (L := .app (.app (m.acval Setlec.natBleName φ)
        (m.acval Setlec.natZeroName φ)) (.bvar 0))
      (R := m.acval Setlec.boolTrueName φ)
      (by rw [denoteP_app, denoteP_app, hKc 2, hKz 2, denoteP_fvar]
          rfl)
      (hKT 2) hzm hy
    simp only [interp2_app, interp2_bvar, cons_zero,
      acval_interp2_closedC m Setlec.natBleName φ _ ρ,
      acval_interp2_closedC m Setlec.natZeroName φ _ ρ,
      acval_interp2_closedC m Setlec.boolTrueName φ _ ρ] at h
    exact h
  have hS0 : ∀ x : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Setlec.natBleName φ))
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) x))
        (interp2 V ρ (m.acval Setlec.natZeroName φ))
      = interp2 V ρ (m.acval Setlec.boolFalseName φ) := by
    intro x hx
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natBleName [])
          (.app (.const Setlec.natSuccName [])
            (.fvar 0 (.str .anonymous "x")
              (.const Setlec.natName []))))
        (.const Setlec.natZeroName []),
        .const Setlec.boolFalseName []))
      (by decide)
      (L := .app (.app (m.acval Setlec.natBleName φ)
        (.app (m.acval Setlec.natSuccName φ) (.bvar 1)))
        (m.acval Setlec.natZeroName φ))
      (R := m.acval Setlec.boolFalseName φ)
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_app, hKs 2,
            denoteP_fvar, hKz 2]
          rfl)
      (hKF 2) hx hzm
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natBleName φ _ ρ,
      acval_interp2_closedC m Setlec.natZeroName φ _ ρ,
      acval_interp2_closedC m Setlec.natSuccName φ _ ρ,
      acval_interp2_closedC m Setlec.boolFalseName φ _ ρ] at h
    exact h
  have hSS : ∀ x y : V,
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      y ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Setlec.natBleName φ))
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) x))
        (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natSuccName φ)) y)
      = SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Setlec.natBleName φ)) x) y := by
    intro x y hx hy
    have h := natEq_valueP m hops (by decide) hf
      (eq := (.app (.app (.const Setlec.natBleName [])
          (.app (.const Setlec.natSuccName [])
            (.fvar 0 (.str .anonymous "x")
              (.const Setlec.natName []))))
        (.app (.const Setlec.natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const Setlec.natName []))),
        .app (.app (.const Setlec.natBleName [])
          (.fvar 0 (.str .anonymous "x") (.const Setlec.natName [])))
          (.fvar 1 (.str .anonymous "y") (.const Setlec.natName []))))
      (by decide)
      (L := .app (.app (m.acval Setlec.natBleName φ)
        (.app (m.acval Setlec.natSuccName φ) (.bvar 1)))
        (.app (m.acval Setlec.natSuccName φ) (.bvar 0)))
      (R := .app (.app (m.acval Setlec.natBleName φ) (.bvar 1))
        (.bvar 0))
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_app, hKs 2,
            denoteP_fvar, denoteP_app, hKs 2, denoteP_fvar]
          rfl)
      (by rw [denoteP_app, denoteP_app, hKc 2, denoteP_fvar,
            denoteP_fvar]
          rfl)
      hx hy
    simp only [interp2_app, interp2_bvar, cons_succ, cons_zero,
      acval_interp2_closedC m Setlec.natBleName φ _ ρ,
      acval_interp2_closedC m Setlec.natSuccName φ _ ρ] at h
    exact h
  intro a
  induction a with
  | zero =>
    intro b
    rw [natLitP_zero, h0y _ (natLitP_mem m hnh hval hs ρ b),
      if_pos (Nat.zero_le b)]
  | succ a ih =>
    intro b
    match b with
    | 0 =>
      rw [natLitP_zero, natLitP_succ, interp2_app,
        hS0 _ (natLitP_mem m hnh hval hs ρ a), if_neg (by omega)]
    | b + 1 =>
      rw [natLitP_succ, natLitP_succ, interp2_app, interp2_app,
        hSS _ _ (natLitP_mem m hnh hval hs ρ a)
          (natLitP_mem m hnh hval hs ρ b), ih b]
      by_cases hab : a ≤ b
      · rw [if_pos hab, if_pos (by omega)]
      · rw [if_neg hab, if_neg (by omega)]

end Setlec.SetR.Interp2
