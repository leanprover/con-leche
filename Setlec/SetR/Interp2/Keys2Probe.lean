import Setlec.SetR.Interp2.Denote2Extend

/-!
# Section 3 — the three keys: where each one actually stalls

The batch was briefed *"cheapest first: `ReducePin2`, `MemberBlock2`,
`DeclStep2`"*, with seal 34's survey pricing the first two as **one
`DefEq.sound` application** and **pure transport**.

**Attempting them found that the survey priced the v1 proofs, not the
interp2 ones**, and that the two prices do not transfer.  This file
records the stall points, mechanizes the one that is a theorem rather
than an absence, and lands the instances that *are* reachable — so
that what remains is a named supplier rather than an open question.

## The one structural fact, mechanized: there is no erasure bridge

Every v1 key's V content is a fact about `interp` and `cval`.  Every
interp2 key's V content is a fact about `interp2` and `acval`.  A
transport between them would need `interp2 V ρ ea = interp V ρ
ea.erase`, and **that equation is false** —
`interp2_ne_interp_erase` below, at an empty-domain λ, which is the
#100 countermodel's own witness (`lamC_empty` is `pt`,
`lamR_pos_empty` is `empty`).

This is not a gap to be filled: the disagreement *is* the interp2
lane's reason to exist.  It does mean that "the v1 proof, transposed"
is never a discharge plan for a key — only a shape.

## `ReducePin2` — blocked on relation-level soundness over `interp2`

The v1 discharge (`Install/ReducePin.lean:reducePinS`, 118 lines)
consumes `ReducePinR`'s certificate, which is a **derivation**:
`DefEq μ env cval φ [E] (.app V (.bvar 0)) (.bvar 0)`
(`SetR/Decl.lean:231`).  Its whole V content is one `DefEq.sound`, and
`DefEq.sound` (`Sound/Main.lean:96`) is soundness of the `SetR`
relation **over `interp`**, unconditional.

Over `interp2` there is **no relation-level soundness at all**.  The
interp2 lane is a *checker-run* development (`Claims2*`,
`CheckStep2B`), and even that is conditional: `checkStep2B_of_quarters`
still takes eight named residues.  So the certificate cannot be cashed.

*The supplier `ReducePin2` needs is `DefEq.sound` over `interp2` — a
whole soundness, not a lemma.*  Its conclusion is nevertheless
satisfiable, non-vacuously: `reducePin2_witness` below.

## `MemberBlock2` — the existence conjunct is `Denote2Total`'s wall

`MemberBlock2` asserts a `denote2` **success** as a conclusion.  Seal
37's own sweep flagged this and supplied fuel slack (`∃ F' ≥ F`), for
the checked reason that a `∀`-typed subject is `none` at fuel `1`.
**The slack is over the fuel, and the obstruction is not the fuel**:
for a `∀`-typed subject `denote2` must run `sortOfE` at each binder,
i.e. `inferTypeCore` and `whnf` must *succeed* — which is
`Denote2Total`, parked at seal 33.

So `MemberBlock2` is reachable exactly where no binder is crossed.
`memberBlock2_probe` discharges it at section 1's axiom, whose type is
`.sort .zero`: every conjunct is met, at every mode, fuel and
valuation.  That is the key's first genuine instance, and it locates
the wall precisely — one binder away.

## `DeclStep2` — inherits `MemberBlock2`, and now has its other half

`DeclStep2 env₂ = Nonempty (EnvS2U V env₂)`.  Section 1 closed its
vacuity exposure and section 2 supplies the transport half for the
*old* constants (`denote2_envExtend`, modulo its two named
hypotheses).  What is missing is the **new** constant's `mem_type2`,
which is `MemberBlock2` — so `DeclStep2` is blocked exactly where
`MemberBlock2` is, and nowhere else.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable (V : Type w) [SetTheory V]

/-! ## No erasure bridge -/

/-- **`interp2` is not `interp ∘ erase`.**  At an empty-domain λ with
a positive codomain numeral the two disagree: the collapse sends it to
the proof point, the two-regime reading keeps it a graph — here the
empty one.

Consequence for this batch: **a v1 key's proof is a shape, never a
transport.**  Every discharge over `interp2` must be rebuilt from
interp2-side suppliers. -/
theorem interp2_ne_interp_erase (ρ : Nat → V) :
    interp2 V ρ (.lam 1 (.const .empty [0]) (.bvar 0))
      ≠ interp V ρ
        (AVExpr.lam 1 (.const .empty [0]) (.bvar 0)).erase := by
  rw [interp2_lam, interp2_const, AVExpr.erase_lam, interp_lam]
  show lamR 1 (empty : V) _ ≠ lamC (empty : V) _
  rw [lamR_pos_empty (by decide), lamC_empty]
  exact fun h => pt_ne_empty h.symm

/-! ## `MemberBlock2`, discharged at section 1's axiom

The first genuine instance of a key over `interp2`.  Its subject is
the probe's stored axiom: a `Prop`-typed constant, so `denote2` needs
no sort computation and the existence conjunct is met outright. -/

/-- **`MemberBlock2` holds at the probe.**  All three parts: the type
denotes (at *every* fuel, so the existential slack is not even used),
the leaf inhabits it (`empty ∈ˢ univ 0`), and the type is truthful
(the `.sort` clause). -/
theorem memberBlock2_probe (μ : CheckMode) (ψ : Name → Nat) :
    MemberBlock2 V μ probeEnv (fun _ _ => .const .empty [0]) ψ
      probeCi.toConstantVal := by
  intro F
  refine ⟨F, .sort 0, Nat.le_refl F, probe_denote2_type μ ψ F,
    fun ρ => ⟨?_, ?_⟩⟩
  · rw [interp2_sort, interp2_const]
    exact empty_mem_univ 0
  · simp

/-! ## `ReducePin2`'s conclusion is satisfiable, non-vacuously

The key is blocked on its *supplier*, not on its statement.  A witness
separates the two: if the conclusion were unsatisfiable the statement
would be the problem, and it is not.

The trap this witness is built to avoid is the obvious one — an
element leaf whose interpretation is **empty** satisfies the identity
clause vacuously, and would prove nothing.  `reducePin2_domain_ne`
records that this witness's domain has a member. -/

/-- The witness valuation: the element leaf is `Prop` (a *non-empty*
set), and the operation's leaf is the identity λ over it, at a
positive codomain numeral so the graph regime applies. -/
noncomputable def reduceAcvalW :
    Name → (Name → Nat) → AVExpr := fun n _ =>
  if n = Setlec.natName then .sort 0
  else .lam 1 (.sort 0) (.bvar 0)

/-- The witness's domain is inhabited, so the identity clause below is
**not** discharged by an empty quantifier. -/
theorem reducePin2_domain_ne (ρ : Nat → V) (φ : Name → Nat) :
    ∃ x : V, x ∈ˢ interp2 V ρ
      (reduceAcvalW
        (Setlec.reduceElemName Setlec.reduceNatName) φ) := by
  refine ⟨empty, ?_⟩
  rw [show Setlec.reduceElemName Setlec.reduceNatName
      = Setlec.natName from by
    rw [Setlec.reduceElemName, if_pos rfl],
    reduceAcvalW, if_pos rfl, interp2_sort]
  exact empty_mem_univ 0

/-- **`ReducePin2`'s conclusion is satisfiable.**  The element type is
stored (`natLitEnv` holds the `Nat` block) and the operation's leaf is
the identity on it. -/
theorem reducePin2_witness (φ : Name → Nat) :
    ReducePin2 V natLitEnv reduceAcvalW φ Setlec.reduceNatName := by
  have hnat : Setlec.reduceElemName Setlec.reduceNatName
      = Setlec.natName := by
    rw [Setlec.reduceElemName, if_pos rfl]
  refine ⟨by rw [hnat]; decide, ?_⟩
  intro ρ x hx
  rw [hnat, reduceAcvalW, if_pos rfl, interp2_sort] at hx
  rw [reduceAcvalW,
    if_neg (show Setlec.reduceNatName ≠ Setlec.natName by decide),
    interp2_lam, interp2_sort]
  exact app_lamR_pos (by decide) hx

end Setlec.SetR.Interp2
