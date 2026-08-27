import Setlec.TTVerify.MajorStep
import Setlec.TTVerify.Consistency

/-!
# `CheckDeclTT`: the per-declaration step

The milestone.  `checkDecl` dispatches on the declaration's kind and
`CheckDeclTT` follows it exactly — six cases, each stated as
`checkDecl` **restricted to one constructor of `Declaration`**.

That restriction is §8.6's permitted move and not the forbidden one:
each obligation's hypothesis is `checkDecl`'s *own* call, with the
subject's shape fixed; none of them refers to a position inside
`checkDecl`'s body.  The dispatch below is then the whole of
`CheckDeclTT`, and every case can be discharged independently.

## What each case owes

`EnvTT.cons` is the single install lemma (`Setlec/TTVerify/Extend.lean`),
so each case owes exactly its list of head hypotheses at the constant it
installs.  Most are vacuous per kind — a `defnInfo` head discharges the
recursor, eta, unit and projection clauses by constructor
disjointness — and what remains is the *content*:

| kind | content |
| --- | --- |
| `defnDecl` | the body's typing; the `Nat`-operation recurrences and the div/mod certificates |
| `thmDecl` | the proof value's typing (`thm_ok` is the valuation's definition) |
| `opaqueDecl` | as `thmDecl`, plus the compiler-trust identity |
| `axiomDecl` | inhabitation of the three pinned families, or nothing at all for a tolerated skip |
| `basisDecl` | the pinned block's valuations, laws and iota rules |
| `indDecl` | the modeled family's install: `RecRulesTT`, `CapsOkTT`, `ProjOkT` |

The two literal-free cases (`axiomDecl`'s tolerated branch) are proved
here because they install nothing; the rest are named.

## The direct-install hypothesis is consumed here

`CertifiedConfigTT` is what lets the `indDecl` case ignore
`checkDirectStruct` — `directParts?` is gated on the switch, so with it
off the dispatch always takes `checkIndDecl`.  That is the one place
the hypothesis of `Setlec/TTVerify/Consistency.lean` is used, and it is
used as a *fall-through*, exactly as its docstring says.
-/

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

variable {F : Nat}

/-! ## The six cases -/

/-- A checked `def` preserves the derivation model. -/
def DeclDefnTT (F : Nat) : Prop :=
  ∀ {env env₁ : Env} {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint},
    checkDecl mode (fueledOps mode F) env (.defnDecl cv value hint) = .ok env₁ →
    EnvTT env → Nonempty (EnvTT env₁)

/-- A checked `theorem` preserves the derivation model. -/
def DeclThmTT (F : Nat) : Prop :=
  ∀ {env env₁ : Env} {cv : ConstantVal} {value : Expr},
    checkDecl mode (fueledOps mode F) env (.thmDecl cv value) = .ok env₁ →
    EnvTT env → Nonempty (EnvTT env₁)

/-- A checked `opaque` preserves the derivation model. -/
def DeclOpaqueTT (F : Nat) : Prop :=
  ∀ {env env₁ : Env} {cv : ConstantVal} {value : Expr},
    checkDecl mode (fueledOps mode F) env (.opaqueDecl cv value) = .ok env₁ →
    EnvTT env → Nonempty (EnvTT env₁)

/-- An accepted `axiom` — one of the three pinned families — preserves
the derivation model. -/
def DeclAxiomTT (F : Nat) : Prop :=
  ∀ {env env₁ : Env} {cv : ConstantVal},
    checkDecl mode (fueledOps mode F) env (.axiomDecl cv) = .ok env₁ →
    EnvTT env → Nonempty (EnvTT env₁)

/-- Installing a pinned basis block preserves the derivation model. -/
def DeclBasisTT (F : Nat) : Prop :=
  ∀ {env env₁ : Env} {kind : BasisKind},
    checkDecl mode (fueledOps mode F) env (.basisDecl kind) = .ok env₁ →
    EnvTT env → Nonempty (EnvTT env₁)

/-- Installing an inductive block preserves the derivation model.  The
direct-install switch is off, so this is `checkIndDecl`.  The stored
eta families' closure enters as a hypothesis — the one case that reads
it (see `CheckDeclTT`): a fresh block constructor whose name is an
*older* eta-capable former's capability constructor would owe that
family's law, and only closure refutes the collision. -/
def DeclIndTT (F : Nat) : Prop :=
  ∀ {env env₁ : Env} {block : List ConstantInfo},
    checkDecl mode (fueledOps mode F) env (.indDecl block) = .ok env₁ →
    CertifiedConfigTT mode →
    EnvTT env → EtaFamiliesClosedT env → Nonempty (EnvTT env₁)

/-! ## The dispatch

One `cases`, and each branch is its own obligation applied to the same
hypothesis.  Nothing else belongs here: `checkDecl`'s body *is* the
dispatch, so the transpose of the dispatch is the dispatch. -/

/-- **`CheckDeclTT`, from the six per-kind obligations.** -/
theorem checkDeclTT_of (hdefn : DeclDefnTT F) (hthm : DeclThmTT F)
    (hopaq : DeclOpaqueTT F) (hax : DeclAxiomTT F) (hbas : DeclBasisTT F)
    (hind : DeclIndTT F) : CheckDeclTT F := by
  intro mode' env env₁ d h hdir m hE1
  -- task #147: the certified configuration pins the running mode
  obtain rfl : mode' = .ttModel := hdir.mode_eq
  cases d with
  | defnDecl cv value hint => exact hdefn h m
  | thmDecl cv value => exact hthm h m
  | opaqueDecl cv value => exact hopaq h m
  | axiomDecl cv => exact hax h m
  | basisDecl kind => exact hbas h m
  | indDecl block => exact hind h hdir m hE1

end Setlec.TTVerify
