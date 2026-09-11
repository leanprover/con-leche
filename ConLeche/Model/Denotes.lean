module

public import ConLeche.Denotes
public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Verify.Close
import ConLeche.Model.Claims
import ConLeche.Verify.EnvGuards
import ConLeche.Verify.Denote.VClosed
import ConLeche.SetModel.TupleTower
import ConLeche.Semantics.Tower.TowerLeaf

public section

/-!
# The model the invariant carries, read through `Denotes`

`ConLeche/Denotes.lean` states what a model of an environment is;
this module builds one from the graded invariant `EnvModelM`
(`Model/Annot/EnvModelM.lean`) the fold establishes.  Three steps:

* **the leaves become sets**: `cvalOf acval n ψ` is the interpretation
  of the (closed) annotated leaf `acval n ψ` — under every variable
  environment the same set (`interp_cvalOf`);
* **the bridge** `Denotes_of_denoteMeta`: wherever the invariant's
  reading `denoteMeta` reads a term at depth `d`, and the reading is
  graded and bit-valid (`WellDenotedV`), `interp` of the reading is a
  `Denotes`-denotation of the term's CLOSURE (`Expr.closeN`, the
  checker's opened `fvar`s turned back into the de Bruijn indices the
  relation reads) at the interpreted leaves.  The regime premises of
  the two binder rules are exactly the invariant's sort facts:
  `AnnotValid`'s `pi` clause and `WellDenoted`'s `lam` clause.
* **the model** `Model.ofEnvModelM`: `mem` from `type_reads` and
  `mem_type` at depth `0` (a stored type has no `fvar`, so it is its
  own closure); `false_empty` from the pinned `False` leaf
  (`EnvModel.cvalE_pinned`: the leaf is `.const .empty [0]`, whose
  interpretation is the empty set).
-/

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.SetModel ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche.SetTheory.Tower (projS)
open ConLeche (Env Expr Name Level ConstantInfo)
open ConLeche.Expr (closeN)

universe w

variable {V : Type w} [SetTheory V]

/-- The set-valued leaf of an annotated valuation. -/
noncomputable def cvalOf (acval : Name → (Name → Nat) → AnnotTerm)
    (n : Name) (ψ : Name → Nat) : V :=
  interp V (fun _ => SetTheory.empty) (acval n ψ)

/-- A closed leaf interprets to its `cvalOf` under every environment. -/
theorem interp_cvalOf {acval : Name → (Name → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) (n : Name) (ψ : Name → Nat)
    (ρ : Nat → V) : interp V ρ (acval n ψ) = cvalOf acval n ψ :=
  interp_closed (V := V) (hcl n ψ) ρ _

omit [SetTheory V] in
theorem push_eq_cons (x : V) (ρ : Nat → V) : ConLeche.push x ρ = cons x ρ := by
  funext i; cases i <;> rfl

theorem field_eq_projS : ∀ (i : Nat) (p : V), ConLeche.field i p = projS i p
  | 0, _ => rfl
  | i + 1, p => field_eq_projS i (ssnd p)

theorem regime_eq_pwBit (φ : Name → Nat) (pw : ConLeche.PropWhen) :
    ConLeche.regime φ pw = pwBit φ pw := rfl

/-! ### The literal spines -/

/-- Under the `Nat`-literal guard, the constructor form of a literal
denotes the annotated numeral `denoteMeta` reads. -/
theorem Denotes_natLitToConstructor {acval : Name → (Name → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) {env : Env} {φ : Name → Nat}
    (hsup : ConLeche.natLitSupported env = true) (ρ : Nat → V) :
    ∀ k, Denotes (cvalOf (V := V) acval) env φ ρ (ConLeche.natLitToConstructor k)
      (interp V ρ (natLitAV (acval natZeroName (Level.substFn φ [] []))
        (acval natSuccName (Level.substFn φ [] [])) k)) := by
  sorry

/-- Under the `String`-literal guard, the constructor form of a literal
denotes what `denoteMeta` reads for the literal. -/
theorem Denotes_strLitToConstructor {acval : Name → (Name → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) {env : Env} {φ : Name → Nat}
    (hsup : ConLeche.strLitSupported env = true) (ρ : Nat → V) (s : String) :
    Denotes (cvalOf (V := V) acval) env φ ρ (ConLeche.strLitToConstructor s)
      (interp V ρ (.app (acval stringOfListName (Level.substFn φ [] []))
        (charListAV
          (.app (acval listNilName
              (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (.app (acval listConsName
              (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (acval charOfNatName (Level.substFn φ [] []))
          (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] []))
          s.toList))) := by
  sorry

/-! ### The bridge -/

/-- Grading and bit-validity descend a tower projection to its subject. -/
theorem wellDenotedV_of_projAV {ρ : Nat → V} :
    ∀ (i : Nat) (e : AnnotTerm), WellDenotedV V ρ (projAV i e) → WellDenotedV V ρ e := by
  sorry

/-- **The bridge**: wherever `denoteMeta` reads a term whose reading is
graded and bit-valid, `interp` of the reading is a denotation of the
term's closure under `Denotes` at the interpreted leaves. -/
theorem Denotes_of_denoteMeta {acval : Name → (Name → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) {env : Env} {φ : Name → Nat} :
    ∀ (d : Nat) (e : Expr) {ta : AnnotTerm},
      denoteMeta acval env φ d e = some ta →
      Expr.fvarsBelow d e → e.looseBVarsBounded 0 = true →
      ∀ ρ : Nat → V, WellDenotedV V ρ ta →
        Denotes (cvalOf (V := V) acval) env φ ρ (closeN d e) (interp V ρ ta) := by
  sorry

/-! ### The model -/

/-- **The model, read off the invariant**: `Model V env` from
`EnvModelM V μ env`. -/
noncomputable def Model.ofEnvModelM {μ : ConLeche.CheckMode} {env : Env}
    (m : EnvModelM V μ env) : ConLeche.Model V env where
  cval := cvalOf m.base2.acval
  mem := by
    sorry
  false_empty := by
    sorry

end ConLeche.Model
