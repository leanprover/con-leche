import Setlec.TT.Semantics.Consistency
import Setlec.TT.Deq

/-!
# REFUTATION: `Typable e → InferOnly e t → HasType Γ e t` is false

The infer-only design's target theorem is refuted outright, in the
empty context, by a closed witness.

`InferOnly` below is the *smallest* relation containing the design's
mandated clauses — a lambda's type is `pi` of its annotation over the
body's inferred type, and an application's type is the codomain of the
function's inferred type instantiated at the (never examined) argument.
Any infer-only relation must contain these instances: in the witness
the function's inferred type is *syntactically* a `pi`, so a whnf step
between `InferOnly f tf` and reading off the domain is the identity.

The witness is `w := (fun (x : False) => x) Nat.zero`:

* `w` is **typable**: `False → False` and `Nat → (0 = 0)` are
  interderivable inhabited `Prop`s, so four applications of `propext`
  give an equation between them, `conv` retypes the identity-on-`False`
  at `Nat → (0 = 0)`, and the application to `0` types at `0 = 0`.
  (This is exactly the task-#125 / F2 engine.)
* `InferOnly` computes `w`'s type to be `False`: the function's
  inferred type is `False → False`, and infer-only *never looks at the
  argument*.
* `HasType [] w False` would be a closed proof of `False` —
  impossible by the layer's own consistency theorem
  (`no_proof_of_empty`).

So the failure is not "the induction doesn't go through"; the
statement is **false**.  Note what the witness does *not* need: no
exotic context (it is closed), no untypable subterm (every subterm of
`w` is typable), and no dependent codomain (both codomains are
constant).  The failure is manufactured entirely by `propext`
retyping the function between two `Prop`-sorted `pi` types with
unrelated domains — the F2 phenomenon consumed by an application node.
-/

namespace Setlec.TT
namespace Spike

open VExpr

/-- The design's `Typable` predicate. -/
def Typable (Γ : List VExpr) (e : VExpr) : Prop := ∃ T, HasType Γ e T

/-- The infer-only clauses the design mandates.  Only the three clauses
the witness exercises are included; a fuller relation contains this
one, so the refutation applies a fortiori. -/
inductive InferOnly : List VExpr → VExpr → VExpr → Prop where
  /-- Leaves read the context. -/
  | bvar {Γ i A} : Γ[i]? = some A → InferOnly Γ (.bvar i) (A.liftN (i + 1))
  /-- A lambda's type is read off its annotation and its body's
  inferred type — the annotation itself is never checked. -/
  | lam {Γ A b tb} : InferOnly (A :: Γ) b tb →
      InferOnly Γ (.lam A b) (.pi A tb)
  /-- The infer-only application clause: the argument is **never
  examined** — no typing, no domain comparison.  (The design interposes
  a whnf on `tf`; in the witness `tf` is already syntactically a `pi`,
  so whnf is the identity there.) -/
  | app {Γ f a A B} : InferOnly Γ f (.pi A B) →
      InferOnly Γ (.app f a) (B.inst a)

/-- `False → False` (`Empty.{0}` is the layer's `False`). -/
def P1 : VExpr := .pi (emptyT 0) (emptyT 0)

/-- The inhabited `Prop` `0 = 0`. -/
def trueP : VExpr := .eqE natT natZeroT natZeroT

/-- `Nat → (0 = 0)`. -/
def P2 : VExpr := .pi natT trueP

/-- The identity on `False`. -/
def idFalse : VExpr := .lam (emptyT 0) (.bvar 0)

/-- The witness: `(fun (x : False) => x) Nat.zero`. -/
def w : VExpr := .app idFalse natZeroT

/-- `idFalse : False → False`, the structural typing. -/
theorem idFalse_hasType_P1 : HasType [] idFalse P1 :=
  .lam (.bvar (A := emptyT 0) rfl)

theorem P1_prop : HasType [] P1 (.sort 0) :=
  .pi (u := 0) (v := 0) .const .const

theorem P2_prop : HasType [] P2 (.sort 0) :=
  .pi (u := 1) (v := 0) .const .eqType

/-- `fun (_ : P1) (_ : Nat) => prf : P1 → P2`. -/
theorem impl12 :
    HasType [] (.lam P1 (.lam natT .prf)) (.pi P1 P2) :=
  .lam (.lam (.refl (T := natT) (a := natZeroT)))

/-- `fun (_ : P2) (x : False) => x : P2 → P1`. -/
theorem impl21 :
    HasType [] (.lam P2 (.lam (emptyT 0) (.bvar 0))) (.pi P2 P1) :=
  .lam (.lam (.bvar (A := emptyT 0) rfl))

/-- Four applications of `propext` prove `P1 = P2`.  (Built inside-out
so the elaborator computes each `inst` before the next `app` reads its
`pi` shape.) -/
theorem propext_P1_P2 :
    HasType []
      (.app (.app (.app (.app (.const .propext []) P1) P2)
        (.lam P1 (.lam natT .prf)))
        (.lam P2 (.lam (emptyT 0) (.bvar 0))))
      (.eqE (.sort 0) P1 P2) := by
  have h1 := HasType.app (Γ := []) (.const (c := .propext) (us := [])) P1_prop
  have h2 := HasType.app h1 P2_prop
  have h3 := HasType.app h2 impl12
  exact HasType.app h3 impl21

/-- The retyping that makes the witness typable: `idFalse : Nat → (0 = 0)`. -/
theorem idFalse_hasType_P2 : HasType [] idFalse P2 :=
  .conv idFalse_hasType_P1 propext_P1_P2

/-- **`w` is typable** — at the inhabited `Prop` `0 = 0`. -/
theorem w_typable : Typable [] w :=
  ⟨trueP, .app (A := natT) (B := trueP) idFalse_hasType_P2 .const⟩

/-- **Infer-only assigns `w` the type `False`**: the function is a
lambda annotated `False`, so its inferred type is `False → False`, and
the argument `0` is never examined. -/
theorem w_inferOnly_false : InferOnly [] w (emptyT 0) :=
  .app (A := emptyT 0) (B := emptyT 0)
    (.lam (.bvar (A := emptyT 0) rfl))

/-- **The refutation.**  On the layer's typability, infer-only produces
an invalid type: granting the target theorem yields a closed proof of
`False`, contradicting the layer's consistency (parametric in any model
of the `SetTheory` interface, as everywhere in this project). -/
theorem infer_only_target_refuted (V : Type w) [SetTheory V] :
    ¬ ∀ (Γ : List VExpr) (e t : VExpr),
        Typable Γ e → InferOnly Γ e t → HasType Γ e t := by
  intro h
  exact no_proof_of_empty V (h [] w (emptyT 0) w_typable w_inferOnly_false)

/-- Every proper subterm of the witness is typable too, so no
"all subterms typable" strengthening of the hypothesis rescues the
statement. -/
theorem w_subterms_typable :
    Typable [] idFalse ∧ Typable [] natZeroT ∧
      Typable [(emptyT 0)] (.bvar 0) ∧ Typable [] (emptyT 0) :=
  ⟨⟨P1, idFalse_hasType_P1⟩, ⟨natT, .const⟩,
    ⟨emptyT 0, .bvar (A := emptyT 0) rfl⟩, ⟨.sort 0, .const⟩⟩

end Spike
end Setlec.TT
