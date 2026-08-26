import Setlec.TT.Judgment

/-!
# The little inversion the bridge needs

**A deliberate, bounded departure from the layer's "no syntactic
metatheory" discipline, and it lives here rather than in
`Setlec/TT/*` for exactly that reason.**

`Setlec/TT/DESIGN.md` §6 makes a point of the layer having no syntactic
metatheory: soundness goes straight to the model, so the whole
substitution story is two *semantic* lemmas rather than lean4lean's 123
syntactic ones.  That claim is about **soundness**, and it stands.

**Currently unconsumed, and kept deliberately.**  These were built for
the threaded claim shape, which is now withdrawn
(`Setlec/TTVerify/Claims.lean`); the certificate-only claims need no
inversion at all.  They are kept because the *argument* for that
withdrawal runs through them — route 2 of
`Setlec/TTVerify/DESIGN.md` §6 is precisely "what inversion supplies,
and why it is not enough" — so deleting them would delete the evidence.
If a later clause does want inversion, these are what is available; if
the count ever reaches four, that is the signal
`Setlec/TT/DESIGN.md` §3.1 warns about.

The **bridge** needed them because of the shape task #119's stage 2
briefly took.  Threading a typing hypothesis through
the reduction claims (rather than re-deriving membership at every node
— see `Setlec/TTVerify/DESIGN.md` §6) means that when the induction
recurses into a subterm, it must hand the recursive call a typing for
*that* subterm.  The checker's `whnfCore` recurses into the head of an
application and into the subject of a projection, so those are the two
inversions below, and there are no others.

They are cheap, and the reason is worth stating because it is what
bounds the departure: **the subject of a `HasType` derivation
determines which rules could have concluded it**, up to `conv`, which
does not change the subject.  So each inversion is one induction with
two interesting cases (the rule itself, and `conv`) and a catch-all
that is closed by constructor disjointness.  Nothing here resembles
Church–Rosser, unique typing, or weakening.

**Π-injectivity is not among these, and it never can be: it is
inadmissible.**  The bridge would want it to weaken `HasType.beta`'s
premise (`Setlec/TTVerify/DESIGN.md` §6) — inverting a typed redex
yields the argument at the *ambient* domain `A₀`, while `beta` asks for
it at the λ's annotation `A`.  But `Deq Δ (Π A B') (Π A₀ B₀) →
Deq Δ A A₀` is **refuted by `propext`**: `False → False` and
`Nat → PUnit.{0}` are interderivable `Prop`s, so injectivity would give
`Deq [] Empty Nat` and soundness would force `∅ = ω`.  The same witness
kills codomain-injectivity.  Adding either as a rule would be unsound,
so the checker's beta certificate supplies the premise permanently.

(An earlier revision recorded this as an open question.  It was closed
negatively; the argument had to come from inside the rule set, from a
rule the layer has, not from the model.)
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- Inversion for application, over an arbitrary conclusion type: a
derivation whose subject is `f a` ends (before some number of `conv`
steps) in the `app` rule, so the head and the argument are typed. -/
theorem hasType_app_inv :
    ∀ {Δ : List VExpr} {e C : VExpr}, HasType Δ e C →
      ∀ {f a : VExpr}, e = .app f a →
        ∃ A B, HasType Δ f (.pi A B) ∧ HasType Δ a A := by
  intro Δ e C h
  induction h with
  | app hf ha =>
    intro f a he
    simp only [VExpr.app.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, _, hf, ha⟩
  | conv _ _ ih _ => intro f a he; exact ih he
  | _ => intro f a he; cases he

/-- Inversion for projection: a derivation whose subject is `p.i` ends
(before some `conv` steps) in `projFst` or `projSnd`, so the subject is
typed at a pair type.  The field index is *not* returned — a `conv`
chain cannot change it, but the caller never needs it: what the
recursion wants is a typing for `p`. -/
theorem hasType_proj_inv :
    ∀ {Δ : List VExpr} {e C : VExpr}, HasType Δ e C →
      ∀ {i : Nat} {p : VExpr}, e = .proj i p →
        ∃ u v A B, HasType Δ A (.sort u) ∧
          HasType Δ B (arrow A (.sort v)) ∧ HasType Δ p (psigmaT u v A B) := by
  intro Δ e C h
  induction h with
  | projFst hA hB hp =>
    intro i p he
    simp only [pfstT, VExpr.proj.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact ⟨_, _, _, _, hA, hB, hp⟩
  | projSnd hA hB hp =>
    intro i p he
    simp only [psndT, VExpr.proj.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact ⟨_, _, _, _, hA, hB, hp⟩
  | conv _ _ ih _ => intro i p he; exact ih he
  | _ => intro i p he; cases he

/-- The form the claims use: a typed application has a typed head. -/
theorem hasType_appFn {Δ : List VExpr} {f a C : VExpr}
    (h : HasType Δ (.app f a) C) : ∃ A B, HasType Δ f (.pi A B) :=
  (hasType_app_inv h rfl).imp fun _ h => h.imp fun _ h => h.1

/-- …and a typed argument. -/
theorem hasType_appArg {Δ : List VExpr} {f a C : VExpr}
    (h : HasType Δ (.app f a) C) : ∃ A, HasType Δ a A :=
  (hasType_app_inv h rfl).elim fun _ h => h.elim fun _ h => ⟨_, h.2⟩

/-- A typed projection has a typed subject. -/
theorem hasType_projSubj {Δ : List VExpr} {i : Nat} {p C : VExpr}
    (h : HasType Δ (.proj i p) C) : ∃ P, HasType Δ p P :=
  (hasType_proj_inv h rfl).elim fun _ h => h.elim fun _ h => h.elim fun _ h =>
    h.elim fun _ h => ⟨_, h.2.2⟩

end Setlec.TTVerify
