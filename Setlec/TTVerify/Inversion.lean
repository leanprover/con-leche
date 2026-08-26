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

The **bridge** needs a little more, and only because of the shape
task #119's stage 2 now takes.  Threading a typing hypothesis through
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
Church–Rosser, unique typing, or weakening; in particular note that
**Π-injectivity is *not* among these and must not be added** — it is
semantically false under the domain-relative collapse
(`Setlec/TTVerify/DESIGN.md` §6, the beta clause).
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
