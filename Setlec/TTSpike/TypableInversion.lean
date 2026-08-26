import Setlec.TTSpike.InferOnlyRefuted

/-!
# The `Typable`-inversion family (Q3)

For each `VExpr` former: does `Typable e` invert to typability of the
subterms?  The method is the stage-2 one (`Setlec/TTVerify/Inversion.lean`,
`hasType_app_inv`): the subject of a derivation determines which rule
concluded it, up to `conv`, which does not change the subject.

**Where inversion holds** (mechanized below, plus `app`/`proj` already
on the stage-2 branch):

| former | inverts to |
|---|---|
| `app f a` | `f` at a `pi`, `a` at its domain (stage-2) |
| `proj i p` | `p` at a pair type (stage-2) |
| `lam A b` | `b` typable in `A :: Γ` — **not `A`** |
| `pi A B` | `A : sort u` and `B : sort v` in `A :: Γ` |
| `letE ty v b` | `ty : sort u`, `v : ty`, and the **substituted** body `b.inst v` — not `b` itself |

**Where inversion fails** (mechanized witnesses below):

* the **annotation of a `lam`** — the `lam` rule has no premise on its
  domain (§2.4's premise-free doctrine), so `lam A b` is typable with
  an untypable `A`;
* **every subterm of `eqE`** — `eqType` is premise-free, so
  `eqE T a b : Sort 0` holds with untypable `T`, `a`, `b`;
* (and the argument-side of `app` *does* invert, but only at the
  ambient domain — the F2-refuted gap to the annotation is recorded in
  the stage-2 DESIGN.)

The failures land **exactly on the positions an infer-only traversal
skips** (lam annotations, eqE components, app arguments' *domains*),
and the successes exactly on the positions it recurses into.  So the
inversion family is aligned with the design's traversal — the failures
do not by themselves break the induction; what breaks it is recorded in
`InferOnlyRefuted.lean` and `UniqueTypingRefuted.lean`.
-/

namespace Setlec.TT
namespace Spike

open VExpr

/-- Inversion for `lam`, subject-directed: the body is typed under the
annotation.  Nothing about the annotation itself is (or can be)
concluded. -/
theorem hasType_lam_inv :
    ∀ {Γ : List VExpr} {e C : VExpr}, HasType Γ e C →
      ∀ {A b : VExpr}, e = .lam A b → ∃ B, HasType (A :: Γ) b B := by
  intro Γ e C h
  induction h with
  | lam hb =>
    intro A b he
    simp only [VExpr.lam.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, hb⟩
  | conv _ _ ih _ => intro A b he; exact ih he
  | _ => intro A b he; first | cases he | (simp only [pfstT, psndT] at he; cases he)

theorem typable_lam_inv {Γ : List VExpr} {A b : VExpr}
    (h : Typable Γ (.lam A b)) : Typable (A :: Γ) b :=
  h.elim fun _ ht => (hasType_lam_inv ht rfl).imp fun _ h => h

/-- Inversion for `pi`: both components are sorted. -/
theorem hasType_pi_inv :
    ∀ {Γ : List VExpr} {e C : VExpr}, HasType Γ e C →
      ∀ {A B : VExpr}, e = .pi A B →
        ∃ u v, HasType Γ A (.sort u) ∧ HasType (A :: Γ) B (.sort v) := by
  intro Γ e C h
  induction h with
  | pi hA hB =>
    intro A B he
    simp only [VExpr.pi.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, _, hA, hB⟩
  | conv _ _ ih _ => intro A B he; exact ih he
  | _ => intro A B he; first | cases he | (simp only [pfstT, psndT] at he; cases he)

theorem typable_pi_inv {Γ : List VExpr} {A B : VExpr}
    (h : Typable Γ (.pi A B)) : Typable Γ A ∧ Typable (A :: Γ) B :=
  h.elim fun _ ht =>
    (hasType_pi_inv ht rfl).elim fun _ h => h.elim fun _ h =>
      ⟨⟨_, h.1⟩, ⟨_, h.2⟩⟩

/-- Inversion for `letE`: the annotation is a sort, the value is typed
at it, and the **substituted** body is typed — the raw body is not
(the rule types `body.inst val`, per the substituting-`letE` design). -/
theorem hasType_letE_inv :
    ∀ {Γ : List VExpr} {e C : VExpr}, HasType Γ e C →
      ∀ {ty val body : VExpr}, e = .letE ty val body →
        ∃ u B, HasType Γ ty (.sort u) ∧ HasType Γ val ty ∧
          HasType Γ (body.inst val) B := by
  intro Γ e C h
  induction h with
  | letE hty hval hbody =>
    intro ty val body he
    simp only [VExpr.letE.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨_, _, hty, hval, hbody⟩
  | conv _ _ ih _ => intro ty val body he; exact ih he
  | _ => intro ty val body he; first | cases he | (simp only [pfstT, psndT] at he; cases he)

theorem typable_letE_inv {Γ : List VExpr} {ty val body : VExpr}
    (h : Typable Γ (.letE ty val body)) :
    Typable Γ ty ∧ Typable Γ val ∧ Typable Γ (body.inst val) :=
  h.elim fun _ ht =>
    (hasType_letE_inv ht rfl).elim fun _ h => h.elim fun _ h =>
      ⟨⟨_, h.1⟩, ⟨_, h.2.1⟩, ⟨_, h.2.2⟩⟩

/-- A typed de Bruijn variable is in range — the tool for the failure
witnesses. -/
theorem hasType_bvar_lt :
    ∀ {Γ : List VExpr} {e C : VExpr}, HasType Γ e C →
      ∀ {i : Nat}, e = .bvar i → i < Γ.length := by
  intro Γ e C h
  induction h with
  | bvar hi =>
    intro i he
    simp only [VExpr.bvar.injEq] at he
    subst he
    exact (List.getElem?_eq_some_iff.mp hi).1
  | conv _ _ ih _ => intro i he; exact ih he
  | _ => intro i he; first | cases he | (simp only [pfstT, psndT] at he; cases he)

theorem bvar5_untypable : ¬ Typable [] (.bvar 5) := by
  rintro ⟨T, h⟩
  simpa using hasType_bvar_lt h rfl

/-- **Failure witness, `eqE`**: `eqType` is premise-free, so an `eqE`
with untypable components is typable. -/
theorem eqE_inversion_fails :
    Typable [] (.eqE natT (.bvar 5) (.bvar 5)) ∧ ¬ Typable [] (.bvar 5) :=
  ⟨⟨.sort 0, .eqType⟩, bvar5_untypable⟩

/-- **Failure witness, `lam` annotation**: the `lam` rule has no domain
premise, so a lambda with an untypable annotation is typable (its body
here types by premise-free `refl`). -/
theorem lam_annotation_inversion_fails :
    Typable [] (.lam (.bvar 5) .prf) ∧ ¬ Typable [] (.bvar 5) :=
  ⟨⟨.pi (.bvar 5) (.eqE natT natZeroT natZeroT),
    .lam (.refl (T := natT) (a := natZeroT))⟩, bvar5_untypable⟩

end Spike
end Setlec.TT
