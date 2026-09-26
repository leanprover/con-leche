module

public import ConLeche.Verify.Denote
import ConLeche.Verify.StrLitExpr

public section

/-!
# The string-literal constructor form, denoted

Relocated out of `ConLeche/TTVerify/{NatOpsStep,StrLitStep}.lean`
(task #148, T3) and **generalized from `EnvTT` to `ValParams`**: every
statement below is about `denote`, `Env.find?` and the literal-support
guard — no typing judgment, no `EnvTT` field beyond level insensitivity.  Both
lanes need them: the TT lane at its string-literal inference clause, the
`ConLeche/SetR/*` bridge at R7/R16 (`Red.strLitCtor`'s `denoteClosed` side
condition) and at `defeqStep`'s two string-expansion cases.

The `EnvTT`-shaped specializations stay where their consumers are
(`denote_const_nolevels`, `denote_nilTerm`, `denote_consTerm`,
`denote_strLitList`, `denote_strLitToConstructor`); each is now one line
over the generalized statement here, so there is exactly one proof.

The namespace is `ConLeche.Verify` because that is where `denote` and
the shape lemmas already live; the module sits below both lanes.
-/

namespace ConLeche.Verify

open ConLeche.Term

/-! ## The pinned shapes

Each guard component is a `match` on the stored declaration, so
extracting the shape is a `split` and a `simp`.  They are separated
from the typings below because the *shape* facts are about `Env` alone
and would move to `ConLeche/Verify/*` with the rest of the stranded
guard machinery. -/

/-- `Char : Type`. -/
theorem char_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci, env.find? charName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type = .sort (.succ .zero) := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, h6⟩, -⟩ := hg
  cases hf : env.find? charName with
  | none => rw [hf] at h6; exact nomatch h6
  | some ci =>
    rw [hf] at h6
    simp only [charTyOk, Bool.and_eq_true, beq_iff_eq] at h6
    exact ⟨ci, rfl, by simpa [List.isEmpty_iff] using h6.1, h6.2⟩

/-- `Char.ofNat : Nat → Char`. -/
theorem charOfNat_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci mb, env.find? charOfNatName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type =
        .forallE (.const natName []) (.const charName []) mb := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, h7⟩ := hg
  cases hf : env.find? charOfNatName with
  | none => rw [hf] at h7; exact nomatch h7
  | some ci =>
    rw [hf] at h7
    simp only [charOfNatTyOk, Bool.and_eq_true] at h7
    obtain ⟨he, hty⟩ := h7
    split at hty
    · next c1 c2 mb hsh =>
      simp only [beq_iff_eq, Bool.and_eq_true] at hty
      obtain ⟨rfl, rfl⟩ := hty
      exact ⟨ci, mb, rfl, by simpa [List.isEmpty_iff] using he, hsh⟩
    · exact nomatch hty

/-- `String.ofList : List.{0} Char → String`. -/
theorem stringOfList_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci mb, env.find? stringOfListName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type =
        .forallE (.app (.const listName [.zero]) (.const charName []))
          (.const stringName []) mb := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg
  cases hf : env.find? stringOfListName with
  | none => rw [hf] at h2; exact nomatch h2
  | some ci =>
    rw [hf] at h2
    simp only [stringOfListTyOk, Bool.and_eq_true] at h2
    obtain ⟨he, hty⟩ := h2
    split at hty
    · next l1 us1 c1 c2 mb hsh =>
      simp only [beq_iff_eq, Bool.and_eq_true] at hty
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hty
      exact ⟨ci, mb, rfl, by simpa [List.isEmpty_iff] using he, hsh⟩
    · exact nomatch hty

/-! ## The list constructors

`List.nil` and `List.cons` are the two support constants with a level
parameter, and `strLitT` instantiates it at `Level.zero`.  Their types
therefore have to be denoted at the *substituted* assignment, which is
where `EnvTT.val_params` earns its keep: the assignment `strLitT` uses
and the one the stored type is denoted at differ only away from the
constant's own parameters, so the valuation cannot tell them apart. -/

/-- `List.nil.{p} : ∀ (α : Sort (p+1)), List.{p} α`. -/
theorem listNil_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci p mb, env.find? listNilName = some ci ∧
      ci.toConstantVal.levelParams = [p] ∧
      ci.toConstantVal.type =
        .forallE (.sort (.succ (.param p)))
          (.app (.const listName [.param p]) (.bvar 0)) mb := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h4⟩, -⟩, -⟩, -⟩ := hg
  cases hf : env.find? listNilName with
  | none => rw [hf] at h4; exact nomatch h4
  | some ci =>
    rw [hf] at h4
    simp only [listNilTyOk] at h4
    split at h4
    · next p hlp =>
      split at h4
      · next u1 l1 us1 mb hsh =>
        simp only [beq_iff_eq, Bool.and_eq_true] at h4
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
        exact ⟨ci, p, mb, rfl, hlp, hsh⟩
      · exact nomatch h4
    · exact nomatch h4

/-- `List.cons.{p} : ∀ (α : Sort (p+1)) (_ : α) (_ : List.{p} α),
List.{p} α`. -/
theorem listCons_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci p mb₁ mb₂ mb₃, env.find? listConsName = some ci ∧
      ci.toConstantVal.levelParams = [p] ∧
      ci.toConstantVal.type =
        .forallE (.sort (.succ (.param p)))
          (.forallE (.bvar 0)
            (.forallE (.app (.const listName [.param p]) (.bvar 1))
              (.app (.const listName [.param p]) (.bvar 2)) mb₃) mb₂) mb₁ := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, h5⟩, -⟩, -⟩ := hg
  cases hf : env.find? listConsName with
  | none => rw [hf] at h5; exact nomatch h5
  | some ci =>
    rw [hf] at h5
    simp only [listConsTyOk] at h5
    split at h5
    · next p hlp =>
      split at h5
      · next u1 l1 us1 l2 us2 mb₃ mb₂ mb₁ hsh =>
        simp only [beq_iff_eq, Bool.and_eq_true] at h5
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h5
        exact ⟨ci, p, mb₁, mb₂, mb₃, rfl, hlp, hsh⟩
      · exact nomatch h5
    · exact nomatch h5

end ConLeche.Verify
