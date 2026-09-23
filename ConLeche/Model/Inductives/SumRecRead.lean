module

public import ConLeche.Model.Inductives.StructRecRead
import ConLeche.Model.Annot.BitInst
public section

/-!
# The generated sum recursor's readings (task #175 sum-types, indexed)

`ConLeche/Model/Inductives/StructRecRead.lean` at a constructor list over
an indexed family: the generated recursor type reads to the Π-tower
over `sumRecDataAV` (parameters, motive over the index telescope, one
minor per constructor, the index telescope again, major), with the
core `motive ı⃗ t`, and rule `j` reads to the λ-tower over
`sumRuleDataAV` at constructor `j`'s field data, with the core
`minor_j f⃗`.  The minor entries are read by one induction over the
constructor list (`denoteP_minorsPis` / `denoteP_minorsLams`), the
accumulated variables (the motive first, then the earlier minors)
threaded as `extras`.

The one genuinely new reading is the minor's conclusion
`motive e⃗ (C p⃗ f⃗)`: the constructor's index expressions, spelled at
the recursor frame (under the extras), read to the constructor's own
index readings lifted above the fields
(`denoteMetaSpine_idxArgs_lift`) — obtained by reading the whole opened
residual `T p⃗ e⃗` at that frame and inverting the application spine.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BinderMeta PropWhen)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## `AnnotTerm` bookkeeping -/

theorem liftN_mkAppN (n k : Nat) : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    AnnotTerm.liftN n (AnnotTerm.mkAppN f as) k
      = AnnotTerm.mkAppN (AnnotTerm.liftN n f k) (as.map fun a => AnnotTerm.liftN n a k)
  | [], _ => rfl
  | a :: as, f => by
    simp only [AnnotTerm.mkAppN_cons, List.map_cons, liftN_mkAppN n k as, AnnotTerm.liftN_app]

theorem mkAppN_inj_args :
    ∀ {as bs : List AnnotTerm} {f g : AnnotTerm},
      AnnotTerm.mkAppN f as = AnnotTerm.mkAppN g bs → as.length = bs.length → f = g ∧ as = bs
  | [], [], _, _, h, _ => ⟨h, rfl⟩
  | [], _ :: _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, hl => by simp at hl
  | a :: as, b :: bs, f, g, h, hl => by
    simp only [AnnotTerm.mkAppN_cons] at h
    obtain ⟨hfg, hab⟩ := mkAppN_inj_args h (by simpa using hl)
    obtain ⟨rfl, rfl⟩ := AnnotTerm.app.inj hfg
    exact ⟨rfl, by rw [hab]⟩

/-- A leaf fixed by every one-step lift is fixed by every lift. -/
theorem liftN_eq_self_of_one {e : AnnotTerm} (h : ∀ k, AnnotTerm.liftN 1 e k = e) :
    ∀ (n k : Nat), AnnotTerm.liftN n e k = e
  | 0, k => AnnotTerm.liftN_zero e k
  | n + 1, k => by
    rw [show n + 1 = 1 + n from by omega, ← AnnotTerm.liftN_liftN e 1 n k,
      liftN_eq_self_of_one h n k, h k]

theorem DenoteMetaSpine.append_inv {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ {as bs : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d (as ++ bs) vs →
      ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧
        DenoteMetaSpine acval env φ d as vs₁ ∧ DenoteMetaSpine acval env φ d bs vs₂
  | [], bs, vs, h => ⟨[], vs, rfl, .nil, h⟩
  | a :: as, bs, vs, h => by
    rw [List.cons_append] at h
    cases h with
    | cons ha htl =>
      obtain ⟨vs₁, vs₂, rfl, h1, h2⟩ := DenoteMetaSpine.append_inv htl
      exact ⟨_ :: vs₁, vs₂, rfl, .cons ha h1, h2⟩

theorem DenoteMetaSpine.unique {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ {as : List Expr} {vs vs' : List AnnotTerm},
      DenoteMetaSpine acval env φ d as vs → DenoteMetaSpine acval env φ d as vs' → vs = vs'
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _, _, .cons ha h, .cons ha' h' => by
    rw [Option.some.inj (ha.symm.trans ha'), DenoteMetaSpine.unique h h']

/-! ## The entries -/

/-- A constructor datum: name, field count, field data, index readings. -/
abbrev CtorDatum := Name × Nat × List (Nat × Nat × AnnotTerm) × List AnnotTerm

end ConLeche.Model
