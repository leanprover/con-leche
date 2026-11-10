module

public import ConLeche.Model.Env.CanonCrest
public import ConLeche.Model.Cover
public import ConLeche.Verify.EnvExt
import ConLeche.Verify.BridgeDecl
import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Verify.Inductives.NestContInv

public section

/-!
# What a run reads of an environment

A family's telescope walk (`familyTelescope`) gives one result at every fuel that reaches one
(`familyTelescope_unique`), named as any run reads it (`readTelescope`), and reads alike at an
extension of the environment it ran at (`familyTelescope_ext`).  What a run needs of an
environment to be read at its extensions is `NatFacts`; the tables across added constants keep
their old names' entries (`findTable_of_added`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify

open ConLeche (Env Expr Name ConstantVal ConstantInfo IndCaps fueledOps reducedFormer)

universe w

variable {V : Type w} [SetTheory V]

/-- A family's telescope is one, at every fuel a run has. -/
theorem familyTelescope_unique {env : Env} {cv : ConstantVal} {caps : IndCaps} {F₁ F₂ : Nat}
    {t₁ t₂ : Expr}
    (h₁ : ConLeche.familyTelescope (fueledOps .verified F₁) env cv caps = .ok t₁)
    (h₂ : ConLeche.familyTelescope (fueledOps .verified F₂) env cv caps = .ok t₂) : t₁ = t₂ := by
  rcases ConLeche.familyTelescope_cases h₁ with ⟨hfl, rfl⟩ | ⟨hfl, r₁, hr₁, rfl⟩ <;>
  rcases ConLeche.familyTelescope_cases h₂ with ⟨hfl', rfl⟩ | ⟨hfl', r₂, hr₂, rfl⟩
  · rfl
  · rw [hfl] at hfl'; exact nomatch hfl'
  · rw [hfl] at hfl'; exact nomatch hfl'
  · have g₁ : reducedFormer (fueledOps .verified (max F₁ F₂)) env cv (caps.nparams + caps.nIdx)
        = .ok r₁ := by
      rw [← reducedFormer_datF]
      exact ConLeche.Cached.FueledM.up (Nat.le_max_left _ _) (by rw [reducedFormer_datF]; exact hr₁)
    have g₂ : reducedFormer (fueledOps .verified (max F₁ F₂)) env cv (caps.nparams + caps.nIdx)
        = .ok r₂ := by
      rw [← reducedFormer_datF]
      exact ConLeche.Cached.FueledM.up (Nat.le_max_right _ _) (by rw [reducedFormer_datF]; exact hr₂)
    rw [g₁] at g₂
    obtain rfl : r₁ = r₂ := by simpa using g₂
    rfl

open Classical in
/-- **A family's telescope, as any run reads it** (its declared type where no run reaches one). -/
noncomputable def readTelescope (env : Env) (cv : ConstantVal) (caps : IndCaps) : Expr :=
  if h : ∃ F ty, ConLeche.familyTelescope (fueledOps .verified F) env cv caps = .ok ty then
    h.choose_spec.choose
  else cv.type

theorem readTelescope_eq {env : Env} {cv : ConstantVal} {caps : IndCaps} {F : Nat} {ty : Expr}
    (h : ConLeche.familyTelescope (fueledOps .verified F) env cv caps = .ok ty) :
    readTelescope env cv caps = ty := by
  have hx : ∃ F ty, ConLeche.familyTelescope (fueledOps .verified F) env cv caps = .ok ty :=
    ⟨F, ty, h⟩
  unfold readTelescope
  rw [dite_eq_left hx]
  exact familyTelescope_unique hx.choose_spec.choose_spec h

/-- The tables on the old names across added constants and no table. -/
theorem findTable_of_added {env env₂ : Env} {new : List ConstantInfo}
    (hnew : env₂.consts = new ++ env.consts) (htab : env₂.tables = env.tables) (T : Name)
    (hT : (env.find? T).isSome = true) : env₂.findTable? T = env.findTable? T := by
  have hs₂ : (env₂.find? T).isSome = true := by
    show (env₂.consts.find? (·.name == T)).isSome = true
    rw [hnew, List.find?_append, Option.isSome_or]
    exact Bool.or_eq_true_iff.mpr (Or.inr hT)
  unfold Env.findTable?
  rw [hs₂, hT, htab]

/-- A family's telescope reads alike at an extension. -/
theorem familyTelescope_ext {env₁ env₂ : Env} (hx : EnvExt env₁ env₂) (F : Nat) {cv : ConstantVal}
    (caps : IndCaps) (hr : cv.type.constsResolve env₁ = true) :
    ConLeche.familyTelescope (fueledOps .verified F) env₂ cv caps
      = ConLeche.familyTelescope (fueledOps .verified F) env₁ cv caps := by
  unfold ConLeche.familyTelescope ConLeche.reducedFormer
  rw [whnfTelescope_ext hx F _ 0 hr]

/-- **What a run needs of an environment to be read at its extensions.** -/
structure NatFacts (env : Env) : Prop where
  trio : (env.find? ConLeche.natName).isSome = true ∨ (env.find? ConLeche.natZeroName).isSome = true ∨
      (env.find? ConLeche.natSuccName).isSome = true →
    (env.find? ConLeche.natName).isSome = true ∧ (env.find? ConLeche.natZeroName).isSome = true ∧
      (env.find? ConLeche.natSuccName).isSome = true

/-- **What the knot reads of an environment past the term in hand**, off the carrier. -/
theorem EnvModelM.storedFacts {env : Env} (mp : EnvModelM V env) (hN : NatFacts env) :
    StoredFacts env where
  wf := mp.base2.wf
  natTrio := hN.trio
  recCtors := mp.base2.rec_ctors
  tableCtors := fun _ _ hf => by
    obtain ⟨-, -, -, -, cvC, hc, -⟩ := mp.base2.proj_ok _ _ hf
    rw [hc]; rfl
  boolCtors := by
    have hg : ∀ c, c ∈ ConLeche.natOpNames → (c = ConLeche.natBeqName ∨ c = ConLeche.natBleName) →
        (env.find? c).isSome = true →
        (env.find? ConLeche.boolTrueName).isSome = true ∧
          (env.find? ConLeche.boolFalseName).isSome = true := by
      intro c hmemc hc hs
      obtain ⟨-, -, hb⟩ := ConLeche.natOpGuard_inv (natOpGuardLaw_of mp c (Or.inl hmemc) hs).1
      obtain ⟨⟨ciT, hT, -⟩, ⟨ciF, hF', -⟩⟩ := hb (by rcases hc with h | h <;> simp [h])
      rw [hT, hF']
      exact ⟨rfl, rfl⟩
    rintro (h | h)
    · exact hg _ (by simp [ConLeche.natOpNames]) (Or.inl rfl) h
    · exact hg _ (by simp [ConLeche.natOpNames]) (Or.inr rfl) h

omit [SetTheory V] in
/-- An unreserved name is none of `Nat`'s block's three. -/
theorem nat_names_of_unreserved {n : Name} (h : ConLeche.reservedBasisNames.contains n = false) :
    n ≠ ConLeche.natName ∧ n ≠ ConLeche.natZeroName ∧ n ≠ ConLeche.natSuccName := by
  refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; revert h; decide)

omit [SetTheory V] in
/-- New constants named none of `Nat`'s block's names. -/
theorem NatFacts.append {env env₂ : Env} {new : List ConstantInfo} (hN : NatFacts env)
    (hnew : env₂.consts = new ++ env.consts)
    (hres : ∀ c ∈ new, c.name ≠ ConLeche.natName ∧ c.name ≠ ConLeche.natZeroName ∧
      c.name ≠ ConLeche.natSuccName) : NatFacts env₂ := by
  have hf : ∀ n, (∀ c ∈ new, c.name ≠ n) → env₂.find? n = env.find? n := by
    intro n hn
    show env₂.consts.find? (·.name == n) = _
    rw [hnew, List.find?_append]
    rw [List.find?_eq_none.mpr (fun c hc => by
      intro he
      exact hn c hc (by simpa using he))]
    rfl
  have h₁ := hf ConLeche.natName fun c hc => (hres c hc).1
  have h₂ := hf ConLeche.natZeroName fun c hc => (hres c hc).2.1
  have h₃ := hf ConLeche.natSuccName fun c hc => (hres c hc).2.2
  exact ⟨by rw [h₁, h₂, h₃]; exact hN.trio⟩

end ConLeche.Model
