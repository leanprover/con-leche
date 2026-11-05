module

public import ConLeche.Model.Env.CanonCrest
public import ConLeche.Verify.EnvExt
import ConLeche.Verify.BridgeDecl
import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Verify.Inductives.NestContInv

public section

/-!
# A recorded family's telescope, run

A member whose declared type does not show its telescope has it read at use: by a reduction at
the environment of the use. The block's check ran that reduction at its own environment. A run
does not see an extension of the environment it ran at, so every later reading finds what the
check found (`FamilyRan.read`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify

open ConLeche (Env Expr Name ConstantVal IndCaps fueledOps reducedFormer)

universe w

variable {V : Type w} [SetTheory V]

/-- An extension of an extension. -/
theorem envExt_trans {env₁ env₂ env₃ : Env} (h₁ : EnvExt env₁ env₂)
    (hf : ∀ n ci, env₂.find? n = some ci → env₃.find? n = some ci)
    (ht : ∀ T, (env₂.find? T).isSome = true → env₃.findTable? T = env₂.findTable? T) :
    EnvExt env₁ env₃ where
  find := fun n ci h => hf n ci (h₁.find n ci h)
  table := fun T hT => by
    have hs : (env₂.find? T).isSome = true := by
      cases hc : env₁.find? T with
      | none => rw [hc] at hT; exact nomatch hT
      | some ci => rw [h₁.find T ci hc]; rfl
    rw [ht T hs]; exact h₁.table T hT
  facts := h₁.facts

/-- A family's telescope is one, at every fuel a run has. -/
theorem familyTelescope_unique {env : Env} {cv : ConstantVal} {caps : IndCaps} {F₁ F₂ : Nat}
    {t₁ t₂ : Expr}
    (h₁ : ConLeche.familyTelescope (fueledOps .verified F₁) env cv caps = .ok t₁)
    (h₂ : ConLeche.familyTelescope (fueledOps .verified F₂) env cv caps = .ok t₂) : t₁ = t₂ := by
  rcases ConLeche.familyTelescope_cases h₁ with ⟨hfl, rfl⟩ | ⟨hfl, -, -, r₁, hr₁, rfl⟩ <;>
  rcases ConLeche.familyTelescope_cases h₂ with ⟨hfl', rfl⟩ | ⟨hfl', -, -, r₂, hr₂, rfl⟩
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
  rw [dif_pos hx]
  exact familyTelescope_unique hx.choose_spec.choose_spec h

/-- **The reductions behind a carrier's recorded telescopes**: a member whose declared type does
not show its telescope reduced to what its block read, at a prefix of the environment. -/
@[expose] def FamilyRan {env : Env} (mp : EnvModelM V env) : Prop :=
  ∀ D ∈ mp.lfpBlocks, ∀ (mm : Nat) (f : ConstantVal), mm < D.k → D.shown mm = some f →
    ∀ (cv : ConstantVal) (caps : IndCaps), env.find? (D.member mm) = some (.indInfo cv caps) →
    ConLeche.formerDefHeaded cv = true →
    ∃ (envB : Env) (F : Nat), EnvExt envB env ∧ cv.type.constsResolve envB = true ∧
      reducedFormer (fueledOps .verified F) envB cv (caps.nparams + caps.nIdx) = .ok f

/-- **What a run reads of a recorded family's telescope is what its block read**, at an
environment that extends the carrier's, with the carrier's blocks. -/
theorem FamilyRan.read {env env' : Env} {mp : EnvModelM V env} {mk : EnvModelM V env'}
    (hS : FamilyRan mp) (hx : EnvExt env env') (hb : ∀ D ∈ mk.lfpBlocks, D ∈ mp.lfpBlocks)
    (F : Nat) : FamilyRead mk F := by
  intro D hD mm cv caps ty hmm hf hfam
  obtain ⟨-, -, hrd, -⟩ := mk.lfp_ok D hD
  obtain ⟨cv', caps', hf', ⟨hsame, hsh⟩, -⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  rcases ConLeche.familyTelescope_cases hfam with ⟨hfl, rfl⟩ | ⟨hfl, -, -, cvR, hrun, rfl⟩
  · rw [hsame hfl]
  · rcases hsh with ⟨-, hn⟩ | ⟨f, hs, -⟩
    · rw [hfl] at hn; exact nomatch hn
    · obtain ⟨cv₀, caps₀, hf₀⟩ := (mp.lfp_ok D (hb D hD)).2.1.1 mm hmm
      have hf₁ := hx.find _ _ hf₀
      rw [hf] at hf₁
      obtain ⟨rfl, rfl⟩ : cv = cv₀ ∧ caps = caps₀ := by simpa using hf₁
      obtain ⟨envB, F₁, hxB, hr, hrun₁⟩ := hS D (hb D hD) mm f hmm hs cv caps hf₀ hfl
      have h₁ := reducedFormer_ext (envExt_trans hxB hx.find hx.table) hr hrun₁
      have g₁ : reducedFormer (fueledOps .verified (max F₁ F)) env' cv (caps.nparams + caps.nIdx)
          = .ok f := by
        rw [← reducedFormer_datF]
        exact ConLeche.Cached.FueledM.up (Nat.le_max_left _ _) (by rw [reducedFormer_datF]; exact h₁)
      have g₂ : reducedFormer (fueledOps .verified (max F₁ F)) env' cv (caps.nparams + caps.nIdx)
          = .ok cvR := by
        rw [← reducedFormer_datF]
        exact ConLeche.Cached.FueledM.up (Nat.le_max_right _ _) (by rw [reducedFormer_datF]; exact hrun)
      rw [g₁] at g₂
      obtain rfl : f = cvR := by simpa using g₂
      simp [LfpDatum.formerAt, hs]

end ConLeche.Model
