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
