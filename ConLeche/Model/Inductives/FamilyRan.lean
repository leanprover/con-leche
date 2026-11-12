module

public import ConLeche.Model.Env.CanonCrest
public import ConLeche.Model.Cover
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

open ConLeche (Env Expr Name ConstantVal ConstantInfo IndCaps fueledOps reducedFormer)

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

/-- **The reductions behind a carrier's recorded telescopes**: a member whose declared type does
not show its telescope reduced to what its block read, at a prefix of the environment. -/
@[expose] def FamilyRan {env : Env} (mp : EnvModelM V env) : Prop :=
  ∀ D ∈ mp.lfpBlocks, ∀ (mm : Nat) (f : ConstantVal), mm < D.k → D.telescope mm = some f →
    ∀ (cv : ConstantVal) (caps : IndCaps), env.find? (D.member mm) = some (.indInfo cv caps) →
    ConLeche.formerDefHeaded cv = true →
    ∃ (envB : Env) (F : Nat), EnvExt envB env ∧ cv.type.constsResolve envB = true ∧
      reducedFormer (fueledOps .verified F) envB cv (caps.nparams + caps.nIdx) = .ok f

/-- **What a run reads of a recorded family's telescope is what its block read**, at an
environment that extends the carrier's, with the carrier's blocks. -/
theorem FamilyRan.read {env env' : Env} {mp : EnvModelM V env} {mk : EnvModelM V env'}
    (hS : FamilyRan mp) (hxf : ∀ n ci, env.find? n = some ci → env'.find? n = some ci)
    (hxt : ∀ T, (env.find? T).isSome = true → env'.findTable? T = env.findTable? T)
    (hb : ∀ D ∈ mk.lfpBlocks, D ∈ mp.lfpBlocks) (F : Nat) : FamilyRead mk F := by
  intro D hD mm cv caps ty hmm hf hfam
  obtain ⟨-, -, hrd, -⟩ := mk.lfp_ok D hD
  obtain ⟨cv', caps', hf', ⟨hsame, hsh⟩, -⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  rcases ConLeche.familyTelescope_cases hfam with ⟨hfl, rfl⟩ | ⟨hfl, cvR, hrun, rfl⟩
  · rw [hsame hfl]
  · rcases hsh with ⟨-, hn⟩ | ⟨f, hs, -⟩
    · rw [hfl] at hn; exact nomatch hn
    · obtain ⟨cv₀, caps₀, hf₀⟩ := (mp.lfp_ok D (hb D hD)).2.1.1 mm hmm
      have hf₁ := hxf _ _ hf₀
      rw [hf] at hf₁
      obtain ⟨rfl, rfl⟩ : cv = cv₀ ∧ caps = caps₀ := by simpa using hf₁
      obtain ⟨envB, F₁, hxB, hr, hrun₁⟩ := hS D (hb D hD) mm f hmm hs cv caps hf₀ hfl
      have h₁ := reducedFormer_ext (envExt_trans hxB hxf hxt) hr hrun₁
      have hfam₁ : ConLeche.familyTelescope (fueledOps .verified F₁) env' cv caps = .ok f.type := by
        unfold ConLeche.familyTelescope
        rw [ite_eq_left hfl, h₁]
        rfl
      rw [familyTelescope_unique hfam hfam₁]
      simp [LfpDatum.formerAt, hs]

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
  opDefn := mp.op_defn
  tableCtors := fun _ _ hf => by
    obtain ⟨-, -, -, -, cvC, _, hc, -⟩ := mp.base2.proj_ok _ _ hf
    rw [hc]; rfl
  boolCtors := by
    have hg : ∀ c, c ∈ ConLeche.natOpNames → (c = ConLeche.natBeqName ∨ c = ConLeche.natBleName) →
        ConLeche.isDefinitionAt env c = true →
        (env.find? ConLeche.boolTrueName).isSome = true ∧
          (env.find? ConLeche.boolFalseName).isSome = true := by
      intro c hmemc hc hs
      obtain ⟨-, -, hb⟩ := ConLeche.natOpGuard_inv (natOpGuardLaw_of mp c (Or.inl hmemc) hs)
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

/-- **Shown telescopes across a step that records none.** -/
theorem FamilyRan.step {env env' : Env} {mp : EnvModelM V env} {mp' : EnvModelM V env'}
    (hS : FamilyRan mp) (r : CoverRel mp mp')
    (htb : ∀ T, (env.find? T).isSome = true → env'.findTable? T = env.findTable? T) :
    FamilyRan mp' := by
  intro D hD mm f hmm hs cv caps hf hdh
  rcases r.blocks D hD with h₀ | h₀
  · obtain ⟨cv₀, caps₀, hf₀⟩ := (mp.lfp_ok D h₀).2.1.1 mm hmm
    have hf₁ := r.find _ _ hf₀
    rw [hf] at hf₁
    obtain ⟨rfl, rfl⟩ : cv = cv₀ ∧ caps = caps₀ := by simpa using hf₁
    obtain ⟨envB, F, hx, hres, hrun⟩ := hS D h₀ mm f hmm hs cv caps hf₀ hdh
    exact ⟨envB, F, envExt_trans hx r.find htb, hres, hrun⟩
  · rw [h₀] at hs; exact nomatch hs

end ConLeche.Model
