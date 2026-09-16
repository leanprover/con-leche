module

public import ConLeche.Model.Inductives.NestedPremise
import ConLeche.Model.Inductives.BlockRepCross
import ConLeche.Model.Install
import ConLeche.Verify.Inductives.ContainerFrame
import ConLeche.Verify.Inductives.NestedGroupInv
public section

/-!
# A container's block model across an environment extension (task #315, M7-3)

`EnvModelB` (`NestedPremise.lean`) carries `EnvBlockModels`: every
stored container's block model, at the carrier.  The fold extends the
environment one declaration at a time, so the field's MAINTENANCE is
two questions per stage, and this module answers both generically:

* **does the reading move?** — `containerInfo?` consults the
  environment only through inductive-kind lookups, so a non-inductive
  extension leaves every container's block exactly as it was
  (`containerInfo?_cons_nonInd`, `Verify/Inductives/ContainerFrame.lean`),
  and an inductive one leaves every OLD container's alone
  (`containerInfo?_ext_ind`);
* **does the block model move?** — no: `ContainerModeled`'s
  model-facing clauses are the block's representation and its typing,
  and those cross an extension by `BlockRepCross.lean`'s four
  hypotheses (`hF`, `hres`, `hag`, `hde`).  `ContainerModeled.crossEnv`
  is that transport; its remaining clauses (`k`, `nP`, `inj`, `frame`,
  `ordFree`, `pinsNotMembers`, `pinNP`) name no model at all — `pinNP`
  reads `containerInfo?` at the block's OWN pre-block environment
  `d.env₀`, which no later extension touches.

`EnvModelB.ofNonIndStep` puts the two together at the shape every
VALUE kind of the fold installs (`NonIndStep`): nothing at all, or one
fresh cons of a kind that is neither inductive nor a projection table.
Its one model-facing input is `AcvalAgrees` — the new carrier values
every old constant as the old one did — which the cons-level steps
always proved (their `acvalWith` equation, `exists_agrees_of_cons`)
and the stage theorems used to drop.  The lifts themselves are
`EnvModelBStages.lean`.

An INDUCTIVE extension keeps `EnvBlockModels` only modulo the new
block's own containers, which is the installing route's obligation:
`EnvBlockModels.crossInd` takes it as its last argument.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecRule ContainerInfo
  IndCaps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## The group is never empty -/

/-- **A container's group has a member**: `containerInfo?` returns only
a group whose name list CONTAINS the container it was asked about
(`names.contains I`), and the members are that list, read one by one. -/
theorem containerInfo?_members_pos {env : Env} {I : Name} {ci : ContainerInfo}
    (h : ConLeche.containerInfo? env I = some ci) : 0 < ci.members.length := by
  obtain ⟨-, -, -, -, -, -, -, -, hmem, -⟩ := ConLeche.containerInfo?_inv h
  cases hc : ci.members with
  | nil => rw [hc] at hmem; exact nomatch hmem
  | cons M Ms => simp

/-! ## The block model across the change -/

/-- **A container's block model crosses an environment change**: its
representation (`IsBlockModels`), the per-member `IsBlockModel` of the
`member` clause and the three typing clauses travel by
`BlockRepCross.lean`'s four hypotheses; every other clause is
model-free (`pinNP` reads `containerInfo?` at `d.env₀`, the block's own
pre-block environment, not at the model's). -/
theorem ContainerModeled.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {ci : ContainerInfo} {d : BlockModel V}
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hk : 0 < d.k) (C : ContainerModeled m₁ ci d) : ContainerModeled m₂ ci d where
  k := C.k
  nP := C.nP
  reps := C.reps.crossEnv hF hres hag hde
  typed := fun ψ =>
    ⟨(C.typed ψ).1.crossEnv hag C.reps, (C.typed ψ).2.1.crossEnv hag C.reps,
      (C.typed ψ).2.2.crossEnv hag C.reps hk⟩
  inj := C.inj
  member := fun i M hM => by
    obtain ⟨hname, hctors, cvR, mI, rP, rules, hI⟩ := C.member i M hM
    exact ⟨hname, hctors, cvR, mI, rP, rules, hI.crossEnv hF hres hag hde⟩
  frame := C.frame
  ordFree := C.ordFree
  pinsNotMembers := C.pinsNotMembers
  pinNP := C.pinNP

/-! ## The field across an extension -/

/-- **The blocks survive a change of carrier at the SAME environment**:
the reading does not move at all, and `ContainerModeled` crosses on the
agreement alone. -/
theorem EnvBlockModels.crossSame {env : Env} {m₁ m₂ : EnvModel V env}
    (hag : AcvalAgrees m₁ m₂) (hb : EnvBlockModels m₁) : EnvBlockModels m₂ := by
  intro J ci hci
  obtain ⟨d, C⟩ := hb J ci hci
  refine ⟨d, C.crossEnv (fun _ _ _ hf => hf) (fun _ h => h) hag ?_
    (C.k ▸ containerInfo?_members_pos hci)⟩
  intro ψ dp e ea hd
  rw [denoteMeta_acval_congr (acval₁ := m₂.acval) (acval₂ := m₁.acval) hag dp e]
  exact hd

/-- **The blocks survive a non-inductive fresh cons**: the reading does
not move (`containerInfo?_cons_nonInd`) and the block model crosses.
The only model-facing input is the carriers' AGREEMENT at the stored
names: `denoteMeta` consults the valuation only at names it found, so
the reading transport `hde` follows from it
(`denoteMeta_acval_congr` then `denoteMeta_env_mono`). -/
theorem EnvBlockModels.crossCons {env : Env} {m₁ : EnvModel V env} {c₀ : ConstantInfo}
    {m₂ : EnvModel V ⟨c₀ :: env.consts⟩}
    (hfresh : env.find? c₀.name = none)
    (hkind : (∀ cv caps, c₀ ≠ .indInfo cv caps) ∧
      (∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) ∧
      (∀ cv nP nF, c₀ ≠ .ctorInfo cv nP nF))
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl)
    (hag : AcvalAgrees m₁ m₂)
    (hb : EnvBlockModels m₁) : EnvBlockModels m₂ := by
  intro J ci hci
  rw [ConLeche.containerInfo?_cons_nonInd hfresh hkind] at hci
  obtain ⟨d, C⟩ := hb J ci hci
  refine ⟨d, C.crossEnv (fun n c _ hf => Env.find?_cons_of_fresh hfresh hf)
    (constsResolve_of_findPreserved (findPreserved_cons hfresh)) hag ?_
    (C.k ▸ containerInfo?_members_pos hci)⟩
  intro ψ dp e ea hd
  refine denoteMeta_env_mono (findPreserved_cons hfresh) (litGuardsMono_cons hfresh)
    (findProj?_cons_of_base_none hntc) dp e ?_
  rw [denoteMeta_acval_congr (acval₁ := m₂.acval) (acval₂ := m₁.acval) hag dp e]
  exact hd

/-- **The blocks survive an inductive extension, modulo the new block's
own containers**: an OLD container's block is read the same at the
extended environment (`containerInfo?_ext_ind`) and its model crosses;
the containers the extension itself creates are the installing route's
obligation, `hnew`. -/
theorem EnvBlockModels.crossInd {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {N : List Name}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnewN : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨ n ∈ N)
    (hfreshN : ∀ n ∈ N, env₁.find? n = none)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) → n.str "rec" ∈ N → n ∈ N)
    (hwf : ConLeche.EnvWF env₁) (hrc : ConLeche.RecCtorsStored env₁)
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hb : EnvBlockModels m₁)
    (hnew : ∀ J ∈ N, ∀ ci : ContainerInfo, ConLeche.containerInfo? env₂ J = some ci →
      ∃ d : BlockModel V, ContainerModeled m₂ ci d) :
    EnvBlockModels m₂ := by
  intro J ci hci
  by_cases hJ : J ∈ N
  · exact hnew J hJ ci hci
  · have h₁ := ConLeche.containerInfo?_ext_ind hext hnewN hfreshN hrecN hwf hrc hJ hci
    obtain ⟨d, C⟩ := hb J ci h₁
    exact ⟨d, C.crossEnv hF hres hag hde (C.k ▸ containerInfo?_members_pos h₁)⟩

/-! ## The non-inductive stages of the fold -/

/-- **A stage that installs NOTHING, or conses ONE fresh constant of a
non-inductive kind** — the shape of every value-kind stage of the P
fold (definitions, theorems, opaques, axioms; the tolerated axiom skip
is the left arm): the new environment is the old one or one cons whose
name is fresh and whose head is neither of the three inductive kinds
`containerInfo?` reads nor a projection table. -/
@[expose] def NonIndStep (env env₂ : Env) : Prop :=
  env₂ = env ∨
    ∃ c₀ : ConstantInfo, env₂ = ⟨c₀ :: env.consts⟩ ∧ env.find? c₀.name = none ∧
      (∀ cv caps, c₀ ≠ .indInfo cv caps) ∧
      (∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) ∧
      (∀ cv nP nF, c₀ ≠ .ctorInfo cv nP nF) ∧ (∀ tbl, c₀ ≠ .projInfo tbl)

/-- **The model WITH ITS BLOCKS survives a non-inductive stage** — the
maintenance shape of every value-kind stage of the fold: the
`EnvModelM` the stage already produces, plus the agreement of its
carrier with the old one at the stored names, give the `blocks` field
back. -/
noncomputable def EnvModelB.ofNonIndStep {env env₂ : Env}
    (mb : EnvModelB V μ env) (m' : EnvModelM V μ env₂)
    (hstep : NonIndStep env env₂)
    (hag : AcvalAgrees mb.base2 m'.base2) :
    EnvModelB V μ env₂ where
  toEnvModelM := m'
  blocks := by
    rcases hstep with rfl | ⟨c₀, rfl, hfresh, hi, hr, hc, ht⟩
    · exact EnvBlockModels.crossSame hag mb.blocks
    · exact EnvBlockModels.crossCons hfresh ⟨hi, hr, hc⟩ ht hag mb.blocks

end ConLeche.Model
