module

import ConLeche.Model.Inductives.ContainerCross
public import ConLeche.Model.Inductives.BasisBlocksZero
import ConLeche.Verify.Inductives.NestedGroupInv
public section

/-!
# The basis step's shape for the `EnvModelB` flip (task #315, M7-4, DESIGN §U.45)

All five pinned basis blocks carry block models
(`BasisBlocksZero/Unit/Nat/Eq.lean`).  What the fold's basis step owes
at M8's flip is then one shape, and this module is it: the assignment
`B` grows by ONE group, the old containers travel by
`EnvBlocksOf.crossInd` (`ContainerCross.lean`, M7-3), and the new group
is the block's own `BlockAt`.

```
EnvBlocksOf m₁ B → <the block's run> → EnvBlocksOf m₂ (extendAt B ci₀ d₀)
```

The `hold` half of the crossing — the extended assignment agrees with
the old one at every OLD group — is discharged here once and for all,
from FRESHNESS: an old group's members are all stored at the old
environment (`containerInfo?_inv`), and the new block's are not.

What is NOT here, and is M8's: the basis runs' own crossing facts.
`declBasisPB_*` returns `Nonempty (EnvModelM V μ env₂)` — an anonymous
model — so there is nothing to state `EnvBlocksOf m₂ _` about until
those steps hand back a NAMED model with its agreement, exactly as the
value kinds did at §U.31 (c).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule ContainerInfo ContainerMember
  IndCaps)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The assignment, extended at one group -/

open Classical in
/-- **The assignment with one more group**: the block just installed at
its own group, every other group as before. -/
@[expose] noncomputable def extendAt (B : ContainerInfo → BlockModel V) (ci₀ : ContainerInfo)
    (d₀ : BlockModel V) : ContainerInfo → BlockModel V :=
  fun ci => if ci = ci₀ then d₀ else B ci

omit [SetTheory V] in
theorem extendAt_self (B : ContainerInfo → BlockModel V) (ci₀ : ContainerInfo)
    (d₀ : BlockModel V) : extendAt B ci₀ d₀ ci₀ = d₀ := by
  unfold extendAt; exact if_pos rfl

omit [SetTheory V] in
theorem extendAt_ne {B : ContainerInfo → BlockModel V} {ci₀ ci : ContainerInfo}
    {d₀ : BlockModel V} (h : ci ≠ ci₀) : extendAt B ci₀ d₀ ci = B ci := by
  unfold extendAt; exact if_neg h

/-! ## The step -/

/-- **A group whose members are not all stored is not an old group**:
`containerInfo?` reads only groups whose every member is a stored
inductive, so a group with a FRESH member is new. -/
theorem containerInfo?_ne_of_fresh {env : Env} {J : Name} {ci ci₀ : ContainerInfo}
    (hci : ConLeche.containerInfo? env J = some ci)
    (hfresh : ∃ M ∈ ci₀.members, env.find? M.name = none) : ci ≠ ci₀ := by
  rintro rfl
  obtain ⟨M, hM, hf⟩ := hfresh
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, -, -, -, hmem⟩ := ConLeche.containerInfo?_inv hci
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hfM, -⟩ := hmem M hM
  rw [hf] at hfM
  exact nomatch hfM

/-- **THE BASIS STEP'S SHAPE** (task #315 M7-4, DESIGN §U.45): the
blocks survive the install of ONE new group — the old containers by
`EnvBlocksOf.crossInd`, the new group by its own `BlockAt`, and the
`hold` half by the new block's freshness.

`hnewG` is how each pinned block discharges the new names: the former
reads back the group (its own `containerInfo?_*A` theorem), and every
other constant of the block — the constructors and the recursor — is
not an `indInfo`, so `containerInfo?` returns `none` at it. -/
theorem EnvBlocksOf.extendBasis {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {N : List Name} {B : ContainerInfo → BlockModel V} {ci₀ : ContainerInfo} {d₀ : BlockModel V}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnewN : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨ n ∈ N)
    (hfreshN : ∀ n ∈ N, env₁.find? n = none)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) → n.str "rec" ∈ N → n ∈ N)
    (hmimN : ∀ (n : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (Name.appendIndexAfter (n.str "rec") j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter (n.str "rec") j ∈ N → n ∈ N)
    (hwf : ConLeche.EnvWF env₁) (hrc : ConLeche.RecCtorsStored env₁)
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hfreshM : ∃ M ∈ ci₀.members, env₁.find? M.name = none)
    (hb : EnvBlocksOf m₁ B)
    (hnewG : ∀ J ∈ N, ∀ ci : ContainerInfo,
      ConLeche.containerInfo? env₂ J = some ci → ci = ci₀)
    (hAt : BlockAt m₂ (extendAt B ci₀ d₀) ci₀) :
    EnvBlocksOf m₂ (extendAt B ci₀ d₀) := by
  refine EnvBlocksOf.crossInd hext hnewN hfreshN hrecN hmimN hwf hrc hF hres hag hde ?_ hb ?_
  · exact fun J ci _ hci => extendAt_ne (containerInfo?_ne_of_fresh hci hfreshM)
  · intro J hJ ci hci
    rw [hnewG J hJ ci hci]
    exact hAt

/-- **A constant that is not a stored inductive reads no group**: the
shape every basis block's constructors and recursor discharge. -/
theorem containerInfo?_eq_none_of_not_ind {env : Env} {J : Name} {c : ConstantInfo}
    (hf : env.find? J = some c) (hnot : ∀ cv caps, c ≠ .indInfo cv caps) :
    ConLeche.containerInfo? env J = none := by
  cases hci : ConLeche.containerInfo? env J with
  | none => rfl
  | some ci =>
    obtain ⟨cv, caps, hf'⟩ := containerInfo?_found hci
    rw [hf] at hf'
    exact absurd (Option.some.inj hf') (hnot cv caps)

/-- **THE BASIS STEP'S SHAPE, at a block's own names**: `extendBasis`
with `hnewG` discharged the way every pinned block discharges it — the
FORMER reads the group back, and every other constant of the block is
not an `indInfo`, so `containerInfo?` reads nothing at it. -/
theorem EnvBlocksOf.extendBasisOf {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {N : List Name} {B : ContainerInfo → BlockModel V} {ci₀ : ContainerInfo} {d₀ : BlockModel V}
    {J₀ : Name}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnewN : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨ n ∈ N)
    (hfreshN : ∀ n ∈ N, env₁.find? n = none)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) → n.str "rec" ∈ N → n ∈ N)
    (hmimN : ∀ (n : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (Name.appendIndexAfter (n.str "rec") j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter (n.str "rec") j ∈ N → n ∈ N)
    (hwf : ConLeche.EnvWF env₁) (hrc : ConLeche.RecCtorsStored env₁)
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hfreshM : ∃ M ∈ ci₀.members, env₁.find? M.name = none)
    (hb : EnvBlocksOf m₁ B)
    (hread : ConLeche.containerInfo? env₂ J₀ = some ci₀)
    (hother : ∀ J ∈ N, J ≠ J₀ →
      ∃ c : ConstantInfo, env₂.find? J = some c ∧ ∀ cv caps, c ≠ .indInfo cv caps)
    (hAt : BlockAt m₂ (extendAt B ci₀ d₀) ci₀) :
    EnvBlocksOf m₂ (extendAt B ci₀ d₀) := by
  refine EnvBlocksOf.extendBasis hext hnewN hfreshN hrecN hmimN hwf hrc hF hres hag hde hfreshM hb
    (fun J hJ ci hci => ?_) hAt
  by_cases hJ₀ : J = J₀
  · subst hJ₀
    exact Option.some.inj (hci.symm.trans hread)
  · obtain ⟨c, hf, hnot⟩ := hother J hJ hJ₀
    rw [containerInfo?_eq_none_of_not_ind hf hnot] at hci
    exact nomatch hci

/-- **The step at `Empty`**, as the flip will read it: the block's two
names, its computed read-back, and its `BlockAt`.  The other four
pinned blocks instantiate `extendBasisOf` the same way (their
`containerInfo?_*A` and `*BlockAt` are in the sibling modules); what
none of them can supply yet is the run's own crossing facts, which is
M8's half. -/
theorem emptyBlocksStep {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnewN : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨ n ∈ [ConLeche.emptyName, ConLeche.emptyName.str "rec"])
    (hfreshN : ∀ n ∈ [ConLeche.emptyName, ConLeche.emptyName.str "rec"], env₁.find? n = none)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) →
      n.str "rec" ∈ [ConLeche.emptyName, ConLeche.emptyName.str "rec"] →
      n ∈ [ConLeche.emptyName, ConLeche.emptyName.str "rec"])
    (hmimN : ∀ (n : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (Name.appendIndexAfter (n.str "rec") j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter (n.str "rec") j ∈ [ConLeche.emptyName, ConLeche.emptyName.str "rec"] →
      n ∈ [ConLeche.emptyName, ConLeche.emptyName.str "rec"])
    (hwf : ConLeche.EnvWF env₁) (hrc : ConLeche.RecCtorsStored env₁)
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hb : EnvBlocksOf m₁ B)
    (hT : env₂.find? ConLeche.emptyName = some ConLeche.emptyA)
    (hR : env₂.find? (ConLeche.emptyName.str "rec") = some ConLeche.emptyRecA)
    (hmim : ConLeche.blockOwnMimicsOk env₂ ConLeche.emptyName 0 = true) :
    EnvBlocksOf m₂ (extendAt B
      ⟨0, [⟨ConLeche.emptyName, [], ConLeche.emptyA.toConstantVal.type, []⟩]⟩
      (zeroCtorBlock (V := V) ConLeche.emptyName (.succ .zero) ⟨[]⟩)) := by
  refine EnvBlocksOf.extendBasisOf (J₀ := ConLeche.emptyName) hext hnewN hfreshN hrecN hmimN hwf
    hrc hF hres hag hde ⟨_, List.mem_singleton.mpr rfl,
      hfreshN ConLeche.emptyName (List.mem_cons.mpr (Or.inl rfl))⟩ hb
    (containerInfo?_emptyA hT hR) (fun J hJ hne => ?_) ?_
  · rcases List.mem_cons.mp hJ with rfl | hJ'
    · exact absurd rfl hne
    · rcases List.mem_singleton.mp hJ' with rfl
      exact ⟨ConLeche.emptyRecA, hR, fun _ _ h => nomatch h⟩
  · exact emptyBlockAt hT hR hmim (extendAt_self _ _ _)

end ConLeche.Model

