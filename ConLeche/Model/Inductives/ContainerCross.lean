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
  namesLen := C.namesLen
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
  pinψ := fun q hq cvT caps hf => by
    obtain ⟨cvT', cvR', mI', rP', rules', h0⟩ := C.reps 0 hk
    obtain ⟨cv, caps', hf₁⟩ := h0.pinsFound q hq
    have hf₂ := hF _ (.indInfo cv caps') (fun _ _ _ _ h => nomatch h) hf₁
    have he := ConLeche.ConstantInfo.indInfo.inj (Option.some.inj (hf.symm.trans hf₂))
    rw [he.1]
    exact C.pinψ q hq cv caps' hf₁

/-! ## The pins' laws and shapes across the change -/

/-- **A stored block's pins' shapes cross an environment change**: the
shapes read the carrier only at the block's members, its pins'
containers and the containers' own pins' containers — all stored at
the old environment — and the pins' containers' groups are read the
same at the new one (`hci`). -/
theorem PinShapes.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V} {d : BlockModel V} {pc : Nat → PinCtors V}
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hk : 0 < d.k) (hd : IsBlockModels m₁ d)
    (hB : ∀ q, q < d.nPins → ∀ ci : ContainerInfo,
      ConLeche.containerInfo? env₁ (d.pinAt q).J = some ci → IsBlockModels m₁ (B ci))
    (hci : ∀ q, q < d.nPins → ∀ ci : ContainerInfo,
      ConLeche.containerInfo? env₁ (d.pinAt q).J = some ci →
      ConLeche.containerInfo? env₂ (d.pinAt q).J = some ci)
    (h : PinShapes m₁ B d pc) : PinShapes m₂ B d pc := by
  intro q hq
  obtain ⟨q₀, kJ, i, ci, hqe, hi, hcont, hgv, hsh⟩ := h q hq
  refine ⟨q₀, kJ, i, ci, hqe, hi, hci q hq ci hcont, hgv, fun ψ ρp hρp i' j hi' hj cvT₂ caps₂ hf₂ => ?_⟩
  obtain ⟨cvT, cvR, mI, rP, rules, h0⟩ := hd 0 hk
  -- the pin's container at the new environment is the one at the old
  obtain ⟨cv₁, caps₁, hf₁⟩ := h0.pinsFound (q₀ + i') (by
    have := hgv.seg; omega)
  have he := ConLeche.ConstantInfo.indInfo.inj
    (Option.some.inj (hf₂.symm.trans (hF _ (.indInfo cv₁ caps₁) (fun _ _ _ _ h => nomatch h) hf₁)))
  rw [he.1]
  have hmem : ∀ t, t < d.k →
      m₂.acval (d.memberNames.getD t .anonymous) ψ = m₁.acval (d.memberNames.getD t .anonymous) ψ := by
    intro t ht
    obtain ⟨cv, caps, hf⟩ := h0.memsFound t ht
    exact congrFun (hag (d.memberNames.getD t .anonymous)
      (by rw [show d.memberNames.getD t .anonymous = d.memberName t from rfl, hf]; rfl)) ψ
  have hpin : ∀ q', q' < d.pins.length →
      m₂.acval (d.pins.getD q' default).J ((d.pins.getD q' default).ψJ ψ)
        = m₁.acval (d.pins.getD q' default).J ((d.pins.getD q' default).ψJ ψ) := by
    intro q' hq'
    obtain ⟨cv, caps, hf⟩ := h0.pinsFound q' hq'
    exact congrFun (hag (d.pins.getD q' default).J
      (by rw [show d.pins.getD q' default = d.pinAt q' from rfl, hf]; rfl)) _
  have hBci := hB q hq ci hcont
  have hac : ∀ qK, qK < (B ci).nPins →
      m₂.acval ((B ci).pinAt qK).J (((B ci).pinAt qK).ψJ ((d.pinAt q₀).ψJ ψ))
        = m₁.acval ((B ci).pinAt qK).J (((B ci).pinAt qK).ψJ ((d.pinAt q₀).ψJ ψ)) := by
    intro qK hqK
    obtain ⟨cvT', cvR', mI', rP', rules', hI'⟩ := hBci i' (hgv.kEq ▸ hi')
    obtain ⟨cv, caps, hf⟩ := hI'.pinsFound qK hqK
    exact congrFun (hag _ (by rw [hf]; rfl)) _
  exact CopyCtorShape.of_EA (TV := d.targetView m₁.acval ψ)
    (targetRead m₂.acval d.memberNames d.pins d.nP d.k ψ) (targetRead_congr hmem hpin) hac
    (hBci.tgt_pin_lt (hgv.kEq ▸ hi') (List.getElem?_eq_getElem hj))
    (hsh ψ ρp hρp i' j hi' hj cv₁ caps₁ hf₁)

/-- **A container group's obligation crosses an environment change**
(the block model by `ContainerModeled.crossEnv`, the pins' laws
model-free, the shapes by `PinShapes.crossEnv`), given the pins'
containers' groups at the old environment and their reading at the
new one. -/
theorem BlockAt.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V} {ci : ContainerInfo}
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hk : 0 < (B ci).k)
    (hB : ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env₁ ((B ci).pinAt q).J = some ci' → IsBlockModels m₁ (B ci'))
    (hci : ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env₁ ((B ci).pinAt q).J = some ci' →
      ConLeche.containerInfo? env₂ ((B ci).pinAt q).J = some ci')
    (h : BlockAt m₁ B ci) : BlockAt m₂ B ci := by
  obtain ⟨C, pc, hL, hS⟩ := h
  exact ⟨C.crossEnv hF hres hag hde hk, pc, hL.cross, hS.crossEnv hF hag hk C.reps hB hci⟩

/-! ## The field across an extension -/

/-- **The pins' containers' groups of a stored block are stored**: at
an assignment carrying every group, a container's pin's container reads
a group whose model is `IsBlockModels`. -/
theorem EnvBlocksOf.pinGroups {env : Env} {m : EnvModel V env} {B : ContainerInfo → BlockModel V}
    (hb : EnvBlocksOf m B) {ci : ContainerInfo} :
    ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env ((B ci).pinAt q).J = some ci' → IsBlockModels m (B ci') :=
  fun _ _ ci' hci' => (hb _ ci' hci').1.reps

/-- **The blocks survive a change of carrier at the SAME environment**:
the reading does not move at all, and every obligation crosses on the
agreement alone. -/
theorem EnvBlocksOf.crossSame {env : Env} {m₁ m₂ : EnvModel V env}
    {B : ContainerInfo → BlockModel V} (hag : AcvalAgrees m₁ m₂) (hb : EnvBlocksOf m₁ B) :
    EnvBlocksOf m₂ B := by
  intro J ci hci
  refine (hb J ci hci).crossEnv (fun _ _ _ hf => hf) (fun _ h => h) hag ?_
    ((hb J ci hci).1.k ▸ containerInfo?_members_pos hci) hb.pinGroups (fun _ _ _ h => h)
  intro ψ dp e ea hd
  rw [denoteMeta_acval_congr (acval₁ := m₂.acval) (acval₂ := m₁.acval) hag dp e]
  exact hd

theorem EnvBlockModels.crossSame {env : Env} {m₁ m₂ : EnvModel V env}
    (hag : AcvalAgrees m₁ m₂) (hb : EnvBlockModels m₁) : EnvBlockModels m₂ := by
  obtain ⟨B, hB⟩ := hb
  exact ⟨B, hB.crossSame hag⟩

/-- **The blocks survive a non-inductive fresh cons**: the reading does
not move (`containerInfo?_cons_nonInd`) and every obligation crosses.
The only model-facing input is the carriers' AGREEMENT at the stored
names: `denoteMeta` consults the valuation only at names it found, so
the reading transport `hde` follows from it
(`denoteMeta_acval_congr` then `denoteMeta_env_mono`). -/
theorem EnvBlocksOf.crossCons {env : Env} {m₁ : EnvModel V env} {c₀ : ConstantInfo}
    {m₂ : EnvModel V ⟨c₀ :: env.consts⟩} {B : ContainerInfo → BlockModel V}
    (hfresh : env.find? c₀.name = none)
    (hkind : (∀ cv caps, c₀ ≠ .indInfo cv caps) ∧
      (∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) ∧
      (∀ cv nP nF, c₀ ≠ .ctorInfo cv nP nF))
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl)
    (hag : AcvalAgrees m₁ m₂)
    (hb : EnvBlocksOf m₁ B) : EnvBlocksOf m₂ B := by
  intro J ci hci
  rw [ConLeche.containerInfo?_cons_nonInd hfresh hkind] at hci
  refine (hb J ci hci).crossEnv (fun n c _ hf => Env.find?_cons_of_fresh hfresh hf)
    (constsResolve_of_findPreserved (findPreserved_cons hfresh)) hag ?_
    ((hb J ci hci).1.k ▸ containerInfo?_members_pos hci) hb.pinGroups
    (fun q _ ci' h => by rw [ConLeche.containerInfo?_cons_nonInd hfresh hkind]; exact h)
  intro ψ dp e ea hd
  refine denoteMeta_env_mono (findPreserved_cons hfresh) (litGuardsMono_cons hfresh)
    (findProj?_cons_of_base_none hntc) dp e ?_
  rw [denoteMeta_acval_congr (acval₁ := m₂.acval) (acval₂ := m₁.acval) hag dp e]
  exact hd

theorem EnvBlockModels.crossCons {env : Env} {m₁ : EnvModel V env} {c₀ : ConstantInfo}
    {m₂ : EnvModel V ⟨c₀ :: env.consts⟩}
    (hfresh : env.find? c₀.name = none)
    (hkind : (∀ cv caps, c₀ ≠ .indInfo cv caps) ∧
      (∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) ∧
      (∀ cv nP nF, c₀ ≠ .ctorInfo cv nP nF))
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl)
    (hag : AcvalAgrees m₁ m₂)
    (hb : EnvBlockModels m₁) : EnvBlockModels m₂ := by
  obtain ⟨B, hB⟩ := hb
  exact ⟨B, hB.crossCons hfresh hkind hntc hag⟩

/-- **The blocks survive an inductive extension, modulo the new block's
own containers**: an OLD container's block is read the same at the
extended environment (`containerInfo?_ext_ind_eq`) and its obligation
crosses at an assignment `B'` agreeing with the old one at the old
groups (`hold`); the containers the extension itself creates are the
installing route's obligation at `B'`, `hnew`. -/
theorem EnvBlocksOf.crossInd {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {N : List Name} {B B' : ContainerInfo → BlockModel V}
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
    (hold : ∀ (J : Name) (ci : ContainerInfo), J ∉ N →
      ConLeche.containerInfo? env₁ J = some ci → B' ci = B ci)
    (hb : EnvBlocksOf m₁ B)
    (hnew : ∀ J ∈ N, ∀ ci : ContainerInfo, ConLeche.containerInfo? env₂ J = some ci →
      BlockAt m₂ B' ci) :
    EnvBlocksOf m₂ B' := by
  -- a name stored at the old environment is not a new one
  have hstored : ∀ n : Name, (env₁.find? n).isSome = true → n ∉ N := by
    intro n hn hmem
    rw [hfreshN n hmem] at hn
    exact nomatch hn
  intro J ci hci
  by_cases hJ : J ∈ N
  · exact hnew J hJ ci hci
  · have h₁ := ConLeche.containerInfo?_ext_ind hext hnewN hfreshN hrecN hwf hrc hJ hci
    have hB := hb J ci h₁
    -- the pins' containers of an old block are old, and read the same
    have hpc : ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
        ConLeche.containerInfo? env₁ ((B ci).pinAt q).J = some ci' →
        ((B ci).pinAt q).J ∉ N ∧ ConLeche.containerInfo? env₂ ((B ci).pinAt q).J = some ci' := by
      intro q hq ci' hci'
      obtain ⟨cv, caps, hf⟩ := containerInfo?_found hci'
      have hnot : ((B ci).pinAt q).J ∉ N := hstored _ (by rw [hf]; rfl)
      refine ⟨hnot, ?_⟩
      rw [ConLeche.containerInfo?_ext_ind_eq hext hnewN hfreshN hrecN hwf hrc hnot]
      exact hci'
    obtain ⟨C, pc, hL, hS⟩ := hB.crossEnv hF hres hag hde (hB.1.k ▸ containerInfo?_members_pos h₁)
      hb.pinGroups (fun q hq ci' hci' => (hpc q hq ci' hci').2)
    have hBci : B' ci = B ci := hold J ci hJ h₁
    refine ⟨by rw [hBci]; exact C, pc, by rw [hBci]; exact hL, ?_⟩
    rw [hBci]
    refine hS.congrB fun q hq ci' hci' => ?_
    -- `ci'` is the old reading of the pin's container
    obtain ⟨q₀, kJ, i, ci₁, -, -, hci₁, -, -⟩ := hB.2.choose_spec.2 q hq
    obtain ⟨hnot, hci₂⟩ := hpc q hq ci₁ hci₁
    obtain rfl : ci' = ci₁ := Option.some.inj (hci'.symm.trans hci₂)
    exact hold _ ci' hnot hci₁

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
    (hnew : ∀ B : ContainerInfo → BlockModel V, EnvBlocksOf m₁ B →
      ∃ B' : ContainerInfo → BlockModel V,
        (∀ (J : Name) (ci : ContainerInfo), J ∉ N →
          ConLeche.containerInfo? env₁ J = some ci → B' ci = B ci) ∧
        ∀ J ∈ N, ∀ ci : ContainerInfo, ConLeche.containerInfo? env₂ J = some ci →
          BlockAt m₂ B' ci) :
    EnvBlockModels m₂ := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨B', hold, hnew'⟩ := hnew B hB
  exact ⟨B', hB.crossInd hext hnewN hfreshN hrecN hwf hrc hF hres hag hde hold hnew'⟩

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
