module

public import ConLeche.Model.Inductives.NestedPremise
public import ConLeche.Model.Inductives.BlockRepCross
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

**The reading hypothesis `hde` is too strong for the INDUCTIVE routes**
(task #315 M7-3 session 2, DESIGN §U.40): every inductive route ends by
consing the projection tables of its structure-like members, and a
table cons MOVES a successful reading — `denoteMeta` reads `.proj sn i`
through the table when there is one and through the pair decoder when
there is none.  `denoteMeta_not_mono_of_newTable` and
`hde_not_of_newTable` are that refutation, in the tree, with the shape
of the weaker hypothesis that replaces it (the readings guarded by the
subjects' proj-freedom at the newly tabled structures, which the block
model's own `BlockOpened` clauses already record).  The VALUE kinds are
unaffected: `crossCons` excludes a projection table by `hntc`.

`ContainerModeled.of_readBack` is the other half the routes need —
K.34's Bool, inverted: the block just installed reads back as its own
`ContainerInfo`, so the record's four data clauses are the block's own
data.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
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
theorem ContainerModeled.crossEnvP {Ts : List Name} {env₁ env₂ : Env}
    {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {ci : ContainerInfo} {d : BlockModel V}
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hfresh : ∀ T ∈ Ts, env₁.find? T = none)
    (hnpMem : ∀ M ∈ ci.members, ProjFree Ts M.type)
    (hk : 0 < d.k) (C : ContainerModeled m₁ ci d) : ContainerModeled m₂ ci d := by
  -- the member clause crosses at the STORED constant, whose type is
  -- guarded; `IsBlockModels` is then READ OFF it (the `member` clause
  -- is the stronger one — DESIGN §U.31 (e) 2)
  have hmemCross : ∀ (i : Nat) (M : ConLeche.ContainerMember), ci.members[i]? = some M →
      d.memberName i = M.name ∧ (d.ctorsM i).map (·.1.name) = M.ctors.map (·.name) ∧
      ∃ (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
        IsBlockModel m₂ M.name ⟨M.name, M.lps, M.type⟩ cvR mI rP rules d i := by
    intro i M hM
    obtain ⟨hname, hctors, cvR, mI, rP, rules, hI⟩ := C.member i M hM
    exact ⟨hname, hctors, cvR, mI, rP, rules,
      hI.crossEnvP hF hres hag hde hfresh (hnpMem M (List.mem_of_getElem? hM))⟩
  have hreps₂ : IsBlockModels m₂ d := by
    intro mm hmm
    obtain ⟨M, hM⟩ : ∃ M, ci.members[mm]? = some M :=
      ⟨_, List.getElem?_eq_getElem (by rw [← C.k]; exact hmm)⟩
    obtain ⟨hname, -, cvR, mI, rP, rules, hI⟩ := hmemCross mm M hM
    exact ⟨⟨M.name, M.lps, M.type⟩, cvR, mI, rP, rules, by rw [hname]; exact hI⟩
  exact
    { k := C.k
      namesLen := C.namesLen
      nP := C.nP
      reps := hreps₂
      typed := fun ψ =>
        ⟨(C.typed ψ).1.crossEnv hag C.reps, (C.typed ψ).2.1.crossEnv hag C.reps,
          (C.typed ψ).2.2.crossEnv hag C.reps hk⟩
      inj := C.inj
      member := hmemCross
      frame := C.frame
      ordFree := C.ordFree
      nestMention := C.nestMention
      pinsNotMembers := C.pinsNotMembers
      pinNP := C.pinNP
      pinψ := fun q hq cvT caps hf => by
        obtain ⟨cvT', cvR', mI', rP', rules', h0⟩ := C.reps 0 hk
        obtain ⟨cv, caps', hf₁⟩ := h0.pinsFound q hq
        have hf₂ := hF _ (.indInfo cv caps') (fun _ _ _ _ h => nomatch h) hf₁
        have he := ConLeche.ConstantInfo.indInfo.inj (Option.some.inj (hf.symm.trans hf₂))
        rw [he.1]
        exact C.pinψ q hq cv caps' hf₁ }

/-- **A container's block model crosses an environment change**: the
unguarded crossing (`Ts := []`), for an extension that installs no
projection table — the value kinds' shape.  An INDUCTIVE extension
takes `crossEnvP`. -/
theorem ContainerModeled.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {ci : ContainerInfo} {d : BlockModel V}
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hk : 0 < d.k) (C : ContainerModeled m₁ ci d) : ContainerModeled m₂ ci d :=
  C.crossEnvP (Ts := []) hF hres hag (fun ψ dp e _ {_ea} hr => hde ψ dp e hr)
    (fun _ hT => nomatch hT) (fun M _ => ProjFree.nil M.type) hk

/-- **A stored container's member types are guarded at names the
environment does not carry**: `containerInfo?` returns the members'
STORED types (`containerInfo?_inv`), those resolve (`EnvWF`), and a
resolving expression has no projection at an unstored structure
(`ProjFree.of_constsResolve`).  This is what lets an OLD container's
block model cross an INDUCTIVE extension: the block being installed is
fresh, so its projection tables are at structures no old subject
mentions. -/
theorem projFree_members {Ts : List Name} {env : Env} (m : EnvModel V env)
    (hfresh : ∀ T ∈ Ts, env.find? T = none) {J : Name} {ci : ContainerInfo}
    (hci : ConLeche.containerInfo? env J = some ci) :
    ∀ M ∈ ci.members, ProjFree Ts M.type := by
  intro M hM
  obtain ⟨cvT, caps, cvR, mI, rP, rules, H⟩ := ConLeche.containerInfo?_inv hci
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hfind, -, -, htype, -⟩ := H.2.2.2.2 M hM
  rw [htype]
  exact ProjFree.of_constsResolve hfresh
    (m.wf _ (ConLeche.Semantics.Env.find?_mem hfind)).2.2.1

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

/-- **A container group's obligation crosses an INDUCTIVE extension**
(task #315 M7-3 session 3): `ContainerModeled.crossEnvP` for the block
model, the pins' laws model-free, `PinShapes.crossEnv` for the shapes —
with the readings guarded at the structures the extension tables
(`hde`, `hfresh`) rather than asked of every expression. -/
theorem BlockAt.crossEnvP {Ts : List Name} {env₁ env₂ : Env}
    {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V} {ci : ContainerInfo}
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hfresh : ∀ T ∈ Ts, env₁.find? T = none)
    (hnpMem : ∀ M ∈ ci.members, ProjFree Ts M.type)
    (hk : 0 < (B ci).k)
    (hB : ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env₁ ((B ci).pinAt q).J = some ci' → IsBlockModels m₁ (B ci'))
    (hci : ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env₁ ((B ci).pinAt q).J = some ci' →
      ConLeche.containerInfo? env₂ ((B ci).pinAt q).J = some ci')
    (h : BlockAt m₁ B ci) : BlockAt m₂ B ci := by
  obtain ⟨C, pc, hL, hS⟩ := h
  exact ⟨C.crossEnvP hF hres hag hde hfresh hnpMem hk, pc, hL.cross,
    hS.crossEnv hF hag hk C.reps hB hci⟩

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
installing route's obligation at `B'`, `hnew`.  The readings cross
under the GUARD (task #315 M7-3 session 3): the extension's new
projection tables are at structures fresh in `env₁` (`hfresh`), and an
old container's subjects are its members' STORED types, which resolve
there (`projFree_members`). -/
theorem EnvBlocksOf.crossIndP {Ts : List Name} {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
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
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hfresh : ∀ T ∈ Ts, env₁.find? T = none)
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
    obtain ⟨C, pc, hL, hS⟩ := hB.crossEnvP hF hres hag hde hfresh
      (projFree_members m₁ hfresh h₁) (hB.1.k ▸ containerInfo?_members_pos h₁)
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

/-- `EnvBlocksOf.crossIndP` at an extension that installs NO projection
table (`Ts := []`), where the readings cross unguarded. -/
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

/-- **The field survives an inductive extension** (the guarded form):
`EnvBlocksOf.crossIndP` with the assignment quantified. -/
theorem EnvBlockModels.crossIndP {Ts : List Name} {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
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
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hfresh : ∀ T ∈ Ts, env₁.find? T = none)
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
  exact ⟨B', hB.crossIndP hext hnewN hfreshN hrecN hwf hrc hF hres hag hde hfresh hold hnew'⟩

/-- `EnvBlockModels.crossIndP` at `Ts := []`. -/
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

/-! ## What the crossing cannot be asked across a projection table -/

/-- Every TOWER reading of a field is headed by `fst`
(`projAV k e = .fst (.snd^[k] e)`). -/
theorem projAV_head_fst : ∀ (k : Nat) (e : AnnotTerm), ∃ x, projAV k e = .fst x
  | 0, e => ⟨e, rfl⟩
  | k + 1, e => projAV_head_fst k (.snd e)

/-- **A NEW PROJECTION TABLE MOVES THE READING** (task #315 M7-3
session 2, DESIGN §U.40).  `denoteMeta` reads `.proj sn i e` through
the environment's table when there is one (`projAV`, headed by `fst`)
and through the PAIR decoder when there is none (`projPair?`, which at
`i = 1` is `snd`).  So an extension that adds a table at a structure
whose slot `1` was untabled changes a SUCCESSFUL reading — the two
readings of `.proj sn 1 (.sort .zero)` differ in their head former.

This is the exact hypothesis `ContainerModeled.crossEnv` and
`EnvBlocksOf.crossInd` take as `hde`, and it is why no install route
can discharge it as it stands: every route ends by consing the
projection tables of its structure-like members
(`checkNativeTable`/`mutualTables`/`nestedTables`), and a structure
with two or more fields has a slot `1`. -/
theorem denoteMeta_not_mono_of_newTable {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm}
    {env₁ env₂ : Env} {ψ : Name → Nat} {dp : Nat} {sn : Name} {entry : ConLeche.ProjEntry}
    (h₁ : env₁.findProj? sn 1 = none) (h₂ : env₂.findProj? sn 1 = some entry) :
    ∃ (e : Expr) (ea : AnnotTerm),
      denoteMeta acval₁ env₁ ψ dp e = some ea ∧ denoteMeta acval₂ env₂ ψ dp e ≠ some ea := by
  refine ⟨.proj sn 1 (.sort .zero), .snd (.sort (Level.zero.eval ψ)), ?_, ?_⟩
  · simp only [denoteMeta, h₁, bind, Option.bind]
    rfl
  · simp only [denoteMeta, h₂, bind, Option.bind]
    intro hh
    obtain ⟨x, hx⟩ := projAV_head_fst (1 + entry.off) (.sort (Level.zero.eval ψ))
    rw [hx] at hh
    exact nomatch (Option.some.inj hh)

/-- **The crossing's reading hypothesis is REFUTABLE across a table
cons**: `ContainerModeled.crossEnv`'s `hde` (and with it
`BlockAt.crossEnv`, `EnvBlocksOf.crossInd`) asks for EVERY expression's
reading to survive, which an extension installing a projection table
does not grant.  The fix is not a stronger route fact but a WEAKER
hypothesis — the readings guarded by the subjects' resolution at the
block's own pre-block environment (`BlockOpened`'s `ord`/`recF`/
`reflF`/`nestF` clauses already record it, and a block's members are
fresh there, so `noProjAt_of_constsResolve` applies) — DESIGN §U.40. -/
theorem hde_not_of_newTable {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {sn : Name} {entry : ConLeche.ProjEntry}
    (h₁ : env₁.findProj? sn 1 = none) (h₂ : env₂.findProj? sn 1 = some entry) :
    ¬ (∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
        denoteMeta m₁.acval env₁ ψ dp e = some ea →
        denoteMeta m₂.acval env₂ ψ dp e = some ea) := by
  intro h
  obtain ⟨e, ea, h1, h2⟩ :=
    denoteMeta_not_mono_of_newTable (acval₁ := m₁.acval) (acval₂ := m₂.acval)
      (ψ := fun _ => 0) (dp := 0) h₁ h₂
  exact h2 (h _ _ e h1)

/-! ## The route's own read-back (task #315 K.34) -/

/-- Structural equality on the container data is an equality: every
field is a `Name`, an `Expr`, a `Nat` or a list of those, and all of
those are `LawfulBEq`.  The three instances are what makes K.34's
Bool — `containerInfo? envOut M.name == some want` — readable as the
EQUATION `EnvBlocksOf` is quantified over. -/
instance : LawfulBEq ConLeche.ContainerCtor where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp only [BEq.beq, ConLeche.instBEqContainerCtor.beq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [ConLeche.ContainerCtor.mk.injEq]
    exact ⟨eq_of_beq h1, eq_of_beq h2, of_decide_eq_true h3⟩
  rfl {a} := by
    cases a
    simp only [BEq.beq, ConLeche.instBEqContainerCtor.beq, Bool.and_eq_true]
    exact ⟨beq_self_eq_true (α := Name) _, beq_self_eq_true (α := Expr) _, by simp⟩

@[inherit_doc instLawfulBEqContainerCtor]
instance : LawfulBEq ConLeche.ContainerMember where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp only [BEq.beq, ConLeche.instBEqContainerMember.beq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [ConLeche.ContainerMember.mk.injEq]
    exact ⟨eq_of_beq h1, eq_of_beq h2, eq_of_beq h3, eq_of_beq h4⟩
  rfl {a} := by
    cases a
    simp only [BEq.beq, ConLeche.instBEqContainerMember.beq, Bool.and_eq_true]
    exact ⟨beq_self_eq_true (α := Name) _, beq_self_eq_true (α := List Name) _,
      beq_self_eq_true (α := Expr) _,
      beq_self_eq_true (α := List ConLeche.ContainerCtor) _⟩

@[inherit_doc instLawfulBEqContainerCtor]
instance : LawfulBEq ContainerInfo where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp only [BEq.beq, ConLeche.instBEqContainerInfo.beq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    simp only [ConLeche.ContainerInfo.mk.injEq]
    exact ⟨of_decide_eq_true h1, eq_of_beq h2⟩
  rfl {a} := by
    cases a
    simp only [BEq.beq, ConLeche.instBEqContainerInfo.beq, Bool.and_eq_true]
    exact ⟨by simp, beq_self_eq_true (α := List ConLeche.ContainerMember) _⟩

/-- **THE READ-BACK, INVERTED** (task #315 K.34, DESIGN §U.31 (d)): the
route's own Bool says that `containerInfo?` of the environment it
produced reads, AT EVERY MEMBER of the block it installed, exactly the
block's own data — so at member `i` the reading is
`blockContainerInfo`, which is the `ContainerInfo` the field
`EnvBlocksOf` is quantified over asks about. -/
theorem containerInfo?_of_readBack {envOut : Env} {nP : Nat}
    {members : List (ConstantVal × List (ConstantVal × Nat))}
    (h : ConLeche.blockReadBackOk envOut nP members = true)
    {i : Nat} {c : ConstantVal × List (ConstantVal × Nat)} (hi : members[i]? = some c) :
    ConLeche.containerInfo? envOut c.1.name
      = some (ConLeche.blockContainerInfo nP members) := by
  unfold ConLeche.blockReadBackOk at h
  rw [List.all_eq_true] at h
  have hM : (⟨c.1.name, c.1.levelParams, c.1.type,
      c.2.map fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ : ConLeche.ContainerMember)
      ∈ (ConLeche.blockContainerInfo nP members).members :=
    List.mem_map_of_mem (List.mem_of_getElem? hi)
  exact eq_of_beq (h _ hM)

/-- **The block just installed IS its own container group** (task #315
K.34's inversion at the model tier): at the reading the route
certifies, `ContainerModeled`'s four DATA clauses — the member count,
the parameter count, the member names and the constructors' names —
are the block's own, so the record is the block model's ties to the
route's data (`hk`, `hnP`, `hnames`, `hctorNames`) together with the
model-facing facts the route already proves.  The member clause's
constant is the stored one on the nose: `blockContainerInfo` copies
the member's `ConstantVal` field by field.

What every route must still bring is the LAST argument, `hmember`:
`IsBlockModel` at the OUTPUT model.  Every route builds it at the
model of its RECURSORS' environment and then conses its projection
tables, and the block model does not cross that cons — DESIGN §U.40. -/
theorem ContainerModeled.of_readBack {env : Env} {m : EnvModel V env} {nP : Nat}
    {members : List (ConstantVal × List (ConstantVal × Nat))} {d : BlockModel V}
    (hk : d.k = members.length) (hnP : d.nP = nP)
    (hnamesLen : d.memberNames.length = d.k)
    (hnames : ∀ i, i < d.k → d.memberName i = (members.getD i default).1.name)
    (hctorNames : ∀ i, i < d.k →
      (d.ctorsM i).map (·.1.name) = (members.getD i default).2.map (·.1.name))
    (hreps : IsBlockModels m d)
    (htyped : ∀ ψ : Name → Nat, FormersTyped m d ψ ∧ CtorsTyped m d ψ ∧ PinsTyped m d ψ)
    (hinj : ∀ (ψ : Name → Nat) (mm' j : Nat) (fs : List V),
      d.inj ψ mm' j fs = injW (d.w ψ) j (mkTower (fs ++ [pt])))
    (hframe : ∀ i, i < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (d.params ψ).reverse ρ ↔ Sat V (((d.ppsM i ψ).take d.nP).map (·.2.2)).reverse ρ)
    (hordFree : ∀ (i j l : Nat) (x : Expr), i < d.k → j < (d.ctorsM i).length →
      (d.xFvsF i j)[l]? = some x → (d.ksF i j).getD l .ordinary = .ordinary →
      ConLeche.mentionsMember d.memberNames x.fvarTypeD = false)
    (hnestMention : ∀ q, q < d.nPins →
      ∃ e ∈ (d.pinAt q).DsE.take (d.pinAt q).nPJ,
        ConLeche.mentionsMember d.memberNames e = true)
    (hpinsNotMembers : ∀ q, q < d.nPins → (d.pinAt q).J ∉ d.memberNames)
    (hpinNP : ∀ q, q < d.nPins → ∃ ci' : ContainerInfo,
      ConLeche.containerInfo? d.env₀ (d.pinAt q).J = some ci' ∧ (d.pinAt q).nPJ = ci'.nP)
    (hpinψ : ∀ q, q < d.nPins → ∀ (cvT : ConstantVal) (caps : IndCaps),
      env.find? (d.pinAt q).J = some (.indInfo cvT caps) →
      (d.pinAt q).lvls.length = cvT.levelParams.length ∧
      ∀ ψ : Name → Nat, (d.pinAt q).ψJ ψ = Level.substFn ψ cvT.levelParams (d.pinAt q).lvls)
    (hmember : ∀ i, i < d.k → ∃ (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      IsBlockModel m (members.getD i default).1.name (members.getD i default).1 cvR mI rP rules
        d i) :
    ContainerModeled m (ConLeche.blockContainerInfo nP members) d where
  k := by rw [hk]; show _ = (members.map _).length; rw [List.length_map]
  namesLen := hnamesLen
  nP := hnP
  reps := hreps
  typed := htyped
  inj := fun _ => hinj
  frame := hframe
  ordFree := hordFree
  nestMention := hnestMention
  pinsNotMembers := hpinsNotMembers
  pinNP := hpinNP
  pinψ := hpinψ
  member := fun i M hM => by
    -- the `i`-th entry is the `i`-th member of the route's list
    have hMl : (members.map fun (cvT, cs) =>
        (⟨cvT.name, cvT.levelParams, cvT.type,
          cs.map fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ : ConLeche.ContainerMember))[i]?
        = some M := hM
    rw [List.getElem?_map] at hMl
    cases hc : members[i]? with
    | none => rw [hc] at hMl; exact nomatch hMl
    | some c =>
      rw [hc] at hMl
      obtain rfl : M = ⟨c.1.name, c.1.levelParams, c.1.type,
          c.2.map fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ := (Option.some.inj hMl).symm
      have hik : i < d.k := by
        rw [hk]; exact (List.getElem?_eq_some_iff.mp hc).1
      have hcD : members.getD i default = c := by
        rw [List.getD_eq_getElem?_getD, hc]; rfl
      refine ⟨by rw [hnames i hik, hcD], ?_, ?_⟩
      · rw [hctorNames i hik, hcD]
        show _ = (c.2.map _).map _
        rw [List.map_map]; rfl
      · obtain ⟨cvR, mI, rP, rules, hI⟩ := hmember i hik
        rw [hcD] at hI
        exact ⟨cvR, mI, rP, rules, hI⟩

/-! ## A block with no pins -/

/-- **A block with NO PINS carries its group's obligation as soon as
its `ContainerModeled` holds** (task #315 M7-3 session 6): at
`d.pins = []` every clause of `PinRecLaws` but `mkZero` is quantified
`q < d.nPins` and so vacuous, `mkZero` is the `Inhabited (PinCtors V)`
witness's own injection (`fun _ _ _ => pt`, which is `mkZero`), and
`PinShapes` is vacuous.  The mutual and native routes' blocks are of
this shape (`MutualBlockModelOf.pins`). -/
theorem BlockAt.of_noPins {env : Env} {m : EnvModel V env} {B : ContainerInfo → BlockModel V}
    {ci : ContainerInfo} (hc : ContainerModeled m ci (B ci)) (hp : (B ci).pins = []) :
    BlockAt m B ci := by
  have h0 : (B ci).nPins = 0 := by show (B ci).pins.length = 0; rw [hp]; rfl
  refine ⟨hc, fun _ => default, ?_, fun q hq => absurd hq (by rw [h0]; omega)⟩
  exact
    { tgtsLt := fun _ q _ _ hq => absurd hq (by rw [h0]; omega)
      idxOk := fun _ _ _ q hq => absurd hq (by rw [h0]; omega)
      fibre := fun _ _ _ _ _ _ q hq => absurd hq (by rw [h0]; omega)
      mkZero := fun _ _ _ _ _ => rfl
      mkInj := fun _ _ q hq => absurd hq (by rw [h0]; omega)
      injW := fun _ q hq => absurd hq (by rw [h0]; omega)
      ind := fun _ _ _ _ _ _ _ q hq => absurd hq (by rw [h0]; omega) }

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

/-- **A block model's members are determined by their NAMES** (task
#315 L-E, DESIGN §U.71 — the alignment's second half): a group's
member-name list is `Nodup` (`containerInfo?_inv`) and
`ContainerModeled.member` reads the block model's members off it
positionally, so two classes of one block model with one name are one
class.  What identifies the root's class with the block's pin group's
member once the two sides' containers are known to be the same. -/
theorem ContainerModeled.memberName_inj {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {d : BlockModel V} (h : ContainerModeled m ci d) {I : Name}
    (hci : ConLeche.containerInfo? env I = some ci) {a b : Nat} (ha : a < d.k) (hb : b < d.k)
    (hab : d.memberName a = d.memberName b) : a = b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hnodup, -⟩ := ConLeche.containerInfo?_inv hci
  have ha' : a < ci.members.length := by rw [← h.k]; exact ha
  have hb' : b < ci.members.length := by rw [← h.k]; exact hb
  have hA := (h.member a ci.members[a] (by rw [List.getElem?_eq_getElem ha'])).1
  have hB := (h.member b ci.members[b] (by rw [List.getElem?_eq_getElem hb'])).1
  have hlenA : a < (ci.members.map (·.name)).length := by rw [List.length_map]; exact ha'
  have hlenB : b < (ci.members.map (·.name)).length := by rw [List.length_map]; exact hb'
  refine (List.getElem_inj (h₀ := hlenA) (h₁ := hlenB) hnodup).mp ?_
  rw [List.getElem_map, List.getElem_map, ← hA, ← hB]
  exact hab


/-- **A group's members share their level parameters, so its data are a
congruence in the level assignment** (task #315 L-E, DESIGN §U.71 —
`classPin_of_views`' `hparK`): at a stored group, two assignments
agreeing on the group's OWN constant's level parameters give one index
universe (`IsBlockModel.uParams`) and one parameter-and-index telescope
(`FormerData.params`) at EVERY member — because `containerInfo?`
records every member's level parameters as the group's
(`containerInfo?_inv`) and `ContainerModeled.member` asserts the
member's `IsBlockModel` at exactly that record. -/
theorem ContainerModeled.params_congr {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {dK : BlockModel V} (h : ContainerModeled m ci dK) {I : Name}
    (hci : ConLeche.containerInfo? env I = some ci)
    {cvI : ConstantVal} {capsI : IndCaps} (hfI : env.find? I = some (.indInfo cvI capsI))
    {ψ₁ ψ₂ : Name → Nat} (hψ : ∀ p ∈ cvI.levelParams, ψ₁ p = ψ₂ p) {a : Nat} (ha : a < dK.k) :
    dK.uM a ψ₁ = dK.uM a ψ₂ ∧ dK.ppsM a ψ₁ = dK.ppsM a ψ₂ := by
  obtain ⟨cvT, _caps, _cvR0, _mI0, _rP0, _rules0, hfind, _hfr0, _hmem0, _hnd0, hall⟩ :=
    ConLeche.containerInfo?_inv hci
  have hcvT : cvT = cvI := (ConstantInfo.indInfo.inj (Option.some.inj (hfind.symm.trans hfI))).1
  have ha' : a < ci.members.length := by rw [← h.k]; exact ha
  have hmem : ci.members[a]? = some ci.members[a] := by rw [List.getElem?_eq_getElem ha']
  obtain ⟨-, -, cvR, mI, rP, rules, hI⟩ := h.member a ci.members[a] hmem
  obtain ⟨_cvC, _capsC, _cvRc, _mIc, _rulesC, _hf1, _hf2, hlps, _hf4, hshare, _hf6, _hf7⟩ :=
    hall ci.members[a] (List.getElem_mem ha')
  have hψ' : ∀ p ∈ (⟨ci.members[a].name, ci.members[a].lps, ci.members[a].type⟩
      : ConstantVal).levelParams, ψ₁ p = ψ₂ p := by
    intro p hp
    exact hψ p (by rw [← hcvT, ← hshare, ← hlps]; exact hp)
  exact ⟨hI.uParams a ha ψ₁ ψ₂ hψ', (hI.former.params ψ₁ ψ₂ hψ').1⟩


/-- **A group's members share their level parameters** (task #315 L-E,
DESIGN §U.73): `containerInfo?_inv` records every member's as the
group's own constant's, and `ContainerModeled.member` asserts the
member's `IsBlockModel` at that record — so a level agreement taken at
ONE member's constant is an agreement at EVERY member's.  What the WALK
needs when it steps from the pair's member to the field's target
member. -/
theorem ContainerModeled.memberLps {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {dK : BlockModel V} (h : ContainerModeled m ci dK) {I : Name}
    (hci : ConLeche.containerInfo? env I = some ci)
    {a b : Nat} (ha : a < dK.k) (hb : b < dK.k)
    {cvA cvB : ConstantVal} {capsA capsB : IndCaps}
    (hA : env.find? (dK.memberName a) = some (.indInfo cvA capsA))
    (hB : env.find? (dK.memberName b) = some (.indInfo cvB capsB)) :
    cvA.levelParams = cvB.levelParams := by
  obtain ⟨cvT, _caps, _cvR0, _mI0, _rP0, _rules0, _hfind, _hfr0, _hmem0, _hnd0, hall⟩ :=
    ConLeche.containerInfo?_inv hci
  have key : ∀ (x : Nat), x < dK.k → ∀ (cvX : ConstantVal) (capsX : IndCaps),
      env.find? (dK.memberName x) = some (.indInfo cvX capsX) → cvX.levelParams = cvT.levelParams := by
    intro x hx cvX capsX hX
    have hx' : x < ci.members.length := by rw [← h.k]; exact hx
    have hmem : ci.members[x]? = some ci.members[x] := by rw [List.getElem?_eq_getElem hx']
    have hname := (h.member x ci.members[x] hmem).1
    obtain ⟨cvC, _capsC, _cvRc, _mIc, _rulesC, hf1, _hf2, _hlps, _hf4, hshare, _hf6, _hf7⟩ :=
      hall ci.members[x] (List.getElem_mem hx')
    rw [hname] at hX
    obtain rfl : cvX = cvC := (ConstantInfo.indInfo.inj (Option.some.inj (hX.symm.trans hf1))).1
    exact hshare
  rw [key a ha cvA capsA hA, key b hb cvB capsB hB]


end ConLeche.Model
