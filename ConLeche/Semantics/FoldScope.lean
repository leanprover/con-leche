module

public import ConLeche.Verify.EnvExt.Fold
public import ConLeche.Semantics.Inductives.DeclBlock
public import ConLeche.Semantics.DeclRun
import ConLeche.Kernel.CheckDecl
public import ConLeche.Kernel.Inductives.FieldNf
import ConLeche.Verify.EnvExt.Telescope
import ConLeche.Verify.EnvExt.FieldNf
import ConLeche.Semantics.Bridge.Sound
import ConLeche.Verify.ExceptBind
import ConLeche.Semantics.Inductives.DeclBlockEta
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.EnvWF

@[expose] public section

/-!
# The fold's environment invariant for the member tie (PRIMREC, FOLDFACTS)

ENVEXT's consumer form (`Verify/EnvExt/Base.lean`) proves that a kernel
run on a term resolving in a base `B` answers the same at any two
environments that extend `B` without new in-scope names.  This file
supplies those two facts for the environments the declaration fold
builds, by induction over the install chain:

* `stepOk_checkDecl` — every accepted `checkDecl` step is a `StepOk`
  extension (`Verify/EnvExt/Fold.lean`): its conses are fresh at the
  step's base, and every name it adds is of the ordinary shape (the
  front door, `checkConstantVal`, rejects `Name.isProjFnShape`; the
  pinned basis names are ordinary) or the projection table of one of
  the block's own members (`checkStructProjTable` demands freshness);
* `stepOk_foldlM` — so is every accepted run of the fold, by
  transitivity;
* `stepOk_checkBlockInds` — and so is the formers' environment
  `env₁(H)` of a block `H` on top of its install environment `B`.

**The member tie** (`memberTie_targetFieldNorms`, `memberTie_nestTeleNf`,
`memberTie_whnf`, …):
for a block `H` installed at `B` with formers' environment `env₁(H)`,
and any `E` the fold reaches from `B` (`StepOk B E`:
`stepOk_declBlockRun` then `stepOk_foldlM`, composed with
`StepOk.trans`) extending `env₁(H)`, a success of a kernel run at `E` on
a term resolving in `B` — in particular the rec check's field telescopes
of `H`'s member-abstracted constructor fields — is its success at
`env₁(H)`.  `EnvWF B`, `RecCtorsStored B` and `NatOpGuards B` are the
fold carrier's own (`EnvModel.wf`/`EnvModel.rec_ctors`,
`natOpGuardLaw_of`).  No prelude hypothesis.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo Declaration
  BlockShape BlockParts MemberShape TargetMajor fueledOps checkDecl checkConstantVal
  consBlockInds consBlockCtors consBlockRecsT checkBlockInds checkBlockCtors)
open ConLeche.EnvExt

/-! ## The stages' names: fresh and of the ordinary shape -/

/-- The front door's two name facts. -/
theorem checkConstantVal_names {mode : CheckMode} {F : Nat} {env : Env} {cv cv' : ConstantVal}
    (h : checkConstantVal (fueledOps mode F) env cv = .ok cv') :
    cv'.name = cv.name ∧ env.find? cv.name = none ∧ cv.name.isProjFnShape = false ∧
      ConLeche.reservedBasisNames.contains cv.name = false := by
  obtain ⟨hf, hr, hs, -, -, -, _, _, _, -, -, -, -, -, heq⟩ := ConLeche.checkConstantVal_inv h
  exact ⟨by rw [heq], hf, hs, hr⟩

/-- **The formers**: every stored former and every member's name is
fresh at the base and of the ordinary shape. -/
theorem checkBlockInds_names {mode : CheckMode} {env envI : Env} {p : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, cvTas, p₁)) :
    (∀ cv ∈ cvTas, env.find? cv.name = none ∧ cv.name.isProjFnShape = false ∧
      ConLeche.reservedBasisNames.contains cv.name = false) ∧
    (∀ ms ∈ p₁.members, env.find? ms.cvT.name = none ∧ ms.cvT.name.isProjFnShape = false ∧
      ConLeche.reservedBasisNames.contains ms.cvT.name = false) := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, rfl, rfl, -, h0, hcvs, -⟩ :=
    ConLeche.checkBlockInds_shape h
  have hone : ∀ {ms : MemberShape} {cv : ConstantVal} {s : Level},
      ConLeche.checkBlockTele (fueledOps mode F) env p.nP ms = .ok (cv, s) →
      (env.find? cv.name = none ∧ cv.name.isProjFnShape = false ∧
        ConLeche.reservedBasisNames.contains cv.name = false) ∧
      (env.find? ms.cvT.name = none ∧ ms.cvT.name.isProjFnShape = false ∧
        ConLeche.reservedBasisNames.contains ms.cvT.name = false) := by
    intro ms cv s hh
    obtain ⟨cvT, hn, -, hcv, -⟩ := ConLeche.checkBlockTele_shape hh
    obtain ⟨he, hf, hs, hr⟩ := checkConstantVal_names hcv
    exact ⟨⟨by rw [he]; exact hf, by rw [he]; exact hs, by rw [he]; exact hr⟩,
      ⟨by rw [← hn]; exact hf, by rw [← hn]; exact hs, by rw [← hn]; exact hr⟩⟩
  obtain ⟨hlen, hall⟩ := ConLeche.checkBlockTeles_inv hcvs
  have hrest : ∀ i (hi : i < rest.length),
      ∃ q, cvs[i]? = some q ∧ ConLeche.checkBlockTele (fueledOps mode F) env p.nP rest[i] = .ok q :=
    fun i hi => hall i rest[i] (List.getElem?_eq_getElem hi)
  refine ⟨fun cv hcv => ?_, fun ms hms => ?_⟩
  · rcases List.mem_cons.mp hcv with rfl | hcv'
    · exact (hone h0).1
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcv'
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
      have hil : i < rest.length := by
        rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨q', hq', hrun⟩ := hrest i hil
      obtain rfl := Option.some.inj (hi.symm.trans hq')
      exact (hone hrun).1
  · simp only [BlockShape.withSort_members] at hms
    rw [hm] at hms
    rcases List.mem_cons.mp hms with rfl | hms'
    · exact (hone h0).2
    · obtain ⟨i, hil, rfl⟩ := List.getElem_of_mem hms'
      obtain ⟨q, -, hrun⟩ := hrest i hil
      exact (hone hrun).2

/-- **One member's constructors**: fresh at the loop's environment and
of the ordinary shape. -/
theorem checkSumCtors_names' {mode : CheckMode} {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal} {F : Nat}
    {cs ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (h : ConLeche.checkSumCtors (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
      cvTa cs = .ok (ctorsA, sortss)) :
    ∀ cA ∈ ctorsA, env.find? cA.1.name = none ∧ cA.1.name.isProjFnShape = false ∧
      ConLeche.reservedBasisNames.contains cA.1.name = false := by
  obtain ⟨hlen, -, hall⟩ := ConLeche.checkSumCtors_inv h
  intro cA hcA
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcA
  obtain ⟨-, _, -, hrun⟩ := hall j (cs[j]'(hlen ▸ hj)) (ctorsA[j])
    (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem hj)
  obtain ⟨⟨_, hccv⟩, -, -⟩ := ConLeche.checkSumCtor_shape hrun
  obtain ⟨he, hf, hs, hr⟩ := checkConstantVal_names hccv
  exact ⟨by rw [he]; exact hf, by rw [he]; exact hs, by rw [he]; exact hr⟩

/-- **Every member's constructors**. -/
theorem checkBlockCtors_names' {mode : CheckMode} {env₀ env : Env} {q : BlockShape} {F : Nat} :
    ∀ {l : List (MemberShape × ConstantVal)} {ctorsAs : List (List (ConstantVal × Nat))}
      {sortsss : List (List (List Level))},
      checkBlockCtors (fueledOps mode F) env₀ env q l = .ok (ctorsAs, sortsss) →
      ∀ ctorsA ∈ ctorsAs, ∀ cA ∈ ctorsA,
        env.find? cA.1.name = none ∧ cA.1.name.isProjFnShape = false ∧
          ConLeche.reservedBasisNames.contains cA.1.name = false
  | [], ctorsAs, sortsss, h => by
    simp only [checkBlockCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun _ h => nomatch h
  | (ms, cvTa) :: rest, ctorsAs, sortsss, h => by
    unfold checkBlockCtors at h
    obtain ⟨r, hr, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨ctorsA, sortss⟩ := r
    try simp only at h
    obtain ⟨r', hr', h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨restC, restS⟩ := r'
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro A hA cA hcA
    rcases List.mem_cons.mp hA with rfl | hA'
    · exact checkSumCtors_names' hr cA hcA
    · exact checkBlockCtors_names' hr' A hA' cA hcA

/-! ## The block install -/

/-- **The formers' environment of a block is a `StepOk` extension of
its install environment.** -/
theorem stepOk_checkBlockInds {mode : CheckMode} {F : Nat} {B env₁ : Env} {p : BlockParts}
    {isRec : Bool} {cvTas : List ConstantVal} {p₁ : BlockShape}
    (h : checkBlockInds (fueledOps mode F) B p isRec = .ok (env₁, cvTas, p₁)) :
    StepOk B env₁ := by
  obtain ⟨-, -, -, -, -, -, -, -, henv, -⟩ := ConLeche.checkBlockInds_shape h
  rw [henv]
  exact (StepOk.refl B).consBlockInds (checkBlockInds_names h).1

/-- **The uniform install is a `StepOk` extension.** -/
theorem stepOk_declBlockRun {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p₀ : BlockParts} (h : DeclBlockRun μ F env block p₀ env₂) :
    StepOk env env₂ := by
  obtain ⟨hndC, -, isRec, env₁, cvTas, p₁, p, ctorsAs, sortsss, kinds, nfs, nodes, isorts, rs,
    hInd, hp, hCtors, -, -, -, -, hRec, hTbl⟩ := h
  subst hp
  obtain ⟨_, _, _, _, _, -, -, hp₁, henv₁, -, -, -⟩ := ConLeche.checkBlockInds_shape hInd
  have hlenCv : cvTas.length = p₁.members.length := by
    rw [ConLeche.checkBlockInds_length hInd, hp₁]; rfl
  obtain ⟨hTn, hMn⟩ := checkBlockInds_names hInd
  -- the formers
  have h1 : StepOk env env₁ := stepOk_checkBlockInds hInd
  -- the constructors
  have hC := checkBlockCtors_names' hCtors
  have h2 : StepOk env (consBlockCtors p₁.nP ctorsAs env₁) :=
    h1.consBlockCtors fun A hA c hc =>
      ⟨h1.fresh (hC A hA c hc).1, (hC A hA c hc).2.1, (hC A hA c hc).2.2⟩
  -- the recursors
  obtain ⟨hnames₀, -⟩ := checkBlockCtors_names hCtors
  have hnames : ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
      = p₁.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) := by
    have hz : (p₁.members.zip cvTas).map Prod.fst = p₁.members :=
      List.map_fst_zip (Nat.le_of_eq hlenCv.symm)
    calc _ = ((p₁.members.zip cvTas).map Prod.fst).map
            (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) := by
          rw [hnames₀, List.map_map]; rfl
      _ = _ := by rw [hz]
  obtain ⟨R⟩ := ConLeche.targetRecCheck_run
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hRec))
  have hS := ConLeche.recStage_of_targetG R (ConLeche.ctorsLen_of_names hnames)
  have h3 : StepOk env (consBlockRecsT (consBlockCtors p₁.nP ctorsAs env₁).find?
      (·.constsResolve (consBlockCtors p₁.nP ctorsAs env₁)) p₁ 0 rs
      (consBlockCtors p₁.nP ctorsAs env₁)) := by
    refine h2.consBlockRecsT fun o ho => ?_
    have hmem : (o.1, o.2.2, o.2.1.nIdx, o.2.1.ctors) ∈ ConLeche.tgtRs rs :=
      List.mem_map_of_mem ho
    obtain ⟨hf, hr, hs, -⟩ := ConLeche.recStage_cvFacts hS _ hmem
    exact ⟨h2.fresh hf, hs, hr⟩
  -- the tables
  refine h3.checkBlockTables (fun x hx => ?_) hTbl
  exact hMn x.1 (List.of_mem_zip hx).1

/-! ## The pinned basis install -/

/-- The pinned declarations' names are of the ordinary shape. -/
theorem basisDecls_shape (kind : ConLeche.BasisKind) :
    ∀ ci ∈ kind.declsA, ci.name.isProjFnShape = false := by
  cases kind <;> decide

/-- A pinned block holding one of the `Nat` trio holds all three, and
one holding `PUnit.rec` holds `PUnit`. -/
theorem basisDecls_mates (kind : ConLeche.BasisKind) :
    (∀ ci ∈ kind.declsA, ci.name ∈ natLitNames →
      ∀ m ∈ natLitNames, ∃ c' ∈ kind.declsA, c'.name = m) ∧
    (∀ ci ∈ kind.declsA, ci.name = ConLeche.punitRecName →
      ∃ c' ∈ kind.declsA, c'.name = ConLeche.punitName) := by
  cases kind <;> decide

/-- A basis run's names are fresh where it starts. -/
theorem basisInstallRun_fresh :
    ∀ {cis : List ConstantInfo} {E E₂ : Env}, BasisInstallRun E cis E₂ →
      ∀ ci ∈ cis, E.find? ci.name = none
  | [], _, _, _ => fun _ h => nomatch h
  | ci :: _, E, _, ⟨hf, hr⟩ => by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Option.isNone_iff_eq_none.mp hf
    · have h := basisInstallRun_fresh hr c hc
      rw [Env.find?_cons] at h
      split at h
      · exact nomatch h
      · exact h

theorem stepOk_basisInstallRun {B : Env} {all : List ConstantInfo}
    (hall : ∀ ci ∈ all, B.find? ci.name = none)
    (hmN : ∀ ci ∈ all, ci.name ∈ natLitNames → ∀ m ∈ natLitNames, ∃ c' ∈ all, c'.name = m)
    (hmP : ∀ ci ∈ all, ci.name = ConLeche.punitRecName →
      ∃ c' ∈ all, c'.name = ConLeche.punitName) :
    ∀ {cis : List ConstantInfo} {E E₂ : Env}, StepOk B E → (∀ ci ∈ cis, ci ∈ all) →
      (∀ ci ∈ cis, ci.name.isProjFnShape = false) →
      BasisInstallRun E cis E₂ → StepOk B E₂
  | [], _, _, h, _, _, hr => hr ▸ h
  | ci :: _, _, _, h, hsub, hs, ⟨hf, hr⟩ => by
    have hci := hsub ci List.mem_cons_self
    have hnew : NewOk B ci.name := by
      refine .inl ⟨hs ci List.mem_cons_self, fun hn m hm => ?_, fun hp => ?_⟩
      · obtain ⟨c', hc', rfl⟩ := hmN ci hci hn m hm
        exact hall c' hc'
      · obtain ⟨c', hc', hname⟩ := hmP ci hci hp
        rw [← hname]; exact hall c' hc'
    exact stepOk_basisInstallRun hall hmN hmP
      (h.cons (h.fresh (Option.isNone_iff_eq_none.mp hf)) hnew)
      (fun c hc => hsub c (List.mem_cons_of_mem _ hc))
      (fun c hc => hs c (List.mem_cons_of_mem _ hc)) hr

theorem stepOk_declBasisRun {env env₂ : Env} {kind : ConLeche.BasisKind}
    (h : DeclBasisRun env kind env₂) : StepOk env env₂ :=
  stepOk_basisInstallRun (basisInstallRun_fresh h.2) (basisDecls_mates kind).1
    (basisDecls_mates kind).2 (StepOk.refl env) (fun _ h => h) (basisDecls_shape kind) h.2

/-! ## The declaration step and the fold -/

/-- A front-door cons. -/
theorem stepOk_constantValRun {μ : CheckMode} {F : Nat} {env : Env} {cv : ConstantVal}
    {type' : Expr} (h : ConstantValRun μ F env cv type') (c : ConstantInfo)
    (hc : c.name = cv.name) : StepOk env ⟨c :: env.consts⟩ :=
  (StepOk.refl env).cons_plain (by rw [hc]; exact Option.isNone_iff_eq_none.mp h.1)
    (by rw [hc]; exact h.2.2.1) (by rw [hc]; exact h.2.1)

/-- **Every accepted declaration step is a `StepOk` extension.** -/
theorem stepOk_checkDecl {μ : CheckMode} {F : Nat} {pins : List ConLeche.NatOpPinSet}
    {env env₂ : Env} {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) pins env d = .ok env₂) : StepOk env env₂ := by
  have hrun := checkDeclRun_ofEnvFactsK h
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hrun
    exact stepOk_constantValRun hcv _ rfl
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
    exact stepOk_constantValRun hcv _ rfl
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl, -⟩ := hrun
    exact stepOk_constantValRun hcv _ rfl
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, hr⟩
    · exact StepOk.refl _
    · rcases hr with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
      · exact stepOk_constantValRun hcv _ rfl
      · exact stepOk_constantValRun hcv _ rfl
      · exact stepOk_constantValRun hcv _ rfl
      · exact StepOk.refl _
  | basisDecl kind => exact stepOk_declBasisRun hrun
  | indDecl block nP =>
    simp only [DeclRun] at hrun
    split at hrun
    · exact stepOk_declBasisRun hrun
    · unfold DeclIndRunDispatchK at hrun
      split at hrun
      · exact stepOk_declBlockRun hrun
      · exact hrun.elim
  | quotDecl k cv =>
    cases k with
    | type => exact stepOk_declBasisRun hrun
    | _ => exact (show env₂ = env from hrun) ▸ StepOk.refl env

/-- **Every accepted run of the fold is a `StepOk` extension.** -/
theorem stepOk_foldlM {μ : CheckMode} {F : Nat} {pins : List ConLeche.NatOpPinSet} :
    ∀ (ds : List Declaration) {env env' : Env},
      ds.foldlM (checkDecl μ (fueledOps μ F) pins) env = .ok env' → StepOk env env'
  | [], env, env', h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ StepOk.refl env
  | d :: ds, env, env', h => by
    simp only [List.foldlM, bind, Except.bind] at h
    cases hd : checkDecl μ (fueledOps μ F) pins env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      exact (stepOk_checkDecl hd).trans (stepOk_foldlM ds h)

/-! ## The member tie -/

section Tie

variable {mode : CheckMode} {Fi : Nat} {B env₁ E : Env} {p : BlockParts} {isRec : Bool}
  {cvTas : List ConstantVal} {p₁ : BlockShape}
  (hwf : ConLeche.EnvWF B) (hctors : ConLeche.RecCtorsStored B) (hnat : NatOpGuards B)
  (hInd : checkBlockInds (fueledOps mode Fi) B p isRec = .ok (env₁, cvTas, p₁))
  (hE : StepOk B E) (h₁E : Extends env₁ E)
include hwf hctors hnat hInd hE h₁E

/-- **The member tie, at the scope agreement**: `env₁(H)` and a later
fold environment `E` agree on `B`'s scope. -/
theorem memberTie_agree : Agree (InScope B) env₁ E :=
  have h₁ := stepOk_checkBlockInds hInd
  Agree.ofBase hwf hctors hnat h₁.1 h₁.noNewInScope hE.1 hE.noNewInScope h₁E

/-- **The member tie for the rec check's field telescopes**: at every
fuel and mode, a success of the field telescopes at `E` of fields whose
(member-abstracted) types resolve in `B` is their success at
`env₁(H)`. -/
theorem memberTie_targetFieldNorms (μ : CheckMode) (F d : Nat) (absM : Expr → Expr)
    {fs : List Expr} (hfs : ∀ f ∈ fs, (absM f.fvarTypeD).constsResolve B = true)
    {ts : List Expr} (h : ConLeche.targetFieldNorms (fueledOps μ F) E d absM fs = .ok ts) :
    ConLeche.targetFieldNorms (fueledOps μ F) env₁ d absM fs = .ok ts :=
  have h₁ := stepOk_checkBlockInds hInd
  targetFieldNorms_base_agree μ F hwf hctors hnat h₁.1 h₁.noNewInScope hE.1 hE.noNewInScope h₁E
    d absM hfs h

/-- The member tie for `whnf`. -/
theorem memberTie_whnf (μ : CheckMode) {F d : Nat} {e r : Expr} (he : e.constsResolve B = true)
    (h : ConLeche.whnf μ E F d e = .ok r) : ConLeche.whnf μ env₁ F d e = .ok r :=
  have h₁ := stepOk_checkBlockInds hInd
  whnf_base_agree μ hwf hctors hnat h₁.1 h₁.noNewInScope hE.1 hE.noNewInScope h₁E he h

/-- The member tie for `inferTypeCore`. -/
theorem memberTie_inferTypeCore (μ : CheckMode) {F d : Nat} {e r : Expr}
    (he : e.constsResolve B = true) (h : ConLeche.inferTypeCore μ E F d e = .ok r) :
    ConLeche.inferTypeCore μ env₁ F d e = .ok r :=
  have h₁ := stepOk_checkBlockInds hInd
  inferTypeCore_base_agree μ hwf hctors hnat h₁.1 h₁.noNewInScope hE.1 hE.noNewInScope h₁E he h

/-- The member tie for `isDefEqCore`. -/
theorem memberTie_isDefEqCore (μ : CheckMode) {F d : Nat} {a b : Expr} {v : Bool}
    (ha : a.constsResolve B = true) (hb : b.constsResolve B = true)
    (h : ConLeche.isDefEqCore μ E F d a b = .ok v) : ConLeche.isDefEqCore μ env₁ F d a b = .ok v :=
  have h₁ := stepOk_checkBlockInds hInd
  isDefEqCore_base_agree μ hwf hctors hnat h₁.1 h₁.noNewInScope hE.1 hE.noNewInScope h₁E ha hb h

/-- The member tie for the walk's field normal form (`nestTeleNf`,
`Kernel/Inductives/FieldNf.lean`), on a constructor type resolving in
`B` (members abstracted to holes). -/
theorem memberTie_nestTeleNf (μ : CheckMode) (F : Nat) (names : List Name)
    (nP hi fuel base nF j : Nat) {cur : Expr} (hc : cur.constsResolve B = true)
    {r : List (Expr × ConLeche.BinderMeta) × Expr}
    (h : ConLeche.nestTeleNf (fueledOps μ F) E names nP hi fuel base nF j cur = .ok r) :
    ConLeche.nestTeleNf (fueledOps μ F) env₁ names nP hi fuel base nF j cur = .ok r :=
  have h₁ := stepOk_checkBlockInds hInd
  nestTeleNf_base_agree μ F names nP hi hwf hctors hnat h₁.1 h₁.noNewInScope hE.1
    hE.noNewInScope h₁E fuel base nF j hc h

end Tie

/-- **The fold-level form**: a block `H` recognised and installed at `B`,
and ANY later fold environment `E` — the rest of
the stream run from `H`'s result — tie. -/
theorem memberTie_fold {μ : CheckMode} {F : Nat} {pins : List ConLeche.NatOpPinSet}
    {B env₂ E : Env} {block : List ConstantInfo} {p₀ : BlockParts}
    (hH : DeclBlockRun μ F B block p₀ env₂) {ds : List Declaration}
    (hrest : ds.foldlM (checkDecl μ (fueledOps μ F) pins) env₂ = .ok E) :
    StepOk B E :=
  (stepOk_declBlockRun hH).trans (stepOk_foldlM ds hrest)

end ConLeche.Semantics
