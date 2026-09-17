module

public import ConLeche.Model.Inductives.NestedRecCtor
public import ConLeche.Model.Inductives.NestedRecTypes
import ConLeche.Model.Inductives.MutualFormersKit
import ConLeche.Model.Inductives.NestedTransfer
import ConLeche.Model.Inductives.MutualRecsStage
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedGroupInv
public import ConLeche.Verify.Inductives.NestedRestoreTbl
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedRecNames
import ConLeche.Verify.Inductives.NestedRecCtorPin
import ConLeche.Verify.Inductives.NestedCopyGlue
import ConLeche.Verify.Inductives.NestedRestoreKit
public section

/-!
# The restored recursor types' frames, by transfer (task #315, M7-2, PLAN-M7 §1e)

The thirteen bookkeeping clauses of `NestedRecReadings` are
`NestedTailIn.readings`' (`NestedRecTypes.lean`); its fourteenth,
`frames = ReadingFramesT`, is this file's — by TRANSFER along the
restore walk's reading law (`denoteMeta_restoreWalk`,
`NestedRecWalk.lean`): a spine fitting the RESTORED recursor type's
reading fits the SCRATCH one's, whose frame inversion is the MUTUAL
`IsBlockModels.spineFit_recData_inv` at the auxiliary block's own
block model, and the frame's semantic clauses transfer back through
the fibre kit (`NestedRecFibre.lean`).

* B1 `NestedRecTysAuxOk` — the walk's shape precondition at the run
  (K.35's model face: every read-back recursor type, below its
  parameter prefix, is `AuxAppsOk` at the restore table);
* B2 `NestedTailIn.restoreAgree` — `RestoreAgree` instantiated at the
  tail, with T2's `NestedTailIn.ctorArm` as its `ctor` field.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock MutualFormer MutualCtor4 AuxStored ElimState NestedPin IndCaps
  AuxType ContainerInfo ContainerMember ContainerCtor fueledOps BinderMeta PropWhen RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## B1 — the walk's precondition at the run -/

/-- **K.35's model face** (PLAN-M7 §1a, provisional until the kernel
record lands): every read-back recursor type, below its parameter
prefix of `b.nP` binders, has the shape the restore walk relies on —
every application headed by a restore-table key carries the block's
parameter variables in its first `nP` arguments and the key's arity
(`nestedArity`) in all — stated at depth `0` below the prefix. -/
@[expose] def NestedRecTysAuxOk (p : NestedParts) (st : ElimState) (b : MutualBlock)
    (stored : List AuxStored) (pinsS : List PinSyn) : Prop :=
  ∀ (c : Nat) (a : AuxStored), stored[c]? = some a →
    ∃ (pbs : List (Expr × BinderMeta)) (body : Expr),
      a.cvRa.type.stripPis b.nP = some (pbs, body) ∧
      AuxAppsOk (ConLeche.restoreTbl p st) b.lps (nestedArity p st pinsS) 0 body

/-! ## The arity at a pin key -/

/-- With the keys pairwise distinct, the element with the sought key IS
what `find?` returns on the indexed list, at its own index. -/
private theorem findIdx_key_of_nodup {α : Type} (f : α → Name) :
    ∀ {l : List α} {i s : Nat} {a : α}, (l.map f).Nodup → l[i]? = some a →
      (l.zipIdx s).find? (fun x => f x.1 == f a) = some (a, s + i)
  | [], i, _, _, _, hi => absurd hi (by simp)
  | x :: l, i, s, a, hnd, hi => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.zipIdx_cons, List.find?_cons]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [beq_self_eq_true, Nat.add_zero]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have hne : (f x == f a) = false := by
        rw [beq_eq_false_iff_ne]
        intro hh
        exact hnd.1 (List.mem_map.mpr ⟨a, List.mem_of_getElem? hi, hh.symm⟩)
      simp only [hne, findIdx_key_of_nodup f hnd.2 hi, Option.some.injEq, Prod.mk.injEq,
        true_and]
      omega

/-- **THE ARITY AT A PIN'S AUXILIARY NAME** is the container's index
count: the pins, listed once each, answer at their own key. -/
theorem nestedArity_pin {p : NestedParts} {st : ElimState} {pinsS : List PinSyn}
    {q : Nat} {qn : NestedPin} (hnd : (st.pins.map (·.aux)).Nodup)
    (hqn : st.pins[q]? = some qn) :
    nestedArity p st pinsS qn.aux = some (pinsS.getD q default).nIdx := by
  have hfind := findIdx_key_of_nodup (·.aux) (l := st.pins) (i := q) (s := 0) hnd hqn
  simp only [nestedArity, hfind, Nat.zero_add]

/-! ## The run's section -/

section Run

variable {env : Env} {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {envOut : Env}
  {st : ElimState} {b : MutualBlock} {envAux : Env} {stored : List AuxStored}
  {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms cvRns : List ConstantVal}
  {rulesM rulesN : List (List RecRule)} {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}
  {mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
    (ConLeche.consMutualFormers (fms.take p.k) env))}

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)
local notation "ENV₂" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))
local notation "ENVA" =>
  (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

local notation "DA" => (mutualBlockModel (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xFvsF xrestF eissF tssF)

local notation "PC" => (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)

local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

variable (I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN
  fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF
  tssF dsR xFvsR pinsS mp₂)
include I

/-! ### The formers' prefix, as an environment extension -/

/-- The auxiliary block's member names are pairwise distinct. -/
theorem NestedTailIn.fmsNodup : (fms.map (·.cvTa.name)).Nodup := by
  rw [I.out.facts.names]
  have h0 := I.out.nodup
  unfold ConLeche.MutualBlock.blockNames at h0
  exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1

/-- The block's own members' conses preserve the pre-block
environment. -/
theorem NestedTailIn.findPre1 : FindPreserved env (ENV₁) :=
  (consMutualFormers_extend (fms := fms.take p.k) (env := env)
    (fun f hf => by
      obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_take hf)
      exact I.out.facts.fresh t f ht)
    (by
      have := I.fmsNodup
      rw [← List.take_append_drop p.k fms, List.map_append] at this
      exact (List.nodup_append.mp this).1)).1

/-! ### The pin's reading at the restored model -/

/-- **A PIN, RE-OPENED AT THE PARAMETER OPENERS, READS AS THE
CONTAINER AT THE LIFTED COMPONENTS** at every depth past the
parameters (`ReadCtx.pinRead`'s twin at the tail's restored model):
the pins' facts (`pinRec`, `pinψ`, `pinDs`), the container's store and
`pinsClosed`, through `nt_denoteMeta_restoredPin`. -/
theorem NestedTailIn.pinRead {q : Nat} {qn : NestedPin} {ci : ContainerInfo}
    (hqn : st.pins[q]? = some qn) (hq : q < pinsS.length)
    (hci : ConLeche.containerInfo? env qn.container = some ci) (ψ : Name → Nat) :
    ∀ (fvsP : List Expr) (d : Nat), OpenersFrom fvsP 0 b.nP →
      denoteMeta mp₂.base2.acval (ENV₂) ψ (b.nP + d)
          (Expr.instSeq fvsP (b.nP - 1) (Expr.abstractRange qn.pin 0 p.nP 0))
        = some (AnnotTerm.mkAppN (mp₂.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
            ((((D).pinAt q).Ds ψ).map (·.liftN d 0))) := by
  intro fvsP d hfvsP
  obtain ⟨hnP, -, -, -⟩ := ConLeche.auxBlock_fields I.hb
  obtain ⟨hPJ, hpinEq⟩ := I.out.stage.pinRec q qn hqn
  have hpinDs : DenoteMetaSpine mp₂.base2.acval (ENV₂) ψ b.nP ((D).pinAt q).DsE
    (((D).pinAt q).Ds ψ) := I.out.stage.pinDs q hq ψ
  have hfv0 := (ConLeche.pinsClosed_inv I.hclosed qn (List.mem_of_getElem? hqn)).1
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfindI, -, -, -, -⟩ := ConLeche.containerInfo?_inv hci
  have hfindI1 : (ENV₁).find? ((D).pinAt q).J = some (.indInfo cvT caps) := by
    rw [hPJ]; exact I.findPre1 hfindI
  obtain ⟨hlvlsLen, hψJ⟩ := I.out.stage.pinψ q hq cvT caps hfindI1
  have hfindI2 : (ENV₂).find? ((D).pinAt q).J = some (.indInfo cvT caps) :=
    I.out.stage.find hfindI1
  have hidx : ∀ k, k < b.nP → ∃ ty, fvsP[k]? = some (.fvar k ty) := by
    intro k hk
    obtain ⟨x, hx⟩ : ∃ x, fvsP[k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hfvsP.1]; exact hk)⟩
    obtain ⟨ty, rfl⟩ := hfvsP.2 k x hx
    exact ⟨ty, by simpa using hx⟩
  have hψJ' : ∀ ψ' : Name → Nat,
      ((D).pinAt q).ψJ ψ' = Level.substFn ψ' cvT.levelParams ((D).pinAt q).lvls := hψJ
  have hfv : (Expr.abstractRange (Expr.mkAppN (.const qn.container ((D).pinAt q).lvls)
      ((D).pinAt q).DsE) 0 b.nP 0).hasFvar = false := by
    rw [hnP, ← hpinEq]
    exact hfv0
  rw [hpinEq, ← hnP, hPJ]
  have hfindI2' : (ENV₂).find? qn.container = some (.indInfo cvT caps) := by
    rw [hPJ] at hfindI2; exact hfindI2
  rw [nt_denoteMeta_restoredPin mp₂.base2 hfvsP.1 hidx hfv hfindI2'
    (show ((D).pinAt q).lvls.length
      = (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length from hlvlsLen) hpinDs,
    show (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams = cvT.levelParams from rfl,
    ← hψJ' ψ]

/-! ### The copy's block position -/

/-- **A PIN'S AUXILIARY NAME IS ITS COPY'S MEMBER NAME**: the
elimination's type at `k + q` is the pin's copy (`elimNested_aligned`),
the auxiliary block's members are its types (`auxBlock_former`), and
the formers' run carries the block's member names. -/
theorem NestedTailIn.copyName {q : Nat} {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    (hq : q < pinsS.length) :
    ∃ f : MutualFormerA, fms[p.k + q]? = some f ∧ f.cvTa.name = qn.aux := by
  have hlen0 : (ConLeche.nestedTypes0 p fmsA ctorsA₀).length = p.k := by
    rw [ConLeche.nestedTypes0_length, ConLeche.nestedAnnotFormers_length I.hfA]
    rfl
  have hal := ConLeche.elimNested_aligned hlen0 I.helim
  obtain ⟨-, hform⟩ := ConLeche.auxBlock_former I.hb
  obtain ⟨t', ht', htn'⟩ := hal.2 q qn hqn
  obtain ⟨nIdx', hfo', -⟩ := hform (p.k + q) t' ht'
  obtain ⟨f, hf⟩ : ∃ f, fms[p.k + q]? = some f :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.out.facts.lenFms, I.out.bk]; omega)⟩
  refine ⟨f, hf, ?_⟩
  have h1 : (fms.map (·.cvTa.name))[p.k + q]? = some f.cvTa.name := by
    rw [List.getElem?_map, hf]; rfl
  rw [I.out.facts.names] at h1
  have h2 : b.memberNames[p.k + q]? = some t'.name := by
    simp only [ConLeche.MutualBlock.memberNames, List.getElem?_map, hfo', Option.map_some]
  rw [Option.some.inj (h1.symm.trans h2), htn']

/-! ### B2 — the pin's arm of `RestoreAgree` -/

/-- **THE COPY'S AGREEMENT AT THE TAIL** (`RestoreAgree.pin`): a `pins`
hit is a recorded pin, abstracted at the block's parameters and so
bounded there; its copy is a member of the scratch block, stored with
the block's level parameters, and the key's arity is the container's
index count (`nestedArity_pin`); the restored pin reads as the
container at the lifted components (`pinRead`); and the two readings
interpret alike — THE PIN IDENTITY `nestedIdent_of`, the copy's leaf
being the scratch model's own (`NestedScratchOut.leafM` through
`MutualFormersFacts.leaf`). -/
theorem NestedTailIn.pinArm {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas) (ψ : Name → Nat) :
    ∀ (n : Name) (pin : Expr), (ConLeche.restoreTbl p st).pins.lookup n = some pin →
      pin.looseBVarsBounded b.nP = true ∧
      ∃ (ci : ConstantInfo) (J : Name) (ψJ : Name → Nat) (Ds : List AnnotTerm) (nIdx : Nat),
        (ENVA).find? n = some ci ∧ ci.toConstantVal.levelParams = b.lps ∧
        nestedArity p st pinsS n = some nIdx ∧
        (∀ (fvsP : List Expr) (d : Nat), OpenersFrom fvsP 0 b.nP →
          denoteMeta mp₂.base2.acval (ENV₂) ψ (b.nP + d) (Expr.instSeq fvsP (b.nP - 1) pin)
            = some (AnnotTerm.mkAppN (mp₂.base2.acval J ψJ) (Ds.map (·.liftN d 0)))) ∧
        ∀ (d : Nat) (as xs : List V) (ρ₀ : Nat → V) (Es : List AnnotTerm),
          SpineFit ρ₀ ((D).params ψ) as → xs.length = d → Es.length = nIdx →
          WellDenoted V (consList xs (consList as ρ₀))
            (AnnotTerm.mkAppN (mp₂.base2.acval J ψJ) (Ds.map (·.liftN d 0) ++ Es)) →
          interp V (consList xs (consList as ρ₀))
              (AnnotTerm.mkAppN (mp₂.base2.acval J ψJ) (Ds.map (·.liftN d 0) ++ Es))
            = interp V (consList xs (consList as ρ₀))
              (AnnotTerm.mkAppN (mpA.base2.acval n ψ) (paramBvarsAt b.nP (b.nP + d) ++ Es)) := by
  intro n pin hlook
  obtain ⟨qn, hqnm, rfl, rfl⟩ := ConLeche.rk_restoreTbl_pins_lookup_inv hlook
  obtain ⟨q, hqn⟩ := List.getElem?_of_mem hqnm
  have hq : q < pinsS.length := by
    rw [I.out.stage.pinsLen]; exact (List.getElem?_eq_some_iff.mp hqn).1
  obtain ⟨hnP, -, -, -⟩ := ConLeche.auxBlock_fields I.hb
  obtain ⟨f, hf, hfn⟩ := I.copyName hqn hq
  -- the container's record
  obtain ⟨t₀, pbs, body, -, -, hsrc⟩ := ConLeche.nestedCopySrcOk_inv I.hsrc
  obtain ⟨t₂, Jn, lvls, Ds₀, ci, J, cpy, ht₂, -, hJn, -, hci, -, -, -, -, -, -⟩ := hsrc q qn hqn
  rw [hJn] at hci
  refine ⟨?_, .indInfo f.cvTa {}, ((D).pinAt q).J, ((D).pinAt q).ψJ ψ, ((D).pinAt q).Ds ψ,
    ((D).pinAt q).nIdx, ?_, ?_, ?_, I.pinRead hqn hq hci ψ, ?_⟩
  · -- the abstracted pin is bounded at the block's parameters
    rw [hnP]
    exact (ConLeche.rk_pinsClosed_of I.hclosed qn hqnm).2
  · rw [← hfn]
    exact (S.memberStored (p.k + q) f hf).find
  · show f.cvTa.levelParams = b.lps
    exact I.out.facts.lps _ f hf
  · rw [← hfn, hfn]
    exact nestedArity_pin (ConLeche.nestedPinAux_nodup I.hfA I.helim I.hb I.haux) hqn
  · intro d as xs ρ₀ Es hsp hxs hEs hwd
    have hleaf : mpA.base2.acval qn.aux ψ
        = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF (p.k + q) ψ := by
      rw [← hfn, S.leafM (p.k + q) f hf, I.out.facts.leaf (p.k + q) f hf]
    rw [hleaf]
    exact nestedIdent_of I.hμ I.out.facts I.out.grouped I.out.bk mp₂.base2 I.out.stage.groups
      q hq ψ ρ₀ as hsp d xs Es hxs hEs hwd

/-! ### The auxiliary names, from the two sides of the block -/

/-- The elimination's alignment at the tail. -/
theorem NestedTailIn.aligned : ConLeche.PinsAligned p.k st := by
  have hlen0 : (ConLeche.nestedTypes0 p fmsA ctorsA₀).length = p.k := by
    rw [ConLeche.nestedTypes0_length, ConLeche.nestedAnnotFormers_length I.hfA]
    rfl
  exact ConLeche.elimNested_aligned hlen0 I.helim

/-- **A COPY'S MEMBER NAME IS AN AUXILIARY NAME**: past the block's own
`k` members the auxiliary block's members are the elimination's copies,
and a copy's name is the pin's key. -/
theorem NestedTailIn.memberName_aux {t : Nat} {f : MutualFormerA} (hf : fms[t]? = some f)
    (ht : p.k ≤ t) : f.cvTa.name ∈ (ConLeche.restoreTbl p st).auxNames := by
  have hal := I.aligned
  have hk : b.k = st.types.length := ConLeche.auxBlock_k I.hb
  obtain ⟨-, hform⟩ := ConLeche.auxBlock_former I.hb
  have htl : t < fms.length := (List.getElem?_eq_some_iff.mp hf).1
  obtain ⟨q, rfl⟩ : ∃ q, t = p.k + q := ⟨t - p.k, by omega⟩
  have hq : q < st.pins.length := by
    have h1 := I.out.facts.lenFms
    have h2 := I.out.bk
    have h3 := I.out.stage.pinsLen
    omega
  obtain ⟨qn, hqn⟩ : ∃ qn, st.pins[q]? = some qn := ⟨_, List.getElem?_eq_getElem hq⟩
  obtain ⟨t', ht', htn'⟩ := hal.2 q qn hqn
  obtain ⟨nIdx', hfo', -⟩ := hform (p.k + q) t' ht'
  have h1 : (fms.map (·.cvTa.name))[p.k + q]? = some f.cvTa.name := by
    rw [List.getElem?_map, hf]; rfl
  rw [I.out.facts.names] at h1
  have h2 : b.memberNames[p.k + q]? = some t'.name := by
    simp only [ConLeche.MutualBlock.memberNames, List.getElem?_map, hfo', Option.map_some]
  rw [Option.some.inj (h1.symm.trans h2), htn']
  exact ConLeche.restoreTbl_aux_mem hqn

/-- **A COPY'S CONSTRUCTOR NAME IS AN AUXILIARY NAME**: the auxiliary
block's constructors past the block's own members are the copies'. -/
theorem NestedTailIn.copyCtorName_aux {J : Nat} {c : ConLeche.MutualCtor}
    (hJ : b.ctors[J]? = some c) (hmem : p.k ≤ c.member) :
    c.cv.name ∈ (ConLeche.restoreTbl p st).auxNames := by
  obtain ⟨-, -, -, hct⟩ := ConLeche.auxBlock_fields I.hb
  rw [hct] at hJ
  have hcmem := List.mem_of_getElem? hJ
  rw [List.mem_flatten] at hcmem
  obtain ⟨l, hl, hcl⟩ := hcmem
  obtain ⟨tm, htm, rfl⟩ := List.mem_map.mp hl
  obtain ⟨t, mIdx⟩ := tm
  simp only [List.mem_map] at hcl
  obtain ⟨cc, hcc, rfl⟩ := hcl
  have hmIdx : p.k ≤ mIdx := hmem
  have hst : st.types[mIdx]? = some t := List.mk_mem_zipIdx_iff_getElem?.mp htm
  have htd : t ∈ st.types.drop p.k := by
    refine List.mem_of_getElem? (i := mIdx - p.k) ?_
    rw [List.getElem?_drop, show p.k + (mIdx - p.k) = mIdx from by omega]
    exact hst
  show cc.1 ∈ (ConLeche.restoreTbl p st).auxNames
  simp only [ConLeche.restoreTbl]
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  exact List.mem_flatMap.mpr ⟨t, htd, List.mem_map.mpr ⟨cc, hcc, rfl⟩⟩

/-- **THE RESTORED CONSTRUCTOR'S NAME IS THE AUXILIARY ONE'S**
(`restoredCtors_at`'s public half at the tail): the restore keeps every
constructor's name, and the read-back's constructors at member `mm` are
the block's own run of `b.ownCtors mm`. -/
theorem NestedTailIn.ctorsRName {mm j : Nat} {l : List (ConstantVal × Nat × Nat)}
    {c : ConstantVal × Nat × Nat} (hl : ctorsR[mm]? = some l) (hc : l[j]? = some c) :
    ∃ cA : ConstantVal × Nat, ctorsA[b.ownOffset mm + j]? = some cA ∧ c.1.name = cA.1.name := by
  obtain ⟨hlenR, hallR⟩ := ConLeche.mapM_except_inv I.hctors
  have hmm : mm < (stored.take p.k).length := by
    rw [← hlenR]; exact (List.getElem?_eq_some_iff.mp hl).1
  obtain ⟨a, l', ha, hl', hrun⟩ := hallR mm hmm
  obtain rfl := Option.some.inj (hl'.symm.trans hl)
  have hst : stored[mm]? = some a := by
    rw [List.getElem?_take] at ha
    by_cases hlt : mm < p.k
    · rwa [if_pos hlt] at ha
    · rw [if_neg hlt] at ha; exact absurd ha (by simp)
  obtain ⟨hlenC, hallC⟩ := ConLeche.restoreCtors_id hrun
  have hj : j < a.ctors.length := by
    rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, a.ctors[j]? = some c₀ := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨ty, -, hceq⟩ := hallC j c₀ c hc₀ hc
  obtain ⟨hlenOwn, hallOwn⟩ :=
    ConLeche.auxStored_ctor_eq I.haux I.out.formers I.out.ctors I.out.grouped I.hstored hst
  obtain ⟨cA, hcA, e1, -, -⟩ := hallOwn j c₀ hc₀
  refine ⟨cA, hcA, ?_⟩
  rw [hceq]
  show c₀.1.name = cA.1.name
  exact congrArg ConstantVal.name e1

/-! ### The name classification -/

/-- **A NAME OFF THE AUXILIARY NAMES IS THE BLOCK'S OWN, OR OFF THE
BLOCK**: it is one of the `k` declared members, one of their
constructors, or neither (the copies and their constructors carry
auxiliary names). -/
theorem NestedTailIn.nameCases (n : Name) (hn : n ∉ (ConLeche.restoreTbl p st).auxNames) :
    (∃ (t : Nat) (f : MutualFormerA), t < p.k ∧ fms[t]? = some f ∧ f.cvTa.name = n) ∨
    (∃ (mm j : Nat) (cA : ConstantVal × Nat), mm < p.k ∧ j < (b.ownCtors mm).length ∧
      ctorsA[b.ownOffset mm + j]? = some cA ∧ cA.1.name = n) ∨
    ((∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → f.cvTa.name ≠ n) ∧
      ∀ cA ∈ ctorsA, cA.1.name ≠ n) := by
  by_cases hm : ∃ (t : Nat) (f : MutualFormerA), fms[t]? = some f ∧ f.cvTa.name = n
  · obtain ⟨t, f, hf, rfl⟩ := hm
    refine Or.inl ⟨t, f, ?_, hf, rfl⟩
    rcases Nat.lt_or_ge t p.k with hlt | hlt
    · exact hlt
    · exact absurd (I.memberName_aux hf hlt) hn
  · by_cases hc : ∃ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA ∧ cA.1.name = n
    · obtain ⟨J, cA, hJ, rfl⟩ := hc
      obtain ⟨hlenA, hnamesA⟩ :=
        ctorsA_names_of I.out.ctors (ConLeche.checkMutualCore_inv I.haux).2.1
      obtain ⟨ct, hct⟩ : ∃ ct, b.ctors[J]? = some ct :=
        ⟨_, List.getElem?_eq_getElem (by rw [← hlenA]; exact (List.getElem?_eq_some_iff.mp hJ).1)⟩
      have hname : cA.1.name = ct.cv.name := (hnamesA J cA ct hJ hct).1
      have hmem : ct.member < p.k := by
        rcases Nat.lt_or_ge ct.member p.k with hlt | hlt
        · exact hlt
        · exact absurd (hname ▸ I.copyCtorName_aux hct hlt) hn
      obtain ⟨hle, hown⟩ := ConLeche.ownCtors_of_ctors I.out.grouped hct
      refine Or.inr (Or.inl ⟨ct.member, J - b.ownOffset ct.member, cA, hmem,
        (List.getElem?_eq_some_iff.mp hown).1, ?_, rfl⟩)
      rw [show b.ownOffset ct.member + (J - b.ownOffset ct.member) = J from by omega]
      exact hJ
    · refine Or.inr (Or.inr ⟨fun t f hf hne => hm ⟨t, f, hf, hne⟩, fun cA hcA hne => ?_⟩)
      obtain ⟨J, hJ⟩ := List.getElem?_of_mem hcA
      exact hc ⟨J, cA, hJ, hne⟩

/-! ### The auxiliary names against the block's own constructors -/

/-- A pin's key is a member name of the auxiliary block, and its
recursor's name a recursor name of it. -/
theorem NestedTailIn.pinAuxMem {q : Nat} {qn : NestedPin} (hqn : st.pins[q]? = some qn) :
    qn.aux ∈ b.memberNames ∧ qn.aux.str "rec" ∈ (List.range b.k).map b.recName := by
  have hal := I.aligned
  have hk : b.k = st.types.length := ConLeche.auxBlock_k I.hb
  obtain ⟨-, hform⟩ := ConLeche.auxBlock_former I.hb
  obtain ⟨t, ht, htn⟩ := hal.2 q qn hqn
  obtain ⟨nIdx, hfo, -⟩ := hform (p.k + q) t ht
  have hq : q < st.pins.length := (List.getElem?_eq_some_iff.mp hqn).1
  constructor
  · refine List.mem_of_getElem? (i := p.k + q) ?_
    simp only [ConLeche.MutualBlock.memberNames, List.getElem?_map, hfo, Option.map_some, htn]
  · refine List.mem_map.mpr ⟨p.k + q, List.mem_range.mpr ?_, ?_⟩
    · rw [hk, hal.1]; omega
    · simp only [ConLeche.MutualBlock.recName, List.getD_eq_getElem?_getD, hfo, Option.getD_some,
        htn]

/-- **A DECLARED MEMBER'S CONSTRUCTOR NAME IS ONE OF THE BLOCK'S OWN
TYPES' CONSTRUCTORS** (`copyCtorName_aux`'s twin below `p.k`). -/
theorem NestedTailIn.memberCtorName {J : Nat} {c : ConLeche.MutualCtor}
    (hJ : b.ctors[J]? = some c) (hmem : c.member < p.k) :
    c.cv.name ∈ (st.types.take p.k).flatMap (fun t => t.ctors.map (·.1)) := by
  obtain ⟨-, -, -, hct⟩ := ConLeche.auxBlock_fields I.hb
  rw [hct] at hJ
  have hcmem := List.mem_of_getElem? hJ
  rw [List.mem_flatten] at hcmem
  obtain ⟨l, hl, hcl⟩ := hcmem
  obtain ⟨tm, htm, rfl⟩ := List.mem_map.mp hl
  obtain ⟨t, mIdx⟩ := tm
  simp only [List.mem_map] at hcl
  obtain ⟨cc, hcc, rfl⟩ := hcl
  have hmIdx : mIdx < p.k := hmem
  have hst : st.types[mIdx]? = some t := List.mk_mem_zipIdx_iff_getElem?.mp htm
  have htd : t ∈ st.types.take p.k := by
    refine List.mem_of_getElem? (i := mIdx) ?_
    rw [List.getElem?_take_of_lt hmIdx]
    exact hst
  exact List.mem_flatMap.mpr ⟨t, htd, List.mem_map.mpr ⟨cc, hcc, rfl⟩⟩


omit I in
/-- The constructors of a list of types, flattened, by name. -/
theorem map_flatMap_ctors (ts : List AuxType) :
    (ts.flatMap (·.ctors)).map (·.1) = ts.flatMap (fun t => t.ctors.map (·.1)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [List.flatMap_cons, List.map_append, ih, List.flatMap_cons]

/-- The restored constructors' lists are the block's own members'. -/
theorem NestedTailIn.ctorsRlt {mm : Nat} {l : List (ConstantVal × Nat × Nat)}
    (hl : ctorsR[mm]? = some l) : mm < p.k := by
  obtain ⟨hlenR, -⟩ := ConLeche.mapM_except_inv I.hctors
  have h2 := (List.getElem?_eq_some_iff.mp hl).1
  rw [hlenR, List.length_take] at h2
  omega

/-- **THE RESTORED CONSTRUCTOR IS ITS MEMBER'S**: at member `mm` and
position `j` the auxiliary block's constructor `ownOffset mm + j` is
member `mm`'s, and carries the restored one's name. -/
theorem NestedTailIn.ctorsRMember {mm j : Nat} {l : List (ConstantVal × Nat × Nat)}
    {c : ConstantVal × Nat × Nat} (hl : ctorsR[mm]? = some l) (hc : l[j]? = some c) :
    ∃ ct : ConLeche.MutualCtor, b.ctors[b.ownOffset mm + j]? = some ct ∧ ct.member = mm ∧
      c.1.name = ct.cv.name := by
  have hmm : mm < p.k := I.ctorsRlt hl
  have hlD : ctorsR.getD mm [] = l := by rw [List.getD_eq_getElem?_getD, hl]; rfl
  have hj : j < (b.ownCtors mm).length := by
    rw [← I.out.stage.ctorsLen mm hmm, hlD]
    exact (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨x, hx⟩ : ∃ x, (b.ownCtors mm)[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨J, ct⟩ := x
  have hJ : J = b.ownOffset mm + j := ConLeche.ownCtors_getElem?_idx I.out.grouped hx
  obtain ⟨hct, hmember⟩ := ConLeche.ownCtors_getElem?_ctors hx
  rw [hJ] at hct
  refine ⟨ct, hct, hmember, ?_⟩
  obtain ⟨cA, hcA, hname⟩ := I.ctorsRName hl hc
  obtain ⟨hlenA, hnamesA⟩ :=
    ctorsA_names_of I.out.ctors (ConLeche.checkMutualCore_inv I.haux).2.1
  rw [hname]
  exact (hnamesA _ cA ct hcA hct).1

/-- **NO DECLARED MEMBER'S CONSTRUCTOR CARRIES AN AUXILIARY NAME**: the
copies' member names and their recursors' are not constructor names at
all (`blockNames.Nodup`), and the copies' own constructors are the
other half of one list without repetitions. -/
theorem NestedTailIn.memberCtor_ne_aux {J : Nat} {c : ConLeche.MutualCtor}
    (hJ : b.ctors[J]? = some c) (hmem : c.member < p.k) :
    c.cv.name ∉ (ConLeche.restoreTbl p st).auxNames := by
  have hnd : b.blockNames.Nodup := I.out.nodup
  rw [ConLeche.MutualBlock.blockNames] at hnd
  have hcn : (b.ctors.map (·.cv.name)).Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  have hmemC : c.cv.name ∈ b.ctors.map (·.cv.name) :=
    List.mem_map.mpr ⟨c, List.mem_of_getElem? hJ, rfl⟩
  obtain ⟨-, -, -, hct⟩ := ConLeche.auxBlock_fields I.hb
  have hsplit : ((st.types.take p.k).flatMap (fun t => t.ctors.map (·.1))
      ++ (st.types.drop p.k).flatMap (fun t => t.ctors.map (·.1))).Nodup := by
    have h := hcn
    rw [hct, auxCtorNames_flat p.lps st.types 0] at h
    rw [← List.take_append_drop p.k st.types, List.flatMap_append, List.map_append,
      map_flatMap_ctors, map_flatMap_ctors] at h
    exact h
  have hdisj := (List.nodup_append.mp hsplit).2.2
  intro hin
  simp only [ConLeche.restoreTbl, List.mem_append] at hin
  rcases hin with (hin | hin) | hin
  · -- a copy's member name
    obtain ⟨qn, hqnm, hqe⟩ := List.mem_map.mp hin
    obtain ⟨q, hqn⟩ := List.getElem?_of_mem hqnm
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 _ (I.pinAuxMem hqn).1 _ hmemC
      hqe
  · -- a copy's constructor name
    exact hdisj _ (I.memberCtorName hJ hmem) _ hin rfl
  · -- a copy's recursor name
    obtain ⟨qn, hqnm, hqe⟩ := List.mem_map.mp hin
    obtain ⟨q, hqn⟩ := List.getElem?_of_mem hqnm
    exact (List.nodup_append.mp hnd).2.2 _ (List.mem_append_right _ hmemC) _
      (I.pinAuxMem hqn).2 hqe.symm

/-! ### `RestoreAgree`'s freshness clause -/

/-- **THE AUXILIARY NAMES ARE ABSENT FROM THE RESTORED ENVIRONMENT**
(`RestoreAgree.auxFresh`): they are fresh before the block
(`copiesFresh`), they are none of the `k` declared members, and none of
the restored constructors (whose names are the declared members'
constructors'). -/
theorem NestedTailIn.auxFresh : ∀ n ∈ (ConLeche.restoreTbl p st).auxNames,
    (ENV₂).find? n = none := by
  intro n hn
  obtain ⟨hfresh0, hnotmem⟩ :=
    ConLeche.rk_restoreTbl_auxNames_fresh I.out.nodup I.aligned I.hb I.hfresh n hn
  have hmn : b.memberNames = fms.map (·.cvTa.name) := I.out.facts.names.symm
  rw [ConLeche.consNestedCtors_find?_of_ne ?_, consMutualFormers_find?_of_ne ?_]
  · exact hfresh0
  · -- no declared member carries an auxiliary name
    intro g hg hge
    refine hnotmem ?_
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hg
    have htk : t < p.k := by
      have h2 := (List.getElem?_eq_some_iff.mp ht).1
      rw [List.length_take] at h2
      omega
    have ht' : fms[t]? = some g := by
      rw [← List.getElem?_take_of_lt htk]; exact ht
    refine List.mem_of_getElem? (i := t) ?_
    rw [List.getElem?_take_of_lt htk, hmn, List.getElem?_map, ht']
    exact congrArg some hge
  · -- no restored constructor carries an auxiliary name
    intro c hc hce
    obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
    obtain ⟨mm, hmm⟩ := List.getElem?_of_mem hl
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcl
    obtain ⟨ct, hct, hmember, hname⟩ := I.ctorsRMember hmm hj
    refine I.memberCtor_ne_aux hct ?_ ?_
    · rw [hmember]; exact I.ctorsRlt hmm
    · rw [← hname, hce]; exact hn

/-! ### The leaves off the auxiliary names -/

/-- The restored constructors' list at a member of the block. -/
theorem NestedTailIn.ctorsRget {mm : Nat} (hmm : mm < p.k) :
    ctorsR[mm]? = some (ctorsR.getD mm []) := by
  obtain ⟨hlenR, -⟩ := ConLeche.mapM_except_inv I.hctors
  have hlt : mm < ctorsR.length := by
    rw [hlenR, List.length_take, I.storedLen, I.out.bk]
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  rfl

/-- The auxiliary block's constructor names are pairwise distinct. -/
theorem NestedTailIn.ctorsANodup : (ctorsA.map (·.1.name)).Nodup := by
  have hnd : b.blockNames.Nodup := I.out.nodup
  rw [ConLeche.MutualBlock.blockNames] at hnd
  have hcn : (b.ctors.map (·.cv.name)).Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  obtain ⟨hlenA, hnamesA⟩ :=
    ctorsA_names_of I.out.ctors (ConLeche.checkMutualCore_inv I.haux).2.1
  have hmap : ctorsA.map (·.1.name) = b.ctors.map (·.cv.name) := by
    refine List.ext_getElem? fun J => ?_
    rw [List.getElem?_map, List.getElem?_map]
    cases hJ : ctorsA[J]? with
    | none =>
      rw [List.getElem?_eq_none (by rw [← hlenA]; exact List.getElem?_eq_none_iff.mp hJ)]
      rfl
    | some cA =>
      obtain ⟨ct, hct⟩ : ∃ ct, b.ctors[J]? = some ct :=
        ⟨_, List.getElem?_eq_getElem (by rw [← hlenA]; exact (List.getElem?_eq_some_iff.mp hJ).1)⟩
      rw [hct]
      exact congrArg some (hnamesA J cA ct hJ hct).1
  rw [hmap]
  exact hcn

/-- **A NAME OFF THE AUXILIARY NAMES IS FOUND ALIKE** at the scratch
constructors' environment and at the restored one (`RestoreAgree.leafSome`):
a declared member is stored at both with its own constant, a declared
member's constructor at both (the restore keeps the name and the level
parameters), and everything else is the pre-block environment's. -/
theorem NestedTailIn.leafSome {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas) :
    ∀ n, n ∉ (ConLeche.restoreTbl p st).auxNames → ∀ ci : ConstantInfo,
      (ENVA).find? n = some ci → ∃ ci' : ConstantInfo, (ENV₂).find? n = some ci' ∧
        ci'.toConstantVal.levelParams = ci.toConstantVal.levelParams := by
  intro n hn ci hfind
  rcases I.nameCases n hn with ⟨t, f, htk, hf, rfl⟩ | ⟨mm, j, cA, hmm, hj, hcA, rfl⟩ | ⟨hnf, hnc⟩
  · obtain rfl : ci = .indInfo f.cvTa {} :=
      Option.some.inj (hfind.symm.trans (S.memberStored t f hf).find)
    exact ⟨_, I.out.stage.findM t f htk hf, rfl⟩
  · obtain rfl : ci = .ctorInfo cA.1 b.nP cA.2 :=
      Option.some.inj (hfind.symm.trans
        (ConLeche.consMutualCtors_find?_self I.ctorsANodup hcA))
    have hjR : j < (ctorsR.getD mm []).length := by rw [I.out.stage.ctorsLen mm hmm]; exact hj
    obtain ⟨c, hc⟩ : ∃ c, (ctorsR.getD mm [])[j]? = some c :=
      ⟨_, List.getElem?_eq_getElem hjR⟩
    obtain ⟨cAx, hcAx, hname⟩ := I.ctorsRName (I.ctorsRget hmm) hc
    have hxe : cAx = cA := Option.some.inj (hcAx.symm.trans hcA)
    rw [hxe] at hname
    obtain ⟨-, -, -, -, -, hBC⟩ := I.out.stage.ctorFacts mm j c hmm hc
    obtain ⟨hfindR, hlpsR, -⟩ := hBC
    rw [← hname]
    refine ⟨_, hfindR, ?_⟩
    show c.1.levelParams = cA.1.levelParams
    obtain ⟨hlenA, hnamesA⟩ :=
      ctorsA_names_of I.out.ctors (ConLeche.checkMutualCore_inv I.haux).2.1
    obtain ⟨ct, hct⟩ : ∃ ct, b.ctors[b.ownOffset mm + j]? = some ct :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hlenA]; exact (List.getElem?_eq_some_iff.mp hcA).1)⟩
    rw [hlpsR, (hnamesA _ cA ct hcA hct).2.2]
  · rw [ConLeche.consMutualCtors_find?_of_ne (fun c hc => hnc c hc),
      consMutualFormers_find?_of_ne ?_] at hfind
    · exact ⟨ci, I.out.stage.find (I.findPre1 hfind), rfl⟩
    · intro g hg
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hg
      exact hnf t g ht

/-- **A NAME ABSENT FROM THE SCRATCH ENVIRONMENT IS ABSENT FROM THE
RESTORED ONE** (`RestoreAgree.leafNone`), off the auxiliary names. -/
theorem NestedTailIn.leafNone {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas) :
    ∀ n, n ∉ (ConLeche.restoreTbl p st).auxNames → (ENVA).find? n = none →
      (ENV₂).find? n = none := by
  intro n hn hfind
  rcases I.nameCases n hn with ⟨t, f, htk, hf, rfl⟩ | ⟨mm, j, cA, hmm, hj, hcA, rfl⟩ | ⟨hnf, hnc⟩
  · rw [(S.memberStored t f hf).find] at hfind; exact nomatch hfind
  · rw [ConLeche.consMutualCtors_find?_self I.ctorsANodup hcA] at hfind
    exact nomatch hfind
  · rw [ConLeche.consMutualCtors_find?_of_ne (fun c hc => hnc c hc),
      consMutualFormers_find?_of_ne ?_] at hfind
    · rw [ConLeche.consNestedCtors_find?_of_ne ?_, consMutualFormers_find?_of_ne ?_]
      · exact hfind
      · intro g hg
        obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_take hg)
        exact hnf t g ht
      · intro c hc
        obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
        obtain ⟨mm, hmm⟩ := List.getElem?_of_mem hl
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hcl
        obtain ⟨cA, hcA, hname⟩ := I.ctorsRName hmm hj
        rw [hname]
        exact hnc cA (List.mem_of_getElem? hcA)
    · intro g hg
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hg
      exact hnf t g ht

/-- **THE LEAVES AGREE OFF THE AUXILIARY NAMES** (`RestoreAgree.leaf`):
a declared member's leaf is the block's own `mutMemberLeaf` at both
models, a declared member's constructor's the SAME tagged tower (the
member-local tag `j` on both sides), and off the block both models are
the pre-block model's. -/
theorem NestedTailIn.leafAcval {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    :
    ∀ n, n ∉ (ConLeche.restoreTbl p st).auxNames →
      mpA.base2.acval n = mp₂.base2.acval n := by
  intro n hn
  rcases I.nameCases n hn with ⟨t, f, htk, hf, rfl⟩ | ⟨mm, j, cA, hmm, hj, hcA, rfl⟩ | ⟨hnf, hnc⟩
  · rw [S.leafM t f hf, I.out.facts.leaf t f hf, I.out.stage.leafM t f htk hf]
  · have hjR : j < (ctorsR.getD mm []).length := by rw [I.out.stage.ctorsLen mm hmm]; exact hj
    obtain ⟨c, hc⟩ : ∃ c, (ctorsR.getD mm [])[j]? = some c :=
      ⟨_, List.getElem?_eq_getElem hjR⟩
    obtain ⟨cAx, hcAx, hname⟩ := I.ctorsRName (I.ctorsRget hmm) hc
    have hxe : cAx = cA := Option.some.inj (hcAx.symm.trans hcA)
    rw [hxe] at hname
    obtain ⟨-, -, -, hleafR, -, -⟩ := I.out.stage.ctorFacts mm j c hmm hc
    obtain ⟨-, -, hleafA⟩ := S.cons _ cA hcA
    obtain ⟨ct, hct, hmember, -⟩ := I.ctorsRMember (I.ctorsRget hmm) hc
    have hmemF : mutMemF b (b.ownOffset mm + j) = mm := by
      show (b.ctors.getD (b.ownOffset mm + j) default).member = mm
      rw [List.getD_eq_getElem?_getD, hct]
      exact hmember
    funext ψ
    rw [hleafA ψ, ← hname, hleafR ψ, hmemF, Nat.add_sub_cancel_left]
  · rw [S.agree n (fun cA hcA hne => hnc cA hcA hne.symm),
      I.out.facts.off n (fun t g ht hne => hnf t g ht hne.symm),
      I.out.stage.agreeR n
        (fun c hc heq => by
          obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
          obtain ⟨mm, hmm⟩ := List.getElem?_of_mem hl
          obtain ⟨j, hj⟩ := List.getElem?_of_mem hcl
          obtain ⟨cA, hcA, hname⟩ := I.ctorsRName hmm hj
          exact hnc cA (List.mem_of_getElem? hcA) (by rw [← hname, ← heq]))
        (fun t g ht hg heq => hnf t g hg heq.symm)]

/-! ### The recursor map's clauses -/

omit I in
/-- A key no entry carries is a `lookup` miss. -/
private theorem lookupNone_of {β : Type} {a : Name} :
    ∀ {l : List (Name × β)}, (∀ q ∈ l, q.1 ≠ a) → l.lookup a = none
  | [], _ => rfl
  | (k, v) :: l, h => by
    rw [List.lookup_cons]
    have hk : ¬ (a == k) = true := fun hb => h (k, v) List.mem_cons_self (beq_iff_eq.mp hb).symm
    rw [Bool.not_eq_true] at hk
    rw [hk]
    exact lookupNone_of fun q hq => h q (List.mem_cons_of_mem _ hq)

omit I in
/-- **THE RECURSOR MAP DECLINES OFF THE COPIES' RECURSOR NAMES**: its
keys are the auxiliary names with `rec` appended. -/
theorem recMapNone_of {n : Name} (hshape : ∀ q' ∈ st.pins, n ≠ q'.aux.str "rec") :
    (ConLeche.restoreTbl p st).recMap.lookup n = none := by
  simp only [ConLeche.restoreTbl]
  refine lookupNone_of ?_
  intro pr hpr
  obtain ⟨qj, hqj, rfl⟩ := List.mem_map.mp hpr
  obtain ⟨q₀, j⟩ := qj
  exact fun hc => hshape q₀ (List.fst_mem_of_mem_zipIdx hqj) hc.symm

/-- A copy's constructor name is one of the auxiliary block's
constructor names. -/
theorem NestedTailIn.ctorKeyName {q jc : Nat} {t : AuxType} {c : Name × Expr × Nat}
    (ht : st.types[p.k + q]? = some t) (hc : t.ctors[jc]? = some c) :
    c.1 ∈ b.ctors.map (·.cv.name) :=
  List.mem_map.mpr ⟨_, List.mem_of_getElem?
    (ConLeche.auxBlock_ctors_getElem? I.hb I.out.grouped (p.k + q) jc t c ht hc), rfl⟩

/-- **A TABLE KEY IS NO COPY'S RECURSOR** (`RestoreAgree.keyNotRec`): a
pin's key is a member name of the auxiliary block, a constructor pin's
one of its constructor names, and `blockNames.Nodup` keeps both off the
recursor names. -/
theorem NestedTailIn.keyNotRec : ∀ n, (ConLeche.restoreTbl p st).IsKey n →
    (ConLeche.restoreTbl p st).recMap.lookup n = none := by
  have hnd : b.blockNames.Nodup := I.out.nodup
  rw [ConLeche.MutualBlock.blockNames] at hnd
  intro n hkey
  rcases hkey with hp | hc
  · obtain ⟨pin, hpin⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨qn, hqnm, rfl, -⟩ := ConLeche.rk_restoreTbl_pins_lookup_inv hpin
    obtain ⟨q, hqn⟩ := List.getElem?_of_mem hqnm
    exact ConLeche.restoreTbl_recMap_lookup_aux' I.hfA I.helim I.hb I.haux hqn
  · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨n', pin, newName⟩ := z
    obtain rfl : n' = n := by
      have := List.find?_some hz
      simpa using this
    obtain ⟨q, qn, t, jc, c, hqn, ht, hcj, hn, -, -⟩ := ConLeche.restoreTbl_ctorPins_find? hz
    refine recMapNone_of fun q' hq' hce => ?_
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq'
    refine (List.nodup_append.mp hnd).2.2 _
      (List.mem_append_right _ (hn ▸ I.ctorKeyName ht hcj)) _ (I.pinAuxMem hj).2 ?_
    rw [← hce]

/-- **A COPY'S RECURSOR NAME IS ABSENT FROM THE SCRATCH CONSTRUCTORS'
ENVIRONMENT**: it is fresh before the block (`copiesFresh`) and is
neither a member name nor a constructor name of the auxiliary block. -/
theorem NestedTailIn.recKeyNone {n n' : Name}
    (hr : (ConLeche.restoreTbl p st).recMap.lookup n = some n') : (ENVA).find? n = none := by
  have hnd : b.blockNames.Nodup := I.out.nodup
  rw [ConLeche.MutualBlock.blockNames] at hnd
  -- the key is a copy's recursor name
  have hkey : ∃ (q : Nat) (qn : NestedPin), st.pins[q]? = some qn ∧ n = qn.aux.str "rec" := by
    rcases Classical.em (∃ (q : Nat) (qn : NestedPin),
        st.pins[q]? = some qn ∧ n = qn.aux.str "rec") with h | h
    · exact h
    · exfalso
      have hnone : (ConLeche.restoreTbl p st).recMap.lookup n = none :=
        recMapNone_of (fun q' hq' hce => by
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq'
          exact h ⟨j, q', hj, hce⟩)
      rw [hnone] at hr
      exact nomatch hr
  obtain ⟨q, qn, hqn, rfl⟩ := hkey
  have hrecMem := (I.pinAuxMem hqn).2
  have hnfms : ∀ g ∈ fms, g.cvTa.name ≠ qn.aux.str "rec" := by
    intro g hg hge
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hg
    have hmem : g.cvTa.name ∈ b.memberNames := by
      rw [← I.out.facts.names]
      exact List.mem_map_of_mem hg
    exact (List.nodup_append.mp hnd).2.2 _ (List.mem_append_left _ hmem) _ hrecMem hge
  have hnctors : ∀ cA ∈ ctorsA, cA.1.name ≠ qn.aux.str "rec" := by
    intro cA hcA hce
    obtain ⟨J, hJ⟩ := List.getElem?_of_mem hcA
    obtain ⟨hlenA, hnamesA⟩ :=
      ctorsA_names_of I.out.ctors (ConLeche.checkMutualCore_inv I.haux).2.1
    obtain ⟨ct, hct⟩ : ∃ ct, b.ctors[J]? = some ct :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hlenA]; exact (List.getElem?_eq_some_iff.mp hJ).1)⟩
    have hmem : cA.1.name ∈ b.ctors.map (·.cv.name) := by
      rw [(hnamesA J cA ct hJ hct).1]
      exact List.mem_map.mpr ⟨ct, List.mem_of_getElem? hct, rfl⟩
    exact (List.nodup_append.mp hnd).2.2 _ (List.mem_append_right _ hmem) _ hrecMem hce
  rw [ConLeche.consMutualCtors_find?_of_ne hnctors, consMutualFormers_find?_of_ne hnfms]
  exact (ConLeche.rk_restoreTbl_auxNames_fresh I.out.nodup I.aligned I.hb I.hfresh _
    (by
      simp only [ConLeche.restoreTbl]
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨qn, List.mem_of_getElem? hqn, rfl⟩))).1

omit I in
/-- An answered key is an entry. -/
private theorem lookupMem_of {β : Type} {a : Name} {v : β} :
    ∀ {l : List (Name × β)}, l.lookup a = some v → (a, v) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k, w) :: l, h => by
    rw [List.lookup_cons] at h
    split at h
    · rename_i he
      rw [beq_iff_eq] at he
      subst he
      rw [Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookupMem_of h)

/-- **THE RESTORED MIMIC RECURSOR NAMES ARE FRESH** at the restored
constructors' environment: the restore checked every one of them
through the pre-annotated front door, whose first guard is freshness
(`restoreRecTys_door`). -/
theorem NestedTailIn.mimicRecFresh {j : Nat} (hj : j < pinsS.length) :
    (ENV₂).find? (p.mimicRecName j) = none := by
  have hnum : st.pins.length = p.numNested := I.hcount
  have hjn : j < p.numNested := by rw [← hnum, ← I.out.stage.pinsLen]; exact hj
  obtain ⟨o, ho⟩ : ∃ o, cvRns[j]? = some o :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.lenN]; exact hj)⟩
  have hnm : ((List.range p.numNested).map p.mimicRecName)[j]? = some (p.mimicRecName j) := by
    rw [List.getElem?_map, List.getElem?_range hjn]
    rfl
  have h := (ConLeche.restoreRecTys_door I.hrn j (p.mimicRecName j) o hnm ho).2.1
  rw [I.henv] at h
  exact h

/-! ### B2 — `RestoreAgree` at the tail -/

/-- **THE WALK'S LEAF AGREEMENTS AT THE TAIL** (PLAN-M7 §1e B2):
`RestoreAgree` at the restore table of the elimination, the scratch
install's model `mpA` and the restored one `mp₂` — the parameter count
(`tblNP`), the leaves off the auxiliary names (`leafSome`, `leafNone`,
`leafAcval`), the auxiliary names' absence from the restored
environment (`auxFresh`), the recursor map's two clauses (its keys are
absent from the scratch constructors' environment, its values fresh at
the restored one), a key's distinctness from a recursor name
(`keyNotRec`), THE PIN IDENTITY (`pinArm`, `nestedIdent_of`) and THE
COPY CONSTRUCTOR'S AGREEMENT (`ctorArm`, T2). -/
theorem NestedTailIn.restoreAgree {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (ψ : Name → Nat) :
    RestoreAgree (V := V) (ConLeche.restoreTbl p st) b.lps (nestedArity p st pinsS)
      mpA.base2.acval mp₂.base2.acval (ENVA) (ENV₂) ψ b.nP ((D).params ψ) := by
  refine
    { nPEq := I.tblNP
      leafSome := I.leafSome S
      leafNone := I.leafNone S
      leaf := I.leafAcval S
      auxFresh := I.auxFresh
      recKey := ?_
      recNone := ?_
      keyNotRec := I.keyNotRec
      pin := I.pinArm S ψ
      ctor := I.ctorArm S hnames hctorsJ ψ }
  · intro n n' hr ci hfind
    rw [I.recKeyNone hr] at hfind
    exact nomatch hfind
  · intro n n' hr _hfind
    have hmem := lookupMem_of hr
    simp only [ConLeche.restoreTbl, List.mem_map] at hmem
    obtain ⟨⟨q', jq⟩, hqj, hpair⟩ := hmem
    obtain ⟨-, hn'⟩ := Prod.mk.inj hpair
    have hjl : jq < st.pins.length := by
      have := List.mk_mem_zipIdx_iff_getElem?.mp hqj
      exact (List.getElem?_eq_some_iff.mp this).1
    rw [← hn']
    exact I.mimicRecFresh (by rw [I.out.stage.pinsLen]; exact hjl)

/-! ### The readings, from the frames -/

/-- **THE READINGS AT THE TAIL** (PLAN-M7 §1e): `NestedTailIn.readings`
with its one open premise supplied — the thirteen bookkeeping clauses
of `NestedRecReadings` are the run's (`NestedRecTypes.lean`), the
fourteenth is `hfr`, the readings' FRAMES.  Consumer:
`nestedRecReadingsOf_of` → `nestedTailModeled_of`. -/
theorem NestedTailIn.readingsOf
    (hfr : ∀ (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (concM : Nat → AnnotTerm),
      (∀ (c : Nat) (ψ : Name → Nat), c < (D).kT →
        denoteMeta mp₂.base2.acval (ENV₂) ψ 0 (nestedRecCvAt p.k cvRms cvRns c).type
          = some (mkPisAV (rdsM c ψ) (concM c))) →
      (∀ (c : Nat) (ψ : Name → Nat), c < (D).kT →
        (rdsM c ψ).length = (D).nP + (D).kT + (D).nCtorsT (PC) + (D).nIdxT c + 1) →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < (D).kT →
        (D).ReadingFramesT (PC) ψ (b.elimLevel.eval ψ) (rdsM c ψ) (concM c) c ρ) :
    ∃ (s : (Name → Nat) → Nat) (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (concM : Nat → AnnotTerm),
      NestedRecReadings mp₂.base2 (D) (PC) cvRms cvRns b.rlps b.elimLevel s rdsM concM :=
  I.readings hfr

end Run

/-! ## The named fact and its consumer -/

/-- **THE READINGS' FRAMES AT THE RUN** (DESIGN §U.25 (e) 2, second
half; PLAN-M7 §1e): at every tail input and every reading of the
`k + nPins` restored recursor types characterised by the two premises
`NestedTailIn.readings` supplies (the type's reading and its length),
every fitting spine decomposes into the block's frame with the frame's
motives and minors typed semantically (`ReadingFramesT`).

What remains of §1e: the transfer along the walk's reading law
(`denoteMeta_restoreWalk` at `NestedTailIn.restoreAgree`, this file's
B2) to the SCRATCH reading of the same recursor, whose frame inversion
is the mutual `IsBlockModels.spineFit_recData_inv` at the auxiliary
block's own block model, and the fibre kit (`NestedRecFibre.lean`) to
carry the frame's semantic clauses back to the composed model. -/
@[expose] def NestedRecFramesOf (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  ∀ {env : Env} (mp : EnvModelM V μ env) (p : NestedParts) (envOut : Env) (st : ElimState)
    (b : MutualBlock) (envAux : Env) (stored : List AuxStored)
    (ctorsR : List (List (ConstantVal × Nat × Nat))) (cvRms cvRns : List ConstantVal)
    (rulesM rulesN : List (List RecRule)) (fmsA ctorsA₀ : List ConstantVal)
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
    (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (xFvsR : Nat → Nat → List Expr)
    (pinsS : List PinSyn)
    (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
      (ConLeche.consMutualFormers (fms.take p.k) env))),
    NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀
      fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR
      xFvsR pinsS mp₂ →
    ∀ (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (concM : Nat → AnnotTerm),
      (∀ (c : Nat) (ψ : Name → Nat),
        c < (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS).kT →
        denoteMeta mp₂.base2.acval
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consMutualFormers (fms.take p.k) env)) ψ 0
            (nestedRecCvAt p.k cvRms cvRns c).type
          = some (mkPisAV (rdsM c ψ) (concM c))) →
      (∀ (c : Nat) (ψ : Name → Nat),
        c < (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS).kT →
        (rdsM c ψ).length =
          (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
            xrestF eissF tssF ctorsR dsR xFvsR pinsS).nP +
          (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
            xrestF eissF tssF ctorsR dsR xFvsR pinsS).kT +
          (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
            xrestF eissF tssF ctorsR dsR xFvsR pinsS).nCtorsT
            (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF) +
          (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
            xrestF eissF tssF ctorsR dsR xFvsR pinsS).nIdxT c + 1) →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat),
        c < (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS).kT →
        (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS).ReadingFramesT
          (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF) ψ (b.elimLevel.eval ψ)
          (rdsM c ψ) (concM c) c ρ

/-- **THE READINGS AT THE RUN, FROM THE FRAMES**: `NestedRecReadingsOf`
— the first of `nestedTailModeled_of`'s three named facts — is
`NestedTailIn.readings` at every tail input, its one premise the
frames. -/
theorem nestedRecReadingsOf_of {F : Nat} (hfr : NestedRecFramesOf V μ F) :
    NestedRecReadingsOf V μ F := fun mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM
    rulesN fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
    xrestF eissF tssF dsR xFvsR pinsS mp₂ I =>
  I.readingsOf (hfr mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀
    fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR
    xFvsR pinsS mp₂ I)

/-- **THE CONSUMER** (consumer-first): the frames feed the recursors'
stage verbatim — `nestedTailModeled_of` at `nestedRecReadingsOf_of`'s
output and the stage's other two named facts. -/
theorem nestedTailModeled_of_frames {F : Nat} (hfr : NestedRecFramesOf V μ F)
    (heqs : NestedRecEqsOf V μ F) (hst : NestedRecsStored V μ F) : NestedTailModeled V μ F :=
  nestedTailModeled_of (nestedRecReadingsOf_of hfr) heqs hst


end ConLeche.Model
