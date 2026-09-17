module

public import ConLeche.Model.Inductives.NestedRecCtor
public import ConLeche.Model.Inductives.NestedRecTypes
import ConLeche.Model.Inductives.NestedRecFibre
import ConLeche.Model.Inductives.MutualFormersKit
import ConLeche.Model.Inductives.NestedTransfer
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedRestoreTbl
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

end Run

end ConLeche.Model
