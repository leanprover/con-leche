module

public import ConLeche.Model.Inductives.CopyCtorRun
import ConLeche.Verify.Inductives.NestedCtors
import ConLeche.Verify.Inductives.NestedFields
import ConLeche.Verify.Inductives.NestedLeaves
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InstLevels

public section

/-!
# The copies' constructors, READ off the walk (task #279 M-B′ step 3o, DESIGN §M.41)

`CopyCtors.lean` states the record `CopyCtorAsRead` — a copy's
constructor read through the container's, field by field — and
`CopyCtorRun.lean` closes ψ under it as a premise (`CopyCtorsRead`).
`Verify/Inductives/NestedFields.lean` gives the SYNTACTIC half
(`copyCtorFields_of_walk`: every field of a walked copy constructor is
unfired or a fire at the top).  This module is the MODEL half: the
readings of the instantiated container constructor at the block's
parameter frame, and the record's clauses from the walk's per-field
disjunction.

* **`ctor_peel`** — the constructor twin of `former_peel`
  (`CopyPins.lean`): the container's stored constructor, level
  instantiated and `instPis`'d at the pin's annotated components, reads
  at the block's parameter depth as `instSeq DsA` of the container's
  own reading below its parameters (`CtorDataI.read`,
  `denoteMeta_instLevels`, `denoteMeta_instPisAt_peel`);
* **`ctorInst_fields`** — that reading opened at the copy's field
  variables (`denoteMeta_openPis`): field `i` reads as
  `instSeq DsA (nPJ - 1 + i)` of the container's field `i`, the residual
  as `instSeq DsA (nPJ - 1 + nF)` of the container's body.

What the record's clauses are then read from is stated in §M.41 and
carried below as `CopyCtorWalkFacts`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType NestedPin ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The constructor, peeled at the pin -/

/-- **The container's constructor, peeled at the pin**: at the level
instantiation the pin names, `instPis` of the stored constructor type at
the pin's annotated components reads (at the block's parameter depth)
as the container's field telescope and body instantiated at the
components' readings — `former_peel`'s constructor twin.  The
container's data are at the pin's assignment `ψ'`, which agrees with
the level substitution on the constructor's level parameters
(`CtorDataI.params`) and reads the family's leaf alike (`hacv`). -/
theorem ctor_peel {μ : CheckMode} {env : Env} (mp : EnvModelM V μ env) {ψ ψ' : Name → Nat}
    {T : Name} {lps : List Name} {cvC : ConstantVal} {nPJ nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    (hfind : env.find? cvC.name = some (.ctorInfo cvC nPJ nF)) (hlpsC : cvC.levelParams = lps)
    (hc : CtorDataI mp.base2 T lps cvC nPJ nF nIdx resSort isProp large idxArgs ds Es srcs)
    {lvls : List Level} (hag : ∀ q ∈ lps, ψ' q = Level.substFn ψ lps lvls q)
    (hacv : mp.base2.acval T ψ' = mp.base2.acval T (Level.substFn ψ lps lvls))
    {nP : Nat} {argsA : List Expr} {DsA : List AnnotTerm} (hlenA : argsA.length = nPJ)
    (hargs : ∀ a ∈ argsA, Expr.WScoped nP a ∧ a.looseBVarsBounded 0 = true)
    (hsp : DenoteMetaSpine mp.base2.acval env ψ nP argsA DsA)
    {rest : Expr}
    (hrest : Expr.instPis (cvC.type.instantiateLevelParams lps lvls) argsA = some rest) :
    denoteMeta mp.base2.acval env ψ nP rest
      = some (ConLeche.Model.AnnotTerm.instSeq DsA (nPJ - 1)
          (mkPisAV ((ds ψ').drop nPJ) (ctorBodyAVI mp.base2 T nPJ nF ψ' (Es ψ')))) := by
  have hwf := mp.base2.wf _ (ConLeche.find?_mem hfind)
  have hnf : (cvC.type.instantiateLevelParams lps lvls).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwf.1
  have hb : (cvC.type.instantiateLevelParams lps lvls).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
  -- the reading at depth 0: the container's own, at the pin's assignment
  have hagree : ∀ q ∈ cvC.levelParams, Level.substFn ψ lps lvls q = ψ' q := by
    rw [hlpsC]; exact fun q hq => (hag q hq).symm
  obtain ⟨hds, hEs⟩ := hc.params _ _ hagree
  have hread0 : denoteMeta mp.base2.acval env ψ 0 (cvC.type.instantiateLevelParams lps lvls)
      = some (mkPisAV (ds ψ') (ctorBodyAVI mp.base2 T nPJ nF ψ' (Es ψ'))) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core mp.base2) ψ, hc.read, hds, hEs]
    unfold ctorBodyAVI
    rw [hacv]
  have hreadN : denoteMeta mp.base2.acval env ψ nP (cvC.type.instantiateLevelParams lps lvls)
      = some (mkPisAV (ds ψ') (ctorBodyAVI mp.base2 T nPJ nF ψ' (Es ψ'))) :=
    denoteMeta_depth_of_closed mp.base2.acval_closed hnf
      (fun k => denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed hnf hb hread0 1 k)
      hread0 nP
  -- the peel
  obtain ⟨dsI, hpr⟩ := instPisAt_of_instPis argsA hrest
  obtain ⟨restA, hrestA, hpeel⟩ := denoteMeta_instPisAt_peel mp.base2.acval_closed
    (acval_inst_self mp.base2) argsA hpr (Expr.WScoped.of_not_hasFvar hnf) hargs hreadN hsp
  have hlenD : DsA.length = nPJ := by rw [← DenoteMetaSpine.length hsp, hlenA]
  have hle : nPJ ≤ (ds ψ').length := by rw [hc.len ψ']; omega
  have htele : PiTeleAV nPJ (mkPisAV (ds ψ') (ctorBodyAVI mp.base2 T nPJ nF ψ' (Es ψ')))
      ((((ds ψ').take nPJ).map (·.2.2)).reverse)
      (mkPisAV ((ds ψ').drop nPJ) (ctorBodyAVI mp.base2 T nPJ nF ψ' (Es ψ'))) :=
    piTeleAV_of_stripPisAV (stripPisAV_mkPisAV_take nPJ (ds ψ') _ hle)
  rw [peelPis_of_piTeleAV nPJ htele hlenD] at hpeel
  rw [hrestA, Option.some.inj hpeel]

/-! ## The instantiated constructor's fields, opened -/

/-- **The instantiated constructor's fields read as the container's
substituted**: the peeled reading (`ctor_peel`'s shape) opened at the
copy's `nF` field variables (`denoteMeta_openPis`) gives, at field `i`,
`instSeq DsA (nPJ - 1 + i)` of the container's field `i` entry, and at
the residual `instSeq DsA (nPJ - 1 + nF)` of the container's body. -/
theorem ctorInst_fields {μ : CheckMode} {env : Env} (mp : EnvModelM V μ env) {ψ : Name → Nat}
    {nP nPJ nF : Nat} {DsA : List AnnotTerm} (hlenD : DsA.length = nPJ)
    {Γ : List (Nat × Nat × AnnotTerm)} (hΓ : Γ.length = nF) {B : AnnotTerm} {rest : Expr}
    (hread : denoteMeta mp.base2.acval env ψ nP rest
      = some (ConLeche.Model.AnnotTerm.instSeq DsA (nPJ - 1) (mkPisAV Γ B)))
    {xFvs : List Expr} {xrest : Expr} (hop : ConLeche.openPisAtFvars nF rest nP = some (xFvs, xrest)) :
    (∀ (i : Nat) (x : Expr), xFvs[i]? = some x →
      denoteMeta mp.base2.acval env ψ (nP + i) x.fvarTypeD
        = some (ConLeche.Model.AnnotTerm.instSeq DsA (nPJ - 1 + i) (Γ.getD i default).2.2)) ∧
    denoteMeta mp.base2.acval env ψ (nP + nF) xrest
      = some (ConLeche.Model.AnnotTerm.instSeq DsA (nPJ - 1 + nF) B) := by
  have hle : DsA.length ≤ nPJ - 1 + 1 := by omega
  rw [instSeq_mkPisAV DsA (nPJ - 1) Γ B hle] at hread
  obtain ⟨pps, b, hst, hb, hlen, hbind⟩ := denoteMeta_openPis nF hop hread
  have hlenI : nF ≤ (instSeqDoms DsA (nPJ - 1) Γ).length := by
    rw [instSeqDoms_length, hΓ]; exact Nat.le_refl _
  rw [stripPisAV_mkPisAV_take nF _ _ hlenI] at hst
  simp only [Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨hpps, hbE⟩ := hst
  have hdrop : (instSeqDoms DsA (nPJ - 1) Γ).drop nF = [] := by
    rw [List.drop_eq_nil_iff, instSeqDoms_length, hΓ]; exact Nat.le_refl _
  rw [hdrop] at hbE
  simp only [mkPisAV] at hbE
  refine ⟨fun i x hx => ?_, by rw [hb, ← hbE, hΓ]⟩
  obtain ⟨p, hp, -, hpd⟩ := hbind i x hx
  rw [hpd]
  congr 1
  have hi : i < nF := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hp).1
  rw [← hpps, List.getElem?_take_of_lt hi, instSeqDoms_getElem?] at hp
  have hiΓ : i < Γ.length := by rw [hΓ]; exact hi
  rw [List.getElem?_eq_getElem hiΓ, Option.map_some, Option.some.injEq] at hp
  rw [← hp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiΓ]
  rfl

end ConLeche.Model
