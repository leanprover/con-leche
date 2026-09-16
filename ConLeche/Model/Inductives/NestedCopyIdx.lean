module

public import ConLeche.Model.Inductives.NestedPins
import ConLeche.Model.Levels
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitErase
import ConLeche.Model.Steps.TowerKit
import ConLeche.Model.Inductives.StructRead
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.Inductives.NestedCopyTele
import ConLeche.Verify.Inductives.NestedCopySort
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.EraseAnnots
import ConLeche.Verify.InstLevels
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.BridgeWfImp
import ConLeche.Semantics.Tower.FixWire
public section

/-!
# The copies' index telescopes (task #315 L-B, DESIGN §U.23)

`NestedPinsIdent` (`NestedPins.lean`) asks three facts of every pin
group: `idx` — the copy's index telescope is the container's
instantiated at the pin — `shape` — `CopyCtorShape` at every copy
constructor (lane L-B) — and `entry` — the entries at the auxiliary
carrier (the whole block's theorem, lane L-E, DESIGN §U.36).  This
module discharges `idx` from the run and names the other two as the
residuals `NestedPinsShape` and `NestedPinsEntry`; `nestedPinsIdent_of`
is the consumer.

The chain for `idx`: K.28 certifies the copy's former as `mkCopy`'s
output at the recorded source, i.e. `closeTelescope pbs 0 tyI` with
`tyI = instPis (instantiateLevelParams J.lps lvls J.type) Ds`
(`mkCopy_type`); `closeTelescope` over the first former's binders is
that former's own telescope over the bulk abstraction
(`closeTelescope_eq_mkPisB`), whose opening is `instSeq` of the openers
(`openPisAtFvars_mkPisB`) and reads as `tyI` (`eraseAnnots_openAbstract`
+ the erasure law); `tyI` reads as the container's type read at the
pin's level assignment (`denoteMeta_instLevels`, `denoteMeta_lift`) and
peeled along the components' readings (`denoteMeta_instPisAt_peel`) —
and a Π-tower's peel along the parameters IS the tower over the index
data instantiated at the components (`peelPis_mkPisAV_sort`, the
`instAll` order).  The two `FormerData` (the copy's at the pre-block
model crossed to the prefix model; the container's at the stored
constant) pin both ends.  The components' scope is K.30's
(`NestedPinsRun.scoped`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock ElimState NestedPin IndCaps ContainerInfo ContainerMember AuxStored
  fueledOps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Kit: a Π-tower's data under a peel -/

/-- A telescope's binder data instantiated at `ds`, entry `m` at cut
`c + m` (`instTele` on the triples). -/
def instTeleP (ds : List AnnotTerm) :
    Nat → List (Nat × Nat × AnnotTerm) → List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | c, d :: pps => (d.1, d.2.1, AnnotTerm.instAll ds c d.2.2) :: instTeleP ds (c + 1) pps

theorem instTeleP_map (ds : List AnnotTerm) :
    ∀ (c : Nat) (pps : List (Nat × Nat × AnnotTerm)),
      (instTeleP ds c pps).map (·.2.2) = instTele ds c (pps.map (·.2.2))
  | _, [] => rfl
  | c, d :: pps => by
    simp only [instTeleP, instTele, List.map_cons, instTeleP_map ds (c + 1) pps]

theorem instTeleP_nil : ∀ (c : Nat) (pps : List (Nat × Nat × AnnotTerm)), instTeleP [] c pps = pps
  | _, [] => rfl
  | c, d :: pps => by simp only [instTeleP, AnnotTerm.instAll, instTeleP_nil (c + 1) pps]

/-- One substitution along the binder data, entry `m` at cut `k + m`. -/
def instDomsAt (a : AnnotTerm) :
    Nat → List (Nat × Nat × AnnotTerm) → List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | k, d :: pps => (d.1, d.2.1, d.2.2.inst a k) :: instDomsAt a (k + 1) pps

theorem instDomsAt_length (a : AnnotTerm) :
    ∀ (k : Nat) (pps : List (Nat × Nat × AnnotTerm)), (instDomsAt a k pps).length = pps.length
  | _, [] => rfl
  | k, _ :: pps => by simp only [instDomsAt, List.length_cons, instDomsAt_length a (k + 1) pps]

theorem instDomsAt_append (a : AnnotTerm) :
    ∀ (k : Nat) (l₁ l₂ : List (Nat × Nat × AnnotTerm)),
      instDomsAt a k (l₁ ++ l₂) = instDomsAt a k l₁ ++ instDomsAt a (k + l₁.length) l₂
  | _, [], _ => by simp [instDomsAt]
  | k, d :: l₁, l₂ => by
    simp only [List.cons_append, instDomsAt, instDomsAt_append a (k + 1) l₁ l₂, List.length_cons]
    rw [show k + 1 + l₁.length = k + (l₁.length + 1) from by omega]

/-- A Π-tower under `inst`: the binder data at their cuts, the
conclusion under the binders. -/
theorem inst_mkPisAV (a : AnnotTerm) :
    ∀ (pps : List (Nat × Nat × AnnotTerm)) (C : AnnotTerm) (k : Nat),
      (mkPisAV pps C).inst a k = mkPisAV (instDomsAt a k pps) (C.inst a (k + pps.length))
  | [], C, k => by simp [mkPisAV, instDomsAt]
  | d :: pps, C, k => by
    simp only [mkPisAV, instDomsAt, AnnotTerm.inst_pi, inst_mkPisAV a pps C (k + 1),
      List.length_cons]
    rw [show k + 1 + pps.length = k + (pps.length + 1) from by omega]

/-- The substitution at the highest cut is `instAll`'s first step. -/
theorem instTeleP_instDomsAt (v : AnnotTerm) (vs : List AnnotTerm) :
    ∀ (c : Nat) (pps : List (Nat × Nat × AnnotTerm)),
      instTeleP vs c (instDomsAt v (c + vs.length) pps) = instTeleP (v :: vs) c pps
  | _, [] => rfl
  | c, d :: pps => by
    simp only [instTeleP, instDomsAt, AnnotTerm.instAll]
    rw [show c + vs.length + 1 = c + 1 + vs.length from by omega,
      instTeleP_instDomsAt v vs (c + 1) pps]

/-- **The peel of a Π-tower ending in a sort along a spine of the
parameters' length** is the tower over the remaining data instantiated
at the spine from cut `0` — `instPis`'s order (the outermost parameter
first, at the highest cut) is `instAll`'s. -/
theorem peelPis_mkPisAV_sort :
    ∀ (ps I : List (Nat × Nat × AnnotTerm)) (vs : List AnnotTerm) (s : Nat),
      vs.length = ps.length →
      AnnotTerm.peelPis (mkPisAV (ps ++ I) (.sort s)) vs
        = some (mkPisAV (instTeleP vs 0 I) (.sort s))
  | [], I, [], s, _ => by
    simp only [List.nil_append, AnnotTerm.peelPis, instTeleP_nil]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | p :: ps, I, v :: vs, s, h => by
    simp only [List.cons_append, mkPisAV, AnnotTerm.peelPis]
    rw [inst_mkPisAV, instDomsAt_append, AnnotTerm.inst_sort]
    have hl : vs.length = ps.length := by simpa using h
    have hlen : vs.length = (instDomsAt v 0 ps).length := by rw [instDomsAt_length, hl]
    rw [peelPis_mkPisAV_sort _ _ vs s hlen, Nat.zero_add, ← hl, ← Nat.zero_add vs.length,
      instTeleP_instDomsAt]

/-- Two Π-towers ending in sorts agree iff their data and sorts do. -/
theorem mkPisAV_sort_inj :
    ∀ {l₁ l₂ : List (Nat × Nat × AnnotTerm)} {u₁ u₂ : Nat},
      mkPisAV l₁ (.sort u₁) = mkPisAV l₂ (.sort u₂) → l₁ = l₂ ∧ u₁ = u₂
  | [], [], _, _, h => ⟨rfl, by simpa [mkPisAV] using h⟩
  | [], _ :: _, _, _, h => by simp [mkPisAV] at h
  | _ :: _, [], _, _, h => by simp [mkPisAV] at h
  | d₁ :: l₁, d₂ :: l₂, u₁, u₂, h => by
    simp only [mkPisAV, AnnotTerm.pi.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨rfl, rfl⟩ := mkPisAV_sort_inj h4
    refine ⟨?_, rfl⟩
    congr 1
    exact Prod.ext h1 (Prod.ext h2 h3)

/-! ## Kit: the copy's former, read -/

/-- **The copy's telescope reads as the container's instantiated at the
pin.**  With the first former's binders `pbs` (fvar-free, `nP` of them),
the container's stored type `T` (closed) reading at the pin's level
assignment as a Π-tower over `ppsJ` ending in a sort, and the
components `Ds` (scoped at `nP`, bounded) reading as `vs` at depth
`nP`: whenever `mkCopy`'s type `closeTelescope pbs 0 (instPis
(instantiateLevelParams ks us T) Ds)` reads as a Π-tower over `ppsC`
ending in a sort, the data past the block's parameters are `ppsJ`'s
past the components, instantiated at `vs` (`instTeleP` from cut `0`),
and the sorts agree. -/
theorem copyType_read (m : EnvModel V env) {ψ ψJ : Name → Nat}
    {pbs : List (Expr × ConLeche.BinderMeta)} {nP : Nat}
    (hpbs : pbs.length = nP) (hpfree : ∀ bb ∈ pbs, bb.1.hasFvar = false)
    {T : Expr} (hTcl : T.hasFvar = false) (hTb : T.looseBVarsBounded 0 = true)
    {ks : List Name} {us : List Level} (hψJ : ψJ = Level.substFn ψ ks us)
    {ppsJ : List (Nat × Nat × AnnotTerm)} {s : Nat}
    (hread : denoteMeta m.acval env ψJ 0 T = some (mkPisAV ppsJ (.sort s)))
    (hbelow : DomsBelow 0 ppsJ)
    {Ds : List Expr} {vs : List AnnotTerm} (hvl : vs.length ≤ ppsJ.length)
    (hDs : ∀ a ∈ Ds, Expr.WScoped nP a ∧ a.looseBVarsBounded 0 = true)
    (hspine : DenoteMetaSpine m.acval env ψ nP Ds vs)
    {tyI : Expr} (hinst : Expr.instPis (Expr.instantiateLevelParams ks us T) Ds = some tyI)
    {ppsC : List (Nat × Nat × AnnotTerm)} {sC : Nat} (hlenC : nP ≤ ppsC.length)
    (hcopy : denoteMeta m.acval env ψ 0 (ConLeche.closeTelescope pbs 0 tyI)
      = some (mkPisAV ppsC (.sort sC))) :
    ppsC.drop nP = instTeleP vs 0 (ppsJ.drop vs.length) ∧ sC = s := by
  -- the closed telescope is the first former's binders over the bulk abstraction
  rw [ConLeche.closeTelescope_eq_mkPisB pbs 0 tyI hpfree, hpbs] at hcopy
  obtain ⟨fvs, hlen, -, hlaw⟩ := ConLeche.openPisAtFvars_mkPisB nP pbs hpbs 0
  have hop := hlaw (tyI.abstractRange 0 nP 0)
  obtain ⟨pps, bA, hst, hbA, -, -⟩ := denoteMeta_openPis nP hop hcopy
  rw [stripPisAV_mkPisAV_take nP ppsC _ hlenC] at hst
  have hst' := Option.some.inj hst
  obtain rfl : bA = mkPisAV (ppsC.drop nP) (.sort sC) := (congrArg Prod.snd hst').symm
  -- the opened body reads as `tyI`
  have hbI : tyI.looseBVarsBounded 0 = true :=
    ConLeche.looseBVarsBounded_instPis Ds _ tyI
      (by rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hTb)
      (fun a ha => (hDs a ha).2) hinst
  have hidx : ∀ k, k < nP → ∃ ty, fvs[k]? = some (.fvar k ty) := by
    intro k hk
    have hxk : fvs[k]? = some fvs[k] := List.getElem?_eq_getElem (by omega)
    obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index nP _ 0 hop k _ hxk
    exact ⟨ty, by rw [hxk, hty, Nat.zero_add]⟩
  have hbody : denoteMeta m.acval env ψ nP tyI = some (mkPisAV (ppsC.drop nP) (.sort sC)) := by
    rw [Nat.zero_add] at hbA
    rw [← denoteMeta_congr_eraseAnnots nP _ _
      (ConLeche.Expr.eraseAnnots_openAbstract tyI hbI fvs hlen hidx)]
    exact hbA
  -- the container's type at depth `nP`, at the pin's level assignment
  have hTa : denoteMeta m.acval env ψ nP (Expr.instantiateLevelParams ks us T)
      = some (mkPisAV ppsJ (.sort s)) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m) ψ nP T, ← hψJ,
      denoteMeta_lift m.acval_closed (Expr.WScoped.of_not_hasFvar (d := 0) hTcl) nP (Nat.zero_le _),
      hread]
    simp only [Option.map_some, Nat.sub_zero]
    rw [liftN_eq_self_of_closed (mkPisAV_below_of hbelow (by simp [AnnotTerm.erase, Term.bvarsBelow]))
      0 nP]
  -- the peel
  obtain ⟨ds, hpr⟩ := ConLeche.instPis_instPisAt Ds _ tyI hinst
  obtain ⟨restA, hrest, hpeel⟩ := denoteMeta_instPisAt_peel m.acval_closed (acval_inst_self m) Ds hpr
    (Expr.WScoped.of_not_hasFvar (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hTcl))
    hDs hTa hspine
  rw [← List.take_append_drop vs.length ppsJ,
    peelPis_mkPisAV_sort _ _ vs s (by rw [List.length_take, Nat.min_eq_left hvl])] at hpeel
  rw [hbody] at hrest
  obtain rfl := Option.some.inj hrest
  obtain ⟨h1, h2⟩ := mkPisAV_sort_inj (Option.some.inj hpeel)
  exact ⟨h1.symm, h2.symm⟩

/-! ## Kit: a pin's scope from the openers -/

/-- **A term over the first former's openers is well-scoped at the
parameter count** (`pinRead_of_inferAt`'s scope half): its leaves are
openers, whose annotations the opening scopes at their own index. -/
theorem WScoped_of_openers (mp₁ : EnvModelM V μ env) {cvT₀ : ConstantVal} {nP nIdx₀ : Nat}
    {s₀ : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp₁.base2 cvT₀ (nP + nIdx₀) s₀ pps)
    (hcl : cvT₀.type.hasFvar = false) (hbt : cvT₀.type.looseBVarsBounded 0 = true)
    {fvs : List Expr} {o : Expr} (hop : ConLeche.openPisAtFvars nP cvT₀.type 0 = some (fvs, o))
    {pin : Expr} (hleaf : ∀ l ∈ pin.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) (ψ : Name → Nat) :
    Expr.WScoped nP pin := by
  obtain ⟨Γ, R, -, O⟩ := opened_of (V := V) hop hcl hbt (hFD.read ψ) (hFD.okTy ψ)
  have hlenF : fvs.length = nP := openPisAtFvars_length nP hop
  have hidx := openPisAtFvars_index nP cvT₀.type 0 hop
  have hleafAt : ∀ l ∈ pin.fvarLeaves, fvs[l.1]? = some (Expr.fvar l.1 l.2) := by
    intro l hl
    obtain ⟨pos, hpos⟩ := List.getElem?_of_mem (hleaf l hl)
    obtain ⟨ty', hx⟩ := hidx pos _ hpos
    rw [Nat.zero_add] at hx
    obtain ⟨rfl, -⟩ : l.1 = pos ∧ l.2 = ty' := by
      injection hx with a bb
      exact ⟨a, bb⟩
    exact hpos
  refine WScoped_of_leaves pin fun l hl => ?_
  have hat := hleafAt l hl
  obtain ⟨-, hw, -, -, -⟩ := O.var l.1 _ hat
  exact ⟨by rw [← hlenF]; exact (List.getElem?_eq_some_iff.mp hat).1, hw⟩

/-! ## The discharge of `idx` -/

section Discharge

variable {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {st : ElimState} {b : MutualBlock}
  {envAux : Env} {stored : List AuxStored} {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env)}
  (R : NestedPinsRun V μ F mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁
    ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁')
include R

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)

/-- The first former's binders are fvar-free (its type is closed), and
the pins' data hold at them. -/
theorem NestedPinsRun.pinDataFree :
    ∃ pbs : List (Expr × ConLeche.BinderMeta), pbs.length = p.nP ∧
      (∀ bb ∈ pbs, bb.1.hasFvar = false) ∧ ∀ q, q < st.pins.length → PinData env st p pbs q := by
  obtain ⟨t₀, pbs, body, ht₀, hstrip₀, hK28⟩ := ConLeche.nestedCopySrcOk_inv R.hsrc
  refine ⟨pbs, Expr.stripPis_length _ hstrip₀, ?_, pinData_of hK28 R.hgrp R.hcont⟩
  have ht₀' : st.types[0]? = some t₀ := by rw [← List.head?_eq_getElem?]; exact ht₀
  obtain ⟨hcvTa, -⟩ := R.formerType 0 f₀ R.h.first t₀ ht₀'
  obtain ⟨-, hcl, -, -⟩ := R.former0
  rw [hcvTa] at hcl
  have hcl' : t₀.type.hasFvar = false := hcl
  rw [ConLeche.stripPis_mkPisB _ hstrip₀] at hcl'
  exact (ConLeche.hasFvar_mkPisB _ _ hcl').1

/-- **`idx` at any pin list with the syntactic facts and any group with
the syntactic half**, under K.30's scope of the pins. -/
theorem NestedPinsRun.idxIdent
    {fvs : List Expr} {o : Expr} (hop : ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some (fvs, o))
    (hsc : ∀ q ∈ st.pins, q.pin.looseBVarsBounded 0 = true ∧
      ∀ l ∈ q.pin.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    {pinsS : List PinSyn}
    (SF : NestedPinSynFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
      (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
      (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
      (tssF := tssF) (ctorsR := ctorsR) (pinsS := pinsS) st mp₁')
    {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
    {q₀ kJ : Nat} {dJ : BlockModel V}
    (S : NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
      (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
      (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
      (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
      st mp₁'.base2 q₀ kJ dJ) :
    ∀ i, i < kJ → ∀ (ψ : Name → Nat) (i' : Nat), i' < kJ →
      blockIds b.nP ppsF ψ (p.k + q₀ + i')
        = instTele ((pinsS.getD (q₀ + i) default).Ds ψ) 0
            (dJ.IdsM i' ((pinsS.getD (q₀ + i) default).ψJ ψ)) := by
  intro i hi ψ i' hi'
  have hpinAt : ∀ n, (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
      srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt n = pinsS.getD n default :=
    fun _ => rfl
  have hlenS := SF.pinsLen
  have hseg := S.seg
  have hqi : q₀ + i < pinsS.length := by omega
  have hq : q₀ + i' < pinsS.length := by omega
  -- the group's pins share the level assignment and the components
  have hψ := S.ψJEq i i' hi hi' ψ
  rw [hpinAt, hpinAt] at hψ
  have hDs : (pinsS.getD (q₀ + i) default).Ds ψ = (pinsS.getD (q₀ + i') default).Ds ψ := by
    have hE : (pinsS.getD (q₀ + i) default).DsE = (pinsS.getD (q₀ + i') default).DsE := by
      have a := (S.same i hi).2
      have bb := (S.same i' hi').2
      rw [hpinAt, hpinAt] at a bb
      rw [a, bb]
    rw [(SF.pinDs _ hqi ψ).eq_map, (SF.pinDs _ hq ψ).eq_map, hE]
  rw [hψ, hDs]
  -- the pin `q₀ + i'`: its record, K.28's source, the block at the stored constant
  obtain ⟨pbs, hpbs, hpfree, hPD⟩ := R.pinDataFree
  have hqst : q₀ + i' < st.pins.length := by rw [← hlenS]; exact hq
  have PD := hPD _ hqst
  obtain ⟨hJ, hpinS⟩ := SF.pinRec _ _ PD.pin
  have hpin := PD.pinEq
  rw [hpinS] at hpin
  have hlv : (pinsS.getD (q₀ + i') default).lvls = (srcAtE st p (q₀ + i')).2.1 := by
    have := congrArg Expr.getAppFn hpin
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at this
    exact (Expr.const.inj this).2
  have hDsE : (pinsS.getD (q₀ + i') default).DsE = (srcAtE st p (q₀ + i')).2.2 := by
    have := congrArg Expr.getAppArgs hpin
    simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append] at this
    exact this
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, hψJ⟩ := S.stored i' hi'
  rw [hpinAt] at hfind hI hψJ
  rw [hJ] at hfind hI
  obtain ⟨ci, hci, -, -, -, -, J, hJfind, hJn, c, hmk, hct, -⟩ := PD.own
  obtain ⟨_cvT₀, _caps₀, _cvR₀, _mI₀, _rP₀, _rules₀, -, -, -, -, hall⟩ :=
    ConLeche.containerInfo?_inv hci
  obtain ⟨cvC, capsC, _cvRc, _mIc, _rulesC, hfC, -, hlpsJ, htyJ, -, -, -⟩ :=
    hall J (List.mem_of_find?_eq_some hJfind)
  obtain ⟨hF, -, -, hde⟩ := R.cross
  have hfC₁ : (ENV₁).find? J.name = some (.indInfo cvC capsC) :=
    hF _ _ (fun _ _ _ _ h => nomatch h) hfC
  rw [hJn] at hfC₁
  obtain rfl : cvT = cvC :=
    (ConstantInfo.indInfo.inj (Option.some.inj (hfind.symm.trans hfC₁))).1
  -- the copy's former: its data at the pre-block model, crossed to the prefix model
  have hnP : b.nP = p.nP := (ConLeche.auxBlock_former R.hb).1
  have hlt : p.k + (q₀ + i') < fms.length := by rw [R.h.lenFms, R.hbk]; omega
  obtain ⟨hcvTa, -⟩ := R.formerType _ _ (fms_get hlt) _ PD.ty
  have hFD := R.h.FD₀ _ _ (fms_get hlt)
  have hreadC := hde ψ 0 _ (hFD.read ψ)
  rw [hcvTa] at hreadC
  have hlenC := hFD.len ψ
  obtain ⟨tyI, hinst, hcty⟩ := ConLeche.mkCopy_type hmk
  have hcopyTy : (copyAtE st p (q₀ + i')).type = ConLeche.closeTelescope pbs 0 tyI := by
    rw [← hct, hcty]
  change denoteMeta mp₁'.base2.acval (ENV₁) ψ 0 (copyAtE st p (q₀ + i')).type = _ at hreadC
  rw [hcopyTy] at hreadC
  -- the container's stored constant is closed
  have hwf := mp₁'.base2.wf _ (List.mem_of_find?_eq_some hfind)
  have hTcl : cvT.type.hasFvar = false := hwf.1
  have hTb : cvT.type.looseBVarsBounded 0 = true := hwf.2.2.2.1
  -- the components' scope (K.30) and readings
  obtain ⟨hk0, hcl₀, hbt₀, hFD₀⟩ := R.former0
  have hmem : pinAtE st (q₀ + i') ∈ st.pins := List.mem_of_getElem? PD.pin
  obtain ⟨hbnd, hleaf⟩ := hsc _ hmem
  have hws := WScoped_of_openers mp₁' hFD₀ hcl₀ hbt₀ hop hleaf ψ
  rw [PD.pinEq] at hbnd hws
  obtain ⟨-, hwsD⟩ := ConLeche.WScoped_of_mkAppN hws
  obtain ⟨-, hbndD⟩ := ConLeche.looseBVarsBounded_of_mkAppN hbnd
  have hDsSc : ∀ a ∈ (srcAtE st p (q₀ + i')).2.2,
      Expr.WScoped b.nP a ∧ a.looseBVarsBounded 0 = true :=
    fun a ha => ⟨hwsD a ha, hbndD a ha⟩
  have hspine := SF.pinDs _ hq ψ
  rw [hDsE] at hspine
  -- the identity, through the reading of the copy's type
  have hFDJ := hI.former
  have hDsLen := S.pinDsLen i' hi' ψ
  rw [hpinAt] at hDsLen
  have hvl : ((pinsS.getD (q₀ + i') default).Ds ψ).length
      ≤ (dJ.ppsM i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).length := by
    rw [hDsLen, hFDJ.len]; omega
  rw [hlpsJ, htyJ, ← hlv] at hinst
  obtain ⟨hdrop, -⟩ := copyType_read mp₁'.base2 (hpbs.trans hnP.symm) hpfree hTcl hTb (hψJ ψ)
    (hFDJ.read _) (hFDJ.below _) hvl hDsSc hspine hinst (by rw [hlenC]; omega) hreadC
  unfold blockIds
  rw [Nat.add_assoc, hdrop, instTeleP_map, hDsLen]
  rfl

end Discharge

/-! ## The consumer -/

/-- **`idx` from the run** — `NestedPinsIdsAt` at the index-telescope
identity, with K.30's scope of the pins read off the run. -/
theorem nestedPinsIdx {F : Nat} :
    NestedPinsIdsAt V μ F fun _ p _ b _ _ _ _ ppsF _ _ _ _ _ _ _ _ _ _ _ _ pinsS _ q₀ kJ dJ =>
      ∀ i, i < kJ → ∀ (ψ : Name → Nat) (i' : Nat), i' < kJ →
        blockIds b.nP ppsF ψ (p.k + q₀ + i')
          = instTele ((pinsS.getD (q₀ + i) default).Ds ψ) 0
              (dJ.IdsM i' ((pinsS.getD (q₀ + i) default).ψJ ψ)) := by
  intro env mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF
    dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S
  obtain ⟨-, fvs, o, hop, hsc⟩ := R.scoped
  exact R.idxIdent hop hsc SF S

/-- **The copies' constructor SHAPES** (NAMED — lane L-B's deliverable,
DESIGN §U.23/§U.36; consumer `nestedPinsIdent_of`): `CopyShapeA` at
every constructor of every copy of the group — the entry-free
identities (`len`, `recF`, `ordF` at the reading, `pinF`'s pin
correspondence, `es`), K.28's pre-image computed through
`replaceAllNested`'s action. -/
@[expose] def NestedPinsShape (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  NestedPinsIdsAt V μ F fun _ p _ b fms f₀ ctorsA kinds ppsF W _ dsF esF _ _ _ eissF tssF _
      _ _ pinsS mp₁' q₀ kJ dJ =>
    ∀ i, i < kJ → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length →
      CopyShapeA (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
        (pins := pinsS) (offs := b.ownOffset) (memberNames := (fms.take p.k).map (·.cvTa.name))
        (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
        (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
        (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
        (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
        (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
        mp₁'.base2.acval dJ ((pinsS.getD (q₀ + i) default).ψJ ψ) ((pinsS.getD (q₀ + i) default).Ds ψ)
        q₀ kJ i' j

/-- **The copies' ENTRIES at the auxiliary carrier** (NAMED — lane L-E's
global entry theorem `nestedPinLeaf_all`, DESIGN §U.36; consumer
`nestedPinsIdent_of`): `CopyEntryA` at every constructor of every copy
of the group — at every copy-recursive field targeting OUTSIDE the
group, the container's domain read at the pin's frame is the copy's
slot at the auxiliary least tuple.  Not a per-group fact: a pin target
is another group's `pinLeaf`, and the pin reference graph is cyclic at
a self-nested container. -/
@[expose] def NestedPinsEntry (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  NestedPinsIdsAt V μ F fun _ p _ b _ f₀ ctorsA kinds ppsF W _ dsF esF _ _ _ eissF tssF _
      _ _ pinsS _ q₀ kJ dJ =>
    ∀ i, i < kJ → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length →
      CopyEntryA (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
        (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
        (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
        (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
        (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
        (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
        (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
        (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
        dJ ((pinsS.getD (q₀ + i) default).ψJ ψ) ((pinsS.getD (q₀ + i) default).Ds ψ) q₀ kJ i' j

/-- **`NestedPinsIdent` from the shapes and the entries**: `idx` is a
theorem (`nestedPinsIdx`), the shape and the entry the named residuals. -/
theorem nestedPinsIdent_of {F : Nat} (hSh : NestedPinsShape V μ F) (hEn : NestedPinsEntry V μ F) :
    NestedPinsIdent V μ F := by
  intro env mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF
    dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S
  exact ⟨nestedPinsIdx mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds
      mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S,
    hSh mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF
      esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S,
    hEn mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF
      esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S⟩

end ConLeche.Model
