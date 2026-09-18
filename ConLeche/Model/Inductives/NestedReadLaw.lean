module

public import ConLeche.Model.Inductives.NestedCtorRead
import ConLeche.Model.Inductives.NestedCtorOpened
import ConLeche.Model.Inductives.NestedCtorRefl
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Model.Inductives.NestedTransfer
public section

/-!
# `NestedReadLaw`, discharged (task #315, M6 s9′)

The restore reading law is a theorem: `nestedReadLaw`.  Per restored
constructor the record `RestoredCtor` (`NestedCtorRead.lean`) and the
reading `ReadSpec` are chosen; the block model's opened form is lane
O's `ReadCtx.blockOpened_of` (`NestedCtorOpened.lean`), the reflexive
nested entries lane R's `ReadCtx.fieldEqC` (`NestedCtorRefl.lean`);
`ReadCtx.nestedCtorRead_of` assembles `NestedCtorRead`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock ElimState NestedPin IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

section Assembly

variable {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {b : MutualBlock}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)
local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

variable {st : ElimState} {envAux : Env} {stored : List AuxStored} {fmsA ctorsA₀ : List ConstantVal}
  {mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env)}
  (C : ReadCtx (V := V) (μ := μ) (env := env) (F := F) (mp := mp) (p := p) (b := b) (fms := fms)
    (f₀ := f₀) (ctorsA := ctorsA) (sortss := sortss) (kinds := kinds) (mp₁ := mp₁) (ppsF := ppsF)
    (W := W) (idxF := idxF) (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF)
    (xFvsF := xFvsF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF) (ctorsR := ctorsR)
    (pinsS := pinsS) st envAux stored fmsA ctorsA₀ mp₁')
include C

section Hooks

variable {mm j : Nat} {c : ConstantVal × Nat × Nat} {cA : ConstantVal × Nat}
  {crestR : Expr} {xFvsRc : List Expr}
  (RC : RestoredCtor (μ := μ) (env := env) (F := F) (p := p) (b := b) (fms := fms)
    (ctorsA := ctorsA) (kinds := kinds) (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF)
    (st := st) mm j c cA crestR xFvsRc)
  {dsRc : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  (RS : ReadSpec mp₁' (fms.getD mm default).cvTa.name b.nP cA.2 c.1 (esF (b.ownOffset mm + j)) dsRc)
include RC RS

omit C in
/-- The parameter openers' annotations are scoped at their own depth. -/
theorem ReadCtx.paramWScoped : ∀ (k : Nat) (x : Expr), (fvsPF (b.ownOffset mm + j))[k]? = some x →
    Expr.WScoped k x.fvarTypeD := by
  intro k x hx
  have hO := ReadCtx.openedR RC RS (fun _ => 0)
  have hkl : k < (fvsPF (b.ownOffset mm + j)).length := (List.getElem?_eq_some_iff.mp hx).1
  exact (hO.var k x (by rw [List.getElem?_append_left hkl]; exact hx)).2.1

/-- **The reflexive nested clauses** at the restored constructor (lane
R's `fieldEqC` at the record's arm (C)). -/
theorem ReadCtx.reflC_of (ψ : Name → Nat) (i q : Nat) (x : Expr) (hx : xFvsRc[i]? = some x)
    (hq : (D).nestOf mm j i = some q)
    (hk : (kindsOf (mutKsOf kinds (b.ownOffset mm + j))).getD i .ordinary = .reflexive) :
    (∃ afvs body,
      openPisAtFvars ((tssF (b.ownOffset mm + j) ψ).getD i []).length x.fvarTypeD (b.nP + i)
        = some (afvs, body) ∧
      ((tssF (b.ownOffset mm + j) ψ).getD i []).length = (x.fvarTypeD.piBinders).1.length ∧
      (∀ k a, afvs[k]? = some a →
        denoteMeta mp₁'.base2.acval ENV₁ ψ (b.nP + i + k) a.fvarTypeD
          = some (((tssF (b.ownOffset mm + j) ψ).getD i []).getD k default).2.2) ∧
      DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ
        (b.nP + i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length)
        (body.getAppArgs.drop ((D).pinAt q).nPJ) ((eissF (b.ownOffset mm + j) ψ).getD i [])) ∧
    ((eissF (b.ownOffset mm + j) ψ).getD i []).length = ((D).pinAt q).nIdx ∧
    ((dsRc ψ).getD (b.nP + i) default).2.2
      = mkPisAV ((tssF (b.ownOffset mm + j) ψ).getD i [])
          (AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
            ((((D).pinAt q).Ds ψ).map
                (·.liftN (i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length) 0)
              ++ (eissF (b.ownOffset mm + j) ψ).getD i [])) := by
  have hCD := C.h.CD _ _ RC.hJ
  have hi : i < cA.2 := by rw [← RC.hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
  have hil : i < (xFvsF (b.ownOffset mm + j)).length := by rw [hCD.xLen]; exact hi
  obtain ⟨xA, hxA⟩ : ∃ xA, (xFvsF (b.ownOffset mm + j))[i]? = some xA := ⟨_, List.getElem?_eq_getElem hil⟩
  obtain ⟨ty', hx', hF⟩ := RC.fields i xA hxA
  obtain rfl : x = .fvar (b.nP + i) ty' := Option.some.inj (hx.symm.trans hx')
  rw [kindsOf_getD'] at hk
  obtain ⟨hql, qn, hqn, htq, hnIdx⟩ := C.pinTarget RC hq
  rcases hF with ⟨hA, -⟩ | ⟨q', qn', -, -, hk', -, -⟩
    | ⟨q', qn', tbs, is₀, afvs, is, hqn', htq', -, hopA, hstripA, his, hstripR⟩
  · exfalso
    rcases hA with hA | hA
    · rw [hA] at hk; exact nomatch hk
    · omega
  · rw [hk'] at hk; exact nomatch hk
  · have hqq : q' = q := by omega
    subst q'
    obtain rfl := Option.some.inj (hqn.symm.trans hqn')
    obtain ⟨hopR, hLpi, hdoms, hsp, hentry⟩ :=
      C.fieldEqC RC RS ψ hxA hx' hqn hk hopA hstripA his hstripR
    -- the pin's argument count
    have hnPJ : (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
        (Expr.abstractRange qn.pin 0 p.nP 0)).getAppArgs.length = ((D).pinAt q).nPJ := by
      obtain ⟨-, hpin⟩ := C.PF.pinRec q qn hqn
      obtain ⟨q₀, kJ, i', dJ, hqe, hi', G⟩ := C.PF.groups dsR xFvsR q hql
      have hDsE : (pinsS.getD q default).DsE.length = ((D).pinAt q).nPJ := by
        rw [(C.PF.pinDs q hql ψ).length]
        show ((pinsS.getD q default).Ds ψ).length = (pinsS.getD q default).nPJ
        rw [hqe] at hql ⊢
        rw [show ((pinsS.getD (q₀ + i') default).Ds ψ).length = (((D).pinAt (q₀ + i')).Ds ψ).length from rfl,
          G.pinDsLen i' hi' ψ, ← G.pinNP i' hi']
        rfl
      rw [hpin, ← C.hnP]
      rw [ConLeche.rk_restoredPin_getAppArgs_length hCD.pLen (C.fvsPIdx RC.hJ)
        (nt_pin_bounded (C.PF.pinDs q hql ψ))]
      exact hDsE
    refine ⟨⟨afvs, _, hopR, hLpi, hdoms, ?_⟩, ?_, hentry⟩
    · rw [Expr.getAppArgs_mkAppN, List.drop_left' hnPJ]
      exact hsp
    · rw [hCD.eisLenRefl ψ i hk hi, hnIdx]

end Hooks

/-- **`NestedCtorRead` at every restored constructor**, at the chosen
records and readings. -/
theorem ReadCtx.nestedCtorRead {mm j : Nat} {c : ConstantVal × Nat × Nat} {cA : ConstantVal × Nat}
    {crestR : Expr}
    (RC : RestoredCtor (μ := μ) (env := env) (F := F) (p := p) (b := b) (fms := fms)
      (ctorsA := ctorsA) (kinds := kinds) (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF)
      (st := st) mm j c cA crestR (xFvsR mm j))
    (RS : ReadSpec mp₁' (fms.getD mm default).cvTa.name b.nP cA.2 c.1 (esF (b.ownOffset mm + j))
      (dsR mm j)) :
    NestedCtorRead (V := V) (F := F) (p := p) (b := b) (fms := fms) (f₀ := f₀)
      (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W)
      (idxF := idxF) (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF)
      (xrestF := xrestF) (eissF := eissF) (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR)
      (xFvsR := xFvsR) (pinsS := pinsS) mp₁' mm j c :=
  C.nestedCtorRead_of RC RS
    (C.blockOpened_of RC.hmm RC.hJ RC.hlenX (ReadCtx.paramWScoped RC RS) RC.fields)
    (fun ψ i q x hx hq hk => C.reflC_of RC RS ψ i q x hx hq hk)

end Assembly

/-! ## The law -/

/-- **THE RESTORE READING LAW** (`NestedReadLaw`, DESIGN §U.21b): at
every restored constructor, its record and its reading are chosen
(`ReadCtx.restoredCtor`, `ReadCtx.readSpec_of`), and
`ReadCtx.nestedCtorRead` assembles `NestedCtorRead`. -/
theorem nestedReadLaw {F : Nat} : NestedReadLaw V μ F := by
  intro hμ env mp hE p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
    idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' hPM h0 h1 hfA hcA helim hcount hfresh hcont
    hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hkinds hformers h hbk h3 hnd hctorsA hleafM'
    hoff' hfind' hctors pinsS PF
  have C : ReadCtx (V := V) (μ := μ) (env := env) (F := F) (mp := mp) (p := p) (b := b) (fms := fms)
      (f₀ := f₀) (ctorsA := ctorsA) (sortss := sortss) (kinds := kinds) (mp₁ := mp₁) (ppsF := ppsF)
      (W := W) (idxF := idxF) (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF)
      (xFvsF := xFvsF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF) (ctorsR := ctorsR)
      (pinsS := pinsS) st envAux stored fmsA ctorsA₀ mp₁' :=
    ⟨hμ, hfA, helim, hfresh, hb, haux, hstored, hclosed, hformers, h, hbk, h3, hnd, hctorsA, hleafM',
      hoff', hfind', hctors, PF⟩
  -- the records and the readings, chosen per position
  have hex : ∀ mm j : Nat, ∃ (xf : List Expr) (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      mm < p.k → ∀ c : ConstantVal × Nat × Nat, (ctorsR.getD mm [])[j]? = some c →
        ∃ (cA : ConstantVal × Nat) (crestR : Expr),
          RestoredCtor (μ := μ) (env := env) (F := F) (p := p) (b := b) (fms := fms)
            (ctorsA := ctorsA) (kinds := kinds) (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF)
            (st := st) mm j c cA crestR xf ∧
          ReadSpec mp₁' (fms.getD mm default).cvTa.name b.nP cA.2 c.1 (esF (b.ownOffset mm + j)) ds := by
    intro mm j
    rcases Classical.em (mm < p.k ∧ ∃ c : ConstantVal × Nat × Nat, (ctorsR.getD mm [])[j]? = some c)
      with ⟨hmm, c, hc⟩ | hno
    · obtain ⟨cA, crestR, xf, RC⟩ := C.restoredCtor hmm hc
      obtain ⟨ds, RS⟩ := C.readSpec_of RC
      refine ⟨xf, ds, fun _ c' hc' => ?_⟩
      obtain rfl := Option.some.inj (hc.symm.trans hc')
      exact ⟨cA, crestR, RC, RS⟩
    · refine ⟨[], fun _ => [], fun hmm c hc => absurd ⟨hmm, c, hc⟩ hno⟩
  refine ⟨fun mm j => Classical.choose (Classical.choose_spec (hex mm j)),
    fun mm j => Classical.choose (hex mm j), ?_⟩
  intro mm j c hmm hc
  obtain ⟨cA, crestR, RC, RS⟩ := Classical.choose_spec (Classical.choose_spec (hex mm j)) hmm c hc
  exact C.nestedCtorRead RC RS

/-- **`NestedCtorsStaged` with the reading law DISCHARGED** (task #315
L-E, DESIGN §U.112): `nestedCtorsStaged_of` takes `NestedReadLaw` as a
premise and `nestedReadLaw` above PROVES it unconditionally, so the
composition leaves only the pins' stage — and no consumer has to carry
the reading law as a residual.

Wired because it was not: the law was proved and had no call site, and
a premise with no call site is indistinguishable from a premise with no
proof (this project's `consumer-first-hypotheses` rule).  It cost this
lane's own residual walk one of its four entries before the producer
was found. -/
theorem nestedCtorsStaged_of_pins {F : Nat} (hpins : NestedPinsStaged V μ F) :
    NestedCtorsStaged V μ F :=
  nestedCtorsStaged_of hpins nestedReadLaw

end ConLeche.Model
