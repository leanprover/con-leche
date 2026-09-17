module

public import ConLeche.Model.Inductives.DeclNestedCore
import ConLeche.Model.Inductives.NestedRec
public import ConLeche.Model.Inductives.NestedPinLaws
import ConLeche.Verify.Inductives.NestedElimInv
public section

/-!
# The nested block's recursors' stage: the skeleton (task #315, M7-2)

`MutualRecsModeled`'s twin at `k + nPins` classes (DESIGN §U.25 (e) 5,
§U.29), stated CONSUMER FIRST: `NestedTailModeled` (`DeclNestedCore.lean`)
is discharged by `nestedTailModeled_of` from three named facts at the
run's data — the tail's conjuncts and the core's concrete output
(`NestedTailIn`) — each with this skeleton as its consumer, the pins'
constructors `nestedPc` and their laws `PinRecLaws` at
`nestedBlockModel` being lane M7-1's theorem `nestedPinRecLaws_of`
(`NestedPinLaws.lean`, DESIGN §U.28):

* `NestedRecReadingsOf` — THE READINGS (item 2, this lane): the
  `k + nPins` restored recursor types read at the model of the restored
  environment to Π-towers `mkPisAV (rdsM c ψ) (concM c)`, formed at a
  sort `s` and graded (`nestedRecs`'s `hT`), with the bookkeeping the
  stage reads (`len`/`bits`/`below`/`params`), and their FRAMES
  (`ReadingFramesT`, the one readings-facing premise of `hcandT`);
* `NestedRecEqsOf` — the rules' equations at those readings (items 3
  and 4: `heq`, `hceq` at the candidate `blockCandT`);
* `NestedRecsStored` — the stage proper (item 5): from the readings, the
  equations and the chosen tuple, the provision conses, the rule law,
  the store swap, the post-checks and the tables cons a model of the
  post-block environment.

`nestedRecsTuple_of` is the skeleton's semantic core: the chosen tuple
of the `k + nPins` restored recursors (`nestedRecs`, `NestedRec.lean`)
from the readings and the equations, `hcand` discharged by `hcandT`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock AuxStored ElimState NestedPin IndCaps fueledOps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## The readings, the equations, the tuple -/

/-- **The `k + nPins` restored recursor types' readings** at a model
`m` of the restored environment, at a block model `d` with the pins'
constructors `pc` (DESIGN §U.29): the members' recursors `cvRms` and
the auxiliary ones `cvRns` read to the Π-towers `mkPisAV (rdsM c ψ)
(concM c)` (class `c < k` a member's, `k + q` pin `q`'s), carry the
recursors' level parameters `rlps`, and the readings are formed at the
sort `s` and graded (`nestedRecs`'s `hT`), of the stage's length, with
the elimination level's bits, closed at their depths, stable under the
level parameters, `ℓ = 0` at a `Prop`-valued block, and — THE ONE
READINGS-FACING PREMISE of `hcandT` — decompose at every fitting spine
into the frame `(p⃗, M⃗, m⃗, ı⃗_c, t)` with the frame's motives and
minors typed semantically (`ReadingFramesT`). -/
structure NestedRecReadings {env₂ : Env} (m : EnvModel V env₂) (d : BlockModel V)
    (pc : Nat → PinCtors V) (cvRms cvRns : List ConstantVal) (rlps : List Name) (elimL : Level)
    (s : (Name → Nat) → Nat) (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (concM : Nat → AnnotTerm) : Prop where
  lenM : cvRms.length = d.k
  lenN : cvRns.length = d.nPins
  readM : ∀ t, t < d.k → ∀ ψ : Name → Nat,
    denoteMeta m.acval env₂ ψ 0 (cvRms.getD t default).type = some (mkPisAV (rdsM t ψ) (concM t))
  readN : ∀ q, q < d.nPins → ∀ ψ : Name → Nat,
    denoteMeta m.acval env₂ ψ 0 (cvRns.getD q default).type
      = some (mkPisAV (rdsM (d.k + q) ψ) (concM (d.k + q)))
  lpsM : ∀ t, t < d.k → (cvRms.getD t default).levelParams = rlps
  lpsN : ∀ q, q < d.nPins → (cvRns.getD q default).levelParams = rlps
  len : ∀ (c : Nat) (ψ : Name → Nat), c < d.kT →
    (rdsM c ψ).length = d.nP + d.kT + d.nCtorsT pc + d.nIdxT c + 1
  bits : ∀ (c : Nat) (ψ : Name → Nat), c < d.kT → ∀ e ∈ rdsM c ψ, (elimL.eval ψ = 0 ↔ e.2.1 = 0)
  below : ∀ (c : Nat) (ψ : Name → Nat), c < d.kT → DomsBelow 0 (rdsM c ψ)
  params : ∀ (c : Nat) (ψ₁ ψ₂ : Name → Nat), c < d.kT → (∀ q ∈ rlps, ψ₁ q = ψ₂ q) →
    rdsM c ψ₁ = rdsM c ψ₂
  okTy : ∀ (c : Nat) (ψ : Name → Nat) (ρ : Nat → V), c < d.kT →
    WellDenotedV V ρ (mkPisAV (rdsM c ψ) (concM c))
  sort : ∀ (c : Nat) (ψ : Name → Nat) (ρ : Nat → V), c < d.kT →
    interp V ρ (mkPisAV (rdsM c ψ) (concM c)) ∈ˢ (univ (s ψ) : V)
  wℓ : ∀ ψ : Name → Nat, d.w ψ = 0 → elimL.eval ψ = 0
  frames : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < d.kT →
    d.ReadingFramesT pc ψ (elimL.eval ψ) (rdsM c ψ) (concM c) c ρ

/-- **The rules' equations at the readings** — `nestedRecs`'s `heq` and
`hceq` (DESIGN §U.25 (e) 3–4): the equations `eqs ψ` (the members'
rules' and the auxiliary rules') are truth values and graded at every
tuple typed at the readings, and every equation holds at the CANDIDATE
tuple `blockCandT` (the class recursor over the extended union at the
frame's motives and minors). -/
structure NestedRecEqs (d : BlockModel V) (pc : Nat → PinCtors V) (ℓ : (Name → Nat) → Nat)
    (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (concM : Nat → AnnotTerm)
    (eqs : (Name → Nat) → List AnnotTerm) : Prop where
  heq : ∀ (ψ : Name → Nat) (ρ : Nat → V) (rs : List V), rs.length = d.kT →
    (∀ c, c < d.kT → rs.getD c pt ∈ˢ interp V ρ (mkPisAV (rdsM c ψ) (concM c))) →
    ∀ e ∈ eqs ψ, interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e
  hceq : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ e ∈ eqs ψ,
    (pt : V) ∈ˢ interp V
      (consList ((List.range d.kT).map fun c => d.blockCandT pc ψ (ℓ ψ) (rdsM c ψ) c ρ) ρ) e

/-- **The chosen tuple's facts** — `nestedRecs`'s conclusion: at every
frame the `k + nPins` leaves `blockLeafAV` are typed at the readings,
graded, and their tuple satisfies every equation. -/
@[expose] def NestedRecTuple (d : BlockModel V) (s : (Name → Nat) → Nat)
    (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (concM : Nat → AnnotTerm)
    (eqs : (Name → Nat) → List AnnotTerm) : Prop :=
  ∀ (ψ : Name → Nat) (ρ : Nat → V), ∃ a : Nat → V,
    (∀ c, c < d.kT →
      a c ∈ˢ interp V ρ (mkPisAV (rdsM c ψ) (concM c)) ∧
      interp V ρ (blockLeafAV (s ψ) d.kT (fun t => rdsM t ψ) concM (eqs ψ) c) = a c ∧
      WellDenoted V ρ (blockLeafAV (s ψ) d.kT (fun t => rdsM t ψ) concM (eqs ψ) c)) ∧
    ∀ e ∈ eqs ψ, (pt : V) ∈ˢ interp V (consList ((List.range d.kT).map a) ρ) e

/-- **The tuple from the readings and the equations** — the skeleton's
semantic core: `nestedRecs` at the readings' `hT`, the equations'
`heq`/`hceq`, and `hcand` discharged by `hcandT` from the readings'
frames (at a member's `IsBlockModel`, the block having a member). -/
theorem nestedRecsTuple_of {env₂ : Env} {m : EnvModel V env₂} {d : BlockModel V}
    (hreps : IsBlockModels m d) {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) (hk : 0 < d.k)
    {cvRms cvRns : List ConstantVal} {rlps : List Name} {elimL : Level} {s : (Name → Nat) → Nat}
    {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {concM : Nat → AnnotTerm}
    (R : NestedRecReadings m d pc cvRms cvRns rlps elimL s rdsM concM)
    {eqs : (Name → Nat) → List AnnotTerm} (E : NestedRecEqs d pc (fun ψ => elimL.eval ψ) rdsM concM eqs) :
    NestedRecTuple d s rdsM concM eqs := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps 0 hk
  have hne : ∀ c ψ, c < d.kT → rdsM c ψ ≠ [] := by
    intro c ψ hc hnil
    have := R.len c ψ hc
    rw [hnil] at this
    simp at this
  have hcand := h.hcandT hreps hp R.wℓ hne R.bits R.frames
  exact nestedRecs d pc s (fun ψ => elimL.eval ψ) rdsM concM eqs
    (fun ψ ρ c hc => ⟨R.sort c ψ ρ hc, (R.okTy c ψ ρ hc).1⟩) E.heq hcand E.hceq

/-! ## The tail's input -/

/-- **The tail's input**: `NestedTailModeled`'s hypotheses as a record —
the run's conjuncts from the pins' models through post-check (c), the
environment identity of the restored formers, and the core's concrete
output (`NestedCoreOut`).  The four named facts of the recursors'
stage are stated over it. -/
structure NestedTailIn {env : Env} (F : Nat) (mp : EnvModelM V μ env) (p : NestedParts)
    (envOut : Env) (st : ElimState) (b : MutualBlock) (envAux : Env) (stored : List AuxStored)
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
      (ConLeche.consMutualFormers (fms.take p.k) env))) : Prop where
  hμ : μ.verifiedChecks = true
  hE : ConLeche.EtaFamiliesClosed env
  hPM : PinsModeled mp.base2 st.pins
  h0 : (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
    (p.ctors.map (fun c => c.cv.type)).all (fun t => !t.mentionsNestedAux)) = true
  h1 : uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
    (p.ctors.map (fun c => c.cv.type)) = true
  hfA : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
    = .ok fmsA
  hcA : ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (fueledOps μ F)
    (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA₀
  helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA₀) = .ok st
  hcount : st.pins.length = p.numNested
  hfresh : ConLeche.copiesFresh env p.k st = true
  hcont : ConLeche.nestedContainersOk env st.pins = true
  hb : ConLeche.auxBlock p st = some b
  haux : ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true = .ok envAux
  hstored : ConLeche.auxStoredAll envAux b b.k = some stored
  hclosed : ConLeche.pinsClosed p.nP st.pins = true
  hpinsAux : ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envAux p.nP st.pins
    = .ok ()
  hcaps : (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true
  hsrc : ConLeche.nestedCopySrcOk env p st = true
  hgrp : ConLeche.nestedGroupsOk env p st = true
  hkinds : ConLeche.nestedPinKindsOk p b st stored = true
  hctors : (stored.take p.k).mapM (fun a =>
      ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
        a.ctors)
    = .ok ctorsR
  hrm : ConLeche.restoreRecTys (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consNestedFormers (stored.take p.k) env))
      (ConLeche.restoreTbl p st) p.lps
      ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
      (stored.take p.k) = .ok cvRms
  hrn : ConLeche.restoreRecTys (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consNestedFormers (stored.take p.k) env))
      (ConLeche.restoreTbl p st) p.lps
      ((List.range p.numNested).map p.mimicRecName)
      (stored.drop p.k) = .ok cvRns
  hrulesM : (cvRms.zip (stored.take p.k)).mapM (fun (cvRa, a) =>
      ConLeche.restoreRules (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.provisionNestedRecs
          ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
            ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consNestedFormers (stored.take p.k) env)))
        (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules)
    = .ok rulesM
  hrulesN : (cvRns.zip (stored.drop p.k)).mapM (fun (cvRa, a) =>
      ConLeche.restoreRules (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.provisionNestedRecs
          ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
            ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consNestedFormers (stored.take p.k) env)))
        (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules)
    = .ok rulesN
  htbl : ConLeche.nestedTables (m := ConLeche.CheckM)
      (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
        ((p.formers.getD mIdx default).1.name, a.tbl, cs))
      (ConLeche.storeNestedRecs
        ((cvRms.zip ((stored.take p.k).zip rulesM)).map
            (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
          ++ (cvRns.zip ((stored.drop p.k).zip rulesN)).map
            (fun (cv, a, rs) => (cv, a.mI, a.rP, rs)))
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env))) = .ok envOut
  hpinsOut : ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envOut p.nP st.pins
    = .ok ()
  hcnt : (p.memberRecs.length == cvRms.length && p.mimicRecs.length == cvRns.length) = true
  hrecs : ConLeche.nestedRecsOk (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consNestedFormers (stored.take p.k) env))
      p.nP b.k b.n
      ((((p.memberRecs.zip cvRms).zip rulesM).zipIdx.map
          (fun (((sr, cv), rs), mIdx) =>
            (sr, (b.ownCtors mIdx).map (fun (J, c) => (J, c.nF)), cv, rs)))
        ++ (((p.mimicRecs.zip cvRns).zip rulesN).zipIdx.map
          (fun (((sr, cv), rs), j) =>
            (sr, (b.ownCtors (p.k + j)).map (fun (J, c) => (J, c.nF)), cv, rs))))
    = .ok ()
  henv : ConLeche.consNestedFormers (stored.take p.k) env
    = ConLeche.consMutualFormers (fms.take p.k) env
  out : NestedCoreOut F mp p st b ctorsR fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
    fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂

section Facts

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

/-- The block has a member (the elimination reads the first type). -/
theorem NestedTailIn.kpos (I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns
    rulesM rulesN fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
    xrestF eissF tssF dsR xFvsR pinsS mp₂) : 0 < p.k := by
  have hlenA : fmsA.length = p.k := ConLeche.nestedAnnotFormers_length I.hfA
  have he := I.helim
  unfold ConLeche.elimNested at he
  cases hh : (ConLeche.nestedTypes0 p fmsA ctorsA₀).head? with
  | none =>
    rw [hh] at he
    exact nomatch he
  | some t₀ =>
    have hlen := ConLeche.nestedTypes0_length p fmsA ctorsA₀
    rw [hlenA] at hlen
    cases hl : ConLeche.nestedTypes0 p fmsA ctorsA₀ with
    | nil => rw [hl] at hh; exact nomatch hh
    | cons x xs => rw [hl] at hlen; simp only [List.length_cons] at hlen; omega

end Facts

/-! ## The named facts, at the run -/

/-- **The readings at the run** (DESIGN §U.25 (e) 2, this lane): at
every tail input, a sort `s` and readings `rdsM`/`concM` with
`NestedRecReadings` at the model of the restored environment, the
block model `nestedBlockModel`, the pins' constructors `nestedPc`,
the restored recursors `cvRms`/`cvRns`, the recursors' level
parameters `b.rlps` and the elimination level `b.elimLevel`.
Consumer: `nestedTailModeled_of`. -/
@[expose] def NestedRecReadingsOf (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
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
    ∃ (s : (Name → Nat) → Nat) (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (concM : Nat → AnnotTerm),
      NestedRecReadings mp₂.base2
        (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS)
        (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)
        cvRms cvRns b.rlps b.elimLevel s rdsM concM

/-- **The equations at the run** (DESIGN §U.25 (e) 3–4): at every tail
input and every readings record, equations `eqs` with `NestedRecEqs`
(graded at the readings, satisfied at the candidate).  Consumer:
`nestedTailModeled_of`. -/
@[expose] def NestedRecEqsOf (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
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
    ∀ (s : (Name → Nat) → Nat) (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (concM : Nat → AnnotTerm),
      NestedRecReadings mp₂.base2
        (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS)
        (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)
        cvRms cvRns b.rlps b.elimLevel s rdsM concM →
      ∃ eqs : (Name → Nat) → List AnnotTerm,
        NestedRecEqs
          (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
            xrestF eissF tssF ctorsR dsR xFvsR pinsS)
          (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)
          (fun ψ => b.elimLevel.eval ψ) rdsM concM eqs

/-- **The stage proper** (DESIGN §U.25 (e) 5): at every tail input, from
the readings, the equations and the chosen tuple, the provision conses
of the `k + nPins` rule-less recursors, the rule law per restored rule,
the store swap, the post-checks and the tables cons a model of the
post-block environment.  Consumer: `nestedTailModeled_of`. -/
@[expose] def NestedRecsStored (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
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
    ∀ (s : (Name → Nat) → Nat) (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (concM : Nat → AnnotTerm) (eqs : (Name → Nat) → List AnnotTerm),
      NestedRecReadings mp₂.base2
        (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS)
        (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)
        cvRms cvRns b.rlps b.elimLevel s rdsM concM →
      NestedRecEqs
        (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS)
        (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)
        (fun ψ => b.elimLevel.eval ψ) rdsM concM eqs →
      NestedRecTuple
        (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS) s rdsM concM eqs →
      -- task #315 M7-3 session 10 (DESIGN §U.56 (c)): the conclusion is
      -- `NestedTailModeled`'s, which now carries the install's conses, the
      -- agreements, the block's representation at the OUTPUT model and the
      -- pins' groups with their containers' models NAMED — what the route's
      -- lift to `EnvModelB` reads (`declNested_of`).  This lane's proof
      -- obligation grew with it; nothing else in the skeleton moved.
      ∃ mpOut : EnvModelM V μ envOut,
        NestedTailOut (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
          (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
          (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
          (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
          mp stored mp₂ envOut mpOut

/-! ## The skeleton -/

/-- **THE RECURSORS' STAGE OF A NESTED BLOCK, assembled** — `NestedTailModeled`
from its three named facts: at the tail's input the pins' laws are
M7-1's (`nestedPinRecLaws_of`), the readings are found, the equations at the readings follow, the chosen
tuple exists (`nestedRecsTuple_of`: `nestedRecs` with `hcand` from
`hcandT` at the readings' frames), and the stage conses the post-block
model from them. -/
theorem nestedTailModeled_of {F : Nat}
    (hrd : NestedRecReadingsOf V μ F) (heqs : NestedRecEqsOf V μ F)
    (hst : NestedRecsStored V μ F) : NestedTailModeled V μ F := by
  intro hμ env mp hE p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀
    hPM h0 h1 hfA hcA helim hcount hfresh hcont hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hkinds
    hctors hrm hrn hrulesM hrulesN htbl hpinsOut hcnt hrecs fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF
    dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂ henv O
  have I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA
      ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF
      dsR xFvsR pinsS mp₂ :=
    ⟨hμ, hE, hPM, h0, h1, hfA, hcA, helim, hcount, hfresh, hcont, hb, haux, hstored, hclosed,
      hpinsAux, hcaps, hsrc, hgrp, hkinds, hctors, hrm, hrn, hrulesM, hrulesN, htbl, hpinsOut, hcnt,
      hrecs, henv, O⟩
  have hp := nestedPinRecLaws_of hμ O.facts O.grouped O.bk mp₂.base2 O.stage.groups
  obtain ⟨s, rdsM, concM, R⟩ := hrd mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN
    fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF
    tssF dsR xFvsR pinsS mp₂ I
  obtain ⟨eqs, E⟩ := heqs mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA
    ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF
    dsR xFvsR pinsS mp₂ I s rdsM concM R
  have hk : 0 < (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF
      fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).k := I.kpos
  exact hst mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀ fms f₀
    ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS
    mp₂ I s rdsM concM eqs R E (nestedRecsTuple_of O.reps hp hk R E)

end ConLeche.Model
