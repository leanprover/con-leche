module

public import ConLeche.Model.Inductives.NestedRecsStore
public import ConLeche.Model.Inductives.NestedRecEqs
import ConLeche.Model.Inductives.MutualRecsProvision
import ConLeche.Verify.Inductives.NestedRecNames
public import ConLeche.Verify.Inductives.NestedRecRuleKit
import ConLeche.Verify.Inductives.NestedElimInv
public section

/-!
# The scratch recursors provisioned at OUR leaves (task #315, M7-2, item 5 step 2a)

The recursors' rule law (item 5 step 2) needs the auxiliary (scratch)
rule's right-hand side to READ at a model whose recursor leaves are
OUR chosen tuple's projections: the walk's reading law
`denoteMeta_restoreWalk` identifies the restored right-hand side with
the auxiliary one only when the two sides' recursor leaves agree
(`RestoreAgree.recKey`/`.leafSome`), and the restored side's leaves are
ours (`NestedTailIn.provisioned`).  The scratch install's own recursor
tuple is the auxiliary block model's; what the law wants is the scratch
environment consed with OURS.

That is legitimate because the two Π-towers are ONE SET at every frame
(`NestedTailIn.towerAgree`): our leaf, typed at the RESTORED reading,
is typed at the SCRATCH reading too.  Everything else is the mutual
provision's own assembly (`mutualRecsProvision`): the leaf's three laws
are `nestedRecLeaf_typed`/`_below`/`_params`, the front door is the
scratch run's shape (`checkMutualRecTys_inv`, `checkMutualRecTy_shape`)
with the names' freedom `nestedRecNames_of`, and the conses are
`recsProvision`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock MutualFormer MutualCtor4 AuxStored ElimState NestedPin IndCaps
  fueledOps BinderMeta PropWhen RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

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

local notation "ENVA" =>
  (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))

local notation "ENV2" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))

/-- the COMPOSED nested block's block model -/
local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

/-- the SCRATCH (auxiliary) block's block model — the MUTUAL one -/
local notation "DA" => (mutualBlockModel (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xFvsF xrestF eissF tssF)

/-- the pins' constructors at the nested block model -/
local notation "PC" => (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)

/-- the pin groups at the restored environment's model -/
local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

variable (I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN
  fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF
  tssF dsR xFvsR pinsS mp₂)
include I

/-- **THE SCRATCH RECURSORS PROVISIONED AT OUR LEAVES** (PLAN-M7 §4b,
item 5 step 2a): the scratch block's `k` recursors consed RULE-LESS
onto the SCRATCH constructors' environment — the environment the
auxiliary rules were checked at — but with class `c`'s leaf OUR chosen
tuple's `c`-th projection (`nestedRecLeaf`) instead of the scratch
install's own.

The one thing to see is that our leaf is typed there: it is typed at
the RESTORED reading (`nestedRecLeaf_typed`), and the restored and the
scratch Π-towers are ONE SET at every frame
(`NestedTailIn.towerAgree`).  The rest is `mutualRecsProvision`'s
assembly at the scratch run's shape. -/
theorem NestedTailIn.scratchProv {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hK35 : NestedRecTysAuxOk p st b stored)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    (R : NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM)
    (E : NestedRecEqs (D) PC (fun ψ => b.elimLevel.eval ψ) rdsM concM eqs)
    (Tu : NestedRecTuple (D) s rdsM concM eqs) :
    ∃ mpP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)),
      ConLeche.EtaFamiliesClosed (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)) ∧
      (∀ c, c < b.k → MutualRecData mpP.base2 (cvRas.getD c default) (DA).nP (DA).k (DA).nCtors
        ((DA).nIdxAt c) c b.elimLevel ((DA).blockRds mpA.base2 b.elimLevel c)) ∧
      (∀ c, c < b.k → ∀ ψ : Name → Nat, mpP.base2.acval (cvRas.getD c default).name ψ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c ψ) ∧
      (∀ c, c < b.k → (cvRas.getD c default).name = b.recName c ∧
        (cvRas.getD c default).levelParams = b.rlps) ∧
      (∀ nm : Name, (∀ c, c < b.k → nm ≠ (cvRas.getD c default).name) →
        mpP.base2.acval nm = mpA.base2.acval nm) := by
  have hdk : (DA).k = b.k := S.record.k
  have hkT : (D).kT = b.k := I.kT
  have hlt : ∀ c, c < (DA).k → c < b.k := fun c hc => by rw [← hdk]; exact hc
  -- **the run shape** of the scratch recursor types (`mutualRecsProvision`'s `hshape`)
  obtain ⟨-, hallR⟩ := ConLeche.checkMutualRecTys_inv S.rectys
  have hshape : ∀ c, c < b.k →
      (cvRas.getD c default).name = b.recName c ∧
      (cvRas.getD c default).levelParams = b.rlps ∧
      (cvRas.getD c default).type.hasFvar = false ∧
      (cvRas.getD c default).type.allLevelParamsDefined b.rlps = true ∧
      (cvRas.getD c default).type.looseBVarsBounded 0 = true ∧
      (cvRas.getD c default).type.constsResolve (ENVA) = true := by
    intro c hc
    obtain ⟨cvRa, hget, hrun⟩ := hallR c hc
    obtain ⟨recTy, sty, u, -, hlp, hres, hbv, hfv, -, -, -, rfl⟩ :=
      ConLeche.checkMutualRecTy_shape hrun
    rw [List.getD_eq_getElem?_getD, hget]
    exact ⟨rfl, rfl, hfv, hlp, hbv, hres⟩
  -- **the recursor names** are free at the scratch environment, reserved-free, not proj-shaped
  have hrecNames := ConLeche.nestedRecNames_of I.hfA I.helim I.hfresh I.hb I.haux I.hstored I.hrm
    I.out.formers I.out.ctors
  -- **the names are distinct** (`mutualRecsProvision`'s `hnd`)
  have hnd : (cvRas.map (·.name)).Nodup := by
    have hmapEq : cvRas.map (·.name) = (List.range b.k).map b.recName := by
      refine List.ext_getElem? fun c => ?_
      rw [List.getElem?_map, List.getElem?_map]
      by_cases hc : c < b.k
      · have hcl : c < cvRas.length := by rw [S.cvLen]; exact hc
        rw [List.getElem?_range hc, List.getElem?_eq_getElem hcl]
        have hn := (hshape c hc).1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl] at hn
        simp only [Option.map_some, Option.some.injEq]
        exact hn
      · rw [List.getElem?_eq_none (by rw [S.cvLen]; omega),
          List.getElem?_eq_none (by rw [List.length_range]; omega)]
        rfl
    rw [hmapEq]
    have h0' := I.out.nodup
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp h0').2.1
  -- **OUR leaf is typed at the SCRATCH reading**: the tower agreement
  have hleaf : ∀ c, c < (DA).k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c ψ) ∧
      interp V ρ (nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c ψ)
        ∈ˢ interp V ρ (mkPisAV ((DA).blockRds mpA.base2 b.elimLevel c ψ)
          (mutualConcAV (DA).k (DA).nCtors ((DA).nIdxAt c) c)) := by
    intro c hc' ψ ρ
    have hc : c < b.k := hlt c hc'
    have hcT : c < (D).kT := by rw [hkT]; exact hc
    have h := nestedRecLeaf_typed R E Tu c hcT ψ ρ
    refine ⟨h.1, ?_⟩
    have hconc : (DA).blockConc c = mutualConcAV (DA).k (DA).nCtors ((DA).nIdxAt c) c := rfl
    have ht := I.towerAgree S hnames hctorsJ hK35 hc ψ ρ (NestedTailIn.readAtOf R hcT ψ)
      (I.lenAtOf R hc ψ)
    rw [← hconc, ← ht]
    exact h.2
  -- **the conses**
  obtain ⟨mpP, hEP, -, hRDP, hleafP, hagP⟩ :=
    recsProvision (k := (DA).k) (nP := (DA).nP) (n := (DA).nCtors) (nIdxOf := (DA).nIdxAt)
      (elimL := b.elimLevel) (rds := (DA).blockRds mpA.base2 b.elimLevel)
      (A := nestedRecLeaf (D).kT s rdsM concM eqs b.rlps) (b := b) (fms := fms) mpA
      (by rw [S.cvLen, hdk]) hleaf
      (fun c _ ψ => nestedRecLeaf_below R E c ψ)
      (fun c hc ψ₁ ψ₂ hφ =>
        nestedRecLeaf_params (by rw [← (hshape c (hlt c hc)).2.1]; exact hφ))
      (fun c hc => by rw [(hshape c (hlt c hc)).1]; exact (hrecNames c (hlt c hc)).2.1)
      (fun c hc => by rw [(hshape c (hlt c hc)).1]; exact (hrecNames c (hlt c hc)).2.2)
      (fun c hc => ⟨(hshape c (hlt c hc)).2.2.1,
        by rw [(hshape c (hlt c hc)).2.1]; exact (hshape c (hlt c hc)).2.2.2.1,
        (hshape c (hlt c hc)).2.2.2.2.1⟩)
      hnd
      (fun c hc => by rw [(hshape c (hlt c hc)).1]; exact (hrecNames c (hlt c hc)).1)
      (fun c hc => (hshape c (hlt c hc)).2.2.2.2.2)
      S.etaA
      (fun c hc => (S.recData c (hlt c hc)).1)
  exact ⟨mpP, hEP, fun c hc => hRDP c (by rw [hdk]; exact hc),
    fun c hc ψ => hleafP c (by rw [hdk]; exact hc) ψ,
    fun c hc => ⟨(hshape c hc).1, (hshape c hc).2.1⟩,
    fun nm hn => hagP nm fun c hc => hn c (hlt c hc)⟩

/-! ## K.35's face AT THE RULES -/

omit I in
/-- **K.35's model face at the RULES** (the type half is
`NestedRecTysAuxOk`, `NestedRecFrames.lean`): every read-back rule's
right-hand side, below its `λ p⃗` prefix, has the shape the restore
walk relies on.  The restore strips exactly `R.nP` binders
(`restoreNested_lams`), so the walk's depth-`0` shape and the Bool's
`stripLams p.nP` agree on the nose. -/
@[expose] def NestedRulesAuxOk (p : NestedParts) (st : ElimState) (b : MutualBlock)
    (stored : List AuxStored) : Prop :=
  ∀ (c : Nat) (a : AuxStored), stored[c]? = some a → ∀ rl ∈ a.rules,
    ∃ (lbs : List (Expr × BinderMeta)) (body : Expr),
      rl.rhs.stripLams b.nP = some (lbs, body) ∧
      ConLeche.AuxAppsOk (ConLeche.restoreTbl p st) b.lps (nestedArityK p st) 0 body

omit I in
/-- **AND IT COMES FROM THE SAME BOOL**: K.35's `nestedAuxAppsOk` is a
conjunction — the recursor type's shape AND every rule's
(`Kernel/Inductives/NestedInstall.lean:1359`) — so the rules' half is
`hall.2` where `nestedRecTysAuxOk_of_bool` reads `hall.1`.  No kernel
work: the record already covers the rules. -/
theorem nestedRulesAuxOk_of_bool (hb : ConLeche.auxBlock p st = some b)
    (h : ConLeche.nestedAuxAppsOk p st stored = true) :
    NestedRulesAuxOk p st b stored := by
  obtain ⟨hnP, hlps, -, -⟩ := ConLeche.auxBlock_fields hb
  intro c a ha rl hrl
  have hmem : a ∈ stored := List.mem_of_getElem? ha
  have hall : ((match a.cvRa.type.stripPis p.nP with
      | some (_, body) => ConLeche.auxAppsOk (ConLeche.restoreTbl p st) p.lps
          (nestedArityK p st) 0 body
      | none => false) &&
      a.rules.all fun rl =>
        match rl.rhs.stripLams p.nP with
        | some (_, body) => ConLeche.auxAppsOk (ConLeche.restoreTbl p st) p.lps
            (nestedArityK p st) 0 body
        | none => false) = true := List.all_eq_true.mp h a hmem
  simp only [Bool.and_eq_true] at hall
  have hrule := List.all_eq_true.mp hall.2 rl hrl
  cases hs : rl.rhs.stripLams p.nP with
  | none => rw [hs] at hrule; exact nomatch hrule
  | some pr =>
    obtain ⟨lbs, body⟩ := pr
    rw [hs] at hrule
    refine ⟨lbs, body, by rw [hnP]; exact hs, ?_⟩
    rw [hlps]
    exact ConLeche.auxAppsOk_reflect body 0 hrule

end Run

end ConLeche.Model
