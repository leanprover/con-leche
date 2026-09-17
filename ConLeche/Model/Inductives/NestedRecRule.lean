module

public import ConLeche.Model.Inductives.NestedRecsStore
public import ConLeche.Model.Inductives.MutualRecsLaw
public import ConLeche.Model.Inductives.NestedRecEqs
import ConLeche.Model.Inductives.MutualRecsProvision
import ConLeche.Model.Inductives.BlockRepCross
import ConLeche.Model.Inductives.MutualRecsSwap
import ConLeche.Model.Inductives.MutualRecsStore
import ConLeche.Model.Inductives.BlockRecBridge
import ConLeche.Verify.Inductives.NestedRecDoor
import ConLeche.Verify.Inductives.NestedRecNames
import ConLeche.Verify.Inductives.NestedRecRuleKit
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

/-! ## The restored recursors' provision, as a reading crossing

`BlockRepCross.lean`'s instance (i) (`provision_hde`) at the NESTED
route's loop.  The three extension facts are
`provisionNestedRecs_extend` (`Verify/Inductives/NestedRecRuleKit.lean`,
which needs no `SetTheory`); here they are fed to
`denoteMeta_env_mono`, exactly as the mutual twin does.
-/

/-- **The provisioned recursors, as an environment extension**
(`provisionMutualRecs_extend`'s twin over the read-back's TRIPLE list):
every stored lookup survives, the literal guards only grow, and no
projection table appears — the three facts `provisionNestedRecs_hde`
rests on.  It lives here, and not beside the kit's other
`provisionNestedRecs` lookup lemmas, because `LitGuardsMono` is a
MODEL-tier definition (`Model/Annot/BitExtend.lean`) — which is why
the mutual twin sits in `BlockRepCross.lean` too. -/
theorem provisionNestedRecs_extend :
    ∀ {l : List (ConstantVal × Nat × Nat)} {env : Env},
      (∀ x ∈ l, env.find? x.1.name = none) →
      (l.map (·.1.name)).Nodup →
      FindPreserved env (ConLeche.provisionNestedRecs l env) ∧
      LitGuardsMono env (ConLeche.provisionNestedRecs l env) ∧
      (∀ (sn : Name) (i : Nat), env.findProj? sn i = none →
        (ConLeche.provisionNestedRecs l env).findProj? sn i = none)
  | [], _, _, _ => ⟨fun h => h, ⟨fun h => h, fun h => h⟩, fun _ _ h => h⟩
  | x :: rest, env, hfresh, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hx : env.find? x.1.name = none := hfresh x List.mem_cons_self
    have hfresh' : ∀ g ∈ rest,
        (Env.mk (ConstantInfo.recInfo x.1 x.2.1 x.2.2 [] :: env.consts)).find? g.1.name = none := by
      intro g hg
      refine (find?_cons_of_name_ne (c := .recInfo x.1 x.2.1 x.2.2 [])
        (fun hh => ?_)).trans (hfresh g (List.mem_cons_of_mem _ hg))
      refine hnd.1 ?_
      have hnm : x.1.name = g.1.name := hh
      rw [hnm]
      exact List.mem_map_of_mem hg
    obtain ⟨hFp, hL, -⟩ := provisionNestedRecs_extend hfresh' hnd.2
    show FindPreserved env
        (ConLeche.provisionNestedRecs rest ⟨.recInfo x.1 x.2.1 x.2.2 [] :: env.consts⟩) ∧ _
    exact ⟨fun h => hFp (findPreserved_cons hx h),
      ⟨fun h => hL.1 ((litGuardsMono_cons hx).1 h),
        fun h => hL.2 ((litGuardsMono_cons hx).2 h)⟩,
      fun sn i h => ConLeche.provisionNestedRecs_findProj?_none sn i h⟩

/-- **`hde` AT THE RESTORED PROVISION** (`provision_hde`'s twin over
the read-back's triples): the models' valuations agree at every stored
name, so a successful reading at the restored constructors'
environment is reproduced at the provisioned one. -/
theorem provisionNestedRecs_hde {l : List (ConstantVal × Nat × Nat)} {env : Env}
    {m : EnvModel V env} {mP : EnvModel V (ConLeche.provisionNestedRecs l env)}
    (hfresh : ∀ x ∈ l, env.find? x.1.name = none)
    (hnd : (l.map (·.1.name)).Nodup)
    (hag : ∀ n : Name, (env.find? n).isSome = true → mP.acval n = m.acval n) :
    ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m.acval env ψ dp e = some ea →
        denoteMeta mP.acval (ConLeche.provisionNestedRecs l env) ψ dp e = some ea := by
  obtain ⟨hFp, hG, hproj⟩ := provisionNestedRecs_extend hfresh hnd
  intro ψ dp e ea hread
  refine denoteMeta_env_mono hFp hG hproj dp e ?_
  rw [← denoteMeta_acval_congr (acval₂ := mP.acval) (fun n hn => (hag n hn).symm) dp e]
  exact hread

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

/-! ## The rule's reading law: the two PROVISIONED environments (item 5 step 2c)

`NestedTailIn.restoreAgree` (`NestedRecFrames.lean`) is the walk's leaf
agreement at the SCRATCH constructors' model against the RESTORED
constructors' one.  That is the right pair for the recursor TYPES,
which mention no recursor name.  A RULE's right-hand side mentions all
`k + nPins` of them, so its law runs one environment later on each
side: the scratch recursors provisioned rule-less at OUR leaves
(`scratchProv`) against the restored ones (`NestedTailIn.provisioned`).

Every clause is either the old record's, transported by the two
provisions' "off the new names the model is the old one" reports, or a
new-name clause discharged by the two leaf reports being ONE function
of the class.  The class bridge is the names: below `p.k` a member's
restored recursor carries the SCRATCH name `b.recName c`
(`recCvNameM`), above it the mimic's carries `p.mimicRecName j`
(`recCvNameN`) while the scratch side keeps `q.aux.str "rec"` — which
is why `recKey` exists and why `leafSome` is stated at a name the
scratch side FINDS (`NestedRecWalk.lean`'s note).
-/

omit I in
/-- An answered key is an entry (`NestedRecFrames.lean`'s own, `private`
there). -/
private theorem rrLookupMem {β : Type} {a : Name} {v : β} :
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
    · exact List.mem_cons_of_mem _ (rrLookupMem h)

/-- **A COPY'S RECURSOR NAME IS ITS CLASS'S** (`pinAuxMem`'s
computation, named): the pin at `q` is the scratch block's member
`p.k + q` (`PinsAligned`), so that member's recursor name is
`q.aux.str "rec"`. -/
theorem NestedTailIn.recNameAux {q : Nat} {qn : NestedPin} (hqn : st.pins[q]? = some qn) :
    b.recName (p.k + q) = qn.aux.str "rec" := by
  obtain ⟨-, hform⟩ := ConLeche.auxBlock_former I.hb
  obtain ⟨t, ht, htn⟩ := I.aligned.2 q qn hqn
  obtain ⟨nIdx, hfo, -⟩ := hform (p.k + q) t ht
  simp only [ConLeche.MutualBlock.recName, List.getD_eq_getElem?_getD, hfo, Option.getD_some, htn]

omit I in
/-- A copy's recursor name IS an auxiliary name — `auxNames`' third
component is that list, which is why the reading law's `const` case
reaches `recKey` and not `leafSome` at a mimic's scratch recursor. -/
theorem NestedTailIn.auxRecMem {q : Nat} {qn : NestedPin} (hqn : st.pins[q]? = some qn) :
    qn.aux.str "rec" ∈ (ConLeche.restoreTbl p st).auxNames := by
  simp only [ConLeche.restoreTbl]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨qn, List.mem_of_getElem? hqn, rfl⟩)

/-- Below `p.k` the scratch block's member name is the DECLARED
member's (`auxBlock_memberNames`). -/
theorem NestedTailIn.memberNameAt {c : Nat} (hc : c < p.k) :
    (b.formers.getD c default).1.name = (p.formers.getD c default).1.name := by
  have hbk : b.k = p.k + pinsS.length := I.out.bk
  obtain ⟨f, hf⟩ : ∃ f, b.formers[c]? = some f :=
    ⟨_, List.getElem?_eq_getElem (by show c < b.k; omega)⟩
  obtain ⟨g, hg⟩ : ∃ g, p.formers[c]? = some g :=
    ⟨_, List.getElem?_eq_getElem (by exact hc)⟩
  have h1 : (b.memberNames.take p.k)[c]? = some f.1.name := by
    rw [List.getElem?_take_of_lt hc]
    simp only [ConLeche.MutualBlock.memberNames, List.getElem?_map, hf, Option.map_some]
  have h2 : p.memberNames[c]? = some g.1.name := by
    simp only [ConLeche.NestedParts.memberNames, List.getElem?_map, hg, Option.map_some]
  rw [ConLeche.auxBlock_memberNames I.hfA I.helim I.hb, h2] at h1
  rw [List.getD_eq_getElem?_getD, hf, List.getD_eq_getElem?_getD, hg]
  exact (Option.some.inj h1).symm

/-- **A MEMBER'S RESTORED RECURSOR CARRIES THE SCRATCH NAME**: the
restore checked it at `T_c.rec` for the DECLARED member `T_c`
(`restoreRecTys_door`'s name clause), and below `p.k` the scratch
block's member IS that member (`memberNameAt`).  This is what makes
`leafSome` — not `recKey` — the clause a member's recursor goes
through. -/
theorem NestedTailIn.recCvNameM {c : Nat} (hc : c < p.k) :
    (nestedRecCvAt p.k cvRms cvRns c).name = b.recName c := by
  obtain ⟨o, ho⟩ : ∃ o, cvRms[c]? = some o :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.lenM]; exact hc)⟩
  have hcv : nestedRecCvAt p.k cvRms cvRns c = o := by
    unfold nestedRecCvAt
    rw [if_pos hc, List.getD_eq_getElem?_getD, ho]
    rfl
  have hnm : ((List.range p.k).map fun mIdx =>
      ((p.formers.getD mIdx default).1.name.str "rec"))[c]?
      = some ((p.formers.getD c default).1.name.str "rec") := by
    rw [List.getElem?_map, List.getElem?_range hc]
    rfl
  obtain ⟨hname, -, -, -⟩ := ConLeche.restoreRecTys_door I.hrm c _ o hnm ho
  rw [hcv, hname]
  unfold ConLeche.MutualBlock.recName
  rw [I.memberNameAt hc]

/-- **A MIMIC'S RESTORED RECURSOR CARRIES THE MINTED NAME**
`p.mimicRecName j` — the `recMap`'s value at the scratch key
`q.aux.str "rec"`. -/
theorem NestedTailIn.recCvNameN {j : Nat} (hj : j < pinsS.length) :
    (nestedRecCvAt p.k cvRms cvRns (p.k + j)).name = p.mimicRecName j := by
  have hck : ¬ (p.k + j < p.k) := by omega
  obtain ⟨o, ho⟩ : ∃ o, cvRns[j]? = some o :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.lenN]; exact hj)⟩
  have hcv : nestedRecCvAt p.k cvRms cvRns (p.k + j) = o := by
    unfold nestedRecCvAt
    rw [if_neg hck, show p.k + j - p.k = j from by omega, List.getD_eq_getElem?_getD, ho]
    rfl
  have hqn : j < p.numNested := by rw [← I.hcount, ← I.out.stage.pinsLen]; exact hj
  have hnm : ((List.range p.numNested).map p.mimicRecName)[j]? = some (p.mimicRecName j) := by
    rw [List.getElem?_map, List.getElem?_range hqn]
    rfl
  obtain ⟨hname, -, -, -⟩ := ConLeche.restoreRecTys_door I.hrn j _ o hnm ho
  rw [hcv, hname]

/-- The provision list's entries are FREE at the restored
constructors' environment (`recCvDoor`, positionally). -/
theorem NestedTailIn.provListFresh :
    ∀ x ∈ nestedProvList p stored cvRms cvRns,
      (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consMutualFormers (fms.take p.k) env)).find? x.1.name = none := by
  intro x hx
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hx
  have hlen := nestedProvList_length (p := p) (stored := stored) (cvRms := cvRms)
    (cvRns := cvRns) (b := b) (pinsS := pinsS) I.lenM I.lenN I.storedLen I.out.bk
  have hcb : c < b.k := by
    have hlt := (List.getElem?_eq_some_iff.mp hc).1
    rw [hlen] at hlt
    rw [I.out.bk]
    exact hlt
  rw [nestedProvList_fst I.lenM I.lenN I.storedLen I.out.bk c x hc]
  exact (I.recCvDoor hcb).1

/-- The provision list's entry at class `c` (`nestedProvList_fst`, with
the position supplied). -/
theorem NestedTailIn.provListAt {c : Nat} (hc : c < b.k) :
    ∃ x ∈ nestedProvList p stored cvRms cvRns, x.1 = nestedRecCvAt p.k cvRms cvRns c := by
  have hlen := nestedProvList_length (p := p) (stored := stored) (cvRms := cvRms)
    (cvRns := cvRns) (b := b) (pinsS := pinsS) I.lenM I.lenN I.storedLen I.out.bk
  obtain ⟨x, hx⟩ : ∃ x, (nestedProvList p stored cvRms cvRns)[c]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlen, ← I.out.bk]; exact hc)⟩
  exact ⟨x, List.mem_of_getElem? hx, nestedProvList_fst I.lenM I.lenN I.storedLen I.out.bk c x hx⟩

/-- An entry of the provision list is some class's restored recursor. -/
theorem NestedTailIn.provListMem {x : ConstantVal × Nat × Nat}
    (hx : x ∈ nestedProvList p stored cvRms cvRns) :
    ∃ c, c < b.k ∧ x.1 = nestedRecCvAt p.k cvRms cvRns c := by
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hx
  have hlen := nestedProvList_length (p := p) (stored := stored) (cvRms := cvRms)
    (cvRns := cvRns) (b := b) (pinsS := pinsS) I.lenM I.lenN I.storedLen I.out.bk
  have hcb : c < b.k := by
    have hlt := (List.getElem?_eq_some_iff.mp hc).1
    rw [hlen] at hlt
    rw [I.out.bk]
    exact hlt
  exact ⟨c, hcb, nestedProvList_fst I.lenM I.lenN I.storedLen I.out.bk c x hc⟩

/-- **THE RULE'S READING LAW: `RestoreAgree` AT THE TWO PROVISIONED
MODELS** (PLAN-M7 §4b, item 5 step 2c).

The scratch side is the auxiliary rules' own environment — the scratch
constructors' consed with the `k` scratch recursors, rule-less, AT OUR
LEAVES (`scratchProv`) — and the restored side the restored rules' own
(`NestedTailIn.provisioned`).  Every clause is the tail's record
(`NestedTailIn.restoreAgree`) transported by the two provisions'
"off the new names the model is the old one" reports, plus the
new-name clauses: a MEMBER's recursor is stored under the SAME name on
both sides and goes through `leafSome` (`recCvNameM`), a MIMIC's under
the scratch key on one side and `p.mimicRecName j` on the other and
goes through `recKey` (`recCvNameN`), and both carry OUR leaf at the
class, so the two leaf reports close them.

Two residues are hypotheses:

* `hauxNe` — no auxiliary name is a restored recursor name.  This is
  the KERNEL's to check (K.43, beside K.39): the mint's copy names and
  the mimics' `T₁.rec_j` are both `Name.appendIndexAfter`-shaped, so
  separating them needs `Nat.repr` injectivity, which is exactly why
  K.39 is a `decide` rather than a proof.  The Bool
  `decide ((restoreTbl p st).auxNames.all fun n =>
  !((cvRms.map (·.name) ++ cvRns.map (·.name)).contains n))` discharges
  it verbatim.
* `hlitP` — the literal readings agree at the provisioned pair.  The
  tail's `litAgree` is the same fact one environment down; crossing it
  needs the basis constants separated from the provisioned recursor
  names, which is the guards' own business (a recursor never satisfies
  `natIndOk`/`listConsTyOk`/…).
The pin arm's container and the constructor arm's restored
constructor are STORED at the restored constructors' environment —
a fact the arms know and, since they package `J`/`newName` inside an
existential, could not be asked for from outside: it is now ONE EXTRA
CONJUNCT of `NestedTailIn.pinArm`/`ctorArm` (the record's own field
drops it), which is why those two arms are consumed here directly
rather than through `hOld`. -/
theorem NestedTailIn.restoreAgreeP {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hndR : (cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    {mpAP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx ENVA)}
    {mpP : EnvModelM V μ
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)}
    (hshapeA : ∀ c, c < b.k → (cvRas.getD c default).name = b.recName c ∧
      (cvRas.getD c default).levelParams = b.rlps)
    (hleafA : ∀ c, c < b.k → ∀ φ : Name → Nat,
      mpAP.base2.acval (cvRas.getD c default).name φ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c φ)
    (hagA : ∀ nm : Name, (∀ c, c < b.k → nm ≠ (cvRas.getD c default).name) →
      mpAP.base2.acval nm = mpA.base2.acval nm)
    (hleafR : ∀ c, c < (D).kT → ∀ φ : Name → Nat,
      mpP.base2.acval (nestedRecCvAt p.k cvRms cvRns c).name φ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c φ)
    (hagR : ∀ nm : Name, (∀ c, c < (D).kT → nm ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      mpP.base2.acval nm = mp₂.base2.acval nm)
    (hauxNe : ∀ n ∈ (ConLeche.restoreTbl p st).auxNames, ∀ c, c < b.k →
      n ≠ (nestedRecCvAt p.k cvRms cvRns c).name)
    (ψ : Name → Nat) :
    RestoreAgree (V := V) (ConLeche.restoreTbl p st) b.lps (nestedArityK p st)
      mpAP.base2.acval mpP.base2.acval
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx ENVA)
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2)
      ψ b.nP ((D).params ψ) := by
  have hkT : (D).kT = b.k := I.kT
  have hbk : b.k = p.k + pinsS.length := I.out.bk
  have hOld := I.restoreAgree S hnames hctorsJ ψ
  have hpinArm := I.pinArm S ψ
  have hctorArm := I.ctorArm S hnames hctorsJ ψ
  rw [I.arityK] at hOld hpinArm hctorArm
  -- **the scratch recursor names are FREE** at the scratch constructors' environment
  have hrecNames := ConLeche.nestedRecNames_of I.hfA I.helim I.hfresh I.hb I.haux I.hstored I.hrm
    I.out.formers I.out.ctors
  -- **the scratch provision's list**: its entries, their freshness, their distinctness
  have hzipMem : ∀ x ∈ cvRas.zipIdx, x.2 < b.k ∧ x.1 = cvRas.getD x.2 default := by
    intro x hx
    have hget : cvRas[x.2]? = some x.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx)
    exact ⟨by rw [← S.cvLen]; exact (List.getElem?_eq_some_iff.mp hget).1,
      by rw [List.getD_eq_getElem?_getD, hget]; rfl⟩
  have hfreshA : ∀ x ∈ cvRas.zipIdx, (ENVA).find? x.1.name = none := by
    intro x hx
    rw [(hzipMem x hx).2, (hshapeA x.2 (hzipMem x hx).1).1]
    exact (hrecNames x.2 (hzipMem x hx).1).1
  have hndA : (cvRas.zipIdx.map (·.1.name)).Nodup := by
    have hmapEq : cvRas.map (·.name) = (List.range b.k).map b.recName := by
      refine List.ext_getElem? fun c => ?_
      rw [List.getElem?_map, List.getElem?_map]
      by_cases hc : c < b.k
      · have hcl : c < cvRas.length := by rw [S.cvLen]; exact hc
        rw [List.getElem?_range hc, List.getElem?_eq_getElem hcl]
        have hn := (hshapeA c hc).1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl] at hn
        simp only [Option.map_some, Option.some.injEq]
        exact hn
      · rw [List.getElem?_eq_none (by rw [S.cvLen]; omega),
          List.getElem?_eq_none (by rw [List.length_range]; omega)]
        rfl
    rw [show cvRas.zipIdx.map (·.1.name) = cvRas.map (·.name) from by
      rw [show (fun x : ConstantVal × Nat => x.1.name) = (fun c : ConstantVal => c.name) ∘ Prod.fst
        from rfl, ← List.map_map, List.zipIdx_map_fst], hmapEq]
    have h0' := I.out.nodup
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp h0').2.1
  -- **the restored provision's list**
  have hfresh3 := I.provListFresh
  have hnd3 : ((nestedProvList p stored cvRms cvRns).map (fun x => x.1.name)).Nodup := by
    rw [nestedProvList_names I.lenM I.lenN I.storedLen I.out.bk]
    exact hndR
  -- **the two provisions' lookups**
  have hfindA_ne : ∀ n : Name, (∀ c, c < b.k → n ≠ (cvRas.getD c default).name) →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? n = (ENVA).find? n := by
    intro n hn
    refine provisionMutualRecs_find?_of_ne (fun x hx => ?_)
    rw [(hzipMem x hx).2]
    exact hn x.2 (hzipMem x hx).1
  have hfindA_mem : ∀ c, c < b.k → ∃ mI rP : Nat,
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? (cvRas.getD c default).name
        = some (.recInfo (cvRas.getD c default) mI rP []) := by
    intro c hc
    have hmem : (cvRas.getD c default, c) ∈ cvRas.zipIdx := by
      refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [S.cvLen]; exact hc)]
      rfl
    exact ⟨_, _, provisionMutualRecs_find?_mem hndA hmem⟩
  have hfindR_ne : ∀ n : Name, (∀ c, c < b.k → n ≠ (nestedRecCvAt p.k cvRms cvRns c).name) →
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find? n
        = (ENV2).find? n := by
    intro n hn
    refine ConLeche.provisionNestedRecs_find?_of_ne (fun x hx => ?_)
    obtain ⟨c, hc, hxe⟩ := I.provListMem hx
    rw [hxe]
    exact hn c hc
  have hfindR_mem : ∀ c, c < b.k → ∃ mI rP : Nat,
      (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)).find?
          (nestedRecCvAt p.k cvRms cvRns c).name
        = some (.recInfo (nestedRecCvAt p.k cvRms cvRns c) mI rP []) := by
    intro c hc
    obtain ⟨x, hx, hxe⟩ := I.provListAt hc
    refine ⟨x.2.1, x.2.2, ?_⟩
    rw [← hxe]
    exact ConLeche.provisionNestedRecs_find?_mem hnd3 hx
  -- **the two agreements at a STORED name** (a provisioned name is fresh below)
  have hagA2 : ∀ nm : Name, ((ENVA).find? nm).isSome = true →
      mpAP.base2.acval nm = mpA.base2.acval nm := by
    intro nm hnm
    refine hagA nm (fun c hc he => ?_)
    rw [he, (hshapeA c hc).1, (hrecNames c hc).1] at hnm
    simp at hnm
  have hagR2 : ∀ nm : Name, ((ENV2).find? nm).isSome = true →
      mpP.base2.acval nm = mp₂.base2.acval nm := by
    intro nm hnm
    refine hagR nm (fun c hc he => ?_)
    rw [hkT] at hc
    rw [he, (I.recCvDoor hc).1] at hnm
    simp at hnm
  -- **the restored reading crosses the restored provision**
  have hdeR := provisionNestedRecs_hde (m := mp₂.base2) (mP := mpP.base2) hfresh3 hnd3 hagR2
  -- **a mimic's SCRATCH recursor name is an auxiliary name**
  have hmimAux : ∀ c, c < b.k → ¬ c < p.k →
      (cvRas.getD c default).name ∈ (ConLeche.restoreTbl p st).auxNames := by
    intro c hc hck
    obtain ⟨j, rfl⟩ : ∃ j, c = p.k + j := ⟨c - p.k, by omega⟩
    have hjS : j < pinsS.length := by rw [hbk] at hc; omega
    have hjl : j < st.pins.length := by rw [← I.out.stage.pinsLen]; exact hjS
    obtain ⟨qn, hqn⟩ : ∃ qn, st.pins[j]? = some qn := ⟨_, List.getElem?_eq_getElem hjl⟩
    rw [(hshapeA _ hc).1, I.recNameAux hqn]
    exact NestedTailIn.auxRecMem hqn
  -- **a restored recursor name that is no scratch one is FRESH below**
  have hrestFresh : ∀ (n : Name) (c : Nat), c < b.k →
      n = (nestedRecCvAt p.k cvRms cvRns c).name →
      (∀ c', c' < b.k → n ≠ (cvRas.getD c' default).name) → (ENV2).find? n = none := by
    intro n c hc hne hnotA
    by_cases hck : c < p.k
    · exact absurd (hne.trans ((I.recCvNameM hck).trans ((hshapeA c hc).1).symm)) (hnotA c hc)
    · obtain ⟨j, rfl⟩ : ∃ j, c = p.k + j := ⟨c - p.k, by omega⟩
      have hjS : j < pinsS.length := by rw [hbk] at hc; omega
      rw [hne, I.recCvNameN hjS]
      exact I.mimicRecFresh hjS
  -- **THE TWO CARRIERS AGREE AT A NAME BOTH PROVISIONED ENVIRONMENTS
  -- FIND** — which is what a literal's reading gives on both sides.  A
  -- MEMBER's recursor is the one name both provisions add, and there the
  -- two leaf reports are one function of the class; off it the name is
  -- stored below on both sides and the tail's record moves it.
  have hbothAg : ∀ m : Name,
      ((ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? m).isSome = true →
      ((ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
        (ENV2)).find? m).isSome = true →
      mpAP.base2.acval m = mpP.base2.acval m ∧
        ConLeche.Verify.levelParamsAt (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)) m
          = ConLeche.Verify.levelParamsAt
            (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) (ENV2)) m := by
    intro m hmA hmR
    -- an auxiliary name is absent from the restored provision
    have hnaux : m ∉ (ConLeche.restoreTbl p st).auxNames := by
      intro hmem
      rw [hfindR_ne m (fun c hc => hauxNe m hmem c hc), I.auxFresh m hmem] at hmR
      simp at hmR
    by_cases hrec : ∃ c, c < b.k ∧ m = (cvRas.getD c default).name
    · -- a SCRATCH recursor name, hence a MEMBER's (a mimic's is auxiliary)
      obtain ⟨c, hc, rfl⟩ := hrec
      have hck : c < p.k := by
        rcases Nat.lt_or_ge c p.k with hck | hck
        · exact hck
        · exact absurd (hmimAux c hc (by omega)) hnaux
      obtain ⟨mI, rP, hfA⟩ := hfindA_mem c hc
      obtain ⟨mI', rP', hfR⟩ := hfindR_mem c hc
      have hnmEq : (nestedRecCvAt p.k cvRms cvRns c).name = (cvRas.getD c default).name := by
        rw [I.recCvNameM hck, ← (hshapeA c hc).1]
      rw [hnmEq] at hfR
      refine ⟨?_, ?_⟩
      · funext φ
        rw [hleafA c hc φ, ← hnmEq]
        exact (hleafR c (by rw [hkT]; exact hc) φ).symm
      · show (match (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find?
              (cvRas.getD c default).name with
            | some ci => ci.toConstantVal.levelParams | none => [])
          = (match (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
              (ENV2)).find? (cvRas.getD c default).name with
            | some ci => ci.toConstantVal.levelParams | none => [])
        rw [hfA, hfR]
        show (cvRas.getD c default).levelParams = (nestedRecCvAt p.k cvRms cvRns c).levelParams
        rw [(hshapeA c hc).2, (I.classRecTy hc).1]
    · -- no provisioned name: the tail's record, transported
      have hne : ∀ c, c < b.k → m ≠ (cvRas.getD c default).name := fun c hc he => hrec ⟨c, hc, he⟩
      rw [hfindA_ne m hne] at hmA
      obtain ⟨ci, hfA⟩ := Option.isSome_iff_exists.mp hmA
      obtain ⟨ci', hf2, hlps, hleaf2⟩ := hOld.leafSome m hnaux ci hfA
      have hfR : (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
          (ENV2)).find? m = some ci' := by
        rw [hfindR_ne m ?_]
        · exact hf2
        · intro c hc he
          rw [hrestFresh m c hc he hne] at hf2
          exact nomatch hf2
      refine ⟨?_, ?_⟩
      · rw [hagA2 m (by rw [hfA]; rfl), hagR2 m (by rw [hf2]; rfl)]
        exact hleaf2
      · show (match (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? m with
            | some ci => ci.toConstantVal.levelParams | none => [])
          = (match (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns)
              (ENV2)).find? m with
            | some ci => ci.toConstantVal.levelParams | none => [])
        rw [hfindA_ne m hne, hfA, hfR]
        exact hlps.symm
  -- a guard that fails at `none` answers only where the name is stored
  have hsomeOf : ∀ (f : Option ConstantInfo → Bool), f none = false →
      ∀ (e : Env) (m : Name), f (e.find? m) = true → (e.find? m).isSome = true := by
    intro f hf e m h
    cases hm : e.find? m with
    | none => rw [hm, hf] at h; exact nomatch h
    | some _ => rfl
  -- **`litEq` AT THE PROVISIONED PAIR** (`litAgree`'s shape: the
  -- readings are compared only where BOTH are `some`, and each side's
  -- guard is what says its environment finds the basis constant)
  have hlitP : ∀ (dpt : Nat) (l : ConLeche.Literal) {A A' : AnnotTerm},
      denoteMeta mpAP.base2.acval (ConLeche.provisionMutualRecs b fms cvRas.zipIdx ENVA) ψ dpt
          (.lit l) = some A →
      denoteMeta mpP.base2.acval
          (ConLeche.provisionNestedRecs (nestedProvList p stored cvRms cvRns) ENV2) ψ dpt
          (.lit l) = some A' → A = A' := by
    intro dpt l A A' hA hA'
    cases l with
    | natVal n =>
      rw [denoteMeta] at hA hA'
      split at hA'
      · next hsupp =>
        split at hA
        · next hsuppA =>
          obtain rfl := Option.some.inj hA
          obtain rfl := Option.some.inj hA'
          simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hsupp hsuppA
          rw [(hbothAg _ (hsomeOf _ rfl _ _ hsuppA.1.2) (hsomeOf _ rfl _ _ hsupp.1.2)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hsuppA.2) (hsomeOf _ rfl _ _ hsupp.2)).1]
        · exact nomatch hA
      · exact nomatch hA'
    | strVal str =>
      rw [denoteMeta] at hA hA'
      split at hA'
      · next hsupp =>
        split at hA
        · next hsuppA =>
          obtain rfl := Option.some.inj hA
          obtain rfl := Option.some.inj hA'
          simp only [ConLeche.strLitSupported, ConLeche.natLitSupported,
            Bool.and_eq_true] at hsupp hsuppA
          obtain ⟨⟨⟨⟨⟨⟨⟨hnat, hstr⟩, hsol⟩, hlist⟩, hnil⟩, hcons⟩, hchar⟩, hcon⟩ := hsupp
          obtain ⟨⟨⟨⟨⟨⟨⟨hnatA, hstrA⟩, hsolA⟩, hlistA⟩, hnilA⟩, hconsA⟩, hcharA⟩, hconA⟩ := hsuppA
          rw [(hbothAg _ (hsomeOf _ rfl _ _ hsolA) (hsomeOf _ rfl _ _ hsol)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hnilA) (hsomeOf _ rfl _ _ hnil)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hconsA) (hsomeOf _ rfl _ _ hcons)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hcharA) (hsomeOf _ rfl _ _ hchar)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hconA) (hsomeOf _ rfl _ _ hcon)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hnatA.1.2) (hsomeOf _ rfl _ _ hnat.1.2)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hnatA.2) (hsomeOf _ rfl _ _ hnat.2)).1,
            (hbothAg _ (hsomeOf _ rfl _ _ hnilA) (hsomeOf _ rfl _ _ hnil)).2,
            (hbothAg _ (hsomeOf _ rfl _ _ hconsA) (hsomeOf _ rfl _ _ hcons)).2]
        · exact nomatch hA
      · exact nomatch hA'
  refine
    { nPEq := I.tblNP
      leafSome := ?_
      auxFresh := ?_
      recKey := ?_
      recNone := ?_
      keyNotRec := I.keyNotRec
      projEq := ?_
      litEq := fun dpt l => hlitP dpt l
      pin := ?_
      ctor := ?_ }
  · -- **`leafSome`**
    intro n hn ci hfind
    by_cases hrec : ∃ c, c < b.k ∧ n = (cvRas.getD c default).name
    · -- a SCRATCH recursor name, hence (off the auxiliary names) a MEMBER's
      obtain ⟨c, hc, rfl⟩ := hrec
      have hck : c < p.k := by
        rcases Nat.lt_or_ge c p.k with hck | hck
        · exact hck
        · exact absurd (hmimAux c hc (by omega)) hn
      obtain ⟨mI, rP, hfR⟩ := hfindR_mem c hc
      obtain ⟨mI', rP', hfA⟩ := hfindA_mem c hc
      refine ⟨.recInfo (nestedRecCvAt p.k cvRms cvRns c) mI rP [], ?_, ?_, ?_⟩
      · rw [(hshapeA c hc).1, ← I.recCvNameM hck]
        exact hfR
      · obtain rfl : ConstantInfo.recInfo (cvRas.getD c default) mI' rP' [] = ci :=
          Option.some.inj (hfA.symm.trans hfind)
        show (nestedRecCvAt p.k cvRms cvRns c).levelParams = (cvRas.getD c default).levelParams
        rw [(I.classRecTy hc).1, (hshapeA c hc).2]
      · funext φ
        rw [hleafA c hc φ, (hshapeA c hc).1, ← I.recCvNameM hck]
        exact (hleafR c (by rw [hkT]; exact hc) φ).symm
    · -- not a scratch recursor name: the tail's record, transported
      have hne : ∀ c, c < b.k → n ≠ (cvRas.getD c default).name := fun c hc he => hrec ⟨c, hc, he⟩
      rw [hfindA_ne n hne] at hfind
      obtain ⟨ci', hf2, hlps, hleaf2⟩ := hOld.leafSome n hn ci hfind
      refine ⟨ci', ?_, hlps, ?_⟩
      · rw [hfindR_ne n ?_]
        · exact hf2
        · intro c hc he
          rw [hrestFresh n c hc he hne] at hf2
          exact nomatch hf2
      · rw [hagA2 n (by rw [hfind]; rfl), hagR2 n (by rw [hf2]; rfl)]
        exact hleaf2
  · -- **`auxFresh`**: the provision adds only the restored recursor names (K.43)
    intro n hn
    rw [hfindR_ne n (fun c hc => hauxNe n hn c hc)]
    exact I.auxFresh n hn
  · -- **`recKey`**: the class the two names share
    intro n n' hr ci hfind
    obtain ⟨j, qn, hqn, hnE, hn'E, hjS, hc⟩ :
        ∃ (j : Nat) (qn : NestedPin), st.pins[j]? = some qn ∧
          n = (cvRas.getD (p.k + j) default).name ∧
          n' = (nestedRecCvAt p.k cvRms cvRns (p.k + j)).name ∧
          j < pinsS.length ∧ p.k + j < b.k := by
      have hmem := rrLookupMem hr
      simp only [ConLeche.restoreTbl, List.mem_map] at hmem
      obtain ⟨⟨q', jq⟩, hqj, hpair⟩ := hmem
      obtain ⟨hn, hn'⟩ := Prod.mk.inj hpair
      have hqn : st.pins[jq]? = some q' := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hqj)
      have hjl : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hqn).1
      have hjS : jq < pinsS.length := by rw [I.out.stage.pinsLen]; exact hjl
      have hc : p.k + jq < b.k := by rw [hbk]; omega
      exact ⟨jq, q', hqn,
        (((hshapeA _ hc).1.trans (I.recNameAux hqn)).trans hn).symm,
        ((I.recCvNameN hjS).trans hn').symm, hjS, hc⟩
    obtain ⟨mI, rP, hfR⟩ := hfindR_mem _ hc
    obtain ⟨mI', rP', hfA⟩ := hfindA_mem _ hc
    refine ⟨.recInfo (nestedRecCvAt p.k cvRms cvRns (p.k + j)) mI rP [], ?_, ?_, ?_⟩
    · rw [hn'E]; exact hfR
    · rw [hnE] at hfind
      obtain rfl : ConstantInfo.recInfo (cvRas.getD (p.k + j) default) mI' rP' [] = ci :=
        Option.some.inj (hfA.symm.trans hfind)
      show (nestedRecCvAt p.k cvRms cvRns (p.k + j)).levelParams
        = (cvRas.getD (p.k + j) default).levelParams
      rw [(I.classRecTy hc).1, (hshapeA _ hc).2]
    · funext φ
      rw [hnE, hn'E, hleafA _ hc φ]
      exact (hleafR _ (by rw [hkT]; exact hc) φ).symm
  · -- **`recNone`**: the scratch provision STORED the key
    intro n n' hr hnone
    exfalso
    have hmem := rrLookupMem hr
    simp only [ConLeche.restoreTbl, List.mem_map] at hmem
    obtain ⟨⟨q', jq⟩, hqj, hpair⟩ := hmem
    obtain ⟨hn, -⟩ := Prod.mk.inj hpair
    have hqn : st.pins[jq]? = some q' := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hqj)
    have hjl : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hqn).1
    have hc : p.k + jq < b.k := by rw [hbk, ← I.out.stage.pinsLen] at *; omega
    obtain ⟨mI', rP', hfA⟩ := hfindA_mem _ hc
    rw [← hn, ← I.recNameAux hqn, ← (hshapeA _ hc).1, hfA] at hnone
    exact nomatch hnone
  · -- **`projEq`**: neither provision is a projection table
    intro sn i
    have hprojA : (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).findProj? sn i
        = (ENVA).findProj? sn i := by
      cases h : (ENVA).findProj? sn i with
      | none => exact (provisionMutualRecs_extend hfreshA hndA).2.2 sn i h
      | some entry =>
        obtain ⟨tbl, h0, hi, rfl⟩ := ConLeche.Env.findProj?_some h
        exact ConLeche.Env.findProj?_of_table
          (provisionMutualRecs_findPreserved hfreshA _ _ h0) hi
    rw [hprojA, ConLeche.provisionNestedRecs_findProj?_eq hfresh3 sn i]
    exact hOld.projEq sn i
  · -- **`pin`**: the tail's arm, crossed to the two provisioned environments
    intro n pin hlook
    obtain ⟨hbnd, ci, J, ψJ, Ds, nIdx, hstJ, hfA, hlpsA, harity, hread, hident⟩ :=
      hpinArm n pin hlook
    have hJ : mpP.base2.acval J = mp₂.base2.acval J := hagR2 J hstJ
    have hnA : mpAP.base2.acval n = mpA.base2.acval n := hagA2 n (by rw [hfA]; rfl)
    refine ⟨hbnd, ci, J, ψJ, Ds, nIdx,
      provisionMutualRecs_findPreserved hfreshA n ci hfA, hlpsA, harity, ?_, ?_⟩
    · intro fvsP d hP
      rw [hJ]
      exact hdeR ψ (b.nP + d) _ (hread fvsP d hP)
    · intro d as xs ρ₀ Es hsp hxs hEs hwd
      rw [hJ] at hwd ⊢
      rw [hnA]
      exact hident d as xs ρ₀ Es hsp hxs hEs hwd
  · -- **`ctor`**: likewise, at the restored constructor's name
    intro n pin newName hfindc
    obtain ⟨hbnd, hpinNone, ci, J, ilvls, ψJ, Ds, nF, hstN, hfA, hlpsA, harity, hhead, hread,
      hident⟩ := hctorArm n pin newName hfindc
    have hJ : mpP.base2.acval newName = mp₂.base2.acval newName := hagR2 newName hstN
    have hnA : mpAP.base2.acval n = mpA.base2.acval n := hagA2 n (by rw [hfA]; rfl)
    refine ⟨hbnd, hpinNone, ci, J, ilvls, ψJ, Ds, nF,
      provisionMutualRecs_findPreserved hfreshA n ci hfA, hlpsA, harity, hhead, ?_, ?_⟩
    · intro fvsP fvs d hP hF
      rw [hJ]
      exact hdeR ψ (b.nP + d) _ (hread fvsP fvs d hP hF)
    · intro d as xs ρ₀ Fs hsp hxs hFs hwd
      rw [hJ] at hwd ⊢
      rw [hnA]
      exact hident d as xs ρ₀ Fs hsp hxs hFs hwd

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

/-! ## The auxiliary rule, generated and read (item 5 step 2d)

The rule law runs between the TWO PROVISIONED models (§U.29 (ee)), and
its right-hand side is the AUXILIARY rule's restored.  So the auxiliary
rule has to be identified with the scratch install's generated one
(`auxStored_rules_eq`, the door's twin at the rules) and read at the
scratch provision AT OUR LEAVES (`ruleRhs_read_of`, which is already
stated at an arbitrary `EnvModel`).
-/

/-- **THE READ-BACK'S RULE IS THE SCRATCH INSTALL'S GENERATED ONE**:
a rule of the read-back's recursor at class `c` is one of class `c`'s
constructors' — the block model's constructor at some position `i`,
the rule's own six fields, and the generated right-hand side at the
block position `minorIdx c i` (`auxStored_rules_eq` for the rule list,
`mutualRules_mem_shape` for the fields, `memberRule_of` for the
generator), with the formers'/constructors'/kinds' runs identified with
the tail's by determinism. -/
theorem NestedTailIn.auxRuleGen {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    {c : Nat} (hc : c < b.k) {a : AuxStored} (ha : stored[c]? = some a)
    {rl : RecRule} (hrl : rl ∈ a.rules) :
    ∃ (i : Nat) (cA : ConstantVal × Nat), ((DA).ctorsM c)[i]? = some cA ∧
      rl.ctor = cA.1.name ∧ rl.nfields = cA.2 ∧ rl.ctorParams = b.nP ∧
      rl.paramsBlind = true ∧ cA.1.levelParams = b.lps ∧
      ConLeche.mutualRecRhs b.lps b.elim b.large b.nP
          (ConLeche.mutualGenData b fms ctorsA kinds).1
          (ConLeche.mutualGenData b fms ctorsA kinds).2 b.recName
          (b.rlps.map Level.param) ((DA).minorIdx c i) = some rl.rhs ∧
      rl.rhs.allLevelParamsDefined b.rlps = true ∧
      rl.rhs.looseBVarsBounded 0 = true ∧ rl.rhs.hasFvar = false := by
  obtain ⟨fms', f₀', ctorsA', sortss', kinds', cvRas', rulesOf, hformers', hf₀', hctors', hkinds',
    hrules, -, -, hrulesEq⟩ := ConLeche.auxStored_rules_eq I.haux I.hstored ha
  -- the runs are the tail's own
  have hfms : fms = fms' := congrArg Prod.snd (Except.ok.inj (I.out.formers.symm.trans hformers'))
  subst hfms
  have hf0 : f₀ = f₀' := Option.some.inj (I.out.facts.first.symm.trans hf₀')
  subst hf0
  have hctA : (ctorsA, sortss) = (ctorsA', sortss') :=
    Except.ok.inj (I.out.ctors.symm.trans hctors')
  have hcA : ctorsA = ctorsA' := congrArg Prod.fst hctA
  subst hcA
  have hkd : kinds = kinds' := Except.ok.inj (I.out.kindsRun.symm.trans hkinds')
  subst hkd
  -- the member's own stage of the rules' run
  obtain ⟨-, hallU⟩ := ConLeche.checkMutualAllRules_inv hrules
  obtain ⟨rules, hget, hrun⟩ := hallU c hc
  have hrulesD : rulesOf.getD c [] = rules := by rw [List.getD_eq_getElem?_getD, hget]; rfl
  rw [hrulesEq, hrulesD] at hrl
  obtain ⟨cr, hcr, kb, eb, rfl⟩ := mutualRules_mem_shape hrl
  -- the constructor and the generator
  obtain ⟨hlenA, hnamesA⟩ := ctorsA_names_of I.out.ctors (ConLeche.checkMutualCore_inv I.haux).2.1
  obtain ⟨i, cA, hi, hnm, hnF, hlps, hgen, hlpsRhs, -, hbv, hfv⟩ :=
    memberRule_of S.record (ConLeche.checkMutualCore_inv I.haux).2.2.2.1 hlenA hnamesA hc hrun hcr
  exact ⟨i, cA, hi, hnm.symm, hnF.symm, rfl, rfl, hlps, hgen, hlpsRhs, hbv, hfv⟩

/-- **THE AUXILIARY RULE'S RIGHT-HAND SIDE READS AT OUR LEAVES**: at
the SCRATCH provision (`scratchProv` — the scratch constructors'
environment consed with the `k` scratch recursors carrying OUR chosen
tuple's projections) the generated right-hand side reads to the
λ-tower `ruleRhsAV` over the rule's binder data with `nestedRecLeaf`
as the recursors.  Pure assembly: `ruleRhs_read_of` is stated at an
arbitrary `EnvModel`, its three model hypotheses are the scratch
ones crossed over the provision (`IsBlockModels.crossEnv`,
`MemberStored.crossEnv`, whose four premises are
`provisionMutualRecs_extend`, `constsResolve_of_findPreserved`,
`scratchProv`'s own agreement and `provision_hde`), and the leaves are
rewritten by `scratchProv`'s leaf report. -/
theorem NestedTailIn.auxRuleRead {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm} {eqs : (Name → Nat) → List AnnotTerm}
    {mpAP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx ENVA)}
    (hshapeA : ∀ c, c < b.k → (cvRas.getD c default).name = b.recName c ∧
      (cvRas.getD c default).levelParams = b.rlps)
    (hleafA : ∀ c, c < b.k → ∀ φ : Name → Nat,
      mpAP.base2.acval (cvRas.getD c default).name φ
        = nestedRecLeaf (D).kT s rdsM concM eqs b.rlps c φ)
    (hagA : ∀ nm : Name, (∀ c, c < b.k → nm ≠ (cvRas.getD c default).name) →
      mpAP.base2.acval nm = mpA.base2.acval nm)
    {c : Nat} (hc : c < b.k) {i : Nat} {cA : ConstantVal × Nat}
    (hi : ((DA).ctorsM c)[i]? = some cA) {rhs : Expr}
    (hgen : ConLeche.mutualRecRhs b.lps b.elim b.large b.nP
      (ConLeche.mutualGenData b fms ctorsA kinds).1
      (ConLeche.mutualGenData b fms ctorsA kinds).2 b.recName
      (b.rlps.map Level.param) ((DA).minorIdx c i) = some rhs)
    (ψ : Name → Nat) :
    denoteMeta mpAP.base2.acval (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)) ψ 0 rhs
      = some ((DA).ruleRhsAV mpA.base2 b.elimLevel
          (fun t' => nestedRecLeaf (D).kT s rdsM concM eqs b.rlps t' ψ) c i cA.2 ψ) := by
  have hkT : (D).kT = b.k := I.kT
  have hdk : (DA).k = b.k := S.record.k
  have h0k : 0 < b.k := by
    have := I.kpos
    have := I.out.bk
    omega
  -- **the scratch provision's list**: its entries, their freshness, their distinctness
  have hrecNames := ConLeche.nestedRecNames_of I.hfA I.helim I.hfresh I.hb I.haux I.hstored I.hrm
    I.out.formers I.out.ctors
  have hzipMem : ∀ x ∈ cvRas.zipIdx, x.2 < b.k ∧ x.1 = cvRas.getD x.2 default := by
    intro x hx
    have hget : cvRas[x.2]? = some x.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx)
    exact ⟨by rw [← S.cvLen]; exact (List.getElem?_eq_some_iff.mp hget).1,
      by rw [List.getD_eq_getElem?_getD, hget]; rfl⟩
  have hfreshA : ∀ x ∈ cvRas.zipIdx, (ENVA).find? x.1.name = none := by
    intro x hx
    rw [(hzipMem x hx).2, (hshapeA x.2 (hzipMem x hx).1).1]
    exact (hrecNames x.2 (hzipMem x hx).1).1
  have hndA : (cvRas.zipIdx.map (·.1.name)).Nodup := by
    have hmapEq : cvRas.map (·.name) = (List.range b.k).map b.recName := by
      refine List.ext_getElem? fun t => ?_
      rw [List.getElem?_map, List.getElem?_map]
      by_cases ht : t < b.k
      · have htl : t < cvRas.length := by rw [S.cvLen]; exact ht
        rw [List.getElem?_range ht, List.getElem?_eq_getElem htl]
        have hn := (hshapeA t ht).1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl] at hn
        simp only [Option.map_some, Option.some.injEq]
        exact hn
      · rw [List.getElem?_eq_none (by rw [S.cvLen]; omega),
          List.getElem?_eq_none (by rw [List.length_range]; omega)]
        rfl
    rw [show cvRas.zipIdx.map (·.1.name) = cvRas.map (·.name) from by
      rw [show (fun x : ConstantVal × Nat => x.1.name) = (fun c : ConstantVal => c.name) ∘ Prod.fst
        from rfl, ← List.map_map, List.zipIdx_map_fst], hmapEq]
    have h0' := I.out.nodup
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp h0').2.1
  -- **the crossing** of the scratch model over the provision
  obtain ⟨hFP, -, -⟩ := provisionMutualRecs_extend (b := b) (fms := fms) hfreshA hndA
  have hF₁ : ∀ (n : Name) (ci : ConstantInfo), (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (ENVA).find? n = some ci →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? n = some ci :=
    fun _ _ _ h => hFP h
  have hagA2 : ∀ nm : Name, ((ENVA).find? nm).isSome = true →
      mpAP.base2.acval nm = mpA.base2.acval nm := by
    intro nm hnm
    refine hagA nm (fun c' hc' he => ?_)
    rw [he, (hshapeA c' hc').1, (hrecNames c' hc').1] at hnm
    simp at hnm
  have hdeA := provision_hde (m := mpA.base2) (mP := mpAP.base2) hfreshA hndA hagA2
  have hrepsP : IsBlockModels mpAP.base2 (DA) :=
    S.reps.crossEnv hF₁ (constsResolve_of_findPreserved hFP) hagA2 hdeA
  have hstoredP : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      MemberStored mpAP.base2 b.lps b.nP f (DA).resSort ((DA).ppsM t) :=
    fun t f hf => (S.memberStored t f hf).crossEnv hF₁ hdeA
  -- **the recursor table at the provision**, with OUR leaves
  have hfR : ∀ t, t < (DA).k → ∃ ci : ConstantInfo,
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx (ENVA)).find? (b.recName t) = some ci ∧
      ci.toConstantVal.levelParams = b.rlps := by
    intro t ht
    rw [hdk] at ht
    have hmem : (cvRas.getD t default, t) ∈ cvRas.zipIdx := by
      refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [S.cvLen]; exact ht)]
      rfl
    refine ⟨.recInfo (cvRas.getD t default) (b.rulePrefix + (fms.getD t default).nIdx)
      b.rulePrefix [], ?_, (hshapeA t ht).2⟩
    rw [← (hshapeA t ht).1]
    exact provisionMutualRecs_find?_mem hndA hmem
  -- **the reading**, and then the leaves rewritten
  rw [ruleRhs_read_of S.record rfl I.out.facts.lenFms h0k
    (ConLeche.checkMutualCore_inv I.haux).2.2.1 (ConLeche.checkMutualCore_inv I.haux).2.2.2.1
    I.out.facts.lenA I.out.facts.lenK
    (ctorsA_names_of I.out.ctors (ConLeche.checkMutualCore_inv I.haux).2.1).2
    (fun _ _ _ _ => ⟨rfl, fun _ => rfl⟩) hrepsP hstoredP hfR (by rw [hdk]; exact hc) hi hgen ψ]
  unfold BlockModel.ruleRhsAV BlockModel.ruleData
  congr 2
  · -- the binder data: the members' and constructors' leaves are the scratch model's
    rw [mutualRuleDataAV_congr (m₂ := mpA.base2) fun cd hcd => by
      obtain ⟨c', j', cA', hc', hj', hname⟩ := (DA).mem_recCds hcd
      obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := S.reps c' hc'
      rw [hname]
      exact congrFun (hagA2 _ (by rw [(hrep.ctors c' j' cA' hc' hj').1]; rfl)) ψ]
    congr 1
    unfold BlockModel.recLs
    refine List.map_congr_left fun t' ht' => ?_
    have ht'' : t' < (DA).k := List.mem_range.mp ht'
    rw [hdk] at ht''
    have ht''' : t' < fms.length := by rw [I.out.facts.lenFms]; exact ht''
    have hfind := (S.memberStored t' (fms.getD t' default)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht''']; rfl)).find
    have hname : (DA).memberName t' = (fms.getD t' default).cvTa.name :=
      mutualBlockModel_memberName
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht''']; rfl)
    exact congrFun (hagA2 _ (by rw [hname, hfind]; rfl)) ψ
  · -- the core: the recursors are OUR leaves
    refine mutualRuleCoreAV_congr_Rof fun i' hi'' => ?_
    obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := S.reps c (by rw [hdk]; exact hc)
    have hj' : i < ((DA).ctorsM c).length := (List.getElem?_eq_some_iff.mp hi).1
    have htgt := hrep.tgt_lt hj' (mem_recIdxOf.mp hi'').1 S.record.pins
    rw [hdk] at htgt
    rw [← (hshapeA _ htgt).1]
    exact hleafA _ htgt ψ

end Run

end ConLeche.Model
