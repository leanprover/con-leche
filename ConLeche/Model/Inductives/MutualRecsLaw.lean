module

public import ConLeche.Model.Inductives.MutualRecsStage
import ConLeche.Model.Inductives.BlockRecBridge
import ConLeche.Model.Inductives.BlockRecValid
import ConLeche.Model.Inductives.BlockRecLeaf
import ConLeche.Model.Inductives.BlockRecEq
import ConLeche.Model.Inductives.BlockRecKit
import ConLeche.Model.Inductives.BlockRecTyped
import ConLeche.Model.Inductives.StructRecLam
import ConLeche.Model.Inductives.FixRecLaw
import ConLeche.Model.Inductives.FixRuleKit
import ConLeche.Model.Inductives.FixIntro
import ConLeche.Model.Inductives.StructRecLawKit
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Inductives.StructStageFormer
import ConLeche.Model.Inductives.StructEntryKit2
import ConLeche.Model.Inductives.MutualLeafBelow
import ConLeche.Model.IndStageKit
import ConLeche.Model.Levels
import ConLeche.Model.Steps.BitLevels
import ConLeche.Model.Steps.IrrelFast
import ConLeche.Semantics.Tower.FixRecCoreI
import ConLeche.Semantics.Tower.SumRec
public section

/-!
# The rule law at the datum (task #315 U-9, M4 s4b)

The stored rules of a block's recursors fire in the model
(`RecRuleLaw`, `Annot/EnvModelM.lean`): at every level assignment and
every fitting spine, member `t`'s recursor at the spine and constructor
`(t, j)`'s value is the rule's right-hand side at the spine's prefix
and the constructor's fields.  Two facts make the law at the uniform
datum:

* **The equation.**  The chosen tuple satisfies rule `(t, j)`'s
  equation `specEqAV` at the tuple frame (`ProvisionedRecs.iota`,
  `blockRecs_iota`): at every fitting spine, the tuple's member `t`
  applied to the parameters, motives, minors, the constructor's index
  readings and the constructor's value is the rule core — with the
  TUPLE's variables as the recursors.  `BlockRecBridge.lean` turns the
  tuple's variables into the leaves (`interp_specRuleCoreAV_leaf`),
  which is what the rule's right-hand side reads to
  (`denoteMeta_mutualRecRhs`: the λ-tower `ruleRhsAV` over the rule's
  binder data with the leaves as the recursors).
* **The fibre's converse.**  The kernel's rule is `paramsBlind`: the
  major's parameters are not compared with the recursor's.  The
  constructor's value ignores its parameters (`BlockRep.ctor`: an
  injection of the field spine), and the major's membership in the
  member's carrier at the RECURSOR's parameters (the recursor spine's
  fit) decodes it (`BlockRep.fibre`, `mkInj`): the fields fit at the
  recursor's parameters and the index arguments are the constructor's
  index readings there — so the equation applies at the recursor's own
  parameter spine, and no index pin (`IotaIndexPin`) is consumed.

The right-hand side's grading (`ruleRhs_wdV`) is the equation's
(`blockEq_wd`, `blockEq_valid`) carried across the bridge: the rule's
λ-tower over the equation's own domains, its body the core with the
leaves, typed by the minor's conclusion at the rule's frame
(`ruleConcAV`, `minor_conc`, `minor_fold_mem`).

At a `Prop`-valued elimination (`ℓ = 0`) both sides of the law are the
point (the recursor's type and the rule's binders carry the zero bit),
as on the fixpoint route (`fixRecLawCore`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w u

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The rule's right-hand side at the datum -/

namespace BlockRepData

variable (d : BlockRepData V)

/-- **Rule `(c, j)`'s binder data** at the datum's readings. -/
@[expose] def ruleData (m : EnvModel V env) (elimL : Level) (c j : Nat) (ψ : Name → Nat) :
    List (Nat × AnnotTerm) :=
  mutualRuleDataAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL (d.recPps ψ) (d.recIpss ψ) (d.recCds ψ)
    d.recMots d.recTgts (d.dsF c j ψ)

/-- **Rule `(c, j)`'s right-hand side** with the recursors `Rof`: the
λ-tower over the rule's binder data of the `k`-motive rule core. -/
@[expose] def ruleRhsAV (m : EnvModel V env) (elimL : Level) (Rof : Nat → AnnotTerm)
    (c j nF : Nat) (ψ : Name → Nat) : AnnotTerm :=
  mkLamsAV (d.ruleData m elimL c j ψ)
    (mutualRuleCoreAV (pwBit ψ (Level.zeronessOf elimL)) Rof (d.tgts c j) d.nP d.k d.nCtors nF
      (d.minorIdx c j) (ConLeche.recIdxOf (d.ksF c j)) (d.tssF c j ψ) (d.eissF c j ψ))

/-- **The minor's conclusion at the rule's frame**: member `c`'s motive
at the constructor's index readings (moved under the `k + n` motives
and minors) and the constructor at the parameters and fields. -/
@[expose] def ruleConcAV (m : EnvModel V env) (c j nF : Nat) (ψ : Name → Nat) (C : Name) :
    AnnotTerm :=
  AnnotTerm.mkAppN (.bvar (nF + (d.k + d.nCtors) - 1 - c))
    (((d.esF c j ψ).map fun E => E.liftN (d.k + d.nCtors) nF) ++
      [AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt d.nP (d.nP + (d.k + d.nCtors) + nF) ++
        fieldBvars nF)])

end BlockRepData

/-! ## Domain lists -/

omit [SetTheory V] in
/-- `getD_range_map` at any universe. -/
theorem getD_range_map' {α : Type u} (g : Nat → α) (k t : Nat) (h : t < k) (d : α) :
    ((List.range k).map g).getD t d = g t := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

omit [SetTheory V] in
/-- The equation's binder triples over the rule data's pairs read the
same domains. -/
theorem map_ruleDoms (L : List (Nat × Nat × AnnotTerm)) :
    (((L.map fun q : Nat × Nat × AnnotTerm => (q.2.1, q.2.2)).map
        fun q : Nat × AnnotTerm => ((0 : Nat), (0 : Nat), q.2)).map (·.2.2))
      = L.map (·.2.2) := by
  rw [List.map_map, List.map_map]
  rfl

omit [SetTheory V] in
theorem map_ruleDoms' (L : List (Nat × Nat × AnnotTerm)) :
    (L.map fun q : Nat × Nat × AnnotTerm => (q.2.1, q.2.2)).map (·.2) = L.map (·.2.2) := by
  rw [List.map_map]
  rfl

/-! ## The right-hand side, graded -/

/-- **The rule's right-hand side is graded at every frame** (`blockEq_wd`
and `blockEq_valid` carried across the bridge): the λ-tower over the
rule's binder data with the leaves `Rof` as the recursors, at a tuple
`rs` of the leaves' values typed at the recursor types. -/
theorem BlockReps.ruleRhs_wdV {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) (hcT : CtorsTyped m d ψ)
    (hval : ∀ (n : Name) (ρ : Nat → V), AnnotValid V ρ (m.acval n ψ))
    {elimL : Level}
    (hR : BlockReadings m d ψ elimL (d.recLs m ψ) d.recNIdxs (d.recPps ψ) (d.recIpss ψ) (d.recCds ψ)
      d.recMots d.recTgts)
    (hokT : ∀ mm, mm < d.k → ∀ ρ : Nat → V,
      WellDenotedV V ρ (mkPisAV (d.blockRds m elimL mm ψ) (d.blockConc mm)))
    (ρ : Nat → V) {rs : List V} (hlen : rs.length = d.k)
    (hrs : ∀ mm, mm < d.k → rs.getD mm pt ∈ˢ interp V ρ
      (mkPisAV (d.blockRds m elimL mm ψ) (d.blockConc mm)))
    {Rof : Nat → AnnotTerm} (hRcl : ∀ t, t < d.k → Term.bvarsBelow 0 (Rof t).erase)
    (hRok : ∀ t, t < d.k → ∀ σ : Nat → V, WellDenotedV V σ (Rof t))
    (hRval : ∀ t, t < d.k → ∀ σ : Nat → V, interp V σ (Rof t) = rs.getD t pt)
    {c : Nat} (hc : c < d.k) {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) :
    WellDenotedV V ρ (d.ruleRhsAV m elimL Rof c j cA.2 ψ) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hj' : j < (d.ctorsM c).length := (List.getElem?_eq_some_iff.mp hj).1
  have hk : 0 < d.k := by omega
  have hpl := hreps.params_length hk ψ
  have hb : pwBit ψ (Level.zeronessOf elimL) = 0 ↔ elimL.eval ψ = 0 := pwBit_zeronessOf ψ elimL
  have hJ := d.minorIdx_lt hc hj'
  have hlenLc : (d.recLs m ψ).length + (d.recCds ψ).length = d.k + d.nCtors := by
    rw [hR.lsLen, hR.cdsLen]
  have hppsLen : (d.recPps ψ).length = d.nP := by
    have hl := congrArg List.length hR.ppsDom
    rw [List.length_map, hpl] at hl
    exact hl
  have hρcD : ∀ t, t < d.k → consList rs ρ (d.k - 1 - t) = rs.getD t pt := by
    intro t ht
    rw [consList_apply_lt' _ _ (by omega), hlen, show d.k - 1 - (d.k - 1 - t) = t from by omega]
  -- the equation's grading and validity at the tuple frame
  have hokT' : ∀ mm, mm < d.k → ∀ ρ' : Nat → V,
      WellDenotedV V ρ' (mkPisAV (mutualRecDataAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL
        (d.recPps ψ) (d.recIpss ψ) (d.recCds ψ) d.recMots d.recTgts mm)
        (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)) := hokT
  have hrs' : ∀ mm, mm < d.k → rs.getD mm pt ∈ˢ interp V ρ
      (mkPisAV (mutualRecDataAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL (d.recPps ψ) (d.recIpss ψ)
        (d.recCds ψ) d.recMots d.recTgts mm) (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)) := hrs
  have hwdEq := hreps.blockEq_wd hfT hcT hR (fun mm hmm ρ' => (hokT' mm hmm ρ').1) ρ hlen hrs' hc hj
  have hvEq := hreps.blockEq_valid hfT hcT hval hR hokT' ρ hlen hrs' hc hj
  unfold specEqAV at hwdEq hvEq
  obtain ⟨-, hbodyW⟩ := WellDenoted_mkPisAV_inv hwdEq
  obtain ⟨-, hbodyV⟩ := AnnotValid_mkPisAV_inv hvEq
  -- the rule data's domains: the prefix and the lifted fields
  have hbelowPre : DomsBelow 0 (recPrefixAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL (d.recPps ψ)
      (d.recIpss ψ) (d.recCds ψ) d.recMots d.recTgts) := by
    have := hR.below c hc
    rw [mutualRecDataAV_eq_prefix] at this
    exact DomsBelow.append_left this
  have hpreLen : (recPrefixAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL (d.recPps ψ) (d.recIpss ψ)
      (d.recCds ψ) d.recMots d.recTgts).length = d.nP + d.k + d.nCtors := by
    unfold recPrefixAV
    rw [List.length_append, List.length_append, rebit_length, motivesDataGo_length,
      fixMinorsDataM_length, hppsLen, hR.lsLen, hR.cdsLen]
  have hdrop : DomsBelow d.nP ((d.dsF c j ψ).drop d.nP) := by
    have hdr := DomsBelow.drop (k := 0) d.nP (hcd.below ψ)
    simpa using hdr
  have hfieldsB : DomsBelow (0 + (recPrefixAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL (d.recPps ψ)
      (d.recIpss ψ) (d.recCds ψ) d.recMots d.recTgts).length)
      (rebit (pwBit ψ (Level.zeronessOf elimL))
        (liftDoms ((d.recLs m ψ).length + (d.recCds ψ).length) 0 ((d.dsF c j ψ).drop d.nP))) := by
    rw [hpreLen]
    have hlift := domsBelow_liftDoms (n := (d.recLs m ψ).length + (d.recCds ψ).length) (kk := 0) hdrop
    exact domsBelow_rebit (domsBelow_mono (by rw [hR.lsLen, hR.cdsLen]; omega) hlift)
  -- the rule data as a list of triples
  have hLdef : d.ruleData m elimL c j ψ
      = (recPrefixAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL (d.recPps ψ) (d.recIpss ψ) (d.recCds ψ)
          d.recMots d.recTgts ++
        rebit (pwBit ψ (Level.zeronessOf elimL))
          (liftDoms ((d.recLs m ψ).length + (d.recCds ψ).length) 0 ((d.dsF c j ψ).drop d.nP))).map
        fun q : Nat × Nat × AnnotTerm => (q.2.1, q.2.2) := by
    unfold BlockRepData.ruleData mutualRuleDataAV recPrefixAV
    simp only [List.append_assoc]
  have hL0 : DomsBelow 0 (recPrefixAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL (d.recPps ψ)
      (d.recIpss ψ) (d.recCds ψ) d.recMots d.recTgts ++
      rebit (pwBit ψ (Level.zeronessOf elimL))
        (liftDoms ((d.recLs m ψ).length + (d.recCds ψ).length) 0 ((d.dsF c j ψ).drop d.nP))) :=
    domsBelow_append hbelowPre hfieldsB
  have hdomsEq : ((d.ruleData m elimL c j ψ).map fun q : Nat × AnnotTerm =>
      ((0 : Nat), (0 : Nat), q.2)).map (·.2.2)
      = (recPrefixAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL (d.recPps ψ) (d.recIpss ψ) (d.recCds ψ)
          d.recMots d.recTgts).map (·.2.2) ++
        (rebit (pwBit ψ (Level.zeronessOf elimL))
          (liftDoms ((d.recLs m ψ).length + (d.recCds ψ).length) 0 ((d.dsF c j ψ).drop d.nP))).map
          (·.2.2) := by
    rw [hLdef, map_ruleDoms, List.map_append]
  -- the λ-tower: bits and the walk
  unfold BlockRepData.ruleRhsAV
  rw [hLdef]
  refine ⟨mkLamsAV_bits_wellDenoted (m := pwBit ψ (Level.zeronessOf elimL))
    (T := d.ruleConcAV m c j cA.2 ψ cA.1.name) (fun q hq => ?_) ?_, mkLamsAV_bits_validV ?_⟩
  · -- every binder carries the elimination bit
    have hmem : (q.2.1, q.2.2) ∈ mutualRuleDataAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL
        (d.recPps ψ) (d.recIpss ψ) (d.recCds ψ) d.recMots d.recTgts (d.dsF c j ψ) := by
      show _ ∈ d.ruleData m elimL c j ψ
      rw [hLdef]; exact List.mem_map_of_mem hq
    have := mem_mutualRuleDataAV hmem
    simp only at this
    rw [this]
  · -- the walk: domains graded, the body typed by the minor's conclusion
    refine underTowerOk_of_fieldsOkB ?_ ?_
    · -- **the domains**
      rw [List.map_append]
      refine FieldsOkB.append ?_ fun xs hxs => ?_
      · have := (WellDenoted_mkPisAV_inv (hokT' c hc ρ).1).1
        rw [mutualRecDataAV_eq_prefix, List.map_append] at this
        exact FieldsOkB.append_left this
      · obtain ⟨ps, Msl, msl, rfl, hF⟩ := spineFit_prefix_inv hR hxs
        have hρp : Sat V (d.params ψ).reverse (consList ps ρ) := d.satOfSpine hF.params
        rw [rebit_map_dom]
        refine fieldsOkB_liftDoms _ _ _ ?_
        rw [consList_append, consList_append, ← consList_append Msl msl,
          show (d.recLs m ψ).length + (d.recCds ψ).length = (Msl ++ msl).length from by
            rw [List.length_append, hF.mslLen, hF.minsLen, hlenLc],
          shiftE_consList, ← BlockRep.Fss_getD hj]
        exact (h.ctor_okB hj hρp).1
    · -- **the body at a fitting spine**
      intro xs hxs
      have hxs₀ := hxs
      rw [List.map_append] at hxs
      obtain ⟨xs₁, fs, rfl, hpre, hfsL⟩ := spineFit_append_inv hxs
      obtain ⟨ps, Msl, msl, rfl, hF⟩ := spineFit_prefix_inv hR hpre
      have hlenps : ps.length = d.nP := by rw [hF.params.length_eq, hpl]
      have hρp : Sat V (d.params ψ).reverse (consList ps ρ) := d.satOfSpine hF.params
      have hbP : DomsBelow 0 (rebit (pwBit ψ (Level.zeronessOf elimL)) (d.recPps ψ)) :=
        DomsBelow.append_left (DomsBelow.append_left hbelowPre)
      have hpsC : SpineFit (consList rs ρ) (d.params ψ) ps := by
        have := spineFit_transport₀ hbP (ρ₁ := ρ) (ρ₂ := consList rs ρ)
          (by rw [rebit_map_dom, hR.ppsDom]; exact hF.params)
        rw [rebit_map_dom, hR.ppsDom] at this
        exact this
      have hlenfs : fs.length = cA.2 := by
        rw [hfsL.length_eq, List.length_map, rebit_length, liftDoms_length, List.length_drop, hcd.len]
        omega
      have hlenMm : (d.recLs m ψ).length + (d.recCds ψ).length = (Msl ++ msl).length := by
        rw [List.length_append, hF.mslLen, hF.minsLen, hlenLc]
      have hfs : SpineFit (consList ps ρ) ((d.Fss c ψ).getD j []) fs := by
        rw [rebit_map_dom, spineFit_liftDoms, consList_append, consList_append,
          ← consList_append Msl msl, hlenMm, shiftE_consList] at hfsL
        rw [BlockRep.Fss_getD hj]; exact hfsL
      have hfs' : SpineFit (consList ps (consList rs ρ)) ((d.Fss c ψ).getD j []) fs := by
        rw [BlockRep.Fss_getD hj] at hfs ⊢
        exact spineFit_transport (DomsBelow.drop d.nP (hcd.below ψ)) (by rw [hlenps, Nat.zero_add]) hfs
      -- the same spine fits at the tuple frame
      have hxsσ : SpineFit (consList rs ρ)
          (((d.ruleData m elimL c j ψ).map fun q : Nat × AnnotTerm =>
            ((0 : Nat), (0 : Nat), q.2)).map (·.2.2)) (ps ++ Msl ++ msl ++ fs) := by
        rw [hdomsEq, ← List.map_append]
        exact spineFit_transport₀ hL0 hxs₀
      have hfrσ : consList (ps ++ Msl ++ msl ++ fs) (consList rs ρ)
          = consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))) := by
        simp only [consList_append]
      have hfrρ : consList (ps ++ Msl ++ msl ++ fs) ρ
          = consList fs (consList msl (consList Msl (consList ps ρ))) := by
        simp only [consList_append]
      -- the core with the tuple's variables, graded and valid at the tuple frame
      have hwdT := hbodyW _ hxsσ
      have hvT := hbodyV _ hxsσ
      rw [hfrσ, WellDenoted_eqE] at hwdT
      rw [hfrσ, AnnotValid_eqE] at hvT
      -- the inductive hypotheses' applications (at the tuple frame)
      have hih := fun i (hiI : i ∈ ConLeche.recIdxOf (d.ksF c j)) =>
        hreps.ihApp_facts hfT hR ρ hlen hrs' hc hj hpre hF hpsC hfs hfs' hiI
      -- the bridge's premises: the tuple's variables read to the leaves
      have hbr : ∀ i ∈ ConLeche.recIdxOf (d.ksF c j), ∀ bs : List V,
          bs.length = ((d.tssF c j ψ).getD i []).length →
          interp V (consList bs (consList fs (consList msl (consList Msl (consList ps (consList rs ρ))))))
              (tupleVarAV d.k (d.nP + d.k + d.nCtors + cA.2 + ((d.tssF c j ψ).getD i []).length)
                (d.tgts c j i))
            = interp V (consList bs (consList fs (consList msl (consList Msl (consList ps (consList rs ρ))))))
              (Rof (d.tgts c j i)) := by
        intro i hiI bs hbs
        have htgt : d.tgts c j i < d.k := h.tgtsLt c j i hc hj' (mem_recIdxOf.mp hiI).1
        rw [← hbs, interp_tupleVarAV_at hlenps hF.mslLen hF.minsLen hlenfs, hρcD _ htgt,
          hRval _ htgt]
      have hbrW : ∀ i ∈ ConLeche.recIdxOf (d.ksF c j), ∀ bs : List V,
          bs.length = ((d.tssF c j ψ).getD i []).length →
          WellDenoted V (consList bs (consList fs (consList msl (consList Msl (consList ps (consList rs ρ))))))
            (Rof (d.tgts c j i)) := by
        intro i hiI bs _
        exact (hRok _ (h.tgtsLt c j i hc hj' (mem_recIdxOf.mp hiI).1) _).1
      have hbrV : ∀ i ∈ ConLeche.recIdxOf (d.ksF c j), ∀ bs : List V,
          bs.length = ((d.tssF c j ψ).getD i []).length →
          AnnotValid V (consList bs (consList fs (consList msl (consList Msl (consList ps (consList rs ρ))))))
            (Rof (d.tgts c j i)) := by
        intro i hiI bs _
        exact (hRok _ (h.tgtsLt c j i hc hj' (mem_recIdxOf.mp hiI).1) _).2
      -- the core with the leaves, at the tuple frame
      have hwdL := WellDenoted_specRuleCoreAV_leaf hbr hbrW hwdT.2
      have hvL := AnnotValid_specRuleCoreAV_leaf hbrV hvT.2
      have hvalL := interp_specRuleCoreAV_leaf (b := pwBit ψ (Level.zeronessOf elimL))
        (J := d.minorIdx c j) (Eiss := d.eissF c j ψ) hbr
      -- the core is closed under the rule's binders
      have hcl : Term.bvarsBelow (ps ++ Msl ++ msl ++ fs).length
          (mutualRuleCoreAV (pwBit ψ (Level.zeronessOf elimL)) Rof (d.tgts c j) d.nP d.k d.nCtors cA.2
            (d.minorIdx c j) (ConLeche.recIdxOf (d.ksF c j)) (d.tssF c j ψ) (d.eissF c j ψ)).erase := by
        refine mutualRuleCoreAV_below
          (fun i hi => hRcl _ (h.tgtsLt c j i hc hj' (mem_recIdxOf.mp hi).1)) hk (fun i hi => ?_)
          (hcd.tssBelow ψ) (hcd.eissBelow ψ) ?_
        · rw [← hcd.ksLen]; exact (mem_recIdxOf.mp hi).1
        · simp only [List.length_append, hlenps, hF.mslLen, hF.minsLen, hlenfs]
          omega
      have hagree : ∀ i, i < (ps ++ Msl ++ msl ++ fs).length →
          consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))) i
            = consList fs (consList msl (consList Msl (consList ps ρ))) i := by
        rw [← hfrσ, ← hfrρ]
        exact consList_agree_below _ _ _
      have hI := interp_congr_below V _ _ _ _ hcl hagree
      refine ⟨?_, ?_, ?_⟩
      · -- graded
        rw [hfrρ]
        exact (WellDenoted_congr_below _ _ _ _ hcl hagree).mp hwdL
      · -- typed by the minor's conclusion
        rw [hfrρ, ← hI, ← hvalL]
        -- the core's value: the minor at the fields and the ih values
        unfold specRuleCoreAV
        rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList fs (consList msl (consList Msl
          (consList ps (consList rs ρ)))))) (g := SetTheory.app), List.map_append, interp_bvar,
          show cA.2 + d.nCtors - 1 - d.minorIdx c j = (d.nCtors - 1 - d.minorIdx c j) + fs.length from by
            rw [hlenfs]; omega,
          consList_apply_add, consList_apply_lt' _ _ (by rw [hF.minsLen]; omega), hF.minsLen,
          show d.nCtors - 1 - (d.nCtors - 1 - d.minorIdx c j) = d.minorIdx c j from by omega,
          show fieldBvars cA.2 = (List.range cA.2).map (fun k => AnnotTerm.bvar (cA.2 - 1 - k)) from rfl,
          map_fieldBvars_interp hlenfs, List.map_map]
        simp only [Function.comp_def]
        -- the minor's conclusion at the rule's frame
        have hoJ : Msl.length + (msl.take (d.minorIdx c j)).length = d.k + d.minorIdx c j := by
          rw [hF.mslLen, List.length_take, hF.minsLen]; congr 1; exact Nat.min_eq_left (Nat.le_of_lt hJ)
        have ho : Msl.length + msl.length = d.k + d.nCtors := by rw [hF.mslLen, hF.minsLen]
        have hconc := hreps.minor_conc hfT hc hj hρp (Msl := Msl) (msl' := msl) ho hF.mslLen hF.motives hfs
        unfold BlockRepData.ruleConcAV
        rw [hconc.1]
        refine hreps.minor_fold_mem hfT hc hj hρp (Msl := Msl) (msl' := msl.take (d.minorIdx c j)) hoJ
          hF.mslLen hF.motives hb (hF.minors c j cA hc hj) hfs (by rw [List.length_map]) ?_
        intro l hl
        rw [List.length_map] at hl
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some,
          Option.getD_some]
        have hiI : (ConLeche.recIdxOf (d.ksF c j))[l] ∈ ConLeche.recIdxOf (d.ksF c j) := List.getElem_mem hl
        have hgetD : (ConLeche.recIdxOf (d.ksF c j)).getD l 0 = (ConLeche.recIdxOf (d.ksF c j))[l] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
        rw [hgetD]
        exact (hih _ hiI).2
      · -- the `Prop` regime: the conclusion is a truth value
        intro hb0
        rw [hfrρ]
        have ho : Msl.length + msl.length = d.k + d.nCtors := by rw [hF.mslLen, hF.minsLen]
        have hconc := hreps.minor_conc hfT hc hj hρp (Msl := Msl) (msl' := msl) ho hF.mslLen hF.motives hfs
        unfold BlockRepData.ruleConcAV
        rw [hconc.1]
        have := hconc.2
        rwa [hb.mp hb0, univ_zero] at this
  · -- **bit-valid**
    refine underTowerValid_of_fieldsValid ?_ fun xs hxs => ?_
    · rw [List.map_append]
      refine FieldsValid.append ?_ fun xs hxs => ?_
      · have := (AnnotValid_mkPisAV_inv (hokT' c hc ρ).2).1
        rw [mutualRecDataAV_eq_prefix, List.map_append] at this
        exact FieldsValid.append_left this
      · obtain ⟨ps, Msl, msl, rfl, hF⟩ := spineFit_prefix_inv hR hxs
        have hρp : Sat V (d.params ψ).reverse (consList ps ρ) := d.satOfSpine hF.params
        rw [rebit_map_dom]
        refine fieldsValid_liftDoms _ _ _ ?_
        rw [consList_append, consList_append, ← consList_append Msl msl,
          show (d.recLs m ψ).length + (d.recCds ψ).length = (Msl ++ msl).length from by
            rw [List.length_append, hF.mslLen, hF.minsLen, hlenLc],
          shiftE_consList, ← BlockRep.Fss_getD hj]
        exact (h.ctor_validV hj hρp).1
    · have hxs₀ := hxs
      rw [List.map_append] at hxs
      obtain ⟨xs₁, fs, rfl, hpre, hfsL⟩ := spineFit_append_inv hxs
      obtain ⟨ps, Msl, msl, rfl, hF⟩ := spineFit_prefix_inv hR hpre
      have hlenps : ps.length = d.nP := by rw [hF.params.length_eq, hpl]
      have hlenfs : fs.length = cA.2 := by
        rw [hfsL.length_eq, List.length_map, rebit_length, liftDoms_length, List.length_drop, hcd.len]
        omega
      have hxsσ : SpineFit (consList rs ρ)
          (((d.ruleData m elimL c j ψ).map fun q : Nat × AnnotTerm =>
            ((0 : Nat), (0 : Nat), q.2)).map (·.2.2)) (ps ++ Msl ++ msl ++ fs) := by
        rw [hdomsEq, ← List.map_append]
        exact spineFit_transport₀ hL0 hxs₀
      have hfrσ : consList (ps ++ Msl ++ msl ++ fs) (consList rs ρ)
          = consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))) := by
        simp only [consList_append]
      have hfrρ : consList (ps ++ Msl ++ msl ++ fs) ρ
          = consList fs (consList msl (consList Msl (consList ps ρ))) := by
        simp only [consList_append]
      have hvT := hbodyV _ hxsσ
      rw [hfrσ, AnnotValid_eqE] at hvT
      have hbrV : ∀ i ∈ ConLeche.recIdxOf (d.ksF c j), ∀ bs : List V,
          bs.length = ((d.tssF c j ψ).getD i []).length →
          AnnotValid V (consList bs (consList fs (consList msl (consList Msl (consList ps (consList rs ρ))))))
            (Rof (d.tgts c j i)) := by
        intro i hiI bs _
        exact (hRok _ (h.tgtsLt c j i hc hj' (mem_recIdxOf.mp hiI).1) _).2
      have hvL := AnnotValid_specRuleCoreAV_leaf hbrV hvT.2
      have hcl : Term.bvarsBelow (ps ++ Msl ++ msl ++ fs).length
          (mutualRuleCoreAV (pwBit ψ (Level.zeronessOf elimL)) Rof (d.tgts c j) d.nP d.k d.nCtors cA.2
            (d.minorIdx c j) (ConLeche.recIdxOf (d.ksF c j)) (d.tssF c j ψ) (d.eissF c j ψ)).erase := by
        refine mutualRuleCoreAV_below
          (fun i hi => hRcl _ (h.tgtsLt c j i hc hj' (mem_recIdxOf.mp hi).1)) hk (fun i hi => ?_)
          (hcd.tssBelow ψ) (hcd.eissBelow ψ) ?_
        · rw [← hcd.ksLen]; exact (mem_recIdxOf.mp hi).1
        · simp only [List.length_append, hlenps, hF.mslLen, hF.minsLen, hlenfs]
          omega
      have hagree : ∀ i, i < (ps ++ Msl ++ msl ++ fs).length →
          consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))) i
            = consList fs (consList msl (consList Msl (consList ps ρ))) i := by
        rw [← hfrσ, ← hfrρ]
        exact consList_agree_below _ _ _
      rw [hfrρ]
      exact (AnnotValid_congr_below _ _ _ _ hcl hagree).mp hvL

/-! ## The rule law -/

/-- **The rule law at the datum** (`fixRecRuleLaw` at the uniform
datum): at a model `m₃` of the store's environment whose recursor leaf
for member `t` is the chosen tuple's projection (`hleafR`), whose
constructors' leaves are the constructors' model's (`hagC`), and at
which the recursor type, the constructor type and the rule read as the
datum says (`hRD`, `hCread`, `hread`), rule `(t, j)` fires: the
equation of the chosen tuple (`hiota`) at the recursor's own parameter
spine — the major decoded by the fibre's converse — and the rule's
right-hand side β-reduced along the fitting spine. -/
theorem blockRecRuleLaw {env₀ env₃ : Env} {m₀ : EnvModel V env₀} (m₃ : EnvModel V env₃)
    {d : BlockRepData V} (hreps : BlockReps m₀ d)
    (hfT : ∀ ψ, FormersTyped m₀ d ψ) (hcT : ∀ ψ, CtorsTyped m₀ d ψ)
    (hval : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (m₀.acval n ψ))
    {elimL : Level} (hwℓ : ∀ ψ, d.w ψ = 0 → elimL.eval ψ = 0)
    (hR : ∀ ψ, BlockReadings m₀ d ψ elimL (d.recLs m₀ ψ) d.recNIdxs (d.recPps ψ) (d.recIpss ψ)
      (d.recCds ψ) d.recMots d.recTgts)
    (hokT : ∀ (ψ : Name → Nat) (mm : Nat), mm < d.k → ∀ ρ : Nat → V,
      WellDenotedV V ρ (mkPisAV (d.blockRds m₀ elimL mm ψ) (d.blockConc mm)))
    {rlps : List Name} {s : (Name → Nat) → Nat}
    (hrdsR : ∀ t, t < d.k → ∀ ψ,
      d.blockRds m₀ elimL t (restrictΨ rlps ψ) = d.blockRds m₀ elimL t ψ)
    (hleafCl : ∀ t, t < d.k → ∀ ψ, Term.bvarsBelow 0 (d.recLeaf m₀ elimL s rlps t ψ).erase)
    (hleaf : ∀ t, t < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (d.recLeaf m₀ elimL s rlps t ψ) ∧
      interp V ρ (d.recLeaf m₀ elimL s rlps t ψ)
        ∈ˢ interp V ρ (mkPisAV (d.blockRds m₀ elimL t ψ) (d.blockConc t)))
    (hiota : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ∀ e ∈ d.recEqs m₀ elimL (restrictΨ rlps ψ),
        (pt : V) ∈ˢ interp V
          (consList ((List.range d.k).map fun t => interp V ρ (d.recLeaf m₀ elimL s rlps t ψ)) ρ) e)
    (hagC : ∀ (c j : Nat) (cA : ConstantVal × Nat), c < d.k → (d.ctorsM c)[j]? = some cA →
      ∀ ψ, m₃.acval cA.1.name ψ = m₀.acval cA.1.name ψ)
    {t : Nat} (ht : t < d.k) {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM t)[j]? = some cA)
    {cvRa : ConstantVal} (hlpsSub : ∀ q ∈ cA.1.levelParams, q ∈ rlps)
    (hRD : MutualRecData m₃ cvRa d.nP d.k d.nCtors (d.nIdxAt t) t elimL (d.blockRds m₀ elimL t))
    (hleafR : ∀ ψ, m₃.acval cvRa.name ψ = d.recLeaf m₀ elimL s rlps t ψ)
    (hfC : env₃.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2))
    (hCread : ∀ ψ, denoteMeta m₃.acval env₃ ψ 0 cA.1.type
      = some (mkPisAV (d.dsF t j ψ) (ctorBodyAVI m₃ (d.memberName t) d.nP cA.2 ψ (d.esF t j ψ))))
    {rhs : Expr} (hlpsRhs : rhs.allLevelParamsDefined rlps = true)
    (hread : ∀ ψ, denoteMeta m₃.acval env₃ ψ 0 rhs
      = some (d.ruleRhsAV m₀ elimL (fun t' => d.recLeaf m₀ elimL s rlps t' ψ) t j cA.2 ψ))
    {mI rP : Nat} (hmI : mI = d.nP + d.k + d.nCtors + d.nIdxAt t) (hrP : rP = d.nP + d.k + d.nCtors)
    {rl : RecRule} {kb eb : Bool} (hrule : rl = ⟨cA.1.name, cA.2, d.nP, .plain, rhs, kb, eb, true⟩)
    (φ : Name → Nat) : RecRuleLaw m₃ φ cvRa.name cvRa mI rP rl := by
  subst hrule hmI hrP
  refine ⟨by omega, fun us hus => ?_⟩
  dsimp only
  have hinstR : ∀ (dp : Nat) (e : Expr),
      denoteMeta m₃.acval env₃ φ dp (e.instantiateLevelParams cvRa.levelParams us)
        = denoteMeta m₃.acval env₃ (Level.substFn φ cvRa.levelParams us) dp e :=
    fun dp e => denoteMeta_instLevels (acvalParamsAt_of_core m₃) φ dp e
  generalize hψR : Level.substFn φ cvRa.levelParams us = ψR at hinstR ⊢
  -- the assignment and its restriction agree on the recursors' level parameters
  have hφ : ∀ q ∈ rlps, ψR q = restrictΨ rlps ψR q := fun q hq => (restrictΨ_agree rlps ψR q hq).symm
  have hleafRes : ∀ t', d.recLeaf m₀ elimL s rlps t' (restrictΨ rlps ψR)
      = d.recLeaf m₀ elimL s rlps t' ψR := by
    intro t'
    unfold BlockRepData.recLeaf
    rw [restrictΨ_congr (lps := rlps) (fun q hq => restrictΨ_agree rlps ψR q hq)]
  have hreadR : denoteMeta m₃.acval env₃ ψR 0 rhs
      = some (d.ruleRhsAV m₀ elimL (fun t' => d.recLeaf m₀ elimL s rlps t' ψR) t j cA.2
          (restrictΨ rlps ψR)) := by
    rw [denoteMeta_params_ext m₃ hφ 0 rhs hlpsRhs, hread,
      show (fun t' => d.recLeaf m₀ elimL s rlps t' (restrictΨ rlps ψR))
        = fun t' => d.recLeaf m₀ elimL s rlps t' ψR from funext hleafRes]
  have hrdsR' : ∀ t', t' < d.k →
      d.blockRds m₀ elimL t' (restrictΨ rlps ψR) = d.blockRds m₀ elimL t' ψR :=
    fun t' ht' => hrdsR t' ht' ψR
  have hiotaR := hiota ψR
  generalize restrictΨ rlps ψR = ψ' at hφ hreadR hrdsR' hiotaR
  -- the leaves, their values
  have hRcl : ∀ t', t' < d.k → Term.bvarsBelow 0 (d.recLeaf m₀ elimL s rlps t' ψR).erase :=
    fun t' ht' => hleafCl t' ht' ψR
  have hRok : ∀ t', t' < d.k → ∀ σ : Nat → V,
      WellDenotedV V σ (d.recLeaf m₀ elimL s rlps t' ψR) :=
    fun t' ht' σ => (hleaf t' ht' ψR σ).1
  -- **the right-hand side is graded**
  have hokRa : ∀ ρ : Nat → V, WellDenotedV V ρ
      (d.ruleRhsAV m₀ elimL (fun t' => d.recLeaf m₀ elimL s rlps t' ψR) t j cA.2 ψ') := by
    intro ρ
    refine hreps.ruleRhs_wdV (hfT ψ') (hcT ψ') (fun n ρ' => hval n ψ' ρ') (hR ψ') (hokT ψ') ρ
      (rs := (List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR))
      (by simp) (fun mm hmm => ?_) hRcl hRok (fun t' ht' σ => ?_) ht hj
    · rw [getD_range_map' _ _ _ hmm]
      have hm := (hleaf mm hmm ψR ρ).2
      rw [← hrdsR' mm hmm] at hm
      exact hm
    · rw [getD_range_map' _ _ _ ht']
      exact interp_closed V (hRcl t' ht') σ ρ
  refine ⟨_, by rw [hinstR, hreadR], hokRa, fun _ _ h => absurd h (by simp), ?_⟩
  intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl husjl hψ _ _ _ hTVa hTVja
    hfitR hfitC
  -- the constructor found is the block's
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfC.symm.trans hfcj))
  -- the constructor's level assignment agrees with the restriction on its level parameters
  have hagree : ∀ q ∈ cA.1.levelParams, Level.substFn φ cA.1.levelParams usj q = ψR q := by
    have h := hψ
    simp only [ConLeche.recFireComparands] at h
    rw [← hψR]
    exact substFn_agree_of_comparand h
  generalize hψC : Level.substFn φ cA.1.levelParams usj = ψC at hagree hTVja hfitR hfitC ⊢
  have hCψ : ∀ q ∈ cA.1.levelParams, ψC q = ψ' q :=
    fun q hq => (hagree q hq).trans (hφ q (hlpsSub q hq))
  obtain ⟨cvT, cvR, mI', rP', rules, h⟩ := hreps t ht
  have hcd := h.ctorData hj
  obtain ⟨hfC₀, -, -⟩ := h.ctors t j cA ht hj
  have hj' : j < (d.ctorsM t).length := (List.getElem?_eq_some_iff.mp hj).1
  have hk : 0 < d.k := by omega
  have hpl := hreps.params_length hk ψ'
  have hdsEq : d.dsF t j ψC = d.dsF t j ψ' := (hcd.params ψC ψ' hCψ).1
  have hesEq : d.esF t j ψC = d.esF t j ψ' := (hcd.params ψC ψ' hCψ).2
  have hCac : m₃.acval cA.1.name ψC = m₀.acval cA.1.name ψ' := by
    rw [hagC t j cA ht hj ψC]
    exact m₀.acval_params _ _ hfC₀ ψC ψ' hCψ
  -- the recursor type's and the constructor type's readings
  have hTVa' : TVa = mkPisAV (d.blockRds m₀ elimL t ψ') (d.blockConc t) := by
    have h' := hTVa
    rw [hinstR] at h'
    rw [Option.some.inj (h'.symm.trans (hRD.read ψR)), hrdsR' t ht]
    rfl
  have hTVja' : TVja = mkPisAV (d.dsF t j ψ')
      (ctorBodyAVI m₃ (d.memberName t) d.nP cA.2 ψC (d.esF t j ψ')) := by
    have h' := hTVja
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₃) φ 0 cA.1.type, hψC] at h'
    rw [Option.some.inj (h'.symm.trans (hCread ψC)), hdsEq, hesEq]
  -- the fits, as spines
  have hlenRds' := hRD.len ψ'
  have hspR : SpineFit ρ ((d.blockRds m₀ elimL t ψ').map (·.2.2))
      ((xs ++ [AnnotTerm.mkAppN (m₃.acval cA.1.name ψC) ys]).map (interp V ρ)) := by
    have hst := stripPisAV_mkPisAV (d.blockRds m₀ elimL t ψ') (d.blockConc t)
    rw [hlenRds'] at hst
    have htele := piTeleAV_of_stripPisAV hst
    have hfit := hfitR
    rw [hTVa'] at hfit
    try simp only [RecRule.ctor] at hfit
    have hchain := teleFitPA_to_chain (d.nP + d.k + d.nCtors + d.nIdxAt t + 1) htele
      (by simp [hxl]) hfit
    refine spineFit_of_chain (by simp [hxl, hlenRds']) ?_
    intro q hq
    have := hchain q (by simpa [hlenRds'] using hq)
    simpa [hlenRds'] using this
  have hstC := stripPisAV_mkPisAV (d.dsF t j ψ')
    (ctorBodyAVI m₃ (d.memberName t) d.nP cA.2 ψC (d.esF t j ψ'))
  rw [hcd.len ψ'] at hstC
  have hteleC := piTeleAV_of_stripPisAV hstC
  have hspC : SpineFit ρ ((d.dsF t j ψ').map (·.2.2)) (ys.map (interp V ρ)) := by
    have hfit := hfitC
    rw [hTVja'] at hfit
    have hchain := teleFitPA_to_chain (d.nP + cA.2) hteleC (by simpa using hyl) hfit
    refine spineFit_of_chain (by simp [hyl, hcd.len ψ']) ?_
    intro q hq
    have := hchain q (by simpa [hcd.len ψ'] using hq)
    simpa [hcd.len ψ'] using this
  -- the arguments' values
  have hargsEq : (xs.take (d.nP + d.k + d.nCtors) ++ ys.drop d.nP).map (interp V ρ)
      = (xs.map (interp V ρ)).take (d.nP + d.k + d.nCtors) ++ (ys.map (interp V ρ)).drop d.nP := by
    rw [List.map_append, List.map_take, List.map_drop]
  -- the rule's binder data: bits, length, the prefix
  have hppsLen : (d.recPps ψ').length = d.nP := by
    have hl := congrArg List.length (hR ψ').ppsDom
    rw [List.length_map, hpl] at hl
    exact hl
  have hrdLen : (d.ruleData m₀ elimL t j ψ').length = d.nP + d.k + d.nCtors + cA.2 := by
    unfold BlockRepData.ruleData
    rw [mutualRuleDataAV_length hppsLen (hcd.len ψ'), (hR ψ').lsLen, (hR ψ').cdsLen]
  have hbits : ∀ q ∈ d.ruleData m₀ elimL t j ψ', q.1 = pwBit ψ' (Level.zeronessOf elimL) :=
    fun q hq => mem_mutualRuleDataAV hq
  have hb : pwBit ψ' (Level.zeronessOf elimL) = 0 ↔ elimL.eval ψ' = 0 := pwBit_zeronessOf ψ' elimL
  have hleafR' : m₃.acval cvRa.name ψR = d.recLeaf m₀ elimL s rlps t ψR := hleafR ψR
  try simp only [RecRule.ctor, RecRule.ctorParams] at hyl ⊢
  rw [hleafR']
  by_cases hℓ0 : elimL.eval ψ' = 0
  · -- **the `Prop` regime**: both sides are the point
    have hRpt : interp V ρ (d.recLeaf m₀ elimL s rlps t ψR) = pt := by
      have hmem := (hleaf t ht ψR ρ).2
      rw [← hrdsR' t ht] at hmem
      refine eq_pt_of_mem_univZero ?_ hmem
      cases hrds : d.blockRds m₀ elimL t ψ' with
      | nil => rw [hrds] at hlenRds'; simp at hlenRds'
      | cons q rest =>
        show piR q.2.1 _ _ ∈ˢ _
        rw [(hRD.bits ψ' q (by rw [hrds]; exact List.mem_cons_self)).mp hℓ0]
        exact piR_zero_mem_univZero
    have hRaPt : interp V ρ
        (d.ruleRhsAV m₀ elimL (fun t' => d.recLeaf m₀ elimL s rlps t' ψR) t j cA.2 ψ') = pt := by
      unfold BlockRepData.ruleRhsAV
      cases hlds : d.ruleData m₀ elimL t j ψ' with
      | nil => rw [hlds] at hrdLen; simp at hrdLen; omega
      | cons q rest =>
        have hq : q.1 = 0 := by
          rw [hbits q (by rw [hlds]; exact List.mem_cons_self)]
          exact hb.mpr hℓ0
        rw [mkLamsAV, interp_lam, hq, lamR_zero]
    refine ⟨?_, ?_⟩
    · rw [interp_mkAppN_pt hRpt, interp_mkAppN_pt hRaPt]
    · intro hxs_ok hys_ok
      refine mkAppN_wellDenotedV_of_pt (hokRa ρ) hRaPt fun a ha => ?_
      rcases List.mem_append.mp ha with h' | h'
      · exact hxs_ok a (List.mem_of_mem_take h')
      · exact hys_ok a (List.mem_of_mem_drop h')
  · -- **the graph regime**
    have hw : d.w ψ' ≠ 0 := fun hw => hℓ0 (hwℓ ψ' hw)
    have hnz : ∀ q ∈ d.ruleData m₀ elimL t j ψ', q.1 ≠ 0 := by
      intro q hq h0
      rw [hbits q hq] at h0
      exact hℓ0 (hb.mp h0)
    -- the recursor's spine, decomposed
    have hspR' : SpineFit ρ ((mutualRecDataAV m₀ ψ' (d.recLs m₀ ψ') d.nP d.recNIdxs elimL
        (d.recPps ψ') (d.recIpss ψ') (d.recCds ψ') d.recMots d.recTgts t).map (·.2.2))
        (xs.map (interp V ρ) ++ [interp V ρ (AnnotTerm.mkAppN (m₃.acval cA.1.name ψC) ys)]) := by
      rw [List.map_append, List.map_cons, List.map_nil] at hspR
      exact hspR
    obtain ⟨ps, Msl, msl, is, tv, heq, hF, his, htv⟩ :=
      hreps.spineFit_recData_inv (hR ψ') ht hspR'
    have hxsv : xs.map (interp V ρ) = ps ++ Msl ++ msl ++ is :=
      List.append_inj_left' heq rfl
    have hCv : interp V ρ (AnnotTerm.mkAppN (m₃.acval cA.1.name ψC) ys) = tv :=
      List.singleton_inj.mp (List.append_inj_right' heq rfl)
    have hlenps : ps.length = d.nP := by rw [hF.params.length_eq, hpl]
    have hρp : Sat V (d.params ψ').reverse (consList ps ρ) := d.satOfSpine hF.params
    -- the constructor's spine, decomposed at the parameters
    have hdsSplit : (d.dsF t j ψ').map (·.2.2)
        = ((d.dsF t j ψ').take d.nP).map (·.2.2) ++ ((d.dsF t j ψ').drop d.nP).map (·.2.2) := by
      rw [← List.map_append, List.take_append_drop]
    rw [hdsSplit] at hspC
    obtain ⟨psY, fsY, hys, hspY₁, hspY₂⟩ := spineFit_append_inv hspC
    have hlenPY : psY.length = d.nP := by
      rw [hspY₁.length_eq, List.length_map, List.length_take, hcd.len ψ']
      exact Nat.min_eq_left (Nat.le_add_right _ _)
    have hlenFY : fsY.length = cA.2 := by
      rw [hspY₂.length_eq, List.length_map, List.length_drop, hcd.len ψ']
      omega
    -- the constructor's parameters fit the former's telescope
    have hpsY : SpineFit ρ (d.params ψ') psY := by
      have hsat := sat_of_spineFit (Sat_nil V ρ) hspY₁
      rw [List.append_nil] at hsat
      exact spineFit_of_sat_len (by rw [hlenPY, hpl])
        ((h.paramsIff t j cA ht hj ψ' _).mpr hsat)
    have hfsY : SpineFit (consList psY ρ) ((d.Fss t ψ').getD j []) fsY := by
      rw [BlockRep.Fss_getD hj]; exact hspY₂
    -- the constructor's value is its injection
    have hCinj : tv = d.inj ψ' t j fsY := by
      rw [← hCv, interp_mkAppN, ← List.foldl_map (f := interp V ρ) (g := SetTheory.app), hys, hCac]
      exact h.ctor t j cA ht hj ψ' ρ psY fsY hpsY hfsY
    -- **the fibre's converse**: the fields fit at the recursor's parameters, the
    -- index arguments are the constructor's index readings
    have hidxMem : d.tup ψ' t is ∈ˢ d.idx ψ' (consList ps ρ) t := d.tupMem his
    have hdec := (h.fibre ψ' (consList ps ρ) hρp _ (lfpTuple_mem _ _ _ _) t ht _ hidxMem tv).mp
      (by rw [h.carrier_app_eq hρp ht hidxMem]; exact htv)
    obtain ⟨j', fs', hj'lt, hchain, hinj⟩ := hdec
    obtain ⟨rfl, rfl⟩ := h.mkInj ψ' hw t ht j fsY j' fs' hj' hj'lt
      (by rw [hlenFY, h.Fss_length hj]) hchain.1.length_eq (hCinj.symm.trans hinj)
    have hfs : SpineFit (consList ps ρ) ((d.Fss t ψ').getD j []) fsY :=
      hreps.spineFit_of_fitsFrom (hfT ψ') ht hj hρp (TupleLe.refl _ _ _) hchain.1
    have hisEq : (d.esF t j ψ').map (interp V (consList fsY (consList ps ρ))) = is :=
      h.es_eq_is hρp hj his hchain.2
    -- the tuple of the leaves' values
    have hlenrs : ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)).length
        = d.k := by simp
    have hρcD : ∀ t', t' < d.k →
        consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ
          (d.k - 1 - t') = interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR) := by
      intro t' ht'
      rw [consList_apply_lt' _ _ (by rw [hlenrs]; omega), hlenrs,
        show d.k - 1 - (d.k - 1 - t') = t' from by omega, getD_range_map' _ _ _ ht']
    -- the rule's spine fits its binder data, at the frame and at the tuple frame
    have hbelowPre : DomsBelow 0 (recPrefixAV m₀ ψ' (d.recLs m₀ ψ') d.nP d.recNIdxs elimL
        (d.recPps ψ') (d.recIpss ψ') (d.recCds ψ') d.recMots d.recTgts) := by
      have := (hR ψ').below t ht
      rw [mutualRecDataAV_eq_prefix] at this
      exact DomsBelow.append_left this
    have hpreLen : (recPrefixAV m₀ ψ' (d.recLs m₀ ψ') d.nP d.recNIdxs elimL (d.recPps ψ')
        (d.recIpss ψ') (d.recCds ψ') d.recMots d.recTgts).length = d.nP + d.k + d.nCtors := by
      unfold recPrefixAV
      rw [List.length_append, List.length_append, rebit_length, motivesDataGo_length,
        fixMinorsDataM_length, hppsLen, (hR ψ').lsLen, (hR ψ').cdsLen]
    have hpre : SpineFit ρ ((recPrefixAV m₀ ψ' (d.recLs m₀ ψ') d.nP d.recNIdxs elimL (d.recPps ψ')
        (d.recIpss ψ') (d.recCds ψ') d.recMots d.recTgts).map (·.2.2)) (ps ++ Msl ++ msl) := by
      rw [mutualRecDataAV_eq_prefix, List.map_append, heq] at hspR'
      obtain ⟨as₁, as₂, heq', h1, -⟩ := spineFit_append_inv hspR'
      have hlen₁ : (ps ++ Msl ++ msl).length = as₁.length := by
        rw [h1.length_eq, List.length_map, hpreLen, List.length_append, List.length_append, hlenps,
          hF.mslLen, hF.minsLen]
      have : ps ++ Msl ++ msl = as₁ := by
        have h2 : ps ++ Msl ++ msl ++ (is ++ [tv]) = as₁ ++ as₂ := by
          rw [← heq', List.append_assoc, List.append_assoc, List.append_assoc]
          simp only [List.append_assoc]
        exact (List.append_inj h2 hlen₁).1
      rw [this]; exact h1
    have hlenMm : (d.recLs m₀ ψ').length + (d.recCds ψ').length = (Msl ++ msl).length := by
      rw [List.length_append, hF.mslLen, hF.minsLen, (hR ψ').lsLen, (hR ψ').cdsLen]
    have hfields : SpineFit (consList (ps ++ Msl ++ msl) ρ)
        ((rebit (pwBit ψ' (Level.zeronessOf elimL))
          (liftDoms ((d.recLs m₀ ψ').length + (d.recCds ψ').length) 0 ((d.dsF t j ψ').drop d.nP))).map
          (·.2.2)) fsY := by
      rw [rebit_map_dom, spineFit_liftDoms, consList_append, consList_append,
        ← consList_append Msl msl, hlenMm, shiftE_consList, ← BlockRep.Fss_getD hj]
      exact hfs
    have hfitρ : SpineFit ρ ((d.ruleData m₀ elimL t j ψ').map (·.2)) (ps ++ Msl ++ msl ++ fsY) := by
      unfold BlockRepData.ruleData
      rw [mutualRuleDataAV_eq_prefix, List.map_append]
      exact SpineFit.append hpre hfields
    have hL0 : DomsBelow 0 ((recPrefixAV m₀ ψ' (d.recLs m₀ ψ') d.nP d.recNIdxs elimL (d.recPps ψ')
        (d.recIpss ψ') (d.recCds ψ') d.recMots d.recTgts ++
        rebit (pwBit ψ' (Level.zeronessOf elimL))
          (liftDoms ((d.recLs m₀ ψ').length + (d.recCds ψ').length) 0 ((d.dsF t j ψ').drop d.nP)))) := by
      refine domsBelow_append hbelowPre ?_
      rw [hpreLen]
      have hdrop : DomsBelow d.nP ((d.dsF t j ψ').drop d.nP) := by
        have hdr := DomsBelow.drop (k := 0) d.nP (hcd.below ψ')
        simpa using hdr
      have hlift := domsBelow_liftDoms (n := (d.recLs m₀ ψ').length + (d.recCds ψ').length) (kk := 0) hdrop
      exact domsBelow_rebit (domsBelow_mono (by rw [(hR ψ').lsLen, (hR ψ').cdsLen]; omega) hlift)
    have hfitσ : SpineFit (consList ((List.range d.k).map fun t' =>
        interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ)
        ((d.ruleData m₀ elimL t j ψ').map (·.2)) (ps ++ Msl ++ msl ++ fsY) := by
      have hfitρ' := hfitρ
      unfold BlockRepData.ruleData at hfitρ' ⊢
      rw [mutualRuleDataAV_eq_prefix] at hfitρ' ⊢
      exact spineFit_transport₀ hL0 hfitρ'
    -- **the equation** at the recursor's own parameter spine
    have hEq := blockRecs_iota (k := d.k)
      (a := fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR))
      (hiotaR ρ _ (d.mem_specEqs_of ht hj)) _ hfitσ
    -- the frames
    have hfrσ : consList (ps ++ Msl ++ msl ++ fsY)
        (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ)
        = consList fsY (consList msl (consList Msl (consList ps
          (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ)))) := by
      simp only [consList_append]
    have hfrρ : consList (ps ++ Msl ++ msl ++ fsY) ρ
        = consList fsY (consList msl (consList Msl (consList ps ρ))) := by
      simp only [consList_append]
    -- the left-hand side of the equation is the recursor's value at the spine
    have hpsC : SpineFit (consList ((List.range d.k).map fun t' =>
        interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ) (d.params ψ') ps := by
      have hbP : DomsBelow 0 (rebit (pwBit ψ' (Level.zeronessOf elimL)) (d.recPps ψ')) :=
        DomsBelow.append_left (DomsBelow.append_left hbelowPre)
      have := spineFit_transport₀ hbP (ρ₁ := ρ)
        (ρ₂ := consList ((List.range d.k).map fun t' =>
          interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ)
        (by rw [rebit_map_dom, (hR ψ').ppsDom]; exact hF.params)
      rw [rebit_map_dom, (hR ψ').ppsDom] at this
      exact this
    have hfs' : SpineFit (consList ps (consList ((List.range d.k).map fun t' =>
        interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ)) ((d.Fss t ψ').getD j []) fsY := by
      rw [BlockRep.Fss_getD hj] at hfs ⊢
      exact spineFit_transport (DomsBelow.drop d.nP (hcd.below ψ')) (by rw [hlenps, Nat.zero_add]) hfs
    have hlhs : interp V (consList (ps ++ Msl ++ msl ++ fsY)
        (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ))
        (specLhsAV d.k d.nP d.nCtors cA.2 t (d.esF t j ψ') (m₀.acval cA.1.name ψ'))
        = (ps ++ Msl ++ msl ++ is ++ [tv]).foldl SetTheory.app
          (interp V ρ (d.recLeaf m₀ elimL s rlps t ψR)) := by
      rw [hfrσ, interp_specLhsAV_at hlenps hF.mslLen hF.minsLen hlenFY, hρcD t ht]
      congr 1
      -- the index readings and the constructor's application
      have hEsρ : (d.esF t j ψ').map (interp V (consList fsY (consList ps
          (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ))))
          = (d.esF t j ψ').map (interp V (consList fsY (consList ps ρ))) := by
        apply List.map_congr_left
        intro E hE
        rw [← consList_append ps fsY, ← consList_append ps fsY ρ]
        exact interp_closed_bottom (hcd.belowE ψ' E hE) (by rw [List.length_append, hlenps, hlenFY]) _ _
      have hCval : ∀ σ σ' : Nat → V,
          interp V σ (m₀.acval cA.1.name ψ') = interp V σ' (m₀.acval cA.1.name ψ') :=
        fun σ σ' => interp_closed (V := V) (m₀.cval_closedL _ ψ') σ σ'
      have hrng : (List.range d.nP).reverse.map (consList ps
          (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ)) = ps := by
        rw [← hlenps]; exact range_reverse_map_consList ps _
      have hargsC : (paramBvarsAt d.nP (d.nP + d.k + d.nCtors + cA.2) ++ fieldBvars cA.2).map
          (interp V (consList fsY (consList msl (consList Msl (consList ps
            (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ))))))
          = ps ++ fsY := by
        rw [List.map_append, show d.nP + d.k + d.nCtors + cA.2 = d.nP + (d.k + d.nCtors + cA.2) from by omega,
          map_paramBvarsAt_interp (ρp := consList ps (consList ((List.range d.k).map fun t' =>
            interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ)) (fun j' => by
            rw [show j' + (d.k + d.nCtors + cA.2) = ((j' + Msl.length) + msl.length) + fsY.length from by
                rw [hF.mslLen, hF.minsLen, hlenFY]; omega,
              consList_apply_add, consList_apply_add, consList_apply_add]),
          show fieldBvars cA.2 = (List.range cA.2).map (fun k => AnnotTerm.bvar (cA.2 - 1 - k)) from rfl,
          map_fieldBvars_interp hlenFY, hrng]
      have hC : interp V (consList fsY (consList msl (consList Msl (consList ps
          (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ)))))
          (AnnotTerm.mkAppN (m₀.acval cA.1.name ψ')
            (paramBvarsAt d.nP (d.nP + d.k + d.nCtors + cA.2) ++ fieldBvars cA.2)) = d.inj ψ' t j fsY := by
        rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList fsY (consList msl (consList Msl
          (consList ps (consList ((List.range d.k).map fun t' =>
            interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ)))))) (g := SetTheory.app), hargsC,
          hCval _ (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ)]
        exact h.ctor t j cA ht hj ψ' _ ps fsY hpsC hfs'
      rw [hEsρ, hisEq, hC, ← hCinj]
    -- the right-hand side of the equation is the rule's core with the leaves, at the frame
    have hcl : Term.bvarsBelow (ps ++ Msl ++ msl ++ fsY).length
        (mutualRuleCoreAV (pwBit ψ' (Level.zeronessOf elimL))
          (fun t' => d.recLeaf m₀ elimL s rlps t' ψR) (d.tgts t j) d.nP d.k d.nCtors cA.2
          (d.minorIdx t j) (ConLeche.recIdxOf (d.ksF t j)) (d.tssF t j ψ') (d.eissF t j ψ')).erase := by
      refine mutualRuleCoreAV_below
        (fun i hi => hRcl _ (h.tgtsLt t j i ht hj' (mem_recIdxOf.mp hi).1)) hk (fun i hi => ?_)
        (hcd.tssBelow ψ') (hcd.eissBelow ψ') ?_
      · rw [← hcd.ksLen]; exact (mem_recIdxOf.mp hi).1
      · simp only [List.length_append, hlenps, hF.mslLen, hF.minsLen, hlenFY]
        omega
    have hagreeF : ∀ i, i < (ps ++ Msl ++ msl ++ fsY).length →
        consList fsY (consList msl (consList Msl (consList ps ρ))) i
          = consList fsY (consList msl (consList Msl (consList ps
            (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ)))) i := by
      rw [← hfrσ, ← hfrρ]
      exact consList_agree_below _ _ _
    have hbr : ∀ i ∈ ConLeche.recIdxOf (d.ksF t j), ∀ bs : List V,
        bs.length = ((d.tssF t j ψ').getD i []).length →
        interp V (consList bs (consList fsY (consList msl (consList Msl (consList ps
          (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ))))))
            (tupleVarAV d.k (d.nP + d.k + d.nCtors + cA.2 + ((d.tssF t j ψ').getD i []).length)
              (d.tgts t j i))
          = interp V (consList bs (consList fsY (consList msl (consList Msl (consList ps
            (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ))))))
            (d.recLeaf m₀ elimL s rlps (d.tgts t j i) ψR) := by
      intro i hiI bs hbs
      have htgt : d.tgts t j i < d.k := h.tgtsLt t j i ht hj' (mem_recIdxOf.mp hiI).1
      rw [← hbs, interp_tupleVarAV_at hlenps hF.mslLen hF.minsLen hlenFY, hρcD _ htgt]
      exact (interp_closed V (hRcl _ htgt) _ _).symm
    have hrhs : interp V (consList (ps ++ Msl ++ msl ++ fsY)
        (consList ((List.range d.k).map fun t' => interp V ρ (d.recLeaf m₀ elimL s rlps t' ψR)) ρ))
        (specRuleCoreAV (pwBit ψ' (Level.zeronessOf elimL)) d.k (d.tgts t j) d.nP d.nCtors cA.2
          (d.minorIdx t j) (ConLeche.recIdxOf (d.ksF t j)) (d.tssF t j ψ') (d.eissF t j ψ'))
        = interp V (consList (ps ++ Msl ++ msl ++ fsY) ρ)
          (mutualRuleCoreAV (pwBit ψ' (Level.zeronessOf elimL))
            (fun t' => d.recLeaf m₀ elimL s rlps t' ψR) (d.tgts t j) d.nP d.k d.nCtors cA.2
            (d.minorIdx t j) (ConLeche.recIdxOf (d.ksF t j)) (d.tssF t j ψ') (d.eissF t j ψ')) := by
      rw [hfrσ, interp_specRuleCoreAV_leaf (b := pwBit ψ' (Level.zeronessOf elimL))
        (J := d.minorIdx t j) (Eiss := d.eissF t j ψ') hbr, hfrρ]
      exact (interp_congr_below V _ _ _ _ hcl hagreeF).symm
    refine ⟨?_, ?_⟩
    · -- **the law**
      rw [interp_mkAppN, ← List.foldl_map (f := interp V ρ) (g := SetTheory.app), List.map_append,
        List.map_cons, List.map_nil, hxsv, hCv, ← hlhs, hEq, hrhs, interp_mkAppN,
        ← List.foldl_map (f := interp V ρ) (g := SetTheory.app), hargsEq, hxsv, hys,
        List.take_left' (by rw [List.length_append, List.length_append, hlenps, hF.mslLen, hF.minsLen]),
        List.drop_left' hlenPY]
      unfold BlockRepData.ruleRhsAV
      exact (mkLamsAV_fold hnz hfitρ).symm
    · -- **the application is graded**
      intro hxs_ok hys_ok
      have hargs : ∀ a ∈ xs.take (d.nP + d.k + d.nCtors) ++ ys.drop d.nP, WellDenotedV V ρ a := by
        intro a ha
        rcases List.mem_append.mp ha with h' | h'
        · exact hxs_ok a (List.mem_of_mem_take h')
        · exact hys_ok a (List.mem_of_mem_drop h')
      refine mkAppN_wellDenotedV_of_lam (hokRa ρ) hargs (hokRa ρ).1 (Or.inr rfl) ?_
      rw [hargsEq, hxsv, hys,
        List.take_left' (by rw [List.length_append, List.length_append, hlenps, hF.mslLen, hF.minsLen]),
        List.drop_left' hlenPY]
      exact hfitρ

end ConLeche.Model
