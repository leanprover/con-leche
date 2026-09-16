module

public import ConLeche.Model.Inductives.BlockRecWD
import ConLeche.Model.Inductives.FixLeafOk
import ConLeche.Model.Inductives.StructEntryKit2
import ConLeche.Model.Inductives.SumIntro
import ConLeche.Model.Inductives.FixIntro
import ConLeche.Model.Inductives.FixRuleKit
import ConLeche.Model.Inductives.BlockRecFrames
import ConLeche.Model.Inductives.BlockRecEq
public section

/-!
# The rules' equations bit-valid at every typed tuple (task #315, M3)

`blockEq_wd`'s twin for the annotation's second currency: every rule's
equation (`specEqAV`) is `AnnotValid` at the frame of ANY tuple typed
at the recursor types' readings.

Validity is cheaper than grading at exactly the places where
`WellDenoted` carries a semantic package: the `app` and `eqE` clauses
are bare conjunctions (no application chain), and the `lam` clause is
the domain's validity plus the body's at every value of the domain (no
fibre package, no `Prop`-regime side condition).  So the proof keeps
`blockEq_wd`'s frame bookkeeping — the same `hdoms` split, the same
`spineFit_prefix_inv`/`spineFit_append_inv` decomposition, the same
lift transports — and drops every chain obligation:

* the DOMAINS are the recursor type's prefix (`hokT`'s validity half)
  and the constructor's fields lifted under the motives and minors
  (the constructor type's validity half, `IsBlockModel.ctor_validV`);
* the LEFT-hand side is a spine of bound variables, the constructor's
  index readings (valid at the fields' frame, lifted) and the
  constructor's own value (`hval`);
* the RIGHT-hand side is the minor's variable at the fields and the
  inductive hypotheses' λ-towers (`IsBlockModels.ihApp_validV`): the moved
  telescope's validity is the field's telescope's (`fieldsValid_ihTeleAtGo`)
  and the moved index expressions' is the field's (`AnnotValid_ihIdxAtM`),
  both read off the field's own entry in the constructor's telescope
  (`recEntry`/`reflEntry`).

The Π-tower's `univZero` obligation is the equation's own
(`eqv_mem_univZero`): every rule binder carries bit `0`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Kit: the `FieldsValid` twins of the `FieldsOkB` walks -/

/-- Valid fields' prefix. -/
theorem FieldsValid.append_left :
    ∀ {Fs₁ Fs₂ : List AnnotTerm} {ρ : Nat → V}, FieldsValid ρ (Fs₁ ++ Fs₂) → FieldsValid ρ Fs₁
  | [], _, _, _ => trivial
  | _ :: Fs₁, Fs₂, _, h =>
    ⟨h.1, fun a ha => FieldsValid.append_left (Fs₁ := Fs₁) (Fs₂ := Fs₂) (h.2 a ha)⟩

/-- Valid fields, appended: the suffix at every fitting spine of the
prefix. -/
theorem FieldsValid.append :
    ∀ {Fs₁ Fs₂ : List AnnotTerm} {ρ : Nat → V}, FieldsValid ρ Fs₁ →
      (∀ as, SpineFit ρ Fs₁ as → FieldsValid (consList as ρ) Fs₂) → FieldsValid ρ (Fs₁ ++ Fs₂)
  | [], _, _, _, h₂ => by simpa using h₂ [] trivial
  | F :: Fs₁, Fs₂, ρ, h₁, h₂ => by
    refine ⟨h₁.1, fun a ha => FieldsValid.append (h₁.2 a ha) fun as hsp => ?_⟩
    have := h₂ (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- Lifted domains are valid at the lifted frame when the domains are
valid at the shifted one (`fieldsOkB_liftDoms`'s twin). -/
theorem fieldsValid_liftDoms {n : Nat} :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k : Nat) (σ : Nat → V),
      FieldsValid (shiftE n k σ) (ds.map (·.2.2)) → FieldsValid σ ((liftDoms n k ds).map (·.2.2))
  | [], _, _, _ => trivial
  | d :: ds, k, σ, h => by
    simp only [liftDoms, List.map_cons]
    simp only [List.map_cons] at h
    refine ⟨(AnnotValid_liftN V n _ k σ).mpr h.1, fun a ha => ?_⟩
    rw [interp_liftN] at ha
    exact fieldsValid_liftDoms ds (k + 1) (cons a σ) (by rw [shiftE_cons_succ']; exact h.2 a ha)

omit [SetTheory V] in
/-- The `k`-motive leading spine is variables only. -/
theorem recPrefixBvarsMK_validV [SetTheory V] {nP k n nF m : Nat} {σ : Nat → V} {a : AnnotTerm}
    (ha : a ∈ recPrefixBvarsMK nP k n nF m) : AnnotValid V σ a := by
  unfold recPrefixBvarsMK at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial
  · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial

omit [SetTheory V] in
theorem fieldBvars_validV [SetTheory V] {nF : Nat} {σ : Nat → V} {a : AnnotTerm}
    (ha : a ∈ fieldBvars nF) : AnnotValid V σ a := by
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial

omit [SetTheory V] in
theorem teleVarsAV_validV [SetTheory V] {m : Nat} {σ : Nat → V} {a : AnnotTerm}
    (ha : a ∈ teleVarsAV m) : AnnotValid V σ a := by
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial

namespace IsBlockModel

variable {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
  {rules : List RecRule} {d : BlockModel V} {mm : Nat}
  (h : IsBlockModel m T cvT cvR mI rP rules d mm)
include h

/-- **The constructor's fields are valid and its body is valid at
every fitting field spine** — its stored type's `AnnotValid` under the
parameters (`ctor_okB`'s twin). -/
theorem ctor_validV {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM mm)[j]? = some cA)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) :
    FieldsValid ρp ((d.Fss mm ψ).getD j []) ∧
    ∀ fs, SpineFit ρp ((d.Fss mm ψ).getD j []) fs →
      AnnotValid V (consList fs ρp)
        (AnnotTerm.mkAppN (m.acval (d.memberName mm) ψ)
          (paramBvarsAt d.nP (d.nP + cA.2) ++ d.esF mm j ψ)) := by
  have hok := ((h.ctorData hj).okTy ψ (fun i => ρp (i + d.nP))).2
  rw [← List.take_append_drop d.nP (d.dsF mm j ψ), mkPisAV_append] at hok
  have h1 := (AnnotValid_mkPisAV_inv hok).2 _ (h.ctor_params_fit hj hρp)
  rw [consList_range_reverse] at h1
  have h2 := AnnotValid_mkPisAV_inv h1
  rw [← Fss_getD hj] at h2
  refine ⟨h2.1, fun fs hfs => ?_⟩
  have := h2.2 fs hfs
  unfold ctorBodyAVI at this
  rwa [paramBvars_eq_paramBvarsAt] at this

end IsBlockModel

omit [SetTheory V] in
theorem tupleVarAV_validV [SetTheory V] {k dp t : Nat} {σ : Nat → V} :
    AnnotValid V σ (tupleVarAV k dp t) := by
  unfold tupleVarAV; trivial

/-! ## A recursive field's telescope and index readings, valid -/

namespace IsBlockModel

variable {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
  {rules : List RecRule} {d : BlockModel V} {mm : Nat}
  (h : IsBlockModel m T cvT cvR mI rP rules d mm)
include h

/-- **A recursive field's validity data**: field `i`'s telescope is
valid at the field's own frame and its index expressions are valid
under every fitting telescope spine — read off the constructor's entry
at that position (`recEntry` has no telescope, `reflEntry` one, and
both end in the target former's application, whose arguments the
`mkAppN` inversion hands back). -/
theorem field_kind_validV {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM mm)[j]? = some cA)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp)
    {fs : List V} (hfs : SpineFit ρp ((d.Fss mm ψ).getD j []) fs)
    {i : Nat} (hiI : i ∈ ConLeche.recIdxOf (d.ksF mm j)) :
    FieldsValid (consList (fs.take i) ρp) (((d.tssF mm j ψ).getD i []).map (·.2.2)) ∧
    ∀ bs, SpineFit (consList (fs.take i) ρp) (((d.tssF mm j ψ).getD i []).map (·.2.2)) bs →
      ∀ E ∈ (d.eissF mm j ψ).getD i [], AnnotValid V (consList bs (consList (fs.take i) ρp)) E := by
  have hcd := h.ctorData hj
  have hiK : i < (d.ksF mm j).length := (mem_recIdxOf.mp hiI).1
  have hiA : i < cA.2 := by rw [← hcd.ksLen]; exact hiK
  have hkind := (mem_recIdxOf.mp hiI).2
  have hfsI := spineFit_take' hfs (i := i) (by rw [h.Fss_length hj]; exact Nat.le_of_lt hiA)
  have hdomF : ((d.Fss mm ψ).getD j []).getD i default
      = ((d.dsF mm j ψ).getD (d.nP + i) default).2.2 := by
    rw [IsBlockModel.Fss_getD hj, fields_getD (by rw [List.length_drop, hcd.len]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  have hvF : AnnotValid V (consList (fs.take i) ρp)
      (((d.dsF mm j ψ).getD (d.nP + i) default).2.2) := by
    rw [← hdomF]
    exact fieldsValid_getD (h.ctor_validV hj hρp).1 (by rw [h.Fss_length hj]; exact hiA) hfsI
  rcases hkind with hrec | hrefl
  · have htl : (d.tssF mm j ψ).getD i [] = [] := hcd.tssNone ψ i (by rw [hrec]; decide)
    rw [htl]
    refine ⟨trivial, fun bs hbs => ?_⟩
    cases bs with
    | cons _ _ => exact hbs.elim
    | nil =>
      intro E hE
      rw [hcd.recEntry ψ i hrec hiA] at hvF
      rw [consList_nil]
      exact (AnnotValid.mkAppN_inv hvF).2 E (List.mem_append_right _ hE)
  · rw [hcd.reflEntry ψ i hrefl hiA] at hvF
    have hinv := AnnotValid_mkPisAV_inv hvF
    exact ⟨hinv.1, fun bs hbs E hE =>
      (AnnotValid.mkAppN_inv (hinv.2 bs hbs)).2 E (List.mem_append_right _ hE)⟩

end IsBlockModel

/-! ## One inductive hypothesis' application, valid -/

/-- **An inductive hypothesis' application is bit-valid at the rule's
frame** (`ihApp_facts`'s validity half): the λ-tower over the field's
moved telescope, whose domains are the field's telescope moved
(`fieldsValid_ihTeleAtGo`) and whose body is an application chain of
bound variables, the field's index readings moved
(`AnnotValid_ihIdxAtM`) and the field's own variable applied to the
telescope's — no application-chain obligation is owed here, so the
frame's motives and minors are consumed by the moves alone. -/
theorem IsBlockModels.ihApp_validV {m : EnvModel V env} {d : BlockModel V} (hreps : IsBlockModels m d)
    {ψ : Name → Nat} {elimL : Level} {ρ : Nat → V} {rs : List V}
    {c : Nat} (hc : c < d.k) {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA)
    {ps Msl msl fs : List V} (hmsl : Msl.length = d.k) (hmin : msl.length = d.nCtors)
    (hpsC : SpineFit (consList rs ρ) (d.params ψ) ps)
    (hfs' : SpineFit (consList ps (consList rs ρ)) ((d.Fss c ψ).getD j []) fs)
    {i : Nat} (hiI : i ∈ ConLeche.recIdxOf (d.ksF c j)) :
    AnnotValid V (consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))))
      (ihAppAVK (tupleVarAV d.k (d.nP + d.k + d.nCtors + cA.2 + ((d.tssF c j ψ).getD i []).length)
          (d.tgts c j i))
        d.nP d.k d.nCtors cA.2 i (rebit (pwBit ψ (Level.zeronessOf elimL)) ((d.tssF c j ψ).getD i []))
        ((d.eissF c j ψ).getD i [])) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hρpc : Sat V (d.params ψ).reverse (consList ps (consList rs ρ)) := d.satOfSpine hpsC
  have hlenfs : fs.length = cA.2 := by rw [hfs'.length_eq, h.Fss_length hj]
  have hiA : i < cA.2 := by rw [← hcd.ksLen]; exact (mem_recIdxOf.mp hiI).1
  have hkindV := h.field_kind_validV hj hρpc hfs' hiI
  have hk : 0 < d.k := by omega
  obtain ⟨M0, Msl', rfl⟩ : ∃ M0 Msl', Msl = M0 :: Msl' := by
    cases Msl with
    | nil => exact absurd hk (by rw [← hmsl]; exact Nat.lt_irrefl _)
    | cons M0 Msl' => exact ⟨M0, Msl', rfl⟩
  have hms : (Msl' ++ msl).length + 1 = d.nCtors + d.k := by
    rw [List.length_append, hmin]; simp only [List.length_cons] at hmsl; omega
  have ho : (M0 :: Msl').length + msl.length = d.nCtors + d.k := by rw [hmsl, hmin]; omega
  have hne : 0 < (M0 :: Msl').length := by simp
  have hfr : consList fs (consList msl (consList (M0 :: Msl') (consList ps (consList rs ρ))))
      = consList [] (consList [] (consList fs (consList (Msl' ++ msl)
          (cons M0 (consList ps (consList rs ρ)))))) := by
    rw [consList_nil, consList_nil, consList_motives_cons]
  have hfr' : consList fs (consList msl (consList (M0 :: Msl') (consList ps (consList rs ρ))))
      = consList [] (consList fs (consList (Msl' ++ msl)
          (cons M0 (consList ps (consList rs ρ))))) := by
    rw [consList_nil, consList_motives_cons]
  unfold ihAppAVK
  refine mkLamsAV_bits_validV (underTowerValid_of_fieldsValid ?_ fun bs hbs => ?_)
  · -- the moved telescope's domains
    unfold ihTeleAtR
    rw [hfr]
    have := fieldsValid_ihTeleAtGo (ρp := consList ps (consList rs ρ)) (M := M0) (ms := Msl' ++ msl)
      hms hlenfs (ihs := []) rfl (Nat.le_of_lt hiA)
      (rebit (pwBit ψ (Level.zeronessOf elimL)) ((d.tssF c j ψ).getD i [])) []
      (by rw [rebit_map_dom, consList_nil]; exact hkindV.1)
    simpa only [List.length_nil] using this
  · -- the body at every fitting telescope spine
    rw [rebit_length]
    have hbsc : SpineFit (consList (fs.take i) (consList ps (consList rs ρ)))
        (((d.tssF c j ψ).getD i []).map (·.2.2)) bs := by
      have := (spineFit_ihTeleAtR_M (ρp := consList ps (consList rs ρ)) (Msl := M0 :: Msl')
        (msl := msl) ho hne hlenfs (ihs := []) rfl (Nat.le_of_lt hiA) _ bs).mp
        (by rw [consList_nil]; exact hbs)
      rwa [rebit_map_dom] at this
    have hlenbs : bs.length = ((d.tssF c j ψ).getD i []).length := by
      rw [hbs.length_eq, List.length_map, ihTeleAtR_length, rebit_length]
    rw [← hlenbs]
    refine mkAppN_validV tupleVarAV_validV fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact recPrefixBvarsMK_validV ha
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
        rw [hfr']
        exact (AnnotValid_ihIdxAtM hms hlenfs rfl (Nat.le_of_lt hiA) bs E).mpr
          (hkindV.2 bs hbsc E hE)
    · obtain rfl := List.mem_singleton.mp ha
      exact mkAppN_validV trivial fun a' ha' => teleVarsAV_validV ha'

/-! ## The rules' equations, valid -/

/-- **The rules' equations are bit-valid at every typed tuple** —
`blockEq_wd`'s `AnnotValid` half. -/
theorem IsBlockModels.blockEq_valid {m : EnvModel V env} {d : BlockModel V} (hreps : IsBlockModels m d)
    {ψ : Name → Nat} (_hfT : FormersTyped m d ψ) (_hcT : CtorsTyped m d ψ)
    (hval : ∀ (n : Name) (ρ : Nat → V), AnnotValid V ρ (m.acval n ψ))
    {elimL : Level} {Ls : List AnnotTerm} {nIdxs : List Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} (hR : BlockReadings m d ψ elimL Ls nIdxs pps ipss cds mots tgts)
    (hokT : ∀ mm, mm < d.k → ∀ ρ : Nat → V,
      WellDenotedV V ρ (mkPisAV (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm)
        (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)))
    (ρ : Nat → V) {rs : List V} (hlen : rs.length = d.k)
    (_hrs : ∀ mm, mm < d.k → rs.getD mm pt ∈ˢ interp V ρ
      (mkPisAV (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm)
        (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)))
    {c : Nat} (hc : c < d.k) {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) :
    AnnotValid V (consList rs ρ)
      (specEqAV (mutualRuleDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts (d.dsF c j ψ))
        (specLhsAV d.k d.nP d.nCtors cA.2 c (d.esF c j ψ) (m.acval cA.1.name ψ))
        (specRuleCoreAV (pwBit ψ (Level.zeronessOf elimL)) d.k (d.tgts c j) d.nP d.nCtors cA.2
          (d.minorIdx c j) (ConLeche.recIdxOf (d.ksF c j)) (d.tssF c j ψ) (d.eissF c j ψ))) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hpl := hreps.params_length (by omega) ψ
  have hlenLc : Ls.length + cds.length = d.k + d.nCtors := by rw [hR.lsLen, hR.cdsLen]
  -- the rule's binder data: the prefix and the lifted fields
  have hdoms : ((mutualRuleDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts (d.dsF c j ψ)).map
      fun d' : Nat × AnnotTerm => ((0 : Nat), (0 : Nat), d'.2)).map (·.2.2)
      = (recPrefixAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts).map (·.2.2) ++
        (rebit (pwBit ψ (Level.zeronessOf elimL))
          (liftDoms (Ls.length + cds.length) 0 ((d.dsF c j ψ).drop d.nP))).map (·.2.2) := by
    rw [List.map_map, ← List.map_append]
    exact mutualRuleDataAV_eq_prefix
  have hbelowPre : DomsBelow 0 (recPrefixAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts) := by
    have := hR.below c hc
    rw [mutualRecDataAV_eq_prefix] at this
    exact DomsBelow.append_left this
  unfold specEqAV
  refine AnnotValid_mkPisAV_of (w := 0) (fun dd hdd => ?_) ?_ ?_ (fun _ xs _ => ?_)
  · obtain ⟨-, -, rfl⟩ := List.mem_map.mp hdd; exact Iff.rfl
  · -- **the domains**
    rw [hdoms]
    refine FieldsValid.append ?_ fun xs hxs => ?_
    · have := (AnnotValid_mkPisAV_inv (hokT c hc (consList rs ρ)).2).1
      rw [mutualRecDataAV_eq_prefix, List.map_append] at this
      exact FieldsValid.append_left this
    · obtain ⟨ps, Msl, msl, rfl, hF⟩ := spineFit_prefix_inv hR hxs
      have hρp : Sat V (d.params ψ).reverse (consList ps (consList rs ρ)) := d.satOfSpine hF.params
      rw [rebit_map_dom]
      refine fieldsValid_liftDoms _ _ _ ?_
      rw [consList_append, consList_append, ← consList_append Msl msl,
        show Ls.length + cds.length = (Msl ++ msl).length from by
          rw [List.length_append, hF.mslLen, hF.minsLen, hlenLc],
        shiftE_consList, ← IsBlockModel.Fss_getD hj]
      exact (h.ctor_validV hj hρp).1
  · -- **the body at a fitting spine**
    intro xs hxs
    rw [hdoms] at hxs
    obtain ⟨xs₁, fs, rfl, hpre, hfsL⟩ := spineFit_append_inv hxs
    have hpreρ := spineFit_transport₀ hbelowPre (ρ₂ := ρ) hpre
    obtain ⟨ps, Msl, msl, rfl, hF⟩ := spineFit_prefix_inv hR hpreρ
    have hlenps : ps.length = d.nP := by rw [hF.params.length_eq, hpl]
    have hbP : DomsBelow 0 (rebit (pwBit ψ (Level.zeronessOf elimL)) pps) :=
      DomsBelow.append_left (DomsBelow.append_left hbelowPre)
    have hpsC : SpineFit (consList rs ρ) (d.params ψ) ps := by
      have := spineFit_transport₀ hbP (ρ₁ := ρ) (ρ₂ := consList rs ρ)
        (by rw [rebit_map_dom, hR.ppsDom]; exact hF.params)
      rw [rebit_map_dom, hR.ppsDom] at this
      exact this
    have hρpc : Sat V (d.params ψ).reverse (consList ps (consList rs ρ)) := d.satOfSpine hpsC
    have hlenfs : fs.length = cA.2 := by
      rw [hfsL.length_eq, List.length_map, rebit_length, liftDoms_length, List.length_drop, hcd.len]
      omega
    have hlenMm : Ls.length + cds.length = (Msl ++ msl).length := by
      rw [List.length_append, hF.mslLen, hF.minsLen, hlenLc]
    have hfs' : SpineFit (consList ps (consList rs ρ)) ((d.Fss c ψ).getD j []) fs := by
      rw [rebit_map_dom, spineFit_liftDoms, consList_append, consList_append,
        ← consList_append Msl msl, hlenMm, shiftE_consList] at hfsL
      rw [IsBlockModel.Fss_getD hj]; exact hfsL
    have hfr : consList (ps ++ Msl ++ msl ++ fs) (consList rs ρ)
        = consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))) := by
      simp only [consList_append]
    rw [hfr, AnnotValid_eqE]
    have hokV := h.ctor_validV hj hρpc
    constructor
    · -- **the left-hand side**
      unfold specLhsAV
      refine mkAppN_validV tupleVarAV_validV fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact recPrefixBvarsMK_validV ha
        · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
          rw [AnnotValid_liftN, ← consList_append Msl msl,
            show d.k + d.nCtors = (Msl ++ msl).length from by
              rw [List.length_append, hF.mslLen, hF.minsLen],
            ← hlenfs, shiftE_consList_len, shiftE_consList]
          exact (AnnotValid.mkAppN_inv (hokV.2 fs hfs')).2 E (List.mem_append_right _ hE)
      · obtain rfl := List.mem_singleton.mp ha
        refine mkAppN_validV (hval _ _) fun a' ha' => ?_
        rcases List.mem_append.mp ha' with ha' | ha'
        · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha'; trivial
        · exact fieldBvars_validV ha'
    · -- **the right-hand side**
      unfold specRuleCoreAV
      refine mkAppN_validV trivial fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · exact fieldBvars_validV ha
      · obtain ⟨i, hiI, rfl⟩ := List.mem_map.mp ha
        exact hreps.ihApp_validV hc hj hF.mslLen hF.minsLen hpsC hfs' hiI
  · -- **the `Prop` regime**: an equation is a truth value
    show interp V (consList xs (consList rs ρ)) (AnnotTerm.eqE _ _) ∈ˢ (univZero : V)
    rw [interp_eqE]
    exact eqv_mem_univZero _ _
