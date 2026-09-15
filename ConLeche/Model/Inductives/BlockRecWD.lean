module

public import ConLeche.Model.Inductives.BlockRecTyped
import ConLeche.Model.Inductives.BlockRecEq
import ConLeche.Model.Inductives.FixRuleKit
import ConLeche.Model.Inductives.BlockRecFrames
public section

/-!
# The rules' equations graded at every typed tuple (task #315, M3)

`blockRecs`'s `heq`: every rule's equation (`specEqAV`, `BlockRec.lean`)
is graded (`WellDenoted`) at the frame of ANY tuple typed at the
recursor types' readings — not only the candidate's.  The Π-tower's
domains are the recursor type's prefix (graded by the type's own
grading, `hokT`) and the constructor's fields lifted under the motives
and minors (graded by the constructor type's, `ctor_okB`); the body is
the equation of two application chains.  The left-hand side applies
the tuple's component to a spine fitting its recursor type
(`spineFit_recData_of`) — with the constructor's application graded
by the CONSTRUCTOR's typing (`CtorsTyped`, the run's `mem_type` at the
stored constructor, the fits finding's sibling); the right-hand side
applies the frame's minor to the fields and the inductive hypotheses'
applications, each a λ-tower over the field's moved telescope whose
body applies the target's component to a spine fitting ITS recursor
type, the tower in the ih binder's domain (`interp_ihDomAVM`), the
chain along the minor's type (`appChainOk_of_mkPisAV'` at the fields,
`ihPisAVM_appChainOk` at the hypotheses).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Kit -/

/-- The constructors' values typed at their types' readings — the
run's `EnvModelM.mem_type` at each stored constructor (with
`CtorDataI.read`); consumed by the left-hand side's grading. -/
@[expose] def CtorsTyped (m : EnvModel V env) (d : BlockRepData V) (ψ : Name → Nat) : Prop :=
  ∀ c, c < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
    ∀ ρ : Nat → V,
      interp V ρ (m.acval cA.1.name ψ)
        ∈ˢ interp V ρ (mkPisAV (d.dsF c j ψ) (ctorBodyAVI m (d.memberName c) d.nP cA.2 ψ (d.esF c j ψ)))

/-- Graded fields' prefix. -/
theorem FieldsOkB.append_left {w : Nat} :
    ∀ {Fs₁ Fs₂ : List AnnotTerm} {ρ : Nat → V}, FieldsOkB w ρ (Fs₁ ++ Fs₂) → FieldsOkB w ρ Fs₁
  | [], _, _, _ => trivial
  | _ :: Fs₁, Fs₂, _, h => ⟨h.1, h.2.1, fun a ha => FieldsOkB.append_left (Fs₁ := Fs₁) (Fs₂ := Fs₂) (h.2.2 a ha)⟩

/-- Graded fields, appended: the suffix at every fitting spine of the
prefix. -/
theorem FieldsOkB.append {w : Nat} :
    ∀ {Fs₁ Fs₂ : List AnnotTerm} {ρ : Nat → V}, FieldsOkB w ρ Fs₁ →
      (∀ as, SpineFit ρ Fs₁ as → FieldsOkB w (consList as ρ) Fs₂) → FieldsOkB w ρ (Fs₁ ++ Fs₂)
  | [], _, _, _, h₂ => by simpa using h₂ [] trivial
  | F :: Fs₁, Fs₂, ρ, h₁, h₂ => by
    refine ⟨h₁.1, h₁.2.1, fun a ha => FieldsOkB.append (h₁.2.2 a ha) fun as hsp => ?_⟩
    have := h₂ (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- A graded application chain's arguments are graded. -/
theorem wellDenoted_of_mkAppN_arg :
    ∀ {args : List AnnotTerm} {f : AnnotTerm} {σ : Nat → V},
      WellDenoted V σ (AnnotTerm.mkAppN f args) → ∀ a ∈ args, WellDenoted V σ a
  | [], _, _, _, _, ha => absurd ha (List.not_mem_nil)
  | a :: args, f, σ, h, a', ha' => by
    rw [AnnotTerm.mkAppN_cons] at h
    rcases List.mem_cons.mp ha' with rfl | ha'
    · have := wellDenoted_of_mkAppN_arg (args := args) (f := .app f a') h
      cases args with
      | nil => exact ((WellDenoted_app V σ f a').mp h).2.1
      | cons b bs =>
        have hh : WellDenoted V σ (AnnotTerm.mkAppN (.app f a') (b :: bs)) := h
        exact ((WellDenoted_app V σ f a').mp (wellDenoted_of_mkAppN_head hh)).2.1
    · exact wellDenoted_of_mkAppN_arg h a' ha'
where
  /-- the head of a graded chain is graded -/
  wellDenoted_of_mkAppN_head :
    ∀ {args : List AnnotTerm} {f : AnnotTerm} {σ : Nat → V},
      WellDenoted V σ (AnnotTerm.mkAppN f args) → WellDenoted V σ f
  | [], _, _, h => h
  | a :: args, f, σ, h => by
    rw [AnnotTerm.mkAppN_cons] at h
    exact ((WellDenoted_app V σ f a).mp (wellDenoted_of_mkAppN_head h)).1

omit [SetTheory V] in
/-- The `k`-motive leading spine is variables only. -/
theorem recPrefixBvarsMK_wellDenoted [SetTheory V] {nP k n nF m : Nat} {σ : Nat → V} {a : AnnotTerm}
    (ha : a ∈ recPrefixBvarsMK nP k n nF m) : WellDenoted V σ a := by
  unfold recPrefixBvarsMK at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial
  · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial

omit [SetTheory V] in
theorem tupleVarAV_wellDenoted [SetTheory V] {k dp t : Nat} {σ : Nat → V} :
    WellDenoted V σ (tupleVarAV k dp t) := by
  unfold tupleVarAV; trivial

omit [SetTheory V] in
theorem fieldBvars_wellDenoted [SetTheory V] {nF : Nat} {σ : Nat → V} {a : AnnotTerm}
    (ha : a ∈ fieldBvars nF) : WellDenoted V σ a := by
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial

/-- Lifted domains are graded at the lifted frame when the domains are
graded at the shifted one. -/
theorem fieldsOkB_liftDoms {w n : Nat} :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k : Nat) (σ : Nat → V),
      FieldsOkB w (shiftE n k σ) (ds.map (·.2.2)) → FieldsOkB w σ ((liftDoms n k ds).map (·.2.2))
  | [], _, _, _ => trivial
  | d :: ds, k, σ, h => by
    simp only [liftDoms, List.map_cons]
    simp only [List.map_cons] at h
    refine ⟨(WellDenoted_liftN V n _ k σ).mpr h.1, fun hw => by rw [interp_liftN]; exact h.2.1 hw,
      fun a ha => ?_⟩
    rw [interp_liftN] at ha
    have := fieldsOkB_liftDoms ds (k + 1) (cons a σ) (by rw [shiftE_cons_succ']; exact h.2.2 a ha)
    exact this

/-- **The ih binders' application chain**: with each value in its
binder's domain (at the frame of the earlier ones), the applications
along the ih Π-tower are graded. -/
theorem ihPisAVM_appChainOk {b nF o : Nat} {moti : Nat → Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)} :
    ∀ (is : List Nat) (l₀ : Nat) (vs : List V) (frame : Nat → V) (body : AnnotTerm) (x : V),
      vs.length = is.length →
      x ∈ˢ interp V frame (ihPisAVM moti nF o b tls Eiss is l₀ body) →
      (b = 0 → ∀ ihs : List V, ihs.length = is.length →
        interp V (consList ihs frame) body ∈ˢ (univZero : V)) →
      (∀ l, l < is.length →
        vs.getD l pt ∈ˢ interp V (consList (vs.take l) frame)
          (ihDomAVM (moti (is.getD l 0)) nF o (is.getD l 0) (l₀ + l)
            (rebit b (tls.getD (is.getD l 0) [])) (Eiss.getD (is.getD l 0) []))) →
      AppChainOk x vs
  | [], _, [], _, _, _, _, _, _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | [], _, _ :: _, _, _, _, hlen, _, _, _ => nomatch hlen
  | _ :: _, _, [], _, _, _, hlen, _, _, _ => nomatch hlen
  | i :: is, l₀, v :: vs, frame, body, x, hlen, hx, hb0, hvs => by
    simp only [ihPisAVM, interp_pi] at hx
    have hv := hvs 0 (by simp)
    simp only [List.getD_cons_zero, List.take_zero, consList_nil, Nat.add_zero] at hv
    have hB0 : b = 0 → ∀ y, y ∈ˢ interp V frame
        (ihDomAVM (moti i) nF o i l₀ (rebit b (tls.getD i [])) (Eiss.getD i [])) →
        interp V (cons y frame) (ihPisAVM moti nF o b tls Eiss is (l₀ + 1) body) ∈ˢ (univZero : V) := by
      intro hb y _
      exact ihPisAVM_zero_univZero hb is (l₀ + 1) (cons y frame) body fun ihs hl => by
        have := hb0 hb (y :: ihs) (by simp [hl])
        rwa [consList_cons] at this
    have hxv : SetTheory.app x v
        ∈ˢ interp V (cons v frame) (ihPisAVM moti nF o b tls Eiss is (l₀ + 1) body) :=
      app_mem_piR hx hv hB0
    have ih := ihPisAVM_appChainOk is (l₀ + 1) vs (cons v frame) body (SetTheory.app x v)
      (by simpa using hlen) hxv
      (fun hb ihs hl => by
        have := hb0 hb (v :: ihs) (by simp [hl])
        rwa [consList_cons] at this)
      (fun l hl => by
        have := hvs (l + 1) (by simpa using hl)
        simp only [List.getD_cons_succ, List.take_succ_cons, consList_cons] at this
        rw [show l₀ + (l + 1) = l₀ + 1 + l from by omega] at this
        exact this)
    intro l hl
    cases l with
    | zero =>
      simp only [List.take_zero, List.foldl_nil, List.getD_cons_zero]
      exact ⟨b, _, _, hx, hv, hB0⟩
    | succ l =>
      obtain ⟨v', A', B', hm', ha', hz'⟩ := ih l (by simpa using hl)
      simp only [List.take_succ_cons, List.foldl_cons, List.getD_cons_succ]
      exact ⟨v', A', B', hm', ha', hz'⟩

/-! ## The conclusion at level zero; the constructor's application -/

/-- At elimination level zero the recursor type's conclusion is a truth
value at every fitting spine (the `Prop`-regime side condition of the
applications). -/
theorem BlockReps.conc_univZero {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} {elimL : Level} {Ls : List AnnotTerm} {nIdxs : List Nat}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    (hR : BlockReadings m d ψ elimL Ls nIdxs pps ipss cds mots tgts) {mm : Nat} (hmm : mm < d.k)
    (hℓ : elimL.eval ψ = 0) (ρ : Nat → V) {xs : List V}
    (hxs : SpineFit ρ ((mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm).map (·.2.2)) xs) :
    interp V (consList xs ρ) (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm) ∈ˢ (univZero : V) := by
  obtain ⟨ps, Msl, msl, is, t, rfl, hF, his, ht⟩ := hreps.spineFit_recData_inv hR hmm hxs
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps mm hmm
  have hpl := hreps.params_length (by omega) ψ
  have hρp : Sat V (d.params ψ).reverse (consList ps ρ) := d.satOfSpine hF.params
  have hlenI : is.length = d.nIdxAt mm := by rw [his.length_eq, h.IdsM_length]
  rw [interp_mutualConcAV_at d ρ t hF.mslLen hF.minsLen hmm hlenI]
  have := h.motive_app_mem hpl hρp (hF.motives mm hmm) his ht
  rwa [hℓ, univ_zero] at this

/-- A member's carrier at an index tuple lies in the block's universe. -/
theorem BlockRepData.carrier_app_mem_univ (d : BlockRepData V) {ψ : Name → Nat} {ρp : Nat → V} {mm : Nat} (hmm : mm < d.k)
    {is : List V} (his : SpineFit ρp (d.IdsM mm ψ) is) :
    SetTheory.app (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) mm) (d.tup ψ mm is)
      ∈ˢ (univ (d.w ψ) : V) :=
  famSpace_app (lfpTuple_mem (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) mm hmm) (d.tupMem his)

/-- **The constructor's application chain at a parameter frame**: with
the constructor typed at its type's reading (`CtorsTyped`), the
constructor at parameters `ps` and a fitting field spine `fs` is graded
along the chain. -/
theorem BlockReps.ctor_chainOk {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) (hcT : CtorsTyped m d ψ) {c : Nat} (hc : c < d.k)
    {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) {ρ₀ : Nat → V}
    {ps : List V} (hps : SpineFit ρ₀ (d.params ψ) ps) {fs : List V}
    (hfs : SpineFit (consList ps ρ₀) ((d.Fss c ψ).getD j []) fs) :
    AppChainOk (interp V ρ₀ (m.acval cA.1.name ψ)) (ps ++ fs) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hpl := hreps.params_length (by omega) ψ
  have hlenps : ps.length = d.nP := by rw [hps.length_eq, hpl]
  have hρp : Sat V (d.params ψ).reverse (consList ps ρ₀) := d.satOfSpine hps
  -- the spine fits the constructor's binder data
  have hspC : SpineFit ρ₀ ((d.dsF c j ψ).map (·.2.2)) (ps ++ fs) := by
    rw [← List.take_append_drop d.nP (d.dsF c j ψ), List.map_append]
    refine SpineFit.append ?_ ?_
    · have := h.ctor_params_fit hj hρp
      have hrng : (List.range d.nP).reverse.map (consList ps ρ₀) = ps := by
        rw [← hlenps]; exact range_reverse_map_consList ps ρ₀
      have hρ₀ : (fun i => consList ps ρ₀ (i + d.nP)) = ρ₀ := by
        funext i; rw [← hlenps, consList_apply_add]
      rw [hrng, hρ₀] at this
      exact this
    · rw [← BlockRep.Fss_getD hj]; exact hfs
  have hbitsC : ∀ d' ∈ d.dsF c j ψ, (d.w ψ = 0 ↔ d'.2.1 = 0) := fun d' hd' => hcd.bits ψ d' hd'
  refine appChainOk_of_mkPisAV' hbitsC (fun hw as' hsp => ?_) (hcT c hc j cA hj ρ₀) hspC
  -- the `Prop` regime: the body is the carrier at a tuple, a truth value
  rw [← List.take_append_drop d.nP (d.dsF c j ψ), List.map_append] at hsp
  obtain ⟨ps', fs', rfl, hps', hfs'⟩ := spineFit_append_inv hsp
  have hsat' : Sat V (d.params ψ).reverse (consList ps' ρ₀) := by
    refine (h.paramsIff c j cA hc hj ψ _).mpr ?_
    have := ConLeche.Model.sat_of_spineFit (Sat_nil V ρ₀) hps'
    simpa using this
  have hlenps' : ps'.length = d.nP := by
    rw [hps'.length_eq, List.length_map, List.length_take, hcd.len]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hlenfs' : fs'.length = cA.2 := by
    rw [hfs'.length_eq, List.length_map, List.length_drop, hcd.len]; omega
  have hfsF : SpineFit (consList ps' ρ₀) ((d.Fss c ψ).getD j []) fs' := by
    rw [BlockRep.Fss_getD hj]; exact hfs'
  have hEs := hreps.res_es_fit hfT hc hj hsat' hfsF
  unfold ctorBodyAVI
  rw [consList_append, paramBvars_eq_paramBvarsAt, ← hlenfs',
    h.leaf_app' hpl hsat' rfl hEs]
  have := d.carrier_app_mem_univ hc hEs
  rw [hw, univ_zero] at this
  rw [hw]
  exact this

/-! ## One inductive hypothesis' application, at any typed tuple -/

/-- **An inductive hypothesis' application at the rule's frame, at any
typed tuple**: graded, and its value in the ih binder's domain — the
λ-tower over the field's telescope of the target's component at the
parameters, motives, minors, the field's index readings and the field
applied.  Stated at the tuple frame `consList rs ρ`; the prefix's frame
`hF` is at the base frame `ρ` (the readings are closed). -/
theorem BlockReps.ihApp_facts {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {elimL : Level} {Ls : List AnnotTerm}
    {nIdxs : List Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} (hR : BlockReadings m d ψ elimL Ls nIdxs pps ipss cds mots tgts)
    (ρ : Nat → V) {rs : List V} (hlen : rs.length = d.k)
    (hrs : ∀ mm, mm < d.k → rs.getD mm pt ∈ˢ interp V ρ
      (mkPisAV (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm)
        (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)))
    {c : Nat} (hc : c < d.k) {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA)
    {ps Msl msl fs : List V}
    (hpre : SpineFit ρ ((recPrefixAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts).map (·.2.2))
      (ps ++ Msl ++ msl))
    (hF : PrefixFrame m d ψ elimL ρ ps Msl msl)
    (hpsC : SpineFit (consList rs ρ) (d.params ψ) ps)
    (hfs : SpineFit (consList ps ρ) ((d.Fss c ψ).getD j []) fs)
    (hfs' : SpineFit (consList ps (consList rs ρ)) ((d.Fss c ψ).getD j []) fs)
    {i : Nat} (hiI : i ∈ ConLeche.recIdxOf (d.ksF c j)) :
    WellDenoted V (consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))))
      (ihAppAVK (tupleVarAV d.k (d.nP + d.k + d.nCtors + cA.2 + ((d.tssF c j ψ).getD i []).length)
          (d.tgts c j i))
        d.nP d.k d.nCtors cA.2 i (rebit (pwBit ψ (Level.zeronessOf elimL)) ((d.tssF c j ψ).getD i []))
        ((d.eissF c j ψ).getD i [])) ∧
    interp V (consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))))
      (ihAppAVK (tupleVarAV d.k (d.nP + d.k + d.nCtors + cA.2 + ((d.tssF c j ψ).getD i []).length)
          (d.tgts c j i))
        d.nP d.k d.nCtors cA.2 i (rebit (pwBit ψ (Level.zeronessOf elimL)) ((d.tssF c j ψ).getD i []))
        ((d.eissF c j ψ).getD i []))
      ∈ˢ piTele (elimL.eval ψ)
          (teleOfFields (consList (fs.take i) (consList ps ρ)) (((d.tssF c j ψ).getD i []).map (·.2.2)))
          (fun bs => SetTheory.app
            ((((d.eissF c j ψ).getD i []).map
              (interp V (consList bs (consList (fs.take i) (consList ps ρ))))).foldl
                SetTheory.app (Msl.getD (d.tgts c j i) pt))
            (bs.foldl SetTheory.app (fs.getD i pt))) [] := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hj' : j < (d.ctorsM c).length := (List.getElem?_eq_some_iff.mp hj).1
  have hpl := hreps.params_length (by omega) ψ
  have hlenps : ps.length = d.nP := by rw [hF.params.length_eq, hpl]
  have hρp : Sat V (d.params ψ).reverse (consList ps ρ) := d.satOfSpine hF.params
  have hρpc : Sat V (d.params ψ).reverse (consList ps (consList rs ρ)) := d.satOfSpine hpsC
  have hb : pwBit ψ (Level.zeronessOf elimL) = 0 ↔ elimL.eval ψ = 0 := pwBit_zeronessOf ψ elimL
  have hk : 0 < d.k := by omega
  have hbits : ∀ mm, ∀ d' ∈ mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm,
      (elimL.eval ψ = 0 ↔ d'.2.1 = 0) := by
    intro mm d' hd'
    rw [mem_mutualRecDataAV hd', pwBit_zeronessOf]
  have hρcD : ∀ t, t < d.k → consList rs ρ (d.k - 1 - t) = rs.getD t pt := by
    intro t ht
    rw [consList_apply_lt' _ _ (by omega), hlen, show d.k - 1 - (d.k - 1 - t) = t from by omega]
  have hlenfs : fs.length = cA.2 := by rw [hfs.length_eq, h.Fss_length hj]
  have hiK : i < (d.ksF c j).length := (mem_recIdxOf.mp hiI).1
  have hiA : i < cA.2 := by rw [← hcd.ksLen]; exact hiK
  have hkind := (mem_recIdxOf.mp hiI).2
  have hr : (rsOf (d.ksF c j)).getD i false = true := by
    rw [rsOf_getD hiK, decide_eq_true_iff]; exact hkind
  have hiR : i ∈ recIdx ((d.rss c).getD j []) ((d.Fss c ψ).getD j []).length := by
    rw [h.recIdx_eq hj]; exact hiI
  have htgt : d.tgts c j i < d.k := h.tgtsLt c j i hc hj' hiK
  obtain ⟨cvT', cvR', mI', rP', rules', h'⟩ := hreps _ htgt
  have hfsI := spineFit_take' hfs (i := i) (by rw [h.Fss_length hj]; exact Nat.le_of_lt hiA)
  have hfsI' := spineFit_take' hfs' (i := i) (by rw [h.Fss_length hj]; exact Nat.le_of_lt hiA)
  have hlenI : (fs.take i).length = i := by
    rw [List.length_take, hlenfs]; exact Nat.min_eq_left (Nat.le_of_lt hiA)
  have hfitL := hreps.fitsFrom_of_spineFit_go hfT hc hj hρp _ 0 [] fs rfl trivial
    (by rw [consList_nil]; exact hfs)
  rw [consList_nil] at hfitL
  -- the motives are non-empty
  obtain ⟨M0, Msl', rfl⟩ : ∃ M0 Msl', Msl = M0 :: Msl' := by
    cases Msl with
    | nil => exact absurd hk (by rw [← hF.mslLen]; exact Nat.lt_irrefl _)
    | cons M0 Msl' => exact ⟨M0, Msl', rfl⟩
  have hms : (Msl' ++ msl).length + 1 = d.nCtors + d.k := by
    rw [List.length_append, hF.minsLen]; have := hF.mslLen; simp only [List.length_cons] at this; omega
  have ho : (M0 :: Msl').length + msl.length = d.nCtors + d.k := by
    rw [hF.mslLen, hF.minsLen]; omega
  have hne : 0 < (M0 :: Msl').length := by simp
  -- the frames
  have hfr : consList fs (consList msl (consList (M0 :: Msl') (consList ps (consList rs ρ))))
      = consList [] (consList [] (consList fs (consList (Msl' ++ msl) (cons M0 (consList ps (consList rs ρ)))))) := by
    rw [consList_nil, consList_nil, consList_motives_cons]
  have hfr' : consList fs (consList msl (consList (M0 :: Msl') (consList ps (consList rs ρ))))
      = consList [] (consList fs (consList (Msl' ++ msl) (cons M0 (consList ps (consList rs ρ))))) := by
    rw [consList_nil, consList_motives_cons]
  -- the field's domain at its position
  have hdomF : ((d.Fss c ψ).getD j []).getD i default = ((d.dsF c j ψ).getD (d.nP + i) default).2.2 := by
    rw [BlockRep.Fss_getD hj, fields_getD (by rw [List.length_drop, hcd.len]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  have hwdF : WellDenoted V (consList (fs.take i) (consList ps (consList rs ρ)))
      (((d.dsF c j ψ).getD (d.nP + i) default).2.2) := by
    rw [← hdomF]
    exact FieldsOkB.wellDenoted_at (h.ctor_okB hj hρpc).1 i (by rw [h.Fss_length hj]; exact hiA) _ hfsI'
  have hmemF : fs.getD i pt ∈ˢ interp V (consList (fs.take i) (consList ps (consList rs ρ)))
      (((d.dsF c j ψ).getD (d.nP + i) default).2.2) := by
    rw [← hdomF]
    exact FixKI.spineFit_getD_mem' hfs' (by rw [h.Fss_length hj]; exact hiA)
  -- per kind: the telescope graded, the index readings graded, the field's chain
  have hkindF : FieldsOkB 0 (consList (fs.take i) (consList ps (consList rs ρ)))
        (((d.tssF c j ψ).getD i []).map (·.2.2)) ∧
      (∀ bs, SpineFit (consList (fs.take i) (consList ps (consList rs ρ)))
          (((d.tssF c j ψ).getD i []).map (·.2.2)) bs →
        (∀ E ∈ (d.eissF c j ψ).getD i [],
          WellDenoted V (consList bs (consList (fs.take i) (consList ps (consList rs ρ)))) E) ∧
        AppChainOk (fs.getD i pt) bs) := by
    rcases hkind with hrec | hrefl
    · have htl : (d.tssF c j ψ).getD i [] = [] := hcd.tssNone ψ i (by rw [hrec]; decide)
      rw [htl]
      refine ⟨trivial, fun bs hbs => ?_⟩
      cases bs with
      | cons _ _ => exact hbs.elim
      | nil =>
        refine ⟨fun E hE => ?_, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
        rw [hcd.recEntry ψ i hrec hiA] at hwdF
        rw [consList_nil]
        exact wellDenoted_of_mkAppN_arg hwdF E (List.mem_append_right _ hE)
    · rw [hcd.reflEntry ψ i hrefl hiA] at hwdF hmemF
      have hinv := WellDenoted_mkPisAV_inv hwdF
      refine ⟨hinv.1, fun bs hbs => ⟨fun E hE => ?_, ?_⟩⟩
      · exact wellDenoted_of_mkAppN_arg (hinv.2 bs hbs) E (List.mem_append_right _ hE)
      · refine appChainOk_of_mkPisAV' (m := d.w ψ) (fun d' hd' => (hcd.tssBits ψ i d' hd').symm)
          (fun hw bs' hbs' => ?_) hmemF hbs
        have hlenbs' : bs'.length = ((d.tssF c j ψ).getD i []).length := by
          rw [hbs'.length_eq, List.length_map]
        rw [← consList_append (fs.take i) bs', show d.nP + i + ((d.tssF c j ψ).getD i []).length
            = d.nP + (fs.take i ++ bs').length from by
              rw [List.length_append, hlenI, hlenbs']; omega]
        have hE := hreps.refl_eis_fit hfT hc hj hρpc hiA hrefl hfsI' hbs'
        rw [← consList_append (fs.take i) bs'] at hE
        rw [h'.leaf_app' hpl hρpc rfl hE]
        have := d.carrier_app_mem_univ htgt hE
        rw [hw, univ_zero] at this
        rw [hw]
        exact this
  -- **the body facts at a fitting telescope spine (at the base frame)**
  have hbody : ∀ bs, SpineFit (consList (fs.take i) (consList ps ρ)) (((d.tssF c j ψ).getD i []).map (·.2.2)) bs →
      SpineFit (consList (fs.take i) (consList ps (consList rs ρ))) (((d.tssF c j ψ).getD i []).map (·.2.2)) bs ∧
      ((d.eissF c j ψ).getD i []).map (interp V (consList bs (consList (fs.take i) (consList ps (consList rs ρ)))))
        = ((d.eissF c j ψ).getD i []).map (interp V (consList bs (consList (fs.take i) (consList ps ρ)))) ∧
      AppChainOk (rs.getD (d.tgts c j i) pt)
        (ps ++ M0 :: Msl' ++ msl ++
          ((d.eissF c j ψ).getD i []).map (interp V (consList bs (consList (fs.take i) (consList ps ρ)))) ++
          [bs.foldl SetTheory.app (fs.getD i pt)]) ∧
      (ps ++ M0 :: Msl' ++ msl ++
          ((d.eissF c j ψ).getD i []).map (interp V (consList bs (consList (fs.take i) (consList ps ρ)))) ++
          [bs.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app (rs.getD (d.tgts c j i) pt)
        ∈ˢ SetTheory.app
          ((((d.eissF c j ψ).getD i []).map
            (interp V (consList bs (consList (fs.take i) (consList ps ρ))))).foldl
              SetTheory.app ((M0 :: Msl').getD (d.tgts c j i) pt))
          (bs.foldl SetTheory.app (fs.getD i pt)) ∧
      SetTheory.app
          ((((d.eissF c j ψ).getD i []).map
            (interp V (consList bs (consList (fs.take i) (consList ps ρ))))).foldl
              SetTheory.app ((M0 :: Msl').getD (d.tgts c j i) pt))
          (bs.foldl SetTheory.app (fs.getD i pt)) ∈ˢ (univ (elimL.eval ψ) : V) := by
    intro bs hbs
    have hlenbs : bs.length = ((d.tssF c j ψ).getD i []).length := by
      rw [hbs.length_eq, List.length_map]
    have hbsc : SpineFit (consList (fs.take i) (consList ps (consList rs ρ)))
        (((d.tssF c j ψ).getD i []).map (·.2.2)) bs := by
      have := spineFit_transport (hcd.tssBelow ψ i) (as := ps ++ fs.take i)
        (by rw [List.length_append, hlenps, hlenI]) (ρ₁ := ρ) (ρ₂ := consList rs ρ)
        (by rw [consList_append]; exact hbs)
      rwa [consList_append] at this
    have hEisρ : ((d.eissF c j ψ).getD i []).map
        (interp V (consList bs (consList (fs.take i) (consList ps (consList rs ρ)))))
        = ((d.eissF c j ψ).getD i []).map (interp V (consList bs (consList (fs.take i) (consList ps ρ)))) := by
      apply List.map_congr_left
      intro E hE
      rw [← consList_append ps (fs.take i), ← consList_append (ps ++ fs.take i) bs,
        ← consList_append ps (fs.take i), ← consList_append (ps ++ fs.take i) bs]
      exact interp_closed_bottom (hcd.eissBelow ψ i E hE)
        (by rw [List.length_append, List.length_append, hlenps, hlenI, hlenbs]) _ _
    have hEis : SpineFit (consList ps ρ) (d.IdsM (d.tgts c j i) ψ)
        (((d.eissF c j ψ).getD i []).map (interp V (consList bs (consList (fs.take i) (consList ps ρ))))) :=
      hreps.eis_fit hfT hc hj hρp hiA hr hfsI hbs
    have hv := hreps.kitPred_mem hc hj' hfitL hiR
      (bs := bs) (by rw [BlockRepData.teleAt, BlockRep.tlss_getD hj]; exact hbs) pt
    rw [BlockRepData.eisAt, BlockRep.Eiss_getD hj] at hv
    have hfold : bs.foldl SetTheory.app (fs.getD i pt)
        ∈ˢ SetTheory.app (lfpTuple (d.w ψ) d.k (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ)) (d.tgts c j i))
          (d.tup ψ (d.tgts c j i)
            (((d.eissF c j ψ).getD i []).map (interp V (consList bs (consList (fs.take i) (consList ps ρ)))))) :=
      (tagged_mem_unionSet_iff.mp (relPred_subset _ _ _ _ hv)).2.2
    have hsp₂ := hreps.spineFit_recData_of hR htgt hpre hF hEis hfold
    have hlenEis : (((d.eissF c j ψ).getD i []).map
        (interp V (consList bs (consList (fs.take i) (consList ps ρ))))).length = d.nIdxAt (d.tgts c j i) := by
      rw [hEis.length_eq, h'.IdsM_length]
    have hval := mkPisAV_fold_mem (hbits _) (fun h0 as' hsp => hreps.conc_univZero hR htgt h0 ρ hsp)
      (hrs _ htgt) hsp₂
    rw [interp_mutualConcAV_at d ρ _ hF.mslLen hF.minsLen htgt hlenEis] at hval
    refine ⟨hbsc, hEisρ, appChainOk_of_mkPisAV' (hbits _)
      (fun h0 as' hsp => hreps.conc_univZero hR htgt h0 ρ hsp) (hrs _ htgt) hsp₂, hval,
      h'.motive_app_mem hpl hρp (hF.motives _ htgt) hEis hfold⟩
  constructor
  · -- **graded**: the λ-tower over the moved telescope
    unfold ihAppAVK
    refine mkLamsAV_bits_wellDenoted (m := pwBit ψ (Level.zeronessOf elimL)) (fun d' hd' => ?_)
      (underTowerOk_of_walk (b := _) (C := AnnotTerm.mkAppN
        (.bvar (cA.2 + (d.nCtors + d.k) - 1 + 0 + ((d.tssF c j ψ).getD i []).length - d.tgts c j i))
        (((d.eissF c j ψ).getD i []).map (ihIdxAtM cA.2 (d.nCtors + d.k) i 0 ((d.tssF c j ψ).getD i []).length) ++
          [AnnotTerm.mkAppN (.bvar (cA.2 - 1 - i + 0 + ((d.tssF c j ψ).getD i []).length))
            (teleVarsAV ((d.tssF c j ψ).getD i []).length)])) ?_ ?_)
    · obtain ⟨d'', hd'', he⟩ := mem_ihTeleAtGo hd'
      rw [he, mem_rebit hd'']
    · -- the walk over the moved telescope
      refine domsWalk_of_fieldsOkB (w := 0) ?_
      unfold ihTeleAtR
      rw [hfr]
      have := fieldsOkB_ihTeleAtGo (w := 0) (ρp := consList ps (consList rs ρ)) (M := M0) (ms := Msl' ++ msl)
        hms hlenfs (ihs := []) rfl (Nat.le_of_lt hiA) (rebit (pwBit ψ (Level.zeronessOf elimL))
          ((d.tssF c j ψ).getD i [])) []
        (by rw [rebit_map_dom, consList_nil]; exact hkindF.1)
      simpa only [List.length_nil] using this
    · -- the leaf at every fitting spine
      intro bs hbs
      rw [rebit_length]
      have hbsc : SpineFit (consList (fs.take i) (consList ps (consList rs ρ)))
          (((d.tssF c j ψ).getD i []).map (·.2.2)) bs := by
        have := (spineFit_ihTeleAtR_M (ρp := consList ps (consList rs ρ)) (Msl := M0 :: Msl') (msl := msl)
          ho hne hlenfs (ihs := []) rfl (Nat.le_of_lt hiA) _ bs).mp (by rw [consList_nil]; exact hbs)
        rwa [rebit_map_dom] at this
      have hbsρ : SpineFit (consList (fs.take i) (consList ps ρ)) (((d.tssF c j ψ).getD i []).map (·.2.2)) bs := by
        have := spineFit_transport (hcd.tssBelow ψ i) (as := ps ++ fs.take i)
          (by rw [List.length_append, hlenps, hlenI]) (ρ₁ := consList rs ρ) (ρ₂ := ρ)
          (by rw [consList_append]; exact hbsc)
        rwa [consList_append] at this
      obtain ⟨-, hEisρ, hchain, hval, huniv⟩ := hbody bs hbsρ
      have hlenbs : bs.length = ((d.tssF c j ψ).getD i []).length := by
        rw [hbs.length_eq, List.length_map, ihTeleAtR_length, rebit_length]
      rw [← hlenbs]
      -- the ih domain's body reads to the target's conclusion
      have hT : interp V (consList bs (consList fs (consList msl (consList (M0 :: Msl') (consList ps (consList rs ρ))))))
          (AnnotTerm.mkAppN (.bvar (cA.2 + (d.nCtors + d.k) - 1 + 0 + bs.length - d.tgts c j i))
            (((d.eissF c j ψ).getD i []).map (ihIdxAtM cA.2 (d.nCtors + d.k) i 0 bs.length) ++
              [AnnotTerm.mkAppN (.bvar (cA.2 - 1 - i + 0 + bs.length)) (teleVarsAV bs.length)]))
          = SetTheory.app
            ((((d.eissF c j ψ).getD i []).map
              (interp V (consList bs (consList (fs.take i) (consList ps ρ))))).foldl
                SetTheory.app ((M0 :: Msl').getD (d.tgts c j i) pt))
            (bs.foldl SetTheory.app (fs.getD i pt)) := by
        have := interp_ihDomBodyM (ρp := consList ps (consList rs ρ)) (Msl := M0 :: Msl') (msl := msl)
          ho (by rw [hF.mslLen]; exact htgt) hlenfs (ihs := []) (l := 0) rfl hiA bs ((d.eissF c j ψ).getD i [])
        rw [consList_nil] at this
        rw [this, hEisρ]
      -- the telescope's variables and the field's variable, read
      have hteleVars : (teleVarsAV bs.length).map
          (interp V (consList bs (consList fs (consList msl (consList (M0 :: Msl') (consList ps (consList rs ρ))))))) = bs :=
        map_fieldBvars_interp rfl _
      have hfi : consList bs (consList fs (consList msl (consList (M0 :: Msl') (consList ps (consList rs ρ)))))
          (cA.2 - 1 - i + bs.length) = fs.getD i pt := by
        rw [consList_apply_add, consList_apply_lt' fs _ (by omega),
          show fs.length - 1 - (cA.2 - 1 - i) = i from by omega]
      have hEmap := map_ihIdxAtM_interp (ρp := consList ps (consList rs ρ)) (Msl := M0 :: Msl') (msl := msl)
        (o := d.nCtors + d.k) (l := 0) ho hne hlenfs (ihs := []) rfl (Nat.le_of_lt hiA) bs
        ((d.eissF c j ψ).getD i [])
      rw [consList_nil] at hEmap
      refine ⟨?_, ?_, fun h0 => ?_⟩
      · -- the body is graded
        refine (mkAppN_wellDenoted_of_chain tupleVarAV_wellDenoted (fun a ha => ?_) ?_).1
        · rcases List.mem_append.mp ha with ha | ha
          · rcases List.mem_append.mp ha with ha | ha
            · exact recPrefixBvarsMK_wellDenoted ha
            · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
              have hwdE := (hkindF.2 bs hbsc).1 E hE
              rw [hfr']
              exact (WellDenoted_ihIdxAtM hms hlenfs rfl (Nat.le_of_lt hiA) bs E).mpr hwdE
          · obtain rfl := List.mem_singleton.mp ha
            refine (mkAppN_wellDenoted_of_chain (f := AnnotTerm.bvar (cA.2 - 1 - i + bs.length))
              (args := teleVarsAV bs.length) (by simp) (fun a ha => teleVarsAV_wellDenoted ha) ?_).1
            rw [interp_bvar, hteleVars, hfi]
            exact (hkindF.2 bs hbsc).2
        · rw [interp_tupleVarAV_at hlenps hF.mslLen hF.minsLen hlenfs, hρcD _ htgt, List.map_append,
            List.map_append, map_recPrefixBvarsMK_interp hlenps hF.mslLen hF.minsLen hlenfs, hEmap,
            List.map_cons, List.map_nil, interp_mkAppN, interp_bvar, hfi,
            ← List.foldl_map (f := interp V (consList bs (consList fs (consList msl (consList (M0 :: Msl')
              (consList ps (consList rs ρ))))))) (g := SetTheory.app) (l := teleVarsAV bs.length),
            hteleVars, hEisρ]
          exact hchain
      · rw [interp_ihAppBody_at hlenps hF.mslLen hF.minsLen hlenfs hk hiA, hρcD _ htgt, hEisρ, hT]
        exact hval
      · rw [hT]
        have := huniv
        rw [hb.mp h0, univ_zero] at this
        exact this
  · -- **in the ih domain**: the tower at the base frame, in the product
    rw [interp_ihAppAVK_at hlenps hF.mslLen hF.minsLen hlenfs hk hiA, hρcD _ htgt, lamTower_bit_agree hb,
      show consList (fs.take i) (consList ps (consList rs ρ)) = consList (ps ++ fs.take i) (consList rs ρ)
        from by rw [consList_append]]
    rw [lamTower_congr_bottom (ρ₂ := ρ)
      (g₂ := fun σ'' => (ps ++ M0 :: Msl' ++ msl ++ ((d.eissF c j ψ).getD i []).map (interp V σ'') ++
        [(ConLeche.Semantics.frameIdx ((d.tssF c j ψ).getD i []).length σ'').foldl SetTheory.app (fs.getD i pt)]).foldl
          SetTheory.app (rs.getD (d.tgts c j i) pt))
      (fun k' d' hd' => by
        rw [List.length_append, hlenps, hlenI]
        exact domsBelow_getElem? (hcd.tssBelow ψ i) hd')
      (fun bs hbs => ?_)]
    · rw [consList_append ps (fs.take i) ρ]
      refine lamTower_mem_piTele (acc := []) fun bs hbs => ?_
      obtain ⟨-, -, -, hval, -⟩ := hbody bs hbs
      have hlenbs : bs.length = ((d.tssF c j ψ).getD i []).length := by
        rw [hbs.length_eq, List.length_map]
      simp only [List.nil_append]
      rw [← hlenbs, frameIdx_consList']
      exact hval
    · rw [consList_append] at hbs
      have hbsρ : SpineFit (consList (fs.take i) (consList ps ρ)) (((d.tssF c j ψ).getD i []).map (·.2.2)) bs := by
        have := spineFit_transport (hcd.tssBelow ψ i) (as := ps ++ fs.take i)
          (by rw [List.length_append, hlenps, hlenI]) (ρ₁ := consList rs ρ) (ρ₂ := ρ)
          (by rw [consList_append]; exact hbs)
        rwa [consList_append] at this
      obtain ⟨-, hEisρ, -, -, -⟩ := hbody bs hbsρ
      have hlenbs : bs.length = ((d.tssF c j ψ).getD i []).length := by
        rw [hbs.length_eq, List.length_map]
      show (ps ++ M0 :: Msl' ++ msl ++ ((d.eissF c j ψ).getD i []).map (interp V (consList (ps ++ fs.take i ++ bs) (consList rs ρ))) ++
          [(ConLeche.Semantics.frameIdx ((d.tssF c j ψ).getD i []).length (consList (ps ++ fs.take i ++ bs) (consList rs ρ))).foldl
            SetTheory.app (fs.getD i pt)]).foldl SetTheory.app (rs.getD (d.tgts c j i) pt) = _
      rw [consList_append (ps ++ fs.take i) bs (consList rs ρ), consList_append (ps ++ fs.take i) bs ρ,
        ← hlenbs, frameIdx_consList', frameIdx_consList', consList_append ps (fs.take i) ρ,
        consList_append ps (fs.take i) (consList rs ρ), hEisρ]

/-! ## `heq` -/

/-- **The rules' equations are graded at every typed tuple**
(`blockRecs`'s `heq`, per rule): at the frame of any tuple `rs` whose
components are typed at the recursor types' readings, rule `(c, j)`'s
equation is `WellDenoted`.  The Π-tower's domains are the recursor
type's prefix (graded by `hokT`) and the constructor's fields lifted
under the motives and minors (`ctor_okB`); at a fitting spine the
left-hand side's chain is the tuple's component at a spine fitting its
type (`spineFit_recData_of`) with the constructor's application graded
by `CtorsTyped`, and the right-hand side's chain is the frame's minor
at the fields (its type's leading Π-tower) and the inductive
hypotheses' applications (`ihApp_facts`, then `ihPisAVM_appChainOk`). -/
theorem BlockReps.blockEq_wd {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) (hcT : CtorsTyped m d ψ) {elimL : Level}
    {Ls : List AnnotTerm} {nIdxs : List Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} (hR : BlockReadings m d ψ elimL Ls nIdxs pps ipss cds mots tgts)
    (hokT : ∀ mm, mm < d.k → ∀ ρ : Nat → V,
      WellDenoted V ρ (mkPisAV (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm)
        (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)))
    (ρ : Nat → V) {rs : List V} (hlen : rs.length = d.k)
    (hrs : ∀ mm, mm < d.k → rs.getD mm pt ∈ˢ interp V ρ
      (mkPisAV (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm)
        (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)))
    {c : Nat} (hc : c < d.k) {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) :
    WellDenoted V (consList rs ρ)
      (specEqAV (mutualRuleDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts (d.dsF c j ψ))
        (specLhsAV d.k d.nP d.nCtors cA.2 c (d.esF c j ψ) (m.acval cA.1.name ψ))
        (specRuleCoreAV (pwBit ψ (Level.zeronessOf elimL)) d.k (d.tgts c j) d.nP d.nCtors cA.2
          (d.minorIdx c j) (ConLeche.recIdxOf (d.ksF c j)) (d.tssF c j ψ) (d.eissF c j ψ))) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hj' : j < (d.ctorsM c).length := (List.getElem?_eq_some_iff.mp hj).1
  have hpl := hreps.params_length (by omega) ψ
  have hb : pwBit ψ (Level.zeronessOf elimL) = 0 ↔ elimL.eval ψ = 0 := pwBit_zeronessOf ψ elimL
  have hJ := d.minorIdx_lt hc hj'
  have hk : 0 < d.k := by omega
  have hbits : ∀ mm, ∀ d' ∈ mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm,
      (elimL.eval ψ = 0 ↔ d'.2.1 = 0) := by
    intro mm d' hd'
    rw [mem_mutualRecDataAV hd', pwBit_zeronessOf]
  have hρcD : ∀ t, t < d.k → consList rs ρ (d.k - 1 - t) = rs.getD t pt := by
    intro t ht
    rw [consList_apply_lt' _ _ (by omega), hlen, show d.k - 1 - (d.k - 1 - t) = t from by omega]
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
  refine WellDenoted_mkPisAV_of (w := 0) ?_ ?_
  · -- **the domains**
    rw [hdoms]
    refine FieldsOkB.append ?_ fun xs hxs => ?_
    · have := (WellDenoted_mkPisAV_inv (hokT c hc (consList rs ρ))).1
      rw [mutualRecDataAV_eq_prefix, List.map_append] at this
      exact FieldsOkB.append_left this
    · obtain ⟨ps, Msl, msl, rfl, hF⟩ := spineFit_prefix_inv hR hxs
      have hρp : Sat V (d.params ψ).reverse (consList ps (consList rs ρ)) := d.satOfSpine hF.params
      rw [rebit_map_dom]
      refine fieldsOkB_liftDoms _ _ _ ?_
      rw [consList_append, consList_append, ← consList_append Msl msl,
        show Ls.length + cds.length = (Msl ++ msl).length from by
          rw [List.length_append, hF.mslLen, hF.minsLen, hlenLc],
        shiftE_consList, ← BlockRep.Fss_getD hj]
      exact (h.ctor_okB hj hρp).1
  · -- **the body at a fitting spine**
    intro xs hxs
    rw [hdoms] at hxs
    obtain ⟨xs₁, fs, rfl, hpre, hfsL⟩ := spineFit_append_inv hxs
    have hpreρ := spineFit_transport₀ hbelowPre (ρ₂ := ρ) hpre
    obtain ⟨ps, Msl, msl, rfl, hF⟩ := spineFit_prefix_inv hR hpreρ
    have hlenps : ps.length = d.nP := by rw [hF.params.length_eq, hpl]
    have hρp : Sat V (d.params ψ).reverse (consList ps ρ) := d.satOfSpine hF.params
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
      rw [rebit_map_dom, spineFit_liftDoms, consList_append, consList_append, ← consList_append Msl msl,
        hlenMm, shiftE_consList] at hfsL
      rw [BlockRep.Fss_getD hj]; exact hfsL
    have hfs : SpineFit (consList ps ρ) ((d.Fss c ψ).getD j []) fs := by
      rw [BlockRep.Fss_getD hj] at hfs' ⊢
      exact spineFit_transport (DomsBelow.drop d.nP (hcd.below ψ)) (by rw [hlenps, Nat.zero_add]) hfs'
    have hEsρ : (d.esF c j ψ).map (interp V (consList fs (consList ps (consList rs ρ))))
        = (d.esF c j ψ).map (interp V (consList fs (consList ps ρ))) := by
      apply List.map_congr_left
      intro E hE
      rw [← consList_append ps fs (consList rs ρ), ← consList_append ps fs ρ]
      exact interp_closed_bottom (hcd.belowE ψ E hE) (by rw [List.length_append, hlenps, hlenfs]) _ _
    have hfr : consList (ps ++ Msl ++ msl ++ fs) (consList rs ρ)
        = consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))) := by
      simp only [consList_append]
    rw [hfr, WellDenoted_eqE]
    have hokB := h.ctor_okB hj hρpc
    constructor
    · -- **the left-hand side**
      unfold specLhsAV
      have hEs : SpineFit (consList ps ρ) (d.IdsM c ψ)
          ((d.esF c j ψ).map (interp V (consList fs (consList ps ρ)))) :=
        hreps.res_es_fit hfT hc hj hρp hfs
      have hinj := hreps.inj_mem hfT hc hj hρp hfs
      have hsp₁ := hreps.spineFit_recData_of hR hc hpreρ hF hEs hinj
      -- the constructor's application: its value and its grading
      have hCval : ∀ σ σ' : Nat → V, interp V σ (m.acval cA.1.name ψ) = interp V σ' (m.acval cA.1.name ψ) :=
        fun σ σ' => interp_closed (V := V) (m.cval_closedL _ ψ) σ σ'
      have hrng : (List.range d.nP).reverse.map (consList ps (consList rs ρ)) = ps := by
        rw [← hlenps]; exact range_reverse_map_consList ps _
      have hargsC : (paramBvarsAt d.nP (d.nP + d.k + d.nCtors + cA.2) ++ fieldBvars cA.2).map
          (interp V (consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))))) = ps ++ fs := by
        rw [List.map_append, show d.nP + d.k + d.nCtors + cA.2 = d.nP + (d.k + d.nCtors + cA.2) from by omega,
          map_paramBvarsAt_interp (ρp := consList ps (consList rs ρ)) (fun j' => by
            rw [show j' + (d.k + d.nCtors + cA.2) = ((j' + Msl.length) + msl.length) + fs.length from by
                rw [hF.mslLen, hF.minsLen, hlenfs]; omega,
              consList_apply_add, consList_apply_add, consList_apply_add]),
          show fieldBvars cA.2 = (List.range cA.2).map (fun k => AnnotTerm.bvar (cA.2 - 1 - k)) from rfl,
          map_fieldBvars_interp hlenfs, hrng]
      have hC : interp V (consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))))
          (AnnotTerm.mkAppN (m.acval cA.1.name ψ)
            (paramBvarsAt d.nP (d.nP + d.k + d.nCtors + cA.2) ++ fieldBvars cA.2)) = d.inj ψ c j fs := by
        rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList fs (consList msl (consList Msl
          (consList ps (consList rs ρ)))))) (g := SetTheory.app), hargsC, hCval _ (consList rs ρ)]
        exact h.ctor c j cA hc hj ψ _ ps fs hpsC hfs'
      have hCwd : WellDenoted V (consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))))
          (AnnotTerm.mkAppN (m.acval cA.1.name ψ)
            (paramBvarsAt d.nP (d.nP + d.k + d.nCtors + cA.2) ++ fieldBvars cA.2)) := by
        refine (mkAppN_wellDenoted_of_chain (m.acval_wellDenoted _ _ _) (fun a ha => ?_) ?_).1
        · rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial
          · exact fieldBvars_wellDenoted ha
        · rw [hargsC, hCval _ (consList rs ρ)]
          exact hreps.ctor_chainOk hfT hcT hc hj hpsC hfs'
      refine (mkAppN_wellDenoted_of_chain tupleVarAV_wellDenoted (fun a ha => ?_) ?_).1
      · rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp ha with ha | ha
          · exact recPrefixBvarsMK_wellDenoted ha
          · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
            rw [WellDenoted_liftN, ← consList_append Msl msl,
              show d.k + d.nCtors = (Msl ++ msl).length from by rw [List.length_append, hF.mslLen, hF.minsLen],
              ← hlenfs, shiftE_consList_len, shiftE_consList]
            exact wellDenoted_of_mkAppN_arg (hokB.2 fs hfs') E (List.mem_append_right _ hE)
        · obtain rfl := List.mem_singleton.mp ha
          exact hCwd
      · have hvar := interp_tupleVarAV_at (bs := []) (ρc := consList rs ρ) hlenps hF.mslLen hF.minsLen hlenfs c
        rw [List.length_nil, consList_nil, Nat.add_zero] at hvar
        have hpre' := map_recPrefixBvarsMK_interp (bs := []) (ρ' := consList rs ρ) hlenps hF.mslLen hF.minsLen hlenfs
        rw [List.length_nil, consList_nil] at hpre'
        rw [hvar, hρcD c hc, List.map_append, List.map_append, hpre',
          map_liftN_interp (by rw [hF.mslLen, hF.minsLen]) hlenfs, List.map_cons, List.map_nil, hC, hEsρ]
        exact appChainOk_of_mkPisAV' (hbits c) (fun h0 as' hsp => hreps.conc_univZero hR hc h0 ρ hsp)
          (hrs c hc) hsp₁
    · -- **the right-hand side**
      unfold specRuleCoreAV
      -- the inductive hypotheses' applications
      have hih := fun i (hiI : i ∈ ConLeche.recIdxOf (d.ksF c j)) =>
        hreps.ihApp_facts hfT hR ρ hlen hrs hc hj hpreρ hF hpsC hfs hfs' hiI
      refine (mkAppN_wellDenoted_of_chain (f := AnnotTerm.bvar (cA.2 + d.nCtors - 1 - d.minorIdx c j))
        (by simp) (fun a ha => ?_) ?_).1
      · rcases List.mem_append.mp ha with ha | ha
        · exact fieldBvars_wellDenoted ha
        · obtain ⟨i, hiI, rfl⟩ := List.mem_map.mp ha
          exact (hih i hiI).1
      · -- the chain along the minor's type
        rw [List.map_append, interp_bvar,
          show cA.2 + d.nCtors - 1 - d.minorIdx c j = (d.nCtors - 1 - d.minorIdx c j) + fs.length from by
            rw [hlenfs]; omega,
          consList_apply_add, consList_apply_lt' _ _ (by rw [hF.minsLen]; omega), hF.minsLen,
          show d.nCtors - 1 - (d.nCtors - 1 - d.minorIdx c j) = d.minorIdx c j from by omega,
          show fieldBvars cA.2 = (List.range cA.2).map (fun k => AnnotTerm.bvar (cA.2 - 1 - k)) from rfl,
          map_fieldBvars_interp hlenfs, List.map_map]
        simp only [Function.comp_def]
        have hmin := hF.minors c j cA hc hj
        unfold minorAVAtRM at hmin
        have hoJ : Msl.length + (msl.take (d.minorIdx c j)).length = d.k + d.minorIdx c j := by
          rw [hF.mslLen, List.length_take, hF.minsLen]; congr 1; exact Nat.min_eq_left (Nat.le_of_lt hJ)
        have hbitsM : ∀ d' ∈ rebit (pwBit ψ (Level.zeronessOf elimL))
            (liftDoms (d.k + d.minorIdx c j) 0 ((d.dsF c j ψ).drop d.nP)), (elimL.eval ψ = 0 ↔ d'.2.1 = 0) := by
          intro d' hd'
          rw [mem_rebit hd']; exact hb.symm
        -- the fields fit the minor's leading binders
        have hfitM : SpineFit (consList (msl.take (d.minorIdx c j)) (consList Msl (consList ps ρ)))
            ((rebit (pwBit ψ (Level.zeronessOf elimL))
              (liftDoms (d.k + d.minorIdx c j) 0 ((d.dsF c j ψ).drop d.nP))).map (·.2.2)) fs := by
          rw [rebit_map_dom, spineFit_liftDoms, ← consList_append Msl (msl.take (d.minorIdx c j)),
            show d.k + d.minorIdx c j = (Msl ++ msl.take (d.minorIdx c j)).length from by
              rw [List.length_append]; exact hoJ.symm,
            shiftE_consList, ← BlockRep.Fss_getD hj]
          exact hfs
        -- the `Prop` regime: the minor's conclusion is a truth value
        have hconcZ : elimL.eval ψ = 0 → ∀ fs' : List V, SpineFit (consList ps ρ) ((d.Fss c ψ).getD j []) fs' →
            ∀ ihs : List V, ihs.length = (ConLeche.recIdxOf (d.ksF c j)).length →
            interp V (consList ihs (consList fs' (consList (msl.take (d.minorIdx c j)) (consList Msl (consList ps ρ)))))
              ((AnnotTerm.mkAppN (.bvar (cA.2 + (d.k + d.minorIdx c j) - 1 - c))
                (((d.esF c j ψ).map fun E => E.liftN (d.k + d.minorIdx c j) cA.2) ++
                  [AnnotTerm.mkAppN (m.acval cA.1.name ψ)
                    (paramBvarsAt d.nP (d.nP + (d.k + d.minorIdx c j) + cA.2) ++ fieldBvars cA.2)])).liftN
                (ConLeche.recIdxOf (d.ksF c j)).length 0) ∈ˢ (univZero : V) := by
          intro h0 fs' hfs'' ihs hl
          rw [interp_liftN, ← hl, shiftE_consList]
          have hmc := hreps.minor_conc hfT hc hj hρp (Msl := Msl) (msl' := msl.take (d.minorIdx c j)) hoJ
            hF.mslLen hF.motives hfs''
          rw [hmc.1]
          have := hmc.2
          rwa [h0, univ_zero] at this
        have hpropM : elimL.eval ψ = 0 → ∀ as', SpineFit (consList (msl.take (d.minorIdx c j)) (consList Msl (consList ps ρ)))
            ((rebit (pwBit ψ (Level.zeronessOf elimL))
              (liftDoms (d.k + d.minorIdx c j) 0 ((d.dsF c j ψ).drop d.nP))).map (·.2.2)) as' →
            interp V (consList as' (consList (msl.take (d.minorIdx c j)) (consList Msl (consList ps ρ))))
              (ihPisAVM (d.tgts c j) cA.2 (d.k + d.minorIdx c j) (pwBit ψ (Level.zeronessOf elimL))
                (d.tssF c j ψ) (d.eissF c j ψ) (ConLeche.recIdxOf (d.ksF c j)) 0
                ((AnnotTerm.mkAppN (.bvar (cA.2 + (d.k + d.minorIdx c j) - 1 - c))
                  (((d.esF c j ψ).map fun E => E.liftN (d.k + d.minorIdx c j) cA.2) ++
                    [AnnotTerm.mkAppN (m.acval cA.1.name ψ)
                      (paramBvarsAt d.nP (d.nP + (d.k + d.minorIdx c j) + cA.2) ++ fieldBvars cA.2)])).liftN
                  (ConLeche.recIdxOf (d.ksF c j)).length 0)) ∈ˢ (univZero : V) := by
          intro h0 as' hsp
          have hfs'' : SpineFit (consList ps ρ) ((d.Fss c ψ).getD j []) as' := by
            rw [rebit_map_dom, spineFit_liftDoms, ← consList_append Msl (msl.take (d.minorIdx c j)),
              show d.k + d.minorIdx c j = (Msl ++ msl.take (d.minorIdx c j)).length from by
                rw [List.length_append]; exact hoJ.symm,
              shiftE_consList, ← BlockRep.Fss_getD hj] at hsp
            exact hsp
          exact ihPisAVM_zero_univZero (hb.mpr h0) _ _ _ _ (hconcZ h0 as' hfs'')
        refine appChainOk_append (appChainOk_of_mkPisAV' hbitsM hpropM hmin hfitM) ?_
        -- along the inductive hypotheses
        have hx := mkPisAV_fold_mem hbitsM hpropM hmin hfitM
        refine ihPisAVM_appChainOk _ 0 _ _ _ _ (by rw [List.length_map]) hx
          (fun hb0 ihs hl => hconcZ (hb.mp hb0) fs hfs ihs hl) fun l hl => ?_
        -- the `l`-th hypothesis' value is in its domain
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some,
          Option.getD_some]
        have hiI : (ConLeche.recIdxOf (d.ksF c j))[l] ∈ ConLeche.recIdxOf (d.ksF c j) := List.getElem_mem hl
        have hiA : (ConLeche.recIdxOf (d.ksF c j))[l] < cA.2 := by
          rw [← hcd.ksLen]; exact (mem_recIdxOf.mp hiI).1
        have hgetD : (ConLeche.recIdxOf (d.ksF c j)).getD l 0 = (ConLeche.recIdxOf (d.ksF c j))[l] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
        have hmotL : d.tgts c j (ConLeche.recIdxOf (d.ksF c j))[l] < Msl.length := by
          rw [hF.mslLen]; exact h.tgtsLt c j _ hc hj' (mem_recIdxOf.mp hiI).1
        have hlenTake : (((ConLeche.recIdxOf (d.ksF c j)).map fun i =>
            interp V (consList fs (consList msl (consList Msl (consList ps (consList rs ρ)))))
              (ihAppAVK (tupleVarAV d.k (d.nP + d.k + d.nCtors + cA.2 + ((d.tssF c j ψ).getD i []).length) (d.tgts c j i))
                d.nP d.k d.nCtors cA.2 i (rebit (pwBit ψ (Level.zeronessOf elimL)) ((d.tssF c j ψ).getD i []))
                ((d.eissF c j ψ).getD i []))).take l).length = l := by
          rw [List.length_take, List.length_map]; exact Nat.min_eq_left (Nat.le_of_lt hl)
        rw [hgetD, Nat.zero_add, interp_ihDomAVM (ℓ := elimL.eval ψ) (ρp := consList ps ρ) (Msl := Msl)
          (msl := msl.take (d.minorIdx c j)) hoJ hmotL hlenfs hlenTake hiA
          (tl := rebit (pwBit ψ (Level.zeronessOf elimL)) ((d.tssF c j ψ).getD (ConLeche.recIdxOf (d.ksF c j))[l] []))
          (fun d' hd' => by rw [mem_rebit hd']; exact hb) _, rebit_map_dom]
        exact (hih _ hiI).2

/-! ## `blockRecs` at the datum's readings — closed modulo the run facts -/

/-- **The block's rule equations**, in the kernel's constructor order
(`minorIdx`): member by member, constructor by constructor. -/
@[expose] def BlockRepData.specEqs {env : Env} (d : BlockRepData V) (m : EnvModel V env)
    (ψ : Name → Nat) (elimL : Level) (Ls : List AnnotTerm) (nIdxs : List Nat)
    (pps : List (Nat × Nat × AnnotTerm)) (ipss : List (List (Nat × Nat × AnnotTerm)))
    (cds : List CtorDatumR) (mots : Nat → Nat) (tgts : Nat → Nat → Nat) : List AnnotTerm :=
  (List.range d.k).flatMap fun c => (List.range (d.ctorsM c).length).map fun j =>
    specEqAV (mutualRuleDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts (d.dsF c j ψ))
      (specLhsAV d.k d.nP d.nCtors ((d.ctorsM c).getD j default).2 c (d.esF c j ψ)
        (m.acval ((d.ctorsM c).getD j default).1.name ψ))
      (specRuleCoreAV (pwBit ψ (Level.zeronessOf elimL)) d.k (d.tgts c j) d.nP d.nCtors
        ((d.ctorsM c).getD j default).2 (d.minorIdx c j) (ConLeche.recIdxOf (d.ksF c j))
        (d.tssF c j ψ) (d.eissF c j ψ))

/-- An equation of the block is a rule's. -/
theorem BlockRepData.mem_specEqs {env : Env} {d : BlockRepData V} {m : EnvModel V env}
    {ψ : Name → Nat} {elimL : Level} {Ls : List AnnotTerm} {nIdxs : List Nat}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat} {e : AnnotTerm}
    (he : e ∈ d.specEqs m ψ elimL Ls nIdxs pps ipss cds mots tgts) :
    ∃ (c j : Nat) (cA : ConstantVal × Nat), c < d.k ∧ (d.ctorsM c)[j]? = some cA ∧
      e = specEqAV (mutualRuleDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts (d.dsF c j ψ))
        (specLhsAV d.k d.nP d.nCtors cA.2 c (d.esF c j ψ) (m.acval cA.1.name ψ))
        (specRuleCoreAV (pwBit ψ (Level.zeronessOf elimL)) d.k (d.tgts c j) d.nP d.nCtors cA.2
          (d.minorIdx c j) (ConLeche.recIdxOf (d.ksF c j)) (d.tssF c j ψ) (d.eissF c j ψ)) := by
  unfold BlockRepData.specEqs at he
  obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  have hj' : j < (d.ctorsM c).length := List.mem_range.mp hj
  refine ⟨c, j, (d.ctorsM c).getD j default, List.mem_range.mp hc, ?_, rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']; rfl

/-- **The block's recursors at the datum's readings** — `blockRecs`
with its four premises discharged (`blockCand_mem`, `blockCand_eq`,
`blockEq_wd`) from the run-level facts at every level assignment: the
datum at every member (`BlockReps`), the members and constructors
typed (`FormersTyped`, `CtorsTyped`), the readings the datum's
(`BlockReadings`), the regime fact `w = 0 → ℓ = 0`, and the recursor
types' formation (`hT`).  What M4's recursor stage consumes. -/
theorem BlockReps.blockRecsAt {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    (hfT : ∀ ψ, FormersTyped m d ψ) (hcT : ∀ ψ, CtorsTyped m d ψ) {elimL : Level}
    (hwℓ : ∀ ψ, d.w ψ = 0 → elimL.eval ψ = 0) {Ls : (Name → Nat) → List AnnotTerm}
    {nIdxs : List Nat} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {ipss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {cds : (Name → Nat) → List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    (hR : ∀ ψ, BlockReadings m d ψ elimL (Ls ψ) nIdxs (pps ψ) (ipss ψ) (cds ψ) mots tgts)
    {s : (Name → Nat) → Nat}
    (hT : ∀ (ψ : Name → Nat) (ρ : Nat → V) (mm : Nat), mm < d.k →
      interp V ρ (mkPisAV (mutualRecDataAV m ψ (Ls ψ) d.nP nIdxs elimL (pps ψ) (ipss ψ) (cds ψ) mots tgts mm)
        (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)) ∈ˢ (univ (s ψ) : V) ∧
      WellDenoted V ρ (mkPisAV (mutualRecDataAV m ψ (Ls ψ) d.nP nIdxs elimL (pps ψ) (ipss ψ) (cds ψ) mots tgts mm)
        (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm))) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V), ∃ a : Nat → V,
      (∀ mm, mm < d.k →
        a mm ∈ˢ interp V ρ
          (mkPisAV (mutualRecDataAV m ψ (Ls ψ) d.nP nIdxs elimL (pps ψ) (ipss ψ) (cds ψ) mots tgts mm)
            (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)) ∧
        interp V ρ (blockLeafAV (s ψ) d.k
          (fun t => mutualRecDataAV m ψ (Ls ψ) d.nP nIdxs elimL (pps ψ) (ipss ψ) (cds ψ) mots tgts t)
          (fun mm => mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)
          (d.specEqs m ψ elimL (Ls ψ) nIdxs (pps ψ) (ipss ψ) (cds ψ) mots tgts) mm) = a mm ∧
        WellDenoted V ρ (blockLeafAV (s ψ) d.k
          (fun t => mutualRecDataAV m ψ (Ls ψ) d.nP nIdxs elimL (pps ψ) (ipss ψ) (cds ψ) mots tgts t)
          (fun mm => mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)
          (d.specEqs m ψ elimL (Ls ψ) nIdxs (pps ψ) (ipss ψ) (cds ψ) mots tgts) mm)) ∧
      ∀ e ∈ d.specEqs m ψ elimL (Ls ψ) nIdxs (pps ψ) (ipss ψ) (cds ψ) mots tgts,
        (pt : V) ∈ˢ interp V (consList ((List.range d.k).map a) ρ) e :=
  blockRecs d s (fun ψ => elimL.eval ψ)
    (fun t ψ => mutualRecDataAV m ψ (Ls ψ) d.nP nIdxs elimL (pps ψ) (ipss ψ) (cds ψ) mots tgts t)
    (fun mm => mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)
    (fun ψ => d.specEqs m ψ elimL (Ls ψ) nIdxs (pps ψ) (ipss ψ) (cds ψ) mots tgts)
    hT
    (fun ψ ρ rs hlen hrs e he => by
      obtain ⟨c, j, cA, hc, hj, rfl⟩ := d.mem_specEqs he
      exact ⟨specEqAV_univZero _ _ _ _,
        hreps.blockEq_wd (hfT ψ) (hcT ψ) (hR ψ) (fun mm hmm ρ => (hT ψ ρ mm hmm).2) ρ hlen hrs hc hj⟩)
    (fun ψ ρ mm hmm => hreps.blockCand_mem (hfT ψ) (hwℓ ψ) (hR ψ) ρ hmm)
    (fun ψ ρ e he => by
      obtain ⟨c, j, cA, hc, hj, rfl⟩ := d.mem_specEqs he
      exact hreps.blockCand_eq (hfT ψ) (hwℓ ψ) (hR ψ) ρ hc hj)

end ConLeche.Model
