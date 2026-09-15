module

public import ConLeche.Model.Inductives.BlockRecTyped
import ConLeche.Model.Inductives.FixRecPre
public section

/-!
# The rules' equations at the candidate (task #315, M3)

`blockRecs`'s `hceq`: every rule's equation (`specEqAV`, `BlockRec.lean`)
holds at the tuple of the candidates.  At a fitting spine of the
rule's binder data — the recursor type's prefix and the constructor's
fields — the left-hand side is member `c`'s candidate at the frame,
the result index readings and the constructor's injection: by
`lamTower_fold` its leaf, the union recursor at the frame
(`blockLeafV_at`), whose recursion equation (`blockRecAt_eq`) is the
minor at the fields and the inductive hypotheses (`kitSt_tagged`, the
decode by `mkInj`); the right-hand side is that minor at the fields
and the ih applications `ihAppAVK`, each a λ-tower over the moved
telescope whose leaf is the target's candidate at the field's index
readings and the field — by the same fold, the target's leaf, which is
the graph's value at the predecessor.  At `ℓ = 0` both sides are the
point.  The spine's fit is stated at the tuple frame; the readings'
closedness (`BlockReadings.below`, the constructor's `below`) moves it
to the base frame, where the candidates live.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Closed binder data: fits move between bottoms -/

omit [SetTheory V] in
theorem DomsBelow.append_left {k : Nat} :
    ∀ {l₁ l₂ : List (Nat × Nat × AnnotTerm)}, DomsBelow k (l₁ ++ l₂) → DomsBelow k l₁
  | [], _, _ => trivial
  | _ :: l₁, l₂, h => ⟨h.1, DomsBelow.append_left (l₁ := l₁) (l₂ := l₂) h.2⟩

/-- A fit of closed binder data at one bottom is a fit at any bottom. -/
theorem spineFit_transport {ds : List (Nat × Nat × AnnotTerm)} {k : Nat} (hb : DomsBelow k ds)
    {as : List V} (hlen : as.length = k) {ρ₁ ρ₂ : Nat → V} {bs : List V}
    (h : SpineFit (consList as ρ₁) (ds.map (·.2.2)) bs) :
    SpineFit (consList as ρ₂) (ds.map (·.2.2)) bs :=
  spineFit_closed_bottom (fun k' d hd => by rw [hlen]; exact domsBelow_getElem? hb hd) h

theorem spineFit_transport₀ {ds : List (Nat × Nat × AnnotTerm)} (hb : DomsBelow 0 ds)
    {ρ₁ ρ₂ : Nat → V} {bs : List V} (h : SpineFit ρ₁ (ds.map (·.2.2)) bs) :
    SpineFit ρ₂ (ds.map (·.2.2)) bs := by
  have := spineFit_transport hb (as := []) rfl (ρ₁ := ρ₁) (ρ₂ := ρ₂) (by rw [consList_nil]; exact h)
  rwa [consList_nil] at this

/-! ## The frames' spellings, read -/

/-- Variables at an offset below a consed spine read to the spine. -/
theorem map_range_bvar_interp {k D : Nat} {as : List V} (hlen : as.length = k) (σ : Nat → V)
    (hσ : ∀ t, t < k → σ (D + (k - 1 - t)) = as.getD t pt) :
    ((List.range k).map fun t => AnnotTerm.bvar (D + (k - 1 - t))).map (interp V σ) = as := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, interp_bvar]
    rw [hσ i (by simpa using h1), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
      Option.getD_some]

/-- **The recursor's leading spine `p⃗ M⃗ m⃗` reads to the frame's
parameters, motives and minors** under `bs` further binders. -/
theorem map_recPrefixBvarsMK_interp {nP k n nF : Nat} {ρ' : Nat → V} {ps Msl msl fs bs : List V}
    (hps : ps.length = nP) (hMsl : Msl.length = k) (hmsl : msl.length = n) (hfs : fs.length = nF) :
    (recPrefixBvarsMK nP k n nF bs.length).map
        (interp V (consList bs (consList fs (consList msl (consList Msl (consList ps ρ'))))))
      = ps ++ Msl ++ msl := by
  unfold recPrefixBvarsMK
  rw [List.map_append, List.map_append]
  have hp : (paramBvarsAt nP (nP + (nF + n + k + bs.length))).map
      (interp V (consList bs (consList fs (consList msl (consList Msl (consList ps ρ'))))))
      = ps := by
    rw [map_paramBvarsAt_interp (ρp := consList ps ρ') fun j => by
      rw [show j + (nF + n + k + bs.length) = (((j + Msl.length) + msl.length) + fs.length) + bs.length
          from by rw [hfs, hmsl, hMsl]; omega,
        consList_apply_add, consList_apply_add, consList_apply_add, consList_apply_add]]
    rw [← hps]
    exact range_reverse_map_consList ps ρ'
  rw [show nP + nF + n + k + bs.length = nP + (nF + n + k + bs.length) from by omega, hp]
  congr 1
  · congr 1
    rw [show ((List.range k).map fun t => AnnotTerm.bvar (nF + n + k - 1 - t + bs.length))
        = (List.range k).map fun t => AnnotTerm.bvar ((nF + n + bs.length) + (k - 1 - t)) from by
          apply List.map_congr_left; intro t ht; rw [List.mem_range] at ht
          exact congrArg AnnotTerm.bvar (by omega)]
    refine map_range_bvar_interp hMsl _ fun t ht => ?_
    rw [show nF + n + bs.length + (k - 1 - t) = (((k - 1 - t) + msl.length) + fs.length) + bs.length
        from by rw [hmsl, hfs]; omega,
      consList_apply_add, consList_apply_add, consList_apply_add, consList_apply_lt' _ _ (by omega),
      hMsl, show k - 1 - (k - 1 - t) = t from by omega]
  · rw [show ((List.range n).map fun l => AnnotTerm.bvar (nF + n - 1 - l + bs.length))
        = (List.range n).map fun l => AnnotTerm.bvar ((nF + bs.length) + (n - 1 - l)) from by
          apply List.map_congr_left; intro l hl; rw [List.mem_range] at hl
          exact congrArg AnnotTerm.bvar (by omega)]
    refine map_range_bvar_interp hmsl _ fun l hl => ?_
    rw [show nF + bs.length + (n - 1 - l) = ((n - 1 - l) + fs.length) + bs.length
        from by rw [hfs]; omega,
      consList_apply_add, consList_apply_add, consList_apply_lt' _ _ (by omega),
      hmsl, show n - 1 - (n - 1 - l) = l from by omega]

/-- A λ-tower spelled with the entries' bits (all `b`) reads to the
semantic tower at `b`. -/
theorem interp_mkLamsAV_bits {b : Nat} (body : AnnotTerm) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (σ : Nat → V), (∀ d ∈ ds, d.2.1 = b) →
      interp V σ (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) body)
        = lamTower b σ ds (fun σ' => interp V σ' body)
  | [], _, _ => rfl
  | d :: ds, σ, h => by
    simp only [List.map_cons, mkLamsAV, interp_lam, lamTower]
    rw [h d List.mem_cons_self]
    exact lamR_congr fun a _ =>
      interp_mkLamsAV_bits body ds (cons a σ) fun d' hd' => h d' (List.mem_cons_of_mem _ hd')

/-- **A λ-tower over the moved telescope at the ih frame is the tower
over the telescope at the field's own frame** when the leaves agree
(`piTele_ihTeleAtGo`'s λ twin). -/
theorem lamTower_ihTeleAtGo {mm nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) {g₁ g₂ : (Nat → V) → V} :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      (∀ bs, SpineFit (consList as (consList (fs.take i) ρp)) (tl.map (·.2.2)) bs →
        g₁ (consList bs (consList as (consList ihs (consList fs (consList ms (cons M ρp))))))
          = g₂ (consList bs (consList as (consList (fs.take i) ρp)))) →
      lamTower mm (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
          (ihTeleAtGo nF o i l as.length tl) g₁
        = lamTower mm (consList as (consList (fs.take i) ρp)) tl g₂
  | [], as, hg => by
    show g₁ (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
      = g₂ (consList as (consList (fs.take i) ρp))
    exact hg [] trivial
  | d :: tl, as, hg => by
    show lamR mm (interp V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l as.length d.2.2))
        (fun a => lamTower mm (cons a (consList as (consList ihs (consList fs (consList ms (cons M ρp))))))
          (ihTeleAtGo nF o i l (as.length + 1) tl) g₁)
      = lamR mm (interp V (consList as (consList (fs.take i) ρp)) d.2.2)
        (fun a => lamTower mm (cons a (consList as (consList (fs.take i) ρp))) tl g₂)
    rw [interp_ihIdxAtM hms hfs hihs hi as d.2.2]
    refine lamR_congr fun a ha => ?_
    have key := lamTower_ihTeleAtGo (mm := mm) (g₁ := g₁) (g₂ := g₂) (M := M) (ρp := ρp) hms hfs hihs hi
      tl (as ++ [a]) ?_
    · rw [consList_append, consList_cons, consList_nil, consList_append, consList_cons, consList_nil,
        List.length_append, List.length_singleton] at key
      exact key
    · intro bs hbs
      rw [consList_append, consList_cons, consList_nil] at hbs
      have := hg (a :: bs) ⟨ha, hbs⟩
      rw [consList_cons, consList_cons] at this
      rw [consList_append, consList_cons, consList_nil, consList_append, consList_cons, consList_nil]
      exact this

/-! ## The readings' spine, assembled -/

/-- **A fitting spine of member `mm`'s recursor type, from the pieces**
(the converse of `spineFit_recData_inv`): the prefix's fit, a fitting
index spine and a major in the carrier's fibre. -/
theorem BlockReps.spineFit_recData_of {m : EnvModel V env} {d : BlockRepData V}
    (hreps : BlockReps m d) {ψ : Name → Nat} {elimL : Level} {Ls : List AnnotTerm}
    {nIdxs : List Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} (hR : BlockReadings m d ψ elimL Ls nIdxs pps ipss cds mots tgts)
    {mm : Nat} (hmm : mm < d.k) {ρ : Nat → V} {ps Msl msl is : List V} {t : V}
    (hpre : SpineFit ρ ((recPrefixAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts).map (·.2.2))
      (ps ++ Msl ++ msl))
    (hF : PrefixFrame m d ψ elimL ρ ps Msl msl) (his : SpineFit (consList ps ρ) (d.IdsM mm ψ) is)
    (ht : t ∈ˢ SetTheory.app (lfpTuple (d.w ψ) d.k (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ)) mm)
      (d.tup ψ mm is)) :
    SpineFit ρ ((mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm).map (·.2.2))
      (ps ++ Msl ++ msl ++ is ++ [t]) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps mm hmm
  have hpl := hreps.params_length (by omega) ψ
  have hρp : Sat V (d.params ψ).reverse (consList ps ρ) := d.satOfSpine hF.params
  rw [mutualRecDataAV_eq_prefix, List.map_append, List.map_append,
    show ps ++ Msl ++ msl ++ is ++ [t] = (ps ++ Msl ++ msl) ++ (is ++ [t]) from by
      simp only [List.append_assoc]]
  refine hpre.append (SpineFit.append ?_ ?_)
  · rw [rebit_map_dom, spineFit_liftDoms, consList_append, consList_append, ← consList_append Msl msl,
      show Ls.length + cds.length = (Msl ++ msl).length from by
        rw [List.length_append, hR.lsLen, hR.cdsLen, hF.mslLen, hF.minsLen],
      shiftE_consList, hR.ipsAt mm hmm]
    exact his
  · refine ⟨?_, trivial⟩
    show t ∈ˢ interp V (consList is (consList (ps ++ Msl ++ msl) ρ))
      (majorAVAtK (Ls.getD mm default) d.nP (nIdxs.getD mm 0) Ls.length cds.length)
    unfold majorAVAtK
    rw [hR.leafAt mm hmm, hR.nIdxAt mm hmm, hR.lsLen, hR.cdsLen, consList_append, consList_append,
      ← consList_append Msl msl, show d.nP + d.k + d.nCtors + d.nIdxAt mm
        = d.nP + ((Msl ++ msl).length + d.nIdxAt mm) from by
          rw [List.length_append, hF.mslLen, hF.minsLen]; omega,
      h.leaf_app hpl hρp his (Msl ++ msl)]
    exact ht

/-! ## The `Prop` regime: the minors are the point -/

/-- At a zero bit a frame's minor is the point (its type is a
`Prop`-regime Π-tower, or the truth value of its conclusion). -/
theorem BlockReps.minor_eq_pt {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {c : Nat} (hc : c < d.k) {j : Nat}
    {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {Msl msl' : List V} {o : Nat}
    (ho : Msl.length + msl'.length = o) (hMsl : Msl.length = d.k) {elimL : Level}
    (hℓ : elimL.eval ψ = 0)
    (hMs : ∀ c', c' < d.k → Msl.getD c' pt ∈ˢ interp V ρp
      (motiveAVIL (m.acval (d.memberName c') ψ) ψ d.nP (d.nIdxAt c') elimL ((d.ppsM c' ψ).drop d.nP)))
    {mJ : V}
    (hmJ : mJ ∈ˢ interp V (consList msl' (consList Msl ρp))
      (minorAVAtRM c (d.tgts c j) m cA.1.name ψ d.nP cA.2 0 o (d.dsF c j ψ) (d.esF c j ψ)
        (ConLeche.recIdxOf (d.ksF c j)) (d.tssF c j ψ) (d.eissF c j ψ))) :
    mJ = pt := by
  unfold minorAVAtRM at hmJ
  cases hds : (d.dsF c j ψ).drop d.nP with
  | cons d' ds' =>
    rw [hds] at hmJ
    exact eq_pt_of_mem_piR_zero hmJ
  | nil =>
    rw [hds] at hmJ
    simp only [liftDoms, rebit_nil, mkPisAV] at hmJ
    cases hr : ConLeche.recIdxOf (d.ksF c j) with
    | cons i' is' =>
      rw [hr] at hmJ
      exact eq_pt_of_mem_piR_zero hmJ
    | nil =>
      rw [hr] at hmJ
      simp only [ihPisAVM, List.length_nil] at hmJ
      rw [interp_liftN, shiftE_zero_zero] at hmJ
      have hfs : SpineFit ρp ((d.Fss c ψ).getD j []) [] := by
        rw [BlockRep.Fss_getD hj, hds]; trivial
      have hconc := hreps.minor_conc hfT hc hj hρp ho hMsl hMs hfs
      rw [consList_nil] at hconc
      rw [hconc.1] at hmJ
      rw [hℓ, univ_zero] at hconc
      exact eq_pt_of_mem_univZero hconc.2 hmJ

/-! ## The equation's sides, read positionally -/

/-- The tuple variable of member `t` at the rule's field frame reads to
the tuple frame's `t`-th component. -/
theorem interp_tupleVarAV_at {nP k n nF : Nat} {ρc : Nat → V} {ps Msl msl fs bs : List V}
    (hps : ps.length = nP) (hMsl : Msl.length = k) (hmsl : msl.length = n) (hfs : fs.length = nF)
    (t : Nat) :
    interp V (consList bs (consList fs (consList msl (consList Msl (consList ps ρc)))))
        (tupleVarAV k (nP + k + n + nF + bs.length) t) = ρc (k - 1 - t) := by
  unfold tupleVarAV
  rw [interp_bvar, show nP + k + n + nF + bs.length + (k - 1 - t)
      = (((((k - 1 - t) + ps.length) + Msl.length) + msl.length) + fs.length) + bs.length from by
        rw [hps, hMsl, hmsl, hfs]; omega,
    consList_apply_add, consList_apply_add, consList_apply_add, consList_apply_add, consList_apply_add]

/-- **The equation's left-hand side at the rule's frame**: the tuple's
component at the parameters, motives, minors, the result index
readings and the constructor at the parameters and fields. -/
theorem interp_specLhsAV_at {nP k n nF : Nat} {ρc : Nat → V} {ps Msl msl fs : List V}
    (hps : ps.length = nP) (hMsl : Msl.length = k) (hmsl : msl.length = n) (hfs : fs.length = nF)
    (c : Nat) (Es : List AnnotTerm) (C : AnnotTerm) :
    interp V (consList fs (consList msl (consList Msl (consList ps ρc))))
        (specLhsAV k nP n nF c Es C)
      = (ps ++ Msl ++ msl ++ Es.map (interp V (consList fs (consList ps ρc))) ++
          [interp V (consList fs (consList msl (consList Msl (consList ps ρc))))
            (AnnotTerm.mkAppN C (paramBvarsAt nP (nP + k + n + nF) ++ fieldBvars nF))]).foldl
          SetTheory.app (ρc (k - 1 - c)) := by
  unfold specLhsAV
  rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList fs (consList msl (consList Msl
    (consList ps ρc))))) (g := SetTheory.app), List.map_append, List.map_append]
  have hvar := interp_tupleVarAV_at (bs := []) (ρc := ρc) hps hMsl hmsl hfs c
  rw [List.length_nil, consList_nil, Nat.add_zero] at hvar
  rw [hvar]
  have hpre := map_recPrefixBvarsMK_interp (bs := []) (ρ' := ρc) hps hMsl hmsl hfs
  rw [List.length_nil, consList_nil] at hpre
  rw [hpre, map_liftN_interp (by omega) hfs, List.map_cons, List.map_nil]

/-- A λ-tower reads its binder data's domains only. -/
theorem lamTower_rebit {mm b : Nat} {g : (Nat → V) → V} :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (ρ : Nat → V), lamTower mm ρ (rebit b ds) g = lamTower mm ρ ds g
  | [], _ => rfl
  | d :: ds, ρ => by
    show lamR mm (interp V ρ d.2.2) (fun a => lamTower mm (cons a ρ) (rebit b ds) g)
      = lamR mm (interp V ρ d.2.2) (fun a => lamTower mm (cons a ρ) ds g)
    exact lamR_congr fun a _ => lamTower_rebit ds (cons a ρ)

/-- The ih application's body at the rule's field frame under the
telescope's values: the target's tuple component at the parameters,
motives, minors, the field's index readings and the field applied. -/
theorem interp_ihAppBody_at {nP k n nF i : Nat} {ρc : Nat → V} {ps Msl msl fs bs : List V}
    (hps : ps.length = nP) (hMsl : Msl.length = k) (hmsl : msl.length = n) (hfs : fs.length = nF)
    (hk : 0 < k) (hi : i < nF) (tgt : Nat) (Eis : List AnnotTerm) :
    interp V (consList bs (consList fs (consList msl (consList Msl (consList ps ρc)))))
        (AnnotTerm.mkAppN (tupleVarAV k (nP + k + n + nF + bs.length) tgt)
          (recPrefixBvarsMK nP k n nF bs.length ++
            Eis.map (ihIdxAtM nF (n + k) i 0 bs.length) ++
            [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)]))
      = (ps ++ Msl ++ msl ++ Eis.map (interp V (consList bs (consList (fs.take i) (consList ps ρc)))) ++
          [bs.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app (ρc (k - 1 - tgt)) := by
  rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList bs (consList fs (consList msl (consList Msl
    (consList ps ρc)))))) (g := SetTheory.app), List.map_append, List.map_append,
    interp_tupleVarAV_at hps hMsl hmsl hfs tgt, map_recPrefixBvarsMK_interp hps hMsl hmsl hfs]
  have hEis := map_ihIdxAtM_interp (ρp := consList ps ρc) (Msl := Msl) (msl := msl) (o := n + k)
    (l := 0) (by omega) (by rw [hMsl]; exact hk) hfs (ihs := []) rfl (Nat.le_of_lt hi) bs Eis
  rw [consList_nil] at hEis
  rw [hEis, List.map_cons, List.map_nil, interp_mkAppN, interp_bvar,
    ← List.foldl_map (f := interp V (consList bs (consList fs (consList msl (consList Msl
      (consList ps ρc)))))) (g := SetTheory.app) (l := teleVarsAV bs.length)]
  have hvars : (teleVarsAV bs.length).map
      (interp V (consList bs (consList fs (consList msl (consList Msl (consList ps ρc)))))) = bs :=
    map_fieldBvars_interp rfl _
  have hf : consList bs (consList fs (consList msl (consList Msl (consList ps ρc))))
      (nF - 1 - i + bs.length) = fs.getD i pt := by
    rw [consList_apply_add, consList_apply_lt' fs _ (by omega),
      show fs.length - 1 - (nF - 1 - i) = i from by omega]
  rw [hvars, hf]

/-- **An inductive-hypothesis application at the rule's frame** reads
to the λ-tower over the field's telescope (at the field's own frame)
of the target's tuple component at the parameters, motives, minors,
the field's index readings and the field applied to the telescope's
values. -/
theorem interp_ihAppAVK_at {nP k n nF i : Nat} {ρc : Nat → V} {ps Msl msl fs : List V}
    (hps : ps.length = nP) (hMsl : Msl.length = k) (hmsl : msl.length = n) (hfs : fs.length = nF)
    (hk : 0 < k) (hi : i < nF) {b : Nat} (tgt : Nat) (tl : List (Nat × Nat × AnnotTerm))
    (Eis : List AnnotTerm) :
    interp V (consList fs (consList msl (consList Msl (consList ps ρc))))
        (ihAppAVK (tupleVarAV k (nP + k + n + nF + tl.length) tgt) nP k n nF i (rebit b tl) Eis)
      = lamTower b (consList (fs.take i) (consList ps ρc)) tl fun σ'' =>
          (ps ++ Msl ++ msl ++ Eis.map (interp V σ'') ++
            [(ConLeche.Semantics.frameIdx tl.length σ'').foldl SetTheory.app (fs.getD i pt)]).foldl
            SetTheory.app (ρc (k - 1 - tgt)) := by
  obtain ⟨M0, Msl', rfl⟩ : ∃ M0 Msl', Msl = M0 :: Msl' := by
    cases Msl with
    | nil => exact absurd hk (by rw [← hMsl]; exact Nat.lt_irrefl _)
    | cons M0 Msl' => exact ⟨M0, Msl', rfl⟩
  have hms : (Msl' ++ msl).length + 1 = n + k := by
    rw [List.length_append, hmsl]; simp only [List.length_cons] at hMsl; omega
  unfold ihAppAVK
  rw [interp_mkLamsAV_bits (b := b) _ _ _ (fun d hd => by
    obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hd
    rw [he]; exact mem_rebit hd')]
  simp only [rebit_length]
  unfold ihTeleAtR
  rw [consList_motives_cons, ← lamTower_rebit (b := b) tl]
  have key := lamTower_ihTeleAtGo (mm := b) (M := M0) (ρp := consList ps ρc) hms hfs (ihs := [])
    (l := 0) rfl (Nat.le_of_lt hi) (rebit b tl) []
    (g₁ := fun σ'' => interp V σ''
      (AnnotTerm.mkAppN (tupleVarAV k (nP + k + n + nF + tl.length) tgt)
        (recPrefixBvarsMK nP k n nF tl.length ++
          Eis.map (ihIdxAtM nF (n + k) i 0 tl.length) ++
          [AnnotTerm.mkAppN (.bvar (nF - 1 - i + tl.length)) (teleVarsAV tl.length)])))
    (g₂ := fun σ'' => (ps ++ M0 :: Msl' ++ msl ++ Eis.map (interp V σ'') ++
      [(ConLeche.Semantics.frameIdx tl.length σ'').foldl SetTheory.app (fs.getD i pt)]).foldl
        SetTheory.app (ρc (k - 1 - tgt))) ?_
  · simp only [List.length_nil, consList_nil] at key
    exact key
  · intro bs hbs
    simp only [consList_nil]
    rw [rebit_map_dom] at hbs
    have hlenbs : bs.length = tl.length := by rw [hbs.length_eq, List.length_map]
    rw [← consList_motives_cons, ← hlenbs, interp_ihAppBody_at hps hMsl hmsl hfs hk hi tgt Eis,
      frameIdx_consList']

/-! ## `hceq` -/

/-- **The rules' equations hold at the candidate** (`blockRecs`'s
`hceq`, per rule): at the tuple of the candidates, rule `(c, j)`'s
equation holds — at every fitting spine of its binder data the
left-hand side (member `c`'s candidate at the frame, the result index
readings and the constructor's injection) and the right-hand side
(the minor at the fields and the inductive hypotheses' applications)
read to the same value: at `ℓ ≠ 0` both are the union recursor's
step at the decomposed value; at `ℓ = 0` both are the point. -/
theorem BlockReps.blockCand_eq {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {elimL : Level}
    (hwℓ : d.w ψ = 0 → elimL.eval ψ = 0) {Ls : List AnnotTerm} {nIdxs : List Nat}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    (hR : BlockReadings m d ψ elimL Ls nIdxs pps ipss cds mots tgts) (ρ : Nat → V) {c : Nat}
    (hc : c < d.k) {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) :
    (pt : V) ∈ˢ interp V
        (consList ((List.range d.k).map fun mm =>
          d.blockCand ψ (elimL.eval ψ)
            (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm) mm ρ) ρ)
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
  -- the tuple frame
  generalize hcands : ((List.range d.k).map fun mm =>
    d.blockCand ψ (elimL.eval ψ) (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm)
      mm ρ) = cands
  have hcandsLen : cands.length = d.k := by rw [← hcands, List.length_map, List.length_range]
  have hcandsD : ∀ t, t < d.k → cands.getD t pt
      = d.blockCand ψ (elimL.eval ψ)
          (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts t) t ρ := by
    intro t ht
    rw [← hcands, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]; rfl
  have hρcD : ∀ t, t < d.k → consList cands ρ (d.k - 1 - t) = cands.getD t pt := by
    intro t ht
    rw [consList_apply_lt' _ _ (by omega), hcandsLen, show d.k - 1 - (d.k - 1 - t) = t from by omega]
  rw [pt_mem_specEqAV_iff]
  intro xs hxs
  rw [mutualRuleDataAV_eq_prefix, List.map_append] at hxs
  obtain ⟨xs₁, fs, rfl, hpre, hfsL⟩ := spineFit_append_inv hxs
  -- the prefix, at the base frame
  have hbelowPre : DomsBelow 0 (recPrefixAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts) := by
    have := hR.below c hc
    rw [mutualRecDataAV_eq_prefix] at this
    exact DomsBelow.append_left this
  have hpreρ := spineFit_transport₀ hbelowPre (ρ₂ := ρ) hpre
  obtain ⟨ps, Msl, msl, rfl, hF⟩ := spineFit_prefix_inv hR hpreρ
  have hlenps : ps.length = d.nP := by rw [hF.params.length_eq, hpl]
  have hρp : Sat V (d.params ψ).reverse (consList ps ρ) := d.satOfSpine hF.params
  have hlenfs : fs.length = cA.2 := by
    rw [hfsL.length_eq, List.length_map, rebit_length, liftDoms_length, List.length_drop, hcd.len]
    omega
  have hlenMm : Ls.length + cds.length = (Msl ++ msl).length := by
    rw [List.length_append, hR.lsLen, hR.cdsLen, hF.mslLen, hF.minsLen]
  -- the fields, at both parameter frames
  have hfs' : SpineFit (consList ps (consList cands ρ)) ((d.Fss c ψ).getD j []) fs := by
    rw [rebit_map_dom, spineFit_liftDoms, consList_append, consList_append, ← consList_append Msl msl,
      hlenMm, shiftE_consList] at hfsL
    rw [BlockRep.Fss_getD hj]; exact hfsL
  have hfs : SpineFit (consList ps ρ) ((d.Fss c ψ).getD j []) fs := by
    rw [BlockRep.Fss_getD hj] at hfs' ⊢
    exact spineFit_transport (DomsBelow.drop d.nP (hcd.below ψ)) (by rw [hlenps, Nat.zero_add]) hfs'
  have hEsρ : (d.esF c j ψ).map (interp V (consList fs (consList ps (consList cands ρ))))
      = (d.esF c j ψ).map (interp V (consList fs (consList ps ρ))) := by
    apply List.map_congr_left
    intro E hE
    rw [← consList_append ps fs (consList cands ρ), ← consList_append ps fs ρ]
    exact interp_closed_bottom (hcd.belowE ψ E hE) (by rw [List.length_append, hlenps, hlenfs]) _ _
  have hfr : consList (ps ++ Msl ++ msl ++ fs) (consList cands ρ)
      = consList fs (consList msl (consList Msl (consList ps (consList cands ρ)))) := by
    simp only [consList_append]
  rw [hfr]
  -- the frame's data functions
  have hMseq : ∀ c', c' < d.k →
      (fun c' => if c' < d.k then Msl.getD c' pt else pt) c' = Msl.getD c' pt :=
    fun c' hc' => if_pos hc'
  have hMs : ∀ c', c' < d.k → (fun c' => if c' < d.k then Msl.getD c' pt else pt) c' ∈ˢ
      interp V (consList ps ρ) (motiveAVIL (m.acval (d.memberName c') ψ) ψ d.nP (d.nIdxAt c') elimL
        ((d.ppsM c' ψ).drop d.nP)) := fun c' hc' => by
    rw [hMseq c' hc']; exact hF.motives c' hc'
  have hms : ∀ c' j' cA', c' < d.k → (d.ctorsM c')[j']? = some cA' →
      (fun J => if J < d.nCtors then msl.getD J pt else pt) (d.minorIdx c' j')
        ∈ˢ interp V (consList (msl.take (d.minorIdx c' j')) (consList Msl (consList ps ρ)))
          (minorAVAtRM c' (d.tgts c' j') m cA'.1.name ψ d.nP cA'.2 (pwBit ψ (Level.zeronessOf elimL))
            (d.k + d.minorIdx c' j') (d.dsF c' j' ψ) (d.esF c' j' ψ) (ConLeche.recIdxOf (d.ksF c' j'))
            (d.tssF c' j' ψ) (d.eissF c' j' ψ)) := fun c' j' cA' hc' hj' => by
    show (if d.minorIdx c' j' < d.nCtors then msl.getD (d.minorIdx c' j') pt else pt) ∈ˢ _
    rw [if_pos (d.minorIdx_lt hc' (List.getElem?_eq_some_iff.mp hj').1)]
    exact hF.minors c' j' cA' hc' hj'
  -- the left-hand side
  rw [interp_specLhsAV_at hlenps hF.mslLen hF.minsLen hlenfs, hρcD c hc, hcandsD c hc, hEsρ]
  have hC : interp V (consList fs (consList msl (consList Msl (consList ps (consList cands ρ)))))
      (AnnotTerm.mkAppN (m.acval cA.1.name ψ)
        (paramBvarsAt d.nP (d.nP + d.k + d.nCtors + cA.2) ++ fieldBvars cA.2)) = d.inj ψ c j fs := by
    rw [show consList fs (consList msl (consList Msl (consList ps (consList cands ρ))))
        = consList fs (consList (Msl ++ msl) (consList ps (consList cands ρ))) from by
          rw [consList_append],
      show d.nP + d.k + d.nCtors + cA.2 = d.nP + ((Msl ++ msl).length + cA.2) from by
        rw [List.length_append, hF.mslLen, hF.minsLen]; omega,
      interp_formerApp hlenfs _ (m.cval_closedL _ ψ), ← hlenps, range_reverse_map_consList ps]
    have hρ₀ : (fun i => consList ps (consList cands ρ) (i + ps.length)) = consList cands ρ := by
      funext i; rw [consList_apply_add]
    rw [hρ₀]
    have hbP : DomsBelow 0 (rebit (pwBit ψ (Level.zeronessOf elimL)) pps) :=
      DomsBelow.append_left (DomsBelow.append_left hbelowPre)
    have hpsC : SpineFit (consList cands ρ) (d.params ψ) ps := by
      have := spineFit_transport₀ hbP (ρ₁ := ρ) (ρ₂ := consList cands ρ)
        (by rw [rebit_map_dom, hR.ppsDom]; exact hF.params)
      rw [rebit_map_dom, hR.ppsDom] at this
      exact this
    exact h.ctor c j cA hc hj ψ _ ps fs hpsC hfs'
  rw [hC]
  -- the right-hand side
  unfold specRuleCoreAV
  rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList fs (consList msl (consList Msl
    (consList ps (consList cands ρ)))))) (g := SetTheory.app), List.map_append, interp_bvar,
    show cA.2 + d.nCtors - 1 - d.minorIdx c j = (d.nCtors - 1 - d.minorIdx c j) + fs.length from by
      rw [hlenfs]; omega,
    consList_apply_add, consList_apply_lt' _ _ (by rw [hF.minsLen]; omega), hF.minsLen,
    show d.nCtors - 1 - (d.nCtors - 1 - d.minorIdx c j) = d.minorIdx c j from by omega,
    show fieldBvars cA.2 = (List.range cA.2).map (fun k => AnnotTerm.bvar (cA.2 - 1 - k)) from rfl,
    map_fieldBvars_interp hlenfs, List.map_map]
  rcases Classical.em (elimL.eval ψ = 0) with hℓ0 | hℓ
  · -- the `Prop` regime: both sides are the point
    have hne : mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts c ≠ [] := by
      intro hnil
      have := congrArg List.length hnil
      rw [mutualRecDataAV_length (by rw [← List.length_map, hR.ppsDom]; exact hpl)] at this
      simp at this
    have hpt : d.blockCand ψ (elimL.eval ψ)
        (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts c) c ρ = pt := by
      unfold BlockRepData.blockCand
      cases hd : mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts c with
      | nil => exact absurd hd hne
      | cons d' ds' =>
        show lamR (elimL.eval ψ) _ _ = pt
        rw [hℓ0]; exact lamR_zero
    have hmpt : msl.getD (d.minorIdx c j) pt = pt := by
      have hmin := hF.minors c j cA hc hj
      rw [hb.mpr hℓ0] at hmin
      exact hreps.minor_eq_pt hfT hc hj hρp (Msl := Msl) (msl' := msl.take (d.minorIdx c j))
        (o := d.k + d.minorIdx c j)
        (by rw [hF.mslLen, List.length_take, hF.minsLen]; congr 1; exact Nat.min_eq_left (Nat.le_of_lt hJ))
        hF.mslLen hℓ0 hF.motives hmin
    rw [hpt, hmpt, foldl_app_pt, foldl_app_pt]
  · have hw : d.w ψ ≠ 0 := fun hw0 => hℓ (hwℓ hw0)
    have hk : 0 < d.k := by omega
    -- the left-hand side is the union recursor at the frame
    have hEs : SpineFit (consList ps ρ) (d.IdsM c ψ)
        ((d.esF c j ψ).map (interp V (consList fs (consList ps ρ)))) :=
      hreps.res_es_fit hfT hc hj hρp hfs
    have hinj := hreps.inj_mem hfT hc hj hρp hfs
    have hsp₁ := hreps.spineFit_recData_of hR hc hpreρ hF hEs hinj
    have hlenEs : ((d.esF c j ψ).map (interp V (consList fs (consList ps ρ)))).length = d.nIdxAt c := by
      rw [List.length_map, hcd.lenE]
    unfold BlockRepData.blockCand
    rw [lamTower_fold hℓ hsp₁, d.blockLeafV_at ψ (elimL.eval ψ) c ρ _ hF.mslLen hF.minsLen hlenEs,
      hreps.blockRecAt_eq hfT hρp hw hF.mslLen hMseq hMs hb hF.minsLen
        (ms := fun J => if J < d.nCtors then msl.getD J pt else pt) hms hc
        (i := d.tup ψ c ((d.esF c j ψ).map (interp V (consList fs (consList ps ρ))))) (tupW_mem hEs) hinj]
    -- the decode is the decomposition
    have hdec : d.Decodes ψ c (d.inj ψ c j fs) := ⟨j, fs, hj', hfs.length_eq, rfl⟩
    obtain ⟨j', fs', hj'', hlen', hx', heq⟩ := d.kitSt_tagged ψ (consList ps ρ) (elimL.eval ψ) _ _ hdec
    rw [heq]
    obtain ⟨rfl, rfl⟩ := h.mkInj ψ hw c hc j fs j' fs' hj' hj'' hfs.length_eq hlen' hx'
    show (fs ++ d.kitIhs ψ (consList ps ρ) (elimL.eval ψ) c j fs _).foldl SetTheory.app
      (if d.minorIdx c j < d.nCtors then msl.getD (d.minorIdx c j) pt else pt) = _
    rw [if_pos hJ, List.foldl_append, List.foldl_append]
    congr 1
    -- the inductive hypotheses' values
    unfold BlockRepData.kitIhs
    rw [h.recIdx_eq hj]
    apply List.map_congr_left
    intro i hiI
    have hiK : i < (d.ksF c j).length := (mem_recIdxOf.mp hiI).1
    have hiA : i < cA.2 := by rw [← hcd.ksLen]; exact hiK
    have hr : (rsOf (d.ksF c j)).getD i false = true := by
      rw [rsOf_getD hiK, decide_eq_true_iff]; exact (mem_recIdxOf.mp hiI).2
    have hiR : i ∈ recIdx ((d.rss c).getD j []) ((d.Fss c ψ).getD j []).length := by
      rw [h.recIdx_eq hj]; exact hiI
    have htgt : d.tgts c j i < d.k := h.tgtsLt c j i hc hj' hiK
    obtain ⟨cvT', cvR', mI', rP', rules', ht⟩ := hreps _ htgt
    have hfsI := spineFit_take' hfs (i := i) (by rw [h.Fss_length hj]; exact Nat.le_of_lt hiA)
    have hlenI : (fs.take i).length = i := by
      rw [List.length_take, hlenfs]; exact Nat.min_eq_left (Nat.le_of_lt hiA)
    have hfitL := hreps.fitsFrom_of_spineFit_go hfT hc hj hρp _ 0 [] fs rfl trivial
      (by rw [consList_nil]; exact hfs)
    rw [consList_nil] at hfitL
    -- the ih application, read and moved to the base frame
    simp only [Function.comp]
    rw [interp_ihAppAVK_at hlenps hF.mslLen hF.minsLen hlenfs hk hiA, hρcD _ htgt, hcandsD _ htgt,
      lamTower_bit_agree hb, BlockRepData.teleAt, BlockRep.tlss_getD hj, BlockRepData.eisAt,
      BlockRep.Eiss_getD hj]
    symm
    rw [show consList (fs.take i) (consList ps (consList cands ρ))
        = consList (ps ++ fs.take i) (consList cands ρ) from by rw [consList_append],
      show consList (fs.take i) (consList ps ρ) = consList (ps ++ fs.take i) ρ from by
        rw [consList_append]]
    refine lamTower_congr_bottom (fun k' d' hd' => ?_) fun bs hbs => ?_
    · rw [List.length_append, hlenps, hlenI]
      exact domsBelow_getElem? (hcd.tssBelow ψ i) hd'
    -- the leaves: the target's candidate at the frame, the union recursor at the predecessor
    have hlenbs : bs.length = ((d.tssF c j ψ).getD i []).length := by
      rw [hbs.length_eq, List.length_map]
    have hbsρ : SpineFit (consList (fs.take i) (consList ps ρ))
        (((d.tssF c j ψ).getD i []).map (·.2.2)) bs := by
      have := spineFit_transport (hcd.tssBelow ψ i) (as := ps ++ fs.take i)
        (by rw [List.length_append, hlenps, hlenI]) (ρ₁ := consList cands ρ) (ρ₂ := ρ) hbs
      rwa [consList_append] at this
    have hEisρ : ((d.eissF c j ψ).getD i []).map
        (interp V (consList (ps ++ fs.take i ++ bs) (consList cands ρ)))
        = ((d.eissF c j ψ).getD i []).map (interp V (consList (ps ++ fs.take i ++ bs) ρ)) := by
      apply List.map_congr_left
      intro E hE
      exact interp_closed_bottom (hcd.eissBelow ψ i E hE)
        (by rw [List.length_append, List.length_append, hlenps, hlenI, hlenbs]) _ _
    rw [hEisρ, consList_append (ps ++ fs.take i) bs (consList cands ρ),
      consList_append (ps ++ fs.take i) bs ρ, ← hlenbs, frameIdx_consList', frameIdx_consList',
      consList_append ps (fs.take i) ρ]
    have hEis : SpineFit (consList ps ρ) (d.IdsM (d.tgts c j i) ψ)
        (((d.eissF c j ψ).getD i []).map (interp V (consList bs (consList (fs.take i) (consList ps ρ))))) :=
      hreps.eis_fit hfT hc hj hρp hiA hr hfsI hbsρ
    have hlenEis : (((d.eissF c j ψ).getD i []).map
        (interp V (consList bs (consList (fs.take i) (consList ps ρ))))).length = d.nIdxAt (d.tgts c j i) := by
      rw [hEis.length_eq, ht.IdsM_length]
    have hv := hreps.kitPred_mem hc hj' hfitL hiR
      (bs := bs) (by rw [BlockRepData.teleAt, BlockRep.tlss_getD hj]; exact hbsρ)
      (d.tup ψ c ((d.esF c j ψ).map (interp V (consList fs (consList ps ρ)))))
    rw [BlockRepData.eisAt, BlockRep.Eiss_getD hj] at hv
    have hvU := relPred_subset _ _ _ _ hv
    have hfold : bs.foldl SetTheory.app (fs.getD i pt)
        ∈ˢ SetTheory.app (lfpTuple (d.w ψ) d.k (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ)) (d.tgts c j i))
          (d.tup ψ (d.tgts c j i)
            (((d.eissF c j ψ).getD i []).map (interp V (consList bs (consList (fs.take i) (consList ps ρ)))))) :=
      (tagged_mem_unionSet_iff.mp hvU).2.2
    have hsp₂ := hreps.spineFit_recData_of hR htgt hpreρ hF hEis hfold
    unfold BlockRepData.blockCand
    rw [lamTower_fold hℓ hsp₂, d.blockLeafV_at ψ (elimL.eval ψ) _ ρ _ hF.mslLen hF.minsLen hlenEis,
      app_graph hv]
    rfl

end ConLeche.Model
