module

public import ConLeche.Model.Inductives.MutualRecLeaf
import ConLeche.Model.Inductives.FixLeafOk
import ConLeche.Model.Inductives.FixIntro
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so `PropWhen.never.isNever` does not reduce.  `import all`
restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen
public section

/-!
# The member recursor leaf's typing (task #278, M2.3d)

Member `mm`'s recursor leaf `mutualRecAVI` is the λ-tower over its
STORED type's binder data (`mutualRecDataAV`) whose body applies the
AUXILIARY recursor to the parameters, the motive dispatch, the minors,
the tagged index tuple and the major.  Its typing is read off the
auxiliary leaf's (`auxRecLeafFacts`, taken here as the hypothesis
`haux`) through three transfers:

* the public motive `m'`'s domain reads member `m'`'s motive space
  (`interp_memberMotive`), so the dispatch's `MotDispHyp` holds at the
  leaf frame and `motDispAV_facts` applies;
* the public minor `J`'s domain and the auxiliary minor `J`'s domain
  read the SAME set — the dispatch's computation law turns
  `disp ⟨inj m' ı⃗⟩ x` into `M_{m'} ı⃗ x` at the conclusion and at every
  inductive hypothesis (`minor_spaces_eq`);
* the public major's domain and the tagged index binder read the
  auxiliary family's fibre at the tagged tuple (`mutualLeafApp`).

The λ-tower's laws are then `mkLamsC_mem`/`_wellDenoted`/`_validV`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Kit -/

/-- The domain walk from the Π-tower's own grading inversion. -/
theorem domsWalk_of_fieldsOkB :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      FieldsOkB 0 ρ (ds.map (·.2.2)) → DomsWalk ρ ds
  | [], _, _ => trivial
  | d :: ds, ρ, h => by
    rw [List.map_cons] at h
    exact ⟨h.1, fun a ha => domsWalk_of_fieldsOkB (h.2.2 a ha)⟩

omit [SetTheory V] in
/-- The frame BELOW `nP` consed parameter values is the base frame. -/
theorem paramFrame_shift {ps : List V} {ρ : Nat → V} {nP : Nat} (h : ps.length = nP) :
    (fun j => consList ps ρ (j + nP)) = ρ := by
  subst h
  funext j
  exact consList_apply_add ps ρ j

/-- The parameter VARIABLES' values at a consed parameter frame are the
parameter values themselves. -/
theorem paramVals_consList {ps : List V} {ρ : Nat → V} {nP : Nat} (h : ps.length = nP) :
    (List.range nP).reverse.map (consList ps ρ) = ps := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < ps.length := h2
  have hidx : ((List.range ps.length).reverse)[i]'(by simpa using h1) = ps.length - 1 - i := by
    rw [List.getElem_reverse]
    simp
  rw [List.getElem_map, hidx, consList_apply_lt' ps ρ (by omega),
    show ps.length - 1 - (ps.length - 1 - i) = i from by omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- **A fitting spine transfers** between two binder chains whose
entries read the same set at every prefix frame. -/
theorem spineFit_transfer :
    ∀ {Ds Ds' : List AnnotTerm} {vs : List V} {ρ ρ' : Nat → V},
      Ds.length = Ds'.length →
      (∀ (us : List V) (j : Nat), us.length = j → j < Ds.length →
        interp V (consList us ρ) (Ds.getD j default)
          = interp V (consList us ρ') (Ds'.getD j default)) →
      SpineFit ρ Ds vs → SpineFit ρ' Ds' vs
  | [], [], [], _, _, _, _, _ => trivial
  | [], [], _ :: _, _, _, _, _, hsp => hsp.elim
  | [], _ :: _, _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, _ :: _, [], _, _, _, _, hsp => hsp.elim
  | D :: Ds, D' :: Ds', a :: vs, ρ, ρ', hlen, h, hsp => by
    have h0 := h [] 0 rfl (by simp)
    simp only [consList_nil, List.getD_cons_zero] at h0
    refine ⟨by rw [← h0]; exact hsp.1, ?_⟩
    refine spineFit_transfer (by simpa using hlen) (fun us j hus hj => ?_) hsp.2
    have := h (a :: us) (j + 1) (by simp [hus]) (by simpa using hj)
    rw [consList_cons, List.getD_cons_succ, List.getD_cons_succ] at this
    exact this

/-- Minor spaces over one chain agree when their conclusions agree at
fitting field spines. -/
theorem minorSpI_congr_body {ℓ : Nat} {c c' : List V → V} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V} {acc : List V},
      (∀ as : List V, SpineFit ρ Fs as → c (acc ++ as) = c' (acc ++ as)) →
      minorSpI ℓ c Fs ρ acc = minorSpI ℓ c' Fs ρ acc
  | [], ρ, acc, h => by
    have := h [] trivial
    simpa [minorSpI] using this
  | F :: Fs, ρ, acc, h => by
    simp only [minorSpI]
    refine piR_congr fun a ha => ?_
    refine minorSpI_congr_body fun as hsp => ?_
    have := h (a :: as) ⟨ha, hsp⟩
    rwa [List.append_cons] at this

/-- Nested products over one telescope agree when their bodies agree at
fitting tuples (the same bit). -/
theorem piTele_congr_body {v : Nat} {B B' : List V → V} :
    ∀ {n : Nat} {T : TeleS V n} {acc : List V},
      (∀ as, FitsS T as → B (acc ++ as) = B' (acc ++ as)) →
      piTele v T B acc = piTele v T B' acc
  | _, .nil, acc, h => by
    have := h [] trivial
    simpa [piTele] using this
  | _, .cons A T, acc, h => by
    simp only [piTele]
    refine piR_congr fun a ha => ?_
    refine piTele_congr_body fun as hfit => ?_
    have := h (a :: as) ⟨ha, hfit⟩
    rwa [List.append_cons] at this

/-! ## The member leaf, applied -/

section Leaf

variable {W w nP nIdx t : Nat} {pps ips : List (Nat × Nat × AnnotTerm)}
  {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
  {Fss₀ Ess' : List (List AnnotTerm)} {L : AnnotTerm} {Ids : List AnnotTerm} {ρp : Nat → V}

/-- **Member `t`'s leaf at the parameter variables and index
expressions** reads, under `as` values at the parameter frame `ρp`, to
the auxiliary family's fibre at the tagged tuple of the expressions'
values (`fixLeafApp`'s shape at the mutual leaf). -/
theorem mutualLeafApp (hlenP : pps.length = nP)
    (hipd : ips.map (·.2.2) = Ids) (hlenIds : Ids.length = nIdx)
    (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hT : TagOk W ρp Idss)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess')
    (hIds : Idss[t]? = some Ids)
    (hleafM : ∀ σ : Nat → V, interp V σ L
      = interp V (fun j => ρp (j + nP))
          (mutualTyAVI W w (pps ++ ips) nIdx Idss rss tlss Eiss' Fss₀ Ess' t))
    {as : List V} {Eis : List AnnotTerm}
    (hsp : SpineFit ρp Ids (Eis.map (interp V (consList as ρp)))) :
    interp V (consList as ρp) (AnnotTerm.mkAppN L (paramBvarsAt nP (nP + as.length) ++ Eis))
      = auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess'
          (inj t (mkTower (Eis.map (interp V (consList as ρp)) ++ [pt]))) := by
  have hlenP' : ((pps.map (·.2.2))).length = nP := by rw [List.length_map, hlenP]
  have hlenIs : (Eis.map (interp V (consList as ρp))).length = nIdx := by
    rw [hsp.length_eq, hlenIds]
  have hps : (paramBvarsAt nP (nP + as.length)).map (interp V (consList as ρp))
      = (List.range nP).reverse.map ρp :=
    map_paramBvarsAt_interp fun j => consList_apply_add as ρp j
  rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList as ρp)) (g := SetTheory.app),
    List.map_append, hps, hleafM]
  have hspP := spineFit_of_sat (Δ₀ := []) (Ds := pps.map (·.2.2))
    (by rw [List.append_nil]; exact hsatP)
  rw [hlenP'] at hspP
  have hρ0 : consList ((List.range nP).reverse.map ρp) (fun j => ρp (j + nP)) = ρp :=
    consList_range_reverse nP ρp
  have hspAll : SpineFit (fun j => ρp (j + nP)) ((pps ++ ips).map (·.2.2))
      ((List.range nP).reverse.map ρp ++ Eis.map (interp V (consList as ρp))) := by
    rw [List.map_append]
    refine hspP.append ?_
    rw [hρ0, hipd]
    exact hsp
  have hframe : consList ((List.range nP).reverse.map ρp ++ Eis.map (interp V (consList as ρp)))
      (fun j => ρp (j + nP)) = consList (Eis.map (interp V (consList as ρp))) ρp := by
    rw [consList_append, hρ0]
  have hsh : shiftE nIdx 0 (consList (Eis.map (interp V (consList as ρp))) ρp) = ρp := by
    rw [← hlenIs]; exact shiftE_consList _ ρp
  have hfrIdx : ConLeche.Semantics.frameIdx nIdx
      (consList (Eis.map (interp V (consList as ρp))) ρp)
      = Eis.map (interp V (consList as ρp)) := frameIdx_consList hlenIs ρp
  have hbase : MutualBaseI W w
      (consList ((List.range nP).reverse.map ρp ++ Eis.map (interp V (consList as ρp)))
        (fun j => ρp (j + nP))) nIdx Idss rss tlss Eiss' Fss₀ Ess' t := by
    rw [hframe]
    refine ⟨by rw [hsh]; exact hT, by rw [hsh]; exact hok, Ids, hIds, hlenIds, ?_⟩
    rw [hsh, hfrIdx]
    exact hsp
  rw [mutualTyAVI_fold hspAll hbase, hframe, hsh, hfrIdx]
  rfl

/-- **The major's domain at a `k`-motive K-frame** reads to the
auxiliary family's fibre at member `mm`'s tagged index tuple. -/
theorem interp_majorAVAtK {k n : Nat} {Ms Ss : List V} (hlenP : pps.length = nP)
    (hipd : ips.map (·.2.2) = Ids) (hlenIds : Ids.length = nIdx)
    (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hT : TagOk W ρp Idss)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess')
    (hIds : Idss[t]? = some Ids)
    (hleafM : ∀ σ : Nat → V, interp V σ L
      = interp V (fun j => ρp (j + nP))
          (mutualTyAVI W w (pps ++ ips) nIdx Idss rss tlss Eiss' Fss₀ Ess' t))
    (hlenMs : Ms.length = k) (hlenSs : Ss.length = n)
    {is : List V} (hfit : SpineFit ρp Ids is) :
    interp V (consList is (consList Ss (consList Ms ρp))) (majorAVAtK L nP nIdx k n)
      = auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess' (inj t (mkTower (is ++ [pt]))) := by
  have hlenIs : is.length = nIdx := by rw [hfit.length_eq, hlenIds]
  have hfr : consList (Ms ++ Ss ++ is) ρp = consList is (consList Ss (consList Ms ρp)) := by
    rw [consList_append, consList_append]
  have hfb : (fieldBvars nIdx).map (interp V (consList (Ms ++ Ss ++ is) ρp)) = is := by
    rw [hfr]
    exact map_fieldBvars_interp hlenIs _
  have h := mutualLeafApp (as := Ms ++ Ss ++ is) (Eis := fieldBvars nIdx) hlenP hipd hlenIds
    hsatP hT hok hIds hleafM (by rw [hfb]; exact hfit)
  rw [hfb, hfr, show nP + (Ms ++ Ss ++ is).length = nP + k + n + nIdx from by
    simp [hlenMs, hlenSs, hlenIs]; omega] at h
  exact h

/-- **Member `t`'s motive domain reads member `t`'s motive space.** -/
theorem interp_memberMotive {ψ : Name → Nat} {elimL : Level} {ℓ : Nat}
    (hℓ : elimL.eval ψ = ℓ) (hlenP : pps.length = nP)
    (hipd : ips.map (·.2.2) = Ids) (hlenIds : Ids.length = nIdx)
    (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hT : TagOk W ρp Idss)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess')
    (hIds : Idss[t]? = some Ids)
    (hleafM : ∀ σ : Nat → V, interp V σ L
      = interp V (fun j => ρp (j + nP))
          (mutualTyAVI W w (pps ++ ips) nIdx Idss rss tlss Eiss' Fss₀ Ess' t)) :
    interp V ρp (motiveAVIL L ψ nP nIdx elimL ips)
      = memberMotSp ℓ W w ρp Idss rss tlss Eiss' Fss₀ Ess' t := by
  have hm : t < Idss.length := (List.getElem?_eq_some_iff.mp hIds).1
  have hg : Idss.getD t [] = Ids := by rw [List.getD_eq_getElem?_getD, hIds]; rfl
  rw [memberMotSp_eq hT hm, hg]
  unfold motiveAVIL
  rw [interp_mkPisAV_piTele (v := ℓ + 1) (gds := rebit (pwBit ψ PropWhen.never) ips)
    (fun d hd => by
      rw [mem_rebit hd]
      exact ⟨fun h => absurd h (pwBit_ne_zero_of_isNever rfl ψ),
        fun h => absurd h (Nat.succ_ne_zero _)⟩)
    (B := fun is' => piR (ℓ + 1)
      (auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess' (inj t (mkTower (is' ++ [pt]))))
      fun _ => (univ ℓ : V)) (acc := []) ?_, rebit_map_dom, hipd]
  intro as hsp
  rw [rebit_map_dom, hipd] at hsp
  have hlenAs : as.length = nIdx := by rw [hsp.length_eq, hlenIds]
  rw [interp_pi, hℓ, List.nil_append]
  have hfb : (fieldBvars nIdx).map (interp V (consList as ρp)) = as :=
    map_fieldBvars_interp hlenAs _
  have h := mutualLeafApp (as := as) (Eis := fieldBvars nIdx) hlenP hipd hlenIds hsatP hT hok hIds
    hleafM (by rw [hfb]; exact hsp)
  rw [hfb, hlenAs] at h
  rw [h, piR_congr_bit (v' := ℓ + 1)
    ⟨fun h0 => absurd h0 (pwBit_ne_zero_of_isNever rfl ψ), fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩]
  rfl

end Leaf

/-! ## The dispatch's bit validity

`motDispAV_facts` gives the dispatch's value law, its membership and
its grading; `WellDenotedV` also asks for bit validity, and the pieces
are the sum route's own `*_validV` lemmas along the dispatch's
spelling. -/

/-- A λ-tower's body is valid at every fitting spine (`mkLamsC_validV`,
inverted). -/
theorem mkLamsC_validV_inv {mb : Nat} {b : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {as : List V},
      AnnotValid V ρ (mkLamsC mb ds b) → SpineFit ρ (ds.map (·.2.2)) as →
      AnnotValid V (consList as ρ) b
  | [], _, [], h, _ => h
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | d :: ds, ρ, a :: as, h, hsp => by
    have h' : AnnotValid V ρ (.lam mb d.2.2 (mkLamsC mb ds b)) := h
    rw [AnnotValid_lam] at h'
    rw [consList_cons]
    exact mkLamsC_validV_inv (h'.2 a hsp.1) hsp.2

section DispValid

variable {ℓ W w k : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)} {Mv : V} {ms : List V}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss' : List (List (List AnnotTerm))} {Fss₀ Ess' : List (List AnnotTerm)}

/-- The tag type is bit-valid. -/
theorem tagTyAV_validV (hv : SumFieldsValid ρp Idss) :
    AnnotValid V ρp (tagTyAV W Idss) := by
  unfold tagTyAV
  exact sumBodyAV_validV (uChains_validV hv)

/-- The auxiliary family's index telescope is bit-valid. -/
theorem auxIds_validV (hv : SumFieldsValid ρp Idss) :
    FieldsValid ρp (auxIds W Idss) :=
  ⟨tagTyAV_validV hv, fun _ _ => trivial⟩

/-- A constructor branch with NO inductive hypotheses is bit-valid. -/
theorem caseBaseNoIh_validV {ℓ' w' n nIdx D j : Nat} {Fss' : List (List AnnotTerm)}
    {ar : Nat → Nat} {ρ₀ σ : Nat → V} (hfr : RecFrameS D ρ₀ σ)
    (hvF : SumFieldsValid ρ₀ Fss') :
    AnnotValid V σ (caseBaseAVI ℓ' w' Fss' ar (fun _ _ => []) n nIdx D j) := by
  show AnnotValid V σ (.lam ℓ' ((towerBodyAV w' (Fss'.getD j [])).liftN D 0) _)
  rw [AnnotValid_lam]
  refine ⟨?_, fun _ _ => ?_⟩
  · rw [AnnotValid_liftN, hfr]
    by_cases hj : j < Fss'.length
    · refine towerBodyAV_validV (hvF _ (List.mem_of_getElem? (i := j) ?_))
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact towerBodyAV_validV trivial
  · refine mkAppN_validV trivial fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
      exact projAV_validV trivial
    · exact (List.not_mem_nil ha).elim

/-- The tag block's restricted chains are bit-valid at the K-frame. -/
theorem tagRChains_validV (h : TagFrameHyp ℓ W w k ρp Idss Mv ms)
    (hv : SumFieldsValid ρp Idss) :
    SumFieldsValid (tagKFrame ρp Mv ms) (rChains (k + 1) 0 Idss (List.replicate k [])) := by
  have hE0 : ∀ j, (List.replicate k ([] : List AnnotTerm)).getD j [] = [] := by
    intro j
    by_cases hj : j < k
    · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hj]; rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
  have hsh : shiftE (k + 1) 0 (tagKFrame ρp Mv ms) = ρp := tagKFrame_shift h.hlen
  refine rChains_validV (d := k + 1) (nIdx := 0) (by rw [hsh]; exact hv)
    fun j _ bs _ E hE => ?_
  rw [hE0 j] at hE
  exact (List.not_mem_nil hE).elim

/-- **The dispatch's case recursor is bit-valid** at every frame below
the K-frame (`fixCaseRec_validV`'s shape at NO inductive hypotheses). -/
theorem dispCaseRec_validV (h : TagFrameHyp ℓ W w k ρp Idss Mv ms)
    (hv : SumFieldsValid ρp Idss) :
    ∀ (r : Nat) {D j : Nat} {σ : Nat → V} {kx : AnnotTerm},
      RecFrameS D (tagKFrame ρp Mv ms) σ → AnnotValid V σ kx →
      AnnotValid V σ
        (caseRecAVI (dispLevel w ℓ) W (rChains (k + 1) 0 Idss (List.replicate k []))
          (fun j => (Idss.getD j []).length) (fun _ _ => []) k 0 r D j kx)
  | 0, _, _, σ, _, _, _ => by
    show AnnotValid V σ (.lam (dispLevel w ℓ) (.const .empty [W]) .prf)
    rw [AnnotValid_lam]
    exact ⟨trivial, fun _ _ => trivial⟩
  | r + 1, D, j, σ, kx, hfr, hk => by
    have hyp := (tagRecHyp h).toRecHypCore
    have hvR := tagRChains_validV h hv
    have hvR' : SumFieldsValid (tagKFrame ρp Mv ms)
        (rChains (([] : List AnnotTerm).length + Idss.length + 1) ([] : List AnnotTerm).length
          Idss (List.replicate k [])) := by
      simp only [List.length_nil, Nat.zero_add]; rw [h.hk]; exact hvR
    have hmot := motive_validV (D := D) (ρ₀ := tagKFrame ρp Mv ms) (σ := σ) hfr hyp hvR' j
    have hmb := fun (b : V) =>
      motiveBody_validV (D := D) (ρ₀ := tagKFrame ρp Mv ms) (σ := σ) hfr hyp hvR' j b
    simp only [List.length_nil, Nat.zero_add] at hmot hmb
    rw [h.hk] at hmot hmb
    refine natRecAV_validV hmot (caseBaseNoIh_validV hfr hvR) ?_ hk
    rw [AnnotValid_lam]
    refine ⟨trivial, fun b _ => ?_⟩
    rw [AnnotValid_lam]
    refine ⟨hmb b, fun a _ => ?_⟩
    exact dispCaseRec_validV h hv r (hfr.step a b) (kx := .bvar 1) trivial

/-- **The dispatch's body is bit-valid.** -/
theorem dispBodyAV_validV (h : TagFrameHyp ℓ W w k ρp Idss Mv ms)
    (hv : SumFieldsValid ρp Idss) (i : V) :
    AnnotValid V (cons i (tagKFrame ρp Mv ms)) (dispBodyAV ℓ W w k Idss) := by
  have hfr : RecFrameS 1 (tagKFrame ρp Mv ms) (cons i (tagKFrame ρp Mv ms)) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  unfold dispBodyAV
  rw [AnnotValid_app, AnnotValid_snd]
  exact ⟨dispCaseRec_validV h hv k hfr trivial, trivial⟩

/-- **The dispatch's residual is bit-valid.** -/
theorem dispLamAV_validV (h : TagFrameHyp ℓ W w k ρp Idss Mv ms)
    (hv : SumFieldsValid ρp Idss) :
    AnnotValid V (tagKFrame ρp Mv ms) (dispLamAV ℓ W w k Idss) := by
  unfold dispLamAV
  rw [AnnotValid_lam]
  refine ⟨?_, fun i _ => dispBodyAV_validV h hv i⟩
  rw [AnnotValid_liftN, tagKFrame_shift h.hlen]
  exact tagTyAV_validV hv

/-- The tag motive's type is bit-valid. -/
theorem tagMotTyAV_validV (hv : SumFieldsValid ρp Idss) :
    AnnotValid V ρp (tagMotTyAV ℓ W w Idss) := by
  unfold tagMotTyAV
  rw [AnnotValid_pi]
  exact ⟨tagTyAV_validV hv, fun _ _ => trivial, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩

/-- Tag minor `m'`'s type is bit-valid at its K-frame position. -/
theorem tagMinorTyAV_validV (hv : SumFieldsValid ρp Idss) {m' : Nat}
    {Ids : List AnnotTerm} (hIds : Idss[m']? = some Ids) {τ : Nat → V}
    (hfr : shiftE (1 + m') 0 τ = ρp) :
    AnnotValid V τ (tagMinorTyAV ℓ W w m' Idss) := by
  have hg : Idss.getD m' [] = Ids := by rw [List.getD_eq_getElem?_getD, hIds]; rfl
  unfold tagMinorTyAV
  simp only [hg]
  have hdoms : ((liftFields (1 + m') 0 Ids).map fun F => (W, dispLevel w ℓ, F)).map (·.2.2)
      = liftFields (1 + m') 0 Ids := by simp [Function.comp_def]
  refine AnnotValid_mkPisAV_of (w := dispLevel w ℓ)
    (fun d hd => by obtain ⟨F, -, rfl⟩ := List.mem_map.mp hd; exact Iff.rfl) ?_ ?_
    (fun h0 => absurd h0 (dispLevel_ne_zero w ℓ))
  · rw [hdoms, FieldsValid_liftFields, hfr]
    exact hv Ids (List.mem_of_getElem? hIds)
  · intro as hsp
    rw [hdoms] at hsp
    have hlen : as.length = Ids.length := by rw [hsp.length_eq, liftFields_length]
    have hfr' : shiftE (1 + m' + Ids.length) 0 (consList as τ) = ρp := by
      rw [show 1 + m' + Ids.length = as.length + (1 + m') by omega, shiftE_consList_add, hfr]
    rw [AnnotValid_app]
    refine ⟨trivial, tagTupleAV_validV hv hIds hfr' fun E hE => ?_⟩
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hE
    trivial

/-- The dispatch tower's validity premise along the minors. -/
theorem dispTower_underValid_go (hT : TagOk W ρp Idss) (hMv : Mv ∈ˢ tagMotSp ℓ W w ρp Idss)
    (hk : Idss.length = k) (hv : SumFieldsValid ρp Idss) :
    ∀ (r m' : Nat) (ms' : List V), m' + r = k → ms'.length = m' →
      (∀ j, j < m' → ms'.getD j pt ∈ˢ tagMinorSp ℓ w ρp Idss Mv j) →
      UnderTowerValid (consList ms' (cons Mv ρp)) (dispLamAV ℓ W w k Idss)
        ((List.range' m' r).map fun j => (W, dispLevel w ℓ, tagMinorTyAV ℓ W w j Idss))
  | 0, m', ms', hr, hlen, hms => by
    rw [List.range'_zero, List.map_nil]
    exact dispLamAV_validV ⟨hT, hMv, hk, by omega, fun j hj => hms j (by omega)⟩ hv
  | r + 1, m', ms', hr, hlen, hms => by
    rw [List.range'_succ, List.map_cons]
    obtain ⟨Ids, hIds⟩ : ∃ Ids, Idss[m']? = some Ids :=
      ⟨_, List.getElem?_eq_getElem (by rw [hk]; omega)⟩
    have hty := tagMinorTyAV_facts hT hMv (m' := m') (by rw [hk]; omega)
      (minorFrame_shift hlen) (minorFrame_motive hlen)
    refine ⟨tagMinorTyAV_validV hv hIds (minorFrame_shift hlen), fun a ha => ?_⟩
    rw [hty.1] at ha
    have := dispTower_underValid_go hT hMv hk hv r (m' + 1) (ms' ++ [a]) (by omega)
      (by simp [hlen]) ?_
    · rwa [consList_append, consList_cons, consList_nil] at this
    · intro j hj
      rcases Nat.lt_or_ge j m' with hlt | hge
      · rw [getD_snoc_lt (by omega)]; exact hms j hlt
      · have hjm : j = m' := by omega
        rw [hjm, ← hlen, getD_snoc_self, hlen]
        exact ha

/-- **The dispatch's tower is bit-valid.** -/
theorem dispTowerAV_validV (hT : TagOk W ρp Idss) (hk : Idss.length = k)
    (hv : SumFieldsValid ρp Idss) :
    AnnotValid V ρp (dispTowerAV ℓ W w k Idss) := by
  unfold dispTowerAV
  refine mkLamsC_validV ?_
  unfold dispDs
  refine ⟨tagMotTyAV_validV hv, fun Mv' hMv' => ?_⟩
  rw [(tagMotTyAV_facts hT).1] at hMv'
  have := dispTower_underValid_go (Mv := Mv') hT hMv' hk hv k 0 [] (Nat.zero_add k) rfl
    (fun j hj => absurd hj (Nat.not_lt_zero j))
  rwa [consList_nil, ← List.range_eq_range'] at this

/-- The tag motive is bit-valid at the parameter frame. -/
theorem tagMotAV_validV (hT : TagOk W ρp Idss) (hv : SumFieldsValid ρp Idss)
    (hAux : AnnotValid V ρp (auxBodyAV W w Idss rss tlss Eiss' Fss₀ Ess')) :
    AnnotValid V ρp (tagMotAV ℓ W w Idss rss tlss Eiss' Fss₀ Ess') := by
  have hI := auxIds_idxOk (V := V) (ρp := ρp) hT
  unfold tagMotAV
  rw [AnnotValid_lam]
  refine ⟨tagTyAV_validV hv, fun i _ => ?_⟩
  have hsh : shiftE 1 0 (cons i ρp) = ρp := by
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  rw [AnnotValid_pi]
  refine ⟨?_, fun _ _ => trivial, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
  unfold auxAtAV
  rw [AnnotValid_app]
  refine ⟨by rw [AnnotValid_liftN, hsh]; exact hAux, ?_⟩
  refine mkAppN_validV ?_ fun a ha => by rw [List.mem_singleton] at ha; subst ha; trivial
  rw [AnnotValid_liftN, hsh]
  exact tuplerAV_validV hI (auxIds_validV hv)

/-- **The motive dispatch is bit-valid.** -/
theorem motDispAV_validV {D mOff : Nat} {σ : Nat → V} (hfr : shiftE D 0 σ = ρp)
    (hT : TagOk W ρp Idss) (hk : Idss.length = k) (hv : SumFieldsValid ρp Idss)
    (hAux : AnnotValid V ρp (auxBodyAV W w Idss rss tlss Eiss' Fss₀ Ess')) :
    AnnotValid V σ (motDispAV ℓ W w D mOff k Idss rss tlss Eiss' Fss₀ Ess') := by
  unfold motDispAV
  refine AnnotValid_mkAppN (by rw [AnnotValid_liftN, hfr]; exact dispTowerAV_validV hT hk hv) ?_
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · rw [AnnotValid_liftN, hfr]
    exact tagMotAV_validV hT hv hAux
  · obtain ⟨m', -, rfl⟩ := List.mem_map.mp ha
    trivial

end DispValid

/-! ## The public and auxiliary minor spaces agree -/

section MinorEq

variable {ℓ W w k n J nF : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {EissO Eiss' : List (List (List AnnotTerm))} {FssR Fss₀ Ess' : List (List AnnotTerm)}
  {mems : Nat → Nat} {tgts : Nat → Nat → Nat} {Ms : List V} {dispV : V}
  {Es Fs : List AnnotTerm}

/-- **The dispatch's computation law**, at a member and a fitting index
spine: `disp ⟨inj m' ı⃗⟩ x = M_{m'} ı⃗ x`. -/
theorem dispLaw_of {mOff : Nat} {σ : Nat → V}
    (hdisp : ∀ (i x : V), i ∈ˢ tagSet W ρp Idss →
      x ∈ˢ auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess' i →
      ∃ (m' : Nat) (y : V), m' < k ∧ i = inj m' y ∧
        SetTheory.app (SetTheory.app dispV i) x
          = SetTheory.app (((List.range (Idss.getD m' []).length).map fun l => projS l y).foldl
              SetTheory.app (σ (mOff + k - 1 - m'))) x)
    (hMs : ∀ m', m' < k → σ (mOff + k - 1 - m') = Ms.getD m' pt)
    (hT : TagOk W ρp Idss)
    (m' : Nat) (hm' : m' < k) {Ids : List AnnotTerm} (hIds : Idss[m']? = some Ids)
    {is : List V} (hfit : SpineFit ρp Ids is) (x : V)
    (hx : x ∈ˢ auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess' (inj m' (mkTower (is ++ [pt])))) :
    SetTheory.app (SetTheory.app dispV (inj m' (mkTower (is ++ [pt])))) x
      = SetTheory.app (is.foldl SetTheory.app (Ms.getD m' pt)) x := by
  have hg : Idss.getD m' [] = Ids := by rw [List.getD_eq_getElem?_getD, hIds]; rfl
  obtain ⟨m'', y, hm'', heq, hval⟩ := hdisp _ x (tagTuple_mem hT hIds hfit) hx
  obtain ⟨rfl, rfl⟩ := inj_inj heq
  rw [hval, hMs m' hm', hg]
  congr 2
  have hlen : is.length = Ids.length := hfit.length_eq
  have : ((List.range is.length).map fun l => projS l (mkTower (is ++ [pt]))) = is := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      have hi : i < is.length := by simpa using h1
      rw [projS_mkTower i (is ++ [pt]) (by simp; omega), List.getElem_append_left hi]
  rw [← hlen, this]

/-- **The public minor `J` and the auxiliary minor `J` read the same
set**: the dispatch's computation law at the conclusion and at every
inductive hypothesis. -/
theorem minor_space_eq (hT : TagOk W ρp Idss)
    (hnF : Fs.length = nF) (har : (FssR.getD J []).length = nF)
    (hEiss' : Eiss'.getD J [] = (List.range nF).map fun i =>
      [tagTupleAV W (tgts J i) (i + ((tlss.getD J []).getD i []).length) Idss
        ((EissO.getD J []).getD i [])])
    (hlaw : ∀ (m' : Nat), m' < k → ∀ Ids, Idss[m']? = some Ids → ∀ is : List V,
      SpineFit ρp Ids is → ∀ x : V,
      x ∈ˢ auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess' (inj m' (mkTower (is ++ [pt]))) →
      SetTheory.app (SetTheory.app dispV (inj m' (mkTower (is ++ [pt])))) x
        = SetTheory.app (is.foldl SetTheory.app (Ms.getD m' pt)) x)
    (hmemsJ : mems J < k) (htgtsJ : ∀ i, tgts J i < k)
    {IdsC : List AnnotTerm} (hIdsC : Idss[mems J]? = some IdsC)
    (hIdsT : ∀ i, ∃ Ids, Idss[tgts J i]? = some Ids)
    (hctor : ∀ fs : List V, SpineFit ρp Fs fs →
      (∀ E ∈ Es, WellDenoted V (consList fs ρp) E) ∧
      SpineFit ρp IdsC (idxValsAt ρp Es fs) ∧
      ctorValI w J fs ∈ˢ auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess'
        (inj (mems J) (mkTower (idxValsAt ρp Es fs ++ [pt]))))
    (hslot : ∀ i ∈ recIdx (rss.getD J []) nF, ∀ fs : List V, SpineFit ρp Fs fs →
      ∀ as : List V, SpineFit (consList (fs.take i) ρp)
        (((tlss.getD J []).getD i []).map (·.2.2)) as →
      (∀ E ∈ (EissO.getD J []).getD i [],
        WellDenoted V (consList as (consList (fs.take i) ρp)) E) ∧
      (∀ Ids, Idss[tgts J i]? = some Ids → SpineFit ρp Ids
        (((EissO.getD J []).getD i []).map
          (interp V (consList as (consList (fs.take i) ρp))))) ∧
      as.foldl SetTheory.app (fs.getD i pt) ∈ˢ auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess'
        (inj (tgts J i) (mkTower ((((EissO.getD J []).getD i []).map
          (interp V (consList as (consList (fs.take i) ρp)))) ++ [pt])))) :
    minorSpI ℓ (fun fs => ihSpL ℓ (concI w ρp (Ms.getD (mems J) pt) Es J fs)
        (ihDomsIM ℓ ρp (fun i => Ms.getD (tgts J i) pt) rss tlss EissO
          (fun j' => (FssR.getD j' []).length) J fs)) Fs ρp []
      = minorSpI ℓ (fun fs => ihSpL ℓ
          (concI w ρp dispV [tagTupleAV W (mems J) nF Idss Es] J fs)
          (ihDomsI ℓ ρp dispV rss tlss Eiss' (fun j' => (FssR.getD j' []).length) J fs))
        Fs ρp [] := by
  refine minorSpI_congr_body fun fs hfs => ?_
  rw [List.nil_append]
  have hlenfs : fs.length = nF := by rw [hfs.length_eq, hnF]
  obtain ⟨hEok, hEfit, hfib⟩ := hctor fs hfs
  -- the conclusions agree
  have hconc : concI w ρp (Ms.getD (mems J) pt) Es J fs
      = concI w ρp dispV [tagTupleAV W (mems J) nF Idss Es] J fs := by
    have hsh : shiftE nF 0 (consList fs ρp) = ρp := by
      rw [← hlenfs]; exact shiftE_consList fs ρp
    have htup := tagTupleAV_facts hT hIdsC (d := nF) (τ := consList fs ρp) hsh hEok hEfit
    unfold concI idxValsAt
    rw [List.map_singleton, htup.1, List.foldl_cons, List.foldl_nil]
    exact (hlaw (mems J) hmemsJ IdsC hIdsC _ hEfit _ hfib).symm
  -- the inductive hypotheses agree
  have hdoms : ihDomsIM ℓ ρp (fun i => Ms.getD (tgts J i) pt) rss tlss EissO
        (fun j' => (FssR.getD j' []).length) J fs
      = ihDomsI ℓ ρp dispV rss tlss Eiss' (fun j' => (FssR.getD j' []).length) J fs := by
    unfold ihDomsIM ihDomsI
    simp only [har]
    refine List.map_congr_left fun i hi => ?_
    have hiF : i < nF := (mem_recIdx.mp hi).1
    have hEi : (Eiss'.getD J []).getD i []
        = [tagTupleAV W (tgts J i) (i + ((tlss.getD J []).getD i []).length) Idss
            ((EissO.getD J []).getD i [])] := by
      rw [hEiss', List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hiF]
      rfl
    rw [hEi]
    refine piTele_congr_body fun as hfit => ?_
    rw [List.nil_append]
    have hspAs : SpineFit (consList (fs.take i) ρp)
        (((tlss.getD J []).getD i []).map (·.2.2)) as := fitsS_teleOfFields.mp hfit
    obtain ⟨hEok', hEfit', hfib'⟩ := hslot i hi fs hfs as hspAs
    obtain ⟨IdsT, hIdsT'⟩ := hIdsT i
    have hlenAs : as.length = (((tlss.getD J []).getD i []).map (·.2.2)).length := hspAs.length_eq
    have hlenTake : (fs.take i).length = i := by rw [List.length_take]; omega
    have hshi : shiftE i 0 (consList (fs.take i) ρp) = ρp := by
      simpa [hlenTake] using shiftE_consList (fs.take i) ρp
    have hsh : shiftE (i + ((tlss.getD J []).getD i []).length) 0
        (consList as (consList (fs.take i) ρp)) = ρp := by
      rw [show i + ((tlss.getD J []).getD i []).length
          = as.length + i from by rw [hlenAs, List.length_map]; omega,
        shiftE_consList_add, hshi]
    have htup := tagTupleAV_facts hT hIdsT' (d := i + ((tlss.getD J []).getD i []).length)
      (τ := consList as (consList (fs.take i) ρp)) hsh hEok' (hEfit' IdsT hIdsT')
    rw [List.map_singleton, htup.1, List.foldl_cons, List.foldl_nil]
    exact (hlaw (tgts J i) (htgtsJ i) IdsT hIdsT' _ (hEfit' IdsT hIdsT') _ hfib').symm
  rw [hconc, hdoms]

end MinorEq

/-! ## The hypotheses -/

/-- **What the mutual data give at one parameter frame** for the member
recursor leaf: the tag and the auxiliary family's chains, the
constructors' index readings (their fits, their gradings, and the
values they name in the auxiliary fibre — the dispatch's law is applied
at exactly those). -/
structure MutualFrameOkM (V : Type w) [SetTheory V] {env : Env} (m : EnvModel V env)
    (W wB nP : Nat) (Idss : List (List AnnotTerm)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (EissO Eiss' : List (List (List AnnotTerm))) (FssR Fss₀ Ess' : List (List AnnotTerm))
    (mems : Nat → Nat) (tgts : Nat → Nat → Nat) (cds : List CtorDatumR) (ρp : Nat → V) :
    Prop where
  tag : TagOk W ρp Idss
  tagValid : SumFieldsValid ρp Idss
  chains : FixChainsOkI W wB ρp (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess'
  xchains : XChainsOk W wB ρp (auxIds W Idss) rss tlss Eiss' Fss₀ Ess'
  auxValid : AnnotValid V ρp (auxBodyAV W wB Idss rss tlss Eiss' Fss₀ Ess')
  fieldsB : SumFieldsOkB wB ρp FssR
  /-- the constructor's index expressions: graded, fitting its member's
  telescope, and its value in the auxiliary fibre there -/
  ctor : ∀ (J : Nat) (cd : CtorDatumR), cds[J]? = some cd →
    ∀ fs : List V, SpineFit ρp ((cd.2.2.1.drop nP).map (·.2.2)) fs →
      (∀ E ∈ cd.2.2.2.1, WellDenoted V (consList fs ρp) E) ∧
      (∀ Ids, Idss[mems J]? = some Ids → SpineFit ρp Ids (idxValsAt ρp cd.2.2.2.1 fs)) ∧
      ctorValI wB J fs ∈ˢ auxFib W wB ρp Idss rss tlss Eiss' Fss₀ Ess'
        (inj (mems J) (mkTower (idxValsAt ρp cd.2.2.2.1 fs ++ [pt])))
  /-- a recursive slot's index expressions: the same, at the target member -/
  slot : ∀ (J : Nat) (cd : CtorDatumR), cds[J]? = some cd →
    ∀ i ∈ recIdx (rss.getD J []) cd.2.1, ∀ fs : List V,
      SpineFit ρp ((cd.2.2.1.drop nP).map (·.2.2)) fs →
      ∀ as : List V, SpineFit (consList (fs.take i) ρp)
        (((tlss.getD J []).getD i []).map (·.2.2)) as →
      (∀ E ∈ (EissO.getD J []).getD i [],
        WellDenoted V (consList as (consList (fs.take i) ρp)) E) ∧
      (∀ Ids, Idss[tgts J i]? = some Ids → SpineFit ρp Ids
        (((EissO.getD J []).getD i []).map
          (interp V (consList as (consList (fs.take i) ρp))))) ∧
      as.foldl SetTheory.app (fs.getD i pt) ∈ˢ auxFib W wB ρp Idss rss tlss Eiss' Fss₀ Ess'
        (inj (tgts J i) (mkTower ((((EissO.getD J []).getD i []).map
          (interp V (consList as (consList (fs.take i) ρp)))) ++ [pt])))

/-- **The member recursor leaf's hypotheses**: the regime facts and the
counts, the members' leaves and index data, the constructors' data, the
auxiliary leaf's own facts (`auxRecLeafFacts`'s conclusion) and the
STORED type's typing. -/
structure MutualLeafHyp (V : Type w) [SetTheory V] {env : Env} (m : EnvModel V env)
    (ψ : Name → Nat) (elimL : Level) (ℓ W wB nP s b k n : Nat)
    (Ls : List AnnotTerm) (nIdxs : List Nat) (pps : List (Nat × Nat × AnnotTerm))
    (ipss : List (List (Nat × Nat × AnnotTerm))) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (EissO Eiss' : List (List (List AnnotTerm))) (FssR Fss₀ Ess' : List (List AnnotTerm))
    (mems : Nat → Nat) (tgts : Nat → Nat → Nat) (cds : List CtorDatumR) (mm : Nat) : Prop where
  hℓ : elimL.eval ψ = ℓ
  hb : pwBit ψ (Level.zeronessOf elimL) = b
  hbz : ℓ = 0 ↔ b = 0
  hlenP : pps.length = nP
  hk : Idss.length = k
  hLs : Ls.length = k
  hnIdxs : nIdxs.length = k
  hipss : ipss.length = k
  hn : cds.length = n
  hmm : mm < k
  hmems : ∀ J, J < n → mems J < k
  htgts : ∀ J i, tgts J i < k
  /-- member `t`'s index telescope is its reading's index data -/
  hIdss : ∀ t, t < k → ∃ Ids, Idss[t]? = some Ids ∧ Ids.length = nIdxs.getD t 0 ∧
    (ipss.getD t []).map (·.2.2) = Ids
  /-- member `t`'s leaf is the mutual leaf at the parameter frame -/
  hleafM : ∀ t, t < k → ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
    ∀ σ : Nat → V, interp V σ (Ls.getD t default)
      = interp V (fun j => ρp (j + nP))
          (mutualTyAVI W wB (pps ++ ipss.getD t []) (nIdxs.getD t 0) Idss rss tlss Eiss'
            Fss₀ Ess' t)
  /-- the constructors' data, positionally -/
  hcd : ∀ J cd, cds[J]? = some cd →
    cd.2.2.1.length = nP + cd.2.1 ∧
    (∀ ρp : Nat → V, Sat V (((cd.2.2.1.take nP).map (·.2.2)).reverse) ρp ↔
      Sat V ((pps.map (·.2.2)).reverse) ρp) ∧
    m.acval cd.1 ψ = sumMkAV wB J cd.2.2.1 ((cd.2.2.1.drop nP).map (·.2.2)) (uChains FssR) ∧
    Term.bvarsBelow 0 (m.acval cd.1 ψ).erase ∧
    FssR[J]? = some ((cd.2.2.1.drop nP).map (·.2.2)) ∧
    cd.2.2.2.2.1 = recIdx (rss.getD J []) cd.2.1 ∧
    cd.2.2.2.2.2.2 = tlss.getD J [] ∧
    cd.2.2.2.2.2.1 = EissO.getD J [] ∧
    Eiss'.getD J [] = (List.range cd.2.1).map fun i =>
      [tagTupleAV W (tgts J i) (i + ((tlss.getD J []).getD i []).length) Idss
        ((EissO.getD J []).getD i [])]
  hframes : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
    MutualFrameOkM V m W wB nP Idss rss tlss EissO Eiss' FssR Fss₀ Ess' mems tgts cds ρp
  /-- the auxiliary former's leaf is closed -/
  hclL : Term.bvarsBelow 0 (auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess').erase
  /-- the auxiliary recursor's leaf is closed -/
  hclR : Term.bvarsBelow 0
    (auxRecAV m ψ ℓ W wB nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds).erase
  /-- `auxRecLeafFacts`'s conclusion -/
  haux : ∀ ρ : Nat → V,
    WellDenotedV V ρ
      (auxRecAV m ψ ℓ W wB nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds) ∧
    interp V ρ
        (auxRecAV m ψ ℓ W wB nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds)
      ∈ˢ interp V ρ (mkPisAV
          (auxRecDataAV m ψ W wB nP elimL pps Idss rss tlss Eiss' Fss₀ Ess' mems tgts cds)
          (recConcAV n 1))
  /-- `auxConc_facts`'s universe component -/
  hauxConc : ∀ (ρ : Nat → V) (as : List V),
    SpineFit ρ ((auxRecDataAV m ψ W wB nP elimL pps Idss rss tlss Eiss' Fss₀ Ess'
      mems tgts cds).map (·.2.2)) as →
    interp V (consList as ρ) (recConcAV n 1) ∈ˢ (univ ℓ : V)
  /-- the STORED recursor type's typing (the checker's) -/
  hstore : ∀ ρ : Nat → V, WellDenotedV V ρ
    (mkPisAV (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm)
      (mutualConcAV k n (nIdxs.getD mm 0) mm))

/-! ## The leaf's facts -/

section Facts

variable {m : EnvModel V env} {ψ : Name → Nat} {elimL : Level} {ℓ W wB nP s b k n : Nat}
  {Ls : List AnnotTerm} {nIdxs : List Nat} {pps : List (Nat × Nat × AnnotTerm)}
  {ipss : List (List (Nat × Nat × AnnotTerm))} {Idss : List (List AnnotTerm)}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {EissO Eiss' : List (List (List AnnotTerm))} {FssR Fss₀ Ess' : List (List AnnotTerm)}
  {mems : Nat → Nat} {tgts : Nat → Nat → Nat} {cds : List CtorDatumR} {mm : Nat}

/-- The public binder data's domains, split. -/
theorem mutualRecDataAV_doms
    (hb : pwBit ψ (Level.zeronessOf elimL) = b) (hLs : Ls.length = k) (hn : cds.length = n) :
    (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm).map (·.2.2)
      = (((pps.map (·.2.2) ++
          (motivesDataGo (fun t => Ls.getD t default) (fun t => nIdxs.getD t 0)
            (fun t => ipss.getD t []) ψ nP elimL b k 0).map (·.2.2)) ++
          (fixMinorsDataM mems tgts m ψ nP b cds k).map (·.2.2)) ++
          (liftDoms (k + n) 0 (ipss.getD mm [])).map (·.2.2)) ++
        [majorAVAtK (Ls.getD mm default) nP (nIdxs.getD mm 0) k n] := by
  unfold mutualRecDataAV
  rw [hb, hLs, hn]
  simp only [List.map_append, List.map_cons, List.map_nil, rebit_map_dom]

/-- The auxiliary binder data's domains, split. -/
theorem auxRecDataAV_doms
    (hb : pwBit ψ (Level.zeronessOf elimL) = b) (hn : cds.length = n) :
    (auxRecDataAV m ψ W wB nP elimL pps Idss rss tlss Eiss' Fss₀ Ess' mems tgts cds).map (·.2.2)
      = (((pps.map (·.2.2) ++
          [motiveAVIL (auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess') ψ nP 1 elimL
            (tagIps W Idss)]) ++
          (fixMinorsData m ψ nP b (auxCtorData W Idss mems tgts cds) 1).map (·.2.2)) ++
          (liftDoms (n + 1) 0 (tagIps W Idss)).map (·.2.2)) ++
        [majorAVAtL (auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess') nP 1 n] := by
  unfold auxRecDataAV fixRecDataAVL
  rw [hb, auxCtorData_length, hn]
  simp only [List.map_append, List.map_cons, List.map_nil, rebit_map_dom]

/-- The public minor entries, positionally. -/
theorem pubMinor_getD {b : Nat} (J : Nat) (cd : CtorDatumR) (hcd : cds[J]? = some cd) :
    ((fixMinorsDataM mems tgts m ψ nP b cds k).map (·.2.2)).getD J default
      = minorAVAtRM (mems J) (tgts J) m cd.1 ψ nP cd.2.1 b (k + J) cd.2.2.1 cd.2.2.2.1
          cd.2.2.2.2.1 cd.2.2.2.2.2.2 cd.2.2.2.2.2.1 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, fixMinorsDataM_getElem?, hcd]
  rfl

/-- The auxiliary minor entries, positionally. -/
theorem auxMinor_getD {b : Nat} (J : Nat) (cd : CtorDatumR) (hcd : cds[J]? = some cd) :
    ((fixMinorsData m ψ nP b (auxCtorData W Idss mems tgts cds) 1).map (·.2.2)).getD J default
      = minorAVAtR m cd.1 ψ nP cd.2.1 b (1 + J) cd.2.2.1
          [tagTupleAV W (mems J) cd.2.1 Idss cd.2.2.2.1] cd.2.2.2.2.1 cd.2.2.2.2.2.2
          ((List.range cd.2.1).map fun i =>
            [tagTupleAV W (tgts J i) (i + (cd.2.2.2.2.2.2.getD i []).length) Idss
              (cd.2.2.2.2.2.1.getD i [])]) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, fixMinorsData_getElem?,
    auxCtorData_getElem?, hcd]
  rfl


/-! ## The public → auxiliary spine transfer

The two facts the member leaf's typing and the block's ι law share:
the AUXILIARY recursor's spine at a fitting PUBLIC spine
(`mutualAuxSpine_of`) and, at a constructor's fields, the public
recursor spine of each recursive slot's inductive hypothesis
(`mutualIhSpine_of`).  Both are stated at the frames
`spineFit_append_inv` hands over when the public spine is cut along
`mutualRecDataAV_doms`, so a caller passes its split verbatim. -/

set_option maxHeartbeats 1600000 in
/-- **The auxiliary recursor's spine**, from member `mm`'s public one.
At a spine `(p⃗, M⃗, S⃗, ı⃗, t)` fitting member `mm`'s stored binder data,
the tuple `(p⃗, disp, S⃗, ⟨inj mm ı⃗⟩, t)` fits the AUXILIARY recursor's:
the motive slot takes the dispatch (`auxMotive_interp` at
`motDispAV_facts`), the minor slots transfer because the public and
auxiliary minor spaces agree at the dispatch (`minor_space_eq` through
`spineFit_transfer`), the ONE auxiliary index slot takes member `mm`'s
tagged tuple and the major slot is the public major read as the
auxiliary fibre (`interp_majorAVAtK`, `interp_majorAVAtL`).

This is `mutualRecBody_facts`' own step, exported: `mutualRecIotaCore`
asks for exactly this spine (`hspAux`). -/
theorem mutualAuxSpine_of
    (hyp : MutualLeafHyp V m ψ elimL ℓ W wB nP s b k n Ls nIdxs pps ipss Idss rss tlss
      EissO Eiss' FssR Fss₀ Ess' mems tgts cds mm)
    {ρ : Nat → V} {ps Ms Ss is : List V} {t : V}
    (hlenMs : Ms.length = k) (hlenSs : Ss.length = n)
    (hlenIs : is.length = nIdxs.getD mm 0)
    (hspP : SpineFit ρ (pps.map (·.2.2)) ps)
    (hspM : SpineFit (consList ps ρ)
      ((motivesDataGo (fun q => Ls.getD q default) (fun q => nIdxs.getD q 0)
        (fun q => ipss.getD q []) ψ nP elimL b k 0).map (·.2.2)) Ms)
    (hspS : SpineFit (consList (ps ++ Ms) ρ)
      ((fixMinorsDataM mems tgts m ψ nP b cds k).map (·.2.2)) Ss)
    (hspI : SpineFit (consList (ps ++ Ms ++ Ss) ρ)
      ((liftDoms (k + n) 0 (ipss.getD mm [])).map (·.2.2)) is)
    (ht : t ∈ˢ interp V (consList (ps ++ Ms ++ Ss ++ is) ρ)
      (majorAVAtK (Ls.getD mm default) nP (nIdxs.getD mm 0) k n)) :
    SpineFit ρ ((auxRecDataAV m ψ W wB nP elimL pps Idss rss tlss Eiss' Fss₀ Ess'
        mems tgts cds).map (·.2.2))
      (ps ++ [interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
          (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
            rss tlss Eiss' Fss₀ Ess')] ++ Ss
        ++ [inj mm (mkTower (is ++ [pt]))] ++ [t]) := by
  classical
  have hmmk : mm < k := hyp.hmm
  obtain ⟨IdsM, hIdsMM, hlenIdsMM, hipdMM⟩ := hyp.hIdss mm hmmk
  -- the frames
  have hfr1 : consList (ps ++ Ms) ρ = consList Ms (consList ps ρ) := consList_append _ _ _
  have hfr2 : consList (ps ++ Ms ++ Ss) ρ = consList Ss (consList Ms (consList ps ρ)) := by
    rw [consList_append, hfr1]
  have hfr3 : consList (ps ++ Ms ++ Ss ++ is) ρ
      = consList is (consList Ss (consList Ms (consList ps ρ))) := by
    rw [consList_append, hfr2]
  rw [hfr1] at hspS
  rw [hfr2] at hspI
  rw [hfr3] at ht
  -- the parameter frame
  have hsatP : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hspP
    rwa [List.append_nil] at h
  have hF := hyp.hframes _ hsatP
  -- the motives
  have hmot : ∀ t', t' < k →
      Ms.getD t' pt ∈ˢ memberMotSp ℓ W wB (consList ps ρ) Idss rss tlss Eiss' Fss₀ Ess' t' := by
    intro t' ht'
    obtain ⟨Ids', hIds', hlenIds', hipd'⟩ := hyp.hIdss t' ht'
    have hlenTake : (Ms.take t').length = t' := by rw [List.length_take]; omega
    have hmem := FixKI.spineFit_getD_mem' hspM (l := t')
      (by rw [List.length_map, motivesDataGo_length]; omega)
    have hentry : ((motivesDataGo (fun q => Ls.getD q default) (fun q => nIdxs.getD q 0)
        (fun q => ipss.getD q []) ψ nP elimL b k 0).map (·.2.2)).getD t' default
        = (motiveAVIL (Ls.getD t' default) ψ nP (nIdxs.getD t' 0) elimL
            (ipss.getD t' [])).liftN (0 + t') 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        motivesDataGo_getElem? _ _ _ ψ nP elimL b k 0 t' ht']
      rfl
    have hsh : shiftE t' 0 (consList (Ms.take t') (consList ps ρ)) = consList ps ρ := by
      simpa [hlenTake] using shiftE_consList (Ms.take t') (consList ps ρ)
    rw [hentry, interp_liftN, Nat.zero_add, hsh,
      interp_memberMotive hyp.hℓ hyp.hlenP hipd' hlenIds' hsatP hF.tag hF.chains hIds'
        (fun σ' => hyp.hleafM t' ht' _ hsatP σ')] at hmem
    exact hmem
  -- the frame's slots
  have hσmot : ∀ (q t' : Nat), t' < k → q = nIdxs.getD mm 0 + n + (k - 1 - t') + 1 →
      cons t (consList is (consList Ss (consList Ms (consList ps ρ)))) q = Ms.getD t' pt := by
    intro q t' ht' hq
    subst hq
    rw [cons_succ,
      show nIdxs.getD mm 0 + n + (k - 1 - t') = (n + (k - 1 - t')) + is.length from by
        rw [hlenIs]; omega,
      consList_apply_add,
      show n + (k - 1 - t') = (k - 1 - t') + Ss.length from by rw [hlenSs]; omega,
      consList_apply_add, consList_apply_lt' Ms (consList ps ρ) (by omega),
      show Ms.length - 1 - (k - 1 - t') = t' from by omega]
  have hσeq : cons t (consList is (consList Ss (consList Ms (consList ps ρ))))
      = consList (Ms ++ Ss ++ is ++ [t]) (consList ps ρ) := by
    rw [consList_append, consList_append, consList_append, consList_cons, consList_nil]
  have hσshift : shiftE (k + n + nIdxs.getD mm 0 + 1) 0
      (cons t (consList is (consList Ss (consList Ms (consList ps ρ))))) = consList ps ρ := by
    rw [hσeq, show k + n + nIdxs.getD mm 0 + 1 = (Ms ++ Ss ++ is ++ [t]).length from by
      simp [hlenMs, hlenSs, hlenIs]; omega]
    exact shiftE_consList _ _
  -- the index binders, reduced to member `mm`'s telescope
  have hshY : shiftE (k + n) 0 (consList Ss (consList Ms (consList ps ρ))) = consList ps ρ := by
    rw [← consList_append, show k + n = (Ms ++ Ss).length from by simp [hlenMs, hlenSs]]
    exact shiftE_consList _ _
  rw [spineFit_liftDoms_iff, hshY, hipdMM] at hspI
  -- the major, read as the auxiliary fibre
  have hmaj : interp V (consList is (consList Ss (consList Ms (consList ps ρ))))
        (majorAVAtK (Ls.getD mm default) nP (nIdxs.getD mm 0) k n)
      = auxFib W wB (consList ps ρ) Idss rss tlss Eiss' Fss₀ Ess'
          (inj mm (mkTower (is ++ [pt]))) :=
    interp_majorAVAtK hyp.hlenP hipdMM hlenIdsMM hsatP hF.tag hF.chains hIdsMM
      (fun σ' => hyp.hleafM mm hyp.hmm _ hsatP σ') hlenMs hlenSs hspI
  rw [hmaj] at ht
  -- the dispatch
  have hdispHyp : MotDispHyp ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k
      (consList ps ρ) (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
      Idss rss tlss Eiss' Fss₀ Ess' :=
    ⟨hσshift, hF.tag, hF.chains, hyp.hk, fun t' ht' => by
      rw [hσmot _ t' ht' (by omega)]; exact hmot t' ht'⟩
  obtain ⟨hlaw0, hdispMem, -⟩ := motDispAV_facts hdispHyp
  have hlaw : ∀ (t' : Nat), t' < k → ∀ Ids', Idss[t']? = some Ids' → ∀ is' : List V,
      SpineFit (consList ps ρ) Ids' is' → ∀ x : V,
      x ∈ˢ auxFib W wB (consList ps ρ) Idss rss tlss Eiss' Fss₀ Ess'
        (inj t' (mkTower (is' ++ [pt]))) →
      SetTheory.app (SetTheory.app
          (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
            (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
              rss tlss Eiss' Fss₀ Ess')) (inj t' (mkTower (is' ++ [pt])))) x
        = SetTheory.app (is'.foldl SetTheory.app (Ms.getD t' pt)) x :=
    fun t' ht' Ids' hIds' is' hfit x hx =>
      dispLaw_of hlaw0 (fun t'' ht'' => hσmot _ t'' ht'' (by omega)) hF.tag t' ht' hIds' hfit x hx
  -- the minors: the public and auxiliary spaces agree at the dispatch
  have hspSaux : SpineFit
      (cons (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
        (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
          rss tlss Eiss' Fss₀ Ess')) (consList ps ρ))
      ((fixMinorsData m ψ nP b (auxCtorData W Idss mems tgts cds) 1).map (·.2.2)) Ss := by
    refine spineFit_transfer ?_ ?_ hspS
    · rw [List.length_map, List.length_map, fixMinorsDataM_length, fixMinorsData_length,
        auxCtorData_length]
    · intro us J hus hJ
      rw [List.length_map, fixMinorsDataM_length, hyp.hn] at hJ
      obtain ⟨cd, hcd⟩ : ∃ cd, cds[J]? = some cd :=
        ⟨_, List.getElem?_eq_getElem (by rw [hyp.hn]; omega)⟩
      obtain ⟨hlenDs, htakeP, hleafC, hclC, hFsj, hrecIdx, htls, hEissO, hEiss'⟩ :=
        hyp.hcd J cd hcd
      have hsatC : Sat V (((cd.2.2.1.take nP).map (·.2.2)).reverse) (consList ps ρ) :=
        (htakeP _).mpr hsatP
      have hnF : ((cd.2.2.1.drop nP).map (·.2.2)).length = cd.2.1 := by
        rw [List.length_map, List.length_drop, hlenDs]; omega
      have har : (FssR.getD J []).length = cd.2.1 := by
        rw [List.getD_eq_getElem?_getD, hFsj, Option.getD_some, hnF]
      obtain ⟨IdsC, hIdsC, -, -⟩ := hyp.hIdss (mems J) (hyp.hmems J hJ)
      rw [pubMinor_getD J cd hcd, auxMinor_getD J cd hcd, hrecIdx, htls, hEissO, ← hEiss',
        interp_minorAVAtRM (Ms := Ms) (ℓ := ℓ) (Fss := FssR) (rss := rss) (tlss := tlss)
          (Eiss := EissO) hyp.hbz hlenMs hus (hyp.hmems J hJ) hlenDs
          (fun i _ => hyp.htgts J i) hleafC hclC hFsj hF.fieldsB hsatC,
        interp_minorAVAtR (ℓ := ℓ) (Fss := FssR) (rss := rss) (tlss := tlss) (Eiss := Eiss')
          hyp.hbz hus hlenDs hleafC hclC hFsj hF.fieldsB hsatC]
      exact minor_space_eq hF.tag hnF har hEiss' hlaw (hyp.hmems J hJ) (fun i => hyp.htgts J i)
        hIdsC (fun i => by
          obtain ⟨I, hI, -, -⟩ := hyp.hIdss (tgts J i) (hyp.htgts J i); exact ⟨I, hI⟩)
        (fun fs hfs => ⟨(hF.ctor J cd hcd fs hfs).1,
          (hF.ctor J cd hcd fs hfs).2.1 IdsC hIdsC, (hF.ctor J cd hcd fs hfs).2.2⟩)
        (fun i hi fs hfs bs hbs => hF.slot J cd hcd i hi fs hfs bs hbs)
  -- the tag element
  have htagMem : inj mm (mkTower (is ++ [pt])) ∈ˢ interp V (consList ps ρ) (tagTyAV W Idss) := by
    rw [(tagTyAV_facts hF.tag).1]
    exact tagTuple_mem hF.tag hIdsMM hspI
  -- the auxiliary spine, block by block
  rw [auxRecDataAV_doms hyp.hb hyp.hn]
  refine SpineFit.append (SpineFit.append (SpineFit.append (SpineFit.append hspP ?_) ?_) ?_) ?_
  · refine ⟨?_, trivial⟩
    rw [auxMotive_interp hyp.hℓ hyp.hlenP hsatP hF.tag hF.xchains hyp.hclL]
    exact hdispMem
  · rw [show consList (ps ++ [interp V (cons t (consList is (consList Ss
        (consList Ms (consList ps ρ)))))
          (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
            rss tlss Eiss' Fss₀ Ess')]) ρ
        = cons (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
            (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
              rss tlss Eiss' Fss₀ Ess')) (consList ps ρ) from by
      rw [consList_append]; rfl]
    exact hspSaux
  · rw [show consList (ps ++ [interp V (cons t (consList is (consList Ss
        (consList Ms (consList ps ρ)))))
          (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
            rss tlss Eiss' Fss₀ Ess')] ++ Ss) ρ
        = consList Ss (cons (interp V (cons t (consList is (consList Ss
            (consList Ms (consList ps ρ)))))
            (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
              rss tlss Eiss' Fss₀ Ess')) (consList ps ρ)) from by
      rw [consList_append, consList_append]; rfl]
    rw [spineFit_liftDoms_iff, shiftE_minors hlenSs, tagIps_doms]
    exact ⟨htagMem, trivial⟩
  · rw [show consList (ps ++ [interp V (cons t (consList is (consList Ss
        (consList Ms (consList ps ρ)))))
          (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
            rss tlss Eiss' Fss₀ Ess')] ++ Ss ++ [inj mm (mkTower (is ++ [pt]))]) ρ
        = consList [inj mm (mkTower (is ++ [pt]))] (consList Ss
            (cons (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
              (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
                rss tlss Eiss' Fss₀ Ess')) (consList ps ρ))) from by
      rw [consList_append, consList_append, consList_append]; rfl]
    refine ⟨?_, trivial⟩
    rw [interp_majorAVAtL (ips := tagIps W Idss) (nIdx := 1) hyp.hlenP rfl hsatP
      (by rw [tagIps_doms]; exact hF.xchains)
      (auxFormer_hleafT (nP := nP) hyp.hclL (consList ps ρ)) hlenSs
      (by rw [tagIps_doms]; exact ⟨htagMem, trivial⟩), tagIps_doms]
    exact ht

set_option maxHeartbeats 1600000 in
/-- **The inductive hypotheses' public spines**, at constructor `J`'s
fields.  At a field spine `a⃗` fitting constructor `J`'s field domains
and a telescope spine `b⃗` of recursive slot `i`, the slot's index
expressions are graded, fit the TARGET member's telescope and have its
index count, and the tuple `(p⃗, M⃗, S⃗, e⃗_i(b⃗), f_i b⃗)` fits the target
member's STORED binder data — the recursor spine `mutualRecIotaCore`'s
`hih` asks for.  The slot's three index facts are
`MutualFrameOkM.slot`'s; the spine is `mutualRecDataAV_doms` at the
recursor's own parameter, motive and minor blocks with
`interp_majorAVAtK` at the target member's leaf. -/
theorem mutualIhSpine_of
    (hyp : MutualLeafHyp V m ψ elimL ℓ W wB nP s b k n Ls nIdxs pps ipss Idss rss tlss
      EissO Eiss' FssR Fss₀ Ess' mems tgts cds mm)
    {ρ : Nat → V} {ps Ms Ss as₂ : List V} {J : Nat} {cd : CtorDatumR}
    (hcd : cds[J]? = some cd)
    (hlenMs : Ms.length = k) (hlenSs : Ss.length = n)
    (hspP : SpineFit ρ (pps.map (·.2.2)) ps)
    (hspM : SpineFit (consList ps ρ)
      ((motivesDataGo (fun q => Ls.getD q default) (fun q => nIdxs.getD q 0)
        (fun q => ipss.getD q []) ψ nP elimL b k 0).map (·.2.2)) Ms)
    (hspS : SpineFit (consList (ps ++ Ms) ρ)
      ((fixMinorsDataM mems tgts m ψ nP b cds k).map (·.2.2)) Ss)
    (hfitF : SpineFit (consList ps ρ) ((cd.2.2.1.drop nP).map (·.2.2)) as₂) :
    ∀ i ∈ recIdx (rss.getD J []) cd.2.1, ∀ bs : List V,
      SpineFit (consList (as₂.take i) (consList ps ρ))
        (((tlss.getD J []).getD i []).map (·.2.2)) bs →
      (∃ Ids' : List AnnotTerm, Idss[tgts J i]? = some Ids' ∧
        SpineFit (consList ps ρ) Ids'
          (((EissO.getD J []).getD i []).map
            (interp V (consList bs (consList (as₂.take i) (consList ps ρ)))))) ∧
      (∀ E ∈ (EissO.getD J []).getD i [],
        WellDenoted V (consList bs (consList (as₂.take i) (consList ps ρ))) E) ∧
      (((EissO.getD J []).getD i []).length = nIdxs.getD (tgts J i) 0) ∧
      SpineFit ρ
        ((mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts (tgts J i)).map (·.2.2))
        (ps ++ Ms ++ Ss ++
          (((EissO.getD J []).getD i []).map
            (interp V (consList bs (consList (as₂.take i) (consList ps ρ))))) ++
          [(Semantics.frameIdx ((tlss.getD J []).getD i []).length
              (consList bs (consList (as₂.take i) (consList ps ρ)))).foldl
            SetTheory.app (as₂.getD i pt)]) := by
  classical
  intro i hi bs hbs
  have hsatP : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hspP
    rwa [List.append_nil] at h
  have hF := hyp.hframes _ hsatP
  obtain ⟨hEok, hEfit, hfib⟩ := hF.slot J cd hcd i hi as₂ hfitF bs hbs
  obtain ⟨Ids', hIds', hlenIds', hipd'⟩ := hyp.hIdss (tgts J i) (hyp.htgts J i)
  have hfit' := hEfit Ids' hIds'
  have hlenEis : ((EissO.getD J []).getD i []).length = nIdxs.getD (tgts J i) 0 := by
    have h := hfit'.length_eq
    rw [List.length_map, hlenIds'] at h
    exact h
  have hbsLen : bs.length = (((tlss.getD J []).getD i []).map (·.2.2)).length := hbs.length_eq
  have hfrIdx : Semantics.frameIdx ((tlss.getD J []).getD i []).length
      (consList bs (consList (as₂.take i) (consList ps ρ))) = bs :=
    frameIdx_consList (by rw [hbsLen, List.length_map]) _
  refine ⟨⟨Ids', hIds', hfit'⟩, hEok, hlenEis, ?_⟩
  rw [hfrIdx]
  -- the frames
  have hfr1 : consList (ps ++ Ms) ρ = consList Ms (consList ps ρ) := consList_append _ _ _
  rw [hfr1] at hspS
  have hshY : shiftE (k + n) 0 (consList Ss (consList Ms (consList ps ρ))) = consList ps ρ := by
    rw [← consList_append, show k + n = (Ms ++ Ss).length from by simp [hlenMs, hlenSs]]
    exact shiftE_consList _ _
  rw [mutualRecDataAV_doms hyp.hb hyp.hLs hyp.hn]
  refine SpineFit.append (SpineFit.append (SpineFit.append (SpineFit.append hspP hspM) ?_) ?_) ?_
  · rw [consList_append]
    exact hspS
  · rw [consList_append, consList_append, spineFit_liftDoms_iff, hshY, hipd']
    exact hfit'
  · rw [consList_append, consList_append, consList_append]
    refine ⟨?_, trivial⟩
    rw [interp_majorAVAtK hyp.hlenP hipd' hlenIds' hsatP hF.tag hF.chains hIds'
      (fun σ' => hyp.hleafM (tgts J i) (hyp.htgts J i) _ hsatP σ') hlenMs hlenSs hfit']
    exact hfib

/-- **The member recursor's body**, at a frame satisfying the stored
type's binder data: graded, valid, in the conclusion's reading, and (at
a `Prop` elimination) the conclusion is a truth value. -/
theorem mutualRecBody_facts
    (hyp : MutualLeafHyp V m ψ elimL ℓ W wB nP s b k n Ls nIdxs pps ipss Idss rss tlss
      EissO Eiss' FssR Fss₀ Ess' mems tgts cds mm)
    (ρ : Nat → V) (as : List V)
    (hsp : SpineFit ρ
      ((mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm).map (·.2.2)) as) :
    WellDenotedV V (consList as ρ)
        (mutualRecBodyAV ℓ W wB nP k n (nIdxs.getD mm 0) mm Idss rss tlss Eiss' Fss₀ Ess'
          (auxRecAV m ψ ℓ W wB nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds)) ∧
      interp V (consList as ρ)
          (mutualRecBodyAV ℓ W wB nP k n (nIdxs.getD mm 0) mm Idss rss tlss Eiss' Fss₀ Ess'
            (auxRecAV m ψ ℓ W wB nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds))
        ∈ˢ interp V (consList as ρ) (mutualConcAV k n (nIdxs.getD mm 0) mm) ∧
      (b = 0 → interp V (consList as ρ) (mutualConcAV k n (nIdxs.getD mm 0) mm)
        ∈ˢ (univZero : V)) := by
  classical
  have hmmk : mm < k := hyp.hmm
  obtain ⟨IdsM, hIdsMM, hlenIdsMM, hipdMM⟩ := hyp.hIdss mm hmmk
  -- the spine, split
  rw [mutualRecDataAV_doms hyp.hb hyp.hLs hyp.hn] at hsp
  obtain ⟨as₃, ts, rfl, hsp₃, hspT⟩ := spineFit_append_inv hsp
  obtain ⟨t, rfl, ht⟩ := spineFit_singleton hspT
  obtain ⟨as₂, is, rfl, hsp₂, hspI⟩ := spineFit_append_inv hsp₃
  obtain ⟨as₁, Ss, rfl, hsp₁, hspS⟩ := spineFit_append_inv hsp₂
  obtain ⟨ps, Ms, rfl, hspP, hspM⟩ := spineFit_append_inv hsp₁
  -- the frames
  have hlenPs : ps.length = nP := by rw [hspP.length_eq, List.length_map, hyp.hlenP]
  have hlenMs : Ms.length = k := by
    rw [hspM.length_eq, List.length_map, motivesDataGo_length]
  have hlenSs : Ss.length = n := by
    rw [hspS.length_eq, List.length_map, fixMinorsDataM_length, hyp.hn]
  have hlenIs : is.length = nIdxs.getD mm 0 := by
    rw [hspI.length_eq, List.length_map, liftDoms_length, ← hlenIdsMM, ← hipdMM, List.length_map]
  have hfr1 : consList (ps ++ Ms) ρ = consList Ms (consList ps ρ) := consList_append _ _ _
  have hfr2 : consList (ps ++ Ms ++ Ss) ρ = consList Ss (consList Ms (consList ps ρ)) := by
    rw [consList_append, hfr1]
  have hfr3 : consList (ps ++ Ms ++ Ss ++ is) ρ
      = consList is (consList Ss (consList Ms (consList ps ρ))) := by
    rw [consList_append, hfr2]
  have hfr4 : consList (ps ++ Ms ++ Ss ++ is ++ [t]) ρ
      = cons t (consList is (consList Ss (consList Ms (consList ps ρ)))) := by
    rw [consList_append, hfr3, consList_cons, consList_nil]
  -- the auxiliary recursor's spine (`mutualAuxSpine_of`, at the split)
  have hfitA0 := mutualAuxSpine_of hyp hlenMs hlenSs hlenIs hspP hspM hspS hspI ht
  rw [hfr2] at hspI
  rw [hfr3] at ht
  rw [hfr4]
  -- the parameter frame
  have hsatP : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hspP
    rwa [List.append_nil] at h
  have hF := hyp.hframes _ hsatP
  -- the motives
  have hmot : ∀ t', t' < k →
      Ms.getD t' pt ∈ˢ memberMotSp ℓ W wB (consList ps ρ) Idss rss tlss Eiss' Fss₀ Ess' t' := by
    intro t' ht'
    obtain ⟨Ids', hIds', hlenIds', hipd'⟩ := hyp.hIdss t' ht'
    have hlenTake : (Ms.take t').length = t' := by rw [List.length_take]; omega
    have hmem := FixKI.spineFit_getD_mem' hspM (l := t')
      (by rw [List.length_map, motivesDataGo_length]; omega)
    have hentry : ((motivesDataGo (fun t => Ls.getD t default) (fun t => nIdxs.getD t 0)
        (fun t => ipss.getD t []) ψ nP elimL b k 0).map (·.2.2)).getD t' default
        = (motiveAVIL (Ls.getD t' default) ψ nP (nIdxs.getD t' 0) elimL
            (ipss.getD t' [])).liftN (0 + t') 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        motivesDataGo_getElem? _ _ _ ψ nP elimL b k 0 t' ht']
      rfl
    have hsh : shiftE t' 0 (consList (Ms.take t') (consList ps ρ)) = consList ps ρ := by
      simpa [hlenTake] using shiftE_consList (Ms.take t') (consList ps ρ)
    rw [hentry, interp_liftN, Nat.zero_add, hsh,
      interp_memberMotive hyp.hℓ hyp.hlenP hipd' hlenIds' hsatP hF.tag hF.chains hIds'
        (fun σ' => hyp.hleafM t' ht' _ hsatP σ')] at hmem
    exact hmem
  -- the frame's slots
  have hσmot : ∀ (q t' : Nat), t' < k → q = nIdxs.getD mm 0 + n + (k - 1 - t') + 1 →
      cons t (consList is (consList Ss (consList Ms (consList ps ρ)))) q = Ms.getD t' pt := by
    intro q t' ht' hq
    subst hq
    rw [cons_succ,
      show nIdxs.getD mm 0 + n + (k - 1 - t') = (n + (k - 1 - t')) + is.length from by
        rw [hlenIs]; omega,
      consList_apply_add,
      show n + (k - 1 - t') = (k - 1 - t') + Ss.length from by rw [hlenSs]; omega,
      consList_apply_add, consList_apply_lt' Ms (consList ps ρ) (by omega),
      show Ms.length - 1 - (k - 1 - t') = t' from by omega]
  have hσminor : ∀ i, i < n →
      cons t (consList is (consList Ss (consList Ms (consList ps ρ))))
        (nIdxs.getD mm 0 + 1 + n - 1 - i) = Ss.getD i pt := by
    intro i hi
    rw [show nIdxs.getD mm 0 + 1 + n - 1 - i = (n - 1 - i + is.length) + 1 from by
        rw [hlenIs]; omega,
      cons_succ, consList_apply_add, consList_apply_lt' Ss _ (by omega),
      show Ss.length - 1 - (n - 1 - i) = i from by omega]
  have hσeq : cons t (consList is (consList Ss (consList Ms (consList ps ρ))))
      = consList (Ms ++ Ss ++ is ++ [t]) (consList ps ρ) := by
    rw [consList_append, consList_append, consList_append, consList_cons, consList_nil]
  have hσshift : shiftE (k + n + nIdxs.getD mm 0 + 1) 0
      (cons t (consList is (consList Ss (consList Ms (consList ps ρ))))) = consList ps ρ := by
    rw [hσeq, show k + n + nIdxs.getD mm 0 + 1 = (Ms ++ Ss ++ is ++ [t]).length from by
      simp [hlenMs, hlenSs, hlenIs]; omega]
    exact shiftE_consList _ _
  have hfr1' : RecFrameS 1 (consList is (consList Ss (consList Ms (consList ps ρ))))
      (cons t (consList is (consList Ss (consList Ms (consList ps ρ))))) := by
    show shiftE 1 0 _ = _
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  -- the index variables and the tagged tuple
  have hshY : shiftE (k + n) 0 (consList Ss (consList Ms (consList ps ρ))) = consList ps ρ := by
    rw [← consList_append, show k + n = (Ms ++ Ss).length from by simp [hlenMs, hlenSs]]
    exact shiftE_consList _ _
  rw [spineFit_liftDoms_iff, hshY, hipdMM] at hspI
  have hidxvars : (idxVarsAV (nIdxs.getD mm 0) 1).map
      (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))) = is := by
    rw [map_idxVarsAV_interp hfr1', frameIdx_consList hlenIs]
  have htagvals := tagTupleAV_facts hF.tag hIdsMM (d := k + n + nIdxs.getD mm 0 + 1)
    (τ := cons t (consList is (consList Ss (consList Ms (consList ps ρ))))) hσshift
    (Es := idxVarsAV (nIdxs.getD mm 0) 1)
    (fun E hE => by obtain ⟨l, -, rfl⟩ := List.mem_map.mp hE; trivial)
    (by rw [hidxvars]; exact hspI)
  rw [hidxvars] at htagvals
  -- the major
  have hmaj : interp V (consList is (consList Ss (consList Ms (consList ps ρ))))
        (majorAVAtK (Ls.getD mm default) nP (nIdxs.getD mm 0) k n)
      = auxFib W wB (consList ps ρ) Idss rss tlss Eiss' Fss₀ Ess'
          (inj mm (mkTower (is ++ [pt]))) :=
    interp_majorAVAtK hyp.hlenP hipdMM hlenIdsMM hsatP hF.tag hF.chains hIdsMM
      (fun σ' => hyp.hleafM mm hyp.hmm _ hsatP σ') hlenMs hlenSs hspI
  rw [hmaj] at ht
  -- the dispatch
  have hdispHyp : MotDispHyp ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k
      (consList ps ρ) (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
      Idss rss tlss Eiss' Fss₀ Ess' :=
    ⟨hσshift, hF.tag, hF.chains, hyp.hk, fun t' ht' => by
      rw [hσmot _ t' ht' (by omega)]; exact hmot t' ht'⟩
  obtain ⟨hlaw0, -, hdispOk⟩ := motDispAV_facts hdispHyp
  have hlaw : ∀ (t' : Nat), t' < k → ∀ Ids', Idss[t']? = some Ids' → ∀ is' : List V,
      SpineFit (consList ps ρ) Ids' is' → ∀ x : V,
      x ∈ˢ auxFib W wB (consList ps ρ) Idss rss tlss Eiss' Fss₀ Ess'
        (inj t' (mkTower (is' ++ [pt]))) →
      SetTheory.app (SetTheory.app
          (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
            (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
              rss tlss Eiss' Fss₀ Ess')) (inj t' (mkTower (is' ++ [pt])))) x
        = SetTheory.app (is'.foldl SetTheory.app (Ms.getD t' pt)) x :=
    fun t' ht' Ids' hIds' is' hfit x hx =>
      dispLaw_of hlaw0 (fun t'' ht'' => hσmot _ t'' ht'' (by omega)) hF.tag t' ht' hIds' hfit x hx
  -- the auxiliary spine, at the parameter frame's base
  have hcl0 : consList ((List.range nP).reverse.map (consList ps ρ))
      (fun j => consList ps ρ (j + nP)) = consList ps ρ := consList_range_reverse nP _
  have hfitA : SpineFit (fun j => consList ps ρ (j + nP)) ((auxRecDataAV m ψ W wB nP elimL pps Idss rss tlss Eiss' Fss₀ Ess' mems tgts cds).map (·.2.2)) ((List.range nP).reverse.map (consList ps ρ) ++ [(interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
      (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
        rss tlss Eiss' Fss₀ Ess'))] ++ Ss
      ++ [inj mm (mkTower (is ++ [pt]))] ++ [t]) := by
    rw [paramFrame_shift (V := V) (ρ := ρ) hlenPs, paramVals_consList (V := V) (ρ := ρ) hlenPs]
    exact hfitA0
  -- the arguments' values
  have hargsP : (paramBvarsAt nP (nP + (k + n + nIdxs.getD mm 0 + 1))).map (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ))))))
      = (List.range nP).reverse.map (consList ps ρ) :=
    map_paramBvarsAt_interp fun j => by
      rw [Nat.add_comm]; exact RecFrameS.apply hσshift j
  have hargsS : ((List.range n).map fun J =>
        AnnotTerm.bvar (nIdxs.getD mm 0 + 1 + n - 1 - J)).map (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))) = Ss := by
    rw [List.map_map]
    apply List.ext_getElem
    · simp [hlenSs]
    · intro i h1 h2
      have hi : i < n := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, Function.comp_def, interp_bvar]
      rw [hσminor i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  have hargvals : ((paramBvarsAt nP (nP + (k + n + nIdxs.getD mm 0 + 1)) ++
        [motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
          rss tlss Eiss' Fss₀ Ess'] ++
        ((List.range n).map fun J => AnnotTerm.bvar (nIdxs.getD mm 0 + 1 + n - 1 - J)) ++
        [tagTupleAV W mm (k + n + nIdxs.getD mm 0 + 1) Idss (idxVarsAV (nIdxs.getD mm 0) 1)] ++
        [AnnotTerm.bvar 0]).map (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ))))))) = ((List.range nP).reverse.map (consList ps ρ) ++ [(interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
      (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
        rss tlss Eiss' Fss₀ Ess'))] ++ Ss
      ++ [inj mm (mkTower (is ++ [pt]))] ++ [t]) := by
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [hargsP, hargsS, htagvals.1, interp_bvar, cons_zero]
  have hleafeq : interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ))))) ((auxRecAV m ψ ℓ W wB nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds).liftN (k + n + nIdxs.getD mm 0 + 1) 0)
      = interp V (fun j => consList ps ρ (j + nP)) (auxRecAV m ψ ℓ W wB nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds) := by
    rw [interp_liftN, hσshift]
    exact interp_closed (V := V) hyp.hclR _ _
  have hzA : ∀ d ∈ (auxRecDataAV m ψ W wB nP elimL pps Idss rss tlss Eiss' Fss₀ Ess' mems tgts cds), (ℓ = 0 ↔ d.2.1 = 0) := fun d hd => by
    rw [mem_fixRecDataAVL hd, hyp.hb]; exact hyp.hbz
  have hconc0 : ℓ = 0 → ∀ as', SpineFit (fun j => consList ps ρ (j + nP)) ((auxRecDataAV m ψ W wB nP elimL pps Idss rss tlss Eiss' Fss₀ Ess' mems tgts cds).map (·.2.2)) as' →
      interp V (consList as' (fun j => consList ps ρ (j + nP))) (recConcAV n 1) ∈ˢ (univZero : V) := by
    intro h0 as' hsp'
    have h := hyp.hauxConc _ as' hsp'
    rwa [h0, univ_zero] at h
  have hmemA := mkPisAV_fold_mem (m := ℓ) hzA hconc0 (hyp.haux (fun j => consList ps ρ (j + nP))).2 hfitA
  have hfrAll : consList ((List.range nP).reverse.map (consList ps ρ) ++ [(interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
      (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
        rss tlss Eiss' Fss₀ Ess'))] ++ Ss
      ++ [inj mm (mkTower (is ++ [pt]))] ++ [t]) (fun j => consList ps ρ (j + nP))
      = cons t (consList [inj mm (mkTower (is ++ [pt]))]
          (consList Ss (cons (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
      (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
        rss tlss Eiss' Fss₀ Ess')) (consList ps ρ)))) := by
    rw [consList_append, consList_append, consList_append, consList_append, hcl0]
    rfl
  have hconcA : interp V (consList ((List.range nP).reverse.map (consList ps ρ) ++ [(interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
      (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
        rss tlss Eiss' Fss₀ Ess'))] ++ Ss
      ++ [inj mm (mkTower (is ++ [pt]))] ++ [t]) (fun j => consList ps ρ (j + nP))) (recConcAV n 1)
      = SetTheory.app (is.foldl SetTheory.app (Ms.getD mm pt)) t := by
    rw [hfrAll, recConcAV_at (n := n) (nIdx := 1) [inj mm (mkTower (is ++ [pt]))] rfl t,
      show consList Ss (cons (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
      (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
        rss tlss Eiss' Fss₀ Ess')) (consList ps ρ)) n = (interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
      (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
        rss tlss Eiss' Fss₀ Ess')) from by
        rw [show n = 0 + Ss.length from by omega, consList_apply_add]; rfl,
      List.foldl_cons, List.foldl_nil]
    exact hlaw mm hmmk IdsM hIdsMM is hspI t ht
  have hconcPub : interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ))))) (mutualConcAV k n (nIdxs.getD mm 0) mm)
      = SetTheory.app (is.foldl SetTheory.app (Ms.getD mm pt)) t := by
    unfold mutualConcAV
    rw [interp_app, interp_mkAppN_foldl, hidxvars, interp_bvar, interp_bvar, cons_zero,
      hσmot _ mm hmmk (by omega)]
  rw [hconcPub]
  rw [hconcA] at hmemA
  refine ⟨⟨?_, ?_⟩, ?_, fun h0 => ?_⟩
  · unfold mutualRecBodyAV
    refine (mkAppN_wellDenoted_of_chain ?_ ?_ ?_).1
    · rw [WellDenoted_liftN, hσshift]; exact (hyp.haux _).1.1
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp ha with ha | ha
          · rcases List.mem_append.mp ha with ha | ha
            · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
            · rw [List.mem_singleton] at ha; subst ha; exact hdispOk
          · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
        · rw [List.mem_singleton] at ha; subst ha; exact htagvals.2
      · rw [List.mem_singleton] at ha; subst ha; trivial
    · rw [hargvals, hleafeq]
      exact appChainOk_of_mkPisAV' (m := ℓ) hzA hconc0 (hyp.haux (fun j => consList ps ρ (j + nP))).2 hfitA
  · unfold mutualRecBodyAV
    refine AnnotValid_mkAppN ?_ ?_
    · rw [AnnotValid_liftN, hσshift]; exact (hyp.haux _).1.2
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp ha with ha | ha
          · rcases List.mem_append.mp ha with ha | ha
            · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
            · rw [List.mem_singleton] at ha; subst ha
              exact motDispAV_validV hσshift hF.tag hyp.hk hF.tagValid hF.auxValid
          · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
        · rw [List.mem_singleton] at ha; subst ha
          exact tagTupleAV_validV hF.tagValid hIdsMM hσshift
            (fun E hE => by obtain ⟨l, -, rfl⟩ := List.mem_map.mp hE; trivial)
      · rw [List.mem_singleton] at ha; subst ha; trivial
  · unfold mutualRecBodyAV
    rw [interp_mkAppN_foldl, hargvals, hleafeq]
    exact hmemA
  · have h := hyp.hauxConc (fun j => consList ps ρ (j + nP)) ((List.range nP).reverse.map (consList ps ρ) ++ [(interp V (cons t (consList is (consList Ss (consList Ms (consList ps ρ)))))
      (motDispAV ℓ W wB (k + n + nIdxs.getD mm 0 + 1) (n + nIdxs.getD mm 0 + 1) k Idss
        rss tlss Eiss' Fss₀ Ess'))] ++ Ss
      ++ [inj mm (mkTower (is ++ [pt]))] ++ [t]) hfitA
    rw [hconcA, hyp.hbz.mpr h0, univ_zero] at h
    exact h

/-- **The member recursor leaf's facts**: member `mm`'s recursor leaf is
`WellDenotedV` at every frame and inhabits the reading of its STORED
type. -/
theorem mutualRecLeafFacts
    (hyp : MutualLeafHyp V m ψ elimL ℓ W wB nP s b k n Ls nIdxs pps ipss Idss rss tlss
      EissO Eiss' FssR Fss₀ Ess' mems tgts cds mm) (ρ : Nat → V) :
    WellDenotedV V ρ
        (mutualRecAVI m ψ ℓ W wB nP s b elimL Ls nIdxs pps ipss Idss rss tlss Eiss' FssR Fss₀
          Ess' mems tgts cds mm) ∧
      interp V ρ
          (mutualRecAVI m ψ ℓ W wB nP s b elimL Ls nIdxs pps ipss Idss rss tlss Eiss' FssR Fss₀
            Ess' mems tgts cds mm)
        ∈ˢ interp V ρ
            (mkPisAV (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm)
              (mutualConcAV k n (nIdxs.getD mm 0) mm)) := by
  have hbits : ∀ d ∈ mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm,
      (b = 0 ↔ d.2.1 = 0) := by
    intro d hd
    rw [mem_mutualRecDataAV hd, hyp.hb]
  have hunder : ∀ ρ' : Nat → V, UnderTowerOk b ρ'
      (mutualRecBodyAV ℓ W wB nP k n (nIdxs.getD mm 0) mm Idss rss tlss Eiss' Fss₀ Ess'
        (auxRecAV m ψ ℓ W wB nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds))
      (mutualConcAV k n (nIdxs.getD mm 0) mm)
      (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm) := by
    intro ρ'
    refine underTowerOk_of_walk
      (domsWalk_of_fieldsOkB (WellDenoted_mkPisAV_inv (hyp.hstore ρ').1).1) fun as hsp => ?_
    obtain ⟨⟨hok, -⟩, hmem, h0⟩ := mutualRecBody_facts hyp ρ' as hsp
    exact ⟨hok, hmem, h0⟩
  have hvalid : ∀ ρ' : Nat → V, UnderTowerValid ρ'
      (mutualRecBodyAV ℓ W wB nP k n (nIdxs.getD mm 0) mm Idss rss tlss Eiss' Fss₀ Ess'
        (auxRecAV m ψ ℓ W wB nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds))
      (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm) := by
    intro ρ'
    refine underTowerValid_of_fieldsValid (AnnotValid_mkPisAV_inv (hyp.hstore ρ').2).1
      fun as hsp => (mutualRecBody_facts hyp ρ' as hsp).1.2
  show WellDenotedV V ρ (mkLamsC b _ _) ∧ interp V ρ (mkLamsC b _ _) ∈ˢ _
  rw [hyp.hLs, hyp.hn]
  exact ⟨⟨mkLamsC_wellDenoted hbits (hunder ρ), mkLamsC_validV (hvalid ρ)⟩,
    mkLamsC_mem hbits (hunder ρ)⟩

end Facts

end ConLeche.Model
