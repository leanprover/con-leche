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

end ConLeche.Model
