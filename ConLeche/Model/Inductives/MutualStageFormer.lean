module

public import ConLeche.Model.Inductives.FixStageFormer
public import ConLeche.Model.Inductives.MutualChains
public import ConLeche.Model.Inductives.MutualRecPre2
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.MutualWF
public section

/-!
# The mutual block's former stage (task #278, M2.5b)

`stageMutualFormer`: the P step at ONE member's cons — the member's
leaf `mutualTyAVI` (`Semantics/Tower/MutualLeafI.lean`) consed with the
block's EMPTY capability record, `stageFixFormer` with the fibre leaf
in place of the fixpoint one.  `mutualLeafWalks` is `fixLeafWalks` at
that leaf: the member's hereditary premise (`ParamsOkMI`) and the
tower's validity are walked from the former's binder data
(`FormerData`) down to the frame below the parameters and the member's
index variables, where the block's chain facts at the parameter frame
(the tag `TagOk`, the auxiliary family's `FixChainsOkI`, the chains'
validity) are the base.

`stageMutualFormers` folds it over the formers' loop
(`mutualFormers`): `k` conses, member `t`'s leaf at tag `t`, with the
members' binder data and the block's chain data given.  Its two
conclusions are the ones the constructor and recursor stages read: the
positional leaf equation at every member, and the agreement off the
block.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps MutualFormerA)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The member leaf's closedness, grading and validity -/

omit [SetTheory V] in
/-- **The member's leaf is closed**: its body is the auxiliary family
(closed at the parameters) applied to the auxiliary tupler at the
member's tagged tuple of its own index variables. -/
theorem mutualTyAVI_below {W w nP nIdx t : Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)}
    (hp : DomsBelow 0 pps) (hlen : pps.length = nP + nIdx)
    (hIds : ∀ Ids ∈ Idss, FieldsBelow nP Ids)
    (hchains : ∀ chain ∈ chainsXI W (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess',
      FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow 0 (mutualTyAVI W w pps nIdx Idss rss tlss Eiss' Fss₀ Ess' t).erase := by
  have hauxB : FieldsBelow nP (auxIds W Idss) := ⟨tagTyAV_below hIds, trivial⟩
  unfold mutualTyAVI
  refine mkLamsAV_below hp.mapC ?_
  rw [List.length_map, hlen, Nat.zero_add]
  simp only [AnnotTerm.erase_app, Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · rw [AnnotTerm.erase_liftN]
    have := VExprAux.bvarsBelow_liftN nIdx
      (auxBodyAV W w Idss rss tlss Eiss' Fss₀ Ess').erase nP 0
      (fixBodyAVI_below (w := w) (nIdx := 1) hauxB hchains)
    exact this
  · rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN ?_ ?_
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN nIdx _ _ _ (tuplerAV_below hauxB)
    · intro a ha
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_singleton] at hE
      subst hE
      refine tagTupleAV_below hIds ?_
      intro E hE
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hE
      rw [List.mem_range] at hj
      show Term.bvarsBelow (nP + nIdx) (Term.bvar (nIdx - 1 - j))
      show nIdx - 1 - j < nP + nIdx
      omega

/-- **The auxiliary family's functor is bit-valid** at the parameter
frame — `fixBody_validV`'s function half at the tag telescope, read
off a fitting one-element index spine. -/
theorem auxBodyAV_validV {W w : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss₀ Ess' : List (List AnnotTerm)}
    (hI : IdxOk W ρp (auxIds W Idss)) (hIV : FieldsValid ρp (auxIds W Idss))
    (hchains : ∀ X, X ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss)) →
      ∀ t, t ∈ˢ idxSet W ρp (auxIds W Idss) →
      SumFieldsValid (cons t (cons X ρp))
        (chainsXI W (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess'))
    {z : V} (hsp : SpineFit ρp (auxIds W Idss) [z]) :
    AnnotValid V ρp (auxBodyAV W w Idss rss tlss Eiss' Fss₀ Ess') := by
  have h := fixBody_validV (u := W) (w := w) (Ids := auxIds W Idss) (rss := rss)
    (tlss := tlss) (Eiss := Eiss') (Fss := Fss₀) (Ess := Ess') hI hIV hchains hsp
  rw [AnnotValid_app] at h
  have hf := h.1
  rw [AnnotValid_liftN] at hf
  have hsh : shiftE (auxIds W Idss).length 0 (consList [z] ρp) = ρp := by
    rw [show (auxIds W Idss).length = [z].length from rfl]
    exact shiftE_consList _ ρp
  rw [hsh] at hf
  exact hf


/-! ## The member leaf's walks -/

/-- **The member leaf's body** at its own frame (the parameters and
member `t`'s index variables): the auxiliary family applied to the
1-tuple of the member's tagged index tuple. -/
@[expose] def mutualLeafBodyAV (W w nIdx : Nat) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss₀ Ess' : List (List AnnotTerm)) (t : Nat) :
    AnnotTerm :=
  .app ((auxBodyAV W w Idss rss tlss Eiss' Fss₀ Ess').liftN nIdx 0)
    (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN nIdx 0)
      [tagTupleAV W t nIdx Idss (teleVarsAV nIdx)])

omit [SetTheory V] in
/-- The member's leaf is the constant-bit λ-tower over its binder data
with that body. -/
theorem mutualTyAVI_eq_mkLamsC (W w : Nat) (pps : List (Nat × Nat × AnnotTerm)) (nIdx : Nat)
    (Idss : List (List AnnotTerm)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss₀ Ess' : List (List AnnotTerm)) (t : Nat) :
    mutualTyAVI W w pps nIdx Idss rss tlss Eiss' Fss₀ Ess' t
      = mkLamsC (w + 1) pps (mutualLeafBodyAV W w nIdx Idss rss tlss Eiss' Fss₀ Ess' t) := by
  rfl

/-- **The member leaf's P currency**: graded at the hereditary premise
(`ParamsOkMI`), valid under the tower. -/
theorem mutualTyAVI_wellDenotedV {W w nIdx t : Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)} {ρ : Nat → V}
    (hok : ParamsOkMI W w ρ nIdx Idss rss tlss Eiss' Fss₀ Ess' t pps)
    (hval : UnderTowerValid ρ (mutualLeafBodyAV W w nIdx Idss rss tlss Eiss' Fss₀ Ess' t) pps) :
    WellDenotedV V ρ (mutualTyAVI W w pps nIdx Idss rss tlss Eiss' Fss₀ Ess' t) :=
  ⟨mutualTyAVI_wellDenoted hok,
    by rw [mutualTyAVI_eq_mkLamsC]; exact mkLamsC_validV (m := w + 1) hval⟩

/-- **The block's chain facts at member `t`'s parameter frame**: the
tag graded and bit-valid, the auxiliary family's chains graded and
bit-valid, and member `t`'s own index telescope the `t`-th entry of the
block's index telescopes.  Everything here is about the ANNOTATED data
alone — no carrier occurs — so the caller supplies it from the
constructors' readings, after the formers' loop. -/
@[expose] def MemberChainsOk (V : Type w) [SetTheory V] (nP t : Nat) (resSort : Level)
    (W : (Name → Nat) → Nat) (Idss : (Name → Nat) → List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : (Name → Nat) → List (List (List AnnotTerm)))
    (Fss₀ Ess' : (Name → Nat) → List (List AnnotTerm))
    (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)) : Prop :=
  (∀ ψ : Name → Nat, (Idss ψ)[t]? = some (((pps ψ).drop nP).map (·.2.2))) ∧
  ∀ (ψ : Name → Nat) (ρp : Nat → V),
    Sat V (((pps ψ).take nP).map (·.2.2)).reverse ρp →
    TagOk (W ψ) ρp (Idss ψ) ∧
    (∀ Ids ∈ Idss ψ, FieldsValid ρp Ids) ∧
    FixChainsOkI (W ψ) (resSort.eval ψ) ρp (auxIds (W ψ) (Idss ψ)) 1 rss (tlss ψ) (Eiss' ψ)
      (Fss₀ ψ) (Ess' ψ) ∧
    (∀ X, X ∈ˢ lfpFamSpace V (resSort.eval ψ) (idxSet (W ψ) ρp (auxIds (W ψ) (Idss ψ))) →
      ∀ τ, τ ∈ˢ idxSet (W ψ) ρp (auxIds (W ψ) (Idss ψ)) →
      SumFieldsValid (cons τ (cons X ρp))
        (chainsXI (W ψ) (auxIds (W ψ) (Idss ψ)) 1 rss (tlss ψ) (Eiss' ψ) (Fss₀ ψ) (Ess' ψ)))

/-- **The member leaf's two hereditary premises**, from the former's
binder data and the block's chain facts at the parameter frame
(`fixLeafWalks` at the fibre leaf). -/
theorem mutualLeafWalks {m : EnvModel V env} {cvT : ConstantVal} {nP nIdx t : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {lvls : (Name → Nat) → List Nat}
    (hFD : FormerData m cvT (nP + nIdx) resSort pps lvls)
    {W : (Name → Nat) → Nat} {Idss : (Name → Nat) → List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : (Name → Nat) → List (List (List AnnotTerm))}
    {Fss₀ Ess' : (Name → Nat) → List (List AnnotTerm)}
    (hC : MemberChainsOk V nP t resSort W Idss rss tlss Eiss' Fss₀ Ess' pps)
    (ψ : Name → Nat) (ρ : Nat → V) :
    ParamsOkMI (W ψ) (resSort.eval ψ) ρ nIdx (Idss ψ) rss (tlss ψ) (Eiss' ψ) (Fss₀ ψ) (Ess' ψ) t
        (pps ψ) ∧
      UnderTowerValid ρ
        (mutualLeafBodyAV (W ψ) (resSort.eval ψ) nIdx (Idss ψ) rss (tlss ψ) (Eiss' ψ) (Fss₀ ψ)
          (Ess' ψ) t) (pps ψ) := by
  obtain ⟨hIdsT, hfacts⟩ := hC
  have hst := stripPisAV_mkPisAV (pps ψ) (.sort (resSort.eval ψ))
  rw [hFD.len ψ] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ _ => hFD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hlenΓ : (((pps ψ).map (·.2.2)).reverse).length = nP + nIdx := by simp [hFD.len ψ]
  have hent : ∀ i, i < nP + nIdx → ∃ p, (pps ψ)[i]? = some p ∧
      p.2.2 = (((pps ψ).map (·.2.2)).reverse).getD (nP + nIdx - 1 - i) default := by
    intro i hi
    have hil : i < (pps ψ).length := by rw [hFD.len ψ]; exact hi
    refine ⟨(pps ψ)[i], List.getElem?_eq_getElem hil, ?_⟩
    rw [getD_reverse_of_peel (hFD.len ψ) hi (List.getElem?_eq_getElem hil)]
  have hΓnil : (((pps ψ).map (·.2.2)).reverse).drop (nP + nIdx - 0) = [] := by
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlenΓ]; exact Nat.le_refl _)]
  have hIdsLen : ((((pps ψ).drop nP).map (·.2.2))).length = nIdx := by simp [hFD.len ψ]
  -- the base facts at a frame satisfying the whole telescope
  have hbase : ∀ ρ : Nat → V, Sat V (((pps ψ).map (·.2.2)).reverse) ρ →
      MutualBaseI (W ψ) (resSort.eval ψ) ρ nIdx (Idss ψ) rss (tlss ψ) (Eiss' ψ) (Fss₀ ψ)
        (Ess' ψ) t ∧
      AnnotValid V ρ
        (mutualLeafBodyAV (W ψ) (resSort.eval ψ) nIdx (Idss ψ) rss (tlss ψ) (Eiss' ψ) (Fss₀ ψ)
          (Ess' ψ) t) := by
    intro ρ hρ
    rw [reverse_map_take_drop (pps ψ) nP] at hρ
    have hρp : Sat V (((pps ψ).take nP).map (·.2.2)).reverse (fun j => ρ (j + nIdx)) := by
      have := Sat_drop hρ nIdx
      rwa [List.drop_append_of_le_length (by rw [List.length_reverse, hIdsLen]; exact Nat.le_refl _),
        List.drop_eq_nil_of_le (by rw [List.length_reverse, hIdsLen]; exact Nat.le_refl _),
        List.nil_append] at this
    have hsh : shiftE nIdx 0 ρ = fun j => ρ (j + nIdx) := by rw [shiftE_zero]
    have hspI := spineFit_of_sat (Δ₀ := (((pps ψ).take nP).map (·.2.2)).reverse)
      (Ds := ((pps ψ).drop nP).map (·.2.2)) hρ
    rw [hIdsLen, ← frameIdx_eq_reverse_map] at hspI
    obtain ⟨hTagρ, hVρ, hFixρ, hXVρ⟩ := hfacts ψ _ hρp
    have hI : IdxOk (W ψ) (fun j => ρ (j + nIdx)) (auxIds (W ψ) (Idss ψ)) := auxIds_idxOk hTagρ
    have hIV : FieldsValid (fun j => ρ (j + nIdx)) (auxIds (W ψ) (Idss ψ)) :=
      auxIds_fieldsValid hVρ
    refine ⟨⟨by rw [hsh]; exact hTagρ, by rw [hsh]; exact hFixρ,
      _, hIdsT ψ, hIdsLen, by rw [hsh]; exact hspI⟩, ?_⟩
    have hsp1 : SpineFit (fun j => ρ (j + nIdx)) (auxIds (W ψ) (Idss ψ))
        [inj t (mkTower (frameIdx nIdx ρ ++ [pt]))] := by
      refine ⟨?_, trivial⟩
      rw [(tagTyAV_facts hTagρ).1]
      exact tagTuple_mem hTagρ (hIdsT ψ) hspI
    rw [mutualLeafBodyAV, AnnotValid_app]
    refine ⟨?_, ?_⟩
    · rw [AnnotValid_liftN, hsh]
      exact auxBodyAV_validV hI hIV hXVρ hsp1
    · refine mkAppN_validV ?_ ?_
      · rw [AnnotValid_liftN, hsh]
        exact tuplerAV_validV hI hIV
      · intro a ha
        rw [List.mem_singleton] at ha
        subst ha
        refine tagTupleAV_validV hVρ (hIdsT ψ) hsh ?_
        intro E hE
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hE
        trivial
  constructor
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => ParamsOkMI (W ψ) (resSort.eval ψ) ρ nIdx (Idss ψ) rss (tlss ψ) (Eiss' ψ)
        (Fss₀ ψ) (Ess' ψ) t ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => (hbase ρ hρ).1)
      (fun ρ d ds hd hok hrec => ⟨hFD.bits ψ d hd, hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => UnderTowerValid ρ
        (mutualLeafBodyAV (W ψ) (resSort.eval ψ) nIdx (Idss ψ) rss (tlss ψ) (Eiss' ψ) (Fss₀ ψ)
          (Ess' ψ) t) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => (hbase ρ hρ).2)
      (fun ρ d ds hd hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw

end ConLeche.Model
