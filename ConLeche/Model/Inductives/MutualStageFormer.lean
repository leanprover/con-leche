module

public import ConLeche.Model.Inductives.FixStageFormer
public import ConLeche.Model.Inductives.MutualChains
import ConLeche.Model.Inductives.MutualLeafBelow
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


/-! ## Closedness of the tagged tuple

`tagTuplerAV_below`/`tagTupleAV_below` are proved in
`Model/Inductives/MutualRecPre2.lean` too, but that module and
`MutualChains.lean` both declare `tagTupleAV_validVC` and so cannot be
imported together; until that duplicate is resolved the two closedness
lemmas are restated here under their own names. -/

omit [SetTheory V] in
/-- Member `m`'s tag tupler is bounded at the parameters. -/
theorem tagTuplerAV_belowM {W nP m : Nat} {Idss : List (List AnnotTerm)}
    (h : ∀ Ids ∈ Idss, FieldsBelow nP Ids) :
    Term.bvarsBelow nP (tagTuplerAV W m Idss).erase := by
  have hIds : FieldsBelow nP (Idss.getD m []) := by
    rw [List.getD_eq_getElem?_getD]
    cases hm : Idss[m]? with
    | none => exact trivial
    | some Ids => exact h Ids (List.mem_of_getElem? hm)
  unfold tagTuplerAV
  refine sumMkAV_below (nP := 0) (domsBelow_tuplerData hIds) hIds
    (fun Fs' hFs' => uChains_below h Fs' hFs') ?_
  simp [tuplerData]

omit [SetTheory V] in
/-- A tagged tuple is closed at the frame its index expressions are. -/
theorem tagTupleAV_belowM {W nP m d : Nat} {Idss : List (List AnnotTerm)} {Es : List AnnotTerm}
    (h : ∀ Ids ∈ Idss, FieldsBelow nP Ids)
    (hEs : ∀ E ∈ Es, Term.bvarsBelow (nP + d) E.erase) :
    Term.bvarsBelow (nP + d) (tagTupleAV W m d Idss Es).erase := by
  unfold tagTupleAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN ?_ ?_
  · rw [AnnotTerm.erase_liftN]
    exact VExprAux.bvarsBelow_liftN d _ _ _ (tagTuplerAV_belowM h)
  · intro a ha
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
    exact hEs E hE

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
      refine tagTupleAV_belowM hIds ?_
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
    (hFD : FormerData m cvT (nP + nIdx) resSort pps)
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
        [inj t (mkTower (ConLeche.Semantics.frameIdx nIdx ρ ++ [pt]))] := by
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
        refine tagTupleAV_validVC hVρ (hIdsT ψ) hsh ?_
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

/-! ## The member's cons -/

/-- **What one member's cons needs of its constant check, AT THE
CARRIER IT IS CONSED ONTO.**  The mutual stage checks EVERY former at
the pre-block environment (official's `check_inductive_types` runs
before `declare_inductive_types`), so these facts are established
there once and travel forward across the earlier members' conses
(`MemberConsOk.cons`) instead of being re-derived at each of them. -/
structure MemberConsOk (env : Env) (cvTa : ConstantVal) : Prop where
  /-- the member's name is fresh here -/
  fresh : env.find? cvTa.name = none
  /-- … and is neither a reserved basis name … -/
  nres : ConLeche.reservedBasisNames.contains cvTa.name = false
  /-- … nor a projection name -/
  pshape : cvTa.name.isProjFnShape = false
  /-- the checked type is closed, … -/
  noFvar : cvTa.type.hasFvar = false
  /-- … level-defined, … -/
  lpsOk : cvTa.type.allLevelParamsDefined cvTa.levelParams = true
  /-- … resolving here … -/
  resolve : cvTa.type.constsResolve env = true
  /-- … and bounded -/
  bounded : cvTa.type.looseBVarsBounded 0 = true

/-- The constant check establishes it. -/
theorem MemberConsOk.ofCheck {F : Nat} {cvT cvTa : ConstantVal}
    (h : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cvT = .ok cvTa) :
    MemberConsOk env cvTa := by
  obtain ⟨hfind, hnres, hpshape, -, -, -, type', -, -, -, -, htr', -, -, hty⟩ :=
    ConLeche.checkConstantVal_inv h
  have hname : cvTa.name = cvT.name := by rw [hty]
  obtain ⟨htf, htp, htr, htb⟩ := ConLeche.checkConstantVal_typeWF h
  exact ⟨by rw [hname]; exact hfind, by rw [hname]; exact hnres,
    by rw [hname]; exact hpshape, htf, htp, htr, htb⟩

/-- … and it travels across a cons of a DIFFERENT name (freshness by
the name, resolution by monotonicity). -/
theorem MemberConsOk.cons {c₀ : ConstantInfo} {cvTa : ConstantVal}
    (hne : c₀.name ≠ cvTa.name) (h : MemberConsOk env cvTa) :
    MemberConsOk ⟨c₀ :: env.consts⟩ cvTa := by
  refine ⟨?_, h.nres, h.pshape, h.noFvar, h.lpsOk,
    Expr.constsResolve_mono h.resolve, h.bounded⟩
  rw [ConLeche.Env.find?_cons]
  split
  · next hb => exact absurd hb hne
  · exact h.fresh

/-- **The P step at one member's cons**: `stageFixFormer` with the
member's fibre leaf `mutualTyAVI` and the block's EMPTY capability
record (K never fires on a mutual block; η and unit-likeness at a
recursion-free block's structure-like members are a later task), so
the block's own capability laws are vacuous. -/
theorem stageMutualFormer (mp : EnvModelM V μ env)
    (hE₀ : ConLeche.EtaFamiliesClosed env)
    {cvTa : ConstantVal} {nP nIdx t : Nat} {resSort : Level}
    (hok : MemberConsOk env cvTa)
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort pps)
    {W : (Name → Nat) → Nat} {Idss : (Name → Nat) → List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : (Name → Nat) → List (List (List AnnotTerm))}
    {Fss₀ Ess' : (Name → Nat) → List (List AnnotTerm)}
    (hParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) →
      W ψ₁ = W ψ₂ ∧ Idss ψ₁ = Idss ψ₂ ∧ tlss ψ₁ = tlss ψ₂ ∧ Eiss' ψ₁ = Eiss' ψ₂ ∧
        Fss₀ ψ₁ = Fss₀ ψ₂ ∧ Ess' ψ₁ = Ess' ψ₂)
    (hIdsBelow : ∀ ψ : Name → Nat, ∀ Ids ∈ Idss ψ, FieldsBelow nP Ids)
    (hbelow : ∀ ψ : Name → Nat, ∀ chain ∈ chainsXI (W ψ) (auxIds (W ψ) (Idss ψ)) 1 rss (tlss ψ)
      (Eiss' ψ) (Fss₀ ψ) (Ess' ψ), FieldsBelow (nP + 2) chain)
    (hC : MemberChainsOk V nP t resSort W Idss rss tlss Eiss' Fss₀ Ess' pps) :
    ∃ mp' : EnvModelM V μ ⟨.indInfo cvTa {} :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvTa.name
        (fun ψ => mutualTyAVI (W ψ) (resSort.eval ψ) (pps ψ) nIdx (Idss ψ) rss (tlss ψ) (Eiss' ψ)
          (Fss₀ ψ) (Ess' ψ) t) := by
  have hfresh : env.find? cvTa.name = none := hok.fresh
  have hcb : ConstsBound env cvTa.type := constsBound_of_constsResolve _ hok.resolve
  have hicw : ConLeche.IndCapsWF (.indInfo cvTa {}) :=
    ConLeche.IndCapsWF.of_caps (fun hu => absurd hu (by decide)) (fun he => absurd he (by decide))
  have hwfI : ConLeche.EnvWF ⟨.indInfo cvTa {} :: env.consts⟩ :=
    ConLeche.EnvWF.cons mp.base2.wf (ConLeche.structConstWF hok.noFvar hok.lpsOk
      (Expr.constsResolve_mono hok.resolve) hok.bounded
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
      (by intro tbl hh; exact ConstantInfo.noConfusion hh) hicw)
  let A : (Name → Nat) → AnnotTerm := fun ψ =>
    mutualTyAVI (W ψ) (resSort.eval ψ) (pps ψ) nIdx (Idss ψ) rss (tlss ψ) (Eiss' ψ) (Fss₀ ψ)
      (Ess' ψ) t
  have hAbelow : ∀ ψ, Term.bvarsBelow 0 (A ψ).erase := fun ψ =>
    mutualTyAVI_below (hFD.below ψ) (hFD.len ψ) (hIdsBelow ψ) (hbelow ψ)
  have hwalks := mutualLeafWalks hFD hC
  have hreadI : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvTa.name A)
        ⟨.indInfo cvTa {} :: env.consts⟩ ψ 0 cvTa.type
        = some (mkPisAV (pps ψ) (.sort (resSort.eval ψ))) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .indInfo cvTa {}) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hFD.read ψ)
  have hnresI : ConLeche.reservedBasisNames.contains
      (ConstantInfo.indInfo cvTa {}).name = false := hok.nres
  have hpshapeI : (ConstantInfo.indInfo cvTa {}).name.isProjFnShape = false := hok.pshape
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .indInfo cvTa {})
    (A := A) hfresh hnresI (Or.inl ⟨_, _, rfl⟩)
    (ConsHead.ofFresh hwfI (fun ψ => hAbelow ψ) hnresI
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ψ₁ ψ₂ hφ
    obtain ⟨hp, hw⟩ := hFD.params ψ₁ ψ₂ hφ
    obtain ⟨hu, hIdss, htlss, hEiss, hFss, hEss⟩ := hParams ψ₁ ψ₂ hφ
    show mutualTyAVI _ _ _ _ _ _ _ _ _ _ _ = mutualTyAVI _ _ _ _ _ _ _ _ _ _ _
    rw [hp, hw, hu, hIdss, htlss, hEiss, hFss, hEss]
  · exact fun ψ ρ => mutualTyAVI_wellDenoted (hwalks ψ ρ).1
  · exact fun ψ ρ => (mutualTyAVI_wellDenotedV (hwalks ψ ρ).1 (hwalks ψ ρ).2).2
  · exact fun ψ => ⟨_, hreadI ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact hFD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact mutualTyAVI_mem (hwalks ψ ρ).1
  · intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .indInfo cvTa {})
      (A := A) (T := cvTa.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeI
      (Or.inl ⟨cvTa, {}, rfl, rfl⟩)
      (fun T' cvT' caps' hf _ hres hcape => hE₀ T' cvT' caps' hf hcape hres)
      m₂ hac ?_
    intro cvT' caps' hf _
    have hself := ConLeche.Env.find?_cons_self (ConstantInfo.indInfo cvTa {}) env
    obtain ⟨rfl, rfl⟩ :=
      ConstantInfo.indInfo.inj (Option.some.inj (hself.symm.trans hf))
    exact ⟨fun he _ => absurd he (by decide), fun hu => absurd hu (by decide)⟩

/-! ## The formers' loop -/

/-- **The formers' loop, folded** (the induction over the remaining
members; `idxs i` is the block position of the loop's `i`-th member).
The loop is over the CHECKED formers, not the declared ones: every one
of them was checked at the pre-block environment, and the induction
carries that forward across the earlier members' conses. -/
theorem stageMutualFormersGo {nP : Nat} {resSort : Level} {lps : List Name}
    {W : (Name → Nat) → Nat} {Idss : (Name → Nat) → List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : (Name → Nat) → List (List (List AnnotTerm))}
    {Fss₀ Ess' : (Name → Nat) → List (List AnnotTerm)}
    {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      W ψ₁ = W ψ₂ ∧ Idss ψ₁ = Idss ψ₂ ∧ tlss ψ₁ = tlss ψ₂ ∧ Eiss' ψ₁ = Eiss' ψ₂ ∧
        Fss₀ ψ₁ = Fss₀ ψ₂ ∧ Ess' ψ₁ = Ess' ψ₂)
    (hIdsBelow : ∀ ψ : Name → Nat, ∀ Ids ∈ Idss ψ, FieldsBelow nP Ids)
    (hchainBelow : ∀ ψ : Name → Nat, ∀ chain ∈ chainsXI (W ψ) (auxIds (W ψ) (Idss ψ)) 1 rss
      (tlss ψ) (Eiss' ψ) (Fss₀ ψ) (Ess' ψ), FieldsBelow (nP + 2) chain) :
    ∀ (fs : List MutualFormerA) (idxs : Nat → Nat) (env' : Env)
      (mp' : EnvModelM V μ env'),
      ConLeche.EtaFamiliesClosed env' →
      (∀ f ∈ fs, MemberConsOk env' f.cvTa) →
      (fs.map (fun f => f.cvTa.name)).Nodup →
      (∀ (i : Nat) (f : MutualFormerA), fs[i]? = some f →
        f.cvTa.levelParams = lps ∧
        FormerData mp'.base2 f.cvTa (nP + f.nIdx) resSort (ppsF (idxs i)) ∧
        MemberChainsOk V nP (idxs i) resSort W Idss rss tlss Eiss' Fss₀ Ess' (ppsF (idxs i))) →
      ∃ mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fs env'),
        (∀ (i : Nat) (f : MutualFormerA), fs[i]? = some f →
          mp₁.base2.acval f.cvTa.name
            = fun ψ => mutualTyAVI (W ψ) (resSort.eval ψ) (ppsF (idxs i) ψ) f.nIdx (Idss ψ) rss
                (tlss ψ) (Eiss' ψ) (Fss₀ ψ) (Ess' ψ) (idxs i)) ∧
        (∀ n : Name,
          (∀ (i : Nat) (f : MutualFormerA), fs[i]? = some f → n ≠ f.cvTa.name) →
          mp₁.base2.acval n = mp'.base2.acval n) := by
  intro fs
  induction fs with
  | nil =>
    intro idxs env' mp' _ _ _ _
    exact ⟨mp', fun i f hf => by simp at hf, fun _ _ => rfl⟩
  | cons f₁ rest ih =>
    intro idxs env' mp' hE hcons hnd hmem
    obtain ⟨cvTa, nIdx, s⟩ := f₁
    obtain ⟨hlps₀, hFD₀, hC₀⟩ := hmem 0 ⟨cvTa, nIdx, s⟩ rfl
    have hok₀ : MemberConsOk env' cvTa := hcons ⟨cvTa, nIdx, s⟩ List.mem_cons_self
    have hfresh : env'.find? cvTa.name = none := hok₀.fresh
    have hcb₀ : ConstsBound env' cvTa.type :=
      constsBound_of_constsResolve _ hok₀.resolve
    -- member 0's name differs from every later member's (the block's
    -- shape guard, `b.blockNames.Nodup`)
    rw [List.map_cons, List.nodup_cons] at hnd
    have hne₀ : ∀ (i : Nat) (f : MutualFormerA), rest[i]? = some f → cvTa.name ≠ f.cvTa.name := by
      intro i f hf hh
      exact hnd.1 (hh ▸ List.mem_map_of_mem (List.mem_of_getElem? hf))
    obtain ⟨mpI, hacI⟩ := stageMutualFormer mp' hE hok₀ hFD₀
      (fun ψ₁ ψ₂ hφ => hParams ψ₁ ψ₂ (by rw [← hlps₀]; exact hφ)) hIdsBelow hchainBelow hC₀
    have hE' : ConLeche.EtaFamiliesClosed ⟨.indInfo cvTa {} :: env'.consts⟩ :=
      ConLeche.EtaFamiliesClosed.cons_nonind hE hfresh (fun cv'' caps heq he => by
        obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj heq
        exact absurd he (by decide))
    -- the later members' data cross the cons
    obtain ⟨mp₁, hpos, hoff⟩ := ih (fun i => idxs (i + 1)) _ mpI hE' (by
      intro f hf
      refine (hcons f (List.mem_cons_of_mem _ hf)).cons (c₀ := .indInfo cvTa {}) ?_
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hf
      exact hne₀ i f hi) hnd.2 (by
      intro i f hf
      obtain ⟨hlps, hFD, hC⟩ := hmem (i + 1) f (by simpa using hf)
      have hcb : ConstsBound env' f.cvTa.type :=
        constsBound_of_constsResolve _ (hcons f (List.mem_cons_of_mem _
          (List.mem_of_getElem? hf))).resolve
      exact ⟨hlps,
        hFD.cross (c₀ := .indInfo cvTa {}) hfresh
          (ConsCrossAt.ofNtc fun _ h => nomatch h) hcb mpI.base2 hacI, hC⟩)
    refine ⟨mp₁, ?_, ?_⟩
    · intro i f hf
      cases i with
      | zero =>
        obtain rfl : f = ⟨cvTa, nIdx, s⟩ := Option.some.inj hf.symm
        show mp₁.base2.acval cvTa.name = _
        rw [hoff cvTa.name hne₀, hacI, acvalWith_self]
      | succ i =>
        have hf' : rest[i]? = some f := by simpa using hf
        exact hpos i f hf'
    · intro n hn
      rw [hoff n (fun i f hf => hn (i + 1) f (by simpa using hf)), hacI,
        acvalWith_ne (hn 0 ⟨cvTa, nIdx, s⟩ rfl)]

/-- **The formers' stage of the mutual install**: the block's `k`
members consed, member `t`'s leaf the fibre `mutualTyAVI … t` of the
one auxiliary family.  The members' binder data `ppsF` and
the block's chain data are given; the chain facts are stated per
member, at that member's parameter frame, about the annotated data
alone — the cross-member parameter identification
(`mutualCrossChecks`) is therefore not consumed here and stays with
the caller.  Since the stage checks every former at the PRE-BLOCK
environment, the per-member hypotheses are stated at `mp`/`env`
outright (`ConstsBound` is no longer among them: it is the constant
check's own `constsResolve`), and the members' distinctness — the
block's shape guard `b.blockNames.Nodup` — is what carries each
member's freshness across the earlier members' conses.  The conclusion
is the positional leaf equation plus the agreement off the block. -/
theorem stageMutualFormers {F nP : Nat} {resSort : Level} {lps : List Name}
    {W : (Name → Nat) → Nat} {Idss : (Name → Nat) → List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : (Name → Nat) → List (List (List AnnotTerm))}
    {Fss₀ Ess' : (Name → Nat) → List (List AnnotTerm)}
    {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      W ψ₁ = W ψ₂ ∧ Idss ψ₁ = Idss ψ₂ ∧ tlss ψ₁ = tlss ψ₂ ∧ Eiss' ψ₁ = Eiss' ψ₂ ∧
        Fss₀ ψ₁ = Fss₀ ψ₂ ∧ Ess' ψ₁ = Ess' ψ₂)
    (hIdsBelow : ∀ ψ : Name → Nat, ∀ Ids ∈ Idss ψ, FieldsBelow nP Ids)
    (hchainBelow : ∀ ψ : Name → Nat, ∀ chain ∈ chainsXI (W ψ) (auxIds (W ψ) (Idss ψ)) 1 rss
      (tlss ψ) (Eiss' ψ) (Fss₀ ψ) (Ess' ψ), FieldsBelow (nP + 2) chain)
    {formers : List (ConstantVal × Nat)} {env₁ : Env} {fms : List MutualFormerA}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hrun : ConLeche.mutualFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) nP formers env
      = .ok (env₁, fms))
    (hnd : (fms.map (fun f => f.cvTa.name)).Nodup)
    (hmem : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      f.cvTa.levelParams = lps ∧
      FormerData mp.base2 f.cvTa (nP + f.nIdx) resSort (ppsF t) ∧
      MemberChainsOk V nP t resSort W Idss rss tlss Eiss' Fss₀ Ess' (ppsF t)) :
    ∃ mp₁ : EnvModelM V μ env₁,
      (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
        mp₁.base2.acval f.cvTa.name
          = fun ψ => mutualTyAVI (W ψ) (resSort.eval ψ) (ppsF t ψ) f.nIdx (Idss ψ) rss (tlss ψ)
              (Eiss' ψ) (Fss₀ ψ) (Ess' ψ) t) ∧
      (∀ n : Name, (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → n ≠ f.cvTa.name) →
        mp₁.base2.acval n = mp.base2.acval n) := by
  obtain ⟨hchecks, rfl⟩ := ConLeche.mutualFormers_inv hrun
  exact stageMutualFormersGo hParams hIdsBelow hchainBelow fms (fun i => i) env mp hE
    (fun f hf => MemberConsOk.ofCheck (ConLeche.mutualFormerChecks_checked hchecks f hf).choose_spec)
    hnd hmem

end ConLeche.Model
