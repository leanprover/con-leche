module

public import ConLeche.Model.Inductives.MutualChains
public import ConLeche.Model.Inductives.MutualRecData
import ConLeche.Model.Inductives.FixCtorsLoop
import ConLeche.Verify.Inductives.MutualWF
public section

/-!
# The mutual block's constructor stage (task #278, M2.5c)

`stageMutualCtor`: the P step at ONE constructor's cons — the sum
route's constructor leaf `sumMkAV (w ψ) J …` at the constructor's
GLOBAL block position `J` (the tag the auxiliary family's tagged union
carries), over the whole block's REAL field chains `FssR`.  It is
`stageCtorGen` (`Model/Inductives/SumStageCtor.lean`) with three
mutual differences:

* the residual folds to the auxiliary family's fibre at the TAGGED
  index tuple, so the index block is the ONE tag expression
  `[tagTupleAV W mem nF Idss Es]` and the restricted chains are
  `rChains 1 1` — the hereditary premise is `mutualCtorMkPre`
  (`MutualChains.lean`), which is `ctorWalksGen`'s parameter walk at
  that shape;
* the member's own parameter frame and the constructor's agree only up
  to the block's cross-member parameter identification, so the fold's
  frame hypothesis is `hiff`, exactly as on the sum route;
* the block claims NO capability (the members are consed with the empty
  record), so the capability obligation is discharged at `T :=
  cvCa.name` — a name the cons stores as a CONSTRUCTOR, so the
  block-family half of `capsOk_cons_native` is vacuous and the rest is
  `EtaFamiliesClosed`.

`stageMutualCtors` is the loop.  The kernel checks every constructor
at the formers' environment and conses them all afterwards, in block
order (`consMutualCtors`), so the loop's invariant is the sum route's
pair — `MutualConsedAt` for the constructors already consed (their
facts and their leaves) and `MutualPendingAt` for the rest (their
freshness and their data) — with `MutualCtorDataI.cross` threading a
constructor's data over each later cons.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The mutual constructor's data across a cons -/

/-- **The mutual constructor data cross a cons** whose head is neither
the constructor's own member nor any member a field targets
(`FixCtorDataI.cross` with the per-field TARGET member). -/
theorem MutualCtorDataI.cross {m : EnvModel V env} {env₀ : Env}
    {members : List (Name × Nat × Nat)} {T : Name} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)}
    {ks : List (RecFieldKind × Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : MutualCtorDataI m env₀ members T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (htgt : ∀ i, i < nF → (kindAt ks i = .recursive ∨ kindAt ks i = .reflexive) →
      mutualNameOf members (tgtAt ks i) ≠ c₀.name)
    (hat : ∀ e : Expr, ConsCrossAt c₀ e) (hcb : ConstsBound env cvC.type)
    (hcbI : ∀ e ∈ idxArgs, ConstsBound env e)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    MutualCtorDataI m₂ env₀ members T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss := by
  have hbase := h.toCtorDataI.cross hfresh hT hat hcb hcbI m₂ hac
  obtain ⟨crest, hopP, hopX⟩ := h.opens
  have hopAll : openPisAtFvars (nP + nF) cvC.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hfvs, -⟩ := openPisAtFvars_constsBound (nP + nF) hcb hopAll
  have hxcb : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x → ConstsBound env x.fvarTypeD := by
    intro i x hx
    have hb := hfvs x (List.mem_append_right _ (List.mem_of_getElem? hx))
    obtain ⟨ty, rfl⟩ := h.xIdx i x hx
    rw [constsBound_fvar] at hb
    exact hb
  exact {
    toCtorDataI := hbase
    opened := h.opened
    opens := h.opens
    ksLen := h.ksLen
    xLen := h.xLen
    pLen := h.pLen
    xIdx := h.xIdx
    pIdx := h.pIdx
    idxEq := h.idxEq
    domRead := fun ψ i x hx => by
      rw [hac]
      exact denoteMeta_cons_mono hfresh (hat _) ψ (nP + i) (hxcb i x hx) (h.domRead ψ i x hx)
    eissLen := h.eissLen
    eisRead := fun ψ i x hx hk => by
      rw [hac]
      exact DenoteMetaSpine.cons_mono hfresh hat
        (fun a ha => constsBound_getAppArgs _ (hxcb i x hx) a (List.mem_of_mem_drop ha))
        (h.eisRead ψ i x hx hk)
    eisLen := h.eisLen
    recEntry := fun ψ i hk hi => by
      rw [hac, acvalWith_ne (htgt i hi (Or.inl hk))]
      exact h.recEntry ψ i hk hi
    eissParams := h.eissParams
    eissBelow := h.eissBelow
    ordNone := h.ordNone
    tssLen := h.tssLen
    tssNone := h.tssNone
    tssBits := h.tssBits
    tssPiBits := h.tssPiBits
    tssBelow := h.tssBelow
    tssParams := h.tssParams
    reflOpen := fun ψ i x hx hk => by
      obtain ⟨afvs, body, hop, hlenTl, hdoms, hsp⟩ := h.reflOpen ψ i x hx hk
      obtain ⟨hafvs, hbody⟩ := openPisAtFvars_constsBound _ (hxcb i x hx) hop
      refine ⟨afvs, body, hop, hlenTl, fun k a hka => ?_, ?_⟩
      · rw [hac]
        refine denoteMeta_cons_mono hfresh (hat _) ψ (nP + i + k) ?_ (hdoms k a hka)
        have hb := hafvs a (List.mem_of_getElem? hka)
        obtain ⟨ty, hy⟩ := (opening_vars_at hop).2.1 k a hka
        rw [hy, constsBound_fvar] at hb
        rw [hy]
        exact hb
      · rw [hac]
        exact DenoteMetaSpine.cons_mono hfresh hat
          (fun a ha => constsBound_getAppArgs _ hbody a (List.mem_of_mem_drop ha)) hsp
    eisLenRefl := h.eisLenRefl
    reflEntry := fun ψ i hk hi => by
      rw [hac, acvalWith_ne (htgt i hi (Or.inr hk))]
      exact h.reflEntry ψ i hk hi }
/-- The constructor's data at an equivalent result sort (the block's
members' sorts are `isEquiv` to the first member's, not equal). -/
theorem MutualCtorDataI.congr_sort {m : EnvModel V env} {env₀ : Env}
    {members : List (Name × Nat × Nat)} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort resSort' : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List (RecFieldKind × Nat)} {fvsP xFvs : List Expr}
    {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : MutualCtorDataI m env₀ members T lps cvC nP nF nIdx resSort isProp large idxArgs
      ds Es srcs ks fvsP xFvs xrest Eiss tss)
    (hs : ∀ ψ : Name → Nat, resSort.eval ψ = resSort'.eval ψ) :
    MutualCtorDataI m env₀ members T lps cvC nP nF nIdx resSort' isProp large idxArgs
      ds Es srcs ks fvsP xFvs xrest Eiss tss :=
  { h with
    bits := fun ψ d hd => by rw [← hs ψ]; exact h.bits ψ d hd
    srcProp := fun hl ψ h0 => by rw [← hs ψ] at h0; exact h.srcProp hl ψ h0
    tssBits := fun ψ i d hd => by rw [← hs ψ]; exact h.tssBits ψ i d hd }


/-! ## The constructor leaf's validity walk -/

/-- **The constructor leaf's body is bit-valid under the whole binder
tower** (`ctorWalksGen`'s second half, with the index block left
abstract): the block's chains are bit-valid at the parameter frame, so
the injection of the point-terminated tupler is at every field
frame. -/
theorem ctorUnderValid {nP nF J w : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {bodyC : AnnotTerm} {Fss : List (List AnnotTerm)}
    (hlenDs : ds.length = nP + nF)
    (hokTy : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV ds bodyC))
    (hFsJ : Fss[J]? = some ((ds.drop nP).map (·.2.2)))
    (hvalid : ∀ ρ : Nat → V, Sat V (((ds.take nP).map (·.2.2)).reverse) ρ →
      SumFieldsValid ρ Fss)
    (ρ : Nat → V) :
    UnderTowerValid ρ
      (sumInjAtAV w (uChains Fss) ((ds.drop nP).map (·.2.2)).length (numeralAV J)
        (mkTowerGoU w ((ds.drop nP).map (·.2.2)) (idxEqAV [])))
      (ds.take nP ++ ds.drop nP) := by
  let Fs : List AnnotTerm := (ds.drop nP).map (·.2.2)
  have hlenFs : Fs.length = nF := by simp [Fs, hlenDs]
  have hst := stripPisAV_mkPisAV ds bodyC
  rw [hlenDs] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ' _ => hokTy ρ')
  simp only [List.append_nil] at okΓ
  have hΓlen : ((ds.map (·.2.2)).reverse).length = nP + nF := by simp [hlenDs]
  have hent : ∀ i, i < nP + nF → ∃ q, ds[i]? = some q ∧
      q.2.2 = ((ds.map (·.2.2)).reverse).getD (nP + nF - 1 - i) default := by
    intro i hi
    have hil : i < ds.length := by omega
    exact ⟨_, List.getElem?_eq_getElem hil,
      by rw [getD_reverse_of_peel hlenDs hi (List.getElem?_eq_getElem hil)]⟩
  have hw := hereditaryWalk (V := V)
    (Q := fun ρ ds' => UnderTowerValid ρ
      (sumInjAtAV w (uChains Fss) Fs.length (numeralAV J)
        (mkTowerGoU w Fs (idxEqAV []))) ds')
    hΓlen hlenDs hent okΓ
    (fun ρ' hρ' => ?_)
    (fun ρ d ds' _ hok hrec => ⟨hok.2, hrec⟩)
    0 (Nat.zero_le _) ρ (by
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓlen]; exact Nat.le_refl _)]
      exact Sat_nil V ρ)
  · rw [List.take_append_drop]
    rw [List.drop_zero] at hw
    exact hw
  rw [reverse_map_take_drop ds nP] at hρ'
  have hspF := spineFit_of_sat (Δ₀ := ((ds.take nP).map (·.2.2)).reverse)
    (Ds := (ds.drop nP).map (·.2.2)) hρ'
  rw [hlenFs] at hspF
  have hρp : Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ' (j + nF)) := by
    have := Sat_drop hρ' nF
    rw [List.drop_append_of_le_length (by simp [hlenDs]),
      List.drop_eq_nil_of_le (by simp [hlenDs]), List.nil_append] at this
    exact this
  have hvAll := hvalid _ hρp
  have hvF : FieldsValid (fun j => ρ' (j + nF)) Fs :=
    hvAll _ (List.mem_of_getElem? hFsJ)
  have := sumInj_validV_at_fields (w := w) (j := J) (uChains_validV hvAll) hvF hspF
  rwa [consList_range_reverse] at this

/-! ## One constructor's cons -/

/-- **The P step at a mutual constructor's cons**: constructor `J` (its
GLOBAL block position — the tag the auxiliary family's tagged union
carries) of member `mem`, consed with the sum route's constructor leaf
`sumMkAV (w ψ) J (ds ψ) Fs (uChains (FssR ψ))` over the WHOLE block's
real field chains.  `hfold` is `mutualCtorFold`'s conclusion at the
member's own parameter frame (the constructor's residual reads to the
auxiliary family's fibre at the tagged index tuple), `hiff` the
block's cross-member parameter identification, and the capability
obligation is vacuous: the members carry the empty record, so the
block claims nothing. -/
theorem stageMutualCtor
    {F : Nat} {memberNames : List Name} {T : Name} {lps : List Name}
    {nP nF nIdx J mem : Nat} {resSort : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal} {env₀ : Env}
    (mp : EnvModelM V μ env)
    (hE₀ : ConLeche.EtaFamiliesClosed env)
    {sorts : List Level}
    (hCtor : ConLeche.checkMutualCtor (ConLeche.fueledOps μ F) env₀ memberNames T lps nP nIdx
      resSort isProp large cvC nF cvTa = .ok (cvCa, sorts))
    -- the constructor is fresh at the cons's environment and its type
    -- resolves there
    (hfresh : env.find? cvCa.name = none)
    (htr : cvCa.type.constsResolve env = true)
    (hlpsC : cvCa.levelParams = lps)
    {W w : (Name → Nat) → Nat}
    {Idss FssR Ess' : (Name → Nat) → List (List AnnotTerm)}
    {ppsM ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm}
    {idxArgs : List Expr} {srcs : List (Option Nat)}
    -- the block's one result sort
    (hw : ∀ ψ : Name → Nat, resSort.eval ψ = w ψ)
    (hCD : CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    -- the residual folds to the auxiliary family's fibre at the tagged
    -- index tuple (`mutualCtorFold`)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsM ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
        interp V (consList bs ρ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))
          = sumSet (w ψ) (sumFibre (w ψ)
              (consList (idxValsAt ρ [tagTupleAV (W ψ) mem nF (Idss ψ) (Es ψ)] bs) ρ)
              (rChains 1 1 (FssR ψ) (Ess' ψ))))
    (hFsJ : ∀ ψ : Name → Nat, (FssR ψ)[J]? = some (((ds ψ).drop nP).map (·.2.2)))
    (hEsJ : ∀ ψ : Name → Nat,
      (Ess' ψ)[J]? = some [tagTupleAV (W ψ) mem nF (Idss ψ) (Es ψ)])
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      w ψ₁ = w ψ₂ ∧ FssR ψ₁ = FssR ψ₂)
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ FssR ψ, FieldsBelow nP Fs)
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsM ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (w ψ) ρ (FssR ψ) ∧ SumFieldsValid ρ (FssR ψ)) :
    ∃ mp' : EnvModelM V μ ⟨.ctorInfo cvCa nP nF :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvCa.name
        (fun ψ => sumMkAV (w ψ) J (ds ψ) (((ds ψ).drop nP).map (·.2.2)) (uChains (FssR ψ))) := by
  obtain ⟨⟨_, hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hCtor
  obtain ⟨-, hnres, hpshape, -, hlbt, hitf, type', -, -, hann', htp, -, -, -, hty⟩ :=
    ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  have hCname : cvCa.name = cvC.name := by rw [hty]
  have hcb : ConstsBound env cvCa.type := constsBound_of_constsResolve _ htr
  have hwfC : ConLeche.EnvWF ⟨.ctorInfo cvCa nP nF :: env.consts⟩ := by
    refine ConLeche.EnvWF.cons mp.base2.wf (ConLeche.structConstWF ?_ ?_
      (Expr.constsResolve_mono htr) ?_
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
    · show cvCa.type.hasFvar = false; rw [hty]; exact htf'
    · show cvCa.type.allLevelParamsDefined cvCa.levelParams = true; rw [hty]; exact htp
    · show cvCa.type.looseBVarsBounded 0 = true; rw [hty]; exact hbt'
  let A : (Name → Nat) → AnnotTerm := fun ψ =>
    sumMkAV (w ψ) J (ds ψ) (((ds ψ).drop nP).map (·.2.2)) (uChains (FssR ψ))
  have hAbelow : ∀ ψ, Term.bvarsBelow 0 (A ψ).erase := fun ψ =>
    sumMkAV_below (hCD.below ψ)
      ((DomsBelow.drop nP (hCD.below ψ)).fields)
      (by rw [Nat.zero_add]; exact uChains_below (hFssBelow ψ))
      (by show nP + (((ds ψ).drop nP).map (·.2.2)).length = (ds ψ).length
          simp [hCD.len ψ])
  -- the two hereditary premises
  have hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      MkPreS (w ψ) J ρ (((ds ψ).drop nP).map (·.2.2)) (uChains (FssR ψ))
        (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) ((ds ψ).take nP) := by
    intro ψ ρ
    refine mutualCtorMkPre (hCD.len ψ) (fun ρ' => hCD.okTy ψ ρ') (hFsJ ψ) (hEsJ ψ) rfl
      (fun ρ' hρ' => (hFssOkP ψ ρ' hρ').1) (fun ρ' hρ' bs hsp => ?_) ρ
    exact hfold ψ ρ' ((hiff ψ ρ').mpr hρ') bs hsp
  have hval : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      UnderTowerValid ρ
        (sumInjAtAV (w ψ) (uChains (FssR ψ)) ((((ds ψ).drop nP).map (·.2.2))).length
          (numeralAV J) (mkTowerGoU (w ψ) (((ds ψ).drop nP).map (·.2.2)) (idxEqAV [])))
        ((ds ψ).take nP ++ (ds ψ).drop nP) := fun ψ ρ =>
    ctorUnderValid (hCD.len ψ) (fun ρ' => hCD.okTy ψ ρ') (hFsJ ψ)
      (fun ρ' hρ' => (hFssOkP ψ ρ' hρ').2) ρ
  have hz : ∀ ψ : Name → Nat, ∀ d ∈ (ds ψ).take nP ++ (ds ψ).drop nP,
      (w ψ = 0 ↔ d.2.1 = 0) := by
    intro ψ d hd
    rw [List.take_append_drop] at hd
    rw [← hw ψ]
    exact hCD.bits ψ d hd
  have hreadC : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvCa.name A)
        ⟨.ctorInfo cvCa nP nF :: env.consts⟩ ψ 0 cvCa.type
        = some (mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .ctorInfo cvCa nP nF) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hCD.read ψ)
  have hnresC : ConLeche.reservedBasisNames.contains
      (ConstantInfo.ctorInfo cvCa nP nF).name = false := by
    show ConLeche.reservedBasisNames.contains cvCa.name = false
    rw [hCname]; exact hnres
  have hpshapeC : (ConstantInfo.ctorInfo cvCa nP nF).name.isProjFnShape = false := by
    show cvCa.name.isProjFnShape = false
    rw [hCname]; exact hpshape
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .ctorInfo cvCa nP nF)
    (A := A) hfresh hnresC (Or.inr ⟨_, _, _, rfl⟩)
    (ConsHead.ofFresh hwfC (fun ψ => hAbelow ψ) hnresC
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ψ₁ ψ₂ hφ
    have hφ' : ∀ q ∈ lps, ψ₁ q = ψ₂ q := by rw [← hlpsC]; exact hφ
    obtain ⟨hwe, hFe⟩ := hFssParams ψ₁ ψ₂ hφ'
    show sumMkAV _ J (ds ψ₁) (((ds ψ₁).drop nP).map (·.2.2)) (uChains (FssR ψ₁))
      = sumMkAV _ J (ds ψ₂) (((ds ψ₂).drop nP).map (·.2.2)) (uChains (FssR ψ₂))
    rw [hwe, hFe, (hCD.params ψ₁ ψ₂ hφ).1]
  · intro ψ ρ
    have := sumMkAV_wellDenotedV (V := V) (hz ψ) (hpre ψ ρ) (hval ψ ρ)
    rw [List.take_append_drop] at this
    exact this.1
  · intro ψ ρ
    have := sumMkAV_wellDenotedV (V := V) (hz ψ) (hpre ψ ρ) (hval ψ ρ)
    rw [List.take_append_drop] at this
    exact this.2
  · exact fun ψ => ⟨_, hreadC ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    exact hCD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    have := sumMkAV_mem (V := V) (hz ψ) (hpre ψ ρ)
    rw [List.take_append_drop] at this
    exact this
  · -- `caps_ok`: the block claims nothing, and the cons stores a
    -- CONSTRUCTOR at the name the obligation is taken at
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .ctorInfo cvCa nP nF) (A := A)
      (T := cvCa.name) hfresh (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeC
      (Or.inr fun _ _ h => nomatch h)
      (fun T' cvT' caps' hf _ hres hcape => hE₀ T' cvT' caps' hf hcape hres)
      m₂ hac ?_
    intro cvT' caps' hf _
    have hself := ConLeche.Env.find?_cons_self (ConstantInfo.ctorInfo cvCa nP nF) env
    rw [show (ConstantInfo.ctorInfo cvCa nP nF).name = cvCa.name from rfl] at hself
    exact nomatch (hself.symm.trans hf)

/-! ## The loop's invariants -/

/-- The block names a constructor's data mention are stored: its own
member's former and the former of every member one of its recursive or
reflexive fields targets. -/
@[expose] def CtorMembersFound (env : Env) (members : List (Name × Nat × Nat))
    (Tname : Nat → Name) (mots : Nat → Nat) (ksF : Nat → List (RecFieldKind × Nat))
    (J nF : Nat) : Prop :=
  (env.find? (Tname (mots J))).isSome = true ∧
  ∀ i, i < nF → (kindAt (ksF J) i = .recursive ∨ kindAt (ksF J) i = .reflexive) →
    (env.find? (mutualNameOf members (tgtAt (ksF J) i))).isSome = true

/-- **The per-constructor facts of a mutual block at a position**
(`FixCtorFactsAt` with the member's name and index count looked up
through `mots`): the constructor is stored at the block's parameter
count and level parameters, and its data are its `MutualCtorDataI` at
its OWN member. -/
@[expose] def MutualCtorFactsAt {env : Env} (m : EnvModel V env) (env₀ : Env)
    (members : List (Name × Nat × Nat)) (lps : List Name) (nP : Nat) (isProp large : Bool)
    (Tname : Nat → Name) (nIdxOf : Nat → Nat) (mots : Nat → Nat) (resSortOf : Nat → Level)
    (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List (RecFieldKind × Nat)) (fvsPF xFvsF : Nat → List Expr)
    (xrestF : Nat → Expr) (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (J : Nat) (cA : ConstantVal × Nat) : Prop :=
  env.find? cA.1.name = some (.ctorInfo cA.1 nP cA.2) ∧
  cA.1.levelParams = lps ∧
  MutualCtorDataI m env₀ members (Tname (mots J)) lps cA.1 nP cA.2 (nIdxOf (mots J))
    (resSortOf J) isProp large (idxF J) (dsF J) (esF J) (srcsF J) (ksF J) (fvsPF J) (xFvsF J)
    (xrestF J) (eissF J) (tssF J)

/-- The facts about the pending constructors of a mutual block at an
environment (`PendingAt` with the mutual data). -/
@[expose] def MutualPendingAt {env : Env} (m : EnvModel V env) (env₀ : Env)
    (members : List (Name × Nat × Nat)) (lps : List Name) (nP : Nat) (isProp large : Bool)
    (Tname : Nat → Name) (nIdxOf mots : Nat → Nat) (resSortOf : Nat → Level)
    (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List (RecFieldKind × Nat)) (fvsPF xFvsF : Nat → List Expr)
    (xrestF : Nat → Expr) (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (ctorsA : List (ConstantVal × Nat)) (k : Nat) : Prop :=
  ∀ J cA, k ≤ J → ctorsA[J]? = some cA →
    env.find? cA.1.name = none ∧ cA.1.type.constsResolve env = true ∧
    (∀ e ∈ idxF J, e.constsResolve env = true) ∧ cA.1.levelParams = lps ∧
    MutualCtorDataI m env₀ members (Tname (mots J)) lps cA.1 nP cA.2 (nIdxOf (mots J))
      (resSortOf J) isProp large (idxF J) (dsF J) (esF J) (srcsF J) (ksF J) (fvsPF J)
      (xFvsF J) (xrestF J) (eissF J) (tssF J)

/-- The facts about the consed constructors of a mutual block at an
environment (`ConsedAt` with the mutual data and the GLOBAL block
position as the tag). -/
@[expose] def MutualConsedAt {env : Env} (m : EnvModel V env) (env₀ : Env)
    (members : List (Name × Nat × Nat)) (lps : List Name) (nP : Nat) (isProp large : Bool)
    (Tname : Nat → Name) (nIdxOf mots : Nat → Nat) (resSortOf : Nat → Level)
    (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List (RecFieldKind × Nat)) (fvsPF xFvsF : Nat → List Expr)
    (xrestF : Nat → Expr) (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (w : (Name → Nat) → Nat) (FssR : (Name → Nat) → List (List AnnotTerm))
    (ctorsA : List (ConstantVal × Nat)) (k : Nat) : Prop :=
  ∀ J cA, J < k → ctorsA[J]? = some cA →
    MutualCtorFactsAt m env₀ members lps nP isProp large Tname nIdxOf mots resSortOf
      idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF J cA ∧
    (∀ e ∈ idxF J, e.constsResolve env = true) ∧
    ∀ ψ, m.acval cA.1.name ψ
      = sumMkAV (w ψ) J (dsF J ψ) (((dsF J ψ).drop nP).map (·.2.2)) (uChains (FssR ψ))

/-! ## The constructors' conses, in block order -/

/-- **The constructors' conses, in block order** (the induction over
the remaining constructors).  The kernel checks every constructor at
the formers' environment and conses them afterwards
(`consMutualCtors`), so the data of every constructor — consed or
pending — crosses each cons (`MutualCtorDataI.cross`, licensed by the
block names being stored and the constructor names fresh) and the
members' leaves are untouched. -/
theorem stageMutualCtorsGo
    {F : Nat} {memberNames : List Name} {members : List (Name × Nat × Nat)}
    {lps : List Name} {nP : Nat} {isProp large : Bool} {env₀ : Env}
    {Tname : Nat → Name} {nIdxOf mots : Nat → Nat} {resSortOf : Nat → Level}
    {cvTaOf : Nat → ConstantVal}
    {idxF : Nat → List Expr}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List (RecFieldKind × Nat)} {fvsPF xFvsF : Nat → List Expr}
    {xrestF : Nat → Expr} {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {ctorsA : List (ConstantVal × Nat)}
    {W w : (Name → Nat) → Nat}
    {Idss FssR Ess' : (Name → Nat) → List (List AnnotTerm)}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {leafT : Nat → (Name → Nat) → AnnotTerm}
    (hnd : (ctorsA.map (·.1.name)).Nodup)
    (hrun : ∀ J cA, ctorsA[J]? = some cA → ∃ (cvC : ConstantVal) (sorts : List Level),
      ConLeche.checkMutualCtor (ConLeche.fueledOps μ F) env₀ memberNames (Tname (mots J)) lps
        nP (nIdxOf (mots J)) (resSortOf J) isProp large cvC cA.2 (cvTaOf (mots J))
        = .ok (cA.1, sorts))
    (hw : ∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat, (resSortOf J).eval ψ = w ψ)
    (hfold : ∀ J cA, ctorsA[J]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsOf (mots J) ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF J ψ).drop nP).map (·.2.2)) bs →
        interp V (consList bs ρ)
            (AnnotTerm.mkAppN (leafT J ψ) (paramBvars nP cA.2 ++ esF J ψ))
          = sumSet (w ψ) (sumFibre (w ψ)
              (consList (idxValsAt ρ
                [tagTupleAV (W ψ) (mots J) cA.2 (Idss ψ) (esF J ψ)] bs) ρ)
              (rChains 1 1 (FssR ψ) (Ess' ψ))))
    (hFsJ : ∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat,
      (FssR ψ)[J]? = some (((dsF J ψ).drop nP).map (·.2.2)))
    (hEsJ : ∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat,
      (Ess' ψ)[J]? = some [tagTupleAV (W ψ) (mots J) cA.2 (Idss ψ) (esF J ψ)])
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      w ψ₁ = w ψ₂ ∧ FssR ψ₁ = FssR ψ₂)
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ FssR ψ, FieldsBelow nP Fs)
    (hiff : ∀ J cA, ctorsA[J]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsOf (mots J) ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsF J ψ).take nP).map (·.2.2)).reverse ρ)
    (hFssOkP : ∀ J cA, ctorsA[J]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF J ψ).take nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (w ψ) ρ (FssR ψ) ∧ SumFieldsValid ρ (FssR ψ))
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop)
    (hInv : ∀ {env' : Env} (m' : EnvModel V env') (cA : ConstantVal × Nat)
      (A : (Name → Nat) → AnnotTerm)
      (mC : EnvModel V ⟨.ctorInfo cA.1 nP cA.2 :: env'.consts⟩),
      (∃ J : Nat, ctorsA[J]? = some cA) → env'.find? cA.1.name = none →
      mC.acval = acvalWith m'.acval cA.1.name A → Inv m' → Inv mC) :
    ∀ (rest : List (ConstantVal × Nat)) (k : Nat) (env : Env) (mp : EnvModelM V μ env),
      (∀ i, rest[i]? = ctorsA[k + i]?) → k + rest.length = ctorsA.length →
      ConLeche.EtaFamiliesClosed env →
      (∀ J cA, ctorsA[J]? = some cA → CtorMembersFound env members Tname mots ksF J cA.2) →
      (∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat,
        mp.base2.acval (Tname (mots J)) ψ = leafT J ψ) →
      MutualConsedAt mp.base2 env₀ members lps nP isProp large Tname nIdxOf mots resSortOf
        idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF w FssR ctorsA k →
      MutualPendingAt mp.base2 env₀ members lps nP isProp large Tname nIdxOf mots resSortOf
        idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ctorsA k →
      Inv mp.base2 →
      ∃ mp' : EnvModelM V μ (ConLeche.consMutualCtors nP rest env),
        ConLeche.EtaFamiliesClosed (ConLeche.consMutualCtors nP rest env) ∧
        (∀ J cA, ctorsA[J]? = some cA →
          CtorMembersFound (ConLeche.consMutualCtors nP rest env) members Tname mots ksF
            J cA.2) ∧
        (∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat,
          mp'.base2.acval (Tname (mots J)) ψ = leafT J ψ) ∧
        MutualConsedAt mp'.base2 env₀ members lps nP isProp large Tname nIdxOf mots resSortOf
          idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF w FssR ctorsA ctorsA.length ∧
        Inv mp'.base2 ∧
        (∀ n : Name, (∀ cA ∈ rest, n ≠ cA.1.name) → mp'.base2.acval n = mp.base2.acval n)
  | [], k, env, mp, _, hk, hE, hfound, hleaf, hcons, _, hinv => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    exact ⟨mp, hE, hfound, hleaf, hcons, hinv, fun _ _ => rfl⟩
  | cA :: rest, k, env, mp, hrest, hk, hE, hfound, hleaf, hcons, hpend, hinv => by
    have hcAk : ctorsA[k]? = some cA := by
      have := hrest 0; simpa using this.symm
    obtain ⟨hfresh, htr, hidxRes, hlpsC, hCD⟩ := hpend k cA (Nat.le_refl _) hcAk
    obtain ⟨cvC, sorts, hCtor⟩ := hrun k cA hcAk
    have hcross : ∀ e : Expr, ConsCrossAt (.ctorInfo cA.1 nP cA.2) e :=
      fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
    have hnameNe : ∀ n : Name, (env.find? n).isSome = true → n ≠ cA.1.name := by
      intro n hs h
      rw [h, hfresh] at hs
      exact nomatch hs
    have hTne : ∀ J cAJ, ctorsA[J]? = some cAJ → Tname (mots J) ≠ cA.1.name :=
      fun J cAJ hJ => hnameNe _ (hfound J cAJ hJ).1
    have htgtNe : ∀ J cAJ, ctorsA[J]? = some cAJ → ∀ i, i < cAJ.2 →
        (kindAt (ksF J) i = .recursive ∨ kindAt (ksF J) i = .reflexive) →
        mutualNameOf members (tgtAt (ksF J) i) ≠ cA.1.name :=
      fun J cAJ hJ i hi hkind => hnameNe _ ((hfound J cAJ hJ).2 i hi hkind)
    -- the stage
    have hfoldC : ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsOf (mots k) ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ bs : List V, SpineFit ρ (((dsF k ψ).drop nP).map (·.2.2)) bs →
          interp V (consList bs ρ)
              (ctorBodyAVI mp.base2 (Tname (mots k)) nP cA.2 ψ (esF k ψ))
            = sumSet (w ψ) (sumFibre (w ψ)
                (consList (idxValsAt ρ
                  [tagTupleAV (W ψ) (mots k) cA.2 (Idss ψ) (esF k ψ)] bs) ρ)
                (rChains 1 1 (FssR ψ) (Ess' ψ))) := by
      intro ψ ρ hρ bs hsp
      unfold ctorBodyAVI
      rw [hleaf k cA hcAk ψ]
      exact hfold k cA hcAk ψ ρ hρ bs hsp
    have hcbC : ConstsBound env cA.1.type := constsBound_of_constsResolve _ htr
    obtain ⟨mpC, hacC⟩ := stageMutualCtor (J := k) (mem := mots k) mp hE hCtor hfresh htr hlpsC
      (hw k cA hcAk) hCD.toCtorDataI hfoldC (hFsJ k cA hcAk) (hEsJ k cA hcAk) hFssParams
      hFssBelow (hiff k cA hcAk) (hFssOkP k cA hcAk)
    -- the invariants at the extension
    have hE' : ConLeche.EtaFamiliesClosed ⟨.ctorInfo cA.1 nP cA.2 :: env.consts⟩ :=
      hE.cons_nonind hfresh (fun _ _ heq => nomatch heq)
    have hfound' : ∀ J cAJ, ctorsA[J]? = some cAJ →
        CtorMembersFound ⟨.ctorInfo cA.1 nP cA.2 :: env.consts⟩ members Tname mots ksF J cAJ.2 := by
      intro J cAJ hJ
      obtain ⟨h1, h2⟩ := hfound J cAJ hJ
      refine ⟨by rw [ConLeche.Env.find?_cons_of_isSome hfresh h1]; exact h1, ?_⟩
      intro i hi hkind
      have := h2 i hi hkind
      rw [ConLeche.Env.find?_cons_of_isSome hfresh this]
      exact this
    have hleaf' : ∀ J cAJ, ctorsA[J]? = some cAJ → ∀ ψ : Name → Nat,
        mpC.base2.acval (Tname (mots J)) ψ = leafT J ψ := by
      intro J cAJ hJ ψ
      rw [hacC]
      show acvalWith mp.base2.acval cA.1.name _ (Tname (mots J)) ψ = _
      rw [acvalWith_ne (hTne J cAJ hJ)]
      exact hleaf J cAJ hJ ψ
    have hcons' : MutualConsedAt mpC.base2 env₀ members lps nP isProp large Tname nIdxOf mots
        resSortOf idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF w FssR ctorsA (k + 1) := by
      intro J cAJ hJk hJ
      rcases Nat.lt_or_ge J k with hlt | hge
      · obtain ⟨⟨hfi, hlpsi, hCDi⟩, hresi, hleafi⟩ := hcons J cAJ hlt hJ
        have hne : cAJ.1.name ≠ cA.1.name := names_ne_of_nodup hnd hJ hcAk (by omega)
        have hcbi : ConstsBound env cAJ.1.type :=
          constsBound_of_constsResolve _
            (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfi)).2.2.1
        refine ⟨⟨ConLeche.Env.find?_cons_of_fresh hfresh hfi, hlpsi,
          hCDi.cross (c₀ := .ctorInfo cA.1 nP cA.2) hfresh (hTne J cAJ hJ) (htgtNe J cAJ hJ)
            hcross hcbi
            (fun e he => constsBound_of_constsResolve _ (hresi e he)) mpC.base2 hacC⟩,
          fun e he => Expr.constsResolve_mono (hresi e he), ?_⟩
        intro ψ
        rw [hacC]
        show acvalWith mp.base2.acval cA.1.name _ cAJ.1.name ψ = _
        rw [acvalWith_ne hne]
        exact hleafi ψ
      · have hJk' : J = k := by omega
        subst hJk'
        obtain rfl := Option.some.inj (hcAk.symm.trans hJ)
        refine ⟨⟨ConLeche.Env.find?_cons_self (.ctorInfo cA.1 nP cA.2) env, hlpsC,
          hCD.cross (c₀ := .ctorInfo cA.1 nP cA.2) hfresh (hTne J cA hJ) (htgtNe J cA hJ)
            hcross hcbC
            (fun e he => constsBound_of_constsResolve _ (hidxRes e he)) mpC.base2 hacC⟩,
          fun e he => Expr.constsResolve_mono (hidxRes e he), ?_⟩
        intro ψ
        rw [hacC]
        show acvalWith mp.base2.acval cA.1.name _ cA.1.name ψ = _
        rw [acvalWith_self]
    have hpend' : MutualPendingAt mpC.base2 env₀ members lps nP isProp large Tname nIdxOf mots
        resSortOf idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ctorsA (k + 1) := by
      intro J cAJ hJk hJ
      obtain ⟨hfreshi, htri, hresi, hlpsi, hCDi⟩ := hpend J cAJ (by omega) hJ
      have hne : cA.1.name ≠ cAJ.1.name := names_ne_of_nodup hnd hcAk hJ (by omega)
      refine ⟨?_, Expr.constsResolve_mono htri,
        fun e he => Expr.constsResolve_mono (hresi e he), hlpsi,
        hCDi.cross (c₀ := .ctorInfo cA.1 nP cA.2) hfresh (hTne J cAJ hJ) (htgtNe J cAJ hJ) hcross
          (constsBound_of_constsResolve _ htri)
          (fun e he => constsBound_of_constsResolve _ (hresi e he)) mpC.base2 hacC⟩
      rw [ConLeche.Env.find?_cons]
      split
      · next h => exact absurd h hne
      · exact hfreshi
    have hrest' : ∀ i, rest[i]? = ctorsA[k + 1 + i]? := by
      intro i
      have := hrest (i + 1)
      rwa [show k + (i + 1) = k + 1 + i from by omega] at this
    have hinv' : Inv mpC.base2 :=
      hInv mp.base2 cA _ mpC.base2 ⟨k, hcAk⟩ hfresh hacC hinv
    obtain ⟨mp', hE'', hfound'', hleaf'', hcons'', hinv'', hag⟩ :=
      stageMutualCtorsGo hnd hrun hw hfold hFsJ hEsJ hFssParams hFssBelow hiff hFssOkP Inv hInv
        rest (k + 1) _ mpC hrest' (by simp at hk; omega) hE' hfound' hleaf' hcons' hpend' hinv'
    refine ⟨mp', hE'', hfound'', hleaf'', hcons'', hinv'', ?_⟩
    intro n hn
    rw [hag n (fun cA' hcA' => hn cA' (List.mem_cons_of_mem _ hcA')), hacC]
    exact acvalWith_ne (hn cA List.mem_cons_self)

/-- **The constructors' stage of the mutual install**: the block's `n`
constructors consed onto the formers' environment in block order
(`consMutualCtors`), constructor `J` with the sum route's leaf at its
GLOBAL position `J` over the whole block's real field chains.  The
environment the conses land on keeps its stored η families closed and
its block names found, every member's leaf is untouched, and the
constructors' facts and leaves hold at the end. -/
theorem stageMutualCtors
    {F : Nat} {memberNames : List Name} {members : List (Name × Nat × Nat)}
    {lps : List Name} {nP : Nat} {isProp large : Bool} {env₀ env₁ : Env}
    {Tname : Nat → Name} {nIdxOf mots : Nat → Nat} {resSortOf : Nat → Level}
    {cvTaOf : Nat → ConstantVal}
    {idxF : Nat → List Expr}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List (RecFieldKind × Nat)} {fvsPF xFvsF : Nat → List Expr}
    {xrestF : Nat → Expr} {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {ctorsA : List (ConstantVal × Nat)}
    {W w : (Name → Nat) → Nat}
    {Idss FssR Ess' : (Name → Nat) → List (List AnnotTerm)}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {leafT : Nat → (Name → Nat) → AnnotTerm}
    (mp₁ : EnvModelM V μ env₁)
    (hnd : (ctorsA.map (·.1.name)).Nodup)
    (hrun : ∀ J cA, ctorsA[J]? = some cA → ∃ (cvC : ConstantVal) (sorts : List Level),
      ConLeche.checkMutualCtor (ConLeche.fueledOps μ F) env₀ memberNames (Tname (mots J)) lps
        nP (nIdxOf (mots J)) (resSortOf J) isProp large cvC cA.2 (cvTaOf (mots J))
        = .ok (cA.1, sorts))
    (hw : ∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat, (resSortOf J).eval ψ = w ψ)
    (hfold : ∀ J cA, ctorsA[J]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsOf (mots J) ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF J ψ).drop nP).map (·.2.2)) bs →
        interp V (consList bs ρ)
            (AnnotTerm.mkAppN (leafT J ψ) (paramBvars nP cA.2 ++ esF J ψ))
          = sumSet (w ψ) (sumFibre (w ψ)
              (consList (idxValsAt ρ
                [tagTupleAV (W ψ) (mots J) cA.2 (Idss ψ) (esF J ψ)] bs) ρ)
              (rChains 1 1 (FssR ψ) (Ess' ψ))))
    (hFsJ : ∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat,
      (FssR ψ)[J]? = some (((dsF J ψ).drop nP).map (·.2.2)))
    (hEsJ : ∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat,
      (Ess' ψ)[J]? = some [tagTupleAV (W ψ) (mots J) cA.2 (Idss ψ) (esF J ψ)])
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      w ψ₁ = w ψ₂ ∧ FssR ψ₁ = FssR ψ₂)
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ FssR ψ, FieldsBelow nP Fs)
    (hiff : ∀ J cA, ctorsA[J]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsOf (mots J) ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsF J ψ).take nP).map (·.2.2)).reverse ρ)
    (hFssOkP : ∀ J cA, ctorsA[J]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF J ψ).take nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (w ψ) ρ (FssR ψ) ∧ SumFieldsValid ρ (FssR ψ))
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop)
    (hInv : ∀ {env' : Env} (m' : EnvModel V env') (cA : ConstantVal × Nat)
      (A : (Name → Nat) → AnnotTerm)
      (mC : EnvModel V ⟨.ctorInfo cA.1 nP cA.2 :: env'.consts⟩),
      (∃ J : Nat, ctorsA[J]? = some cA) → env'.find? cA.1.name = none →
      mC.acval = acvalWith m'.acval cA.1.name A → Inv m' → Inv mC)
    (hE : ConLeche.EtaFamiliesClosed env₁)
    (hfound : ∀ J cA, ctorsA[J]? = some cA →
      CtorMembersFound env₁ members Tname mots ksF J cA.2)
    (hleafT : ∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat,
      mp₁.base2.acval (Tname (mots J)) ψ = leafT J ψ)
    (hpend : MutualPendingAt mp₁.base2 env₀ members lps nP isProp large Tname nIdxOf mots
      resSortOf idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ctorsA 0)
    (hinv : Inv mp₁.base2) :
    ∃ mp₂ : EnvModelM V μ (ConLeche.consMutualCtors nP ctorsA env₁),
      ConLeche.EtaFamiliesClosed (ConLeche.consMutualCtors nP ctorsA env₁) ∧
      (∀ J cA, ctorsA[J]? = some cA →
        CtorMembersFound (ConLeche.consMutualCtors nP ctorsA env₁) members Tname mots ksF
          J cA.2) ∧
      (∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat,
        mp₂.base2.acval (Tname (mots J)) ψ = leafT J ψ) ∧
      MutualConsedAt mp₂.base2 env₀ members lps nP isProp large Tname nIdxOf mots resSortOf
        idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF w FssR ctorsA ctorsA.length ∧
      Inv mp₂.base2 ∧
      (∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat,
        mp₂.base2.acval cA.1.name ψ
          = sumMkAV (w ψ) J (dsF J ψ) (((dsF J ψ).drop nP).map (·.2.2)) (uChains (FssR ψ))) ∧
      (∀ n : Name, (∀ cA ∈ ctorsA, n ≠ cA.1.name) →
        mp₂.base2.acval n = mp₁.base2.acval n) := by
  obtain ⟨mp₂, hE₂, hfound₂, hleaf₂, hcons₂, hinv₂, hag⟩ :=
    stageMutualCtorsGo hnd hrun hw hfold hFsJ hEsJ hFssParams hFssBelow hiff hFssOkP Inv hInv
      ctorsA 0 env₁ mp₁ (fun i => by rw [Nat.zero_add]) (by omega) hE hfound hleafT
      (fun J cA h => absurd h (Nat.not_lt_zero J)) hpend hinv
  refine ⟨mp₂, hE₂, hfound₂, hleaf₂, hcons₂, hinv₂, ?_, hag⟩
  intro J cA hJ
  exact (hcons₂ J cA (List.getElem?_eq_some_iff.mp hJ).1 hJ).2.2

end ConLeche.Model
