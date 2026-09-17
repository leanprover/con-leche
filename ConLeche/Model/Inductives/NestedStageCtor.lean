module

public import ConLeche.Semantics.Tower.MutualTagI
public import ConLeche.Model.Inductives.SumData
public import ConLeche.Kernel.Inductives.NestedInstall
import ConLeche.Model.Inductives.MutualStageCtor
import ConLeche.Semantics.Tower.PiCongr
import ConLeche.Model.Inductives.BlockRepCross
import ConLeche.Verify.Inductives.FrontDoor
import ConLeche.Verify.Inductives.NestedInv
public section

/-!
# The restored constructor's cons (task #315, M6 s8)

`stageNestedCtor`: `stageMutualCtor`'s twin at a RESTORED constructor
(DESIGN §U.20).  The restore replaces, at every nested field, the
copy's head `aux p⃗ is` by the container at the pin's components
`J Ds is`; the constructor is re-checked through the pre-annotated
front door at the prefix environment, so its data (`CtorDataI` at the
restored domains `dsR`) come from that door, while its LEAF stays the
auxiliary constructor's — the sum route's injection over the AUXILIARY
domains `dsA` and the auxiliary block's chains, exactly as
`stageMutualCtor` conses it.  The one new obligation is the leaf's
membership in the RESTORED type: `sumMkAV_mem` places it in the
Π-tower over the auxiliary domains, and the two towers read alike
(`interp_mkPisAV_congr_fit`) because the two domain lists agree at
every fitting prefix — the parameters verbatim, the fields by the
caller's `hagree` (the pin identification of the nested entries,
`nestedIdent_of`, and equality elsewhere).

Everything else is `stageMutualCtor` with the auxiliary constructor's
run replaced by the door's syntactic facts (`FrontDoorFacts`), the
auxiliary data's `okTy`/`len`/`bits`/`below`/`params` taken at the
auxiliary domains (term-level facts of the SAME annotated term at the
scratch model, the member's leaf being the same), and the restored
data's `read`/`okTy` at the current model.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The two towers read alike -/

/-- **The auxiliary and the restored Π-towers read alike** at every frame:
the domain lists have one length, the same parameter prefix and the same
binder bits, and their fields read alike at every fitting prefix. -/
theorem interp_mkPisAV_restored {R : AnnotTerm} {nP nF : Nat}
    {dsA dsR : List (Nat × Nat × AnnotTerm)}
    (hlenA : dsA.length = nP + nF) (hlenR : dsR.length = dsA.length)
    (htake : dsR.take nP = dsA.take nP)
    (hbits : ∀ i, (dsR.getD i default).2.1 = (dsA.getD i default).2.1)
    (hagree : ∀ ρ : Nat → V, Sat V ((dsA.take nP).map (·.2.2)).reverse ρ →
      ∀ l, l < nF → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ (((dsA.drop nP).map (·.2.2)).take l) fs₁ →
        SpineFit ρ (((dsR.drop nP).map (·.2.2)).take l) fs₁ →
        interp V (consList fs₁ ρ) (dsA.getD (nP + l) default).2.2
          = interp V (consList fs₁ ρ) (dsR.getD (nP + l) default).2.2)
    (σ : Nat → V) :
    interp V σ (mkPisAV dsA R) = interp V σ (mkPisAV dsR R) := by
  refine interp_mkPisAV_congr_fit hlenR.symm (fun i _ => (hbits i).symm) ?_
  intro l hl as hlas hspA hspR
  rcases Nat.lt_or_ge l nP with hlt | hge
  · -- a parameter position: the entries are equal
    have hA : dsA.getD l default = (dsA.take nP).getD l default := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt]
    have hR : dsR.getD l default = (dsR.take nP).getD l default := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt]
    rw [hA, hR, htake]
  · -- a field position: split the spine at the parameters
    obtain ⟨l', rfl⟩ : ∃ l', l = nP + l' := ⟨l - nP, by omega⟩
    have hl' : l' < nF := by omega
    have htakeA : (dsA.take (nP + l')).map (·.2.2)
        = (dsA.take nP).map (·.2.2) ++ (((dsA.drop nP).map (·.2.2)).take l') := by
      simp only [List.take_add, List.map_append, List.map_take]
    have htakeR : (dsR.take (nP + l')).map (·.2.2)
        = (dsA.take nP).map (·.2.2) ++ (((dsR.drop nP).map (·.2.2)).take l') := by
      rw [← htake]
      simp only [List.take_add, List.map_append, List.map_take]
    rw [htakeA] at hspA
    rw [htakeR] at hspR
    obtain ⟨ps, fs₁, rfl, hspP, hspA'⟩ := spineFit_append_inv hspA
    obtain ⟨ps', fs₁', heq, hspP', hspR'⟩ := spineFit_append_inv hspR
    have hlenP : ps.length = nP := by
      rw [hspP.length_eq, List.length_map, List.length_take, hlenA]
      exact Nat.min_eq_left (Nat.le_add_right _ _)
    have hlenP' : ps'.length = nP := by
      rw [hspP'.length_eq, List.length_map, List.length_take, hlenA]
      exact Nat.min_eq_left (Nat.le_add_right _ _)
    obtain ⟨rfl, rfl⟩ := List.append_inj heq (hlenP.trans hlenP'.symm)
    have hsat : Sat V ((dsA.take nP).map (·.2.2)).reverse (consList ps σ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V σ) hspP
      rwa [List.append_nil] at this
    have hlen₁ : fs₁.length = l' := by
      rw [List.length_append, hlenP] at hlas
      omega
    rw [consList_append]
    exact hagree (consList ps σ) hsat l' hl' fs₁ hlen₁ hspA' hspR'

/-! ## The step -/

/-- **The P step at a restored constructor's cons** (`stageMutualCtor`'s
twin, DESIGN §U.20): the constructor `cvA`, through the pre-annotated
front door (`hfd`, its syntactic facts), fresh at the cons's
environment and resolving there, with its data at the RESTORED domains
`dsR` at the current model (`hCD`) and the auxiliary constructor's
term-level facts at the AUXILIARY domains `dsA` (`hokTyA` etc.: the
same annotated term as at the scratch model), the two domain lists
agreeing at every fitting prefix (`hagree`) — is consed with the
auxiliary leaf `sumMkAV (w ψ) J (dsA ψ) …` over the caller's chains. -/
theorem stageNestedCtor
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx J mem : Nat} {resSort : Level}
    {isProp large : Bool} {cvA : ConstantVal} {env₀ : Env}
    (mp : EnvModelM V μ env)
    (hE₀ : ConLeche.EtaFamiliesClosed env)
    (hfd : ConLeche.FrontDoorFacts μ F env₀ cvA cvA)
    (hfresh : env.find? cvA.name = none)
    (htr : cvA.type.constsResolve env = true)
    (hlpsC : cvA.levelParams = lps)
    {W w : (Name → Nat) → Nat}
    {Idss FssR Ess' : (Name → Nat) → List (List AnnotTerm)}
    {ppsM dsA dsR : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm}
    {idxArgs : List Expr} {srcs : List (Option Nat)}
    (hw : ∀ ψ : Name → Nat, resSort.eval ψ = w ψ)
    (hCD : CtorDataI mp.base2 T lps cvA nP nF nIdx resSort isProp large idxArgs dsR Es srcs)
    -- the auxiliary constructor's term-level facts at the auxiliary domains
    (hlenA : ∀ ψ : Name → Nat, (dsA ψ).length = nP + nF)
    (hokTyA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (mkPisAV (dsA ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))))
    (hbitsA : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ dsA ψ →
      (resSort.eval ψ = 0 ↔ d.2.1 = 0))
    (hbelowA : ∀ ψ : Name → Nat, DomsBelow 0 (dsA ψ))
    (hparamsA : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) → dsA ψ₁ = dsA ψ₂)
    -- the two domain lists agree at every fitting prefix
    (hlenR : ∀ ψ : Name → Nat, (dsR ψ).length = (dsA ψ).length)
    (htakeR : ∀ ψ : Name → Nat, (dsR ψ).take nP = (dsA ψ).take nP)
    (hbitsR : ∀ (ψ : Name → Nat) (i : Nat), ((dsR ψ).getD i default).2.1 = ((dsA ψ).getD i default).2.1)
    (hagree : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsA ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ l, l < nF → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ ((((dsA ψ).drop nP).map (·.2.2)).take l) fs₁ →
        SpineFit ρ ((((dsR ψ).drop nP).map (·.2.2)).take l) fs₁ →
        interp V (consList fs₁ ρ) ((dsA ψ).getD (nP + l) default).2.2
          = interp V (consList fs₁ ρ) ((dsR ψ).getD (nP + l) default).2.2)
    -- the residual folds to the auxiliary family's fibre at the tagged
    -- index tuple, at the auxiliary domains (`mutualCtorFold`)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsM ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsA ψ).drop nP).map (·.2.2)) bs →
        interp V (consList bs ρ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))
          = sumSet (w ψ) (sumFibre (w ψ)
              (consList (idxValsAt ρ [tagTupleAV (W ψ) mem nF (Idss ψ) (Es ψ)] bs) ρ)
              (rChains 1 1 (FssR ψ) (Ess' ψ))))
    (hFsJ : ∀ ψ : Name → Nat, (FssR ψ)[J]? = some (((dsA ψ).drop nP).map (·.2.2)))
    (hEsJ : ∀ ψ : Name → Nat,
      (Ess' ψ)[J]? = some [tagTupleAV (W ψ) mem nF (Idss ψ) (Es ψ)])
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      w ψ₁ = w ψ₂ ∧ FssR ψ₁ = FssR ψ₂)
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ FssR ψ, FieldsBelow nP Fs)
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsM ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsA ψ).take nP).map (·.2.2)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsA ψ).take nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (w ψ) ρ (FssR ψ) ∧ SumFieldsValid ρ (FssR ψ)) :
    ∃ mp' : EnvModelM V μ ⟨.ctorInfo cvA nP nF :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvA.name
        (fun ψ => sumMkAV (w ψ) J (dsA ψ) (((dsA ψ).drop nP).map (·.2.2)) (uChains (FssR ψ))) := by
  have hcb : ConstsBound env cvA.type := constsBound_of_constsResolve _ htr
  have hwfC : ConLeche.EnvWF ⟨.ctorInfo cvA nP nF :: env.consts⟩ := by
    refine ConLeche.EnvWF.cons mp.base2.wf (ConLeche.structConstWF ?_ ?_
      (Expr.constsResolve_mono htr) ?_
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
    · exact hfd.noFvar
    · exact hfd.lpsOk
    · exact hfd.bounded
  let A : (Name → Nat) → AnnotTerm := fun ψ =>
    sumMkAV (w ψ) J (dsA ψ) (((dsA ψ).drop nP).map (·.2.2)) (uChains (FssR ψ))
  have hAbelow : ∀ ψ, Term.bvarsBelow 0 (A ψ).erase := fun ψ =>
    sumMkAV_below (hbelowA ψ)
      ((DomsBelow.drop nP (hbelowA ψ)).fields)
      (by rw [Nat.zero_add]; exact uChains_below (hFssBelow ψ))
      (by show nP + (((dsA ψ).drop nP).map (·.2.2)).length = (dsA ψ).length
          simp [hlenA ψ])
  -- the two hereditary premises, at the auxiliary domains
  have hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      MkPreS (w ψ) J ρ (((dsA ψ).drop nP).map (·.2.2)) (uChains (FssR ψ))
        (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) ((dsA ψ).take nP) := by
    intro ψ ρ
    refine mutualCtorMkPre (hlenA ψ) (fun ρ' => hokTyA ψ ρ') (hFsJ ψ) (hEsJ ψ) rfl
      (fun ρ' hρ' => (hFssOkP ψ ρ' hρ').1) (fun ρ' hρ' bs hsp => ?_) ρ
    exact hfold ψ ρ' ((hiff ψ ρ').mpr hρ') bs hsp
  have hval : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      UnderTowerValid ρ
        (sumInjAtAV (w ψ) (uChains (FssR ψ)) ((((dsA ψ).drop nP).map (·.2.2))).length
          (numeralAV J) (mkTowerGoU (w ψ) (((dsA ψ).drop nP).map (·.2.2)) (idxEqAV [])))
        ((dsA ψ).take nP ++ (dsA ψ).drop nP) := fun ψ ρ =>
    ctorUnderValid (hlenA ψ) (fun ρ' => hokTyA ψ ρ') (hFsJ ψ)
      (fun ρ' hρ' => (hFssOkP ψ ρ' hρ').2) ρ
  have hz : ∀ ψ : Name → Nat, ∀ d ∈ (dsA ψ).take nP ++ (dsA ψ).drop nP,
      (w ψ = 0 ↔ d.2.1 = 0) := by
    intro ψ d hd
    rw [List.take_append_drop] at hd
    rw [← hw ψ]
    exact hbitsA ψ d hd
  -- the restored type reads at the cons's model as at the current one
  have hreadC : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvA.name A)
        ⟨.ctorInfo cvA nP nF :: env.consts⟩ ψ 0 cvA.type
        = some (mkPisAV (dsR ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .ctorInfo cvA nP nF) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hCD.read ψ)
  have hnresC : ConLeche.reservedBasisNames.contains
      (ConstantInfo.ctorInfo cvA nP nF).name = false := hfd.nres
  have hpshapeC : (ConstantInfo.ctorInfo cvA nP nF).name.isProjFnShape = false := hfd.pshape
  -- the leaf's membership in the RESTORED tower, through the auxiliary one
  have hmem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (mkPisAV (dsR ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))) := by
    intro ψ ρ
    have h1 := sumMkAV_mem (V := V) (hz ψ) (hpre ψ ρ)
    rw [List.take_append_drop] at h1
    rw [← interp_mkPisAV_restored (hlenA ψ) (hlenR ψ) (htakeR ψ) (hbitsR ψ) (hagree ψ) ρ]
    exact h1
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .ctorInfo cvA nP nF)
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
    show sumMkAV _ J (dsA ψ₁) (((dsA ψ₁).drop nP).map (·.2.2)) (uChains (FssR ψ₁))
      = sumMkAV _ J (dsA ψ₂) (((dsA ψ₂).drop nP).map (·.2.2)) (uChains (FssR ψ₂))
    rw [hwe, hFe, hparamsA ψ₁ ψ₂ hφ']
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
    exact hmem ψ ρ
  · -- `caps_ok`: the block claims nothing, and the cons stores a
    -- CONSTRUCTOR at the name the obligation is taken at
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .ctorInfo cvA nP nF) (A := A)
      (T := cvA.name) hfresh (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeC
      (Or.inr fun _ _ h => nomatch h)
      (fun T' cvT' caps' hf _ hres hcape => hE₀ T' cvT' caps' hf hcape hres)
      m₂ hac ?_
    intro cvT' caps' hf _
    have hself := ConLeche.Env.find?_cons_self (ConstantInfo.ctorInfo cvA nP nF) env
    rw [show (ConstantInfo.ctorInfo cvA nP nF).name = cvA.name from rfl] at hself
    exact nomatch (hself.symm.trans hf)


/-! ## The loop over the restored constructors -/

/-- **One restored constructor's inputs at the prefix model** `mp₁`
(the loop's per-constructor hypotheses; the reading law supplies
them): the door's facts, the constructor's data at the RESTORED
domains `dsR` at `mp₁`, the auxiliary constructor's term-level facts
at the AUXILIARY domains `dsA`, the two domain lists' agreement at
every fitting prefix (the pin identification, at `mp₁`), the fold to
the auxiliary block's fibre, and the chain facts. -/
structure NestedCtorInput {env₁ : Env} (mp₁ : EnvModelM V μ env₁) (F : Nat) (T : Name)
    (lps : List Name) (nP nF nIdx J mem : Nat) (resSort : Level) (isProp large : Bool)
    (cvA : ConstantVal) (W w : (Name → Nat) → Nat)
    (Idss FssR Ess' : (Name → Nat) → List (List AnnotTerm))
    (ppsM dsA dsR : (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (Es : (Name → Nat) → List AnnotTerm) (idxArgs : List Expr) (srcs : List (Option Nat)) :
    Prop where
  door : ConLeche.FrontDoorFacts μ F env₁ cvA cvA
  lpsC : cvA.levelParams = lps
  Tfound : (env₁.find? T).isSome = true
  idxRes : ∀ e ∈ idxArgs, e.constsResolve env₁ = true
  wEq : ∀ ψ : Name → Nat, resSort.eval ψ = w ψ
  CD : CtorDataI mp₁.base2 T lps cvA nP nF nIdx resSort isProp large idxArgs dsR Es srcs
  lenA : ∀ ψ : Name → Nat, (dsA ψ).length = nP + nF
  okTyA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    WellDenotedV V ρ (mkPisAV (dsA ψ) (ctorBodyAVI mp₁.base2 T nP nF ψ (Es ψ)))
  bitsA : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ dsA ψ →
    (resSort.eval ψ = 0 ↔ d.2.1 = 0)
  belowA : ∀ ψ : Name → Nat, DomsBelow 0 (dsA ψ)
  paramsA : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) → dsA ψ₁ = dsA ψ₂
  lenR : ∀ ψ : Name → Nat, (dsR ψ).length = (dsA ψ).length
  takeR : ∀ ψ : Name → Nat, (dsR ψ).take nP = (dsA ψ).take nP
  bitsR : ∀ (ψ : Name → Nat) (i : Nat), ((dsR ψ).getD i default).2.1 = ((dsA ψ).getD i default).2.1
  agree : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (((dsA ψ).take nP).map (·.2.2)).reverse ρ →
    ∀ l, l < nF → ∀ fs₁ : List V, fs₁.length = l →
      SpineFit ρ ((((dsA ψ).drop nP).map (·.2.2)).take l) fs₁ →
      SpineFit ρ ((((dsR ψ).drop nP).map (·.2.2)).take l) fs₁ →
      interp V (consList fs₁ ρ) ((dsA ψ).getD (nP + l) default).2.2
        = interp V (consList fs₁ ρ) ((dsR ψ).getD (nP + l) default).2.2
  fold : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (((ppsM ψ).take nP).map (·.2.2)).reverse ρ →
    ∀ bs : List V, SpineFit ρ (((dsA ψ).drop nP).map (·.2.2)) bs →
      interp V (consList bs ρ) (ctorBodyAVI mp₁.base2 T nP nF ψ (Es ψ))
        = sumSet (w ψ) (sumFibre (w ψ)
            (consList (idxValsAt ρ [tagTupleAV (W ψ) mem nF (Idss ψ) (Es ψ)] bs) ρ)
            (rChains 1 1 (FssR ψ) (Ess' ψ)))
  FsJ : ∀ ψ : Name → Nat, (FssR ψ)[J]? = some (((dsA ψ).drop nP).map (·.2.2))
  EsJ : ∀ ψ : Name → Nat, (Ess' ψ)[J]? = some [tagTupleAV (W ψ) mem nF (Idss ψ) (Es ψ)]
  FssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) → w ψ₁ = w ψ₂ ∧ FssR ψ₁ = FssR ψ₂
  FssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ FssR ψ, FieldsBelow nP Fs
  frameIff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (((ppsM ψ).take nP).map (·.2.2)).reverse ρ ↔
      Sat V (((dsA ψ).take nP).map (·.2.2)).reverse ρ
  FssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (((dsA ψ).take nP).map (·.2.2)).reverse ρ →
    SumFieldsOkB (w ψ) ρ (FssR ψ) ∧ SumFieldsValid ρ (FssR ψ)

/-- A reading at the environment before a fresh constructor's cons is a
reading after it (no boundedness premise: `denoteMeta_env_mono`). -/
theorem cons_hde {acval : Name → (Name → Nat) → AnnotTerm} {cv : ConstantVal} {nP nF : Nat}
    {A : (Name → Nat) → AnnotTerm} (hfresh : env.find? cv.name = none) :
    ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta acval env ψ dp e = some ea →
      denoteMeta (acvalWith acval cv.name A) ⟨.ctorInfo cv nP nF :: env.consts⟩ ψ dp e = some ea := by
  intro ψ dp e ea h
  refine denoteMeta_env_mono (findPreserved_cons (c₀ := .ctorInfo cv nP nF) hfresh)
    (litGuardsMono_cons (c₀ := .ctorInfo cv nP nF) hfresh)
    (ConLeche.Verify.findProj?_cons_of_base_none (c₀ := .ctorInfo cv nP nF) (fun _ h => nomatch h))
    dp e ?_
  rw [denoteMeta_acvalWith_fresh hfresh]
  exact h

/-- The leaf constructor `i` of the loop is consed with: the sum route's
injection at its member-local tag over the auxiliary domains and its
member's chains. -/
@[expose] def nestedCtorLeaf (w : (Name → Nat) → Nat) (Jof : Nat → Nat) (nP : Nat)
    (dsAOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (FssROf : Nat → (Name → Nat) → List (List AnnotTerm)) (i : Nat) (ψ : Name → Nat) : AnnotTerm :=
  sumMkAV (w ψ) (Jof i) (dsAOf i ψ) (((dsAOf i ψ).drop nP).map (·.2.2)) (uChains (FssROf i ψ))

/-- Two constructors at distinct positions of a name-nodup list have distinct names. -/
theorem names_ne_of_nodup₃ {cs : List (ConstantVal × Nat × Nat)}
    (hnd : (cs.map (·.1.name)).Nodup) {i j : Nat} {ci cj : ConstantVal × Nat × Nat}
    (hi : cs[i]? = some ci) (hj : cs[j]? = some cj) (hne : i ≠ j) :
    ci.1.name ≠ cj.1.name := by
  have hil : i < cs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjl : j < cs.length := (List.getElem?_eq_some_iff.mp hj).1
  have hp := List.pairwise_iff_getElem.mp hnd
  have hi' : cs[i] = ci := by
    have := List.getElem?_eq_getElem hil; rw [hi] at this; exact (Option.some.inj this).symm
  have hj' : cs[j] = cj := by
    have := List.getElem?_eq_getElem hjl; rw [hj] at this; exact (Option.some.inj this).symm
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := hp i j (by simpa using hil) (by simpa using hjl) hlt
    simp only [List.getElem_map, hi', hj'] at this
    exact this
  · have := hp j i (by simpa using hjl) (by simpa using hil) hgt
    simp only [List.getElem_map, hi', hj'] at this
    exact fun h => this h.symm

section Loop

variable {F : Nat} {env₁ : Env} (mp₁ : EnvModelM V μ env₁) {lps : List Name} {nP : Nat}
  {isProp large : Bool} {W w : (Name → Nat) → Nat}
  {Tof : Nat → Name} {nIdxOf Jof memOf : Nat → Nat} {resSortOf : Nat → Level}
  {IdssOf FssROf EssOf : Nat → (Name → Nat) → List (List AnnotTerm)}
  {ppsOf dsAOf dsROf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {EsOf : Nat → (Name → Nat) → List AnnotTerm} {idxOf : Nat → List Expr}
  {srcsOf : Nat → List (Option Nat)}


/-- **The loop's step** (the induction over the remaining constructors,
`stageMutualCtorsGo`'s twin): the constructors `cs[k], cs[k+1], …` are
consed in order onto an environment extending the prefix one, where
the earlier ones are already stored with their leaves and the later
ones are fresh; every reading at the prefix model survives (`hde`),
and the model agrees with the prefix model off the consed names. -/
theorem stageNestedCtorsGo
    {cs : List (ConstantVal × Nat × Nat)}
    (hnd : (cs.map (·.1.name)).Nodup)
    (hnP : ∀ c ∈ cs, c.2.1 = nP)
    (hin : ∀ (i : Nat) (c : ConstantVal × Nat × Nat), cs[i]? = some c →
      NestedCtorInput mp₁ F (Tof i) lps nP c.2.2 (nIdxOf i) (Jof i) (memOf i) (resSortOf i)
        isProp large c.1 W w (IdssOf i) (FssROf i) (EssOf i) (ppsOf i) (dsAOf i) (dsROf i)
        (EsOf i) (idxOf i) (srcsOf i))
    (done : List Name) (hdone : ∀ n : Name, (env₁.find? n).isSome = true → n ∉ done) :
    ∀ (rest : List (ConstantVal × Nat × Nat)) (k : Nat) (env : Env) (mp : EnvModelM V μ env),
      (∀ i, rest[i]? = cs[k + i]?) → k + rest.length = cs.length →
      ConLeche.EtaFamiliesClosed env →
      FindPreserved env₁ env →
      (∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
        denoteMeta mp₁.base2.acval env₁ ψ dp e = some ea →
        denoteMeta mp.base2.acval env ψ dp e = some ea) →
      (∀ n : Name, n ∉ done → (∀ (i : Nat) (c : ConstantVal × Nat × Nat), i < k → cs[i]? = some c →
        n ≠ c.1.name) → mp.base2.acval n = mp₁.base2.acval n) →
      (∀ (i : Nat) (c : ConstantVal × Nat × Nat), i < k → cs[i]? = some c →
        env.find? c.1.name = some (.ctorInfo c.1 nP c.2.2) ∧
        ∀ ψ : Name → Nat, mp.base2.acval c.1.name ψ = nestedCtorLeaf w Jof nP dsAOf FssROf i ψ) →
      (∀ (i : Nat) (c : ConstantVal × Nat × Nat), k ≤ i → cs[i]? = some c →
        env.find? c.1.name = none) →
      ∃ mp' : EnvModelM V μ (ConLeche.consNestedCtors rest env),
        ConLeche.EtaFamiliesClosed (ConLeche.consNestedCtors rest env) ∧
        FindPreserved env₁ (ConLeche.consNestedCtors rest env) ∧
        (∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
          denoteMeta mp₁.base2.acval env₁ ψ dp e = some ea →
          denoteMeta mp'.base2.acval (ConLeche.consNestedCtors rest env) ψ dp e = some ea) ∧
        (∀ n : Name, n ∉ done → (∀ c ∈ cs, n ≠ c.1.name) →
          mp'.base2.acval n = mp₁.base2.acval n) ∧
        (∀ n : Name, (∀ c ∈ rest, n ≠ c.1.name) → mp'.base2.acval n = mp.base2.acval n) ∧
        FindPreserved env (ConLeche.consNestedCtors rest env) ∧
        (∀ (i : Nat) (c : ConstantVal × Nat × Nat), cs[i]? = some c →
          (ConLeche.consNestedCtors rest env).find? c.1.name = some (.ctorInfo c.1 nP c.2.2) ∧
          ∀ ψ : Name → Nat, mp'.base2.acval c.1.name ψ = nestedCtorLeaf w Jof nP dsAOf FssROf i ψ)
  | [], k, env, mp, _, hk, hE, hF, hde, hag, hcons, _ => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    refine ⟨mp, hE, hF, hde, fun n hd hn => hag n hd fun i c _ hc => hn c (List.mem_of_getElem? hc),
      fun _ _ => rfl, fun h => h, ?_⟩
    intro i c hc
    exact hcons i c (List.getElem?_eq_some_iff.mp hc).1 hc
  | c :: rest, k, env, mp, hrest, hk, hE, hF, hde, hag, hcons, hpend => by
    have hck : cs[k]? = some c := by
      have := hrest 0; simpa using this.symm
    have hklt : k < cs.length := (List.getElem?_eq_some_iff.mp hck).1
    have hcmem : c ∈ cs := List.mem_of_getElem? hck
    obtain ⟨cvA, nP', nF⟩ := c
    obtain rfl := (hnP _ hcmem : nP' = nP).symm
    have I := hin k _ hck
    have hfresh : env.find? cvA.name = none := hpend k _ (Nat.le_refl _) hck
    -- names found at the prefix environment are no constructor's
    have hneC : ∀ n : Name, (env₁.find? n).isSome = true →
        ∀ (i : Nat) (c' : ConstantVal × Nat × Nat), cs[i]? = some c' → n ≠ c'.1.name := by
      intro n hn i c' hc' heq
      have := (hin i c' hc').door.fresh
      rw [heq, this] at hn
      exact nomatch hn
    have hag₁ : ∀ n : Name, (env₁.find? n).isSome = true → mp.base2.acval n = mp₁.base2.acval n :=
      fun n hn => hag n (hdone n hn) fun i c' _ hc' => hneC n hn i c' hc'
    have hTag : mp.base2.acval (Tof k) = mp₁.base2.acval (Tof k) := hag₁ _ I.Tfound
    have hbody : ∀ ψ, ctorBodyAVI mp.base2 (Tof k) nP nF ψ (EsOf k ψ)
        = ctorBodyAVI mp₁.base2 (Tof k) nP nF ψ (EsOf k ψ) := by
      intro ψ; unfold ctorBodyAVI; rw [hTag]
    -- the step
    obtain ⟨mpC, hacC⟩ := stageNestedCtor (J := Jof k) (mem := memOf k) (W := W) (w := w)
      (Idss := IdssOf k) (FssR := FssROf k) (Ess' := EssOf k) (ppsM := ppsOf k)
      mp hE I.door hfresh (constsResolve_of_findPreserved hF _ I.door.resolve) I.lpsC I.wEq
      (CtorDataI.crossEnv hag₁ hde I.Tfound I.CD) I.lenA
      (fun ψ ρ => by rw [hbody]; exact I.okTyA ψ ρ) I.bitsA I.belowA I.paramsA I.lenR I.takeR
      I.bitsR I.agree (fun ψ ρ hρ bs hsp => by rw [hbody]; exact I.fold ψ ρ hρ bs hsp)
      I.FsJ I.EsJ I.FssParams I.FssBelow I.frameIff I.FssOkP
    -- the invariants at the extension
    have hE' : ConLeche.EtaFamiliesClosed ⟨.ctorInfo cvA nP nF :: env.consts⟩ :=
      hE.cons_nonind hfresh (fun _ _ heq => nomatch heq)
    have hF' : FindPreserved env₁ ⟨.ctorInfo cvA nP nF :: env.consts⟩ :=
      fun h => findPreserved_cons (c₀ := .ctorInfo cvA nP nF) hfresh (hF h)
    have hde' : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
        denoteMeta mp₁.base2.acval env₁ ψ dp e = some ea →
        denoteMeta mpC.base2.acval ⟨.ctorInfo cvA nP nF :: env.consts⟩ ψ dp e = some ea := by
      intro ψ dp e ea h
      rw [hacC]
      exact cons_hde hfresh ψ dp e (hde ψ dp e h)
    have hag' : ∀ n : Name, n ∉ done → (∀ (i : Nat) (c' : ConstantVal × Nat × Nat), i < k + 1 →
        cs[i]? = some c' → n ≠ c'.1.name) → mpC.base2.acval n = mp₁.base2.acval n := by
      intro n hd hn
      rw [hacC]
      show acvalWith mp.base2.acval cvA.name _ n = _
      rw [acvalWith_ne (hn k _ (Nat.lt_succ_self _) hck)]
      exact hag n hd fun i c' hi hc' => hn i c' (Nat.lt_succ_of_lt hi) hc'
    have hcons' : ∀ (i : Nat) (c' : ConstantVal × Nat × Nat), i < k + 1 → cs[i]? = some c' →
        (⟨.ctorInfo cvA nP nF :: env.consts⟩ : Env).find? c'.1.name
          = some (.ctorInfo c'.1 nP c'.2.2) ∧
        ∀ ψ : Name → Nat, mpC.base2.acval c'.1.name ψ = nestedCtorLeaf w Jof nP dsAOf FssROf i ψ := by
      intro i c' hi hc'
      rcases Nat.lt_or_ge i k with hlt | hge
      · obtain ⟨hfi, hleafi⟩ := hcons i c' hlt hc'
        have hne : c'.1.name ≠ cvA.name := names_ne_of_nodup₃ hnd hc' hck (by omega)
        refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfi, fun ψ => ?_⟩
        rw [hacC]
        show acvalWith mp.base2.acval cvA.name _ c'.1.name ψ = _
        rw [acvalWith_ne hne]
        exact hleafi ψ
      · have hik : i = k := by omega
        subst hik
        obtain rfl := Option.some.inj (hck.symm.trans hc')
        refine ⟨ConLeche.Env.find?_cons_self (.ctorInfo cvA nP nF) env, fun ψ => ?_⟩
        rw [hacC]
        show acvalWith mp.base2.acval cvA.name _ cvA.name ψ = _
        rw [acvalWith_self]
        rfl
    have hpend' : ∀ (i : Nat) (c' : ConstantVal × Nat × Nat), k + 1 ≤ i → cs[i]? = some c' →
        (⟨.ctorInfo cvA nP nF :: env.consts⟩ : Env).find? c'.1.name = none := by
      intro i c' hi hc'
      have hne : cvA.name ≠ c'.1.name := names_ne_of_nodup₃ hnd hck hc' (by omega)
      rw [ConLeche.Env.find?_cons]
      split
      · next h => exact absurd h hne
      · exact hpend i c' (by omega) hc'
    have hrest' : ∀ i, rest[i]? = cs[k + 1 + i]? := by
      intro i
      have := hrest (i + 1)
      rwa [show k + (i + 1) = k + 1 + i from by omega] at this
    obtain ⟨mp', hE'', hF'', hde'', hag'', hagS, hFS, hcons''⟩ :=
      stageNestedCtorsGo hnd hnP hin done hdone rest (k + 1) _ mpC hrest' (by simp at hk; omega)
        hE' hF' hde' hag' hcons' hpend'
    refine ⟨mp', hE'', hF'', hde'', hag'', ?_, ?_, hcons''⟩
    · intro n hn
      rw [hagS n (fun c' hc' => hn c' (List.mem_cons_of_mem _ hc')), hacC]
      exact acvalWith_ne (hn _ List.mem_cons_self)
    · exact fun h => hFS (findPreserved_cons (c₀ := .ctorInfo cvA nP nF) hfresh h)

/-- **The loop over the restored constructors**: consed in order onto
the prefix environment (`consNestedCtors`), with the prefix model's
readings surviving, the agreement off the consed names, and every
constructor stored with its auxiliary leaf. -/
theorem stageNestedCtors
    {cs : List (ConstantVal × Nat × Nat)}
    (hnd : (cs.map (·.1.name)).Nodup)
    (hnP : ∀ c ∈ cs, c.2.1 = nP)
    (hin : ∀ (i : Nat) (c : ConstantVal × Nat × Nat), cs[i]? = some c →
      NestedCtorInput mp₁ F (Tof i) lps nP c.2.2 (nIdxOf i) (Jof i) (memOf i) (resSortOf i)
        isProp large c.1 W w (IdssOf i) (FssROf i) (EssOf i) (ppsOf i) (dsAOf i) (dsROf i)
        (EsOf i) (idxOf i) (srcsOf i))
    (hE : ConLeche.EtaFamiliesClosed env₁) :
    ∃ mp₂ : EnvModelM V μ (ConLeche.consNestedCtors cs env₁),
      ConLeche.EtaFamiliesClosed (ConLeche.consNestedCtors cs env₁) ∧
      FindPreserved env₁ (ConLeche.consNestedCtors cs env₁) ∧
      (∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
        denoteMeta mp₁.base2.acval env₁ ψ dp e = some ea →
        denoteMeta mp₂.base2.acval (ConLeche.consNestedCtors cs env₁) ψ dp e = some ea) ∧
      (∀ n : Name, (∀ c ∈ cs, n ≠ c.1.name) → mp₂.base2.acval n = mp₁.base2.acval n) ∧
      (∀ (i : Nat) (c : ConstantVal × Nat × Nat), cs[i]? = some c →
        (ConLeche.consNestedCtors cs env₁).find? c.1.name = some (.ctorInfo c.1 nP c.2.2) ∧
        ∀ ψ : Name → Nat, mp₂.base2.acval c.1.name ψ = nestedCtorLeaf w Jof nP dsAOf FssROf i ψ) := by
  obtain ⟨mp₂, hE₂, hF₂, hde₂, hag₂, -, -, hcons₂⟩ :=
    stageNestedCtorsGo mp₁ hnd hnP hin [] (fun _ _ h => List.not_mem_nil h) cs 0 env₁ mp₁
      (fun i => by rw [Nat.zero_add]) (by omega)
      hE (fun h => h) (fun _ _ _ _ h => h) (fun _ _ _ => rfl)
      (fun i _ hi _ => absurd hi (Nat.not_lt_zero i))
      (fun i c _ hc => (hin i c hc).door.fresh)
  exact ⟨mp₂, hE₂, hF₂, hde₂, fun n hn => hag₂ n List.not_mem_nil hn, hcons₂⟩

end Loop

/-! ## The loop over the members -/

omit [SetTheory V] in
/-- The constructors' conses split at an append. -/
theorem consNestedCtors_append :
    ∀ (l₁ l₂ : List (ConstantVal × Nat × Nat)) (env : Env),
      ConLeche.consNestedCtors (l₁ ++ l₂) env
        = ConLeche.consNestedCtors l₂ (ConLeche.consNestedCtors l₁ env)
  | [], _, _ => rfl
  | (cv, nP, nF) :: l₁, l₂, env => by
    show ConLeche.consNestedCtors (l₁ ++ l₂) ⟨.ctorInfo cv nP nF :: env.consts⟩ = _
    exact consNestedCtors_append l₁ l₂ _

section Members

variable {F : Nat} {env₁ : Env} (mp₁ : EnvModelM V μ env₁) {lps : List Name} {nP : Nat}
  {isProp large : Bool} {W w : (Name → Nat) → Nat}
  {Tof : Nat → Name} {nIdxOf : Nat → Nat} {resSortOf : Nat → Level}
  {Idss : (Name → Nat) → List (List AnnotTerm)}
  {FssROf EssOf : Nat → (Name → Nat) → List (List AnnotTerm)}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {dsAOf dsROf : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {EsOf : Nat → Nat → (Name → Nat) → List AnnotTerm} {idxOf : Nat → Nat → List Expr}
  {srcsOf : Nat → Nat → List (Option Nat)}

/-- **The loop over the members** (the induction over the remaining
members, the already-consed ones `pre`): member `mm`'s constructors
are consed by `stageNestedCtorsGo` at the member-local tags `j` over
the member's chains `FssROf mm`, on top of the earlier members'. -/
theorem stageNestedMembersGo {ctorsR : List (List (ConstantVal × Nat × Nat))}
    (hnd : (ctorsR.flatten.map (·.1.name)).Nodup)
    (hnP : ∀ c ∈ ctorsR.flatten, c.2.1 = nP)
    (hin : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), (ctorsR.getD mm [])[j]? = some c →
      NestedCtorInput mp₁ F (Tof mm) lps nP c.2.2 (nIdxOf mm) j mm (resSortOf mm) isProp large c.1
        W w Idss (FssROf mm) (EssOf mm) (ppsOf mm) (dsAOf mm j) (dsROf mm j) (EsOf mm j)
        (idxOf mm j) (srcsOf mm j)) :
    ∀ (rest pre : List (List (ConstantVal × Nat × Nat))) (env : Env) (mp : EnvModelM V μ env),
      ctorsR = pre ++ rest →
      ConLeche.EtaFamiliesClosed env →
      FindPreserved env₁ env →
      (∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
        denoteMeta mp₁.base2.acval env₁ ψ dp e = some ea →
        denoteMeta mp.base2.acval env ψ dp e = some ea) →
      (∀ n : Name, (∀ c ∈ pre.flatten, n ≠ c.1.name) → mp.base2.acval n = mp₁.base2.acval n) →
      (∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), mm < pre.length →
        (ctorsR.getD mm [])[j]? = some c →
        env.find? c.1.name = some (.ctorInfo c.1 nP c.2.2) ∧
        ∀ ψ : Name → Nat, mp.base2.acval c.1.name ψ
          = nestedCtorLeaf w id nP (dsAOf mm) (fun _ => FssROf mm) j ψ) →
      (∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), pre.length ≤ mm →
        (ctorsR.getD mm [])[j]? = some c → env.find? c.1.name = none) →
      ∃ mp' : EnvModelM V μ (ConLeche.consNestedCtors rest.flatten env),
        ConLeche.EtaFamiliesClosed (ConLeche.consNestedCtors rest.flatten env) ∧
        FindPreserved env₁ (ConLeche.consNestedCtors rest.flatten env) ∧
        (∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
          denoteMeta mp₁.base2.acval env₁ ψ dp e = some ea →
          denoteMeta mp'.base2.acval (ConLeche.consNestedCtors rest.flatten env) ψ dp e = some ea) ∧
        (∀ n : Name, (∀ c ∈ ctorsR.flatten, n ≠ c.1.name) →
          mp'.base2.acval n = mp₁.base2.acval n) ∧
        (∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), (ctorsR.getD mm [])[j]? = some c →
          (ConLeche.consNestedCtors rest.flatten env).find? c.1.name
            = some (.ctorInfo c.1 nP c.2.2) ∧
          ∀ ψ : Name → Nat, mp'.base2.acval c.1.name ψ
            = nestedCtorLeaf w id nP (dsAOf mm) (fun _ => FssROf mm) j ψ)
  | [], pre, env, mp, hpre, hE, hF, hde, hag, hcons, _ => by
    rw [List.append_nil] at hpre
    subst hpre
    refine ⟨mp, hE, hF, hde, hag, ?_⟩
    intro mm j c hc
    have hmm : mm < ctorsR.length := by
      rcases Nat.lt_or_ge mm ctorsR.length with h | h
      · exact h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h] at hc
        simp at hc
    exact hcons mm j c hmm hc
  | cs :: rest, pre, env, mp, hpre, hE, hF, hde, hag, hcons, hpend => by
    have hcs : ctorsR.getD pre.length [] = cs := by
      rw [hpre, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self]
      rfl
    have hflat : ctorsR.flatten = pre.flatten ++ (cs ++ rest.flatten) := by
      rw [hpre, List.flatten_append, List.flatten_cons]
    -- the names of member `pre.length` are pairwise distinct and disjoint from the others
    have hnd' := hnd
    rw [hflat, List.map_append, List.map_append] at hnd'
    obtain ⟨hndPre, hndCsRest, hdisjPre⟩ := List.nodup_append.mp hnd'
    obtain ⟨hndCs, hndRest, hdisjRest⟩ := List.nodup_append.mp hndCsRest
    have hnPcs : ∀ c ∈ cs, c.2.1 = nP := fun c hc =>
      hnP c (by rw [hflat]; exact List.mem_append_right _ (List.mem_append_left _ hc))
    have hincs : ∀ (i : Nat) (c : ConstantVal × Nat × Nat), cs[i]? = some c →
        NestedCtorInput mp₁ F (Tof pre.length) lps nP c.2.2 (nIdxOf pre.length) i pre.length
          (resSortOf pre.length) isProp large c.1 W w Idss (FssROf pre.length) (EssOf pre.length)
          (ppsOf pre.length) (dsAOf pre.length i) (dsROf pre.length i) (EsOf pre.length i)
          (idxOf pre.length i) (srcsOf pre.length i) := by
      intro i c hc
      have := hin pre.length i c (by rw [hcs]; exact hc)
      exact this
    -- a name found at the prefix environment is no earlier member's constructor's
    have hdone : ∀ n : Name, (env₁.find? n).isSome = true → n ∉ pre.flatten.map (·.1.name) := by
      intro n hn hmem
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
      obtain ⟨mm, hmm⟩ := List.getElem?_of_mem hl
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hcl
      have hmmk : mm < pre.length := (List.getElem?_eq_some_iff.mp hmm).1
      have hc' : (ctorsR.getD mm [])[j]? = some c := by
        rw [hpre, List.getD_eq_getElem?_getD, List.getElem?_append_left hmmk, hmm]
        exact hj
      have := (hin mm j c hc').door.fresh
      rw [this] at hn
      exact nomatch hn
    obtain ⟨mpC, hEC, hFC, hdeC, hagC, hagS, hFS, hconsC⟩ :=
      stageNestedCtorsGo (Tof := fun _ => Tof pre.length) (nIdxOf := fun _ => nIdxOf pre.length)
        (Jof := id) (memOf := fun _ => pre.length) (resSortOf := fun _ => resSortOf pre.length)
        (IdssOf := fun _ => Idss) (FssROf := fun _ => FssROf pre.length)
        (EssOf := fun _ => EssOf pre.length) (ppsOf := fun _ => ppsOf pre.length)
        (dsAOf := dsAOf pre.length) (dsROf := dsROf pre.length) (EsOf := EsOf pre.length)
        (idxOf := idxOf pre.length) (srcsOf := srcsOf pre.length)
        mp₁ hndCs hnPcs hincs (pre.flatten.map (·.1.name)) hdone cs 0 env mp
        (fun i => by rw [Nat.zero_add]) (by omega) hE hF hde
        (fun n hd _ => hag n fun c hc heq => hd (heq ▸ List.mem_map_of_mem hc))
        (fun i _ hi _ => absurd hi (Nat.not_lt_zero i))
        (fun i c _ hc => hpend pre.length i c (Nat.le_refl _) (by rw [hcs]; exact hc))
    -- the invariants at the extension
    have hpre' : ctorsR = (pre ++ [cs]) ++ rest := by rw [hpre, List.append_assoc]; rfl
    have hag' : ∀ n : Name, (∀ c ∈ (pre ++ [cs]).flatten, n ≠ c.1.name) →
        mpC.base2.acval n = mp₁.base2.acval n := by
      intro n hn
      rw [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] at hn
      exact hagC n (fun hm => by
          obtain ⟨c, hc, heq⟩ := List.mem_map.mp hm
          exact hn c (List.mem_append_left _ hc) heq.symm)
        (fun c hc => hn c (List.mem_append_right _ hc))
    have hcons' : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), mm < (pre ++ [cs]).length →
        (ctorsR.getD mm [])[j]? = some c →
        (ConLeche.consNestedCtors cs env).find? c.1.name = some (.ctorInfo c.1 nP c.2.2) ∧
        ∀ ψ : Name → Nat, mpC.base2.acval c.1.name ψ
          = nestedCtorLeaf w id nP (dsAOf mm) (fun _ => FssROf mm) j ψ := by
      intro mm j c hmm hc
      rw [List.length_append, List.length_singleton] at hmm
      rcases Nat.lt_or_ge mm pre.length with hlt | hge
      · obtain ⟨hfi, hleafi⟩ := hcons mm j c hlt hc
        have hmemPre : c ∈ pre.flatten := by
          rw [List.mem_flatten]
          refine ⟨ctorsR.getD mm [], ?_, List.mem_of_getElem? hc⟩
          rw [hpre, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
            List.getElem?_eq_getElem hlt]
          exact List.getElem_mem hlt
        have hne : ∀ c' ∈ cs, c.1.name ≠ c'.1.name := fun c' hc' =>
          hdisjPre _ (List.mem_map_of_mem hmemPre) _
            (List.mem_append_left _ (List.mem_map_of_mem hc'))
        refine ⟨hFS hfi, fun ψ => ?_⟩
        rw [hagS c.1.name hne]
        exact hleafi ψ
      · have hmm' : mm = pre.length := by omega
        subst hmm'
        rw [hcs] at hc
        exact hconsC j c hc
    have hpend' : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), (pre ++ [cs]).length ≤ mm →
        (ctorsR.getD mm [])[j]? = some c → (ConLeche.consNestedCtors cs env).find? c.1.name = none := by
      intro mm j c hmm hc
      rw [List.length_append, List.length_singleton] at hmm
      have hmemRest : c ∈ rest.flatten := by
        rw [List.mem_flatten]
        refine ⟨ctorsR.getD mm [], ?_, List.mem_of_getElem? hc⟩
        have hmmR : mm - (pre.length + 1) < rest.length := by
          have := (List.getElem?_eq_some_iff.mp hc).1
          rw [List.getD_eq_getElem?_getD] at this
          rcases hx : ctorsR[mm]? with _ | l
          · rw [hx] at this; simp at this
          · have hl := (List.getElem?_eq_some_iff.mp hx).1
            rw [hpre, List.length_append, List.length_cons] at hl
            omega
        rw [hpre, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
          show mm - pre.length = (mm - (pre.length + 1)) + 1 from by omega,
          List.getElem?_cons_succ, List.getElem?_eq_getElem hmmR]
        exact List.getElem_mem hmmR
      have hne : ∀ c' ∈ cs, c'.1.name ≠ c.1.name := fun c' hc' =>
        hdisjRest _ (List.mem_map_of_mem hc') _ (List.mem_map_of_mem hmemRest)
      rw [ConLeche.consNestedCtors_find?_of_ne hne]
      exact hpend mm j c (by omega) hc
    obtain ⟨mp', hE', hF', hde', hag'', hcons''⟩ :=
      stageNestedMembersGo hnd hnP hin rest (pre ++ [cs]) _ mpC hpre' hEC hFC hdeC hag' hcons' hpend'
    rw [List.flatten_cons, consNestedCtors_append]
    exact ⟨mp', hE', hF', hde', hag'', hcons''⟩

/-- **The restored constructors' loop over the members** at the prefix
model: every member's constructors consed at their member-local tags
over the member's chains, onto the prefix environment. -/
theorem stageNestedMembers {ctorsR : List (List (ConstantVal × Nat × Nat))}
    (hnd : (ctorsR.flatten.map (·.1.name)).Nodup)
    (hnP : ∀ c ∈ ctorsR.flatten, c.2.1 = nP)
    (hin : ∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), (ctorsR.getD mm [])[j]? = some c →
      NestedCtorInput mp₁ F (Tof mm) lps nP c.2.2 (nIdxOf mm) j mm (resSortOf mm) isProp large c.1
        W w Idss (FssROf mm) (EssOf mm) (ppsOf mm) (dsAOf mm j) (dsROf mm j) (EsOf mm j)
        (idxOf mm j) (srcsOf mm j))
    (hE : ConLeche.EtaFamiliesClosed env₁) :
    ∃ mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten env₁),
      ConLeche.EtaFamiliesClosed (ConLeche.consNestedCtors ctorsR.flatten env₁) ∧
      FindPreserved env₁ (ConLeche.consNestedCtors ctorsR.flatten env₁) ∧
      (∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
        denoteMeta mp₁.base2.acval env₁ ψ dp e = some ea →
        denoteMeta mp₂.base2.acval (ConLeche.consNestedCtors ctorsR.flatten env₁) ψ dp e = some ea) ∧
      (∀ n : Name, (∀ c ∈ ctorsR.flatten, n ≠ c.1.name) →
        mp₂.base2.acval n = mp₁.base2.acval n) ∧
      (∀ (mm j : Nat) (c : ConstantVal × Nat × Nat), (ctorsR.getD mm [])[j]? = some c →
        (ConLeche.consNestedCtors ctorsR.flatten env₁).find? c.1.name
          = some (.ctorInfo c.1 nP c.2.2) ∧
        ∀ ψ : Name → Nat, mp₂.base2.acval c.1.name ψ
          = nestedCtorLeaf w id nP (dsAOf mm) (fun _ => FssROf mm) j ψ) :=
  stageNestedMembersGo mp₁ hnd hnP hin ctorsR [] env₁ mp₁ rfl hE (fun h => h) (fun _ _ _ _ h => h)
    (fun _ _ => rfl) (fun _ _ _ h _ => absurd h (Nat.not_lt_zero _))
    (fun mm j c _ hc => (hin mm j c hc).door.fresh)

end Members

end ConLeche.Model
