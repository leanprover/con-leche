import ConLeche.SetP.Direct.DirectCtorFramesP

/-!
# The constructor's cons (task #175 W4c, P3 module 6, part 5)

`stageCtor`: the P step at the constructor's cons.  The leaf is
`directMkAV (resSort.eval ψ) (ds ψ) (Fs ψ)` over the constructor
type's peel; its two hereditary premises (`MkPre`, `UnderTowerValid`)
walk the parameter frame and the full frame from the constructor's
data and frames; the family application at the bottom folds the
former's real leaf along the parameters (`formerFold`), the frames
identified.
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AVExpr)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

omit [SetTheory V] in
theorem consN_eq_consList : ∀ (ts : List V) (ρ : Nat → V), consN ts ρ = consList ts ρ
  | [], _ => rfl
  | t :: ts, ρ => consN_eq_consList ts (cons t ρ)

omit [SetTheory V] in
/-- The reversed range under a consed spine recovers the spine. -/
theorem range_reverse_map_consList :
    ∀ (as : List V) (ρ : Nat → V),
      (List.range as.length).reverse.map (consList as ρ) = as
  | [], _ => rfl
  | a :: as, ρ => by
    rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, consList_cons]
    have h0 : consList as (cons a ρ) as.length = a := by
      have := consList_apply_add as (cons a ρ) 0
      rw [Nat.zero_add] at this
      rw [this]; rfl
    rw [h0, range_reverse_map_consList as (cons a ρ)]

/-- Two domain lists whose reversed contexts have the same satisfying
valuations fit the same spines. -/
theorem spineFit_iff_of_sat2_iff {Ds₁ Ds₂ : List AVExpr}
    (hlen : Ds₁.length = Ds₂.length)
    (hiff : ∀ ρ : Nat → V, Sat2 V Ds₁.reverse ρ ↔ Sat2 V Ds₂.reverse ρ)
    (ρ : Nat → V) (as : List V) (hl : as.length = Ds₁.length) :
    SpineFit ρ Ds₁ as ↔ SpineFit ρ Ds₂ as := by
  have key : ∀ (Ds₁ Ds₂ : List AVExpr), Ds₁.length = Ds₂.length →
      (∀ ρ : Nat → V, Sat2 V Ds₁.reverse ρ → Sat2 V Ds₂.reverse ρ) →
      ∀ (ρ : Nat → V) (as : List V), as.length = Ds₁.length →
      SpineFit ρ Ds₁ as → SpineFit ρ Ds₂ as := by
    intro Ds₁ Ds₂ hlen hsat ρ as hl h
    have h1 := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ) h
    rw [List.append_nil] at h1
    have h2 := spineFit_of_sat2 (Δ₀ := []) (Ds := Ds₂)
      (by rw [List.append_nil]; exact hsat _ h1)
    have e1 : (fun j => consList as ρ (j + Ds₂.length)) = ρ := by
      funext j; rw [← hlen, ← hl, consList_apply_add]
    have e2 : ((List.range Ds₂.length).reverse.map (consList as ρ)) = as := by
      rw [← hlen, ← hl]; exact range_reverse_map_consList as ρ
    rw [e1, e2] at h2
    exact h2
  exact ⟨key Ds₁ Ds₂ hlen (fun ρ => (hiff ρ).mp) ρ as hl,
    key Ds₂ Ds₁ hlen.symm (fun ρ => (hiff ρ).mpr) ρ as (by rw [hl, hlen])⟩

/-- The reversed constructor context's parameter entries are the
reversed parameter context's. -/
theorem getD_reverse_take {ds : List (Nat × Nat × AVExpr)} {nP nF : Nat}
    (hlen : ds.length = nP + nF) {i : Nat} (hi : i < nP) :
    ((ds.map (·.2.2)).reverse).getD (nP + nF - 1 - i) default
      = (((ds.take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
  have hil : i < ds.length := by omega
  rw [getD_reverse_of_peel hlen (by omega) (List.getElem?_eq_getElem hil),
    getD_reverse_of_peel (List.length_take_of_le (by omega)) hi
      (by rw [List.getElem?_take_of_lt hi]; exact List.getElem?_eq_getElem hil)]

/-! ## The constructor leaf's premises -/

/-- **The constructor leaf's hereditary premises**: `MkPre` along the
parameters and `UnderTowerValid` along the whole frame. -/
theorem ctorWalks {m : EnvS2Core V env} {T : Name} {cvT cvC : ConstantVal}
    {nP nF : Nat} {resSort : Level}
    {pps ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData m cvT nP resSort pps)
    (hCD : CtorData m T cvC nP nF resSort ds)
    (hleafT : ∀ ψ, m.acval T ψ
      = directTyAV (resSort.eval ψ) (pps ψ) (((ds ψ).drop nP).map (·.2.2)))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)))
    (ψ : Name → Nat) (ρ : Nat → V) :
    MkPre (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2))
        (ctorBodyAV m T nP nF ψ) ((ds ψ).take nP) ∧
      UnderTowerValid ρ (mkTowerGo (resSort.eval ψ) (((ds ψ).drop nP).map (·.2.2)))
        ((ds ψ).take nP ++ (ds ψ).drop nP) := by
  have hlenDs := hCD.len ψ
  have hlenP : ((ds ψ).take nP).length = nP := List.length_take_of_le (by omega)
  let Fs : List AVExpr := ((ds ψ).drop nP).map (·.2.2)
  -- the full frame's gradings
  have hst := stripPisAV_mkPisAV (ds ψ) (ctorBodyAV m T nP nF ψ)
  rw [hlenDs] at hst
  have htele := piTeleP_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleP_graded (V := V) htele (Δ₀ := []) (fun ρ _ => hCD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = nP + nF := by simp [hlenDs]
  have hΓplen : ((((ds ψ).take nP).map (·.2.2)).reverse).length = nP := by
    rw [List.length_reverse, List.length_map, hlenP]
  -- the parameter frame's gradings, from the full frame's
  have okΓp : ∀ i, i < nP → ∀ ρ : Nat → V,
      Sat2 V (((((ds ψ).take nP).map (·.2.2)).reverse).drop (nP - i)) ρ →
      AnnotOkP V ρ (((((ds ψ).take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default) := by
    intro i hi ρ hρ
    rw [← getD_reverse_take hlenDs hi]
    refine okΓ i (by omega) ρ ?_
    rw [drop_fields_eq hlenDs i (by omega)]
    exact hρ
  have hentP : ∀ i, i < nP → ∃ q, ((ds ψ).take nP)[i]? = some q ∧
      q.2.2 = ((((ds ψ).take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
    intro i hi
    have hil : i < ((ds ψ).take nP).length := by omega
    exact ⟨_, List.getElem?_eq_getElem hil,
      by rw [getD_reverse_of_peel hlenP hi (List.getElem?_eq_getElem hil)]⟩
  have hent : ∀ i, i < nP + nF → ∃ q, (ds ψ)[i]? = some q ∧
      q.2.2 = (((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - i) default := by
    intro i hi
    have hil : i < (ds ψ).length := by omega
    exact ⟨_, List.getElem?_eq_getElem hil,
      by rw [getD_reverse_of_peel hlenDs hi (List.getElem?_eq_getElem hil)]⟩
  -- the former's hereditary premise at the parameter frame
  have hpok : ∀ ρ₀ : Nat → V, ParamsOkT (resSort.eval ψ) ρ₀
      (((ds ψ).drop nP).map (·.2.2)) (pps ψ) := fun ρ₀ =>
    (formerWalks hFD (fun ψ' ρ' h => hfields ψ' ρ' ((hiff ψ' ρ').mp h)) ψ ρ₀).1
  constructor
  · -- `MkPre` along the parameters
    have hw := hereditaryWalk (V := V)
      (Q := fun ρ pds => MkPre (resSort.eval ψ) ρ Fs (ctorBodyAV m T nP nF ψ) pds)
      hΓplen hlenP hentP okΓp
      (fun ρ hρ => ?_)
      (fun ρ d ds' _ hok hrec => ⟨hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓplen]; exact Nat.le_refl _)]
        exact Sat2_nil V ρ)
    · rw [List.drop_zero] at hw; exact hw
    -- the base: the field chain and the family's fold
    refine ⟨(hfields ψ ρ hρ).1, fun bs hsp => ?_⟩
    -- the parameter values, from the frame
    have hρt : Sat2 V ((pps ψ).map (·.2.2)).reverse ρ := (hiff ψ ρ).mpr hρ
    have hspP := spineFit_of_sat2 (Δ₀ := []) (Ds := (pps ψ).map (·.2.2))
      (by rw [List.append_nil]; exact hρt)
    simp only [List.length_map, hFD.len ψ] at hspP
    have hlenB : bs.length = nF := by
      rw [hsp.length_eq]
      show ((((ds ψ).drop nP).map (·.2.2))).length = nF
      simp [hlenDs]
    -- the body: the family at the parameters
    have hK : VExpr.bvarsBelow 0 (m.acval T ψ).erase := m.cval_closedL T ψ
    have hbody : interp2 V (consList bs ρ) (ctorBodyAV m T nP nF ψ)
        = ((List.range nP).reverse.map ρ).foldl SetTheory.app
            (interp2 V (fun j => ρ (j + nP)) (m.acval T ψ)) := by
      unfold ctorBodyAV paramBvars
      have hlen' : ((List.range nP).reverse.map ρ).length = nP := by simp
      have := interp2_bvarSpine (V := V) ((List.range nP).reverse.map ρ)
        (ρ := fun j => ρ (j + nP)) (σ := consList bs ρ) (K := m.acval T ψ)
        (fun q => nP + nF - 1 - q)
        (fun q hq => by
          rw [consN_eq_consList, consList_range_reverse, hlen',
            show nP + nF - 1 - q = (nP - 1 - q) + bs.length from by omega,
            consList_apply_add])
        (interp2_closed (V := V) hK _ _)
      rw [hlen'] at this
      exact this
    rw [hbody, hleafT, formerFold (hpok _) hspP, consList_range_reverse]
  · -- `UnderTowerValid` along the whole frame
    have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds' => UnderTowerValid ρ (mkTowerGo (resSort.eval ψ) Fs) ds')
      hΓlen hlenDs hent okΓ
      (fun ρ' hρ' => ?_)
      (fun ρ d ds' _ hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓlen]; exact Nat.le_refl _)]
        exact Sat2_nil V ρ)
    · rw [List.take_append_drop]
      rw [List.drop_zero] at hw
      exact hw
    -- the base: the tupler is valid at the full frame, which is a
    -- fitting field spine over a parameter valuation
    rw [reverse_map_take_drop (ds ψ) nP] at hρ'
    have hspF := spineFit_of_sat2 (Δ₀ := (((ds ψ).take nP).map (·.2.2)).reverse)
      (Ds := ((ds ψ).drop nP).map (·.2.2)) hρ'
    have hlenF : (((ds ψ).drop nP).map (·.2.2)).length = nF := by simp [hlenDs]
    rw [hlenF] at hspF
    have hρp : Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse (fun j => ρ' (j + nF)) := by
      have := Sat2_drop hρ' nF
      rw [List.drop_append_of_le_length (by simp [hlenDs]),
        List.drop_eq_nil_of_le (by simp [hlenDs]), List.nil_append] at this
      exact this
    obtain ⟨hokB, hval⟩ := hfields ψ _ hρp
    have := mkTowerGo_validV (w := resSort.eval ψ) hval (fun hw => hokB.toBound hw) hspF
    rwa [consList_range_reverse] at this

/-! ## The cons -/

/-- **The P step at the constructor's cons.** -/
theorem stageCtor
    (hE₀ : ConLeche.EtaFamiliesClosed env)
    {F : Nat} {p : DirectParts} {envI envC : Env} {cvTa cvCa : ConstantVal}
    {sorts : List Level}
    (henvI : envI = ⟨.indInfo cvTa (ConLeche.directCaps p) :: env.consts⟩)
    (hTfresh₀ : env.find? p.cvT.name = none)
    (hTname : cvTa.name = p.cvT.name)
    (hlpsC : cvCa.levelParams = cvTa.levelParams)
    (mpI : EnvS2PM V μ envI)
    (hCtor : ConLeche.checkDirectCtor (ConLeche.fueledOps μ F) env envI p cvTa
      = .ok (envC, cvCa, sorts))
    -- the first projection slot is still empty at the extension (all
    -- slots are, until the entries are installed), so the block's
    -- family is η-complete there only when fieldless
    (hslot0 : 0 < p.nF → envC.find? (ConLeche.projFnName p.cvT.name 0) = none)
    {pps ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mpI.base2 cvTa p.nP p.resSort pps)
    (hCD : CtorData mpI.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds)
    (hleafT : ∀ ψ, mpI.base2.acval p.cvT.name ψ
      = directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2)))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2))) :
    ∃ mp' : EnvS2PM V μ envC,
      mp'.base2.acval = acvalWith mpI.base2.acval cvCa.name
        (fun ψ => directMkAV (p.resSort.eval ψ) (ds ψ) (((ds ψ).drop p.nP).map (·.2.2))) := by
  obtain ⟨hccv, rfl, -, -⟩ := ConLeche.checkDirectCtor_shape hCtor
  obtain ⟨hfind, hnres, hpshape, -, hlbt, hitf, type', -, -, hann', -, htr', -, -, hty⟩ :=
    ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  have hCname : cvCa.name = p.cvC.name := by rw [hty]
  have hfresh : envI.find? cvCa.name = none := by rw [hCname]; exact hfind
  have htr : cvCa.type.constsResolve envI = true := by rw [hty]; exact htr'
  have hcb : ConstsBound envI cvCa.type := constsBound_of_constsResolve _ htr
  have hfT : envI.find? p.cvT.name = some (.indInfo cvTa (ConLeche.directCaps p)) := by
    subst henvI
    have := ConLeche.Env.find?_cons_self (ConstantInfo.indInfo cvTa (ConLeche.directCaps p)) env
    rw [← hTname]
    exact this
  have hTC : p.cvT.name ≠ cvCa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  obtain ⟨hwfC, -, -⟩ := ConLeche.direct_ctor_wf mpI.base2.wf hCtor
  -- the leaf
  let Fs : (Name → Nat) → List AVExpr := fun ψ => ((ds ψ).drop p.nP).map (·.2.2)
  let A : (Name → Nat) → AVExpr :=
    fun ψ => directMkAV (p.resSort.eval ψ) (ds ψ) (Fs ψ)
  have hAbelow : ∀ ψ, VExpr.bvarsBelow 0 (A ψ).erase := fun ψ =>
    directMkAV_below (hCD.below ψ) ((DomsBelow.drop p.nP (hCD.below ψ)).fields)
      (by show p.nP + (((ds ψ).drop p.nP).map (·.2.2)).length = (ds ψ).length
          simp [hCD.len ψ])
  have hwalks := ctorWalks hFD hCD hleafT hiff hfields
  have hz : ∀ ψ, ∀ d ∈ (ds ψ).take p.nP ++ (ds ψ).drop p.nP,
      (p.resSort.eval ψ = 0 ↔ d.2.1 = 0) := by
    intro ψ d hd
    rw [List.take_append_drop] at hd
    exact hCD.bits ψ d hd
  have hFsmap : ∀ ψ, ((ds ψ).drop p.nP).map (·.2.2) = Fs ψ := fun _ => rfl
  -- the reading at the extension
  have hreadC : ∀ ψ : Name → Nat,
      denoteP (acvalWith mpI.base2.acval cvCa.name A)
        ⟨.ctorInfo cvCa p.nP p.nF :: envI.consts⟩ ψ 0 cvCa.type
        = some (mkPisAV (ds ψ) (ctorBodyAV mpI.base2 p.cvT.name p.nP p.nF ψ)) := fun ψ =>
    denoteP_cons_mono (c₀ := .ctorInfo cvCa p.nP p.nF) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hCD.read ψ)
  have hnresC : ConLeche.reservedBasisNames.contains
      (ConstantInfo.ctorInfo cvCa p.nP p.nF).name = false := by
    show ConLeche.reservedBasisNames.contains cvCa.name = false
    rw [hCname]; exact hnres
  have hpshapeC : (ConstantInfo.ctorInfo cvCa p.nP p.nF).name.isProjFnShape = false := by
    show cvCa.name.isProjFnShape = false
    rw [hCname]; exact hpshape
  refine declStepPM_of_ind_member_cons mpI (c₀ := .ctorInfo cvCa p.nP p.nF)
    (A := A) hfresh hnresC (Or.inr ⟨_, _, _, rfl⟩)
    (ConsHeadP.ofFresh hwfC (fun ψ => hAbelow ψ) hnresC
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- level dependence
    intro ψ₁ ψ₂ hφ
    have hφT : ∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q := by rw [← hlpsC]; exact hφ
    obtain ⟨-, hw⟩ := hFD.params ψ₁ ψ₂ hφT
    show directMkAV _ (ds ψ₁) (((ds ψ₁).drop p.nP).map (·.2.2))
      = directMkAV _ (ds ψ₂) (((ds ψ₂).drop p.nP).map (·.2.2))
    rw [hw, hCD.params ψ₁ ψ₂ hφ]
  · intro ψ ρ
    have := directMkAV_okP (V := V) (hz ψ) (hwalks ψ ρ).1 (hwalks ψ ρ).2
    rw [List.take_append_drop] at this
    exact this.1
  · intro ψ ρ
    have := directMkAV_okP (V := V) (hz ψ) (hwalks ψ ρ).1 (hwalks ψ ρ).2
    rw [List.take_append_drop] at this
    exact this.2
  · exact fun ψ => ⟨_, hreadC ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    exact hCD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    have := directMkAV_mem (V := V) (hz ψ) (hwalks ψ ρ).1
    rw [List.take_append_drop] at this
    exact this
  · -- `caps_ok`
    intro m₂ hac
    refine capsOkP_cons_direct mpI (c₀ := .ctorInfo cvCa p.nP p.nF) (A := A)
      (T := p.cvT.name) hfresh (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeC
      (Or.inr fun _ _ h => nomatch h) ?_ m₂ hac ?_
    · -- every other family's constructor is stored in the pre-block
      -- environment, hence here
      intro T' cvT' caps' hf hne hres hcape
      have hf₀ : env.find? T' = some (.indInfo cvT' caps') := by
        rw [henvI, ConLeche.Env.find?_cons] at hf
        split at hf
        · next heq =>
          exfalso
          apply hne
          have : cvTa.name = T' := heq
          rw [← this, hTname]
        · exact hf
      obtain ⟨cvC', hfC'⟩ := hE₀ T' cvT' caps' hf₀ hcape hres
      refine ⟨cvC', ?_⟩
      rw [henvI, ConLeche.Env.find?_cons_of_isSome
        (by show env.find? cvTa.name = none; rw [hTname]; exact hTfresh₀)
        (by rw [hfC']; rfl)]
      exact hfC'
    · intro cvT caps hf hres
      have hfT' : (⟨.ctorInfo cvCa p.nP p.nF :: envI.consts⟩ : Env).find? p.cvT.name
          = some (.indInfo cvTa (ConLeche.directCaps p)) := by
        rw [ConLeche.Env.find?_cons, if_neg (fun h => hTC h.symm)]
        exact hfT
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT'.symm.trans hf))
      have hFD₂ : FormerData m₂ cvTa p.nP p.resSort pps :=
        hFD.cross (c₀ := .ctorInfo cvCa p.nP p.nF) (A := A) hfresh
          (ConsCrossAt.ofNtc fun _ h => nomatch h)
          (constsBound_of_constsResolve _
            (mpI.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)).2.2.1) m₂ hac
      have hleafT₂ : ∀ ψ, m₂.acval p.cvT.name ψ
          = directTyAV (p.resSort.eval ψ) (pps ψ) (Fs ψ) := by
        intro ψ
        rw [hac]
        show acvalWith mpI.base2.acval cvCa.name A p.cvT.name ψ = _
        rw [acvalWith_ne hTC]
        exact hleafT ψ
      have hpok : ∀ ψ ρ, ParamsOkT (p.resSort.eval ψ) ρ (Fs ψ) (pps ψ) := fun ψ ρ =>
        (formerWalks hFD (fun ψ' ρ' h => hfields ψ' ρ' ((hiff ψ' ρ').mp h)) ψ ρ).1
      refine ⟨fun _ hfam φ' => ?_, fun hunit φ' => ?_⟩
      · -- η: fieldless (the slots are empty otherwise)
        rcases Nat.eq_zero_or_pos p.nF with hnF | hnF
        · have hFs0 : ∀ ψ, Fs ψ = [] := by
            intro ψ
            show ((ds ψ).drop p.nP).map (·.2.2) = []
            rw [List.drop_eq_nil_of_le (by rw [hCD.len ψ, hnF]; exact Nat.le_refl _)]
            rfl
          refine directEtaLawP0 (m := m₂) (T := p.cvT.name) (caps := ConLeche.directCaps p)
            (ds := ds) hnF ?_ ?_ hFD₂.read hFD₂.okTy ?_ ?_ ?_
          · intro ψ; rw [hleafT₂ ψ, hFs0 ψ]
          · intro ψ
            rw [show (ConLeche.directCaps p).etaCtor = cvCa.name from by rw [hCname]; rfl, hac]
            show acvalWith mpI.base2.acval cvCa.name A cvCa.name ψ = _
            rw [acvalWith_self]
            show directMkAV _ _ (Fs ψ) = _
            rw [hFs0 ψ]
          · intro ψ ρ; have := hpok ψ ρ; rwa [hFs0 ψ] at this
          · intro ψ ρ as hsp
            have hl := hsp.length_eq
            have hds : ds ψ = (ds ψ).take p.nP := by
              rw [List.take_of_length_le (by rw [hCD.len ψ, hnF]; exact Nat.le_refl _)]
            rw [hds]
            exact (spineFit_iff_of_sat2_iff (by simp [hFD.len ψ, hCD.len ψ, hnF])
              (hiff ψ) ρ as (by simpa using hl)).mp hsp
          · intro ψ; show p.nP = (pps ψ).length; rw [hFD.len ψ]
        · exfalso
          obtain ⟨-, -, hfP⟩ := hfam
          obtain ⟨cv, mI, rP, rules, hf0⟩ := hfP 0 hnF
          rw [hslot0 hnF] at hf0
          exact nomatch hf0
      · have hnF : p.nF = 0 := by
          have : (p.nF == 0) = true := hunit
          simpa using this
        have hFs0 : ∀ ψ, Fs ψ = [] := by
          intro ψ
          show ((ds ψ).drop p.nP).map (·.2.2) = []
          rw [List.drop_eq_nil_of_le (by rw [hCD.len ψ, hnF]; exact Nat.le_refl _)]
          rfl
        refine directUnitLawP (m := m₂) (T := p.cvT.name) (caps := ConLeche.directCaps p)
          ?_ hFD₂.read hFD₂.okTy ?_ ?_
        · intro ψ; rw [hleafT₂ ψ, hFs0 ψ]
        · intro ψ ρ; have := hpok ψ ρ; rwa [hFs0 ψ] at this
        · intro ψ; show p.nP = (pps ψ).length; rw [hFD.len ψ]

end ConLeche.SetP
