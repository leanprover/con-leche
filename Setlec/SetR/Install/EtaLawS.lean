import Setlec.SetR.Install.IndStagesS

/-!
# The eta law, from the checked `_model.eta` theorem (task #148, T5 c5)

`etaLawKeyS` is the [set] transpose of `eta_rule_fold`
(`Setlec/Model/EtaInstall.lean`): the checked `T._model.eta` theorem,
fired at a fitting parameter spine and a member of the family, yields
`EtaLawV` — every member of the interpreted structure is the
constructor's value applied to its projections' values.

It is `fireS` at `rP := caps.etaParams`, `cnF := 1`: the statement's
telescope is the model former's parameters followed by the major, and
its body is the pinned `Eq`-spine.  Two things differ from the iota
bottoms and are the whole content of finding 4's repair:

* the **left** side (`.bvar 0`, the major) inhabits the slot for free
  — `checkEtaThm` pins the major's binder domain to `T._model p⃗`,
  which is the slot, so `Sat` supplies it;
* the **right** side (the fabricated constructor application) is
  typed by **no** `--set-model` check — `checkEtaThm` is a pure `Bool`
  shape match with no side certification — and is recovered instead by
  `Eq`-slot rigidity (`EqLawV.dom`) against the statement's own
  truthfulness.  That is why `EqLawV` is stated at the two-fold
  application.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The eta-law key**: the checked `T._model.eta` theorem's kit, the
public/model valuation identifications, and the public type former's
renaming pin yield the stored family's fired `EtaLawV`. -/
def EtaLawKeyS (V : Type w) [SetTheory V] : Prop :=
  ∀ {envS : Env} (mS : EnvS V envS)
    {T ctor : Name} {cvT : ConstantVal} {caps : IndCaps}
    {lps : List Name} {nP nF : Nat}
    (_hlps : cvT.levelParams = lps)
    (_hnP : caps.etaParams = nP) (_hnF : caps.etaFields = nF)
    (_hctor : caps.etaCtor = ctor)
    -- the model artifacts (`checkEtaThm`'s lookups)
    {tcv : ConstantVal} {tval : Expr}
    (_hthmE : envS.find? ((T.str "_model").str "eta")
      = some (.thmInfo tcv tval))
    (_htlps : tcv.levelParams = lps)
    {cvmT : ConstantVal} {mvalT : Expr} {hmT : ReducibilityHint}
    (_hTmE : envS.find? (T.str "_model")
      = some (.defnInfo cvmT mvalT hmT))
    (_hTmlps : cvmT.levelParams = lps)
    {cvmC : ConstantVal} {mvalC : Expr} {hmC : ReducibilityHint}
    (_hCmE : envS.find? (ctor.str "_model")
      = some (.defnInfo cvmC mvalC hmC))
    (_hCmlps : cvmC.levelParams = lps)
    (_hprojE : ∀ j, j < nF → ∃ cvmj mvalj hmj,
      envS.find? (projModelName T j) = some (.defnInfo cvmj mvalj hmj) ∧
      cvmj.levelParams = lps)
    (_heqfE : envS.find? eqName = some eqA)
    -- the statement's shape pins (`checkEtaThm`'s matches)
    {sbinders tbindersM : List (Name × Expr × BinderMeta)}
    {sbody tbodyM tySlot : Expr} {ℓA : Level}
    (_hSstrip : tcv.type.stripPis (nP + 1) = some (sbinders, sbody))
    (_hTstrip : cvmT.type.stripPis nP = some (tbindersM, tbodyM))
    (_hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta), k < nP →
      sbinders[k]? = some b → tbindersM[k]? = some b' →
      b.2.1 = b'.2.1)
    (_hxdom : ∃ nx mx, sbinders[nP]? = some (nx,
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)), mx))
    (_hsbody : sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot, .bvar 0,
       Expr.mkAppN (.const (ctor.str "_model") (lps.map .param))
        (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
         (List.range nF).map fun j => Expr.mkAppN
           (.const (projModelName T j) (lps.map .param))
           (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
            [Expr.bvar 0]))])
    (_htySlot : tySlot = Expr.mkAppN (.const (T.str "_model")
        (lps.map .param))
      ((List.range nP).map fun k => Expr.bvar (nP - k)))
    -- the public/model valuation identifications (install-supplied)
    (_hvT : ∀ ψ : Name → Nat, mS.cval T ψ = mS.cval (T.str "_model") ψ)
    (_hvC : ∀ ψ : Name → Nat,
      mS.cval ctor ψ = mS.cval (ctor.str "_model") ψ)
    (_hvP : ∀ j, j < nF → ∀ ψ : Name → Nat,
      mS.cval (projFnName T j) ψ = mS.cval (projModelName T j) ψ)
    -- the public type former's type is the model's, renamed
    {fb : Name → Name} (_hroB : RenameOkT mS.cval envS fb)
    (_hrenT : RenEqT fb cvT.type cvmT.type),
    EtaLawV V envS mS.cval T cvT caps

set_option maxHeartbeats 12800000 in
theorem etaLawKeyS : EtaLawKeyS V := by
  intro envS mS T ctor cvT caps lps nP nF hlps hnP hnF hctor tcv tval
    hthmE htlps cvmT mvalT hmT hTmE hTmlps cvmC mvalC hmC hCmE hCmlps
    hprojE heqfE sbinders tbindersM
    sbody tbodyM tySlot ℓA hSstrip hTstrip hsdoms hxdom hsbody htySlot
    hvT hvC hvP fb hroB hrenT
  subst hlps
  intro φ' us ρ xs TV rest B hlenX hTVden hfitT hB
  rw [hnP] at hlenX
  rw [hnF, hctor]
  have hcl' := mS.cval_closed
  have hvp : ValParams envS mS.cval := mS.val_params
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : Name → Nat,
      ψ' = Level.substFn φ' cvT.levelParams us := ⟨_, rfl⟩
  rw [← hψ'] at hB ⊢
  have henv := mS.toHyp ψ'
  rw [hψ'] at henv
  rw [← hψ'] at henv
  -- ===== the statement's front doors =====
  obtain ⟨Tst, hTstden, hTstFacts⟩ :=
    mS.mem_type (.thmInfo tcv tval) (find?_mem hthmE) ψ'
  have hTst0 : denote mS.cval envS ψ' 0 tcv.type = some Tst := hTstden
  obtain ⟨Γs, Rbody, htowerS, hΓslen, hRbodyDen, hdomsS⟩ :=
    stripPis_denoteTele (nP + 1) hSstrip hTst0
  -- ===== the model former's tower =====
  have hTV0 : denote mS.cval envS ψ' 0 cvmT.type = some TV := by
    have h := hTVden
    unfold denoteClosed at h
    rw [denote_instLevels hvp] at h
    rw [← hψ'] at h
    rw [RenEqT.denote (cval := mS.cval) (env := envS) (φ := ψ')
      hroB hrenT 0]
    exact h
  obtain ⟨Γm, Rm, htowerM, hΓmlen, hRmDen, hdomsM⟩ :=
    stripPis_denoteTele nP hTstrip hTV0
  -- the two contexts agree on the parameters
  have hΓsdrop : Γs.drop 1 = Γm := by
    refine towerCtxEq (cval := mS.cval) (env := envS) (ψ := ψ')
      (rbinders := sbinders.take nP) (cbinders := tbindersM)
      (by rw [List.length_take, Expr.stripPis_length _ hSstrip]; omega)
      (Expr.stripPis_length _ hTstrip)
      (by rw [List.length_drop, hΓslen]; omega) hΓmlen ?_ hdomsM ?_
    · intro i0 b hb
      have hi0 : i0 < nP := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        rw [List.length_take, Expr.stripPis_length _ hSstrip] at this
        omega
      rw [List.getElem?_take_of_lt hi0] at hb
      have h := hdomsS i0 b hb
      rw [h]
      congr 1
      rw [List.getD, List.getD, List.getElem?_drop,
        show 1 + (nP - 1 - i0) = nP + 1 - 1 - i0 from by omega]
    · intro i0 b b' hi0 hb hb'
      rw [List.getElem?_take_of_lt hi0] at hb
      exact hsdoms i0 b b' hi0 hb hb'
  -- ===== the fired spine =====
  have hzslen : (xs ++ [B]).length = nP + 1 := by
    rw [List.length_append, hlenX, List.length_cons, List.length_nil]
  have hzsPre : ∀ n, n < nP →
      (xs ++ [B]).getD n default = xs.getD n default := by
    intro n hn
    rw [List.getD, List.getD, List.getElem?_append_left (by omega)]
  have hzsTake : ∀ n, n ≤ nP → (xs ++ [B]).take n = xs.take n := by
    intro n hn
    rw [List.take_append_of_le_length (by omega)]
  have hzsLast : (xs ++ [B]).getD nP default = B := by
    rw [List.getD, List.getElem?_append_right (by omega), hlenX,
      Nat.sub_self]
    rfl
  -- the major's context entry is the slot's value
  obtain ⟨nx, mx, hxb⟩ := hxdom
  have hfamOpen : Expr.instSeq (openFvars 0 nP) (nP - 1)
      (Expr.mkAppN (.const (T.str "_model") (cvT.levelParams.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)))
      = Expr.mkAppN (.const (T.str "_model")
          (cvT.levelParams.map .param)) (openFvars 0 nP) := by
    rw [Expr.instSeq_mkAppN, List.map_map]
    congr 1
    · exact Expr.instSeq_eq_self _ _ rfl
    · refine List.ext_getElem (by simp) ?_
      intro q h1 h2
      have hq : q < nP := by simpa using h1
      rw [List.getElem_map, List.getElem_range]
      have hhit := Expr.instSeq_bvar (openFvars 0 nP) (nP - 1)
        (nP - 1 - q) (openFvars_bounded 0 nP) (by omega)
        (by rw [openFvars_length]; omega)
      rw [show nP - 1 - (nP - 1 - q) = q from by omega,
        List.getElem?_eq_getElem h2] at hhit
      exact (Option.some.inj hhit).symm
  have hslotDen : denote mS.cval envS ψ' (0 + nP)
      (Expr.instSeq (openFvars 0 nP) (nP - 1)
        (Expr.mkAppN (.const (T.str "_model")
          (cvT.levelParams.map .param))
          ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))))
      = some (Γs.getD (nP + 1 - 1 - nP) default) :=
    hdomsS nP _ hxb
  -- ===== the memberships of the fired spine =====
  have hchainM := teleFitV_to_chain nP htowerM hlenX hfitT
  have hallK : ∀ m, m < nP + 1 →
      interp V ρ ((xs ++ [B]).getD m default)
        ∈ˢ interp V (chainE V ρ ((xs ++ [B]).take m))
          (Γs.getD (nP + 1 - 1 - m) default) := by
    intro m hm
    rcases Nat.lt_or_ge m nP with hmn | hmn
    · rw [hzsPre m hmn, hzsTake m (by omega),
        show nP + 1 - 1 - m = 1 + (nP - 1 - m) from by omega,
        show Γs.getD (1 + (nP - 1 - m)) default
            = (Γs.drop 1).getD (nP - 1 - m) default from by
          rw [List.getD, List.getD, List.getElem?_drop],
        hΓsdrop]
      exact hchainM m hmn
    · rw [show m = nP from by omega]
      rw [hzsLast, hzsTake nP (Nat.le_refl _),
        List.take_of_length_le (by rw [hlenX]; omega)]
      -- the slot's value, computed
      rw [Nat.zero_add, hfamOpen] at hslotDen
      obtain ⟨vh, vargs, hvh, hsp, hdec⟩ := denote_mkAppN_inv
        (by rw [← hfamOpen] at hslotDen ⊢; exact hslotDen)
      have hvh' : vh = mS.cval (T.str "_model") ψ' := by
        rw [denote_const, hTmE] at hvh
        dsimp only at hvh
        have hTmlps' : (ConstantInfo.defnInfo cvmT mvalT
            hmT).toConstantVal.levelParams = cvT.levelParams := hTmlps
        rw [if_pos (by rw [hTmlps', List.length_map]), hTmlps',
          show Level.substFn ψ' cvT.levelParams
              (cvT.levelParams.map .param) = ψ' from
            funext fun _ => Level.substFn_map_param] at hvh
        exact (Option.some.inj hvh).symm
      have hvargs : vargs = (List.range nP).map
          (fun q => VExpr.bvar (nP - 1 - q)) := by
        have hlenv : vargs.length = nP := by
          rw [hsp.length, openFvars_length]
        refine List.ext_getElem (by simp [hlenv]) ?_
        intro q h1 h2
        have hq : q < nP := by rw [hlenv] at h1; exact h1
        obtain ⟨v, hv, hdv⟩ := denoteSpine_getElem?' hsp q _
          (openFvars_getElem? (d := 0) hq)
        rw [denote_fvar] at hdv
        obtain rfl : v = VExpr.bvar (nP - 1 - (0 + q)) :=
          (Option.some.inj hdv).symm
        rw [List.getElem_map, List.getElem_range]
        have := List.getElem?_eq_getElem h1
        rw [hv] at this
        rw [← Option.some.inj this,
          show nP - 1 - (0 + q) = nP - 1 - q from by omega]
      rw [show Γs.getD (nP + 1 - 1 - nP) default
          = VExpr.mkAppN vh vargs from hdec, hvh', hvargs,
        interp_mkAppN_map]
      have hmapEq : ((List.range nP).map
          (fun q => VExpr.bvar (nP - 1 - q))).map
            (interp V (chainE V ρ xs))
          = xs.map (interp V ρ) := by
        refine List.ext_getElem (by simp [hlenX]) ?_
        intro q h1 h2
        have hq : q < nP := by simpa using h1
        rw [List.getElem_map, List.getElem_map, List.getElem_range,
          interp_bvar, chainE_lt (by rw [hlenX]; omega), hlenX,
          show nP - 1 - (nP - 1 - q) = q from by omega]
        rw [List.getD]
        have h3 := List.getElem?_eq_getElem (show q < xs.length from by omega)
        rw [h3, List.getElem_map]
        rfl
      rw [hmapEq,
        interp_closed V (hcl' (T.str "_model") ψ') (chainE V ρ xs) ρ]
      have hBmem := hB
      rw [interp_mkAppN_map, hvT] at hBmem
      exact hBmem
  have hsat : Sat V Γs (chainE V ρ (xs ++ [B])) :=
    sat_of_tower htowerS hzslen hallK
  have hfitS : TeleFitV V ρ Tst (xs ++ [B])
      (VExpr.instSeq (xs ++ [B]) (nP + 1 - 1) Rbody) :=
    teleFitV_of_tower (nP + 1) htowerS hzslen hallK
  -- ===== the opened body is the pinned `Eq` spine =====
  rw [hsbody, Expr.instSeq_mkAppN] at hRbodyDen
  rw [Nat.zero_add] at hRbodyDen
  have hconstFix : Expr.instSeq (openFvars 0 (nP + 1)) (nP + 1 - 1)
      (Expr.const eqName [ℓA]) = Expr.const eqName [ℓA] :=
    Expr.instSeq_eq_self _ _ rfl
  rw [hconstFix] at hRbodyDen
  simp only [List.map_cons, List.map_nil] at hRbodyDen
  -- ===== the opened body's three components, denoted =====
  have hbvarOpen : ∀ j, j ≤ nP →
      Expr.instSeq (openFvars 0 (nP + 1)) (nP + 1 - 1) (Expr.bvar j)
        = Expr.fvar (nP - j) Name.anonymous (.sort .zero) := by
    intro j hj
    have hhit := Expr.instSeq_bvar (openFvars 0 (nP + 1)) (nP + 1 - 1) j
      (openFvars_bounded 0 (nP + 1)) (by omega)
      (by rw [openFvars_length]; omega)
    rw [openFvars_getElem? (d := 0) (k := nP + 1)
      (i := nP + 1 - 1 - j) (by omega),
      show (0 : Nat) + (nP + 1 - 1 - j) = nP - j from by omega] at hhit
    exact (Option.some.inj hhit).symm
  have hbvarDen : ∀ j, j ≤ nP →
      denote mS.cval envS ψ' (nP + 1)
        (Expr.instSeq (openFvars 0 (nP + 1)) (nP + 1 - 1) (Expr.bvar j))
        = some (VExpr.bvar j) := by
    intro j hj
    rw [hbvarOpen j hj, denote_fvar,
      show nP + 1 - 1 - (nP - j) = j from by omega]
  have hconstDen : ∀ (c : Name) (ci : ConstantInfo) (d : Nat),
      envS.find? c = some ci →
      ci.toConstantVal.levelParams = cvT.levelParams →
      denote mS.cval envS ψ' d
          (Expr.const c (cvT.levelParams.map .param))
        = some (mS.cval c ψ') := by
    intro c ci d hf hlp
    rw [denote_const, hf]
    dsimp only
    rw [if_pos (by rw [hlp, List.length_map]), hlp,
      show Level.substFn ψ' cvT.levelParams
          (cvT.levelParams.map .param) = ψ' from
        funext fun _ => Level.substFn_map_param]
  have hconstFix2 : ∀ (c : Name) (lvls : List Level),
      Expr.instSeq (openFvars 0 (nP + 1)) (nP + 1 - 1)
        (Expr.const c lvls) = Expr.const c lvls :=
    fun _ _ => Expr.instSeq_eq_self _ _ rfl
  -- the parameter spine, opened and denoted
  have hpspine : ∀ (d : Nat), DenoteSpine mS.cval envS ψ' (nP + 1)
      (((List.range nP).map fun k => Expr.bvar (nP - k)).map
        (Expr.instSeq (openFvars 0 (nP + 1)) (nP + 1 - 1)))
      ((List.range nP).map fun k => VExpr.bvar (nP - k)) := by
    intro _
    rw [List.map_map]
    exact DenoteSpine.map (fun k hk =>
      hbvarDen (nP - k) (by omega))
  -- the fabricated side, denoted
  have hprojDen : ∀ j, j < nF →
      denote mS.cval envS ψ' (nP + 1)
        (Expr.instSeq (openFvars 0 (nP + 1)) (nP + 1 - 1)
          (Expr.mkAppN (.const (projModelName T j)
            (cvT.levelParams.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
              [Expr.bvar 0])))
        = some (VExpr.mkAppN (mS.cval (projModelName T j) ψ')
            (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++
              [VExpr.bvar 0])) := by
    intro j hj
    obtain ⟨cvmj, mvalj, hmj, hjE, hjlps⟩ := hprojE j hj
    rw [Expr.instSeq_mkAppN, hconstFix2, List.map_append]
    refine denote_mkAppN (DenoteSpine.append (hpspine 0) ?_)
      (hconstDen _ _ _ hjE hjlps)
    exact DenoteSpine.cons (hbvarDen 0 (by omega)) DenoteSpine.nil
  have hfabDen : denote mS.cval envS ψ' (nP + 1)
      (Expr.instSeq (openFvars 0 (nP + 1)) (nP + 1 - 1)
        (Expr.mkAppN (.const (ctor.str "_model")
          (cvT.levelParams.map .param))
          (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
           (List.range nF).map fun j => Expr.mkAppN
             (.const (projModelName T j) (cvT.levelParams.map .param))
             (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
              [Expr.bvar 0]))))
      = some (VExpr.mkAppN (mS.cval (ctor.str "_model") ψ')
          (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++
           (List.range nF).map fun j =>
             VExpr.mkAppN (mS.cval (projModelName T j) ψ')
               (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++
                [VExpr.bvar 0]))) := by
    rw [Expr.instSeq_mkAppN, hconstFix2, List.map_append]
    refine denote_mkAppN (DenoteSpine.append (hpspine 0) ?_)
      (hconstDen _ _ _ hCmE hCmlps)
    rw [List.map_map]
    exact DenoteSpine.map (fun j hj => hprojDen j (List.mem_range.mp hj))
  -- the slot, denoted
  have hslotD : denote mS.cval envS ψ' (nP + 1)
      (Expr.instSeq (openFvars 0 (nP + 1)) (nP + 1 - 1) tySlot)
      = some (VExpr.mkAppN (mS.cval (T.str "_model") ψ')
          ((List.range nP).map fun k => VExpr.bvar (nP - k))) := by
    rw [htySlot, Expr.instSeq_mkAppN, hconstFix2]
    exact denote_mkAppN (hpspine 0) (hconstDen _ _ _ hTmE hTmlps)
  -- ===== the chain reads the spine =====
  have hchainBvar : ∀ j, j ≤ nP →
      interp V (chainE V ρ (xs ++ [B])) (VExpr.bvar j)
        = interp V ρ ((xs ++ [B]).getD (nP - j) default) := by
    intro j hj
    rw [interp_bvar, chainE_lt (by rw [hzslen]; omega), hzslen,
      show nP + 1 - 1 - j = nP - j from by omega]
  have hchainPar : ((List.range nP).map fun k => VExpr.bvar (nP - k)).map
      (interp V (chainE V ρ (xs ++ [B]))) = xs.map (interp V ρ) := by
    refine List.ext_getElem (by simp [hlenX]) ?_
    intro q h1 h2
    have hq : q < nP := by simpa using h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range,
      hchainBvar (nP - q) (by omega),
      show nP - (nP - q) = q from by omega, hzsPre q hq, List.getD]
    have h3 := List.getElem?_eq_getElem (show q < xs.length from by omega)
    rw [h3]
    simp
  have hchainMajor : interp V (chainE V ρ (xs ++ [B])) (VExpr.bvar 0)
      = interp V ρ B := by
    rw [hchainBvar 0 (by omega), Nat.sub_zero, hzsLast]
  -- the slot's interpretation is the family at the parameters
  have hslotVal : interp V (chainE V ρ (xs ++ [B]))
      (VExpr.mkAppN (mS.cval (T.str "_model") ψ')
        ((List.range nP).map fun k => VExpr.bvar (nP - k)))
      = interp V ρ (VExpr.mkAppN (mS.cval T ψ') xs) := by
    rw [interp_mkAppN_map, interp_mkAppN_map, hchainPar, hvT,
      interp_closed V (hcl' (T.str "_model") ψ')
        (chainE V ρ (xs ++ [B])) ρ]
  -- the equation head, denoted
  have heqDen : denote mS.cval envS ψ' (nP + 1) (Expr.const eqName [ℓA])
      = some (mS.cval eqName
          (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA])) := by
    rw [denote_const, heqfE]
    dsimp only
    rw [if_pos (show ([ℓA] : List Level).length
      = eqA.toConstantVal.levelParams.length from rfl)]
  -- the opened body's value
  have hRbodyEq : Rbody = VExpr.mkAppN (mS.cval eqName
      (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA]))
      [VExpr.mkAppN (mS.cval (T.str "_model") ψ')
      ((List.range nP).map fun k => VExpr.bvar (nP - k)), VExpr.bvar 0,
       VExpr.mkAppN (mS.cval (ctor.str "_model") ψ')
      (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++
       (List.range nF).map fun j =>
         VExpr.mkAppN (mS.cval (projModelName T j) ψ')
           (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++ [VExpr.bvar 0]))] := by
    have hd := denote_mkAppN (DenoteSpine.cons hslotD
      (DenoteSpine.cons (hbvarDen 0 (by omega))
        (DenoteSpine.cons hfabDen DenoteSpine.nil))) heqDen
    rw [hd] at hRbodyDen
    exact (Option.some.inj hRbodyDen).symm
  -- ===== the sides' memberships =====
  have hsides : ∀ vα vL vR,
      denote mS.cval envS ψ' (nP + 1)
        (Expr.instSeq (openFvars 0 (nP + 1)) (nP + 1 - 1) tySlot)
        = some vα →
      denote mS.cval envS ψ' (nP + 1)
        (Expr.instSeq (openFvars 0 (nP + 1)) (nP + 1 - 1) (.bvar 0))
        = some vL →
      denote mS.cval envS ψ' (nP + 1)
        (Expr.instSeq (openFvars 0 (nP + 1)) (nP + 1 - 1)
          (Expr.mkAppN (.const (ctor.str "_model")
            (cvT.levelParams.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
             (List.range nF).map fun j => Expr.mkAppN
               (.const (projModelName T j) (cvT.levelParams.map .param))
               (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
                [Expr.bvar 0])))) = some vR →
      interp V (chainE V ρ (xs ++ [B])) vα ∈ˢ univ (ℓA.eval ψ') →
      interp V (chainE V ρ (xs ++ [B])) vL
          ∈ˢ interp V (chainE V ρ (xs ++ [B])) vα ∧
      interp V (chainE V ρ (xs ++ [B])) vR
          ∈ˢ interp V (chainE V ρ (xs ++ [B])) vα := by
    intro vα vL vR hvα hvL hvR hαuniv
    obtain rfl : vα = VExpr.mkAppN (mS.cval (T.str "_model") ψ')
      ((List.range nP).map fun k => VExpr.bvar (nP - k)) := by
      rw [hslotD] at hvα
      exact (Option.some.inj hvα).symm
    obtain rfl : vL = VExpr.bvar 0 := by
      rw [hbvarDen 0 (by omega)] at hvL
      exact (Option.some.inj hvL).symm
    obtain rfl : vR = VExpr.mkAppN (mS.cval (ctor.str "_model") ψ')
      (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++
       (List.range nF).map fun j =>
         VExpr.mkAppN (mS.cval (projModelName T j) ψ')
           (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++ [VExpr.bvar 0])) := by
      rw [hfabDen] at hvR
      exact (Option.some.inj hvR).symm
    have hLmem : interp V (chainE V ρ (xs ++ [B])) (VExpr.bvar 0)
        ∈ˢ interp V (chainE V ρ (xs ++ [B])) (VExpr.mkAppN (mS.cval (T.str "_model") ψ')
      ((List.range nP).map fun k => VExpr.bvar (nP - k))) := by
      rw [hchainMajor, hslotVal]
      exact hB
    refine ⟨hLmem, ?_⟩
    -- the fabricated side, by `Eq`-slot rigidity against the
    -- statement's own truthfulness (finding 4's repair)
    have hdescend := annotOkV_descend (nP + 1) htowerS ρ
      ((xs ++ [B]).map (interp V ρ))
      (by rw [List.length_map, hzslen]) (hTstFacts ρ).2
      (sat_chain_mems htowerS hzslen hsat)
    rw [consChain_map_interp, hRbodyEq,
      show VExpr.mkAppN (mS.cval eqName
          (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA]))
          [VExpr.mkAppN (mS.cval (T.str "_model") ψ')
      ((List.range nP).map fun k => VExpr.bvar (nP - k)), VExpr.bvar 0, VExpr.mkAppN (mS.cval (ctor.str "_model") ψ')
      (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++
       (List.range nF).map fun j =>
         VExpr.mkAppN (mS.cval (projModelName T j) ψ')
           (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++ [VExpr.bvar 0]))]
        = .app (.app (.app (mS.cval eqName
            (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA]))
          (VExpr.mkAppN (mS.cval (T.str "_model") ψ')
      ((List.range nP).map fun k => VExpr.bvar (nP - k)))) (VExpr.bvar 0)) (VExpr.mkAppN (mS.cval (ctor.str "_model") ψ')
      (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++
       (List.range nF).map fun j =>
         VExpr.mkAppN (mS.cval (projModelName T j) ψ')
           (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++ [VExpr.bvar 0]))) from rfl,
      AnnotOkV_app] at hdescend
    obtain ⟨-, -, A₃, B₃, hpi₃, hmem₃⟩ := hdescend
    rw [interp_app, interp_app] at hpi₃
    exact EqLawV.dom (V := V) mS.eq_lawV heqfE _ _ _ _
      (by
        rw [show (Level.substFn ψ' eqA.toConstantVal.levelParams
            [ℓA]) uN = ℓA.eval ψ' from rfl]
        exact hαuniv)
      hLmem hpi₃ _ hmem₃
  -- ===== fire the checked equation =====
  obtain ⟨vα, vL, vR, hvα, hvL, hvR, heqLR⟩ :=
    fireS henv mS.eq_lawV heqfE htowerS
      (fun ρ0 => (hTstFacts ρ0).2) (fun ρ0 => ⟨_, (hTstFacts ρ0).1⟩)
      hRbodyDen rfl hsides hzslen hsat hfitS
  obtain rfl : vL = VExpr.bvar 0 := by
    rw [hbvarDen 0 (by omega)] at hvL
    exact (Option.some.inj hvL).symm
  obtain rfl : vR = VExpr.mkAppN (mS.cval (ctor.str "_model") ψ')
      (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++
       (List.range nF).map fun j =>
         VExpr.mkAppN (mS.cval (projModelName T j) ψ')
           (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++ [VExpr.bvar 0])) := by
    rw [hfabDen] at hvR
    exact (Option.some.inj hvR).symm
  -- ===== the two sides, read at the fired spine =====
  rw [← hchainMajor, heqLR, interp_mkAppN_map, interp_mkAppN_map,
    interp_closed V (hcl' (ctor.str "_model") ψ')
      (chainE V ρ (xs ++ [B])) ρ,
    ← hvC, List.map_append, etaFabArgsV, List.map_append, hchainPar,
    projSpinesV, List.map_map, List.map_map]
  refine congrArg (fun l => List.foldl SetTheory.app
    (interp V ρ (mS.cval ctor ψ'))
    (List.map (interp V ρ) xs ++ l))
    (List.map_congr_left fun j hj => ?_)
  have hjlt : j < nF := List.mem_range.mp hj
  show interp V (chainE V ρ (xs ++ [B]))
      (VExpr.mkAppN (mS.cval (projModelName T j) ψ')
        (((List.range nP).map fun k => VExpr.bvar (nP - k)) ++
          [VExpr.bvar 0]))
    = interp V ρ
      (VExpr.mkAppN (mS.cval (projFnName T j) ψ') (xs ++ [B]))
  rw [interp_mkAppN_map, interp_mkAppN_map,
    interp_closed V (hcl' (projModelName T j) ψ')
      (chainE V ρ (xs ++ [B])) ρ,
    ← hvP j hjlt, List.map_append, List.map_append, hchainPar]
  refine congrArg (fun l => List.foldl SetTheory.app
    (interp V ρ (mS.cval (projFnName T j) ψ'))
    (List.map (interp V ρ) xs ++ l)) ?_
  show [interp V (chainE V ρ (xs ++ [B])) (VExpr.bvar 0)]
    = [interp V ρ B]
  rw [hchainMajor]

end Setlec.SetR
