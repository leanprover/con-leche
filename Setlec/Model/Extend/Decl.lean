import Setlec.Verify.Extend.Decl
import Setlec.Model.Extend.Ind
import Setlec.Model.Extend.Recs
import Setlec.Model.Extend.Proj
import Setlec.Model.DirectDecl

/-!
# Decl — split out of `Setlec.Model.Extend`

`checkIndDecl_sound`: checking a modeled inductive block preserves
having a model and keeps the stored eta families closed
(`EtaFamiliesClosed`, the side invariant the consistency fold threads
next to the model).  The single-constructor arm is assembled member by
member — the block's non-recursor part is exactly its former and its
constructor (`two_elem_split`) — so the family-completing member's
step can discharge the public eta law through `blockMember_headEta`
with the group-local identification in scope.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}

variable {V : Type u} [SetTheory V]

open SetTheory Expr

set_option maxHeartbeats 6400000 in
/-- Checking a modeled inductive block preserves having a model and
keeps the stored eta families closed. -/
theorem checkIndDecl_sound {env env₂ : Env} {block : List ConstantInfo}
    (h : checkIndDecl mode (fueledOps mode F) env block = .ok env₂)
    (m : EnvModel V env) (hE1 : EtaFamiliesClosed env) :
    Nonempty (EnvModel V env₂) ∧ EtaFamiliesClosed env₂ := by
  rw [checkIndDecl] at h
  simp only [Bind.bind, Except.bind] at h
  have hbn : ∀ ci ∈ block, (block.map (·.name)).contains ci.name = true :=
    fun ci hci => by
      have : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
      simpa using this
  -- the recursor-suffix split
  split at h
  case isFalse => exact nomatch h
  rename_i hsplit
  simp only [pure, Except.pure, Except.bind] at h
  try dsimp only at h
  split at h
  · -- the single-constructor arm
    rename_i cvT capsT cvC nP nF heqI heqC
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨env₁, hfold, h⟩ := Except.bind_ok h
    obtain ⟨env₃, hrecs, h⟩ := Except.bind_ok h
    have hbnrec : ∀ ci ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => true | _ => false),
        (block.map (·.name)).contains ci.name = true :=
      fun ci hci => hbn ci (List.mem_filter.mp hci).1
    have hbnnon : ∀ ci ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => false | _ => true),
        (block.map (·.name)).contains ci.name = true :=
      fun ci hci => hbn ci (List.mem_filter.mp hci).1
    -- block names are fresh at the base
    have hbfresh : ∀ n, (block.map (·.name)).contains n = true →
        env.find? n = none := by
      intro n hn
      have hmem : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with hci₀ | hci₀
      · exact checkIndMember_fold_names _ env env₁ hfold ci₀ hci₀
      · have h1 := checkIndRecs_names hrecs ci₀ hci₀
        cases hf₀ : env.find? ci₀.name with
        | none => rfl
        | some ci₂ =>
          exfalso
          have h2 : (env₁.find? ci₀.name).isSome = true :=
            checkIndFold_mono _ env env₁ hfold ci₀.name
              (by rw [hf₀]; rfl)
          rw [h1] at h2
          exact nomatch h2
    -- the non-recursor part is exactly the former and the constructor
    have hIfilt : (block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => false | _ => true)).filter
        (fun ci => match ci with
        | .indInfo _ _ => true | _ => false) =
        [ConstantInfo.indInfo cvT capsT] := by
      rw [List.filter_filter_of_imp (fun a ha => by
        cases a <;> first | rfl | exact nomatch ha)]
      exact heqI
    have hCfilt : (block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => false | _ => true)).filter
        (fun ci => match ci with
        | .ctorInfo _ _ _ => true | _ => false) =
        [ConstantInfo.ctorInfo cvC nP nF] := by
      rw [List.filter_filter_of_imp (fun a ha => by
        cases a <;> first | rfl | exact nomatch ha)]
      exact heqC
    have hkindsB : ∀ ci ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => false | _ => true),
        (fun ci => match ci with
          | ConstantInfo.indInfo _ _ => true | _ => false) ci = true ∨
        (fun ci => match ci with
          | ConstantInfo.ctorInfo _ _ _ => true | _ => false) ci
          = true := by
      intro ci hci
      rcases checkIndFold_kinds _ env env₁ hfold ci hci with
        ⟨cv, caps', rfl⟩ | ⟨cv, nP', nF', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    have horder := two_elem_split
      (fun x hx => by
        obtain ⟨h1, h2⟩ := hx
        cases x <;> simp at h1 h2)
      _ hkindsB hIfilt hCfilt
    have hfold' : (block.filter (fun ci => match ci with
        | ConstantInfo.recInfo _ _ _ _ => false
        | _ => true)).foldlM (checkIndMember (fueledOps mode F)
          (block.map (·.name)) (indBlockCaps mode env cvT cvC nP nF)) env
        = .ok env₁ := hfold
    -- the eta constructor's residual (task #136): a syntactic guard on
    -- the *stored* constructor, refuted exactly like the freshness one
    by_cases hctorRes : ctorResidualOk mode env₃ cvT.name cvC.name
        cvT.levelParams nP nF (indBlockCaps mode env cvT cvC nP nF).eta = true
    case neg => rw [if_neg hctorRes] at h; exact nomatch h
    rw [if_pos hctorRes] at h
    try simp only [pure, Except.pure] at h
    try dsimp only at h
    try simp only [Bind.bind, Except.bind] at h
    -- the projection-family freshness check (extracted early: the
    -- member steps' refutations read it back through the monotone
    -- phases)
    by_cases hfreshP : ((List.range nF).all
        (fun j => (env₃.find? (projFnName cvT.name j)).isNone)) = true
    case neg => rw [if_neg hfreshP] at h; exact nomatch h
    rw [if_pos hfreshP] at h
    try simp only [pure, Except.pure] at h
    try dsimp only at h
    try simp only [Bind.bind, Except.bind] at h
    obtain ⟨env₄, hart, htpl⟩ := Except.bind_ok h
    have hmono₁₃ : ∀ n, (env₁.find? n).isSome = true →
        (env₃.find? n).isSome = true :=
      fun n hn => checkIndRecs_mono hrecs hbnrec n hn
    have hPfree₃ : ∀ j, j < nF →
        env₃.find? (projFnName cvT.name j) = none := by
      intro j hj
      have h1 := List.all_eq_true.mp hfreshP j (List.mem_range.mpr hj)
      exact Option.isNone_iff_eq_none.mp (by simpa using h1)
    have hPfree₁ : ∀ j, j < nF →
        env₁.find? (projFnName cvT.name j) = none := by
      intro j hj
      cases hf₀ : env₁.find? (projFnName cvT.name j) with
      | none => rfl
      | some ci₂ =>
        exfalso
        have h2 := hmono₁₃ _ (by rw [hf₀]; rfl)
        rw [hPfree₃ j hj] at h2
        exact nomatch h2
    -- pins for the former at the base, and the two members' block
    -- membership
    have hpinsT0 : EtaPins mode env cvT.name cvT.levelParams
        (indBlockCaps mode env cvT cvC nP nF) := by
      refine ⟨?_, ?_⟩
      · intro hcape
        simp only [indBlockCaps, Bool.and_eq_true] at hcape
        exact checkEtaThm_inv hcape.2
      · intro hcapu
        simp only [indBlockCaps] at hcapu
        exact checkUnitThm_inv hcapu
    have hTin : (ConstantInfo.indInfo cvT capsT) ∈ block := by
      have h1 : ConstantInfo.indInfo cvT capsT ∈
          [ConstantInfo.indInfo cvT capsT] := List.mem_singleton.mpr rfl
      rw [← heqI] at h1
      exact (List.mem_filter.mp h1).1
    have hCin : (ConstantInfo.ctorInfo cvC nP nF) ∈ block := by
      have h1 : ConstantInfo.ctorInfo cvC nP nF ∈
          [ConstantInfo.ctorInfo cvC nP nF] := List.mem_singleton.mpr rfl
      rw [← heqC] at h1
      exact (List.mem_filter.mp h1).1
    have hbnT : (block.map (·.name)).contains cvT.name = true := by
      have hmm : cvT.name ∈ block.map (fun x => x.name) :=
        List.mem_map_of_mem (f := fun x => x.name) hTin
      simpa using hmm
    have hbnC : (block.map (·.name)).contains cvC.name = true := by
      have hmm : cvC.name ∈ block.map (fun x => x.name) :=
        List.mem_map_of_mem (f := fun x => x.name) hCin
      simpa using hmm
    have hI₀ : BlockInstalled (block.map (·.name)) env m.val := by
      intro n hn ci₂ hf₂
      rw [hbfresh n hn] at hf₂
      exact nomatch hf₂
    have hnonmem : ∀ ci₀, ci₀ ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => false | _ => true) →
        ci₀ = ConstantInfo.indInfo cvT capsT ∨
        ci₀ = ConstantInfo.ctorInfo cvC nP nF := by
      intro ci₀ hci₀
      rcases horder with hord | hord <;> rw [hord] at hci₀ <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hci₀
      · exact hci₀
      · exact hci₀.symm
    have hbshape : ∀ n, (block.map (·.name)).contains n = true →
        n.isProjFnShape = false := by
      intro n hn
      have hmem : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with hci₀ | hci₀
      · exact checkIndFold_projshape _ env env₁ hfold ci₀ hci₀
      · exact checkIndRecs_projshape hrecs ci₀ hci₀
    -- the shared tail: recursors, projection family, template phase,
    -- and the closedness of the stored eta families
    have hrest : ∀ (m₂' : EnvModel V env₁),
        BlockInstalled (block.map (·.name)) env₁ m₂'.val →
        (∃ cvTA, env₁.find? cvT.name =
          some (.indInfo cvTA (indBlockCaps mode env cvT cvC nP nF)) ∧
          EtaPins mode env₁ cvT.name cvTA.levelParams
            (indBlockCaps mode env cvT cvC nP nF)) →
        (∃ cvCA, env₁.find? cvC.name = some (.ctorInfo cvCA nP nF)) →
        (∀ (n : Name) (cv2 : ConstantVal) (caps2 : IndCaps),
          env₁.find? n = some (.indInfo cv2 caps2) →
          env.find? n = some (.indInfo cv2 caps2) ∨ n = cvT.name) →
        Nonempty (EnvModel V env₂) ∧ EtaFamiliesClosed env₂ := by
      rintro m₂' hI₂ ⟨cvTA, hTst, hpins₁⟩ ⟨cvCA, hCst⟩ hindAt₁
      obtain ⟨m₃, hI₃⟩ := checkIndRecs_sound hrecs hbnrec
        (fun n hn => by
          have hmem : n ∈ block.map (·.name) := by simpa using hn
          obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
          rw [hsplit] at hci₀
          rcases List.mem_append.mp hci₀ with hci₀ | hci₀
          · rcases hnonmem ci₀ hci₀ with rfl | rfl
            · exact Or.inl (by
                rw [show (ConstantInfo.indInfo cvT capsT).name = cvT.name
                  from rfl, hTst]
                rfl)
            · exact Or.inl (by
                rw [show (ConstantInfo.ctorInfo cvC nP nF).name = cvC.name
                  from rfl, hCst]
                rfl)
          · exact Or.inr ⟨ci₀, hci₀, rfl⟩)
        (fun n hn => by
          have hmem : n ∈ block.map (·.name) := by simpa using hn
          obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
          rw [hsplit] at hci₀
          rcases List.mem_append.mp hci₀ with hci₀ | hci₀
          · exact checkIndFold_modelfree _ env env₁ hfold ci₀ hci₀
          · exact checkIndRecs_modelfree hrecs ci₀ hci₀)
        m₂' hI₂
      have hTst₃ : env₃.find? cvT.name =
          some (.indInfo cvTA (indBlockCaps mode env cvT cvC nP nF)) :=
        checkIndRecs_find_preserved hrecs hbnrec _ _ hTst
          (fun _ _ _ _ hcon => nomatch hcon)
      have hCst₃ : env₃.find? cvC.name = some (.ctorInfo cvCA nP nF) :=
        checkIndRecs_find_preserved hrecs hbnrec _ _ hCst
          (fun _ _ _ _ hcon => nomatch hcon)
      have hinv₀ : ProjPhaseInv cvT.name cvC.name nF env₃ m₃.val := by
        refine ⟨?_, ?_, ?_⟩
        · intro ci hf
          obtain ⟨cvm, mval, hm, hfm, hlps, -, hv⟩ :=
            hI₃ cvT.name hbnT ci hf
          exact ⟨cvm, mval, hm, hfm, hlps, hv⟩
        · intro ci hf
          obtain ⟨cvm, mval, hm, hfm, hlps, -, hv⟩ :=
            hI₃ cvC.name hbnC ci hf
          exact ⟨cvm, mval, hm, hfm, hlps, hv⟩
        · intro j hj ci hf
          rw [hPfree₃ j hj] at hf
          exact nomatch hf
      obtain ⟨m₄, -⟩ := checkProjFold_sound hbnT hbshape
        (List.range nF) env₃ env₄ hart m₃ hinv₀ hI₃
        (fun cvT' capsT' hf => by
          rw [hTst₃] at hf
          obtain heq := Option.some.inj hf
          injection heq with e1 e2
          subst e1
          subst e2
          exact EtaPins.transport hpins₁
            (fun n ci hf' hnr =>
              checkIndRecs_find_preserved hrecs hbnrec n ci hf' hnr))
        (fun cvT' capsT' hf hcape => by
          rw [hTst₃] at hf
          obtain heq := Option.some.inj hf
          injection heq with e1 e2
          subst e1
          subst e2
          exact hbnC)
        (fun cvT' capsT' hf hcape => by
          rw [hTst₃] at hf
          obtain heq := Option.some.inj hf
          injection heq with e1 e2
          subst e1
          subst e2
          rfl)
      refine ⟨installProjTemplates_sound (List.range nF) env₄ env₂
        htpl m₄, ?_⟩
      -- the stored eta families stay closed
      intro T' cvT' capsT' hfT₂ hcape' hres'
      obtain ⟨htplNew, htplMono⟩ :=
        installProjTemplates_find_new (List.range nF) env₄ env₂ htpl
      rcases htplNew T' _ hfT₂ with hf₄ | ⟨entry, heq⟩
      case inr => exact nomatch heq
      rcases checkProjFold_find_new (List.range nF) env₃ env₄ hart
        T' _ hf₄ with hf₃ | ⟨cv2, mI2, rP2, rules2, heq⟩
      case inr => exact nomatch heq
      rcases checkIndRecs_find_new hrecs hbnrec T' _ hf₃ with
        hf₁ | ⟨cv2, mI2, rP2, rules2, heq⟩
      case inr => exact nomatch heq
      rcases hindAt₁ T' cvT' capsT' hf₁ with hf₀ | rfl
      · obtain ⟨cvC0, hfC0⟩ := hE1 T' cvT' capsT' hf₀ hcape' hres'
        refine ⟨cvC0, ?_⟩
        refine installProjTemplates_find_preserved (List.range nF)
          env₄ env₂ htpl _ _ ?_
        refine checkProjFold_find_preserved (List.range nF) env₃ env₄
          hart _ _ ?_
        refine checkIndRecs_find_preserved hrecs hbnrec _ _ ?_
          (fun _ _ _ _ hcon => nomatch hcon)
        exact checkIndFold_find_preserved _ env env₁ hfold _ _ hfC0
      · rw [hTst] at hf₁
        obtain heq := Option.some.inj hf₁
        injection heq with e1 e2
        subst e1
        subst e2
        refine ⟨cvCA, ?_⟩
        show env₂.find? cvC.name = some (.ctorInfo cvCA nP nF)
        refine installProjTemplates_find_preserved (List.range nF)
          env₄ env₂ htpl _ _ ?_
        exact checkProjFold_find_preserved (List.range nF) env₃ env₄
          hart _ _ hCst₃
    -- the two member steps, in either order
    rcases horder with hord | hord
    · -- [former, constructor]
      rw [hord] at hfold'
      simp only [List.foldlM_cons, List.foldlM_nil, Bind.bind,
        Except.bind, pure, Except.pure] at hfold'
      cases hs1 : checkIndMember (fueledOps mode F) (block.map (·.name))
          (indBlockCaps mode env cvT cvC nP nF) env
          (ConstantInfo.indInfo cvT capsT) with
      | error e => rw [hs1] at hfold'; exact nomatch hfold'
      | ok envm => ?_
      rw [hs1] at hfold'
      try dsimp only at hfold'
      cases hs2 : checkIndMember (fueledOps mode F) (block.map (·.name))
          (indBlockCaps mode env cvT cvC nP nF) envm
          (ConstantInfo.ctorInfo cvC nP nF) with
      | error e => rw [hs2] at hfold'; exact nomatch hfold'
      | ok envf => ?_
      rw [hs2] at hfold'
      obtain rfl : env₁ = envf := by
        have h9 : envf = env₁ := by simpa using hfold'
        exact h9.symm
      obtain ⟨cvAI, cvmI, mvalI, hmcvmI, hccvI, hmsI, hfmI, hlpsI,
        hrenfI, hkindI⟩ := checkIndMember_inv hs1
      obtain ⟨hfindI, hnresI, hshapeI, -, hlbI, hfvI, tyAI, sI, uI,
        hannI, hlpI, hresI, -, -, hcvAI⟩ := checkConstantVal_inv hccvI
      have hnameI : cvAI.name = cvT.name := by rw [hcvAI]; rfl
      have hlpsAI : cvAI.levelParams = cvT.levelParams := by
        rw [hcvAI]
        rfl
      have htyfI : cvAI.type.hasFvar = false := by
        rw [show cvAI.type = tyAI from by rw [hcvAI]]
        exact not_hasFvar_of_fvarsBelow_zero
          ((annotateCore_WScoped F _ hannI
            (WScoped.of_not_hasFvar hfvI)).fvarsBelow)
      have htresI : cvAI.type.constsResolve env = true := by
        rw [show cvAI.type = tyAI from by rw [hcvAI]]
        exact hresI
      have henvm : envm = ⟨.indInfo cvAI
          (indBlockCaps mode env cvT cvC nP nF) :: env.consts⟩ := by
        rcases hkindI with ⟨-, he⟩ | ⟨cv', nP', nF', heqTT, -⟩
        · exact he
        · exact nomatch heqTT
      subst henvm
      obtain ⟨cvAC, cvmC2, mvalC2, hmcvmC2, hccvC, hmsC2, hfmC2,
        hlpsC2, hrenfC2, hkindC⟩ := checkIndMember_inv hs2
      obtain ⟨hfindC, hnresC, hshapeC, -, hlbC, hfvC, tyAC, sC, uC,
        hannC, hlpC, hresC, -, -, hcvAC⟩ := checkConstantVal_inv hccvC
      have hnameC : cvAC.name = cvC.name := by rw [hcvAC]; rfl
      have henv₁ : env₁ = ⟨.ctorInfo cvAC nP nF ::
          (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF) ::
            env.consts⟩ : Env).consts⟩ := by
        rcases hkindC with ⟨⟨cv', caps'', heqTT⟩, -⟩ | ⟨cv', nP', nF', heqTT, he⟩
        · exact nomatch heqTT
        · obtain ⟨e1, e2, e3⟩ : cvC = cv' ∧ nP = nP' ∧ nF = nF' := by
            injection heqTT with f1 f2 f3
            exact ⟨f1, f2, f3⟩
          subst e1
          subst e2
          subst e3
          exact he
      have hfreshI : env.find? (ConstantInfo.indInfo cvAI
          (indBlockCaps mode env cvT cvC nP nF)).name = none := by
        show env.find? cvAI.name = none
        rw [hnameI]
        exact hfindI
      have hfindCm : (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF)
          :: env.consts⟩ : Env).find? cvC.name = none := hfindC
      -- step 1: the former
      have hHE1 := blockMember_headEta (mode := mode) m
        (ciH := .indInfo cvAI (indBlockCaps mode env cvT cvC nP nF))
        hfreshI
        (show reservedBasisNames.contains cvAI.name = false from by
          rw [hnameI]
          exact hnresI)
        (show cvAI.name.isProjFnShape = false from by
          rw [hnameI]
          exact hshapeI)
        (fun cv2 v2 hcon => nomatch hcon)
        (show (block.map (·.name)).contains cvAI.name = true from by
          rw [hnameI]
          exact hbnT)
        (fun T' cvT' capsT' hf he hr _ => hE1 T' cvT' capsT' hf he hr)
        (by
          intro T' cvT' capsT' hfT' hTb' hcape'
          by_cases hTh : (ConstantInfo.indInfo cvAI
              (indBlockCaps mode env cvT cvC nP nF)).name = T'
          · subst hTh
            rw [Env.find?_cons, if_pos rfl] at hfT'
            obtain heq2 := Option.some.inj hfT'
            injection heq2 with e1 e2
            subst e1
            subst e2
            refine ⟨?_, ?_, htyfI, htresI, ?_⟩
            · show EtaPins mode env cvAI.name cvAI.levelParams
                (indBlockCaps mode env cvT cvC nP nF)
              rw [hnameI, hlpsAI]
              exact hpinsT0
            · show (block.map (·.name)).contains cvC.name = true
              exact hbnC
            · intro j hj
              show env.find? (projFnName cvAI.name j) = none
              rw [hnameI]
              cases hf₀ : env.find? (projFnName cvT.name j) with
              | none => rfl
              | some ci₂ =>
                exfalso
                have h2 : (env₁.find? (projFnName cvT.name j)).isSome
                    = true :=
                  checkIndFold_mono _ env env₁ hfold _
                    (by rw [hf₀]; rfl)
                rw [hPfree₁ j hj] at h2
                exact nomatch h2
          · rw [Env.find?_cons, if_neg hTh] at hfT'
            exfalso
            rw [hbfresh T' hTb'] at hfT'
            exact nomatch hfT')
      obtain ⟨m₁, hI₁⟩ := checkIndMember_sound (mode := mode) hs1
        (fun cv caps₂ heq => by
          injection heq with e1 e2
          subst e1
          exact hpinsT0)
        (show (block.map (·.name)).contains
          (ConstantInfo.indInfo cvT capsT).name = true from hbnT)
        m hI₀
        (fun T' cvT' capsT' hfT' hcape' hres' hfam' hpart' val₁
            hagr hv hI₁' =>
          hHE1 T' cvT' capsT' hfT' hcape' hres' hfam'
            (by
              show T' = cvAI.name ∨ capsT'.etaCtor = cvAI.name ∨
                ∃ j, j < capsT'.etaFields ∧ projFnName T' j = cvAI.name
              rw [hnameI]
              exact hpart')
            val₁
            (fun n ψ hne => hagr n ψ
              (fun hh => hne (hh.trans hnameI.symm)))
            (fun ψ => by
              show val₁ cvAI.name ψ = m.val (cvAI.name.str "_model") ψ
              rw [hnameI]
              exact hv ψ)
            hI₁')
      -- step 2: the constructor
      have hHE2 := blockMember_headEta (mode := mode) m₁
        (ciH := .ctorInfo cvAC nP nF)
        (show (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF) ::
            env.consts⟩ : Env).find? cvAC.name = none from by
          rw [hnameC]
          exact hfindCm)
        (show reservedBasisNames.contains cvAC.name = false from by
          rw [hnameC]
          exact hnresC)
        (show cvAC.name.isProjFnShape = false from by
          rw [hnameC]
          exact hshapeC)
        (fun cv2 v2 hcon => nomatch hcon)
        (show (block.map (·.name)).contains cvAC.name = true from by
          rw [hnameC]
          exact hbnC)
        (by
          -- outside formers stay closed at the intermediate
          -- environment
          intro T' cvT' capsT' hf he hr hTb'
          have hTne : T' ≠ (ConstantInfo.indInfo cvAI
              (indBlockCaps mode env cvT cvC nP nF)).name := by
            intro hcontra
            rw [hcontra] at hTb'
            rw [show ((ConstantInfo.indInfo cvAI (indBlockCaps mode env cvT
              cvC nP nF)).name : Name) = cvAI.name from rfl, hnameI,
              hbnT] at hTb'
            exact nomatch hTb'
          rw [Env.find?_cons, if_neg (fun hh => hTne hh.symm)] at hf
          obtain ⟨cvC0, hfC0⟩ := hE1 T' cvT' capsT' hf he hr
          refine ⟨cvC0, ?_⟩
          rw [Env.find?_cons_of_isSome hfreshI (by rw [hfC0]; rfl)]
          exact hfC0)
        (by
          intro T' cvT' capsT' hfT' hTb' hcape'
          by_cases hTh : (ConstantInfo.ctorInfo cvAC nP nF).name = T'
          · subst hTh
            rw [Env.find?_cons, if_pos rfl] at hfT'
            exact nomatch (Option.some.inj hfT')
          · rw [Env.find?_cons, if_neg hTh] at hfT'
            by_cases hTI : (ConstantInfo.indInfo cvAI
                (indBlockCaps mode env cvT cvC nP nF)).name = T'
            · subst hTI
              rw [Env.find?_cons, if_pos rfl] at hfT'
              obtain heq2 := Option.some.inj hfT'
              injection heq2 with e1 e2
              subst e1
              subst e2
              refine ⟨?_, ?_, htyfI, Expr.constsResolve_mono htresI, ?_⟩
              · show EtaPins mode (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC
                    nP nF) :: env.consts⟩ : Env) cvAI.name
                  cvAI.levelParams (indBlockCaps mode env cvT cvC nP nF)
                refine EtaPins.step ?_ hfreshI
                rw [hnameI, hlpsAI]
                exact hpinsT0
              · show (block.map (·.name)).contains cvC.name = true
                exact hbnC
              · intro j hj
                show (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF)
                  :: env.consts⟩ : Env).find?
                    (projFnName cvAI.name j) = none
                rw [hnameI]
                cases hf₀ : (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC
                    nP nF) :: env.consts⟩ : Env).find?
                    (projFnName cvT.name j) with
                | none => rfl
                | some ci₂ =>
                  exfalso
                  have h2 : (env₁.find? (projFnName cvT.name j)).isSome
                      = true := by
                    rw [henv₁]
                    rw [Env.find?_cons_of_isSome
                      (by
          show (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF) ::
            env.consts⟩ : Env).find? cvAC.name = none
          rw [hnameC]
          exact hfindCm)
                      (by rw [hf₀]; rfl)]
                    rw [hf₀]
                    rfl
                  rw [hPfree₁ j hj] at h2
                  exact nomatch h2
            · rw [Env.find?_cons, if_neg hTI] at hfT'
              exfalso
              rw [hbfresh T' hTb'] at hfT'
              exact nomatch hfT')
      have henv₁' : (⟨.ctorInfo cvAC nP nF ::
          (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF) ::
            env.consts⟩ : Env).consts⟩ : Env) = env₁ := henv₁.symm
      obtain ⟨m₂', hI₂⟩ := checkIndMember_sound (mode := mode) hs2
        (fun cv caps₂ heq => nomatch heq)
        (show (block.map (·.name)).contains
          (ConstantInfo.ctorInfo cvC nP nF).name = true from hbnC)
        m₁ hI₁
        (by
          rw [← henv₁']
          exact fun T' cvT' capsT' hfT' hcape' hres' hfam' hpart' val₁
              hagr hv hI₁' =>
            hHE2 T' cvT' capsT' hfT' hcape' hres' hfam'
              (by
                show T' = cvAC.name ∨ capsT'.etaCtor = cvAC.name ∨
                  ∃ j, j < capsT'.etaFields ∧
                    projFnName T' j = cvAC.name
                rw [hnameC]
                exact hpart')
              val₁
              (fun n ψ hne => hagr n ψ
                (fun hh => hne (hh.trans hnameC.symm)))
              (fun ψ => by
                show val₁ cvAC.name ψ =
                  m₁.val (cvAC.name.str "_model") ψ
                rw [hnameC]
                exact hv ψ)
              hI₁')
      refine hrest m₂' hI₂ ⟨cvAI, ?_, ?_⟩ ⟨cvAC, ?_⟩ ?_
      · rw [henv₁]
        rw [Env.find?_cons_of_isSome (by
          show (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF) ::
            env.consts⟩ : Env).find? cvAC.name = none
          rw [hnameC]
          exact hfindCm)
          (by rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo
            cvAI (indBlockCaps mode env cvT cvC nP nF)).name = cvT.name
            from hnameI)]; rfl)]
        rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo cvAI
          (indBlockCaps mode env cvT cvC nP nF)).name = cvT.name
          from hnameI)]
      · rw [henv₁]
        refine EtaPins.step ?_ (by
          show (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF) ::
            env.consts⟩ : Env).find? cvAC.name = none
          rw [hnameC]
          exact hfindCm)
        refine EtaPins.step ?_ hfreshI
        rw [← hlpsAI] at hpinsT0
        exact hpinsT0
      · rw [henv₁]
        rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo cvAC
          nP nF).name = cvC.name from hnameC)]
      · intro n cv2 caps2 hf
        rw [henv₁, Env.find?_cons] at hf
        split at hf
        · exact nomatch (Option.some.inj hf)
        · rw [Env.find?_cons] at hf
          split at hf
          · next hh =>
            obtain heq2 := Option.some.inj hf
            injection heq2 with e1 e2
            refine Or.inr ?_
            rw [← hh]
            exact hnameI.symm ▸ rfl
          · exact Or.inl hf
    · -- [constructor, former]
      rw [hord] at hfold'
      simp only [List.foldlM_cons, List.foldlM_nil, Bind.bind,
        Except.bind, pure, Except.pure] at hfold'
      cases hs1 : checkIndMember (fueledOps mode F) (block.map (·.name))
          (indBlockCaps mode env cvT cvC nP nF) env
          (ConstantInfo.ctorInfo cvC nP nF) with
      | error e => rw [hs1] at hfold'; exact nomatch hfold'
      | ok envm => ?_
      rw [hs1] at hfold'
      try dsimp only at hfold'
      cases hs2 : checkIndMember (fueledOps mode F) (block.map (·.name))
          (indBlockCaps mode env cvT cvC nP nF) envm
          (ConstantInfo.indInfo cvT capsT) with
      | error e => rw [hs2] at hfold'; exact nomatch hfold'
      | ok envf => ?_
      rw [hs2] at hfold'
      obtain rfl : env₁ = envf := by
        have h9 : envf = env₁ := by simpa using hfold'
        exact h9.symm
      obtain ⟨cvAC, cvmC2, mvalC2, hmcvmC2, hccvC, hmsC2, hfmC2,
        hlpsC2, hrenfC2, hkindC⟩ := checkIndMember_inv hs1
      obtain ⟨hfindC, hnresC, hshapeC, -, hlbC, hfvC, tyAC, sC, uC,
        hannC, hlpC, hresC, -, -, hcvAC⟩ := checkConstantVal_inv hccvC
      have hnameC : cvAC.name = cvC.name := by rw [hcvAC]; rfl
      have henvm : envm = ⟨.ctorInfo cvAC nP nF :: env.consts⟩ := by
        rcases hkindC with ⟨⟨cv', caps'', heqTT⟩, -⟩ |
          ⟨cv', nP', nF', heqTT, he⟩
        · exact nomatch heqTT
        · obtain ⟨e1, e2, e3⟩ : cvC = cv' ∧ nP = nP' ∧ nF = nF' := by
            injection heqTT with f1 f2 f3
            exact ⟨f1, f2, f3⟩
          subst e1
          subst e2
          subst e3
          exact he
      subst henvm
      obtain ⟨cvAI, cvmI, mvalI, hmcvmI, hccvI, hmsI, hfmI, hlpsI,
        hrenfI, hkindI⟩ := checkIndMember_inv hs2
      obtain ⟨hfindI, hnresI, hshapeI, -, hlbI, hfvI, tyAI, sI, uI,
        hannI, hlpI, hresI, -, -, hcvAI⟩ := checkConstantVal_inv hccvI
      have hnameI : cvAI.name = cvT.name := by rw [hcvAI]; rfl
      have hlpsAI : cvAI.levelParams = cvT.levelParams := by
        rw [hcvAI]
        rfl
      have htyfI : cvAI.type.hasFvar = false := by
        rw [show cvAI.type = tyAI from by rw [hcvAI]]
        exact not_hasFvar_of_fvarsBelow_zero
          ((annotateCore_WScoped F _ hannI
            (WScoped.of_not_hasFvar hfvI)).fvarsBelow)
      have htresIm : cvAI.type.constsResolve
          (⟨.ctorInfo cvAC nP nF :: env.consts⟩ : Env) = true := by
        rw [show cvAI.type = tyAI from by rw [hcvAI]]
        exact hresI
      have henv₁ : env₁ = ⟨.indInfo cvAI
          (indBlockCaps mode env cvT cvC nP nF) ::
          (⟨.ctorInfo cvAC nP nF :: env.consts⟩ : Env).consts⟩ := by
        rcases hkindI with ⟨-, he⟩ | ⟨cv', nP', nF', heqTT, -⟩
        · exact he
        · exact nomatch heqTT
      have hfreshC : env.find? (ConstantInfo.ctorInfo cvAC nP
          nF).name = none := by
        show env.find? cvAC.name = none
        rw [hnameC]
        exact hfindC
      have hfreshIm : (⟨.ctorInfo cvAC nP nF :: env.consts⟩ :
          Env).find? (ConstantInfo.indInfo cvAI (indBlockCaps mode env cvT
            cvC nP nF)).name = none := by
        show (⟨.ctorInfo cvAC nP nF :: env.consts⟩ : Env).find?
          cvAI.name = none
        rw [hnameI]
        exact hfindI
      -- step 1: the constructor (nothing eta-capable is stored yet)
      have hHE1 := blockMember_headEta (mode := mode) m
        (ciH := .ctorInfo cvAC nP nF)
        hfreshC
        (show reservedBasisNames.contains cvAC.name = false from by
          rw [hnameC]
          exact hnresC)
        (show cvAC.name.isProjFnShape = false from by
          rw [hnameC]
          exact hshapeC)
        (fun cv2 v2 hcon => nomatch hcon)
        (show (block.map (·.name)).contains cvAC.name = true from by
          rw [hnameC]
          exact hbnC)
        (fun T' cvT' capsT' hf he hr _ => hE1 T' cvT' capsT' hf he hr)
        (by
          intro T' cvT' capsT' hfT' hTb' hcape'
          by_cases hTh : (ConstantInfo.ctorInfo cvAC nP nF).name = T'
          · subst hTh
            rw [Env.find?_cons, if_pos rfl] at hfT'
            exact nomatch (Option.some.inj hfT')
          · rw [Env.find?_cons, if_neg hTh] at hfT'
            exfalso
            rw [hbfresh T' hTb'] at hfT'
            exact nomatch hfT')
      obtain ⟨m₁, hI₁⟩ := checkIndMember_sound (mode := mode) hs1
        (fun cv caps₂ heq => nomatch heq)
        (show (block.map (·.name)).contains
          (ConstantInfo.ctorInfo cvC nP nF).name = true from hbnC)
        m hI₀
        (fun T' cvT' capsT' hfT' hcape' hres' hfam' hpart' val₁
            hagr hv hI₁' =>
          hHE1 T' cvT' capsT' hfT' hcape' hres' hfam'
            (by
              show T' = cvAC.name ∨ capsT'.etaCtor = cvAC.name ∨
                ∃ j, j < capsT'.etaFields ∧ projFnName T' j = cvAC.name
              rw [hnameC]
              exact hpart')
            val₁
            (fun n ψ hne => hagr n ψ
              (fun hh => hne (hh.trans hnameC.symm)))
            (fun ψ => by
              show val₁ cvAC.name ψ = m.val (cvAC.name.str "_model") ψ
              rw [hnameC]
              exact hv ψ)
            hI₁')
      -- step 2: the former (a fieldless family may complete here)
      have hHE2 := blockMember_headEta (mode := mode) m₁
        (ciH := .indInfo cvAI (indBlockCaps mode env cvT cvC nP nF))
        hfreshIm
        (show reservedBasisNames.contains cvAI.name = false from by
          rw [hnameI]
          exact hnresI)
        (show cvAI.name.isProjFnShape = false from by
          rw [hnameI]
          exact hshapeI)
        (fun cv2 v2 hcon => nomatch hcon)
        (show (block.map (·.name)).contains cvAI.name = true from by
          rw [hnameI]
          exact hbnT)
        (by
          intro T' cvT' capsT' hf he hr hTb'
          have hTne : T' ≠ (ConstantInfo.ctorInfo cvAC nP nF).name := by
            intro hcontra
            rw [hcontra] at hTb'
            rw [show ((ConstantInfo.ctorInfo cvAC nP nF).name : Name) =
              cvAC.name from rfl, hnameC, hbnC] at hTb'
            exact nomatch hTb'
          rw [Env.find?_cons, if_neg (fun hh => hTne hh.symm)] at hf
          obtain ⟨cvC0, hfC0⟩ := hE1 T' cvT' capsT' hf he hr
          refine ⟨cvC0, ?_⟩
          rw [Env.find?_cons_of_isSome hfreshC (by rw [hfC0]; rfl)]
          exact hfC0)
        (by
          intro T' cvT' capsT' hfT' hTb' hcape'
          by_cases hTh : (ConstantInfo.indInfo cvAI
              (indBlockCaps mode env cvT cvC nP nF)).name = T'
          · subst hTh
            rw [Env.find?_cons, if_pos rfl] at hfT'
            obtain heq2 := Option.some.inj hfT'
            injection heq2 with e1 e2
            subst e1
            subst e2
            refine ⟨?_, ?_, htyfI, ?_, ?_⟩
            · show EtaPins mode (⟨.ctorInfo cvAC nP nF :: env.consts⟩ : Env)
                cvAI.name cvAI.levelParams
                (indBlockCaps mode env cvT cvC nP nF)
              refine EtaPins.step ?_ hfreshC
              rw [hnameI, hlpsAI]
              exact hpinsT0
            · show (block.map (·.name)).contains cvC.name = true
              exact hbnC
            · show cvAI.type.constsResolve
                (⟨.ctorInfo cvAC nP nF :: env.consts⟩ : Env) = true
              exact htresIm
            · intro j hj
              show (⟨.ctorInfo cvAC nP nF :: env.consts⟩ : Env).find?
                (projFnName cvAI.name j) = none
              rw [hnameI]
              cases hf₀ : (⟨.ctorInfo cvAC nP nF :: env.consts⟩ :
                  Env).find? (projFnName cvT.name j) with
              | none => rfl
              | some ci₂ =>
                exfalso
                have h2 : (env₁.find? (projFnName cvT.name j)).isSome
                    = true := by
                  rw [henv₁]
                  rw [Env.find?_cons_of_isSome hfreshIm
                    (by rw [hf₀]; rfl)]
                  rw [hf₀]
                  rfl
                rw [hPfree₁ j hj] at h2
                exact nomatch h2
          · rw [Env.find?_cons, if_neg hTh] at hfT'
            by_cases hTC : (ConstantInfo.ctorInfo cvAC nP nF).name = T'
            · subst hTC
              rw [Env.find?_cons, if_pos rfl] at hfT'
              exact nomatch (Option.some.inj hfT')
            · rw [Env.find?_cons, if_neg hTC] at hfT'
              exfalso
              rw [hbfresh T' hTb'] at hfT'
              exact nomatch hfT')
      have henv₁' : (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF) ::
          (⟨.ctorInfo cvAC nP nF :: env.consts⟩ : Env).consts⟩ : Env)
          = env₁ := henv₁.symm
      obtain ⟨m₂', hI₂⟩ := checkIndMember_sound (mode := mode) hs2
        (fun cv caps₂ heq => by
          injection heq with e1 e2
          subst e1
          exact EtaPins.step hpinsT0 hfreshC)
        (show (block.map (·.name)).contains
          (ConstantInfo.indInfo cvT capsT).name = true from hbnT)
        m₁ hI₁
        (by
          rw [← henv₁']
          exact fun T' cvT' capsT' hfT' hcape' hres' hfam' hpart' val₁
              hagr hv hI₁' =>
            hHE2 T' cvT' capsT' hfT' hcape' hres' hfam'
              (by
                show T' = cvAI.name ∨ capsT'.etaCtor = cvAI.name ∨
                  ∃ j, j < capsT'.etaFields ∧
                    projFnName T' j = cvAI.name
                rw [hnameI]
                exact hpart')
              val₁
              (fun n ψ hne => hagr n ψ
                (fun hh => hne (hh.trans hnameI.symm)))
              (fun ψ => by
                show val₁ cvAI.name ψ =
                  m₁.val (cvAI.name.str "_model") ψ
                rw [hnameI]
                exact hv ψ)
              hI₁')
      refine hrest m₂' hI₂ ⟨cvAI, ?_, ?_⟩ ⟨cvAC, ?_⟩ ?_
      · rw [henv₁]
        rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo cvAI
          (indBlockCaps mode env cvT cvC nP nF)).name = cvT.name
          from hnameI)]
      · rw [henv₁]
        refine EtaPins.step ?_ hfreshIm
        refine EtaPins.step ?_ hfreshC
        rw [← hlpsAI] at hpinsT0
        exact hpinsT0
      · rw [henv₁]
        rw [Env.find?_cons_of_isSome hfreshIm
          (by rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo
            cvAC nP nF).name = cvC.name from hnameC)]; rfl)]
        rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo cvAC
          nP nF).name = cvC.name from hnameC)]
      · intro n cv2 caps2 hf
        rw [henv₁, Env.find?_cons] at hf
        split at hf
        · next hh =>
          obtain heq2 := Option.some.inj hf
          injection heq2 with e1 e2
          refine Or.inr ?_
          rw [← hh]
          exact hnameI.symm ▸ rfl
        · rw [Env.find?_cons] at hf
          split at hf
          · exact nomatch (Option.some.inj hf)
          · exact Or.inl hf
  · -- no single-constructor structure: member fold, then the recursors
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨env₁, hfold, hrecs⟩ := Except.bind_ok h
    have hbnrec : ∀ ci ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => true | _ => false),
        (block.map (·.name)).contains ci.name = true :=
      fun ci hci => hbn ci (List.mem_filter.mp hci).1
    have hI₀ : BlockInstalled (block.map (·.name)) env m.val := by
      intro n hn ci₂ hf₂
      have hmem : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with hci₀ | hci₀
      · rw [checkIndMember_fold_names _ env env₁ hfold ci₀ hci₀] at hf₂
        exact nomatch hf₂
      · have h1 := checkIndRecs_names hrecs ci₀ hci₀
        have h2 : (env₁.find? ci₀.name).isSome = true :=
          checkIndFold_mono _ env env₁ hfold ci₀.name (by rw [hf₂]; rfl)
        rw [h1] at h2
        exact nomatch h2
    have hE1O₀ : EtaFamiliesClosedO (block.map (·.name)) env :=
      fun T cvT caps hf he hr _ => hE1 T cvT caps hf he hr
    have hBcaps₀ : BlockCapsPinned (block.map (·.name)) {} env := by
      intro n cvS capsS hnb hf
      exfalso
      have hmem : n ∈ block.map (·.name) := by simpa using hnb
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with hci₀ | hci₀
      · rw [checkIndMember_fold_names _ env env₁ hfold ci₀ hci₀] at hf
        exact nomatch hf
      · have h1 := checkIndRecs_names hrecs ci₀ hci₀
        have h2 : (env₁.find? ci₀.name).isSome = true :=
          checkIndFold_mono _ env env₁ hfold ci₀.name (by rw [hf]; rfl)
        rw [h1] at h2
        exact nomatch h2
    obtain ⟨m₁, hI₁, hE1O₁, hBcaps₁⟩ := checkIndFold_sound (by decide)
      _ env env₁
      (fun ci hci => hbn ci (List.mem_filter.mp hci).1)
      (fun _ _ _ => ⟨fun hcape => absurd hcape (by decide),
        fun hcapu => absurd hcapu (by decide)⟩)
      hfold m hI₀ hE1O₀ hBcaps₀
    obtain ⟨m₂', -⟩ := checkIndRecs_sound hrecs
      (fun ci hci => hbn ci (List.mem_filter.mp hci).1)
      (fun n hn => by
        have hmem : n ∈ block.map (·.name) := by simpa using hn
        obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
        rw [hsplit] at hci₀
        rcases List.mem_append.mp hci₀ with hci₀ | hci₀
        · exact Or.inl (checkIndFold_stored _ env env₁ hfold ci₀ hci₀)
        · exact Or.inr ⟨ci₀, hci₀, rfl⟩)
      (fun n hn => by
        have hmem : n ∈ block.map (·.name) := by simpa using hn
        obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
        rw [hsplit] at hci₀
        rcases List.mem_append.mp hci₀ with hci₀ | hci₀
        · exact checkIndFold_modelfree _ env env₁ hfold ci₀ hci₀
        · exact checkIndRecs_modelfree hrecs ci₀ hci₀)
      m₁ hI₁
    refine ⟨⟨m₂'⟩, ?_⟩
    -- the stored eta families stay closed: nothing eta-capable was
    -- added (the generic record claims no capability)
    intro T cvT capsT hfT hcape hresT
    rcases checkIndRecs_find_new hrecs hbnrec T _ hfT with hfT₁ | hk
    · rcases checkIndFold_find_new _ env env₁
        (fun ci hci => hbn ci (List.mem_filter.mp hci).1) hfold T _ hfT₁
        with hfT₀ | ⟨-, hknew⟩
      · obtain ⟨cvC0, hfC0⟩ := hE1 T cvT capsT hfT₀ hcape hresT
        refine ⟨cvC0, ?_⟩
        exact checkIndRecs_find_preserved hrecs hbnrec _ _
          (checkIndFold_find_preserved _ env env₁ hfold _ _ hfC0)
          (fun _ _ _ _ hcon => nomatch hcon)
      · rcases hknew with ⟨cv, heq⟩ | ⟨cv, nP', nF', heq⟩
        · injection heq with e1 e2
          rw [e2] at hcape
          exact absurd hcape (by decide)
        · exact nomatch heq
    · obtain ⟨cv, mI, rP, rules, heq⟩ := hk
      exact nomatch heq


end Setlec
