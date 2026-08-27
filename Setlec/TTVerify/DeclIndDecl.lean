import Setlec.TTVerify.DeclIndProj
import Setlec.Verify.Extend.Decl
import Setlec.TTVerify.DeclStep

/-!
# `DeclIndTT`, assembled

The transpose of `checkIndDecl_sound` (`Setlec/Model/Extend/Decl.lean`):
the recursor-suffix split, the single-constructor arm assembled member
by member with the family-completing step discharging the public eta
law, the constructor-residual (#136) and projection-freshness checks,
the recursor group and the projection phases — and with it, the sixth
case of `CheckDeclTT`.

The threaded `EtaFamiliesClosed` is consumed exactly once, at the
member installs: a fresh block constructor whose name is an *older*
eta-capable former's capability constructor would owe that family's
law, and closure refutes the collision (the older family's constructor
slot is already taken).
-/

set_option linter.unusedVariables false

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

variable {F : Nat}

/-- Invert the task-#136 constructor-residual check at a positive
capability. -/
theorem ctorResidualOk_invT {env' : Env} {T ctorName : Name}
    {lps : List Name} {nP nF : Nat}
    (h : ctorResidualOk mode env' T ctorName lps nP nF true = true) :
    ∃ cvCA a b bs, env'.find? ctorName = some (.ctorInfo cvCA a b) ∧
      cvCA.type.stripPis (nP + nF) = some (bs, directFam T lps nP nF) := by
  rw [ctorResidualOk] at h
  simp only [Bool.not_true] at h
  revert h
  match hfc : env'.find? ctorName with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvCA a b) => ?_
  intro h
  dsimp only at h
  revert h
  match hs : cvCA.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some (bs, cbody) => ?_
  intro h
  dsimp only at h
  exact ⟨cvCA, a, b, bs, rfl, by rw [hs, eq_of_beq h]⟩

/-- The direct-install path is off under the certified
configuration. -/
theorem directParts?_none (hdir : CertifiedConfigTT mode) (env : Env)
    (block : List ConstantInfo) : directParts? env block = none := by
  unfold directParts?
  cases directPartsCore? block with
  | none => rfl
  | some p =>
    rw [show directStructsEnabled = false from hdir.direct]
    rfl

set_option maxHeartbeats 12800000 in
/-- **The modeled-inductive install preserves the derivation model.**
Transpose of `checkIndDecl_sound`'s statement half (its closure half
is `FamiliesStepTT`'s business). -/
theorem declIndTT : DeclIndTT F := by
  intro env env₁ block h hdir m hE1
  rw [show checkDecl mode (fueledOps mode F) env (.indDecl block) =
      (match directParts? env block with
        | some p => checkDirectStruct (fueledOps mode F) env p
        | none => checkIndDecl mode (fueledOps mode F) env block) from rfl,
    directParts?_none hdir env block] at h
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
  simp only [pure, Except.pure] at h
  try dsimp only at h
  split at h
  · -- the single-constructor arm
    rename_i cvT capsT cvC nP nF heqI heqC
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨env₂, hfold, h⟩ := Except.bind_ok h
    obtain ⟨env₃, hrecs, h⟩ := Except.bind_ok h
    have hbnrec : ∀ ci ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => true | _ => false),
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
      · exact checkIndMember_fold_names _ env env₂ hfold ci₀ hci₀
      · have h1 := checkIndRecs_names hrecs ci₀ hci₀
        cases hf₀ : env.find? ci₀.name with
        | none => rfl
        | some ci₂ =>
          exfalso
          have h2 : (env₂.find? ci₀.name).isSome = true :=
            checkIndFold_mono _ env env₂ hfold ci₀.name
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
      rcases checkIndFold_kinds _ env env₂ hfold ci hci with
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
        = .ok env₂ := hfold
    -- the eta constructor's residual (task #136)
    by_cases hctorRes : ctorResidualOk mode env₃ cvT.name cvC.name
        cvT.levelParams nP nF (indBlockCaps mode env cvT cvC nP nF).eta = true
    case neg => rw [if_neg hctorRes] at h; exact nomatch h
    rw [if_pos hctorRes] at h
    try simp only [pure, Except.pure] at h
    try dsimp only at h
    try simp only [Bind.bind, Except.bind] at h
    -- the projection-family freshness check
    by_cases hfreshP : ((List.range nF).all
        (fun j => (env₃.find? (projFnName cvT.name j)).isNone)) = true
    case neg => rw [if_neg hfreshP] at h; exact nomatch h
    rw [if_pos hfreshP] at h
    try simp only [pure, Except.pure] at h
    try dsimp only at h
    try simp only [Bind.bind, Except.bind] at h
    obtain ⟨env₄, hart, htpl⟩ := Except.bind_ok h
    have hmono₁₃ : ∀ n, (env₂.find? n).isSome = true →
        (env₃.find? n).isSome = true :=
      fun n hn => checkIndRecs_mono hrecs hbnrec n hn
    have hPfree₃ : ∀ j, j < nF →
        env₃.find? (projFnName cvT.name j) = none := by
      intro j hj
      have h1 := List.all_eq_true.mp hfreshP j (List.mem_range.mpr hj)
      exact Option.isNone_iff_eq_none.mp (by simpa using h1)
    have hPfree₂ : ∀ j, j < nF →
        env₂.find? (projFnName cvT.name j) = none := by
      intro j hj
      cases hf₀ : env₂.find? (projFnName cvT.name j) with
      | none => rfl
      | some ci₂ =>
        exfalso
        have h2 := hmono₁₃ _ (by rw [hf₀]; rfl)
        rw [hPfree₃ j hj] at h2
        exact nomatch h2
    -- pins for the former at the base
    have hpinsT0 : EtaPins mode env cvT.name cvT.levelParams
        (indBlockCaps mode env cvT cvC nP nF) := etaPinsT_of_caps
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
    have hI₀ : BlockInstalledTT (block.map (·.name)) env m.cval := by
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
      · exact checkIndFold_projshape _ env env₂ hfold ci₀ hci₀
      · exact checkIndRecs_projshape hrecs ci₀ hci₀
    have hnmS : ∀ n, (block.map (·.name)).contains n = true →
        n.isModelSuffix = false := by
      intro n hn
      have hmem : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with hci₀ | hci₀
      · exact checkIndFold_modelfree _ env env₂ hfold ci₀ hci₀
      · exact checkIndRecs_modelfree hrecs ci₀ hci₀
    -- the residual pin, once (its find? is at env₃; the member steps
    -- transport their own into it)
    have hPinAt : (indBlockCaps mode env cvT cvC nP nF).eta = true →
        ∀ cvC' : ConstantVal,
        env₃.find? cvC.name = some (.ctorInfo cvC' nP nF) →
        CtorResidualPin cvT.name cvT.levelParams cvC' nP nF := by
      intro hcape cvC' hf₃
      rw [hcape] at hctorRes
      obtain ⟨cvCA, a, b, bs, hfCA, hstrip⟩ := ctorResidualOk_invT
        hctorRes
      rw [hf₃] at hfCA
      obtain heq2 := Option.some.inj hfCA
      injection heq2 with e1 e2 e3
      subst e1
      exact ⟨bs, hstrip⟩
    -- the shared tail: recursors, projections, templates
    have hrest : ∀ (m₂ : EnvTT env₂),
        BlockInstalledTT (block.map (·.name)) env₂ m₂.cval →
        reservedBasisNames.contains cvT.name = false →
        (∃ cvTA, env₂.find? cvT.name =
          some (.indInfo cvTA (indBlockCaps mode env cvT cvC nP nF)) ∧
          cvTA.levelParams = cvT.levelParams ∧
          EtaPins mode env₂ cvT.name cvTA.levelParams
            (indBlockCaps mode env cvT cvC nP nF)) →
        (∃ cvCA, env₂.find? cvC.name = some (.ctorInfo cvCA nP nF)) →
        Nonempty (EnvTT env₁) := by
      rintro m₂ hI₂ hTnres ⟨cvTA, hTst, hTAlps, hpins₂⟩ ⟨cvCA, hCst⟩
      obtain ⟨m₃, hI₃⟩ := checkIndRecsTT hrecs hbnrec
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
        (fun n hn => hnmS n hn)
        m₂ hI₂
      have hTst₃ : env₃.find? cvT.name =
          some (.indInfo cvTA (indBlockCaps mode env cvT cvC nP nF)) :=
        checkIndRecs_find_preserved hrecs hbnrec _ _ hTst
          (fun _ _ _ _ hcon => nomatch hcon)
      have hCst₃ : env₃.find? cvC.name = some (.ctorInfo cvCA nP nF) :=
        checkIndRecs_find_preserved hrecs hbnrec _ _ hCst
          (fun _ _ _ _ hcon => nomatch hcon)
      have hinv₀ : ProjPhaseInvT cvT.name cvC.name nF env₃ m₃.cval := by
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
      obtain ⟨m₄, hinv₄⟩ := checkProjFoldTT hbnT hbshape
        (List.range nF) env₃ env₄ hart m₃ hinv₀ hI₃
        ⟨cvTA, _, hTst₃⟩
        (fun cvT' capsT' hf => by
          rw [hTst₃] at hf
          obtain heq := Option.some.inj hf
          injection heq with e1 e2
          subst e1
          subst e2
          exact EtaPins.transport hpins₂
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
      exact installProjTemplatesTT hTnres (List.range nF) env₄ env₁
        htpl m₄
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
      obtain rfl : env₂ = envf := by
        have h9 : envf = env₂ := by simpa using hfold'
        exact h9.symm
      obtain ⟨cvAI, cvmI, mvalI, hmcvmI, hccvI, hmsI, hfmI, hlpsI,
        hrenfI, hkindI⟩ := checkIndMember_inv hs1
      obtain ⟨hfindI, hnresI, hshapeI, -, hlbI, hfvI, tyAI, sI, uI,
        hannI, hlpI, hresI, -, -, hcvAI⟩ := checkConstantVal_inv hccvI
      have hnameI : cvAI.name = cvT.name := by rw [hcvAI]; rfl
      have hlpsAI : cvAI.levelParams = cvT.levelParams := by
        rw [hcvAI]
        rfl
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
      have henv₂ : env₂ = ⟨.ctorInfo cvAC nP nF ::
          (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF) ::
            env.consts⟩ : Env).consts⟩ := by
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
      subst henv₂
      have hfreshI : env.find? cvAI.name = none := by
        rw [hnameI]
        exact hfindI
      have hfreshT : env.find? cvT.name = none := by
        rw [← hnameI]
        exact hfreshI
      have hfindCm : (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF)
          :: env.consts⟩ : Env).find? cvC.name = none := hfindC
      have hCneT : cvC.name ≠ cvT.name := by
        intro he
        rw [he] at hfindCm
        rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo cvAI
          (indBlockCaps mode env cvT cvC nP nF)).name = cvT.name
          from hnameI)] at hfindCm
        exact nomatch hfindCm
      -- projection names of the block former are free at the base
      have hPfree₀ : ∀ j, j < nF →
          env.find? (projFnName cvT.name j) = none := by
        intro j hj
        cases hf₀ : env.find? (projFnName cvT.name j) with
        | none => rfl
        | some ci₂ =>
          exfalso
          have h2 := checkIndFold_mono _ env _ hfold
            (projFnName cvT.name j) (by rw [hf₀]; rfl)
          rw [hPfree₂ j hj] at h2
          exact nomatch h2
      -- step 1: the former
      obtain ⟨m₁, hI₁⟩ := checkIndMemberTT hs1
        (fun cv caps₂ heq => by
          injection heq with e1 e2
          subst e1
          exact hpinsT0)
        (show (block.map (·.name)).contains
          (ConstantInfo.indInfo cvT capsT).name = true from hbnT)
        m hI₀
        (by
          -- the eta head obligation
          intro T' cvT' capsT' hfT' hcape' hres' hfam' hpart' cval₁
            hagr halias hI₁c
          have hcv : cval₁ =
              cvalAlias m.cval cvAI.name (cvAI.name.str "_model") := by
            funext c ψ
            by_cases hc : c = cvAI.name
            · subst hc
              rw [cvalAlias_self, hnameI]
              exact congrFun halias ψ
            · rw [cvalAlias_ne hc]
              exact congrFun (hagr c (fun hh => hc (hh.trans
                (show (ConstantInfo.indInfo cvT capsT).name =
                  cvAI.name from hnameI.symm)))) ψ
          subst hcv
          refine blockMemberHeadEtaTT (ciH := .indInfo cvAI
            (indBlockCaps mode env cvT cvC nP nF)) m hfreshI
            (show reservedBasisNames.contains cvAI.name = false from by
              rw [hnameI]; exact hnresI)
            (show cvAI.name.isProjFnShape = false from by
              rw [hnameI]; exact hshapeI)
            (Or.inl ⟨_, _, rfl⟩)
            (show (block.map (·.name)).contains cvAI.name = true from by
              rw [hnameI]; exact hbnT)
            (fun T2 cvT2 capsT2 hf2 he2 hr2 _ => hE1 T2 cvT2 capsT2
              hf2 he2 hr2)
            ?_ hI₁c T' cvT' capsT' hfT' hcape' hres' hfam'
            (by
              rw [show (ConstantInfo.indInfo cvAI (indBlockCaps mode env cvT
                cvC nP nF)).name = cvAI.name from rfl, hnameI]
              exact hpart')
          -- the block-former facts at the extension
          intro T2 cvT2 capsT2 hfT2 hTb2 hcape2
          by_cases hTh : (ConstantInfo.indInfo cvAI
              (indBlockCaps mode env cvT cvC nP nF)).name = T2
          · rw [Env.find?_cons, if_pos hTh] at hfT2
            obtain heq2 := Option.some.inj hfT2
            injection heq2 with e1 e2
            subst e1
            subst e2
            rw [← hTh]
            refine ⟨?_, ?_, ?_, ?_⟩
            · show EtaPins mode env cvAI.name cvAI.levelParams
                (indBlockCaps mode env cvT cvC nP nF)
              rw [hnameI, hlpsAI]
              exact hpinsT0
            · show (block.map (·.name)).contains cvC.name = true
              exact hbnC
            · exact htresI
            · intro j hj
              show env.find? (projFnName cvAI.name j) = none
              rw [hnameI]
              exact hPfree₀ j hj
          · rw [Env.find?_cons, if_neg hTh] at hfT2
            exfalso
            rw [hbfresh T2 hTb2] at hfT2
            exact nomatch hfT2)
        (by
          -- the residual head obligation
          intro T' cvT' capsT' cvC' hfT' hcape' hTres' hCres' hfC' hor
          exfalso
          rcases hor with rfl | hC
          · -- the fresh former's family: its constructor is unstored
            rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo cvAI
              (indBlockCaps mode env cvT cvC nP nF)).name =
              (ConstantInfo.indInfo cvT capsT).name from hnameI)] at hfT'
            obtain heq2 := Option.some.inj hfT'
            injection heq2 with e1 e2
            subst e1
            subst e2
            have hCneH : cvC.name ≠ (ConstantInfo.indInfo cvT
                capsT).name := hCneT
            rw [show (indBlockCaps mode env cvT cvC nP nF).etaCtor
              = cvC.name from rfl] at hfC'
            rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.indInfo cvAI
              (indBlockCaps mode env cvT cvC nP nF)).name = cvC.name from
              fun hh => hCneT ((hnameI.symm.trans hh).symm))] at hfC'
            rw [hbfresh cvC.name hbnC] at hfC'
            exact nomatch hfC'
          · -- an older family's constructor slot is already taken
            by_cases hTh : T' = (ConstantInfo.indInfo cvT capsT).name
            · subst hTh
              rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo
                cvAI (indBlockCaps mode env cvT cvC nP nF)).name =
                (ConstantInfo.indInfo cvT capsT).name from hnameI)]
                at hfT'
              obtain heq2 := Option.some.inj hfT'
              injection heq2 with e1 e2
              subst e1
              subst e2
              exact hCneT hC
            · rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.indInfo
                cvAI (indBlockCaps mode env cvT cvC nP nF)).name = T' from
                fun hh => hTh (hnameI.symm.trans hh).symm)] at hfT'
              obtain ⟨cvC0, hfC0⟩ := hE1 T' cvT' capsT' hfT' hcape'
                hTres'
              have hsC : (env.find? capsT'.etaCtor).isSome = true := by
                rw [hfC0]
                rfl
              rw [hC] at hsC
              rw [show (ConstantInfo.indInfo cvT capsT).name = cvT.name
                from rfl, hfreshT] at hsC
              exact nomatch hsC)
      -- step 2: the constructor
      have hfreshC : (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC nP nF) ::
          env.consts⟩ : Env).find? cvAC.name = none := by
        rw [hnameC]
        exact hfindCm
      obtain ⟨m₂, hI₂⟩ := checkIndMemberTT hs2
        (fun cv caps₂ heq => nomatch heq)
        (show (block.map (·.name)).contains
          (ConstantInfo.ctorInfo cvC nP nF).name = true from hbnC)
        m₁ hI₁
        (by
          -- the eta head obligation: the fieldless family may
          -- complete here
          intro T' cvT' capsT' hfT' hcape' hres' hfam' hpart' cval₁
            hagr halias hI₁c
          have hcv : cval₁ =
              cvalAlias m₁.cval cvAC.name (cvAC.name.str "_model") := by
            funext c ψ
            by_cases hc : c = cvAC.name
            · subst hc
              rw [cvalAlias_self, hnameC]
              exact congrFun halias ψ
            · rw [cvalAlias_ne hc]
              exact congrFun (hagr c (fun hh => hc (hh.trans
                (show (ConstantInfo.ctorInfo cvC nP nF).name =
                  cvAC.name from hnameC.symm)))) ψ
          subst hcv
          refine blockMemberHeadEtaTT (ciH := .ctorInfo cvAC nP nF)
            m₁ hfreshC
            (show reservedBasisNames.contains cvAC.name = false from by
              rw [hnameC]; exact hnresC)
            (show cvAC.name.isProjFnShape = false from by
              rw [hnameC]; exact hshapeC)
            (Or.inr (Or.inl ⟨_, _, _, rfl⟩))
            (show (block.map (·.name)).contains cvAC.name = true from by
              rw [hnameC]; exact hbnC)
            ?_ ?_ hI₁c T' cvT' capsT' hfT' hcape' hres' hfam'
            (by
              rw [show (ConstantInfo.ctorInfo cvAC nP nF).name =
                cvAC.name from rfl, hnameC]
              exact hpart')
          · -- outside formers stay closed at the intermediate
            -- environment
            intro T2 cvT2 capsT2 hf2 he2 hr2 hTb2
            have hTne : T2 ≠ (ConstantInfo.indInfo cvAI
                (indBlockCaps mode env cvT cvC nP nF)).name := by
              intro hcontra
              rw [hcontra] at hTb2
              rw [show ((ConstantInfo.indInfo cvAI (indBlockCaps mode env cvT
                cvC nP nF)).name : Name) = cvAI.name from rfl, hnameI,
                hbnT] at hTb2
              exact nomatch hTb2
            rw [Env.find?_cons, if_neg (fun hh => hTne hh.symm)] at hf2
            obtain ⟨cvC0, hfC0⟩ := hE1 T2 cvT2 capsT2 hf2 he2 hr2
            refine ⟨cvC0, ?_⟩
            rw [Env.find?_cons_of_isSome hfreshI (by rw [hfC0]; rfl)]
            exact hfC0
          · -- the block-former facts at the extension
            intro T2 cvT2 capsT2 hfT2 hTb2 hcape2
            by_cases hTh : (ConstantInfo.ctorInfo cvAC nP nF).name = T2
            · exfalso
              rw [Env.find?_cons, if_pos hTh] at hfT2
              exact nomatch (Option.some.inj hfT2)
            · rw [Env.find?_cons, if_neg hTh] at hfT2
              by_cases hTI : (ConstantInfo.indInfo cvAI
                  (indBlockCaps mode env cvT cvC nP nF)).name = T2
              · rw [Env.find?_cons, if_pos hTI] at hfT2
                obtain heq2 := Option.some.inj hfT2
                injection heq2 with e1 e2
                subst e1
                subst e2
                rw [← hTI]
                refine ⟨?_, ?_, ?_, ?_⟩
                · show EtaPins mode (⟨.indInfo cvAI (indBlockCaps mode env cvT cvC
                    nP nF) :: env.consts⟩ : Env) cvAI.name
                    cvAI.levelParams (indBlockCaps mode env cvT cvC nP nF)
                  refine EtaPins.step ?_ hfreshI
                  rw [hnameI, hlpsAI]
                  exact hpinsT0
                · show (block.map (·.name)).contains cvC.name = true
                  exact hbnC
                · exact Expr.constsResolve_mono htresI
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
                    have h2 : (((⟨ConstantInfo.ctorInfo cvAC nP nF ::
                        (⟨ConstantInfo.indInfo cvAI (indBlockCaps mode env
                          cvT cvC nP nF) :: env.consts⟩ :
                          Env).consts⟩ : Env)).find?
                        (projFnName cvT.name j)).isSome = true := by
                      rw [Env.find?_cons_of_isSome hfreshC
                        (by rw [hf₀]; rfl), hf₀]
                      rfl
                    rw [hPfree₂ j hj] at h2
                    exact nomatch h2
              · rw [Env.find?_cons, if_neg hTI] at hfT2
                exfalso
                rw [hbfresh T2 hTb2] at hfT2
                exact nomatch hfT2)
        (by
          -- the residual head obligation: the pin, or closure
          intro T' cvT' capsT' cvC' hfT' hcape' hTres' hCres' hfC' hor
          have hCheadT : (ConstantInfo.ctorInfo cvC nP nF).name
              = cvC.name := rfl
          by_cases hTI : T' = cvAI.name
          · -- the block former's family: the checker's #136 pin
            subst hTI
            rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.ctorInfo
              cvAC nP nF).name = cvAI.name from fun hh =>
                hCneT ((hnameC.symm.trans hh).trans hnameI))] at hfT'
            rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo cvAI
              (indBlockCaps mode env cvT cvC nP nF)).name = cvAI.name
              from rfl)] at hfT'
            obtain heq2 := Option.some.inj hfT'
            injection heq2 with e1 e2
            subst e1
            subst e2
            rw [show (indBlockCaps mode env cvT cvC nP nF).etaCtor = cvC.name
              from rfl] at hfC'
            rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo cvAC
              nP nF).name = cvC.name from hnameC)] at hfC'
            obtain heq3 := Option.some.inj hfC'
            injection heq3 with f1 f2 f3
            subst f1
            have hpin := hPinAt hcape' cvAC
              (checkIndRecs_find_preserved hrecs hbnrec _ _ (by
                  rw [Env.find?_cons, if_pos (show
                    (ConstantInfo.ctorInfo cvAC nP nF).name = cvC.name
                    from hnameC)])
                  (fun _ _ _ _ hcon => nomatch hcon))
            show CtorResidualPin cvAI.name cvAI.levelParams cvAC
              (indBlockCaps mode env cvT cvC nP nF).etaParams
              (indBlockCaps mode env cvT cvC nP nF).etaFields
            rw [hnameI, hlpsAI]
            exact hpin
          · -- an older family: closure refutes the collision
            exfalso
            rcases hor with rfl | hC
            · rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo
                cvAC nP nF).name = (ConstantInfo.ctorInfo cvC
                nP nF).name from hnameC)] at hfT'
              exact nomatch (Option.some.inj hfT')
            · by_cases hTC : (ConstantInfo.ctorInfo cvAC nP nF).name = T'
              · rw [Env.find?_cons, if_pos hTC] at hfT'
                exact nomatch (Option.some.inj hfT')
              rw [Env.find?_cons, if_neg hTC] at hfT'
              rw [Env.find?_cons, if_neg (fun hh => hTI hh.symm)] at hfT'
              obtain ⟨cvC0, hfC0⟩ := hE1 T' cvT' capsT' hfT' hcape'
                hTres'
              have hsC : (env.find? capsT'.etaCtor).isSome = true := by
                rw [hfC0]
                rfl
              rw [hC, hCheadT, hbfresh cvC.name hbnC] at hsC
              exact nomatch hsC)
      -- assemble the tail
      refine hrest m₂ hI₂ (hnameI ▸ hnresI)
        ⟨cvAI, ?_, hlpsAI, ?_⟩ ⟨cvAC, ?_⟩
      · rw [Env.find?_cons_of_isSome hfreshC
          (by rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo
            cvAI (indBlockCaps mode env cvT cvC nP nF)).name = cvT.name
            from hnameI)]; rfl)]
        rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo cvAI
          (indBlockCaps mode env cvT cvC nP nF)).name = cvT.name
          from hnameI)]
      · rw [hlpsAI]
        refine EtaPins.step ?_ hfreshC
        refine EtaPins.step ?_ hfreshI
        exact hpinsT0
      · rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo cvAC
          nP nF).name = cvC.name from hnameC)]
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
      obtain rfl : env₂ = envf := by
        have h9 : envf = env₂ := by simpa using hfold'
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
      have htresIm : cvAI.type.constsResolve
          (⟨.ctorInfo cvAC nP nF :: env.consts⟩ : Env) = true := by
        rw [show cvAI.type = tyAI from by rw [hcvAI]]
        exact hresI
      have henv₂ : env₂ = ⟨.indInfo cvAI
          (indBlockCaps mode env cvT cvC nP nF) ::
          (⟨.ctorInfo cvAC nP nF :: env.consts⟩ : Env).consts⟩ := by
        rcases hkindI with ⟨-, he⟩ | ⟨cv', nP', nF', heqTT, -⟩
        · exact he
        · exact nomatch heqTT
      subst henv₂
      have hfreshC : env.find? cvAC.name = none := by
        rw [hnameC]
        exact hfindC
      have hfreshCb : env.find? cvC.name = none := by
        rw [← hnameC]
        exact hfreshC
      have hfreshIm : (⟨.ctorInfo cvAC nP nF :: env.consts⟩ :
          Env).find? cvAI.name = none := by
        rw [hnameI]
        exact hfindI
      have hTneC : cvT.name ≠ cvC.name := by
        intro he
        have h0 : (⟨.ctorInfo cvAC nP nF :: env.consts⟩ :
            Env).find? cvAI.name = none := hfreshIm
        rw [hnameI, he] at h0
        rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo cvAC
          nP nF).name = cvC.name from hnameC)] at h0
        exact nomatch h0
      have hPfree₀ : ∀ j, j < nF →
          env.find? (projFnName cvT.name j) = none := by
        intro j hj
        cases hf₀ : env.find? (projFnName cvT.name j) with
        | none => rfl
        | some ci₂ =>
          exfalso
          have h2 := checkIndFold_mono _ env _ hfold
            (projFnName cvT.name j) (by rw [hf₀]; rfl)
          rw [hPfree₂ j hj] at h2
          exact nomatch h2
      -- step 1: the constructor (nothing eta-capable is stored yet)
      obtain ⟨m₁, hI₁⟩ := checkIndMemberTT hs1
        (fun cv caps₂ heq => nomatch heq)
        (show (block.map (·.name)).contains
          (ConstantInfo.ctorInfo cvC nP nF).name = true from hbnC)
        m hI₀
        (by
          intro T' cvT' capsT' hfT' hcape' hres' hfam' hpart' cval₁
            hagr halias hI₁c
          exfalso
          rcases hpart' with rfl | hC | ⟨j, hj, hP⟩
          · rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo
              cvAC nP nF).name = (ConstantInfo.ctorInfo cvC
              nP nF).name from hnameC)] at hfT'
            exact nomatch (Option.some.inj hfT')
          · obtain ⟨-, ⟨cvC0, hfC0⟩, -⟩ := hfam'
            rw [hC, Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo
              cvAC nP nF).name = (ConstantInfo.ctorInfo cvC
              nP nF).name from hnameC)] at hfC0
            obtain heq0 := Option.some.inj hfC0
            -- the head *is* a constructor: T' must be older, and its
            -- family closed
            by_cases hTh : (ConstantInfo.ctorInfo cvAC nP nF).name = T'
            · rw [Env.find?_cons, if_pos hTh] at hfT'
              exact nomatch (Option.some.inj hfT')
            · rw [Env.find?_cons, if_neg hTh] at hfT'
              obtain ⟨cvC1, hfC1⟩ := hE1 T' cvT' capsT' hfT' hcape'
                hres'
              have hsC : (env.find? capsT'.etaCtor).isSome = true := by
                rw [hfC1]
                rfl
              rw [hC] at hsC
              rw [show (ConstantInfo.ctorInfo cvC nP nF).name = cvC.name
                from rfl, hfreshCb] at hsC
              exact nomatch hsC
          · have hP' : projFnName T' j =
                (ConstantInfo.ctorInfo cvC nP nF).name := hP
            have hshapeC' : cvC.name.isProjFnShape = false := hshapeC
            rw [show ((ConstantInfo.ctorInfo cvC nP nF).name : Name) =
              cvC.name from rfl] at hP'
            rw [← hP'] at hshapeC'
            simp [projFnName, Name.isProjFnShape] at hshapeC')
        (by
          intro T' cvT' capsT' cvC' hfT' hcape' hTres' hCres' hfC' hor
          exfalso
          rcases hor with rfl | hC
          · rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo
              cvAC nP nF).name = (ConstantInfo.ctorInfo cvC
              nP nF).name from hnameC)] at hfT'
            exact nomatch (Option.some.inj hfT')
          · by_cases hTh : (ConstantInfo.ctorInfo cvAC nP nF).name = T'
            · rw [Env.find?_cons, if_pos hTh] at hfT'
              exact nomatch (Option.some.inj hfT')
            · rw [Env.find?_cons, if_neg hTh] at hfT'
              obtain ⟨cvC0, hfC0⟩ := hE1 T' cvT' capsT' hfT' hcape'
                hTres'
              have hsC : (env.find? capsT'.etaCtor).isSome = true := by
                rw [hfC0]
                rfl
              rw [hC] at hsC
              rw [show ((ConstantInfo.ctorInfo cvC nP nF).name : Name)
                = cvC.name from rfl, hfreshCb] at hsC
              exact nomatch hsC)
      -- step 2: the former (a fieldless family may complete here)
      obtain ⟨m₂, hI₂⟩ := checkIndMemberTT hs2
        (fun cv caps₂ heq => by
          injection heq with e1 e2
          subst e1
          exact EtaPins.step (c₁ := .ctorInfo cvAC nP nF) hpinsT0
            (show env.find? (ConstantInfo.ctorInfo cvAC nP nF).name
              = none from hfreshC))
        (show (block.map (·.name)).contains
          (ConstantInfo.indInfo cvT capsT).name = true from hbnT)
        m₁ hI₁
        (by
          intro T' cvT' capsT' hfT' hcape' hres' hfam' hpart' cval₁
            hagr halias hI₁c
          have hcv : cval₁ =
              cvalAlias m₁.cval cvAI.name (cvAI.name.str "_model") := by
            funext c ψ
            by_cases hc : c = cvAI.name
            · subst hc
              rw [cvalAlias_self, hnameI]
              exact congrFun halias ψ
            · rw [cvalAlias_ne hc]
              exact congrFun (hagr c (fun hh => hc (hh.trans
                (show (ConstantInfo.indInfo cvT capsT).name =
                  cvAI.name from hnameI.symm)))) ψ
          subst hcv
          refine blockMemberHeadEtaTT (ciH := .indInfo cvAI
            (indBlockCaps mode env cvT cvC nP nF)) m₁ hfreshIm
            (show reservedBasisNames.contains cvAI.name = false from by
              rw [hnameI]; exact hnresI)
            (show cvAI.name.isProjFnShape = false from by
              rw [hnameI]; exact hshapeI)
            (Or.inl ⟨_, _, rfl⟩)
            (show (block.map (·.name)).contains cvAI.name = true from by
              rw [hnameI]; exact hbnT)
            ?_ ?_ hI₁c T' cvT' capsT' hfT' hcape' hres' hfam'
            (by
              rw [show (ConstantInfo.indInfo cvAI (indBlockCaps mode env cvT
                cvC nP nF)).name = cvAI.name from rfl, hnameI]
              exact hpart')
          · -- outside formers stay closed at the intermediate
            -- environment
            intro T2 cvT2 capsT2 hf2 he2 hr2 hTb2
            have hTne : T2 ≠ (ConstantInfo.ctorInfo cvAC nP nF).name := by
              intro hcontra
              rw [hcontra] at hTb2
              rw [show ((ConstantInfo.ctorInfo cvAC nP nF).name : Name) =
                cvAC.name from rfl, hnameC, hbnC] at hTb2
              exact nomatch hTb2
            rw [Env.find?_cons, if_neg (fun hh => hTne hh.symm)] at hf2
            obtain ⟨cvC0, hfC0⟩ := hE1 T2 cvT2 capsT2 hf2 he2 hr2
            refine ⟨cvC0, ?_⟩
            rw [Env.find?_cons_of_isSome hfreshC (by rw [hfC0]; rfl)]
            exact hfC0
          · -- the block-former facts at the extension
            intro T2 cvT2 capsT2 hfT2 hTb2 hcape2
            by_cases hTh : (ConstantInfo.indInfo cvAI
                (indBlockCaps mode env cvT cvC nP nF)).name = T2
            · rw [Env.find?_cons, if_pos hTh] at hfT2
              obtain heq2 := Option.some.inj hfT2
              injection heq2 with e1 e2
              subst e1
              subst e2
              rw [← hTh]
              refine ⟨?_, ?_, ?_, ?_⟩
              · show EtaPins mode (⟨.ctorInfo cvAC nP nF :: env.consts⟩ :
                  Env) cvAI.name cvAI.levelParams
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
                show (⟨.ctorInfo cvAC nP nF :: env.consts⟩ :
                  Env).find? (projFnName cvAI.name j) = none
                rw [hnameI]
                cases hf₀ : (⟨.ctorInfo cvAC nP nF :: env.consts⟩ :
                    Env).find? (projFnName cvT.name j) with
                | none => rfl
                | some ci₂ =>
                  exfalso
                  have h2 : (((⟨ConstantInfo.indInfo cvAI (indBlockCaps mode
                      env cvT cvC nP nF) ::
                      (⟨ConstantInfo.ctorInfo cvAC nP nF ::
                        env.consts⟩ : Env).consts⟩ : Env)).find?
                      (projFnName cvT.name j)).isSome = true := by
                    rw [Env.find?_cons_of_isSome hfreshIm
                      (by rw [hf₀]; rfl), hf₀]
                    rfl
                  rw [hPfree₂ j hj] at h2
                  exact nomatch h2
            · rw [Env.find?_cons, if_neg hTh] at hfT2
              by_cases hTC : (ConstantInfo.ctorInfo cvAC nP nF).name
                  = T2
              · exfalso
                rw [Env.find?_cons, if_pos hTC] at hfT2
                exact nomatch (Option.some.inj hfT2)
              · rw [Env.find?_cons, if_neg hTC] at hfT2
                exfalso
                rw [hbfresh T2 hTb2] at hfT2
                exact nomatch hfT2)
        (by
          intro T' cvT' capsT' cvC' hfT' hcape' hTres' hCres' hfC' hor
          by_cases hTI : T' = cvAI.name
          · -- the block former's family: the checker's #136 pin
            subst hTI
            rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo cvAI
              (indBlockCaps mode env cvT cvC nP nF)).name = cvAI.name
              from rfl)] at hfT'
            obtain heq2 := Option.some.inj hfT'
            injection heq2 with e1 e2
            subst e1
            subst e2
            rw [show (indBlockCaps mode env cvT cvC nP nF).etaCtor = cvC.name
              from rfl] at hfC'
            rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.indInfo cvAI
              (indBlockCaps mode env cvT cvC nP nF)).name = cvC.name from
              fun hh => hTneC ((hnameI.symm.trans hh)))] at hfC'
            rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo cvAC
              nP nF).name = cvC.name from hnameC)] at hfC'
            obtain heq3 := Option.some.inj hfC'
            injection heq3 with f1 f2 f3
            subst f1
            have hpin := hPinAt hcape' cvAC
              (checkIndRecs_find_preserved hrecs hbnrec _ _ (by
                  rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.indInfo
                    cvAI (indBlockCaps mode env cvT cvC nP nF)).name =
                    cvC.name from fun hh =>
                      hTneC (hnameI.symm.trans hh))]
                  rw [Env.find?_cons, if_pos (show
                    (ConstantInfo.ctorInfo cvAC nP nF).name = cvC.name
                    from hnameC)])
                  (fun _ _ _ _ hcon => nomatch hcon))
            show CtorResidualPin cvAI.name cvAI.levelParams cvAC
              (indBlockCaps mode env cvT cvC nP nF).etaParams
              (indBlockCaps mode env cvT cvC nP nF).etaFields
            rw [hnameI, hlpsAI]
            exact hpin
          · exfalso
            rcases hor with rfl | hC
            · rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo
                cvAI (indBlockCaps mode env cvT cvC nP nF)).name =
                (ConstantInfo.indInfo cvT capsT).name from hnameI)]
                at hfT'
              exact hTI (hnameI ▸ rfl)
            · by_cases hTC : (ConstantInfo.indInfo cvAI (indBlockCaps mode
                  env cvT cvC nP nF)).name = T'
              · exact hTI hTC.symm
              rw [Env.find?_cons, if_neg hTC] at hfT'
              by_cases hTC2 : (ConstantInfo.ctorInfo cvAC nP nF).name
                  = T'
              · rw [Env.find?_cons, if_pos hTC2] at hfT'
                exact nomatch (Option.some.inj hfT')
              rw [Env.find?_cons, if_neg hTC2] at hfT'
              obtain ⟨cvC0, hfC0⟩ := hE1 T' cvT' capsT' hfT' hcape'
                hTres'
              have hsC : (env.find? capsT'.etaCtor).isSome = true := by
                rw [hfC0]
                rfl
              rw [hC] at hsC
              rw [show ((ConstantInfo.indInfo cvT capsT).name : Name)
                = cvT.name from rfl] at hsC
              rw [show env.find? cvT.name = none from by
                rw [← hnameI]
                cases hf0 : env.find? cvAI.name with
                | none => rfl
                | some ci0 =>
                  exfalso
                  have h1 : ((⟨ConstantInfo.ctorInfo cvAC nP nF ::
                      env.consts⟩ : Env).find? cvAI.name).isSome
                      = true := by
                    rw [Env.find?_cons_of_isSome hfreshC
                      (by rw [hf0]; rfl), hf0]
                    rfl
                  rw [hfreshIm] at h1
                  exact nomatch h1] at hsC
              exact nomatch hsC)
      -- assemble the tail
      refine hrest m₂ hI₂ (hnameI ▸ hnresI)
        ⟨cvAI, ?_, hlpsAI, ?_⟩ ⟨cvAC, ?_⟩
      · rw [Env.find?_cons, if_pos (show (ConstantInfo.indInfo cvAI
          (indBlockCaps mode env cvT cvC nP nF)).name = cvT.name
          from hnameI)]
      · rw [hlpsAI]
        refine EtaPins.step ?_ hfreshIm
        refine EtaPins.step (c₁ := .ctorInfo cvAC nP nF) ?_
          (show env.find? (ConstantInfo.ctorInfo cvAC nP nF).name
            = none from hfreshC)
        exact hpinsT0
      · rw [Env.find?_cons_of_isSome hfreshIm
          (by rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo
            cvAC nP nF).name = cvC.name from hnameC)]; rfl)]
        rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo cvAC
          nP nF).name = cvC.name from hnameC)]
  · -- no single-constructor structure: member fold, then the recursors
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨env₂, hfold, hrecs⟩ := Except.bind_ok h
    have hbnrec : ∀ ci ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => true | _ => false),
        (block.map (·.name)).contains ci.name = true :=
      fun ci hci => hbn ci (List.mem_filter.mp hci).1
    have hI₀ : BlockInstalledTT (block.map (·.name)) env m.cval := by
      intro n hn ci₂ hf₂
      have hmem : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with hci₀ | hci₀
      · rw [checkIndMember_fold_names _ env env₂ hfold ci₀ hci₀] at hf₂
        exact nomatch hf₂
      · have h1 := checkIndRecs_names hrecs ci₀ hci₀
        have h2 : (env₂.find? ci₀.name).isSome = true :=
          checkIndFold_mono _ env env₂ hfold ci₀.name (by rw [hf₂]; rfl)
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
      · rw [checkIndMember_fold_names _ env env₂ hfold ci₀ hci₀] at hf
        exact nomatch hf
      · have h1 := checkIndRecs_names hrecs ci₀ hci₀
        have h2 : (env₂.find? ci₀.name).isSome = true :=
          checkIndFold_mono _ env env₂ hfold ci₀.name (by rw [hf]; rfl)
        rw [h1] at h2
        exact nomatch h2
    obtain ⟨m₁, hI₁, hE1O₁, hBcaps₁⟩ := checkIndFoldTT (by decide)
      (by decide) _ env env₂
      (fun ci hci => hbn ci (List.mem_filter.mp hci).1)
      (fun _ _ _ => ⟨fun hcape => absurd hcape (by decide),
        fun hcapu => absurd hcapu (by decide)⟩)
      hfold m hI₀ hE1O₀ hBcaps₀
    obtain ⟨m₂, -⟩ := checkIndRecsTT hrecs
      (fun ci hci => hbn ci (List.mem_filter.mp hci).1)
      (fun n hn => by
        have hmem : n ∈ block.map (·.name) := by simpa using hn
        obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
        rw [hsplit] at hci₀
        rcases List.mem_append.mp hci₀ with hci₀ | hci₀
        · exact Or.inl (checkIndFold_stored _ env env₂ hfold ci₀ hci₀)
        · exact Or.inr ⟨ci₀, hci₀, rfl⟩)
      (fun n hn => by
        have hmem : n ∈ block.map (·.name) := by simpa using hn
        obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
        rw [hsplit] at hci₀
        rcases List.mem_append.mp hci₀ with hci₀ | hci₀
        · exact checkIndFold_modelfree _ env env₂ hfold ci₀ hci₀
        · exact checkIndRecs_modelfree hrecs ci₀ hci₀)
      m₁ hI₁
    exact ⟨m₂⟩

end Setlec.TTVerify
