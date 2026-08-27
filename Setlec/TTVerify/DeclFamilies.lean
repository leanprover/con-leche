import Setlec.TTVerify.DeclIndDecl

/-!
# `FamiliesStepTT`: the closure of stored eta families, preserved

The purely syntactic half of the model's `checkDecl_sound` conclusion,
separated (see `Setlec/TTVerify/Consistency.lean`): every kind of
checked declaration keeps `EtaFamiliesClosed` — value kinds and
basis blocks by `EtaFamiliesClosed.cons_nonind` (their heads are
never non-reserved eta-capable formers), the modeled-inductive block
by its own structure (the single-constructor arm stores the capability
constructor in the same block).
-/

set_option linter.unusedVariables false

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

variable {F : Nat}

/-! ## Shape inversions of the value installs -/

private theorem checkDefnVal_shape {env env₂ : Env} {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint}
    (h : checkDefnVal (fueledOps mode F) env cv value hint = .ok env₂) :
    ∃ valueA, env₂ = ⟨.defnInfo cv valueA hint :: env.consts⟩ := by
  simp only [checkDefnVal, fueledOps_annotate, fueledOps_inferType,
    fueledOps_isDefEq, Bind.bind, Except.bind] at h
  by_cases hlb : value.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hfv : value.hasFvar = true
  case pos => simp [hfv] at h
  simp only [hfv] at h
  try dsimp only at h
  cases hann : annotateCore mode env F 0 value with
  | error e => rw [hann] at h; exact nomatch h
  | ok valueA =>
  rw [hann] at h
  try dsimp only at h
  by_cases hlp : valueA.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hlp] at h
  simp only [hlp] at h
  by_cases hres : valueA.constsResolve env = true
  case neg => simp [hres] at h
  simp only [hres] at h
  cases hvt : inferTypeCore mode env F 0 valueA with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore mode env F 0 vtype cv.type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, reduceIte, pure, Except.pure,
    Except.ok.injEq] at h
  exact ⟨valueA, h.symm⟩

private theorem checkThmVal_shape {env env₂ : Env} {cv : ConstantVal}
    {value : Expr}
    (h : checkThmVal (fueledOps mode F) env cv value = .ok env₂) :
    ∃ valueA, env₂ = ⟨.thmInfo cv valueA :: env.consts⟩ := by
  simp only [checkThmVal, fueledOps_annotate, fueledOps_inferType,
    fueledOps_isDefEq, fueledOps_ensureSort, Bind.bind,
    Except.bind] at h
  cases hst : inferTypeCore mode env F 0 cv.type with
  | error e => rw [hst] at h; exact nomatch h
  | ok stype =>
  rw [hst] at h
  try dsimp only at h
  cases hsort : ensureSortCore mode env F 0 stype with
  | error e => rw [hsort] at h; exact nomatch h
  | ok u =>
  rw [hsort] at h
  try dsimp only at h
  cases hpz : Level.isEquiv u Level.zero with
  | none => rw [hpz] at h; simp [liftFueled] at h
  | some bz =>
  rw [hpz] at h
  cases bz with
  | false => simp [liftFueled, pure, Except.pure] at h
  | true =>
  simp only [liftFueled, pure, Except.pure] at h
  try dsimp only at h
  by_cases hlb : value.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hfv : value.hasFvar = true
  case pos => simp [hfv] at h
  simp only [hfv] at h
  try dsimp only at h
  cases hann : annotateCore mode env F 0 value with
  | error e => rw [hann] at h; exact nomatch h
  | ok valueA =>
  rw [hann] at h
  try dsimp only at h
  by_cases hlp : valueA.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hlp] at h
  simp only [hlp] at h
  by_cases hres : valueA.constsResolve env = true
  case neg => simp [hres] at h
  simp only [hres] at h
  cases hvt : inferTypeCore mode env F 0 valueA with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore mode env F 0 vtype cv.type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, reduceIte, Except.ok.injEq] at h
  exact ⟨valueA, h.symm⟩

private theorem checkOpaqueVal_shape {env env₂ : Env} {cv : ConstantVal}
    {value : Expr}
    (h : checkOpaqueVal (fueledOps mode F) env cv value = .ok env₂) :
    env₂ = ⟨.axiomInfo cv :: env.consts⟩ := by
  simp only [checkOpaqueVal, fueledOps_annotate, fueledOps_inferType,
    fueledOps_isDefEq, Bind.bind, Except.bind] at h
  by_cases hlb : value.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hfv : value.hasFvar = true
  case pos => simp [hfv] at h
  simp only [hfv] at h
  try dsimp only at h
  cases hann : annotateCore mode env F 0 value with
  | error e => rw [hann] at h; exact nomatch h
  | ok valueA =>
  rw [hann] at h
  try dsimp only at h
  by_cases hlp : valueA.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hlp] at h
  simp only [hlp] at h
  by_cases hres : valueA.constsResolve env = true
  case neg => simp [hres] at h
  simp only [hres] at h
  cases hvt : inferTypeCore mode env F 0 valueA with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore mode env F 0 vtype cv.type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, reduceIte, pure, Except.pure,
    Except.ok.injEq] at h
  exact h.symm

/-! ## The basis blocks -/

private theorem installBasisDecl_shape {env env₂ : Env}
    {ci : ConstantInfo}
    (h : (installBasisDecl env ci : CheckM Env) = .ok env₂) :
    env.find? ci.name = none ∧ env₂ = ⟨ci :: env.consts⟩ := by
  simp only [installBasisDecl, Bind.bind, Except.bind] at h
  by_cases hn : (env.find? ci.name).isNone = true
  case neg => simp [hn] at h
  simp only [hn] at h
  rw [if_pos trivial] at h
  injection h with h2
  exact ⟨Option.isNone_iff_eq_none.mp hn,
    by first | exact h2 | exact h2.symm⟩

/-- A basis member is never a non-reserved eta-capable former.  The
pinned formers are all reserved names; the only non-reserved basis
members (the psigma pair projection helpers) are recursors. -/
private def basisHeadOk (ci : ConstantInfo) : Bool :=
  match ci with
  | .indInfo _ caps => !caps.eta || reservedBasisNames.contains ci.name
  | _ => true

private theorem basisFold_closed {ds : List ConstantInfo}
    (hres : ∀ ci ∈ ds, basisHeadOk ci = true) :
    ∀ {env env₂ : Env},
    (ds.foldlM installBasisDecl env : CheckM Env) = .ok env₂ →
    EtaFamiliesClosed env → EtaFamiliesClosed env₂ := by
  induction ds with
  | nil =>
    intro env env₂ h hE1
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hE1
  | cons ci ds ih =>
    intro env env₂ h hE1
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : (installBasisDecl env ci : CheckM Env) with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ =>
      rw [hstep] at h
      obtain ⟨hfresh, rfl⟩ := installBasisDecl_shape hstep
      refine ih (fun c hc => hres c (List.mem_cons_of_mem _ hc)) h
        (EtaFamiliesClosed.cons_nonind hE1 hfresh ?_)
      intro cv caps heq hcape
      have hok := hres ci List.mem_cons_self
      rw [heq] at hok ⊢
      simp only [basisHeadOk, hcape, Bool.not_true, Bool.false_or] at hok
      exact hok

/-! ## The modeled-inductive block -/

set_option maxHeartbeats 6400000 in
private theorem indFamilies {env env₁ : Env} {block : List ConstantInfo}
    (h : checkIndDecl mode (fueledOps mode F) env block = .ok env₁)
    (hE1 : EtaFamiliesClosed env) : EtaFamiliesClosed env₁ := by
  rw [checkIndDecl] at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  case isFalse => exact nomatch h
  rename_i hsplit
  simp only [pure, Except.pure] at h
  try dsimp only at h
  have hbn : ∀ ci ∈ block, (block.map (·.name)).contains ci.name = true :=
    fun ci hci => by
      have : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
      simpa using this
  have hbnrec : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => true | _ => false),
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbn ci (List.mem_filter.mp hci).1
  have hbnnon : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => false | _ => true),
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbn ci (List.mem_filter.mp hci).1
  split at h
  · -- the single-constructor arm
    rename_i cvT capsT cvC nP nF heqI heqC
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨env₂, hfold, h⟩ := Except.bind_ok h
    obtain ⟨env₃, hrecs, h⟩ := Except.bind_ok h
    by_cases hctorRes : ctorResidualOk mode env₃ cvT.name cvC.name
        cvT.levelParams nP nF (indBlockCaps mode env cvT cvC nP nF).eta = true
    case neg => rw [if_neg hctorRes] at h; exact nomatch h
    rw [if_pos hctorRes] at h
    try simp only [pure, Except.pure] at h
    try dsimp only at h
    try simp only [Bind.bind, Except.bind] at h
    by_cases hfreshP : ((List.range nF).all
        (fun j => (env₃.find? (projFnName cvT.name j)).isNone)) = true
    case neg => rw [if_neg hfreshP] at h; exact nomatch h
    rw [if_pos hfreshP] at h
    try simp only [pure, Except.pure] at h
    try dsimp only at h
    try simp only [Bind.bind, Except.bind] at h
    obtain ⟨env₄, hart, htpl⟩ := Except.bind_ok h
    -- the member fold stores at most the former and the constructor,
    -- and the constructor is stored whenever the former is
    have hcorr₂ : ∀ (n : Name) (cv2 : ConstantVal) (caps2 : IndCaps),
        env₂.find? n = some (.indInfo cv2 caps2) →
        env.find? n = some (.indInfo cv2 caps2) ∨
        (n = cvT.name ∧ caps2 = indBlockCaps mode env cvT cvC nP nF ∧
          ∃ cvCA, env₂.find? cvC.name = some (.ctorInfo cvCA nP nF)) := by
      -- unroll the two members
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
      intro n cv2 caps2 hf₂
      rcases horder with hord | hord <;> rw [hord] at hfold' <;>
        simp only [List.foldlM_cons, List.foldlM_nil, Bind.bind,
          Except.bind, pure, Except.pure] at hfold'
      · -- [former, constructor]
        revert hfold'
        cases hs1 : checkIndMember (fueledOps mode F) (block.map (·.name))
            (indBlockCaps mode env cvT cvC nP nF) env
            (ConstantInfo.indInfo cvT capsT) with
        | error e => intro hfold'; exact nomatch hfold'
        | ok envm => ?_
        intro hfold'
        try dsimp only at hfold'
        revert hfold'
        cases hs2 : checkIndMember (fueledOps mode F) (block.map (·.name))
            (indBlockCaps mode env cvT cvC nP nF) envm
            (ConstantInfo.ctorInfo cvC nP nF) with
        | error e => intro hfold'; exact nomatch hfold'
        | ok envf => ?_
        intro hfold'
        obtain rfl : env₂ = envf := by
          have h9 : envf = env₂ := by simpa using hfold'
          exact h9.symm
        obtain ⟨cvAI, cvmI, mvalI, hmcvmI, hccvI, -, -, -, -, hkindI⟩ :=
          checkIndMember_inv hs1
        obtain ⟨-, -, -, -, -, -, tyAI, sI, uI, -, -, -, -, -, hcvAI⟩ :=
          checkConstantVal_inv hccvI
        have hnameI : cvAI.name = cvT.name := by rw [hcvAI]; rfl
        have henvm : envm = ⟨.indInfo cvAI
            (indBlockCaps mode env cvT cvC nP nF) :: env.consts⟩ := by
          rcases hkindI with ⟨-, he⟩ | ⟨cv', nP', nF', heqTT, -⟩
          · exact he
          · exact nomatch heqTT
        subst henvm
        obtain ⟨cvAC, cvmC2, mvalC2, hmcvmC2, hccvC, -, -, -, -,
          hkindC⟩ := checkIndMember_inv hs2
        obtain ⟨-, -, -, -, -, -, tyAC, sC, uC, -, -, -, -, -,
          hcvAC⟩ := checkConstantVal_inv hccvC
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
        rw [Env.find?_cons] at hf₂
        split at hf₂
        · exact nomatch (Option.some.inj hf₂)
        · rw [Env.find?_cons] at hf₂
          split at hf₂
          · next hh =>
            obtain heq2 := Option.some.inj hf₂
            injection heq2 with e1 e2
            refine Or.inr ⟨?_, e2.symm, cvAC, ?_⟩
            · rw [← hh]
              exact hnameI.symm ▸ rfl
            · rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo
                cvAC nP nF).name = cvC.name from hnameC)]
          · exact Or.inl hf₂
      · -- [constructor, former]
        revert hfold'
        cases hs1 : checkIndMember (fueledOps mode F) (block.map (·.name))
            (indBlockCaps mode env cvT cvC nP nF) env
            (ConstantInfo.ctorInfo cvC nP nF) with
        | error e => intro hfold'; exact nomatch hfold'
        | ok envm => ?_
        intro hfold'
        try dsimp only at hfold'
        revert hfold'
        cases hs2 : checkIndMember (fueledOps mode F) (block.map (·.name))
            (indBlockCaps mode env cvT cvC nP nF) envm
            (ConstantInfo.indInfo cvT capsT) with
        | error e => intro hfold'; exact nomatch hfold'
        | ok envf => ?_
        intro hfold'
        obtain rfl : env₂ = envf := by
          have h9 : envf = env₂ := by simpa using hfold'
          exact h9.symm
        obtain ⟨cvAC, cvmC2, mvalC2, hmcvmC2, hccvC, -, -, -, -,
          hkindC⟩ := checkIndMember_inv hs1
        obtain ⟨-, -, -, -, -, -, tyAC, sC, uC, -, -, -, -, -,
          hcvAC⟩ := checkConstantVal_inv hccvC
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
        obtain ⟨cvAI, cvmI, mvalI, hmcvmI, hccvI, -, -, -, -, hkindI⟩ :=
          checkIndMember_inv hs2
        obtain ⟨hfindI, -, -, -, -, -, tyAI, sI, uI, -, -, -, -, -,
          hcvAI⟩ := checkConstantVal_inv hccvI
        have hnameI : cvAI.name = cvT.name := by rw [hcvAI]; rfl
        have henv₂ : env₂ = ⟨.indInfo cvAI
            (indBlockCaps mode env cvT cvC nP nF) ::
            (⟨.ctorInfo cvAC nP nF :: env.consts⟩ : Env).consts⟩ := by
          rcases hkindI with ⟨-, he⟩ | ⟨cv', nP', nF', heqTT, -⟩
          · exact he
          · exact nomatch heqTT
        subst henv₂
        rw [Env.find?_cons] at hf₂
        split at hf₂
        · next hh =>
          obtain heq2 := Option.some.inj hf₂
          injection heq2 with e1 e2
          refine Or.inr ⟨?_, e2.symm, cvAC, ?_⟩
          · rw [← hh]
            exact hnameI.symm ▸ rfl
          · rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.indInfo cvAI
              (indBlockCaps mode env cvT cvC nP nF)).name = cvC.name from
              fun hh2 => by
                have h0 : cvAI.name = cvC.name := hh2
                rw [hnameI] at h0
                have hfindI2 : (⟨ConstantInfo.ctorInfo cvAC nP nF ::
                    env.consts⟩ : Env).find? cvT.name = none := hfindI
                rw [Env.find?_cons, if_pos (show
                  (ConstantInfo.ctorInfo cvAC nP nF).name = cvT.name
                  from by
                    show cvAC.name = cvT.name
                    rw [hnameC, h0])] at hfindI2
                exact nomatch hfindI2)]
            rw [Env.find?_cons, if_pos (show (ConstantInfo.ctorInfo
              cvAC nP nF).name = cvC.name from hnameC)]
        · rw [Env.find?_cons] at hf₂
          split at hf₂
          · exact nomatch (Option.some.inj hf₂)
          · exact Or.inl hf₂
    -- the closure at the final environment
    intro T' cvT' capsT' hfT₂ hcape' hres'
    obtain ⟨htplNew, htplMono⟩ :=
      installProjTemplates_find_new (List.range nF) env₄ env₁ htpl
    rcases htplNew T' _ hfT₂ with hf₄ | ⟨entry, heq⟩
    case inr => exact nomatch heq
    rcases checkProjFold_find_new (List.range nF) env₃ env₄ hart
      T' _ hf₄ with hf₃ | ⟨cv2, mI2, rP2, rules2, heq⟩
    case inr => exact nomatch heq
    rcases checkIndRecs_find_new hrecs hbnrec T' _ hf₃ with
      hf₂ | ⟨cv2, mI2, rP2, rules2, heq⟩
    case inr => exact nomatch heq
    rcases hcorr₂ T' cvT' capsT' hf₂ with hf₀ | ⟨rfl, rfl, cvCA, hCst⟩
    · obtain ⟨cvC0, hfC0⟩ := hE1 T' cvT' capsT' hf₀ hcape' hres'
      refine ⟨cvC0, ?_⟩
      refine installProjTemplates_find_preserved (List.range nF)
        env₄ env₁ htpl _ _ ?_
      refine checkProjFold_find_preserved (List.range nF) env₃ env₄
        hart _ _ ?_
      refine checkIndRecs_find_preserved hrecs hbnrec _ _ ?_
        (fun _ _ _ _ hcon => nomatch hcon)
      exact checkIndFold_find_preserved _ env env₂ hfold _ _ hfC0
    · refine ⟨cvCA, ?_⟩
      show env₁.find? cvC.name = some (.ctorInfo cvCA nP nF)
      refine installProjTemplates_find_preserved (List.range nF)
        env₄ env₁ htpl _ _ ?_
      refine checkProjFold_find_preserved (List.range nF) env₃ env₄
        hart _ _ ?_
      refine checkIndRecs_find_preserved hrecs hbnrec _ _ hCst
        (fun _ _ _ _ hcon => nomatch hcon)
  · -- the generic arm: nothing eta-capable is added
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨env₂, hfold, hrecs⟩ := Except.bind_ok h
    intro T cvT caps hfT hcape hresT
    rcases checkIndRecs_find_new hrecs hbnrec T _ hfT with hfT₁ | hk
    · rcases checkIndFold_find_new _ env env₂
        (fun ci hci => hbn ci (List.mem_filter.mp hci).1) hfold T _ hfT₁
        with hfT₀ | ⟨-, hknew⟩
      · obtain ⟨cvC0, hfC0⟩ := hE1 T cvT caps hfT₀ hcape hresT
        refine ⟨cvC0, ?_⟩
        exact checkIndRecs_find_preserved hrecs hbnrec _ _
          (checkIndFold_find_preserved _ env env₂ hfold _ _ hfC0)
          (fun _ _ _ _ hcon => nomatch hcon)
      · rcases hknew with ⟨cv, heq⟩ | ⟨cv, nP', nF', heq⟩
        · injection heq with e1 e2
          rw [e2] at hcape
          exact absurd hcape (by decide)
        · exact nomatch heq
    · obtain ⟨cv, mI, rP, rules, heq⟩ := hk
      exact nomatch heq

/-! ## The step -/

/-- No pinned basis block contains a non-reserved eta-capable
former. -/
private theorem basisDecls_headOk (kind : BasisKind) :
    ∀ ci ∈ kind.declsA, basisHeadOk ci = true := by
  cases kind <;> decide

set_option maxHeartbeats 3200000 in
/-- **`FamiliesStepTT`, discharged.** -/
theorem familiesStepTT : FamiliesStepTT F := by
  intro mode' env env₁ d h hdir hE1
  -- task #147: the certified configuration pins the running mode
  obtain rfl : mode' = .ttModel := hdir.mode_eq
  cases d with
  | defnDecl cv value hint =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal (fueledOps mode F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cvA =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', -, -, -, -, -, type, stype, u, -, -, -, -, -,
      rfl⟩ := checkConstantVal_invT hccv
    revert h
    cases hdv : checkDefnVal (fueledOps mode F) env
        { cv with type := type } value hint with
    | error e => intro h; exact nomatch h
    | ok env₂ => ?_
    intro h
    try dsimp only at h
    -- the nat-op / div-mod gate tree: every accepting leaf is
    -- `pure env₂`
    have henv : env₁ = env₂ := by
      by_cases hnop : natOpNames.contains cv.name = true
      case neg =>
        rw [if_neg hnop] at h
        by_cases hdm : natDivModNames.contains cv.name = true
        case neg =>
          rw [if_neg hdm] at h
          simp only [pure, Except.pure] at h
          exact (Except.ok.inj h).symm
        rw [if_pos hdm] at h
        revert h
        cases hpin : checkDivModPin (fueledOps mode F) env env₂ cv.name with
        | error err => intro h; exact nomatch h
        | ok u =>
          intro h
          simp only [pure, Except.pure] at h
          exact (Except.ok.inj h).symm
      rw [if_pos hnop] at h
      by_cases hgd : (natOpGuard env₂ cv.name &&
          (natOpDeps cv.name).all (natOpStoredOk env₂)) = true
      case neg =>
        rw [if_neg hgd] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      rw [if_pos hgd] at h
      revert h
      cases hfind2 : env₂.find? cv.name with
      | none =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      | some ci =>
      cases ci
      case defnInfo val value' hint' =>
        intro h
        try dsimp only at h
        revert h
        cases hcert : certifyNatEqs (fueledOps mode F) env
            ((natOpEquations 0 cv.name).map fun eq =>
              (Expr.substConst0 cv.name value' eq.1,
               Expr.substConst0 cv.name value' eq.2)) with
        | error err => intro h; exact nomatch h
        | ok okb =>
        cases okb with
        | false =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        | true =>
        intro h
        simp only [↓reduceIte] at h
        by_cases hdm : natDivModNames.contains cv.name = true
        case neg =>
          rw [if_neg hdm] at h
          simp only [pure, Except.pure] at h
          exact (Except.ok.inj h).symm
        rw [if_pos hdm] at h
        revert h
        cases hpin : checkDivModPin (fueledOps mode F) env env₂ cv.name with
        | error err => intro h; exact nomatch h
        | ok u =>
          intro h
          simp only [pure, Except.pure] at h
          exact (Except.ok.inj h).symm
      all_goals
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    subst henv
    obtain ⟨valueA, rfl⟩ := checkDefnVal_shape hdv
    exact EtaFamiliesClosed.cons_nonind hE1 hfind'
      (fun _ _ hx _ => ConstantInfo.noConfusion hx)
  | thmDecl cv value =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal (fueledOps mode F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cvA =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', -, -, -, -, -, type, stype, u, -, -, -, -, -,
      rfl⟩ := checkConstantVal_invT hccv
    obtain ⟨valueA, rfl⟩ := checkThmVal_shape h
    exact EtaFamiliesClosed.cons_nonind hE1 hfind'
      (fun _ _ hx _ => ConstantInfo.noConfusion hx)
  | opaqueDecl cv value =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal (fueledOps mode F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cvA =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', -, -, -, -, -, type, stype, u, -, -, -, -, -,
      rfl⟩ := checkConstantVal_invT hccv
    revert h
    cases hov : checkOpaqueVal (fueledOps mode F) env
        { cv with type := type } value with
    | error e => intro h; exact nomatch h
    | ok env₂ => ?_
    intro h
    try dsimp only at h
    -- the reduce-pin gate: both accepting leaves are `pure env₂`
    have henv : env₁ = env₂ := by
      by_cases hro : reduceOpNames.contains cv.name = true
      case neg =>
        rw [if_neg hro] at h
        simp only [pure, Except.pure] at h
        exact (Except.ok.inj h).symm
      rw [if_pos hro] at h
      revert h
      cases hrp : checkReducePin (fueledOps mode F) env env₂ cv.name value with
      | error err => intro h; exact nomatch h
      | ok u =>
        intro h
        simp only [pure, Except.pure] at h
        exact (Except.ok.inj h).symm
    subst henv
    obtain rfl := checkOpaqueVal_shape hov
    exact EtaFamiliesClosed.cons_nonind hE1 hfind'
      (fun _ _ hx _ => ConstantInfo.noConfusion hx)
  | axiomDecl cv =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal (fueledOps mode F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cvA =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', -, -, -, -, -, type, stype, u, -, -, -, -, -,
      rfl⟩ := checkConstantVal_invT hccv
    have hnonind : EtaFamiliesClosed
        ⟨.axiomInfo { cv with type := type } :: env.consts⟩ :=
      EtaFamiliesClosed.cons_nonind hE1 hfind'
        (fun _ _ hx _ => ConstantInfo.noConfusion hx)
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hnonind
    split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hnonind
      · exact nomatch h
    split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hnonind
      · exact nomatch h
    split at h
    · exact nomatch h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hE1
    · exact nomatch h
  | basisDecl kind =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    revert h
    by_cases hq : kind = BasisKind.quotK
    · subst hq
      simp only [reduceIte]
      by_cases heqf : env.find? eqName = some eqA
      case neg =>
        intro h
        rw [if_neg heqf] at h
        exact nomatch h
      intro h
      rw [if_pos heqf] at h
      try dsimp only at h
      exact basisFold_closed (basisDecls_headOk _) h hE1
    · intro h
      rw [if_neg hq] at h
      try dsimp only at h
      exact basisFold_closed (basisDecls_headOk _) h hE1
  | indDecl block =>
    rw [show checkDecl mode (fueledOps mode F) env (.indDecl block) =
        (match directParts? env block with
          | some p => checkDirectStruct (fueledOps mode F) env p
          | none => checkIndDecl mode (fueledOps mode F) env block) from rfl,
      directParts?_none hdir env block] at h
    exact indFamilies h hE1

end Setlec.TTVerify
