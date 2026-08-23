import Setlec.Model.Extend.BasisOne
import Setlec.Model.Extend.Iota
import Setlec.Model.Extend.Transport

/-!
# Modeled — split out of `Setlec.Model.Extend`

Extension by opaque modeled inductive-kind members:
`extend_modeled_one` for type formers and constructors,
`extend_modeled_rec` for recursors with checked iota rules, and the
`checkIndMember` inversion feeding them.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Extend a model by one opaque modeled inductive-kind member (an
inductive type former or constructor; the recursor carries rule
obligations and is handled separately): its value is its `_model`
counterpart's, and its type interprets identically through the block
renaming.  The type agreement is structural up to display-only binder
names (`Expr.eqUpToNames`) — the interpretation never reads them — so
the member's own annotation truthfulness is a hypothesis (`hannT`,
from the member's annotation run) rather than transported from the
model's. -/
theorem extend_modeled_one {env : Env} (m : EnvModel V env)
    (ci : ConstantInfo) (f : Name → Name) (mname : Name)
    {cvm : ConstantVal} {mval : Expr}
    (hfind' : env.find? ci.name = none)
    (hnres : reservedBasisNames.contains ci.name = false)
    (hwf : ConstWF ⟨ci :: env.consts⟩ ci)
    (htyres0 : ci.toConstantVal.type.constsResolve env = true)
    (hkind : (∃ cv caps, ci = .indInfo cv caps) ∨
      (∃ cv nP nF, ci = .ctorInfo cv nP nF) ∨
      (∃ cv mI rP, ci = .recInfo cv mI rP []))
    (hmodel : env.find? mname = some (.defnInfo cvm mval hmcvm))
    (hlps : cvm.levelParams = ci.toConstantVal.levelParams)
    (hren : Expr.eqUpToNames (ci.toConstantVal.type.renameConsts f)
      cvm.type = true)
    (hannT : ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) ci.toConstantVal.type)
    (hro : RenameOk m.val env f)
    (hmodm : ((∃ cv caps, ci = .indInfo cv caps) ∨
        (∃ cv cnP cnF, ci = .ctorInfo cv cnP cnF)) →
      (env.find? (ci.name.str "_model")).isSome = true ∧
      ∀ ψ : Name → Nat, m.val mname ψ = m.val (ci.name.str "_model") ψ)
    (hprojm : ∀ (T : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule), ci.name = projFnName T j →
      ci = .recInfo cv mI rP rules →
      (env.find? (projModelName T j)).isSome = true ∧
      ∀ ψ : Name → Nat, m.val mname ψ = m.val (projModelName T j) ψ)
    (hetaLm : ∀ cv caps, ci = .indInfo cv caps → caps.eta = true →
      reservedBasisNames.contains ci.name = false →
      (env.find? (caps.etaCtor.str "_model")).isSome = true ∧
      (∀ j, j < caps.etaFields →
        (env.find? (projModelName ci.name j)).isSome = true) ∧
      ∀ (φ'' : Name → Nat) (us : List Level) (ps : List V) (x : V)
        (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V)
        (rest : Expr),
        ps.length = caps.etaParams →
        x ∈ˢ SpineFold V
          (m.val mname (Level.substFn φ'' cv.levelParams us)) ps →
        TeleFit V m.val env φ'' d₁ ρ₁
          (cv.type.instantiateLevelParams cv.levelParams us) ps d₂ ρ₂
          rest →
        x = SpineFold V (m.val (caps.etaCtor.str "_model")
            (Level.substFn φ'' cv.levelParams us))
          (ps ++ (List.range caps.etaFields).map fun j =>
            SpineFold V (m.val (projModelName ci.name j)
              (Level.substFn φ'' cv.levelParams us)) (ps ++ [x])))
    (hunitLm : ∀ cv caps, ci = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains ci.name = false →
      ∀ (φ'' : Name → Nat) (us : List Level) (ps : List V) (x y : V)
        (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V)
        (rest : Expr),
        ps.length = caps.unitParams →
        x ∈ˢ SpineFold V
          (m.val mname (Level.substFn φ'' cv.levelParams us)) ps →
        y ∈ˢ SpineFold V
          (m.val mname (Level.substFn φ'' cv.levelParams us)) ps →
        TeleFit V m.val env φ'' d₁ ρ₁
          (cv.type.instantiateLevelParams cv.levelParams us) ps d₂ ρ₂
          rest →
        x = y) :
    ∃ m' : EnvModel V ⟨ci :: env.consts⟩,
      (∀ ψ, m'.val ci.name ψ = m.val mname ψ) ∧
      (∀ n ψ, n ≠ ci.name → m'.val n ψ = m.val n ψ) := by
  have hmm : ConstantInfo.defnInfo cvm mval hmcvm ∈ env.consts :=
    List.mem_of_find?_eq_some hmodel
  have hkey : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m.val env ψ ci.toConstantVal.type = some T ∧
        m.val (mname) ψ ∈ˢ T := by
    intro ψ
    obtain ⟨T, hT, hmem⟩ := m.mem_type _ hmm ψ
    have hname : cvm.name = mname := by
      have := List.find?_some hmodel
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
    refine ⟨T, ?_, by rw [← hname]; exact hmem⟩
    have hri : interpClosed V m.val env ψ (ci.toConstantVal.type.renameConsts f) =
        interpClosed V m.val env ψ ci.toConstantVal.type :=
      interp_renameConsts hro _ 0 (rho0 V)
    have hre : interpClosed V m.val env ψ
        (ci.toConstantVal.type.renameConsts f) =
        interpClosed V m.val env ψ cvm.type :=
      interp_erasedEq (Expr.ErasedEq.of_eqUpToNames hren) 0 (rho0 V)
    rw [← hri, hre]
    exact hT
  exact extend_basis_one m ci (fun ψ => m.val (mname) ψ)
    hfind' hwf htyres0
    (fun cv2 value2 h2 => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩ <;> simp)
    hkey
    (fun ψ₁ ψ₂ hψ => by
      refine m.val_params _ _ hmodel ψ₁ ψ₂ ?_
      intro p hp
      refine hψ p ?_
      rwa [show (ConstantInfo.defnInfo cvm mval hmcvm).toConstantVal = cvm from rfl,
        hlps] at hp)
    (fun ψ => hannT ψ)
    (fun cv caps heq hn => absurd (hn ▸ hnres) (by decide))
    (fun cv nP nF heq hn => absurd (hn ▸ hnres) (by decide))
    (fun cv caps heq hn => absurd (hn ▸ hnres) (by decide))
    (fun hn => absurd (hn ▸ hnres) (by decide))
    (fun _ hres2 => absurd (hres2 ▸ hnres) (by simp))
    (fun cv mI rP rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · exact ⟨fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide)⟩)
    (fun val' _ _ cvR mI rP rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with h1 h2 h3 h4
        subst h4
        intro r hr
        cases hr)
    (fun cvR mI rP rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with h1 h2 h3 h4
        subst h4
        intro r hr
        cases hr)
    (fun _ => hmodm) hprojm
    (fun entry heq _ => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩ <;> exact nomatch heq)
    hetaLm hunitLm
    (fun cv2 value2 => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩ <;> simp)

/-- The fold invariant of `checkIndDecl`: every installed block member
has its `_model` companion stored (as a definition with the same level
parameters) and is interpreted by it. -/
def BlockInstalled (blockNames : List Name) (env' : Env)
    (val : ConstVal V) : Prop :=
  ∀ n, blockNames.contains n = true → ∀ ci, env'.find? n = some ci →
    ∃ cvm mval hmcvm, env'.find? (n.str "_model") = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat, val n ψ = val (n.str "_model") ψ

omit [SetTheory V] in
/-- Installing one member with its model's value preserves the fold
invariant. -/
theorem BlockInstalled.step {blockNames : List Name} {env' : Env}
    {val val₁ : ConstVal V} {ci₁ : ConstantInfo} {cvm : ConstantVal}
    {mval : Expr} {hmcvm : ReducibilityHint}
    (hI : BlockInstalled blockNames env' val)
    (hms : ci₁.name.isModelSuffix = false)
    (hfm : env'.find? (ci₁.name.str "_model") = some (.defnInfo cvm mval hmcvm))
    (hlps : cvm.levelParams = ci₁.toConstantVal.levelParams)
    (hval₁ : ∀ ψ, val₁ ci₁.name ψ = val (ci₁.name.str "_model") ψ)
    (hpres₁ : ∀ n ψ, n ≠ ci₁.name → val₁ n ψ = val n ψ) :
    BlockInstalled blockNames ⟨ci₁ :: env'.consts⟩ val₁ := by
  intro n hbn ci₂ hf₂
  rw [Env.find?_cons] at hf₂
  split at hf₂
  · next hh =>
    obtain rfl := Option.some.inj hf₂
    obtain rfl : ci₁.name = n := hh
    refine ⟨cvm, mval, hmcvm, ?_, hlps, ?_⟩
    · rw [Env.find?_cons,
        if_neg (fun h => Name.str_ne ci₁.name "_model" h.symm)]
      exact hfm
    · intro ψ
      rw [hval₁ ψ, hpres₁ _ ψ (Name.str_ne ci₁.name "_model")]
  · next hh =>
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hI n hbn ci₂ hf₂
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, ?_⟩
    · rw [Env.find?_cons, if_neg (show ¬ci₁.name = n.str "_model" from
        fun h => Name.str_model_ne hms h.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres₁ _ ψ (fun h => hh h.symm),
        hpres₁ _ ψ (fun h => Name.str_model_ne hms h),
        hv₂ ψ]

/-- Invert a successful `checkMemberVal` run. -/
theorem checkMemberVal_inv {blockNames : List Name} {env' : Env}
    {cv cvA : ConstantVal}
    (h : checkMemberVal (fueledOps F) blockNames env' cv = .ok cvA) :
    checkConstantVal (fueledOps F) env' cv = .ok cvA ∧
    cvA.name.isModelSuffix = false ∧
    ∃ cvm mval hmcvm,
      env'.find? (cvA.name.str "_model") =
        some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = cvA.levelParams ∧
      Expr.eqUpToNames (cvA.type.renameConsts (fun n =>
        if blockNames.contains n then n.str "_model" else n)) cvm.type =
        true := by
  simp only [checkMemberVal, fueledOps_annotate, fueledOps_inferType,
    fueledOps_isDefEq, fueledOps_ensureSort, fueledOps_whnf, Bind.bind,
    Except.bind] at h
  cases hccv : checkConstantVal (fueledOps F) env' cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cvA' =>
  rw [hccv] at h
  try dsimp only at h
  by_cases hms : cvA'.name.isModelSuffix = true
  case pos => rw [if_pos hms] at h; exact nomatch h
  rw [if_neg hms] at h
  have hmsF : cvA'.name.isModelSuffix = false := by
    revert hms; cases cvA'.name.isModelSuffix <;> simp
  try dsimp only at h
  revert h
  match hfm : env'.find? (cvA'.name.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvm mval hmcvm) => ?_
  intro h
  dsimp only at h
  by_cases hlps : cvm.levelParams = cvA'.levelParams
  case neg => rw [if_neg hlps] at h; exact nomatch h
  rw [if_pos hlps] at h
  try dsimp only at h
  by_cases hren : Expr.eqUpToNames (cvA'.type.renameConsts (fun n =>
      if blockNames.contains n then n.str "_model" else n))
      cvm.type = true
  case neg => rw [if_neg hren] at h; exact nomatch h
  rw [if_pos hren] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, hmsF, cvm, mval, hmcvm, hfm, hlps, hren⟩

/-- Invert a successful `checkIndMember` run (non-recursor members). -/
theorem checkIndMember_inv {blockNames : List Name} {caps : IndCaps}
    {env' env₁ : Env} {ci : ConstantInfo}
    (h : checkIndMember (fueledOps F) blockNames caps env' ci = .ok env₁) :
    ∃ cvA cvm mval hmcvm,
      checkConstantVal (fueledOps F) env' ci.toConstantVal = .ok cvA ∧
      cvA.name.isModelSuffix = false ∧
      env'.find? (cvA.name.str "_model") = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = cvA.levelParams ∧
      Expr.eqUpToNames (cvA.type.renameConsts (fun n =>
        if blockNames.contains n then n.str "_model" else n)) cvm.type =
        true ∧
      ((∃ cv caps', ci = .indInfo cv caps') ∧
         env₁ = ⟨.indInfo cvA caps :: env'.consts⟩ ∨
       (∃ cv nP nF, ci = .ctorInfo cv nP nF ∧
         env₁ = ⟨.ctorInfo cvA nP nF :: env'.consts⟩)) := by
  simp only [checkIndMember, Bind.bind, Except.bind] at h
  cases hcmv : checkMemberVal (fueledOps F) blockNames env'
      ci.toConstantVal with
  | error e => rw [hcmv] at h; exact nomatch h
  | ok cvA =>
  rw [hcmv] at h
  obtain ⟨hccv, hms, cvm, mval, hmcvm, hfm, hlps, hren⟩ :=
    checkMemberVal_inv hcmv
  refine ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hren, ?_⟩
  cases ci with
  | axiomInfo cv => exact nomatch h
  | projInfo _ => exact nomatch h
  | defnInfo cv value hint => exact nomatch h
  | thmInfo cv value => exact nomatch h
  | recInfo cv mI rP rules => exact nomatch h
  | indInfo cv caps' =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨⟨cv, caps', rfl⟩, h.symm⟩
  | ctorInfo cv nP nF =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inr ⟨cv, nP, nF, rfl, h.symm⟩

/-- One step of `provisionRecs`. -/
theorem provisionRecs_cons_inv {blockNames : List Name}
    {envAcc : Env} {ci : ConstantInfo} {rest : List ConstantInfo}
    {p : Env × List (ConstantVal × Nat × Nat × List RecRule)}
    (h : provisionRecs (fueledOps F) blockNames envAcc (ci :: rest) =
      .ok p) :
    ∃ cv mI rP rules cvA p',
      ci = .recInfo cv mI rP rules ∧
      checkMemberVal (fueledOps F) blockNames envAcc ci.toConstantVal =
        .ok cvA ∧
      provisionRecs (fueledOps F) blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ rest = .ok p' ∧
      p = (p'.1, (cvA, mI, rP, rules) :: p'.2) := by
  revert h
  match ci with
  | .recInfo cv mI rP rules => ?_
  | .axiomInfo _ => intro h; exact nomatch h
  | .projInfo _ => intro h; exact nomatch h
  | .defnInfo _ _ _ => intro h; exact nomatch h
  | .thmInfo _ _ => intro h; exact nomatch h
  | .indInfo _ _ => intro h; exact nomatch h
  | .ctorInfo _ _ _ => intro h; exact nomatch h
  intro h
  simp only [provisionRecs, Bind.bind, Except.bind] at h
  cases hcmv : checkMemberVal (fueledOps F) blockNames envAcc
      (ConstantInfo.recInfo cv mI rP rules).toConstantVal with
  | error e => rw [hcmv] at h; exact nomatch h
  | ok cvA =>
  rw [hcmv] at h
  try dsimp only at h
  cases hrec : provisionRecs (fueledOps F) blockNames
      ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ rest with
  | error e => rw [hrec] at h; exact nomatch h
  | ok p' =>
  rw [hrec] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨cv, mI, rP, rules, cvA, p', rfl, rfl, hrec, h.symm⟩

end Setlec
