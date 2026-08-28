import Setlec.SetR.Install.IndRecsS
import Setlec.SetR.Install.IndBottomProjS
import Setlec.Verify.Extend.Iota

/-!
# The projection-function phase (task #148, T5, stage 5)

`projFnS` installs one projection function and `projInstallS` folds it
over the fields.  The transpose is of `checkProjFn_sound` /
`checkProjFold_sound` (`Setlec/Model/Extend/Proj.lean`), and the
scoping note this file replaces got one thing wrong: the eta head
obligation is **not** forwarded here.  It is discharged in-fold,
because `hbshape` narrows its head disjunct — a block name is never
projection-shaped, so neither `T' = projFnName T i` nor
`capsT.etaCtor = projFnName T i` can hold, and the only surviving
disjunct is the projection one, which pins `T' = T` and the field
index.  (Practice P2, again: the disjunct had to be read, not
summarised.)

The phase's own invariant, `ProjPhaseInvS`, is what makes the
renaming work: `projFwd`'s three cases are exactly its three
conjuncts, so `RenameOkT` for the pruned map falls straight out of it.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The projection phase's fold invariant** ([set] transpose of
`ProjPhaseInv`): the parent type and the constructor still carry their
model values, and every installed projection function carries its
`_model.proj_j`'s.  These three conjuncts are `projFwd`'s three
cases. -/
def ProjPhaseInvS (T ctorName : Name) (nF : Nat) (env' : Env)
    (cval : TConstVal) : Prop :=
  (∀ ci, env'.find? T = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (T.str "_model") = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat, cval T ψ = cval (T.str "_model") ψ) ∧
  (∀ ci, env'.find? ctorName = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (ctorName.str "_model")
        = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        cval ctorName ψ = cval (ctorName.str "_model") ψ) ∧
  (∀ j, j < nF → ∀ ci, env'.find? (projFnName T j) = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (projModelName T j)
        = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        cval (projFnName T j) ψ = cval (projModelName T j) ψ)

/-- The projection renaming, pruned to the stored names, is sound at
the phase invariant.  Its three cases *are* the invariant's three
conjuncts. -/
theorem projFwd_renameOkT {T ctorName : Name} {nF : Nat} {env' : Env}
    {cval : TConstVal} (hinv : ProjPhaseInvS T ctorName nF env' cval) :
    RenameOkT cval env' (fun n => if (env'.find? n).isSome = true then
      projFwd T ctorName nF n else n) := by
  have hfound : ∀ n ci₂, env'.find? n = some ci₂ →
      (∃ ci', env'.find? (projFwd T ctorName nF n) = some ci' ∧
        ci'.toConstantVal.levelParams = ci₂.toConstantVal.levelParams) ∧
      (∀ ψ : Name → Nat,
        cval (projFwd T ctorName nF n) ψ = cval n ψ) := by
    intro n ci₂ hf₂
    unfold projFwd
    try dsimp only
    by_cases h1 : n = T
    · subst h1
      rw [if_pos rfl]
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.1 ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
    rw [if_neg h1]
    by_cases h2 : n = ctorName
    · subst h2
      rw [if_pos rfl]
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.1 ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
    rw [if_neg h2]
    cases hfind : (List.range nF).find?
      (fun j => n == projFnName T j) with
    | none => exact ⟨⟨ci₂, hf₂, rfl⟩, fun ψ => rfl⟩
    | some j =>
      have hjlt : j < nF :=
        List.mem_range.mp (List.mem_of_find?_eq_some hfind)
      have hn : n = projFnName T j := by
        have hprop := List.find?_some hfind
        exact eq_of_beq (by simpa using hprop)
      subst hn
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ :=
        hinv.2.2 j hjlt ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n ci₂ hf₂
    dsimp only
    rw [if_pos (show (env'.find? n).isSome = true by rw [hf₂]; rfl)]
    exact (hfound n ci₂ hf₂).1
  · intro n hf₂
    dsimp only
    rw [if_neg (show ¬(env'.find? n).isSome = true by
      rw [hf₂]; exact fun hx => nomatch hx)]
    exact hf₂
  · intro n ψ
    dsimp only
    cases hf₂ : env'.find? n with
    | none =>
      rw [if_neg (show ¬(none : Option ConstantInfo).isSome = true
        from fun hx => nomatch hx)]
    | some ci₂ =>
      rw [if_pos (show (some ci₂ : Option ConstantInfo).isSome = true
        from rfl)]
      exact (hfound n ci₂ hf₂).2 ψ

/-! ## One field: provision rule-less, fire, swap

The projection recursor cannot be consed **with** its rule and then
have `indBottomProjS` fire at the result: the bottom is premised on an
`EnvS`, and `EnvS.cons`'s `hheadRec` is a field of the very bundle
being built (practice P1).  The recursor group's architecture is
therefore forced here too — provision rule-less, fire at the
provisioned environment where a model genuinely exists, and swap the
rule in (`EnvS.swap`, stage 3a; `RecRuleLawV.swapS`, stage 3c).
Unlike the group case the provisioning is a single cons, so no fold is
needed. -/

/-- The rule-less projection entry. -/
abbrev projProvEntry (T : Name) (lps : List Name) (pty : Expr)
    (nP i : Nat) : ConstantInfo :=
  .recInfo ⟨projFnName T i, lps, pty⟩ nP nP []

/-- The ruled projection entry (`ProjFnR`'s stored output). -/
abbrev projRuledEntry (T ctorName : Name) (lps : List Name) (pty : Expr)
    (nP nF i : Nat) (rhsA : Expr) : ConstantInfo :=
  .recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [⟨ctorName, nF, nP,
      if Expr.recRulePlain pty nP nP nP then .plain else .inert,
      rhsA⟩]

/-- **The phase invariant crosses a projection cons.**  Parameterised
by the head entry, because both the provisioned (rule-less) and the
ruled entry need it — they differ only in a rule list, which the
invariant never reads. -/
theorem projPhaseInvS_cons {T ctorName : Name} {nF : Nat} {env' : Env}
    {cval cval₀ : TConstVal} {c₀ : ConstantInfo} {lps : List Name}
    {pty : Expr} {i : Nat} {mcv : ConstantVal} {mval : Expr}
    {mhint : ReducibilityHint}
    (hcvA : c₀.toConstantVal = ⟨projFnName T i, lps, pty⟩)
    (hinv : ProjPhaseInvS T ctorName nF env' cval)
    (hfresh : env'.find? (projFnName T i) = none)
    (hTf : (env'.find? T).isSome = true)
    (hCf : (env'.find? ctorName).isSome = true)
    (hfm : env'.find? (projModelName T i)
      = some (.defnInfo mcv mval mhint))
    (hmlps : mcv.levelParams = lps)
    (hilt : i < nF)
    (hself : ∀ ψ : Name → Nat,
      cval₀ (projFnName T i) ψ = cval (projModelName T i) ψ)
    (hag : ∀ n, n ≠ projFnName T i → cval n = cval₀ n) :
    ProjPhaseInvS T ctorName nF ⟨c₀ :: env'.consts⟩ cval₀ := by
  have hname : c₀.name = projFnName T i := by
    rw [show c₀.name = c₀.toConstantVal.name from rfl, hcvA]
  -- the head's name differs from every name the invariant reads
  have hneP : ∀ n : Name, (env'.find? n).isSome = true →
      n ≠ projFnName T i := by
    intro n hn hh
    rw [hh, hfresh] at hn
    exact nomatch hn
  have hne : ∀ n : Name, (env'.find? n).isSome = true →
      ¬c₀.name = n :=
    fun n hn hh => hneP n hn (by rw [← hh, hname])
  have hmodelNeP : ∀ j : Nat, projModelName T j ≠ projFnName T i :=
    fun j hh => Name.num_ne_str _ _ _ _ hh.symm
  have hmodelNe : ∀ (j : Nat), ¬c₀.name = projModelName T j :=
    fun j hh => hmodelNeP j (by rw [← hh, hname])
  have hdown : ∀ (n : Name) (ci : ConstantInfo),
      Env.find? ⟨c₀ :: env'.consts⟩ n = some ci → ¬c₀.name = n →
      env'.find? n = some ci := by
    intro n ci hf hn
    rw [Env.find?_cons, if_neg hn] at hf
    exact hf
  have hup : ∀ (n : Name) (ci : ConstantInfo),
      env'.find? n = some ci → ¬c₀.name = n →
      Env.find? ⟨c₀ :: env'.consts⟩ n = some ci := by
    intro n ci hf hn
    rw [Env.find?_cons, if_neg hn]
    exact hf
  have hstrNeP : ∀ n : Name, n.str "_model" ≠ projFnName T i :=
    fun n hh => Name.num_ne_str _ _ _ _ hh.symm
  have hstrNe : ∀ n : Name, ¬c₀.name = n.str "_model" :=
    fun n hh => hstrNeP n (by rw [← hh, hname])
  refine ⟨?_, ?_, ?_⟩
  · intro ci hf
    obtain ⟨cvm, mv, hm, hfm', hlps', hv'⟩ :=
      hinv.1 ci (hdown T ci hf (hne T hTf))
    refine ⟨cvm, mv, hm, hup _ _ hfm' (hstrNe T), hlps', ?_⟩
    intro ψ
    rw [← hag T (hneP T hTf), ← hag _ (hstrNeP T)]
    exact hv' ψ
  · intro ci hf
    obtain ⟨cvm, mv, hm, hfm', hlps', hv'⟩ :=
      hinv.2.1 ci (hdown ctorName ci hf (hne ctorName hCf))
    refine ⟨cvm, mv, hm, hup _ _ hfm' (hstrNe ctorName), hlps', ?_⟩
    intro ψ
    rw [← hag ctorName (hneP ctorName hCf), ← hag _ (hstrNeP ctorName)]
    exact hv' ψ
  · intro j hj ci hf
    by_cases hji : j = i
    · subst hji
      rw [Env.find?_cons, if_pos hname] at hf
      obtain rfl := Option.some.inj hf
      refine ⟨mcv, mval, mhint, hup _ _ hfm (hmodelNe j), ?_, ?_⟩
      · rw [hcvA, hmlps]
      · intro ψ
        rw [hself, ← hag _ (hmodelNeP j)]
    · have hjneP : projFnName T j ≠ projFnName T i := by
        intro hh
        have hh2 : Name.num (T.str "proj") j
          = Name.num (T.str "proj") i := hh
        injection hh2 with _hp hij
        exact hji hij
      have hjne : ¬c₀.name = projFnName T j :=
        fun hh => hjneP (by rw [← hh, hname])
      obtain ⟨cvm, mv, hm, hfm', hlps', hv'⟩ :=
        hinv.2.2 j hj ci (hdown _ ci hf hjne)
      refine ⟨cvm, mv, hm, hup _ _ hfm' (hmodelNe j), hlps', ?_⟩
      intro ψ
      rw [← hag _ hjneP, ← hag _ (hmodelNeP j)]
      exact hv' ψ

set_option maxHeartbeats 3200000 in
/-- **The rule-less projection entry installs.**  Everything but the
front door and the eta head is either vacuous at a `.recInfo` head or
a name-distinctness fact; the front door is the model projection's own,
read through the renaming; the eta head is `etaLawKeyS` one
environment ahead (finding 6). -/
theorem projProvisionS {μ : CheckMode} {env' : Env} (m : EnvS V env')
    {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    {blockNames : List Name} {mcv : ConstantVal} {mval : Expr}
    {mhint : ReducibilityHint} {pty : Expr}
    (hfm : env'.find? (projModelName T i)
      = some (.defnInfo mcv mval mhint))
    (hmlps : mcv.levelParams = lps)
    (hpnone : (env'.find? (projFnName T i)).isNone = true)
    -- `hptyB` (the `projBack` definition of `pty`) is *not* needed:
    -- the roundtrip equation alone identifies the denotation
    (hround : (pty.renameConsts (projFwd T ctorName nF) == mcv.type)
      = true)
    (hptyres : pty.constsResolve env' = true)
    (hptyb : pty.looseBVarsBounded 0 = true)
    (hptyf : pty.hasFvar = false)
    (hptylp : pty.allLevelParamsDefined lps = true)
    (hinv : ProjPhaseInvS T ctorName nF env' m.cval)
    (hIB : BlockInstalledTT blockNames env' m.cval)
    (hTblock : blockNames.contains T = true)
    -- no `hbshape` here: the eta head's first two disjuncts are
    -- refuted by the *stored kind* (a `.recInfo` sits where the
    -- family wants an `.indInfo` / a `.ctorInfo`), which is cheaper
    -- than the Model lane's name-shape argument
    (hpinsT : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      EtaPins μ env' T cvT.levelParams capsT)
    (hCblock : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → blockNames.contains capsT.etaCtor = true)
    (hFields : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → capsT.etaFields = nF) :
    ∃ m₀ : EnvS V ⟨projProvEntry T lps pty nP i :: env'.consts⟩,
      m₀.cval = cvalWith m.cval (projFnName T i)
        (fun ψ => m.cval (projModelName T i) ψ) := by
  obtain ⟨cval₀, hcval₀⟩ : ∃ c, c = cvalWith m.cval (projFnName T i)
      (fun ψ => m.cval (projModelName T i) ψ) := ⟨_, rfl⟩
  have hfresh : env'.find? (projFnName T i) = none :=
    Option.isNone_iff_eq_none.mp hpnone
  have hnres : reservedBasisNames.contains (projFnName T i) = false :=
    reservedBasisNames_not_num _ _
  -- the install
  have hag : ∀ n, n ≠ projFnName T i → m.cval n = cval₀ n := by
    intro n hn
    rw [hcval₀, cvalWith_ne hn]
  have hi : Installs env' m.cval cval₀ (projProvEntry T lps pty nP i) :=
    Installs.of_fresh hfresh hag
  have hself : cval₀ (projFnName T i)
      = fun ψ => m.cval (projModelName T i) ψ := by
    rw [hcval₀]; exact cvalWith_self
  have hselfA : ∀ ψ : Name → Nat,
      cval₀ (projFnName T i) ψ = m.cval (projModelName T i) ψ :=
    fun ψ => congrFun hself ψ
  refine ⟨EnvS.cons m hi ?_ ?_ ?_ ?_ ?_
    (fun cv2 v2 h2 heq => ConstantInfo.noConfusion heq)
    (fun cv2 v2 heq => ConstantInfo.noConfusion heq)
    (fun heq => absurd heq (Name.num_ne_str _ _ _ _))
    (fun cv2 mI2 rP2 rules2 heq r hr => by
      injection heq with _ _ _ h4
      rw [← h4] at hr
      exact nomatch hr)
    (fun cv2 mI2 rP2 rules2 heq rl hrl => by
      injection heq with _ _ _ h4
      rw [← h4] at hrl
      exact nomatch hrl)
    ?_
    (fun cv2 caps2 heq => ConstantInfo.noConfusion heq)
    (fun e heq => ConstantInfo.noConfusion heq)
    (fun i2 e heq => ConstantInfo.noConfusion heq)
    (fun heq => absurd heq (Name.num_ne_str _ _ _ _))
    (fun hres => absurd
      (show reservedBasisNames.contains (projFnName T i) = true
        from hres)
      (by rw [hnres]; exact fun h => nomatch h))
    (fun cv2 v2 h2 heq => ConstantInfo.noConfusion heq)
    (fun cv2 v2 h2 heq => ConstantInfo.noConfusion heq)
    (fun cv2 heq => ConstantInfo.noConfusion heq), hcval₀⟩
  · -- `EnvWF` at the extension
    refine EnvWF.cons m.wf ⟨hptyf, hptylp,
      Expr.constsResolve_mono hptyres, hptyb,
      (fun cv2 v2 h2 heq => ConstantInfo.noConfusion heq), ?_,
      (fun cv2 v2 heq => ConstantInfo.noConfusion heq)⟩
    intro cv2 mI2 rP2 rules2 heq r hr
    injection heq with _ _ _ h4
    rw [← h4] at hr
    exact nomatch hr
  · -- closedness
    intro ψ
    show VExpr.Closed (cval₀ (projFnName T i) ψ)
    rw [hselfA]
    exact m.cval_closed _ _
  · -- level-parameter dependence
    intro φ₁ φ₂ hp
    show cval₀ (projFnName T i) φ₁ = cval₀ (projFnName T i) φ₂
    rw [hselfA, hselfA]
    refine m.val_params _ _ hfm φ₁ φ₂ ?_
    intro p hp'
    exact hp p (show p ∈ lps from by rw [← hmlps]; exact hp')
  · -- truthfulness
    intro ψ ρ
    show AnnotOkV V ρ (cval₀ (projFnName T i) ψ)
    rw [hselfA]
    exact m.annot_okV _ _ _
  · -- the front door: the model projection's own, read through the
    -- projection renaming (`ProjPhaseInvS` is what makes it sound)
    intro φ
    obtain ⟨t, ht, hfacts⟩ :=
      m.mem_type (.defnInfo mcv mval mhint) (find?_mem hfm) φ
    refine ⟨t, ?_, ?_⟩
    · show denoteClosed cval₀ ⟨projProvEntry T lps pty nP i ::
        env'.consts⟩ φ pty = some t
      refine hi.denoteUp (d := 0) ?_
      have hrenP : pty.renameConsts (fun n =>
          if (env'.find? n).isSome = true then
            projFwd T ctorName nF n else n) = mcv.type := by
        rw [Expr.renameConsts_congr_resolve
          (g := projFwd T ctorName nF)
          (fun n hn => by simp only [hn, if_true]) _ hptyres]
        exact eq_of_beq hround
      rw [← denote_renameConsts (projFwd_renameOkT hinv) pty 0, hrenP]
      exact ht
    · intro ρ
      show interp V ρ (cval₀ (projFnName T i) φ) ∈ˢ interp V ρ t ∧
        AnnotOkV V ρ t
      rw [hselfA, ← show (ConstantInfo.defnInfo mcv mval mhint).name
        = projModelName T i from Env.find?_name hfm]
      exact hfacts ρ
  · -- the eta head: the *completing* projection fires `etaLawKeyS`
    intro T' cvT capsT hfT' hcape hresT' hfam hpart
    -- the first two disjuncts store a `.recInfo` where the family
    -- wants an `.indInfo` / a `.ctorInfo`
    obtain ⟨j, hj, hP⟩ : ∃ j, j < capsT.etaFields ∧
        projFnName T' j = projFnName T i := by
      rcases hpart with hh | hh | hh
      · rw [Env.find?_cons, if_pos (show
          (projProvEntry T lps pty nP i).name = T'
          from hh.symm)] at hfT'
        exact nomatch (Option.some.inj hfT')
      · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
        rw [Env.find?_cons, if_pos (show
          (projProvEntry T lps pty nP i).name = capsT.etaCtor
          from hh.symm)] at hfC
        exact nomatch (Option.some.inj hfC)
      · exact hh
    -- the projection disjunct pins the family and the index
    obtain ⟨hTT, hji⟩ : T' = T ∧ j = i := by
      have hh' : Name.num (T'.str "proj") j
        = Name.num (T.str "proj") i := hP
      injection hh' with hp hij
      injection hp with hT hs
      exact ⟨hT, hij⟩
    rw [hTT] at hfT' hfam ⊢
    -- the family, below the head
    have hfT : env'.find? T = some (.indInfo cvT capsT) := by
      rw [Env.find?_cons] at hfT'
      split at hfT'
      · exact nomatch (Option.some.inj hfT')
      · exact hfT'
    obtain ⟨tcv, tval, cvmT, mvalT, hmTh, sbinders, tbindersM, sbody,
      tbodyM, tySlot, ℓA, hthmE, htlps, hTmE, hTmlps, hctorM, hprojE,
      heqfE, hSstrip, hTstrip, hsdoms, hxdom, hsbody, htySlot, -⟩ :=
      (hpinsT cvT capsT hfT).1 hcape
    obtain ⟨cvmC, mvalC, hmC, hCmE, hCmlps⟩ := hctorM
    obtain ⟨cvmT', mvalT', hmT', hfmT', hlpsT', hrenT', hvT'⟩ :=
      hIB T hTblock _ hfT
    have hcvmEq : cvmT' = cvmT := by
      obtain ⟨h1, -, -⟩ :=
        ConstantInfo.defnInfo.inj (Option.some.inj (hfmT'.symm.trans
          hTmE))
      exact h1
    rw [hcvmEq] at hrenT'
    -- the constructor, below the head
    have hCblockT : blockNames.contains capsT.etaCtor = true :=
      hCblock cvT capsT hfT hcape
    obtain ⟨cvC, hfC0⟩ := hfam.2.1
    have hfC : env'.find? capsT.etaCtor
        = some (.ctorInfo cvC capsT.etaParams capsT.etaFields) := by
      rw [Env.find?_cons] at hfC0
      split at hfC0
      · exact nomatch (Option.some.inj hfC0)
      · exact hfC0
    obtain ⟨-, -, -, -, -, -, hvC'⟩ := hIB capsT.etaCtor hCblockT _ hfC
    -- the three valuation identifications, on the installed valuation
    have hagS : ∀ n, (env'.find? n).isSome = true →
        cval₀ n = m.cval n := fun n hn => (hi.agree hn).symm
    have hvT : ∀ ψ : Name → Nat,
        cval₀ T ψ = cval₀ (T.str "_model") ψ := by
      intro ψ
      rw [hagS T (by rw [hfT]; rfl),
        hagS (T.str "_model") (by rw [hfmT']; rfl)]
      exact hvT' ψ
    have hvC : ∀ ψ : Name → Nat,
        cval₀ capsT.etaCtor ψ
          = cval₀ (capsT.etaCtor.str "_model") ψ := by
      intro ψ
      rw [hagS _ (by rw [hfC]; rfl), hagS _ (by rw [hCmE]; rfl)]
      exact hvC' ψ
    have hvP : ∀ j', j' < capsT.etaFields → ∀ ψ : Name → Nat,
        cval₀ (projFnName T j') ψ
          = cval₀ (projModelName T j') ψ := by
      intro j' hj' ψ
      obtain ⟨cvmj, mvalj, hmj, hfPmj, -⟩ := hprojE j' hj'
      by_cases hji' : j' = i
      · subst hji'
        rw [hselfA, hagS _ (by rw [hfPmj]; rfl)]
      · obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfam.2.2 j' hj'
        have hne2 : ¬(projProvEntry T lps pty nP i).name
            = projFnName T j' := by
          intro hh
          exact hji' (by
            have hh2 : Name.num (T.str "proj") i
              = Name.num (T.str "proj") j' := hh
            injection hh2 with _hp2 hij2
            exact hij2.symm)
        rw [Env.find?_cons, if_neg hne2] at hf2
        rw [hagS _ (by rw [hf2]; rfl), hagS _ (by rw [hfPmj]; rfl)]
        obtain ⟨-, -, -, -, -, hv2⟩ := hinv.2.2 j' (by
          rw [← hFields cvT capsT hfT hcape]; exact hj') _ hf2
        exact hv2 ψ
    -- the rest of `etaLawKeyS`'s inputs
    have hclA : ∀ (n : Name) (ψ : Name → Nat),
        VExpr.Closed (cval₀ n ψ) := by
      intro n ψ
      by_cases hn : n = projFnName T i
      · subst hn
        rw [hselfA]
        exact m.cval_closed _ _
      · rw [hcval₀, cvalWith_ne hn]
        exact m.cval_closed _ _
    obtain ⟨-, -, hTres0, -, -, -, -⟩ := m.wf _ (find?_mem hfT)
    have hTres : cvT.type.constsResolve env' = true := hTres0
    have hresTA : ∀ us : List Level,
        (cvT.type.instantiateLevelParams cvT.levelParams
          us).constsResolve env' = true := by
      intro us
      rw [Expr.constsResolve_instantiateLevelParams]
      exact hTres
    have hroB : RenameOkT cval₀ env' (fun n =>
        if (env'.find? n).isSome = true then
          (if blockNames.contains n then n.str "_model" else n)
        else n) :=
      renameOkT_cvalStep hi (fun n hn => by simp [hn]) hIB.renameOkT
    have hrenTA : RenEqT (fun n =>
        if (env'.find? n).isSome = true then
          (if blockNames.contains n then n.str "_model" else n)
        else n) cvT.type cvmT.type := by
      unfold RenEqT
      rw [Expr.renameConsts_congr_resolve
        (g := fun n => if blockNames.contains n then n.str "_model"
          else n)
        (fun n hn => by simp only [hn, if_true]) _ hTres]
      exact Expr.ErasedEq.of_eqUpToNames hrenT'
    exact etaLawKeyS (V := V) m hi hclA hresTA rfl rfl rfl rfl hthmE
      htlps hTmE hTmlps hCmE hCmlps hprojE heqfE hSstrip hTstrip
      hsdoms hxdom hsbody htySlot hvT hvC hvP hroB hrenTA

end Setlec.SetR
