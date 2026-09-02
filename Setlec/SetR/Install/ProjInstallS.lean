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

/-- The model projection's own name is a `projFwd` fixed point: it is
not the family, not the constructor (their stored *kinds* differ), and
not shaped like a public projection. -/
theorem projFwd_model_self {T ctorName : Name} {nF i : Nat}
    (hC : projModelName T i ≠ ctorName) :
    projFwd T ctorName nF (projModelName T i) = projModelName T i := by
  unfold projFwd
  rw [if_neg (show ¬projModelName T i = T from Name.str_str_ne T _ _),
    if_neg hC]
  rw [show (List.range nF).find?
      (fun j => projModelName T i == projFnName T j) = none from by
    rw [List.find?_eq_none]
    intro j _
    intro hh
    exact Name.num_ne_str _ _ _ _ (eq_of_beq hh).symm]

/-! ## One field: the cons, with the bottom fired below it

P1 says a helper premised on a bundle cannot establish a field of that
bundle, and `EnvS.cons`'s `hheadRec` *is* such a field — so
`indBottomProjS`, premised on an `EnvS`, cannot fire at the extension.
The remedy is **not** to provision-and-swap (that was this file's first
plan, and it needs the sides pack transported to the bigger
environment, which nothing tools).  It is to **re-aim the bottom
below**: `checkProjFn` runs its checks before the recursor is stored,
so the whole kit already lives at the base environment, and
instantiating the bottom at `Rn := projModelName T i` — the *model's*
name, which the pinned statement's head names anyway — makes its
conclusion a law about `cval (T._model.proj_i)`.  At the cons that is
definitionally the installed constant's valuation
(`cvalWith_self`), so the law arrives already in the right shape.

The same reading is what the TT lane records at
`TTVerify/DeclIndProj.lean`'s "Where the bottom runs". -/

/-- The stored projection entry: a degenerate recursor, at whatever
rule list the caller installs. -/
abbrev projEntry (T : Name) (lps : List Name) (pty : Expr)
    (nP i : Nat) (rules : List RecRule) : ConstantInfo :=
  .recInfo ⟨projFnName T i, lps, pty⟩ nP nP rules

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
/-- **The projection entry installs.**  Everything but the front door,
the stored rules and the eta head is either vacuous at a `.recInfo`
head or a name-distinctness fact; the front door is the model
projection's own, read through the renaming; the eta head is
`etaLawKeyS` one environment ahead (finding 6).  The *rules* are the
caller's, because the projection bottom fires **below** this cons —
see the module docstring. -/
theorem projConsS {μ : CheckMode} {env' : Env} (m : EnvS V env')
    {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    {rules : List RecRule}
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
      capsT.eta = true → capsT.etaFields = nF)
    -- the stored rules' own obligations
    (hrulesWF : ∀ r ∈ rules,
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined lps = true ∧
      (RecRule.rhs r).constsResolve env' = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      ∀ lvls pins, RecRule.fire r ≠ .nested lvls pins)
    (hheadCtors : ∀ r ∈ rules, ∃ cvj cnP cnF,
      env'.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hheadRec : ∀ (φ : Name → Nat), ∀ rl ∈ rules,
      RecRule.fire rl ≠ .inert →
      RecRuleLawV V ⟨projEntry T lps pty nP i rules :: env'.consts⟩
        (cvalWith m.cval (projFnName T i)
          (fun ψ => m.cval (projModelName T i) ψ)) φ
        (projFnName T i) ⟨projFnName T i, lps, pty⟩ nP nP rl) :
    ∃ m₀ : EnvS V ⟨projEntry T lps pty nP i rules :: env'.consts⟩,
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
  have hi : Installs env' m.cval cval₀
      (projEntry T lps pty nP i rules) :=
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
      obtain ⟨cvjr, cnPr, cnFr, hfr⟩ := hheadCtors r hr
      exact ⟨cvjr, cnPr, cnFr, hfr⟩)
    (fun cv2 mI2 rP2 rules2 heq rl hrl hfire => by
      injection heq with h1 h2 h3 h4
      subst h1; subst h2; subst h3
      rw [← h4] at hrl
      refine ⟨(hheadRec (fun _ => 0) rl hrl hfire).1, ?_⟩
      intro φ us hus
      rw [← hcval₀] at hheadRec
      exact (hheadRec φ rl hrl hfire).2 us hus)
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
    injection heq with h1 _ _ h4
    rw [← h4] at hr
    obtain ⟨w1, w2, w3, w4, w5⟩ := hrulesWF r hr
    refine ⟨w1, by rw [← h1]; exact w2,
      Expr.constsResolve_mono w3, w4, ?_⟩
    intro lvls pins hfr
    exact absurd hfr (w5 lvls pins)
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
    · show denoteClosed cval₀ ⟨projEntry T lps pty nP i rules ::
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
          (projEntry T lps pty nP i rules).name = T'
          from hh.symm)] at hfT'
        exact nomatch (Option.some.inj hfT')
      · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
        rw [Env.find?_cons, if_pos (show
          (projEntry T lps pty nP i rules).name = capsT.etaCtor
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
        have hne2 : ¬(projEntry T lps pty nP i rules).name
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

set_option maxHeartbeats 6400000 in
/-- **One projection field installs.**  The bottom fires at the *base*
environment under `Rn := projModelName T i`; `projConsS` then stores
the entry, and `cvalWith_self` makes the base law's head the installed
constant's valuation. -/
theorem projFnS {μ : CheckMode} {F : Nat} {env' env₁ : Env}
    {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    {blockNames : List Name} (m : EnvS V env')
    (hR : ProjFnR μ F env' m.cval T ctorName lps nP nF i env₁)
    (hinv : ProjPhaseInvS T ctorName nF env' m.cval)
    (hIB : BlockInstalledTT blockNames env' m.cval)
    (hTblock : blockNames.contains T = true)
    (hbshape : ∀ n, blockNames.contains n = true →
      n.isProjFnShape = false)
    (hpinsT : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      EtaPins μ env' T cvT.levelParams capsT)
    (hCblock : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → blockNames.contains capsT.etaCtor = true)
    (hFields : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → capsT.etaFields = nF) :
    ∃ m₁ : EnvS V env₁,
      m₁.cval = cvalWith m.cval (projFnName T i)
        (fun ψ => m.cval (projModelName T i) ψ) ∧
      ProjPhaseInvS T ctorName nF env₁ m₁.cval ∧
      BlockInstalledTT blockNames env₁ m₁.cval := by
  obtain ⟨cvj, mcv, mval, mhint, pty, rhsA, hctor, hfm, hmlps, hpnone,
    hTf, heqf, hptyB, hround, hptyres, hptyb, hptyf, hptylp, hstrip1,
    hilt, hstripP, hbig, henv⟩ := hR
  obtain ⟨cbinders, cbody, hCstrip, hcbodyArity, hcbodyHead, hrhsw,
    hrhsb, hrlp, hrres, hrstrip, hrhsKey, -, hthmpack⟩ := hbig
  obtain ⟨rbinders, hrhsAstrip, hrdomsEq⟩ := hrstrip
  obtain ⟨tcv, tval, hthmE, htlps, hsbodyPin, fvsI, sbodyO, hopen,
    hsidesTy, -, -⟩ := hthmpack
  obtain ⟨sbinders, ℓA, tySlot, hSstrip, hdomsSC⟩ := hsbodyPin
  subst henv
  have hfresh : env'.find? (projFnName T i) = none :=
    Option.isNone_iff_eq_none.mp hpnone
  have hCf : (env'.find? ctorName).isSome = true := by rw [hctor]; rfl
  -- the model projection is not the constructor: the stored kinds
  -- would clash
  have hPCne : projModelName T i ≠ ctorName := by
    intro hh
    rw [hh, hctor] at hfm
    exact nomatch (Option.some.inj hfm)
  -- the pruned projection renaming, and its fixed point at `Rn`
  have hro := projFwd_renameOkT hinv
  have hfRn : (if (env'.find? (projModelName T i)).isSome = true then
      projFwd T ctorName nF (projModelName T i)
      else projModelName T i) = projModelName T i := by
    rw [if_pos (show (env'.find? (projModelName T i)).isSome = true
      from by rw [hfm]; rfl)]
    exact projFwd_model_self hPCne
  have hfCt : (if (env'.find? ctorName).isSome = true then
      projFwd T ctorName nF ctorName else ctorName)
      = ctorName.str "_model" := by
    rw [if_pos hCf]
    unfold projFwd
    by_cases hCT : ctorName = T
    · rw [if_pos hCT, hCT]
    · rw [if_neg hCT, if_pos rfl]
  -- the stored constants' syntactic facts
  obtain ⟨hCw, -, hCres, hCb, -, -, -⟩ := m.wf _ (find?_mem hctor)
  obtain ⟨hSw, -, -, hSb, -, -, -⟩ := m.wf _ (find?_mem hthmE)
  have hClp :
      cvj.type.allLevelParamsDefined cvj.levelParams = true := by
    obtain ⟨-, h2, -⟩ := m.wf _ (find?_mem hctor)
    exact h2
  -- the model constructor, from the phase invariant
  obtain ⟨cvmC, mvalC, hmC, hfCm, hlpsC, -⟩ := hinv.2.1 _ hctor
  -- the statement's opened parts
  obtain ⟨hfvsIlen, hheadEqO, αS, hargs3O⟩ :=
    projStmtParts hilt hSb hopen hSstrip
  have hnPle : nP ≤ fvsI.length := by rw [hfvsIlen]; omega
  -- the two spine facts the bottom's pins need
  have hlargs : (Expr.mkAppN (.const (projModelName T i)
      (lps.map .param))
      (fvsI.take nP ++ [Expr.mkAppN
        (.const (ctorName.str "_model") (cvj.levelParams.map .param))
        (fvsI.take nP ++ fvsI.drop nP)])).getAppArgs
      = fvsI.take nP ++ [Expr.mkAppN
        (.const (ctorName.str "_model") (cvj.levelParams.map .param))
        (fvsI.take nP ++ fvsI.drop nP)] :=
    Expr.getAppArgs_mkAppN _ _
  -- the rhs key, at the base environment
  have hrhsKeyS : ∀ ψ' : Name → Nat, ∃ Rv t,
      denoteClosed m.cval env' ψ' rhsA = some Rv ∧
      ∀ ρ : Nat → V,
        AnnotOkV V ρ Rv ∧ interp V ρ Rv ∈ˢ interp V ρ t := by
    intro ψ'
    obtain ⟨Rv, t, hRv, hInf⟩ := hrhsKey ψ'
    exact ⟨Rv, t, hRv, fun ρ =>
      Infer.sound (m.toHyp ψ') hInf ρ (Sat_nil V ρ)⟩
  -- the statement's front door
  have hthmS : ∀ ψ' : Name → Nat, ∃ t,
      denoteClosed m.cval env' ψ' tcv.type = some t ∧
      ∀ ρ : Nat → V,
        (∃ pv : V, pv ∈ˢ interp V ρ t) ∧ AnnotOkV V ρ t := by
    intro ψ'
    obtain ⟨t, ht, hfacts⟩ :=
      m.mem_type (.thmInfo tcv tval) (find?_mem hthmE) ψ'
    exact ⟨t, ht, fun ρ => ⟨⟨_, (hfacts ρ).1⟩, (hfacts ρ).2⟩⟩
  -- the domain pin, at the pruned renaming
  have hdomsSCp : ∀ (i0 : Nat) (b b' : Name × Expr × BinderMeta),
      i0 < nP + nF → sbinders[i0]? = some b → cbinders[i0]? = some b' →
      b.2.1 = b'.2.1.renameConsts (fun n =>
        if (env'.find? n).isSome = true then
          projFwd T ctorName nF n else n) := by
    intro i0 b b' hi0 hb hb'
    rw [Expr.renameConsts_congr_resolve
      (g := projFwd T ctorName nF)
      (fun n hn => by simp only [hn, if_true]) _
      ((Expr.constsResolve_stripPis (nP + nF) hCstrip hCres).1 b'
        (List.mem_of_getElem? hb'))]
    exact hdomsSC i0 b b' hi0 hb hb'
  -- the pinned left-hand side, named
  obtain ⟨ctorSpine, hctorSpine⟩ : ∃ e, e = Expr.mkAppN
      (.const (ctorName.str "_model") (cvj.levelParams.map .param))
      (fvsI.take nP ++ fvsI.drop nP) := ⟨_, rfl⟩
  obtain ⟨lhsLit, hlhsLit⟩ : ∃ e, e = Expr.mkAppN
      (.const (projModelName T i) (lps.map .param))
      (fvsI.take nP ++ [ctorSpine]) := ⟨_, rfl⟩
  have hargs3 : sbodyO.getAppArgs
      = [αS, lhsLit, fvsI.getD (nP + i) default] := by
    rw [hlhsLit, hctorSpine]; exact hargs3O
  have hlargsE : lhsLit.getAppArgs = fvsI.take nP ++ [ctorSpine] := by
    rw [hlhsLit]; exact Expr.getAppArgs_mkAppN _ _
  have htakeLen : (fvsI.take nP).length = nP := by
    rw [List.length_take]; omega
  have hlhead : lhsLit.getAppFn
      = Expr.const (if (env'.find? (projModelName T i)).isSome = true
        then projFwd T ctorName nF (projModelName T i)
        else projModelName T i) (lps.map .param) := by
    rw [hlhsLit, Expr.getAppFn_mkAppN, hfRn]
    rfl
  have hlarity : lhsLit.getAppArgs.length = nP + 1 := by
    rw [hlargsE]
    simp [htakeLen]
  have hlpre : lhsLit.getAppArgs.take nP = fvsI.take nP := by
    rw [hlargsE]
    exact List.take_left' htakeLen
  have hmaj : lhsLit.getAppArgs.getLastD (.bvar 0) = ctorSpine := by
    rw [hlargsE]
    simp
  have hsidesTyS : ∀ ψ' : Name → Nat,
      IotaSidesTyR μ env' m.cval ψ' (nP + nF) αS lhsLit
        (fvsI.getD (nP + i) default) := by
    intro ψ'
    have h := hsidesTy ψ'
    rw [hargs3] at h
    simpa using h
  obtain ⟨Dc, usc, hcbodyHead'⟩ := hcbodyHead
  -- **the bottom fires, at the base environment**
  have hbot := indBottomProjS (V := V) (Rn := projModelName T i)
    (lps := lps) (tyA := pty) (mI := nP) (rP := nP) (i := i)
    m hro heqf (by rw [hfRn]; exact hfm)
    (show ConstantVal.levelParams
      (ConstantInfo.defnInfo mcv mval mhint).toConstantVal = lps
      from hmlps) hctor
    (by rw [hfCt]; exact hfCm)
    (show ConstantVal.levelParams
      (ConstantInfo.defnInfo cvmC mvalC hmC).toConstantVal
      = cvj.levelParams from hlpsC)
    hCw hCb hClp rfl rfl hilt
    hCstrip hcbodyArity hcbodyHead' hrhsw hrhsb hrhsAstrip hrdomsEq
    hrhsKeyS hSw hSb hthmS hopen hheadEqO hargs3 hlhead hlarity hlpre
    (by rw [hmaj, hctorSpine, hfCt]) rfl hSstrip hdomsSCp hsidesTyS
  -- the installed valuation and its install
  obtain ⟨cval₀, hcval₀⟩ : ∃ c, c = cvalWith m.cval (projFnName T i)
      (fun ψ => m.cval (projModelName T i) ψ) := ⟨_, rfl⟩
  have hag : ∀ n, n ≠ projFnName T i → m.cval n = cval₀ n := by
    intro n hn
    rw [hcval₀, cvalWith_ne hn]
  have hselfA : ∀ ψ : Name → Nat,
      cval₀ (projFnName T i) ψ = m.cval (projModelName T i) ψ := by
    intro ψ
    rw [hcval₀]
    exact congrFun cvalWith_self ψ
  have hiA : Installs env' m.cval cval₀
      (projEntry T lps pty nP i
        [⟨ctorName, nF, nP,
          if Expr.recRulePlain pty nP nP nP then .plain else .inert,
          rhsA⟩]) :=
    Installs.of_fresh hfresh hag
  have hCne : ctorName ≠ projFnName T i := by
    intro hh
    rw [hh, hfresh] at hctor
    exact nomatch hctor
  -- **the bridge**: the base law, read at the installed entry
  have hheadRecS : ∀ (φ : Name → Nat), ∀ rl ∈ [(⟨ctorName, nF, nP,
        if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
        else .inert, rhsA⟩ : RecRule)],
      RecRule.fire rl ≠ .inert →
      RecRuleLawV V ⟨projEntry T lps pty nP i
        [⟨ctorName, nF, nP,
          if Expr.recRulePlain pty nP nP nP then .plain else .inert,
          rhsA⟩] :: env'.consts⟩ cval₀ φ
        (projFnName T i) ⟨projFnName T i, lps, pty⟩ nP nP rl := by
    intro φ rl hrl hfire
    obtain rfl : rl = ⟨ctorName, nF, nP,
        if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
        else .inert, rhsA⟩ := by
      rcases List.mem_cons.mp hrl with h | h
      · exact h
      · exact nomatch h
    -- an `.inert` rule is excluded by the clause's own premise
    have hplainFire : (if Expr.recRulePlain pty nP nP nP then
        RecRuleFire.plain else .inert) = .plain := by
      by_cases hc : Expr.recRulePlain pty nP nP nP = true
      · simp [hc]
      · exact absurd (show RecRule.fire _ = RecRuleFire.inert from by
          simp only [eq_false_of_ne_true hc]; rfl) hfire
    refine ⟨Nat.le_refl _, ?_⟩
    intro us hus
    obtain ⟨RV, hRVden, hRVlaw⟩ := hbot φ us hus
    refine ⟨RV, hiA.denoteUp hRVden, ?_⟩
    intro cvj' cnP' cnF' hfc' usj ρ xs ys TV TVj restR restC hlenX
      hlenY husjlen hlev hplain hnested hidx hTV hTVj hfitR hfitC
    -- the stored constructor is the one the kit named
    obtain ⟨rfl, -, -⟩ : cvj' = cvj ∧ cnP' = nP ∧ cnF' = nF := by
      rw [Env.find?_cons, if_neg (show ¬(projEntry T lps pty nP i
        [⟨ctorName, nF, nP, if Expr.recRulePlain pty nP nP nP then
          .plain else .inert, rhsA⟩]).name = ctorName from
        fun hh => hCne hh.symm), hctor] at hfc'
      obtain ⟨h1, h2, h3⟩ :=
        ConstantInfo.ctorInfo.inj (Option.some.inj hfc')
      exact ⟨h1.symm, h2.symm, h3.symm⟩
    replace hTV := hiA.denoteDown (by
      rw [Expr.constsResolve_instantiateLevelParams]; exact hptyres)
      hTV
    replace hTVj := hiA.denoteDown (by
      rw [Expr.constsResolve_instantiateLevelParams]; exact hCres)
      hTVj
    rw [← hag ctorName hCne] at hfitR ⊢
    rw [hselfA]
    refine hRVlaw usj ρ xs ys TV TVj restR restC hlenX hlenY husjlen
      ?_ (fun i0 h1 h2 => hplain hplainFire i0 h1 h2) hidx hTV hTVj
      hfitR hfitC
    rw [hlev, recFireComparands_plain hplainFire]
  rw [hcval₀] at hheadRecS
  -- the stored rule's own obligations
  have hrulesWFS : ∀ r ∈ [(⟨ctorName, nF, nP,
        if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
        else .inert, rhsA⟩ : RecRule)],
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined lps = true ∧
      (RecRule.rhs r).constsResolve env' = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      ∀ lvls pins, RecRule.fire r ≠ .nested lvls pins := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · refine ⟨hrhsw, hrlp, hrres, hrhsb, ?_⟩
      intro lvls pins
      by_cases hc : Expr.recRulePlain pty nP nP nP = true
      · simp only [hc, if_true]
        exact fun hh => nomatch hh
      · simp only [eq_false_of_ne_true hc]
        exact fun hh => nomatch hh
    · exact nomatch h
  have hheadCtorsS : ∀ r ∈ [(⟨ctorName, nF, nP,
        if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
        else .inert, rhsA⟩ : RecRule)],
      ∃ cvj' cnP' cnF', env'.find? (RecRule.ctor r)
        = some (.ctorInfo cvj' cnP' cnF') := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · exact ⟨cvj, nP, nF, hctor⟩
    · exact nomatch h
  have hnotb : blockNames.contains (projFnName T i) = false := by
    cases hc : blockNames.contains (projFnName T i) with
    | false => rfl
    | true =>
      exact absurd (hbshape _ hc)
        (by rw [show (projFnName T i).isProjFnShape = true from rfl]
            exact fun hh => nomatch hh)
  obtain ⟨m₁, hm₁cval⟩ := projConsS m hfm hmlps hpnone hround hptyres
    hptyb hptyf hptylp hinv hIB hTblock hpinsT hCblock hFields
    hrulesWFS hheadCtorsS hheadRecS
  refine ⟨m₁, hm₁cval, ?_, ?_⟩
  · rw [hm₁cval]
    exact projPhaseInvS_cons rfl hinv hfresh hTf hCf hfm hmlps hilt
      (fun ψ => congrFun cvalWith_self ψ)
      (fun n hn => (cvalWith_ne hn).symm)
  · rw [hm₁cval]
    exact BlockInstalledTT.fresh_cons hIB hnotb hfresh
      (fun n ψ hn => congrFun (cvalWith_ne hn) ψ)

set_option maxHeartbeats 1600000 in
/-- **The projection-function fold.**  The skip branch is a no-op, so
only the install branch moves anything; the block-level premises are
re-established at each step from freshness (`EtaPins.step`) and the
fact that a projection name is never a block name. -/
theorem projInstallS {μ : CheckMode} {F : Nat} {T ctorName : Name}
    {lps : List Name} {nP nF : Nat} {blockNames : List Name}
    (hTblock : blockNames.contains T = true)
    (hbshape : ∀ n, blockNames.contains n = true →
      n.isProjFnShape = false) :
    ∀ (fields : List Nat) {env' : Env} (m : EnvS V env')
      {env₄ : Env} {cval₄ : TConstVal},
      ProjInstallR μ F T ctorName lps nP nF env' m.cval fields env₄
        cval₄ →
      ProjPhaseInvS T ctorName nF env' m.cval →
      BlockInstalledTT blockNames env' m.cval →
      (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
        EtaPins μ env' T cvT.levelParams capsT) →
      (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
        capsT.eta = true → blockNames.contains capsT.etaCtor = true) →
      (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
        capsT.eta = true → capsT.etaFields = nF) →
      ∃ m₄ : EnvS V env₄, m₄.cval = cval₄ ∧
        ProjPhaseInvS T ctorName nF env₄ cval₄ ∧
        BlockInstalledTT blockNames env₄ cval₄ := by
  intro fields
  induction fields with
  | nil =>
    intro env' m env₄ cval₄ h hinv hIB hpinsT hCblock hFields
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m, rfl, hinv, hIB⟩
  | cons i rest ih =>
    intro env' m env₄ cval₄ h hinv hIB hpinsT hCblock hFields
    obtain ⟨env'', cval'', hstep, hrec⟩ := h
    rcases hstep with ⟨hR, rfl⟩ | ⟨hskip, rfl, rfl⟩
    case inr => exact ih m hrec hinv hIB hpinsT hCblock hFields
    -- the install branch
    obtain ⟨m₁, hm₁cval, hinv₁, hIB₁⟩ :=
      projFnS m hR hinv hIB hTblock hbshape hpinsT hCblock hFields
    -- the block-level premises, re-established
    obtain ⟨cvj, mcv, mval, mhint, pty, rhsA, hctor, hfm, hmlps,
      hpnone, hTf, -, -, -, -, -, -, -, -, hilt, -, -, henv⟩ := hR
    have hfresh : env'.find? (projFnName T i) = none :=
      Option.isNone_iff_eq_none.mp hpnone
    have hTne : T ≠ projFnName T i := by
      intro hh
      rw [hh, hfresh] at hTf
      exact nomatch hTf
    have hdown : ∀ (cvT : ConstantVal) (capsT : IndCaps),
        env''.find? T = some (.indInfo cvT capsT) →
        env'.find? T = some (.indInfo cvT capsT) := by
      intro cvT capsT hf
      rw [henv, Env.find?_cons,
        if_neg (fun hh => hTne hh.symm)] at hf
      exact hf
    refine ih m₁ (by rw [hm₁cval]; exact hrec)
      hinv₁ hIB₁
      (fun cvT capsT hf => by
        rw [henv]
        exact EtaPins.step (hpinsT cvT capsT (hdown cvT capsT hf))
          hfresh)
      (fun cvT capsT hf => hCblock cvT capsT (hdown cvT capsT hf))
      (fun cvT capsT hf => hFields cvT capsT (hdown cvT capsT hf))

/-! ## The elimination templates

A template entry exists *precisely because* the field has no
`T._model.proj_i` artifact — so, unlike every other block entry, there
is no model valuation to copy and `cvalModeled` does not apply.  The
install chooses one, and the relation only records that the step is a
fresh-name `cvalWith` extension (dictating the choice there would
freeze an install decision the relation has no business making).

`VExpr.eqE (.sort 0) .prf .prf` is the choice: `eqv_mem_univ` puts it
in `univ 0` — which is what `denote (.sort .zero)` interprets to, the
entry's stored junk type — `AnnotOkV`'s `eqE` clause bottoms out at
two `prf` leaves, and it is closed and level-independent. -/

/-- The valuation an elimination-template entry takes. -/
def templateVal : (Name → Nat) → VExpr :=
  fun _ => .eqE (.sort 0) .prf .prf

set_option maxHeartbeats 1600000 in
/-- **One elimination-template entry installs.** -/
theorem templateConsS {env' : Env} (m : EnvS V env')
    {T : Name} {lps : List Name} {i : Nat} {entry : ProjEntry}
    (hstruct : entry.structName = T) (hidx : entry.idx = i)
    (hnat : entry.native = false)
    (hlps : entry.levelParams = lps)
    (hty : entry.ty = .sort .zero)
    (hpnone : (env'.find? (projFnName T i)).isNone = true)
    (hTnres : reservedBasisNames.contains T = false) :
    ∃ m' : EnvS V ⟨.projInfo entry :: env'.consts⟩,
      m'.cval = cvalWith m.cval (projFnName T i) templateVal := by
  have hname : (ConstantInfo.projInfo entry).name = projFnName T i := by
    show projFnName entry.structName entry.idx = projFnName T i
    rw [hstruct, hidx]
  have hcvA : (ConstantInfo.projInfo entry).toConstantVal
      = ⟨projFnName T i, lps, .sort .zero⟩ := by
    show (⟨projFnName entry.structName entry.idx, entry.levelParams,
      entry.ty⟩ : ConstantVal) = _
    rw [hstruct, hidx, hlps, hty]
  have hfresh :
      env'.find? (ConstantInfo.projInfo entry).name = none := by
    rw [hname]
    exact Option.isNone_iff_eq_none.mp hpnone
  obtain ⟨cval₀, hcval₀⟩ : ∃ c, c = cvalWith m.cval (projFnName T i)
      templateVal := ⟨_, rfl⟩
  have hag : ∀ n, n ≠ (ConstantInfo.projInfo entry).name →
      m.cval n = cval₀ n := by
    intro n hn
    rw [hcval₀, cvalWith_ne (by rw [← hname]; exact hn)]
  have hi : Installs env' m.cval cval₀ (.projInfo entry) :=
    Installs.of_fresh hfresh hag
  have hselfA : ∀ ψ : Name → Nat,
      cval₀ (ConstantInfo.projInfo entry).name ψ
        = VExpr.eqE (.sort 0) .prf .prf := by
    intro ψ
    rw [hname, hcval₀]
    exact congrFun cvalWith_self ψ
  have hnres : reservedBasisNames.contains
      (ConstantInfo.projInfo entry).name = false := by
    rw [hname]; exact reservedBasisNames_not_num _ _
  refine ⟨EnvS.cons m hi ?_ ?_ ?_ ?_ ?_
    (fun cv2 v2 h2 heq => ConstantInfo.noConfusion heq)
    (fun cv2 v2 heq => ConstantInfo.noConfusion heq)
    (fun heq => absurd (hname ▸ heq) (Name.num_ne_str _ _ _ _))
    (fun cv2 mI2 rP2 rules2 heq => ConstantInfo.noConfusion heq)
    (fun cv2 mI2 rP2 rules2 heq => ConstantInfo.noConfusion heq)
    ?_
    (fun cv2 caps2 heq => ConstantInfo.noConfusion heq)
    (fun e2 heq hnat2 => by
      obtain rfl := ConstantInfo.projInfo.inj heq
      rw [hnat] at hnat2
      exact nomatch hnat2)
    ?_
    (fun heq => absurd (hname ▸ heq) (Name.num_ne_str _ _ _ _))
    (fun hres => absurd hres (by rw [hnres]; exact fun h => nomatch h))
    (fun cv2 v2 h2 heq => ConstantInfo.noConfusion heq)
    (fun cv2 v2 h2 heq => ConstantInfo.noConfusion heq)
    (fun cv2 heq => ConstantInfo.noConfusion heq), hcval₀⟩
  · -- `EnvWF`
    refine EnvWF.cons m.wf ⟨?_, ?_, ?_, ?_,
      (fun cv2 v2 h2 heq => ConstantInfo.noConfusion heq),
      (fun cv2 mI2 rP2 rules2 heq => ConstantInfo.noConfusion heq),
      (fun cv2 v2 heq => ConstantInfo.noConfusion heq)⟩ <;>
      rw [hcvA] <;> rfl
  · intro ψ
    rw [hselfA]
    exact ⟨trivial, trivial, trivial⟩
  · intro φ₁ φ₂ _
    rw [hselfA, hselfA]
  · intro ψ ρ
    rw [hselfA]
    exact ⟨trivial, trivial⟩
  · -- the front door: the junk value inhabits `Prop`
    intro φ
    refine ⟨.sort 0, ?_, ?_⟩
    · show denoteClosed cval₀ ⟨.projInfo entry :: env'.consts⟩ φ
        (ConstantInfo.projInfo entry).toConstantVal.type = _
      rw [hcvA]
      show denote cval₀ _ φ 0 (Expr.sort Level.zero) = _
      rw [denote_sort]
      rfl
    · intro ρ
      rw [hselfA, interp_sort, interp_eqE]
      exact ⟨eqv_mem_univ _ _, trivial⟩
  · -- the eta head: a template entry is a `.projInfo`, so nothing
    -- can complete a family through it
    intro T' cvT capsT hfT' hcape hresT hfam hpart
    exfalso
    rcases hpart with hh | hh | ⟨j, hj, hh⟩
    · rw [Env.find?_cons, if_pos hh.symm] at hfT'
      exact nomatch (Option.some.inj hfT')
    · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
      rw [Env.find?_cons, if_pos hh.symm] at hfC
      exact nomatch (Option.some.inj hfC)
    · obtain ⟨-, -, hfP⟩ := hfam
      obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
      rw [Env.find?_cons, if_pos hh.symm] at hf2
      exact nomatch (Option.some.inj hf2)
  · -- the pinned-pair obligation: `T` is not `PSigma'`
    intro i2 e2 heq hpair
    exfalso
    obtain rfl := ConstantInfo.projInfo.inj heq
    rw [hname] at hpair
    have hTps : T = psigmaName := by
      have hh : Name.num (T.str "proj") i
        = Name.num (psigmaName.str "proj") i2 := hpair
      exact (Name.str.inj (Name.num.inj hh).1).1
    rw [hTps] at hTnres
    exact absurd hTnres (by decide)

/-- **The elimination-template fold.**  Nothing but the model
survives it: a template entry carries no artifact, so no block
invariant is claimed of it, and the relation carries no valuation —
the install's choice is `templateVal`. -/
theorem templatesS {T ctorName : Name} {lps : List Name} {nP nF : Nat}
    (hTnres : reservedBasisNames.contains T = false) :
    ∀ (fields : List Nat) {env' : Env} (_m : EnvS V env') {env₂ : Env},
      DeclIndR.TemplatesR T ctorName lps nP nF env' fields env₂ →
      Nonempty (EnvS V env₂) := by
  intro fields
  induction fields with
  | nil =>
    intro env' m env₂ h
    obtain rfl := h
    exact ⟨m⟩
  | cons i rest ih =>
    intro env' m env₂ h
    obtain ⟨env'', hstep, hrec⟩ := h
    rcases hstep with rfl | ⟨entry, hstruct, hidx, hnat, hlps,
      hty, hpnone, rfl⟩
    · exact ih m hrec
    · obtain ⟨m', -⟩ :=
        templateConsS m hstruct hidx hnat hlps hty hpnone hTnres
      exact ih m' hrec

end Setlec.SetR
