import Setlec.TTVerify.DeclIndRecs
import Setlec.TTVerify.IndBottomProj
import Setlec.Verify.Extend.Proj

/-!
# The projection-family install

Transpose of `Setlec/Model/Extend/{Proj,ProjFn}.lean`: the phase
invariant (`ProjPhaseInvT`), one projection-function install
(`checkProjFnTT` — the projection bottom fires here), the artifact
fold, and the elimination-template fold.

## Where the bottom runs

`checkProjFn`'s checks run *before* its recursor is stored, so the kit
lives at the base environment — where the projection's own name has no
valuation.  The assembly therefore instantiates `IndBottomProjTT` with
`Rn := projModelName T i` (the *model's* name, which the statement's
head names anyway) under the *pruned* projection renaming, which fixes
it; the base law's head `cval (T._model.proj_i)` then becomes the
installed constant's valuation by the alias — `cvalAlias`'s defining
equation, at the `EnvTT.cons`.  This is the same base-vs-extended
bridging `proj_rule_eq` does on the set-model side, paid at the cons
instead of inside the per-rule lemma.

## The opened statement (§24's practical note (ii))

`checkProjIota` pins the statement in *strip* form while the bottom
consumes the *opened* form, so the transfer — `openPisAtFvars` is
`Expr.instSeq` at the collected openers, exactly, and the pinned body
computes — is Expr-level computation, sealed here
(`openPisAtFvars_instSeq`, `projStmtParts`).
-/

set_option linter.unusedVariables false

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

variable {F : Nat}

/-! ## The opened statement -/

/-- The opened body is the strip body instantiated at the collected
openers — *exactly*, annotations included (the ErasedEq form is
`openPisAtFvars_stripPis`; the pinned-spine transfers need
equality). -/
theorem openPisAtFvars_instSeq :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr}
      {bs : List (Name × Expr × BinderMeta)} {body₀ : Expr},
      openPisAtFvars k e d = some (fvs, body) →
      e.stripPis k = some (bs, body₀) →
      body = Expr.instSeq fvs (k - 1) body₀ := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body bs body₀ h hs
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, rfl⟩ := hs
    rfl
  | succ k ih =>
    intro e d fvs body bs body₀ h hs
    match e, h with
    | .forallE nm dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar d nm dom))
          (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Expr.stripPis] at hs
        cases hs1 : bodyE.stripPis k with
        | none => rw [hs1] at hs; exact nomatch hs
        | some p1 =>
          rw [hs1] at hs
          simp only [Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hs
          obtain ⟨-, rfl⟩ := hs
          obtain ⟨q1, hq1⟩ := Option.isSome_iff_exists.mp
            (Expr.stripPis_instantiate1_isSome
              (v := .fvar d nm dom) k 0 (by rw [hs1]; rfl))
          obtain ⟨hbody1, -⟩ := Expr.stripPis_instantiate1_eq k 0 hs1 hq1
          have hihb := ih hop (show Expr.stripPis k
            (bodyE.instantiate1 (Expr.fvar d nm dom)) =
              some (q1.1, q1.2) from by rw [hq1])
          rw [Nat.zero_add] at hbody1
          rw [hihb, hbody1]
          show _ = Expr.instSeq (Expr.fvar d nm dom :: p.1) (k + 1 - 1) _
          rw [show Expr.instSeq (Expr.fvar d nm dom :: p.1) (k + 1 - 1)
              p1.2 = Expr.instSeq p.1 (k + 1 - 1 - 1)
              (p1.2.instantiate1 (.fvar d nm dom) (k + 1 - 1)) from rfl,
            Nat.add_sub_cancel]

/-- Indexing a prefix of a list by `range`. -/
theorem range_map_getD_prefix {α : Type _} [Inhabited α] (xs : List α)
    (nP : Nat) (h : nP ≤ xs.length) :
    (List.range nP).map (fun k => xs.getD k default) = xs.take nP := by
  refine List.ext_getElem? ?_
  intro j
  rw [List.getElem?_map]
  rcases Nat.lt_or_ge j nP with hj | hj
  · rw [List.getElem?_range hj, List.getElem?_take_of_lt hj,
      List.getElem?_eq_getElem (show j < xs.length from by omega)]
    simp [List.getD, List.getElem?_eq_getElem
      (show j < xs.length from by omega)]
  · rw [List.getElem?_eq_none (by simpa using hj),
      List.getElem?_eq_none (by simp; omega)]
    rfl

/-- Indexing a suffix of a list by `range`. -/
theorem range_map_getD_suffix {α : Type _} [Inhabited α] (xs : List α)
    (nP nF : Nat) (h : xs.length = nP + nF) :
    (List.range nF).map (fun k => xs.getD (nP + k) default) =
      xs.drop nP := by
  refine List.ext_getElem? ?_
  intro j
  rw [List.getElem?_map]
  rcases Nat.lt_or_ge j nF with hj | hj
  · rw [List.getElem?_range hj, List.getElem?_drop,
      List.getElem?_eq_getElem (show nP + j < xs.length from by omega)]
    simp [List.getD, List.getElem?_eq_getElem
      (show nP + j < xs.length from by omega)]
  · rw [List.getElem?_eq_none (by simpa using hj),
      List.getElem?_eq_none (by simp; omega)]
    rfl

set_option maxHeartbeats 3200000 in
/-- **The pinned projection statement, opened.**  `checkProjIota` pins
the strip-form body; the bottom consumes the opened form; the pinned
spine computes through `Expr.instSeq` at the openers. -/
theorem projStmtParts {sty : Expr} {nP nF i : Nat}
    {fvsO : List Expr} {sbodyO : Expr}
    {sbinders : List (Name × Expr × BinderMeta)}
    {tySlot : Expr} {ℓA : Level} {Pm Cm : Name}
    {lpsE cusE : List Level}
    (hilt : i < nF)
    (hSb : sty.looseBVarsBounded 0 = true)
    (hopenO : openPisAtFvars (nP + nF) sty 0 = some (fvsO, sbodyO))
    (hS_strip : sty.stripPis (nP + nF) = some (sbinders,
      .app (.app (.app (.const eqName [ℓA]) tySlot)
        (Expr.mkAppN (.const Pm lpsE)
          (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
           [Expr.mkAppN (.const Cm cusE)
             (((List.range nP).map fun k =>
                 Expr.bvar (nP + nF - 1 - k)) ++
              ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))])))
        (.bvar (nF - 1 - i)))) :
    fvsO.length = nP + nF ∧
    sbodyO.getAppFn = .const eqName [ℓA] ∧
    ∃ αS, sbodyO.getAppArgs = [αS,
      Expr.mkAppN (.const Pm lpsE)
        (fvsO.take nP ++
         [Expr.mkAppN (.const Cm cusE) (fvsO.take nP ++ fvsO.drop nP)]),
      fvsO.getD (nP + i) default] := by
  have hbody := openPisAtFvars_instSeq (nP + nF) hopenO hS_strip
  obtain ⟨bsS, body₀S, hstripO, hlenO, hIdx, -⟩ :=
    openPisAtFvars_stripPis (nP + nF) hopenO
  have hfvsB : ∀ a ∈ fvsO, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, hjlt, rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨nm, ty, hfj⟩ := hIdx j (by rw [← hlenO]; exact hjlt)
    rw [List.getElem?_eq_getElem hjlt] at hfj
    rw [Option.some.inj hfj]
    rfl
  have hbv : ∀ j, j < nP + nF →
      Expr.instSeq fvsO (nP + nF - 1) (.bvar j) =
        fvsO.getD (nP + nF - 1 - j) default := by
    intro j hj
    have hb := Expr.instSeq_bvar fvsO (nP + nF - 1) j hfvsB (by omega)
      (by rw [hlenO]; omega)
    have hklt : nP + nF - 1 - j < fvsO.length := by rw [hlenO]; omega
    rw [List.getElem?_eq_getElem hklt] at hb
    rw [show fvsO.getD (nP + nF - 1 - j) default =
      fvsO[nP + nF - 1 - j] from by
        simp [List.getD, List.getElem?_eq_getElem hklt]]
    exact (Option.some.inj hb).symm
  have hpre : ((List.range nP).map fun k =>
      Expr.bvar (nP + nF - 1 - k)).map
      (Expr.instSeq fvsO (nP + nF - 1)) = fvsO.take nP := by
    rw [List.map_map,
      show ((Expr.instSeq fvsO (nP + nF - 1)) ∘ fun k =>
          Expr.bvar (nP + nF - 1 - k)) = fun k =>
          Expr.instSeq fvsO (nP + nF - 1) (.bvar (nP + nF - 1 - k))
        from rfl]
    rw [List.map_congr_left (fun k hk => by
      have hklt : k < nP := List.mem_range.mp hk
      rw [hbv (nP + nF - 1 - k) (by omega),
        show nP + nF - 1 - (nP + nF - 1 - k) = k from by omega])]
    exact range_map_getD_prefix fvsO nP (by rw [hlenO]; omega)
  have hsuf : ((List.range nF).map fun k =>
      Expr.bvar (nF - 1 - k)).map
      (Expr.instSeq fvsO (nP + nF - 1)) = fvsO.drop nP := by
    rw [List.map_map,
      show ((Expr.instSeq fvsO (nP + nF - 1)) ∘ fun k =>
          Expr.bvar (nF - 1 - k)) = fun k =>
          Expr.instSeq fvsO (nP + nF - 1) (.bvar (nF - 1 - k))
        from rfl]
    rw [List.map_congr_left (fun k hk => by
      have hklt : k < nF := List.mem_range.mp hk
      rw [hbv (nF - 1 - k) (by omega),
        show nP + nF - 1 - (nF - 1 - k) = nP + k from by omega])]
    exact range_map_getD_suffix fvsO nP nF hlenO
  -- the strip body is a three-argument spine over the equality head
  rw [show (Expr.app (.app (.app (.const eqName [ℓA]) tySlot)
      (Expr.mkAppN (.const Pm lpsE)
        (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const Cm cusE)
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))])))
      (.bvar (nF - 1 - i))) = Expr.mkAppN (.const eqName [ℓA])
      [tySlot,
       Expr.mkAppN (.const Pm lpsE)
        (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const Cm cusE)
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)] from rfl,
    Expr.instSeq_mkAppN,
    Expr.instSeq_eq_self _ _ (show (Expr.const eqName
      [ℓA]).looseBVarsBounded 0 = true from rfl)] at hbody
  refine ⟨hlenO, ?_, ?_⟩
  · rw [hbody, Expr.getAppFn_mkAppN]
    rfl
  · refine ⟨Expr.instSeq fvsO (nP + nF - 1) tySlot, ?_⟩
    rw [hbody, Expr.getAppArgs_mkAppN]
    rw [show (Expr.const eqName [ℓA]).getAppArgs = [] from rfl,
      List.nil_append]
    simp only [List.map_cons, List.map_nil]
    rw [Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (show (Expr.const Pm
        lpsE).looseBVarsBounded 0 = true from rfl),
      List.map_append, hpre]
    simp only [List.map_cons, List.map_nil]
    rw [Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (show (Expr.const Cm
        cusE).looseBVarsBounded 0 = true from rfl),
      List.map_append, hpre, hsuf,
      hbv (nF - 1 - i) (by omega),
      show nP + nF - 1 - (nF - 1 - i) = nP + i from by omega]

/-! ## The phase invariant -/

/-- The projection-phase fold invariant: the parent type and the
constructor still carry their model values, and every installed
projection function carries its `_model.proj_j`'s.  Transpose of
`ProjPhaseInv`. -/
def ProjPhaseInvT (T ctorName : Name) (nF : Nat) (env' : Env)
    (cval : TConstVal) : Prop :=
  (∀ ci, env'.find? T = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (T.str "_model") = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat, cval T ψ = cval (T.str "_model") ψ) ∧
  (∀ ci, env'.find? ctorName = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (ctorName.str "_model") =
        some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        cval ctorName ψ = cval (ctorName.str "_model") ψ) ∧
  (∀ j, j < nF → ∀ ci, env'.find? (projFnName T j) = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (projModelName T j) = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        cval (projFnName T j) ψ = cval (projModelName T j) ψ)

set_option maxHeartbeats 12800000 in
/-- One projection-function install preserves having a derivation
model together with the phase invariant — the projection bottom fires
here.  Transpose of `checkProjFn_sound`; see the module docstring for
where the bottom runs. -/
theorem checkProjFnTT {env' env₁ : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat} {blockNames : List Name}
    (h : checkProjFn mode (fueledOps mode F) env' T ctorName lps nP nF i = .ok env₁)
    (m : EnvTT env')
    (hinv : ProjPhaseInvT T ctorName nF env' m.cval)
    (hIB : BlockInstalledTT blockNames env' m.cval)
    (hTblock : blockNames.contains T = true)
    (hbshape : ∀ n, blockNames.contains n = true →
      n.isProjFnShape = false)
    (hTind : ∃ cvT capsT, env'.find? T = some (.indInfo cvT capsT))
    (hpinsT : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      EtaPins mode env' T cvT.levelParams capsT)
    (hCblock : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → blockNames.contains capsT.etaCtor = true)
    (hFields : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → capsT.etaFields = nF) :
    ∃ m₁ : EnvTT env₁, ProjPhaseInvT T ctorName nF env₁ m₁.cval ∧
      BlockInstalledTT blockNames env₁ m₁.cval ∧
      ∃ ciH : ConstantInfo, env₁ = ⟨ciH :: env'.consts⟩ ∧
        env'.find? ciH.name = none ∧ ciH.name = projFnName T i := by
  obtain ⟨cvj, mcv, hlk, pty, hty, ⟨u0, hshape⟩, hilt, rhsA, hrule,
    ⟨u, hio⟩, henv₁⟩ := checkProjFn_inv h
  obtain ⟨mval, hmmcv, hctor, hfm, hmlps, hpnone, hTf, heqf⟩ :=
    checkProjLookups_inv hlk
  obtain ⟨hptyB, hround, hptyres, hptyb, hptyf, hptylp⟩ :=
    checkProjTy_inv hty
  obtain ⟨raw, rbinders, cbindersR, cbody, hraw, hrawf, hrawb, hann,
    hrlp, hrres, hrb, hrf, hstripR, hC_strip, hdomsB,
    fvsP0, rest00, cdomsP0, crestP0, xFvs0, crest2X0, ldoms0, lrestL0,
    hopenP0, hcinstP0, hdeParsP0, hopenX0, hlinstP0, hdeLamP0,
    rhsTy0, hity0⟩ := checkProjRule_inv hrule
  obtain ⟨tcv, tval, sbinders, cbindersR₂, cbody₂, tySlot, ℓA,
    hthm, htlps, hC_strip₂, hsdomsB, hS_strip,
    fvsO, sbodyO, hopenO, hlhsTyC0, hrhsTyC0, hslot0⟩ :=
    checkProjIota_inv hio
  obtain ⟨rfl, rfl⟩ : cbindersR = cbindersR₂ ∧ cbody = cbody₂ := by
    have hpair := Option.some.inj (hC_strip.symm.trans hC_strip₂)
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  subst henv₁
  -- the projection's model name and its basic disequalities
  obtain ⟨cvTI, capsTI, hfTI⟩ := hTind
  have hpmnT : projModelName T i ≠ T := by
    intro he
    rw [← he, hfm] at hfTI
    exact nomatch (Option.some.inj hfTI)
  have hpmnC : projModelName T i ≠ ctorName := by
    intro he
    rw [← he, hfm] at hctor
    exact nomatch (Option.some.inj hctor)
  have hTneP : T ≠ projFnName T i := by
    intro he
    rw [he, hpnone] at hTf
    exact nomatch hTf
  have hCneP : ctorName ≠ projFnName T i := by
    intro he
    rw [he, hpnone] at hctor
    exact nomatch hctor
  have hPmneP : projModelName T i ≠ projFnName T i := by
    intro he
    rw [he, hpnone] at hfm
    exact nomatch hfm
  -- the pruned projection renaming and its facts
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Name → Name, f₀ = fun n =>
      if (env'.find? n).isSome then projFwd T ctorName nF n else n :=
    ⟨_, rfl⟩
  have hfound : ∀ n (ci₂ : ConstantInfo), env'.find? n = some ci₂ →
      (∃ ci', env'.find? (projFwd T ctorName nF n) = some ci' ∧
        ci'.toConstantVal.levelParams = ci₂.toConstantVal.levelParams) ∧
      (∀ ψ : Name → Nat,
        m.cval (projFwd T ctorName nF n) ψ = m.cval n ψ) := by
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
    cases hfind : (List.range nF).find? (fun j => n == projFnName T j) with
    | none => exact ⟨⟨ci₂, hf₂, rfl⟩, fun ψ => rfl⟩
    | some j =>
      have hjlt : j < nF :=
        List.mem_range.mp (List.mem_of_find?_eq_some hfind)
      have hprop' : (n == projFnName T j) = true := by
        simpa using List.find?_some hfind
      have hn : n = projFnName T j := eq_of_beq hprop'
      subst hn
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ :=
        hinv.2.2 j hjlt ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
  have hro : RenameOkT m.cval env' f₀ := by
    refine ⟨?_, ?_, ?_⟩
    · intro n ci₂ hf₂
      rw [hf₀]
      dsimp only
      rw [if_pos (show (env'.find? n).isSome = true by rw [hf₂]; rfl)]
      exact (hfound n ci₂ hf₂).1
    · intro n hf₂
      rw [hf₀]
      dsimp only
      rw [if_neg (show ¬(env'.find? n).isSome = true by
        rw [hf₂]; exact fun hx => nomatch hx)]
      exact hf₂
    · intro n ψ
      rw [hf₀]
      dsimp only
      cases hf₂ : env'.find? n with
      | none =>
        rw [if_neg (show ¬(none : Option ConstantInfo).isSome = true
          from fun hx => nomatch hx)]
      | some ci₂ =>
        rw [if_pos (show (some ci₂ : Option ConstantInfo).isSome = true
          from rfl)]
        exact (hfound n ci₂ hf₂).2 ψ
  have hf0stored : ∀ n, (env'.find? n).isSome = true →
      f₀ n = projFwd T ctorName nF n := by
    intro n hn
    rw [hf₀]
    dsimp only
    rw [if_pos hn]
  have hf0pmn : f₀ (projModelName T i) = projModelName T i := by
    rw [hf0stored _ (by rw [hfm]; rfl)]
    unfold projFwd
    try dsimp only
    rw [if_neg hpmnT, if_neg hpmnC]
    cases hfind : (List.range nF).find?
        (fun j => projModelName T i == projFnName T j) with
    | none => rfl
    | some j =>
      exfalso
      have hprop' : (projModelName T i == projFnName T j) = true := by
        simpa using List.find?_some hfind
      exact Name.num_ne_str _ _ _ _ (eq_of_beq hprop').symm
  have hf0ctor : f₀ ctorName = ctorName.str "_model" := by
    rw [hf0stored _ (by rw [hctor]; rfl)]
    unfold projFwd
    try dsimp only
    by_cases hCT : ctorName = T
    · exfalso
      rw [hCT, hfTI] at hctor
      exact nomatch (Option.some.inj hctor)
    · rw [if_neg hCT, if_pos rfl]
  -- wf facts
  obtain ⟨hSw, -, -, hSb, -, -, -⟩ := m.wf _ (find?_mem hthm)
  obtain ⟨hCw, hClp, hCres, hCb, -, -, -⟩ := m.wf _ (find?_mem hctor)
  -- the statement, opened
  have hSwT : tcv.type.hasFvar = false := hSw
  have hSbT : tcv.type.looseBVarsBounded 0 = true := hSb
  obtain ⟨hfvsOlen, hheadEqO, αS, hargs3O⟩ :=
    projStmtParts hilt hSbT hopenO hS_strip
  -- the constructor model's stored facts
  obtain ⟨cvmC, mvalC, hmC, hfmC, hlpsC2, -⟩ := hinv.2.1 _ hctor
  have hlpsC : cvmC.levelParams = cvj.levelParams := hlpsC2
  have hfCm : env'.find? (f₀ ctorName) =
      some (.defnInfo cvmC mvalC hmC) := by
    rw [hf0ctor]
    exact hfmC
  -- the projection model's stored facts, at the renamed head
  have hfRm : env'.find? (f₀ (projModelName T i)) =
      some (.defnInfo mcv mval hmmcv) := by
    rw [hf0pmn]
    exact hfm
  -- the statement's pinned pieces at the bottom's spelling
  have hlhs : sbodyO.getAppArgs.getD 1 (.bvar 0) =
      Expr.mkAppN (.const (projModelName T i) (lps.map .param))
        (fvsO.take nP ++
         [Expr.mkAppN (.const (ctorName.str "_model")
             (cvj.levelParams.map .param))
           (fvsO.take nP ++ fvsO.drop nP)]) := by
    rw [hargs3O]
    rfl
  have hrhs : sbodyO.getAppArgs.getD 2 (.bvar 0) =
      fvsO.getD (nP + i) default := by
    rw [hargs3O]
    rfl
  have hαS : sbodyO.getAppArgs.getD 0 (.bvar 0) = αS := by
    rw [hargs3O]
    rfl
  have htakelen : (fvsO.take nP).length = nP := by
    rw [List.length_take, hfvsOlen]
    omega
  have hlheadO : (Expr.mkAppN (.const (projModelName T i)
      (lps.map .param))
      (fvsO.take nP ++
       [Expr.mkAppN (.const (ctorName.str "_model")
           (cvj.levelParams.map .param))
         (fvsO.take nP ++ fvsO.drop nP)])).getAppFn =
      Expr.const (f₀ (projModelName T i)) (lps.map .param) := by
    rw [Expr.getAppFn_mkAppN, hf0pmn]
    rfl
  have hlargsO : (Expr.mkAppN (.const (projModelName T i)
      (lps.map .param))
      (fvsO.take nP ++
       [Expr.mkAppN (.const (ctorName.str "_model")
           (cvj.levelParams.map .param))
         (fvsO.take nP ++ fvsO.drop nP)])).getAppArgs =
      fvsO.take nP ++
       [Expr.mkAppN (.const (ctorName.str "_model")
           (cvj.levelParams.map .param))
         (fvsO.take nP ++ fvsO.drop nP)] := by
    rw [Expr.getAppArgs_mkAppN]
    rfl
  have hlarityO : (fvsO.take nP ++
      [Expr.mkAppN (.const (ctorName.str "_model")
          (cvj.levelParams.map .param))
        (fvsO.take nP ++ fvsO.drop nP)]).length = nP + 1 := by
    rw [List.length_append, htakelen]
    rfl
  have hlpreO : (fvsO.take nP ++
      [Expr.mkAppN (.const (ctorName.str "_model")
          (cvj.levelParams.map .param))
        (fvsO.take nP ++ fvsO.drop nP)]).take nP = fvsO.take nP := by
    rw [List.take_append_of_le_length (Nat.le_of_eq htakelen.symm),
      List.take_take]
    simp
  have hmajO : (fvsO.take nP ++
      [Expr.mkAppN (.const (ctorName.str "_model")
          (cvj.levelParams.map .param))
        (fvsO.take nP ++ fvsO.drop nP)]).getLastD (.bvar 0) =
      Expr.mkAppN (.const (f₀ ctorName) (cvj.levelParams.map .param))
        (fvsO.take nP ++ fvsO.drop nP) := by
    rw [hf0ctor, List.getLastD_eq_getLast?, List.getLast?_append]
    rfl
  -- the statement's telescope domains are the constructor's, renamed
  have hdomsSC : PiDomsRenEqT f₀ (nP + nF) cvj.type tcv.type := by
    have hdomres :=
      (Expr.constsResolve_stripPis (nP + nF) hC_strip hCres).1
    refine PiDomsRenEqT.of_pointwise (nP + nF) hC_strip hS_strip ?_
    intro k b₁ b₂ hb₁ hb₂
    have hk : k < nP + nF := by
      rcases Nat.lt_or_ge k (nP + nF) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by
          rw [Expr.stripPis_length _ hC_strip]; omega)] at hb₁
        exact nomatch hb₁
    have hkfwd := domsMatchAux_inv hsdomsB hk
      (by rw [Nat.zero_add]; exact hb₂) (by rw [Nat.zero_add]; exact hb₁)
    show Expr.ErasedEq ((b₁.2.1).renameConsts f₀) b₂.2.1
    rw [hkfwd]
    rw [Expr.renameConsts_congr_resolve (g := projFwd T ctorName nF)
      hf0stored _ (hdomres b₁ (List.mem_of_getElem? hb₁))]
    exact Expr.ErasedEq.rfl _
  -- the rule's binder domains are the constructor's
  have hrdomsEq : ∀ (i0 : Nat) (b b' : Name × Expr × BinderMeta),
      i0 < nP + nF → rbinders[i0]? = some b →
      cbindersR[i0]? = some b' → b.2.1 = b'.2.1 := by
    intro i0 b b' hi0 hb hb'
    exact domsMatchAux_inv hdomsB hi0
      (by rw [Nat.zero_add]; exact hb) (by rw [Nat.zero_add]; exact hb')
  -- the theorem's typing
  have hthmty : ∀ ψ' : Name → Nat, ∃ pv t,
      denoteClosed m.cval env' ψ' tcv.type = some t ∧
      HasType [] pv t := by
    intro ψ'
    obtain ⟨t, ht, hd⟩ := m.has_type _ (find?_mem hthm) ψ'
    exact ⟨_, t, ht, hd⟩
  -- the fvsP prefix is whole
  have hfvsP0len : fvsP0.length = nP := by
    obtain ⟨-, -, -, hlen, -, -⟩ :=
      openPisAtFvars_stripPis nP hopenP0
    exact hlen
  have htakeP : fvsP0.take nP = fvsP0 :=
    List.take_of_length_le (Nat.le_of_eq hfvsP0len)
  -- the bottom fires
  have hbot := IndBottomProjTT (F := F) (Rn := projModelName T i)
    (lps := lps) (mI := nP) (rP := nP) m checkStepTT hro heqf
    hptyf hptyb hfRm (show (ConstantInfo.defnInfo mcv mval
      hmmcv).toConstantVal.levelParams = lps from hmlps)
    hctor hfCm (show (ConstantInfo.defnInfo cvmC mvalC
      hmC).toConstantVal.levelParams = cvj.levelParams from hlpsC)
    hCw hCb hClp rfl rfl hilt hrf hrb hity0 hSwT hSbT hthmty
    hopenO hheadEqO hargs3O
    hlheadO
    (by rw [hlargsO]; exact hlarityO)
    (by rw [hlargsO]; exact hlpreO)
    (by rw [hlargsO]; exact hmajO)
    hC_strip hdomsSC rfl hstripR
    (fun i0 b b' hi0 hb hb' => hrdomsEq i0 b b' hi0 hb hb')
    hopenP0 (by rw [htakeP]; exact hcinstP0)
    (by rw [htakeP]; exact hdeParsP0)
    (by rw [hlhs] at hlhsTyC0; rw [hαS] at hlhsTyC0; exact hlhsTyC0)
    (by rw [hrhs] at hrhsTyC0; rw [hαS] at hrhsTyC0; exact hrhsTyC0)
    (by rw [hαS] at hslot0; exact (hslot0 rfl))
  -- the stored rule and constant
  have hnresP : reservedBasisNames.contains (projFnName T i) = false :=
    reservedBasisNames_not_num _ _
  have hheadname : (ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
      [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then
        RecRuleFire.plain else .inert), rhsA⟩]).name =
      projFnName T i := rfl
  have hnotb : blockNames.contains (projFnName T i) = false := by
    cases hc : blockNames.contains (projFnName T i) with
    | false => rfl
    | true =>
      have hsh := hbshape _ hc
      rw [show (projFnName T i).isProjFnShape = true from rfl] at hsh
      exact nomatch hsh
  have hnamePmn : mcv.name = projModelName T i := by
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
      List.find?_some hfm
  have hag : ∀ n, n ≠ projFnName T i →
      m.cval n = cvalAlias m.cval (projFnName T i) (projModelName T i) n :=
    fun n hn => (cvalAlias_ne hn).symm
  have hi : Installs env' m.cval
      (cvalAlias m.cval (projFnName T i) (projModelName T i))
      (.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then
          RecRuleFire.plain else .inert), rhsA⟩]) :=
    Installs.of_fresh hpnone hag
  -- the projection type denotes to the model's
  have hptyDen : ∀ ψ : Name → Nat,
      denoteClosed m.cval env' ψ pty =
      denoteClosed m.cval env' ψ mcv.type := by
    intro ψ
    show denote m.cval env' ψ 0 pty = denote m.cval env' ψ 0 mcv.type
    rw [← hround,
      ← Expr.renameConsts_congr_resolve (g := projFwd T ctorName nF)
        hf0stored pty hptyres]
    exact (denote_renameConsts hro pty 0).symm
  have hkey : ∀ ψ : Name → Nat, ∃ t,
      denoteClosed m.cval env' ψ pty = some t ∧
      HasType [] (m.cval (projModelName T i) ψ) t := by
    intro ψ
    obtain ⟨t, ht, hd⟩ := m.has_type _ (find?_mem hfm) ψ
    refine ⟨t, ?_, ?_⟩
    · rw [hptyDen ψ]
      exact ht
    · rw [← hnamePmn]
      exact hd
  -- the family-completion discharge (the model's `hheadEtaP` block)
  have hheadEtaP : ∀ (T' : Name) (cvT : ConstantVal) (capsT : IndCaps),
      (⟨ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then
          RecRuleFire.plain else .inert), rhsA⟩] :: env'.consts⟩ : Env).find? T' = some (ConstantInfo.indInfo cvT capsT) →
      capsT.eta = true → reservedBasisNames.contains T' = false →
      EtaFamilyStoredT (⟨ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then
          RecRuleFire.plain else .inert), rhsA⟩] :: env'.consts⟩ : Env) T' capsT →
      (T' = projFnName T i ∨ capsT.etaCtor = projFnName T i ∨
        ∃ j, j < capsT.etaFields ∧ projFnName T' j = projFnName T i) →
      EtaLawTT (⟨ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then
          RecRuleFire.plain else .inert), rhsA⟩] :: env'.consts⟩ : Env)
        (cvalAlias m.cval (projFnName T i) (projModelName T i))
        T' cvT capsT := by
    intro T' cvT capsT hfT' hcape hresT hfam hpart
    rcases hpart with rfl | hC | ⟨j, hj, hP⟩
    · exfalso
      rw [Env.find?_cons, if_pos hheadname] at hfT'
      exact nomatch (Option.some.inj hfT')
    · exfalso
      obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
      rw [hC, Env.find?_cons, if_pos hheadname] at hfC
      exact nomatch (Option.some.inj hfC)
    · -- the family completes here
      have hh' : Name.num (T'.str "proj") j =
          Name.num (T.str "proj") i := hP
      injection hh' with hp hij
      injection hp with hT hs
      obtain rfl : i = j := hij.symm
      obtain rfl : T = T' := hT.symm
      have hfT'' : env'.find? T = some (.indInfo cvT capsT) := by
        rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.recInfo
          ⟨projFnName T i, lps, pty⟩ nP nP [⟨ctorName, nF, nP,
            (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
              else .inert), rhsA⟩]).name = T from
          fun hh => hTneP hh.symm)] at hfT'
        exact hfT'
      have hpins₁ : EtaPins mode (⟨ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then
          RecRuleFire.plain else .inert), rhsA⟩] :: env'.consts⟩ : Env) T cvT.levelParams capsT :=
        EtaPins.step (hpinsT cvT capsT hfT'') hpnone
      have hI₁ : BlockInstalledTT blockNames (⟨ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then
          RecRuleFire.plain else .inert), rhsA⟩] :: env'.consts⟩ : Env)
          (cvalAlias m.cval (projFnName T i) (projModelName T i)) :=
        BlockInstalledTT.fresh_cons hIB hnotb hpnone
          (fun n ψ hn => by
            rw [cvalAlias_ne (show n ≠ projFnName T i from hn)])
      have hvp : ValParams (⟨ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then
          RecRuleFire.plain else .inert), rhsA⟩] :: env'.consts⟩ : Env)
          (cvalAlias m.cval (projFnName T i) (projModelName T i)) := by
        intro n ci₂ hf ψ₁ ψ₂ hψ
        by_cases hn : n = projFnName T i
        · subst hn
          rw [Env.find?_cons, if_pos hheadname] at hf
          obtain rfl := Option.some.inj hf
          rw [cvalAlias_self]
          refine m.val_params _ _ hfm ψ₁ ψ₂ ?_
          intro p hp'
          refine hψ p ?_
          rw [show (ConstantInfo.defnInfo mcv mval
            hmmcv).toConstantVal = mcv from rfl] at hp'
          show p ∈ lps
          rw [← hmlps]
          exact hp'
        · rw [Env.find?_cons, if_neg (fun hh => hn hh.symm)] at hf
          rw [cvalAlias_ne hn]
          exact m.val_params n ci₂ hf ψ₁ ψ₂ hψ
      obtain ⟨cvmT', mvalT', hmT', hfmT', hlpsT', hrenT', hvT'⟩ :=
        hIB T hTblock _ hfT''
      obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
      have hCb : blockNames.contains capsT.etaCtor = true :=
        hCblock cvT capsT hfT'' hcape
      have hCne : capsT.etaCtor ≠ projFnName T i := by
        intro hh
        have hCshape := hbshape _ hCb
        rw [hh] at hCshape
        rw [show (projFnName T i).isProjFnShape = true from rfl]
          at hCshape
        exact nomatch hCshape
      have hfC' : env'.find? capsT.etaCtor =
          some (.ctorInfo cvC capsT.etaParams capsT.etaFields) := by
        rw [Env.find?_cons, if_neg (fun hh => hCne hh.symm)] at hfC
        exact hfC
      obtain ⟨cvmC', mvalC', hmC', hfmC', hlpsCB, -, hvC'⟩ :=
        hIB capsT.etaCtor hCb _ hfC'
      -- the field count is this family's
      have hEF : capsT.etaFields = nF := hFields cvT capsT hfT'' hcape
      refine modeledCapsEtaTT
        (ci := .recInfo ⟨projFnName T i, lps, pty⟩ nP nP
          [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then
            RecRuleFire.plain else .inert), rhsA⟩]) m hpnone hnresP
        (Or.inr (Or.inr ⟨_, _, _, _, rfl⟩))
        (fun n hn => cvalAlias_ne hn)
        (cvalAlias_closed m.cval_closed) hvp hI₁ hcape hpins₁ ?_ ?_
        ?_ ?_ ?_ ?_ ?_
      · intro cvmT mvalT hm2 hfm₁
        rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.recInfo
          ⟨projFnName T i, lps, pty⟩ nP nP [⟨ctorName, nF, nP,
            (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
              else .inert), rhsA⟩]).name = T.str "_model" from
          fun hh => Name.num_ne_str _ _ _ _ hh)] at hfm₁
        rw [hfmT'] at hfm₁
        obtain h1 := Option.some.inj hfm₁
        injection h1 with e1 e2 e3
        subst e1
        exact hrenT'
      · obtain ⟨-, -, h3, -⟩ := m.wf _ (find?_mem hfT'')
        exact Expr.constsResolve_mono h3
      · intro ψ
        rw [hheadname]
        rw [cvalAlias_ne hTneP,
          cvalAlias_ne (show T.str "_model" ≠ projFnName T i from
            fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hvT' ψ
      · intro ψ
        rw [hheadname]
        rw [cvalAlias_ne hCne,
          cvalAlias_ne (show capsT.etaCtor.str "_model" ≠
            projFnName T i from
            fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hvC' ψ
      · intro j' hj' ψ
        rw [hheadname]
        by_cases hji : j' = i
        · rw [hji]
          rw [cvalAlias_self,
            cvalAlias_ne (show projModelName T i ≠ projFnName T i from
              fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        · obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j' hj'
          have hne2 : projFnName T j' ≠ projFnName T i := by
            intro hh
            have hh2 : Name.num (T.str "proj") j' =
                Name.num (T.str "proj") i := hh
            injection hh2 with hp2 hij2
            exact hji hij2
          have hf2' : env'.find? (projFnName T j') =
              some (.recInfo cv2 mI2 rP2 rules2) := by
            rw [Env.find?_cons, if_neg (fun hh => hne2 hh.symm)] at hf2
            exact hf2
          have hjnF : j' < nF := by
            rw [← hEF]
            exact hj'
          obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ :=
            hinv.2.2 j' hjnF _ hf2'
          rw [cvalAlias_ne hne2,
            cvalAlias_ne (show projModelName T j' ≠ projFnName T i from
              fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
          exact hv₂ ψ
      · -- the capability constructor's stored level parameters
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
          ⟨cvmC2, mvalC2, hmC2, hCmE, hCmlpsE⟩, -⟩ := hpins₁.1 hcape
        rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.recInfo
          ⟨projFnName T i, lps, pty⟩ nP nP [⟨ctorName, nF, nP,
            (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
              else .inert), rhsA⟩]).name =
            capsT.etaCtor.str "_model" from
          fun hh => Name.num_ne_str _ _ _ _ hh)] at hCmE
        rw [hfmC'] at hCmE
        obtain heq := Option.some.inj hCmE
        injection heq with e1 e2 e3
        subst e1
        unfold levelParamsAt
        rw [hfC]
        show cvC.levelParams = cvT.levelParams
        rw [show (ConstantInfo.ctorInfo cvC capsT.etaParams
          capsT.etaFields).toConstantVal = cvC from rfl] at hlpsCB
        rw [← hlpsCB]
        exact hCmlpsE
      · -- the projection functions' stored level parameters
        intro j' hj'
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
          hPjE, -⟩ := hpins₁.1 hcape
        obtain ⟨cvmj, mvalj, hmj, hfj, hjlps⟩ := hPjE j' hj'
        by_cases hji : j' = i
        · subst hji
          unfold levelParamsAt
          rw [Env.find?_cons, if_pos hheadname]
          show lps = cvT.levelParams
          rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.recInfo
            ⟨projFnName T j', lps, pty⟩ nP nP [⟨ctorName, nF, nP,
              (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
                else .inert), rhsA⟩]).name = projModelName T j' from
            fun hh => Name.num_ne_str _ _ _ _ hh)] at hfj
          rw [hfm] at hfj
          obtain heq := Option.some.inj hfj
          injection heq with e1 e2 e3
          subst e1
          rw [← hmlps]
          exact hjlps
        · obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j' hj'
          have hne2 : projFnName T j' ≠ projFnName T i := by
            intro hh
            have hh2 : Name.num (T.str "proj") j' =
                Name.num (T.str "proj") i := hh
            injection hh2 with hp2 hij2
            exact hji hij2
          have hf2' : env'.find? (projFnName T j') =
              some (.recInfo cv2 mI2 rP2 rules2) := by
            rw [Env.find?_cons, if_neg (fun hh => hne2 hh.symm)] at hf2
            exact hf2
          have hjnF : j' < nF := by
            rw [← hEF]
            exact hj'
          obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ :=
            hinv.2.2 j' hjnF _ hf2'
          rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.recInfo
            ⟨projFnName T i, lps, pty⟩ nP nP [⟨ctorName, nF, nP,
              (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
                else .inert), rhsA⟩]).name = projModelName T j' from
            fun hh => Name.num_ne_str _ _ _ _ hh)] at hfj
          rw [hfm₂] at hfj
          obtain heq := Option.some.inj hfj
          injection heq with e1 e2 e3
          subst e1
          unfold levelParamsAt
          rw [Env.find?_cons, if_neg (fun hh => hne2 hh.symm), hf2']
          show cv2.levelParams = cvT.levelParams
          rw [show (ConstantInfo.recInfo cv2 mI2 rP2
            rules2).toConstantVal.levelParams = cv2.levelParams
            from rfl] at hlps₂
          rw [← hlps₂]
          exact hjlps
  -- the install
  obtain ⟨m₁, hcval₁⟩ : ∃ m₁ : EnvTT
      ⟨ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then
          RecRuleFire.plain else .inert), rhsA⟩] :: env'.consts⟩,
      m₁.cval = cvalAlias m.cval (projFnName T i) (projModelName T i) := by
    refine ⟨EnvTT.cons m hi (EnvWF.cons m.wf ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      hheadEtaP ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩
    · -- ConstWF of the new degenerate recursor
      refine ⟨hptyf, hptylp, Expr.constsResolve_mono hptyres, hptyb,
        ?_, ?_, ?_⟩
      · intro cv2 v2 h2 heq
        exact nomatch heq
      · intro cv2 mI' rP' rules'' heq r hr
        injection heq with e1 e2 e3 e4
        subst e4
        rcases List.mem_cons.mp hr with rfl | hr
        · refine ⟨hrf, ?_, Expr.constsResolve_mono hrres, hrb, ?_⟩
          · rw [← e1]
            exact hrlp
          · intro lvls pins hcon
            cases hcond : Expr.recRulePlain pty nP nP nP <;>
              simp [hcond] at hcon
        · exact absurd hr List.not_mem_nil
      · intro cv2 v2 heq
        exact nomatch heq
    · -- the valuation is closed
      intro ψ
      rw [hheadname, cvalAlias_self]
      exact m.cval_closed _ ψ
    · -- it reads only the declared parameters
      intro φ₁ φ₂ hp
      rw [hheadname, cvalAlias_self]
      refine m.val_params _ _ hfm φ₁ φ₂ ?_
      intro p hp'
      refine hp p ?_
      rw [show (ConstantInfo.defnInfo mcv mval
        hmmcv).toConstantVal = mcv from rfl] at hp'
      show p ∈ lps
      rw [← hmlps]
      exact hp'
    · -- and it has a derivation of the projection type
      intro φ
      obtain ⟨t, ht, hd⟩ := hkey φ
      refine ⟨t, hi.denoteUp ht, ?_⟩
      rw [hheadname, cvalAlias_self]
      exact hd
    · intro cv2 v2 h2 heq φ
      exact nomatch heq
    · intro cv2 v2 heq φ
      exact nomatch heq
    · -- `Empty` is reserved
      intro hE
      rw [hheadname] at hE
      rw [hE] at hnresP
      exact absurd hnresP (by decide)
    · -- the rule's constructor is stored
      intro cv2 mI' rP' rules'' heq r hr
      injection heq with e1 e2 e3 e4
      subst e4
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨cvj, nP, nF, hctor⟩
      · exact absurd hr List.not_mem_nil
    · -- **the fold obligation: the projection bottom's law**
      intro cv2 mI' rP' rules'' heq rl hrl hfire
      injection heq with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      obtain rfl : rl = ⟨ctorName, nF, nP,
          (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
            else .inert), rhsA⟩ := by
        rcases List.mem_cons.mp hrl with h' | h'
        · exact h'
        · exact absurd h' List.not_mem_nil
      by_cases hpl : Expr.recRulePlain pty nP nP nP = true
      case neg =>
        exfalso
        refine hfire ?_
        show (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
          else .inert) = .inert
        rw [if_neg hpl]
      have hfireEq : RecRule.fire (⟨ctorName, nF, nP,
          (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
            else .inert), rhsA⟩ : RecRule) = .plain := by
        show (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
          else .inert) = .plain
        rw [if_pos hpl]
      refine ⟨Nat.le_refl nP, ?_⟩
      intro φ d us hlenU
      have hlenU' : us.length = lps.length := hlenU
      obtain ⟨RV, hRV, hlaw⟩ := hbot φ d us hlenU'
      refine ⟨RV, hi.denoteUp hRV, ?_⟩
      intro cvj' cnP' cnF' hctor₁
      have hctorS : env'.find? ctorName =
          some (.ctorInfo cvj' cnP' cnF') := by
        rw [show RecRule.ctor (⟨ctorName, nF, nP,
            (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
              else .inert), rhsA⟩ : RecRule) = ctorName from rfl] at hctor₁
        rw [Env.find?_cons, if_neg (fun hh =>
          hCneP (hheadname ▸ hh).symm)] at hctor₁
        exact hctor₁
      obtain ⟨g1, g2, g3⟩ : cvj = cvj' ∧ nP = cnP' ∧ nF = cnF' := by
        rw [hctor] at hctorS
        have h0 := Option.some.inj hctorS
        injection h0 with a1 a2 a3
        exact ⟨a1, a2, a3⟩
      subst g1; subst g2; subst g3
      intro Δ usj xs ys TV TVj restR restC hlenX hlenY hlenJ hlev hpar
        hparN hidx hTV hTVj hfitR hfitC
      rw [recFireComparands_plain hfireEq] at hlev
      have hpar' := hpar hfireEq
      rw [show RecRule.ctorParams (⟨ctorName, nF, nP,
          (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
            else .inert), rhsA⟩ : RecRule) = nP from rfl] at hpar'
      rw [show RecRule.ctorParams (⟨ctorName, nF, nP,
          (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
            else .inert), rhsA⟩ : RecRule) = nP from rfl,
        show RecRule.nfields (⟨ctorName, nF, nP,
          (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
            else .inert), rhsA⟩ : RecRule) = nF from rfl] at hlenY
      rw [show RecRule.ctorParams (⟨ctorName, nF, nP,
          (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
            else .inert), rhsA⟩ : RecRule) = nP from rfl] at hidx
      -- premises down to the base
      have hTV₀ : denote m.cval env' φ d
          (pty.instantiateLevelParams lps us) = some TV := by
        refine hi.denoteDown ?_ hTV
        rw [Expr.constsResolve_instantiateLevelParams]
        exact hptyres
      have hTVj₀ : denote m.cval env' φ d
          (cvj.type.instantiateLevelParams cvj.levelParams usj)
          = some TVj := by
        refine hi.denoteDown ?_ hTVj
        rw [Expr.constsResolve_instantiateLevelParams]
        exact hCres
      rw [show RecRule.ctor (⟨ctorName, nF, nP,
          (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
            else .inert), rhsA⟩ : RecRule) = ctorName from rfl,
        cvalAlias_ne hCneP] at hfitR
      have hout := hlaw Δ usj xs ys TV TVj restR restC
        hlenX hlenY hlenJ hlev hpar' hidx hTV₀ hTVj₀ hfitR hfitC
      rw [hheadname, cvalAlias_self,
        show RecRule.ctor (⟨ctorName, nF, nP,
          (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
            else .inert), rhsA⟩ : RecRule) = ctorName from rfl,
        cvalAlias_ne hCneP,
        show RecRule.ctorParams (⟨ctorName, nF, nP,
          (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain
            else .inert), rhsA⟩ : RecRule) = nP from rfl]
      exact hout
    · -- no unit-like family is installed
      intro cv2 caps2 heq
      exact nomatch heq
    · -- the residual head is refuted by kind
      intro T' cvT capsT cvC hfT hcape hTres hCres' hfC hor
      exfalso
      rcases hor with rfl | hC
      · rw [Env.find?_cons, if_pos rfl] at hfT
        exact nomatch (Option.some.inj hfT)
      · rw [hC, Env.find?_cons, if_pos rfl] at hfC
        exact nomatch (Option.some.inj hfC)
    · intro entry heq
      exact nomatch heq
    · intro i' entry heq
      exact nomatch heq
    · -- `Eq` is reserved
      intro hE
      rw [hheadname] at hE
      rw [hE] at hnresP
      exact absurd hnresP (by decide)
    · -- the projection name is not reserved
      intro hres
      rw [hheadname] at hres
      rw [hres] at hnresP
      exact nomatch hnresP
    · intro cv2 v2 hint2 heq
      exact nomatch heq
    · intro cv2 v2 hint2 heq
      exact nomatch heq
    · intro cv2 heq
      exact nomatch heq
  -- the phase invariants at the extension
  have hfindNe : ∀ n : Name, n ≠ projFnName T i →
      (⟨ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then
          RecRuleFire.plain else .inert), rhsA⟩] ::
        env'.consts⟩ : Env).find? n = env'.find? n := by
    intro n hn
    rw [Env.find?_cons, if_neg (fun hh => hn (hheadname ▸ hh).symm)]
  refine ⟨m₁, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- the parent type's clause
    intro ci₂ hf₂
    rw [hfindNe T hTneP] at hf₂
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.1 ci₂ hf₂
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, ?_⟩
    · rw [hfindNe (T.str "_model")
        (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
      exact hfm₂
    · intro ψ
      rw [hcval₁, cvalAlias_ne hTneP,
        cvalAlias_ne (show T.str "_model" ≠ projFnName T i from
          fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
      exact hv₂ ψ
  · -- the constructor's clause
    intro ci₂ hf₂
    rw [hfindNe ctorName hCneP] at hf₂
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.1 ci₂ hf₂
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, ?_⟩
    · rw [hfindNe (ctorName.str "_model")
        (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
      exact hfm₂
    · intro ψ
      rw [hcval₁, cvalAlias_ne hCneP,
        cvalAlias_ne (show ctorName.str "_model" ≠ projFnName T i from
          fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
      exact hv₂ ψ
  · -- the projection-family clause
    intro j hj ci₂ hf₂
    by_cases hji : projFnName T j = projFnName T i
    · -- the freshly installed projection
      have hn' : Name.num (T.str "proj") j =
          Name.num (T.str "proj") i := hji
      injection hn' with hp hij
      obtain rfl : i = j := hij.symm
      refine ⟨mcv, mval, hmmcv, ?_, ?_, ?_⟩
      · rw [hfindNe (projModelName T i)
          (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hfm
      · rw [Env.find?_cons, if_pos hheadname] at hf₂
        obtain rfl := Option.some.inj hf₂
        exact hmlps
      · intro ψ
        rw [hcval₁, cvalAlias_self,
          cvalAlias_ne (show projModelName T i ≠ projFnName T i from
            fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
    · -- an earlier install, preserved
      rw [hfindNe (projFnName T j) hji] at hf₂
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.2 j hj ci₂ hf₂
      refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, ?_⟩
      · rw [hfindNe (projModelName T j)
          (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hfm₂
      · intro ψ
        rw [hcval₁, cvalAlias_ne hji,
          cvalAlias_ne (show projModelName T j ≠ projFnName T i from
            fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hv₂ ψ
  · -- the block invariant, preserved across the fresh non-member head
    rw [hcval₁]
    exact BlockInstalledTT.fresh_cons hIB hnotb hpnone
      (fun n ψ hn => by
        rw [cvalAlias_ne (show n ≠ projFnName T i from hn)])
  · -- the head's shape
    exact ⟨_, rfl, hpnone, hheadname⟩

set_option maxHeartbeats 3200000 in
/-- The projection-phase fold preserves having a derivation model
together with the phase invariant.  Transpose of
`checkProjFold_sound`. -/
theorem checkProjFoldTT {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} {blockNames : List Name}
    (hTblock : blockNames.contains T = true)
    (hbshape : ∀ n, blockNames.contains n = true →
      n.isProjFnShape = false) :
    ∀ (idxs : List Nat) (env' env₁ : Env),
    idxs.foldlM (installProjFnStep mode (fueledOps mode F) T ctorName lps nP nF)
      env' = .ok env₁ →
    ∀ m : EnvTT env', ProjPhaseInvT T ctorName nF env' m.cval →
    BlockInstalledTT blockNames env' m.cval →
    (∃ cvT capsT, env'.find? T = some (.indInfo cvT capsT)) →
    (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      EtaPins mode env' T cvT.levelParams capsT) →
    (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → blockNames.contains capsT.etaCtor = true) →
    (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → capsT.etaFields = nF) →
    ∃ m₁ : EnvTT env₁, ProjPhaseInvT T ctorName nF env₁ m₁.cval
  | [], env', env₁, h, m, hinv, _, _, _, _, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨m, hinv⟩
  | i₀ :: rest, env', env₁, h, m, hinv, hIB, hTind, hpinsT, hCblock,
      hFields => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    unfold installProjFnStep at h
    by_cases hm : (env'.find? (projModelName T i₀)).isSome = true
    · rw [if_pos hm] at h
      cases hstep : checkProjFn mode (fueledOps mode F) env' T ctorName lps nP nF
          i₀ with
      | error e => rw [hstep] at h; exact nomatch h
      | ok env₂ => ?_
      rw [hstep] at h
      obtain ⟨m₂, hinv₂, hIB₂, ciH, rfl, hfreshH, hnameH⟩ :=
        checkProjFnTT hstep m hinv hIB hTblock hbshape hTind hpinsT
          hCblock hFields
      have hTneH : T ≠ ciH.name := by
        intro he
        have hsh := hbshape T hTblock
        rw [he, hnameH] at hsh
        rw [show (projFnName T i₀).isProjFnShape = true from rfl] at hsh
        exact nomatch hsh
      have hTdown : ∀ cvT capsT,
          (⟨ciH :: env'.consts⟩ : Env).find? T =
            some (.indInfo cvT capsT) →
          env'.find? T = some (.indInfo cvT capsT) := by
        intro cvT capsT hf
        rw [Env.find?_cons, if_neg (fun hh => hTneH hh.symm)] at hf
        exact hf
      obtain ⟨cvT0, capsT0, hfT0⟩ := hTind
      refine checkProjFoldTT hTblock hbshape rest _ env₁ h m₂ hinv₂
        hIB₂ ⟨cvT0, capsT0, ?_⟩ ?_ ?_ ?_
      · rw [Env.find?_cons_of_isSome hfreshH (by rw [hfT0]; rfl)]
        exact hfT0
      · intro cvT capsT hf
        exact EtaPins.step (hpinsT cvT capsT (hTdown cvT capsT hf))
          hfreshH
      · intro cvT capsT hf
        exact hCblock cvT capsT (hTdown cvT capsT hf)
      · intro cvT capsT hf
        exact hFields cvT capsT (hTdown cvT capsT hf)
    · rw [if_neg hm] at h
      simp only [pure, Except.pure] at h
      exact checkProjFoldTT hTblock hbshape rest env' env₁ h m hinv
        hIB hTind hpinsT hCblock hFields

/-- Extend a derivation model by one elimination-template entry: the
entry is semantically inert (its stored type is `Sort 0` and its
valuation an arbitrary `Prop` inhabitant).  Transpose of
`extend_proj_template`, through `EnvTT.cons`. -/
theorem extendProjTemplateTT {env : Env} (m : EnvTT env)
    (entry : ProjEntry)
    (hnat : entry.native = false)
    (hty : entry.ty = .sort .zero)
    (hTnres : reservedBasisNames.contains entry.structName = false)
    (hfind' : env.find? (projFnName entry.structName entry.idx) = none) :
    Nonempty (EnvTT ⟨.projInfo entry :: env.consts⟩) := by
  have hname : (ConstantInfo.projInfo entry).name =
      projFnName entry.structName entry.idx := rfl
  have hnres : reservedBasisNames.contains
      (projFnName entry.structName entry.idx) = false :=
    reservedBasisNames_not_num _ _
  have hi : Installs env m.cval
      (cvalSetC m.cval (projFnName entry.structName entry.idx)
        dummyPropT) (.projInfo entry) :=
    Installs.of_fresh (by rw [hname]; exact hfind')
      (fun n hn => (cvalSetC_ne (show n ≠
        projFnName entry.structName entry.idx from
        fun hh => hn (hh.trans hname.symm))).symm)
  refine ⟨EnvTT.cons m hi (EnvWF.cons m.wf ?_) ?_ ?_ ?_ ?_ ?_ ?_
    (fun cv2 mI rP rules heq => nomatch heq)
    (fun cv2 mI rP rules heq => nomatch heq) ?_
    (fun cv2 caps heq => nomatch heq) ?_ ?_ ?_ ?_ ?_
    (fun cv2 v hint heq => nomatch heq)
    (fun cv2 v hint heq => nomatch heq)
    (fun cv2 heq => nomatch heq)⟩
  · -- ConstWF: the entry's stored type is `Sort 0`
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show entry.ty.hasFvar = false
      rw [hty]; rfl
    · show entry.ty.allLevelParamsDefined _ = true
      rw [hty]; rfl
    · show entry.ty.constsResolve _ = true
      rw [hty]; rfl
    · show entry.ty.looseBVarsBounded 0 = true
      rw [hty]; rfl
    · intro cv2 v2 h2 heq
      exact nomatch heq
    · intro cv2 mI2 rP2 rules2 heq
      exact nomatch heq
    · intro cv2 v2 heq
      exact nomatch heq
  · -- the junk value is closed
    intro ψ
    rw [hname, cvalSetC_self]
    show VExpr.bvarsBelow 0 dummyPropT
    simp [dummyPropT, VExpr.bvarsBelow]
  · -- and reads no parameters
    intro φ₁ φ₂ hp
    rw [hname, cvalSetC_self, cvalSetC_self]
  · -- it inhabits `Prop`
    intro φ
    refine ⟨.sort 0, ?_, ?_⟩
    · show denote _ _ φ 0 (ConstantInfo.projInfo entry).toConstantVal.type
        = some (.sort 0)
      rw [show (ConstantInfo.projInfo entry).toConstantVal.type =
        entry.ty from rfl, hty, denote_sort]
      rfl
    · rw [hname, cvalSetC_self]
      exact dummyPropT_typed []
  · intro cv2 v2 h2 heq φ
    exact nomatch heq
  · intro cv2 v2 heq φ
    exact nomatch heq
  · -- `Empty` is reserved
    intro hE
    rw [hname] at hE
    rw [hE] at hnres
    exact absurd hnres (by decide)
  · -- the eta head is refuted by kind
    intro T' cvT capsT hfT hcape hresT hfam hpart
    exfalso
    rcases hpart with rfl | hC | ⟨j, hj, hP⟩
    · rw [Env.find?_cons, if_pos rfl] at hfT
      exact nomatch (Option.some.inj hfT)
    · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
      rw [hC, Env.find?_cons, if_pos rfl] at hfC
      exact nomatch (Option.some.inj hfC)
    · obtain ⟨-, -, hfP⟩ := hfam
      obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
      rw [hP, Env.find?_cons, if_pos rfl] at hf2
      exact nomatch (Option.some.inj hf2)
  · -- the residual head is refuted by kind
    intro T' cvT capsT cvC hfT hcape hTres hCres hfC hor
    exfalso
    rcases hor with rfl | hC
    · rw [Env.find?_cons, if_pos rfl] at hfT
      exact nomatch (Option.some.inj hfT)
    · rw [hC, Env.find?_cons, if_pos rfl] at hfC
      exact nomatch (Option.some.inj hfC)
  · -- the template entry is not native
    intro entry2 heq hnat2
    obtain rfl := ConstantInfo.projInfo.inj heq
    rw [hnat] at hnat2
    exact nomatch hnat2
  · -- nor a pinned pair projection
    intro i2 entry2 heq hname2
    obtain rfl := ConstantInfo.projInfo.inj heq
    exfalso
    have hh : Name.num (entry.structName.str "proj") entry.idx =
        Name.num (psigmaName.str "proj") i2 := hname2
    injection hh with hp hij
    injection hp with hT hs
    -- the template's parent is the checked block former, which is
    -- not reserved — while `PSigma'` is
    rw [hT] at hTnres
    exact absurd hTnres (by decide)
  · -- `Eq` is reserved
    intro hE
    rw [hname] at hE
    rw [hE] at hnres
    exact absurd hnres (by decide)
  · -- the projection name is not reserved
    intro hres
    rw [hname] at hres
    rw [hres] at hnres
    exact nomatch hnres

/-- The elimination-template fold preserves having a derivation
model: each installed entry is fresh and semantically inert.
Transpose of `installProjTemplates_sound`. -/
theorem installProjTemplatesTT {T ctorName : Name} {lps : List Name}
    {nP nF : Nat}
    (hTnres : reservedBasisNames.contains T = false) :
    ∀ (idxs : List Nat) (env' env₁ : Env),
    idxs.foldlM
      (installProjTemplateStep (m := CheckM) T ctorName lps nP nF)
      env' = .ok env₁ →
    ∀ _ : EnvTT env', Nonempty (EnvTT env₁)
  | [], env', env₁, h, m => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨m⟩
  | i₀ :: rest, env', env₁, h, m => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : installProjTemplateStep (m := CheckM) T ctorName lps
        nP nF env' i₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₂ =>
      rw [hstep] at h
      have hnext : Nonempty (EnvTT env₂) := by
        revert hstep
        unfold installProjTemplateStep installProjTemplate
        split
        case isFalse =>
          intro hstep
          simp only [pure, Except.pure, Except.ok.injEq] at hstep
          exact ⟨hstep ▸ m⟩
        case isTrue hfree =>
          split
          case h_2 =>
            intro hstep
            simp only [pure, Except.pure, Except.ok.injEq] at hstep
            exact ⟨hstep ▸ m⟩
          case h_1 cvR mI2 rP2 rule heqR =>
            split
            case isFalse =>
              intro hstep
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              exact ⟨hstep ▸ m⟩
            case isTrue hcond =>
              intro hstep
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              obtain ⟨m₂⟩ := extendProjTemplateTT m
                ⟨T, i₀, lps, nP, ctorName, nF, .sort .zero, .zero,
                  .zero, false,
                  decide (cvR.levelParams.length = lps.length + 1)⟩
                rfl rfl hTnres
                (Option.isNone_iff_eq_none.mp hcond.1)
              exact ⟨hstep ▸ m₂⟩
      obtain ⟨m₂⟩ := hnext
      exact installProjTemplatesTT hTnres rest env₂ env₁ h m₂

end Setlec.TTVerify
