module

public import ConLeche.Model.Copies
public import ConLeche.Verify.Driver.ComposeCompare
import ConLeche.Model.Modular.Main
public import ConLeche.Model.Modular.Compare
public import ConLeche.Model.Modular.Instance
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Driver.Routes

/-!
# The challenge's environment in a compared modular run (task #608)

A run over the closures of a challenge `C` and its solution `S` (`Driver.Compose.Run.ofCompare`)
is a development every module of which passes the local checks, the challenge one more module
whose context is the compare worker's reach and which has no record of its own.  The modular
theorem gives the development a compatible family of models; the challenge's environment
(`Driver.chalEnvOf`: that context, the records of the challenge's names at the challenge's
level-parameter names) is a copy of the challenge module's (`chal_copies`), so its model is read
off the family's (`Model.ofCopies`, `run_models`):

* every name of the challenge's environment is valued as the module that declares it values it
  (the context's home), at the challenge's level-parameter names;
* every hole of `C` is a constant of the challenge's environment with the hole's statement
  (`chal_hole`), so its type is inhabited (`Model.mem`).
-/

public section

namespace ConLeche.Model.CompareRun

open ConLeche ConLeche.Driver ConLeche.Driver.Compose ConLeche.Verify ConLeche.Model
  ConLeche.Model.Compare ConLeche.Frontend.Olean SetTheory

universe w

/-! ## The copy -/

theorem levelsRenaming_spec {ps lps : List Name} (h : levelsRenaming ps lps = true) :
    ps.Nodup ∧ lps.length = ps.length := by
  simp only [levelsRenaming, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.1.1.symm⟩

/-- A renamed constant is a copy. -/
theorem copy_of_renaming {ps? : Option (List Name)} {ps : List Name} {c : ConstantInfo}
    (h : renamingTo ps? c.toConstantVal.levelParams = some ps) : ConstCopy c (c.atLps ps) := by
  unfold renamingTo at h
  obtain ⟨ps', -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · rename_i hr
    cases h
    simp only [Bool.and_eq_true] at hr
    obtain ⟨hnd, hl⟩ := levelsRenaming_spec hr.2
    exact .inr ⟨_, rfl, hnd, hl⟩
  · cases h

/-- **A context record at the challenge's names installs copies of its constants.** -/
theorem recCopy_chalRec (f : Name → Option (List Name)) : ∀ d, RecCopy d (chalRec f d)
  | .axiomDecl cv => by
    simp only [chalRec]
    split
    · exact RecCopy.refl _
    · rename_i hq
      split
      · rename_i ps hps
        have hc := copy_of_renaming (c := .axiomInfo cv) hps
        refine ⟨?_, rfl⟩
        simp only [declConstants, hq, ↓reduceIte]
        have hn : (cv.atLps ps).name = cv.name := rfl
        rw [hn]
        split
        · exact .nil
        · exact .cons hc .nil
      · exact RecCopy.refl _
  | .defnDecl cv v h => by
    simp only [chalRec]
    split
    · rename_i ps hps
      exact recCopy_single (copy_of_renaming (c := .defnInfo cv v h) hps) rfl rfl rfl
    · exact RecCopy.refl _
  | .thmDecl cv v => by
    simp only [chalRec]
    split
    · rename_i ps hps
      exact recCopy_single (copy_of_renaming (c := .thmInfo cv) hps) rfl rfl rfl
    · exact RecCopy.refl _
  | .opaqueDecl cv v => by
    simp only [chalRec]
    split
    · rename_i ps hps
      exact recCopy_single (copy_of_renaming (c := .axiomInfo cv) hps) rfl rfl rfl
    · exact RecCopy.refl _
  | .quotDecl .. => RecCopy.refl _
  | .indDecl .. => RecCopy.refl _

/-- **The challenge's environment is a copy of the compare worker's context.** -/
theorem chal_copies {c : CmpModuleRead}
    (hnd : (c.w.reach.ctx.toList.flatMap Modular.declNames).Nodup) :
    CopiesEnv (streamEnv c.w.reach.ctx.toList) (chalEnvOf c) := by
  obtain ⟨hc, ht⟩ := records_copy c.w.reach.ctx.toList
    (c.w.reach.ctx.toList.map (chalRec (cmpLps c.w.emitted))) (by simp)
    (fun i h h' => by
      simp only [List.getElem_map]
      exact recCopy_chalRec (cmpLps c.w.emitted) _)
  refine ⟨?_, ?_, ?_⟩
  · rw [Model.Modular.streamEnv_empty_consts, chalEnvOf, Model.Modular.streamEnv_empty_consts]
    exact hc.reverse
  · rw [chalEnvOf, Model.Modular.streamEnv_empty_tables, Model.Modular.streamEnv_empty_tables, ht]
  · rw [Model.Modular.streamEnv_empty_consts, List.map_reverse, (List.reverse_perm _).nodup_iff]
    simp only [Model.Modular.recsC, List.map_flatMap]
    exact hnd

/-! ## The holes -/

/-- **A hole the compare worker accepts**: neither the quotient's axiom nor the placeholder axiom,
and the context's record of its key an axiom or a definition of the hole's statement up to the
names of level parameters. -/
theorem cmpCtxRecord_hole {uses : Declaration → Array Name} {dC dS : Declaration} {h : Name}
    {kindS : String} {f : Option Filled} (hh : isHole uses dC = true)
    (hc : cmpCtxRecord uses dC dS h kindS = .ok f) :
    recKey dC ≠ quotSoundName ∧ recKey dC ≠ sorryAxName ∧ ∃ cv cv', recCv? dC = some cv ∧
      sameCvUpToLevels cv cv' = true ∧ (dS = .axiomDecl cv' ∨ ∃ v r, dS = .defnDecl cv' v r) := by
  unfold cmpCtxRecord at hc
  simp only [hh, ↓reduceIte] at hc
  split at hc
  · cases hc
  rename_i hq
  have hq' : recKey dC ≠ quotSoundName ∧ recKey dC ≠ sorryAxName :=
    ⟨fun e => hq (by simp [e]), fun e => hq (by simp [e])⟩
  refine ⟨hq'.1, hq'.2, ?_⟩
  have hrest : ∀ cv', (if reduceOpNames.contains (recKey dC) && kindS != "axiom" &&
      kindS != "opaque constant" then (Except.error "" : Except String (Option Filled)) else
      match recCv? dC with
      | some cv => if sameCvUpToLevels cv cv' then .ok none else .error ""
      | none => .error "") = .ok f → ∃ cv, recCv? dC = some cv ∧ sameCvUpToLevels cv cv' = true :=
    by
    intro cv' hx
    split at hx
    · cases hx
    · split at hx
      · rename_i cv hcv
        split at hx
        · exact ⟨cv, hcv, by assumption⟩
        · cases hx
      · cases hx
  split at hc
  · rename_i cv'
    split at hc
    · cases hc
    · split at hc
      · rename_i cv hcv
        split at hc
        · exact ⟨cv, cv', hcv, by assumption, .inl rfl⟩
        · cases hc
      · cases hc
  · rename_i cv' v r
    split at hc
    · cases hc
    · split at hc
      · rename_i cv hcv
        split at hc
        · exact ⟨cv, cv', hcv, by assumption, .inr ⟨v, r, rfl⟩⟩
        · cases hc
      · cases hc
  · cases hc

/-- The statement a renaming to the challenge's names gives is the challenge's. -/
theorem renamed_cv {cv cv' : ConstantVal} (hs : sameCvUpToLevels cv cv' = true) :
    (∀ ps, renamingTo (some cv.levelParams) cv'.levelParams = some ps → cv'.atLps ps = cv) ∧
    (renamingTo (some cv.levelParams) cv'.levelParams = none → cv' = cv) := by
  unfold sameCvUpToLevels at hs
  constructor
  · intro ps hps
    simp only [renamingTo, Option.bind_some] at hps
    split at hps
    · cases hps
      rename_i hr
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hr
      have hne : ¬ cv.levelParams = cv'.levelParams := by simpa using hr.1
      simp only [beq_iff_eq, hne, ↓reduceIte] at hs
      simp only [Bool.and_eq_true] at hs
      exact (ConstantVal.eq_of_beqP hs.2)
    · cases hps
  · intro hn
    simp only [renamingTo, Option.bind_some] at hn
    split at hs
    · exact (ConstantVal.eq_of_beqP hs).symm
    · rename_i hne
      simp only [Bool.and_eq_true] at hs
      have hc : (cv.levelParams != cv'.levelParams && levelsRenaming cv.levelParams
          cv'.levelParams) = true := by simp [hs.1]; simpa using hne
      simp only [hc, ↓reduceIte] at hn
      cases hn

/-- **Every hole of the challenge is a constant of the challenge's environment** with the hole's
statement. -/
theorem chal_hole {sp : Roots} {fs : FS} {C S : Name} {jobs : Nat} {c : CmpModuleRead}
    (hc : CmpFacts sp fs C S jobs c) {d : Declaration} (hd : d ∈ c.w.emitted)
    (hh : isHole (ownUses c.w.home) d = true) :
    ∃ cv ci, recCv? d = some cv ∧ ci ∈ (chalEnvOf c).consts ∧ ci.toConstantVal = cv := by
  obtain ⟨k, hk, kindS, f, hcmp⟩ := hc.cmp d hd
  obtain ⟨hq, hsa, cv, cv', hcv, hs, hdS⟩ := cmpCtxRecord_hole hh hcmp
  have hkey : recKey d = cv.name := recKey_of_recCv hcv
  obtain ⟨hlt, -⟩ := ownerMap_spec hk
  have hmem : c.w.reach.ctx.getD k default ∈ c.w.reach.ctx.toList := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
  have hname : cv'.name = cv.name := by
    rcases Decidable.em (renamingTo (some cv.levelParams) cv'.levelParams = none) with hn | hn
    · rw [(renamed_cv hs).2 hn]
    · obtain ⟨ps, hps⟩ := Option.ne_none_iff_exists'.1 hn
      rw [← (renamed_cv hs).1 ps hps]; rfl
  have hlps : cmpLps c.w.emitted cv'.name = some cv.levelParams := by
    rw [hname]; exact cmpLps_of_mem hc.facts.emitted hd hcv
  have hq' : cv'.name ≠ quotSoundName := by rw [hname, ← hkey]; exact hq
  have hsa' : cv.name ≠ sorryAxName := by rw [← hkey]; exact hsa
  -- the renamed record's one constant
  have hci : ∃ ci ∈ declConstants (chalRec (cmpLps c.w.emitted) (c.w.reach.ctx.getD k default)),
      ci.toConstantVal = cv := by
    rcases hdS with hdS | ⟨v, r, hdS⟩ <;> rw [hdS] <;> simp only [chalRec, hq', ↓reduceIte, hlps]
    · split
      · rename_i ps hps
        rw [(renamed_cv hs).1 ps hps]
        exact ⟨.axiomInfo cv, by simp [declConstants, hsa', show cv.name ≠ quotSoundName by
          rw [← hname]; exact hq'], rfl⟩
      · rename_i hps
        rw [(renamed_cv hs).2 hps]
        exact ⟨.axiomInfo cv, by simp [declConstants, hsa', show cv.name ≠ quotSoundName by
          rw [← hname]; exact hq'], rfl⟩
    · split
      · rename_i ps hps
        exact ⟨_, List.mem_singleton_self _, (renamed_cv hs).1 ps hps⟩
      · rename_i hps
        exact ⟨_, List.mem_singleton_self _, (renamed_cv hs).2 hps⟩
  obtain ⟨ci, hci, hcv'⟩ := hci
  refine ⟨cv, ci, hcv, ?_, hcv'⟩
  exact (mem_streamEnv_consts _ Env.empty).2 (.inl ⟨_, List.mem_map_of_mem hmem, hci⟩)

/-! ## The models -/

theorem cast_cval {V : Type w} [SetTheory V] {e₁ e₂ : Env} (h : e₁ = e₂)
    (m : ConLeche.Model V e₁) : (cast (congrArg (ConLeche.Model V) h) m).cval = m.cval := by
  subst h; rfl

theorem le_sum_of_mem : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.sum
  | _ :: l, _, .head _ => by simp
  | b :: l, a, .tail _ h => by have := le_sum_of_mem h; simp; omega

theorem idx_congr {γ : Sort _} {i : Nat} (g : (j : Nat) → j < i + 1 → γ) :
    ∀ {a b : Nat} (_ : a = b) (ha : a < i + 1) (hb : b < i + 1), g a ha = g b hb := by
  rintro a _ rfl _ _; rfl

/-- **The models of a compared run** (see the module docstring): for a run whose module `Cn` is
the compare worker's, a model of every module's own environment and one of the challenge's
environment such that every context name is valued as its home values it, every name of the
challenge's environment as its home values it at the challenge's level-parameter names, and every
hole of the challenge is inhabited. -/
theorem run_models (V : Type w) [SetTheory V] {sp : Roots} {fs : FS} {maxNatSize : Nat}
    (R : Run sp fs maxNatSize) {Cn S : Name} {jobs : Nat} {c : CmpModuleRead}
    (hC : Cn ∈ R.names) (hw : R.w Cn = c.w) (hcf : CmpFacts sp fs Cn S jobs c) :
    ∃ (m : ∀ M, M ∈ R.names → ConLeche.Model V (ownEnvOf sp fs M (R.w M)))
      (mC : ConLeche.Model V (chalEnvOf c)),
      (∀ M (hM : M ∈ R.names) n, ((streamEnv (R.w M).reach.ctx.toList).find? n).isSome = true →
        ∃ hh : ctxHome (R.w M).reach n ∈ R.names, (m M hM).cval n = (m _ hh).cval n) ∧
      (∀ n cC, (chalEnvOf c).find? n = some cC →
        ∃ hh : ctxHome c.w.reach n ∈ R.names, R.x (ctxHome c.w.reach n) = #[] ∧
          ∃ cS, (ownEnvOf sp fs (ctxHome c.w.reach n) (R.w (ctxHome c.w.reach n))).find? n =
            some cS ∧
            cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
            ∀ φ, mC.cval n φ = (m _ hh).cval n (Level.substFn φ cS.toConstantVal.levelParams
              (cC.toConstantVal.levelParams.map Level.param))) ∧
      (∀ d ∈ c.w.emitted, isHole (ownUses c.w.home) d = true → ∃ cv, recCv? d = some cv ∧
        ∀ φ ρ, ∃ T, Denotes mC.cval (chalEnvOf c) φ ρ cv.type T ∧ mC.cval cv.name φ ∈ˢ T) := by
  classical
  let i := (R.names.map R.rk).sum
  have hle : ∀ M ∈ R.names, R.rk M ≤ i := fun M hM => le_sum_of_mem (List.mem_map_of_mem hM)
  have hok : ∀ j ≤ i, Modular.LocalOk .verified natOpPinSets maxNatSize R.dev j :=
    fun j _ => R.localOk j
  obtain ⟨mm, hc⟩ := Model.Modular.modularModels (V := V) (pins := natOpPinSets) hok
  have hex : ∀ j (hj : j < i + 1), ∃ mp : EnvModelM V (R.dev j).own,
      ∀ n, ((R.dev j).own.find? n).isSome = true → mp.base2.acval n = (mm j hj).1 n :=
    fun j hj => (mm j hj).2.2.2.2.elim fun mp h => ⟨mp, h.2.2⟩
  let mp : ∀ j (hj : j < i + 1), EnvModelM V (R.dev j).own := fun j hj =>
    Classical.choose (hex j hj)
  have hmp : ∀ j hj n, ((R.dev j).own.find? n).isSome = true →
      (mp j hj).base2.acval n = (mm j hj).1 n := fun j hj => Classical.choose_spec (hex j hj)
  have hb : ∀ M, M ∈ R.names → R.rk M < i + 1 := fun M hM => Nat.lt_succ_of_le (hle M hM)
  let m : ∀ M, M ∈ R.names → ConLeche.Model V (ownEnvOf sp fs M (R.w M)) := fun M hM =>
    cast (congrArg (ConLeche.Model V) (R.dev_own hM)) (Model.ofEnvModelM (mp (R.rk M) (hb M hM)))
  have hm : ∀ M hM, (m M hM).cval = cvalOf (mp (R.rk M) (hb M hM)).base2.acval := fun M hM => by
    show (cast (congrArg (ConLeche.Model V) (R.dev_own hM))
      (Model.ofEnvModelM (mp (R.rk M) (hb M hM)))).cval = _
    exact (cast_cval (R.dev_own hM) _).trans (Model.Model.ofEnvModelM_cval _)
  -- a context name: its home's leaf
  have hcompat : ∀ M (hM : M ∈ R.names) n,
      ((streamEnv (R.w M).reach.ctx.toList).find? n).isSome = true →
      ∃ hh : R.homeIn M n ∈ R.names, (mp (R.rk M) (hb M hM)).base2.acval n =
        (mp _ (hb _ hh)).base2.acval n := by
    intro M hM n hn
    obtain ⟨hh, -, -⟩ := R.ctx_home hM hn
    have hctx : ((R.dev (R.rk M)).context.find? n).isSome = true := by
      rw [R.dev_rk hM]; exact hn
    obtain ⟨hs, he, -⟩ := hc (R.rk M) (hb M hM) n ⟨hctx, trivial⟩
    have hsrc : (R.dev (R.rk M)).src n = R.rk (R.homeIn M n) := by rw [R.dev_rk hM]; rfl
    have hst := Model.Modular.src_stored hok (hle M hM) hctx
    rw [hsrc] at hst
    refine ⟨hh, ?_⟩
    rw [hmp _ _ n (Model.Modular.own_stored_of_context hok (hle M hM) hctx), hmp _ _ n hst]
    exact he.trans (idx_congr (fun j hj => (mm j hj).1 n) hsrc _ _)
  have hown : (R.w Cn).own = #[] := by rw [hw, hcf.facts.own]; simp [recsOf]
  have henv : (R.dev (R.rk Cn)).own = streamEnv c.w.reach.ctx.toList := by
    rw [R.dev_own hC, R.ownEnv_noOwn hown, hw]
  have hctxEq : (R.dev (R.rk Cn)).context = streamEnv c.w.reach.ctx.toList := by
    rw [R.dev_rk hC]; simp [Run.modOf, Modular.Module.context, Run.ctx, hw]
  have hcp : CopiesEnv (R.dev (R.rk Cn)).own (chalEnvOf c) := by
    rw [henv]; exact chal_copies hcf.facts.nodup
  let mp₀ := mp (R.rk Cn) (hb Cn hC)
  refine ⟨m, Model.ofCopies mp₀ hcp, fun M hM n hn => ?_, fun n cC hfC => ?_, fun d hd hh => ?_⟩
  · obtain ⟨hh, he⟩ := hcompat M hM n hn
    rw [R.homeIn_eq] at hh
    refine ⟨hh, ?_⟩
    rw [hm M hM, hm _ hh]
    exact Model.cvalOf_congr he
  · rcases hcp.find n with ⟨-, h2⟩ | ⟨c0, cC', h1, h2, hr⟩
    · rw [h2] at hfC; cases hfC
    rw [h2] at hfC
    cases hfC
    have hn : ((streamEnv (R.w Cn).reach.ctx.toList).find? n).isSome = true := by
      rw [hw, ← henv, h1]; rfl
    obtain ⟨hh, he⟩ := hcompat Cn hC n hn
    obtain ⟨-, -, hx⟩ := R.ctx_home hC hn
    have hctx : (R.dev (R.rk Cn)).context.find? n = some c0 := by rw [hctxEq, ← henv]; exact h1
    have hsrc : (R.dev (R.rk Cn)).src n = R.rk (R.homeIn Cn n) := by rw [R.dev_rk hC]; rfl
    obtain ⟨cS, hS, hal, -⟩ := Model.Modular.agree_alike hok (Modular.Agree.same (dev := R.dev)
      (i := R.rk Cn) rfl) (hle Cn hC) (by rw [hsrc]; exact hle _ hh) hctx
    rw [hsrc, R.dev_own hh] at hS
    have hlps : cS.toConstantVal.levelParams = c0.toConstantVal.levelParams := by
      rcases hal with rfl | ⟨hcv, -⟩
      · rfl
      · rw [hcv]
    have hhome : R.homeIn Cn n = ctxHome c.w.reach n := by rw [R.homeIn_eq, hw]
    revert hh he hx hS
    rw [hhome]
    intro hh he hx hS
    refine ⟨hh, hx, cS, hS, ?_, fun φ => ?_⟩
    · rw [hlps]
      rcases hr with rfl | ⟨ps, rfl, -, hl⟩
      · rfl
      · rw [atLps_cv]; exact hl
    · rw [Model.ofCopies_cval mp₀ hcp h1 h2 φ, hm _ hh, hlps]
      exact congrFun (Model.cvalOf_congr he) _
  · obtain ⟨cv, ci, hcv, hci, hcv'⟩ := chal_hole hcf hd hh
    refine ⟨cv, hcv, fun φ ρ => ?_⟩
    obtain ⟨T, hT, hmem⟩ := (Model.ofCopies mp₀ hcp).mem ci hci φ ρ
    rw [hcv'] at hT
    have hn : ci.name = cv.name := by rw [ConstantInfo.name, hcv']
    rw [hn] at hmem
    exact ⟨T, hT, hmem⟩

end ConLeche.Model.CompareRun
