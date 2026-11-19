module

import ConLeche.Model.Modular.Compare
public import ConLeche.Model.Copies
public import ConLeche.Verify.Cached.Fill
public import ConLeche.Verify.Driver.CompareJsonRun
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Frontend.Prepare

public section

/-!
# A compared run of two lean4export files, in the model (task #612)

`compare_embeds`: on the comparison's, the order check's and the solution's fold's accept, every
constant of the challenge's environment (its holes as their statements) is a copy of the
solution's constant of that name, at the challenge's level-parameter names, or, for a hole, the
axiom of a copy of that constant's statement.  `compare_json_solved` specialises it and
`compare_solved` to the run of two lean4export files (`Driver.compareJsonG`): every challenge
record its own but a standard axiom's (`Driver.jsonHomes`), the solution's records with their
values in place.
-/

namespace ConLeche.Model.Compare

open ConLeche ConLeche.Driver ConLeche.Verify ConLeche.Model SetTheory

/-- **What a challenge record stands for**: the solution's record, or its statement. -/
theorem cmpRecord_eq {C : Name} {uses : Declaration → Array Name} {own : Bool}
    {homeC homeS : Option Name} {dC dS e : Declaration} {f : Option Filled}
    (h : cmpRecord C uses own homeC homeS dC dS = .ok (e, f)) :
    e = dS ∨ e = Modular.stmtOf dS := by
  unfold cmpRecord at h
  dsimp only at h
  repeat' split at h
  all_goals simp only [reduceCtorEq, Except.ok.injEq, Prod.mk.injEq] at h
  all_goals first
    | exact .inl h.1.symm
    | exact .inr h.1.symm

/-- A constant of a record's statement that is of a statement kind but no axiom is one of the
record's own. -/
theorem stmtOf_const {d : Declaration} {c : ConstantInfo}
    (hc : c ∈ declConstants (Modular.stmtOf d)) (hk : c.isStmtKind = true) :
    c ∈ declConstants d ∨ c = .axiomInfo c.toConstantVal := by
  cases d with
  | defnDecl cv v h | thmDecl cv v | opaqueDecl cv v =>
    simp only [Modular.stmtOf, declConstants] at hc
    split at hc
    · simp only [List.mem_singleton] at hc; subst hc; exact .inr rfl
    · split at hc
      · simp at hc
      · simp only [List.mem_singleton] at hc; subst hc; exact .inr rfl
  | _ => exact .inl hc

/-- **The challenge's environment embeds into the solution's**: on the comparison's, the order
check's and the solution's fold's accept, every constant of the challenge's environment (its
holes as their statements) is a copy of the solution's constant of that name at the challenge's
level-parameter names, or the axiom of a copy of that constant's statement. -/
theorem compare_embeds {pins : List NatOpPinSet} {maxNatSize : Nat}
    {F : Expr → Expr} {C : Name} {uses : Declaration → Array Name}
    {homesC homesS : Std.HashMap Name Name} {recsS : Array Declaration}
    {idxS : Std.HashMap Name Nat} {recsC ctx : Array Declaration} {filled : Array Filled}
    {env : Env}
    (hcmp : compareRecords C uses homesC homesS recsS idxS recsC = .ok (ctx, filled))
    (hsc : ctxScoped ctx = none)
    (hchk : Cached.checkDecls .verified pins maxNatSize (recsS.map (Cached.fillDecl F)) = .ok env) :
    ∀ n cC, (streamEnv (recsC.toList.map (chalRecord C uses homesC))).find? n = some cC →
      ∃ cS, (streamEnv (recsS.map (Cached.fillDecl F)).toList).find? n = some cS ∧
        (ConstCopy cS cC ∨ ConstCopy (.axiomInfo cS.toConstantVal) cC) := by
  classical
  have hok := cmpDev_localOk (F := F) hcmp hsc hchk
  have hcp := chal_copies hcmp hsc
  let dev := cmpDev (recsS.map (Cached.fillDecl F)).toList ctx.toList
  intro n cC hfC
  rcases hcp.find n with ⟨-, h2⟩ | ⟨c, cC', h1, h2, hr⟩
  · rw [h2] at hfC; exact nomatch hfC
  rw [h2] at hfC
  have e := Option.some.inj hfC
  subst e
  obtain ⟨cS, hS, hal, -⟩ := Model.Modular.agree_alike hok (Modular.Agree.same (dev := dev)
    (i := 1) (b := 0) (n := n) rfl) (Nat.le_refl 1) (Nat.zero_le 1) h1
  refine ⟨cS, hS, ?_⟩
  rcases hal with rfl | ⟨hcv, hk, -⟩
  · exact .inl hr
  -- the context record `c` comes from: the solution's record, or its statement
  have hm := ConLeche.Env.find?_mem h1
  have hn := ConLeche.Env.find?_name h1
  obtain ⟨e, he, hce⟩ := ((mem_streamEnv_consts _ Env.empty).1 hm).resolve_right (by
    simp [Env.empty])
  obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp he
  obtain ⟨hsz, hall⟩ := compareRecords_spec hcmp
  have hkc : k < recsC.size := by simp at hk'; omega
  obtain ⟨e', he', dS, hdS, f, hrec⟩ := hall k hkc
  have hei : ctx.toList[k] = e' := by
    simp only [Array.getElem_toList]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by simpa using hk')).symm.trans he')
  rw [hei] at hce
  -- a constant of the solution's record is the solution's constant of its name
  have hown : c ∈ declConstants dS → ConstCopy cS cC' := fun hc => by
    have hnd := Model.Modular.ImportOk.chain (hok 0 (Nat.zero_le 1)).importOk |>.1
    have hf := Model.Modular.own_find?_of_decl (dev := dev) (j := 0) hnd
      (d := Cached.fillDecl F dS)
      (by show _ ∈ (recsS.map (Cached.fillDecl F)).toList; simpa using Array.mem_map_of_mem hdS)
      (by rw [declConstants_fill]; exact hc)
    have hS' : (dev 0).own.find? n = some cS := hS
    rw [hn, hS'] at hf
    obtain rfl := Option.some.inj hf
    exact hr
  rcases cmpRecord_eq hrec with rfl | rfl
  · exact .inl (hown hce)
  · rcases stmtOf_const hce hk with hc | hc
    · exact .inl (hown hc)
    · right
      rw [hc, hcv] at hr
      exact hr

/-! ## The run of two lean4export files -/

/-- Every challenge record but a standard axiom's is the challenge's own. -/
theorem jsonHomes_own {recs : Array Declaration} {d : Declaration} (hd : d ∈ recs)
    (hs : isStdAxiom d = false) : (jsonHomes recs)[recKey d]? = some jsonOwn := by
  unfold jsonHomes
  rw [← Array.foldl_toList]
  have hd' : d ∈ recs.toList := Array.mem_toList_iff.mpr hd
  generalize recs.toList = L at hd'
  suffices H : ∀ (L : List Declaration) (m : Std.HashMap Name Name),
      (d ∈ L ∨ m[recKey d]? = some jsonOwn) →
      (L.foldl (fun m d => if isStdAxiom d then m else m.insert (recKey d) jsonOwn) m)[recKey d]?
        = some jsonOwn from H L {} (.inl hd')
  intro L
  induction L with
  | nil => intro m h; simpa using h
  | cons x L ih =>
    intro m h
    simp only [List.foldl_cons]
    apply ih
    by_cases hx : x = d
    · subst hx
      right
      simp [hs]
    · rcases h with h | h
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact .inl h
      · right
        split
        · exact h
        · rw [Std.HashMap.getElem?_insert]
          split
          · rfl
          · exact h

/-- **Every hole of a challenge file is one of the challenge's records.** -/
theorem mem_jsonRecs {pre : Frontend.PreludeIx} {ds : Array Declaration} {d : Declaration}
    (hd : d ∈ ds) (hh : jsonHole d = true) : d ∈ jsonRecs pre ds := by
  unfold jsonRecs
  obtain ⟨i, hi, he⟩ := Array.getElem_of_mem (Frontend.mem_prepareD (pre := pre)
    (used := Declaration.usedConsts) hd)
  refine Array.mem_map.mpr ⟨(d, i), Array.mem_filter.mpr ⟨?_, by simp [hh]⟩, rfl⟩
  rw [Array.mem_iff_getElem]
  exact ⟨i, by simpa using hi, by simp [he]⟩

theorem map_fillDecl_id (ds : Array Declaration) : ds.map (Cached.fillDecl id) = ds := by
  have : Cached.fillDecl id = id := funext fun d => by cases d <;> rfl
  rw [this, Array.map_id]

universe w

/-- **A compared run of two lean4export files, in the model**: on the comparison's, the order
check's and the solution's fold's accept, the challenge's environment embeds into the
solution's (`compare_embeds`), and there are models `mC` of the challenge's environment and
`mS` of the solution's, `mC` reading every name as `mS` reads it at the challenge's
level-parameter names, in which every hole of the challenge file (`jsonHole`) is inhabited by
the solution's constant of its name. -/
theorem compare_json_solved (V : Type w) [SetTheory V] {pins : List NatOpPinSet}
    {maxNatSize : Nat} {pre : Frontend.PreludeIx} {dsC dsS ctx : Array Declaration}
    {filled : Array Filled} {env : Env}
    (hcmp : compareRecords jsonOwn Declaration.usedConsts (jsonHomes (jsonRecs pre dsC)) {}
      (Frontend.preparePrelude pre dsS) (recIndex (Frontend.preparePrelude pre dsS))
      (jsonRecs pre dsC) = .ok (ctx, filled))
    (hsc : ctxScoped ctx = none)
    (hchk : Cached.checkDecls .verified pins maxNatSize (Frontend.preparePrelude pre dsS) = .ok env) :
    (∀ n cC, (jsonChallengeEnv pre dsC).find? n = some cC →
      ∃ cS, (streamEnv (Frontend.preparePrelude pre dsS).toList).find? n = some cS ∧
        (ConstCopy cS cC ∨ ConstCopy (.axiomInfo cS.toConstantVal) cC)) ∧
    ∃ (mC : ConLeche.Model V (jsonChallengeEnv pre dsC))
      (mS : ConLeche.Model V (streamEnv (Frontend.preparePrelude pre dsS).toList)),
      (∀ n cC, (jsonChallengeEnv pre dsC).find? n = some cC →
        ∃ cS, (streamEnv (Frontend.preparePrelude pre dsS).toList).find? n = some cS ∧
          cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
          ∀ φ, mC.cval n φ = mS.cval n (Level.substFn φ cS.toConstantVal.levelParams
            (cC.toConstantVal.levelParams.map Level.param))) ∧
      ∀ d ∈ dsC, jsonHole d = true →
        ∃ cv cS, recCv? d = some cv ∧
          (streamEnv (Frontend.preparePrelude pre dsS).toList).find? cv.name = some cS ∧
          ∀ φ ρ, ∃ T, Denotes mC.cval (jsonChallengeEnv pre dsC) φ ρ cv.type T ∧
            mS.cval cv.name (Level.substFn φ cS.toConstantVal.levelParams
              (cv.levelParams.map Level.param)) ∈ˢ T := by
  have hchk' : Cached.checkDecls .verified pins maxNatSize
      ((Frontend.preparePrelude pre dsS).map (Cached.fillDecl id)) = .ok env := by
    rw [map_fillDecl_id]; exact hchk
  have hemb := compare_embeds hcmp hsc hchk'
  have H := compare_solved V hcmp hsc hchk'
  rw [map_fillDecl_id] at H hemb
  obtain ⟨mC, mS, h1, h2⟩ := H
  refine ⟨hemb, mC, mS, h1, fun d hd hh => ?_⟩
  have hd' := mem_jsonRecs (pre := pre) hd hh
  simp only [jsonHole, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hh
  obtain ⟨⟨hs, -⟩, hh⟩ := hh
  exact h2 d hd' (jsonHomes_own hd' hs) hh

end ConLeche.Model.Compare
