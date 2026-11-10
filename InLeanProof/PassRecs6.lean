module

public import InLeanProof.PassRecs5
public import InLeanProof.PassEnv
public import InLeanProof.BlockPresR
public import ConLeche.Verify.Cached.GenRecC
import ConLeche.Verify.Inductives.NestContInv
/- `ConstantInfo.name` is read as a projection of `toConstantVal`. -/
import all Lean.Declaration
/- `FEnv.push` (not exposed in `InLean/Push.lean`). -/
import all InLean.Push

/-!
# O7-recursors: the stage's environments (task #451, lane O7-recursors, round 5)

The job's environment premises (`JobEnvI`) at the two environments the
recursor stage reads beside the constructors' one:

* the constructors pushed (`consBlockCtorsF`, the stage's input `fe₂`),
  against master's `consBlockCtors` (`jobEnvI_ctors`);
* the rule-less generated recursors pushed (`classFeR`, InLean's
  `classFeROvl`), against master's `ruleEnv` (`jobEnvI_ruleEnv`).

Both are pushes of fresh entries that are neither formers nor tables
(`presI_push_plain`: `presI_push` at one name); the projection bodies' range
is kept by `projBodiesInRange_one`.

Then the pieces `genRecCheck`'s composition needs beside the earlier rounds'
`*I_run` theorems: its guards translated (`blockLargeElimAllowed_tr`,
`minors_trCR`, `classRecOf_tr`, `structElimLevel_tr`), the classes' former
types as a list, closed (`classFormerTysI_run`, `classFormerTy_lbb` on
master's side), the classes' entries drawn from the positivity table
(`classesNfs_sub`), and what the recursor types' run and the pins give the
rule-less environment (`classRecTysOk_facts`: `rP ≤ mI`, fresh names at the
records' names; `targetRecPins_nodup`).
-/

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

variable {fe : InLean.FEnv} {L : ConLeche.Env}

/-! ## One fresh entry with no table -/

/-- **A fresh entry that is no table pushed** keeps the relation, from its
own entry's relation. -/
theorem presI_push_plain (hlaws : EnvLaws) (hP : EnvPresI fe L) {ci : Lean.ConstantInfo}
    {cci : ConLeche.ConstantInfo} (hfresh : fe.env.find? ci.name = none)
    (hsees : fe.sees ci.name ci = true) (hname : cci.name = toName ci.name)
    (hrel : EntryRelI (fe.push ci) ci cci) (htab : (fe.push ci).findTable? ci.name = none) :
    EnvPresI (fe.push ci) (L.pushDelta [cci] []) := by
  have hfeNone : fe.find? ci.name = none := by
    simp only [FEnv.find?_eq_filter, hfresh, Option.filter_none]
  have hfe' : (fe.push ci).find? ci.name = some ci := by
    rw [FEnv.find?_eq_filter, push_find, find_addConst hlaws hfresh]
    have hs' : (fe.push ci).sees = fe.sees := by rfl
    simp only [↓reduceIte, Option.filter_some, hs', hsees]
  apply presI_push (fe' := fe.push ci) (names := [ci.name]) hP rfl rfl rfl
  · intro n hn; simp only [List.mem_singleton] at hn; subst hn; exact hfresh
  · intro n hn
    simp only [List.mem_singleton] at hn
    rw [push_find, find_addConst hlaws hfresh]
    exact ite_eq_right hn
  · intro c hc
    simp only [List.mem_singleton] at hc; subst hc
    exact ⟨ci.name, by simp, hname⟩
  · intro t ht; cases ht
  · intro n hn ci' hf
    simp only [List.mem_singleton] at hn; subst hn
    rw [hfe'] at hf
    cases hf
    refine ⟨cci, ?_, hrel⟩
    rw [pushDelta_find]
    simp [hname]
  · intro n hn hf
    simp only [List.mem_singleton] at hn; subst hn
    rw [hfe'] at hf; cases hf
  · intro T hT
    simp only [List.mem_singleton] at hT; subst hT
    rw [findTable_fresh hP hfeNone]
    exact htab
  · intro t ht; cases ht

theorem findTable_notInd {fe : InLean.FEnv} {n : Name} {ci : Lean.ConstantInfo}
    (h : fe.find? n = some ci) (hni : ∀ v, ci ≠ .inductInfo v) : fe.findTable? n = none := by
  unfold InLean.FEnv.findTable?
  rw [h]
  cases ci with
  | inductInfo v => exact (hni v rfl).elim
  | _ => rfl

/-- The pushed entry is found at its name. -/
theorem find_push_self (hlaws : EnvLaws) {ci : Lean.ConstantInfo} (hfresh : fe.env.find? ci.name = none)
    (hsees : fe.sees ci.name ci = true) : (fe.push ci).find? ci.name = some ci := by
  rw [FEnv.find?_eq_filter, push_find, find_addConst hlaws hfresh]
  have hs' : (fe.push ci).sees = fe.sees := by rfl
  simp only [↓reduceIte, Option.filter_some, hs', hsees]

theorem push_env_find (hlaws : EnvLaws) {ci : Lean.ConstantInfo} (hfresh : fe.env.find? ci.name = none)
    {n : Name} (hn : n ≠ ci.name) : (fe.push ci).env.find? n = fe.env.find? n := by
  rw [push_find, find_addConst hlaws hfresh]
  exact ite_eq_right hn

/-- **A fresh plain entry pushed keeps the job's premises** but well-formedness,
which is master's. -/
theorem jobEnvI_push_plain (hlaws : EnvLaws) (hP : EnvPresI fe L) (hR : ProjBodiesInRange fe)
    {ci : Lean.ConstantInfo} {cci : ConLeche.ConstantInfo} (hfresh : fe.env.find? ci.name = none)
    (hsees : fe.sees ci.name ci = true) (hname : cci.name = toName ci.name)
    (hrel : EntryRelI (fe.push ci) ci cci) (hni : ∀ v, ci ≠ .inductInfo v) :
    EnvPresI (fe.push ci) (L.pushDelta [cci] []) ∧ ProjBodiesInRange (fe.push ci) :=
  ⟨presI_push_plain hlaws hP hfresh hsees hname hrel
      (findTable_notInd (find_push_self hlaws hfresh hsees) hni),
    projBodiesInRange_one hlaws hR (ctorsStored_of_pres hP) hfresh hni⟩

/-! ## The constructors -/

theorem pushDelta_one (L : ConLeche.Env) (c : ConLeche.ConstantInfo) :
    ({ consts := c :: L.consts, tables := L.tables } : ConLeche.Env) = L.pushDelta [c] [] := by
  simp [ConLeche.Env.pushDelta]

/-- **A member's constructors pushed** against master's `consSumCtors`. -/
theorem presI_consSumCtorsF (hlaws : EnvLaws) {T : Name} {nP : Nat} :
    ∀ (cs : List (Lean.ConstantVal × Nat)) (i : Nat) {fe : InLean.FEnv} {L : ConLeche.Env},
      EnvPresI fe L → ProjBodiesInRange fe →
      (∀ c ∈ cs, fe.env.find? c.1.name = none) → (cs.map (·.1.name)).Nodup →
      (∀ c ∈ cs, c.1.name = InLean.sorryAxName → fe.coreAxioms = true) →
      (∀ c ∈ cs, okC c.1.type = true) →
      EnvPresI (InLean.consSumCtorsF T nP i cs fe) (ConLeche.consSumCtors nP (cs.map trCtor) L) ∧
        ProjBodiesInRange (InLean.consSumCtorsF T nP i cs fe) ∧
        (∀ n, n ∉ cs.map (·.1.name) → (InLean.consSumCtorsF T nP i cs fe).env.find? n = fe.env.find? n) ∧
        (InLean.consSumCtorsF T nP i cs fe).coreAxioms = fe.coreAxioms
  | [], _, fe, L, hP, hR, _, _, _, _ => ⟨hP, hR, fun _ _ => rfl, rfl⟩
  | c :: cs, i, fe, L, hP, hR, hfr, hnd, hso, hok => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [InLean.consSumCtorsF, List.map_cons, ConLeche.consSumCtors]
    generalize hci : Lean.ConstantInfo.ctorInfo
      { toConstantVal := c.1, induct := T, cidx := i, numParams := nP, numFields := c.2, isUnsafe := false } = ci
    have hcn : ci.name = c.1.name := by rw [← hci]; rfl
    have hfr0 : fe.env.find? ci.name = none := by rw [hcn]; exact hfr c List.mem_cons_self
    have hsees : fe.sees ci.name ci = true :=
      sees_safe (by rw [← hci]; rfl) (fun h => hso c List.mem_cons_self (hcn ▸ h))
    have hrel : EntryRelI (fe.push ci) ci (.ctorInfo (trCtor c).1 nP (trCtor c).2) := by
      rw [← hci]
      exact ⟨CVRel_trCV (hok c List.mem_cons_self), rfl, rfl⟩
    obtain ⟨hP1, hR1⟩ := jobEnvI_push_plain hlaws hP hR hfr0 hsees
      (by rw [hcn]; rfl) hrel (by intro v h; rw [← hci] at h; cases h)
    rw [pushDelta_one] at *
    obtain ⟨hP2, hR2, hold, hcore⟩ := presI_consSumCtorsF hlaws cs (i + 1) hP1 hR1
      (fun d hd => by
        rw [push_env_find hlaws hfr0 (by rw [hcn]; exact fun h => hnd.1 ⟨d, hd, h⟩)]
        exact hfr d (List.mem_cons_of_mem _ hd))
      hnd.2 (fun d hd => hso d (List.mem_cons_of_mem _ hd)) (fun d hd => hok d (List.mem_cons_of_mem _ hd))
    rw [← pushDelta_one] at hP2
    refine ⟨hP2, hR2, fun n hn => ?_, hcore⟩
    simp only [List.mem_cons, not_or] at hn
    rw [hold n hn.2, push_env_find hlaws hfr0 (by rw [hcn]; exact hn.1)]

/-- The block's constructor names, member by member. -/
@[expose] def ctorNamesOf (ms : List InLean.MemberShape) : List Name :=
  ms.flatMap fun m => m.ctors.map (·.1.name)

/-- **All members' constructors pushed** against master's `consBlockCtors`. -/
theorem presI_consBlockCtorsF_go (hlaws : EnvLaws) {nP : Nat} :
    ∀ (ms : List InLean.MemberShape) {fe : InLean.FEnv} {L : ConLeche.Env},
      EnvPresI fe L → ProjBodiesInRange fe →
      (∀ m ∈ ms, ∀ c ∈ m.ctors, fe.env.find? c.1.name = none) → (ctorNamesOf ms).Nodup →
      (∀ m ∈ ms, ∀ c ∈ m.ctors, c.1.name = InLean.sorryAxName → fe.coreAxioms = true) →
      (∀ m ∈ ms, ∀ c ∈ m.ctors, okC c.1.type = true) →
      EnvPresI (ms.foldl (fun fe m => InLean.consSumCtorsF m.cvT.name nP 0 m.ctors fe) fe)
          (ConLeche.consBlockCtors nP (ms.map fun m => m.ctors.map trCtor) L) ∧
        ProjBodiesInRange (ms.foldl (fun fe m => InLean.consSumCtorsF m.cvT.name nP 0 m.ctors fe) fe)
  | [], fe, L, hP, hR, _, _, _, _ => ⟨hP, hR⟩
  | m :: ms, fe, L, hP, hR, hfr, hnd, hso, hok => by
    simp only [ctorNamesOf, List.flatMap_cons, List.nodup_append] at hnd
    simp only [List.foldl_cons, List.map_cons, ConLeche.consBlockCtors]
    obtain ⟨hP1, hR1, hold, hcore⟩ := presI_consSumCtorsF hlaws (T := m.cvT.name) (nP := nP) m.ctors 0
      hP hR (hfr m List.mem_cons_self) hnd.1 (hso m List.mem_cons_self) (hok m List.mem_cons_self)
    refine presI_consBlockCtorsF_go hlaws ms hP1 hR1 (fun m' hm' c hc => ?_) hnd.2.1
      (fun m' hm' c hc h => by rw [hcore]; exact hso m' (List.mem_cons_of_mem _ hm') c hc h)
      (fun m' hm' c hc => hok m' (List.mem_cons_of_mem _ hm') c hc)
    have hnot : c.1.name ∉ m.ctors.map (·.1.name) := by
      intro hin
      exact hnd.2.2 _ hin _ (List.mem_flatMap.2 ⟨m', hm', List.mem_map_of_mem hc⟩) rfl
    rw [hold _ hnot]
    exact hfr m' (List.mem_cons_of_mem _ hm') c hc

theorem trShape_memberCtors_trCtor (p : InLean.BlockShape) :
    (trShape p).memberCtors = p.members.map fun m => m.ctors.map trCtor := by
  simp [ConLeche.BlockShape.memberCtors, trShape, trMember]

/-- **`JobEnvI` at the constructors' push** (`consBlockCtorsF`, the recursor
stage's input): the constructors' names fresh and distinct (the
constructors' stage's `checkConstantValC`), their types with a reading;
well-formedness is master's (`checkBlockPassS_run`'s `consBlockCtors`
conjunct). -/
theorem jobEnvI_ctors (hJ : JobEnvI fe L) (p : InLean.BlockShape)
    (hfr : ∀ m ∈ p.members, ∀ c ∈ m.ctors, fe.env.find? c.1.name = none)
    (hnd : (ctorNamesOf p.members).Nodup)
    (hso : ∀ m ∈ p.members, ∀ c ∈ m.ctors, c.1.name = InLean.sorryAxName → fe.coreAxioms = true)
    (hok : ∀ m ∈ p.members, ∀ c ∈ m.ctors, okC c.1.type = true)
    (hwf : ConLeche.EnvWF (ConLeche.consBlockCtors (trShape p).nP (trShape p).memberCtors L)) :
    JobEnvI (InLean.consBlockCtorsF p fe)
      (ConLeche.consBlockCtors (trShape p).nP (trShape p).memberCtors L) := by
  rw [trShape_memberCtors_trCtor] at hwf ⊢
  obtain ⟨hP, hR⟩ := presI_consBlockCtorsF_go hJ.laws (nP := p.nP) p.members hJ.pres hJ.proj hfr hnd
    hso hok
  exact ⟨hJ.laws, hP, hwf, hR⟩

/-! ## The rule-less recursors -/

theorem trShape_majorIdxAt (p : InLean.BlockShape) (m : Nat) :
    (trShape p).majorIdxAt m = p.majorIdxAt m := by
  unfold ConLeche.BlockShape.majorIdxAt InLean.BlockShape.majorIdxAt
  simp only [trShape, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases p.recs[m]? <;> rfl

theorem trShape_rulePrefixAt (p : InLean.BlockShape) (m : Nat) :
    (trShape p).rulePrefixAt m = p.rulePrefixAt m := by
  unfold ConLeche.BlockShape.rulePrefixAt InLean.BlockShape.rulePrefixAt
  simp only [trShape, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases p.recs[m]? <;> rfl

/-- A rule-less recursor entry against master's record. -/
theorem entryRelI_recEntry (fe : InLean.FEnv) (p : InLean.BlockShape) {cv : Lean.ConstantVal}
    {mI rP : Nat} (hok : okC cv.type = true) (hle : rP ≤ mI) :
    EntryRelI fe (InLean.recEntry p cv mI rP false []) (.recInfo (trCV cv) mI rP false []) := by
  refine ⟨trCV cv, [], ?_, CVRel_trCV hok, .nil⟩
  simp only [InLean.majorIdxOf, InLean.rulePrefixOf]
  congr 1
  omega

/-- **The rule-less recursors pushed** against master's `consBlockRecsBare`
(the second components, the index counts, are read by neither). -/
theorem presI_consBlockRecsBareF (hlaws : EnvLaws) {p : InLean.BlockShape}
    (hle : ∀ rc ∈ p.recs, rc.rP ≤ rc.mI) :
    ∀ (l : List (Lean.ConstantVal × Nat)) (l' : List (ConLeche.ConstantVal × Nat)) (m : Nat)
      {fe : InLean.FEnv} {L : ConLeche.Env},
      l'.map Prod.fst = l.map (trCV ·.1) →
      EnvPresI fe L → ProjBodiesInRange fe →
      (∀ x ∈ l, fe.env.find? x.1.name = none) → (l.map (·.1.name)).Nodup →
      (∀ x ∈ l, x.1.name = InLean.sorryAxName → fe.coreAxioms = true) →
      (∀ x ∈ l, okC x.1.type = true) →
      EnvPresI (InLean.consBlockRecsBareF p m l fe) (ConLeche.consBlockRecsBare (trShape p) m l' L) ∧
        ProjBodiesInRange (InLean.consBlockRecsBareF p m l fe)
  | [], [], _, fe, L, _, hP, hR, _, _, _, _ => ⟨hP, hR⟩
  | [], _ :: _, _, _, _, hl, _, _, _, _, _, _ => by cases hl
  | _ :: _, [], _, _, _, hl, _, _, _, _, _, _ => by cases hl
  | x :: l, x' :: l', m, fe, L, hl, hP, hR, hfr, hnd, hso, hok => by
    simp only [List.map_cons, List.cons.injEq] at hl
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨cv', n'⟩ := x'
    obtain ⟨cv, n⟩ := x
    simp only at hl
    obtain ⟨rfl, hl⟩ := hl
    simp only [InLean.consBlockRecsBareF, ConLeche.consBlockRecsBare]
    generalize hci : InLean.recEntry p cv (p.majorIdxAt m) (p.rulePrefixAt m) false [] = ci
    have hcn : ci.name = cv.name := by rw [← hci]; rfl
    have hfr0 : fe.env.find? ci.name = none := by rw [hcn]; exact hfr _ List.mem_cons_self
    have hsees : fe.sees ci.name ci = true :=
      sees_safe (by rw [← hci]; rfl) (fun h => hso _ List.mem_cons_self (hcn ▸ h))
    have hle' : p.rulePrefixAt m ≤ p.majorIdxAt m := by
      unfold InLean.BlockShape.rulePrefixAt InLean.BlockShape.majorIdxAt
      rw [List.getD_eq_getElem?_getD]
      cases h : p.recs[m]? with
      | none => exact Nat.le_refl _
      | some rc => exact hle rc (List.mem_of_getElem? h)
    have hrel := entryRelI_recEntry (fe.push ci) p (hok _ List.mem_cons_self) hle'
    rw [hci] at hrel
    obtain ⟨hP1, hR1⟩ := jobEnvI_push_plain hlaws hP hR hfr0 hsees (by rw [hcn]; rfl) hrel
      (by intro v h; rw [← hci] at h; cases h)
    rw [trShape_majorIdxAt, trShape_rulePrefixAt, pushDelta_one]
    exact presI_consBlockRecsBareF hlaws hle l l' (m + 1) hl hP1 hR1
      (fun d hd => by
        rw [push_env_find hlaws hfr0 (by rw [hcn]; exact fun h => hnd.1 ⟨d, hd, h⟩)]
        exact hfr d (List.mem_cons_of_mem _ hd))
      hnd.2 (fun d hd => hso d (List.mem_cons_of_mem _ hd)) (fun d hd => hok d (List.mem_cons_of_mem _ hd))

theorem zip_fst_sublist {α β : Type} : ∀ (l₁ : List α) (l₂ : List β),
    ((l₁.zip l₂).map Prod.fst).Sublist l₁
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l₁, b :: l₂ => by
    simp only [List.zip_cons_cons, List.map_cons]
    exact (zip_fst_sublist l₁ l₂).cons_cons a

/-- **`JobEnvI` at the rule-less recursors' environment** (`classFeR`, which
InLean's `classFeROvl` is; master's `genRecCheck` pushes by `classFeR`
on `mkFEnv L`, which is `mkFEnv (ruleEnv …)`, `classFeR_mkFEnv`).
Well-formedness is master's `envWF_ruleEnv` from master's checked recursor
types. -/
theorem jobEnvI_ruleEnv (hJ : JobEnvI fe L) {p : InLean.BlockShape} {Ms : List InLean.TargetMajor}
    {cvGs : List Lean.ConstantVal} {recCls : List Nat} (s : InLean.CState)
    (hle : ∀ rc ∈ p.recs, rc.rP ≤ rc.mI)
    (hfr : ∀ x ∈ cvGs, fe.env.find? x.name = none) (hnd : (cvGs.map (·.name)).Nodup)
    (hso : ∀ x ∈ cvGs, x.name = InLean.sorryAxName → fe.coreAxioms = true)
    (hok : ∀ x ∈ cvGs, okC x.type = true)
    {g : ConLeche.ClassGen} {k : Nat} {cvRis : List ConLeche.ConstantVal} {cls : List Nat}
    (hT : Runs (ConLeche.classRecTysOk (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L) g k
      (trShape p).recs cvRis cls) (cvGs.map trCV)) :
    JobEnvI (InLean.classFeR p Ms cvGs recCls fe)
      (ConLeche.Cached.ruleEnv (trShape p) (Ms.map (trTM s)) (cvGs.map trCV) recCls L) := by
  have hmem : ∀ x ∈ (cvGs.zip recCls).map (fun (x : Lean.ConstantVal × Nat) =>
      (x.1, (Ms.getD x.2 default).nIdx)), x.1 ∈ cvGs := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact (List.of_mem_zip hy).1
  have hnd' : (((cvGs.zip recCls).map fun (x : Lean.ConstantVal × Nat) =>
      (x.1, (Ms.getD x.2 default).nIdx)).map (·.1.name)).Nodup := by
    rw [List.map_map]
    have h2 := ((zip_fst_sublist cvGs recCls).map (·.name)).nodup hnd
    rw [List.map_map] at h2
    exact h2
  have hl : (((cvGs.map trCV).zip recCls).map fun (x : ConLeche.ConstantVal × Nat) =>
      (x.1, ((Ms.map (trTM s)).getD x.2 default).nIdx)).map Prod.fst =
      ((cvGs.zip recCls).map fun (x : Lean.ConstantVal × Nat) =>
        (x.1, (Ms.getD x.2 default).nIdx)).map (trCV ·.1) := by
    rw [List.map_map, List.map_map, List.zip_map_left, List.map_map]
    rfl
  obtain ⟨hP, hR⟩ := presI_consBlockRecsBareF hJ.laws hle _ _ 0 hl hJ.pres hJ.proj
    (fun x hx => hfr _ (hmem x hx)) hnd' (fun x hx => hso _ (hmem x hx)) (fun x hx => hok _ (hmem x hx))
  exact ⟨hJ.laws, hP, ConLeche.Cached.envWF_ruleEnv hJ.wf hT _ _, hR⟩


/-! ## The stage's guards, translated -/

theorem isNeverZero_tr : ∀ u : Lean.Level, ConLeche.Level.isNeverZero (trL u) = InLean.isNeverZero u
  | .zero => rfl
  | .succ _ => rfl
  | .max a b => by
    simp only [trL, ConLeche.Level.isNeverZero, InLean.isNeverZero, isNeverZero_tr a, isNeverZero_tr b]
  | .imax _ b => by simp only [trL, ConLeche.Level.isNeverZero, InLean.isNeverZero, isNeverZero_tr b]
  | .param _ => rfl
  | .mvar _ => rfl

theorem numCtorsOf_tr : ∀ l : List InLean.MemberShape,
    ConLeche.numCtorsOf (l.map trMember) = InLean.numCtorsOf l
  | [] => rfl
  | m :: l => by
    simp only [List.map_cons, ConLeche.numCtorsOf, InLean.numCtorsOf, numCtorsOf_tr l, trMember,
      List.length_map]

theorem blockLargeElimAllowed_tr (p : InLean.BlockShape) (b : Bool) :
    ConLeche.blockLargeElimAllowed (trShape p) b = InLean.blockLargeElimAllowed p b := by
  unfold ConLeche.blockLargeElimAllowed InLean.blockLargeElimAllowed
  rw [trShape_k]
  simp only [trShape, ConLeche.BlockShape.numCtors, InLean.BlockShape.numCtors, numCtorsOf_tr,
    isNeverZero_tr]

theorem structElimLevel_tr (elim : Lean.Name) (large : Bool) :
    ConLeche.structElimLevel (toName elim) large = trL (InLean.structElimLevel elim large) := by
  unfold ConLeche.structElimLevel InLean.structElimLevel
  cases large <;> rfl

theorem any_member_trTM (s : InLean.CState) (Ms : List InLean.TargetMajor) :
    (Ms.map (trTM s)).any (·.member.isNone) = Ms.any (·.member.isNone) := by
  simp [List.any_map, Function.comp_def, trTM]

theorem minors_trCR (s : InLean.CState) (rd : InLean.ClassRead) :
    ((trCR s rd).slots.filter ConLeche.ClassSlot.isMinor).length =
      (rd.slots.filter InLean.ClassSlot.isMinor).length := by
  simp only [trCR]
  induction rd.slots with
  | nil => rfl
  | cons sl sls ih =>
    cases sl <;> simp_all [trSlot, List.filter_cons, ConLeche.ClassSlot.isMinor, InLean.ClassSlot.isMinor]

theorem ctorsSum_tr (s : InLean.CState) (xss : List (List InLean.ClassCtor)) :
    ((xss.map (·.map (trCC s))).map List.length).sum = (xss.map List.length).sum := by
  simp [Function.comp_def]

theorem classRecOf_tr (recCls : List Nat) (cvGs : List Lean.ConstantVal) (t : Nat) :
    ConLeche.classRecOf recCls (cvGs.map trCV) t = (InLean.classRecOf recCls cvGs t).map toName := by
  unfold ConLeche.classRecOf InLean.classRecOf
  rw [List.length_map, Option.map_map]
  congr 1
  funext r
  simp only [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases cvGs[r]? <;> rfl

/-! ## The former types -/

/-- **A class's former type is closed** (master's side): a member's
declared type, or a stored former's telescope at the class's levels. -/
theorem classFormerTy_lbb {L : ConLeche.Env} (hwf : ConLeche.EnvWF L) {formers : List ConLeche.ConstantVal}
    {M : ConLeche.TargetMajor} {v : ConLeche.Expr}
    (hT : ∀ cv ∈ formers, cv.type.looseBVarsBounded 0 = true)
    (hmem : ∀ t, M.member = some t → t < formers.length)
    (hR : Runs (ConLeche.classFormerTy (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L) formers M) v) :
    v.looseBVarsBounded 0 = true := by
  obtain ⟨F, hrun⟩ := hR
  rw [ConLeche.classFormerTy_datF] at hrun
  unfold ConLeche.classFormerTy at hrun
  split at hrun
  · rename_i t ht
    simp only [pure, Except.pure, Except.ok.injEq] at hrun
    subst hrun
    have htl := hmem t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl, Option.getD_some]
    exact hT _ (List.getElem_mem htl)
  · split at hrun
    · rename_i cv caps hf
      simp only [bind, Except.bind] at hrun
      split at hrun
      · simp at hrun
      rename_i ty hfam
      simp only [pure, Except.pure, Except.ok.injEq] at hrun
      subst hrun
      rw [ConLeche.mkFEnv_find?_fun] at hf
      have hw := hwf.consts _ (List.mem_of_find?_eq_some hf)
      rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
      exact ConLeche.familyTelescope_bounded
        (fun _ _ _ hw he => ConLeche.whnf_looseBVars hwf F hw he) hfam hw.2.2.2.1
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun

/-- **The classes' former types** (`Ms.mapM classFormerTy`), elementwise
`classFormerTyI_run`, closed. -/
theorem classFormerTysI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hRF : ReducedFormerSimI) {formers : List Lean.ConstantVal}
    (hfo : ∀ cv ∈ formers, okC cv.type = true ∧ (trC cv.type).looseBVarsBounded 0 = true) :
    ∀ (Ms : List InLean.TargetMajor) {s₀ s' : InLean.CState} {v : List Lean.Expr},
      CSOKI .verified false L s₀ →
      (∀ M ∈ Ms, OkTMN s₀ M ∧ ∀ t, M.member = some t → t < formers.length) →
      Ms.mapM (InLean.classFormerTy .verified fe formers) s₀ = .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ OkSL s' v = true ∧ v.length = Ms.length ∧
        (∀ f ∈ v, (TrS s' f).looseBVarsBounded 0 = true) ∧
        RunsAll (ConLeche.classFormerTy (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L)
          (formers.map trCV)) (Ms.map (trTM s₀)) (TrSL s' v)
  | [], s₀, s', v, hs, _, h => by
    rw [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, rfl, rfl, (fun _ h => by cases h), trivial⟩
  | M :: Ms, s₀, s', v, hs, hMs, h => by
    rw [List.mapM_cons] at h
    obtain ⟨x, s₁, h1, h⟩ := bind_run h
    obtain ⟨xs, s₂, h2, h⟩ := bind_run h
    obtain ⟨rfl, rfl⟩ := pure_run h
    obtain ⟨hok, hmem⟩ := hMs M List.mem_cons_self
    obtain ⟨hs₁, ht₁, hxo, hR1⟩ := classFormerTyI_run hJ hRF hs hok.1 (fun cv h => (hfo cv h).1) hmem h1
    obtain ⟨hs₂, ht₂, hxso, hlen, hxsl, hR2⟩ := classFormerTysI_run hJ hRF hfo Ms hs₁
      (fun M' h => ⟨(OkTMN.mono ht₁ (hMs M' (List.mem_cons_of_mem _ h)).1).1,
        (hMs M' (List.mem_cons_of_mem _ h)).2⟩) h2
    have hxl : (TrS s₁ x).looseBVarsBounded 0 = true := by
      refine classFormerTy_lbb hJ.wf (formers := formers.map trCV) (fun cv hcv => ?_) ?_ hR1
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hcv
        exact (hfo c hc).2
      · intro t ht; rw [List.length_map]; exact hmem t ht
    rw [map_trTM_mono ht₁ (fun M' h => (hMs M' (List.mem_cons_of_mem _ h)).1)] at hR2
    refine ⟨hs₂, ht₁.trans ht₂, by simp [OkSL_cons, okS_of_tabLe ht₂ hxo, hxso], by simp [hlen],
      fun f hf => ?_, ?_⟩
    · rcases List.mem_cons.1 hf with rfl | hf
      · rw [TrS_of_tabLe ht₂ hxo]; exact hxl
      · exact hxsl f hf
    · rw [List.map_cons, TrSL_cons, TrS_of_tabLe ht₂ hxo]
      exact ⟨hR1, hR2⟩


/-! ## What the stage's runs give beside their readings -/

theorem targetMajorNfs_sub {mode : InLean.CheckMode} {fe : InLean.FEnv} {p : InLean.BlockShape}
    {formerTys pfvs : List Lean.Expr} {us : List Lean.Level} {ds : List Lean.Expr}
    {ctors : List (Lean.ConstantVal × Nat)} :
    ∀ (tbl : List InLean.NestCtorNf) {s₀ s' : InLean.CState} {r : List InLean.NestCtorNf},
      InLean.targetMajorNfs mode fe p formerTys pfvs us ds ctors tbl s₀ = .ok (r, s') →
      ∀ e ∈ r, e ∈ tbl
  | [], s₀, s', r, h => by
    unfold InLean.targetMajorNfs at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    intro e he; cases he
  | e :: es, s₀, s', r, h => by
    unfold InLean.targetMajorNfs at h
    obtain ⟨rest, s₁, h1, h⟩ := bind_run h
    have ih := targetMajorNfs_sub es h1
    split at h
    · obtain ⟨b, s₂, -, h⟩ := bind_run h
      split at h
      · obtain ⟨rfl, rfl⟩ := pure_run h
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih x hx)
      · obtain ⟨rfl, rfl⟩ := pure_run h
        exact fun x hx => List.mem_cons_of_mem _ (ih x hx)
    · obtain ⟨rfl, rfl⟩ := pure_run h
      exact fun x hx => List.mem_cons_of_mem _ (ih x hx)

/-- **The classes' entries come from the positivity table.** -/
theorem classesNfs_sub {mode : InLean.CheckMode} {fe : InLean.FEnv} {p : InLean.BlockShape}
    {formerTys : List Lean.Expr} {tbl : List InLean.NestCtorNf} :
    ∀ (Ms : List InLean.TargetMajor) {s₀ s' : InLean.CState} {v : List InLean.TargetMajor},
      InLean.classesNfs mode fe p formerTys tbl Ms s₀ = .ok (v, s') →
      ∀ M ∈ v, ∀ e ∈ M.nfs, e ∈ tbl
  | [], s₀, s', v, h => by
    unfold InLean.classesNfs at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    intro M hM; cases hM
  | M :: Ms, s₀, s', v, h => by
    unfold InLean.classesNfs at h
    obtain ⟨es, s₁, h1, h⟩ := bind_run h
    obtain ⟨rest, s₂, h2, h⟩ := bind_run h
    obtain ⟨rfl, rfl⟩ := pure_run h
    intro M' hM'
    rcases List.mem_cons.1 hM' with rfl | hM'
    · exact targetMajorNfs_sub tbl h1
    · exact classesNfs_sub Ms h2 M' hM'

theorem classConstOk_fresh {mode : InLean.CheckMode} {fe : InLean.FEnv} {cv : Lean.ConstantVal}
    {s₀ s' : InLean.CState} {r : Unit} (h : InLean.classConstOk mode fe cv s₀ = .ok (r, s')) :
    fe.env.find? cv.name = none := by
  unfold InLean.classConstOk at h
  cases hf : fe.env.find? cv.name with
  | none => rfl
  | some ci =>
    rw [hf] at h
    simp only [Option.isSome_some, ↓reduceIte] at h
    obtain ⟨_, _, h1, _⟩ := bindI_ok h
    exact (throwI_ok h1).elim

theorem classRecTyOk_facts {mode : InLean.CheckMode} {fe : InLean.FEnv} {g : InLean.ClassGen}
    {k : Nat} {rc : InLean.RecShape} {cvRi : Lean.ConstantVal} {c : Nat} {s₀ s' : InLean.CState}
    {x : Lean.ConstantVal} (h : InLean.classRecTyOk mode fe g k rc cvRi c s₀ = .ok (x, s')) :
    rc.rP ≤ rc.mI ∧ fe.env.find? x.name = none ∧ x.name = rc.cvR.name := by
  unfold InLean.classRecTyOk at h
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k' : α → InLean.CheckCM Lean.ConstantVal}
      {s₁ : InLean.CState}, ¬ ((throw e : InLean.CheckCM α) >>= k') s₁ = .ok (x, s') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bindI_ok h; exact (throwI_ok h1).elim
  cases g1 : (rc.tgt == (g.cls.getD c default).member.getD k) <;> simp only [g1] at h
  · exact absurd h hth
  cases g2 : (rc.rP == g.nP + g.slots.length && rc.mI == rc.rP + (g.cls.getD c default).nIdx) <;>
    simp only [g2] at h
  · exact absurd h hth
  simp only [Bool.and_eq_true, beq_iff_eq] at g2
  simp only [↓reduceIte] at h
  obtain ⟨gty?, s₁, -, h⟩ := bindI_ok h
  obtain ⟨gty, s₂, h2, h⟩ := bindI_ok h
  obtain ⟨-, rfl⟩ := unwrapOrI_run h2
  obtain ⟨_, s₃, -, h⟩ := bindI_ok h
  obtain ⟨_, s₄, h3, h⟩ := bindI_ok h
  have hx := (pureI_ok h).1
  subst hx
  unfold InLean.classRecTyCheck at h3
  obtain ⟨_, _, h4, -⟩ := bindI_ok h3
  exact ⟨by omega, classConstOk_fresh h4, rfl⟩

/-- **The recursor types' run**: each record's rule prefix below its major
index, every generated constant fresh and at its record's name. -/
theorem classRecTysOk_facts {mode : InLean.CheckMode} {fe : InLean.FEnv} {g : InLean.ClassGen}
    {k : Nat} :
    ∀ (rcs : List InLean.RecShape) (cvs : List Lean.ConstantVal) (cs : List Nat)
      {s₀ s' : InLean.CState} {v : List Lean.ConstantVal},
      InLean.classRecTysOk mode fe g k rcs cvs cs s₀ = .ok (v, s') →
      (∀ rc ∈ rcs, rc.rP ≤ rc.mI) ∧ (∀ x ∈ v, fe.env.find? x.name = none) ∧
        v.map (·.name) = rcs.map (·.cvR.name)
  | [], cvs, cs, s₀, s', v, h => by
    unfold InLean.classRecTysOk at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨(fun _ h => by cases h), (fun _ h => by cases h), rfl⟩
  | rc :: rcs, cvRi :: cvs, c :: cs, s₀, s', v, h => by
    unfold InLean.classRecTysOk at h
    obtain ⟨x, s₁, h1, h⟩ := bindI_ok h
    obtain ⟨xs, s₂, h2, h⟩ := bindI_ok h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    obtain ⟨hle, hfr, hn⟩ := classRecTyOk_facts h1
    obtain ⟨hle', hfr', hn'⟩ := classRecTysOk_facts rcs cvs cs h2
    refine ⟨fun r hr => ?_, fun y hy => ?_, by simp [hn, hn']⟩
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact hle
      · exact hle' r hr
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hfr
      · exact hfr' y hy
  | _ :: _, [], _, s₀, s', v, h => by
    unfold InLean.classRecTysOk at h; exact (throwI_ok h).elim
  | _ :: _, _ :: _, [], s₀, s', v, h => by
    unfold InLean.classRecTysOk at h; exact (throwI_ok h).elim

/-- The pins' run: the recursors' names are distinct. -/
theorem targetRecPins_nodup {p : InLean.BlockShape} {block : List Lean.ConstantInfo}
    {s₀ s' : InLean.CState} {u : Unit} (h : InLean.targetRecPins p block s₀ = .ok (u, s')) :
    InLean.namesNodup (p.recs.map (·.cvR.name)) = true := by
  unfold InLean.targetRecPins at h
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k : α → InLean.CheckCM Unit},
      ¬ ((throw e : InLean.CheckCM α) >>= k) s₀ = .ok (u, s') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bind_run h; exact throw_run h1
  cases g1 : InLean.blockRecLpsOk p <;> simp only [g1] at h
  · exact absurd h hth
  cases g2 : InLean.blockRecNamesUnreserved p <;> simp only [g2, ↓reduceIte] at h
  · exact absurd h hth
  split at h
  rotate_left
  · exact absurd h hth
  split at h
  rotate_left
  · exact absurd h hth
  split at h
  rotate_left
  · exact absurd h hth
  rename_i g5
  simpa using g5

end InLeanProof
