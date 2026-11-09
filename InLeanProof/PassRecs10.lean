module

public import InLeanProof.PassRecs9
public import InLeanProof.PassSim
public import InLeanProof.RecFireTr
public import ConLeche.Verify.Inductives.TargetAuxFire
import ConLeche.Verify.Cached.BlockPushes
import ConLeche.Verify.Cached.WalkersC
import ConLeche.Verify.Denote.TeleOpen
/- `ConstantInfo.name` is read as a projection of `toConstantVal`. -/
import all Lean.Declaration
/- `FEnv.pushAll` (not exposed in `InLean/Push.lean`). -/
import all InLean.Push

/-!
# O7-recursors: the generated recursors' environment (task #451, round 8)

* `genStage_majorHead` (master's side): the generated recursor type's
  major domain is its class's inductive (`M.ind`, at the class's levels)
  applied (`classGenRecTy`), at every output.
* `ClassHead`: a class is a member exactly when its inductive is one of
  the block's names (`targetMajorOf`'s two arms, `TargetMajorRun.classHead`);
  the classes' table entries keep it (`classesNfs`).
* `fire_genEntry`: InLean's firing mode read off the generated type at use
  (`recFireAt`) against master's stored one (`generatedFire`): `.plain` at
  a member major (the head is a member), `.nested` at an outside one
  (the head is no member, the arguments are `NestedRead`'s).
* `jobEnvI_genRecs`, `jobEnvI_genRecs_of_run`: the job's environment
  premises at the generated recursors pushed
  (`fe₂.pushAll (blockRecInfosTF p 0 out)`) against master's
  `consBlockRecsT`, from `genRecCheckI_run`'s outputs and master's run.
* `blockTables_tr`, `checkBlockTablesCI_run`: the projection tables InLean
  builds once (`blockTables`) read as master's (the bodies by `projBodyAt_tr`),
  and their check against master's `checkBlockTables` (master's "table taken"
  guard from the members' mark).
-/

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-- **The generated recursor type's major domain is its class's inductive
applied** (`classGenRecTy`), at every output, the output's class being
the stage's class at the recursor's class index. -/
theorem genStage_majorHead {mode : ConLeche.CheckMode} {F : Nat} {env : ConLeche.Env}
    {p : ConLeche.BlockShape} {nestedBit : Bool} {params : List ConLeche.Expr}
    {tbl : List ConLeche.NestCtorNf} {rd : ConLeche.ClassRead} {Ms₀ : List ConLeche.TargetMajor}
    {block : List ConLeche.ConstantInfo}
    {out : List (ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr)}
    (S : ConLeche.GenStageRun mode F (ConLeche.mkFEnv env) p nestedBit params tbl rd Ms₀ block out)
    (hpl : params.length = p.nP)
    {j : Nat} {t : ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr}
    (ht : out[j]? = some t) :
    ∃ c pre dom body, rd.recCls[j]? = some c ∧ t.2.1 = S.Ms.getD c default ∧
      p.rulePrefixAt j ≤ p.majorIdxAt j ∧
      t.1.type.stripPis (p.majorIdxAt j) = some (pre, .forallE dom body) ∧
      dom.getAppFn = .const t.2.1.ind t.2.1.lvls := by
  obtain ⟨hlenG, hallG⟩ := ConLeche.classRecTysOk_run S.hcvGs
  obtain ⟨hlenO, hallO⟩ := ConLeche.classRecsRulesOk_run S.hrules
  have hjo : j < out.length := (List.getElem?_eq_some_iff.mp ht).1
  have hjl : j < p.recs.length := by rw [hlenO, hlenG] at hjo; omega
  obtain ⟨c, cvG, hc, hG, ⟨T⟩⟩ := hallG j p.recs[j] (List.getElem?_eq_getElem hjl)
  obtain ⟨rhss, hoj, -⟩ := hallO j cvG c hG hc
  rw [ht] at hoj
  obtain rfl := Option.some.inj hoj
  refine ⟨c, ?_⟩
  dsimp only
  have hmI : p.majorIdxAt j = p.recs[j].mI := by
    simp [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
  have hrP : p.rulePrefixAt j = p.recs[j].rP := by
    simp [ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
  rw [hmI, hrP]
  have hrPg : p.recs[j].rP = p.nP + rd.slots.length := T.hrP
  have hmIg := T.hmI
  have hcvG := T.hcvG
  have hgty := T.hgty
  have hpre : (ConLeche.genRecGen p params S.Ms S.formerTysC rd S.ctors S.pre).pre.length
      = p.recs[j].rP := by
    rw [hrPg]
    have := ConLeche.ClassGen.prefixBinders_length S.hpre
    simp only [ConLeche.genRecGen] at this ⊢
    rw [this, hpl]
  have hcls : (ConLeche.genRecGen p params S.Ms S.formerTysC rd S.ctors S.pre).cls = S.Ms := rfl
  generalize hg : ConLeche.genRecGen p params S.Ms S.formerTysC rd S.ctors S.pre = g at *
  rw [← hcls]
  generalize hM : g.cls.getD c default = M at *
  rw [hcvG]
  dsimp only
  unfold ConLeche.classGenRecTy at hgty
  obtain ⟨⟨ifs₀, maj⟩, hmaj, hgty⟩ := Option.bind_eq_some_iff.mp hgty
  simp only [Option.pure_def, Option.some.injEq] at hgty
  unfold ConLeche.ClassGen.major at hmaj
  rw [hM] at hmaj
  obtain ⟨ty, hty, hmaj⟩ := Option.bind_eq_some_iff.mp hmaj
  obtain ⟨⟨ifs, o⟩, hifs, hmaj⟩ := Option.bind_eq_some_iff.mp hmaj
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hmaj
  obtain ⟨rfl, rfl⟩ := hmaj
  obtain ⟨-, -, -, hifl, -, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis _ hifs
  have hmIv : p.recs[j].mI = p.recs[j].rP + ifs.length := by rw [hmIg, hifl]
  generalize p.recs[j].rP = rP at *
  generalize p.recs[j].mI = mI at *
  subst hmIv
  have hbsl : (g.pre ++ ifs.map g.binder).length = rP + ifs.length := by simp [hpre]
  obtain ⟨pre', hstrip⟩ := ConLeche.closeTelescope_stripPis (rP + ifs.length)
    (g.pre ++ ifs.map g.binder ++ [ConLeche.Expr.mkAppN (.const M.ind M.lvls) (M.ds ++ ifs)]) 0
    (ConLeche.Expr.mkAppN (g.motVar c) (ifs ++ [.fvar (g.pre.length + ifs.length)
      (ConLeche.Expr.mkAppN (.const M.ind M.lvls) (M.ds ++ ifs))]))
    (by simp [hpre])
  rw [List.drop_left' hbsl] at hstrip
  simp only [ConLeche.closeTelescope, ConLeche.Expr.abstractRange, Nat.zero_add] at hstrip
  rw [hgty] at hstrip
  refine ⟨pre', _, _, hc, rfl, by omega, hstrip, ?_⟩
  rw [ConLeche.abstractRange_mkAppN, ConLeche.Expr.getAppFn_mkAppN]
  rfl

/-- **At a run of the stage**: every output's class is a member exactly
at a member head, and the generated type's major domain is that class's
inductive applied (`genStage_majorHead`), given the input classes'
`ClassHead` (`TargetMajorRun.classHead`) and the recursors' class indices
in range. -/
theorem genRecCheck_majorHead {mode : ConLeche.CheckMode} {F : Nat} {env : ConLeche.Env}
    {p : ConLeche.BlockShape} {nestedBit : Bool} {params : List ConLeche.Expr}
    {tbl : List ConLeche.NestCtorNf} {rd : ConLeche.ClassRead} {Ms₀ : List ConLeche.TargetMajor}
    {block : List ConLeche.ConstantInfo}
    {out : List (ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr)}
    (h : ConLeche.genRecCheck (ConLeche.fueledOps mode F) (ConLeche.mkFEnv env) p nestedBit
      params tbl rd Ms₀ block = .ok out)
    (hpl : params.length = p.nP) (hMs₀ : ∀ M ∈ Ms₀, ClassHead p M)
    (hrc : ∀ c ∈ rd.recCls, c < Ms₀.length)
    {j : Nat} {t : ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr}
    (ht : out[j]? = some t) :
    ClassHead p t.2.1 ∧ p.rulePrefixAt j ≤ p.majorIdxAt j ∧ ∃ pre dom body,
      t.1.type.stripPis (p.majorIdxAt j) = some (pre, .forallE dom body) ∧
      dom.getAppFn = .const t.2.1.ind t.2.1.lvls := by
  obtain ⟨S⟩ := ConLeche.genRecCheck_run h
  obtain ⟨c, pre, dom, body, hc, hM, hle, hs, hf⟩ := genStage_majorHead S hpl ht
  refine ⟨?_, hle, pre, dom, body, hs, hf⟩
  obtain ⟨-, hallN⟩ := ConLeche.classesNfs_run S.hMs
  have hcl : c < Ms₀.length := hrc c (List.mem_of_getElem? hc)
  obtain ⟨nfs, hN, -⟩ := hallN c Ms₀[c] (List.getElem?_eq_getElem hcl)
  rw [hM, List.getD_eq_getElem?_getD, hN, Option.getD_some]
  exact hMs₀ Ms₀[c] (List.getElem_mem hcl)

/-! ## The firing mode at use against the generated one -/

/-- **The firing mode InLean reads off a generated recursor** (`recFireAt`
at a record whose `all` is the block's members and whose type is the
generated one) against master's stored one (`generatedFire`): the major
domain's head is the class's inductive, a member exactly at a member
class (`ClassHead`); at an outside class the domain's arguments are
`NestedRead`'s, so the parameters with the index variables dropped are the
class's pins. -/
theorem fire_genEntry {p : InLean.BlockShape} {rv : RecursorVal} {M : InLean.TargetMajor}
    {s : InLean.CState} {mI rP : Nat} (hok : okC rv.type = true) (hall : rv.all = p.memberNames)
    (hmI : majorIdxOf rv = mI) (hrP : rulePrefixOf rv = rP)
    (hhead : ClassHead (trShape p) (trTM s M))
    {pre : List ConLeche.Expr} {dom body : ConLeche.Expr}
    (hstrip : (trC rv.type).stripPis mI = some (pre, .forallE dom body))
    (hfn : dom.getAppFn = .const (trTM s M).ind (trTM s M).lvls)
    (hargs : M.member = none →
      dom.getAppArgs = ((trTM s M).ds.map (ConLeche.Expr.abstractPrefix rP 0)).map
          (ConLeche.Expr.liftLooseBVars (mI - rP) 0) ++
        (List.range (mI - rP)).map (fun i => ConLeche.Expr.bvar (mI - rP - 1 - i))) :
    FireRel (recFireAt rv false) (ConLeche.generatedFire (trTM s M) rP) := by
  unfold recFireAt
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hmI, hrP, piBody?_eq]
  rw [stripPis_tr] at hstrip
  cases hs : InLean.stripPis mI rv.type with
  | none => rw [hs] at hstrip; cases hstrip
  | some q =>
    obtain ⟨ds, r⟩ := q
    rw [hs] at hstrip
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstrip ⊢
    have hokr : okC (EO.stripTop r) = true := by rw [okC_stripTop]; exact stripPis_okC hok hs
    have htr := hstrip.2
    rw [← trC_stripTop r] at htr
    have hm := stripTop_ne_mdata' r
    generalize EO.stripTop r = x at hokr hm htr
    cases x with
    | forallE n d b bi =>
      have hokd : okC d = true := by
        simp only [okC, okE, Bool.and_eq_true] at hokr; exact hokr.1
      simp only [trC, trE, ConLeche.Expr.forallE.injEq] at htr
      have hdom : dom = trC d := htr.1.symm
      subst hdom
      have hF := fire_head rv.all (mI - rP) hokd _ (getAppFnT_ok hokd) (getAppFnT_not_mdata d)
      refine Eq.mpr (congrArg (FireRel _) ?_) hF
      rw [getAppFn_tr] at hfn
      have hHok := getAppFnT_ok hokd
      have hHm := getAppFnT_not_mdata d
      revert hfn hHok hHm
      generalize Expr.getAppFnT d = H
      intro hfn hHok hHm
      cases H with
      | const n us =>
        simp only [trC, trE, trTM, ConLeche.Expr.const.injEq] at hfn
        obtain ⟨hn, hus⟩ := hfn
        obtain rfl := toName_inj hn
        unfold ClassHead at hhead
        simp only [trTM, trShape_memberNames, contains_map_toName] at hhead
        rw [hall]
        cases hmem : M.member with
        | some t =>
          rw [hmem] at hhead
          have hc : p.memberNames.contains M.ind = true := hhead
          have hlt : (p.memberNames.findIdx? (· == M.ind)).getD p.memberNames.length <
              p.memberNames.length := by
            have hin : M.ind ∈ p.memberNames := by simpa using hc
            obtain ⟨i, hi⟩ : ∃ i, p.memberNames.findIdx? (· == M.ind) = some i := by
              apply Option.isSome_iff_exists.1
              rw [List.findIdx?_isSome, List.any_eq_true]
              exact ⟨M.ind, hin, by simp⟩
            rw [hi]; exact (List.findIdx?_eq_some_iff_getElem.1 hi).1
          rw [ite_eq_left_of_eq_true _ _ (eq_true (show (tgtAtHead p.memberNames (.const M.ind us)).getD
            p.memberNames.length < p.memberNames.length from hlt))]
          simp [ConLeche.generatedFire, trTM, hmem]
        | none =>
          rw [hmem] at hhead
          have hc : p.memberNames.contains M.ind = false := hhead
          have hnone : p.memberNames.findIdx? (· == M.ind) = none := by
            rw [List.findIdx?_eq_none_iff]
            intro a ha
            cases he : a == M.ind
            · rfl
            · have : a = M.ind := by simpa using he
              subst this
              simp [ha] at hc
          rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (tgtAtHead p.memberNames (.const M.ind us)).getD
            p.memberNames.length < p.memberNames.length by
              show ¬ (p.memberNames.findIdx? (· == M.ind)).getD _ < _
              rw [hnone]; exact Nat.lt_irrefl _))]
          have hA := hargs hmem
          simp only [ConLeche.generatedFire, trTM, hmem, ConLeche.auxRuleFire, cFireAtHead, trC, trE]
          rw [show trE (fun _ => none) d = trC d from rfl, hA, ← hus]
          congr 1
          simp only [List.length_append, List.length_map, List.length_range, Nat.add_sub_cancel]
          rw [List.take_left' (by simp), List.map_map]
          conv => lhs; rw [← List.map_id ((TrSL s M.ds).map (ConLeche.Expr.abstractPrefix rP 0))]
          exact (List.map_congr_left fun e _ => ConLeche.Expr.dropVars_lift e _).symm
      | mdata m b => exact absurd rfl (hHm m b)
      | _ =>
        simp [trC, trE] at hfn
    | mdata m b => exact absurd rfl (hm m b)
    | _ => simp [trC, trE] at htr

/-! ## One generated recursor's entry -/

theorem storedT_trC {r : Lean.Expr} (h : okC r = true) : StoredT r (trC r) :=
  ⟨fvarS_of_toExprC (toExpr_of_okE _ h), RangeOk_of_okE h, toExpr_of_okE _ h⟩

theorem sumRules_map_plain : ∀ (cs : List (ConLeche.ConstantVal × Nat)) (rhss : List ConLeche.Expr),
    (ConLeche.sumRules cs rhss).map ({ · with fire := .plain }) = ConLeche.sumRules cs rhss
  | c :: cs, rhs :: rhss => by
    simp only [ConLeche.sumRules, List.map_cons, sumRules_map_plain cs rhss]
  | [], _ => by simp [ConLeche.sumRules]
  | _ :: _, [] => by simp [ConLeche.sumRules]

/-- Master's generated rules all fire `generatedFire`. -/
theorem generatedRules_eq (rP : Nat) (M : ConLeche.TargetMajor) (rhss : List ConLeche.Expr) :
    ConLeche.generatedRules rP M rhss =
      (ConLeche.sumRules M.ctors rhss).map ({ · with fire := ConLeche.generatedFire M rP }) := by
  unfold ConLeche.generatedRules ConLeche.generatedFire
  cases M.member with
  | none => rfl
  | some _ => exact (sumRules_map_plain _ _).symm

theorem sumRules_rel {F : InLean.RecRuleFire} {cF : ConLeche.RecRuleFire} (hF : FireRel F cF) :
    ∀ (cs : List (Lean.ConstantVal × Nat)) (rhss : List Lean.Expr), (∀ r ∈ rhss, okC r = true) →
      LRel (RuleRelS F) (InLean.sumRules cs rhss)
        ((ConLeche.sumRules (cs.map trCtor) (rhss.map trC)).map ({ · with fire := cF }))
  | c :: cs, rhs :: rhss, h => by
    simp only [InLean.sumRules, List.map_cons, ConLeche.sumRules]
    exact .cons ⟨⟨rfl, rfl, hF⟩, storedT_trC (h rhs List.mem_cons_self)⟩
      (sumRules_rel hF cs rhss fun r hr => h r (List.mem_cons_of_mem _ hr))
  | [], _, _ => by simp only [InLean.sumRules, List.map_nil, ConLeche.sumRules]; exact .nil
  | _ :: _, [], _ => by simp only [InLean.sumRules, List.map_cons, List.map_nil, ConLeche.sumRules]; exact .nil

/-- **A generated recursor's entry against master's record**: the counts,
the K flag (`recKExpected_tr`), the type, and rule by rule the
constructor, the field count, the stored right-hand side and the firing
mode read at use (`fire_genEntry`'s premise). -/
theorem entryRelI_genEntry (fe : InLean.FEnv) (p : InLean.BlockShape) (s : InLean.CState)
    {cv : Lean.ConstantVal} {M : InLean.TargetMajor} {rhss : List Lean.Expr} {mI rP : Nat}
    (hok : okC cv.type = true) (hrhs : ∀ r ∈ rhss, okC r = true) (hle : rP ≤ mI)
    (hfire : ∀ rv : RecursorVal, rv.type = cv.type → rv.all = p.memberNames →
      majorIdxOf rv = mI → rulePrefixOf rv = rP →
      FireRel (recFireAt rv false) (ConLeche.generatedFire (trTM s M) rP)) :
    EntryRelI fe (InLean.recEntry p cv mI rP (InLean.recKExpected p M) (InLean.generatedRules M rhss))
      (.recInfo (trCV cv) mI rP (ConLeche.recKExpected (trShape p) (trTM s M))
        (ConLeche.generatedRules rP (trTM s M) (TrSL s rhss))) := by
  have hmI : rP + 0 + 0 + (mI - rP) = mI := by omega
  refine ⟨trCV cv, ConLeche.generatedRules rP (trTM s M) (TrSL s rhss), ?_, CVRel_trCV hok, ?_⟩
  · simp only [InLean.majorIdxOf, InLean.rulePrefixOf, hmI, recKExpected_tr]
    rfl
  · rw [generatedRules_eq, TrSL_of_okC s hrhs]
    exact sumRules_rel (hfire _ rfl rfl (by simp only [InLean.majorIdxOf]; omega) (by simp [InLean.rulePrefixOf]))
      M.ctors rhss hrhs

/-! ## The family pushed -/

/-- What one generated recursor at position `k` needs for its entry:
closed readings of its type and rules, the rule prefix below the major
index, and the firing mode at use against master's. -/
@[expose] def GenEntryOk (p : InLean.BlockShape) (s : InLean.CState) (k : Nat)
    (o : Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr) : Prop :=
  okC o.1.type = true ∧ (∀ r ∈ o.2.2, okC r = true) ∧ p.rulePrefixAt k ≤ p.majorIdxAt k ∧
    ∀ rv : RecursorVal, rv.type = o.1.type → rv.all = p.memberNames →
      majorIdxOf rv = p.majorIdxAt k → rulePrefixOf rv = p.rulePrefixAt k →
      FireRel (recFireAt rv false) (ConLeche.generatedFire (trTM s o.2.1) (p.rulePrefixAt k))

/-- **The generated family pushed** (`FEnv.pushAll` of `blockRecInfosTF`)
against master's `consBlockRecsT`, entry by entry (`jobEnvI_push_plain`,
`entryRelI_genEntry`). -/
theorem presI_blockRecInfosTF (hlaws : EnvLaws) (p : InLean.BlockShape) (s : InLean.CState) :
    ∀ (out : List (Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr)) (m : Nat)
      {fe : InLean.FEnv} {L : ConLeche.Env},
      EnvPresI fe L → ProjBodiesInRange fe →
      (∀ o ∈ out, fe.env.find? o.1.name = none) → (out.map (·.1.name)).Nodup →
      (∀ o ∈ out, o.1.name = InLean.sorryAxName → fe.coreAxioms = true) →
      (∀ i o, out[i]? = some o → GenEntryOk p s (m + i) o) →
      EnvPresI (fe.pushAll (InLean.blockRecInfosTF p m out))
          (ConLeche.consBlockRecsT (trShape p) m (out.map (trOut s)) L) ∧
        ProjBodiesInRange (fe.pushAll (InLean.blockRecInfosTF p m out))
  | [], _, fe, L, hP, hR, _, _, _, _ => ⟨hP, hR⟩
  | o :: out, m, fe, L, hP, hR, hfr, hnd, hso, hok => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨cv, M, rhss⟩ := o
    obtain ⟨h1, h2, h3, h4⟩ := hok 0 (cv, M, rhss) rfl
    simp only [Nat.add_zero] at h1 h2 h3 h4
    simp only [InLean.blockRecInfosTF, List.map_cons, trOut, ConLeche.consBlockRecsT,
      InLean.FEnv.pushAll]
    generalize hci : InLean.recEntry p cv (p.majorIdxAt m) (p.rulePrefixAt m) (InLean.recKExpected p M)
      (InLean.generatedRules M rhss) = ci
    have hcn : ci.name = cv.name := by rw [← hci]; rfl
    have hfr0 : fe.env.find? ci.name = none := by rw [hcn]; exact hfr _ List.mem_cons_self
    have hsees : fe.sees ci.name ci = true :=
      sees_safe (by rw [← hci]; rfl) (fun h => hso _ List.mem_cons_self (hcn ▸ h))
    have hrel := entryRelI_genEntry (fe.push ci) p s (M := M) h1 h2 h3 h4
    rw [hci] at hrel
    obtain ⟨hP1, hR1⟩ := jobEnvI_push_plain hlaws hP hR hfr0 hsees (by rw [hcn]; rfl) hrel
      (by intro v h; rw [← hci] at h; cases h)
    rw [trShape_majorIdxAt, trShape_rulePrefixAt]
    rw [pushDelta_one]
    exact presI_blockRecInfosTF hlaws p s out (m + 1) hP1 hR1
      (fun d hd => by
        rw [push_env_find hlaws hfr0 (by rw [hcn]; exact fun h => hnd.1 ⟨d, hd, h⟩)]
        exact hfr d (List.mem_cons_of_mem _ hd))
      hnd.2 (fun d hd => hso d (List.mem_cons_of_mem _ hd))
      (fun i x hx => by
        have := hok (i + 1) x (by simpa using hx)
        rwa [show m + (i + 1) = m + 1 + i by omega] at this)

/-- **Every generated recursor's entry, from master's run of the stage**
on the readings (`genRecCheckI_run`'s `Runs`): the head and the prefix
bound (`genRecCheck_majorHead`), an outside class's arguments
(`genRecCheck_outFacts`, `NestedRead`), the firing mode (`fire_genEntry`).
The classes' premises are master's on the read classes: `ClassOutParams`
(as `envWF_genRecs`), `ClassHead` (`TargetMajorRun.classHead`), and the
recursors' class indices in range. -/
theorem genEntryOk_of_run {L : ConLeche.Env} {p : InLean.BlockShape} {s : InLean.CState}
    {nestedBit : Bool} {params : List ConLeche.Expr} {tbl : List ConLeche.NestCtorNf}
    {rd : ConLeche.ClassRead} {Ms : List ConLeche.TargetMajor} {block : List ConLeche.ConstantInfo}
    {out : List (Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr)}
    (hR : Runs (ConLeche.genRecCheck (ConLeche.fueledOpsM .verified)
      (ConLeche.mkFEnv L) (trShape p) nestedBit params tbl rd Ms block) (out.map (trOut s)))
    (hpl : params.length = (trShape p).nP) (hMsO : ∀ M ∈ Ms, ConLeche.ClassOutParams (trShape p).nP M)
    (hMsH : ∀ M ∈ Ms, ClassHead (trShape p) M) (hrc : ∀ c ∈ rd.recCls, c < Ms.length)
    (hok : ∀ o ∈ out, okC o.1.type = true ∧ ∀ r ∈ o.2.2, okC r = true) :
    ∀ i o, out[i]? = some o → GenEntryOk p s i o := by
  obtain ⟨F, hF⟩ := hR
  rw [ConLeche.genRecCheck_datF] at hF
  intro i o hi
  have hti : (out.map (trOut s))[i]? = some (trOut s o) := by simp [hi]
  obtain ⟨hhead, hle, pre, dom, body, hs, hfn⟩ := genRecCheck_majorHead hF hpl hMsH hrc hti
  have hnr := (ConLeche.Cached.genRecCheck_outFacts hF hpl hMsO).2 i _ hti
  obtain ⟨h1, h2⟩ := hok o (List.mem_of_getElem? hi)
  simp only [trShape_majorIdxAt, trShape_rulePrefixAt] at hle hs hnr
  refine ⟨h1, h2, hle, fun rv hty hall hmI hrP => ?_⟩
  have hty' : (trOut s o).1.type = trC rv.type := by simp [trOut, trCV, hty]
  rw [hty'] at hs hnr
  refine fire_genEntry (M := o.2.1) (by rw [hty]; exact h1) hall hmI hrP hhead hs hfn fun hm => ?_
  obtain ⟨-, -, -, pre', dom', body', D, hs', -, hargs, -⟩ := hnr hm
  rw [hs] at hs'
  simp only [Option.some.injEq, Prod.mk.injEq, ConLeche.Expr.forallE.injEq] at hs'
  obtain ⟨-, rfl, -⟩ := hs'
  exact hargs

/-- **`JobEnvI` at the generated recursors' environment**
(`fe₂.pushAll (blockRecInfosTF p 0 out)`, where the stored recursors are
checked) against master's `consBlockRecsT`: well-formedness is master's
(`envWF_genRecs`), the entries are `presI_blockRecInfosTF`'s. -/
theorem jobEnvI_genRecs {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {p : InLean.BlockShape} {s : InLean.CState}
    {out : List (Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr)}
    (hwf : ConLeche.EnvWF (ConLeche.consBlockRecsT (trShape p) 0 (out.map (trOut s)) L))
    (hfr : ∀ o ∈ out, fe.env.find? o.1.name = none) (hnd : (out.map (·.1.name)).Nodup)
    (hso : ∀ o ∈ out, o.1.name = InLean.sorryAxName → fe.coreAxioms = true)
    (hok : ∀ i o, out[i]? = some o → GenEntryOk p s i o) :
    JobEnvI (fe.pushAll (InLean.blockRecInfosTF p 0 out))
      (ConLeche.consBlockRecsT (trShape p) 0 (out.map (trOut s)) L) := by
  obtain ⟨hP, hR⟩ := presI_blockRecInfosTF hJ.laws p s out 0 hJ.pres hJ.proj hfr hnd hso
    (fun i o h => by rw [Nat.zero_add]; exact hok i o h)
  exact ⟨hJ.laws, hP, hwf, hR⟩

/-- **The generated recursors are at the stream's recursors' names**
(master's `genRecCheck_outCv` on the readings), so they are distinct
where those are (`genRecCheckI_run`'s `Nodup`). -/
theorem genRecs_names {fe : ConLeche.FEnv} {p : InLean.BlockShape} {s : InLean.CState}
    {nestedBit : Bool} {params : List ConLeche.Expr} {tbl : List ConLeche.NestCtorNf}
    {rd : ConLeche.ClassRead} {Ms : List ConLeche.TargetMajor} {block : List ConLeche.ConstantInfo}
    {out : List (Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr)}
    (hR : Runs (ConLeche.genRecCheck (ConLeche.fueledOpsM .verified)
      fe (trShape p) nestedBit params tbl rd Ms block) (out.map (trOut s))) :
    out.map (·.1.name) = p.recs.map (·.cvR.name) := by
  obtain ⟨F, hF⟩ := hR
  rw [ConLeche.genRecCheck_datF] at hF
  obtain ⟨hlen, hall⟩ := ConLeche.Cached.genRecCheck_outCv hF
  simp only [List.length_map, trShape] at hlen
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map]
  cases ho : out[i]? with
  | none =>
    have : p.recs[i]? = none := by
      rw [List.getElem?_eq_none_iff] at ho ⊢; omega
    simp [this]
  | some o =>
    have hil : i < p.recs.length := by
      have := (List.getElem?_eq_some_iff.mp ho).1; omega
    rw [List.getElem?_eq_getElem hil]
    have h := hall i (trRec p.recs[i]) (trOut s o)
      (by simp [trShape, List.getElem?_eq_getElem hil]) (by simp [ho])
    have hn := congrArg ConLeche.ConstantVal.name h
    simp only [trOut, trCV, trRec] at hn
    simp [toName_inj hn]

/-- **`JobEnvI` at the generated recursors' environment, from the stage's
run**: `genRecCheckI_run`'s outputs (closed readings, fresh names, the
`sorryAx` clause, the recursor names distinct) and master's run on the
readings, with master's premises on the read classes (`ClassOutParams`,
`ClassHead`, class indices in range). -/
theorem jobEnvI_genRecs_of_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {p : InLean.BlockShape} {s : InLean.CState}
    {nestedBit : Bool} {params : List ConLeche.Expr} {tbl : List ConLeche.NestCtorNf}
    {rd : ConLeche.ClassRead} {Ms : List ConLeche.TargetMajor} {block : List ConLeche.ConstantInfo}
    {out : List (Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr)}
    (hR : Runs (ConLeche.genRecCheck (ConLeche.fueledOpsM .verified)
      (ConLeche.mkFEnv L) (trShape p) nestedBit params tbl rd Ms block) (out.map (trOut s)))
    (hpl : params.length = (trShape p).nP) (hMsO : ∀ M ∈ Ms, ConLeche.ClassOutParams (trShape p).nP M)
    (hMsH : ∀ M ∈ Ms, ClassHead (trShape p) M) (hrc : ∀ c ∈ rd.recCls, c < Ms.length)
    (hout : ∀ o ∈ out, okC o.1.type = true ∧ (∀ r ∈ o.2.2, okC r = true) ∧
      fe.env.find? o.1.name = none ∧ (o.1.name = InLean.sorryAxName → fe.coreAxioms = true))
    (hnd : (p.recs.map (·.cvR.name)).Nodup) :
    JobEnvI (fe.pushAll (InLean.blockRecInfosTF p 0 out))
      (ConLeche.consBlockRecsT (trShape p) 0 (out.map (trOut s)) L) :=
  jobEnvI_genRecs hJ (envWF_genRecs hJ.wf hR hpl hMsO) (fun o ho => (hout o ho).2.2.1)
    (by rw [genRecs_names hR]; exact hnd) (fun o ho => (hout o ho).2.2.2)
    (genEntryOk_of_run hR hpl hMsO hMsH hrc fun o ho => ⟨(hout o ho).1, (hout o ho).2.1⟩)

/-! ## The projection tables -/

/-- **A projection body built at use is in range** where `projBodyOk`
says so. -/
theorem projBodyAt_range {T : Name} {nP i : Nat} {cty b : Lean.Expr}
    (hok : projBodyOk T nP i cty = true) (h : projBodyAt T nP i cty = some b) :
    Expr.RangeOk b := by
  unfold projBodyOk at hok
  rw [h] at hok
  simp only [Bool.and_eq_true, Option.all_some] at hok
  exact (RangeOk_of_inRange hok.2).1

/-- An `Option` `mapM` that succeeds: one result per element, each the
function's. -/
theorem mapM_option_spec {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {bl : List β}, l.mapM f = some bl →
      bl.length = l.length ∧ ∀ i (h : i < l.length), f l[i] = bl[i]?
  | [], bl, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun i h => absurd h (by simp)⟩
  | a :: l, bl, h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    obtain ⟨hl, he⟩ := mapM_option_spec hys
    refine ⟨by simp [hl], fun i hi => ?_⟩
    cases i with
    | zero => simpa using hy
    | succ i => simpa using he i (by simpa using hi)

theorem structProjBodiesGo_length (S : ConLeche.Name) :
    ∀ (vs : List ConLeche.Expr) (k i : Nat) (r : ConLeche.Expr) (l : List ConLeche.Expr),
      ConLeche.structProjBodiesGo S vs k i r = some l → l.length = k
  | _, 0, _, _, l, h => by simp only [ConLeche.structProjBodiesGo, Option.some.injEq] at h; subst h; rfl
  | vs, k + 1, i, .forallE d body, l, h => by
    simp only [ConLeche.structProjBodiesGo, Option.map_eq_some_iff] at h
    obtain ⟨l', h', rfl⟩ := h
    simp [structProjBodiesGo_length S _ k _ _ l' h']
  | _, _ + 1, _, .bvar _, _, h | _, _ + 1, _, .fvar _ _, _, h | _, _ + 1, _, .sort _, _, h
  | _, _ + 1, _, .const _ _, _, h | _, _ + 1, _, .app _ _, _, h | _, _ + 1, _, .lam _ _, _, h
  | _, _ + 1, _, .letE _ _ _, _, h | _, _ + 1, _, .lit _, _, h | _, _ + 1, _, .proj _ _ _, _, h => by
    simp [ConLeche.structProjBodiesGo] at h

theorem structProjBodies_size {S : ConLeche.Name} {nP nF : Nat} {cty : ConLeche.Expr}
    {bodies : Array ConLeche.Expr} (h : ConLeche.structProjBodies S nP nF cty = some bodies) :
    bodies.size = nF := by
  unfold ConLeche.structProjBodies at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    simpa using structProjBodiesGo_length S _ _ _ _ l hl
  · cases h

theorem andM_true {x y : InLean.CheckCM Bool} {s s' : InLean.CState}
    (h : (x <&&> y) s = .ok (true, s')) : ∃ s₁, x s = .ok (true, s₁) ∧ y s₁ = .ok (true, s') := by
  unfold andM at h
  obtain ⟨b, s₁, h1, h2⟩ := bindI_ok h
  cases b
  · obtain ⟨h, -⟩ := pureI_ok h2; cases h
  · exact ⟨s₁, h1, h2⟩

theorem allLevelParamsDefined_noSt (lps : List Name) (e : Lean.Expr) :
    NoSt (InLean.allLevelParamsDefined lps e) := by
  unfold InLean.allLevelParamsDefined InLean.withAnnotations InLean.fvarClosureM
  repeat' (first
    | exact NoSt.pure _
    | exact NoSt.get
    | (apply NoSt.bind <;> intros)
    | apply NoSt.ite
    | split)

theorem NoSt.andM {x y : InLean.CheckCM Bool} (hx : NoSt x) (hy : NoSt y) : NoSt (x <&&> y) := by
  unfold _root_.andM
  refine NoSt.bind hx fun b => ?_
  cases b
  · exact NoSt.pure _
  · exact hy

theorem option_mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {bs : List β}, l.mapM f = some bs → ∀ x ∈ l, ∃ y ∈ bs, f x = some y
  | [], _, _, x, hx => by cases hx
  | a :: l, bs, h, x, hx => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨y, List.mem_cons_self, hy⟩
    · obtain ⟨z, hz, hfz⟩ := option_mapM_mem hys x hx
      exact ⟨z, List.mem_cons_of_mem _ hz, hfz⟩

/-- **A projection table InLean built, read as master's** (`blockTables`'
entries): the names and counts translated, every body with a closed reading
in range, the bodies read as master's. -/
@[expose] def ProjTableRelI (t : InLean.ProjTable) (ct : ConLeche.ProjTable) : Prop :=
  ct.structName = toName t.structName ∧ ct.levelParams = t.levelParams.map toName ∧
    ct.numParams = t.numParams ∧ ct.numFields = t.numFields ∧
    ct.bodies.toList = t.bodies.toList.map trC ∧
    ∀ b ∈ t.bodies.toList, okC b = true ∧ Expr.RangeOk b

/-- Two lists of tables related entry by entry (`ProjTableRelI`). -/
inductive ProjTablesRelI : List InLean.ProjTable → List ConLeche.ProjTable → Prop where
  | nil : ProjTablesRelI [] []
  | cons {t ct Q cQ} : ProjTableRelI t ct → ProjTablesRelI Q cQ → ProjTablesRelI (t :: Q) (ct :: cQ)

/-- What a structure-like member needs for its table to be read as master's:
a closed reading of its constructor's type and the projection bodies in range
(`projBodyOk`, which InLean's inductive check runs). -/
@[expose] def TableMemberOk (nP : Nat) (ms : InLean.MemberShape) : Prop :=
  ∀ c, ms.structCtor? = some c → okC c.1.type = true ∧
    ∀ i < c.2, projBodyOk ms.declared.name nP i c.1.type = true

/-- One structure's bodies (`structProjBodies`, the twin of master's cached
`structProjBodiesC`): InLean's one walk, entry by entry the body `projBodyAt` builds
(`structProjBodies_eq_fields`), read as master's (`projBodyAt_tr`). -/
theorem structProjBodies_tr {T : Name} {nP nF : Nat} {cty : Lean.Expr} (hok : okC cty = true)
    (hsteps : ∀ i < nF, projBodyOk T nP i cty = true) {bs : Array Lean.Expr}
    (h : InLean.structProjBodies T nP nF cty = some bs) :
    ∃ cbs, ConLeche.Cached.structProjBodiesC (toName T) nP nF (trC cty) = some cbs ∧
      cbs.toList = bs.toList.map trC ∧ ∀ b ∈ bs.toList, okC b = true ∧ Expr.RangeOk b := by
  rw [ConLeche.Cached.structProjBodiesC_eq]
  have hc : toExprC cty = some (trC cty) := toExpr_of_okE _ hok
  have hbs' := h
  rw [structProjBodies_eq_fields] at hbs'
  cases hpis : hasPis (nP + nF) cty
  · rw [hpis] at hbs'; cases hbs'
  simp only [hpis, ↓reduceIte] at hbs'
  have hcis := (hasPis_iff_structProjBodies (S := toName T) hc).symm.trans hpis
  obtain ⟨cbs, hcbs⟩ := Option.isSome_iff_exists.1 hcis
  have hcsz := structProjBodies_size hcbs
  rw [List.mapM_toArray] at hbs'
  obtain ⟨bl, hbl, rfl⟩ : ∃ bl, (List.range nF).mapM (fun i => projBodyAt T nP i cty) = some bl ∧
      bs = bl.toArray := by
    cases hm : (List.range nF).mapM (fun i => projBodyAt T nP i cty) with
    | none => rw [hm] at hbs'; cases hbs'
    | some bl => rw [hm] at hbs'; exact ⟨bl, rfl, (Option.some.inj hbs').symm⟩
  obtain ⟨hlen0, hent0⟩ := mapM_option_spec hbl
  have hlen : bl.length = nF := by simpa using hlen0
  have hent : ∀ i (hi : i < nF), ∃ b, bl[i]? = some b ∧ projBodyAt T nP i cty = some b := by
    intro i hi
    have hi' : i < (List.range nF).length := by simpa using hi
    refine ⟨bl[i]'(by rw [hlen0]; exact hi'), List.getElem?_eq_getElem _, ?_⟩
    have := hent0 i hi'
    simp only [List.getElem_range] at this
    rw [this]
    exact List.getElem?_eq_getElem _
  refine ⟨cbs, hcbs, ?_, ?_⟩
  · apply List.ext_getElem
    · simp [hcsz, hlen]
    · intro i h1 h2
      have hi : i < nF := by simpa [hcsz] using h1
      obtain ⟨b, hb1, hb2⟩ := hent i hi
      obtain ⟨b', hb'1, -, hb'2⟩ := projBodyAt_tr (hsteps i hi) (RangeOk_of_okE hok) hc hcbs hi
      rw [hb2, Option.some.injEq] at hb'1
      subst hb'1
      have hr := projBodyAt_range (hsteps i hi) hb2
      obtain ⟨-, htr⟩ := trC_of_toExprC hb'2 hr
      have hbi : bl[i]'(hlen ▸ hi) = b := by
        rw [List.getElem?_eq_getElem (hlen ▸ hi)] at hb1; exact Option.some.inj hb1
      simp only [Array.getElem_toList, List.getElem_map, hbi]
      rw [htr]
      have h1' : i < cbs.size := by simpa using h1
      simp [Array.getD_eq_getD_getElem?, h1']
  · intro b hb
    simp only at hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hi' : i < nF := hlen ▸ hi
    obtain ⟨b, hb1, hb2⟩ := hent i hi'
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hb1
    subst hb1
    obtain ⟨b', hb'1, -, hb'2⟩ := projBodyAt_tr (hsteps i hi') (RangeOk_of_okE hok) hc hcbs hi'
    rw [hb2, Option.some.injEq] at hb'1
    subst hb'1
    have hr := projBodyAt_range (hsteps i hi') hb2
    exact ⟨(trC_of_toExprC hb'2 hr).1, hr⟩

/-- **The block's tables, InLean's read as master's cached `blockTablesC`**. -/
theorem blockTables_tr (p : InLean.BlockShape) :
    ∀ (l : List InLean.MemberShape) {Q : List InLean.ProjTable},
      (∀ ms ∈ l, TableMemberOk p.nP ms) → InLean.blockTables p l = some Q →
      ∃ cQ, ConLeche.Cached.blockTablesC (trShape p) (l.map trMember) = some cQ ∧
        ProjTablesRelI Q cQ
  | [], Q, _, h => by
    simp only [InLean.blockTables, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, ProjTablesRelI.nil⟩
  | ms :: rest, Q, hms, h => by
    simp only [InLean.blockTables] at h
    simp only [List.map_cons, ConLeche.Cached.blockTablesC, structCtor_tr]
    cases hsc : ms.structCtor? with
    | none =>
      simp only [hsc] at h
      exact blockTables_tr p rest (fun m hm => hms m (List.mem_cons_of_mem _ hm)) h
    | some c =>
      obtain ⟨hok, hst⟩ := hms ms List.mem_cons_self c hsc
      cases hb : InLean.structProjBodies ms.declared.name p.nP c.2 c.1.type with
      | none => simp only [hsc, hb, Option.bind_none] at h; cases h
      | some bodies =>
        simp only [hsc, hb, Option.bind_some, Option.map_eq_some_iff] at h
        obtain ⟨Q', hQ', rfl⟩ := h
        obtain ⟨cQ', hcQ', hrel⟩ := blockTables_tr p rest (fun m hm => hms m (List.mem_cons_of_mem _ hm)) hQ'
        obtain ⟨cbs, hcbs, hcl, hrb⟩ := structProjBodies_tr hok hst hb
        refine ⟨⟨toName ms.declared.name, p.lps.map toName, p.nP, toName c.1.name, c.2, cbs⟩ :: cQ',
          ?_, ProjTablesRelI.cons ⟨rfl, rfl, rfl, rfl, hcl, hrb⟩ hrel⟩
        simp only [Option.map_some, trCtor, trCV, trMember]
        rw [show (trShape p).nP = p.nP from rfl, hcbs]
        simp only [Option.bind_some, hcQ', Option.map_some, trShape_lps]

/-- A table InLean built is at a member's declared name. -/
theorem blockTables_mem (p : InLean.BlockShape) :
    ∀ (l : List InLean.MemberShape) {Q : List InLean.ProjTable}, InLean.blockTables p l = some Q →
      ∀ t ∈ Q, ∃ ms ∈ l, t.structName = ms.declared.name
  | [], Q, h, t, ht => by
    simp only [InLean.blockTables, Option.some.injEq] at h; subst h; cases ht
  | ms :: rest, Q, h, t, ht => by
    simp only [InLean.blockTables] at h
    split at h
    · cases hb : InLean.structProjBodies ms.declared.name p.nP _ _ with
      | none => rw [hb] at h; cases h
      | some bodies =>
        rw [hb] at h
        simp only [Option.bind_some, Option.map_eq_some_iff] at h
        obtain ⟨Q', hQ', rfl⟩ := h
        rcases List.mem_cons.1 ht with rfl | ht
        · exact ⟨ms, List.mem_cons_self, rfl⟩
        · obtain ⟨m, hm, he⟩ := blockTables_mem p rest hQ' t ht
          exact ⟨m, List.mem_cons_of_mem _ hm, he⟩
    · obtain ⟨m, hm, he⟩ := blockTables_mem p rest h t ht
      exact ⟨m, List.mem_cons_of_mem _ hm, he⟩

/-- InLean's table check of one structure (`checkStructProjTableC`):
accepted, master's `checkStructProjTable` passes on the related table at a
related environment.  The bodies read as master's (`ProjTableRelI`), so the
scoping guard carries over (`constsResolveF_tr`,
`allLevelParamsDefined_of_guard`, the range as the bound).  Master's "table
taken" guard, which InLean does not test: a table at `T` in `L` would be one
InLean reads off a former at `T` not pending (`ProjTableRelI`'s environment
clause), and every former at `T` is pending. -/
theorem checkStructProjTableCI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    {t : InLean.ProjTable} {ct : ConLeche.ProjTable} (hrel : ProjTableRelI t ct)
    (hpend : ∀ v, fe.find? t.structName = some (.inductInfo v) → fe.isPending v.name = true)
    {s₀ s' : InLean.CState}
    (h : InLean.checkStructProjTableC t fe s₀ = .ok ((), s')) :
    s' = s₀ ∧ Runs (ConLeche.checkStructProjTable (m := ConLeche.FueledM) ct L) () := by
  obtain ⟨hn, hl, hnp, hnf, hb, hbok⟩ := hrel
  unfold InLean.checkStructProjTableC at h
  obtain ⟨r, s₂, h2, h3⟩ := bindI_ok h
  have hf : ∀ b : Lean.Expr, NoSt ((fun b => pure !b.hasFVar <&&>
      InLean.allLevelParamsDefined t.levelParams b <&&>
        InLean.constsResolveF fe b <&&> pure (decide (b.looseBVarRange ≤ t.numParams + 1))) b) :=
    fun b => NoSt.andM (NoSt.pure _) (NoSt.andM (allLevelParamsDefined_noSt _ _)
      (NoSt.andM (constsResolveF_noSt _ _) (NoSt.pure _)))
  rw [← Array.allM_toList] at h2
  cases r
  · simp only [Bool.false_eq_true, and_false, ↓reduceIte] at h3
    obtain ⟨_, _, h4, -⟩ := bindI_ok h3
    exact (throwI_ok h4).elim
  obtain ⟨rfl, hall⟩ := allM_true hf _ h2
  by_cases hsz : t.bodies.size = t.numFields
  case neg =>
    simp only [hsz, false_and, ↓reduceIte] at h3
    obtain ⟨_, _, h4, -⟩ := bindI_ok h3
    exact (throwI_ok h4).elim
  by_cases hfind : (fe.find? t.structName).isSome = true
  case neg =>
    simp only [hsz, hfind, and_self, ↓reduceIte, Bool.false_eq_true] at h3
    exact (throwI_ok h3).elim
  simp only [hsz, hfind, and_self, ↓reduceIte] at h3
  obtain ⟨-, rfl⟩ := pureI_ok h3
  refine ⟨rfl, ?_⟩
  have hsize : ct.bodies.size = ct.numFields := by
    rw [hnf, ← hsz, ← Array.length_toList, ← Array.length_toList, hb, List.length_map]
  have hbody : ∀ cb ∈ ct.bodies.toList, (!cb.hasFvar && cb.allLevelParamsDefined ct.levelParams &&
      cb.constsResolve L && cb.looseBVarsBounded (ct.numParams + 1)) = true := by
    intro cb hcb
    rw [hb] at hcb
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hcb
    obtain ⟨hokb, hr⟩ := hbok b hbm
    have hbt := hall b hbm
    obtain ⟨_, ha1, hbt⟩ := andM_true hbt
    obtain ⟨hx1, rfl⟩ := pureI_ok ha1
    obtain ⟨_, ha2, hbt⟩ := andM_true hbt
    have hnfv : b.hasFVar = false := by simpa using hx1
    obtain ⟨rfl, hlp⟩ := allLevelParamsDefined_noFVar hnfv ha2
    obtain ⟨_, ha3, ha4⟩ := andM_true hbt
    obtain ⟨ha4, -⟩ := pureI_ok ha4
    have hres := constsResolveF_tr hP hokb ha3
    have hlpC := allLevelParamsDefined_of_guard (lps := t.levelParams) hr fun hh => by
      simpa [hh] using hlp.symm
    have hbnd : (trC b).looseBVarsBounded (t.numParams + 1) = true := by
      have hcb : toExprC b = some (trC b) := toExpr_of_okE _ hokb
      rw [ConLeche.Expr.looseBVarsBounded_iff, bvarBound_toExpr fvarsOnly_none b (trC b) hcb,
        ← Expr.looseBVarRange_eq hr]
      simpa using ha4.symm
    rw [hl, hnp]
    simp only [trC_hasFvar, Bool.not_false, hlpC, hres, Bool.and_self, hbnd]
  have hfindL : (L.find? ct.structName).isSome = true := by rw [hn]; exact find_isSome_tr hP hfind
  have htab : (L.findTable? ct.structName).isNone = true := by
    rw [hn]
    have ht := hP.table t.structName
    cases hL : L.findTable? (toName t.structName) with
    | none => rfl
    | some tbl =>
      rw [hL] at ht
      obtain ⟨v, c, cv', hv, hpv, -⟩ := ht
      have := hpend v hv
      rw [hpv] at this; cases this
  have hallC : (ct.bodies.all fun b => !b.hasFvar && b.allLevelParamsDefined ct.levelParams &&
      b.constsResolve L && b.looseBVarsBounded (ct.numParams + 1)) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro cb hcb
    exact hbody cb (Array.mem_toList_iff.2 hcb)
  unfold ConLeche.checkStructProjTable
  simp only [hallC]
  simp only [hsize, and_self, ↓reduceIte, hfindL, htab]
  exact Runs.bind (Runs.pure _) (Runs.bind (Runs.pure _) (Runs.pure _))

/-- **The block's projection tables** (`checkBlockTablesC`): InLean's check
passing on its tables means master's `checkBlockTables` passes on the related
ones, table by table (`checkStructProjTableCI_run`); the state is unchanged. -/
theorem checkBlockTablesCI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) :
    ∀ {Q : List InLean.ProjTable} {cQ : List ConLeche.ProjTable} {s₀ s' : InLean.CState},
      ProjTablesRelI Q cQ →
      (∀ t ∈ Q, ∀ v, fe.find? t.structName = some (.inductInfo v) → fe.isPending v.name = true) →
      InLean.checkBlockTablesC fe Q s₀ = .ok ((), s') →
      s' = s₀ ∧ Runs (ConLeche.checkBlockTables (m := ConLeche.FueledM) L cQ) ()
  | [], [], s₀, s', ProjTablesRelI.nil, _, h => by
    unfold InLean.checkBlockTablesC at h
    obtain ⟨-, rfl⟩ := pureI_ok h
    exact ⟨rfl, by unfold ConLeche.checkBlockTables; exact Runs.pure _⟩
  | t :: Q, ct :: cQ, s₀, s', ProjTablesRelI.cons hr hrs, hpend, h => by
    unfold InLean.checkBlockTablesC at h
    obtain ⟨u, s₁, h1, h2⟩ := bindI_ok h
    obtain ⟨rfl, hR1⟩ := checkStructProjTableCI_run hP hr (hpend t List.mem_cons_self) h1
    obtain ⟨rfl, hR⟩ := checkBlockTablesCI_run hP hrs
      (fun t' ht' => hpend t' (List.mem_cons_of_mem _ ht')) h2
    refine ⟨rfl, ?_⟩
    unfold ConLeche.checkBlockTables
    exact Runs.bind hR1 hR

end InLeanProof
