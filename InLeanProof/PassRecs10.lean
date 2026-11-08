module

public import InLeanProof.PassRecs9
public import InLeanProof.PassSim
public import InLeanProof.RecFireTr
public import ConLeche.Verify.Inductives.TargetAuxFire
import ConLeche.Verify.Cached.BlockPushes
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
* `checkBlockTablesFI_run`: the projection tables' check against master's
  `checkBlockTables` (the bodies read as master's, `projBodyAt_tr`; master's
  "table taken" guard from the members' mark).
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
    (h : ConLeche.genRecCheck (ConLeche.ShadowOps.fueled mode F) (ConLeche.mkFEnv env) p nestedBit
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
    (hR : Runs (ConLeche.genRecCheck (ConLeche.ShadowOps.ofOps (ConLeche.fueledOpsM .verified))
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
    (hR : Runs (ConLeche.genRecCheck (ConLeche.ShadowOps.ofOps (ConLeche.fueledOpsM .verified))
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
    (hR : Runs (ConLeche.genRecCheck (ConLeche.ShadowOps.ofOps (ConLeche.fueledOpsM .verified))
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

theorem structProjBodiesGo_length (S : ConLeche.Name) :
    ∀ (k i : Nat) (r : ConLeche.Expr) (l : List ConLeche.Expr),
      ConLeche.structProjBodiesGo S k i r = some l → l.length = k
  | 0, _, _, l, h => by simp only [ConLeche.structProjBodiesGo, Option.some.injEq] at h; subst h; rfl
  | k + 1, i, .forallE d body, l, h => by
    simp only [ConLeche.structProjBodiesGo, Option.map_eq_some_iff] at h
    obtain ⟨l', h', rfl⟩ := h
    simp [structProjBodiesGo_length S k _ _ l' h']
  | _ + 1, _, .bvar _, _, h | _ + 1, _, .fvar _ _, _, h | _ + 1, _, .sort _, _, h
  | _ + 1, _, .const _ _, _, h | _ + 1, _, .app _ _, _, h | _ + 1, _, .lam _ _, _, h
  | _ + 1, _, .letE _ _ _, _, h | _ + 1, _, .lit _, _, h | _ + 1, _, .proj _ _ _, _, h => by
    simp [ConLeche.structProjBodiesGo] at h

theorem structProjBodies_size {S : ConLeche.Name} {nP nF : Nat} {cty : ConLeche.Expr}
    {bodies : Array ConLeche.Expr} (h : ConLeche.structProjBodies S nP nF cty = some bodies) :
    bodies.size = nF := by
  unfold ConLeche.structProjBodies at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    simpa using structProjBodiesGo_length S _ _ _ l hl
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

/-- InLean's table check of one structure (`checkStructProjTableF` at
`structWalkersC`): accepted, master's `checkStructProjTable` passes on the
translated constructor at a related environment.  The bodies: InLean's
built at use (`projBodyAt`) read as master's (`projBodyAt_tr`, given the
bodies and their parameter variables in range, `projBodyOk`), so the scoping guard carries over
(`constsResolveF_tr`, `allLevelParamsDefined_of_guard`, the range as the
bound).  Master's "table taken" guard, which InLean does not test: a table
at `T` in `L` would be one InLean reads off a former at `T` not pending
(`TableRelI`), and every former at `T` is pending. -/
theorem checkStructProjTableI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    {T : Name} {lps : List Name} {nP nF : Nat} {cv : Lean.ConstantVal}
    (hok : okC cv.type = true) (hsteps : ∀ i < nF, projBodyOk T nP i cv.type = true)
    (hpend : ∀ v, fe.find? T = some (.inductInfo v) → fe.isPending v.name = true)
    {s₀ s' : InLean.CState}
    (h : InLean.checkStructProjTableF structWalkersC T lps nP nF cv fe s₀ = .ok ((), s')) :
    s' = s₀ ∧ Runs (ConLeche.checkStructProjTable (m := ConLeche.FueledM) (toName T)
      (lps.map toName) nP nF (trCV cv) L) () := by
  have hc : toExprC cv.type = some (trC cv.type) := toExpr_of_okE _ hok
  unfold InLean.checkStructProjTableF at h
  obtain ⟨bs, s₁, h1, hk⟩ := bindI_ok h
  obtain ⟨hbs, rfl⟩ := unwrapOr_run h1
  have hbs' : InLean.structProjBodies T nP nF cv.type = some bs := hbs
  unfold InLean.structProjBodies at hbs'
  cases hpis : hasPis (nP + nF) cv.type
  · rw [hpis] at hbs'; cases hbs'
  simp only [hpis, ↓reduceIte] at hbs'
  have hcis := (hasPis_iff_structProjBodies (S := toName T) hc).symm.trans hpis
  obtain ⟨cbs, hcbs⟩ := Option.isSome_iff_exists.1 hcis
  have hcsz := structProjBodies_size hcbs
  obtain ⟨r, s₂, h2, h3⟩ := bindI_ok hk
  have hf : ∀ b : Lean.Expr, NoSt ((fun b => pure !b.hasFVar <&&>
      InLean.allLevelParamsDefined lps b <&&>
        structWalkersC.resolve fe b <&&> pure (decide (b.looseBVarRange ≤ nP + 1))) b) :=
    fun b => NoSt.andM (NoSt.pure _) (NoSt.andM (allLevelParamsDefined_noSt _ _)
      (NoSt.andM (constsResolveF_noSt _ _) (NoSt.pure _)))
  rw [← Array.allM_toList] at h2
  cases r
  · simp only [Bool.false_eq_true, and_false, ↓reduceIte] at h3
    obtain ⟨_, _, h4, -⟩ := bindI_ok h3
    exact (throwI_ok h4).elim
  obtain ⟨rfl, hall⟩ := allM_true hf _ h2
  simp only [and_true] at h3
  split at h3
  rotate_left
  · obtain ⟨_, _, h4, -⟩ := bindI_ok h3
    exact (throwI_ok h4).elim
  split at h3
  rotate_left
  · exact (throwI_ok h3).elim
  rename_i hfind
  obtain ⟨-, rfl⟩ := pureI_ok h3
  refine ⟨rfl, ?_⟩
  -- master's guards
  have hbody : ∀ i (hi : i < cbs.size), (!cbs[i].hasFvar &&
      cbs[i].allLevelParamsDefined (lps.map toName) && cbs[i].constsResolve L &&
      cbs[i].looseBVarsBounded (nP + 1)) = true := by
    intro i hi
    have hiF : i < nF := hcsz ▸ hi
    obtain ⟨b, hb1, -, hb2⟩ := projBodyAt_tr (hsteps i hiF) (RangeOk_of_okE hok) hc hcbs hiF
    have hr := projBodyAt_range (hsteps i hiF) hb1
    obtain ⟨hokb, htrb⟩ := trC_of_toExprC hb2 hr
    have hget : cbs.getD i default = cbs[i] := by simp [Array.getD_eq_getD_getElem?, hi]
    rw [hget] at htrb hb2
    rw [List.mapM_toArray] at hbs'
    obtain ⟨bl, hbl, rfl⟩ : ∃ bl, (List.range nF).mapM (fun i => projBodyAt T nP i cv.type) = some bl ∧
        bs = bl.toArray := by
      cases hm : (List.range nF).mapM (fun i => projBodyAt T nP i cv.type) with
      | none => rw [hm] at hbs'; cases hbs'
      | some bl => rw [hm] at hbs'; exact ⟨bl, rfl, (Option.some.inj hbs').symm⟩
    obtain ⟨b', hb'm, hb'⟩ := option_mapM_mem hbl i (List.mem_range.2 hiF)
    rw [hb1, Option.some.injEq] at hb'
    subst hb'
    have hb := hall b (by simpa using hb'm)
    obtain ⟨_, ha1, hb⟩ := andM_true hb
    obtain ⟨hx1, rfl⟩ := pureI_ok ha1
    obtain ⟨_, ha2, hb⟩ := andM_true hb
    have hnf : b.hasFVar = false := by simpa using hx1
    obtain ⟨rfl, hlp⟩ := allLevelParamsDefined_noFVar hnf ha2
    obtain ⟨_, ha3, ha4⟩ := andM_true hb
    have ha3' : InLean.constsResolveF fe b _ = .ok (true, _) := ha3
    obtain ⟨ha4, -⟩ := pureI_ok ha4
    have hres := constsResolveF_tr hP hokb ha3'
    have hlpC := allLevelParamsDefined_of_guard (lps := lps) hr fun hh => by
      simpa [hh] using hlp.symm
    have hbnd : cbs[i].looseBVarsBounded (nP + 1) = true := by
      rw [ConLeche.Expr.looseBVarsBounded_iff, bvarBound_toExpr fvarsOnly_none b _ hb2,
        ← Expr.looseBVarRange_eq hr]
      simpa using ha4.symm
    rw [← htrb] at hbnd ⊢
    simp only [trC_hasFvar, Bool.not_false, hlpC, hres, Bool.and_self, Bool.true_and]
    rw [htrb] at hbnd ⊢
    exact hbnd
  have hfindL : (L.find? (toName T)).isSome = true := find_isSome_tr hP hfind
  have htab : (L.findTable? (toName T)).isNone = true := by
    have ht := hP.table T
    cases hL : L.findTable? (toName T) with
    | none => rfl
    | some tbl =>
      rw [hL] at ht
      obtain ⟨v, c, cv', hv, hpv, -⟩ := ht
      have := hpend v hv
      rw [hpv] at this; cases this
  have hallC : (cbs.all fun b => !b.hasFvar && b.allLevelParamsDefined (lps.map toName) &&
      b.constsResolve L && b.looseBVarsBounded (nP + 1)) = true := Array.all_eq_true.2 hbody
  unfold ConLeche.checkStructProjTable
  simp only [trCV, hcbs, ConLeche.unwrapOr]
  refine Runs.bind (Runs.pure _) ?_
  simp only [hallC]
  simp only [hcsz, and_self, ↓reduceIte, hfindL, htab]
  exact Runs.pure _

/-- What a structure-like member needs for its table's check: a closed
reading of its constructor's type, the projection bodies in range
(`projBodyOk`, which InLean's inductive check runs), and the former at its
name pending (the block's mark). -/
@[expose] def TableMemberOk (fe : InLean.FEnv) (nP : Nat) (ms : InLean.MemberShape) : Prop :=
  ∀ c, ms.structCtor? = some c → okC c.1.type = true ∧
    (∀ i < c.2, projBodyOk ms.cvT.name nP i c.1.type = true) ∧
    ∀ v, fe.find? ms.cvT.name = some (.inductInfo v) → fe.isPending v.name = true

/-- **The block's projection tables** (`checkBlockTablesF` at
`structWalkersC`): InLean's check passing means master's
`checkBlockTables` passes on the translated members, member by member
(`checkStructProjTableI_run`); the state is unchanged. -/
theorem checkBlockTablesFI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (p : InLean.BlockShape) :
    ∀ (l : List InLean.MemberShape) {s₀ s' : InLean.CState}, (∀ ms ∈ l, TableMemberOk fe p.nP ms) →
      InLean.checkBlockTablesF structWalkersC p fe l s₀ = .ok ((), s') →
      s' = s₀ ∧ Runs (ConLeche.checkBlockTables (m := ConLeche.FueledM) (trShape p) L
        (l.map trMember)) ()
  | [], s₀, s', _, h => by
    unfold InLean.checkBlockTablesF at h
    obtain ⟨-, rfl⟩ := pureI_ok h
    exact ⟨rfl, by unfold ConLeche.checkBlockTables; exact Runs.pure _⟩
  | ms :: rest, s₀, s', hms, h => by
    unfold InLean.checkBlockTablesF at h
    obtain ⟨u, s₁, h1, h2⟩ := bindI_ok h
    obtain ⟨hs', hR⟩ := checkBlockTablesFI_run hP p rest
      (fun m hm => hms m (List.mem_cons_of_mem _ hm)) h2
    have hm := hms ms List.mem_cons_self
    simp only [List.map_cons]
    unfold ConLeche.checkBlockTables
    rw [structCtor_tr]
    cases hc : ms.structCtor? with
    | none =>
      rw [hc] at h1
      obtain ⟨-, rfl⟩ := pureI_ok h1
      exact ⟨hs', Runs.bind (Runs.pure _) hR⟩
    | some c =>
      rw [hc] at h1
      obtain ⟨g1, g2, g3⟩ := hm c hc
      obtain ⟨rfl, hR1⟩ := checkStructProjTableI_run hP g1 g2 g3 h1
      refine ⟨hs', Runs.bind (a := ()) ?_ hR⟩
      simpa only [Option.map_some, trMember_cvT, trCV, trShape_lps, trShape_nP, trCtor] using hR1

end InLeanProof
