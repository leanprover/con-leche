module

import ConLeche.Kernel.CheckDecl
import ConLeche.Kernel.Install
import ConLeche.Cached.Decls
public import ConLeche.Verify.Cached.Scoped
public import ConLeche.Verify.Inductives.IotaRead
import ConLeche.Semantics.Bridge.Sound
import ConLeche.Semantics.DeclWF
import ConLeche.Verify.Cached.BridgeC
import ConLeche.Verify.Cached.BlockPushes
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Inductives.BlockShapeInv
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Semantics.Inductives.DeclBlock

public section

/-!
# The pure fold's run, and the cached fold's run as one

`PureRun` (`ConLeche/Kernel/CheckDecl.lean`) is the specification's acceptance of a list of records
from an environment: each record's `checkDecl` at the fueled operations, at its own fuel.  The
modular checks (`Modular.ImportOk.accepted`) and the worker's theorem (`Driver.WorkerAccepted`)
rest on it; the binary runs the cached fold (`DeclsRun`, `ConLeche/Cached/Decls.lean`).

* **The bridge** (`DeclsRun.pureRun`): an accepting cached run from a canonical index whose
  environment is well formed is a `PureRun` between the two environments, ending at a canonical
  index (`checkDeclStepC_run` at each record, `checkDecl_envWF` carrying the well-formedness).
* **What a pure step pushes** (`checkDecl_pushes`, `checkDecl_fresh`): the environment with the
  record's constants and tables pushed (`streamEnv`'s step, a function of the record alone), at
  pairwise distinct names none of which the environment held.  Read off the run relation
  (`checkDeclRun_ofEnvFactsK`), whose records carry every arm's result environment and every
  duplicate guard the checker ran: a value or axiom record conses one constant fresh by its
  `ConstantValRun`; `sorryAx` stores nothing; a quotient record its pin, fresh by its
  `DeclQuotRun`; a block `readBlock` reads installs `blockConstants p₀` (the formers fresh at the
  base, the constructors at the formers' environment, the recursors at the constructors', each
  stage's names distinct: `blockRun_fresh`).
* **What a pure run keeps** (`PureRun.env`, `.chain`, `.envWF`, `.scoped`): its end is
  `streamEnv` of its records over its start; it is a fresh chain; it keeps well-formedness and
  read-scoping.
* **What its records passed** (`PureRun.basisNamesOk`, `.reads`): the reserved names' check, and
  at a block the ι reading rule at the run's end.
-/

namespace ConLeche.Cached

open ConLeche ConLeche.Semantics

/-! ## Lookups past a push -/

/-- A name an environment with `X` pushed does not hold is none of `X`'s and not in the
environment below. -/
theorem find?_none_append {X : List ConstantInfo} {e : Env} {t : List ProjTable} {n : Name}
    (h : (⟨X ++ e.consts, t⟩ : Env).find? n = none) :
    n ∉ X.map (·.name) ∧ e.find? n = none := by
  unfold Env.find? at h ⊢
  rw [List.find?_append] at h
  cases hX : X.find? (·.name == n) with
  | some x => rw [hX] at h; exact nomatch h
  | none =>
    rw [hX, Option.none_or] at h
    refine ⟨fun hm => ?_, h⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    have := List.find?_eq_none.mp hX x hx
    simp at this

/-- `find?_none_append` at a list pushed oldest first (`Env.pushDelta`'s order). -/
theorem find?_none_append_rev {X : List ConstantInfo} {e : Env} {t : List ProjTable} {n : Name}
    (h : (⟨X.reverse ++ e.consts, t⟩ : Env).find? n = none) :
    n ∉ X.map (·.name) ∧ e.find? n = none := by
  obtain ⟨h₁, h₂⟩ := find?_none_append h
  refine ⟨fun hm => h₁ ?_, h₂⟩
  rw [List.map_reverse, List.mem_reverse]
  exact hm

/-- One constant fresh at `e`: a fresh singleton. -/
theorem freshNames_one {e : Env} {c : ConstantInfo} (h : e.find? c.name = none) :
    FreshNames e ([c].map (·.name)) :=
  ⟨by simp, fun n hn => by
    rw [List.map_cons, List.map_nil, List.mem_singleton] at hn
    rw [hn]; exact h⟩

/-! ## The blocks `readBlock` reads -/

/-- **An accepted block pushes its constants and tables**: the install is the check's final
`pure`. -/
theorem checkBlock_pushes {ops : CheckerOps CheckM} {env env' : Env}
    {block : List ConstantInfo} {p₀ : BlockShape}
    (h : checkBlock ops env block p₀ = .ok env') :
    env' = env.pushDelta (blockConstants p₀) ((blockTables p₀ p₀.members).getD []) := by
  unfold checkBlock at h
  cases ht : blockTables p₀ p₀.members with
  | none =>
    simp only [ht, unwrapOr, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals contradiction
  | some Q =>
    simp only [ht, unwrapOr, bind, Except.bind, pure, Except.pure, Option.getD_some] at h ⊢
    repeat' split at h
    all_goals try contradiction
    all_goals exact (Except.ok.inj h).symm

/-- Every member's former was checked fresh at the base. -/
theorem checkBlockTeles_fresh {mode : CheckMode} {F : Nat} {env : Env} {nP : Nat} :
    ∀ {mss : List MemberShape} {cvs : List (ConstantVal × Level)},
      checkBlockTeles (fueledOps mode F) env nP mss = .ok cvs →
      ∀ ms ∈ mss, env.find? ms.cvT.name = none
  | [], _, _ => fun _ h => nomatch h
  | ms :: rest, cvs, h => by
    unfold checkBlockTeles at h
    obtain ⟨q, hq, h⟩ := exceptBind_ok h
    obtain ⟨qs, hqs, -⟩ := exceptBind_ok h
    obtain ⟨cvT, hn, -, -, hccv, -⟩ := checkBlockTele_shape hq
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [← hn]; exact (checkConstantVal_inv hccv).1
    · exact checkBlockTeles_fresh hqs m hm

/-- The recursors' pins check the family's names pairwise distinct. -/
theorem targetRecPins_nodup {q : BlockShape} {block : List ConstantInfo}
    (h : targetRecPins (m := CheckM) q block = .ok ()) : (q.recs.map (·.cvR.name)).Nodup := by
  by_cases hn : (q.recs.map (·.cvR.name)).Nodup
  · exact hn
  exfalso
  unfold targetRecPins at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  simp only [hn, ↓reduceIte] at h
  repeat' split at h
  all_goals exact nomatch h

/-- The recursors' pins check the grouping: the shape's constructors are the block's, by name. -/
theorem targetRecPins_grouping {q : BlockShape} {block : List ConstantInfo}
    (h : targetRecPins (m := CheckM) q block = .ok ()) :
    ∀ cvTs cs rs, blockSplit block = some (cvTs, cs, rs) →
      q.allCtors.map (·.1.name) = cs.map (·.1.name) := by
  intro cvTs cs rs hs
  apply Classical.byContradiction; intro hne
  unfold targetRecPins at h
  simp only [hs, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' split at h
  all_goals simp_all

/-- The generated family carries the records' names, in order. -/
theorem genRecCheck_out_names {mode : CheckMode} {fe : FEnv} {p : BlockShape}
    {nestedBit : Bool} {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead}
    {Ms₀ : List TargetMajor} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : genRecCheck (fueledOps mode F) fe p nestedBit params tbl rd Ms₀
      block = .ok out) :
    out.map (·.1.name) = p.recs.map (·.cvR.name) := by
  obtain ⟨R⟩ := genRecCheck_run h
  have hcvGs := R.hcvGs
  have hrules := R.hrules
  obtain ⟨hlenG, hallG⟩ := classRecTysOk_run hcvGs
  obtain ⟨hlenO, hallO⟩ := classRecsRulesOk_run hrules
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map]
  cases hi : p.recs[i]? with
  | none =>
    have : out[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hi ⊢
      have : out.length ≤ R.cvGs.length := by rw [hlenO]; exact Nat.min_le_left _ _
      omega
    simp [this]
  | some rc =>
    obtain ⟨c, cvG, hc, hG, ⟨T⟩⟩ := hallG i rc hi
    obtain ⟨rhss, hoi, -⟩ := hallO i cvG c hG hc
    simp only [hoi, Option.map_some]
    rw [T.hcvG]

/-- The formers' conses push the declared formers' names. -/
theorem consBlockInds_names (p₁ : BlockShape) (isRec : Bool) :
    ∀ (l : List ConstantVal) (i : Nat),
      ((l.zipIdx i).map fun x => ConstantInfo.indInfo x.1 (blockCapsAt p₁ x.2 isRec)).map
        (·.name) = l.map (·.name)
  | [], _ => rfl
  | a :: l, i => by
    simp only [List.zipIdx_cons, List.map_cons]
    exact congrArg (a.name :: ·) (consBlockInds_names p₁ isRec l (i + 1))

/-- **A recognised block's constants are fresh**: the formers at the base, the constructors at the
formers' environment, the recursors at the constructors', each stage's names distinct.  A block
`readBlock` reads installs `blockConstants p₀`: the formers, then the constructors, then the
recursors (`blockConstants_names`).  `BlockRun` runs its stages at the reduced members `ms`, whose
declared formers, names and constructors are `p₀`'s (`reduceMembers_inv`). -/
theorem blockRun_fresh {F : Nat} {env env' : Env} {block : List ConstantInfo}
    {p₀ : BlockShape} (hd : ∀ m ∈ p₀.members, m.declared = m.cvT)
    (h : BlockRun F env block p₀ env') :
    FreshNames env ((blockConstants p₀).map (·.name)) := by
  obtain ⟨ms, hms, hAt, -, hndC, hndM, -, isRec, env₁, p₁, sortsss, ctx, holes, rd, Ms,
    kinds, nfs, pos, st, isorts, out, -, hInd, hCtors, -, -, -, -, -, -, hRec, -, -, -, -, -⟩ := h
  obtain ⟨-, hdecl, -, -, hctors⟩ := reduceMembers_inv hd hms
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, hp1, henv1, htele0, hteles, -⟩ :=
    checkBlockInds_shape hInd
  subst hp1
  -- the members' names: declared, at the reduced members, in `p₀`
  have hNM : p₀.members.map (·.declared.name) = ms.map (·.cvT.name) := by
    have e₁ : p₀.members.map (·.declared.name) = (p₀.members.map (·.declared)).map (·.name) := by
      rw [List.map_map]; rfl
    have e₂ : ms.map (·.declared.name) = (ms.map (·.declared)).map (·.name) := by
      rw [List.map_map]; rfl
    rw [e₁, ← hdecl, ← e₂]
    exact List.map_congr_left fun m hm => (hAt m hm).name.symm
  have hNC : p₀.allCtors = ms.flatMap (·.ctors) := by
    show (p₀.members.map (·.ctors)).flatten = _
    rw [← hctors, List.flatMap_def]
  -- the formers: fresh at the base
  have hfrM : ∀ m ∈ ms, env.find? m.cvT.name = none := by
    intro m hm'
    change ms = ms0 :: rest at hm
    rw [hm] at hm'
    rcases List.mem_cons.mp hm' with rfl | hm'
    · obtain ⟨cvT, hn, -, -, hccv, -⟩ := checkBlockTele_shape htele0
      rw [← hn]; exact (checkConstantVal_inv hccv).1
    · exact checkBlockTeles_fresh hteles m hm'
  -- what the formers' environment does not hold
  have hE₁ : ∀ n, env₁.find? n = none → n ∉ ms.map (·.cvT.name) ∧ env.find? n = none := by
    intro n hn
    rw [henv1, consBlockInds_consts'] at hn
    obtain ⟨h₁, h₂⟩ := find?_none_append_rev hn
    refine ⟨fun hm' => h₁ ?_, h₂⟩
    rw [consBlockInds_names]
    have : (({ p₀ with members := ms } : BlockShape).members.map (·.declared)).map (·.name)
        = p₀.members.map (·.declared.name) := by
      show (ms.map (·.declared)).map (·.name) = _
      rw [hdecl, List.map_map]; rfl
    rw [this, hNM]; exact hm'
  -- the constructors: fresh at the formers' environment
  have hfrC : ∀ c ∈ p₀.allCtors, env₁.find? c.1.name = none := by
    intro c hc
    rw [hNC, List.mem_flatMap] at hc
    obtain ⟨m, hm', hc⟩ := hc
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hm'
    obtain ⟨sortss, -, -, -, hall⟩ := hCtors.2 i m hi
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    obtain ⟨-, -, -, ⟨-, hccv⟩, -⟩ := hall j c c hj hj
    exact (checkConstantVal_inv hccv).1
  -- what the constructors' environment does not hold
  have hE₂ : ∀ n, (consBlockCtors ({ p₀ with members := ms } : BlockShape).nP
      (({ p₀ with members := ms } : BlockShape).withSort s0).ctorGroups env₁).find? n = none →
      n ∉ p₀.allCtors.map (·.1.name) ∧ env₁.find? n = none := by
    intro n hn
    rw [consBlockCtors_eq] at hn
    obtain ⟨h₁, h₂⟩ := find?_none_append_rev hn
    refine ⟨fun hm' => h₁ ?_, h₂⟩
    have : ((({ p₀ with members := ms } : BlockShape).withSort s0).ctorGroups.flatMap
        fun g => g.2.map fun c => ConstantInfo.ctorInfo c.1
          ({ p₀ with members := ms } : BlockShape).nP c.2 g.1).map (·.name)
        = p₀.allCtors.map (·.1.name) := by
      rw [hNC]
      simp [BlockShape.ctorGroups, BlockShape.withSort, List.flatMap_def, List.map_flatten,
        List.map_map, Function.comp_def, ConstantInfo.name, ConstantInfo.toConstantVal]
    rw [this]
    exact hm'
  -- the recursors: fresh at the constructors' environment, distinct by the pins
  unfold checkBlockRec at hRec
  obtain ⟨R⟩ := genRecCheck_run hRec
  have hndR : (p₀.recs.map (·.cvR.name)).Nodup := by have := targetRecPins_nodup R.pins; exact this
  have hnamesR := genRecCheck_out_names hRec
  have hfrR : ∀ rc ∈ p₀.recs, (consBlockCtors ({ p₀ with members := ms } : BlockShape).nP
      (({ p₀ with members := ms } : BlockShape).withSort s0).ctorGroups env₁).find?
        rc.cvR.name = none := by
    intro rc hrc
    have : rc.cvR.name ∈ out.map (·.1.name) := by
      rw [hnamesR]; exact List.mem_map_of_mem hrc
    obtain ⟨o, ho, hon⟩ := List.mem_map.mp this
    rw [← hon]
    exact genRecCheck_out_fresh hRec o ho
  -- assemble
  have hndM' : (ms.map (·.cvT.name)).Nodup := hndM
  have hndC' : (p₀.allCtors.map (·.1.name)).Nodup := by
    have : ({ p₀ with members := ms } : BlockShape).allCtors = p₀.allCtors := by
      show (ms.map (·.ctors)).flatten = _
      rw [hNC, List.flatMap_def]
    rw [← this]; exact hndC
  rw [blockConstants_names, hNM]
  refine ⟨?_, fun n hn => ?_⟩
  · rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hndM', hndC', fun a ha b hb => ?_⟩, hndR, fun a ha b hb => ?_⟩
    · rintro rfl
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact (hE₁ _ (hfrC c hc)).1 ha
    · rintro rfl
      obtain ⟨rc, hrc, hn⟩ := List.mem_map.mp hb
      have hf := hfrR rc hrc
      rw [hn] at hf
      obtain ⟨h₃, h₄⟩ := hE₂ _ hf
      rcases List.mem_append.mp ha with ha | ha
      · exact (hE₁ _ h₄).1 ha
      · exact h₃ ha
  · rcases List.mem_append.mp hn with hn | hn
    · rcases List.mem_append.mp hn with hn | hn
      · obtain ⟨m, hm', rfl⟩ := List.mem_map.mp hn
        exact hfrM m hm'
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
        exact (hE₁ _ (hfrC c hc)).2
    · obtain ⟨rc, hrc, rfl⟩ := List.mem_map.mp hn
      exact (hE₁ _ (hE₂ _ (hfrR rc hrc)).2).2

/-! ## The value arms -/

/-- The stored type is the declared one, and the name was fresh. -/
theorem constantValRun_type {F : Nat} {env : Env} {cv : ConstantVal} {type' : Expr}
    (h : ConstantValRun F env cv type') : type' = cv.type ∧ env.find? cv.name = none :=
  ⟨h.2.2.2.2.1, Option.isNone_iff_eq_none.mp h.1⟩

/-- The tolerated axiom is no standard one. -/
theorem stdAxiomOk_sorry {env : Env} {cv : ConstantVal} (ht : cv.name = sorryAxName) :
    stdAxiomOk env cv = false := by
  rw [stdAxiomOk, ite_eq_right, ite_eq_right] <;> rw [ht] <;> decide

/-! ## The whole step -/

variable {pins : List NatOpPinSet}

/-- The run record, both halves at once. -/
theorem checkDecl_pushes_fresh {F : Nat} {env env' : Env} {d : Declaration}
    (h : checkDecl .verified (fueledOps .verified F) pins env d = .ok env') :
    env' = env.pushDelta (declConstants d) (declTables d) ∧
      FreshNames env ((declConstants d).map (·.name)) := by
  obtain ⟨-, hrun⟩ := checkDeclRun_ofEnvFactsK h
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, hvf, rfl, -, -⟩ := hrun
    obtain ⟨rfl, hfr⟩ := constantValRun_type hcv
    obtain rfl : value' = value := hvf.2.2.1
    exact ⟨rfl, freshNames_one hfr⟩
  | thmDecl cv value =>
    obtain ⟨-, type', value', hcv, -, -, rfl⟩ := hrun
    obtain ⟨rfl, hfr⟩ := constantValRun_type hcv
    exact ⟨rfl, freshNames_one hfr⟩
  | opaqueDecl cv value =>
    obtain ⟨-, type', value', hcv, -, rfl, -⟩ := hrun
    obtain ⟨rfl, hfr⟩ := constantValRun_type hcv
    exact ⟨rfl, freshNames_one hfr⟩
  | axiomDecl cv =>
    rcases hrun with ⟨hq, -, -, hfr, rfl⟩ | ⟨hqs, type', -, hcv, hdisj⟩
    · simp only [declConstants, declTables, ite_eq_left hq]
      exact ⟨rfl, freshNames_one (Option.isNone_iff_eq_none.mp hfr)⟩
    · obtain ⟨rfl, hfr⟩ := constantValRun_type hcv
      dsimp only at hdisj
      simp only [declConstants, declTables, ite_eq_right hqs]
      rcases hdisj with ⟨hstd, rfl⟩ | ⟨hn, -, rfl⟩ | ⟨hn, -, rfl⟩ |
          ⟨-, -, -, -, -, -, hs, rfl⟩
      · have hs : cv.name ≠ sorryAxName := fun he => by
          have : stdAxiomOk env cv = true := hstd
          rw [stdAxiomOk_sorry he] at this
          exact nomatch this
        rw [ite_eq_right hs]
        exact ⟨rfl, freshNames_one hfr⟩
      · have hs : cv.name ≠ sorryAxName := by rw [hn]; decide
        rw [ite_eq_right hs]
        exact ⟨rfl, freshNames_one hfr⟩
      · have hs : cv.name ≠ sorryAxName := by rcases hn with hn | hn <;> rw [hn] <;> decide
        rw [ite_eq_right hs]
        exact ⟨rfl, freshNames_one hfr⟩
      · rw [ite_eq_left hs]
        exact ⟨rfl, List.nodup_nil, fun _ h => nomatch h⟩
  | quotDecl k cv =>
    obtain ⟨-, -, hfr, rfl⟩ := hrun
    exact ⟨rfl, freshNames_one (Option.isNone_iff_eq_none.mp hfr)⟩
  | indDecl block nP =>
    simp only [DeclKindRun, DeclIndRunDispatchK] at hrun
    obtain ⟨hK, -⟩ := ConLeche.checkDecl_inv h
    simp only [ConLeche.checkDeclKind] at hK
    cases hbp : readBlock nP block with
    | error e => simp only [hbp] at hrun
    | ok p =>
      simp only [hbp] at hrun
      simp only [declConstants, declTables, hbp]
      by_cases hok : indParamsOk nP block = true
      · rw [ite_eq_left hok, hbp] at hK
        -- the block's install, then the ι reading rule at its output (`blockReadsOk`)
        obtain ⟨env₁, hK1, hK2⟩ := exceptBind_ok hK
        have he : env₁ = env' := by
          cases hr : blockReadsOk env₁.find? p with
          | error e => rw [hr] at hK2; exact nomatch hK2
          | ok u => rw [hr] at hK2; exact Except.ok.inj hK2
        subst he
        exact ⟨checkBlock_pushes hK1, blockRun_fresh (readBlock_declared hbp) hrun⟩
      · rw [ite_eq_right hok] at hK
        exact nomatch hK

/-- **An accepted pure step pushes what its record installs**: the result environment is
`streamEnv`'s step, a function of the record. -/
theorem checkDecl_pushes {F : Nat} {env env' : Env} {d : Declaration}
    (h : checkDecl .verified (fueledOps .verified F) pins env d = .ok env') :
    env' = env.pushDelta (declConstants d) (declTables d) :=
  (checkDecl_pushes_fresh h).1

/-- **What an accepted pure step pushes is fresh**: its names pairwise distinct and none of them
in the environment it ran at. -/
theorem checkDecl_fresh {F : Nat} {env env' : Env} {d : Declaration}
    (h : checkDecl .verified (fueledOps .verified F) pins env d = .ok env') :
    ((declConstants d).map (·.name)).Nodup ∧ ∀ c ∈ declConstants d, env.find? c.name = none := by
  obtain ⟨-, hnd, hfr⟩ := checkDecl_pushes_fresh h
  exact ⟨hnd, fun c hc => hfr _ (List.mem_map_of_mem hc)⟩

/-- **An accepted pure block step applied the ι reading rule** (`blockReadsOk`) at its output. -/
theorem checkDecl_blockReadsOk {F : Nat} {env env' : Env} {block : List ConstantInfo} {nP : Nat}
    (h : checkDecl .verified (fueledOps .verified F) pins env (.indDecl block nP) = .ok env')
    {p : BlockShape} (hp : readBlock nP block = .ok p) : blockReadsOk env'.find? p = .ok () := by
  obtain ⟨hK, -⟩ := ConLeche.checkDecl_inv h
  simp only [ConLeche.checkDeclKind] at hK
  by_cases hok : indParamsOk nP block = true
  · rw [ite_eq_left hok, hp] at hK
    obtain ⟨env₁, -, hK2⟩ := exceptBind_ok hK
    cases hr : blockReadsOk env₁.find? p with
    | error e => rw [hr] at hK2; exact nomatch hK2
    | ok u =>
      rw [hr] at hK2
      obtain rfl := Except.ok.inj hK2
      cases u; exact hr
  · rw [ite_eq_right hok] at hK
    exact nomatch hK

/-! ## The push chain -/

/-- **A record's table is one of its formers'.** -/
theorem declTables_former {e : Declaration} {t : ProjTable} (ht : t ∈ declTables e) :
    ∃ cv caps, .indInfo cv caps ∈ declConstants e ∧ cv.name = t.structName := by
  cases e with
  | indDecl block nP =>
    simp only [declTables, declConstants] at ht ⊢
    split at ht
    · next p hp =>
      obtain ⟨ms, hms, he⟩ := blockTables_getD_names p ht
      obtain ⟨i, hi⟩ := List.getElem_of_mem hms
      refine ⟨ms.declared, blockCapsAt p i (blockIsRec p), ?_, he.symm⟩
      simp only [blockConstants, blockFormers, List.mem_append]
      refine .inl (.inl (List.mem_map.mpr ⟨(ms.declared, i), ?_, rfl⟩))
      rw [List.mem_zipIdx_iff_getElem?]
      obtain ⟨hlt, rfl⟩ := hi
      simp [List.getElem?_eq_getElem hlt]
    · exact absurd ht (List.not_mem_nil)
  | _ => simp [declTables] at ht

/-- A constant a block installs is a type former, a constructor or one of its recursors. -/
theorem blockConstants_rec {p : BlockShape} {ci : ConstantInfo} (h : ci ∈ blockConstants p)
    {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule}
    (hci : ci = .recInfo cv mI rP isK rules) : ci ∈ blockRecs p p.recs := by
  unfold blockConstants at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · unfold blockFormers at h
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
      exact nomatch hci
    · unfold blockCtors at h
      obtain ⟨_, -, h⟩ := List.mem_flatMap.mp h
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
      exact nomatch hci
  · exact h


theorem not_mem_names_of_find_none {E : Env} {n : Name} (h : E.find? n = none) :
    n ∉ E.consts.map (·.name) := by
  intro hm
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
  unfold Env.find? at h
  have := List.find?_eq_none.mp h c hc
  simp at this

/-- **A step pushing fresh names extends a fresh chain**: its constants fresh, its tables at its
formers' names. -/
theorem pushChain_step {E₀ E : Env} {pd : Declaration}
    (h : PushChain E₀ (mkFEnv E)) (hnd : ((declConstants pd).map (·.name)).Nodup)
    (hfr : ∀ c ∈ declConstants pd, E.find? c.name = none) :
    PushChain E₀ (mkFEnv (E.pushDelta (declConstants pd) (declTables pd))) := by
  obtain ⟨-, ⟨new, hc, hndn, hfrn⟩, hNd, ⟨newQ, hq, hfrq⟩⟩ := h
  have hE : (mkFEnv E).env = E := rfl
  rw [hE] at hc hq hNd
  have hfr₀ : ∀ c ∈ declConstants pd, E₀.find? c.name = none := fun c hcm =>
    PushChain.find?_none ⟨rfl, ⟨new, hc, hndn, hfrn⟩, hNd, ⟨newQ, hq, hfrq⟩⟩
      (by rw [mkFEnv_find?]; exact hfr c hcm)
  have hdisj : ∀ a ∈ (declConstants pd).reverse.map (·.name), a ∉ E.consts.map (·.name) := by
    intro a ha
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp ha
    exact not_mem_names_of_find_none (hfr c (List.mem_reverse.mp hcm))
  have hndr : ((declConstants pd).reverse.map (·.name)).Nodup := by
    rw [List.map_reverse]; exact (List.reverse_perm _).nodup_iff.mpr hnd
  refine ⟨rfl, ⟨(declConstants pd).reverse ++ new, ?_, ?_, ?_⟩, ?_,
    ⟨(declTables pd).reverse ++ newQ, ?_, ?_⟩⟩
  · show (declConstants pd).reverse ++ E.consts = _
    rw [hc, List.append_assoc]
  · rw [List.map_append, List.nodup_append]
    refine ⟨hndr, hndn, fun a ha b hb hab => ?_⟩
    subst hab
    apply hdisj a ha
    rw [hc, List.map_append]
    exact List.mem_append_left _ hb
  · intro c hcm
    rcases List.mem_append.mp hcm with hcm | hcm
    · exact hfr₀ c (List.mem_reverse.mp hcm)
    · exact hfrn c hcm
  · intro hnd₀
    have hNE := hNd hnd₀
    show ((declConstants pd).reverse ++ E.consts).map (·.name) |>.Nodup
    rw [List.map_append, List.nodup_append]
    exact ⟨hndr, hNE, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
  · show (declTables pd).reverse ++ E.tables = _
    rw [hq, List.append_assoc]
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨cv, caps, hcm, hn⟩ := declTables_former (List.mem_reverse.mp ht)
      rw [← hn]
      exact hfr₀ _ hcm
    · exact hfrq t ht

/-! ## The run -/

/-- The pure fold from one fuel is a run. -/
theorem _root_.ConLeche.PureRun.of_foldlM {F : Nat} :
    ∀ (ds : List Declaration) {E E' : Env},
      ds.foldlM (checkDecl .verified (fueledOps .verified F) pins) E = .ok E' → PureRun pins ds E E'
  | [], _, _, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ .nil _
  | d :: ds, E, _, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl .verified (fueledOps .verified F) pins E d with
    | error e => rw [hd] at h; exact nomatch h
    | ok E₁ =>
      rw [hd] at h
      exact .cons ⟨F, hd⟩ (PureRun.of_foldlM ds h)

/-- Two runs, one after the other. -/
theorem _root_.ConLeche.PureRun.append {ds ds' : List Declaration} {E E₁ E₂ : Env}
    (h : PureRun pins ds E E₁) (h' : PureRun pins ds' E₁ E₂) : PureRun pins (ds ++ ds') E E₂ := by
  induction h with
  | nil => exact h'
  | cons hs _ ih => exact .cons hs (ih h')

/-- **A run's end is what its records install over its start.** -/
theorem _root_.ConLeche.PureRun.env {ds : List Declaration} {E E' : Env} (h : PureRun pins ds E E') :
    E' = streamEnv ds E := by
  induction h with
  | nil => rfl
  | cons hs _ ih =>
    obtain ⟨F, hF⟩ := hs
    rw [ih, checkDecl_pushes hF]
    rfl

/-- **A run is a fresh chain.** -/
theorem _root_.ConLeche.PureRun.chain {ds : List Declaration} {E₀ E E' : Env} (h : PureRun pins ds E E')
    (hp : PushChain E₀ (mkFEnv E)) : PushChain E₀ (mkFEnv E') := by
  induction h with
  | nil => exact hp
  | cons hs _ ih =>
    obtain ⟨F, hF⟩ := hs
    obtain ⟨hnd, hfr⟩ := checkDecl_fresh hF
    rw [checkDecl_pushes hF] at ih
    exact ih (pushChain_step hp hnd hfr)

/-- **A run keeps the environment well formed.** -/
theorem _root_.ConLeche.PureRun.envWF {ds : List Declaration} {E E' : Env} (h : PureRun pins ds E E')
    (hw : EnvWF E) : EnvWF E' := by
  induction h with
  | nil => exact hw
  | cons hs _ ih =>
    obtain ⟨F, hF⟩ := hs
    exact ih (checkDecl_envWF hw hF)

/-- **A run keeps the environment read-scoped.** -/
theorem _root_.ConLeche.PureRun.scoped {ds : List Declaration} {E E' : Env} (h : PureRun pins ds E E')
    (hw : EnvWF E) (hS : Scoped E) : Scoped E' := by
  induction h with
  | nil => exact hS
  | cons hs _ ih =>
    obtain ⟨F, hF⟩ := hs
    exact ih (checkDecl_envWF hw hF) (checkDecl_scoped hw hS hF)

/-- **Every record of a run passed the reserved names' check.** -/
theorem _root_.ConLeche.PureRun.basisNamesOk {ds : List Declaration} {E E' : Env} (h : PureRun pins ds E E') :
    ∀ d ∈ ds, ConLeche.basisNamesOk d = true := by
  induction h with
  | nil => exact fun _ h => nomatch h
  | cons hs _ ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨F, hF⟩ := hs
      exact (ConLeche.checkDecl_inv hF).2
    · exact ih d hd

/-- **Every recursor a run installs reads** at the run's end, or is a quotient constant. -/
theorem _root_.ConLeche.PureRun.reads {ds : List Declaration} {E E' : Env} (h : PureRun pins ds E E') :
    ∀ d ∈ ds, ∀ ci ∈ declConstants d, RecReads E'.find? ci ∨ ∃ k cv, ci = quotAt k cv := by
  induction h with
  | nil => exact fun _ h => nomatch h
  | @cons pd ds E E₁ E' hs rest ih =>
    obtain ⟨F, hF⟩ := hs
    intro d hd ci hci
    rcases List.mem_cons.mp hd with rfl | hd
    · have hq : PushChain E₁ (mkFEnv E') := rest.chain (PushChain.refl E₁)
      cases d with
      | indDecl block nP =>
        simp only [declConstants] at hci
        split at hci
        · next p' hp' =>
          left
          intro cv mI rP isK rules hcr
          have hR := blockReadsOk_reads (checkDecl_blockReadsOk hF hp') ci
            (blockConstants_rec hci hcr)
          exact RecReads.mono (fun n c h => PushChain.find?_some hq h) hR cv mI rP isK rules hcr
        · exact nomatch hci
      | quotDecl k cv =>
        simp only [declConstants, List.mem_singleton] at hci
        exact .inr ⟨k, cv, hci⟩
      | axiomDecl cv =>
        left; intro _ _ _ _ _ hcr
        simp only [declConstants] at hci
        split at hci
        · rw [List.mem_singleton] at hci; subst hci
          simp [quotAt, quotPin, BasisKind.decls, quotBasis, quotSoundA, QuotKind.slot,
            ConstantInfo.atLps] at hcr
        · split at hci
          · exact nomatch hci
          · rw [List.mem_singleton] at hci; subst hci; exact nomatch hcr
      | defnDecl | thmDecl | opaqueDecl =>
        left; intro _ _ _ _ _ hcr
        simp only [declConstants, List.mem_singleton] at hci
        subst hci; exact nomatch hcr
    · exact ih d hd ci hci

/-! ## The cached fold's run is a pure one -/

/-- **An accepting run of the cached fold is a run of the pure one**: from a canonical index whose
environment is well formed, every record's cached check is a pure `checkDecl` run
(`checkDeclStepC_run`), and the run ends at a canonical index. -/
theorem DeclsRun.pureRun {maxNatSize : Nat} {ds : List Declaration} {p q : Nat × FEnv}
    (h : DeclsRun .verified pins maxNatSize none ds p q) :
    p.2 = mkFEnv p.2.env → EnvWF p.2.env → PureRun pins ds p.2.env q.2.env ∧ q.2 = mkFEnv q.2.env := by
  induction h with
  | nil p => exact fun hfe _ => ⟨.nil _, hfe⟩
  | @cons pd ds p p₁ q hstep rest ih =>
    intro hfe hw
    obtain ⟨fe₁, s₁, rfl, hstepC⟩ := declStep_ok hstep
    rw [hfe] at hstepC
    obtain ⟨-, hfe₁, F, hF⟩ := checkDeclStepC_run hw (CSOKF.fresh _) hstepC
    obtain ⟨hrun, hq⟩ := ih hfe₁ (checkDecl_envWF hw hF)
    exact ⟨.cons ⟨F, hF⟩ hrun, hq⟩

end ConLeche.Cached
