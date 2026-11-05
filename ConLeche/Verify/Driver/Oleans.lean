module

public import ConLeche.Driver.CheckMain
public import ConLeche.Verify.Frontend.Olean.Files

/-!
# An `--olean` run, in the model (task #481)

An `--olean` run reads a theorem's value in its check, through the class.  On a snapshot,
every reference therefore stands for one value, the specification's (`ValueAt`, `fillOf`),
and what an exit 0 means is about the records with those values in place:

* `readValue_spec`: a value read is `ValueAt` of its reference, from any state a worker can
  reach (`CacheOK`), over any frontier that holds only the specification's values;
* `oleanStep_spec`: a job that passes has passed on the record holding the value
  (`JobFact`), which is the check phase's whole contribution;
* `checkOleansG_accept`: all the jobs passing, and the install's run transported across the
  values (`InstallRun.fill`), is an accept of `checkDecls` over the records with their
  values in place;
* `checkMainG_oleans_accept`: the same from the driver's run.

That those records are the specification's own is `readOleans_filled`
(`ConLeche/Verify/Frontend/Olean/Files.lean`): a theorem's record, with its value in place, is
the constant the specification reads off that module's files (`constSpec`), its statement and
its proof.
-/

public section

namespace ConLeche.Driver

open ConLeche Frontend.Olean Cached

/-- **A reference, with what it stands for on a snapshot put in its place.** -/
noncomputable def fillOf (sp : SearchPath) (fs : FS) (values : Array ModRef) : Expr → Expr
  | .bvar code =>
    open Classical in
    if h : ∃ e, ValueAt sp fs values code e then h.choose else .bvar code
  | e => e

theorem fillOf_value {sp : SearchPath} {fs : FS} {values : Array ModRef} {code : Nat} {e : Expr}
    (h : ValueAt sp fs values code e) : fillOf sp fs values (.bvar code) = e := by
  have hex : ∃ e, ValueAt sp fs values code e := ⟨e, h⟩
  simp only [fillOf, hex, ↓reduceDIte]
  exact hex.choose_spec.unique h

/-! ## A worker's state -/

/-- **What a worker's kept region is**: its module's, on the snapshot. -/
def CacheOK (sp : SearchPath) (fs : FS) (values : Array ModRef) (c : ValueCache) : Prop :=
  ∀ r, c.region = some r → ∃ md f a, values[c.idx]? = some md ∧
    (readFiles sp md.name .private : ModelIO _) fs (.ok (.ok f)) ∧
    f.viewRegion .private = some (r, a)

theorem cacheOK_empty {sp : SearchPath} {fs : FS} {values : Array ModRef} :
    CacheOK sp fs values {} := fun r h => by simp at h

variable {sp : SearchPath} {fs : FS} {values : Array ModRef}

/-- The region of a module, from a kept one or the files. -/
theorem regionFor_spec {md : ModRef} {idx : Nat} {c : ValueCache}
    {o : ValueCache × Except CheckError Region} (hmd : values[idx]? = some md)
    (hc : CacheOK sp fs values c)
    (h : (regionFor sp md.name idx c : ModelIO _) fs (.ok o)) :
    CacheOK sp fs values o.1 ∧ ∀ r, o.2 = .ok r → ∃ f a,
      (readFiles sp md.name .private : ModelIO _) fs (.ok (.ok f)) ∧
      f.viewRegion .private = some (r, a) := by
  have hread : (regionFor.readRegion sp md.name idx : ModelIO _) fs (.ok o) →
      CacheOK sp fs values o.1 ∧ ∀ r, o.2 = .ok r → ∃ f a,
        (readFiles sp md.name .private : ModelIO _) fs (.ok (.ok f)) ∧
        f.viewRegion .private = some (r, a) := by
    intro h
    simp only [regionFor.readRegion, ModelIO.bind_ok] at h
    obtain ⟨x, hx, h⟩ := h
    rcases x with e | f
    · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
      subst h
      exact ⟨cacheOK_empty, fun r hr => by simp at hr⟩
    · cases hv : f.viewRegion .private with
      | none =>
        simp only [hv, ModelIO.pure_iff, Except.ok.injEq] at h
        subst h
        exact ⟨cacheOK_empty, fun r hr => by simp at hr⟩
      | some x =>
        obtain ⟨r, a⟩ := x
        simp only [hv, ModelIO.pure_iff, Except.ok.injEq] at h
        subst h
        refine ⟨fun r' hr' => ?_, fun r' hr' => ?_⟩
        · simp only [Option.some.injEq] at hr'
          subst hr'
          exact ⟨md, f, a, hmd, hx, hv⟩
        · simp only [Except.ok.injEq] at hr'
          subst hr'
          exact ⟨f, a, hx, hv⟩
  simp only [regionFor] at h
  cases hr : c.region with
  | none =>
    simp only [hr] at h
    exact hread h
  | some r =>
    simp only [hr] at h
    by_cases hidx : (c.idx == idx) = true
    · simp only [hidx, ↓reduceIte, ModelIO.pure_iff, Except.ok.injEq] at h
      subst h
      refine ⟨hc, fun r' hr' => ?_⟩
      simp only [Except.ok.injEq] at hr'
      subst hr'
      obtain ⟨md', f, a, h1, h2, h3⟩ := hc r hr
      simp only [beq_iff_eq] at hidx
      rw [hidx, hmd] at h1
      cases h1
      exact ⟨f, a, h2, h3⟩
    · simp only [hidx] at h
      exact hread h

/-- **A value read is what its reference stands for.** -/
theorem readValue_spec {c : ValueCache} {code : Nat} {o : ValueCache × Except CheckError Expr}
    (hgood : ∀ md ∈ values, ∃ f r a, (readFiles sp md.name .private : ModelIO _) fs (.ok (.ok f)) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r)
    (hc : CacheOK sp fs values c)
    (h : (readValue sp values c code : ModelIO _) fs (.ok o)) :
    CacheOK sp fs values o.1 ∧ ∀ e, o.2 = .ok e → ValueAt sp fs values code e := by
  simp only [readValue] at h
  cases hmd : values[refModule code]? with
  | none =>
    simp only [hmd, ModelIO.pure_iff, Except.ok.injEq] at h
    subst h
    exact ⟨hc, fun e he => by simp at he⟩
  | some md =>
    simp only [hmd, ModelIO.bind_ok] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hc', hr⟩ := regionFor_spec hmd hc hx
    obtain ⟨c', y⟩ := x
    simp only at hc' hr
    rcases y with e | r
    · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
      subst h
      exact ⟨hc', fun e he => by simp at he⟩
    · simp only at h
      obtain ⟨f, a, hf, hreg⟩ := hr r rfl
      cases hv : frontierExpr r md.frontier (refLoc code) with
      | some v =>
        simp only [hv, ModelIO.pure_iff, Except.ok.injEq] at h
        subst h
        refine ⟨hc', fun e he => ?_⟩
        simp only [Except.ok.injEq] at he
        subst he
        obtain ⟨f', r', a', hf', hreg', hB⟩ := hgood md (Array.mem_of_getElem? hmd)
        obtain rfl := readFiles_unique hf hf'
        rw [hreg] at hreg'
        cases hreg'
        rw [frontierExpr_eq hB] at hv
        exact ⟨md, f, r, a, hmd, hf, hreg, hv⟩
      | none =>
        simp only [hv, ModelIO.pure_iff, Except.ok.injEq] at h
        subst h
        exact ⟨hc', fun e he => by simp at he⟩

/-! ## A job -/

/-- **What a job that passed establishes**, at the record holding its value. -/
def JobFact (mode : CheckMode) (J : Jobs) (F : Expr → Expr) (t : Nat) : Prop :=
  match J.order[t]? with
  | some (false, k) => ∀ h : k < J.pend.size, ∃ s,
      checkPending mode J.fe (fillPend F J.pend[k]) {} = .ok ((), s)
  | some (true, b) => ∀ h : b < J.D.size, J.D[b].Ok mode natOpPinSets
  | none => True

/-- `runJob` answers about the job it was asked. -/
theorem runJob_job {mode : CheckMode} {pins : List NatOpPinSet} {fe : FEnv}
    {pend : Array PendingCheck} {D : Array BlockCheck} {j : Job} {x : { j : Job // JobOk mode pins fe pend D j }}
    (h : runJob mode pins fe pend D j = .ok x) : x.1 = j := by
  unfold runJob at h
  split at h
  · split at h
    · split at h
      · simp only [Except.ok.injEq] at h
        subst h
        rfl
      · cases h
    · cases h
  · split at h
    · split at h
      · simp only [Except.ok.injEq] at h
        subst h
        rfl
      · cases h
    · cases h

/-- A job that reads no file passed: what it establishes, where no value is in question. -/
theorem runPlain_fact {mode : CheckMode} {J : Jobs} {F : Expr → Expr} {t : Nat}
    (hF : ∀ k (h : k < J.pend.size), J.order[t]? = some (false, k) →
      fillPend F J.pend[k] = J.pend[k])
    (h : runPlain mode J t = .ok ()) : JobFact mode J F t := by
  unfold runPlain at h
  cases hx : runAt mode J t with
  | error e => simp [hx] at h
  | ok x =>
    unfold runAt at hx
    unfold JobFact
    cases ho : J.order[t]? with
    | none => simp [ho] at hx
    | some j =>
      simp only [ho] at hx
      obtain ⟨j', hj⟩ := x
      obtain rfl : j' = j := runJob_job hx
      obtain ⟨b, k⟩ := j'
      cases b with
      | false =>
        simp only
        intro hk
        have := (hj : JobOk _ _ _ _ _ _)
        simp only [JobOk, Bool.false_eq_true, ↓reduceIte] at this
        obtain ⟨s, hs⟩ := this hk
        exact ⟨s, by rw [hF k hk ho]; exact hs⟩
      | true =>
        simp only
        intro hk
        have := (hj : JobOk _ _ _ _ _ _)
        simp only [JobOk, ↓reduceIte] at this
        exact this hk

/-- **One job's run.** -/
theorem oleanJobRun_spec {mode : CheckMode} {J : Jobs} {c : ValueCache} {t : Nat}
    {o : ValueCache × Except (CheckError × Nat) Unit}
    (hgood : ∀ md ∈ values, ∃ f r a, (readFiles sp md.name .private : ModelIO _) fs (.ok (.ok f)) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r)
    (hc : CacheOK sp fs values c)
    (h : (oleanJobRun mode J sp values c t : ModelIO _) fs (.ok o)) :
    CacheOK sp fs values o.1 ∧ (o.2 = .ok () → JobFact mode J (fillOf sp fs values) t) := by
  have hplain : ∀ {r : ValueCache × Except (CheckError × Nat) Unit},
      (pure (c, runPlain mode J t) : ModelIO _) fs (.ok r) →
      (∀ k (hk : k < J.pend.size), J.order[t]? = some (false, k) →
        fillPend (fillOf sp fs values) J.pend[k] = J.pend[k]) →
      CacheOK sp fs values r.1 ∧ (r.2 = .ok () → JobFact mode J (fillOf sp fs values) t) := by
    intro r hr hF
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hr
    subst hr
    exact ⟨hc, runPlain_fact hF⟩
  unfold oleanJobRun at h
  cases hord : J.order[t]? with
  | none =>
    simp only [hord] at h
    refine hplain h fun k' hk' ho => ?_
    rw [hord] at ho
    cases ho
  | some j =>
    obtain ⟨b, k⟩ := j
    cases b with
    | true =>
      simp only [hord] at h
      refine hplain h fun k' hk' ho => ?_
      rw [hord] at ho
      simp at ho
    | false =>
      simp only [hord] at h
      cases hpc : J.pend[k]? with
      | none =>
        simp only [hpc] at h
        refine hplain h fun k' hk' ho => ?_
        rw [hord] at ho
        simp only [Option.some.injEq, Prod.mk.injEq, true_and] at ho
        subst ho
        rw [Array.getElem?_eq_getElem hk'] at hpc
        cases hpc
      | some pc =>
        simp only [hpc] at h
        obtain ⟨hk, hpk⟩ := Array.getElem?_eq_some_iff.mp hpc
        -- a theorem's check on a reference reads its value
        by_cases hth : ∃ code, pc.vg.kind = .thm ∧ pc.vg.jv = .bvar code
        · obtain ⟨code, hkind, hjv⟩ := hth
          simp only [hkind, hjv, ModelIO.bind_ok] at h
          obtain ⟨x, hx, h⟩ := h
          obtain ⟨hc', hv⟩ := readValue_spec hgood hc hx
          obtain ⟨c', y⟩ := x
          simp only at hc' hv
          rcases y with e | v
          · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
            subst h
            exact ⟨hc', fun he => by simp at he⟩
          · cases hch : checkPending mode J.fe (fillPend (fun _ => v) pc) {} with
            | error e =>
              simp only [hch, ModelIO.pure_iff, Except.ok.injEq] at h
              subst h
              exact ⟨hc', fun he => by simp at he⟩
            | ok x =>
              simp only [hch, ModelIO.pure_iff, Except.ok.injEq] at h
              subst h
              refine ⟨hc', fun _ => ?_⟩
              unfold JobFact
              simp only [hord]
              intro hk'
              obtain ⟨⟨⟩, s⟩ := x
              refine ⟨s, ?_⟩
              have hval := fillOf_value (hv v rfl)
              have hsame : fillPend (fillOf sp fs values) J.pend[k] = fillPend (fun _ => v) pc := by
                rw [hpk]
                simp only [fillPend, hkind, hjv, hval]
              rw [hsame]
              exact hch
        · have hpl : (pure (c, runPlain mode J t) : ModelIO _) fs (.ok o) := by
            revert h
            cases hkind : pc.vg.kind <;> cases hj : pc.vg.jv <;> simp only [] <;>
              first
                | exact id
                | exact fun _ => absurd ⟨_, hkind, hj⟩ hth
          refine hplain hpl fun k' hk' ho => ?_
          rw [hord] at ho
          simp only [Option.some.injEq, Prod.mk.injEq, true_and] at ho
          subst ho
          rw [hpk]
          unfold fillPend
          cases hkind : pc.vg.kind
          case thm =>
            have hF : fillOf sp fs values pc.vg.jv = pc.vg.jv := by
              cases hj : pc.vg.jv with
              | bvar code => exact absurd ⟨code, hkind, hj⟩ hth
              | _ => rfl
            simp only [hF]
          all_goals rfl

/-- **One job of the pool.** -/
theorem oleanStep_spec {mode : CheckMode} {run : OleanRun} {pl : PoolLive} {J : Jobs}
    {s : OleanWorker} {t : Nat} {o : OleanWorker × Except (CheckError × Nat) Unit}
    (hgood : ∀ md ∈ values, ∃ f r a, (readFiles sp md.name .private : ModelIO _) fs (.ok (.ok f)) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r)
    (hc : CacheOK sp fs values s.cache)
    (h : (oleanStep mode run pl J sp values s t : ModelIO _) fs (.ok o)) :
    CacheOK sp fs values o.1.cache ∧ (o.2 = .ok () → JobFact mode J (fillOf sp fs values) t) := by
  simp only [oleanStep, ModelIO.bind_ok] at h
  obtain ⟨_, -, x, hx, _, -, h⟩ := h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  subst h
  exact oleanJobRun_spec hgood hc hx

/-- **Every state a worker can reach keeps its module's region.** -/
theorem oleanWorker_reach {mode : CheckMode} {run : OleanRun} {pl : PoolLive} {J : Jobs}
    (hgood : ∀ md ∈ values, ∃ f r a, (readFiles sp md.name .private : ModelIO _) fs (.ok (.ok f)) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r)
    {s : OleanWorker}
    (h : WorkerReach (fun w => ({ w } : OleanWorker)) (oleanStep mode run pl J sp values) fs s) :
    CacheOK sp fs values s.cache := by
  induction h with
  | init w => exact cacheOK_empty
  | step _ hs ih => exact (oleanStep_spec hgood ih hs).1

/-! ## The check phase -/

/-- Each element of a successful sequential map succeeded. -/
theorem mapExcept_each {α β ε : Type} {f : α → ModelIO (Except ε β)} {fs : FS} :
    ∀ {xs : List α} {ys : List β}, (mapExcept f xs : ModelIO _) fs (.ok (.ok ys)) →
      ∀ x ∈ xs, ∃ y, f x fs (.ok (.ok y))
  | [], _, _, x, hx => by simp at hx
  | a :: xs, ys, h, x, hx => by
    simp only [mapExcept, ModelIO.bind_ok] at h
    obtain ⟨u, hu, h⟩ := h
    rcases u with e | b
    · simp at h
    · simp only [ModelIO.bind_ok] at h
      obtain ⟨c, hc, h⟩ := h
      rcases c with e | bs
      · simp at h
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b, hu⟩
        · exact mapExcept_each hc x hx

/-- **The two phases of an `--olean` run accept the records with their values in place.** -/
theorem checkOleansG_accept {mode : CheckMode} {pace : Pace} {total t0 tParse jobs : Nat}
    {ds : Array Declaration}
    (hgood : ∀ md ∈ values, ∃ f r a, (readFiles sp md.name .private : ModelIO _) fs (.ok (.ok f)) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r)
    (h : (checkOleansG mode pace total t0 tParse jobs sp values ds : ModelIO _) fs (.ok (.ok ()))) :
    ∃ env, checkDecls mode natOpPinSets (ds.map (fillDecl (fillOf sp fs values))) = .ok env := by
  simp only [checkOleansG, ModelIO.bind_ok, ModelIO.liftIO_iff, ModelIO.tryCatch_ok] at h
  obtain ⟨run, -, res, hres, _, -, h⟩ := h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  subst h
  rcases hres with hres | ⟨e, -, hres⟩
  rotate_left
  · obtain ⟨_, -, hres⟩ := hres
    exact ((ModelIO.throw_ok e _ _).1 hres).elim
  obtain ⟨inst, -, hres⟩ := hres
  rcases inst with e | i
  · simp at hres
  simp only [ModelIO.bind_ok, ModelIO.liftIO_iff] at hres
  obtain ⟨⟨pl, tStart⟩, -, ⟨ss, res⟩, hmap, _, -, hres⟩ := hres
  simp only [ModelIO.pure_iff, Except.ok.injEq] at hres
  rcases res with e | us
  · simp at hres
  -- the worker map's elements
  obtain ⟨-, hm⟩ := (hmap : workerMap _ _ _ fs (.ok (ss, .ok us)))
  have hfacts : ∀ t, t < i.jobs.order.size → JobFact mode i.jobs (fillOf sp fs values) t := by
    intro t ht
    obtain ⟨u, s, hreach, s', hs⟩ := mapExcept_each hm t (List.mem_range.mpr ht)
    exact (oleanStep_spec hgood (oleanWorker_reach hgood hreach) hs).2 rfl
  -- every record and every block is a job
  have hord : i.jobs.order = jobOrder i.jobs.pend i.jobs.D := i.horder
  have hP : ∀ k (hk : k < i.jobs.pend.size), ∃ s,
      checkPending mode i.jobs.fe (fillPend (fillOf sp fs values) i.jobs.pend[k]) {} = .ok ((), s) := by
    intro k hk
    obtain ⟨t, ht, ho⟩ := jobOrder_pend hk
    rw [← hord] at ht ho
    have := hfacts t ht
    unfold JobFact at this
    rw [ho] at this
    exact this hk
  have hD : ∀ b ∈ i.jobs.D.toList, b.Ok mode natOpPinSets := by
    intro b hb
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hb)
    obtain ⟨t, ht, ho⟩ := jobOrder_block (pend := i.jobs.pend) hk
    rw [← hord] at ht ho
    have := hfacts t ht
    unfold JobFact at this
    rw [ho] at this
    exact this hk
  -- the install's run, at the values
  have hrun := InstallRun.fill (fillOf sp fs values) (i.run.run hD)
  let F := fillOf sp fs values
  let e : InstalledEnv mode natOpPinSets (ds.map (fillDecl F)).toList :=
    ⟨i.run.p.2.1, i.run.p.2.2.map (fillPend F), ⟨i.run.p.1, by
      rw [Array.toList_map]
      simpa using hrun⟩⟩
  let fc : FullyChecked mode natOpPinSets (ds.map (fillDecl F)).toList :=
    ⟨e, groupChecked_of_pendOk mode natOpPinSets (e := e) fun k hk => by
      have hk' : k < i.jobs.pend.size := by simpa [e, Installed.jobs] using hk
      obtain ⟨s, hs⟩ := hP k hk'
      refine ⟨s, ?_⟩
      simpa [e, Installed.jobs] using hs⟩
  exact ⟨fc.env, fullyChecked_checkDecls mode fc⟩

/-- **An accepted `--olean` run, in the model**: every outcome of the driver's run on the import
closure of `roots` over a snapshot `fs` that is an exit 0 means the built-in prelude parses, the
reader has an outcome on that snapshot (at one job: the parallel map's model is the sequential
map), and `checkDecls` accepts its records prepared with the prelude, with the theorems' values
in place (`fillOf`), whatever the `liftIO` actions answered. -/
theorem checkMainG_oleans_accept {roots : Array Name}
    {cs : Option (Array Name)} {mode : CheckMode} {pace : Pace} {jobs : Nat}
    (h : (checkMainG (.oleans sp roots cs) mode pace jobs : ModelIO _) fs (.ok 0)) :
    ∃ pre rd env, Frontend.builtinPreludeE = .ok pre ∧
      (readOleans sp roots cs : ModelIO _) fs (.ok (.ok rd)) ∧
      checkDecls mode natOpPinSets
        ((Frontend.prepareD pre rd.decls (usedOf (some (sp, rd)))).decls.map
          (fillDecl (fillOf sp fs rd.values))) = .ok env := by
  suffices H : ModelIO.AllOk (checkMainG (.oleans sp roots cs) mode pace jobs) fs
      (fun c => c = 0 → ∃ pre rd env, Frontend.builtinPreludeE = .ok pre ∧
        (readOleans sp roots cs : ModelIO _) fs (.ok (.ok rd)) ∧
        checkDecls mode natOpPinSets
          ((Frontend.prepareD pre rd.decls (usedOf (some (sp, rd)))).decls.map
            (fillDecl (fillOf sp fs rd.values))) = .ok env) from
    H 0 h rfl
  cases hp : Frontend.builtinPreludeE with
  | error x =>
    rcases x with ⟨_ | _ | _, _⟩ <;>
      simp [checkMainG, hp, clockMs, diagLine]
  | ok pre =>
    simp only [checkMainG, hp, readInputG, clockMs, diagLine, ModelIO.allOk_bind,
      ModelIO.liftIO_iff, forall_const]
    intro _ pre' hpre x hx
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hpre
    cases hpre
    simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    rcases x with ⟨_ | _ | _, _⟩ | rd
    rotate_right
    · have hx' : (readOleans sp roots cs : ModelIO _) fs (.ok (.ok rd)) := hx
      have hgood := readOleans_good hx'
      simp only [Except.map]
      refine ModelIO.allOk_ite (fun _ => ?_) (fun _ => ?_) <;>
        simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_const] <;>
        intro _ <;>
        refine ModelIO.allOk_ite (fun _ => ?_) (fun _ => ?_) <;>
        simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_const] <;>
        intro v hv c hc h0
      all_goals
        obtain rfl := verdictG_ok hc h0
        obtain ⟨env, henv⟩ := checkOleansG_accept hgood hv
        exact ⟨pre, rd, env, rfl, hx', henv⟩
    all_goals simp [Except.map]

end ConLeche.Driver
