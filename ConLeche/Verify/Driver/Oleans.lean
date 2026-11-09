module

public import ConLeche.Driver.CheckMain
public import ConLeche.Verify.Frontend.Olean.Files
public import ConLeche.Verify.Cached.Fill

/-!
# An `--olean` run, in the model (task #481)

An `--olean` run reads a theorem's value in its check, through the class.  On a snapshot,
every reference therefore stands for one value, the specification's (`ValueAt`, `fillOf`),
and what an exit 0 means is about the records with those values in place:

* `readValue_spec`: a value read is `ValueAt` of its reference, from any state a worker can
  reach (`CacheOK`), over any frontier that holds only the specification's values;
* `oleanStep_spec`: a job that passes has passed on the record holding the value
  (`JobFact`), which is the check phase's whole contribution;
* `checkOleansG_accept`: all the jobs passing is an accept of `checkDecls` over the records
  with their values in place, since the index does not read a theorem's value
  (`buildIndex_fill`);
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
    ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
    f.viewRegion .private = some (r, a)

theorem cacheOK_empty {sp : SearchPath} {fs : FS} {values : Array ModRef} :
    CacheOK sp fs values {} := fun r h => by simp at h

variable {sp : SearchPath} {fs : FS} {values : Array ModRef}

/-- The region of a module, from a kept one or the files. -/
theorem regionFor_spec {md : ModRef} {idx : Nat} {c : ValueCache}
    {o : ValueCache × Except CheckError Region} (hmd : values[idx]? = some md)
    (hc : CacheOK sp fs values c)
    {hs hs' : HS} (h : (regionFor sp md.name idx c : ModelIO _) fs hs (.ok o) hs') :
    CacheOK sp fs values o.1 ∧ ∀ r, o.2 = .ok r → ∃ f a,
      ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) := by
  have hread : (regionFor.readRegion sp md.name idx : ModelIO _) fs hs (.ok o) hs' →
      CacheOK sp fs values o.1 ∧ ∀ r, o.2 = .ok r → ∃ f a,
        ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
        f.viewRegion .private = some (r, a) := by
    intro h
    simp only [regionFor.readRegion, ModelIO.bind_ok] at h
    obtain ⟨x, _, hx, h⟩ := h
    rcases x with e | f
    · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
      obtain ⟨h, -⟩ := h
      subst h
      exact ⟨cacheOK_empty, fun r hr => by simp at hr⟩
    · cases hv : f.viewRegion .private with
      | none =>
        simp only [hv, ModelIO.pure_iff, Except.ok.injEq] at h
        obtain ⟨h, -⟩ := h
        subst h
        exact ⟨cacheOK_empty, fun r hr => by simp at hr⟩
      | some x =>
        obtain ⟨r, a⟩ := x
        simp only [hv, ModelIO.pure_iff, Except.ok.injEq] at h
        obtain ⟨h, -⟩ := h
        subst h
        refine ⟨fun r' hr' => ?_, fun r' hr' => ?_⟩
        · simp only [Option.some.injEq] at hr'
          subst hr'
          exact ⟨md, f, a, hmd, ⟨_, _, hx⟩, hv⟩
        · simp only [Except.ok.injEq] at hr'
          subst hr'
          exact ⟨f, a, ⟨_, _, hx⟩, hv⟩
  simp only [regionFor] at h
  cases hr : c.region with
  | none =>
    simp only [hr] at h
    exact hread h
  | some r =>
    simp only [hr] at h
    by_cases hidx : (c.idx == idx) = true
    · simp only [hidx, ↓reduceIte, ModelIO.pure_iff, Except.ok.injEq] at h
      obtain ⟨h, -⟩ := h
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
    (hgood : ∀ md ∈ values, ∃ f r a, ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r)
    (hc : CacheOK sp fs values c)
    {hs hs' : HS} (h : (readValue sp values c code : ModelIO _) fs hs (.ok o) hs') :
    CacheOK sp fs values o.1 ∧ ∀ e, o.2 = .ok e → ValueAt sp fs values code e := by
  simp only [readValue] at h
  cases hmd : values[refModule code]? with
  | none =>
    simp only [hmd, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    subst h
    exact ⟨hc, fun e he => by simp at he⟩
  | some md =>
    simp only [hmd, ModelIO.bind_ok] at h
    obtain ⟨x, _, hx, h⟩ := h
    obtain ⟨hc', hr⟩ := regionFor_spec hmd hc hx
    obtain ⟨c', y⟩ := x
    simp only at hc' hr
    rcases y with e | r
    · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
      obtain ⟨h, -⟩ := h
      subst h
      exact ⟨hc', fun e he => by simp at he⟩
    · simp only at h
      obtain ⟨f, a, hf, hreg⟩ := hr r rfl
      cases hv : frontierExpr r md.frontier (refLoc code) with
      | some v =>
        simp only [hv, ModelIO.pure_iff, Except.ok.injEq] at h
        obtain ⟨h, -⟩ := h
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
        obtain ⟨h, -⟩ := h
        subst h
        exact ⟨hc', fun e he => by simp at he⟩

/-! ## A job -/

/-- **What a job that passed establishes**, at the record holding its value. -/
def JobFact (mode : CheckMode) (maxNatSize : Nat) {ds : Array Declaration} (J : Jobs ds) (F : Expr → Expr) (t : Nat) :
    Prop :=
  ∀ ht : t < ds.size, recordJob mode natOpPinSets maxNatSize J.I t (fillDecl F ds[t]) = .ok ()

theorem jobRun_ok {mode : CheckMode} {maxNatSize : Nat} {ds : Array Declaration} {J : Jobs ds} {t : Nat}
    {d : Declaration} (h : jobRun mode maxNatSize J t d = .ok ()) :
    recordJob mode natOpPinSets maxNatSize J.I t d = .ok () := by
  unfold jobRun at h
  split at h
  · assumption
  · cases h

/-- **One job's run.** -/
theorem oleanJobRun_spec {mode : CheckMode} {maxNatSize : Nat} {ds : Array Declaration} {J : Jobs ds}
    {c : ValueCache} {t : Nat} {o : ValueCache × Except (CheckError × Nat) Unit}
    (hgood : ∀ md ∈ values, ∃ f r a, ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r)
    (hc : CacheOK sp fs values c)
    {hs hs' : HS} (h : (oleanJobRun mode maxNatSize J sp values c t : ModelIO _) fs hs (.ok o) hs') :
    CacheOK sp fs values o.1 ∧ (o.2 = .ok () → JobFact mode maxNatSize J (fillOf sp fs values) t) := by
  -- a record whose value, if any, is in place already
  have hplain : ∀ d, ds[t]? = some d → fillDecl (fillOf sp fs values) d = d → ∀ {hs hs' : HS},
      (pure (c, jobRun mode maxNatSize J t d) : ModelIO _) fs hs (.ok o) hs' →
      CacheOK sp fs values o.1 ∧ (o.2 = .ok () → JobFact mode maxNatSize J (fillOf sp fs values) t) := by
    intro d hd hF hs hs' h
    simp only [ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    subst h
    refine ⟨hc, fun hok ht => ?_⟩
    obtain ⟨_, hdt⟩ := Array.getElem?_eq_some_iff.mp hd
    rw [hdt, hF]
    exact jobRun_ok hok
  unfold oleanJobRun at h
  cases hd : ds[t]? with
  | none =>
    simp only [hd, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    subst h
    exact ⟨hc, fun he => by simp at he⟩
  | some d =>
    simp only [hd] at h
    cases d with
    | thmDecl cv v =>
      cases v with
      | bvar code =>
        -- a theorem whose value is still in its file: the value read is the reference's
        simp only [ModelIO.bind_ok] at h
        obtain ⟨x, _, hx, h⟩ := h
        obtain ⟨hc', hv⟩ := readValue_spec hgood hc hx
        obtain ⟨c', y⟩ := x
        simp only at hc' hv
        rcases y with e | v
        · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
          obtain ⟨h, -⟩ := h
          subst h
          exact ⟨hc', fun he => by simp at he⟩
        · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
          obtain ⟨h, -⟩ := h
          subst h
          refine ⟨hc', fun hok ht => ?_⟩
          obtain ⟨_, hdt⟩ := Array.getElem?_eq_some_iff.mp hd
          rw [hdt]
          simp only [fillDecl, fillOf_value (hv v rfl)]
          exact jobRun_ok hok
      | _ => exact hplain _ hd rfl h
    | _ => exact hplain _ hd rfl h

/-- **One job of the pool.** -/
theorem oleanStep_spec {mode : CheckMode} {maxNatSize : Nat} {run : OleanRun} {pl : PoolLive} {ds : Array Declaration}
    {J : Jobs ds} {s : OleanWorker} {t : Nat} {o : OleanWorker × Except (CheckError × Nat) Unit}
    (hgood : ∀ md ∈ values, ∃ f r a, ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r)
    (hc : CacheOK sp fs values s.cache)
    {hs hs' : HS} (h : (oleanStep mode maxNatSize run pl J sp values s t : ModelIO _) fs hs (.ok o) hs') :
    CacheOK sp fs values o.1.cache ∧ (o.2 = .ok () → JobFact mode maxNatSize J (fillOf sp fs values) t) := by
  simp only [oleanStep, ModelIO.bind_ok] at h
  obtain ⟨_, _, -, x, _, hx, _, _, -, h⟩ := h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨h, -⟩ := h
  subst h
  exact oleanJobRun_spec hgood hc hx

/-- **Every state a worker can reach keeps its module's region.** -/
theorem oleanWorker_reach {mode : CheckMode} {maxNatSize : Nat} {run : OleanRun} {pl : PoolLive} {ds : Array Declaration}
    {J : Jobs ds}
    (hgood : ∀ md ∈ values, ∃ f r a, ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r)
    {s : OleanWorker}
    (h : WorkerReach (fun w => ({ w } : OleanWorker)) (oleanStep mode maxNatSize run pl J sp values) fs s) :
    CacheOK sp fs values s.cache := by
  induction h with
  | init w => exact cacheOK_empty
  | step _ hs ih => exact (oleanStep_spec hgood ih hs).1

/-! ## The check phase -/

/-- Each element of a successful sequential map succeeded. -/
theorem mapExcept_each {α β ε : Type} {f : α → ModelIO (Except ε β)} {fs : FS} :
    ∀ {xs : List α} {ys : List β} {hs hs' : HS}, (mapExcept f xs : ModelIO _) fs hs (.ok (.ok ys)) hs' →
      ∀ x ∈ xs, ∃ y hs hs', f x fs hs (.ok (.ok y)) hs'
  | [], _, _, _, _, x, hx => by simp at hx
  | a :: xs, ys, _, _, h, x, hx => by
    simp only [mapExcept, ModelIO.bind_ok] at h
    obtain ⟨u, _, hu, h⟩ := h
    rcases u with e | b
    · simp at h
    · simp only [ModelIO.bind_ok] at h
      obtain ⟨c, _, hc, h⟩ := h
      rcases c with e | bs
      · simp at h
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b, _, _, hu⟩
        · exact mapExcept_each hc x hx

/-- **The check phase of an `--olean` run accepts the records with their values in place.** -/
theorem checkOleansG_accept {mode : CheckMode} {maxNatSize : Nat} {pace : Pace} {t0 tIndex tParse jobs : Nat}
    {ds : Array Declaration} {J : Jobs ds}
    (hgood : ∀ md ∈ values, ∃ f r a, ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r)
    {hs hs' : HS}
    (h : (checkOleansG mode maxNatSize pace t0 tIndex tParse jobs sp values J : ModelIO _) fs hs (.ok (.ok ())) hs') :
    ∃ env, checkDecls mode natOpPinSets maxNatSize (ds.map (fillDecl (fillOf sp fs values))) = .ok env := by
  simp only [checkOleansG, ModelIO.bind_ok, ModelIO.liftIO_iff, exists_eq_left] at h
  obtain ⟨run, ⟨pl, tStart⟩, ⟨ss, res⟩, _, hmap, _, h⟩ := h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  rcases res with e | us
  · simp at h
  -- the worker map's elements
  obtain ⟨-, hm⟩ := (hmap : workerMap _ _ _ fs _ (.ok (ss, .ok us)) _)
  have hfacts : ∀ t, t < ds.size → JobFact mode maxNatSize J (fillOf sp fs values) t := by
    intro t ht
    obtain ⟨u, _, _, s, hreach, s', hs⟩ := mapExcept_each hm t (List.mem_range.mpr ht)
    exact (oleanStep_spec hgood (oleanWorker_reach hgood hreach) hs).2 rfl
  -- every record's job passed, at the records with their values in place
  refine ⟨_, checkDecls_of_jobs (mode := mode) (pins := natOpPinSets) fun k hk => ?_⟩
  have hk' : k < ds.size := by simpa using hk
  rw [buildIndex_fill, Array.getElem_map, ← J.hI]
  exact hfacts k hk' hk'

/-- **An accepted `--olean` run, in the model**: every outcome of the driver's run on the import
closure of `roots` over a snapshot `fs` that is an exit 0 means the built-in prelude parses, the
reader has an outcome on that snapshot (at one job: the parallel map's model is the sequential
map), and `checkDecls` accepts its records prepared with the prelude, with the theorems' values
in place (`fillOf`), whatever the `liftIO` actions answered. -/
theorem checkMainG_oleans_accept {roots : Array Name}
    {cs : Option (Array Name)} {mode : CheckMode} {maxNatSize : Nat} {pace : Pace} {jobs : Nat}
    {hs hs' : HS} (h : (checkMainG (.oleans sp roots cs) mode maxNatSize pace jobs : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre rd env, Frontend.builtinPreludeE = .ok pre ∧
      ModelIO.CanGive (readOleans sp roots cs) fs (.ok rd) ∧
      checkDecls mode natOpPinSets maxNatSize
        ((Frontend.prepareD pre rd.decls (usedOf (some (sp, rd)))).decls.map
          (fillDecl (fillOf sp fs rd.values))) = .ok env := by
  suffices H : ModelIO.AllOk (checkMainG (.oleans sp roots cs) mode maxNatSize pace jobs) fs hs
      (fun c => c = 0 → ∃ pre rd env, Frontend.builtinPreludeE = .ok pre ∧
        ModelIO.CanGive (readOleans sp roots cs) fs (.ok rd) ∧
        checkDecls mode natOpPinSets maxNatSize
          ((Frontend.prepareD pre rd.decls (usedOf (some (sp, rd)))).decls.map
            (fillDecl (fillOf sp fs rd.values))) = .ok env) from
    H 0 hs' h rfl
  cases hp : Frontend.builtinPreludeE with
  | error x =>
    rcases x with ⟨_ | _ | _, _⟩ <;>
      simp [checkMainG, hp, clockMs, diagLine]
  | ok pre =>
    simp only [checkMainG, hp, readInputG, clockMs, diagLine, ModelIO.allOk_bind,
      ModelIO.liftIO_iff, forall_eq]
    intro _ pre' _ hpre _ x _ hx
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hpre
    obtain ⟨rfl, rfl⟩ := hpre
    simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at hx
    obtain ⟨x, _, hx, rfl, rfl⟩ := hx
    rcases x with ⟨_ | _ | _, _⟩ | rd
    rotate_right
    · have hx' : (readOleans sp roots cs : ModelIO _) fs _ (.ok (.ok rd)) _ := hx
      have hgood := readOleans_good hx'
      simp only [Except.map]
      refine ModelIO.allOk_ite (fun _ => ?_) (fun _ => ?_) <;>
        simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq, forall_const] <;>
        intros <;>
        refine ModelIO.allOk_ite (fun _ => ?_) (fun _ => ?_) <;>
        simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq, forall_const] <;>
        intro v _ hv c _ hc h0
      all_goals
        obtain rfl := verdictG_ok hc h0
        obtain ⟨env, henv⟩ := checkOleansG_accept hgood hv
        exact ⟨_, rd, env, rfl, ⟨_, _, hx'⟩, henv⟩
    all_goals simp [Except.map]

end ConLeche.Driver
