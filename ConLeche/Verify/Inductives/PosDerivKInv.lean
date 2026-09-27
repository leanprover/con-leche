module

public import ConLeche.Verify.Inductives.PosDerivK
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Inductives.DirectInv

public section

/-!
# The key-named positivity run, inverted ONCE into the derivation

`posK_deriv`: a successful run of `posK` / `synK` / `useK` / `nodeK`
(`Kernel/Inductives/PositivityK.lean`) — at any fuel, under ANY `ops` —
keeps the cache invariant `DerivCacheK` and yields the derivation `PosDK`
of its input; `nestBlockCtorsGoK_deriv` lifts it to the whole block: every
member constructor derived at the root layout (`MemberCtorDK`) and every
entry of the run's FINAL node cache carrying its node's derivation (the
table the recursor check will read, PROOFPLAN §4).

The cache invariant (`DerivCacheK`): the container lookups are the
environment's (`nestContainer`), and every cached node entry has a `node`
derivation at the entry's recorded met set, the entry's key a member of
that node's group at the node's levels and parameters.  A cache hit copies
that derivation into the `use` rule; a first visit inserts it
(`recordK`).

The met sets.  The run accumulates the current node's met set in its state
(`NestStK.met`); it only ever GROWS within a node (`MetGrow`), a node's walk
saves and restores it.  Every claim below is therefore stated at EVERY
superset of the final met set (`st'.met ⊆ met`), which composes along the
walk without a separate monotonicity lemma; a node is derived at exactly
its recorded met set.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

open Expr

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {hk : UseHookK}

/-! ## Small monad facts -/

/-- A successful `tryCatchThe`: the body succeeded, or it failed and the
handler succeeded. -/
theorem tryCatchK_ok {α : Type} {x : CheckM α} {h : CheckError → CheckM α} {a : α}
    (hr : tryCatchThe CheckError x h = .ok a) : x = .ok a ∨ ∃ e, x = .error e ∧ h e = .ok a := by
  cases x with
  | ok b =>
    left
    simpa [tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] using hr
  | error e =>
    right
    exact ⟨e, rfl, by simpa [tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] using hr⟩

theorem throwK_ne_ok {α : Type} {e : CheckError} {a : α} :
    (throw e : CheckM α) ≠ .ok a := by
  simp [throw, throwThe, MonadExceptOf.throw]

/-- A hook check succeeded (NESTKN-K3): its body did — the gate's trial is opaque, the
body's own run follows it. -/
theorem hookK_ok {α : Type} {what : String} {x : CheckM α} {gate : Bool} {a : α}
    (h : hookK ops what x gate = .ok a) : x = .ok a := by
  unfold hookK at h
  cases gate with
  | false => exact h
  | true =>
    simp only [if_true, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · rename_i b _
      cases b with
      | true => exact h
      | false => simp [throw, throwThe, MonadExceptOf.throw, Except.bind] at h

/-- **A layout's typing step succeeded**: the term inferred. -/
theorem typeAtK_ok {d : Nat} {e : Expr} {sort : Bool}
    (h : typeAtK (m := CheckM) ops env d e sort = .ok ()) :
    ∃ ty, ops.inferType env d e = .ok ty := by
  unfold typeAtK at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i ty hty
    exact ⟨ty, hty⟩

/-! ## The run's invariant -/

/-- The container lookups are the environment's. -/
@[expose] def CtorsOfOk (ctx : NestCtx) (st : NestState) : Prop :=
  ∀ c r, st.ctorsOf.lookup c = some r → r = nestContainer ctx c

/-- **The run's state invariant** (see the module docstring). -/
@[expose] def DerivCacheK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (hk : UseHookK) (st : NestStK) :
    Prop :=
  CtorsOfOk ctx st.base ∧
  ∀ nd ∈ st.cache.toList, ∃ kn lo, PosDKH ops env ctx hk (.node kn lo nd.met) ∧
    nd.key.cname ∈ lo.ginfo.map (·.1) ∧ nd.key.lvls = kn.lvls ∧ nd.key.ds = kn.ds ∧
    nd.dsF = lo.L.dsF ∧ nd.nF = lo.L.nF ∧ nd.merged = lo.merged ∧
    nd.famKeys = lo.L.fams.map (·.1) ∧ nd.famPs = lo.famPs ∧
    nd.famTys = lo.L.famTys ∧ nd.famNIs = lo.L.fams.map (·.2) ∧
    (ctx.names.contains kn.cname = false ∧ kn.cname ≠ quotName)

theorem derivCacheK_empty : DerivCacheK ops env ctx hk {} :=
  ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩

/-- The run's met set only grows. -/
@[expose] def MetGrow (st st' : NestStK) : Prop := st.met ⊆ st'.met

theorem CtorsOfOk.lookup {st : NestState} (h : CtorsOfOk ctx st) (c : Name) :
    (nestContainerC ctx st c).1 = nestContainer ctx c := by
  unfold nestContainerC
  split
  · rename_i r hr; exact h c r hr
  · rfl

theorem CtorsOfOk.insert {st : NestState} (h : CtorsOfOk ctx st) (c : Name) :
    CtorsOfOk ctx (nestContainerC ctx st c).2 := by
  unfold nestContainerC
  split
  · exact h
  · intro c' r hl
    simp only [List.lookup] at hl
    split at hl
    · rename_i heq
      simp only [Option.some.injEq] at hl
      rw [← hl]
      congr 1
      exact (beq_iff_eq.mp heq).symm
    · exact h c' r hl

/-- The invariant survives a new `base` with the same lookups. -/
theorem DerivCacheK.withBase {st : NestStK} (h : DerivCacheK ops env ctx hk st) {b : NestState}
    (hb : CtorsOfOk ctx b) : DerivCacheK ops env ctx hk { st with base := b } :=
  ⟨hb, h.2⟩

theorem DerivCacheK.withMet {st : NestStK} (h : DerivCacheK ops env ctx hk st) (m : List Nat) :
    DerivCacheK ops env ctx hk { st with met := m } :=
  ⟨h.1, h.2⟩

/-- The lookup function a node's walk builds is `nestContainer`. -/
theorem CtorsOfOk.look_eq {st : NestState} (h : CtorsOfOk ctx st) :
    (fun c => match st.ctorsOf.lookup c with
      | some r => r
      | none => nestContainer ctx c) = nestContainer ctx := by
  funext c
  split
  · rename_i r hr; exact h c r hr
  · rfl

/-- The group's constructor listing keeps the lookups the environment's. -/
theorem nestGroupCtors_ctorsOk {nPc : Nat} :
    ∀ (cs : List Name) (st : NestState) (ctors : List (ConstantVal × Nat)) (st' : NestState),
      nestGroupCtors (m := CheckM) ctx nPc cs st = .ok (ctors, st') → CtorsOfOk ctx st →
      CtorsOfOk ctx st'
  | [], st, ctors, st', h, hst => by
    simp only [nestGroupCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hst
  | c :: cs, st, ctors, st', h, hst => by
    simp only [nestGroupCtors, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i q hq
    split at h
    · split at h
      · simp at h
      rename_i r hr
      obtain ⟨rest, st₁⟩ := r
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact nestGroupCtors_ctorsOk cs _ rest st₁ hr (hst.insert c)
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The match (K-d) -/

/-- **The parameter check, inverted**: every parameter `ParamOkK`. -/
theorem checkParamsK_ok {L : LayoutK} {nd : NodeK} {θ : Nat → Option Expr} :
    ∀ (xs : List (Expr × Expr)), checkParamsK (m := CheckM) ops env ctx L nd θ xs = .ok () →
      ∀ x ∈ xs, ParamOkK ops env ctx L nd.merged θ x.1 x.2
  | [], _, x, hx => nomatch hx
  | (p, t) :: rest, h, x, hx => by
    simp only [checkParamsK, bind, Except.bind] at h
    split at h
    · rename_i heq
      rcases List.mem_cons.mp hx with rfl | hx
      · left; exact eq_of_beq heq
      · exact checkParamsK_ok rest h x hx
    split at h
    · rename_i hmerged
      split at h
      · simp at h
      rename_i u₂ hu₂
      split at h
      · simp at h
      rename_i u₃ hu₃
      split at h
      · simp at h
      rename_i bd hbd
      split at h
      · rename_i hbd'
        rcases List.mem_cons.mp hx with rfl | hx
        · right
          refine ⟨hmerged, typeAtK_ok hu₂, typeAtK_ok hu₃, ?_⟩
          rw [hbd, hbd']
        · exact checkParamsK_ok rest h x hx
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The match, inverted**: the lengths agree, the pure match's bindings with
every inner family bound from its outer one, every family bound, every
parameter checked at them. -/
theorem matchK_ok {L : LayoutK} {nd : NodeK} {ps : List Expr} {bs : List (Nat × Expr)}
    (h : matchK (m := CheckM) ops env ctx L nd ps = .ok bs) :
    nd.dsF.length = ps.length ∧ ∃ rs, (nd.dsF.zip ps).mapM (matchStepK ctx L nd.nF) = .ok rs ∧
      bindInnerK ctx L nd (List.range nd.nF).reverse rs.flatten = .ok bs ∧
      (∀ j, j < nd.nF → bs.any (·.1 == j) = true) ∧
      (∀ x ∈ nd.dsF.zip ps, ParamOkK ops env ctx L nd.merged (thetaK ctx nd.nF bs) x.1 x.2) ∧
      bindsOkK ops env ctx L nd (thetaK ctx nd.nF bs) (List.range nd.nF) = .ok () := by
  unfold matchK at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h throwK_ne_ok
  rename_i hlen
  split at h
  · rename_i rs hrs
    simp only [pure, Except.pure] at h
    split at h
    · rename_i bs' hbs'
      try simp only [pure, Except.pure] at h
      split at h
      · rename_i hall
        split at h
        · simp at h
        rename_i u hu
        split at h
        · simp at h
        rename_i u' hu'
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨by simpa using hlen, rs, hrs, hbs', fun j hj => ?_, checkParamsK_ok _ hu, hu'⟩
        simp only [List.all_eq_true, List.mem_range] at hall
        exact hall j hj
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `bindInnerK` reads only the node's flexible families' count, keys and
inner-abstracted parameters. -/
theorem bindInnerK_congr {L : LayoutK} {nd nd' : NodeK} (hP : nd.famPs = nd'.famPs)
    (hF : nd.nF = nd'.nF) (hK : nd.famKeys = nd'.famKeys) :
    ∀ (js : List Nat) (bs : List (Nat × Expr)),
      bindInnerK ctx L nd js bs = bindInnerK ctx L nd' js bs := by
  intro js
  induction js with
  | nil => intro bs; simp [bindInnerK]
  | cons j js ih =>
    intro bs
    simp only [bindInnerK, hP, hF, hK, ih]

/-! ## The claims about the walk functions -/

/-- **The inversion's claim about a field walk** (`posK`, or its call one
fuel lower). -/
@[expose] def RunDerivK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (hk : UseHookK)
    (rec : LayoutK → Nat → Nat → Expr → NestStK → CheckM (NestFieldKind × Expr × NestStK)) :
    Prop :=
  ∀ (L : LayoutK) (dep kb : Nat) (e : Expr) (st : NestStK) (k : NestFieldKind) (nf : Expr)
    (st' : NestStK), rec L dep kb e st = .ok (k, nf, st') → DerivCacheK ops env ctx hk st →
    DerivCacheK ops env ctx hk st' ∧ MetGrow st st' ∧
      ∀ met, st'.met ⊆ met → PosDKH ops env ctx hk (.field L met dep kb e k.erase nf)

/-- **The inversion's claim about a syntactic pass** (`synK`). -/
@[expose] def SynDerivK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (hk : UseHookK)
    (syn : LayoutK → Option NestKey → Expr → NestStK → CheckM NestStK) : Prop :=
  ∀ (L : LayoutK) (skip : Option NestKey) (e : Expr) (st st' : NestStK),
    syn L skip e st = .ok st' → DerivCacheK ops env ctx hk st →
    DerivCacheK ops env ctx hk st' ∧ MetGrow st st' ∧
      ∀ met, st'.met ⊆ met → PosDKH ops env ctx hk (.syn L met e)

/-- **The inversion's claim about a use** (`useK`). -/
@[expose] def UseDerivK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (hk : UseHookK)
    (use : LayoutK → NestKey → List Expr → NestStK → CheckM (Nat × NestStK)) : Prop :=
  ∀ (L : LayoutK) (kc : NestKey) (ps : List Expr) (st : NestStK) (qi : Nat) (st' : NestStK),
    use L kc ps st = .ok (qi, st') → DerivCacheK ops env ctx hk st →
    DerivCacheK ops env ctx hk st' ∧ MetGrow st st' ∧
      (kc.ds = ps.map (rbK ctx L) → ∀ met, st'.met ⊆ met → PosDKH ops env ctx hk (.use L met kc ps))

/-- **The inversion's claim about a node walk** (`nodeK`): the invariant
kept (so the node's derivation is cached), the met set untouched. -/
@[expose] def NodeDerivK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (hk : UseHookK)
    (node : NestKey → NestStK → CheckM NestStK) : Prop :=
  ∀ (kc : NestKey) (st st' : NestStK),
    (ctx.names.contains kc.cname = false ∧ kc.cname ≠ quotName) →
    node kc st = .ok st' → DerivCacheK ops env ctx hk st →
    DerivCacheK ops env ctx hk st' ∧ MetGrow st st'

theorem MetGrow.refl (st : NestStK) : MetGrow st st := List.Subset.refl _

theorem MetGrow.trans {a b c : NestStK} (h₁ : MetGrow a b) (h₂ : MetGrow b c) : MetGrow a c :=
  List.Subset.trans h₁ h₂

/-! ## Met-propagation -/

/-- **Met-propagation, derived**: every binding of a family the node met
has its `bind` judgment at the user. -/
theorem metK_deriv {L : LayoutK}
    {use : LayoutK → NestKey → List Expr → NestStK → CheckM (Nat × NestStK)}
    (huse : UseDerivK ops env ctx hk use) {metc : List Nat} :
    ∀ (bs : List (Nat × Expr)) (st st' : NestStK),
      metK (m := CheckM) ctx L use metc bs st = .ok st' → DerivCacheK ops env ctx hk st →
      DerivCacheK ops env ctx hk st' ∧ MetGrow st st' ∧
        ∀ met, st'.met ⊆ met → ∀ b ∈ bs, b.1 ∈ metc → PosDKH ops env ctx hk (.bind L met b.2)
  | [], st, st', h, hI => by
    simp only [metK, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, MetGrow.refl _, fun _ _ b hb => nomatch hb⟩
  | (j, b) :: bs, st, st', h, hI => by
    simp only [metK, bind, Except.bind] at h
    split at h
    · rename_i hj
      obtain ⟨hI', hg, hd⟩ := metK_deriv huse bs st st' h hI
      refine ⟨hI', hg, fun met hm x hx hxm => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hj
        exact absurd hxm hj
      · exact hd met hm x hx hxm
    have finish : ∀ st₁ : NestStK, DerivCacheK ops env ctx hk st₁ → MetGrow st st₁ →
        (∀ met, st₁.met ⊆ met → PosDKH ops env ctx hk (.bind L met b)) →
        metK (m := CheckM) ctx L use metc bs st₁ = .ok st' →
        DerivCacheK ops env ctx hk st' ∧ MetGrow st st' ∧
          ∀ met, st'.met ⊆ met → ∀ x ∈ (j, b) :: bs, x.1 ∈ metc →
            PosDKH ops env ctx hk (.bind L met x.2) := by
      intro st₁ hI₁ hg₁ hb₁ h
      obtain ⟨hI', hg, hd⟩ := metK_deriv huse bs st₁ st' h hI₁
      refine ⟨hI', hg₁.trans hg, fun met hm x hx hxm => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb₁ met (List.Subset.trans hg hm)
      · exact hd met hm x hx hxm
    split at h
    · rename_i i ty
      split at h
      · rename_i hr
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
        simp only [pure, Except.pure] at h
        split at h
        · rename_i hc
          refine finish st hI (MetGrow.refl _) (fun met hm => .bindFam hr.1 hr.2 (hm ?_)) h
          simpa using hc
        · refine finish _ (hI.withMet _) (fun x hx => List.mem_append_left _ hx)
            (fun met hm => .bindFam hr.1 hr.2 (hm ?_)) h
          exact List.mem_append_right _ (List.mem_singleton_self _)
      · split at h
        · rename_i _ hr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
          simp only [pure, Except.pure] at h
          exact finish st hI (MetGrow.refl _) (fun met _ => .bindOwn rfl hr.1 hr.2) h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · rename_i i ty hfn
        split at h
        · rename_i hr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
          simp only [pure, Except.pure] at h
          exact finish st hI (MetGrow.refl _) (fun met _ => .bindOwn hfn hr.1 hr.2) h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i n us hfn
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · simp at h
          rename_i r hr
          obtain ⟨qi, st₁⟩ := r
          simp only [pure, Except.pure] at h
          obtain ⟨hI₁, hg, hu⟩ := huse _ _ _ _ _ _ hr hI
          exact finish st₁ hI₁ hg (fun met hm => .bindKey hfn (hu rfl met hm)) h
      · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The container case and the syntactic pass -/

/-- **The container case, derived**: today's checks, and the canonical key
(read back) used. -/
theorem contK_deriv
    {use : LayoutK → NestKey → List Expr → NestStK → CheckM (Nat × NestStK)}
    (huse : UseDerivK ops env ctx hk use) {L : LayoutK} {kb : Nat} {n : Name} {us : List Level}
    {args : List Expr} {st : NestStK} {k : NestFieldKind} {st' : NestStK}
    (h : contK (m := CheckM) ctx use L kb n us args st = .ok (k, st'))
    (hI : DerivCacheK ops env ctx hk st) :
    DerivCacheK ops env ctx hk st' ∧ MetGrow st st' ∧ k.erase = .nested (kb != 0) ∧
      ∃ nPc Lc nI cty, nestContainer ctx n = some (nPc, Lc) ∧ n ≠ quotName ∧
        args.length = nPc + nI ∧
        (∀ x ∈ args.drop nPc, x.nestOcc ctx.names ctx.nP L.hi = false) ∧
        (∀ x ∈ args.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ L.hi) ∧
        nestInstType (m := CheckM) ctx L.hi ⟨n, us, args.take nPc⟩ = .ok (nI, cty) ∧
        ∀ met, st'.met ⊆ met →
          PosDKH ops env ctx hk (.use L met ⟨n, us, (args.take nPc).map (rbK ctx L)⟩ (args.take nPc)) := by
  unfold contK at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
  split at h
  · simp at h
  rename_i q hq
  have hq' := unwrapOr_ok hq
  rw [hI.1.lookup n] at hq'
  obtain ⟨nPc, Lc⟩ := q
  split at h
  · simp at h
  rename_i hlen
  split at h
  · simp at h
  rename_i hquot
  split at h
  rotate_left
  · simp at h
  rename_i hds
  split at h
  · simp at h
  rename_i ni hni
  obtain ⟨nI, cty⟩ := ni
  split at h
  rotate_left
  · simp at h
  rename_i hlen'
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨qi, st₁⟩ := r
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hI₁, hg, hu⟩ := huse _ _ _ _ _ _ hr (hI.withBase (hI.1.insert n))
  refine ⟨hI₁, hg, rfl, nPc, Lc, nI, cty, hq', by simpa using hquot, by simpa using hlen',
    ?_, ?_, hni, hu rfl⟩
  · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or,
      Bool.not_eq_false] at hlen
    simpa using hlen.2
  · intro x hx
    have := List.all_eq_true.mp hds x hx
    simpa using this

/-- **A syntactic pass's keys, derived**: each used key a `synUse`, each
skipped one nothing. -/
theorem synKeysK_deriv
    {use : LayoutK → NestKey → List Expr → NestStK → CheckM (Nat × NestStK)}
    (huse : UseDerivK ops env ctx hk use) {L : LayoutK} {skip : Option NestKey} {e : Expr} :
    ∀ (keys : List NestKey) (st st' : NestStK), (∀ k ∈ keys, SynSrc ctx L.hi e k) →
      synKeysK (m := CheckM) ctx L use skip keys st = .ok st' → DerivCacheK ops env ctx hk st →
      DerivCacheK ops env ctx hk st' ∧ MetGrow st st' ∧
        ∀ met, st'.met ⊆ met → PosDKH ops env ctx hk (.syn L met e)
  | [], st, st', _, h, hI => by
    simp only [synKeysK, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, MetGrow.refl _, fun _ _ => .synNil⟩
  | key :: keys, st, st', hks, h, hI => by
    simp only [synKeysK, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
      Except.pure] at h
    split at h
    rotate_left
    · simp at h
    split at h
    · simp at h
    split at h
    · exact synKeysK_deriv huse keys st st' (fun k hk => hks k (List.mem_cons_of_mem _ hk)) h hI
    split at h
    · simp at h
    rename_i q hq
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨qi, st₁⟩ := r
    obtain ⟨hI₁, hg₁, hu⟩ := huse _ _ _ _ _ _ hr (hI.withBase (hI.1.insert key.cname))
    obtain ⟨hI', hg, hd⟩ :=
      synKeysK_deriv huse keys st₁ st' (fun k hk => hks k (List.mem_cons_of_mem _ hk)) h hI₁
    exact ⟨hI', hg₁.trans hg, fun met hm =>
      .synUse (hks key List.mem_cons_self) (hu rfl met (List.Subset.trans hg hm)) (hd met hm)⟩

/-! ## Telescopes and constructors -/

section Tele

variable {rec : LayoutK → Nat → Nat → Expr → NestStK → CheckM (NestFieldKind × Expr × NestStK)}
  {syn : LayoutK → Option NestKey → Expr → NestStK → CheckM NestStK}

/-- **The telescope walk, derived.** -/
theorem fieldsK_deriv (hrec : RunDerivK ops env ctx hk rec) (hsyn : SynDerivK ops env ctx hk syn)
    {L : LayoutK} {err : CheckError} :
    ∀ (nF j : Nat) (cur : Expr) (st : NestStK) (ks : List NestFieldKind)
      (nds : List (Expr × BinderMeta)) (res : Expr) (st' : NestStK),
      fieldsK (m := CheckM) rec syn L err nF j cur st = .ok (ks, nds, res, st') →
      DerivCacheK ops env ctx hk st →
      DerivCacheK ops env ctx hk st' ∧ MetGrow st st' ∧
        ∀ met, st'.met ⊆ met →
          PosDKH ops env ctx hk (.tele L met nF j cur (ks.map (·.erase)) nds res) := by
  intro nF
  induction nF with
  | zero =>
    intro j cur st ks nds res st' h hI
    simp only [fieldsK, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨hI, MetGrow.refl _, fun _ _ => .teleNil⟩
  | succ nF ih =>
    intro j cur st ks nds res st' h hI
    unfold fieldsK at h
    split at h
    · rename_i a b bm
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      rename_i r₁ hr₁
      obtain ⟨k₁, nd₁, st₁⟩ := r₁
      simp only at h
      obtain ⟨hI₁, hg₁, h₁⟩ := hrec L (L.hi + j) 0 a st k₁ nd₁ st₁ hr₁ hI
      split at h
      · simp at h
      rename_i stS hS
      obtain ⟨hIS, hgS, hS'⟩ := hsyn L _ a st₁ stS hS hI₁
      split at h
      · simp at h
      rename_i r₂ hr₂
      obtain ⟨ks₂, nds₂, res₂, st₂⟩ := r₂
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨hI₂, hg₂, h₂⟩ := ih (j + 1) _ stS ks₂ nds₂ res₂ st₂ hr₂ hIS
      refine ⟨hI₂, hg₁.trans (hgS.trans hg₂), fun met hm => ?_⟩
      exact .teleCons (h₁ met (List.Subset.trans (hgS.trans hg₂) hm))
        (hS' met (List.Subset.trans hg₂ hm)) (h₂ met hm)
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **A node's crests walked, derived.** -/
theorem ctorsK_deriv (hrec : RunDerivK ops env ctx hk rec) (hsyn : SynDerivK ops env ctx hk syn)
    {L : LayoutK} :
    ∀ (cs : List ((ConstantVal × Nat) × Expr)) (st st' : NestStK),
      ctorsK (m := CheckM) ctx rec syn L cs st = .ok st' → DerivCacheK ops env ctx hk st →
      DerivCacheK ops env ctx hk st' ∧ MetGrow st st' ∧
        ∀ met, st'.met ⊆ met → PosDKH ops env ctx hk (.ctors L met cs)
  | [], st, st', h, hI => by
    simp only [ctorsK, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, MetGrow.refl _, fun _ _ => .ctorsNil⟩
  | ((cv, nF), crest) :: cs, st, st', h, hI => by
    simp only [ctorsK, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨ks, nds, cur, st₁⟩ := r
    obtain ⟨hI₁, hg₁, h₁⟩ := fieldsK_deriv hrec hsyn nF 0 crest st ks nds cur st₁ hr hI
    simp only at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hu4
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨hI', hg, hd⟩ := ctorsK_deriv hrec hsyn cs _ st' h hI₁
      refine ⟨hI', hg₁.trans hg, fun met hm => ?_⟩
      refine .ctorsCons (h₁ met (List.Subset.trans hg hm)) ?_ hok.1 hok.2 (hd met hm)
      simp only [erase_getD_bne]
      simpa using hu4
    · simp [throw, throwThe, MonadExceptOf.throw] at h

end Tele

/-! ## A node recorded -/

/-- **Recording a node keeps the invariant**: each group member's cache
entry carries the node's derivation. -/
theorem recordK_deriv {kc : NestKey} {lo : LayoutOutK} {met : List Nat}
    (hd : PosDKH ops env ctx hk (.node kc lo met))
    (hu0 : ctx.names.contains kc.cname = false ∧ kc.cname ≠ quotName) :
    ∀ (gs : List (Name × Nat × Expr)) (st : NestStK), (∀ g ∈ gs, g.1 ∈ lo.ginfo.map (·.1)) →
      DerivCacheK ops env ctx hk st →
      DerivCacheK ops env ctx hk (recordK ctx kc lo met gs st) ∧
        (recordK ctx kc lo met gs st).met = st.met
  | [], st, _, hI => ⟨hI, rfl⟩
  | (g, nI, ty) :: gs, st, hgs, hI => by
    unfold recordK
    dsimp only
    split <;>
    · refine recordK_deriv hd hu0 gs _ (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) ⟨hI.1, ?_⟩
      intro nd hnd
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hnd
      rcases hnd with hnd | rfl
      · exact hI.2 nd hnd
      · exact ⟨kc, lo, hd, hgs _ List.mem_cons_self, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          hu0⟩

/-! ## A use and a node -/

/-- A cached node's entry carries its derivation. -/
theorem DerivCacheK.node? {st : NestStK} (hI : DerivCacheK ops env ctx hk st) {kc : NestKey}
    {nd : NodeK} (h : st.node? kc = some nd) :
    nd.key = kc ∧ ∃ kn lo, PosDKH ops env ctx hk (.node kn lo nd.met) ∧
      kc.cname ∈ lo.ginfo.map (·.1) ∧ kc.lvls = kn.lvls ∧ kc.ds = kn.ds ∧
      nd.dsF = lo.L.dsF ∧ nd.nF = lo.L.nF ∧ nd.merged = lo.merged ∧
      nd.famKeys = lo.L.fams.map (·.1) ∧ nd.famPs = lo.famPs ∧
      nd.famTys = lo.L.famTys ∧ nd.famNIs = lo.L.fams.map (·.2) ∧
      (ctx.names.contains kn.cname = false ∧ kn.cname ≠ quotName) := by
  unfold NestStK.node? at h
  have hkey : nd.key = kc := by simpa using Array.find?_some h
  have hm : nd ∈ st.cache.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some h)
  obtain ⟨kn, lo, hd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hI.2 nd hm
  rw [hkey] at h1 h2 h3
  exact ⟨hkey, kn, lo, hd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- **A hook the run discharges** (PRIMREC / NESTKN-M3B): at every use, from
what the use's run established — the node's key's container (U0, carried by
the cache), the used container's parameter count (U1), the key the spelling
read back (every caller's), the node's layout, the match, its inner bindings
and their check (`bindsOkK`, at a node record carrying the layout's family
types, index counts and the met set) — the hook holds. -/
@[expose] def HookOkK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (hk : UseHookK) :
    Prop :=
  ∀ {L : LayoutK} {kc kn : NestKey} {ps : List Expr} {lo : LayoutOutK} {metc : List Nat}
    {rs : List (List (Nat × Expr))} {bs : List (Nat × Expr)} {nd : NodeK},
    (ctx.names.contains kn.cname = false ∧ kn.cname ≠ quotName) →
    (∃ Lc, nestContainer ctx kc.cname = some (ps.length, Lc)) →
    kc.ds = ps.map (rbK ctx L) →
    nestLayoutK (m := CheckM) ops env ctx (nestContainer ctx) kn = .ok lo →
    kc.cname ∈ lo.ginfo.map (·.1) → kc.lvls = kn.lvls → kc.ds = kn.ds →
    lo.L.dsF.length = ps.length →
    (lo.L.dsF.zip ps).mapM (matchStepK ctx L lo.L.nF) = .ok rs →
    bindInnerK ctx L (nodeOfK lo) (List.range lo.L.nF).reverse rs.flatten = .ok bs →
    (∀ j, j < lo.L.nF → bs.any (·.1 == j) = true) →
    nd.famTys = lo.L.famTys → nd.famNIs = lo.L.fams.map (·.2) → nd.met = metc →
    bindsOkK (m := CheckM) ops env ctx L nd (thetaK ctx lo.L.nF bs) (List.range lo.L.nF) = .ok () →
    hk L kc kn ps lo metc bs

/-- The trivial hook is discharged. -/
theorem hookOkK_triv : HookOkK ops env ctx trivHookK := by
  unfold HookOkK; intros; trivial

/-- **A use's tail, derived**: the node found in the cache, the match and
its check, the met families propagated. -/
theorem useTail_deriv (hH : HookOkK ops env ctx hk)
    {use : LayoutK → NestKey → List Expr → NestStK → CheckM (Nat × NestStK)}
    (huse : UseDerivK ops env ctx hk use) {L : LayoutK} {kc : NestKey} {ps : List Expr}
    {st st₁ st' : NestStK} {nd : NodeK} {bs : List (Nat × Expr)}
    (hinst : ∃ r, nestInstType (m := CheckM) ctx L.hi ⟨kc.cname, kc.lvls, ps⟩ = .ok r)
    (hk52 : ∃ ty, ops.inferType env L.hi (Expr.mkAppN (.const kc.cname kc.lvls) ps) = .ok ty)
    (hu1 : ∃ Lc, nestContainer ctx kc.cname = some (ps.length, Lc))
    (hI₁ : DerivCacheK ops env ctx hk st₁) (hg₁ : MetGrow st st₁)
    (hnd : unwrapOr (st₁.node? kc) (CheckError.internal "NESTKN-K: a node not cached after its walk")
      = (.ok nd : CheckM NodeK))
    (hm : matchK (m := CheckM) ops env ctx L nd ps = .ok bs)
    (hmet : metK (m := CheckM) ctx L use nd.met bs st₁ = .ok st') :
    DerivCacheK ops env ctx hk st' ∧ MetGrow st st' ∧
      (kc.ds = ps.map (rbK ctx L) → ∀ met, st'.met ⊆ met → PosDKH ops env ctx hk (.use L met kc ps)) := by
  obtain ⟨-, kn, lo, hd, hgrp, hlv, hkds, hdsF, hnF, hmg, hfk, hfp, hfT, hfN, hu0⟩ :=
    hI₁.node? (unwrapOr_ok hnd)
  obtain ⟨hlen, rs, hrs, hin, hall, hpar, hbok⟩ := matchK_ok hm
  have hlay : nestLayoutK (m := CheckM) ops env ctx (nestContainer ctx) kn = .ok lo := by
    cases hd with
    | node hlay _ => exact hlay
  obtain ⟨hI', hg, hb⟩ := metK_deriv huse _ st₁ st' hmet hI₁
  rw [bindInnerK_congr (nd' := nodeOfK lo) hfp hnF hfk] at hin
  rw [hdsF, hnF] at hrs
  rw [hdsF] at hlen
  rw [hdsF, hnF, hmg] at hpar
  rw [hnF] at hall hin hbok
  exact ⟨hI', hg₁.trans hg, fun hrb met hmt =>
    .use hinst hk52 hd hgrp hlv hkds hlen hrs hin hall hpar
      (fun b hbm hbc => hb met hmt b hbm hbc)
      (hH hu0 hu1 hrb hlay hgrp hlv hkds hlen hrs hin hall hfT hfN rfl hbok)⟩

/-- **A node's walk, derived**: its layout the one function at
`nestContainer`, its crests derived at its final met set, the node recorded
with its derivation. -/
theorem nodeKBody_deriv
    {rec : LayoutK → Nat → Nat → Expr → NestStK → CheckM (NestFieldKind × Expr × NestStK)}
    {syn : LayoutK → Option NestKey → Expr → NestStK → CheckM NestStK}
    (hrec : RunDerivK ops env ctx hk rec) (hsyn : SynDerivK ops env ctx hk syn) {kc : NestKey}
    (hu0 : ctx.names.contains kc.cname = false ∧ kc.cname ≠ quotName)
    {st : NestStK} {base : NestState} (hbase : CtorsOfOk ctx base) (hI : DerivCacheK ops env ctx hk st)
    {lo : LayoutOutK} {st₂ : NestStK}
    (hlay : nestLayoutK (m := CheckM) ops env ctx
      (fun c => match base.ctorsOf.lookup c with
        | some r => r
        | none => nestContainer ctx c) kc = .ok lo)
    (hw : ctorsK (m := CheckM) ctx rec syn lo.L (lo.ctors.zip lo.crests)
      { base := { base with active := lo.L.grp.map (fun g => ⟨g, kc.lvls, kc.ds⟩) ++ base.active },
        cache := st.cache, met := [] } = .ok st₂) :
    CtorsOfOk ctx st₂.base ∧ ∀ b : NestState, CtorsOfOk ctx b →
      DerivCacheK ops env ctx hk (recordK ctx kc lo st₂.met lo.ginfo
        { base := b, cache := st₂.cache, met := st.met }) ∧
      (recordK ctx kc lo st₂.met lo.ginfo { base := b, cache := st₂.cache, met := st.met }).met
        = st.met := by
  rw [hbase.look_eq] at hlay
  obtain ⟨hI₂, -, hd⟩ := ctorsK_deriv hrec hsyn _ _ st₂ hw ⟨hbase, hI.2⟩
  have hnode : PosDKH ops env ctx hk (.node kc lo st₂.met) := .node hlay (hd _ (List.Subset.refl _))
  exact ⟨hI₂.1, fun b hb =>
    recordK_deriv hnode hu0 lo.ginfo _ (fun g hg => List.mem_map_of_mem hg) ⟨hb, hI₂.2⟩⟩

/-! ## THE INVERSION -/

/-- **THE ONE INVERSION OF THE KEY-NAMED POSITIVITY RUN.**  At any fuel and
under any `ops`, a successful `posK` / `synK` / `useK` / `nodeK` keeps the
cache invariant, only grows the current node's met set, and derives its
input (`PosDK`) at every superset of the final met set. -/
theorem posK_deriv (hH : HookOkK ops env ctx hk) : ∀ fuel,
    RunDerivK ops env ctx hk (posK ops env ctx fuel) ∧ SynDerivK ops env ctx hk (synK ops env ctx fuel) ∧
      UseDerivK ops env ctx hk (useK ops env ctx fuel) ∧ NodeDerivK ops env ctx hk (nodeK ops env ctx fuel)
  | 0 => by
    refine ⟨fun _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ h => ?_,
      fun _ _ _ _ h => ?_⟩ <;>
    simp [posK, synK, useK, nodeK, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1 => by
    obtain ⟨ih, ihs, ihu, ihn⟩ := posK_deriv hH fuel
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- the field walk
      intro L dep kb e st k nf st' hrun hI
      rw [posK] at hrun
      cases hw : ops.whnf env dep e with
      | error err => simp [hw, bind, Except.bind] at hrun
      | ok w =>
        simp only [hw, bind, Except.bind] at hrun
        by_cases hocc : w.nestOcc ctx.names ctx.nP L.hi = false
        · rw [if_pos (by simpa using hocc)] at hrun
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl, rfl⟩ := hrun
          exact ⟨hI, MetGrow.refl _, fun _ _ => .const hw hocc⟩
        have hocc' : w.nestOcc ctx.names ctx.nP L.hi = true := by simpa using hocc
        rw [if_neg (by simpa using hocc)] at hrun
        split at hrun
        · -- `pi`
          rename_i a b bm
          by_cases ha : a.nestOcc ctx.names ctx.nP L.hi = true
          · rw [if_pos ha] at hrun
            simp [throw, throwThe, MonadExceptOf.throw] at hrun
          rw [if_neg ha] at hrun
          split at hrun
          · simp at hrun
          rename_i v hv
          obtain ⟨k₁, nb, st₁⟩ := v
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl, rfl⟩ := hrun
          obtain ⟨hI', hg, hb⟩ := ih L (dep + 1) (kb + 1) _ st k₁ nb _ hv hI
          exact ⟨hI', hg, fun met hm => .pi hw hocc' (by simpa using ha) (hb met hm)⟩
        · -- a head applied to arguments
          split at hrun
          · -- a variable head
            rename_i i ty hfn
            by_cases hmem : (decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = true
            · rw [if_pos hmem] at hrun
              by_cases hc : (w.getAppArgs.length == ctx.nP + ctx.nIdxs.getD (i - ctx.nP) 0 &&
                  List.take ctx.nP w.getAppArgs == ctx.params &&
                  w.getAppArgs.all fun x => !Expr.nestOcc ctx.names ctx.nP L.hi x) = true
              · rw [if_pos hc] at hrun
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, rfl, rfl⟩ := hrun
                refine ⟨hI, MetGrow.refl _, fun met _ => ?_⟩
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hmem
                simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
                  Bool.not_eq_eq_eq_not, Bool.not_true] at hc
                have hd := PosDKH.hole (hk := hk) (met := met) (kb := kb) hw hocc' hfn hmem.1 hmem.2 hc.1.1 hc.1.2 hc.2
                by_cases hkb : kb = 0
                · subst hkb; exact hd
                · have : (kb == 0) = false := by simpa using hkb
                  simp only [this, hkb, if_false, Bool.false_eq_true] at hd ⊢
                  exact hd
              · rw [if_neg hc] at hrun
                simp [throw, throwThe, MonadExceptOf.throw] at hrun
            · rw [if_neg hmem] at hrun
              by_cases hfr : (decide (ctx.hiAt 0 ≤ i) && decide (i < L.hi)) = true
              · rw [if_pos hfr] at hrun
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hfr
                by_cases hjn : i - ctx.hiAt 0 < L.nF
                · rw [if_pos hjn] at hrun
                  split at hrun
                  · simp [throw, throwThe, MonadExceptOf.throw] at hrun
                  rename_i key nI hfam
                  by_cases hc : (w.getAppArgs.length == nI &&
                      w.getAppArgs.all fun x => !Expr.nestOcc ctx.names ctx.nP L.hi x) = true
                  · rw [if_pos hc] at hrun
                    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
                      Bool.not_eq_eq_eq_not, Bool.not_true] at hc
                    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨rfl, rfl, rfl⟩ := hrun
                    have hin : i - ctx.hiAt 0 ∈
                        (if (!st.met.contains (i - ctx.hiAt 0)) = true then
                          { st with met := st.met ++ [i - ctx.hiAt 0] } else st).met := by
                      split
                      · exact List.mem_append_right _ (List.mem_singleton_self _)
                      · rename_i hc'
                        simpa using hc'
                    refine ⟨?_, ?_, fun met hm => .famHole hw hocc' hfn hfr.1 hfr.2 hjn hfam hc.1 hc.2
                      (hm hin)⟩
                    · split
                      · exact hI.withMet _
                      · exact hI
                    · split
                      · exact fun x hx => List.mem_append_left _ hx
                      · exact MetGrow.refl _
                  · rw [if_neg hc] at hrun
                    simp [throw, throwThe, MonadExceptOf.throw] at hrun
                · rw [if_neg hjn] at hrun
                  split at hrun
                  · simp [throw, throwThe, MonadExceptOf.throw] at hrun
                  rename_i g hg
                  by_cases hpar : (decide (L.dsF.length ≤ w.getAppArgs.length) &&
                      (List.take L.dsF.length w.getAppArgs == L.dsF)) = true
                  · rw [if_pos hpar] at hrun
                    by_cases hidx : (((w.getAppArgs.drop L.dsF.length).all fun x =>
                        !Expr.nestOcc ctx.names ctx.nP L.hi x) &&
                        (w.getAppArgs.length == nestArity ctx g)) = true
                    · rw [if_pos hidx] at hrun
                      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
                      obtain ⟨rfl, rfl, rfl⟩ := hrun
                      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpar
                      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not,
                        Bool.not_true, beq_iff_eq] at hidx
                      exact ⟨hI, MetGrow.refl _, fun met _ => .ownHole hw hocc' hfn hfr.1 hfr.2
                        (by omega) hg hpar.1 hpar.2 hidx.1 hidx.2⟩
                    · rw [if_neg hidx] at hrun
                      simp [throw, throwThe, MonadExceptOf.throw] at hrun
                  · rw [if_neg hpar] at hrun
                    simp [throw, throwThe, MonadExceptOf.throw] at hrun
              · rw [if_neg hfr] at hrun
                simp [throw, throwThe, MonadExceptOf.throw] at hrun
          · -- a constant head: the container case
            rename_i n us hfn
            by_cases hnm : ctx.names.contains n = true
            · rw [if_pos hnm] at hrun
              simp [throw, throwThe, MonadExceptOf.throw] at hrun
            rw [if_neg hnm] at hrun
            split at hrun
            · simp at hrun
            rename_i v hv
            obtain ⟨k₁, st₁⟩ := v
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl, rfl⟩ := hrun
            obtain ⟨hI', hg, hkind, nPc, Lc, nI, cty, hC, hquot, hlen, hidx, hds, hnI, hu⟩ :=
              contK_deriv ihu hv hI
            refine ⟨hI', hg, fun met hm => ?_⟩
            rw [hkind]
            exact .cont hw hocc' hfn (by simpa using hnm) hC hquot hlen hidx hds hnI (hu met hm)
          · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · -- the syntactic pass
      intro L skip e st st' h hI
      rw [synK] at h
      exact synKeysK_deriv ihu _ st st' (fun _ hk => nestSynOccs_src hk) h hI
    · -- a use
      intro L kc ps st qi st' h hI
      simp only [useK, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
        Except.pure] at h
      -- U0/U1 (NESTKN-K3)
      split at h
      · simp at h
      rename_i hU0
      have hu0 : ctx.names.contains kc.cname = false ∧ kc.cname ≠ quotName := by
        simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hU0
        exact hU0
      have hlook := hI.1.lookup kc.cname
      have hI := hI.withBase (hI.1.insert kc.cname)
      split at h
      rotate_left
      · simp at h
      rename_i q hq
      split at h
      rotate_left
      · simp at h
      rename_i hqn
      have hu1 : ∃ Lc, nestContainer ctx kc.cname = some (ps.length, Lc) := by
        rw [← hlook, hq]
        exact ⟨q.2, by simp only [beq_iff_eq] at hqn; rw [← hqn]⟩
      split at h
      · simp at h
      rename_i r₁ hr₁
      split at h
      · simp at h
      rename_i ty hty
      split at h
      · -- a cache hit
        split at h
        · simp at h
        rename_i nd hnd
        split at h
        · simp at h
        rename_i bs hbs
        split at h
        · simp at h
        rename_i st₂ hst₂
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact useTail_deriv hH ihu ⟨r₁, hr₁⟩ ⟨ty, hty⟩ hu1 hI (MetGrow.refl _) hnd hbs hst₂
      · -- a first visit
        split at h
        · simp at h
        split at h
        · simp at h
        rename_i st₁ hst₁
        obtain ⟨hI₁, hg₁⟩ := ihn kc _ st₁ hu0 hst₁ hI
        split at h
        · simp at h
        rename_i nd hnd
        split at h
        · simp at h
        rename_i bs hbs
        split at h
        · simp at h
        rename_i st₂ hst₂
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact useTail_deriv hH ihu ⟨r₁, hr₁⟩ ⟨ty, hty⟩ hu1 hI₁ hg₁ hnd hbs hst₂
    · -- a node
      intro kc st st' hu0 h hI
      simp only [nodeK, bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      rename_i q hq
      split at h
      · simp at h
      rename_i v hv
      obtain ⟨ctors, base⟩ := v
      have hbase : CtorsOfOk ctx base := nestGroupCtors_ctorsOk _ _ _ _ hv (hI.1.insert kc.cname)
      split at h
      · simp at h
      rename_i lo hlo
      split at h
      · simp at h
      rename_i st₂ hst₂
      split at h
      · simp at h
      rename_i grp hgrp
      split at h
      · simp at h
      rename_i nfs hnfs
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨hb₂, hrest⟩ := nodeKBody_deriv ih ihs hu0 hbase hI hlo hst₂
      obtain ⟨hI', hmet⟩ := hrest
        ⟨st₂.base.keys, st₂.base.ctorsOf, st₂.base.nodes, base.active,
          st₂.base.ctorNfs ++ nfs.toArray⟩ hb₂
      exact ⟨hI', by rw [MetGrow, hmet]; exact List.Subset.refl _⟩

/-! ## The root: the member constructors, the block -/

/-- **A member constructor's run, derived** (at the root layout). -/
theorem nestMemberCtorK_deriv (hH : HookOkK ops env ctx hk) {nF : Nat} {crest : Expr} {st : NestStK}
    {ks : List NestFieldKind} {tyN : Expr} {st' : NestStK}
    (h : nestMemberCtorK (m := CheckM) ops env ctx nF crest st = .ok (ks, tyN, st'))
    (hI : DerivCacheK ops env ctx hk st) :
    DerivCacheK ops env ctx hk st' ∧ MemberCtorDKH ops env ctx hk nF crest (ks.map (·.erase)) tyN := by
  simp only [nestMemberCtorK, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨ks₁, nds₁, res, st₁⟩ := r
  obtain ⟨hI₁, -, ht⟩ := (posK_deriv hH (whnfWalkFuel crest)).1
    |> fun hrec => fieldsK_deriv hrec (posK_deriv hH (whnfWalkFuel crest)).2.1 nF 0 crest st ks₁ nds₁
      res st₁ hr hI
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hu4
  split at h
  · rename_i hok
    split at h
    · rename_i hha
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true] at hok
      refine ⟨hI₁, st₁.met, nds₁, res, ht _ (List.Subset.refl _), rfl, ?_, hok.1, hok.2, hha⟩
      refine Bool.eq_false_iff.mpr fun hany => hu4 ?_
      rw [List.any_eq_true] at hany ⊢
      obtain ⟨i, hi, hx⟩ := hany
      refine ⟨i, hi, ?_⟩
      revert hx
      rw [erase_getD]
      cases ks₁.getD i .ordinary <;> simp [PosKind.guarded, NestFieldKind.erase]
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **One member's constructors, derived**: each its crest derived at the
root layout, with the run's kinds and normal form. -/
theorem nestMemberCtorsK_deriv (hH : HookOkK ops env ctx hk) {holes : List Expr} :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestStK) (kss : List (List NestFieldKind))
      (nss : List Expr) (st' : NestStK),
      nestMemberCtorsK (m := CheckM) ops env ctx holes cs st = .ok (kss, nss, st') →
      DerivCacheK ops env ctx hk st →
      DerivCacheK ops env ctx hk st' ∧ ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ crest ks tyN, instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
          kss[j]? = some ks ∧ nss[j]? = some tyN ∧
          MemberCtorDKH ops env ctx hk cA.2 crest (ks.map (·.erase)) tyN
  | [], st, kss, nss, st', h, hI => by
    simp only [nestMemberCtorsK, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hI, fun j cA hj => by simp at hj⟩
  | c :: cs, st, kss, nss, st', h, hI => by
    simp only [nestMemberCtorsK, bind, Except.bind, pure, Except.pure] at h
    split at h
    · simp at h
    rename_i crest hcrest
    have hcrest' := unwrapOr_ok hcrest
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨ks, tyN, st₁⟩ := r
    obtain ⟨hI₁, hd⟩ := nestMemberCtorK_deriv hH hr hI
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i r₂ hr₂
    obtain ⟨kss₂, nss₂, st₂⟩ := r₂
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨hI₂, hall⟩ := nestMemberCtorsK_deriv hH cs st₁ kss₂ nss₂ st₂ hr₂ hI₁
    refine ⟨hI₂, fun j cA hj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨crest, ks, tyN, hcrest', rfl, rfl, hd⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj ⊢
      exact hall j cA hj

/-- **The whole block's constructors, derived** (`nestBlockCtorsGoK`): every
member constructor derived at the root layout with the run's kinds and
normal form, and the FINAL state's invariant — every entry of the node
cache carries its node's derivation (the table the recursor check reads). -/
theorem nestBlockCtorsGoK_deriv (hH : HookOkK ops env ctx hk) {holes : List Expr} :
    ∀ (css : List (List (ConstantVal × Nat))) (st : NestStK)
      (ksss : List (List (List NestFieldKind))) (nsss : List (List Expr)) (st' : NestStK),
      nestBlockCtorsGoK (m := CheckM) ops env ctx holes css st = .ok (ksss, nsss, st') →
      DerivCacheK ops env ctx hk st →
      DerivCacheK ops env ctx hk st' ∧ ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ crest ks tyN, instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
          (ksss.getD c [])[j]? = some ks ∧ (nsss.getD c [])[j]? = some tyN ∧
          MemberCtorDKH ops env ctx hk cA.2 crest (ks.map (·.erase)) tyN
  | [], st, ksss, nsss, st', h, hI => by
    simp only [nestBlockCtorsGoK, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hI, fun c cs hc => by simp at hc⟩
  | cs :: css, st, ksss, nsss, st', h, hI => by
    simp only [nestBlockCtorsGoK, bind, Except.bind, pure, Except.pure] at h
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨kss, nss, st₁⟩ := r
    obtain ⟨hI₁, hd⟩ := nestMemberCtorsK_deriv hH cs st kss nss st₁ hr hI
    split at h
    · simp at h
    rename_i r₂ hr₂
    obtain ⟨ksss₂, nsss₂, st₂⟩ := r₂
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨hI₂, hall⟩ := nestBlockCtorsGoK_deriv hH css st₁ ksss₂ nsss₂ st₂ hr₂ hI₁
    refine ⟨hI₂, fun c cs' hc => ?_⟩
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      intro j cA hj
      simpa using hd j cA hj
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc
      intro j cA hj
      simpa using hall c cs' hc j cA hj

/-- **`nestBlockCtorsK`, derived**: every member constructor's crest derived
at the root layout, with the run's kinds and normal form. -/
theorem nestBlockCtorsK_deriv (hH : HookOkK ops env ctx hk) {holes : List Expr} {css : List (List (ConstantVal × Nat))}
    {ksss : List (List (List NestFieldKind))} {nsss : List (List Expr)} {base : NestState}
    (h : nestBlockCtorsK (m := CheckM) ops env ctx holes css = .ok (ksss, nsss, base)) :
    ∃ st : NestStK, st.base = base ∧ DerivCacheK ops env ctx hk st ∧
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ crest ks tyN, instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
          (ksss.getD c [])[j]? = some ks ∧ (nsss.getD c [])[j]? = some tyN ∧
          MemberCtorDKH ops env ctx hk cA.2 crest (ks.map (·.erase)) tyN := by
  simp only [nestBlockCtorsK, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨ksss₁, nsss₁, st⟩ := r
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨hI, hall⟩ := nestBlockCtorsGoK_deriv hH css {} ksss₁ nsss₁ st hr derivCacheK_empty
  exact ⟨st, rfl, hI, hall⟩

end ConLeche
