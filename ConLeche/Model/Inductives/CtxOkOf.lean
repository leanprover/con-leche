module

public import ConLeche.Verify.Inductives.PosCompleteLink
public import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Model.Inductives.StoredEnvOf
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Model.Inductives.BlockData
import ConLeche.Model.Inductives.BlockDatum
import ConLeche.Model.Inductives.StructBits
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.SumInv
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.BridgeWfImp
import ConLeche.Semantics.DeclRun
import ConLeche.Semantics.Inductives.DeclBlockEta

public section

/-!
# `CtxOk` from the install's run (lane COMPLETE-6C)

The completeness theorem (`nestedBlockPositivity_of_official_accepts`,
`Verify/Inductives/PosCompleteSide.lean`) reads the walk's context and
the member constructors through `CtxOk`.  This module derives it at the
context the install builds (`BlockShape.nestCtx` over the formers'
environment, at the head former's opened parameters — `nestedShadow`,
`checkBlockPositivity`), from the former stage's run
(`checkBlockInds`) alone, except for:

* `nodup` — the members' names are distinct: `checkBlock`'s (and
  `targetShadow`'s) guard, which `checkBlockInds` does not repeat
  (`nestedShadow` skips it) — a premise;
* `psFvar`'s `G` half — the auxiliary names are fresh in the formers'
  environment: `FreshSupply.envFresh` at this context — a premise;
* `ctorPi` — a constructor binds exactly its parameters and its
  RECORDED field count: the constructor stage's shape check
  (`checkSumCtor`), which `checkBlockInds` does not run.  The generic
  form (`ctxOk_of_formers`) takes it as `piArity` of each constructor
  type; `ctxOk_of_pass` derives it from the constructor stage
  (`checkBlockCtors`, `checkBlockPass`'s context), and
  `ctxOk_of_nestedShadow` from that stage run beside the shadow's own
  constant checks (which do not look at the field count).

Everything here is syntactic: no Model-tier invariant is read.
-/

namespace ConLeche.Model
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BlockShape BlockParts
  MemberShape NestCtx CtxOk CheckMode fueledOps)

variable {mode : CheckMode}

/-! ## Syntactic helpers -/

theorem piArity_of_stripPis :
    ∀ {k : Nat} {e r : Expr} {bs : List (Expr × ConLeche.BinderMeta)},
      e.stripPis k = some (bs, r) → e.piArity = k + r.piArity
  | 0, e, r, bs, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  | k + 1, .forallE ty body m, r, bs, h => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs', r'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    have := piArity_of_stripPis h'
    show body.piArity + 1 = _
    omega
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h => by
    simp [Expr.stripPis] at h

theorem piArity_mkAppN : ∀ (f : Expr) (args : List Expr), f.piArity = 0 →
    (Expr.mkAppN f args).piArity = 0
  | _, [], h => h
  | f, a :: as, _ => piArity_mkAppN (.app f a) as rfl

theorem resultSort_instantiate1_eq {v : Expr} : ∀ (e : Expr) (k : Nat) {u : Level},
    e.resultSort = some u → (e.instantiate1 v k).resultSort = some u
  | .forallE t b m, k, u, h => by
    simp only [Expr.resultSort] at h
    simp only [Expr.instantiate1, Expr.resultSort]
    exact resultSort_instantiate1_eq b (k + 1) h
  | .sort _, _, _, h => by simpa [Expr.instantiate1, Expr.resultSort] using h
  | .bvar _, _, _, h | .fvar _ _, _, _, h | .const _ _, _, _, h | .app _ _, _, _, h
  | .lam _ _ _, _, _, h | .letE _ _ _, _, _, h | .lit _, _, _, h | .proj _ _ _, _, _, h => by
    simp [Expr.resultSort] at h

theorem resultSort_instPisWith : ∀ (ds : List Expr) (t r : Expr) {u : Level},
    t.resultSort = some u → ConLeche.instPisWith ds t = some r → r.resultSort = some u
  | [], t, r, u, hs, h => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h; subst h; exact hs
  | d :: ds, .forallE a b m, r, u, hs, h => by
    simp only [ConLeche.instPisWith] at h
    simp only [Expr.resultSort] at hs
    exact resultSort_instPisWith ds _ r (resultSort_instantiate1_eq b 0 hs) h
  | _ :: _, .bvar _, _, _, _, h | _ :: _, .fvar _ _, _, _, _, h | _ :: _, .sort _, _, _, _, h
  | _ :: _, .const _ _, _, _, _, h | _ :: _, .app _ _, _, _, _, h
  | _ :: _, .lam _ _ _, _, _, _, h | _ :: _, .letE _ _ _, _, _, _, h | _ :: _, .lit _, _, _, _, h
  | _ :: _, .proj _ _ _, _, _, _, h => by
    simp [ConLeche.instPisWith] at h

theorem piBinders_of_resultSort : ∀ {e : Expr} {u : Level},
    e.resultSort = some u → e.piBinders.2 = .sort u
  | .forallE t b m, u, h => by
    simp only [Expr.resultSort] at h
    simp only [Expr.piBinders]
    exact piBinders_of_resultSort h
  | .sort _, _, h => by simp only [Expr.resultSort, Option.some.injEq] at h; subst h; rfl
  | .bvar _, _, h | .fvar _ _, _, h | .const _ _, _, h | .app _ _, _, h
  | .lam _ _ _, _, h | .letE _ _ _, _, h | .lit _, _, h | .proj _ _ _, _, h => by
    simp [Expr.resultSort] at h

/-- Instantiating leading binders at variables loses exactly them. -/
theorem piArity_instPisWith_fvars : ∀ (ds : List Expr) (t r : Expr),
    (∀ d ∈ ds, ∃ i ty, d = .fvar i ty) →
    ConLeche.instPisWith ds t = some r → r.piArity + ds.length = t.piArity
  | [], t, r, _, h => by simp only [ConLeche.instPisWith, Option.some.injEq] at h; subst h; rfl
  | d :: ds, .forallE a b m, r, hd, h => by
    simp only [ConLeche.instPisWith] at h
    obtain ⟨i, ty, rfl⟩ := hd d List.mem_cons_self
    have := piArity_instPisWith_fvars ds _ r (fun d' hd' => hd d' (List.mem_cons_of_mem _ hd')) h
    rw [ConLeche.piArity_instantiate1] at this
    simp only [Expr.piArity, List.length_cons]; omega
  | _ :: _, .bvar _, _, _, h | _ :: _, .fvar _ _, _, _, h | _ :: _, .sort _, _, _, h
  | _ :: _, .const _ _, _, _, h | _ :: _, .app _ _, _, _, h | _ :: _, .lam _ _ _, _, _, h
  | _ :: _, .letE _ _ _, _, _, h | _ :: _, .lit _, _, _, h | _ :: _, .proj _ _ _, _, _, h => by
    simp [ConLeche.instPisWith] at h

/-- Replacing constants by non-`∀` terms keeps the `∀` count. -/
theorem piArity_replaceConsts {f : Name → List Level → Option Expr}
    (hf : ∀ n us v, f n us = some v → v.piArity = 0) :
    ∀ (e : Expr), (e.replaceConsts f).piArity = e.piArity
  | .forallE t b m => by
    simp only [Expr.replaceConsts, Expr.piArity]
    rw [piArity_replaceConsts hf b]
  | .const n us => by
    simp only [Expr.replaceConsts]
    cases h : f n us with
    | none => rfl
    | some v => exact hf n us v h
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _ _ | .letE _ _ _ | .lit _
  | .proj _ _ _ => rfl

theorem option_mapM_mem' {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {rs : List β}, l.mapM f = some rs → ∀ r ∈ rs, ∃ a ∈ l, f a = some r
  | [], rs, h, r, hr => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; exact nomatch hr
  | a :: l, rs, h, r, hr => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some rs' =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨a', ha', h'⟩ := option_mapM_mem' hl r hr
          exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

/-- The member holes are variables. -/
theorem nestHoles_fvar {ctx : NestCtx} {holes : List Expr}
    (h : ConLeche.nestHoles ctx = some holes) : ∀ x ∈ holes, ∃ i ty, x = .fvar i ty := by
  intro x hx
  obtain ⟨mm, -, hmm⟩ := option_mapM_mem' h x hx
  revert hmm
  split
  · intro hmm; exact ⟨_, _, (Option.some.inj hmm).symm⟩
  · intro hmm; exact nomatch hmm

/-- The member abstraction keeps the `∀` count. -/
theorem piArity_nestAbstract {ctx : NestCtx} {holes : List Expr}
    (hh : ConLeche.nestHoles ctx = some holes) (e : Expr) :
    (ConLeche.nestAbstract ctx holes e).piArity = e.piArity := by
  refine piArity_replaceConsts (fun c us v hv => ?_) e
  revert hv
  split
  · split
    · intro hv
      obtain ⟨i, ty, rfl⟩ := nestHoles_fvar hh v (List.mem_of_getElem? hv)
      rfl
    · intro hv; exact nomatch hv
  · intro hv; exact nomatch hv

/-- A former's parameters, opened, are variables. -/
theorem openPisAtFvars_fvar {n : Nat} {e : Expr} {fvs : List Expr} {b : Expr}
    (h : ConLeche.openPisAtFvars n e 0 = some (fvs, b)) : ∀ x ∈ fvs, ∃ i ty, x = .fvar i ty := by
  intro x hx
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
  obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index n e 0 h j x hj
  exact ⟨_, _, rfl⟩

/-! ## Lookups through the formers' conses -/

theorem consBlockInds_find?_self {p₁ : BlockShape} {isRec : Bool} :
    ∀ {cvTas : List ConstantVal} {i : Nat} {env : Env} {j : Nat} {cv : ConstantVal},
      (cvTas.map (·.name)).Nodup → cvTas[j]? = some cv →
      ∃ caps, (ConLeche.consBlockInds p₁ isRec cvTas i env).find? cv.name = some (.indInfo cv caps)
  | [], _, _, _, _, _, h => by simp at h
  | c :: rest, i, env, 0, cv, hnd, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    refine ⟨ConLeche.blockCapsAt p₁ i isRec, ?_⟩
    simp only [ConLeche.consBlockInds]
    rw [ConLeche.Semantics.consBlockInds_find?_of_ne (fun c' hc' he => hnd.1 ⟨c', hc', he⟩)]
    exact ConLeche.Env.find?_cons_self (.indInfo c _) env
  | c :: rest, i, env, j + 1, cv, hnd, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [ConLeche.consBlockInds]
    exact consBlockInds_find?_self hnd.2 h

/-! ## The former stage's facts, per member -/

/-- One member's former run: its name, freshness, resolution, closedness
and telescope. -/
theorem blockTele_facts {F : Nat} {env : Env} {nP : Nat} {ms : MemberShape}
    {cvTa : ConstantVal} {s : Level}
    (h : ConLeche.checkBlockTele (fueledOps mode F) env nP ms = .ok (cvTa, s)) :
    cvTa.name = ms.cvT.name ∧ env.find? cvTa.name = none ∧
      cvTa.type.constsResolve env = true ∧ cvTa.type.hasFvar = false ∧
      cvTa.type.looseBVarsBounded 0 = true ∧
      ∃ bs, cvTa.type.stripPis (nP + ms.nIdx) = some (bs, .sort s) := by
  obtain ⟨cvT, hn, -, hccv, bs, hst⟩ := ConLeche.checkBlockTele_shape h
  obtain ⟨hfind, -, -, -, hlbt, hitf, type', -, -, hann, -, htr, -, -, rfl⟩ :=
    ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := ConLeche.Semantics.annotate_syntax hann hitf hlbt
  exact ⟨hn, hfind, htr, htf', hbt', bs, hst⟩

/-- The former stage, member by member: member `m`'s former is the run
of `q.members[m]`, at the block's parameter count; member 0's ends in
the block's sort itself. -/
theorem checkBlockInds_member {F : Nat} {env envI : Env} {p₀ : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {q : BlockShape}
    (h : ConLeche.checkBlockInds (fueledOps mode F) env p₀ isRec = .ok (envI, cvTas, q)) :
    cvTas.length = q.members.length ∧
    ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
      ∃ ms s, q.members[m]? = some ms ∧
        ConLeche.checkBlockTele (fueledOps mode F) env q.nP ms = .ok (cvTa, s) ∧
        (m = 0 → s = q.resSort) := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hmem, rfl, rfl, -, htele0, hteles, -⟩ :=
    ConLeche.checkBlockInds_shape h
  obtain ⟨hlen, hall⟩ := ConLeche.checkBlockTeles_inv hteles
  have hms : (p₀.toBlockShape.withSort s0).members = ms0 :: rest := hmem
  refine ⟨by rw [hms]; simp [hlen], fun m cvTa hm => ?_⟩
  rw [hms]
  match m with
  | 0 =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
    subst hm
    exact ⟨ms0, s0, rfl, htele0, fun _ => rfl⟩
  | j + 1 =>
    simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hm
    obtain ⟨r, hr, rfl⟩ := hm
    have hj : j < rest.length := hlen ▸ (List.getElem?_eq_some_iff.mp hr).1
    obtain ⟨r', hr', hrun⟩ := hall j rest[j] (List.getElem?_eq_getElem hj)
    rw [hr] at hr'
    obtain rfl := Option.some.inj hr'
    exact ⟨rest[j], r.2, by simp [List.getElem?_eq_getElem hj], hrun, fun h => nomatch h⟩

theorem except_mapM_getElem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {rs : List β}, l.mapM f = .ok rs →
      rs.length = l.length ∧ ∀ i (h : i < l.length), ∃ r, rs[i]? = some r ∧ f l[i] = .ok r
  | [], rs, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i h => absurd h (Nat.not_lt_zero _)⟩
  | a :: l, rs, h => by
    rw [List.mapM_cons] at h
    rcases ha : f a with e | r
    · simp [ha, bind, Except.bind] at h
    · rcases hl : l.mapM f with e | rs'
      · simp [ha, hl, bind, Except.bind] at h
      · simp only [ha, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hlen, hat⟩ := except_mapM_getElem hl
        refine ⟨by simp [hlen], fun i hi => ?_⟩
        match i with
        | 0 => exact ⟨r, rfl, ha⟩
        | i + 1 =>
          obtain ⟨r', hr', h'⟩ := hat i (by simpa using hi)
          exact ⟨r', by simpa using hr', h'⟩

/-! ## `CtxOk` -/

/-- **`CtxOk` at the install's walk context**, from the former stage's
run (`checkBlockInds`) and the head former's opened parameters, for any
constructor lists `ctorss` (one per member) binding exactly their
parameters and recorded fields.  The premises beyond the run: the
members' names are distinct (`checkBlock`'s guard), the auxiliary names
`G` are fresh in the formers' environment (`FreshSupply.envFresh`). -/
theorem ctxOk_of_formers {F : Nat} {env envI : Env} {p₀ : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {q : BlockShape} {G : Name → Bool}
    {cvTa0 : ConstantVal} {fvsP : List Expr} {body : Expr}
    {ctorss : List (List (ConstantVal × Nat))}
    (h : ConLeche.checkBlockInds (fueledOps mode F) env p₀ isRec = .ok (envI, cvTas, q))
    (h0 : cvTas.head? = some cvTa0)
    (hps : ConLeche.openPisAtFvars q.nP cvTa0.type 0 = some (fvsP, body))
    (hnd : q.memberNames.Nodup)
    (hG : ∀ n, G n = true → envI.find? n = none)
    (hlen : ctorss.length = q.memberNames.length)
    (hctor : ∀ cs ∈ ctorss, ∀ cc ∈ cs, cc.1.type.piArity = q.nP + cc.2) :
    CtxOk (q.nestCtx fvsP envI.find? envI.consts) G ctorss := by
  obtain ⟨hlenCv, hmemb⟩ := checkBlockInds_member h
  obtain ⟨-, -, -, -, -, -, -, -, hcons, -⟩ := ConLeche.checkBlockInds_shape h
  have hnamesLen : q.memberNames.length = q.members.length := by
    simp [BlockShape.memberNames]
  -- member `i`'s name is its former's
  have hnameAt : ∀ (i : Nat) (hi : i < cvTas.length),
      cvTas[i].name = q.memberNames[i]'(by rw [hnamesLen, ← hlenCv]; exact hi) := by
    intro i hi
    obtain ⟨ms, s, hms, hrun, -⟩ := hmemb i cvTas[i] (List.getElem?_eq_getElem hi)
    obtain ⟨hn, -⟩ := blockTele_facts hrun
    rw [hn]
    obtain ⟨_, hms'⟩ := List.getElem?_eq_some_iff.mp hms
    simp only [BlockShape.memberNames, List.getElem_map, hms']
  have hmapN : cvTas.map (·.name) = q.memberNames :=
    List.ext_getElem (by rw [List.length_map, hlenCv, hnamesLen])
      fun i h1 h2 => by rw [List.getElem_map]; exact hnameAt i (by simpa using h1)
  have hndCv : (cvTas.map (·.name)).Nodup := hmapN ▸ hnd
  -- member `i` is stored as its former
  have hfindAt : ∀ (i : Nat) (hi : i < q.memberNames.length), ∃ caps,
      envI.find? q.memberNames[i] = some (.indInfo (cvTas[i]'(by
        rw [hlenCv, ← hnamesLen]; exact hi)) caps) := by
    intro i hi
    have hi' : i < cvTas.length := by rw [hlenCv, ← hnamesLen]; exact hi
    rw [← hnameAt i hi', hcons]
    exact consBlockInds_find?_self hndCv (List.getElem?_eq_getElem hi')
  -- a member is fresh before the block
  have hfresh : ∀ n, q.memberNames.contains n = true → env.find? n = none := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.contains_iff_mem.mp hn)
    have hi' : i < cvTas.length := by rw [hlenCv, ← hnamesLen]; exact hi
    rw [← hnameAt i hi']
    obtain ⟨ms, s, -, hrun, -⟩ := hmemb i cvTas[i] (List.getElem?_eq_getElem hi')
    exact (blockTele_facts hrun).2.1
  -- member 0's former
  obtain ⟨ms0, s0, hms0, hrun0, hs0⟩ := hmemb 0 cvTa0 (by rw [← h0, List.head?_eq_getElem?])
  obtain ⟨-, -, hres0, hfv0, -, bs0, hst0⟩ := blockTele_facts hrun0
  have hpsLen : fvsP.length = q.nP := ConLeche.Model.openPisAtFvars_length q.nP hps
  have hpsFv := openPisAtFvars_fvar hps
  -- the stored former at member `i`, and its telescope
  have hformer : ∀ (i : Nat) (hi : i < q.memberNames.length),
      ConLeche.formerOf (q.nestCtx fvsP envI.find? envI.consts) q.memberNames[i]
        = (cvTas[i]'(by rw [hlenCv, ← hnamesLen]; exact hi)).type := by
    intro i hi
    obtain ⟨caps, hf⟩ := hfindAt i hi
    simp only [ConLeche.formerOf, BlockShape.nestCtx, hf]
  refine ⟨hlen, hpsLen, ?psFvar, ?psClosed, hnd, ?nIdx, ?psScoped, ?ctorPi,
    ?ne, ?sort0, ?formerLbb⟩
  case psFvar =>
    intro i hi
    obtain ⟨ty, hx⟩ := ConLeche.openPisAtFvars_index q.nP cvTa0.type 0 hps i fvsP[i]
      (List.getElem?_eq_getElem hi)
    refine ⟨ty, by show fvsP[i] = _; rw [hx, Nat.zero_add], ?_⟩
    have hr := (openPisAtFvars_constsResolve q.nP hres0 hps).1 fvsP[i] (List.getElem_mem hi)
    rw [hx] at hr
    simp only [Expr.constsResolve] at hr
    refine deepOcc_false_of_resolve (fun n hn => ?_) ty hr
    rcases Bool.or_eq_true_iff.mp hn with hn | hn
    · exact hfresh n hn
    · have := hG n hn
      rw [hcons] at this
      exact consBlockInds_find?_none this
  case psClosed =>
    intro p hp
    obtain ⟨i, ty, rfl⟩ := hpsFv p hp
    rfl
  case nIdx =>
    intro i hi ty hty
    have hi' : i < cvTas.length := by rw [hlenCv, ← hnamesLen]; exact hi
    obtain ⟨ms, s, hms, hrun, -⟩ := hmemb i cvTas[i] (List.getElem?_eq_getElem hi')
    obtain ⟨-, -, -, -, -, bs, hst⟩ := blockTele_facts hrun
    change ConLeche.Official.instPiParams (ConLeche.formerOf _ q.memberNames[i]) fvsP = _ at hty
    rw [hformer i hi, ConLeche.Official.instPiParams_ok] at hty
    have ha := piArity_instPisWith_fvars fvsP _ ty hpsFv hty
    rw [piArity_of_stripPis hst, hpsLen] at ha
    have hnI : q.nIdxs.getD i 0 = ms.nIdx := by
      simp [BlockShape.nIdxs, List.getD_eq_getElem?_getD, hms]
    show ty.piArity = q.nIdxs.getD i 0
    rw [hnI]
    simp only [Expr.piArity] at ha
    omega
  case psScoped =>
    intro p hp
    have := (ConLeche.openPisAtFvars_WScoped q.nP cvTa0.type 0 hps
      (ConLeche.Expr.WScoped.of_not_hasFvar hfv0)).1 p hp
    rwa [Nat.zero_add] at this
  case ctorPi =>
    intro holes hh cs hcs cc hcc crest hcr
    have ha := piArity_instPisWith_fvars fvsP _ crest hpsFv hcr
    rw [piArity_nestAbstract hh, hctor cs hcs cc hcc, hpsLen] at ha
    show crest.piArity = cc.2
    omega
  case ne =>
    show q.memberNames ≠ []
    intro hnil
    have : cvTas.length = 0 := by rw [hlenCv, ← hnamesLen, hnil]; rfl
    rw [List.length_eq_zero_iff.mp this] at h0
    exact nomatch h0
  case sort0 =>
    intro n ty hn hty
    change q.memberNames.head? = some n at hn
    have h0l : 0 < q.memberNames.length := by
      rw [List.head?_eq_getElem?] at hn
      exact (List.getElem?_eq_some_iff.mp hn).1
    have hn0 : q.memberNames[0] = n := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0l] at hn
      exact Option.some.inj hn
    have hc0 : cvTas[0]'(by rw [hlenCv, ← hnamesLen]; exact h0l) = cvTa0 := by
      have h0' : cvTas[0]? = some cvTa0 := by rw [← h0, List.head?_eq_getElem?]
      rw [List.getElem?_eq_getElem (by rw [hlenCv, ← hnamesLen]; exact h0l)] at h0'
      exact Option.some.inj h0'
    have hrs : cvTa0.type.resultSort = some q.resSort := by
      rw [← hs0 rfl]; exact resultSort_of_stripPis_sort hst0
    change ConLeche.Official.instPiParams (ConLeche.formerOf _ n) fvsP = _ at hty
    rw [← hn0, hformer 0 h0l, hc0, ConLeche.Official.instPiParams_ok] at hty
    exact piBinders_of_resultSort
      (resultSort_instPisWith fvsP _ ty hrs hty)
  case formerLbb =>
    intro m hm cv caps hf
    obtain ⟨caps', hf'⟩ := hfindAt m hm
    change envI.find? q.memberNames[m] = _ at hf
    rw [hf'] at hf
    obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
    have hi' : m < cvTas.length := by rw [hlenCv, ← hnamesLen]; exact hm
    obtain ⟨ms, s, -, hrun, -⟩ := hmemb m cvTas[m] (List.getElem?_eq_getElem hi')
    exact (blockTele_facts hrun).2.2.2.2.1

/-! ## The constructor stage supplies `ctorPi` -/

/-- **The constructor stage, per constructor**: every constructor the
stage returns is its declared constructor's constant check, keeps the
recorded field count, and binds exactly the parameters and those
fields (`checkSumCtor`'s result check). -/
theorem checkBlockCtors_ctor {F : Nat} {env₀ env : Env} {q : BlockShape} :
    ∀ {l : List (MemberShape × ConstantVal)} {ctorsAs : List (List (ConstantVal × Nat))}
      {sortsss : List (List (List Level))},
      ConLeche.checkBlockCtors (fueledOps mode F) env₀ env q l = .ok (ctorsAs, sortsss) →
      ctorsAs.length = l.length ∧
      ∀ (i : Nat) (mc : MemberShape × ConstantVal), l[i]? = some mc →
        ∃ ctorsA, ctorsAs[i]? = some ctorsA ∧ ctorsA.length = mc.1.ctors.length ∧
          ∀ (j : Nat) (c cA : ConstantVal × Nat), mc.1.ctors[j]? = some c → ctorsA[j]? = some cA →
            cA.2 = c.2 ∧
            ConLeche.checkConstantVal (fueledOps mode F) env c.1 = .ok cA.1 ∧
            cA.1.type.piArity = q.nP + c.2 := by
  intro l ctorsAs sortsss h
  obtain ⟨hlen, -, hall⟩ := ConLeche.checkBlockCtors_inv h
  refine ⟨hlen, fun i mc hmc => ?_⟩
  obtain ⟨ctorsA, sortss, hA, -, hrun⟩ := hall i mc hmc
  obtain ⟨hlenA, -, hallA⟩ := ConLeche.checkSumCtors_inv hrun
  refine ⟨ctorsA, hA, hlenA, fun j c cA hc hcA => ?_⟩
  obtain ⟨h2, sorts, -, hctor⟩ := hallA j c cA hc hcA
  obtain ⟨-, ⟨cbs, es, hst, -⟩, -⟩ := ConLeche.checkSumCtor_shape hctor
  refine ⟨h2, ConLeche.checkSumCtor_ccv hctor, ?_⟩
  rw [piArity_of_stripPis hst, piArity_mkAppN _ _ rfl]
  rfl

/-- **`CtxOk` at `checkBlockPass`'s walk context**: the former stage,
then the constructor stage at the formers' environment, whose
constructors are the walk's. -/
theorem ctxOk_of_pass {F : Nat} {env envI : Env} {p₀ : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {q : BlockShape} {G : Name → Bool}
    {cvTa0 : ConstantVal} {fvsP : List Expr} {body : Expr}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    (h : ConLeche.checkBlockInds (fueledOps mode F) env p₀ isRec = .ok (envI, cvTas, q))
    (hC : ConLeche.checkBlockCtors (fueledOps mode F) envI envI q (q.members.zip cvTas)
      = .ok (ctorsAs, sortsss))
    (h0 : cvTas.head? = some cvTa0)
    (hps : ConLeche.openPisAtFvars q.nP cvTa0.type 0 = some (fvsP, body))
    (hnd : q.memberNames.Nodup)
    (hG : ∀ n, G n = true → envI.find? n = none) :
    CtxOk (q.nestCtx fvsP envI.find? envI.consts) G ctorsAs := by
  obtain ⟨hlenCv, -⟩ := checkBlockInds_member h
  obtain ⟨hlen, hall⟩ := checkBlockCtors_ctor hC
  refine ctxOk_of_formers h h0 hps hnd hG ?_ ?_
  · rw [hlen, List.length_zip, hlenCv, Nat.min_self]; simp [BlockShape.memberNames]
  · intro cs hcs cc hcc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcs
    have hil : i < (q.members.zip cvTas).length := hlen ▸ hi
    obtain ⟨ctorsA, hA, hlenA, hctor⟩ := hall i _ (List.getElem?_eq_getElem hil)
    rw [List.getElem?_eq_getElem hi] at hA
    obtain rfl := Option.some.inj hA
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcc
    obtain ⟨h2, -, hpa⟩ := hctor j _ _ (List.getElem?_eq_getElem (hlenA ▸ hj))
      (List.getElem?_eq_getElem hj)
    rw [hpa, h2]

/-- **`CtxOk` at `nestedShadow`'s walk context.**  The shadow checks the
constructors as constants only, which does not look at their recorded
field counts: `ctorPi` needs the constructor stage (`hC`, which the
install runs at the same environment; the shadow's constructors are
then its). -/
theorem ctxOk_of_nestedShadow {F : Nat} {env envI : Env} {p₀ : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {q : BlockShape} {G : Name → Bool}
    {cvTa0 : ConstantVal} {fvsP : List Expr} {body : Expr}
    {ctorss ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    (h : ConLeche.checkBlockInds (fueledOps mode F) env p₀ isRec = .ok (envI, cvTas, q))
    (h0 : cvTas.head? = some cvTa0)
    (hps : ConLeche.openPisAtFvars q.nP cvTa0.type 0 = some (fvsP, body))
    (hcs : q.members.mapM (fun ms => ms.ctors.mapM fun c => do
        let cvCa ← ConLeche.checkConstantVal (fueledOps mode F) envI c.1
        pure (cvCa, c.2)) = .ok ctorss)
    (hnd : q.memberNames.Nodup)
    (hG : ∀ n, G n = true → envI.find? n = none)
    (hC : ConLeche.checkBlockCtors (fueledOps mode F) envI envI q (q.members.zip cvTas)
      = .ok (ctorsAs, sortsss)) :
    CtxOk (q.nestCtx fvsP envI.find? envI.consts) G ctorss := by
  obtain ⟨hlenCv, -⟩ := checkBlockInds_member h
  obtain ⟨-, hall⟩ := checkBlockCtors_ctor hC
  obtain ⟨hlen, hcsAt⟩ := except_mapM_getElem hcs
  refine ctxOk_of_formers h h0 hps hnd hG (by rw [hlen]; simp [BlockShape.memberNames]) ?_
  intro cs hcs' cc hcc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcs'
  have hi' : i < q.members.length := hlen ▸ hi
  obtain ⟨r, hr, hrun⟩ := hcsAt i hi'
  rw [List.getElem?_eq_getElem hi] at hr
  obtain rfl := Option.some.inj hr
  obtain ⟨hlenC, hcAt⟩ := except_mapM_getElem hrun
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcc
  have hj' : j < q.members[i].ctors.length := hlenC ▸ hj
  obtain ⟨cc, hcc', hcrun⟩ := hcAt j hj'
  rw [List.getElem?_eq_getElem hj] at hcc'
  obtain rfl := Option.some.inj hcc'
  have hiz : i < (q.members.zip cvTas).length := by
    rw [List.length_zip, hlenCv, Nat.min_self]; exact hi'
  obtain ⟨ctorsA, -, hlenA, hctor⟩ := hall i _ (List.getElem?_eq_getElem hiz)
  simp only [List.getElem_zip] at hlenA hctor
  obtain ⟨-, hccv, hpa⟩ := hctor j _ _ (List.getElem?_eq_getElem hj')
    (List.getElem?_eq_getElem (hlenA ▸ hj'))
  -- the shadow's constant check is the stage's
  cases hc : ConLeche.checkConstantVal (fueledOps mode F) envI (q.members[i].ctors[j]).1 with
  | error e => simp [hc, bind, Except.bind] at hcrun
  | ok cvCa =>
    simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hcrun
    rw [← hcrun]
    rw [hccv] at hc
    obtain rfl := Except.ok.inj hc
    exact hpa

end ConLeche.Model
