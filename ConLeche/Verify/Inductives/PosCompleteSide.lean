module

public import ConLeche.Verify.Inductives.PosCompleteLink
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Inductives.PosCompleteUnif

public section

/-!
# The frames' side checks against official's typing (lane COMPLETE-6, (A))

The walk's former check at a container instantiation (`nestInstType`:
the level count, the syntactic telescope, N2 — the index telescope
names no member — and N3 — the sort equivalent to the block's) is
discharged here from official's verdicts on its auxiliary declaration
(`Official.OfficialTypesAt`), through two NAMED hypotheses about
official's type checker, which is not transcribed:

* `TypingContract` — official's typing-oracle contract (`infer_constant`:
  "unknown constant", "incorrect number of universe levels");
* `LevelSim` — official's level equivalence (`is_equivalent`) is never
  refuted by the walk's fueled `Level.isEquiv`.
-/

namespace ConLeche

open Expr

section Side

variable {ctx : NestCtx}

/-! ## The named hypotheses -/

/-- **THE NAMED HYPOTHESIS: official's typing-oracle contract** (not
proved: official's type checker is not transcribed; `type_checker.cpp`,
`infer_constant`).  A term official's type checker accepts mentions only
constants declared in the environment it is checked in ("unknown
constant"), each at its declared number of universe levels ("incorrect
number of universe levels").  Stated for the two checks the walk's former
check mirrors: `check_inductive_types`' check of a type former
(`T.formerOk`, `inductive.cpp` v4.34.0 :261), in the environment BEFORE
the declaration (`before`: none of the declaration's types declared) —
no undeclared name occurs; and the final check of a replaced nested
application (`T.nestedOk`, :1320–1323), in the environment after it
(`after`) — every constant found there is at its level count. -/
@[expose] def TypingContract (T : Official.TypingOracle) (before after : Name → Option ConstantInfo) :
    Prop :=
  (∀ e, T.formerOk e → ∀ N : List Name, (∀ n ∈ N, before n = none) → e.nestOcc N 0 0 = false) ∧
  (∀ e, T.nestedOk e → ∀ n us, Expr.SubOf (.const n us) e → ∀ ci, after n = some ci →
    us.length = ci.toConstantVal.levelParams.length)

/-- **THE NAMED HYPOTHESIS `LevelSim`: official's level equivalence is
never refuted by the walk's** (not proved: official's `is_equivalent`,
`level.cpp`, normalises both levels; the walk's `Level.isEquiv` is a
fueled decision procedure).  Official's equivalence holding, the walk's
answers `true` or runs out of fuel (a decline) — never `false`. -/
@[expose] def LevelSim (T : Official.TypingOracle) : Prop :=
  ∀ l l', T.levelEquiv l l' = true → Level.isEquiv l l' ≠ some false

/-! ## The former check, forward -/

theorem SubOf.mkAppN {x f : Expr} (h : Expr.SubOf x f) :
    ∀ (args : List Expr), Expr.SubOf x (Expr.mkAppN f args)
  | [] => h
  | a :: as => SubOf.mkAppN (.appF a h) as

/-- **The walk's former check succeeds or declines** when each of its
checks holds (the fueled level comparison may run out). -/
theorem nestInstType_ok_of {hi : Nat} {C : Name} {us : List Level} {ds : List Expr}
    {cvC : ConstantVal} {caps : IndCaps} {ty : Expr} {s : Level}
    (hf : ctx.find? C = some (.indInfo cvC caps)) (hlv : us.length = cvC.levelParams.length)
    (hstrip : (cvC.type.stripPis ds.length).isSome = true)
    (hty : instPisWith ds (cvC.type.instantiateLevelParams cvC.levelParams us) = some ty)
    (hs : ty.piBinders.2 = .sort s)
    (hn2 : (ty.piBinders.1.any fun b => b.1.nestOcc ctx.names ctx.nP hi) = false)
    (hn3 : Level.isEquiv s ctx.sort ≠ some false) :
    OkOr (fun _ => True) (nestInstType (m := CheckM) ctx hi ⟨C, us, ds⟩) := by
  unfold nestInstType
  simp only [hf, unwrapOr, hlv, hstrip, hty, hs, hn2, bind, Except.bind, pure, Except.pure,
    if_true, if_false, Bool.false_eq_true]
  rcases he : Level.isEquiv s ctx.sort with _ | b
  · simp [liftFueled, throw, throwThe, MonadExceptOf.throw, Decline, OkOr]
  · cases b
    · exact absurd he hn3
    · simp [liftFueled, OkOr, pure, Except.pure]

/-! ## Syntactic helpers -/

theorem stripPis_isSome_of_piArity : ∀ (n : Nat) (e : Expr), n ≤ e.piArity → (e.stripPis n).isSome = true
  | 0, e, _ => by simp [Expr.stripPis]
  | n + 1, .forallE t b m, h => by
    simp only [Expr.piArity] at h
    have := stripPis_isSome_of_piArity n b (by omega)
    simp only [Expr.stripPis]
    revert this; cases b.stripPis n <;> simp
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h | _ + 1, .const _ _, h
  | _ + 1, .app _ _, h | _ + 1, .lam _ _ _, h | _ + 1, .letE _ _ _, h | _ + 1, .lit _, h
  | _ + 1, .proj _ _ _, h => by simp [Expr.piArity] at h

theorem resultSort_instPisWith : ∀ (ds : List Expr) (t r : Expr), t.resultSort.isSome = true →
    instPisWith ds t = some r → r.resultSort.isSome = true
  | [], t, r, hs, h => by simp only [instPisWith, Option.some.injEq] at h; subst h; exact hs
  | d :: ds, .forallE a b m, r, hs, h => by
    simp only [instPisWith] at h
    simp only [Expr.resultSort] at hs
    exact resultSort_instPisWith ds _ r (resultSort_instantiate1 (v := d) b 0 hs).1 h
  | _ :: _, .bvar _, _, _, h | _ :: _, .fvar _ _, _, _, h | _ :: _, .sort _, _, _, h
  | _ :: _, .const _ _, _, _, h | _ :: _, .app _ _, _, _, h | _ :: _, .lam _ _ _, _, _, h
  | _ :: _, .letE _ _ _, _, _, h | _ :: _, .lit _, _, _, h | _ :: _, .proj _ _ _, _, _, h => by
    simp [instPisWith] at h

theorem piBinders_sort_of_resultSort : ∀ (e : Expr), e.resultSort.isSome = true →
    ∃ s, e.piBinders.2 = .sort s
  | .forallE t b m, h => by
    simp only [Expr.resultSort] at h
    obtain ⟨s, hs⟩ := piBinders_sort_of_resultSort b h
    exact ⟨s, by simpa [Expr.piBinders] using hs⟩
  | .sort u, _ => ⟨u, rfl⟩
  | .bvar _, h | .fvar _ _, h | .const _ _, h | .app _ _, h | .lam _ _ _, h
  | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => by simp [Expr.resultSort] at h

theorem nestOcc_of_piBinders {N : List Name} {lo hi : Nat} : ∀ (e : Expr) (b : Expr × BinderMeta),
    b ∈ e.piBinders.1 → b.1.nestOcc N lo hi = true → e.nestOcc N lo hi = true
  | .forallE t body m, b, hb, ho => by
    simp only [Expr.piBinders, List.mem_cons] at hb
    simp only [Expr.nestOcc, Bool.or_eq_true]
    rcases hb with rfl | hb
    · exact .inl ho
    · exact .inr (nestOcc_of_piBinders body b hb ho)
  | .bvar _, _, hb, _ | .fvar _ _, _, hb, _ | .sort _, _, hb, _ | .const _ _, _, hb, _
  | .app _ _, _, hb, _ | .lam _ _ _, _, hb, _ | .letE _ _ _, _, hb, _ | .lit _, _, hb, _
  | .proj _ _ _, _, hb, _ => by simp [Expr.piBinders] at hb

theorem deepOcc_instantiateLevelParams {p : Name → Bool} {ks : List Name} {us : List Level} :
    ∀ (e : Expr), (e.instantiateLevelParams ks us).deepOcc p = e.deepOcc p := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams, Expr.deepOcc]

variable {σ : SigmaCtx} {o : Official.PosOracle} {prog : List NestHole} {act : List NestKey}

/-- **The σ-relation through a telescope instantiation.** -/
theorem SRel.instPisWith (hσ : SigmaOk ctx σ o) :
    ∀ {ds ds' : List Expr}, Rel2 (SRel ctx σ prog act) ds ds' → ∀ {t t' r : Expr},
      SRel ctx σ prog act t t' → instPisWith ds t = some r →
      ∃ r', instPisWith ds' t' = some r' ∧ SRel ctx σ prog act r r'
  | _, _, .nil, _, _, _, ht, h => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h; subst h; exact ⟨_, rfl, ht⟩
  | _, _, .cons hd hds, t, t', r, ht, h => by
    cases t with
    | forallE a b bm =>
      obtain ⟨a', b', rfl, -, hb⟩ := ht.forallE_inv_left
      simp only [ConLeche.instPisWith] at h ⊢
      exact SRel.instPisWith hσ hds (SRel.instantiate1 hσ hd hb 0) h
    | _ => simp [ConLeche.instPisWith] at h

/-- **The σ-relation through a `Π`-telescope's decomposition.** -/
theorem SRel.piBinders : ∀ {r r' : Expr}, SRel ctx σ prog act r r' →
    Rel2 (fun b b' : Expr × BinderMeta => SRel ctx σ prog act b.1 b'.1) r.piBinders.1 r'.piBinders.1 ∧
      SRel ctx σ prog act r.piBinders.2 r'.piBinders.2
  | .forallE a b bm, r', h => by
    obtain ⟨a', b', rfl, ha, hb⟩ := h.forallE_inv_left
    obtain ⟨h1, h2⟩ := SRel.piBinders hb
    exact ⟨.cons ha h1, h2⟩
  | .bvar _, r', h | .fvar _ _, r', h | .sort _, r', h | .const _ _, r', h | .app _ _, r', h
  | .lam _ _ _, r', h | .letE _ _ _, r', h | .lit _, r', h | .proj _ _ _, r', h => by
    cases r' with
    | forallE a' b' bm =>
      obtain ⟨_, _, he, -, -⟩ := h.forallE_inv
      exact nomatch he
    | _ => exact ⟨.nil, h⟩

theorem SRel.sort_left {u : Level} {x' : Expr} (h : SRel ctx σ prog act (.sort u) x') :
    x' = .sort u := by
  generalize hx : Expr.sort u = x at h
  cases h with
  | sort _ => cases hx; rfl
  | frm _ _ _ =>
    have := congrArg Expr.getAppFn hx
    rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | raw _ _ _ _ _ _ =>
    have := congrArg Expr.getAppFn hx
    rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | cnt _ _ =>
    have := congrArg Expr.getAppFn hx
    rw [Expr.getAppFn_mkAppN] at this; simp [Expr.getAppFn] at this
  | _ => simp at hx

/-! ## Official's formers -/

/-- **Official's type formers of its final auxiliary map** (from
`OfficialTypesAt`): the auxiliary type of every key — the container's
former at the key — typed before the declaration, its sort equivalent to
the block's. -/
structure OffFormers (ctx : NestCtx) (c : Official.ElimCtx) (T : Official.TypingOracle)
    (M : List (Expr × Name)) : Prop where
  former : ∀ J us Ds a, M.lookup (Expr.mkAppN (.const J us) Ds) = some a →
    ∀ cv caps, c.find? J = some (.indInfo cv caps) → ∀ ty,
      instPisWith Ds (cv.type.instantiateLevelParams cv.levelParams us) = some ty →
      T.formerOk ty ∧ ∀ s, ty.piBinders.2 = .sort s → T.levelEquiv s ctx.sort = true

/-- **(N2/N3 and the level count) at a key of official's final map**: the
walk's former check at a container instantiation whose read-back is a
key of official's final map succeeds or declines, under the typing-oracle
contract and `LevelSim`. -/
theorem nestInstType_of_key {c : Official.ElimCtx} {isAux : Name → Bool}
    {M : List (Expr × Name)} {T : Official.TypingOracle}
    (hσ : SigmaOk ctx (sigmaOfMap ctx c isAux M) o) (hlv : c.lvls = ctx.lps.map .param)
    (hoff : OffMap ctx c o isAux M) (hoT : OffTyped ctx c T M) (hoF : OffFormers ctx c T M)
    (hcon : TypingContract T c.find? ctx.find?) (hlev : LevelSim T)
    (hfind : ∀ n, ctx.names.contains n = false → c.find? n = ctx.find? n)
    (hbefore : ∀ n, o.names.contains n = true → c.find? n = none)
    (hfresh : ∀ J cv caps, c.find? J = some (.indInfo cv caps) →
      cv.type.deepOcc (fun n => ctx.names.contains n || isAux n) = false)
    (hsort : ∀ J cv caps, c.find? J = some (.indInfo cv caps) → ∃ u, cv.type.resultSort = some u)
    (hcl : NestCtxOk ctx)
    {P : List NestHole} (hso : StackOk ctx (sigmaOfMap ctx c isAux M) P)
    {C : Name} {us : List Level} {ds : List Expr} {a : Name}
    (hM : M.lookup (rbKey ctx P ⟨C, us, ds⟩) = some a)
    (hws : ∀ d ∈ ds, WShape ctx isAux P d) :
    OkOr (fun _ => True) (nestInstType (m := CheckM) ctx (ctx.hiAt P.length) ⟨C, us, ds⟩) := by
  have hM' : M.lookup (Expr.mkAppN (.const C us) (ds.map (rbE ctx P))) = some a := hM
  obtain ⟨-, hnm, -, ⟨cv, caps, hfc, -⟩, har⟩ := hoff.head C us _ a hM'
  have hf : ctx.find? C = some (.indInfo cv caps) := by rw [← hfind C hnm]; exact hfc
  -- the level count: official's final check of the key
  have hlvl : us.length = cv.levelParams.length :=
    hcon.2 _ (hoT.nested _ a hM') C us (SubOf.mkAppN (.refl _) _) _ hf
  -- the syntactic telescope
  obtain ⟨u, hu⟩ := hsort C cv caps hfc
  have hrs : cv.type.resultSort.isSome = true := by rw [hu]; rfl
  obtain ⟨hrsI, hpaI⟩ := resultSort_instantiateLevelParams (ks := cv.levelParams) (us := us) cv.type hrs
  have hpa : cv.type.piArity = ds.length + o.nIdx a := by
    simp only [nestArity, hf, piBinders_length, List.length_map] at har; exact har
  obtain ⟨ty, hty, -⟩ := instPisWith_of_le_piArity ds
    (cv.type.instantiateLevelParams cv.levelParams us) (by omega)
  have hstrip := stripPis_isSome_of_piArity ds.length cv.type (by omega)
  obtain ⟨s, hs⟩ := piBinders_sort_of_resultSort ty (resultSort_instPisWith ds _ ty hrsI hty)
  -- the walk's instantiated former is related to official's auxiliary former
  have hclf : (cv.type.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hcl.2 _ _ hf
  have hdf : (cv.type.instantiateLevelParams cv.levelParams us).deepOcc
      (fun n => ctx.names.contains n || isAux n) = false := by
    rw [deepOcc_instantiateLevelParams]; exact hfresh C cv caps hfc
  have hrefl : SRel ctx (sigmaOfMap ctx c isAux M) P [] (cv.type.instantiateLevelParams cv.levelParams us)
      (cv.type.instantiateLevelParams cv.levelParams us) :=
    srel_refl_deepFree _ (good_of_scoped _ 0 (Nat.zero_le _) (wscoped_of_hasFvar_false hclf) hdf) hdf
  have hds : Rel2 (SRel ctx (sigmaOfMap ctx c isAux M) P []) ds (ds.map (rbE ctx P)) :=
    Rel2.of_map fun d hd => srel_raw (σ := sigmaOfMap ctx c isAux M) hlv hso (hws d hd)
  obtain ⟨ty', hty', hrel⟩ := SRel.instPisWith hσ hds hrefl hty
  obtain ⟨hfo, hsorts⟩ := hoF.former C us _ a hM' cv caps hfc ty' hty'
  obtain ⟨hbs, hend⟩ := hrel.piBinders
  -- N3
  rw [hs] at hend
  have hs' := hend.sort_left
  have hn3 := hlev s ctx.sort (hsorts s hs')
  -- N2: official's former names no declared type
  have hno : ty'.nestOcc o.names 0 0 = false :=
    hcon.1 ty' hfo o.names fun n hn => hbefore n (List.contains_iff_mem.mpr hn)
  have hn2 : (ty.piBinders.1.any fun b => b.1.nestOcc ctx.names ctx.nP (ctx.hiAt P.length)) = false := by
    rw [List.any_eq_false]
    intro b hb hc
    have := Rel2.forall_left (P := fun b : Expr × BinderMeta =>
        (!b.1.nestOcc ctx.names ctx.nP (ctx.hiAt P.length)) = true)
      (Q := fun b' : Expr × BinderMeta => (!o.occ b'.1) = true)
      (fun b b' hbb' hb' => noOcc_of_srel hσ hbb' hb') hbs (fun b' hb' => by
        cases ho : o.occ b'.1
        · rfl
        · rw [nestOcc_of_piBinders ty' b' hb' ho] at hno; exact nomatch hno) b hb
    rw [hc] at this; exact nomatch this
  exact nestInstType_ok_of hf hlvl hstrip hty hs hn2 hn3

/-- **The frames' former checks, discharged** (`FrameSide` from the
freshness at the frames' constructors, `FrameFresh`): the instantiation's own
former check and its group-mates', at every frame, under the
typing-oracle contract and `LevelSim`. -/
theorem frameSide_of {c : Official.ElimCtx}
    {isAux : Name → Bool} {M : List (Expr × Name)} {T : Official.TypingOracle}
    (hσ : SigmaOk ctx (sigmaOfMap ctx c isAux M) o) (hlv : c.lvls = ctx.lps.map .param)
    (hoff : OffMap ctx c o isAux M) (hoT : OffTyped ctx c T M) (hoF : OffFormers ctx c T M)
    (hcon : TypingContract T c.find? ctx.find?) (hlev : LevelSim T)
    (hfind : ∀ n, ctx.names.contains n = false → c.find? n = ctx.find? n)
    (hbefore : ∀ n, o.names.contains n = true → c.find? n = none)
    (hfresh : ∀ J cv caps, c.find? J = some (.indInfo cv caps) →
      cv.type.deepOcc (fun n => ctx.names.contains n || isAux n) = false)
    (hsort : ∀ J cv caps, c.find? J = some (.indInfo cv caps) → ∃ u, cv.type.resultSort = some u)
    (hcl : NestCtxOk ctx)
    (hctors : ∀ prog act C us ds a, StepInv ctx (sigmaOfMap ctx c isAux M) c o prog →
      (sigmaOfMap ctx c isAux M).contAux prog ⟨C, us, ds⟩ = some a →
      ContKeyOk ctx isAux prog act C us ds → FrameFresh ctx prog act C us ds) :
    FrameSide ctx c o isAux M := by
  intro prog act C us ds a hI ha hk
  have hk' := hk
  obtain ⟨-, -, -, hsc, -, -, -, hws⟩ := hk'
  have hM : M.lookup (rbKey ctx prog ⟨C, us, ds⟩) = some a := ha
  have hins := nestInstType_of_key hσ hlv hoff hoT hoF hcon hlev hfind hbefore hfresh hsort hcl
    hI.1 hM hws
  refine ⟨hins, fun m hm => ?_, hctors prog act C us ds a hI ha hk⟩
  -- the group-mates, at the walk stack
  obtain ⟨⟨L0, hL0⟩, hds⟩ := nestWalkStack_facts (ctx := ctx) hsc
  generalize hwp : nestWalkStack ctx prog ds = wp at hL0 hds
  have hMw : M.lookup (Expr.mkAppN (.const C us) (ds.map (rbE ctx wp))) = some a := by
    have h2 : rbKey ctx prog ⟨C, us, ds⟩ = rbKey ctx wp ⟨C, us, ds⟩ := by
      conv => lhs; rw [hL0]
      exact rbKey_append hds
    rw [h2] at hM; exact hM
  obtain ⟨aJ, hJ⟩ := hoff.block C us _ a hMw m hm
  have hIw : StepInv ctx (sigmaOfMap ctx c isAux M) c o wp := by
    rw [← hwp]; exact stepInv_walkStack hI
  have hwsw : ∀ d ∈ ds, WShape ctx isAux wp d := fun d hd =>
    WShape.restack (P := prog) (Q := wp) (fun i hi => by
      rw [hL0, List.reverse_append, List.getElem?_append_left (by simpa using hi)])
      (fun _ _ => rfl) (hws d hd) (hds d hd)
  exact nestInstType_of_key hσ hlv hoff hoT hoF hcon hlev hfind hbefore hfresh hsort hcl
    hIw.1 (a := aJ) hJ hwsw

/-- **Official's formers of its final map, from the elimination**
(`OffFormers` from `OfficialTypesAt`; the first type's sort is the
block's). -/
theorem offFormers_of_elim {c : Official.ElimCtx} {G : Name → Bool}
    {decl : List Official.MemberDecl} {q : Nat} {st : Official.ElimSt} {T : Official.TypingOracle}
    (hH : EHyp c ctx.names G decl) (hE : EInv c ctx.names G decl q st) (hq : st.types.size ≤ q)
    (hinj : ∀ k k', c.auxName k = c.auxName k' → k = k')
    (htyA : Official.OfficialTypesAt st T (ctx.hiAt 0))
    (hs0 : ∀ t0, st.types.toList.head? = some t0 → t0.type.piBinders.2 = .sort ctx.sort) :
    OffFormers ctx c T st.aux where
  former J us Ds a hl cv caps hf ty hty := by
    obtain ⟨t, -, htm, -, I, J', us', ds', hk, -, -, -, raws, hcp, -⟩ :=
      hE.entry hH hq hinj (lookup_mem_lawful hl)
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_const_inj hk
    obtain ⟨cvJ, capsJ, hfJ, htyJ, -⟩ := hcp
    rw [hf] at hfJ; cases hfJ
    have hty' := Official.instPiParams_ok.mp htyJ
    rw [hty, Option.some.injEq] at hty'
    subst hty'
    refine ⟨htyA.2.2.1 t htm, fun s hs => ?_⟩
    obtain ⟨t0, ht0⟩ : ∃ t0, st.types.toList.head? = some t0 := by
      cases h : st.types.toList with
      | nil => rw [h] at htm; exact nomatch htm
      | cons t0 _ => exact ⟨t0, rfl⟩
    exact htyA.2.2.2 t htm t0 ht0 s ctx.sort hs (hs0 t0 ht0)

/-- **(A): OFFICIAL ACCEPTS ⇒ THE WALK NEVER REJECTS** (at the block's
canonical declaration and elimination context).  Let official accept the
block (`OfficialPosAcceptsAt`: its elimination ends with `st`, its
positivity loop accepts every constructor of the eliminated declaration;
`OfficialTypesAt`: its typing checks on it pass, as the oracle `T`
reports) on a stream official accepted (`OfficialStream`).  Then
`nestedBlockPositivity` succeeds or declines, at every fuel, under:
* the NAMED hypotheses about official's reduction and typing, which is
  not transcribed: `WhnfSim`, `InferSim`, `U4Typed`, `TypingContract`,
  `LevelSim`;
* FRESHNESS at the frames (`FrameFresh`, the sanctioned `FreshOccs`), and
  the members' M3 (`MemberSide`) — still open;
* the install's facts (`StoredEnv`, `CtxOk`) and the spec's fresh-name
  supply (`FreshSupply`). -/
theorem nestedBlockPositivity_of_official_accepts {ops : CheckerOps CheckM} {env : Env}
    {G : Name → Bool} {st : Official.ElimSt}
    {ctorss : List (List (ConstantVal × Nat))} {auxName : Nat → Name}
    {whnf : Nat → Expr → Except CheckError Expr}
    (hacc : Official.OfficialPosAcceptsAt (elimCtxOf ctx auxName) (declOf ctx ctorss) whnf
      (ctx.hiAt 0) st)
    {T : Official.TypingOracle} (htyA : Official.OfficialTypesAt st T (ctx.hiAt 0))
    (hos : OfficialStream ctx)
    (hfs : FreshSupply ctx G ctorss auxName) (hc : CtxOk ctx G ctorss) (hs : StoredEnv ctx)
    (hsim : WhnfSim ops env ctx (sigmaOfMap ctx (elimCtxOf ctx auxName) (finalAux st) st.aux) whnf)
    (hinf : InferSim ops env ctx (sigmaOfMap ctx (elimCtxOf ctx auxName) (finalAux st) st.aux) T)
    (hu4 : U4Typed ops env ctx (sigmaOfMap ctx (elimCtxOf ctx auxName) (finalAux st) st.aux) T)
    (hcon : TypingContract T (elimCtxOf ctx auxName).find? ctx.find?) (hlev : LevelSim T)
    (hctors : ∀ prog act C us ds a,
      StepInv ctx (sigmaOfMap ctx (elimCtxOf ctx auxName) (finalAux st) st.aux) (elimCtxOf ctx auxName)
        (st.oracle (elimCtxOf ctx auxName) whnf) prog →
      (sigmaOfMap ctx (elimCtxOf ctx auxName) (finalAux st) st.aux).contAux prog ⟨C, us, ds⟩ = some a →
      ContKeyOk ctx (finalAux st) prog act C us ds → FrameFresh ctx prog act C us ds)
    {holes : List Expr} (hholes : nestHoles ctx = some holes)
    (hdecl : ∀ cs ∈ ctorss, Official.DeclChecks ctx.names (ctx.lps.map .param) ctx.nP
      (cs.map (·.1.type)))
    (hside : ∀ cs ∈ ctorss, ∀ cc ∈ cs,
      ∀ crest, instPisWith ctx.params (nestAbstract ctx holes cc.1.type) = some crest →
        MemberSide ops env ctx cc.2 crest) :
    OkOr (fun _ => True) (nestedBlockPositivity ops env ctx ctorss) := by
  have hH := ehyp_of hfs hc
  have ⟨⟨fuelE, helim⟩, hacc'⟩ := hacc
  obtain ⟨q, hq, hE⟩ := EInv.elimNested hH helim
  have hfG := finalAux_G hH hE
  have henv := envFacts_of_stored hfG hs hos hfs (auxName := auxName)
  have hee := elimEnv_of_stored (auxName := auxName) hs hfs
  have hoff := offMap_of_elim hH hE hq hfs.inj henv hee hacc'
  have hσ := sigmaOk_of_elim (whnf := whnf) hH hE (declOk_of hc)
  -- the first member's type ends in the block's sort
  have hs0 : ∀ t0, st.types.toList.head? = some t0 → t0.type.piBinders.2 = .sort ctx.sort := by
    intro t0 ht0
    have hlen : 0 < (declOf ctx ctorss).length := by
      rw [declOf_length hc.len]; exact List.length_pos_iff.mpr hc.ne
    obtain ⟨t, ht, -, hty, -⟩ := hE.mems 0 hlen
    rw [List.head?_eq_getElem?] at ht0
    rw [ht0, Option.some.injEq] at ht
    subst ht
    obtain ⟨n, ns, hns⟩ := List.exists_cons_of_ne_nil hc.ne
    have hd0 : (declOf ctx ctorss)[0].type = formerOf ctx n := by
      simp only [declOf, List.getElem_map, List.getElem_zip]
      simp [hns]
    rw [hd0] at hty
    exact hc.sort0 n _ (by rw [hns]; rfl) hty
  have hbefore : ∀ n, (st.oracle (elimCtxOf ctx auxName) whnf).names.contains n = true →
      (elimCtxOf ctx auxName).find? n = none := by
    intro n hn
    rw [hσ.names, Bool.or_eq_true] at hn
    simp only [elimCtxOf]
    split
    · rfl
    · rename_i hnm
      rcases hn with h | h
      · exact absurd h hnm
      · exact hfs.envFresh n (hfG n h)
  have hfresh : ∀ J cv caps, (elimCtxOf ctx auxName).find? J = some (.indInfo cv caps) →
      cv.type.deepOcc (fun n => ctx.names.contains n || finalAux st n) = false := by
    intro J cv caps h
    have hn := elimCtxOf_ind J cv caps h
    have h' : ctx.find? J = some (.indInfo cv caps) := by
      rw [← elimCtxOf_find (auxName := auxName) J hn]; exact h
    exact deepOcc_mono (fun m hm => by
      rw [Bool.or_eq_true] at hm ⊢; exact hm.imp id (hfG m)) _
      (deepOcc_or (hs.formerFresh J cv caps h' hn) (hfs.formersFresh J cv caps h'))
  exact nestedBlockPositivity_of_frameSide hacc hos hfs hc hs hsim htyA hinf hu4
    (frameSide_of (c := elimCtxOf ctx auxName) hσ rfl hoff (offTyped_of_elim hH hE hq hfs.inj htyA)
      (offFormers_of_elim hH hE hq hfs.inj htyA hs0) hcon hlev henv.find hbefore hfresh hee.sortEnd
      hs.closed hctors) hholes hdecl hside

end Side

end ConLeche
