module

public import ConLeche.Verify.Cached.PushChain

public section

/-!
# The checker's ι reading rule, as a fact about the stored recursors (task #622)

`blockReadsOk` (`ConLeche/Kernel/Inductives/IotaRead.lean`) accepts a block when every rule of
every recursor it installs reads (`ruleReadsB`).  Here:

* `RecReads find? ci`: the fact, per stored constant;
* `RecReads.mono`: it uses the lookups only where they answer, so it survives every extension of
  the environment that keeps the answers (`PushChain.find?_some`);
* `blockReadsOk_reads`: an accepting `blockReadsOk` gives it at every recursor of the block.
-/

namespace ConLeche

/-- **A stored recursor's rules read** (`ruleReadsB`) at the lookups `find?`; vacuous at any
other constant. -/
@[expose] def RecReads (find? : Name → Option ConstantInfo) (ci : ConstantInfo) : Prop :=
  ∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules →
    ∀ i rl, rules[i]? = some rl → ruleReadsB find? cv mI rP i rl = true

theorem listRel_mono {α β : Type} {r r' : α → β → Bool} (hr : ∀ a b, r a b = true → r' a b = true) :
    ∀ {as : List α} {bs : List β}, listRel r as bs = true → listRel r' as bs = true
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [listRel, Bool.and_eq_true] at h ⊢
    exact ⟨hr a b h.1, listRel_mono hr h.2⟩
  | [], _ :: _, h => by simp [listRel] at h
  | _ :: _, [], h => by simp [listRel] at h

section Mono

variable {f g : Name → Option ConstantInfo} (hfg : ∀ n c, f n = some c → g n = some c)
include hfg

theorem annWitness_mono {D : Expr} (h : annWitness f D = true) : annWitness g D = true := by
  unfold annWitness at h ⊢
  split at h
  · next n =>
    cases hn : f (n.str "missing") with
    | none => rw [hn] at h; exact absurd h (by simp)
    | some c => rw [hn] at h; rw [hfg _ c hn]; exact h
  · exact absurd h (by simp)

theorem annIdent_mono {n : Name} {a : Nat} (h : annIdent f n a = true) :
    annIdent g n a = true := by
  unfold annIdent at h ⊢
  cases hn : f n with
  | none => rw [hn] at h; exact absurd h (by simp)
  | some c =>
    rw [hn] at h; rw [hfg n c hn]
    cases c with
    | defnInfo cv v hint =>
      simp only at h ⊢
      unfold annIdentVal at h ⊢
      split at h
      · exact h
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
        exact ⟨h.1, h.2.imp id (annWitness_mono hfg)⟩
      · exact absurd h (by simp)
    | _ => exact h

theorem annEq_mono {s c : Expr} (h : annEq f s c = true) : annEq g s c = true := by
  revert h
  fun_induction annEq f s c with
  | case1 n l a b ih =>
    intro h
    rw [annEq]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with h | ⟨⟨hn, hi⟩, hr⟩
    · exact .inl h
    · exact .inr ⟨⟨hn, annIdent_mono hfg hi⟩, ih hr⟩
  | case2 n l a ih =>
    intro h
    rw [annEq]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with h | ⟨⟨hn, hi⟩, hr⟩
    · exact .inl h
    · exact .inr ⟨⟨hn, annIdent_mono hfg hi⟩, ih hr⟩
  | case3 c h1 h2 =>
    intro h
    rw [annEq]
    · exact h
    all_goals assumption

theorem paramsAnnEq_mono {cvj : ConstantVal} {cnP : Nat} {cv : ConstantVal} {rl : RecRule}
    (h : paramsAnnEq f cvj cnP cv rl = true) : paramsAnnEq g cvj cnP cv rl = true := by
  unfold paramsAnnEq at h ⊢
  split at h
  · exact listRel_mono (fun _ _ => annEq_mono hfg) h
  · exact absurd h (by simp)

theorem iotaPartsRel_mono {cvj : ConstantVal} {cnP : Nat} {cv : ConstantVal} {rl : RecRule}
    {p' p : IotaParts} (h : iotaPartsRel f cvj cnP cv rl p' p = true) :
    iotaPartsRel g cvj cnP cv rl p' p = true := by
  unfold iotaPartsRel at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  obtain ⟨h1, h2 | ⟨⟨h3, h4⟩, h5⟩⟩ := h
  · exact ⟨h1, .inl h2⟩
  · exact ⟨h1, .inr ⟨⟨h3, paramsAnnEq_mono hfg h4⟩,
      listRel_mono (fun _ _ => annEq_mono hfg) h5⟩⟩

theorem ruleReadsB_mono {cv : ConstantVal} {mI rP i : Nat} {rl : RecRule}
    (h : ruleReadsB f cv mI rP i rl = true) : ruleReadsB g cv mI rP i rl = true := by
  unfold ruleReadsB at h ⊢
  split at h
  · next p' cvj cnP nF T hp' hc =>
    rw [hp', hfg _ _ hc]
    simp only
    split at h
    · exact iotaPartsRel_mono hfg h
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem RecReads.mono {ci : ConstantInfo} (h : RecReads f ci) : RecReads g ci :=
  fun cv mI rP isK rules hci i rl hrl => ruleReadsB_mono hfg (h cv mI rP isK rules hci i rl hrl)

end Mono

/-- `forM` in `Except` accepts only where every element does. -/
theorem forM_except_ok {α : Type} {f : α → Except CheckError Unit} :
    ∀ {l : List α}, l.forM f = .ok () → ∀ a ∈ l, f a = .ok ()
  | [], _, a, ha => nomatch ha
  | x :: l, h, a, ha => by
    simp only [List.forM] at h
    cases hx : f x with
    | error e => rw [hx] at h; exact nomatch h
    | ok u =>
      rw [hx] at h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hx
      · exact forM_except_ok h a ha

/-- **An accepting `recReadsOk` reads**. -/
theorem recReadsOk_reads {find? : Name → Option ConstantInfo} {ci : ConstantInfo}
    (h : recReadsOk find? ci = .ok ()) : RecReads find? ci := by
  intro cv mI rP isK rules hci i rl hrl
  subst hci
  have := forM_except_ok h (rl, i) (List.mem_zipIdx_iff_getElem?.mpr (by simpa using hrl))
  simp only at this
  by_cases hb : ruleReadsB find? cv mI rP i rl = true
  · exact hb
  · rw [ite_eq_right (by simpa using hb)] at this
    exact nomatch this

/-- **An accepting `blockReadsOk` reads at every recursor the block installs**. -/
theorem blockReadsOk_reads {find? : Name → Option ConstantInfo} {p : BlockShape}
    (h : blockReadsOk find? p = .ok ()) : ∀ ci ∈ blockRecs p p.recs, RecReads find? ci :=
  fun ci hci => recReadsOk_reads (forM_except_ok h ci hci)

/-- A lookup the chain's start answers, its end answers alike. -/
theorem PushChain.find?_some {env : Env} {fe : FEnv} (h : Cached.PushChain env fe) {n : Name}
    {c : ConstantInfo} (hn : env.find? n = some c) : fe.env.find? n = some c := by
  obtain ⟨new, hnew, -, hfresh⟩ := h.2.1
  unfold Env.find? at hn ⊢
  rw [hnew, List.find?_append]
  cases hc : new.find? (·.name == n) with
  | none => simpa using hn
  | some c' =>
    have hm := List.mem_of_find?_eq_some hc
    have hname := List.find?_some hc
    simp only [beq_iff_eq] at hname
    have := hfresh c' hm
    rw [hname] at this
    unfold Env.find? at this
    rw [hn] at this
    exact nomatch this

end ConLeche

namespace ConLeche

/-- **A rule's ι equation through its constructor, taken apart.** -/
theorem iotaEqAt_inv {cvj : ConstantVal} {cnP : Nat} {cv : ConstantVal} {mI rP : Nat}
    {rl : RecRule} {e : Expr} (h : iotaEqAt cvj cnP cv mI rP rl = some e) :
    ∃ (pre idx pd fd : List Expr) (rest body ctorBody concl : Expr) (u : Level),
      cv.type.stripPis rP = some (pre, rest) ∧
      rest.stripPis (mI - rP + 1) = some (idx, body) ∧
      motiveLevel? pre (mI - rP) body = some u ∧
      (cvj.type.instantiateLevelParams cvj.levelParams
        (rl.ctorLevels cvj.levelParams)).stripPis cnP = some (pd, ctorBody) ∧
      (ctorBody.instantiateLift (rl.iotaParams rP cnP).reverse).stripPis rl.nfields
        = some (fd, concl) ∧
      (rl.iotaParams rP cnP).length = cnP ∧ rP ≤ mI ∧
      (concl.getAppArgs.drop cnP).length = mI - rP ∧
      e = iotaEqMk cv rP (mI - rP) pre body u rl
        ⟨fd, concl.getAppArgs.drop cnP, rl.ctorLevels cvj.levelParams, rl.iotaParams rP cnP⟩ := by
  unfold iotaEqAt iotaFrame iotaPartsAt at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨pre, doms, body, u⟩, ⟨⟨pre', rest⟩, hpre, ⟨⟨idx, body'⟩, hbody, ⟨u', hu, he1⟩⟩⟩, h⟩ := h
  simp only [Prod.mk.injEq] at he1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := he1
  obtain ⟨pt, ⟨⟨pd, ctorBody⟩, hcb, ⟨⟨fd, concl⟩, hfd, ⟨_, hg, hpt⟩⟩⟩, rfl⟩ := h
  simp only [guard] at hg
  split at hg
  · rename_i hg'
    subst hpt
    exact ⟨_, _, pd, fd, rest, _, ctorBody, concl, _, hpre, hbody, hu, hcb, hfd,
      hg'.1, hg'.2.1, hg'.2.2, rfl⟩
  · exact nomatch hg

end ConLeche

namespace ConLeche

theorem annIdentVal_one_inv {f : Name → Option ConstantInfo} {ps : List Name} {v : Expr}
    (h : annIdentVal f ps 1 v = true) : ∃ p, ps = [p] ∧ v = .lam (.sort (.param p)) (.bvar 0) := by
  generalize ha : 1 = a at h
  revert h
  fun_cases annIdentVal f ps a v <;> intro h <;> simp_all

theorem annIdentVal_two_inv {f : Name → Option ConstantInfo} {ps : List Name} {v : Expr}
    (h : annIdentVal f ps 2 v = true) : ∃ p D, ps = [p] ∧
      v = .lam (.sort (.param p)) (.lam D (.bvar 1)) ∧ (D = .bvar 0 ∨ annWitness f D = true) := by
  generalize ha : 2 = a at h
  revert h
  fun_cases annIdentVal f ps a v <;> intro h <;> simp_all

theorem annIdent_inv {f : Name → Option ConstantInfo} {n : Name} {a : Nat}
    (h : annIdent f n a = true) : ∃ cv v hint, f n = some (.defnInfo cv v hint) ∧
      annIdentVal f cv.levelParams a v = true := by
  unfold annIdent at h
  cases hn : f n with
  | none => rw [hn] at h; exact absurd h (by simp)
  | some c =>
    rw [hn] at h
    cases c with
    | defnInfo cv v hint => exact ⟨cv, v, hint, rfl, h⟩
    | _ => exact absurd h (by simp)

theorem annWitness_inv {f : Name → Option ConstantInfo} {D : Expr} (h : annWitness f D = true) :
    ∃ n c, D = .const n [] ∧ f (n.str "missing") = some c ∧ c.toConstantVal.type = D ∧
      c.toConstantVal.levelParams = [] := by
  unfold annWitness at h
  split at h
  · next n =>
    cases hn : f (n.str "missing") with
    | none => rw [hn] at h; exact absurd h (by simp)
    | some c =>
      rw [hn] at h
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
      exact ⟨n, c, rfl, hn, h.1, h.2⟩
  · exact absurd h (by simp)

end ConLeche

namespace ConLeche

/-- **The statement's ι equation, taken apart.** -/
theorem iotaEqOf_inv {cv : ConstantVal} {mI rP i : Nat} {rl : RecRule} {e : Expr}
    (h : iotaEqOf cv mI rP i rl = some e) :
    ∃ pre doms body u p', iotaFrame cv mI rP = some (pre, doms, body, u) ∧
      iotaPartsOf cv mI rP i rl = some p' ∧ e = iotaEqMk cv rP (mI - rP) pre body u rl p' := by
  unfold iotaEqOf at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨pre, doms, body, u⟩, hf, p', hp, rfl⟩ := h
  exact ⟨pre, doms, body, u, p', hf, hp, rfl⟩

/-- **The proofs' ι equation, from its parts.** -/
theorem iotaEqAt_of {cvj : ConstantVal} {cnP : Nat} {cv : ConstantVal} {mI rP : Nat}
    {rl : RecRule} {pre doms : List Expr} {body : Expr} {u : Level} {p : IotaParts}
    (hf : iotaFrame cv mI rP = some (pre, doms, body, u))
    (hp : iotaPartsAt cvj cnP mI rP rl = some p) :
    iotaEqAt cvj cnP cv mI rP rl = some (iotaEqMk cv rP (mI - rP) pre body u rl p) := by
  unfold iotaEqAt
  simp only [hf, hp, bind, Option.bind_some, pure]

/-- **Equations of parts with the same indices, levels and parameters** are telescopes over one
body, through their fields' domains. -/
theorem iotaEqMk_fields (cv : ConstantVal) (rP nIdx : Nat) (pre : List Expr) (body : Expr)
    (u : Level) (rl : RecRule) {p' p : IotaParts} (hi : p'.idx = p.idx) (hu : p'.us = p.us)
    (hp : p'.params = p.params) :
    ∃ B, iotaEqMk cv rP nIdx pre body u rl p' = (pre ++ p'.fieldDoms).foldr .forallE B ∧
      iotaEqMk cv rP nIdx pre body u rl p = (pre ++ p.fieldDoms).foldr .forallE B := by
  obtain ⟨fd', idx', us', ps'⟩ := p'
  obtain ⟨fd, idx, us, ps⟩ := p
  simp only at hi hu hp
  subst hi hu hp
  exact ⟨_, rfl, rfl⟩

/-- The statement's reading reads no firing mode. -/
theorem iotaEqOf_unfired (cv : ConstantVal) (mI rP i : Nat) (rl : RecRule) :
    iotaEqOf cv mI rP i { rl with fire := .plain } = iotaEqOf cv mI rP i rl := rfl

/-- **A rule that reads, taken apart.** -/
theorem ruleReadsB_inv {f : Name → Option ConstantInfo} {cv : ConstantVal} {mI rP i : Nat}
    {rl : RecRule} (h : ruleReadsB f cv mI rP i rl = true) :
    ∃ p' cvj cnP nF T p, iotaPartsOf cv mI rP i rl = some p' ∧
      f rl.ctor = some (.ctorInfo cvj cnP nF T) ∧ iotaPartsAt cvj cnP mI rP rl = some p ∧
      p'.idx = p.idx ∧ p'.us = p.us ∧ p'.params = p.params ∧
      (listRel Expr.lvlEq p'.fieldDoms p.fieldDoms = true ∨
        (rl.fire = .plain ∧ paramsAnnEq f cvj cnP cv rl = true ∧
          listRel (annEq f) p'.fieldDoms p.fieldDoms = true)) := by
  unfold ruleReadsB at h
  split at h
  · next p' cvj cnP nF T hp' hc =>
    split at h
    · next p hp =>
      unfold iotaPartsRel at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      exact ⟨p', cvj, cnP, nF, T, p, hp', hc, hp, h1, h2, h3, h4.imp id fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **A plain rule's parameters, taken apart.** -/
theorem paramsAnnEq_inv {f : Name → Option ConstantInfo} {cvj : ConstantVal} {cnP : Nat}
    {cv : ConstantVal} {rl : RecRule} (h : paramsAnnEq f cvj cnP cv rl = true) :
    ∃ rd r pd c, cv.type.stripPis cnP = some (rd, r) ∧
      (cvj.type.instantiateLevelParams cvj.levelParams (rl.ctorLevels cvj.levelParams)).stripPis
        cnP = some (pd, c) ∧ listRel (annEq f) rd pd = true := by
  unfold paramsAnnEq at h
  split at h
  · next rd r pd c h1 h2 => exact ⟨rd, r, pd, c, h1, h2, h⟩
  · exact absurd h (by simp)

theorem listRel_length {α β : Type} {r : α → β → Bool} :
    ∀ {as : List α} {bs : List β}, listRel r as bs = true → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [listRel, Bool.and_eq_true] at h
    simp [listRel_length h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [listRel] at h

theorem isEquivList_length : ∀ {us vs : List Level}, Level.isEquivList us vs = some true →
    us.length = vs.length
  | [], [], _ => rfl
  | u :: us, v :: vs, h => by
    simp only [Level.isEquivList, bind, Option.bind_eq_some_iff] at h
    obtain ⟨b, -, h⟩ := h
    cases b with
    | true => simp [isEquivList_length h]
    | false => simp at h
  | [], _ :: _, h | _ :: _, [], h => by simp [Level.isEquivList] at h

end ConLeche

namespace ConLeche

/-- **A rule's parts through its constructor, taken apart.** -/
theorem iotaPartsAt_inv {cvj : ConstantVal} {cnP mI rP : Nat} {rl : RecRule} {p : IotaParts}
    (h : iotaPartsAt cvj cnP mI rP rl = some p) :
    ∃ pd ctorBody concl, (cvj.type.instantiateLevelParams cvj.levelParams
        (rl.ctorLevels cvj.levelParams)).stripPis cnP = some (pd, ctorBody) ∧
      (ctorBody.instantiateLift (rl.iotaParams rP cnP).reverse).stripPis rl.nfields
        = some (p.fieldDoms, concl) ∧
      (rl.iotaParams rP cnP).length = cnP ∧ rP ≤ mI ∧ p.params = rl.iotaParams rP cnP := by
  unfold iotaPartsAt at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨pd, ctorBody⟩, hcb, ⟨fd, concl⟩, hfd, ⟨_, hg, rfl⟩⟩ := h
  simp only [guard] at hg
  split at hg
  · rename_i hg'
    exact ⟨pd, ctorBody, concl, hcb, hfd, hg'.1, hg'.2.1, rfl⟩
  · exact nomatch hg

/-- **The proofs' ι equation, with its sides named**: a telescope over `@Eq.{u} ty lhs rhs`, and
the statement's, of parts with the same indices, levels and parameters, over the same. -/
theorem iotaEqMk_sides (cv : ConstantVal) (rP nIdx : Nat) (pre : List Expr) (body : Expr)
    (u : Level) (rl : RecRule) {p' p : IotaParts} (hi : p'.idx = p.idx) (hu : p'.us = p.us)
    (hp : p'.params = p.params) :
    ∃ ty lhs rhs : Expr,
      iotaEqMk cv rP nIdx pre body u rl p' = (pre ++ p'.fieldDoms).foldr .forallE
        (.app (.app (.app (.const eqName [u]) ty) lhs) rhs) ∧
      iotaEqMk cv rP nIdx pre body u rl p = (pre ++ p.fieldDoms).foldr .forallE
        (.app (.app (.app (.const eqName [u]) ty) lhs) rhs) := by
  obtain ⟨fd', idx', us', ps'⟩ := p'
  obtain ⟨fd, idx, us, ps⟩ := p
  simp only at hi hu hp
  subst hi hu hp
  exact ⟨_, _, _, rfl, rfl⟩

theorem listRel_forall {α β : Type} {r : α → β → Bool} {P : α → Prop} {Q : β → Prop}
    (hPQ : ∀ a b, r a b = true → Q b → P a) :
    ∀ {as : List α} {bs : List β}, listRel r as bs = true → (∀ b ∈ bs, Q b) → ∀ a ∈ as, P a
  | [], [], _, _, a, ha => nomatch ha
  | a :: as, b :: bs, h, hq, x, hx => by
    simp only [listRel, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hPQ _ _ h.1 (hq b List.mem_cons_self)
    · exact listRel_forall hPQ h.2 (fun b hb => hq b (List.mem_cons_of_mem _ hb)) x hx
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => by simp [listRel] at h

end ConLeche

namespace ConLeche

open BasisDSL

set_option maxRecDepth 4000 in
/-- **`Quot.lift`'s rule reads**, at any level-parameter names: its pinned type's minor premise
`f : α → β` gives its field, its major `Quot α r` the constructor's parameters. -/
theorem quotLift_reads (a b c : Name) {f : Name → Option ConstantInfo}
    (hf : f quotMkName = some (quotMkA.atLps [c])) :
    match quotLiftA.atLps [a, b] with
    | .recInfo cv mI rP _ [rl] => ruleReadsB f cv mI rP 0 rl = true
    | _ => False := by
  simp (config := {decide := true}) [ruleReadsB, ruleAt, hf, iotaPartsOf, iotaPartsAt, iotaFrame,
    iotaPartsRel, quotMkA, quotLiftA, ConstantInfo.atLps, ConstantVal.atLps, RecRuleFire.atLps,
    RecRule.ctorLevels, RecRule.iotaParams, minorsOf, Expr.piTele, motiveLevel?, listRel, piI, pi,
    lm, srt, bv, cnst, ap2, ap3, piA, quotRel, quotLiftF, quotLiftH, u, v, Expr.instantiateLevelParams,
    Expr.stripPis, Expr.getAppFn, Expr.getAppArgs, Expr.piResult, Expr.liftLooseBVars,
    Expr.instantiateLift, Expr.dropVars, prop, Level.subst, Level.subst.go,
    uN, vN, BasisDSL.bn, List.range_succ, List.filter_nil, List.range_zero,
    ConstantInfo.toConstantVal, guard, Option.bind]

set_option maxRecDepth 4000 in
/-- **`Quot.ind`'s rule reads**, at any level-parameter names. -/
theorem quotInd_reads (a c : Name) {f : Name → Option ConstantInfo}
    (hf : f quotMkName = some (quotMkA.atLps [c])) :
    match quotIndA.atLps [a] with
    | .recInfo cv mI rP _ [rl] => ruleReadsB f cv mI rP 0 rl = true
    | _ => False := by
  simp (config := {decide := true}) [ruleReadsB, ruleAt, hf, iotaPartsOf, iotaPartsAt, iotaFrame,
    iotaPartsRel, quotMkA, quotIndA, ConstantInfo.atLps, ConstantVal.atLps, RecRuleFire.atLps,
    RecRule.ctorLevels, RecRule.iotaParams, minorsOf, Expr.piTele, motiveLevel?, listRel, piI, pi,
    lm, srt, bv, cnst, ap2, ap3, piA, quotRel, quotIndMotive, quotIndMk, u, Expr.instantiateLevelParams,
    Expr.stripPis, Expr.getAppFn, Expr.getAppArgs, Expr.piResult, Expr.liftLooseBVars,
    Expr.instantiateLift, Expr.dropVars, prop, Level.subst, Level.subst.go,
    uN, BasisDSL.bn, List.range_succ, List.filter_nil, List.range_zero,
    ConstantInfo.toConstantVal, guard, Option.bind]

end ConLeche
