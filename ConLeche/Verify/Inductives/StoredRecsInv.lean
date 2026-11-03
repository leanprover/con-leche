module

public import ConLeche.Kernel.Inductives.BlockTail
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Inductives.BlockWF

public section

/-!
# The stored recursors' install list (task #431)

`storedOut` — what the install conses once the stored recursors agree
with the generated ones — keeps the generated family's names, level
parameters, majors and length; only the types and the right-hand sides
are the records'.
-/

namespace ConLeche

theorem storedOut_length {recs : List RecShape}
    {out : List (ConstantVal × TargetMajor × List Expr)} (h : out.length = recs.length) :
    (storedOut recs out).length = out.length := by
  simp [storedOut, List.length_zipWith, h]

theorem storedOut_getElem? {recs : List RecShape}
    {out : List (ConstantVal × TargetMajor × List Expr)} {j : Nat}
    {o : ConstantVal × TargetMajor × List Expr} (h : (storedOut recs out)[j]? = some o) :
    ∃ rc g, recs[j]? = some rc ∧ out[j]? = some g ∧
      o = ({ g.1 with type := rc.cvR.type }, g.2.1, rc.rules.map (·.rhs)) := by
  simp only [storedOut, List.getElem?_zipWith] at h
  cases hr : recs[j]? with
  | none => rw [hr] at h; simp at h
  | some rc =>
    cases hg : out[j]? with
    | none => rw [hr, hg] at h; simp at h
    | some g =>
      rw [hr, hg] at h
      exact ⟨rc, g, rfl, rfl, (Option.some.inj h).symm⟩

theorem storedOut_getElem?_of {recs : List RecShape}
    {out : List (ConstantVal × TargetMajor × List Expr)} {j : Nat} {rc : RecShape}
    {g : ConstantVal × TargetMajor × List Expr} (hr : recs[j]? = some rc)
    (hg : out[j]? = some g) :
    (storedOut recs out)[j]? = some ({ g.1 with type := rc.cvR.type }, g.2.1,
      rc.rules.map (·.rhs)) := by
  simp only [storedOut, List.getElem?_zipWith, hr, hg]

theorem mem_storedOut {recs : List RecShape}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    {t : ConstantVal × TargetMajor × List Expr} (h : t ∈ storedOut recs out) :
    ∃ g ∈ out, t.1.name = g.1.name ∧ t.1.levelParams = g.1.levelParams ∧ t.2.1 = g.2.1 := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem h
  obtain ⟨rc, g, -, hg, rfl⟩ := storedOut_getElem? hj
  exact ⟨g, List.mem_of_getElem? hg, rfl, rfl, rfl⟩

theorem storedOut_map_name {recs : List RecShape}
    {out : List (ConstantVal × TargetMajor × List Expr)} (h : out.length = recs.length) :
    (storedOut recs out).map (·.1.name) = out.map (·.1.name) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map]
  cases hg : out[j]? with
  | none =>
    have : (storedOut recs out)[j]? = none := by
      rw [List.getElem?_eq_none_iff, storedOut_length h]
      exact List.getElem?_eq_none_iff.mp hg
    rw [this]
  | some g =>
    obtain ⟨rc, hr⟩ : ∃ rc, recs[j]? = some rc := by
      have hj := (List.getElem?_eq_some_iff.mp hg).1
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [storedOut_getElem?_of hr hg]
    rfl

/-! ## Names, and the stored major's reading -/

/-- A recursor cons at the same names finds the same names (the rule-less
cons of any list carrying them). -/
theorem isSome_consBlockRecsT_bare {f : Name → Option ConstantInfo} {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)}
      {l : List (ConstantVal × Nat)} {envA envB : Env},
      (∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true) →
      out.map (·.1.name) = l.map (·.1.name) →
      ∀ n, ((consBlockRecsT f q m out envA).find? n).isSome = true →
        ((consBlockRecsBare q m l envB).find? n).isSome = true
  | _, [], [], _, _, hf, _, n, h => hf n h
  | _, [], _ :: _, _, _, _, hn, _, _ => by simp at hn
  | _, _ :: _, [], _, _, _, hn, _, _ => by simp at hn
  | m, (cv, M, rhss) :: rest, (cvB, k) :: restB, envA, envB, hf, hn, n, h => by
    simp only [List.map_cons, List.cons.injEq] at hn
    simp only [consBlockRecsT] at h
    simp only [consBlockRecsBare]
    exact isSome_consBlockRecsT_bare (find?_cons_mono (c := .recInfo cv _ _ _)
      (c' := .recInfo cvB _ _ []) hn.1 hf) hn.2 n h

/-- Two rule-less recursor conses at the same names find the same names. -/
theorem isSome_consBlockRecsBare_bare {q : BlockShape} :
    ∀ {m : Nat} {l l' : List (ConstantVal × Nat)} {envA envB : Env},
      (∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true) →
      l.map (·.1.name) = l'.map (·.1.name) →
      ∀ n, ((consBlockRecsBare q m l envA).find? n).isSome = true →
        ((consBlockRecsBare q m l' envB).find? n).isSome = true
  | _, [], [], _, _, hf, _, n, h => hf n h
  | _, [], _ :: _, _, _, _, hn, _, _ => by simp at hn
  | _, _ :: _, [], _, _, _, hn, _, _ => by simp at hn
  | m, (cv, k) :: rest, (cvB, kB) :: restB, envA, envB, hf, hn, n, h => by
    simp only [List.map_cons, List.cons.injEq] at hn
    simp only [consBlockRecsBare] at h ⊢
    exact isSome_consBlockRecsBare_bare (find?_cons_mono (c := .recInfo cv _ _ [])
      (c' := .recInfo cvB _ _ []) hn.1 hf) hn.2 n h

/-- `storedNestedOk` at a `.nested` firing: the stored type's major domain
is the container at the firing data. -/
theorem storedNestedOk_read {ty : Expr} {mI rP : Nat} {lvls : List Level} {pins : List Expr}
    (h : storedNestedOk ty mI rP (.nested lvls pins) = true) :
    ∃ pre dom body D,
      ty.stripPis mI = some (pre, .forallE dom body) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i)) := by
  cases hs : ty.stripPis mI with
  | none => simp [storedNestedOk, hs] at h
  | some pr =>
    obtain ⟨pre, b⟩ := pr
    cases b with
    | forallE dom body =>
      simp only [storedNestedOk, hs] at h
      cases hfn : dom.getAppFn with
      | const D us =>
        simp only [hfn, Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨pre, dom, body, D, rfl, by rw [hfn, h.1], h.2⟩
      | _ => simp [hfn] at h
    | _ => simp [storedNestedOk, hs] at h


/-! ## The stored check, inverted (at an `Except` run) -/

section Inv

variable {ops : CheckerOps CheckM} {w : StructWalkers} {fe : FEnv}

theorem storedRulesShape_inv {rec : Name} :
    ∀ {rs : List RecRule} {cs : List (ConstantVal × Nat)},
      storedRulesShape (m := CheckM) rec rs cs = .ok () →
      rs.length = cs.length ∧ ∀ (i : Nat) (r : RecRule) (c : ConstantVal × Nat),
        rs[i]? = some r → cs[i]? = some c → r.ctor = c.1.name ∧ r.nfields = c.2
  | [], [], _ => ⟨rfl, fun i r c h => by simp at h⟩
  | [], _ :: _, h => by simp [storedRulesShape, throw, throwThe, MonadExceptOf.throw] at h
  | _ :: _, [], h => by simp [storedRulesShape, throw, throwThe, MonadExceptOf.throw] at h
  | r :: rs, c :: cs, h => by
    unfold storedRulesShape at h
    by_cases hc : (r.ctor == c.1.name && r.nfields == c.2) = true
    · simp only [hc, ↓reduceIte] at h
      obtain ⟨hl, hall⟩ := storedRulesShape_inv h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      refine ⟨by simp [hl], fun i r' c' hr hc' => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hc'
        subst hr hc'
        exact hc
      | succ i => exact hall i r' c' (by simpa using hr) (by simpa using hc')
    · simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem storedRulesCheck_inv {rec : Name} {lps : List Name} :
    ∀ {rs : List RecRule} {gs : List Expr},
      storedRulesCheck ops w fe rec lps rs gs = .ok () →
      rs.length = gs.length ∧ ∀ (i : Nat) (r : RecRule) (gi : Expr),
        rs[i]? = some r → gs[i]? = some gi →
        r.rhs = gi ∨ ruleAgree ops w fe rec r.ctor lps r.rhs gi = .ok ()
  | [], [], _ => ⟨rfl, fun i r gi h => by simp at h⟩
  | [], _ :: _, h => by simp [storedRulesCheck, throw, throwThe, MonadExceptOf.throw] at h
  | _ :: _, [], h => by simp [storedRulesCheck, throw, throwThe, MonadExceptOf.throw] at h
  | r :: rs, g :: gs, h => by
    unfold storedRulesCheck at h
    have key : (r.rhs = g ∨ ruleAgree ops w fe rec r.ctor lps r.rhs g = .ok ()) ∧
        storedRulesCheck ops w fe rec lps rs gs = .ok () := by
      by_cases he : (r.rhs == g) = true
      · simp only [he, ↓reduceIte] at h
        exact ⟨Or.inl (beq_iff_eq.mp he), by simpa [pure, Except.pure, bind, Except.bind] using h⟩
      · simp only [he, ↓reduceIte, Bool.false_eq_true] at h
        obtain ⟨u, hu, h⟩ := exceptBind_ok h
        exact ⟨Or.inr (by cases u; exact hu), h⟩
    obtain ⟨hhead, h⟩ := key
    obtain ⟨hl, hall⟩ := storedRulesCheck_inv h
    refine ⟨by simp [hl], fun i r' gi hr hg => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hg
      subst hr hg
      exact hhead
    | succ i => exact hall i r' gi (by simpa using hr) (by simpa using hg)

theorem storedRecCompare_inv {rc : RecShape} {g : ConstantVal × TargetMajor × List Expr}
    (h : storedRecCompare ops w fe rc g = .ok ()) :
    (rc.cvR.type = g.1.type ∨
      recTyCheck ops w fe g.1.name g.1.levelParams (rc.mI + 1) rc.cvR.type g.1.type = .ok ()) ∧
    storedRulesCheck ops w fe g.1.name g.1.levelParams rc.rules g.2.2 = .ok () := by
  unfold storedRecCompare at h
  by_cases he : (rc.cvR.type == g.1.type) = true
  · simp only [he, ↓reduceIte] at h
    exact ⟨Or.inl (beq_iff_eq.mp he), by simpa [pure, Except.pure, bind, Except.bind] using h⟩
  · simp only [he, ↓reduceIte, Bool.false_eq_true] at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    exact ⟨Or.inr (by cases u; exact hu), h⟩

theorem storedRecCheck_inv {rc : RecShape} {g : ConstantVal × TargetMajor × List Expr}
    (h : storedRecCheck ops w fe rc g = .ok ()) :
    storedRulesShape (m := CheckM) rc.cvR.name rc.rules g.2.1.ctors = .ok () ∧
    storedNestedOk rc.cvR.type rc.mI rc.rP (storedFireOf g.2.1 rc.rP) = true ∧
    storedRecCompare ops w fe rc g = .ok () := by
  unfold storedRecCheck at h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  cases u
  by_cases hn : storedNestedOk rc.cvR.type rc.mI rc.rP (storedFireOf g.2.1 rc.rP) = true
  · simp only [hn, ↓reduceIte] at h
    exact ⟨hu, hn, by simpa [pure, Except.pure, bind, Except.bind] using h⟩
  · simp [hn, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem storedRecsCheck_inv :
    ∀ {recs : List RecShape} {out : List (ConstantVal × TargetMajor × List Expr)},
      storedRecsCheck ops w fe recs out = .ok () →
      recs.length = out.length ∧ ∀ (j : Nat) (rc : RecShape)
        (g : ConstantVal × TargetMajor × List Expr), recs[j]? = some rc → out[j]? = some g →
        storedRecCheck ops w fe rc g = .ok ()
  | [], [], _ => ⟨rfl, fun j rc g h => by simp at h⟩
  | [], _ :: _, h => by simp [storedRecsCheck, throw, throwThe, MonadExceptOf.throw] at h
  | _ :: _, [], h => by simp [storedRecsCheck, throw, throwThe, MonadExceptOf.throw] at h
  | rc :: rcs, g :: gs, h => by
    unfold storedRecsCheck at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    cases u
    obtain ⟨hl, hall⟩ := storedRecsCheck_inv h
    refine ⟨by simp [hl], fun j rc' g' hr hg => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hg
      subst hr hg
      exact hu
    | succ j => exact hall j rc' g' (by simpa using hr) (by simpa using hg)

theorem recDomsAt_inv {env : Env} {rec : Name} {sfvs gfvs : List Expr} :
    ∀ {k j : Nat}, recDomsAt ops env rec sfvs gfvs j k = .ok () →
      ∀ i, j ≤ i → i < j + k → ∃ a b, sfvs[i]? = some a ∧ gfvs[i]? = some b ∧
        ops.isDefEq env i a.fvarTypeD b.fvarTypeD = .ok true
  | 0, _, _, i, h1, h2 => absurd h2 (by omega)
  | k + 1, j, h, i, h1, h2 => by
    unfold recDomsAt at h
    obtain ⟨a, ha, h⟩ := exceptBind_ok h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    obtain ⟨c, hc, h⟩ := exceptBind_ok h
    cases c
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp only [↓reduceIte] at h
      have h' : recDomsAt ops env rec sfvs gfvs (j + 1) k = .ok () := by
        simpa [pure, Except.pure, bind, Except.bind] using h
      by_cases hij : i = j
      · subst hij
        exact ⟨a, b, unwrapOr_ok ha, unwrapOr_ok hb, hc⟩
      · exact recDomsAt_inv h' i (by omega) (by omega)

theorem recTyCheck_inv {rec : Name} {lps : List Name} {n : Nat} {s g : Expr}
    (h : recTyCheck ops w fe rec lps n s g = .ok ()) :
    s.looseBVarsBounded 0 = true ∧ s.hasFvar = false ∧ g.hasFvar = false ∧
    s.allLevelParamsDefined lps = true ∧ w.resolve fe s = true ∧
    (∃ st u, ops.inferType fe.env 0 s = .ok st ∧ ops.ensureSort fe.env 0 st = .ok u) ∧
    ∃ sfvs srest gfvs grest, openPisAtFvars n s 0 = some (sfvs, srest) ∧
      openPisAtFvars n g 0 = some (gfvs, grest) ∧
      recDomsAt ops fe.env rec sfvs gfvs 0 n = .ok () ∧
      ops.isDefEq fe.env n srest grest = .ok true := by
  unfold recTyCheck at h
  by_cases h1 : (s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar) = true
  · simp only [h1, ↓reduceIte] at h
    by_cases h2 : s.allLevelParamsDefined lps = true
    · simp only [h2, ↓reduceIte] at h
      by_cases h3 : w.resolve fe s = true
      · simp only [h3, ↓reduceIte] at h
        obtain ⟨st, hst, h⟩ := exceptBind_ok h
        obtain ⟨u, hu, h⟩ := exceptBind_ok h
        cases hos : openPisAtFvars n s 0 with
        | none => simp [hos, recTyOpened, throw, throwThe, MonadExceptOf.throw] at h
        | some qs =>
          obtain ⟨sfvs, srest⟩ := qs
          cases hog : openPisAtFvars n g 0 with
          | none => simp [hos, hog, recTyOpened, throw, throwThe, MonadExceptOf.throw] at h
          | some qg =>
            obtain ⟨gfvs, grest⟩ := qg
            rw [hos, hog] at h
            simp only [recTyOpened] at h
            obtain ⟨v, hv, h⟩ := exceptBind_ok h
            cases v
            obtain ⟨b, hb, h⟩ := exceptBind_ok h
            cases b
            · simp [throw, throwThe, MonadExceptOf.throw] at h
            · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
              exact ⟨h1.1.1, h1.1.2, h1.2, h2, h3, ⟨st, u, hst, hu⟩, sfvs, srest, gfvs, grest,
                rfl, rfl, hv, hb⟩
      · simp [h3, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp [h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem ruleAgree_inv {rec ctor : Name} {lps : List Name} {s g : Expr}
    (h : ruleAgree ops w fe rec ctor lps s g = .ok ()) :
    s.looseBVarsBounded 0 = true ∧ s.hasFvar = false ∧ g.hasFvar = false ∧
    s.allLevelParamsDefined lps = true ∧ w.resolve fe s = true ∧
    ∃ ts tg, ops.inferType fe.env 0 s = .ok ts ∧ ops.inferType fe.env 0 g = .ok tg ∧
      ops.isDefEq fe.env 0 ts tg = .ok true ∧ ops.isDefEq fe.env 0 s g = .ok true := by
  unfold ruleAgree at h
  by_cases h1 : (s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar) = true
  · simp only [h1, ↓reduceIte] at h
    by_cases h2 : s.allLevelParamsDefined lps = true
    · simp only [h2, ↓reduceIte] at h
      by_cases h3 : w.resolve fe s = true
      · simp only [h3, ↓reduceIte] at h
        obtain ⟨ts, hts, h⟩ := exceptBind_ok h
        obtain ⟨tg, htg, h⟩ := exceptBind_ok h
        obtain ⟨b1, hb1, h⟩ := exceptBind_ok h
        cases b1
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
        · simp only [↓reduceIte] at h
          obtain ⟨b2, hb2, h⟩ := exceptBind_ok h
          cases b2
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
            exact ⟨h1.1.1, h1.1.2, h1.2, h2, h3, ts, tg, hts, htg, hb1, hb2⟩
      · simp [h3, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp [h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

end Inv
/-! ## The stored install against the generated one, entry by entry -/

/-- One installed rule: at a constructor of the major, with a
right-hand side (`tgtStoredRules`, rule by rule). -/
@[expose] def tgtRuleAt (find? : Name → Option ConstantInfo) (M : TargetMajor) (rP : Nat)
    (c : ConstantVal × Nat) (rhs : Expr) : RecRule :=
  match M.member with
  | none =>
    { recRuleBits find?
        { ctor := c.1.name, nfields := c.2, ctorParams := M.nPc, fire := .plain, rhs := rhs } with
      fire := auxRuleFire M rP }
  | some _ =>
    recRuleBits find?
      { ctor := c.1.name, nfields := c.2, ctorParams := M.nPc, fire := .plain, rhs := rhs }

theorem sumRules_eq_map {find? : Name → Option ConstantInfo} {rec : Name} {nP : Nat} :
    ∀ (cs : List (ConstantVal × Nat)) (rhss : List Expr),
      sumRules find? rec nP cs rhss = (cs.zip rhss).map (fun p => recRuleBits find?
        { ctor := p.1.1.name, nfields := p.1.2, ctorParams := nP, fire := .plain, rhs := p.2 })
  | [], _ => by simp [sumRules]
  | _ :: _, [] => by simp [sumRules]
  | c :: cs, r :: rs => by
    simp only [sumRules, List.zip_cons_cons, List.map_cons]
    rw [sumRules_eq_map cs rs]

theorem tgtStoredRules_eq_map (find? : Name → Option ConstantInfo) (cv : ConstantVal) (rP : Nat)
    (M : TargetMajor) (rhss : List Expr) :
    tgtStoredRules find? cv rP M rhss = (M.ctors.zip rhss).map (fun p => tgtRuleAt find? M rP p.1 p.2) := by
  unfold tgtStoredRules tgtRuleAt
  rw [sumRules_eq_map]
  cases M.member <;> simp [List.map_map, Function.comp_def]

/-- A rule of the stored install is the generated rule at its
position with the stored right-hand side. -/
theorem storedRule_corr {find? : Name → Option ConstantInfo} {cvS cvG : ConstantVal} {rP : Nat}
    {M : TargetMajor} {rhssS rhssG : List Expr} (hlen : rhssS.length = rhssG.length) {r : RecRule}
    (hr : r ∈ tgtStoredRules find? cvS rP M rhssS) :
    ∃ (i : Nat) (rG : RecRule), rG ∈ tgtStoredRules find? cvG rP M rhssG ∧ rhssS[i]? = some r.rhs ∧
      rhssG[i]? = some rG.rhs ∧ r = { rG with rhs := r.rhs } := by
  rw [tgtStoredRules_eq_map] at hr ⊢
  obtain ⟨⟨c, e⟩, hp, rfl⟩ := List.mem_map.mp hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hp
  obtain ⟨hc, he⟩ := List.getElem?_zip_eq_some.mp hi
  have hil : i < rhssG.length := by
    have := (List.getElem?_eq_some_iff.mp he).1; omega
  refine ⟨i, tgtRuleAt find? M rP c rhssG[i], List.mem_map.mpr ⟨(c, rhssG[i]),
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hc, List.getElem?_eq_getElem hil⟩), rfl⟩,
    ?_, ?_, ?_⟩ <;> unfold tgtRuleAt <;> cases M.member <;> simp [he, List.getElem?_eq_getElem hil] <;> rfl

/-- The generated recursor entry at block position `j`. -/
@[expose] def recEntryG (find? : Name → Option ConstantInfo) (q : BlockShape) (j : Nat)
    (g : ConstantVal × TargetMajor × List Expr) : ConstantInfo :=
  .recInfo g.1 (q.majorIdxAt j) (q.rulePrefixAt j)
    (tgtStoredRules find? g.1 (q.rulePrefixAt j) g.2.1 g.2.2)

/-- The stored recursor entry at block position `j`: the record's type
and right-hand sides at the generated recursor. -/
@[expose] def recEntryS (find? : Name → Option ConstantInfo) (q : BlockShape) (j : Nat)
    (rc : RecShape) (g : ConstantVal × TargetMajor × List Expr) : ConstantInfo :=
  .recInfo { g.1 with type := rc.cvR.type } (q.majorIdxAt j) (q.rulePrefixAt j)
    (tgtStoredRules find? { g.1 with type := rc.cvR.type } (q.rulePrefixAt j) g.2.1
      (rc.rules.map (·.rhs)))

/-- **The stored install against the generated one**: every lookup and
every member of the first is the second's, or a stored entry whose
generated entry the second holds at the same name (`Q` the positions'
facts). -/
@[expose] def StoredCorr (find? : Name → Option ConstantInfo) (q : BlockShape)
    (Q : Nat → RecShape → ConstantVal × TargetMajor × List Expr → Prop) (envS envG : Env) : Prop :=
  (∀ n ci, envS.find? n = some ci → envG.find? n = some ci ∨
    ∃ j rc g, Q j rc g ∧ g.1.name = n ∧ envG.find? n = some (recEntryG find? q j g) ∧
      ci = recEntryS find? q j rc g) ∧
  (∀ c ∈ envS.consts, c ∈ envG.consts ∨
    ∃ j rc g, Q j rc g ∧ c = recEntryS find? q j rc g ∧ recEntryG find? q j g ∈ envG.consts)

theorem StoredCorr.refl (find? : Name → Option ConstantInfo) (q : BlockShape)
    (Q : Nat → RecShape → ConstantVal × TargetMajor × List Expr → Prop) (env : Env) :
    StoredCorr find? q Q env env :=
  ⟨fun _ _ h => Or.inl h, fun _ h => Or.inl h⟩

theorem StoredCorr.cons {find? : Name → Option ConstantInfo} {q : BlockShape}
    {Q : Nat → RecShape → ConstantVal × TargetMajor × List Expr → Prop} {envS envG : Env}
    (h : StoredCorr find? q Q envS envG) {j : Nat} {rc : RecShape}
    {g : ConstantVal × TargetMajor × List Expr} (hQ : Q j rc g) :
    StoredCorr find? q Q ⟨recEntryS find? q j rc g :: envS.consts, envS.tables⟩
      ⟨recEntryG find? q j g :: envG.consts, envG.tables⟩ := by
  obtain ⟨hf, hm⟩ := h
  refine ⟨fun n ci hci => ?_, fun c hc => ?_⟩
  · rw [Env.find?_cons] at hci
    have hG : ∀ n', Env.find? ⟨recEntryG find? q j g :: envG.consts, envG.tables⟩ n'
        = if g.1.name = n' then some (recEntryG find? q j g) else envG.find? n' := fun n' => by
      rw [Env.find?_cons]; rfl
    by_cases hn : g.1.name = n
    · rw [ite_eq_left (show (recEntryS find? q j rc g).name = n from hn)] at hci
      exact Or.inr ⟨j, rc, g, hQ, hn, by rw [hG, ite_eq_left hn], (Option.some.inj hci).symm⟩
    · rw [ite_eq_right (show ¬ (recEntryS find? q j rc g).name = n from hn)] at hci
      rw [hG, ite_eq_right hn]
      exact hf n ci hci
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inr ⟨j, rc, g, hQ, rfl, List.mem_cons_self⟩
    · rcases hm c hc with h | ⟨j', rc', g', hQ', he, hmem⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr ⟨j', rc', g', hQ', he, List.mem_cons_of_mem _ hmem⟩

/-- **The recursors' conses keep the correspondence**, at the stored and
the generated family. -/
theorem StoredCorr.consBlockRecsT {find? : Name → Option ConstantInfo} {q : BlockShape}
    {Q : Nat → RecShape → ConstantVal × TargetMajor × List Expr → Prop} :
    ∀ {m : Nat} {recs : List RecShape} {out : List (ConstantVal × TargetMajor × List Expr)}
      {envS envG : Env}, out.length = recs.length →
      (∀ i rc g, recs[i]? = some rc → out[i]? = some g → Q (m + i) rc g) →
      StoredCorr find? q Q envS envG →
      StoredCorr find? q Q (ConLeche.consBlockRecsT find? q m (storedOut recs out) envS)
        (ConLeche.consBlockRecsT find? q m out envG)
  | _, [], [], _, _, _, _, h => h
  | _, [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _, _ :: _, [], _, _, hl, _, _ => by simp at hl
  | m, rc :: recs, g :: out, envS, envG, hl, hQ, h => by
    simp only [storedOut, List.zipWith_cons_cons, ConLeche.consBlockRecsT]
    exact StoredCorr.consBlockRecsT (m := m + 1) (recs := recs) (out := out)
      (envS := ⟨recEntryS find? q m rc g :: envS.consts, envS.tables⟩)
      (envG := ⟨recEntryG find? q m g :: envG.consts, envG.tables⟩)
      (by simpa using hl)
      (fun i rc' g' hr hg => by
        have := hQ (i + 1) rc' g' (by simpa using hr) (by simpa using hg)
        rwa [show m + (i + 1) = m + 1 + i by omega] at this)
      (h.cons (by simpa using hQ 0 rc g rfl rfl))

end ConLeche
