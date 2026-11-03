module

public import ConLeche.Kernel.Inductives.StoredRecs
public import ConLeche.Kernel.Inductives.BlockTail
import ConLeche.Verify.ExceptBind
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
    (h : storedRecCheck id ops w fe rc g = .ok ()) :
    storedRulesShape (m := CheckM) rc.cvR.name rc.rules g.2.1.ctors = .ok () ∧
    storedNestedOk rc.cvR.type rc.mI rc.rP (storedFireOf g.2.1 rc.rP) = true ∧
    storedRecCompare ops w fe rc g = .ok () := by
  unfold storedRecCheck at h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  cases u
  by_cases hn : storedNestedOk rc.cvR.type rc.mI rc.rP (storedFireOf g.2.1 rc.rP) = true
  · simp only [hn, ↓reduceIte, id_eq] at h
    exact ⟨hu, hn, by simpa [pure, Except.pure, bind, Except.bind] using h⟩
  · simp [hn, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem storedRecsCheck_inv :
    ∀ {recs : List RecShape} {out : List (ConstantVal × TargetMajor × List Expr)},
      storedRecsCheck id ops w fe recs out = .ok () →
      recs.length = out.length ∧ ∀ (j : Nat) (rc : RecShape)
        (g : ConstantVal × TargetMajor × List Expr), recs[j]? = some rc → out[j]? = some g →
        storedRecCheck id ops w fe rc g = .ok ()
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

theorem recTyCheck_inv {rec : Name} {lps : List Name} {n : Nat} {s g : Expr}
    (h : recTyCheck ops w fe rec lps n s g = .ok ()) :
    s.looseBVarsBounded 0 = true ∧ s.hasFvar = false ∧ g.hasFvar = false ∧
    s.allLevelParamsDefined lps = true ∧ w.resolve fe s = true ∧
    ∃ st u, ops.inferType fe.env 0 s = .ok st ∧ ops.ensureSort fe.env 0 st = .ok u ∧
      recTyAgree ops fe.env rec n 0 s g = .ok () := by
  unfold recTyCheck at h
  by_cases h1 : (s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar) = true
  · simp only [h1, ↓reduceIte] at h
    by_cases h2 : s.allLevelParamsDefined lps = true
    · simp only [h2, ↓reduceIte] at h
      by_cases h3 : w.resolve fe s = true
      · simp only [h3, ↓reduceIte] at h
        obtain ⟨st, hst, h⟩ := exceptBind_ok h
        obtain ⟨u, hu, h⟩ := exceptBind_ok h
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
        exact ⟨h1.1.1, h1.1.2, h1.2, h2, h3, st, u, hst, hu, h⟩
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
          · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
          · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
            exact ⟨h1.1.1, h1.1.2, h1.2, h2, h3, ts, tg, hts, htg, hb1, hb2⟩
      · simp [h3, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp [h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

end Inv

end ConLeche
