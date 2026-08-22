import Setlec.Model.InstFrames

/-!
# Consumer glue for the total rule λ-equality (task #58)

The iota step's soundness consumes `RecRulesOk`'s per-rule equality by
pure `app` congruence plus the tower's beta fold (`closeLamsAt_fold`).
This module holds the bridging devices its fire case needs:

* `ruleLhsParts_inv` — the deterministic inversion of the canonical
  left-hand side's construction, exposing the opened frame, the
  constructor spine and the body;
* `fit_mem_frames` — pointwise domain memberships of a consumer-side
  telescope fit, transferred onto any argument spine with the same
  values at any frame (`interp_instSeq_frames` under the hood);
* `FrameFit.of_pointwise` — assembling the canonical frame fit from
  positional membership facts;
* small `InstArgs`/scoping utilities shared with the install side.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {cval : ConstVal V} {env : Env}
  {φ : Name → Nat}

open SetTheory Expr

/-- A free-variable spine with well-formed entries is an argument
spine. -/
theorem InstArgs.of_fvarSpine {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V}, FvarSpine D ρ as vs →
      (∀ a ∈ as, WScoped D a ∧ a.looseBVarsBounded 0 = true) →
      InstArgs cval env φ D ρ as vs
  | [], [], _, _ => trivial
  | _ :: _, [], h, _ => nomatch h
  | [], _ :: _, h, _ => nomatch h
  | a :: as, v :: vs, h, hwf => by
    obtain ⟨⟨i, n, ty, rfl, hiD, hv⟩, h'⟩ := h
    obtain ⟨hw, hb⟩ := hwf _ List.mem_cons_self
    exact ⟨⟨hw, hb, by simp only [interpExpr]; rw [hv]⟩,
      InstArgs.of_fvarSpine h'
        (fun b hb' => hwf b (List.mem_cons_of_mem _ hb'))⟩

/-- `InstArgs` restricts to a suffix. -/
theorem InstArgs.drop {D : Nat} {ρ : Nat → V} (k : Nat) :
    ∀ {args : List Expr} {vs : List V},
      InstArgs cval env φ D ρ args vs →
      InstArgs cval env φ D ρ (args.drop k) (vs.drop k) := by
  induction k with
  | zero => intro args vs h; simpa using h
  | succ k ih =>
    intro args vs h
    match args, vs, h with
    | [], [], _ => simp only [List.drop_nil]; trivial
    | a :: as, v :: vs, ⟨_, h'⟩ =>
      simpa using ih h'

/-- `InstArgs` concatenates. -/
theorem InstArgs.append {D : Nat} {ρ : Nat → V} :
    ∀ {as₁ as₂ : List Expr} {vs₁ vs₂ : List V},
      InstArgs cval env φ D ρ as₁ vs₁ →
      InstArgs cval env φ D ρ as₂ vs₂ →
      InstArgs cval env φ D ρ (as₁ ++ as₂) (vs₁ ++ vs₂)
  | [], _, [], _, _, h₂ => by simpa using h₂
  | [], _, _ :: _, _, h₁, _ => nomatch h₁
  | _ :: _, _, [], _, h₁, _ => nomatch h₁
  | a :: as₁, as₂, v :: vs₁, vs₂, ⟨ha, h₁⟩, h₂ =>
    ⟨ha, InstArgs.append h₁ h₂⟩

omit [SetTheory V] in
/-- A term scoped at depth `0` has no free variables. -/
theorem Expr.not_hasFvar_of_wscoped0 :
    ∀ {e : Expr}, WScoped 0 e → e.hasFvar = false := by
  intro e
  induction e <;> intro h <;> simp only [WScoped] at h <;>
    simp_all [Expr.hasFvar]

/-- Pointwise domain memberships of a telescope fit, transferred onto
any argument spine carrying the same values (at any frame): the
instantiated domains of a closed telescope interpret equally wherever
the instantiating spines' values agree. -/
theorem fit_mem_frames {D₁ D₂ : Nat} {ρ₁ ρ₂ : Nat → V}
    {ty : Expr} {n : Nat} {bs : List (Name × Expr × BinderMeta)}
    {body : Expr} {spine₁ : List Expr} {ds₁ : List Expr} {rest₁ : Expr}
    {args₂ : List Expr} {vs : List V} {rest₂ : Expr}
    (hcl : ty.hasFvar = false)
    (hty0 : ty.looseBVarsBounded 0 = true)
    (hstrip : ty.stripPis n = some (bs, body))
    (hinst₁ : Expr.instPisAt spine₁ ty = some (ds₁, rest₁))
    (hlen₁ : spine₁.length = n)
    (hia₁ : InstArgs cval env φ D₁ ρ₁ spine₁ vs)
    (hfit : TeleFitI V cval env φ D₂ ρ₂ ty args₂ vs rest₂) :
    ∀ (k : Nat) (a : Expr) (v : V), ds₁[k]? = some a → vs[k]? = some v →
      ∃ B, interpExpr V cval env φ D₁ ρ₁ a = some B ∧ v ∈ˢ B := by
  have hia₂ : InstArgs cval env φ D₂ ρ₂ args₂ vs :=
    TeleFitI.toInstArgs hfit
  have hlen₂ : args₂.length = n := by
    rw [InstArgs.length hia₂, ← InstArgs.length hia₁, hlen₁]
  obtain ⟨ds₂, hinst₂, hpt⟩ := TeleFitI.toInstPisAt hfit
  obtain ⟨-, hds₁⟩ := instPisAt_stripPis spine₁ hinst₁
    (by rw [hlen₁]; exact hstrip)
  obtain ⟨-, hds₂⟩ := instPisAt_stripPis args₂ hinst₂
    (by rw [hlen₂]; exact hstrip)
  intro k a v ha hv
  have hkn : k < n := by
    have hdl := instPisAt_length spine₁ hinst₁
    rcases Nat.lt_or_ge k n with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none (by omega)] at ha
      exact nomatch ha
  obtain ⟨b, hb⟩ : ∃ b, bs[k]? = some b := by
    have := Expr.stripPis_length n hstrip
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have ha' := hds₁ k b hb
  rw [ha] at ha'
  obtain rfl := Option.some.inj ha'
  obtain ⟨a₂, ha₂⟩ : ∃ a₂, ds₂[k]? = some a₂ := by
    have := instPisAt_length args₂ hinst₂
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨B, hBi, hvB⟩ := hpt k a₂ v ha₂ hv
  have ha₂' := hds₂ k b hb
  rw [ha₂] at ha₂'
  obtain rfl := Option.some.inj ha₂'
  refine ⟨B, ?_, hvB⟩
  have hdomcl : b.2.1.hasFvar = false :=
    stripPis_doms_hasFvar n hstrip hcl b (List.mem_of_getElem? hb)
  have hdombd : b.2.1.looseBVarsBounded k = true := by
    have := stripPis_doms_bounded n 0 hstrip hty0 k b hb
    simpa using this
  have ht1 : (spine₁.take k).length = k := by
    rw [List.length_take, hlen₁]; omega
  have ht2 : (args₂.take k).length = k := by
    rw [List.length_take, hlen₂]; omega
  have hcong := interp_instSeq_frames (cval := cval) (env := env)
    (φ := φ) (e := b.2.1) (InstArgs.take k hia₁) (InstArgs.take k hia₂)
    hdomcl (by rw [ht1]; exact hdombd)
  rw [ht1, ht2] at hcong
  rw [hcong]
  exact hBi

/-- Assemble the canonical frame fit from positional membership facts
(each stage's interpretation at the canonical extension of the
preceding values). -/
theorem FrameFit.of_pointwise :
    ∀ {fvms : List (Expr × BinderMeta)} {xs : List V} {d : Nat}
      {ρ : Nat → V},
      fvms.length = xs.length →
      (∀ (k : Nat) (p : Expr × BinderMeta), fvms[k]? = some p →
        ∃ nm ty mb, p = (.fvar (d + k) nm ty, mb)) →
      (∀ (k : Nat) (nm : Name) (ty : Expr) (mb : BinderMeta) (x : V),
        fvms[k]? = some (.fvar (d + k) nm ty, mb) → xs[k]? = some x →
        ∃ A, interpExpr V cval env φ (d + k)
            (snocFrame (V := V) d ρ (xs.take k)).2 ty = some A ∧
          x ∈ˢ A) →
      FrameFit cval env φ d ρ fvms xs := by
  intro fvms
  induction fvms with
  | nil =>
    intro xs d ρ hlen _ _
    obtain rfl : xs = [] := by
      cases xs with
      | nil => rfl
      | cons _ _ => exact nomatch hlen
    exact FrameFit.nil
  | cons p fvms ih =>
    intro xs d ρ hlen hshape hmem
    obtain ⟨x, xs, rfl⟩ : ∃ y ys, xs = y :: ys := by
      cases xs with
      | nil => exact nomatch hlen
      | cons y ys => exact ⟨y, ys, rfl⟩
    obtain ⟨nm, ty, mb, rfl⟩ := hshape 0 p (by simp)
    obtain ⟨A, hA, hx⟩ := hmem 0 nm ty mb x (by simp) (by simp)
    refine FrameFit.cons (A := A) hA hx ?_
    refine ih (by simpa using hlen) ?_ ?_
    · intro k q hq
      obtain ⟨nm', ty', mb', hq'⟩ := hshape (k + 1) q (by simpa using hq)
      exact ⟨nm', ty', mb', by
        rw [hq']
        congr 2
        omega⟩
    · intro k nm' ty' mb' y hq hy
      obtain ⟨A', hA', hy'⟩ := hmem (k + 1) nm' ty' mb' y
        (by
          rw [show d + 1 + k = d + (k + 1) from by omega] at hq
          simpa using hq)
        (by simpa using hy)
      refine ⟨A', ?_, hy'⟩
      rw [show d + 1 + k = d + (k + 1) from by omega]
      exact hA'

/-- Deterministic inversion of the shared tail of the canonical
left-hand side's construction. -/
theorem ruleLhsAux_inv {n : Name} {cv : ConstantVal} {rP : Nat}
    {r : RecRule} {fvsP : List Expr} {usC : List Level}
    {cargs : List Expr} {cty : Expr}
    {fvms : List (Expr × BinderMeta)} {bL : Expr}
    (h : ruleLhsAux n cv rP r fvsP usC cargs cty = some (fvms, bL)) :
    ∃ (cdoms : List Expr) (crestP : Expr) (xFvs : List Expr)
      (crest2 : Expr) (rbs : List (Name × Expr × BinderMeta)) (rb : Expr),
      Expr.instPisAt cargs cty = some (cdoms, crestP) ∧
      openPisAtFvars (RecRule.nfields r) crestP rP = some (xFvs, crest2) ∧
      (RecRule.rhs r).stripLams (rP + RecRule.nfields r) = some (rbs, rb) ∧
      fvms = (fvsP ++ xFvs).zip (rbs.map (·.2.2)) ∧
      bL = Expr.mkAppN (.const n (cv.levelParams.map .param))
        (fvsP ++ crest2.getAppArgs.drop (RecRule.ctorParams r) ++
          [Expr.mkAppN (.const (RecRule.ctor r) usC) (cargs ++ xFvs)]) := by
  unfold ruleLhsAux at h
  split at h
  · exact nomatch h
  · next cdoms crestP heq =>
    split at h
    · exact nomatch h
    · next xFvs crest2 heq2 =>
      split at h
      · exact nomatch h
      · next rbs rb heq3 =>
        have h' := Option.some.inj h
        exact ⟨cdoms, crestP, xFvs, crest2, rbs, rb, heq, heq2, heq3,
          (congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩

/-- Deterministic inversion of the canonical left-hand side's
construction: the opened frame, the constructor spine, the residual
carrying the canonical index tuple, the rule right-hand side's binder
list, and the body. -/
theorem ruleLhsParts_inv {n : Name} {cv : ConstantVal} {rP : Nat}
    {r : RecRule} {cvj : ConstantVal}
    {fvms : List (Expr × BinderMeta)} {bL : Expr}
    (h : ruleLhsParts n cv rP r cvj = some (fvms, bL)) :
    ∃ (fvsP : List Expr) (rest0 : Expr) (usC : List Level)
      (cargs cdoms : List Expr) (crestP : Expr)
      (xFvs : List Expr) (crest2 : Expr)
      (rbs : List (Name × Expr × BinderMeta)) (rb : Expr),
      openPisAtFvars rP cv.type 0 = some (fvsP, rest0) ∧
      Expr.instPisAt cargs
        (match RecRule.fire r with
          | .nested lvls _ =>
            cvj.type.instantiateLevelParams cvj.levelParams lvls
          | _ => cvj.type) = some (cdoms, crestP) ∧
      openPisAtFvars (RecRule.nfields r) crestP rP = some (xFvs, crest2) ∧
      (RecRule.rhs r).stripLams (rP + RecRule.nfields r) = some (rbs, rb) ∧
      ((RecRule.fire r = .plain ∧ usC = cvj.levelParams.map Level.param ∧
          cargs = fvsP.take (RecRule.ctorParams r)) ∨
        ∃ lvls pins, RecRule.fire r = .nested lvls pins ∧ usC = lvls ∧
          cargs = pins.map fun p => Expr.instSpine fvsP (rP - 1) p) ∧
      fvms = (fvsP ++ xFvs).zip (rbs.map (·.2.2)) ∧
      bL = Expr.mkAppN (.const n (cv.levelParams.map .param))
        (fvsP ++ crest2.getAppArgs.drop (RecRule.ctorParams r) ++
          [Expr.mkAppN (.const (RecRule.ctor r) usC) (cargs ++ xFvs)]) := by
  unfold ruleLhsParts at h
  split at h
  · exact nomatch h
  · next fvsP rest0 heqO =>
    split at h
    · -- plain
      next hfire =>
      obtain ⟨cdoms, crestP, xFvs, crest2, rbs, rb, h1, h2, h3, h4, h5⟩ :=
        ruleLhsAux_inv h
      exact ⟨fvsP, rest0, cvj.levelParams.map Level.param,
        fvsP.take (RecRule.ctorParams r), cdoms, crestP, xFvs, crest2,
        rbs, rb, heqO, by rw [hfire]; exact h1, h2, h3,
        Or.inl ⟨hfire, rfl, rfl⟩, h4, h5⟩
    · -- nested
      next lvls pins hfire =>
      obtain ⟨cdoms, crestP, xFvs, crest2, rbs, rb, h1, h2, h3, h4, h5⟩ :=
        ruleLhsAux_inv h
      exact ⟨fvsP, rest0, lvls,
        pins.map fun p => Expr.instSpine fvsP (rP - 1) p, cdoms, crestP,
        xFvs, crest2, rbs, rb, heqO, by rw [hfire]; exact h1, h2, h3,
        Or.inr ⟨lvls, pins, hfire, rfl, rfl⟩, h4, h5⟩
    · -- inert
      exact nomatch h


omit [SetTheory V] in
/-- Positional facts of the frame invariant: the `k`-th variable sits
at index `d + k` with a well-scoped, bvar-closed annotation. -/
theorem FrameWf.get :
    ∀ {fvms : List (Expr × BinderMeta)} {d : Nat} {bL : Expr},
      FrameWf d fvms bL →
      ∀ (k : Nat) (p : Expr × BinderMeta), fvms[k]? = some p →
        ∃ nm ty, p.1 = .fvar (d + k) nm ty ∧ WScoped (d + k) ty ∧
          ty.looseBVarsBounded 0 = true ∧ (∃ cod, p.2.cod = some cod) := by
  intro fvms
  induction fvms with
  | nil =>
    intro d bL _ k p hp
    exact nomatch hp
  | cons q fvms ih =>
    intro d bL h k p hp
    obtain ⟨⟨nm, ty, heq, hw, hb, hcod, -, -⟩, hrest⟩ := h
    cases k with
    | zero =>
      obtain rfl : q = p := by simpa using hp
      exact ⟨nm, ty, heq, hw, hb, hcod⟩
    | succ k =>
      obtain ⟨nm', ty', h1, h2, h3, h4⟩ := ih hrest k p (by simpa using hp)
      exact ⟨nm', ty', by rw [h1]; congr 1; omega,
        by rw [show d + (k + 1) = d + 1 + k from by omega]; exact h2,
        h3, h4⟩

omit [SetTheory V] in
/-- Defined level parameters of a stripped telescope's domains. -/
theorem allLevelParamsDefined_stripPis_doms {ps : List Name} :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr},
      e.stripPis k = some (bs, body) →
      e.allLevelParamsDefined ps = true →
      ∀ b ∈ bs, b.2.1.allLevelParamsDefined ps = true := by
  intro k
  induction k with
  | zero =>
    intro e bs body h _
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro b hb
    simp at hb
  | succ k ih =>
    intro e bs body h hps
    match e, h with
    | .forallE nm ty b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : Expr.stripPis k b with
      | none => rw [hs] at h; exact nomatch h
      | some pr =>
        rw [hs] at h
        obtain ⟨bs', body'⟩ := pr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hps
        intro bb hbb
        rcases List.mem_cons.mp hbb with rfl | hbb
        · exact hps.1.1
        · exact ih hs hps.1.2 bb hbb

omit [SetTheory V] in
/-- The canonical frame over a prefix of the values agrees with the
full one below the prefix's end. -/
theorem snocFrame_take_agree :
    ∀ (xs : List V) (k : Nat) (d : Nat) (ρ : Nat → V) (i : Nat),
      i < d + k → k ≤ xs.length →
      (snocFrame (V := V) d ρ (xs.take k)).2 i =
        (snocFrame (V := V) d ρ xs).2 i := by
  intro xs k d ρ i hik hk
  rcases Nat.lt_or_ge i d with hid | hid
  · rw [snocFrame_snd_lt _ _ _ _ hid, snocFrame_snd_lt _ _ _ _ hid]
  · obtain ⟨x, hx⟩ : ∃ x, xs[i - d]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have h1 : (xs.take k)[i - d]? = some x := by
      rw [List.getElem?_take_of_lt (by omega)]
      exact hx
    have h2 := snocFrame_snd_get (V := V) (xs.take k) d ρ (i - d) x h1
    have h3 := snocFrame_snd_get (V := V) xs d ρ (i - d) x hx
    rw [show d + (i - d) = i from by omega] at h2 h3
    rw [h2, h3]


/-- Pointwise domain memberships of a telescope fit on a
level-instantiated closed telescope, transferred onto any spine with
the same values, at any frame and any level assignment composing
equally on the telescope's parameters — the fit side and the target
side may carry different level instantiations of the same raw
telescope. -/
theorem fit_mem_swap₂ (hcp : ConstValParams cval env)
    {ψ : Name → Nat} {T : Expr} {n : Nat}
    {bs : List (Name × Expr × BinderMeta)} {body : Expr}
    {ks₁ ks₂ : List Name} {us₁ us₂ : List Level} {ps : List Name}
    {D₁ D₂ : Nat} {ρ₁ ρ₂ : Nat → V}
    {spineC args₂ : List Expr} {vs : List V} {restI : Expr}
    (hcl : T.hasFvar = false)
    (hb : T.looseBVarsBounded 0 = true)
    (hstrip : T.stripPis n = some (bs, body))
    (hps : T.allLevelParamsDefined ps = true)
    (hφψ : ∀ p ∈ ps,
      Level.substFn ψ ks₁ us₁ p = Level.substFn φ ks₂ us₂ p)
    (hfit : TeleFitI V cval env φ D₂ ρ₂
      (T.instantiateLevelParams ks₂ us₂) args₂ vs restI)
    (hia₁ : InstArgs cval env ψ D₁ ρ₁ spineC vs)
    (hlen₁ : spineC.length = n) :
    ∀ (k : Nat) (b : Name × Expr × BinderMeta) (v : V),
      bs[k]? = some b → vs[k]? = some v →
      ∃ A, interpExpr V cval env ψ D₁ ρ₁
          (instSeq (spineC.take k) (k - 1)
            (b.2.1.instantiateLevelParams ks₁ us₁)) = some A ∧
        v ∈ˢ A := by
  have hia₂ : InstArgs cval env φ D₂ ρ₂ args₂ vs :=
    TeleFitI.toInstArgs hfit
  have hlen₂ : args₂.length = n := by
    rw [InstArgs.length hia₂, ← InstArgs.length hia₁, hlen₁]
  obtain ⟨⟨bsI, bodyI⟩, hstripI⟩ := Option.isSome_iff_exists.mp
    (Expr.stripPis_instantiateLevelParams_isSome ks₂ us₂ n
      (by rw [hstrip]; rfl))
  obtain ⟨-, hbsI⟩ := Expr.stripPis_instantiateLevelParams_eq ks₂ us₂ n
    hstrip hstripI
  obtain ⟨ds₂, hinst₂, hpt⟩ := TeleFitI.toInstPisAt hfit
  obtain ⟨-, hds₂⟩ := instPisAt_stripPis args₂ hinst₂
    (by rw [hlen₂]; exact hstripI)
  intro k b v hbk hv
  have hkn : k < n := by
    have := Expr.stripPis_length n hstrip
    rcases Nat.lt_or_ge k n with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none (by omega)] at hbk
      exact nomatch hbk
  obtain ⟨bI, hbI⟩ : ∃ bI, bsI[k]? = some bI := by
    have := Expr.stripPis_length n hstripI
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hdomEq : bI.2.1 = b.2.1.instantiateLevelParams ks₂ us₂ :=
    hbsI k b bI hbk hbI
  obtain ⟨a₂, ha₂⟩ : ∃ a₂, ds₂[k]? = some a₂ := by
    have := instPisAt_length args₂ hinst₂
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨B, hBi, hvB⟩ := hpt k a₂ v ha₂ hv
  have ha₂' := hds₂ k bI hbI
  rw [ha₂] at ha₂'
  obtain rfl := Option.some.inj ha₂'
  refine ⟨B, ?_, hvB⟩
  have hdomcl : b.2.1.hasFvar = false :=
    stripPis_doms_hasFvar n hstrip hcl b (List.mem_of_getElem? hbk)
  have hdombd : b.2.1.looseBVarsBounded k = true := by
    have := stripPis_doms_bounded n 0 hstrip hb k b hbk
    simpa using this
  have hdomps : b.2.1.allLevelParamsDefined ps = true :=
    allLevelParamsDefined_stripPis_doms n hstrip hps b
      (List.mem_of_getElem? hbk)
  have ht1 : (spineC.take k).length = k := by
    rw [List.length_take, hlen₁]; omega
  have ht2 : (args₂.take k).length = k := by
    rw [List.length_take, hlen₂]; omega
  have hcong := interp_instSeq_swap₂ (φ := φ) hcp
    (ks₁ := ks₁) (ks₂ := ks₂) (us₁ := us₁) (us₂ := us₂)
    (InstArgs.take k hia₁) (InstArgs.take k hia₂)
    hdomcl (by rw [ht1]; exact hdombd) hdomps hφψ
  rw [ht1, ht2] at hcong
  rw [hcong, ← hdomEq]
  exact hBi


omit [SetTheory V] in
/-- Positional components of a zipped list. -/
theorem zip_getElem?_parts {α β : Type _} :
    ∀ (l₁ : List α) (l₂ : List β) (k : Nat) (p : α × β),
      (l₁.zip l₂)[k]? = some p →
      l₁[k]? = some p.1 ∧ l₂[k]? = some p.2 := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ k p hp
    simp [List.zip] at hp
  | cons a l₁ ih =>
    intro l₂ k p hp
    cases l₂ with
    | nil => simp [List.zip] at hp
    | cons b l₂ =>
      cases k with
      | zero =>
        obtain rfl : (a, b) = p := by simpa using hp
        exact ⟨rfl, rfl⟩
      | succ k =>
        exact ih l₂ k p (by simpa using hp)


omit [SetTheory V] in
/-- Level instantiation reflects constant heads. -/
theorem instantiateLevelParams_eq_const {ks : List Name}
    {us : List Level} :
    ∀ {e : Expr} {n : Name} {ls : List Level},
      e.instantiateLevelParams ks us = .const n ls →
      ∃ ls0, e = .const n ls0 ∧ ls = ls0.map (Level.subst ks us) := by
  intro e n ls h
  cases e
  case const n0 ls0 =>
    simp only [Expr.instantiateLevelParams] at h
    injection h with h1 h2
    exact ⟨ls0, by rw [h1], h2.symm⟩
  all_goals exact nomatch h

end Setlec
