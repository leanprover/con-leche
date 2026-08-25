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
theorem InstArgs.of_pointwise {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V},
      as.length = vs.length →
      (∀ (k : Nat) (a : Expr) (v : V), as[k]? = some a →
        vs[k]? = some v → WScoped D a ∧ a.looseBVarsBounded 0 = true ∧
        interpExpr V cval env φ D ρ a = some v) →
      InstArgs cval env φ D ρ as vs
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, v :: vs, hlen, hpt => by
    refine ⟨hpt 0 a v rfl rfl, ?_⟩
    exact InstArgs.of_pointwise (by simpa using hlen)
      (fun k x w hx hw => hpt (k + 1) x w (by simpa using hx)
        (by simpa using hw))

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
          ty.looseBVarsBounded 0 = true := by
  intro fvms
  induction fvms with
  | nil =>
    intro d bL _ k p hp
    exact nomatch hp
  | cons q fvms ih =>
    intro d bL h k p hp
    obtain ⟨⟨nm, ty, heq, hw, hb, -, -⟩, hrest⟩ := h
    cases k with
    | zero =>
      obtain rfl : q = p := by simpa using hp
      exact ⟨nm, ty, heq, hw, hb⟩
    | succ k =>
      obtain ⟨nm', ty', h1, h2, h3⟩ := ih hrest k p (by simpa using hp)
      exact ⟨nm', ty', by rw [h1]; congr 1; omega,
        by rw [show d + (k + 1) = d + 1 + k from by omega]; exact h2,
        h3⟩

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


/-! ## Syntactic well-formedness of the canonical tower (install side) -/

omit [SetTheory V] in
/-- An expression without free variables is consistent at any index. -/
theorem Expr.fvarConsistent_of_not_hasFvar {d : Nat} {n : Name}
    {ty : Expr} :
    ∀ {e : Expr}, e.hasFvar = false → Expr.fvarConsistent d n ty e := by
  intro e
  induction e <;> intro h <;>
    simp_all [Expr.hasFvar, Expr.fvarConsistent]

omit [SetTheory V] in
/-- Consistency is preserved by instantiation with a consistent
argument. -/
theorem Expr.fvarConsistent_instantiate1_arg {d : Nat} {n : Name}
    {ty : Expr} {a : Expr} (ha : Expr.fvarConsistent d n ty a) :
    ∀ (e : Expr) (k : Nat), Expr.fvarConsistent d n ty e →
      Expr.fvarConsistent d n ty (e.instantiate1 a k) := by
  intro e
  induction e <;> intro k hc <;>
    simp_all [Expr.instantiate1, Expr.fvarConsistent]
  case bvar i =>
    split
    · exact ha
    · split <;> simp [Expr.fvarConsistent]

omit [SetTheory V] in
/-- Consistency through an instantiation sequence with consistent
arguments. -/
theorem Expr.fvarConsistent_instSeq {d : Nat} {n : Name} {ty : Expr} :
    ∀ (args : List Expr) (t : Nat) {e : Expr},
      (∀ a ∈ args, Expr.fvarConsistent d n ty a) →
      Expr.fvarConsistent d n ty e →
      Expr.fvarConsistent d n ty (instSeq args t e) := by
  intro args
  induction args with
  | nil => intro t e _ he; exact he
  | cons a as ih =>
    intro t e hargs he
    exact ih (t - 1)
      (fun b hb => hargs b (List.mem_cons_of_mem _ hb))
      (Expr.fvarConsistent_instantiate1_arg
        (hargs a List.mem_cons_self) e t he)

omit [SetTheory V] in
/-- The canonical consistency facts of an opened telescope: outer
consistency is preserved onto every product, and each newly opened
variable is mentioned consistently by the residual and by every later
variable's annotation. -/
theorem openPisAtFvars_consistent :
    ∀ (n : Nat) {e : Expr} (i₀ : Nat) {fvs : List Expr} {rest : Expr},
      openPisAtFvars n e i₀ = some (fvs, rest) →
      WScoped i₀ e →
      (∀ (dv : Nat) (nv : Name) (tv : Expr),
        Expr.fvarConsistent dv nv tv e → dv < i₀ →
        Expr.fvarConsistent dv nv tv rest ∧
        ∀ a ∈ fvs, Expr.fvarConsistent dv nv tv (Expr.fvarTypeD a)) ∧
      (∀ (k : Nat) (nm : Name) (ty : Expr),
        fvs[k]? = some (.fvar (i₀ + k) nm ty) →
        Expr.fvarConsistent (i₀ + k) nm ty rest ∧
        ∀ (j : Nat) (b : Expr), fvs[j]? = some b → k < j →
          Expr.fvarConsistent (i₀ + k) nm ty (Expr.fvarTypeD b))
  | 0, e, i₀, fvs, rest, h, _ => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun dv nv tv hc _ => ⟨hc, fun a ha => by simp at ha⟩,
      fun k nm ty hk => by simp at hk⟩
  | n + 1, e, i₀, fvs, rest, h, hW => by
    match e, h with
    | .forallE nm0 dom0 body0 m0, h =>
      simp only [openPisAtFvars] at h
      cases hrec : openPisAtFvars n
          (body0.instantiate1 (.fvar i₀ nm0 dom0)) (i₀ + 1) with
      | none => rw [hrec] at h; exact nomatch h
      | some pr =>
        rw [hrec] at h
        obtain ⟨fvs', rest'⟩ := pr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hWb : WScoped i₀ dom0 ∧ WScoped i₀ body0 := by
          simpa [WScoped] using hW
        have hWb' : WScoped (i₀ + 1)
            (body0.instantiate1 (.fvar i₀ nm0 dom0)) :=
          WScoped.instantiate1 hWb.1 0 hWb.2
        obtain ⟨hpres, hcanon⟩ :=
          openPisAtFvars_consistent n (i₀ + 1) hrec hWb'
        constructor
        · intro dv nv tv hc hdv
          simp only [Expr.fvarConsistent] at hc
          have hcb : Expr.fvarConsistent dv nv tv
              (body0.instantiate1 (.fvar i₀ nm0 dom0)) :=
            Expr.fvarConsistent_instantiate1_arg
              (by simp [Expr.fvarConsistent]; omega) body0 0 hc.2
          obtain ⟨h1, h2⟩ := hpres dv nv tv hcb (by omega)
          refine ⟨h1, ?_⟩
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hc.1
          · exact h2 a ha
        · intro k nm ty hk
          cases k with
          | zero =>
            have hk0 : Expr.fvar i₀ nm0 dom0 = .fvar (i₀ + 0) nm ty := by
              simpa using hk
            injection hk0 with e1 e2 e3
            have hcb0 : Expr.fvarConsistent i₀ nm ty
                (body0.instantiate1 (.fvar i₀ nm0 dom0)) := by
              rw [show (Expr.fvar i₀ nm0 dom0) =
                .fvar i₀ nm ty from by rw [← e2, ← e3]]
              exact fvarConsistent_instantiate1 body0 0
                hWb.2.fvarsBelow
            have hcb : Expr.fvarConsistent (i₀ + 0) nm ty
                (body0.instantiate1 (.fvar i₀ nm0 dom0)) := hcb0
            obtain ⟨h1, h2⟩ := hpres (i₀ + 0) nm ty hcb (by omega)
            refine ⟨h1, ?_⟩
            intro j b hj hlt
            cases j with
            | zero => omega
            | succ j => exact h2 b (List.mem_of_getElem? (by simpa using hj))
          | succ k =>
            have hk' : fvs'[k]? = some (.fvar (i₀ + 1 + k) nm ty) := by
              rw [show i₀ + (k + 1) = i₀ + 1 + k from by omega] at hk
              simpa using hk
            obtain ⟨h1, h2⟩ := hcanon k nm ty hk'
            rw [show i₀ + 1 + k = i₀ + (k + 1) from by omega] at h1 h2
            refine ⟨h1, ?_⟩
            intro j b hj hlt
            cases j with
            | zero => omega
            | succ j =>
              exact h2 j b (by simpa using hj) (by omega)


omit [SetTheory V] in
/-- Consistency through an instantiation walk. -/
theorem instPisAt_consistent {d : Nat} {n : Name} {ty : Expr} :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instPisAt args e = some (ds, rest) →
      Expr.fvarConsistent d n ty e →
      (∀ a ∈ args, Expr.fvarConsistent d n ty a) →
      Expr.fvarConsistent d n ty rest
  | [], e, ds, rest, h, hc, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact hc
  | a :: args, e, ds, rest, h, hc, hargs => by
    match e, h with
    | .forallE nm0 dom0 body0 m0, h =>
      simp only [Expr.instPisAt] at h
      cases hrec : Expr.instPisAt args (body0.instantiate1 a) with
      | none => rw [hrec] at h; exact nomatch h
      | some pr =>
        rw [hrec] at h
        obtain ⟨ds', rest'⟩ := pr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have hc' : Expr.fvarConsistent d n ty
            (body0.instantiate1 a) :=
          Expr.fvarConsistent_instantiate1_arg
            (hargs a List.mem_cons_self) body0 0
            (by simp only [Expr.fvarConsistent] at hc; exact hc.2)
        exact instPisAt_consistent args hrec hc'
          (fun b hb => hargs b (List.mem_cons_of_mem _ hb))

omit [SetTheory V] in
/-- Assemble the frame invariant from positional facts. -/
theorem FrameWf.of_pointwise :
    ∀ {fvms : List (Expr × BinderMeta)} {d : Nat} {bL : Expr},
      (∀ (k : Nat) (p : Expr × BinderMeta), fvms[k]? = some p →
        ∃ nm ty, p.1 = .fvar (d + k) nm ty ∧ WScoped (d + k) ty ∧
          ty.looseBVarsBounded 0 = true ∧
          Expr.fvarConsistent (d + k) nm ty bL ∧
          ∀ (j : Nat) (q : Expr × BinderMeta), fvms[j]? = some q →
            k < j →
            Expr.fvarConsistent (d + k) nm ty (Expr.fvarTypeD q.1)) →
      WScoped (d + fvms.length) bL → bL.looseBVarsBounded 0 = true →
      FrameWf d fvms bL := by
  intro fvms
  induction fvms with
  | nil =>
    intro d bL _ hW hb
    exact ⟨by simpa using hW, hb⟩
  | cons p fvms ih =>
    intro d bL hpt hW hb
    obtain ⟨nm, ty, h1, h2, h3, h4, h5⟩ := hpt 0 p (by simp)
    obtain ⟨fv, mb⟩ := p
    simp only at h1
    subst h1
    refine ⟨⟨nm, ty, rfl, by simpa using h2, h3, by simpa using h4, ?_⟩,
      ?_⟩
    · intro q hq
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hq
      have := h5 (j + 1) q (by simpa using hj) (by omega)
      simpa using this
    · refine ih ?_ ?_ hb
      · intro k q hq
        obtain ⟨nm', ty', g1, g2, g3, g4, g5⟩ :=
          hpt (k + 1) q (by simpa using hq)
        refine ⟨nm', ty', by
          rw [g1]
          congr 1
          omega, by
          rw [show d + 1 + k = d + (k + 1) from by omega]
          exact g2, g3, by
          rw [show d + 1 + k = d + (k + 1) from by omega]
          exact g4, ?_⟩
        intro j q' hj hlt
        have := g5 (j + 1) q' (by simpa using hj) (by omega)
        rw [show d + 1 + k = d + (k + 1) from by omega]
        exact this
      · rw [show d + 1 + fvms.length = d + (fvms.length + 1) from by
          omega]
        simpa using hW


omit [SetTheory V] in
/-- A frame variable is consistent at its own data and vacuously at
any other index. -/
theorem Expr.fvarConsistent_fvar {d : Nat} {n : Name} {ty : Expr}
    {i : Nat} {n' : Name} {ty' : Expr}
    (h : i = d → n' = n ∧ ty' = ty) :
    Expr.fvarConsistent d n ty (.fvar i n' ty') := h

omit [SetTheory V] in
/-- Consistency is closed under application spines. -/
theorem Expr.fvarConsistent_mkAppN {d : Nat} {n : Name} {ty : Expr} :
    ∀ (xs : List Expr) (f0 : Expr), Expr.fvarConsistent d n ty f0 →
      (∀ x ∈ xs, Expr.fvarConsistent d n ty x) →
      Expr.fvarConsistent d n ty (Expr.mkAppN f0 xs)
  | [], _, hf, _ => hf
  | x :: xs, f0, hf, hxs =>
    Expr.fvarConsistent_mkAppN xs (.app f0 x)
      ⟨hf, hxs x List.mem_cons_self⟩
      (fun y hy => hxs y (List.mem_cons_of_mem _ hy))

omit [SetTheory V] in
/-- Application-spine components inherit consistency. -/
theorem Expr.fvarConsistent_getAppArgs {d : Nat} {n : Name} {ty : Expr} :
    ∀ {e : Expr}, Expr.fvarConsistent d n ty e →
      ∀ x ∈ e.getAppArgs, Expr.fvarConsistent d n ty x := by
  intro e
  induction e <;> intro hc x hx <;>
    simp only [Expr.getAppArgs] at hx
  case app f a ihf iha =>
    rcases List.mem_append.mp hx with hx | hx
    · exact ihf hc.1 x hx
    · obtain rfl : x = a := by simpa using hx
      exact hc.2
  all_goals exact absurd hx (by simp)

omit [SetTheory V] in
/-- Bvar-closure through an instantiation walk at closed arguments. -/
theorem instPisAt_bclosed :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instPisAt args e = some (ds, rest) →
      e.looseBVarsBounded 0 = true →
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      rest.looseBVarsBounded 0 = true
  | [], e, ds, rest, h, hb, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact hb
  | a :: args, e, ds, rest, h, hb, hargs => by
    match e, h with
    | .forallE nm0 dom0 body0 m0, h =>
      simp only [Expr.instPisAt] at h
      cases hrec : Expr.instPisAt args (body0.instantiate1 a) with
      | none => rw [hrec] at h; exact nomatch h
      | some pr =>
        rw [hrec] at h
        obtain ⟨ds', rest'⟩ := pr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have hb' : (body0.instantiate1 a).looseBVarsBounded 0 = true := by
          have hbb : body0.looseBVarsBounded 1 = true := by
            revert hb
            simp [Expr.looseBVarsBounded]
          exact looseBVarsBounded_instantiate1_gen
            (hargs a List.mem_cons_self) hbb
        exact instPisAt_bclosed args hrec hb'
          (fun b hb2 => hargs b (List.mem_cons_of_mem _ hb2))

omit [SetTheory V] in
/-- Leaf-boundedness through an instantiation walk. -/
theorem instPisAt_leaves :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instPisAt args e = some (ds, rest) →
      Expr.LeavesBounded e →
      (∀ a ∈ args, Expr.LeavesBounded a) →
      Expr.LeavesBounded rest
  | [], e, ds, rest, h, hL, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact hL
  | a :: args, e, ds, rest, h, hL, hargs => by
    match e, h with
    | .forallE nm0 dom0 body0 m0, h =>
      simp only [Expr.instPisAt] at h
      cases hrec : Expr.instPisAt args (body0.instantiate1 a) with
      | none => rw [hrec] at h; exact nomatch h
      | some pr =>
        rw [hrec] at h
        obtain ⟨ds', rest'⟩ := pr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have hL' : Expr.LeavesBounded (body0.instantiate1 a) :=
          LeavesBounded.instantiate1
            (LeavesBounded.of_forallE_body hL)
            (hargs a List.mem_cons_self)
        exact instPisAt_leaves args hrec hL'
          (fun b hb2 => hargs b (List.mem_cons_of_mem _ hb2))


omit [SetTheory V] in
/-- Terms scoped below an index are vacuously consistent at it. -/
theorem Expr.fvarConsistent_of_wscoped_lt {D d : Nat} {n : Name}
    {ty : Expr} (hDd : D ≤ d) :
    ∀ {e : Expr}, WScoped D e → Expr.fvarConsistent d n ty e := by
  intro e
  induction e <;> intro h <;>
    simp_all [WScoped, Expr.fvarConsistent]
  omega

omit [SetTheory V] in
/-- The opened variables' annotations are bvar-closed. -/
theorem openPisAtFvars_ty_bounded :
    ∀ (n : Nat) {e : Expr} (i₀ : Nat) {fvs : List Expr} {rest : Expr},
      openPisAtFvars n e i₀ = some (fvs, rest) →
      e.looseBVarsBounded 0 = true →
      ∀ a ∈ fvs, (Expr.fvarTypeD a).looseBVarsBounded 0 = true
  | 0, e, i₀, fvs, rest, h, _ => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro a ha
    simp at ha
  | n + 1, e, i₀, fvs, rest, h, hb => by
    match e, h with
    | .forallE nm0 dom0 body0 m0, h =>
      simp only [openPisAtFvars] at h
      cases hrec : openPisAtFvars n
          (body0.instantiate1 (.fvar i₀ nm0 dom0)) (i₀ + 1) with
      | none => rw [hrec] at h; exact nomatch h
      | some pr =>
        rw [hrec] at h
        obtain ⟨fvs', rest'⟩ := pr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hb2 : dom0.looseBVarsBounded 0 = true ∧
            body0.looseBVarsBounded 1 = true := by
          revert hb
          simp [Expr.looseBVarsBounded]
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simpa [Expr.fvarTypeD] using hb2.1
        · exact openPisAtFvars_ty_bounded n (i₀ + 1) hrec
            (looseBVarsBounded_instantiate1 body0 0 hb2.2) a ha

omit [SetTheory V] in
/-- Leaf-boundedness through an instantiation sequence. -/
theorem LeavesBounded_instSeq :
    ∀ (args : List Expr) (t : Nat) {e : Expr},
      Expr.LeavesBounded e → (∀ a ∈ args, Expr.LeavesBounded a) →
      Expr.LeavesBounded (instSeq args t e) := by
  intro args
  induction args with
  | nil => intro t e hL _; exact hL
  | cons a as ih =>
    intro t e hL hargs
    exact ih (t - 1)
      (LeavesBounded.instantiate1 hL (hargs a List.mem_cons_self))
      (fun b hb => hargs b (List.mem_cons_of_mem _ hb))

omit [SetTheory V] in
/-- Free-variable leaves through an instantiation sequence. -/
theorem fvarLeaves_instSeq :
    ∀ (args : List Expr) (t : Nat) {e : Expr}
      {l : Nat × Name × Expr},
      l ∈ (instSeq args t e).fvarLeaves →
      l ∈ e.fvarLeaves ∨ ∃ a ∈ args, l ∈ a.fvarLeaves := by
  intro args
  induction args with
  | nil => intro t e l hl; exact Or.inl hl
  | cons a as ih =>
    intro t e l hl
    rcases ih (t - 1) hl with hl' | ⟨b, hb, hlb⟩
    · rcases fvarLeaves_instantiate1 e t hl' with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self, h⟩
    · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hlb⟩

/-- The canonical tower's frame is well-formed, from stored data
alone: the syntactic half of a `RecRulesOk` clause, shared by the
modeled install, the basis blocks and the projection functions. -/
theorem ruleLhsParts_frameWf {n : Name} {cv : ConstantVal} {rP : Nat}
    {r : RecRule} {cvj : ConstantVal}
    {fvms : List (Expr × BinderMeta)} {bL : Expr}
    (hparts : ruleLhsParts n cv rP r cvj = some (fvms, bL))
    (hTcl : cv.type.hasFvar = false)
    (hTb : cv.type.looseBVarsBounded 0 = true)
    (hCcl : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hpins : ∀ lvls pins, RecRule.fire r = .nested lvls pins →
      ∀ p ∈ pins, p.hasFvar = false ∧ p.looseBVarsBounded rP = true) :
    FrameWf 0 fvms bL ∧ fvms.length = rP + RecRule.nfields r := by
  obtain ⟨fvsP, rest0, usC, cargs, cdoms, crestP, xFvs, crest2, rbs, rb,
    heqO, hcinst, hopenX, hstripR, hfireCase, hfvmsEq, hbLEq⟩ :=
    ruleLhsParts_inv hparts
  obtain ⟨hfvsPinst, hfvsPlen, hfvsPshape⟩ := openPisAtFvars_spec rP 0 heqO
  obtain ⟨hxFvsInst, hxFvsLen, hxFvsShape⟩ :=
    openPisAtFvars_spec (RecRule.nfields r) rP hopenX
  have hrbsLen : rbs.length = rP + RecRule.nfields r :=
    Expr.stripLams_length _ hstripR
  -- prefix walk facts
  obtain ⟨hfvsWf, hrest0Wf⟩ := openPisAtFvars_wf rP 0 heqO
    (WScoped.of_not_hasFvar hTcl) hTb
    (Expr.LeavesBounded.of_not_hasFvar hTcl)
  obtain ⟨-, hcanon0⟩ := openPisAtFvars_consistent rP 0 heqO
    (WScoped.of_not_hasFvar hTcl)
  have htyB0 := openPisAtFvars_ty_bounded rP 0 heqO hTb
  -- per-position canonical consistency inside the prefix spine
  have hfvsPK : ∀ (k : Nat) (nm : Name) (ty : Expr),
      fvsP[k]? = some (.fvar k nm ty) →
      ∀ a ∈ fvsP, Expr.fvarConsistent k nm ty a := by
    intro k nm ty hk a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨nmj, haj⟩ := hfvsPshape j a hj
    rw [Nat.zero_add] at haj
    rw [haj]
    refine Expr.fvarConsistent_fvar ?_
    intro hjk
    subst hjk
    rw [hj] at hk
    have := Option.some.inj hk
    rw [haj] at this
    injection this with e1 e2 e3
    exact ⟨e2, e3⟩
  -- the fire-generic constructor telescope
  obtain ⟨hctyCl, hctyB, hcargsW, hcargsB0, hcargsL, hcargsK⟩ :
      (match RecRule.fire r with
        | RecRuleFire.nested lvls _ =>
          cvj.type.instantiateLevelParams cvj.levelParams lvls
        | _ => cvj.type).hasFvar = false ∧
      (match RecRule.fire r with
        | RecRuleFire.nested lvls _ =>
          cvj.type.instantiateLevelParams cvj.levelParams lvls
        | _ => cvj.type).looseBVarsBounded 0 = true ∧
      (∀ a ∈ cargs, WScoped rP a) ∧
      (∀ a ∈ cargs, a.looseBVarsBounded 0 = true) ∧
      (∀ a ∈ cargs, Expr.LeavesBounded a) ∧
      (∀ (k : Nat) (nm : Name) (ty : Expr),
        fvsP[k]? = some (.fvar k nm ty) →
        ∀ a ∈ cargs, Expr.fvarConsistent k nm ty a) := by
    rcases hfireCase with ⟨hfp, -, hce⟩ | ⟨lvls, pins, hfn', -, hce⟩
    · rw [hfp, hce]
      refine ⟨hCcl, hCb, ?_, ?_, ?_, ?_⟩
      · intro a ha
        exact (hfvsWf a (List.mem_of_mem_take ha)).1.mono (by omega)
      · intro a ha
        exact (hfvsWf a (List.mem_of_mem_take ha)).2.1
      · intro a ha
        exact (hfvsWf a (List.mem_of_mem_take ha)).2.2
      · intro k nm ty hk a ha
        exact hfvsPK k nm ty hk a (List.mem_of_mem_take ha)
    · rw [hfn', hce]
      refine ⟨by rw [hasFvar_instantiateLevelParams]; exact hCcl,
        by rw [looseBVarsBounded_instantiateLevelParams]; exact hCb,
        ?_, ?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        rw [Expr.instSpine_eq_instSeq]
        exact instSeq_wscoped _
          (WScoped.of_not_hasFvar (hpins lvls pins hfn' p hp).1)
          (fun b hb => (hfvsWf b hb).1.mono (by omega))
      · intro a ha
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        rw [Expr.instSpine_eq_instSeq,
          show (rP : Nat) - 1 = fvsP.length - 1 from by rw [hfvsPlen]]
        refine instSeq_bclosed (fun b hb => (hfvsWf b hb).2.1) ?_
        rw [hfvsPlen]
        exact (hpins lvls pins hfn' p hp).2
      · intro a ha
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        rw [Expr.instSpine_eq_instSeq]
        exact LeavesBounded_instSeq _ _
          (Expr.LeavesBounded.of_not_hasFvar
            (hpins lvls pins hfn' p hp).1)
          (fun b hb => (hfvsWf b hb).2.2)
      · intro k nm ty hk a ha
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        rw [Expr.instSpine_eq_instSeq]
        exact Expr.fvarConsistent_instSeq _ _
          (fun b hb => hfvsPK k nm ty hk b hb)
          (Expr.fvarConsistent_of_not_hasFvar
            (hpins lvls pins hfn' p hp).1)
  -- the instantiated constructor residual and the field walk
  have hcrW : WScoped rP crestP :=
    (instPisAt_wscoped cargs hcinst (WScoped.of_not_hasFvar hctyCl)
      hcargsW).2
  have hcrB : crestP.looseBVarsBounded 0 = true :=
    instPisAt_bclosed cargs hcinst hctyB hcargsB0
  have hcrL : Expr.LeavesBounded crestP :=
    instPisAt_leaves cargs hcinst
      (Expr.LeavesBounded.of_not_hasFvar hctyCl) hcargsL
  have hcrK : ∀ (k : Nat) (nm : Name) (ty : Expr),
      fvsP[k]? = some (.fvar k nm ty) →
      Expr.fvarConsistent k nm ty crestP := by
    intro k nm ty hk
    exact instPisAt_consistent cargs hcinst
      (Expr.fvarConsistent_of_not_hasFvar hctyCl)
      (fun a ha => hcargsK k nm ty hk a ha)
  obtain ⟨hxFvsWf, hcrest2Wf⟩ := openPisAtFvars_wf (RecRule.nfields r) rP
    hopenX hcrW hcrB hcrL
  obtain ⟨hpresX, hcanonX⟩ := openPisAtFvars_consistent
    (RecRule.nfields r) rP hopenX hcrW
  have htyBX := openPisAtFvars_ty_bounded (RecRule.nfields r) rP hopenX
    hcrB
  have hxFvsK : ∀ (k : Nat) (nm : Name) (ty : Expr),
      xFvs[k]? = some (.fvar (rP + k) nm ty) →
      ∀ a ∈ xFvs, Expr.fvarConsistent (rP + k) nm ty a := by
    intro k nm ty hk a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨nmj, haj⟩ := hxFvsShape j a hj
    rw [haj]
    refine Expr.fvarConsistent_fvar ?_
    intro hjk
    have hjk' : j = k := by omega
    subst hjk'
    rw [hj] at hk
    have := Option.some.inj hk
    rw [haj] at this
    injection this with e1 e2 e3
    exact ⟨e2, e3⟩
  -- the spine of the tower and its positional entries
  have hspLen : (fvsP ++ xFvs).length = rP + RecRule.nfields r := by
    rw [List.length_append, hfvsPlen, hxFvsLen]
  have hspineAt : ∀ (k : Nat) (p : Expr × BinderMeta),
      fvms[k]? = some p → (fvsP ++ xFvs)[k]? = some p.1 := by
    intro k p hp
    rw [hfvmsEq] at hp
    exact (zip_getElem?_parts _ _ k p hp).1
  -- canonical consistency of the body at every frame index
  have hbLK : ∀ (k : Nat) (nm : Name) (ty : Expr),
      (fvsP ++ xFvs)[k]? = some (.fvar k nm ty) →
      Expr.fvarConsistent k nm ty bL := by
    intro k nm ty hk
    -- position class
    rcases Nat.lt_or_ge k rP with hkP | hkP
    · -- prefix index
      have hkF : fvsP[k]? = some (.fvar k nm ty) := by
        rw [List.getElem?_append_left (by rw [hfvsPlen]; omega)] at hk
        exact hk
      have hcr2 : Expr.fvarConsistent k nm ty crest2 :=
        (hpresX k nm ty (hcrK k nm ty hkF) (by omega)).1
      rw [hbLEq]
      refine Expr.fvarConsistent_mkAppN _ _ trivial ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact hfvsPK k nm ty hkF x hx
        · exact Expr.fvarConsistent_getAppArgs hcr2 x
            (List.mem_of_mem_drop hx)
      · obtain rfl : x = Expr.mkAppN (.const (RecRule.ctor r) usC)
            (cargs ++ xFvs) := by simpa using hx
        refine Expr.fvarConsistent_mkAppN _ _ trivial ?_
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hcargsK k nm ty hkF y hy
        · obtain ⟨j, hj⟩ := List.getElem?_of_mem hy
          obtain ⟨nmj, hyj⟩ := hxFvsShape j y hj
          rw [hyj]
          exact Expr.fvarConsistent_fvar (fun hcon => by omega)
    · -- field index
      obtain ⟨j, rfl⟩ : ∃ j, k = rP + j := ⟨k - rP, by omega⟩
      have hkX : xFvs[j]? = some (.fvar (rP + j) nm ty) := by
        rw [List.getElem?_append_right (by rw [hfvsPlen]; omega)] at hk
        rw [show rP + j - fvsP.length = j from by rw [hfvsPlen]; omega]
          at hk
        exact hk
      have hcr2 : Expr.fvarConsistent (rP + j) nm ty crest2 :=
        (hcanonX j nm ty hkX).1
      rw [hbLEq]
      refine Expr.fvarConsistent_mkAppN _ _ trivial ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact Expr.fvarConsistent_of_wscoped_lt (by omega)
            (hfvsWf x hx).1
        · exact Expr.fvarConsistent_getAppArgs hcr2 x
            (List.mem_of_mem_drop hx)
      · obtain rfl : x = Expr.mkAppN (.const (RecRule.ctor r) usC)
            (cargs ++ xFvs) := by simpa using hx
        refine Expr.fvarConsistent_mkAppN _ _ trivial ?_
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact Expr.fvarConsistent_of_wscoped_lt (by omega)
            (hcargsW y hy)
        · exact hxFvsK j nm ty hkX y hy
  -- scoping and closure of the body
  have hWbL : WScoped (rP + RecRule.nfields r) bL := by
    rw [hbLEq]
    refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact (hfvsWf x hx).1.mono (by omega)
      · exact hcrest2Wf.1.getAppArgs x (List.mem_of_mem_drop hx)
    · obtain rfl : x = Expr.mkAppN (.const (RecRule.ctor r) usC)
          (cargs ++ xFvs) := by simpa using hx
      refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact (hcargsW y hy).mono (by omega)
      · exact (hxFvsWf y hy).1
  have hbbL : bL.looseBVarsBounded 0 = true := by
    rw [hbLEq]
    refine looseBVarsBounded_mkAppN (by simp [Expr.looseBVarsBounded]) ?_
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact (hfvsWf x hx).2.1
      · exact looseBVarsBounded_getAppArgs hcrest2Wf.2.1 x
          (List.mem_of_mem_drop hx)
    · obtain rfl : x = Expr.mkAppN (.const (RecRule.ctor r) usC)
          (cargs ++ xFvs) := by simpa using hx
      refine looseBVarsBounded_mkAppN
        (by simp [Expr.looseBVarsBounded]) ?_
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hcargsB0 y hy
      · exact (hxFvsWf y hy).2.1
  -- assemble
  have hlen : fvms.length = rP + RecRule.nfields r := by
    rw [hfvmsEq, List.length_zip, List.length_append, hfvsPlen,
      hxFvsLen, List.length_map, hrbsLen]
    omega
  refine ⟨FrameWf.of_pointwise ?_ (by
    first
      | exact hWbL
      | (simp only [Nat.zero_add, hlen]; exact hWbL)) hbbL, hlen⟩
  intro k p hp
  have hkN : k < rP + RecRule.nfields r := by
    rcases Nat.lt_or_ge k (rP + RecRule.nfields r) with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none (by rw [hlen]; omega)] at hp
      exact nomatch hp
  have hpa := hspineAt k p hp
  rcases Nat.lt_or_ge k rP with hkP | hkP
  · have hkF : fvsP[k]? = some p.1 := by
      rw [List.getElem?_append_left (by rw [hfvsPlen]; omega)] at hpa
      exact hpa
    obtain ⟨nm, ha⟩ := hfvsPshape k p.1 hkF
    rw [Nat.zero_add] at ha
    have hkF' : fvsP[k]? = some (.fvar k nm (Expr.fvarTypeD p.1)) := by
      rw [hkF, ha]
      rfl
    refine ⟨nm, Expr.fvarTypeD p.1, by
      rw [show (0 : Nat) + k = k from by omega]
      exact ha, ?_, ?_, ?_, ?_⟩
    · rw [show (0 : Nat) + k = k from by omega]
      have := (hfvsWf p.1 (List.mem_of_getElem? hkF)).1
      rw [ha] at this
      simp only [WScoped] at this
      exact this.2
    · exact htyB0 p.1 (List.mem_of_getElem? hkF)
    · rw [show (0 : Nat) + k = k from by omega]
      exact hbLK k nm (Expr.fvarTypeD p.1) (by rw [hpa, ha]; rfl)
    · intro j q hq hlt
      rw [show (0 : Nat) + k = k from by omega]
      have hqa := hspineAt j q hq
      have hjN : j < rP + RecRule.nfields r := by
        rcases Nat.lt_or_ge j (rP + RecRule.nfields r) with h2 | h2
        · exact h2
        · rw [List.getElem?_eq_none (by rw [hspLen]; omega)] at hqa
          exact nomatch hqa
      rcases Nat.lt_or_ge j rP with hjP | hjP
      · have hjF : fvsP[j]? = some q.1 := by
          rw [List.getElem?_append_left (by rw [hfvsPlen]; omega)] at hqa
          exact hqa
        have h0 := (hcanon0 k nm (Expr.fvarTypeD p.1)
          (by rw [Nat.zero_add]; exact hkF')).2 j q.1 hjF (by omega)
        rw [Nat.zero_add] at h0
        exact h0
      · have hjX : xFvs[j - rP]? = some q.1 := by
          rw [List.getElem?_append_right
            (by rw [hfvsPlen]; omega)] at hqa
          rw [show j - fvsP.length = j - rP from by rw [hfvsPlen]] at hqa
          exact hqa
        exact (hpresX k nm (Expr.fvarTypeD p.1)
          (hcrK k nm (Expr.fvarTypeD p.1) hkF') (by omega)).2
          q.1 (List.mem_of_getElem? hjX)
  · obtain ⟨j0, rfl⟩ : ∃ j0, k = rP + j0 := ⟨k - rP, by omega⟩
    have hkX : xFvs[j0]? = some p.1 := by
      rw [List.getElem?_append_right (by rw [hfvsPlen]; omega)] at hpa
      rw [show rP + j0 - fvsP.length = j0 from by
        rw [hfvsPlen]; omega] at hpa
      exact hpa
    obtain ⟨nm, ha⟩ := hxFvsShape j0 p.1 hkX
    have hkX' : xFvs[j0]? = some
        (.fvar (rP + j0) nm (Expr.fvarTypeD p.1)) := by
      rw [hkX, ha]
      rfl
    refine ⟨nm, Expr.fvarTypeD p.1, by
      rw [show (0 : Nat) + (rP + j0) = rP + j0 from by omega]
      exact ha, ?_, ?_, ?_, ?_⟩
    · rw [show (0 : Nat) + (rP + j0) = rP + j0 from by omega]
      have := (hxFvsWf p.1 (List.mem_of_getElem? hkX)).1
      rw [ha] at this
      simp only [WScoped] at this
      exact this.2
    · exact htyBX p.1 (List.mem_of_getElem? hkX)
    · rw [show (0 : Nat) + (rP + j0) = rP + j0 from by omega]
      exact hbLK (rP + j0) nm (Expr.fvarTypeD p.1)
        (by rw [hpa, ha]; rfl)
    · intro j q hq hlt
      rw [show (0 : Nat) + (rP + j0) = rP + j0 from by omega]
      have hqa := hspineAt j q hq
      rcases Nat.lt_or_ge j rP with hjP | hjP
      · omega
      · have hjX : xFvs[j - rP]? = some q.1 := by
          rw [List.getElem?_append_right
            (by rw [hfvsPlen]; omega)] at hqa
          rw [show j - fvsP.length = j - rP from by rw [hfvsPlen]] at hqa
          exact hqa
        exact (hcanonX j0 nm (Expr.fvarTypeD p.1) hkX').2 (j - rP) q.1
          hjX (by omega)


omit [SetTheory V] in
/-- Closing a binder keeps constants resolving. -/
theorem constsResolve_abstract1 {env : Env} :
    ∀ {e : Expr} (d k : Nat), e.constsResolve env = true →
      (e.abstract1 d k).constsResolve env = true := by
  intro e
  induction e <;> intro d k h
  case fvar idx nm ty ih =>
    simp only [Expr.abstract1]
    split
    · simp [Expr.constsResolve]
    · simpa [Expr.constsResolve] using h
  all_goals simp_all [Expr.abstract1, Expr.constsResolve]

omit [SetTheory V] in
/-- Resolution through an instantiation walk. -/
theorem instPisAt_resolve {env : Env} :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instPisAt args e = some (ds, rest) →
      e.constsResolve env = true →
      (∀ a ∈ args, a.constsResolve env = true) →
      rest.constsResolve env = true
  | [], e, ds, rest, h, hr, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact hr
  | a :: args, e, ds, rest, h, hr, hargs => by
    match e, h with
    | .forallE nm0 dom0 body0 m0, h =>
      simp only [Expr.instPisAt] at h
      cases hrec : Expr.instPisAt args (body0.instantiate1 a) with
      | none => rw [hrec] at h; exact nomatch h
      | some pr =>
        rw [hrec] at h
        obtain ⟨ds', rest'⟩ := pr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have hr2 : dom0.constsResolve env = true ∧
            body0.constsResolve env = true := by
          revert hr
          simp [Expr.constsResolve]
        exact instPisAt_resolve args hrec
          (Expr.constsResolve_instantiate1_gen
            (hargs a List.mem_cons_self) 0 hr2.2)
          (fun b hb => hargs b (List.mem_cons_of_mem _ hb))

omit [SetTheory V] in
/-- The opened variables' annotations resolve. -/
theorem openPisAtFvars_resolve {env : Env} :
    ∀ (n : Nat) {e : Expr} (i₀ : Nat) {fvs : List Expr} {rest : Expr},
      openPisAtFvars n e i₀ = some (fvs, rest) →
      e.constsResolve env = true →
      (∀ a ∈ fvs, a.constsResolve env = true) ∧
      rest.constsResolve env = true
  | 0, e, i₀, fvs, rest, h, hr => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun a ha => by simp at ha, hr⟩
  | n + 1, e, i₀, fvs, rest, h, hr => by
    match e, h with
    | .forallE nm0 dom0 body0 m0, h =>
      simp only [openPisAtFvars] at h
      cases hrec : openPisAtFvars n
          (body0.instantiate1 (.fvar i₀ nm0 dom0)) (i₀ + 1) with
      | none => rw [hrec] at h; exact nomatch h
      | some pr =>
        rw [hrec] at h
        obtain ⟨fvs', rest'⟩ := pr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hr2 : dom0.constsResolve env = true ∧
            body0.constsResolve env = true := by
          revert hr
          simp [Expr.constsResolve]
        have hfv : (Expr.fvar i₀ nm0 dom0).constsResolve env = true := by
          simpa [Expr.constsResolve] using hr2.1
        obtain ⟨h1, h2⟩ := openPisAtFvars_resolve n (i₀ + 1) hrec
          (Expr.constsResolve_instantiate1_gen hfv 0 hr2.2)
        refine ⟨?_, h2⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hfv
        · exact h1 a ha

omit [SetTheory V] in
/-- Resolution of a closed tower from its components. -/
theorem closeLamsAt_resolve {env : Env} :
    ∀ (fvms : List (Expr × BinderMeta)) {bL : Expr},
      (∀ p ∈ fvms, (Expr.fvarTypeD p.1).constsResolve env = true) →
      bL.constsResolve env = true →
      (closeLamsAt fvms bL).constsResolve env = true
  | [], bL, _, hb => hb
  | (fv, m) :: fvms, bL, htys, hb => by
    cases fv with
    | fvar i nm ty =>
      show (Expr.lam nm ty ((closeLamsAt fvms bL).abstract1 i)
        m).constsResolve env = true
      have h1 : ty.constsResolve env = true := by
        have := htys _ List.mem_cons_self
        simpa [Expr.fvarTypeD] using this
      have h2 := constsResolve_abstract1 i 0
        (closeLamsAt_resolve fvms
          (fun p hp => htys p (List.mem_cons_of_mem _ hp)) hb)
      simp [Expr.constsResolve, h1, h2]
    | bvar i =>
      exact closeLamsAt_resolve fvms
        (fun p hp => htys p (List.mem_cons_of_mem _ hp)) hb
    | sort u =>
      exact closeLamsAt_resolve fvms
        (fun p hp => htys p (List.mem_cons_of_mem _ hp)) hb
    | const n0 us0 =>
      exact closeLamsAt_resolve fvms
        (fun p hp => htys p (List.mem_cons_of_mem _ hp)) hb
    | app f0 a0 =>
      exact closeLamsAt_resolve fvms
        (fun p hp => htys p (List.mem_cons_of_mem _ hp)) hb
    | lam n0 t0 b0 m0 =>
      exact closeLamsAt_resolve fvms
        (fun p hp => htys p (List.mem_cons_of_mem _ hp)) hb
    | forallE n0 t0 b0 m0 =>
      exact closeLamsAt_resolve fvms
        (fun p hp => htys p (List.mem_cons_of_mem _ hp)) hb
    | letE n0 t0 v0 b0 =>
      exact closeLamsAt_resolve fvms
        (fun p hp => htys p (List.mem_cons_of_mem _ hp)) hb
    | lit l0 =>
      exact closeLamsAt_resolve fvms
        (fun p hp => htys p (List.mem_cons_of_mem _ hp)) hb
    | proj s0 i0 e0 =>
      exact closeLamsAt_resolve fvms
        (fun p hp => htys p (List.mem_cons_of_mem _ hp)) hb

omit [SetTheory V] in
/-- Resolution of the mkAppN spine. -/
theorem constsResolve_mkAppN {env : Env} :
    ∀ (xs : List Expr) (f0 : Expr), f0.constsResolve env = true →
      (∀ x ∈ xs, x.constsResolve env = true) →
      (Expr.mkAppN f0 xs).constsResolve env = true
  | [], _, hf, _ => hf
  | x :: xs, f0, hf, hxs =>
    constsResolve_mkAppN xs (.app f0 x)
      (by simp [Expr.constsResolve, hf, hxs x List.mem_cons_self])
      (fun y hy => hxs y (List.mem_cons_of_mem _ hy))

/-- The canonical tower's constants resolve, from stored data alone:
the resolution half of a `RecRulesOk` clause. -/
theorem ruleLhsParts_resolve {env : Env} {n : Name} {cv : ConstantVal}
    {rP : Nat} {r : RecRule} {cvj : ConstantVal}
    {fvms : List (Expr × BinderMeta)} {bL : Expr}
    (hparts : ruleLhsParts n cv rP r cvj = some (fvms, bL))
    (hfR : (env.find? n).isSome = true)
    (hfC : (env.find? (RecRule.ctor r)).isSome = true)
    (hTres : cv.type.constsResolve env = true)
    (hCres : cvj.type.constsResolve env = true)
    (hpins : ∀ lvls pins, RecRule.fire r = .nested lvls pins →
      ∀ p ∈ pins, p.constsResolve env = true) :
    (closeLamsAt fvms bL).constsResolve env = true := by
  obtain ⟨fvsP, rest0, usC, cargs, cdoms, crestP, xFvs, crest2, rbs, rb,
    heqO, hcinst, hopenX, hstripR, hfireCase, hfvmsEq, hbLEq⟩ :=
    ruleLhsParts_inv hparts
  obtain ⟨hfvsPres, -⟩ := openPisAtFvars_resolve rP 0 heqO hTres
  have hcargsRes : ∀ a ∈ cargs, a.constsResolve env = true := by
    rcases hfireCase with ⟨-, -, hce⟩ | ⟨lvls, pins, hfn', -, hce⟩
    · rw [hce]
      intro a ha
      exact hfvsPres a (List.mem_of_mem_take ha)
    · rw [hce]
      intro a ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      rw [Expr.instSpine_eq_instSeq, ← Expr.instSpine_eq_instSeq]
      exact instSpine_constsResolve _ (hpins lvls pins hfn' p hp)
        hfvsPres
  have hctyRes : (match RecRule.fire r with
      | RecRuleFire.nested lvls _ =>
        cvj.type.instantiateLevelParams cvj.levelParams lvls
      | _ => cvj.type).constsResolve env = true := by
    rcases hfireCase with ⟨hfp, -, -⟩ | ⟨lvls, pins, hfn', -, -⟩
    · rw [hfp]
      exact hCres
    · rw [hfn']
      rw [Expr.constsResolve_instantiateLevelParams]
      exact hCres
  have hcrRes : crestP.constsResolve env = true :=
    instPisAt_resolve cargs hcinst hctyRes hcargsRes
  obtain ⟨hxFvsRes, hcrest2Res⟩ := openPisAtFvars_resolve
    (RecRule.nfields r) rP hopenX hcrRes
  refine closeLamsAt_resolve fvms ?_ ?_
  · intro p hp
    rw [hfvmsEq] at hp
    obtain ⟨h1, -⟩ := zip_getElem?_parts _ _ _ p
      (List.getElem?_of_mem hp).choose_spec
    have hmem := List.mem_of_getElem? h1
    rcases List.mem_append.mp hmem with hm | hm
    · have := hfvsPres p.1 hm
      cases p1 : p.1 <;> rw [p1] at this <;>
        simp_all [Expr.fvarTypeD, Expr.constsResolve]
    · have := hxFvsRes p.1 hm
      cases p1 : p.1 <;> rw [p1] at this <;>
        simp_all [Expr.fvarTypeD, Expr.constsResolve]
  · rw [hbLEq]
    refine constsResolve_mkAppN _ _ (by simp [Expr.constsResolve, hfR])
      ?_
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hfvsPres x hx
      · exact Expr.constsResolve_getAppArgs hcrest2Res x
          (List.mem_of_mem_drop hx)
    · obtain rfl : x = Expr.mkAppN (.const (RecRule.ctor r) usC)
          (cargs ++ xFvs) := by simpa using hx
      refine constsResolve_mkAppN _ _
        (by simp [Expr.constsResolve, hfC]) ?_
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hcargsRes y hy
      · exact hxFvsRes y hy


/-- Annotation truthfulness only reads what `ErasedEq` preserves
(binder names and `fvar` annotations are display-only for the
interpretation). -/
theorem AnnotOk.erasedEq :
    ∀ (e₂ : Expr) {e₁ : Expr}, Expr.ErasedEq e₁ e₂ →
      ∀ (d : Nat) (ρ : Nat → V), AnnotOk V cval env φ d ρ e₁ →
      AnnotOk V cval env φ d ρ e₂
  | .forallE n' ty' body' m', e₁, he, d, ρ, ha => by
    match e₁, he with
    | .forallE n ty body m, he =>
      obtain ⟨rfl, hty, hbody⟩ := he
      simp only [AnnotOk] at ha ⊢
      obtain ⟨haty, hcod, hcond⟩ := ha
      refine ⟨AnnotOk.erasedEq ty' hty d ρ haty, hcod, ?_⟩
      intro x A hA hx
      rw [← interp_erasedEq hty d ρ] at hA
      obtain ⟨hbodyA, hwfact, htie⟩ := hcond x A hA hx
      have hEE : Expr.ErasedEq (body.instantiate1 (.fvar d n ty))
          (body'.instantiate1 (.fvar d n' ty')) :=
        Expr.ErasedEq.instantiate1 hbody (by exact rfl)
      refine ⟨AnnotOk.erasedEq _ hEE (d + 1) (updV V ρ d x) hbodyA, ?_, ?_⟩
      · obtain ⟨w, hwi, hmem⟩ := hwfact
        refine ⟨w, ?_, hmem⟩
        rw [← interp_erasedEq hEE (d + 1) (updV V ρ d x)]
        exact hwi
      · intro v hv
        obtain ⟨w, hwi, hmem⟩ := htie v hv
        refine ⟨w, ?_, hmem⟩
        rw [← interp_erasedEq hEE (d + 1) (updV V ρ d x)]
        exact hwi
  | .lam n' ty' body' m', e₁, he, d, ρ, ha => by
    match e₁, he with
    | .lam n ty body m, he =>
      obtain ⟨rfl, hty, hbody⟩ := he
      simp only [AnnotOk] at ha ⊢
      obtain ⟨haty, hcod, hcond⟩ := ha
      refine ⟨AnnotOk.erasedEq ty' hty d ρ haty, hcod, ?_⟩
      intro x A hA hx
      rw [← interp_erasedEq hty d ρ] at hA
      obtain ⟨hbodyA, hwfact⟩ := hcond x A hA hx
      have hEE : Expr.ErasedEq (body.instantiate1 (.fvar d n ty))
          (body'.instantiate1 (.fvar d n' ty')) :=
        Expr.ErasedEq.instantiate1 hbody (by exact rfl)
      refine ⟨AnnotOk.erasedEq _ hEE (d + 1) (updV V ρ d x) hbodyA, ?_⟩
      obtain ⟨w, B, hwi, hwB, hBu⟩ := hwfact
      refine ⟨w, B, ?_, hwB, hBu⟩
      rw [← interp_erasedEq hEE (d + 1) (updV V ρ d x)]
      exact hwi
  | .app f' a', e₁, he, d, ρ, ha => by
    match e₁, he with
    | .app f a, he =>
      obtain ⟨hf, ha'⟩ := he
      simp only [AnnotOk] at ha ⊢
      obtain ⟨hAf, hAa, vf, va, vE, A, B, hif, hia, hpi, hmem, hfib⟩ := ha
      refine ⟨AnnotOk.erasedEq f' hf d ρ hAf,
        AnnotOk.erasedEq a' ha' d ρ hAa,
        vf, va, vE, A, B, ?_, ?_, hpi, hmem, hfib⟩
      · rw [← interp_erasedEq hf d ρ]
        exact hif
      · rw [← interp_erasedEq ha' d ρ]
        exact hia
  | .proj s' i' e', e₁, he, d, ρ, ha => by
    match e₁, he with
    | .proj s i e, he =>
      obtain ⟨rfl, rfl, hee⟩ := he
      simp only [AnnotOk] at ha ⊢
      obtain ⟨hAe, hi2, ve, u, v, A, Bf, hie, hmem, hAu, hfib⟩ := ha
      refine ⟨AnnotOk.erasedEq e' hee d ρ hAe, hi2,
        ve, u, v, A, Bf, ?_, hmem, hAu, hfib⟩
      rw [← interp_erasedEq hee d ρ]
      exact hie
  | .bvar i, e₁, he, d, ρ, ha => by
    match e₁, he with
    | .bvar j, _ => simp only [AnnotOk]
  | .fvar i n ty, e₁, he, d, ρ, ha => by
    match e₁, he with
    | .fvar j n' ty', _ => simp only [AnnotOk]
  | .sort u, e₁, he, d, ρ, ha => by
    match e₁, he with
    | .sort u', _ => simp only [AnnotOk]
  | .const n us, e₁, he, d, ρ, ha => by
    match e₁, he with
    | .const n' us', _ => simp only [AnnotOk]
  | .lit l, e₁, he, d, ρ, ha => by
    match e₁, he with
    | .lit l', _ => simp only [AnnotOk]
  | .letE n' ty' v' b', e₁, he, d, ρ, ha => by
    match e₁, he with
    | .letE n ty v b, he =>
      obtain ⟨hty, hv, hb⟩ : Expr.ErasedEq ty ty' ∧ Expr.ErasedEq v v' ∧
        Expr.ErasedEq b b' := he
      simp only [AnnotOk] at ha ⊢
      obtain ⟨haty, hav, xv, hxv, hopen⟩ := ha
      have hEE : Expr.ErasedEq (b.instantiate1 (.fvar d n ty))
          (b'.instantiate1 (.fvar d n' ty')) :=
        Expr.ErasedEq.instantiate1 hb (by exact rfl)
      refine ⟨AnnotOk.erasedEq ty' hty d ρ haty,
        AnnotOk.erasedEq v' hv d ρ hav, xv, ?_, ?_⟩
      · rw [← interp_erasedEq hv d ρ]
        exact hxv
      · exact AnnotOk.erasedEq _ hEE (d + 1) (updV V ρ d xv) hopen
termination_by e₂ => e₂.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Extending the canonical list valuation by one value at its length
is the top-slot update. -/
theorem getD_snoc_eq_updV {xs : List V} {x : V} {k : Nat}
    (h : xs.length = k) :
    (fun j => (xs ++ [x]).getD j SetTheory.empty) =
      updV V (fun j => xs.getD j SetTheory.empty) k x := by
  funext j
  simp only [updV, List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy j k with hj | hj | hj
  · rw [if_neg (by omega), List.getElem?_append_left (by omega)]
  · subst hj
    rw [if_pos rfl, List.getElem?_append_right (by omega), h]
    simp
  · rw [if_neg (by omega), List.getElem?_eq_none (by simp; omega),
      List.getElem?_eq_none (by omega)]

/-- Beyond the list, the canonical valuation is constantly junk. -/
theorem updV_getD_self {xs : List V} {D : Nat} (hD : xs.length ≤ D) :
    updV V (fun i => xs.getD i SetTheory.empty) D SetTheory.empty =
      (fun i => xs.getD i SetTheory.empty) := by
  funext i
  simp only [updV]
  split
  · next h =>
    subst h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  · rfl

/-- Padding depth above the canonical list valuation is invisible to
the interpretation of a term scoped at the list. -/
theorem interp_getD_pad {e : Expr} {xs : List V} {D : Nat}
    (hW : WScoped xs.length e) (hD : xs.length ≤ D) :
    interpExpr V cval env φ D (fun i => xs.getD i SetTheory.empty) e =
      interpExpr V cval env φ xs.length
        (fun i => xs.getD i SetTheory.empty) e := by
  have haux : ∀ n, interpExpr V cval env φ (xs.length + n)
      (fun i => xs.getD i SetTheory.empty) e =
      interpExpr V cval env φ xs.length
        (fun i => xs.getD i SetTheory.empty) e := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hstep := interp_weaken_top (cval := cval) (env := env)
        (φ := φ) (e := e) (d := xs.length + n)
        (ρ := fun i => xs.getD i SetTheory.empty)
        (x := SetTheory.empty) (hW.mono (by omega))
      rw [updV_getD_self (V := V) (xs := xs) (D := xs.length + n)
        (by omega)] at hstep
      exact hstep.trans ih
  have hD' : D = xs.length + (D - xs.length) := by omega
  rw [hD', haux]

/-- The interpretation of a term scoped at a prefix only reads the
prefix of the canonical list valuation. -/
theorem interp_getD_take {e : Expr} {j : Nat} (hW : WScoped j e)
    {xs : List V} (hj : j ≤ xs.length) :
    interpExpr V cval env φ xs.length
        (fun i => xs.getD i SetTheory.empty) e =
      interpExpr V cval env φ j
        (fun i => (xs.take j).getD i SetTheory.empty) e := by
  have haux : ∀ n, j + n ≤ xs.length →
      interpExpr V cval env φ (j + n)
          (fun i => (xs.take (j + n)).getD i SetTheory.empty) e =
        interpExpr V cval env φ j
          (fun i => (xs.take j).getD i SetTheory.empty) e := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      obtain ⟨v, hv⟩ : ∃ v, xs[j + n]? = some v :=
        ⟨xs[j + n]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      rw [show j + (n + 1) = (j + n) + 1 from rfl, List.take_add_one, hv]
      show interpExpr V cval env φ ((j + n) + 1)
        (fun i => (xs.take (j + n) ++ [v]).getD i SetTheory.empty) e = _
      rw [getD_snoc_eq_updV (k := j + n)
          (by rw [List.length_take]; omega),
        interp_weaken_top (hW.mono (by omega))]
      exact ih (by omega)
  have h0 := haux (xs.length - j) (by omega)
  rw [show j + (xs.length - j) = xs.length from by omega,
    List.take_of_length_le (Nat.le_refl _)] at h0
  exact h0

/-- Canonicalize a scoped term's interpretation at any padded
canonical list valuation onto its own prefix frame. -/
theorem interp_getD_canon {e : Expr} {xs : List V} {j D : Nat}
    (hW : WScoped j e) (hjx : j ≤ xs.length) (hxD : xs.length ≤ D) :
    interpExpr V cval env φ D (fun i => xs.getD i SetTheory.empty) e =
      interpExpr V cval env φ j
        (fun i => (xs.take j).getD i SetTheory.empty) e := by
  rw [interp_getD_pad (hW.mono hjx) hxD, interp_getD_take hW hjx]

/-- `AnnotOk` version of `interp_getD_pad` (downward). -/
theorem annotOk_getD_pad {e : Expr} {xs : List V} {D : Nat}
    (hW : WScoped xs.length e) (hD : xs.length ≤ D)
    (ha : AnnotOk V cval env φ D (fun i => xs.getD i SetTheory.empty) e) :
    AnnotOk V cval env φ xs.length
      (fun i => xs.getD i SetTheory.empty) e := by
  have haux : ∀ n,
      AnnotOk V cval env φ (xs.length + n)
        (fun i => xs.getD i SetTheory.empty) e →
      AnnotOk V cval env φ xs.length
        (fun i => xs.getD i SetTheory.empty) e := by
    intro n
    induction n with
    | zero => exact fun h => h
    | succ n ih =>
      intro h
      refine ih ?_
      refine AnnotOk.strengthen_top (x := SetTheory.empty)
        (hW.mono (by omega)) ?_
      rwa [updV_getD_self (V := V) (xs := xs) (D := xs.length + n)
        (by omega)]
  have hD' : D = xs.length + (D - xs.length) := by omega
  rw [hD'] at ha
  exact haux _ ha

/-- `AnnotOk` version of `interp_getD_take` (downward). -/
theorem annotOk_getD_take {e : Expr} {j : Nat} (hW : WScoped j e)
    {xs : List V} (hj : j ≤ xs.length)
    (ha : AnnotOk V cval env φ xs.length
      (fun i => xs.getD i SetTheory.empty) e) :
    AnnotOk V cval env φ j
      (fun i => (xs.take j).getD i SetTheory.empty) e := by
  have haux : ∀ n, j + n ≤ xs.length →
      AnnotOk V cval env φ (j + n)
        (fun i => (xs.take (j + n)).getD i SetTheory.empty) e →
      AnnotOk V cval env φ j
        (fun i => (xs.take j).getD i SetTheory.empty) e := by
    intro n
    induction n with
    | zero => exact fun _ h => h
    | succ n ih =>
      intro hn h
      obtain ⟨v, hv⟩ : ∃ v, xs[j + n]? = some v :=
        ⟨xs[j + n]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      rw [show j + (n + 1) = (j + n) + 1 from rfl, List.take_add_one,
        hv] at h
      replace h : AnnotOk V cval env φ ((j + n) + 1)
          (fun i => (xs.take (j + n) ++ [v]).getD i SetTheory.empty) e :=
        h
      rw [getD_snoc_eq_updV (k := j + n)
        (by rw [List.length_take]; omega)] at h
      exact ih (by omega) (AnnotOk.strengthen_top (hW.mono (by omega)) h)
  have h0 := haux (xs.length - j) (by omega)
  rw [show j + (xs.length - j) = xs.length from by omega,
    List.take_of_length_le (Nat.le_refl _)] at h0
  exact h0 ha

/-- `AnnotOk` version of `interp_getD_canon` (downward). -/
theorem annotOk_getD_canon {e : Expr} {xs : List V} {j D : Nat}
    (hW : WScoped j e) (hjx : j ≤ xs.length) (hxD : xs.length ≤ D)
    (ha : AnnotOk V cval env φ D (fun i => xs.getD i SetTheory.empty) e) :
    AnnotOk V cval env φ j
      (fun i => (xs.take j).getD i SetTheory.empty) e :=
  annotOk_getD_take hW hjx (annotOk_getD_pad (hW.mono hjx) hxD ha)

/-- Build the pointwise tower spec from **flat stage facts at the
canonical list valuations**: the producer supplies, per stage `k` over
any fitting value prefix `xs` (tracked by an abstract invariant `Ok`),
the interp-equality of the frame annotation with (anything
erased-equal to) the rule tower's instantiated binder domain, and at
the bottom the interp-equality of the frame body with (anything
erased-equal to) the tower's instantiated body.  The recursion tracks
the right-hand residual only up to `ErasedEq` — the actual `TowerOk`
walk opens the rule's own binders, the stage facts are proved against
the kernel-checked instantiation at the frame variables. -/
theorem TowerOk.of_stages {bL lrest : Expr}
    {fvms : List (Expr × BinderMeta)} {ldoms : List Expr}
    {Ok : List V → Prop}
    (Hty : ∀ (k : Nat) (xs : List V) (fv : Expr) (m : BinderMeta)
      (ld : Expr), xs.length = k → fvms[k]? = some (fv, m) →
      ldoms[k]? = some ld → Ok xs →
      ∃ A, interpExpr V cval env φ k
          (fun j => xs.getD j SetTheory.empty) (Expr.fvarTypeD fv) =
            some A ∧
        (∀ e, Expr.ErasedEq e ld →
          interpExpr V cval env φ k
            (fun j => xs.getD j SetTheory.empty) e = some A) ∧
        AnnotOk V cval env φ k (fun j => xs.getD j SetTheory.empty)
          (Expr.fvarTypeD fv) ∧
        ∀ x, x ∈ˢ A → Ok (xs ++ [x]))
    (Hbot : ∀ (xs : List V), xs.length = fvms.length → Ok xs →
      (∃ w, interpExpr V cval env φ fvms.length
          (fun j => xs.getD j SetTheory.empty) bL = some w ∧
        ∀ e, Expr.ErasedEq e lrest →
          interpExpr V cval env φ fvms.length
            (fun j => xs.getD j SetTheory.empty) e = some w) ∧
      AnnotOk V cval env φ fvms.length
        (fun j => xs.getD j SetTheory.empty) bL) :
    ∀ (fvmsSuf : List (Expr × BinderMeta)) (k : Nat) (xs : List V)
      (ldomsSuf : List Expr) (eRk eLk : Expr),
      k + fvmsSuf.length = fvms.length →
      xs.length = k →
      fvms.drop k = fvmsSuf →
      ldoms.drop k = ldomsSuf →
      (∀ j p, fvmsSuf[j]? = some p →
        ∃ nm ty, p.1 = Expr.fvar (k + j) nm ty) →
      Expr.ErasedEq eRk eLk →
      Expr.instLamsAt (fvmsSuf.map (·.1)) eLk = some (ldomsSuf, lrest) →
      (∃ rbsK bodyK, eLk.stripLams fvmsSuf.length = some (rbsK, bodyK) ∧
        fvmsSuf.map (·.2) = rbsK.map (·.2.2)) →
      Ok xs →
      TowerOk cval env φ k (fun j => xs.getD j SetTheory.empty)
        fvmsSuf bL eRk := by
  intro fvmsSuf
  induction fvmsSuf with
  | nil =>
    intro k xs ldomsSuf eRk eLk hlen hxs hdropF hdropL hshape hEE hinst
      hstrip hOk
    simp only [List.map_nil, Expr.instLamsAt, Option.some.injEq,
      Prod.mk.injEq] at hinst
    obtain ⟨-, rfl⟩ := hinst
    simp only [List.length_nil, Nat.add_zero] at hlen
    subst hlen
    obtain ⟨⟨w, hbLI, hRI⟩, hAbL⟩ := Hbot xs hxs hOk
    exact TowerOk.nil hbLI (hRI eRk hEE) hAbL
  | cons fvm0 fvms' ih =>
    intro k xs ldomsSuf eRk eLk hlen hxs hdropF hdropL hshape hEE hinst
      hstrip hOk
    obtain ⟨fv0, m0⟩ := fvm0
    -- the head frame variable's shape
    obtain ⟨nm, ty, hfv0⟩ := hshape 0 (fv0, m0) rfl
    simp only [Nat.add_zero] at hfv0
    subst hfv0
    -- destructure the λ-tower residual
    simp only [List.map_cons] at hinst
    obtain ⟨n, dom, body, m, ds', rfl, rfl, hinst'⟩ :=
      instLamsAt_cons_inv hinst
    -- the stripped binders: head meta and the tail decomposition
    obtain ⟨rbsK, bodyK, hsK, hmetas⟩ := hstrip
    simp only [List.length_cons, Expr.stripLams] at hsK
    revert hsK
    cases hs0 : body.stripLams fvms'.length with
    | none => intro hsK; exact nomatch hsK
    | some p0 =>
      intro hsK
      simp only [Option.map_some, Option.some.injEq] at hsK
      obtain ⟨hrbsK, -⟩ : (n, dom, m) :: p0.1 = rbsK ∧ p0.2 = bodyK := by
        cases hsK; exact ⟨rfl, rfl⟩
      subst hrbsK
      simp only [List.map_cons, List.cons.injEq] at hmetas
      obtain ⟨hmm, hmetas'⟩ := hmetas
      -- invert the erased equality at the λ
      match eRk, hEE with
      | .lam nmR domR bodyR mR, hEE =>
      obtain ⟨hmR, hdomEE, hbodyEE⟩ := hEE
      subst hmm
      subst hmR
      -- the stage facts at this frame position
      have hfv : fvms[k]? = some (.fvar k nm ty, mR) := by
        have h0 : (fvms.drop k)[0]? = some (.fvar k nm ty, mR) := by
          rw [hdropF]; rfl
        rwa [List.getElem?_drop, Nat.add_zero] at h0
      have hld : ldoms[k]? = some dom := by
        have h0 : (ldoms.drop k)[0]? = some dom := by rw [hdropL]; rfl
        rwa [List.getElem?_drop, Nat.add_zero] at h0
      obtain ⟨A, hframeI, hldI, hAty, hOkStep⟩ :=
        Hty k xs (.fvar k nm ty) mR dom hxs hfv hld hOk
      refine TowerOk.cons hframeI (hldI domR hdomEE) hAty ?_
      intro x hx
      -- next-stage bookkeeping
      have hdropF' : fvms.drop (k + 1) = fvms' := by
        have h0 : (fvms.drop k).drop 1 = fvms.drop (k + 1) := by
          rw [List.drop_drop]
        rw [← h0, hdropF, List.drop_one, List.tail_cons]
      have hdropL' : ldoms.drop (k + 1) = ds' := by
        have h0 : (ldoms.drop k).drop 1 = ldoms.drop (k + 1) := by
          rw [List.drop_drop]
        rw [← h0, hdropL, List.drop_one, List.tail_cons]
      have hshape' : ∀ j p, fvms'[j]? = some p →
          ∃ nm' ty', p.1 = Expr.fvar (k + 1 + j) nm' ty' := by
        intro j p hp
        obtain ⟨nm', ty', hp'⟩ := hshape (j + 1) p (by simpa using hp)
        exact ⟨nm', ty', by rw [hp']; congr 1; omega⟩
      have hEE' : Expr.ErasedEq
          (bodyR.instantiate1 (.fvar k nmR domR))
          (body.instantiate1 (.fvar k nm ty)) :=
        Expr.ErasedEq.instantiate1 hbodyEE (by exact rfl)
      have hstrip' : ∃ rbs₁ body₁,
          (body.instantiate1 (.fvar k nm ty)).stripLams fvms'.length =
            some (rbs₁, body₁) ∧
          fvms'.map (·.2) = rbs₁.map (·.2.2) := by
        have hsome := Expr.stripLams_instantiate1_isSome
          (v := .fvar k nm ty) fvms'.length 0 (by rw [hs0]; rfl)
        cases hs1 : (body.instantiate1 (.fvar k nm ty)).stripLams
            fvms'.length with
        | none => rw [hs1] at hsome; exact nomatch hsome
        | some p1 =>
          refine ⟨p1.1, p1.2, rfl, ?_⟩
          rw [Expr.stripLams_instantiate1_meta fvms'.length 0 hs0 hs1]
          exact hmetas'
      have hrec := ih (k + 1) (xs ++ [x]) ds'
        (bodyR.instantiate1 (.fvar k nmR domR))
        (body.instantiate1 (.fvar k nm ty))
        (by simp only [List.length_cons] at hlen; omega)
        (by simp [hxs])
        hdropF' hdropL' hshape' hEE' hinst' hstrip' (hOkStep x hx)
      rwa [getD_snoc_eq_updV hxs] at hrec

end Setlec
