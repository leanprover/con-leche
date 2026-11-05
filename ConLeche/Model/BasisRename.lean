module

public import ConLeche.Model.Cover
public import ConLeche.Verify.PinRen
import ConLeche.Model.Reading.Levels
import ConLeche.Model.DivMod

public section

/-!
# The invariant across different copies of the pins

`EnvModelM.rename` carries the model's invariant from one environment to
another that differs only in the level-parameter names of its pinned
constants (`RenEnv`).  The new valuation reads a constant at the assignment
that gives the old parameter `ks[i]` the new parameter `ps[i]`'s value
(`renAcval`), so every term reads alike on both sides (`denote_ren`).
-/

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule IndCaps
  reservedBasisNames pinnedInfo uN vN)

universe w

variable {V : Type w} [SetTheory V]

/-- The old assignment a new constant is read at. -/
@[expose] def renTr (env env' : Env) (n : Name) (ψ : Name → Nat) : Name → Nat :=
  match env.find? n, env'.find? n with
  | some c, some c' =>
    Level.substFn ψ c.toConstantVal.levelParams (c'.toConstantVal.levelParams.map Level.param)
  | _, _ => ψ

/-- The new leaf valuation. -/
@[expose] def renAcval (acval : Name → (Name → Nat) → Term) (env env' : Env) :
    Name → (Name → Nat) → Term :=
  fun n ψ => acval n (renTr env env' n ψ)

section

variable {env env' : Env} (h : RenEnv env env') {acval : Name → (Name → Nat) → Term}

include h

/-- **The new leaf at an instantiation is the old one**, parameter by
parameter. -/
theorem renAcval_inst (hparams : ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acval n ψ₁ = acval n ψ₂)
    {n : Name} {c c' : ConstantInfo} (hf : env.find? n = some c) (hf' : env'.find? n = some c')
    (hr : ConstRen c c') (φ : Name → Nat) {us : List Level}
    (hus : us.length = c.toConstantVal.levelParams.length) :
    renAcval acval env env' n (Level.substFn φ c'.toConstantVal.levelParams us)
      = acval n (Level.substFn φ c.toConstantVal.levelParams us) := by
  unfold renAcval renTr
  rw [hf, hf']
  dsimp only
  rcases hr with rfl | ⟨-, h1, h2⟩
  · rw [Level.substFn_param_self]
  · refine hparams n c hf _ _ fun p hp => ?_
    have hl : c.toConstantVal.levelParams.length = c'.toConstantVal.levelParams.length := by
      rw [h1.2.2, h2.2.2]
    exact substFn_ren h2.2.1 hl (hus.trans hl) (fun _ _ => rfl) p hp

omit h in
/-- A name with the same lookup keeps its leaf. -/
theorem renAcval_same {n : Name} (he : env'.find? n = env.find? n) :
    renAcval acval env env' n = acval n := by
  funext ψ
  unfold renAcval renTr
  rw [he]
  cases env.find? n with
  | none => rfl
  | some c =>
    dsimp only
    rw [Level.substFn_param_self]

omit h in
theorem levelParamsAt_ren {n : Name} (he : env'.find? n = env.find? n) :
    levelParamsAt env' n = levelParamsAt env n := by
  unfold levelParamsAt
  rw [he]

/-- **Every term reads alike on both sides.** -/
theorem denote_ren (hparams : ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acval n ψ₁ = acval n ψ₂)
    (φ : Name → Nat) :
    ∀ (d : Nat) (e : Expr),
      denote (renAcval acval env env') env' φ d e = denote acval env φ d e := by
  have hlen : ∀ {n c c'}, env.find? n = some c → env'.find? n = some c' → ConstRen c c' →
      c.toConstantVal.levelParams.length = c'.toConstantVal.levelParams.length := by
    intro n c c' _ _ hr
    rcases hr with rfl | ⟨-, h1, h2⟩
    · rfl
    · rw [h1.2.2, h2.2.2]
  have hnat : ConLeche.natLitSupported env = ConLeche.natLitSupported env' := h.natLit.symm
  have hstr : ConLeche.strLitSupported env = ConLeche.strLitSupported env' := h.strLit.symm
  have hproj : ∀ (sn : Name) (i : Nat), env.findProj? sn i = env'.findProj? sn i :=
    fun sn i => (h.findProj sn i).symm
  intro d e
  induction d, e using denote.induct (env := env) with
  | case1 d u => rw [denote, denote]
  | case2 d idx ty => rw [denote, denote]
  | case3 d n us ci hf hl =>
    rcases h.find n with ⟨h1, -⟩ | ⟨c, c', h1, h2, hr⟩
    · rw [h1] at hf; exact nomatch hf
    · rw [h1] at hf
      obtain rfl := Option.some.inj hf
      have hl' := hlen h1 h2 hr
      rw [denote, h2, denote, h1]
      dsimp only
      rw [ite_eq_left (hl' ▸ hl), ite_eq_left hl]
      exact congrArg some (renAcval_inst h hparams h1 h2 hr φ hl)
  | case4 d n us ci hf hl =>
    rcases h.find n with ⟨h1, -⟩ | ⟨c, c', h1, h2, hr⟩
    · rw [h1] at hf; exact nomatch hf
    · rw [h1] at hf
      obtain rfl := Option.some.inj hf
      have hl' := hlen h1 h2 hr
      rw [denote, h2, denote, h1]
      dsimp only
      rw [ite_eq_right (fun hh => hl (hh.trans hl'.symm)), ite_eq_right hl]
  | case5 d n us hf =>
    rcases h.find n with ⟨-, h2⟩ | ⟨c, c', h1, h2, hr⟩
    · rw [denote, h2, denote, hf]
    · rw [h1] at hf; exact nomatch hf
  | case6 d ty body ihty ihbody =>
    rw [denote, denote, ihty, ihbody]
  | case7 d ty body ihty ihbody =>
    rw [denote, denote, ihty, ihbody]
  | case8 d f a ihf iha => rw [denote, denote, ihf, iha]
  | case9 d ty val body ihty ihv ihbody =>
    rw [denote, denote, ihty, ihv, ihbody]
  | case10 d sn i e ihe =>
    rw [denote, denote, ihe, hproj sn i]
  | case11 d n hsup =>
    rw [denote, ite_eq_left (hnat ▸ hsup), denote, ite_eq_left hsup,
      renAcval_same (h.find_noLps rfl), renAcval_same (h.find_noLps rfl)]
  | case12 d n hsup =>
    rw [denote, ite_eq_right (fun h => hsup (hnat.trans h)), denote, ite_eq_right hsup]
  | case13 d s hsup =>
    rw [denote, ite_eq_left (hstr ▸ hsup), denote, ite_eq_left hsup,
      renAcval_same (n := ConLeche.natZeroName) (h.find_noLps rfl),
      renAcval_same (n := ConLeche.natSuccName) (h.find_noLps rfl),
      renAcval_same (n := ConLeche.stringOfListName) (h.find_nonres (by decide)),
      renAcval_same (n := ConLeche.listNilName) (h.find_nonres (by decide)),
      renAcval_same (n := ConLeche.listConsName) (h.find_nonres (by decide)),
      renAcval_same (n := ConLeche.charName) (h.find_nonres (by decide)),
      renAcval_same (n := ConLeche.charOfNatName) (h.find_nonres (by decide)),
      levelParamsAt_ren (h.find_nonres (by decide)), levelParamsAt_ren (h.find_nonres (by decide))]
  | case14 d s hsup =>
    rw [denote, ite_eq_right (fun h => hsup (hstr.trans h)), denote, ite_eq_right hsup]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat' hstr' =>
    cases x with
    | bvar i => rw [denote.eq_def, denote.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat' n)
      | strVal s => exact absurd rfl (hstr' s)

end

/-! ## One rule's law across the renaming -/

section Law

variable {env env' : Env} {m : EnvModel V env} {m' : EnvModel V env'} {φ : Name → Nat}
  {n : Name} {cv cv' : ConstantVal} {mI rP : Nat} {isK : Bool} {rl rl' : RecRule}

/-- What one rule's law reads, on both sides. -/
structure RuleRen (m : EnvModel V env) (m' : EnvModel V env') (φ : Name → Nat) (n : Name)
    (cv cv' : ConstantVal) (mI rP : Nat) (isK : Bool) (rl rl' : RecRule) : Prop where
  hde : ∀ (d : Nat) (e : Expr), denote m'.acval env' φ d e = denote m.acval env φ d e
  hlen : cv'.levelParams.length = cv.levelParams.length
  hty : ∀ us : List Level, us.length = cv.levelParams.length →
    cv'.type.instantiateLevelParams cv'.levelParams us
      = cv.type.instantiateLevelParams cv.levelParams us
  hrhs : ∀ us : List Level, us.length = cv.levelParams.length →
    (RecRule.rhs rl').instantiateLevelParams cv'.levelParams us
      = (RecRule.rhs rl).instantiateLevelParams cv.levelParams us
  hctor : RecRule.ctor rl' = RecRule.ctor rl
  hnf : RecRule.nfields rl' = RecRule.nfields rl
  hfire : RecRule.fire rl' = RecRule.fire rl
  hnest : ∀ lvls pins, RecRule.fire rl = .nested lvls pins → cv' = cv
  hleaf : ∀ us : List Level, us.length = cv.levelParams.length →
    m'.acval n (Level.substFn φ cv'.levelParams us) = m.acval n (Level.substFn φ cv.levelParams us)
  hcj : ∀ cvj' cnP cnF, env'.find? (RecRule.ctor rl) = some (.ctorInfo cvj' cnP cnF) →
    ∃ cvj, env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) ∧
      cvj'.levelParams.length = cvj.levelParams.length ∧
      (∀ usj : List Level, usj.length = cvj.levelParams.length →
        cvj'.type.instantiateLevelParams cvj'.levelParams usj
          = cvj.type.instantiateLevelParams cvj.levelParams usj) ∧
      (∀ usj : List Level, usj.length = cvj.levelParams.length →
        m'.acval (RecRule.ctor rl) (Level.substFn φ cvj'.levelParams usj)
          = m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ∧
      (cvj'.type.stripPis (cnP + RecRule.nfields rl)).isSome
        = (cvj.type.stripPis (cnP + RecRule.nfields rl)).isSome ∧
      (∀ us : List Level, us.length = cv.levelParams.length →
        (ConLeche.recFireComparands rl' cnP cv'.levelParams us cvj'.levelParams [] rP).1
          = (ConLeche.recFireComparands rl cnP cv.levelParams us cvj.levelParams [] rP).1) ∧
      (∀ us : List Level, us.length = cv.levelParams.length → ∀ a : List Level,
        a.length = cvj.levelParams.length →
        (Level.substFn φ cvj'.levelParams a = Level.substFn φ cvj'.levelParams
            (ConLeche.recFireComparands rl cnP cv.levelParams us cvj.levelParams [] rP).1 ↔
          Level.substFn φ cvj.levelParams a = Level.substFn φ cvj.levelParams
            (ConLeche.recFireComparands rl cnP cv.levelParams us cvj.levelParams [] rP).1)) ∧
      (isK = false → ∀ us : List Level,
        ConLeche.iotaCtorNeverProp env'.find? cvj' us = ConLeche.iotaCtorNeverProp env.find? cvj us)

theorem recRuleExtra_ren (r : RuleRen m m' φ n cv cv' mI rP isK rl rl')
    (hX : RecRuleExtra m φ n cv mI rP isK rl) : RecRuleExtra m' φ n cv' mI rP isK rl' := by
  intro us hus TVa hTVa
  have hus0 : us.length = cv.levelParams.length := hus.trans r.hlen
  rw [r.hde, r.hty us hus0] at hTVa
  obtain ⟨hK, hC⟩ := hX us hus0 TVa hTVa
  have hLf := r.hleaf us hus0
  refine ⟨fun hk => ?_, fun cvj' cnP cnF hfc => ?_⟩
  · obtain ⟨hnf, hK'⟩ := hK hk
    refine ⟨by rw [r.hnf]; exact hnf, fun Ra hRa ρ xs a restR hxs hfit hw => ?_⟩
    rw [r.hde, r.hrhs us hus0] at hRa
    rw [hLf]
    exact hK' Ra hRa ρ xs a restR hxs hfit hw
  · rw [r.hctor] at hfc
    obtain ⟨cvj, hfcj, hlj, htj, hlfj, hsp, hcmp, hsub, hnp⟩ := r.hcj cvj' cnP cnF hfc
    obtain ⟨har, hrest⟩ := hC cvj cnP cnF hfcj
    refine ⟨by rw [r.hnf, hsp]; exact har, fun hk => ?_⟩
    obtain ⟨hS, hT, hPU⟩ := hrest hk
    have hc := hcmp us hus0
    have hn := hnp hk
    rw [hc, hn, r.hctor, r.hnf]
    refine ⟨hS, fun hne usj hlj' TVja hTVja ρ xs ys restR restC hxs hys hfR hfC hwx hwy hnept => ?_,
      fun usj hlj' hsj TVja hTVja => ?_⟩
    · have hlj0 : usj.length = cvj.levelParams.length := hlj'.trans hlj
      rw [r.hde, htj usj hlj0] at hTVja
      rw [hlfj usj hlj0] at hfR hnept ⊢
      obtain ⟨usj₂, ys₂, TVja₂, restC₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        hT hne usj hlj0 TVja hTVja ρ xs ys restR restC hxs hys hfR hfC hwx hwy hnept
      refine ⟨usj₂, ys₂, TVja₂, restC₂, h1.trans hlj.symm, ?_, ?_, h4, h5, h6, h7, ?_⟩
      · exact (hsub us hus0 usj₂ h1).mpr h2
      · rw [r.hde, htj usj₂ h1]; exact h3
      · rw [hlfj usj₂ h1]; exact h8
    · have hlj0 : usj.length = cvj.levelParams.length := hlj'.trans hlj
      rw [r.hde, htj usj hlj0] at hTVja
      obtain ⟨hP, hU⟩ := hPU usj hlj0 ((hsub us hus0 usj hlj0).mp hsj) TVja hTVja
      rw [hlfj usj hlj0, r.hfire]
      refine ⟨hP, fun ρ xs ys restR restC hxs hys hfR hfC hwx hwy hA hB hD => ?_⟩
      refine hU ρ xs ys restR restC hxs hys hfR hfC hwx hwy hA ?_ hD
      intro lvls pins hfire
      have hcv := r.hnest lvls pins hfire
      subst hcv
      intro hpt i hi vpa hvpa
      exact hB lvls pins hfire hpt i hi vpa (by rw [r.hde]; exact hvpa)

theorem recRuleLaw_ren (r : RuleRen m m' φ n cv cv' mI rP isK rl rl')
    (hL : RecRuleLaw m φ n cv mI rP isK rl) : RecRuleLaw m' φ n cv' mI rP isK rl' := by
  obtain ⟨hle, hmain, hX⟩ := hL
  refine ⟨hle, fun us hus => ?_, recRuleExtra_ren r hX⟩
  have hus0 : us.length = cv.levelParams.length := hus.trans r.hlen
  obtain ⟨Ra, hRa, hok, hpins, hlaw⟩ := hmain us hus0
  refine ⟨Ra, by rw [r.hde, r.hrhs us hus0]; exact hRa, hok, fun lvls pins hfire i hi => ?_,
    fun cvj' cnP cnF hfc usj ρ xs ys TVa TVja restR restC hxs hys hlj' hsj hwy hpt hTVa hTVja hfR hfC => ?_⟩
  · rw [r.hfire] at hfire
    have hcv := r.hnest lvls pins hfire
    subst hcv
    obtain ⟨vpa, hvpa, hg⟩ := hpins lvls pins hfire i hi
    refine ⟨vpa, by rw [r.hde]; exact hvpa, fun ρ zs TVa restR hz hw hTVa hfit => ?_⟩
    rw [r.hde] at hTVa
    exact hg ρ zs TVa restR hz hw hTVa hfit
  · rw [r.hctor] at hfc
    obtain ⟨cvj, hfcj, hlj, htj, hlfj, -, hcmp, hsub, -⟩ := r.hcj cvj' cnP cnF hfc
    have hlj0 : usj.length = cvj.levelParams.length := hlj'.trans hlj
    rw [r.hde, r.hty us hus0] at hTVa
    rw [r.hde, htj usj hlj0] at hTVja
    rw [r.hctor, hlfj usj hlj0] at hfR hpt ⊢
    rw [r.hnf] at hys
    rw [r.hleaf us hus0]
    have hsj' := (hsub us hus0 usj hlj0).mp (by rw [← hcmp us hus0]; exact hsj)
    exact hlaw cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxs hys hlj0 hsj' hwy hpt hTVa hTVja
      hfR hfC

end Law

/-! ## The two sides of one constant -/

/-- **Two instantiations agree at one list of names iff at another**:
the assignment is positional. -/
theorem substFn_pos {φ : Name → Nat} :
    ∀ {ks ks' : List Name} {a b : List Level}, ks.Nodup → ks'.Nodup →
      ks.length = ks'.length → a.length = ks.length → b.length = ks.length →
      (∀ q ∈ ks, Level.substFn φ ks a q = Level.substFn φ ks b q) →
      Level.substFn φ ks' a = Level.substFn φ ks' b
  | [], [], [], [], _, _, _, _, _, _ => rfl
  | k :: ks, k' :: ks', x :: a, y :: b, hn, hn', hl, ha, hb, h => by
    obtain ⟨hk, hnt⟩ := List.nodup_cons.mp hn
    have hhd : Level.eval φ x = Level.eval φ y := by
      have := h k List.mem_cons_self
      simpa [Level.substFn] using this
    have htl := substFn_pos (φ := φ) (a := a) (b := b) hnt (List.nodup_cons.mp hn').2
      (Nat.succ.inj hl) (Nat.succ.inj ha) (Nat.succ.inj hb) (fun q hq => by
        have := h q (List.mem_cons_of_mem _ hq)
        have hne : k ≠ q := fun he => hk (he ▸ hq)
        simpa [Level.substFn, hne] using this)
    funext q
    simp only [Level.substFn]
    by_cases hq : k' = q
    · rw [ite_eq_left hq, ite_eq_left hq, hhd]
    · rw [ite_eq_right hq, ite_eq_right hq, htl]

section Pair

variable {pin : ConstantInfo} {c c' : ConstantInfo}

/-- A copy's common data, spelled out. -/
theorem _root_.ConLeche.Verify.PinCopy.cv (h : PinCopy c pin) :
    c.toConstantVal = pin.toConstantVal.atLps c.toConstantVal.levelParams := by
  have := congrArg ConstantInfo.toConstantVal h.1
  rwa [atLps_cv] at this

/-- One copy is the other renamed. -/
theorem _root_.ConLeche.Verify.PinCopy.type_eq (h : PinCopy c pin) (h' : PinCopy c' pin)
    (hwf : pin.toConstantVal.type.allLevelParamsDefined pin.toConstantVal.levelParams = true) :
    c'.toConstantVal.type = c.toConstantVal.type.instantiateLevelParams
      c.toConstantVal.levelParams (c'.toConstantVal.levelParams.map Level.param) := by
  have e : ∀ {d : ConstantInfo}, PinCopy d pin → d.toConstantVal.type
      = pin.toConstantVal.type.instantiateLevelParams pin.toConstantVal.levelParams
          (d.toConstantVal.levelParams.map Level.param) := fun hd =>
    congrArg ConstantVal.type hd.cv
  rw [e h, inst_ren h.2.1 h.2.2.symm (by rw [List.length_map, h.2.2, h'.2.2]) _ hwf]
  exact e h'

/-- Two copies instantiate alike. -/
theorem _root_.ConLeche.Verify.PinCopy.inst (h : PinCopy c pin) (h' : PinCopy c' pin)
    (hwf : pin.toConstantVal.type.allLevelParamsDefined pin.toConstantVal.levelParams = true)
    {us : List Level} (hus : us.length = c.toConstantVal.levelParams.length) :
    c'.toConstantVal.type.instantiateLevelParams c'.toConstantVal.levelParams us
      = c.toConstantVal.type.instantiateLevelParams c.toConstantVal.levelParams us := by
  have e : ∀ {d : ConstantInfo}, PinCopy d pin → d.toConstantVal.type
      = pin.toConstantVal.type.instantiateLevelParams pin.toConstantVal.levelParams
          (d.toConstantVal.levelParams.map Level.param) := fun hd =>
    congrArg ConstantVal.type hd.cv
  rw [e h', e h,
    inst_ren h'.2.1 h'.2.2.symm (by rw [hus, h.2.2, h'.2.2]) _ hwf,
    inst_ren h.2.1 h.2.2.symm hus _ hwf]

/-- Which kind of constant. -/
@[expose] def conKind : ConstantInfo → Nat
  | .axiomInfo .. => 0
  | .defnInfo .. => 1
  | .thmInfo .. => 2
  | .indInfo .. => 3
  | .ctorInfo .. => 4
  | .recInfo .. => 5

theorem conKind_atLps (ci : ConstantInfo) (ps : List Name) : conKind (ci.atLps ps) = conKind ci := by
  cases ci <;> rfl

theorem _root_.ConLeche.Verify.PinCopy.kind (h : PinCopy c pin) : conKind c = conKind pin := by
  rw [h.1, conKind_atLps]

/-- A copy of a pin is no definition. -/
theorem _root_.ConLeche.Verify.PinCopy.not_defn (h : PinCopy c pin) (hs : pinShapeOk pin = true)
    (cv : ConstantVal) (v : Expr) (hint : ConLeche.ReducibilityHint) :
    c ≠ .defnInfo cv v hint := by
  intro he
  have hk := h.kind
  rw [he] at hk
  cases pin with
  | defnInfo _ _ _ => simp [pinShapeOk] at hs
  | _ => exact nomatch hk

/-- A copy of a constructor's pin is a constructor. -/
theorem _root_.ConLeche.Verify.PinCopy.ctor {cv : ConstantVal} {nP nF : Nat}
    (h : PinCopy (.ctorInfo cv nP nF) pin) (h' : PinCopy c' pin) :
    ∃ cv', c' = .ctorInfo cv' nP nF := by
  have h1 := h.1
  have h2 := h'.1
  generalize c'.toConstantVal.levelParams = ps' at h2
  cases pin with
  | ctorInfo cvp a b =>
    simp only [ConstantInfo.atLps] at h1 h2
    injection h1 with _ e1 e2
    subst e1; subst e2
    exact ⟨_, h2⟩
  | _ => exact nomatch h.kind

/-- A copy of an inductive's pin is an inductive. -/
theorem _root_.ConLeche.Verify.PinCopy.ind {cv : ConstantVal} {caps : IndCaps}
    (h : PinCopy (.indInfo cv caps) pin) (h' : PinCopy c' pin) :
    ∃ cv' caps', c' = .indInfo cv' caps' ∧ caps'.unitlike = caps.unitlike ∧
      caps'.unitParams = caps.unitParams ∧ caps'.eta = caps.eta ∧ caps'.etaParams = caps.etaParams := by
  have h1 := h.1
  have h2 := h'.1
  generalize c'.toConstantVal.levelParams = ps' at h2
  have hps : (ConstantInfo.indInfo cv caps).toConstantVal.levelParams = cv.levelParams := rfl
  rw [hps] at h1
  cases pin with
  | indInfo cvp cp =>
    simp only [ConstantInfo.atLps] at h1 h2
    injection h1 with _ e2
    subst e2
    exact ⟨_, _, h2, rfl, rfl, rfl, rfl⟩
  | _ => exact nomatch h.kind

/-- What a recursor's copy has of the rules. -/
theorem _root_.ConLeche.Verify.PinCopy.recr {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule}
    (h : PinCopy (.recInfo cv mI rP isK rules) pin) (h' : PinCopy c' pin)
    (hs : pinShapeOk pin = true) :
    ∃ cv' rules', c' = .recInfo cv' mI rP isK rules' ∧ ∀ rl' ∈ rules', ∃ rl ∈ rules,
      RecRule.ctor rl' = RecRule.ctor rl ∧ RecRule.nfields rl' = RecRule.nfields rl ∧
      RecRule.fire rl' = RecRule.fire rl ∧ RecRule.fire rl = .plain ∧
      RecRule.rhs rl' = (RecRule.rhs rl).instantiateLevelParams cv.levelParams
        (cv'.levelParams.map Level.param) := by
  have hnd : cv.levelParams.Nodup := h.2.1
  have hl : cv.levelParams.length = pin.toConstantVal.levelParams.length := h.2.2
  have hl' := h'.2.2
  have h1 := h.1
  have h2 := h'.1
  generalize c'.toConstantVal.levelParams = ps' at h2 hl'
  have hps : (ConstantInfo.recInfo cv mI rP isK rules).toConstantVal.levelParams = cv.levelParams := rfl
  rw [hps] at h1
  cases pin with
  | recInfo cvp a b k rs =>
    simp only [ConstantInfo.atLps] at h1 h2
    injection h1 with _ e1 e2 e3 e4
    subst e1; subst e2; subst e3; subst e4
    refine ⟨_, _, h2, fun rl' hrl' => ?_⟩
    obtain ⟨rp, hrp, rfl⟩ := List.mem_map.mp hrl'
    simp only [pinShapeOk, List.all_eq_true, Bool.and_eq_true] at hs
    obtain ⟨hdef, hpl⟩ := hs rp hrp
    have hplain : RecRule.fire rp = .plain := by
      revert hpl
      cases RecRule.fire rp <;> first | (intro; rfl) | (intro h; exact nomatch h)
    refine ⟨_, List.mem_map_of_mem hrp, rfl, rfl, rfl, hplain, ?_⟩
    show (RecRule.rhs rp).instantiateLevelParams cvp.levelParams (ps'.map Level.param) =
      ((RecRule.rhs rp).instantiateLevelParams cvp.levelParams (cv.levelParams.map Level.param)).instantiateLevelParams
        cv.levelParams (ps'.map Level.param)
    exact (inst_ren (ks := cvp.levelParams) (ps := cv.levelParams) (us := ps'.map Level.param) hnd
      hl.symm (by rw [List.length_map]; exact hl'.trans hl.symm) _ hdef).symm
  | _ => exact nomatch h.kind

end Pair

theorem _root_.ConLeche.Verify.ConstRen.len {c c' : ConstantInfo} (h : ConstRen c c') :
    c'.toConstantVal.levelParams.length = c.toConstantVal.levelParams.length := by
  rcases h with rfl | ⟨-, h1, h2⟩
  · rfl
  · rw [h1.2.2, h2.2.2]

theorem _root_.ConLeche.Verify.ConstRen.inst {c c' : ConstantInfo} (h : ConstRen c c') {us : List Level}
    (hus : us.length = c.toConstantVal.levelParams.length) :
    c'.toConstantVal.type.instantiateLevelParams c'.toConstantVal.levelParams us
      = c.toConstantVal.type.instantiateLevelParams c.toConstantVal.levelParams us := by
  rcases h with rfl | ⟨hr, h1, h2⟩
  · rfl
  · exact PinCopy.inst h1 h2 (pinnedInfo_wf hr).1 hus

theorem _root_.ConLeche.Verify.ConstRen.ctor {cv : ConstantVal} {nP nF : Nat} {c' : ConstantInfo}
    (h : ConstRen (.ctorInfo cv nP nF) c') : ∃ cv', c' = .ctorInfo cv' nP nF := by
  rcases h with rfl | ⟨-, h1, h2⟩
  · exact ⟨_, rfl⟩
  · exact h1.ctor h2

theorem _root_.ConLeche.Verify.ConstRen.ind {cv : ConstantVal} {caps : IndCaps} {c' : ConstantInfo}
    (h : ConstRen (.indInfo cv caps) c') : ∃ cv' caps', c' = .indInfo cv' caps' := by
  rcases h with rfl | ⟨-, h1, h2⟩
  · exact ⟨_, _, rfl⟩
  · obtain ⟨cv', caps', he, -⟩ := h1.ind h2
    exact ⟨cv', caps', he⟩

/-- **A stored type, across the renaming.** -/
theorem denote_pair {env : Env} (m : EnvModel V env) {c c' : ConstantInfo} (hr : ConstRen c c')
    (ψ : Name → Nat) (d : Nat) :
    denote m.acval env ψ d c'.toConstantVal.type
      = denote m.acval env
          (Level.substFn ψ c.toConstantVal.levelParams
            (c'.toConstantVal.levelParams.map Level.param)) d c.toConstantVal.type := by
  rcases hr with rfl | ⟨hres, h1, h2⟩
  · rw [Level.substFn_param_self]
  · rw [PinCopy.type_eq h1 h2 (pinnedInfo_wf hres).1, denotePInstLevels]

theorem renTr_pair {env env' : Env} {n : Name} {c c' : ConstantInfo}
    (hf : env.find? n = some c) (hf' : env'.find? n = some c') (ψ : Name → Nat) :
    renTr env env' n ψ = Level.substFn ψ c.toConstantVal.levelParams
      (c'.toConstantVal.levelParams.map Level.param) := by
  unfold renTr
  rw [hf, hf']

/-- **A pinned leaf's value reads its pin's parameters only.** -/
theorem pinnedStructT_congr {n : Name} {ψ₁ ψ₂ : Name → Nat}
    (hres : reservedBasisNames.contains n = true)
    (hag : ∀ p ∈ (pinnedInfo n).toConstantVal.levelParams, ψ₁ p = ψ₂ p) :
    pinnedStructT n ψ₁ = pinnedStructT n ψ₂ := by
  have hmem : n ∈ reservedBasisNames := by simpa using hres
  simp only [reservedBasisNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hu : uN ∈ (pinnedInfo n).toConstantVal.levelParams → ψ₁ uN = ψ₂ uN := hag uN
  have hv : vN ∈ (pinnedInfo n).toConstantVal.levelParams → ψ₁ vN = ψ₂ vN := hag vN
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> first
    | rfl
    | (have e := hu (by decide); simp only [pinnedStructT, e]; rfl)
    | (have e := hu (by decide); have e' := hv (by decide); simp only [pinnedStructT, e, e']; rfl)
    | (show some (Term.const .quotLift [ψ₁ uN, ψ₁ vN]) = some (Term.const .quotLift [ψ₂ uN, ψ₂ vN])
       rw [hu (by decide), hv (by decide)])

/-- A renamed list's values read the new names only. -/
theorem substFn_map_param_agree {ψ₁ ψ₂ : Name → Nat} :
    ∀ {ks ps : List Name}, ks.length = ps.length → (∀ q ∈ ps, ψ₁ q = ψ₂ q) →
      ∀ p ∈ ks, Level.substFn ψ₁ ks (ps.map Level.param) p
        = Level.substFn ψ₂ ks (ps.map Level.param) p
  | k :: ks, q :: ps, hl, hag, p, hp => by
    simp only [List.map_cons, Level.substFn]
    by_cases h : k = p
    · rw [ite_eq_left h, ite_eq_left h]
      simpa [Level.eval] using hag q List.mem_cons_self
    · rw [ite_eq_right h, ite_eq_right h]
      have hp' : p ∈ ks := by
        rcases List.mem_cons.mp hp with rfl | h'
        · exact absurd rfl h
        · exact h'
      exact substFn_map_param_agree (Nat.succ.inj hl)
        (fun x hx => hag x (List.mem_cons_of_mem _ hx)) p hp'
  | [], _, _, _, _, hp => absurd hp List.not_mem_nil
  | _ :: _, [], hl, _, _, _ => nomatch hl

/-! ## The carrier -/

section Base

variable {env env' : Env}

theorem constWF_ren (m : EnvModel V env) (h : RenEnv env env') {c' : ConstantInfo}
    (hc : c' ∈ env'.consts) : ConstWF env' c' := by
  obtain ⟨c, hcm, hr⟩ := h.mem hc
  have hwf := m.wf.consts c hcm
  have hres : (fun e : Expr => e.constsResolve env') = fun e => e.constsResolve env :=
    funext h.constsResolve
  rcases hr with rfl | ⟨hrs, h1, h2⟩
  · unfold ConstWF at hwf ⊢
    simp only [h.constsResolve, hres]
    exact hwf
  · have hshape := (pinnedInfo_wf hrs).2
    have hdef := hwf.2.1
    have hty := PinCopy.type_eq h1 h2 (pinnedInfo_wf hrs).1
    have hlen : c.toConstantVal.levelParams.length = c'.toConstantVal.levelParams.length := by
      rw [h1.2.2, h2.2.2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hty, Expr.hasFvar_instantiateLevelParams]; exact hwf.1
    · rw [hty]; exact expr_defined_ren hlen _ hdef
    · rw [hty, Expr.constsResolve_instantiateLevelParams, h.constsResolve]; exact hwf.2.2.1
    · rw [hty, Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
    · intro cv v hint he
      exact absurd he (h2.not_defn hshape cv v hint)
    · intro cv' mI rP isK rules' he
      subst he
      -- the old side is a recursor as well
      cases c with
      | recInfo cv mI0 rP0 isK0 rules =>
        obtain ⟨cv₂, rules₂, he, hrl⟩ := h1.recr h2 hshape
        injection he with e0 e1 e2 e3 e4
        subst e0; subst e1; subst e2; subst e3; subst e4
        intro r' hr'
        obtain ⟨rl, hrl0, -, -, hfire, hplain, hrhs⟩ := hrl r' hr'
        obtain ⟨g1, g2, g3, g4, -⟩ := hwf.2.2.2.2.2.1 cv mI rP isK rules rfl rl hrl0
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hrhs, Expr.hasFvar_instantiateLevelParams]; exact g1
        · rw [hrhs]; exact expr_defined_ren hlen _ g2
        · rw [hrhs, Expr.constsResolve_instantiateLevelParams, h.constsResolve]; exact g3
        · rw [hrhs, Expr.looseBVarsBounded_instantiateLevelParams]; exact g4
        · intro lvls pins hn
          rw [hfire, hplain] at hn
          exact nomatch hn
      | _ => exact nomatch h1.kind.trans h2.kind.symm
    · intro cv' caps' he
      subst he
      cases c with
      | indInfo cv caps =>
        obtain ⟨cv₂, caps₂, he, e1, e2, e3, e4⟩ := h1.ind h2
        injection he with e0 e5
        subst e0; subst e5
        obtain ⟨hu, he'⟩ := hwf.2.2.2.2.2.2 cv caps rfl
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · rw [e2, show cv'.type = cv.type.instantiateLevelParams cv.levelParams
            (cv'.levelParams.map Level.param) from hty]
          exact Expr.stripPis_instantiateLevelParams_isSome cv.levelParams
            (cv'.levelParams.map Level.param) caps.unitParams (hu (by rw [← e1]; exact hx))
        · rw [e4, show cv'.type = cv.type.instantiateLevelParams cv.levelParams
            (cv'.levelParams.map Level.param) from hty]
          exact Expr.stripPis_instantiateLevelParams_isSome cv.levelParams
            (cv'.levelParams.map Level.param) caps.etaParams (he' (by rw [← e3]; exact hx))
      | _ => exact nomatch h1.kind.trans h2.kind.symm

theorem envWF_ren (m : EnvModel V env) (h : RenEnv env env') : EnvWF env' where
  consts := fun _ hc => constWF_ren m h hc
  tables := fun t ht => by
    rw [h.tables] at ht
    obtain ⟨h1, h2, h3⟩ := m.wf.tables t ht
    refine ⟨by rw [h.isSome]; exact h1, h2, fun i b hb => ?_⟩
    obtain ⟨g1, g2, g3, g4⟩ := h3 i b hb
    exact ⟨g1, g2, by rw [h.constsResolve]; exact g3, g4⟩

theorem projOk_ren (m : EnvModel V env) (h : RenEnv env env') : ProjOkT env' := by
  intro T tbl hf i hi
  rw [h.findTable] at hf
  obtain ⟨h2, h3, h4, h5, ⟨cvT, caps, hT, hlT⟩, ⟨cvC, hC, hlC, hs⟩⟩ := m.proj_ok T tbl hf i hi
  exact ⟨h2, h3, h4, h5, ⟨cvT, caps, (h.find_nonres h2).trans hT, hlT⟩,
    ⟨cvC, (h.find_nonres h4).trans hC, hlC, hs⟩⟩

theorem find_ctor_ren (h : RenEnv env env') {x : Name} {cvj : ConstantVal} {a b : Nat}
    (hf : env.find? x = some (.ctorInfo cvj a b)) :
    ∃ cvj', env'.find? x = some (.ctorInfo cvj' a b) := by
  rcases h.find x with ⟨h1, -⟩ | ⟨c, c', h1, h2, hr⟩
  · rw [h1] at hf; exact nomatch hf
  · rw [h1] at hf
    obtain rfl := Option.some.inj hf
    obtain ⟨cv', rfl⟩ := hr.ctor
    exact ⟨cv', h2⟩

theorem recCtors_ren (m : EnvModel V env) (h : RenEnv env env') : RecCtorsStored env' := by
  intro n cv' mI rP isK rules' hf' r' hr'
  rcases h.find n with ⟨-, h2⟩ | ⟨c, c', h1, h2, hr⟩
  · rw [h2] at hf'; exact nomatch hf'
  · rw [h2] at hf'
    obtain rfl := Option.some.inj hf'
    rcases hr with rfl | ⟨hrs, h3, h4⟩
    · obtain ⟨cvj, a, b, hj⟩ := m.rec_ctors n cv' mI rP isK rules' h1 r' hr'
      obtain ⟨cvj', hj'⟩ := find_ctor_ren h hj
      exact ⟨cvj', a, b, hj'⟩
    · cases c with
      | recInfo cv mI0 rP0 isK0 rules =>
        obtain ⟨cv₂, rules₂, he, hrl⟩ := h3.recr h4 (pinnedInfo_wf hrs).2
        injection he with e0 e1 e2 e3 e4
        subst e0; subst e1; subst e2; subst e3; subst e4
        obtain ⟨rl, hrl0, hct, -⟩ := hrl r' hr'
        obtain ⟨cvj, a, b, hj⟩ := m.rec_ctors n _ _ _ _ _ h1 rl hrl0
        obtain ⟨cvj', hj'⟩ := find_ctor_ren h hj
        exact ⟨cvj', a, b, by rw [hct]; exact hj'⟩
      | _ => exact nomatch h3.kind.trans h4.kind.symm

theorem acvalParams_ren (m : EnvModel V env) (h : RenEnv env env') :
    ∀ (n : Name) (ci : ConstantInfo), env'.find? n = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        renAcval m.acval env env' n ψ₁ = renAcval m.acval env env' n ψ₂ := by
  intro n ci hf' ψ₁ ψ₂ hag
  rcases h.find n with ⟨-, h2⟩ | ⟨c, c', h1, h2, hr⟩
  · rw [h2] at hf'; exact nomatch hf'
  · rw [h2] at hf'
    obtain rfl := Option.some.inj hf'
    unfold renAcval
    refine m.acval_params n c h1 _ _ fun p hp => ?_
    rw [renTr_pair h1 h2, renTr_pair h1 h2]
    rcases hr with rfl | ⟨-, h3, h4⟩
    · rw [Level.substFn_param_self, Level.substFn_param_self]
      exact hag p hp
    · have hl : c.toConstantVal.levelParams.length = c'.toConstantVal.levelParams.length := by
        rw [h3.2.2, h4.2.2]
      exact substFn_map_param_agree hl hag p hp

theorem basisPinned_ren (m : EnvModel V env) (h : RenEnv env env')
    (hlink : ∀ n ci, env'.find? n = some ci → reservedBasisNames.contains n = true →
      PinLinked env' n ci) :
    BasisPinnedTT env' (renAcval m.acval env env') := by
  intro n ci hf' hres
  rcases h.find n with ⟨-, h2⟩ | ⟨c, c', h1, h2, hr⟩
  · rw [h2] at hf'; exact nomatch hf'
  · rw [h2] at hf'
    obtain rfl := Option.some.inj hf'
    obtain ⟨hcp, -, hleaf⟩ := m.basis_pinned n c h1 hres
    have hl' : c'.toConstantVal.levelParams.length = c.toConstantVal.levelParams.length := hr.len
    refine ⟨?_, hlink n c' h2 hres, fun t ψ ht => ?_⟩
    · rcases hr with rfl | ⟨-, -, h4⟩
      · exact hcp
      · have hnm : c.name = n := by simpa using Env.find?_name h1
        rw [hnm] at h4
        exact h4
    · unfold renAcval
      rw [renTr_pair h1 h2]
      refine hleaf t _ ?_
      rw [← ht]
      refine pinnedStructT_congr hres fun p hp => ?_
      unfold pinVal
      rcases hr with rfl | ⟨-, -, -⟩
      · rw [Level.substFn_param_self]
      · refine substFn_ren hcp.2.1 hcp.2.2.symm ?_ (fun _ _ => rfl) p hp
        rw [List.length_map, hl']

/-- **The carrier at the new names.** -/
@[expose] def EnvModel.rename (m : EnvModel V env) (h : RenEnv env env')
    (hlink : ∀ n ci, env'.find? n = some ci → reservedBasisNames.contains n = true →
      PinLinked env' n ci) : EnvModel V env' where
  wf := envWF_ren m h
  acval := renAcval m.acval env env'
  cval_closed := fun n _ => m.cval_closed n _
  basis_pinned := basisPinned_ren m h hlink
  proj_ok := projOk_ren m h
  rec_ctors := recCtors_ren m h
  acval_params := acvalParams_ren m h
  acval_wellDenoted := fun n _ ρ => m.acval_wellDenoted n _ ρ

end Base

end ConLeche.Model
