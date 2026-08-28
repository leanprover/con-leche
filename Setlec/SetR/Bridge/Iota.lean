import Setlec.SetR.Bridge.Major
import Setlec.Verify.Denote.OpenRevDenote
import Setlec.Verify.InstSpine

/-!
# `IotaStepR`, discharged (task #148, T3, batch g) — `CheckStepR` closes

R11, the widest rule of the family, and with it the last obligation of
the bridge's fuel induction.

`iotaRec_inv` returns every side condition R11 names, so the clause is a
transcription; the four places where it is not are worth naming, because
each is a small general fact rather than iota-specific work:

* **the level guard reads no arguments** (`recFireComparands_fst_nil`):
  the `.1` component of `recFireComparands` ignores its `args` in *both*
  fire branches, so the rule's spelling at `[]` and the checker's at the
  real spine agree by `cases … <;> rfl`;
* **the `Nat`-literal major conversion is invisible**
  (`denote_litToCtorIfNat`): `⟦.lit (n+1)⟧` *is* `.app ⟦succ⟧ ⟦.lit n⟧`
  and `⟦.lit 0⟧` *is* the `Nat.zero` valuation, which is design §7.2's
  "`litToCtorIfNat` contributes zero rules" discharged;
* **the residual is the telescope's** (`Tele.residual` +
  `denote_piResidualR`): the `Tele` premise's residual and the checker's
  `piResidual` are the same walk, so premise 6's decomposition is
  `denote_mkAppN_inv` on that shared value;
* **only one nested comparand is known to denote** — the rule
  hypothesises exactly the `i`-th pin's opening — so that component is
  pulled out of `defEqList` *syntactically* (`defEqListP_get`) rather
  than through a whole-list `DenoteSpine`.  Reaching for the list-level
  lemma first is the natural move and it does not work; the premise's
  shape is telling you which one it wants.

The nested pin bridge itself is `denote_openRev` +
`denote_openRev_base`: the checker's comparand is
`instSpine (args.take rP) (rP-1) pin`, the rule's is
`instRevChain (xs.take rP) ⟦openRev 0 rP pin⟧`, and those two lemmas are
exactly that identity plus its base-independence.  The `rP ≤ mI` the
walk needs is `EnvR.rec_params_le` — the bridge-side half of the D3
split, drawing on the same install component the soundness side uses.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify
variable {mode : CheckMode} {env : Env}

/-- The level comparand reads no arguments, in either fire branch. -/
theorem recFireComparands_fst_nil (rl : RecRule) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) :
    (recFireComparands rl lps us cvjLps args rP).1
      = (recFireComparands rl lps us cvjLps [] rP).1 := by
  unfold recFireComparands
  cases rl.fire <;> rfl

/-- A successful `defEqList`'s components — the form the nested pin
premise needs, since only *one* index's comparand is known to denote
(the rule hypothesises exactly that one). -/
theorem defEqListP_get {env : Env} {fuel d : Nat} :
    ∀ {as bs : List Expr}, defEqListP mode env fuel d as bs = .ok true →
      ∀ i, i < as.length →
        isDefEqCore mode env fuel d (as.getD i default) (bs.getD i default)
          = .ok true := by
  intro as
  induction as with
  | nil => intro bs h i hi; exact absurd hi (by simp)
  | cons x xs ih =>
    intro bs h i hi
    cases bs with
    | nil => simp [defEqListP, defEqList, pure, Except.pure] at h
    | cons y ys =>
      obtain ⟨hxy, htail⟩ := defEqList_step_inv h
      match i with
      | 0 => exact hxy
      | j + 1 => simpa using ih htail j (by simpa using hi)

/-- A mapped spine denotes pointwise, at any index type. -/
theorem DenoteSpine.map_pointwise {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {α : Type _} {g : α → Expr} {G : α → VExpr} :
    ∀ (l : List α), (∀ x ∈ l, denote cval env φ d (g x) = some (G x)) →
      DenoteSpine cval env φ d (l.map g) (l.map G) := by
  intro l
  induction l with
  | nil => intro _; exact DenoteSpine.nil
  | cons x xs ih =>
    intro h
    exact DenoteSpine.cons (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- A successful `defEqList` relates lists of equal length. -/
theorem defEqListP_length {env : Env} {fuel d : Nat} :
    ∀ {as bs : List Expr}, defEqListP mode env fuel d as bs = .ok true →
      as.length = bs.length := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil => rfl
    | cons _ _ => simp [defEqListP, defEqList, pure, Except.pure] at h
  | cons x xs ih =>
    intro bs h
    cases bs with
    | nil => simp [defEqListP, defEqList, pure, Except.pure] at h
    | cons y ys => simpa using ih (defEqList_step_inv h).2

/-- A `DefEqL` derivation's components. -/
theorem DefEqL.get {cval : TConstVal} {φ : Name → Nat} {Δ : List VExpr} :
    ∀ {as bs : List VExpr}, DefEqL mode env cval φ Δ as bs →
      ∀ i, i < as.length →
        DefEq mode env cval φ Δ (as.getD i default) (bs.getD i default) := by
  intro as
  induction as with
  | nil => intro bs h i hi; exact absurd hi (by simp)
  | cons a as ih =>
    intro bs h i hi
    cases h with | cons hab htail => ?_
    match i with
    | 0 => exact hab
    | j + 1 =>
      simpa using ih htail j (by simpa using hi)

/-- The frame conditions of a `∀`-telescope's residual: it is built by
instantiating a scoped type with scoped arguments. -/
theorem piResidual_frameR {cval : TConstVal} {φ : Name → Nat} {d : Nat}
    {Δ : List VExpr} :
    ∀ {T : Expr} {args : List Expr} {rest : Expr},
      piResidual T args = some rest →
      Expr.WScoped d T → T.looseBVarsBounded 0 = true →
      Expr.LeavesBounded T → CtxOkR mode cval env φ d Δ T →
      (∀ x ∈ args, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkR mode cval env φ d Δ x) →
      Expr.WScoped d rest ∧ rest.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded rest ∧ CtxOkR mode cval env φ d Δ rest := by
  intro T args
  induction args generalizing T with
  | nil =>
    intro rest h hw hb hL hCt _
    obtain rfl : rest = T := (Option.some.inj h).symm
    exact ⟨hw, hb, hL, hCt⟩
  | cons a as ih =>
    intro rest h hw hb hL hCt hfr
    match T, h with
    | .bvar _, h => exact nomatch h
    | .fvar _ _ _, h => exact nomatch h
    | .sort _, h => exact nomatch h
    | .const _ _, h => exact nomatch h
    | .app _ _, h => exact nomatch h
    | .lam _ _ _ _, h => exact nomatch h
    | .letE _ _ _ _, h => exact nomatch h
    | .lit _, h => exact nomatch h
    | .proj _ _ _, h => exact nomatch h
    | .forallE n ty body mb, h =>
    obtain ⟨hwa, hba, hLa, hCa⟩ := hfr a (by simp)
    simp only [Expr.WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    refine ih h (Expr.WScoped.instantiate1_gen hwa 0 hw.2)
      (Expr.looseBVarsBounded_instantiate1_gen hba hb.2) (fun l hl => ?_)
      ⟨hCt.1, fun l hl => ?_⟩ (fun x hx => hfr x (by simp [hx])) <;>
    · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · first
        | exact hL l (by simp [Expr.fvarLeaves, h2])
        | exact hCt.2 l (by simp [Expr.fvarLeaves, h2])
      · first
        | exact hLa l h2
        | exact hCa.2 l h2

/-- A `Tele` walk's residual is the telescope's `piResidualV`. -/
theorem Tele.residual {cval : TConstVal} {φ : Name → Nat} {Δ : List VExpr} :
    ∀ {T : VExpr} {as : List VExpr} {rest : VExpr},
      Tele mode env cval φ Δ T as rest → piResidualV T as = some rest := by
  intro T as
  induction as generalizing T with
  | nil => intro rest h; cases h; rfl
  | cons a as ih =>
    intro rest h
    cases h with | cons _ _ htail => exact ih htail

/-- **The `Nat`-literal major conversion is invisible to the
denotation** (design §7.2: `litToCtorIfNat` contributes zero rules).
`⟦.lit (n+1)⟧` *is* `.app ⟦succ⟧ (natLitT n)` and `⟦.lit 0⟧` *is* the
`Nat.zero` valuation, so the constructor form denotes identically. -/
theorem denote_litToCtorIfNat {cval : TConstVal} {φ : Name → Nat} (d : Nat)
    (e : Expr) :
    denote cval env φ d (litToCtorIfNat env e) = denote cval env φ d e := by
  match e with
  | .lit (.natVal n) =>
    rw [litToCtorIfNat]
    by_cases hg : natLitSupported env = true
    · rw [if_pos hg]
      match n with
      | 0 =>
        rw [natLitToConstructor, denote_natZeroConstR hg, denote_natLit,
          if_pos hg]
        rfl
      | k + 1 =>
        rw [natLitToConstructor, denote_app, denote_natSuccConstR hg,
          denote_natLit, if_pos hg, denote_natLit, if_pos hg]
        rfl
    · rw [if_neg hg]
  | .lit (.strVal _) | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _
  | .app _ _ | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _
  | .proj _ _ _ => rfl

/-- The frame conditions survive the `Nat`-literal major conversion. -/
theorem frame_litToCtorIfNat {cval : TConstVal} {φ : Name → Nat} {d : Nat}
    {Δ : List VExpr} {e : Expr}
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOkR mode cval env φ d Δ e) :
    Expr.WScoped d (litToCtorIfNat env e) ∧
      (litToCtorIfNat env e).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (litToCtorIfNat env e) ∧
      CtxOkR mode cval env φ d Δ (litToCtorIfNat env e) := by
  match e with
  | .lit (.natVal n) =>
    rw [litToCtorIfNat]
    by_cases hg : natLitSupported env = true
    · rw [if_pos hg]
      refine ⟨natLitToConstructor_WScoped n, natLitToConstructor_looseBVars n,
        fun l hl => ?_, ⟨hC.1, fun l hl => ?_⟩⟩ <;>
      · rw [natLitToConstructor_fvarLeaves] at hl
        exact nomatch hl
    · rw [if_neg hg]; exact ⟨hws, hb, hLb, hC⟩
  | .lit (.strVal _) | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _
  | .app _ _ | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _
  | .proj _ _ _ => exact ⟨hws, hb, hLb, hC⟩

/-- **`IotaStepR`, proved** (R11, with R16 at the major and the
`MajorStepR` rescues). -/
theorem iota_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel) :
    IotaStepR (mode := mode) m φ fuel := by
  intro d Δ e e'' v h hws hb hLb hC hv
  obtain ⟨c, us, cv, mI, rP, rules, major₀, major₁, major, cj, usj, cvj, cnP,
    cnF, r, cbinders, cbody, residual, cr, usr, hfn, hfrec, hlenA, hwmaj,
    hlitmaj, hmajc, hfnmaj, hfcj, hrfind, hlenM, hstripR, hstripC, hfire,
    hlev, hdefP, hcertR, hcertC, hstripEq, hpres, hcbody, hdefI, rfl⟩ :=
    iotaRec_inv h
  -- the recursor spine, denoted
  rw [show e = Expr.mkAppN e.getAppFn e.getAppArgs from
    (Expr.mkAppN_getApp e).symm, hfn] at hv
  obtain ⟨vc, xs, hvc, hspx, rfl⟩ := denote_mkAppN_inv hv
  rw [denote_const, hfrec] at hvc
  dsimp only at hvc
  split at hvc
  · next hlenU =>
    obtain rfl : vc = m.cval c (Level.substFn φ cv.levelParams us) :=
      (Option.some.inj hvc).symm
    have hfrE := frame_spineR (a := e) hws hb hLb hC
    have hmIlt : mI < e.getAppArgs.length := by rw [hlenA]; omega
    have hmemMaj : e.getAppArgs.getD mI (.bvar 0) ∈ e.getAppArgs :=
      getD_mem hmIlt
    obtain ⟨hwM, hbM, hLM, hCM⟩ := hfrE _ hmemMaj
    have hdMaj : denote m.cval env φ d (e.getAppArgs.getD mI (.bvar 0))
        = some (xs.getD mI default) := by
      have hmIx : mI < xs.length := by rw [hspx.length]; exact hmIlt
      have := hspx.get ⟨mI, hmIlt⟩
      simpa [List.getD, List.getElem?_eq_getElem hmIlt,
        List.getElem?_eq_getElem hmIx] using this
    -- the major: whnf, then the literal conversion (R16), then the rescue
    obtain ⟨v₀, hv₀, hR₀, hw₀, hb₀, hL₀, hC₀⟩ :=
      whnf_packageR m φ ihw hwmaj hwM hbM hLM hCM hdMaj
    obtain ⟨v₁, hv₁, hR₁, hw₁, hb₁, hL₁, hC₁⟩ :
        ∃ w, denote m.cval env φ d major₁ = some w ∧
          Red mode env m.cval φ Δ v₀ w ∧
          Expr.WScoped d major₁ ∧ major₁.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded major₁ ∧ CtxOkR mode m.cval env φ d Δ major₁ := by
      rcases litMajorToCtorP_inv hlitmaj with rfl | ⟨s, rfl, hg, hred⟩
      · obtain ⟨hw', hb', hL', hC'⟩ := frame_litToCtorIfNat hw₀ hb₀ hL₀ hC₀
        exact ⟨v₀, by rw [denote_litToCtorIfNat]; exact hv₀, Red.refl,
          hw', hb', hL', hC'⟩
      · obtain ⟨hSC0, hSCc, hSCd⟩ := denote_strLitCtorR m φ hcl hg d s
        obtain ⟨hwc, hbc, hLc, hCc⟩ :=
          frame_strLitCtorR (mode := mode) (cval := m.cval) (φ := φ) s hC.1
        obtain ⟨w, hw, hRw, hww, hbw, hLw, hCw⟩ :=
          whnf_packageR m φ ihw hred hwc hbc hLc hCc hSCd
        rw [denote_strLit, if_pos hg] at hv₀
        obtain rfl : v₀ = strLitT m.cval env φ s := (Option.some.inj hv₀).symm
        exact ⟨w, hw, Red.strLitCtor hg hSC0 hSCc hRw, hww, hbw, hLw, hCw⟩
    obtain ⟨vm, hvm, hRm, hwm, hbm, hLm, hCm⟩ :=
      majorToCtor_stepR m φ hcl ihw ihd ihi hfrec hmajc hw₁ hb₁ hL₁ hC₁ hv₁
    -- the constructor spine
    have hrctor : r.ctor = cj := by
      have := List.find?_some hrfind
      simpa using this
    rw [← hrctor] at hfnmaj hfcj hrfind
    rw [show major = Expr.mkAppN major.getAppFn major.getAppArgs from
      (Expr.mkAppN_getApp major).symm, hfnmaj] at hvm
    obtain ⟨vj, ys, hvj, hspy, rfl⟩ := denote_mkAppN_inv hvm
    rw [denote_const, hfcj] at hvj
    dsimp only at hvj
    split at hvj
    · next hlenUj =>
      obtain rfl : vj = m.cval r.ctor (Level.substFn φ cvj.levelParams usj) :=
        (Option.some.inj hvj).symm
      have hfrM := frame_spineR (a := major) hwm hbm hLm hCm
      -- the three stored denotations
      obtain ⟨TV, hTV0, hTVc, hTVd⟩ := denote_declTypeR m φ hcl hfrec us d
      obtain ⟨hRw, hRb, hRL, hRC⟩ :=
        frame_declTypeR (cval := m.cval) (φ := φ) (mode := mode) m.wf hfrec us d
          hC.1
      obtain ⟨TVj, hTVj0, hTVjc, hTVjd⟩ := denote_declTypeR m φ hcl hfcj usj d
      obtain ⟨hJw, hJb, hJL, hJC⟩ :=
        frame_declTypeR (cval := m.cval) (φ := φ) (mode := mode) m.wf hfcj usj d
          hC.1
      obtain ⟨R, hR0⟩ := m.rec_rhs_denotes _ _ _ _ _ hfrec r
        (List.mem_of_find?_eq_some hrfind) us φ
      obtain ⟨-, -, -, -, -, hrec', -⟩ := m.wf _ (find?_mem hfrec)
      obtain ⟨hRnf, -, -, hRbd, -⟩ := hrec' cv mI rP rules rfl r
        (List.mem_of_find?_eq_some hrfind)
      obtain ⟨hRc, hRd⟩ := denote_closedExprR hcl
        (by rw [Expr.hasFvar_instantiateLevelParams]; exact hRnf)
        (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hRbd) hR0
      -- the recursor telescope, at the rescued major
      have hspR : DenoteSpine m.cval env φ d
          (e.getAppArgs.take mI ++ [major])
          (xs.take mI ++ [VExpr.mkAppN (m.cval r.ctor
            (Level.substFn φ cvj.levelParams usj)) ys]) :=
        (hspx.take mI).append (DenoteSpine.cons (by
          rw [show Expr.mkAppN (.const r.ctor usj) major.getAppArgs = major from by
            rw [← hfnmaj]; exact Expr.mkAppN_getApp major] at hvm
          exact hvm) DenoteSpine.nil)
      have hfrR : ∀ x ∈ e.getAppArgs.take mI ++ [major],
          Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
            Expr.LeavesBounded x ∧ CtxOkR mode m.cval env φ d Δ x := by
        intro x hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hfrE x (List.mem_of_mem_take hx')
        · rcases List.mem_singleton.mp hx' with rfl
          exact ⟨hwm, hbm, hLm, hCm⟩
      obtain ⟨vsR, restR, hspR', hteleR⟩ :=
        certs_teleR m φ hcl ihd ihi _ (e.getAppArgs.take mI ++ [major]) TV
          hcertR hRw hRb hRL hRC hTVd hfrR
      obtain rfl : vsR = xs.take mI ++ [VExpr.mkAppN (m.cval r.ctor
          (Level.substFn φ cvj.levelParams usj)) ys] :=
        DenoteSpine.det hspR' hspR
      -- the constructor telescope
      obtain ⟨vsC, restC, hspC', hteleC⟩ :=
        certs_teleR m φ hcl ihd ihi _ major.getAppArgs TVj hcertC hJw hJb hJL
          hJC hTVjd hfrM
      rw [DenoteSpine.det hspC' hspy] at hteleC
      -- the index decomposition
      obtain ⟨RV, hRVd, hRVp⟩ :=
        denote_piResidualR hcl hpres hTVjd hspy hJw hJb
          (fun x hx => ⟨(hfrM x hx).1, (hfrM x hx).2.1⟩)
      obtain rfl : RV = restC := by
        rw [Tele.residual hteleC] at hRVp; exact (Option.some.inj hRVp).symm
      rw [show residual = Expr.mkAppN residual.getAppFn residual.getAppArgs from
        (Expr.mkAppN_getApp residual).symm] at hRVd
      obtain ⟨H, cargs, hH, hspRes, rfl⟩ := denote_mkAppN_inv hRVd
      -- the residual's frames (a `piResidual` of a closed type at scoped
      -- arguments)
      obtain ⟨hwRes, hbRes, hLRes, hCRes⟩ :=
        piResidual_frameR hpres hJw hJb hJL hJC hfrM
      have hfrRes := frame_spineR (a := residual) hwRes hbRes hLRes hCRes
      have hspIdx : DenoteSpine m.cval env φ d
          ((e.getAppArgs.take mI).drop rP) ((xs.take mI).drop rP) :=
        (hspx.take mI).drop rP
      have hDefI : DefEqL mode env m.cval φ Δ (cargs.drop r.ctorParams)
          ((xs.take mI).drop rP) :=
        defEqL_of_defEqListR m φ ihd hdefI
          (fun x hx => hfrRes x (List.mem_of_mem_drop hx))
          (fun x hx => hfrE x (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
          (hspRes.drop r.ctorParams) hspIdx
      -- the length disjunct
      have hlenDisj : mI = rP ∨ cargs.length = r.ctorParams + (mI - rP) := by
        have hle := m.rec_params_le _ _ _ _ _ hfrec
        have hlen := hDefI.length_eq
        rw [List.length_drop, List.length_drop, List.length_take,
          hspx.length, hlenA] at hlen
        omega
      -- the reduct
      have hspOut : DenoteSpine m.cval env φ d
          (e.getAppArgs.take rP ++ major.getAppArgs.drop r.ctorParams)
          (xs.take rP ++ ys.drop r.ctorParams) :=
        (hspx.take rP).append (hspy.drop r.ctorParams)
      have hdOut : denote m.cval env φ d
          (Expr.mkAppN (r.rhs.instantiateLevelParams cv.levelParams us)
            (e.getAppArgs.take rP ++ major.getAppArgs.drop r.ctorParams))
          = some (VExpr.mkAppN R (xs.take rP ++ ys.drop r.ctorParams)) :=
        denote_mkAppN hspOut (hRd d)
      have hRnf' : (r.rhs.instantiateLevelParams cv.levelParams us).hasFvar
          = false := by rw [Expr.hasFvar_instantiateLevelParams]; exact hRnf
      refine ⟨_, hdOut, ?_, ?_, ?_, ?_, ?_⟩
      · refine Red.iota hfrec hrfind hfire hfcj ?_ (by rw [hspx.length, hlenA])
          (by rw [hspy.length, hlenM]) hlenU hlenUj hstripR hstripC ?_
          hTV0 hTVc hTVj0 hTVjc hR0 hRc rfl
          (hR₀.trans hR₁) hRm ?_ ?_ hteleR hteleC rfl hlenDisj hDefI
        · exact fun lvls pins hn => m.rec_params_le _ _ _ _ _ hfrec
        · rw [recFireComparands_fst_nil] at hlev; exact hlev
        · -- the `.plain` comparands
          intro hp
          rw [show (recFireComparands r cv.levelParams us cvj.levelParams
              e.getAppArgs rP).2 = e.getAppArgs.take r.ctorParams from by
            unfold recFireComparands; rw [hp]] at hdefP
          exact defEqL_of_defEqListR m φ ihd hdefP
            (fun x hx => hfrM x (List.mem_of_mem_take hx))
            (fun x hx => hfrE x (List.mem_of_mem_take hx))
            (hspy.take _) (hspx.take _)
        · -- the `.nested` pins
          intro lvls pins hn i hi vp hvp hbb
          obtain ⟨-, -, -, -, hnest⟩ := hrec' cv mI rP rules rfl r
            (List.mem_of_find?_eq_some hrfind)
          obtain ⟨hrle, -, hpinsWf, -⟩ := hnest lvls pins hn
          have hlenPins : pins.length = r.ctorParams := by
            have := defEqListP_length hdefP
            rw [show (recFireComparands r cv.levelParams us cvj.levelParams
                e.getAppArgs rP).2 = pins.map (fun p =>
                  Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
                    (p.instantiateLevelParams cv.levelParams us)) from by
              unfold recFireComparands; rw [hn]] at this
            rw [List.length_take, List.length_map, hlenM] at this
            omega
          have hprelen : (e.getAppArgs.take rP).length = rP := by
            rw [List.length_take, hlenA]; omega
          have hargsPre : ∀ x ∈ e.getAppArgs.take rP, Expr.WScoped d x ∧
              x.looseBVarsBounded 0 = true ∧ Expr.fvarsBelow d x := by
            intro x hx
            obtain ⟨hw2, hb2, -, -⟩ := hfrE x (List.mem_of_mem_take hx)
            exact ⟨hw2, hb2, hw2.fvarsBelow⟩
          obtain ⟨hpinF, -, -, hpinB⟩ := hpinsWf (pins.getD i default)
            (getD_mem (by rw [hlenPins]; exact hi))
          have hpinF' : ((pins.getD i default).instantiateLevelParams
              cv.levelParams us).hasFvar = false := by
            rw [Expr.hasFvar_instantiateLevelParams]; exact hpinF
          have hpinB' : ((pins.getD i default).instantiateLevelParams
              cv.levelParams us).looseBVarsBounded
              (e.getAppArgs.take rP).length = true := by
            rw [Expr.looseBVarsBounded_instantiateLevelParams, hprelen]
            exact hpinB
          have hcden := denote_openRev hcl (e.getAppArgs.take rP) hargsPre
            ((Expr.WScoped.of_not_hasFvar (d := d) hpinF').fvarsBelow)
            hpinB' (hspx.take rP)
          rw [hprelen] at hcden
          have hbase := denote_openRev_base (env := env) (φ := φ) hcl hpinF'
            (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hpinB) d
          rw [hbase, hvp] at hcden
          -- the comparand list, denoted
          rw [show (recFireComparands r cv.levelParams us cvj.levelParams
              e.getAppArgs rP).2 = pins.map (fun p =>
                Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
                  (p.instantiateLevelParams cv.levelParams us)) from by
            unfold recFireComparands; rw [hn]] at hdefP
          -- the comparand spine denotes pointwise
          have hpinFacts : ∀ j, j < pins.length →
              ((pins.getD j default).instantiateLevelParams
                  cv.levelParams us).hasFvar = false ∧
              ((pins.getD j default).instantiateLevelParams
                  cv.levelParams us).looseBVarsBounded
                (e.getAppArgs.take rP).length = true := by
            intro j hj
            obtain ⟨hF, -, -, hB⟩ := hpinsWf (pins.getD j default) (getD_mem hj)
            exact ⟨by rw [Expr.hasFvar_instantiateLevelParams]; exact hF,
              by rw [Expr.looseBVarsBounded_instantiateLevelParams, hprelen]
                 exact hB⟩
          have hfrPin : ∀ x ∈ pins.map (fun p =>
              Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
                (p.instantiateLevelParams cv.levelParams us)),
              Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
                Expr.LeavesBounded x ∧ CtxOkR mode m.cval env φ d Δ x := by
            intro x hx
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
            obtain ⟨hF, -, -, hB⟩ := hpinsWf q hq
            have hF' : (q.instantiateLevelParams cv.levelParams us).hasFvar
                = false := by rw [Expr.hasFvar_instantiateLevelParams]; exact hF
            refine ⟨instSpine_WScoped _ (Expr.WScoped.of_not_hasFvar hF')
                (fun y hy => (hargsPre y hy).1), ?_, fun l hl => ?_,
              ⟨hC.1, fun l hl => ?_⟩⟩
            · rw [show rP - 1 = (e.getAppArgs.take rP).length - 1 from by
                rw [hprelen]]
              exact instSpine_closed (fun y hy => (hargsPre y hy).2.1)
                (by rw [Expr.looseBVarsBounded_instantiateLevelParams, hprelen]
                    exact hB)
            · rcases fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
              · exact absurd hl' (by
                  rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hF']; simp)
              · exact (hfrE y (List.mem_of_mem_take hy)).2.2.1 l hly
            · rcases fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
              · exact absurd hl' (by
                  rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hF']; simp)
              · exact (hfrE y (List.mem_of_mem_take hy)).2.2.2.2 l hly
          -- only the `i`-th comparand is known to denote (the rule
          -- hypothesises exactly that one), so the component is pulled
          -- out of `defEqList` syntactically rather than through a
          -- whole-list `DenoteSpine`
          have hilt : i < pins.length := by rw [hlenPins]; exact hi
          have hiy : i < major.getAppArgs.length := by rw [hlenM]; omega
          have hgetL : (major.getAppArgs.take r.ctorParams).getD i default
              = major.getAppArgs.getD i default := by
            simp [List.getD, List.getElem?_eq_getElem hiy,
              show i < r.ctorParams from hi]
          have hgetR : ((pins.map (fun p =>
              Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
                (p.instantiateLevelParams cv.levelParams us))).getD i default)
              = Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
                ((pins.getD i default).instantiateLevelParams
                  cv.levelParams us) := by
            simp [List.getD, List.getElem?_map,
              List.getElem?_eq_getElem hilt]
          have hcert := defEqListP_get hdefP i (by
            rw [List.length_take, hlenM]; omega)
          rw [hgetL, hgetR] at hcert
          obtain ⟨hF, -, -, hB⟩ := hpinsWf (pins.getD i default) (getD_mem hilt)
          have hF' : ((pins.getD i default).instantiateLevelParams
              cv.levelParams us).hasFvar = false := by
            rw [Expr.hasFvar_instantiateLevelParams]; exact hF
          obtain ⟨hwA, hbA, hLA, hCA⟩ := hfrM _ (getD_mem hiy)
          have hgy : denote m.cval env φ d (major.getAppArgs.getD i default)
              = some (ys.getD i default) := by
            have hiys : i < ys.length := by rw [hspy.length]; exact hiy
            have := hspy.get ⟨i, hiy⟩
            simpa [List.getD, List.getElem?_eq_getElem hiy,
              List.getElem?_eq_getElem hiys] using this
          rw [Expr.instSpine_eq_instSeq] at hcert
          obtain ⟨hwP, hbP, hLP, hCP⟩ := hfrPin _ (List.mem_map.mpr
            ⟨pins.getD i default, getD_mem hilt, rfl⟩)
          rw [Expr.instSpine_eq_instSeq] at hwP hbP hLP hCP
          exact ihd hcert hwA hbA hLA hwP hbP hLP hCA hCP hgy (by
            simpa using hcden)

      · exact Expr.WScoped.mkAppN (Expr.WScoped.of_not_hasFvar hRnf')
          (fun y hy => by
            rcases List.mem_append.mp hy with hy' | hy'
            · exact (hfrE y (List.mem_of_mem_take hy')).1
            · exact (hfrM y (List.mem_of_mem_drop hy')).1)
      · refine looseBVarsBounded_mkAppN ?_ (fun y hy => by
          rcases List.mem_append.mp hy with hy' | hy'
          · exact (hfrE y (List.mem_of_mem_take hy')).2.1
          · exact (hfrM y (List.mem_of_mem_drop hy')).2.1)
        rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hRbd
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
        · exact absurd hl' (by
            rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hRnf']; simp)
        · rcases List.mem_append.mp hy with hy' | hy'
          · exact (hfrE y (List.mem_of_mem_take hy')).2.2.1 l hly
          · exact (hfrM y (List.mem_of_mem_drop hy')).2.2.1 l hly
      · refine ⟨hC.1, fun l hl => ?_⟩
        rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
        · exact absurd hl' (by
            rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hRnf']; simp)
        · rcases List.mem_append.mp hy with hy' | hy'
          · exact (hfrE y (List.mem_of_mem_take hy')).2.2.2.2 l hly
          · exact (hfrM y (List.mem_of_mem_drop hy')).2.2.2.2 l hly
    · exact nomatch hvj
  · exact nomatch hvc

end Setlec.SetR
