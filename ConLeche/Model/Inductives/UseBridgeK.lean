module

public import ConLeche.Model.Inductives.PosMonoK
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.WellDenotedTransport

public section

/-!
# The semantic side of a use's match, from `UseOkK` (PRIMREC / NESTKN-M3)

`useBridgeK`: at the hook `UseOkK` (`Verify/Inductives/UseOkK.lean`) the
use case of `posDK_mono` has what it needs (`UseBridgeK`): the node's base
instantiated by the match's bindings at the user — the bindings read and fit
the families' types (the hook's typing clauses, `infer_sound`/`defeq_sound`,
read back through the match's substitution), the node's parameters in the
image context (their leaves the key's, hence the user's, or the families'),
and read at the image as the user's spelling (syntactically, or at a merged
family by `defeq_sound`).  With it, `posDK_monoOk` is `posDK_mono` at the hook.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestKey LayoutK LayoutOutK
  instPisWith fueledOps PosDKH PosJK PosKind UseHookK matchStepK thetaK ParamOkK)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## Structural readability reads -/

/-- **A structurally readable term reads**, at every depth. -/
theorem denoteMeta_of_readsS {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (d : Nat) (e : Expr), Expr.ReadsS env 0 e → ∃ ea, denoteMeta acval env φ d e = some ea := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u => intro _; exact ⟨_, by rw [denoteMeta]⟩
  | case2 d idx ty => intro _; exact ⟨_, by rw [denoteMeta]⟩
  | case3 d n us ci hf hlen => intro _; exact ⟨_, by rw [denoteMeta, hf]; dsimp only; rw [if_pos hlen]⟩
  | case4 d n us ci hf hlen =>
    intro h
    obtain ⟨ci', hf', hl⟩ := h
    rw [hf] at hf'; cases hf'
    exact absurd hl hlen
  | case5 d n us hf =>
    intro h
    obtain ⟨ci', hf', -⟩ := h
    rw [hf] at hf'; cases hf'
  | case6 d ty body mb ihty ihbody =>
    intro h
    obtain ⟨ta, hta⟩ := ihty h.1
    obtain ⟨ba, hba⟩ := ihbody (Expr.ReadsS.instantiate1_fvar (k := 0) h.2)
    exact ⟨_, by rw [denoteMeta, hta]; simp only [Option.bind_eq_bind, Option.bind_some]; rw [hba]; rfl⟩
  | case7 d ty body mb ihty ihbody =>
    intro h
    obtain ⟨ta, hta⟩ := ihty h.1
    obtain ⟨ba, hba⟩ := ihbody (Expr.ReadsS.instantiate1_fvar (k := 0) h.2)
    exact ⟨_, by rw [denoteMeta, hta]; simp only [Option.bind_eq_bind, Option.bind_some]; rw [hba]; rfl⟩
  | case8 d fe a ihf iha =>
    intro h
    obtain ⟨fa, hfa⟩ := ihf h.1
    obtain ⟨aa, haa⟩ := iha h.2
    exact ⟨_, by rw [denoteMeta, hfa]; simp only [Option.bind_eq_bind, Option.bind_some]; rw [haa]; rfl⟩
  | case9 d ty val body => intro h; exact h.elim
  | case10 d sn i e ihe =>
    intro h
    obtain ⟨ea, hea⟩ := ihe h.1
    rw [denoteMeta, hea]
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases hfp : env.findProj? sn i with
    | some entry => exact ⟨_, rfl⟩
    | none =>
      rcases h.2 with h2 | h2
      · exact absurd hfp h2
      · rcases i with _ | _ | i
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
        · omega
  | case11 d k hsup => intro _; exact ⟨_, by rw [denoteMeta, if_pos hsup]⟩
  | case12 d k hsup => intro h; exact absurd h hsup
  | case13 d s hsup => intro _; exact ⟨_, by rw [denoteMeta, if_pos hsup]⟩
  | case14 d s hsup => intro h; exact absurd h hsup
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro h
    cases x with
    | bvar i => simp [Expr.ReadsS] at h
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

/-- Structurally readable subjects make a read spine. -/
theorem spine_of_readsS {acval : Name → (Name → Nat) → AnnotTerm} {D : Nat} :
    ∀ (es : List Expr), (∀ e ∈ es, Expr.ReadsS env 0 e) →
      ∃ vs, DenoteMetaSpine acval env φ D es vs
  | [], _ => ⟨[], .nil⟩
  | e :: es, h => by
    obtain ⟨a, ha⟩ := denoteMeta_of_readsS (acval := acval) (φ := φ) D e (h e List.mem_cons_self)
    obtain ⟨vs, hvs⟩ := spine_of_readsS es fun e' he' => h e' (List.mem_cons_of_mem _ he')
    exact ⟨a :: vs, .cons ha hvs⟩

/-! ## A leaf's context package -/

/-- **A leaf's package** in a context (`CtxOkP`'s clause). -/
@[expose] def LeafOkAt (m : EnvModel V env) (φ : Name → Nat) (d : Nat) (Δa : List AnnotTerm)
    (l : Nat × Expr) : Prop :=
  l.1 < d ∧ Expr.WScoped l.1 l.2 ∧ ∃ tl Aa,
    denoteMeta m.acval env φ l.1 l.2 = some tl ∧ Δa[d - 1 - l.1]? = some Aa ∧
    ∀ σ : Nat → V, Sat V (Δa.drop (d - l.1)) σ →
      interp V σ tl = interp V σ Aa ∧ WellDenotedV V σ tl

theorem CtxOkP.leaf {m : EnvModel V env} {d : Nat} {Δa : List AnnotTerm} {e : Expr}
    (h : CtxOkP m φ d Δa e) {l : Nat × Expr} (hl : l ∈ e.fvarLeaves) : LeafOkAt m φ d Δa l :=
  h.2 l hl

theorem CtxOkP.of_leaves {m : EnvModel V env} {d : Nat} {Δa : List AnnotTerm} {e : Expr}
    (hl : Δa.length = d) (h : ∀ l ∈ e.fvarLeaves, LeafOkAt m φ d Δa l) : CtxOkP m φ d Δa e :=
  ⟨hl, h⟩

/-- **A leaf below `h0` keeps its package** in a context sharing the entries
below `h0` (`X` new entries above them). -/
theorem LeafOkAt.rebase {m : EnvModel V env} {d h0 : Nat} {Δa X : List AnnotTerm}
    {l : Nat × Expr} (h : LeafOkAt m φ d Δa l) (hl : l.1 < h0) (hd : h0 ≤ d)
    (hΔ : Δa.length = d) :
    LeafOkAt m φ (h0 + X.length) (X ++ Δa.drop (d - h0)) l := by
  obtain ⟨-, hws, tl, Aa, htl, hA, hk⟩ := h
  refine ⟨by omega, hws, tl, Aa, htl, ?_, ?_⟩
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
    rw [show d - h0 + (h0 + X.length - 1 - l.1 - X.length) = d - 1 - l.1 by omega]
    exact hA
  · rw [show h0 + X.length - l.1 = X.length + (h0 - l.1) by omega, List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left,
      List.drop_drop, show d - h0 + (h0 - l.1) = d - l.1 by omega]
    exact hk

/-! ## Valuations -/

omit [SetTheory V] in
theorem consList_append (A B : List V) (ρ : Nat → V) :
    consList (A ++ B) ρ = consList B (consList A ρ) := by
  induction A generalizing ρ with
  | nil => rfl
  | cons a A ih => simp only [List.cons_append, consList_cons]; exact ih _

omit [SetTheory V] in
/-- Seen below the top `n - j` of `n` values, a frame holds the first `j`. -/
theorem dropV_consList_take (vals : List V) (ρ : Nat → V) (j : Nat) :
    dropV (vals.length - j) (consList vals ρ) = consList (vals.take j) ρ := by
  have e : consList vals ρ = consList (vals.drop j) (consList (vals.take j) ρ) := by
    rw [← consList_append, List.take_append_drop]
  rw [e]
  funext q
  unfold dropV
  have hl : (vals.drop j).length = vals.length - j := by simp
  rw [← hl, consList_apply_add]

/-- The base valuation at a use, of lifted bindings, is the one seen below. -/
theorem useVal_liftN (xsL : List AnnotTerm) {c k : Nat} (hck : c ≤ k) (ρ : Nat → V) :
    useVal (xsL.map (AnnotTerm.liftN c · 0)) k ρ = useVal xsL (k - c) (dropV c ρ) := by
  unfold useVal
  rw [List.map_map]
  congr 1
  · exact List.map_congr_left fun a _ => interp_liftN_drop c ρ a
  · funext q; unfold dropV; congr 1; omega

/-- A spine fits a telescope where each value is in its field at the
earlier values. -/
theorem spineFit_of_getElem :
    ∀ {Fs : List AnnotTerm} {as : List V} {ρ : Nat → V}, as.length = Fs.length →
      (∀ j (h1 : j < as.length) (h2 : j < Fs.length),
        as[j] ∈ˢ interp V (consList (as.take j) ρ) Fs[j]) → SpineFit ρ Fs as
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | F :: Fs, a :: as, ρ, hl, h => by
    refine ⟨?_, ?_⟩
    · have := h 0 (by simp) (by simp)
      simpa using this
    refine spineFit_of_getElem (by simpa using hl) fun j h1 h2 => ?_
    have := h (j + 1) (by simpa using h1) (by simpa using h2)
    simpa using this

/-! ## The node's families at the image context -/

/-- **The node's families' context packages** at the image of a use: their
types read at their depths (`tya`), and every family's leaf has its package in
the context `X ++ (tya.take (j+1)).reverse ++ base` — each family type a TYPE
(the hook's typing clause, `infer_sound`) under the earlier ones, its leaves
the key's (validated below the members) or earlier families'. -/
theorem famPkgK {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (hin : RulesInputs V mp.base2 φ)
    {ctx : NestCtx} {F : Nat} {lo : LayoutOutK} {kn : NestKey} {d : Nat} {Δa : List AnnotTerm}
    (hΔ : Δa.length = d) (h0d : ctx.hiAt 0 ≤ d)
    (hknLeaf : ∀ l, ConLeche.LeafIn kn.ds l → l.1 < ctx.hiAt 0 → LeafOkAt mp.base2 φ d Δa l)
    (htl : lo.L.famTys.length = lo.L.nF)
    (hU3 : ∀ j (hj : j < lo.L.famTys.length),
      Expr.WScoped (ctx.hiAt 0 + j) lo.L.famTys[j] ∧ lo.L.famTys[j].looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded lo.L.famTys[j] ∧ Expr.ReadsS env 0 lo.L.famTys[j] ∧
      (∀ l ∈ lo.L.famTys[j].fvarLeaves, (l.1 < ctx.hiAt 0 ∧ ConLeche.LeafIn kn.ds l) ∨
        ∃ i, ∃ hi : i < j, l = (ctx.hiAt 0 + i, lo.L.famTys[i]'(by omega))) ∧
      ∃ T sv, (fueledOps .verified F).inferType env (ctx.hiAt 0 + j) lo.L.famTys[j] = .ok T ∧
        (fueledOps .verified F).ensureSort env (ctx.hiAt 0 + j) T = .ok sv) :
    ∃ tya : List AnnotTerm, tya.length = lo.L.nF ∧
      (∀ j (hj : j < lo.L.famTys.length) (hj' : j < tya.length),
        denoteMeta mp.base2.acval env φ (ctx.hiAt 0 + j) lo.L.famTys[j] = some tya[j]) ∧
      ∀ j (hj : j < lo.L.famTys.length) (X : List AnnotTerm),
        LeafOkAt mp.base2 φ (ctx.hiAt 0 + (j + 1) + X.length)
          (X ++ ((tya.take (j + 1)).reverse ++ Δa.drop (d - ctx.hiAt 0)))
          (ctx.hiAt 0 + j, lo.L.famTys[j]) := by
  let tya : List AnnotTerm := (List.range lo.L.famTys.length).map fun j =>
    (denoteMeta mp.base2.acval env φ (ctx.hiAt 0 + j) (lo.L.famTys.getD j default)).getD .prf
  have htyal : tya.length = lo.L.famTys.length := by simp [tya]
  have hread : ∀ j (hj : j < lo.L.famTys.length) (hj' : j < tya.length),
      denoteMeta mp.base2.acval env φ (ctx.hiAt 0 + j) lo.L.famTys[j] = some tya[j] := by
    intro j hj hj'
    obtain ⟨-, -, -, hrs, -⟩ := hU3 j hj
    obtain ⟨ea, hea⟩ := denoteMeta_of_readsS (acval := mp.base2.acval) (φ := φ) (ctx.hiAt 0 + j) _ hrs
    simp only [tya, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hea]
    rfl
  have hrev : ∀ i (hi : i < tya.length),
      (tya.take (i + 1)).reverse = tya[i] :: (tya.take i).reverse := by
    intro i hi
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    simp
  -- a family's package, from its type's grading under the earlier ones
  have pkg : ∀ i (hi : i < lo.L.famTys.length),
      (∀ σ : Nat → V, Sat V ((tya.take i).reverse ++ Δa.drop (d - ctx.hiAt 0)) σ →
        WellDenotedV V σ (tya[i]'(by rw [htyal]; exact hi))) →
      ∀ X : List AnnotTerm, LeafOkAt mp.base2 φ (ctx.hiAt 0 + (i + 1) + X.length)
        (X ++ ((tya.take (i + 1)).reverse ++ Δa.drop (d - ctx.hiAt 0))) (ctx.hiAt 0 + i, lo.L.famTys[i]) := by
    intro i hi hPi X
    have hi' : i < tya.length := by rw [htyal]; exact hi
    obtain ⟨hws, -⟩ := hU3 i hi
    refine ⟨by simp only; omega, hws, tya[i], tya[i], hread i hi hi', ?_, fun σ hσ => ⟨rfl, hPi σ ?_⟩⟩
    · simp only
      rw [show ctx.hiAt 0 + (i + 1) + X.length - 1 - (ctx.hiAt 0 + i) = X.length + 0 by omega,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, hrev i hi']
      rfl
    · simp only at hσ
      rw [show ctx.hiAt 0 + (i + 1) + X.length - (ctx.hiAt 0 + i) = X.length + 1 by omega, List.drop_append,
        List.drop_eq_nil_of_le (by omega), List.nil_append,
        show X.length + 1 - X.length = 1 by omega, hrev i hi'] at hσ
      simpa using hσ
  -- each family's type is graded under the earlier ones
  have hP : ∀ j (hj : j < lo.L.famTys.length), ∀ σ : Nat → V,
      Sat V ((tya.take j).reverse ++ Δa.drop (d - ctx.hiAt 0)) σ →
      WellDenotedV V σ (tya[j]'(by rw [htyal]; exact hj)) := by
    intro j
    induction j using Nat.strongRecOn with
    | _ j ih =>
      intro hj
      obtain ⟨hws, hbb, hLb, -, hleaves, T, sv, hT, -⟩ := hU3 j hj
      have hlenj : ((tya.take j).reverse ++ Δa.drop (d - ctx.hiAt 0)).length = ctx.hiAt 0 + j := by
        simp only [List.length_append, List.length_reverse, List.length_take, List.length_drop, hΔ,
          htyal]
        omega
      have hC : CtxOkP mp.base2 φ (ctx.hiAt 0 + j) ((tya.take j).reverse ++ Δa.drop (d - ctx.hiAt 0)) lo.L.famTys[j] := by
        refine CtxOkP.of_leaves hlenj fun l hl => ?_
        rcases hleaves l hl with ⟨hl0, hin'⟩ | ⟨i, hi, rfl⟩
        · have := (hknLeaf l hin' hl0).rebase (X := (tya.take j).reverse) hl0 h0d hΔ
          rwa [List.length_reverse, List.length_take, Nat.min_eq_left (by rw [htyal]; omega)] at this
        · -- an earlier family: its package, below the families between
          have hsplit : (tya.take j).reverse
              = ((tya.take j).drop (i + 1)).reverse ++ (tya.take (i + 1)).reverse := by
            calc (tya.take j).reverse
                = ((tya.take j).take (i + 1) ++ (tya.take j).drop (i + 1)).reverse := by
                  rw [List.take_append_drop]
              _ = _ := by rw [List.reverse_append, List.take_take, Nat.min_eq_left (by omega)]
          rw [hsplit, List.append_assoc]
          have hXl : (((tya.take j).drop (i + 1)).reverse).length = j - (i + 1) := by
            simp only [List.length_reverse, List.length_drop, List.length_take, htyal]; omega
          have := pkg i (by omega) (ih i hi (by omega)) (((tya.take j).drop (i + 1)).reverse)
          rwa [hXl, show ctx.hiAt 0 + (i + 1) + (j - (i + 1)) = ctx.hiAt 0 + j by omega] at this
      have hIS : InferSemFull mp.base2 φ (ctx.hiAt 0 + j) lo.L.famTys[j] T :=
        infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hT)
      obtain ⟨-, -, -, -, hgr, -⟩ := hIS ⟨hws, hbb, hLb⟩ hC.toCtxOk
        (hread j hj (by rw [htyal]; exact hj))
      exact hgr
  exact ⟨tya, htyal.trans htl, hread, fun j hj X => pkg j hj (hP j hj) X⟩

/-! ## The bridge -/

/-- A leaf validated at the user, below `h`, is validated at the user seen at
depth `h`. -/
theorem LeafOkAt.down {m : EnvModel V env} {d h : Nat} {Δa : List AnnotTerm} {l : Nat × Expr}
    (hl : LeafOkAt m φ d Δa l) (hlh : l.1 < h) (hd : h ≤ d) (hΔ : Δa.length = d) :
    LeafOkAt m φ h (Δa.drop (d - h)) l := by
  have := hl.rebase (X := []) hlh hd hΔ
  simpa using this

/-- The match's substitution maps only the families, each to its binding. -/
theorem thetaK_some {ctx : NestCtx} {nF : Nat} {bs : List (Nat × Expr)} {bsL : List Expr}
    (hbsLl : bsL.length = nF)
    (hθb : ∀ j (hj : j < bsL.length), thetaK ctx nF bs (ctx.hiAt 0 + j) = some bsL[j]) {i : Nat}
    {b : Expr} (h : thetaK ctx nF bs i = some b) :
    ∃ j, ∃ hj : j < bsL.length, i = ctx.hiAt 0 + j ∧ b = bsL[j] := by
  have hi : ctx.hiAt 0 ≤ i ∧ i < ctx.hiAt 0 + nF := by
    unfold ConLeche.thetaK at h
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc
    · simp at h
  refine ⟨i - ctx.hiAt 0, by omega, by omega, ?_⟩
  have := hθb (i - ctx.hiAt 0) (by omega)
  rw [show ctx.hiAt 0 + (i - ctx.hiAt 0) = i by omega, h] at this
  exact Option.some.inj this

/-- The match's substitution maps nothing below the families. -/
theorem thetaK_lo {ctx : NestCtx} {nF : Nat} {bs : List (Nat × Expr)} {v : Nat}
    (hv : v < ctx.hiAt 0) : thetaK ctx nF bs v = none := by
  unfold ConLeche.thetaK
  rw [if_neg (by simp; omega)]

/-- **The semantic side of a use's match, at the hook `UseOkK`.** -/
theorem useBridgeK {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (hin : RulesInputs V mp.base2 φ)
    {ctx : NestCtx} {F : Nat} :
    UseBridgeK mp φ ctx (fueledOps .verified F) (ConLeche.UseOkK (fueledOps .verified F) env ctx) := by
  intro L met kc kn ps lo metc rs bs hinst hnode hgrp hlv hkds hlen hbs hinner hall hpar hhook
    ihbind hcov d hd Δa R hR hlay hΔ hps psa hpsa
  obtain ⟨hhd, hnPc, htl, hfl, hU3, hU4, hU5, hU6, hU7⟩ := hhook
  refine ⟨hhd, hnPc, ?_⟩
  have h0L : ctx.hiAt 0 ≤ L.hi := by have := hR.hiEq; omega
  have h0d : ctx.hiAt 0 ≤ d := Nat.le_trans h0L hd
  -- the user's material is validated
  have hsiteLeaf : ∀ l, (ConLeche.LeafIn ps l ∨ ConLeche.LayLeaf L l) →
      LeafOkAt mp.base2 φ d Δa l := by
    rintro l (⟨x, hx, hl⟩ | (⟨x, hx, hl⟩ | ⟨p, hp, x, hx, hl⟩))
    · exact (hps x hx).2.2.2.leaf hl
    · exact (hlay.dsF x hx).leaf hl
    · exact (hlay.keys p hp x hx).2.2.2.1.leaf hl
  have hknLeaf : ∀ l, ConLeche.LeafIn kn.ds l → l.1 < ctx.hiAt 0 →
      LeafOkAt mp.base2 φ d Δa l := by
    intro l hl _
    rcases hU6 l hl with h | ⟨p, hp, h⟩
    · exact hsiteLeaf l (Or.inl h)
    · exact hsiteLeaf l (Or.inr (Or.inr ⟨p, hp, h⟩))
  -- the families' packages at the image context
  obtain ⟨tya, htyal, htyar, hpkg⟩ := famPkgK mp hin hΔ h0d hknLeaf htl hU3
  -- the bindings
  let bsL : List Expr := (List.range lo.L.nF).map fun j =>
    (thetaK ctx lo.L.nF bs (ctx.hiAt 0 + j)).getD default
  have hbsLl : bsL.length = lo.L.nF := by simp [bsL]
  have hθb : ∀ j (hj : j < bsL.length), thetaK ctx lo.L.nF bs (ctx.hiAt 0 + j) = some bsL[j] := by
    intro j hj
    obtain ⟨b, hb, -⟩ := hU7 j (by rw [← hbsLl]; exact hj)
    simp only [bsL, List.getElem_map, List.getElem_range]
    rw [hb]; rfl
  have hθlo : ∀ v, v < ctx.hiAt 0 → thetaK ctx lo.L.nF bs v = none := fun v hv => thetaK_lo hv
  have hbF : ∀ j (hj : j < bsL.length),
      Expr.WScoped L.hi bsL[j] ∧ bsL[j].looseBVarsBounded 0 = true ∧ Expr.LeavesBounded bsL[j] ∧
      Expr.ReadsS env 0 bsL[j] ∧
      (∀ l ∈ bsL[j].fvarLeaves, ConLeche.LeafIn ps l ∨ ConLeche.LayLeaf L l) ∧
      (∃ T, (fueledOps .verified F).inferType env L.hi bsL[j] = .ok T ∧
        (∃ T', (fueledOps .verified F).inferType env L.hi ((lo.L.famTys.getD j default).replaceFVars
          (thetaK ctx lo.L.nF bs)) = .ok T') ∧
        (fueledOps .verified F).isDefEq env L.hi T ((lo.L.famTys.getD j default).replaceFVars
          (thetaK ctx lo.L.nF bs)) = .ok true) ∧
      (j ∈ metc → ∀ key nI, lo.L.fams[j]? = some (key, nI) → ConLeche.BindArityK ctx L bsL[j] nI) := by
    intro j hj
    obtain ⟨b, hb, rest⟩ := hU7 j (by rw [← hbsLl]; exact hj)
    rw [hθb j hj] at hb
    obtain rfl := Option.some.inj hb
    exact rest
  have hbw : ∀ b ∈ bsL, Expr.WScoped L.hi b ∧ b.looseBVarsBounded 0 = true := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    exact ⟨(hbF j hj).1, (hbF j hj).2.1⟩
  have hbCd : ∀ j (hj : j < bsL.length), CtxOkP mp.base2 φ d Δa bsL[j] := fun j hj =>
    CtxOkP.of_leaves hΔ fun l hl => hsiteLeaf l ((hbF j hj).2.2.2.2.1 l hl)
  have hbCL : ∀ j (hj : j < bsL.length), CtxOkP mp.base2 φ L.hi (Δa.drop (d - L.hi)) bsL[j] :=
    fun j hj => (hbCd j hj).drop hd fun l hl =>
      ⟨hl, ConLeche.Expr.fvarLeaves_lt_of_wscoped (hbF j hj).1 l hl⟩
  -- the bindings' readings, at the user's layout depth and at the user's depth
  obtain ⟨xsL, hxsL⟩ := spine_of_readsS (acval := mp.base2.acval) (env := env) (φ := φ)
    (D := L.hi) bsL fun b hb => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
      exact (hbF j hj).2.2.2.1
  have hxs := DenoteMetaSpine.lift (m := mp.base2) (φ := φ) hd (fun b hb => (hbw b hb).1) hxsL
  have hxsLl : xsL.length = lo.L.nF := by rw [← DenoteMetaSpine.length_eq hxsL, hbsLl]
  have huv : ∀ ρ : Nat → V, useVal (xsL.map (AnnotTerm.liftN (d - L.hi) · 0)) (d - ctx.hiAt 0) ρ
      = useVal xsL (L.hi - ctx.hiAt 0) (dropV (d - L.hi) ρ) := by
    intro ρ
    rw [useVal_liftN xsL (by omega) ρ, show d - ctx.hiAt 0 - (d - L.hi) = L.hi - ctx.hiAt 0 by omega]
  have hbL : ∀ j (hj : j < bsL.length) (hj' : j < xsL.length),
      denoteMeta mp.base2.acval env φ L.hi bsL[j] = some xsL[j] := by
    intro j hj hj'
    have := DenoteMetaSpine.getD hxsL default j hj
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some] at this
  -- a substitution image is a binding: scoped, bvar-closed, bounded, its leaves the user's
  have hsubW : ∀ i b, thetaK ctx lo.L.nF bs i = some b → Expr.WScoped L.hi b := by
    intro i b h
    obtain ⟨j, hj, -, rfl⟩ := thetaK_some hbsLl hθb h
    exact (hbF j hj).1
  have hsubB : ∀ i b, thetaK ctx lo.L.nF bs i = some b → b.looseBVarsBounded 0 = true := by
    intro i b h
    obtain ⟨j, hj, -, rfl⟩ := thetaK_some hbsLl hθb h
    exact (hbF j hj).2.1
  -- a node term whose leaves are the key's (below the members) or families', replaced by the
  -- bindings: framed at the user's layout, in the user's context
  have hrep : ∀ (p : Expr) (D : Nat), D ≤ ctx.hiAt 0 + lo.L.nF → Expr.WScoped D p →
      p.looseBVarsBounded 0 = true → Expr.LeavesBounded p →
      (∀ l ∈ p.fvarLeaves, (l.1 < ctx.hiAt 0 ∧ ConLeche.LeafIn kn.ds l) ∨
        ∃ i, i < lo.L.nF ∧ l.1 = ctx.hiAt 0 + i) →
      Frame L.hi (p.replaceFVars (thetaK ctx lo.L.nF bs)) ∧
      CtxOkP mp.base2 φ L.hi (Δa.drop (d - L.hi)) (p.replaceFVars (thetaK ctx lo.L.nF bs)) := by
    intro p D hD hws hbb hLb hleaves
    have hkept : ∀ l ∈ p.fvarLeaves, thetaK ctx lo.L.nF bs l.1 = none → l.1 < L.hi := by
      intro l hl hn
      rcases hleaves l hl with ⟨h1, -⟩ | ⟨i, hi, he⟩
      · omega
      · rw [he, hθb i (by omega)] at hn; simp at hn
    refine ⟨⟨ConLeche.Expr.WScoped_replaceFVars hsubW p hws hkept,
      ConLeche.Expr.looseBVarsBounded_replaceFVars hsubB p 0 hbb, fun l hl => ?_⟩,
      CtxOkP.of_leaves (by simp [hΔ]; omega) fun l hl => ?_⟩
    · rcases ConLeche.Expr.fvarLeaves_replaceFVars p l hl with hl | ⟨i, b, hb, hl⟩
      · exact hLb l hl
      · obtain ⟨j, hj, -, rfl⟩ := thetaK_some hbsLl hθb hb
        exact (hbF j hj).2.2.1 l hl
    · rcases ConLeche.Expr.fvarLeaves_replaceFVars_kept p hws l hl with
        ⟨i, b, hb, hl⟩ | ⟨hlp, i, ty, hn, hit, hli⟩
      · obtain ⟨j, hj, -, rfl⟩ := thetaK_some hbsLl hθb hb
        exact (hsiteLeaf l ((hbF j hj).2.2.2.2.1 l hl)).down
          (ConLeche.Expr.fvarLeaves_lt_of_wscoped (hbF j hj).1 l hl) hd hΔ
      · have hi0 : i < ctx.hiAt 0 := by
          rcases hleaves (i, ty) hit with ⟨h1, -⟩ | ⟨i', hi', he⟩
          · exact h1
          · simp only at he; rw [he, hθb i' (by omega)] at hn; simp at hn
        rcases hleaves l hlp with ⟨hl0, hkn⟩ | ⟨i', -, he⟩
        · exact (hknLeaf l hkn hl0).down (by omega) hd hΔ
        · omega
  have hdropS : ∀ n (ρ : Nat → V), shiftE n 0 ρ = dropV n ρ := by
    intro n ρ; funext i; simp [shiftE, dropV]
  -- each binding is graded at the user's layout and inhabits its family's type at the image
  have hbSem : ∀ j (hj : j < bsL.length) (hj' : j < xsL.length) (hj3 : j < tya.length),
      Graded V (Δa.drop (d - L.hi)) xsL[j] ∧
      ∀ σ, Sat V (Δa.drop (d - L.hi)) σ →
        interp V σ xsL[j] ∈ˢ interp V (useVal xsL (L.hi - ctx.hiAt 0) σ)
          (tya[j].liftN (lo.L.nF - j) 0) := by
    intro j hj hj' hj3
    obtain ⟨hws, hbb, hLb, -, -, ⟨T, hT, ⟨T', hT'⟩, hdef⟩, -⟩ := hbF j hj
    have hIS : InferSemFull mp.base2 φ L.hi bsL[j] T :=
      infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hT)
    obtain ⟨hfrT, hsubT, ta, hta, hgrb, hgrT, hmem⟩ :=
      hIS ⟨hws, hbb, hLb⟩ (hbCL j hj).toCtxOk (hbL j hj hj')
    refine ⟨hgrb, fun σ hσ => ?_⟩
    have hjF : j < lo.L.famTys.length := by omega
    obtain ⟨hwsT, hbbT, hLbT, -, hlvT, -⟩ := hU3 j hjF
    have hgetD : lo.L.famTys.getD j default = lo.L.famTys[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjF]; rfl
    rw [hgetD] at hT' hdef
    obtain ⟨hfrF, hCF⟩ := hrep lo.L.famTys[j] (ctx.hiAt 0 + j) (by omega) hwsT hbbT hLbT
      fun l hl => by
        rcases hlvT l hl with h | ⟨i, hi, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨i, by omega, rfl⟩
    have hpa : denoteMeta mp.base2.acval env φ (ctx.hiAt 0 + bsL.length) lo.L.famTys[j]
        = some (tya[j].liftN (lo.L.nF - j) 0) := by
      rw [denoteMeta_lift mp.base2.acval_closed hwsT _ (by omega), htyar j hjF hj3, Option.map_some,
        show ctx.hiAt 0 + bsL.length - (ctx.hiAt 0 + j) = lo.L.nF - j by omega]
    have hfb : Expr.fvarsBelow (ctx.hiAt 0 + bsL.length) lo.L.famTys[j] :=
      (Expr.WScoped.mono (by omega) hwsT).fvarsBelow
    have hrd := denoteMeta_replaceFVars_use (m := mp.base2) (φ := φ) h0L hθlo hθb hbw hxsL hfb
    rw [hpa, Option.map_some] at hrd
    have hISF : InferSemFull mp.base2 φ L.hi
        (lo.L.famTys[j].replaceFVars (thetaK ctx lo.L.nF bs)) T' :=
      infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hT')
    obtain ⟨-, -, -, -, hgrF, -⟩ := hISF hfrF hCF.toCtxOk hrd
    have hdq : DefEqSem mp.base2 φ L.hi T (lo.L.famTys[j].replaceFVars (thetaK ctx lo.L.nF bs)) :=
      defeq_sound hin (ConLeche.Rules.isDefEqCore_bridge hdef)
    have heq := hdq hfrT hfrF ((hbCL j hj).of_subset hsubT).toCtxOk hCF.toCtxOk hta hrd hgrT hgrF
      σ hσ
    have := hmem σ hσ
    rw [heq, interp_substAV, DenoteMetaSpine.length_eq hxsL, substE_useX h0L] at this
    exact this
  -- the bindings fit the families' types
  have hsat : ∀ ρ, Sat V Δa ρ → SpineFit (dropV (d - ctx.hiAt 0) ρ) tya
      ((xsL.map (AnnotTerm.liftN (d - L.hi) · 0)).map (interp V ρ)) := by
    intro ρ hρ
    have hσ : Sat V (Δa.drop (d - L.hi)) (dropV (d - L.hi) ρ) := Sat_drop hρ _
    refine spineFit_of_getElem (by simp [htyal, hxsLl]) fun j h1 h2 => ?_
    have hj : j < bsL.length := by simp at h1; omega
    have hj' : j < xsL.length := by simp at h1; omega
    have := (hbSem j hj hj' h2).2 _ hσ
    rw [interp_liftN_drop] at this
    have hv := dropV_consList_take ((xsL.map (AnnotTerm.liftN (d - L.hi) · 0)).map (interp V ρ))
      (dropV (d - ctx.hiAt 0) ρ) j
    have hlen : ((xsL.map (AnnotTerm.liftN (d - L.hi) · 0)).map (interp V ρ)).length = lo.L.nF := by
      simp [hxsLl]
    rw [hlen] at hv
    rw [← hv]
    have hu := huv ρ
    unfold useVal at hu
    rw [hu]
    simp only [List.getElem_map]
    rw [interp_liftN_drop]
    exact this
  -- the met families' bindings grow
  have hmet : ∀ (j : Nat) (key : NestKey) (nI : Nat), j < lo.L.nF →
      lo.L.fams[j]? = some (key, nI) → j ∈ metc →
      ∀ hj : j < (xsL.map (AnnotTerm.liftN (d - L.hi) · 0)).length,
        HoleOnVal R (xsL.map (AnnotTerm.liftN (d - L.hi) · 0))[j] nI := by
    intro j key nI hjn hk hjm hj
    have hjb : j < bsL.length := by omega
    have hjx : j < xsL.length := by omega
    have hθj := hθb j hjb
    obtain ⟨p, hp, hp1, hp2⟩ : ∃ p ∈ bs, p.1 = j ∧ p.2 = bsL[j] := by
      unfold ConLeche.thetaK at hθj
      rw [if_pos (by simp; omega)] at hθj
      obtain ⟨p, hfind, hp2⟩ := Option.map_eq_some_iff.mp hθj
      refine ⟨p, List.mem_of_find?_eq_some hfind, ?_, hp2⟩
      have := List.find?_some hfind
      simp only [beq_iff_eq] at this
      omega
    obtain ⟨hws, hbb, hLb, -, -, ⟨T, hT, -, -⟩, har⟩ := hbF j hjb
    have hmono := ihbind p hp (by rw [hp1]; exact hjm)
    rw [hp2] at hmono
    have hIS : InferSemFull mp.base2 φ L.hi bsL[j] T :=
      infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hT)
    obtain ⟨-, -, -, -, hgrb, -⟩ := hIS ⟨hws, hbb, hLb⟩ (hbCL j hjb).toCtxOk (hbL j hjb hjx)
    have hgrd : Graded V Δa (xsL[j].liftN (d - L.hi) 0) := by
      intro ρ hρ
      refine (WellDenotedV_liftN V (d - L.hi) _ 0 ρ).mpr ?_
      rw [hdropS]
      exact hgrb _ (Sat_drop hρ _)
    have hbd : denoteMeta mp.base2.acval env φ d bsL[j] = some (xsL[j].liftN (d - L.hi) 0) := by
      rw [denoteMeta_lift mp.base2.acval_closed hws _ hd, hbL j hjb hjx]; rfl
    simp only [List.getElem_map]
    exact hmono hcov hd hR hlay hΔ hws hbb hLb (hbCd j hjb) hbd hgrd nI (har hjm key nI hk)
  -- the node's parameters at the image context
  obtain ⟨dsa, hdsa⟩ := spine_of_readsS (acval := mp.base2.acval) (env := env) (φ := φ)
    (D := ctx.hiAt 0 + lo.L.nF) lo.L.dsF fun x hx => (hU4 x hx).2.2.2.1
  have hΔc : (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)).length = ctx.hiAt 0 + lo.L.nF := by
    simp only [List.length_append, List.length_reverse, List.length_drop, hΔ, htyal]; omega
  have hfamLeaf : ∀ i (hi : i < lo.L.famTys.length), LeafOkAt mp.base2 φ (ctx.hiAt 0 + lo.L.nF)
      (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)) (ctx.hiAt 0 + i, lo.L.famTys[i]) := by
    intro i hi
    have hsplit : tya.reverse = (tya.drop (i + 1)).reverse ++ (tya.take (i + 1)).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    have := hpkg i hi (tya.drop (i + 1)).reverse
    rw [List.length_reverse, List.length_drop,
      show ctx.hiAt 0 + (i + 1) + (tya.length - (i + 1)) = ctx.hiAt 0 + lo.L.nF by omega,
      ← List.append_assoc, ← hsplit] at this
    exact this
  have hbaseLeaf : ∀ l, ConLeche.LeafIn kn.ds l → l.1 < ctx.hiAt 0 →
      LeafOkAt mp.base2 φ (ctx.hiAt 0 + lo.L.nF) (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)) l := by
    intro l hl hl0
    have := (hknLeaf l hl hl0).rebase (X := tya.reverse) hl0 h0d hΔ
    rwa [List.length_reverse, htyal] at this
  have hCds : ∀ x ∈ lo.L.dsF, CtxOkP mp.base2 φ (ctx.hiAt 0 + lo.L.nF)
      (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)) x := fun x hx =>
    CtxOkP.of_leaves hΔc fun l hl => by
      rcases (hU4 x hx).2.2.2.2 l hl with ⟨hl0, hkn⟩ | ⟨i, hi, rfl⟩
      · exact hbaseLeaf l hkn hl0
      · exact hfamLeaf i hi
  have hlayc : LaySiteK mp.base2 φ ctx (layoutBaseK ctx lo.L) (ctx.hiAt 0 + lo.L.nF)
      (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)) := by
    refine ⟨fun p hp x hx => ?_, hCds⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hU5 p hp x hx
    exact ⟨h1, h2, h3, CtxOkP.of_leaves hΔc fun l hl =>
      hbaseLeaf l (h5 l hl) (ConLeche.Expr.fvarLeaves_lt_of_wscoped h1 l hl),
      denoteMeta_of_readsS _ _ h4⟩
  -- the node's parameters read at the image as the user's spelling
  obtain ⟨psa0, hpsa0, rfl⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) hd
    (fun x hx => (hps x hx).1) hpsa
  have hbwd : ∀ b ∈ bsL, Expr.WScoped d b ∧ b.looseBVarsBounded 0 = true := fun b hb =>
    ⟨Expr.WScoped.mono hd (hbw b hb).1, (hbw b hb).2⟩
  have hpos : ∀ ρ, Sat V Δa ρ →
      dsa.map (interp V (useVal (xsL.map (AnnotTerm.liftN (d - L.hi) · 0)) (d - ctx.hiAt 0) ρ))
        = (psa0.map (AnnotTerm.liftN (d - L.hi) · 0)).map (interp V ρ) := by
    intro ρ hρ
    have hσ : Sat V (Δa.drop (d - L.hi)) (dropV (d - L.hi) ρ) := Sat_drop hρ _
    have hdl : dsa.length = ps.length := by
      rw [← DenoteMetaSpine.length_eq hdsa, hlen]
    have hpl : psa0.length = ps.length := (DenoteMetaSpine.length_eq hpsa0).symm
    apply List.ext_getElem (by simp [hdl, hpl])
    intro i h1 h2
    simp only [List.getElem_map]
    have hi : i < lo.L.dsF.length := by simp at h1; omega
    have hi' : i < ps.length := by simp at h1; omega
    have hid : i < dsa.length := by simp at h1; exact h1
    have hip : i < psa0.length := by omega
    have hmem : (lo.L.dsF[i], ps[i]) ∈ lo.L.dsF.zip ps := by
      have hz : i < (lo.L.dsF.zip ps).length := by simp; omega
      have := List.getElem_mem hz
      rwa [List.getElem_zip] at this
    obtain ⟨hwsp, hbbp, hLbp, -, hlvp⟩ := hU4 _ (List.getElem_mem hi)
    have hdi : denoteMeta mp.base2.acval env φ (ctx.hiAt 0 + bsL.length) lo.L.dsF[i] = some dsa[i] := by
      have := DenoteMetaSpine.getD hdsa default i hi
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hid, Option.getD_some, ← hbsLl] at this
    have hpi0 : denoteMeta mp.base2.acval env φ L.hi ps[i] = some psa0[i] := by
      have := DenoteMetaSpine.getD hpsa0 default i hi'
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hip, Option.getD_some] at this
    have hfb : Expr.fvarsBelow (ctx.hiAt 0 + bsL.length) lo.L.dsF[i] := by
      rw [hbsLl]; exact hwsp.fvarsBelow
    -- the pattern at the bindings, read at the user's layout
    have hqL := denoteMeta_replaceFVars_use (m := mp.base2) (φ := φ) h0L hθlo hθb hbw hxsL hfb
    rw [hdi, Option.map_some] at hqL
    have hθval : interp V (dropV (d - L.hi) ρ) (AnnotTerm.substAV (substTau (ctx.hiAt 0 + bsL.length)
        L.hi (useX (ctx.hiAt 0) L.hi xsL)) dsa[i] 0)
        = interp V (useVal (xsL.map (AnnotTerm.liftN (d - L.hi) · 0)) (d - ctx.hiAt 0) ρ) dsa[i] := by
      rw [interp_substAV, DenoteMetaSpine.length_eq hxsL, substE_useX h0L, huv]
    rw [← hθval, interp_liftN_drop]
    rcases hpar _ hmem with heq | ⟨-, ⟨ty1, hty1⟩, ⟨ty2, hty2⟩, hdef⟩
    · -- syntactically
      simp only at heq
      rw [heq, hpi0] at hqL
      rw [Option.some.inj hqL]
      rfl
    · -- a merged family: defeq at the user's layout
      simp only at hty1 hty2 hdef
      obtain ⟨hfrP, hCP⟩ := hrep lo.L.dsF[i] (ctx.hiAt 0 + lo.L.nF) (Nat.le_refl _) hwsp hbbp hLbp
        fun l hl => by
          rcases hlvp l hl with h | ⟨i', hi', rfl⟩
          · exact Or.inl h
          · exact Or.inr ⟨i', by omega, rfl⟩
      obtain ⟨hwt, hbt, hLt, hCt⟩ := hps ps[i] (List.getElem_mem hi')
      have hCtL : CtxOkP mp.base2 φ L.hi (Δa.drop (d - L.hi)) ps[i] :=
        hCt.drop hd fun l hl => ⟨hl, ConLeche.Expr.fvarLeaves_lt_of_wscoped hwt l hl⟩
      have hIS1 : InferSemFull mp.base2 φ L.hi
          (lo.L.dsF[i].replaceFVars (thetaK ctx lo.L.nF bs)) ty1 :=
        infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hty1)
      obtain ⟨-, -, -, -, hgr1, -⟩ := hIS1 hfrP hCP.toCtxOk hqL
      have hIS2 : InferSemFull mp.base2 φ L.hi ps[i] ty2 :=
        infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hty2)
      obtain ⟨-, -, -, -, hgr2, -⟩ := hIS2 ⟨hwt, hbt, hLt⟩ hCtL.toCtxOk hpi0
      have hdq : DefEqSem mp.base2 φ L.hi (lo.L.dsF[i].replaceFVars (thetaK ctx lo.L.nF bs)) ps[i] :=
        defeq_sound hin (ConLeche.Rules.isDefEqCore_bridge hdef)
      exact hdq hfrP ⟨hwt, hbt, hLt⟩ hCP.toCtxOk hCtL.toCtxOk hqL hpi0 hgr1 hgr2 _ hσ
  exact ⟨xsL.map (AnnotTerm.liftN (d - L.hi) · 0), tya, dsa, by simp [hxsLl], htyal, hsat, hmet,
    fun x hx => ⟨(hU4 x hx).1, (hU4 x hx).2.1⟩, fun x hx => (hU4 x hx).2.2.1, hlayc, hdsa, hCds,
    hpos⟩

/-! ## The derivation at the hook is monotone -/

/-- **THE KEY-NAMED DERIVATION IS MONOTONE** at the hook `UseOkK`: every
judgment of a derivation whose uses satisfy `UseOkK` reads monotonically in
the holes (`posDK_mono` with the bridge `useBridgeK`). -/
theorem posDK_monoOk {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} {F : Nat} :
    ∀ {j : PosJK}, PosDKH (fueledOps .verified F) env ctx
      (ConLeche.UseOkK (fueledOps .verified F) env ctx) j → MonoJK mp φ ctx j :=
  posDK_mono mp hin (useBridgeK mp hin)

/-- **A derived member constructor is positive** (`memberCtorD_mono`'s form)
at the hook `UseOkK`. -/
theorem memberCtorDK_monoOk {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} {F nF : Nat} {crest : Expr}
    {ks : List PosKind} {tyN : Expr}
    (hd : ConLeche.MemberCtorDKH (fueledOps .verified F) env ctx
      (ConLeche.UseOkK (fueledOps .verified F) env ctx) nF crest ks tyN)
    (hcov : (∃ k ∈ ks, k.flat = false) → ContCover mp ctx)
    (hfr : Frame (ctx.hiAt 0) crest)
    {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta mp.base2.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca)
    (hR : HoleRel mp.base2 φ ctx [] (ctx.hiAt 0) Δa R) :
    PiPosThen (ResultIdxConst ctx.nP) nF R ca :=
  memberCtorDK_mono mp hin (useBridgeK mp hin) hd hcov hfr hC hca hgr hR

end ConLeche.Model
