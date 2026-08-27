import Setlec.SetR.Rel
import Setlec.Verify.Denote.HasTypeSubst
import Setlec.Verify.Denote.Shift

/-!
# M1: the mutual weakening metatheory (task #148, T2)

Derivations of the whole relation family lift along context insertion
(`LiftCtx`, reused from `Setlec/Verify/Denote/HasTypeSubst.lean` — the
transpose home of `HasType.weakenN`, whose `bvar`/`beta`/`eta` cases
this file mirrors).  This is design §0 decision 1's cost, consumed by
the `CtxOkR` plumbing (`Setlec/SetR/CtxOkR.lean`).

**Why it goes through** (the `denoteClosed` side-condition discipline):
every side condition of every rule is either `Δ`/depth-free data
(lookups, lengths, level guards) or a denotation fact about a *closed*
object whose closedness the rule carries (deviation D1,
`Setlec/SetR/DESIGN.md`) — so side conditions transport unchanged, and
only subjects, contexts and sub-derivations lift.

**Proof engineering.**  The five relations are one mutual inductive, and
Lean's `induction` tactic does not drive mutual `Prop` families — so the
42 constructor cases are proved once as standalone lemmas (`wk*` below,
each matching its recursor minor premise: constructor hypotheses first,
then the induction hypotheses in premise order), and each of the five
`weakenN` theorems is a single term-mode application of its recursor to
the same 42 lemmas.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open Setlec.TT.VExpr (liftN_eq_self_of_closed)

/-! ## Support lemmas

Searched against the T1 inventory (`Setlec/Verify/Denote/{SubstAlgebra,
VClosed,Shift,TeleOpen}.lean`) first: the lift/inst commutations and
closedness invariance exist and are reused; the `mkAppN`, `getD`,
`piResidualV`, `instRevChain` and spine-builder lift equations below did
not exist and are new (each a one-induction consequence of the existing
algebra). -/

/-- Lifting commutes with cut-`0` instantiation (the `j = 0` face of
`liftN_inst_comm`, named because every β/let/telescope case uses exactly
this face). -/
theorem liftN_inst0 (e a : VExpr) (n k : Nat) :
    (e.inst a).liftN n k = (e.liftN n (k + 1)).inst (a.liftN n k) := by
  simpa using VExpr.liftN_inst_comm e (Nat.zero_le k) a n

/-- Lifting maps through an application spine. -/
theorem liftN_mkAppN : ∀ (as : List VExpr) (f : VExpr) (n k : Nat),
    (VExpr.mkAppN f as).liftN n k
      = VExpr.mkAppN (f.liftN n k) (as.map (·.liftN n k)) := by
  intro as
  induction as with
  | nil => intros; rfl
  | cons a as ih =>
    intro f n k
    simp only [VExpr.mkAppN_cons, List.map_cons]
    rw [ih]
    rfl

/-- `getD` under `map`, below the length. -/
theorem getD_map_of_lt {α β : Type _} (f : α → β) {l : List α} {i : Nat}
    (h : i < l.length) (d : α) (d' : β) :
    (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem h]
  rfl

/-- Lifting commutes with the telescope residual. -/
theorem piResidualV_liftN : ∀ {as : List VExpr} {T r : VExpr},
    piResidualV T as = some r → ∀ (n k : Nat),
      piResidualV (T.liftN n k) (as.map (·.liftN n k))
        = some (r.liftN n k) := by
  intro as
  induction as with
  | nil =>
    intro T r h n k
    cases h
    rfl
  | cons a as ih =>
    intro T r h n k
    cases T
    case pi A B =>
      show piResidualV ((B.liftN n (k + 1)).inst (a.liftN n k))
        (as.map (·.liftN n k)) = some (r.liftN n k)
      rw [← liftN_inst0]
      exact ih (by simpa only [piResidualV] using h) n k
    all_goals simp [piResidualV] at h

/-- Lifting moves through the reverse instantiation chain when the
subject is lifted above the chain's cut (the generalization that makes
the closed corollary below inductive). -/
theorem instRevChain_liftN_high : ∀ (vs : List VExpr) (X : VExpr) (n k : Nat),
    (VExpr.instRevChain vs X).liftN n k
      = VExpr.instRevChain (vs.map (·.liftN n k))
          (X.liftN n (k + vs.length)) := by
  intro vs
  induction vs with
  | nil =>
    intro X n k
    simp [VExpr.instRevChain]
  | cons a vs ih =>
    intro X n k
    show (VExpr.instRevChain vs (X.inst (a.liftN vs.length) 0)).liftN n k = _
    rw [ih]
    show VExpr.instRevChain _ ((X.inst (a.liftN vs.length) 0).liftN n
        (k + vs.length)) = _
    rw [VExpr.liftN_inst_comm X (Nat.zero_le (k + vs.length))
      (a.liftN vs.length) n]
    show VExpr.instRevChain (vs.map _)
        ((X.liftN n (k + vs.length + 1)).inst
          ((a.liftN vs.length).liftN n (k + vs.length)) 0) = _
    rw [show (a.liftN vs.length).liftN n (k + vs.length)
        = (a.liftN n k).liftN vs.length from
      (VExpr.liftN_liftN_comm a (Nat.zero_le k) vs.length n).symm]
    show _ = VExpr.instRevChain (vs.map _)
      ((X.liftN n (k + (vs.length + 1))).inst
        ((a.liftN n k).liftN ((vs.map (·.liftN n k)).length)) 0)
    rw [List.length_map, show k + vs.length + 1 = k + (vs.length + 1) from
      by omega]

/-- Lifting a fully consumed reverse instantiation chain: the subject's
variables are all below the chain, so only the chain's arguments
lift. -/
theorem instRevChain_liftN {vs : List VExpr} {X : VExpr}
    (h : VExpr.bvarsBelow vs.length X) (n k : Nat) :
    (VExpr.instRevChain vs X).liftN n k
      = VExpr.instRevChain (vs.map (·.liftN n k)) X := by
  rw [instRevChain_liftN_high, VExpr.liftN_eq_self
    (VExpr.bvarsBelow.mono (by omega) h)]

section Closed

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- The `Nat`-literal term is closed (the valuation is). -/
theorem natLitV_closed (hcl : ∀ n ψ, VExpr.Closed (cval n ψ)) (m : Nat) :
    VExpr.Closed (natLitV cval φ m) :=
  natLitT_closed (hcl _ _) (hcl _ _) m

/-- Lifting maps through the projection spines of a structural-eta
comparison (the heads are valuation leaves, hence closed). -/
theorem projSpinesV_liftN (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    (T : Name) (ψt : Name → Nat) (ts : List VExpr) (b : VExpr)
    (nF : Nat) (n k : Nat) :
    (projSpinesV cval T ψt ts b nF).map (·.liftN n k)
      = projSpinesV cval T ψt (ts.map (·.liftN n k)) (b.liftN n k) nF := by
  simp only [projSpinesV, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  rw [liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _), List.map_append]
  rfl

/-- Lifting maps through the eta-rescue fabrication spine. -/
theorem etaFabArgsV_liftN (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    (T : Name) (ψt : Name → Nat) (ts : List VExpr) (major : VExpr)
    (nF : Nat) (n k : Nat) :
    (etaFabArgsV cval T ψt ts major nF).map (·.liftN n k)
      = etaFabArgsV cval T ψt (ts.map (·.liftN n k)) (major.liftN n k)
          nF := by
  simp only [etaFabArgsV, List.map_append, projSpinesV_liftN hcl]

end Closed

/-! ## The weakened forms (the five motives) -/

/-- Weakened reduction: the statement `Red.weakenN` proves, and the
first motive of the mutual induction. -/
abbrev RedW (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (Δ : List VExpr) (v w : VExpr) : Prop :=
  ∀ {n k : Nat} {Δ' : List VExpr}, LiftCtx n k Δ Δ' →
    Red μ env cval φ Δ' (v.liftN n k) (w.liftN n k)

/-- Weakened inference. -/
abbrev InfW (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (Δ : List VExpr) (v T : VExpr) : Prop :=
  ∀ {n k : Nat} {Δ' : List VExpr}, LiftCtx n k Δ Δ' →
    Infer μ env cval φ Δ' (v.liftN n k) (T.liftN n k)

/-- Weakened definitional equality. -/
abbrev DeqW (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (Δ : List VExpr) (a b : VExpr) : Prop :=
  ∀ {n k : Nat} {Δ' : List VExpr}, LiftCtx n k Δ Δ' →
    DefEq μ env cval φ Δ' (a.liftN n k) (b.liftN n k)

/-- Weakened telescope certification. -/
abbrev TeleW (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (Δ : List VExpr) (T : VExpr) (as : List VExpr)
    (rest : VExpr) : Prop :=
  ∀ {n k : Nat} {Δ' : List VExpr}, LiftCtx n k Δ Δ' →
    Tele μ env cval φ Δ' (T.liftN n k) (as.map (·.liftN n k))
      (rest.liftN n k)

/-- Weakened spine equality. -/
abbrev DeqLW (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (Δ : List VExpr) (as bs : List VExpr) : Prop :=
  ∀ {n k : Nat} {Δ' : List VExpr}, LiftCtx n k Δ Δ' →
    DefEqL μ env cval φ Δ' (as.map (·.liftN n k)) (bs.map (·.liftN n k))

/-! ## The 42 cases

One private lemma per constructor, in declaration order, each shaped
exactly as its recursor minor premise (constructor hypotheses, then
IHs).  `hcl` (every valuation leaf is closed) is the one ambient
hypothesis — the `EnvTT.cval_closed`-shaped fact every consumer has. -/

section Cases

variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/- Red (R1–R14) -/

private theorem wkRedRefl {Δ : List VExpr} {v : VExpr} :
    RedW μ env cval φ Δ v v := by
  intro _ _ _ _
  exact .refl

private theorem wkRedTrans {Δ : List VExpr} {v w x : VExpr}
    (_ : Red μ env cval φ Δ v w) (_ : Red μ env cval φ Δ w x)
    (ih1 : RedW μ env cval φ Δ v w) (ih2 : RedW μ env cval φ Δ w x) :
    RedW μ env cval φ Δ v x := by
  intro _ _ _ H
  exact .trans (ih1 H) (ih2 H)

private theorem wkRedAppFn {Δ : List VExpr} {f f' a : VExpr}
    (_ : Red μ env cval φ Δ f f')
    (ih : RedW μ env cval φ Δ f f') :
    RedW μ env cval φ Δ (.app f a) (.app f' a) := by
  intro _ _ _ H
  exact .appFn (ih H)

private theorem wkRedBeta {Δ : List VExpr} {A b a ta : VExpr}
    (_ : Infer μ env cval φ Δ a ta) (_ : DefEq μ env cval φ Δ ta A)
    (ih1 : InfW μ env cval φ Δ a ta) (ih2 : DeqW μ env cval φ Δ ta A) :
    RedW μ env cval φ Δ (.app (.lam A b) a) (b.inst a) := by
  intro n k Δ' H
  rw [liftN_inst0]
  exact .beta (ih1 H) (ih2 H)

private theorem wkRedZeta {Δ : List VExpr} {T v b : VExpr} :
    RedW μ env cval φ Δ (.letE T v b) (b.inst v) := by
  intro n k Δ' H
  rw [liftN_inst0]
  exact .zeta

private theorem wkRedProjRed (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {p P fv ta tta te tte : VExpr}
    {i : Nat} {sn : Name} {entry : ProjEntry} {ci : ConstantInfo}
    {us : List Level} {vs : List VExpr}
    (h1 : env.findProj? sn i = some entry) (h2 : entry.native = true)
    (h3 : i < entry.numFields)
    (h4 : vs.length = entry.numParams + entry.numFields)
    (h5 : us.length = entry.levelParams.length)
    (h6 : env.find? entry.ctor = some ci)
    (h7 : us.length = ci.toConstantVal.levelParams.length)
    (h8 : P = VExpr.mkAppN
      (cval entry.ctor
        (Level.substFn φ ci.toConstantVal.levelParams us)) vs)
    (h9 : vs[entry.numParams + i]? = some fv)
    (_ : Red μ env cval φ Δ p P)
    (_ : Infer μ env cval φ Δ fv ta) (_ : Infer μ env cval φ Δ ta tta)
    (_ : Red μ env cval φ Δ tta
      (.sort ((Level.subst entry.levelParams us entry.fieldSort).eval φ)))
    (_ : Infer μ env cval φ Δ P te) (_ : Infer μ env cval φ Δ te tte)
    (_ : Red μ env cval φ Δ tte
      (.sort ((Level.subst entry.levelParams us entry.structSort).eval φ)))
    (ihp : RedW μ env cval φ Δ p P)
    (ihfv : InfW μ env cval φ Δ fv ta)
    (ihta : InfW μ env cval φ Δ ta tta)
    (ihtta : RedW μ env cval φ Δ tta
      (.sort ((Level.subst entry.levelParams us entry.fieldSort).eval φ)))
    (ihP : InfW μ env cval φ Δ P te)
    (ihte : InfW μ env cval φ Δ te tte)
    (ihtte : RedW μ env cval φ Δ tte
      (.sort ((Level.subst entry.levelParams us entry.structSort).eval φ))) :
    RedW μ env cval φ Δ (.proj i p) fv := by
  intro n k Δ' H
  refine Red.projRed (vs := vs.map (·.liftN n k)) h1 h2 h3
    (by simpa using h4) h5 h6 h7 ?_ ?_ (ihp H) (ihfv H) (ihta H)
    (ihtta H) (ihP H) (ihte H) (ihtte H)
  · rw [h8, liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _)]
  · rw [List.getElem?_map, h9]
    rfl

private theorem wkRedStrLit (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {s : String} {SC P : VExpr}
    (h1 : strLitSupported env = true)
    (h2 : denoteClosed cval env φ (strLitToConstructor s) = some SC)
    (h3 : VExpr.Closed SC)
    (_ : Red μ env cval φ Δ SC P)
    (ih : RedW μ env cval φ Δ SC P) :
    RedW μ env cval φ Δ (strLitT cval env φ s) P := by
  intro n k Δ' H
  rw [liftN_eq_self_of_closed (strLitT_closed hcl s)]
  refine Red.strLitCtor h1 h2 h3 ?_
  simpa [liftN_eq_self_of_closed h3] using ih H

private theorem wkRedNatSucc (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {va : VExpr} {m : Nat}
    (h1 : natLitSupported env = true)
    (_ : Red μ env cval φ Δ va (natLitV cval φ m))
    (ih : RedW μ env cval φ Δ va (natLitV cval φ m)) :
    RedW μ env cval φ Δ (.app (succV cval φ) va)
      (natLitV cval φ (m + 1)) := by
  intro n k Δ' H
  have hs : VExpr.Closed (succV cval φ) := hcl _ _
  simp only [VExpr.liftN_app, liftN_eq_self_of_closed hs,
    liftN_eq_self_of_closed (natLitV_closed hcl (m + 1))]
  refine Red.natSucc h1 ?_
  simpa [liftN_eq_self_of_closed (natLitV_closed hcl m)] using ih H

private theorem wkRedNatOp1 (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {va V : VExpr} {c : Name} {m : Nat} {r : Expr}
    (h1 : c = natPredName ∨ c = natLog2Name)
    (h2 : natOpGuard env c = true)
    (h3 : natOpResult c m 0 = some r)
    (h4 : denoteClosed cval env φ r = some V) (h5 : VExpr.Closed V)
    (_ : Red μ env cval φ Δ va (natLitV cval φ m))
    (ih : RedW μ env cval φ Δ va (natLitV cval φ m)) :
    RedW μ env cval φ Δ (.app (cval c (Level.substFn φ [] [])) va) V := by
  intro n k Δ' H
  simp only [VExpr.liftN_app, liftN_eq_self_of_closed (hcl _ _),
    liftN_eq_self_of_closed h5]
  refine Red.natOp1 h1 h2 h3 h4 h5 ?_
  simpa [liftN_eq_self_of_closed (natLitV_closed hcl m)] using ih H

private theorem wkRedNatOp2 (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {va vb V : VExpr} {c : Name} {m₁ m₂ : Nat} {r : Expr}
    (h1 : c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
      c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
      c = natDivName ∨ c = natModName ∨ c = natGcdName ∨
      c = natLandName ∨ c = natLorName ∨ c = natXorName ∨
      c = natShiftLeftName ∨ c = natShiftRightName)
    (h2 : natOpGuard env c = true)
    (h3 : natOpResult c m₁ m₂ = some r)
    (h4 : denoteClosed cval env φ r = some V) (h5 : VExpr.Closed V)
    (_ : Red μ env cval φ Δ va (natLitV cval φ m₁))
    (_ : Red μ env cval φ Δ vb (natLitV cval φ m₂))
    (ih1 : RedW μ env cval φ Δ va (natLitV cval φ m₁))
    (ih2 : RedW μ env cval φ Δ vb (natLitV cval φ m₂)) :
    RedW μ env cval φ Δ
      (.app (.app (cval c (Level.substFn φ [] [])) va) vb) V := by
  intro n k Δ' H
  simp only [VExpr.liftN_app, liftN_eq_self_of_closed (hcl _ _),
    liftN_eq_self_of_closed h5]
  refine Red.natOp2 h1 h2 h3 h4 h5 ?_ ?_
  · simpa [liftN_eq_self_of_closed (natLitV_closed hcl m₁)] using ih1 H
  · simpa [liftN_eq_self_of_closed (natLitV_closed hcl m₂)] using ih2 H

private theorem wkRedIota (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {n' : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {rl : RecRule} {cvj : ConstantVal}
    {cnP cnF : Nat} {us usj : List Level}
    {xs ys : List VExpr} {m₀ m TV TVj R restR restC H' : VExpr}
    {cargs : List VExpr}
    (h1 : env.find? n' = some (.recInfo cv mI rP rules))
    (h2 : rules.find? (fun r' => r'.ctor == rl.ctor) = some rl)
    (h3 : rl.fire ≠ .inert)
    (h4 : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (h5 : rP ≤ mI) (h6 : xs.length = mI + 1)
    (h7 : ys.length = rl.ctorParams + rl.nfields)
    (h8 : us.length = cv.levelParams.length)
    (h9 : usj.length = cvj.levelParams.length)
    (h10 : (cv.type.stripPis (mI + 1)).isSome = true)
    (h11 : (cvj.type.stripPis (rl.ctorParams + rl.nfields)).isSome = true)
    (h12 : Level.isEquivList usj
      (recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1
      = some true)
    (h13 : denoteClosed cval env φ
      (cv.type.instantiateLevelParams cv.levelParams us) = some TV)
    (h13c : TV.Closed)
    (h14 : denoteClosed cval env φ
      (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVj)
    (h14c : TVj.Closed)
    (h15 : denoteClosed cval env φ
      (rl.rhs.instantiateLevelParams cv.levelParams us) = some R)
    (h15c : R.Closed)
    (h16 : m = VExpr.mkAppN
      (cval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys)
    (_ : Red μ env cval φ Δ (xs.getD mI default) m₀)
    (_ : Red μ env cval φ Δ m₀ m)
    (_ : rl.fire = .plain →
      DefEqL μ env cval φ Δ (ys.take rl.ctorParams)
        (xs.take rl.ctorParams))
    (_ : ∀ lvls pins, rl.fire = .nested lvls pins →
      ∀ i, i < rl.ctorParams → ∀ vp : VExpr,
        denote cval env φ rP
          (openRev 0 rP ((pins.getD i default).instantiateLevelParams
            cv.levelParams us)) = some vp →
        VExpr.bvarsBelow rP vp →
        DefEq μ env cval φ Δ (ys.getD i default)
          (VExpr.instRevChain (xs.take rP) vp))
    (_ : Tele μ env cval φ Δ TV (xs.take mI ++ [m]) restR)
    (_ : Tele μ env cval φ Δ TVj ys restC)
    (h23 : restC = VExpr.mkAppN H' cargs)
    (h24 : mI = rP ∨ cargs.length = rl.ctorParams + (mI - rP))
    (_ : DefEqL μ env cval φ Δ (cargs.drop rl.ctorParams)
      ((xs.take mI).drop rP))
    (ih17 : RedW μ env cval φ Δ (xs.getD mI default) m₀)
    (ih18 : RedW μ env cval φ Δ m₀ m)
    (ih19 : ∀ (_ : rl.fire = .plain),
      DeqLW μ env cval φ Δ (ys.take rl.ctorParams)
        (xs.take rl.ctorParams))
    (ih20 : ∀ lvls pins (_ : rl.fire = .nested lvls pins)
      (i : Nat) (_ : i < rl.ctorParams) (vp : VExpr)
      (_ : denote cval env φ rP
        (openRev 0 rP ((pins.getD i default).instantiateLevelParams
          cv.levelParams us)) = some vp)
      (_ : VExpr.bvarsBelow rP vp),
      DeqW μ env cval φ Δ (ys.getD i default)
        (VExpr.instRevChain (xs.take rP) vp))
    (ih21 : TeleW μ env cval φ Δ TV (xs.take mI ++ [m]) restR)
    (ih22 : TeleW μ env cval φ Δ TVj ys restC)
    (ih25 : DeqLW μ env cval φ Δ (cargs.drop rl.ctorParams)
      ((xs.take mI).drop rP)) :
    RedW μ env cval φ Δ
      (VExpr.mkAppN (cval n' (Level.substFn φ cv.levelParams us)) xs)
      (VExpr.mkAppN R (xs.take rP ++ ys.drop rl.ctorParams)) := by
  intro nn kk Δ' HH
  have hxs : mI < xs.length := by omega
  have hxtake : ((xs.take rP).map (·.liftN nn kk)).length = rP := by
    simp only [List.length_map, List.length_take]
    omega
  rw [liftN_mkAppN, liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _),
    liftN_eq_self_of_closed h15c, List.map_append, List.map_take,
    List.map_drop]
  refine Red.iota (m₀ := m₀.liftN nn kk) (m := m.liftN nn kk)
    (restR := restR.liftN nn kk) (restC := restC.liftN nn kk)
    (H := H'.liftN nn kk) (cargs := cargs.map (·.liftN nn kk))
    h1 h2 h3 h4 h5 (by simpa using h6) (by simpa using h7) h8 h9 h10 h11
    h12 h13 h13c h14 h14c h15 h15c ?_ ?_ (ih18 HH) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [h16, liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _)]
  · rw [getD_map_of_lt _ hxs default]
    exact ih17 HH
  · intro hp
    simpa [← List.map_take] using ih19 hp HH
  · intro lvls pins hf i hi vp hden hbb
    have hiy : i < ys.length := by omega
    have hlen : (xs.take rP).length = rP := by
      simp only [List.length_take]
      omega
    have hbb' : VExpr.bvarsBelow (xs.take rP).length vp := by
      rw [hlen]
      exact hbb
    rw [getD_map_of_lt _ hiy default, ← List.map_take,
      ← instRevChain_liftN hbb']
    exact ih20 lvls pins hf i hi vp hden hbb HH
  · simpa [liftN_eq_self_of_closed h13c, ← List.map_take] using ih21 HH
  · simpa [liftN_eq_self_of_closed h14c] using ih22 HH
  · rw [h23, liftN_mkAppN]
  · rcases h24 with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  · simpa [← List.map_take, ← List.map_drop] using ih25 HH

private theorem wkRedRescueK (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {m₀ tm TM tf TVj rest : VExpr} {recName T : Name}
    {cv cvj : ConstantVal} {mI rP : Nat} {rl : RecRule} {cnP cnF : Nat}
    {cvT : ConstantVal} {caps : IndCaps} {tus ust : List Level}
    {ts : List VExpr}
    (h1 : env.find? recName = some (.recInfo cv mI rP [rl]))
    (h2 : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (h3 : (cvj.type.piResult).getAppFn = .const T tus)
    (h4 : env.find? T = some (.indInfo cvT caps))
    (h5 : caps.ruleK = true) (h6 : cnF = 0)
    (h7 : cvj.levelParams.length = ust.length)
    (h8 : ust.length = cvT.levelParams.length)
    (h9 : cnP ≤ ts.length)
    (h10 : (cvj.type.stripPis cnP).isSome = true)
    (h11 : TM = VExpr.mkAppN
      (cval T (Level.substFn φ cvT.levelParams ust)) ts)
    (h12 : denoteClosed cval env φ
      (cvj.type.instantiateLevelParams cvj.levelParams ust) = some TVj)
    (h12c : TVj.Closed)
    (_ : Infer μ env cval φ Δ m₀ tm) (_ : Red μ env cval φ Δ tm TM)
    (_ : Tele μ env cval φ Δ TVj (ts.take cnP) rest)
    (_ : Infer μ env cval φ Δ
      (VExpr.mkAppN (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (ts.take cnP)) tf)
    (_ : DefEq μ env cval φ Δ TM tf)
    (_ : DefEq μ env cval φ Δ
      (VExpr.mkAppN (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (ts.take cnP)) m₀)
    (ih13 : InfW μ env cval φ Δ m₀ tm) (ih14 : RedW μ env cval φ Δ tm TM)
    (ih15 : TeleW μ env cval φ Δ TVj (ts.take cnP) rest)
    (ih16 : InfW μ env cval φ Δ
      (VExpr.mkAppN (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (ts.take cnP)) tf)
    (ih17 : DeqW μ env cval φ Δ TM tf)
    (ih18 : DeqW μ env cval φ Δ
      (VExpr.mkAppN (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (ts.take cnP)) m₀) :
    RedW μ env cval φ Δ m₀
      (VExpr.mkAppN (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (ts.take cnP)) := by
  intro nn kk Δ' HH
  have hfab : (VExpr.mkAppN
      (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
      (ts.take cnP)).liftN nn kk
    = VExpr.mkAppN (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
        ((ts.map (·.liftN nn kk)).take cnP) := by
    rw [liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _), List.map_take]
  rw [hfab]
  refine Red.rescueK (ts := ts.map (·.liftN nn kk))
    (rest := rest.liftN nn kk) h1 h2 h3 h4 h5 h6 h7
    h8 (by simpa using h9) h10 ?_ h12 h12c (ih13 HH) ?_ ?_ ?_ (ih17 HH) ?_
  · rw [h11, liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _)]
  · exact ih14 HH
  · simpa [liftN_eq_self_of_closed h12c, ← List.map_take] using ih15 HH
  · simpa [← hfab] using ih16 HH
  · simpa [← hfab] using ih18 HH

private theorem wkRedRescueEta (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {m₀ tm TM TVj rest : VExpr} {recName T : Name}
    {cv cvj : ConstantVal} {mI rP : Nat} {rl : RecRule} {cnP cnF : Nat}
    {cvT : ConstantVal} {caps : IndCaps} {tus ust : List Level}
    {ts : List VExpr}
    (h1 : env.find? recName = some (.recInfo cv mI rP [rl]))
    (h2 : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (h3 : (cvj.type.piResult).getAppFn = .const T tus)
    (h4 : env.find? T = some (.indInfo cvT caps))
    (h5 : caps.eta = true) (h6 : rl.ctor = caps.etaCtor)
    (h7 : Name.isProjFnShape recName = false)
    (h8 : ts.length = caps.etaParams)
    (h9 : ust.length = cvT.levelParams.length)
    (h10 : piResultNeverZero cvT.levelParams ust cvT.type = true)
    (h11 : cvj.levelParams.length = ust.length)
    (h12 : (cvj.type.stripPis (caps.etaParams + caps.etaFields)).isSome
      = true)
    (h13 : TM = VExpr.mkAppN
      (cval T (Level.substFn φ cvT.levelParams ust)) ts)
    (h14 : denoteClosed cval env φ
      (cvj.type.instantiateLevelParams cvj.levelParams ust) = some TVj)
    (h14c : TVj.Closed)
    (_ : Infer μ env cval φ Δ m₀ tm) (_ : Red μ env cval φ Δ tm TM)
    (_ : Tele μ env cval φ Δ TVj
      (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust) ts m₀
        caps.etaFields) rest)
    (_ : DefEq μ env cval φ Δ
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
        (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust) ts m₀
          caps.etaFields)) m₀)
    (ih15 : InfW μ env cval φ Δ m₀ tm) (ih16 : RedW μ env cval φ Δ tm TM)
    (ih17 : TeleW μ env cval φ Δ TVj
      (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust) ts m₀
        caps.etaFields) rest)
    (ih18 : DeqW μ env cval φ Δ
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
        (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust) ts m₀
          caps.etaFields)) m₀) :
    RedW μ env cval φ Δ m₀
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
        (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust) ts m₀
          caps.etaFields)) := by
  intro nn kk Δ' HH
  have hfab : (VExpr.mkAppN
      (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
      (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust) ts m₀
        caps.etaFields)).liftN nn kk
    = VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
        (etaFabArgsV cval T (Level.substFn φ cvT.levelParams ust)
          (ts.map (·.liftN nn kk)) (m₀.liftN nn kk) caps.etaFields) := by
    rw [liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _),
      etaFabArgsV_liftN hcl]
  rw [hfab]
  refine Red.rescueEta (ts := ts.map (·.liftN nn kk))
    (rest := rest.liftN nn kk) h1 h2 h3 h4 h5 h6
    h7 (by simpa using h8) h9 h10 h11 h12 ?_ h14 h14c (ih15 HH)
    (ih16 HH) ?_ ?_
  · rw [h13, liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _)]
  · simpa [liftN_eq_self_of_closed h14c, etaFabArgsV_liftN hcl]
      using ih17 HH
  · simpa [← hfab] using ih18 HH

private theorem wkRedRescueUnit0 (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {m₀ tm TM TVj rest : VExpr} {recName T : Name}
    {cv cvj : ConstantVal} {mI rP : Nat} {rl : RecRule} {cnP cnF : Nat}
    {cvT : ConstantVal} {caps : IndCaps} {tus ust : List Level}
    {ts : List VExpr}
    (h1 : env.find? recName = some (.recInfo cv mI rP [rl]))
    (h2 : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (h3 : (cvj.type.piResult).getAppFn = .const T tus)
    (h4 : env.find? T = some (.indInfo cvT caps))
    (h5 : caps.eta = true) (h6 : rl.ctor = caps.etaCtor)
    (h7 : Name.isProjFnShape recName = false)
    (h8 : caps.etaFields = 0)
    (h9 : ts.length = caps.etaParams)
    (h10 : ust.length = cvT.levelParams.length)
    (h11 : piResultNeverZero cvT.levelParams ust cvT.type = true)
    (h12 : cvj.levelParams.length = ust.length)
    (h13 : (cvj.type.stripPis (caps.etaParams + caps.etaFields)).isSome
      = true)
    (h14 : TM = VExpr.mkAppN
      (cval T (Level.substFn φ cvT.levelParams ust)) ts)
    (h15 : denoteClosed cval env φ
      (cvj.type.instantiateLevelParams cvj.levelParams ust) = some TVj)
    (h15c : TVj.Closed)
    (_ : Infer μ env cval φ Δ m₀ tm) (_ : Red μ env cval φ Δ tm TM)
    (_ : Tele μ env cval φ Δ TVj ts rest)
    (_ : DefEq μ env cval φ Δ
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust)) ts) m₀)
    (ih16 : InfW μ env cval φ Δ m₀ tm) (ih17 : RedW μ env cval φ Δ tm TM)
    (ih18 : TeleW μ env cval φ Δ TVj ts rest)
    (ih19 : DeqW μ env cval φ Δ
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust)) ts)
      m₀) :
    RedW μ env cval φ Δ m₀
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust)) ts) := by
  intro nn kk Δ' HH
  have hfab : (VExpr.mkAppN
      (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
      ts).liftN nn kk
    = VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
        (ts.map (·.liftN nn kk)) := by
    rw [liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _)]
  rw [hfab]
  refine Red.rescueUnit0 (ts := ts.map (·.liftN nn kk))
    (rest := rest.liftN nn kk) h1 h2 h3 h4 h5 h6
    h7 h8 (by simpa using h9) h10 h11 h12 h13 ?_ h15 h15c (ih16 HH)
    (ih17 HH) ?_ ?_
  · rw [h14, liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _)]
  · simpa [liftN_eq_self_of_closed h15c] using ih18 HH
  · simpa [← hfab] using ih19 HH

/- Infer (I1–I10) -/

private theorem wkInfSort {Δ : List VExpr} {u : Nat} :
    InfW μ env cval φ Δ (.sort u) (.sort (u + 1)) := by
  intro _ _ _ _
  exact .sort

private theorem wkInfBvar {Δ : List VExpr} {i : Nat} {A : VExpr}
    (h : Δ[i]? = some A) :
    InfW μ env cval φ Δ (.bvar i) (A.liftN (i + 1)) := by
  intro nn kk Δ' HH
  by_cases hik : i < kk
  · have h1 := Infer.bvar (μ := μ) (env := env) (cval := cval) (φ := φ)
      (HH.getElem?_lt hik h)
    rw [VExpr.liftN_liftN_comm A (Nat.zero_le (kk - 1 - i)) (i + 1) nn,
      show kk - 1 - i + (i + 1) = kk from by omega] at h1
    simpa only [VExpr.liftN_bvar, if_pos hik] using h1
  · rw [VExpr.liftN_liftN_absorb A (Nat.zero_le kk)
      (show kk ≤ 0 + (i + 1) by omega) nn,
      show i + 1 + nn = i + nn + 1 from by omega]
    simpa only [VExpr.liftN_bvar, if_neg hik] using
      Infer.bvar (μ := μ) (env := env) (cval := cval) (φ := φ)
        (HH.getElem?_ge (by omega) h)

private theorem wkInfConst (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {n : Name} {ci : ConstantInfo} {us : List Level}
    {T : VExpr}
    (h1 : env.find? n = some ci)
    (h2 : us.length = ci.toConstantVal.levelParams.length)
    (h3 : denoteClosed cval env φ
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) = some T)
    (h3c : T.Closed) :
    InfW μ env cval φ Δ
      (cval n (Level.substFn φ ci.toConstantVal.levelParams us)) T := by
  intro nn kk Δ' HH
  rw [liftN_eq_self_of_closed (hcl _ _), liftN_eq_self_of_closed h3c]
  exact .const h1 h2 h3 h3c

private theorem wkInfLitNat (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {m : Nat} (h1 : natLitSupported env = true) :
    InfW μ env cval φ Δ (natLitV cval φ m)
      (cval natName (Level.substFn φ [] [])) := by
  intro nn kk Δ' HH
  rw [liftN_eq_self_of_closed (natLitV_closed hcl m),
    liftN_eq_self_of_closed (hcl _ _)]
  exact .litNat h1

private theorem wkInfLitStr (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {s : String} (h1 : strLitSupported env = true) :
    InfW μ env cval φ Δ (strLitT cval env φ s)
      (cval stringName (Level.substFn φ [] [])) := by
  intro nn kk Δ' HH
  rw [liftN_eq_self_of_closed (strLitT_closed hcl s),
    liftN_eq_self_of_closed (hcl _ _)]
  exact .litStr h1

private theorem wkInfPi {Δ : List VExpr} {A B tA tB : VExpr} {u v : Nat}
    (_ : Infer μ env cval φ Δ A tA)
    (_ : Red μ env cval φ Δ tA (.sort u))
    (_ : Infer μ env cval φ (A :: Δ) B tB)
    (_ : Red μ env cval φ (A :: Δ) tB (.sort v))
    (ihA : InfW μ env cval φ Δ A tA)
    (ihtA : RedW μ env cval φ Δ tA (.sort u))
    (ihB : InfW μ env cval φ (A :: Δ) B tB)
    (ihtB : RedW μ env cval φ (A :: Δ) tB (.sort v)) :
    InfW μ env cval φ Δ (.pi A B) (.sort (imax u v)) := by
  intro _ _ _ H
  exact .pi (ihA H) (ihtA H) (ihB (H.succ _)) (ihtB (H.succ _))

private theorem wkInfLam {Δ : List VExpr} {A b tA B : VExpr} {u : Nat}
    (_ : Infer μ env cval φ Δ A tA)
    (_ : Red μ env cval φ Δ tA (.sort u))
    (_ : Infer μ env cval φ (A :: Δ) b B)
    (ihA : InfW μ env cval φ Δ A tA)
    (ihtA : RedW μ env cval φ Δ tA (.sort u))
    (ihb : InfW μ env cval φ (A :: Δ) b B) :
    InfW μ env cval φ Δ (.lam A b) (.pi A B) := by
  intro _ _ _ H
  exact .lam (ihA H) (ihtA H) (ihb (H.succ _))

private theorem wkInfApp {Δ : List VExpr} {f a tf A B ta : VExpr}
    (_ : Infer μ env cval φ Δ f tf)
    (_ : Red μ env cval φ Δ tf (.pi A B))
    (_ : Infer μ env cval φ Δ a ta)
    (_ : DefEq μ env cval φ Δ ta A)
    (ihf : InfW μ env cval φ Δ f tf)
    (ihtf : RedW μ env cval φ Δ tf (.pi A B))
    (iha : InfW μ env cval φ Δ a ta)
    (ihd : DeqW μ env cval φ Δ ta A) :
    InfW μ env cval φ Δ (.app f a) (B.inst a) := by
  intro nn kk Δ' HH
  rw [liftN_inst0]
  exact .app (ihf HH) (ihtf HH) (iha HH) (ihd HH)

private theorem wkInfProj (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {p tp TP resV : VExpr} {i : Nat} {T : Name}
    {entry : ProjEntry} {ciT : ConstantInfo} {us : List Level}
    {ps : List VExpr}
    (h1 : env.findProj? T i = some entry) (h2 : entry.native = true)
    (h3 : ps.length = entry.numParams)
    (h4 : us.length = entry.levelParams.length)
    (h5 : env.find? T = some ciT)
    (h6 : us.length = ciT.toConstantVal.levelParams.length)
    (h7 : denoteClosed cval env φ
      (entry.ty.instantiateLevelParams entry.levelParams us) = some TP)
    (h7c : TP.Closed)
    (h8 : piResidualV TP (ps ++ [p]) = some resV)
    (_ : Infer μ env cval φ Δ p tp)
    (_ : Red μ env cval φ Δ tp
      (VExpr.mkAppN
        (cval T (Level.substFn φ ciT.toConstantVal.levelParams us)) ps))
    (ihp : InfW μ env cval φ Δ p tp)
    (ihr : RedW μ env cval φ Δ tp
      (VExpr.mkAppN
        (cval T (Level.substFn φ ciT.toConstantVal.levelParams us)) ps)) :
    InfW μ env cval φ Δ (.proj i p) resV := by
  intro nn kk Δ' HH
  refine Infer.proj (ps := ps.map (·.liftN nn kk)) h1 h2
    (by simpa using h3) h4 h5 h6 h7 h7c ?_ (ihp HH) ?_
  · have := piResidualV_liftN h8 nn kk
    rw [liftN_eq_self_of_closed h7c, List.map_append] at this
    simpa using this
  · simpa [liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _)] using ihr HH

private theorem wkInfLetE {Δ : List VExpr} {T v b tT tv B : VExpr}
    {u : Nat}
    (_ : Infer μ env cval φ Δ T tT)
    (_ : Red μ env cval φ Δ tT (.sort u))
    (_ : Infer μ env cval φ Δ v tv)
    (_ : DefEq μ env cval φ Δ tv T)
    (_ : Infer μ env cval φ Δ (b.inst v) B)
    (ihT : InfW μ env cval φ Δ T tT)
    (ihtT : RedW μ env cval φ Δ tT (.sort u))
    (ihv : InfW μ env cval φ Δ v tv)
    (ihd : DeqW μ env cval φ Δ tv T)
    (ihb : InfW μ env cval φ Δ (b.inst v) B) :
    InfW μ env cval φ Δ (.letE T v b) B := by
  intro nn kk Δ' HH
  have hb := ihb HH
  rw [liftN_inst0] at hb
  exact .letE (ihT HH) (ihtT HH) (ihv HH) (ihd HH) hb

/- DefEq (D1–D14) -/

private theorem wkDeqRefl {Δ : List VExpr} {v : VExpr} :
    DeqW μ env cval φ Δ v v := by
  intro _ _ _ _
  exact .refl

private theorem wkDeqSymm {Δ : List VExpr} {a b : VExpr}
    (_ : DefEq μ env cval φ Δ a b) (ih : DeqW μ env cval φ Δ a b) :
    DeqW μ env cval φ Δ b a := by
  intro _ _ _ H
  exact .symm (ih H)

private theorem wkDeqTrans {Δ : List VExpr} {a b c : VExpr}
    (_ : DefEq μ env cval φ Δ a b) (_ : DefEq μ env cval φ Δ b c)
    (ih1 : DeqW μ env cval φ Δ a b) (ih2 : DeqW μ env cval φ Δ b c) :
    DeqW μ env cval φ Δ a c := by
  intro _ _ _ H
  exact .trans (ih1 H) (ih2 H)

private theorem wkDeqOfRed {Δ : List VExpr} {a a' : VExpr}
    (_ : Red μ env cval φ Δ a a') (ih : RedW μ env cval φ Δ a a') :
    DeqW μ env cval φ Δ a a' := by
  intro _ _ _ H
  exact .ofRed (ih H)

private theorem wkDeqPiCong {Δ : List VExpr} {A₁ A₂ B₁ B₂ : VExpr}
    (_ : DefEq μ env cval φ Δ A₁ A₂)
    (_ : DefEq μ env cval φ (A₁ :: Δ) B₁ B₂)
    (ih1 : DeqW μ env cval φ Δ A₁ A₂)
    (ih2 : DeqW μ env cval φ (A₁ :: Δ) B₁ B₂) :
    DeqW μ env cval φ Δ (.pi A₁ B₁) (.pi A₂ B₂) := by
  intro _ _ _ H
  exact .piCong (ih1 H) (ih2 (H.succ _))

private theorem wkDeqLamCong {Δ : List VExpr} {A₁ A₂ b₁ b₂ : VExpr}
    (_ : DefEq μ env cval φ Δ A₁ A₂)
    (_ : DefEq μ env cval φ (A₁ :: Δ) b₁ b₂)
    (ih1 : DeqW μ env cval φ Δ A₁ A₂)
    (ih2 : DeqW μ env cval φ (A₁ :: Δ) b₁ b₂) :
    DeqW μ env cval φ Δ (.lam A₁ b₁) (.lam A₂ b₂) := by
  intro _ _ _ H
  exact .lamCong (ih1 H) (ih2 (H.succ _))

private theorem wkDeqAppCong {Δ : List VExpr} {h₁ h₂ : VExpr}
    {as₁ as₂ : List VExpr}
    (hlen : as₁.length = as₂.length)
    (_ : DefEq μ env cval φ Δ h₁ h₂)
    (_ : DefEqL μ env cval φ Δ as₁ as₂)
    (ih1 : DeqW μ env cval φ Δ h₁ h₂)
    (ih2 : DeqLW μ env cval φ Δ as₁ as₂) :
    DeqW μ env cval φ Δ (VExpr.mkAppN h₁ as₁) (VExpr.mkAppN h₂ as₂) := by
  intro nn kk Δ' HH
  rw [liftN_mkAppN, liftN_mkAppN]
  exact .appCong (by simpa using hlen) (ih1 HH) (ih2 HH)

private theorem wkDeqIrrelProp {Δ : List VExpr}
    {a b ta sta tb stb : VExpr}
    (_ : Infer μ env cval φ Δ a ta)
    (_ : Infer μ env cval φ Δ ta sta)
    (_ : Red μ env cval φ Δ sta (.sort 0))
    (_ : Infer μ env cval φ Δ b tb)
    (_ : Infer μ env cval φ Δ tb stb)
    (_ : Red μ env cval φ Δ stb (.sort 0))
    (ih1 : InfW μ env cval φ Δ a ta)
    (ih2 : InfW μ env cval φ Δ ta sta)
    (ih3 : RedW μ env cval φ Δ sta (.sort 0))
    (ih4 : InfW μ env cval φ Δ b tb)
    (ih5 : InfW μ env cval φ Δ tb stb)
    (ih6 : RedW μ env cval φ Δ stb (.sort 0)) :
    DeqW μ env cval φ Δ a b := by
  intro _ _ _ H
  exact .irrelProp (ih1 H) (ih2 H) (ih3 H) (ih4 H) (ih5 H) (ih6 H)

private theorem wkDeqIrrelUnit (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {a b ta tb : VExpr} {c₁ c₂ : Name}
    {us₁ us₂ : List Level}
    (h1 : isUnitLikeTy env (.const c₁ us₁) = true)
    (h2 : us₁.length = (levelParamsAt env c₁).length)
    (h3 : isUnitLikeTy env (.const c₂ us₂) = true)
    (h4 : us₂.length = (levelParamsAt env c₂).length)
    (_ : Infer μ env cval φ Δ a ta)
    (_ : Red μ env cval φ Δ ta
      (cval c₁ (Level.substFn φ (levelParamsAt env c₁) us₁)))
    (_ : Infer μ env cval φ Δ b tb)
    (_ : Red μ env cval φ Δ tb
      (cval c₂ (Level.substFn φ (levelParamsAt env c₂) us₂)))
    (ih1 : InfW μ env cval φ Δ a ta)
    (ih2 : RedW μ env cval φ Δ ta
      (cval c₁ (Level.substFn φ (levelParamsAt env c₁) us₁)))
    (ih3 : InfW μ env cval φ Δ b tb)
    (ih4 : RedW μ env cval φ Δ tb
      (cval c₂ (Level.substFn φ (levelParamsAt env c₂) us₂))) :
    DeqW μ env cval φ Δ a b := by
  intro nn kk Δ' HH
  refine DefEq.irrelUnit h1 h2 h3 h4 (ih1 HH) ?_ (ih3 HH) ?_
  · simpa [liftN_eq_self_of_closed (hcl _ _)] using ih2 HH
  · simpa [liftN_eq_self_of_closed (hcl _ _)] using ih4 HH

private theorem wkDeqStructEta (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {b tb TFv restT : VExpr} {c T : Name}
    {cvc cvT : ConstantVal} {caps : IndCaps} {cnP cnF : Nat}
    {us us' : List Level} {as ts : List VExpr}
    {cvp : Nat → ConstantVal} {mIp rPp : Nat → Nat}
    {rulesP : Nat → List RecRule} {TPv restP : Nat → VExpr}
    (h1 : env.find? c = some (.ctorInfo cvc cnP cnF))
    (h2 : as.length = cnP + cnF)
    (h3 : env.find? T = some (.indInfo cvT caps))
    (h4 : caps.eta = true) (h5 : caps.etaCtor = c)
    (h6 : caps.etaParams = cnP) (h7 : caps.etaFields = cnF)
    (h8 : reservedBasisNames.contains T = false)
    (h9 : reservedBasisNames.contains c = false)
    (h10 : ts.length = cnP)
    (h11 : us'.length = cvT.levelParams.length)
    (h12 : cvc.levelParams = cvT.levelParams)
    (h13 : (cvT.type.stripPis cnP).isSome = true)
    (h14 : Level.isEquivList us us' = some true)
    (h15 : denoteClosed cval env φ
      (cvT.type.instantiateLevelParams cvT.levelParams us') = some TFv)
    (h15c : TFv.Closed)
    (h16 : ∀ j, j < cnF →
      env.find? (projFnName T j)
        = some (.recInfo (cvp j) (mIp j) (rPp j) (rulesP j)))
    (h17 : ∀ j, j < cnF → (cvp j).levelParams = cvT.levelParams)
    (h18 : ∀ j, j < cnF → ((cvp j).type.stripPis (cnP + 1)).isSome = true)
    (h19 : ∀ j, j < cnF →
      denoteClosed cval env φ
        ((cvp j).type.instantiateLevelParams (cvp j).levelParams us')
        = some (TPv j))
    (h19c : ∀ j, j < cnF → (TPv j).Closed)
    (_ : Infer μ env cval φ Δ b tb)
    (_ : Red μ env cval φ Δ tb
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts))
    (_ : Tele μ env cval φ Δ TFv ts restT)
    (_ : ∀ j, j < cnF →
      Tele μ env cval φ Δ (TPv j) (ts ++ [b]) (restP j))
    (_ : DefEqL μ env cval φ Δ (as.take cnP) ts)
    (_ : DefEqL μ env cval φ Δ (as.drop cnP)
      (projSpinesV cval T (Level.substFn φ cvT.levelParams us') ts b cnF))
    (ih20 : InfW μ env cval φ Δ b tb)
    (ih21 : RedW μ env cval φ Δ tb
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts))
    (ih22 : TeleW μ env cval φ Δ TFv ts restT)
    (ih23 : ∀ j (_ : j < cnF),
      TeleW μ env cval φ Δ (TPv j) (ts ++ [b]) (restP j))
    (ih24 : DeqLW μ env cval φ Δ (as.take cnP) ts)
    (ih25 : DeqLW μ env cval φ Δ (as.drop cnP)
      (projSpinesV cval T (Level.substFn φ cvT.levelParams us') ts b
        cnF)) :
    DeqW μ env cval φ Δ
      (VExpr.mkAppN (cval c (Level.substFn φ cvc.levelParams us)) as)
      b := by
  intro nn kk Δ' HH
  rw [liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _)]
  refine DefEq.structEta (ts := ts.map (·.liftN nn kk)) (cvp := cvp)
    (mIp := mIp) (rPp := rPp) (rulesP := rulesP) (TPv := TPv)
    (restP := fun j => (restP j).liftN nn kk)
    (restT := restT.liftN nn kk)
    h1 (by simpa using h2) h3 h4 h5 h6 h7 h8 h9 (by simpa using h10)
    h11 h12 h13 h14 h15 h15c h16 h17 h18 h19 h19c (ih20 HH) ?_ ?_ ?_ ?_ ?_
  · simpa [liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _)] using ih21 HH
  · simpa [liftN_eq_self_of_closed h15c] using ih22 HH
  · intro j hj
    have := ih23 j hj HH
    rw [liftN_eq_self_of_closed (h19c j hj), List.map_append] at this
    simpa using this
  · simpa [← List.map_take] using ih24 HH
  · have := ih25 HH
    rw [projSpinesV_liftN hcl] at this
    simpa [← List.map_drop] using this

private theorem wkDeqStructUnit (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {a b ta tb TB TFv rest : VExpr} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps} {us' : List Level}
    {ts : List VExpr}
    (h1 : env.find? T = some (.indInfo cvT caps))
    (h2 : caps.unitlike = true)
    (h3 : reservedBasisNames.contains T = false)
    (h4 : ts.length = caps.unitParams)
    (h5 : us'.length = cvT.levelParams.length)
    (h6 : (cvT.type.stripPis caps.unitParams).isSome = true)
    (h7 : denoteClosed cval env φ
      (cvT.type.instantiateLevelParams cvT.levelParams us') = some TFv)
    (h7c : TFv.Closed)
    (_ : Infer μ env cval φ Δ a ta)
    (_ : Red μ env cval φ Δ ta
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts))
    (_ : Infer μ env cval φ Δ b tb)
    (_ : Red μ env cval φ Δ tb TB)
    (_ : DefEq μ env cval φ Δ
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts)
      TB)
    (_ : Tele μ env cval φ Δ TFv ts rest)
    (ih8 : InfW μ env cval φ Δ a ta)
    (ih9 : RedW μ env cval φ Δ ta
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts))
    (ih10 : InfW μ env cval φ Δ b tb)
    (ih11 : RedW μ env cval φ Δ tb TB)
    (ih12 : DeqW μ env cval φ Δ
      (VExpr.mkAppN (cval T (Level.substFn φ cvT.levelParams us')) ts)
      TB)
    (ih13 : TeleW μ env cval φ Δ TFv ts rest) :
    DeqW μ env cval φ Δ a b := by
  intro nn kk Δ' HH
  refine DefEq.structUnit (ts := ts.map (·.liftN nn kk))
    (rest := rest.liftN nn kk) h1 h2 h3
    (by simpa using h4) h5 h6 h7 h7c (ih8 HH) ?_ (ih10 HH) (ih11 HH) ?_ ?_
  · simpa [liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _)] using ih9 HH
  · simpa [liftN_mkAppN, liftN_eq_self_of_closed (hcl _ _)] using ih12 HH
  · simpa [liftN_eq_self_of_closed h7c] using ih13 HH

private theorem wkDeqPairEta (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {pα pβ s₁ s₂ b tb A B : VExpr} {c c' : Name}
    {cvm : ConstantVal} {cvi : ConstantVal} {caps' : IndCaps}
    {cvr : ConstantVal} {mI rP : Nat} {rr : RecRule}
    {us us' : List Level}
    (h1 : env.find? c = some (.ctorInfo cvm 2 2))
    (h2 : env.find? c' = some (.indInfo cvi caps'))
    (h3 : env.find? (c'.str "rec") = some (.recInfo cvr mI rP [rr]))
    (h4 : rr.ctor = c) (h5 : rr.nfields = 2) (h6 : mI = rP)
    (h7 : reservedBasisNames.contains (c'.str "rec") = true)
    (h8 : Level.isEquivList us us' = some true)
    (h9 : us.length = cvm.levelParams.length)
    (h10 : us'.length = cvi.levelParams.length)
    (_ : Infer μ env cval φ Δ b tb)
    (_ : Red μ env cval φ Δ tb
      (.app (.app (cval c' (Level.substFn φ cvi.levelParams us')) A) B))
    (_ : DefEq μ env cval φ Δ pα A) (_ : DefEq μ env cval φ Δ pβ B)
    (_ : DefEq μ env cval φ Δ s₁ (.proj 0 b))
    (_ : DefEq μ env cval φ Δ s₂ (.proj 1 b))
    (ihb : InfW μ env cval φ Δ b tb)
    (ihr : RedW μ env cval φ Δ tb
      (.app (.app (cval c' (Level.substFn φ cvi.levelParams us')) A) B))
    (ihα : DeqW μ env cval φ Δ pα A) (ihβ : DeqW μ env cval φ Δ pβ B)
    (ih1 : DeqW μ env cval φ Δ s₁ (.proj 0 b))
    (ih2 : DeqW μ env cval φ Δ s₂ (.proj 1 b)) :
    DeqW μ env cval φ Δ
      (.app (.app (.app (.app
        (cval c (Level.substFn φ cvm.levelParams us)) pα) pβ) s₁) s₂)
      b := by
  intro nn kk Δ' HH
  simp only [VExpr.liftN_app, liftN_eq_self_of_closed (hcl _ _)]
  refine DefEq.pairEta h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (ihb HH) ?_
    (ihα HH) (ihβ HH) (ih1 HH) (ih2 HH)
  simpa [liftN_eq_self_of_closed (hcl _ _)] using ihr HH

private theorem wkDeqEta {Δ : List VExpr} {A₁ b₁ b tb A₂ B : VExpr}
    (_ : Infer μ env cval φ Δ b tb)
    (_ : Red μ env cval φ Δ tb (.pi A₂ B))
    (_ : DefEq μ env cval φ Δ A₂ A₁)
    (_ : DefEq μ env cval φ (A₁ :: Δ) b₁ (.app b.lift (.bvar 0)))
    (ihb : InfW μ env cval φ Δ b tb)
    (ihr : RedW μ env cval φ Δ tb (.pi A₂ B))
    (ihd : DeqW μ env cval φ Δ A₂ A₁)
    (ihe : DeqW μ env cval φ (A₁ :: Δ) b₁ (.app b.lift (.bvar 0))) :
    DeqW μ env cval φ Δ (.lam A₁ b₁) b := by
  intro nn kk Δ' HH
  have he := ihe (HH.succ A₁)
  simp only [VExpr.liftN_app, VExpr.liftN_bvar,
    if_pos (show (0 : Nat) < kk + 1 by omega)] at he
  rw [show (VExpr.lift b).liftN nn (kk + 1) = (b.liftN nn kk).lift from
    (VExpr.liftN_liftN_comm b (Nat.zero_le kk) 1 nn).symm] at he
  exact .eta (ihb HH) (ihr HH) (ihd HH) he

private theorem wkDeqLitSuccApp (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {x : VExpr} {m : Nat}
    (h1 : natLitSupported env = true)
    (_ : DefEq μ env cval φ Δ (natLitV cval φ m) x)
    (ih : DeqW μ env cval φ Δ (natLitV cval φ m) x) :
    DeqW μ env cval φ Δ (natLitV cval φ (m + 1))
      (.app (succV cval φ) x) := by
  intro nn kk Δ' HH
  simp only [VExpr.liftN_app,
    liftN_eq_self_of_closed (natLitV_closed hcl (m + 1)),
    liftN_eq_self_of_closed (show VExpr.Closed (succV cval φ) from hcl _ _)]
  refine DefEq.litSuccApp h1 ?_
  simpa [liftN_eq_self_of_closed (natLitV_closed hcl m)] using ih HH

/- Tele / DefEqL -/

private theorem wkTeleNil {Δ : List VExpr} {T : VExpr} :
    TeleW μ env cval φ Δ T [] T := by
  intro _ _ _ _
  exact .nil

private theorem wkTeleCons {Δ : List VExpr} {A B a ta rest : VExpr}
    {as : List VExpr}
    (_ : Infer μ env cval φ Δ a ta) (_ : DefEq μ env cval φ Δ ta A)
    (_ : Tele μ env cval φ Δ (B.inst a) as rest)
    (ih1 : InfW μ env cval φ Δ a ta)
    (ih2 : DeqW μ env cval φ Δ ta A)
    (ih3 : TeleW μ env cval φ Δ (B.inst a) as rest) :
    TeleW μ env cval φ Δ (.pi A B) (a :: as) rest := by
  intro nn kk Δ' HH
  have h3 := ih3 HH
  rw [liftN_inst0] at h3
  exact .cons (ih1 HH) (ih2 HH) h3

private theorem wkDeqLNil {Δ : List VExpr} :
    DeqLW μ env cval φ Δ [] [] := by
  intro _ _ _ _
  exact .nil

private theorem wkDeqLCons {Δ : List VExpr} {a b : VExpr}
    {as bs : List VExpr}
    (_ : DefEq μ env cval φ Δ a b) (_ : DefEqL μ env cval φ Δ as bs)
    (ih1 : DeqW μ env cval φ Δ a b)
    (ih2 : DeqLW μ env cval φ Δ as bs) :
    DeqLW μ env cval φ Δ (a :: as) (b :: bs) := by
  intro _ _ _ H
  exact .cons (ih1 H) (ih2 H)

end Cases

/-! ## The five weakening theorems (M1)

Each is one term-mode application of its recursor to the same 42 case
lemmas.  The motives are the `*W` forms above. -/

section M1

variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- **M1 for `Red`**: derivations lift along context insertion. -/
theorem Red.weakenN (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Γ : List VExpr} {v w : VExpr} (h : Red μ env cval φ Γ v w) :
    RedW μ env cval φ Γ v w :=
  Red.rec
    (motive_1 := fun Δ v w _ => RedW μ env cval φ Δ v w)
    (motive_2 := fun Δ v T _ => InfW μ env cval φ Δ v T)
    (motive_3 := fun Δ a b _ => DeqW μ env cval φ Δ a b)
    (motive_4 := fun Δ T as rest _ => TeleW μ env cval φ Δ T as rest)
    (motive_5 := fun Δ as bs _ => DeqLW μ env cval φ Δ as bs)
    wkRedRefl wkRedTrans wkRedAppFn wkRedBeta wkRedZeta
    (wkRedProjRed hcl) (wkRedStrLit hcl) (wkRedNatSucc hcl)
    (wkRedNatOp1 hcl) (wkRedNatOp2 hcl) (wkRedIota hcl)
    (wkRedRescueK hcl) (wkRedRescueEta hcl) (wkRedRescueUnit0 hcl)
    wkInfSort wkInfBvar (wkInfConst hcl) (wkInfLitNat hcl)
    (wkInfLitStr hcl) wkInfPi wkInfLam wkInfApp (wkInfProj hcl)
    wkInfLetE
    wkDeqRefl wkDeqSymm wkDeqTrans wkDeqOfRed wkDeqPiCong wkDeqLamCong
    wkDeqAppCong wkDeqIrrelProp (wkDeqIrrelUnit hcl)
    (wkDeqStructEta hcl) (wkDeqStructUnit hcl) (wkDeqPairEta hcl)
    wkDeqEta (wkDeqLitSuccApp hcl)
    wkTeleNil wkTeleCons wkDeqLNil wkDeqLCons
    h

/-- **M1 for `Infer`**. -/
theorem Infer.weakenN (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Γ : List VExpr} {v T : VExpr} (h : Infer μ env cval φ Γ v T) :
    InfW μ env cval φ Γ v T :=
  Infer.rec
    (motive_1 := fun Δ v w _ => RedW μ env cval φ Δ v w)
    (motive_2 := fun Δ v T _ => InfW μ env cval φ Δ v T)
    (motive_3 := fun Δ a b _ => DeqW μ env cval φ Δ a b)
    (motive_4 := fun Δ T as rest _ => TeleW μ env cval φ Δ T as rest)
    (motive_5 := fun Δ as bs _ => DeqLW μ env cval φ Δ as bs)
    wkRedRefl wkRedTrans wkRedAppFn wkRedBeta wkRedZeta
    (wkRedProjRed hcl) (wkRedStrLit hcl) (wkRedNatSucc hcl)
    (wkRedNatOp1 hcl) (wkRedNatOp2 hcl) (wkRedIota hcl)
    (wkRedRescueK hcl) (wkRedRescueEta hcl) (wkRedRescueUnit0 hcl)
    wkInfSort wkInfBvar (wkInfConst hcl) (wkInfLitNat hcl)
    (wkInfLitStr hcl) wkInfPi wkInfLam wkInfApp (wkInfProj hcl)
    wkInfLetE
    wkDeqRefl wkDeqSymm wkDeqTrans wkDeqOfRed wkDeqPiCong wkDeqLamCong
    wkDeqAppCong wkDeqIrrelProp (wkDeqIrrelUnit hcl)
    (wkDeqStructEta hcl) (wkDeqStructUnit hcl) (wkDeqPairEta hcl)
    wkDeqEta (wkDeqLitSuccApp hcl)
    wkTeleNil wkTeleCons wkDeqLNil wkDeqLCons
    h

/-- **M1 for `DefEq`**. -/
theorem DefEq.weakenN (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Γ : List VExpr} {a b : VExpr} (h : DefEq μ env cval φ Γ a b) :
    DeqW μ env cval φ Γ a b :=
  DefEq.rec
    (motive_1 := fun Δ v w _ => RedW μ env cval φ Δ v w)
    (motive_2 := fun Δ v T _ => InfW μ env cval φ Δ v T)
    (motive_3 := fun Δ a b _ => DeqW μ env cval φ Δ a b)
    (motive_4 := fun Δ T as rest _ => TeleW μ env cval φ Δ T as rest)
    (motive_5 := fun Δ as bs _ => DeqLW μ env cval φ Δ as bs)
    wkRedRefl wkRedTrans wkRedAppFn wkRedBeta wkRedZeta
    (wkRedProjRed hcl) (wkRedStrLit hcl) (wkRedNatSucc hcl)
    (wkRedNatOp1 hcl) (wkRedNatOp2 hcl) (wkRedIota hcl)
    (wkRedRescueK hcl) (wkRedRescueEta hcl) (wkRedRescueUnit0 hcl)
    wkInfSort wkInfBvar (wkInfConst hcl) (wkInfLitNat hcl)
    (wkInfLitStr hcl) wkInfPi wkInfLam wkInfApp (wkInfProj hcl)
    wkInfLetE
    wkDeqRefl wkDeqSymm wkDeqTrans wkDeqOfRed wkDeqPiCong wkDeqLamCong
    wkDeqAppCong wkDeqIrrelProp (wkDeqIrrelUnit hcl)
    (wkDeqStructEta hcl) (wkDeqStructUnit hcl) (wkDeqPairEta hcl)
    wkDeqEta (wkDeqLitSuccApp hcl)
    wkTeleNil wkTeleCons wkDeqLNil wkDeqLCons
    h

/-- **M1 for `Tele`**. -/
theorem Tele.weakenN (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Γ : List VExpr} {T : VExpr} {as : List VExpr} {rest : VExpr}
    (h : Tele μ env cval φ Γ T as rest) :
    TeleW μ env cval φ Γ T as rest :=
  Tele.rec
    (motive_1 := fun Δ v w _ => RedW μ env cval φ Δ v w)
    (motive_2 := fun Δ v T _ => InfW μ env cval φ Δ v T)
    (motive_3 := fun Δ a b _ => DeqW μ env cval φ Δ a b)
    (motive_4 := fun Δ T as rest _ => TeleW μ env cval φ Δ T as rest)
    (motive_5 := fun Δ as bs _ => DeqLW μ env cval φ Δ as bs)
    wkRedRefl wkRedTrans wkRedAppFn wkRedBeta wkRedZeta
    (wkRedProjRed hcl) (wkRedStrLit hcl) (wkRedNatSucc hcl)
    (wkRedNatOp1 hcl) (wkRedNatOp2 hcl) (wkRedIota hcl)
    (wkRedRescueK hcl) (wkRedRescueEta hcl) (wkRedRescueUnit0 hcl)
    wkInfSort wkInfBvar (wkInfConst hcl) (wkInfLitNat hcl)
    (wkInfLitStr hcl) wkInfPi wkInfLam wkInfApp (wkInfProj hcl)
    wkInfLetE
    wkDeqRefl wkDeqSymm wkDeqTrans wkDeqOfRed wkDeqPiCong wkDeqLamCong
    wkDeqAppCong wkDeqIrrelProp (wkDeqIrrelUnit hcl)
    (wkDeqStructEta hcl) (wkDeqStructUnit hcl) (wkDeqPairEta hcl)
    wkDeqEta (wkDeqLitSuccApp hcl)
    wkTeleNil wkTeleCons wkDeqLNil wkDeqLCons
    h

/-- **M1 for `DefEqL`**. -/
theorem DefEqL.weakenN (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Γ : List VExpr} {as bs : List VExpr}
    (h : DefEqL μ env cval φ Γ as bs) :
    DeqLW μ env cval φ Γ as bs :=
  DefEqL.rec
    (motive_1 := fun Δ v w _ => RedW μ env cval φ Δ v w)
    (motive_2 := fun Δ v T _ => InfW μ env cval φ Δ v T)
    (motive_3 := fun Δ a b _ => DeqW μ env cval φ Δ a b)
    (motive_4 := fun Δ T as rest _ => TeleW μ env cval φ Δ T as rest)
    (motive_5 := fun Δ as bs _ => DeqLW μ env cval φ Δ as bs)
    wkRedRefl wkRedTrans wkRedAppFn wkRedBeta wkRedZeta
    (wkRedProjRed hcl) (wkRedStrLit hcl) (wkRedNatSucc hcl)
    (wkRedNatOp1 hcl) (wkRedNatOp2 hcl) (wkRedIota hcl)
    (wkRedRescueK hcl) (wkRedRescueEta hcl) (wkRedRescueUnit0 hcl)
    wkInfSort wkInfBvar (wkInfConst hcl) (wkInfLitNat hcl)
    (wkInfLitStr hcl) wkInfPi wkInfLam wkInfApp (wkInfProj hcl)
    wkInfLetE
    wkDeqRefl wkDeqSymm wkDeqTrans wkDeqOfRed wkDeqPiCong wkDeqLamCong
    wkDeqAppCong wkDeqIrrelProp (wkDeqIrrelUnit hcl)
    (wkDeqStructEta hcl) (wkDeqStructUnit hcl) (wkDeqPairEta hcl)
    wkDeqEta (wkDeqLitSuccApp hcl)
    wkTeleNil wkTeleCons wkDeqLNil wkDeqLCons
    h

/-! ### Head-weakening corollaries (the forms `CtxOkR` consumes) -/

/-- Weakening a definitional equality by a fresh innermost binder
(the transpose of `Deq.weakenHead`, `Setlec/TTVerify/Claims.lean`). -/
theorem DefEq.weakenHead (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Γ : List VExpr} {a b : VExpr} (B : VExpr)
    (h : DefEq μ env cval φ Γ a b) :
    DefEq μ env cval φ (B :: Γ) a.lift b.lift :=
  h.weakenN hcl (.zero [B] rfl)

/-- Weakening an inference by a fresh innermost binder. -/
theorem Infer.weakenHead (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Γ : List VExpr} {v T : VExpr} (B : VExpr)
    (h : Infer μ env cval φ Γ v T) :
    Infer μ env cval φ (B :: Γ) v.lift T.lift :=
  h.weakenN hcl (.zero [B] rfl)

/-- Weakening a reduction by a fresh innermost binder. -/
theorem Red.weakenHead (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Γ : List VExpr} {v w : VExpr} (B : VExpr)
    (h : Red μ env cval φ Γ v w) :
    Red μ env cval φ (B :: Γ) v.lift w.lift :=
  h.weakenN hcl (.zero [B] rfl)

end M1

end Setlec.SetR
