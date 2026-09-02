import Setlec.SetR.Annot.SortCoh.SubstSim

/-!
# The alignment engine (E4, R1-ratified): the map

The core-dichotomy statement per the ratified R1: aligning a
gate-free trace's endpoint against the ACTUAL (gated, deterministic)
run's result — `aligned ∨ DeadCore ∨ seam`, the seams carried as
evidence packs with progress markers (the `NatSplitOut` precedent)
for routed consumers with more facts.  Divergence taxonomy sealed in
DESIGN ("STOP-FINDING at E4"): gate refusals are dead-shaped and
refutable; K fires always agree; the residual seams are the iota
fire divergence (the eta field segment) and the nat-arg grind.

Budget note (the both-fuel-bounds axiom): the aligned disjuncts'
runs feed det-reads and universally-budgeted walk premises, never
measure slots — plain existentials, per the recorded justification.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf whnfCore
  isDefEqCore unfoldDefinition)

section Discharge
variable {μ : CheckMode} {env : Env}

/-- **Dead head-normal shapes** — the gate-refusal outputs.  Shape
only: as an app/proj head each kills the outer (`iotaRec` shape/
length refusals), and at a sort-demanding top the consumer's own
run plus these shapes force a non-sort exit (`loop_dead_exit` for
the non-const heads; `unfoldDefinition_none_of_recInfo` plus the
nat-guard disjointness for the recursor spines). -/
def DeadCore (env : Env) (W : Expr) : Prop :=
  (∃ n ty b m, W.getAppFn = Expr.lam n ty b m ∧
    W.getAppArgs ≠ []) ∨
  (∃ sn i e₀, W.getAppFn = Expr.proj sn i e₀) ∨
  (∃ c us cv mI rP rules, W.getAppFn = Expr.const c us ∧
    env.find? c = some (.recInfo cv mI rP rules) ∧
    mI + 1 ≤ W.getAppArgs.length) ∨
  (∃ lv, W.getAppFn = Expr.lit lv ∧ W.getAppArgs ≠ [])

/-- **The literal residue / pending-literal row**: the actual run
parked at a literal while the trace continues through its
conversion (the conversions live in `litMajorToCtor`/
`projLitToCtor`, AFTER the actual's whnf) — the consumer re-runs
its own conversion (same literal, determinism) and continues along
the residue. -/
def LitResidue (μ : CheckMode) (env : Env) (d G : Nat)
    (f' W : Expr) : Prop :=
  (∃ n, W = Expr.lit (.natVal n) ∧
    RawReach μ env d G (Setlec.litToCtorIfNat env W) f') ∨
  (∃ s t g, W = Expr.lit (.strVal s) ∧
    Setlec.strLitSupported env = true ∧ g ≤ G ∧
    whnf μ env g d (Setlec.strLitToConstructor s) = .ok t ∧
    RawReach μ env d G t f')

/-- **The pending-delta row** (core-tier only): the actual core run
parked at an unfoldable node the trace steps through — the loop
tier consumes it (its own delta is the same unfolding, by the
purity of `unfoldDefinition`). -/
def PendingDelta (μ : CheckMode) (env : Env) (d G : Nat)
    (f' W : Expr) : Prop :=
  ∃ u, Setlec.unfoldDefinition env W = some u ∧
    RawReach μ env d G u f'

/-- **The pending-nat row** (core-tier only): the actual core run
parked at a nat-op node the trace fires through — the loop tier
compares its own `reduceNat` outcome against the claimed reduct
(equal → recurse; else the nat seam). -/
def PendingNat (μ : CheckMode) (env : Env) (d G : Nat)
    (f' W : Expr) : Prop :=
  ∃ (res : Expr) (c : Name) (n₁ n₂ : Nat),
    W.getAppFn = Expr.const c [] ∧
    (∀ cv mI rP rules,
      env.find? c ≠ some (.recInfo cv mI rP rules)) ∧
    (Setlec.natOpResult c n₁ n₂ = some res ∨
      res = Expr.lit (.natVal (n₁ + 1))) ∧
    RawReach μ env d G res f'

/-- **The fire seam** (position-free evidence, defensively
general): the actual's `iotaRec` outcome at a full recursor node
diverged from the claimed fire — refusal or a different result; the
disequality is the progress marker.  The claimed major's trace is
carried whole for the dedicated analysis (the eta field segment
lives here). -/
def FireSeam (μ : CheckMode) (env : Env) (d G : Nat) : Prop :=
  ∃ (S M e''c : Expr) (c : Name) (us : List Level)
    (cv : Setlec.ConstantVal) (mI rP : Nat)
    (rules : List Setlec.RecRule) (g : Nat) (o : Option Expr),
    S.getAppFn = Expr.const c us ∧
    env.find? c = some (.recInfo cv mI rP rules) ∧
    S.getAppArgs.length = mI + 1 ∧
    RawReach μ env d G (S.getAppArgs.getD mI (.bvar 0)) M ∧
    Setlec.iotaRec μ (Setlec.pureFns μ env g) env d S = .ok o ∧
    o ≠ some e''c

/-- **The proj seam** (position-free): the actual's projection-tier
processing diverged from the claimed scrutinee continuation. -/
def ProjSeam (μ : CheckMode) (env : Env) (d G : Nat) : Prop :=
  (∃ (_sn : Name) (_i : Nat) (pe w pe' : Expr) (g : Nat),
    whnf μ env g d pe = .ok w ∧
    RawReach μ env d G w pe' ∧
    pe' ≠ w) ∨
  (∃ (_sn : Name) (_i : Nat) (S e₂ : Expr) (gn : Nat),
    Setlec.reduceNat (Setlec.pureFns μ env gn) env d S
      = .ok (some e₂))

/-- **The conversion-residue seam**: the two sides re-converged at
a literal's conversion but the claimed trace continues past the
converted form (`≠` markers; both literal species). -/
def ConvSeam (μ : CheckMode) (env : Env) (d G : Nat) : Prop :=
  (∃ (n : Nat) (f'' : Expr),
    RawReach μ env d G
      (Setlec.litToCtorIfNat env (.lit (.natVal n))) f'' ∧
    f'' ≠ Setlec.litToCtorIfNat env (.lit (.natVal n))) ∨
  (∃ (s : String) (t f'' : Expr) (g : Nat),
    Setlec.strLitSupported env = true ∧
    whnf μ env g d (Setlec.strLitToConstructor s) = .ok t ∧
    RawReach μ env d G t f'' ∧
    f'' ≠ t)

/-- **The nat seam**: a claimed nat fire against a declined or
divergent actual `reduceNat` — or an actual fire against a claimed
delta (`whnfStep` tries nat first, so an image-side unlocked
literal can preempt a claimed unfolding).  The mismatch is the
progress marker in both rows. -/
def NatSeam (μ : CheckMode) (env : Env) (d _G : Nat) : Prop :=
  (∃ (S res : Expr) (c : Name) (g : Nat) (o : Option Expr)
     (n₁ n₂ : Nat),
    S.getAppFn = Expr.const c [] ∧
    (Setlec.natOpResult c n₁ n₂ = some res ∨
      res = Expr.lit (.natVal (n₁ + 1))) ∧
    Setlec.reduceNat (Setlec.pureFns μ env g) env d S = .ok o ∧
    o ≠ some res) ∨
  (∃ (S u e₂ : Expr) (g : Nat),
    Setlec.reduceNat (Setlec.pureFns μ env g) env d S
      = .ok (some e₂) ∧
    Setlec.unfoldDefinition env S = some u) ∨
  (∃ (S x res : Expr) (c : Name) (n₁ n₂ : Nat),
    S.getAppFn = Expr.const c [] ∧
    (Setlec.natOpResult c n₁ n₂ = some res ∨
      res = Expr.lit (.natVal (n₁ + 1))) ∧
    ((Expr.app S x).getAppArgs.length ≥ 2 ∨ S.getAppArgs = []))

/-- Projection-table constructors are stored constructors — an
install-tier fact (supplier joins the install-facts docket with
`StoredWF`); the aligner uses it to refute a projection fire on a
recursor-headed scrutinee. -/
def ProjCtorWF (env : Env) : Prop :=
  ∀ {sn : Name} {i : Nat} {entry : Setlec.ProjEntry},
    env.findProj? sn i = some entry → entry.native = true →
    ∃ cvj nP nF,
      env.find? entry.ctor = some (.ctorInfo cvj nP nF)

/-- The core-tier alignment conclusion at input knot fuel `g` (the
aligned run is fuel-bounded — the both-fuel-bounds axiom's fourth
instance; the chained assemblies stay within the input's knot). -/
def CoreAlignOut (μ : CheckMode) (env : Env) (d G g : Nat)
    (f' W : Expr) : Prop :=
  (∃ g₂, g₂ ≤ g ∧ whnfCore μ env g₂ d f' = .ok W) ∨
  DeadCore env W ∨
  PendingDelta μ env d G f' W ∨
  PendingNat μ env d G f' W ∨
  LitResidue μ env d G f' W ∨
  FireSeam μ env d G ∨
  ProjSeam μ env d G ∨
  ConvSeam μ env d G ∨
  NatSeam μ env d G

/-- The loop-tier alignment conclusion at input fuels `(g, l)` —
the loop tier has consumed the pendings (its own delta/nat steps),
so only the literal parking survives as a residue. -/
def LoopAlignOut (μ : CheckMode) (env : Env) (d G g l : Nat)
    (f' W : Expr) : Prop :=
  (∃ g₂ l₂, g₂ ≤ g ∧ l₂ ≤ l ∧
    Setlec.whnfLoop (Setlec.pureFns μ env g₂) env d l₂ f'
      = .ok W) ∨
  DeadCore env W ∨
  LitResidue μ env d G f' W ∨
  FireSeam μ env d G ∨
  ProjSeam μ env d G ∨
  ConvSeam μ env d G ∨
  NatSeam μ env d G

/-- **The core alignment claim at one knot fuel** — the discharge
recurses on the knot (scrutinee whnfs and internal continuations
run one fuel down, the kernel's own discipline). -/
def CoreAlignAt (μ : CheckMode) (env : Env) (g : Nat) : Prop :=
  ∀ {d G : Nat} {f f' W : Expr},
    RawReach μ env d G f f' →
    whnfCore μ env g d f = .ok W →
    CoreAlignOut μ env d G g f' W

/-- **The loop alignment claim at one knot fuel** (any budget). -/
def LoopAlignAt (μ : CheckMode) (env : Env) (g : Nat) : Prop :=
  ∀ {d G l : Nat} {f f' W : Expr},
    RawReach μ env d G f f' →
    Setlec.whnfLoop (Setlec.pureFns μ env g) env d l f = .ok W →
    LoopAlignOut μ env d G g l f' W

/-! ### The discharge suppliers -/

/-- `whnfCore` is the identity on literals (positive fuel). -/
theorem whnfCore_lit_id {g d : Nat} {v : Setlec.Literal} :
    whnfCore μ env (g + 1) d (.lit v) = .ok (.lit v) := by
  rw [Setlec.whnfCore_succ]
  rfl

/-- The letE clause's run extractor. -/
theorem whnfCore_letE_extract {g d : Nat}
    {nn : Name} {tt vv bb W : Expr}
    (h : whnfCore μ env (g + 1) d (.letE nn tt vv bb) = .ok W) :
    whnfCore μ env g d (bb.instantiate1 vv) = .ok W := by
  rw [Setlec.whnfCore_succ] at h
  simpa only [Setlec.whnfCoreBody, Setlec.whnfCore_def] using h

/-- `iotaRec` declines a wrong-length recursor spine. -/
theorem iotaRec_none_of_arglen {r : Setlec.CoreFns Setlec.CheckM}
    {d : Nat} {e : Expr} {c : Name} {us : List Level}
    {cv : Setlec.ConstantVal} {mI rP : Nat}
    {rules : List Setlec.RecRule}
    (hfn : e.getAppFn = .const c us)
    (hc : env.find? c = some (.recInfo cv mI rP rules))
    (hlen : e.getAppArgs.length ≠ mI + 1) :
    Setlec.iotaRec μ r env d e = .ok none := by
  unfold Setlec.iotaRec
  rw [hfn]
  simp only [hc]
  rw [if_neg (fun hc => hlen hc.1)]
  rfl

/-- Dead shapes absorb spine extension. -/
theorem DeadCore.app {W x : Expr} (h : DeadCore env W) :
    DeadCore env (.app W x) := by
  have hfn : (Expr.app W x).getAppFn = W.getAppFn := rfl
  have hargs : (Expr.app W x).getAppArgs
      = W.getAppArgs ++ [x] := rfl
  rcases h with ⟨n, ty, b, m, h1, h2⟩ | ⟨sn, i, e₀, h1⟩ |
    ⟨c, us, cv, mI, rP, rules, h1, h2, h3⟩ | ⟨lv, h1, h2⟩
  · exact Or.inl ⟨n, ty, b, m, by rw [hfn]; exact h1, by
      rw [hargs]; simp⟩
  · exact Or.inr (Or.inl ⟨sn, i, e₀, by rw [hfn]; exact h1⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨c, us, cv, mI, rP, rules,
      by rw [hfn]; exact h1, h2, ?_⟩))
    rw [hargs, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  · exact Or.inr (Or.inr (Or.inr ⟨lv, by rw [hfn]; exact h1, by
      rw [hargs]; simp⟩))

/-- Dead shapes are never λ-nodes. -/
theorem DeadCore.not_lam {W : Expr} (h : DeadCore env W)
    {n : Name} {ty b : Expr} {m : Setlec.BinderMeta} :
    W ≠ .lam n ty b m := by
  rintro rfl
  rcases h with ⟨n', ty', b', m', h1, h2⟩ | ⟨sn, i, e₀, h1⟩ |
    ⟨c, us, cv, mI, rP, rules, h1, h2, h3⟩ | ⟨lv, h1, h2⟩
  · exact h2 rfl
  · exact nomatch h1
  · exact nomatch h1
  · exact nomatch h1

/-- `iotaRec` declines every dead-shaped subject extended by an
argument (the head is a λ/proj/literal, or the recursor spine is
already at or past full length). -/
theorem iotaRec_none_of_dead {r : Setlec.CoreFns Setlec.CheckM}
    {d : Nat} {W x : Expr} (h : DeadCore env W) :
    Setlec.iotaRec μ r env d (.app W x) = .ok none := by
  have hfn : (Expr.app W x).getAppFn = W.getAppFn := rfl
  rcases h with ⟨n, ty, b, m, h1, h2⟩ | ⟨sn, i, e₀, h1⟩ |
    ⟨c, us, cv, mI, rP, rules, h1, h2, h3⟩ | ⟨lv, h1, h2⟩
  · refine iotaRec_none_of_fn_not_const (μ := μ) ?_
    rw [hfn, h1]
    exact fun p q h => nomatch h
  · refine iotaRec_none_of_fn_not_const (μ := μ) ?_
    rw [hfn, h1]
    exact fun p q h => nomatch h
  · refine iotaRec_none_of_arglen (by rw [hfn]; exact h1) h2 ?_
    rw [show (Expr.app W x).getAppArgs = W.getAppArgs ++ [x]
      from rfl, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  · refine iotaRec_none_of_fn_not_const (μ := μ) ?_
    rw [hfn, h1]
    exact fun p q h => nomatch h

/-- `Nat.succ` stored as a recursor refutes the literal guard. -/
theorem natLitSupported_succ_not_rec
    (hs : Setlec.natLitSupported env = true)
    {cv : Setlec.ConstantVal} {mI rP : Nat}
    {rules : List Setlec.RecRule}
    (hf : env.find? Setlec.natSuccName
      = some (.recInfo cv mI rP rules)) : False := by
  unfold Setlec.natLitSupported at hs
  rw [hf] at hs
  simp [Setlec.natSuccOk] at hs

/-- An op stored as a recursor refutes its own guard (the op is its
own dependency). -/
theorem natOpGuard_not_rec {c : Name}
    (hc : c = Setlec.natPredName ∨ c = Setlec.natAddName ∨
      c = Setlec.natSubName ∨ c = Setlec.natMulName ∨
      c = Setlec.natPowName ∨ c = Setlec.natBeqName ∨
      c = Setlec.natBleName ∨ c = Setlec.natDivName ∨
      c = Setlec.natModName ∨ c = Setlec.natGcdName ∨
      c = Setlec.natLandName ∨ c = Setlec.natLorName ∨
      c = Setlec.natXorName ∨ c = Setlec.natShiftLeftName ∨
      c = Setlec.natShiftRightName ∨ c = Setlec.natLog2Name)
    (hg : Setlec.natOpGuard env c = true)
    {cv : Setlec.ConstantVal} {mI rP : Nat}
    {rules : List Setlec.RecRule}
    (hf : env.find? c = some (.recInfo cv mI rP rules)) :
    False := by
  have hmem : c ∈ Setlec.natOpDeps c := by
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  have hg' : (Setlec.natOpDeps c).all (fun n =>
      match env.find? n with
      | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
      | _ => false) = true := by
    unfold Setlec.natOpGuard at hg
    simp only [Bool.and_eq_true] at hg
    exact hg.1.2
  rw [List.all_eq_true] at hg'
  have hthis := hg' c hmem
  rw [hf] at hthis
  exact nomatch hthis

/-- Scrutinee congruence for the proj clause at one fuel: the
clause's tail is a function of the scrutinee's whnf. -/
theorem whnfCore_proj_congr {g d : Nat} {pe pe' e₂ W : Expr}
    {sn : Name} {i : Nat}
    (h₁ : whnf μ env g d pe = .ok e₂)
    (h₂ : whnf μ env g d pe' = .ok e₂)
    (hrun : whnfCore μ env (g + 1) d (.proj sn i pe) = .ok W) :
    whnfCore μ env (g + 1) d (.proj sn i pe') = .ok W := by
  rw [Setlec.whnfCore_succ] at hrun ⊢
  unfold Setlec.whnfCoreBody at hrun ⊢
  simp only [Bind.bind, Except.bind] at hrun ⊢
  rw [Setlec.whnf_def] at hrun ⊢
  rw [h₁] at hrun
  rw [h₂]
  exact hrun

/-- Unfolding inversion: the head constant and its stored value
kind. -/
theorem unfoldDefinition_inv {e u : Expr}
    (h : unfoldDefinition env e = some u) :
    ∃ c us, e.getAppFn = Expr.const c us ∧
      ((∃ cv value hint,
          env.find? c = some (.defnInfo cv value hint)) ∨
       (∃ cv value, env.find? c = some (.thmInfo cv value))) := by
  unfold Setlec.unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo cv value) =>
    intro h
    exact ⟨n, us, rfl, Or.inr ⟨cv, value, hf⟩⟩
  | some (.defnInfo cv value hint) =>
    intro h
    exact ⟨n, us, rfl, Or.inl ⟨cv, value, hint, hf⟩⟩

/-- A const-headed run whose head is not a recursor is the
identity (the spine inversion's fired disjunct is refuted). -/
theorem whnfCore_nonrec_id (hm : KnotFuelMono μ env)
    {g d : Nat} {f W : Expr} {c : Name} {us : List Level}
    (hfn : f.getAppFn = Expr.const c us)
    (hnr : ∀ cv mI rP rules,
      env.find? c ≠ some (.recInfo cv mI rP rules))
    (hrun : whnfCore μ env g d f = .ok W) : W = f := by
  have hfeq : Setlec.Expr.mkAppN (.const c us) f.getAppArgs
      = f := by
    have he := Setlec.Expr.mkAppN_getApp f
    rw [hfn] at he
    exact he
  have hspine := whnfCore_rec_spine_inv (μ := μ) hm
    (as := f.getAppArgs) (n := c) (us := us)
    (by rw [hfeq]; exact hrun)
  rcases hspine with heq | ⟨pre, post, g₀, e'', h', hsplit, -, hio,
    -, -⟩
  · rw [heq, hfeq]
  · obtain ⟨c', us', cv, mI, rP, rules, maj₀, maj₁, maj, cj, usj,
      cvj, cnP, cnF, rr, cb, cbody, resid, cr, usr, hfn', hfc,
      -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -⟩ :=
      Setlec.iotaRec_inv (mode := μ)
        (by rw [Setlec.iotaRec_fold] at hio; exact hio)
    rw [Setlec.Expr.getAppFn_mkAppN] at hfn'
    have hce : Expr.const c us = Expr.const c' us' := hfn'
    injection hce with h1 h2
    subst h1
    exact absurd hfc (hnr cv mI rP rules)

/-- Unfolding commutes with spine extension. -/
theorem unfoldDefinition_app {W x u : Expr}
    (h : unfoldDefinition env W = some u) :
    unfoldDefinition env (.app W x) = some (.app u x) := by
  obtain ⟨c, us, hfn, hkind⟩ := unfoldDefinition_inv h
  unfold Setlec.unfoldDefinition at h ⊢
  rw [show (Expr.app W x).getAppFn = W.getAppFn from rfl, hfn]
  rw [hfn] at h
  rcases hkind with ⟨cv, v, hint, hf⟩ | ⟨cv, v, hf⟩ <;>
    simp only [hf] at h ⊢ <;>
    revert h <;>
    split <;>
    intro h
  case _ =>
    obtain rfl := Option.some.inj h
    rw [show (Expr.app W x).getAppArgs = W.getAppArgs ++ [x]
      from rfl, mkAppN_append]
    rfl
  case _ => exact nomatch h
  case _ =>
    obtain rfl := Option.some.inj h
    rw [show (Expr.app W x).getAppArgs = W.getAppArgs ++ [x]
      from rfl, mkAppN_append]
    rfl
  case _ => exact nomatch h

/-- A fired `iotaRec` pins a recursor at the subject's head. -/
theorem iotaRec_fired_head {g₀ d : Nat} {S e'' : Expr}
    (hio : Setlec.iotaRec μ (Setlec.pureFns μ env g₀) env d S
      = .ok (some e'')) :
    ∃ c us cv mI rP rules, S.getAppFn = Expr.const c us ∧
      env.find? c = some (.recInfo cv mI rP rules) := by
  obtain ⟨c, us, cv, mI, rP, rules, maj₀, maj₁, maj, cj, usj,
    cvj, cnP, cnF, rr, cb, cbody, resid, cr, usr, hfn, hfc,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -⟩ :=
    Setlec.iotaRec_inv (mode := μ)
      (by rw [Setlec.iotaRec_fold] at hio; exact hio)
  exact ⟨c, us, cv, mI, rP, rules, hfn, hfc⟩

/-- The full reduction loop is the identity on literals (two knot
levels: one for the loop, one for its core step). -/
theorem whnf_lit_id {g d : Nat} {v : Setlec.Literal} :
    whnf μ env (g + 2) d (.lit v) = .ok (.lit v) := by
  rw [Setlec.whnf_succ]
  show Setlec.whnfLoop (Setlec.pureFns μ env (g + 1)) env d
    Setlec.whnfLoopFuel (.lit v) = .ok (.lit v)
  obtain ⟨n, hn⟩ := Setlec.whnfLoopFuel_succ
  rw [hn, whnfLoop_succ]
  exact whnfStep_assemble_stuck
    (by rw [Setlec.whnfCore_def]; exact whnfCore_lit_id) rfl rfl

set_option maxHeartbeats 3200000 in
/-- **The core alignment discharge at one knot fuel** — trace
induction; strictly-lower tiers through the fuel IHs. -/
theorem coreAlign_step {env : Env} (_henv : EnvWF env)
    (hm : KnotFuelMono μ env) (hPC : ProjCtorWF env) {g : Nat}
    (ihC : ∀ g', g' < g → CoreAlignAt μ env g')
    (ihL : ∀ g', g' < g → LoopAlignAt μ env g') :
    CoreAlignAt μ env g := by
  intro d G f f' W h
  induction h generalizing W with
  | refl e =>
    intro hrun
    exact Or.inl ⟨g, Nat.le_refl g, hrun⟩
  | beta n ty b x m rest ih =>
    intro hrun
    cases g with
    | zero => exact nomatch hrun
    | succ g' =>
    obtain ⟨f_act, hhead, hcase⟩ := whnfCore_app_decompose hrun
    have hfl : f_act = Expr.lam n ty b m := by
      cases g' with
      | zero => exact nomatch hhead
      | succ g'' =>
        rw [Setlec.whnfCore_succ] at hhead
        simp only [Setlec.whnfCoreBody, pure, Except.pure,
          Except.ok.injEq] at hhead
        exact hhead.symm
    subst hfl
    rcases hcase with ⟨n', ty', b', m', ta, heq, -, -, hcont⟩ |
      ⟨n', ty', b', m', ta, heq, -, -, rfl⟩ | ⟨hnl, -⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ :
        n' = n ∧ ty' = ty ∧ b' = b ∧ m' = m := by
        injection heq with h1 h2 h3 h4
        exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩
      exact ih (hm.2.2.1 (Nat.le_succ g') hcont)
    · exact Or.inr (Or.inl (Or.inl ⟨n, ty, b, m, rfl,
        by simp [Setlec.Expr.getAppArgs]⟩))
    · exact absurd rfl (hnl n ty b m)
  | zeta n ty v b rest ih =>
    intro hrun
    cases g with
    | zero => exact nomatch hrun
    | succ g' =>
      exact ih (hm.2.2.1 (Nat.le_succ g')
        (whnfCore_letE_extract hrun))
  | litNat e rest ih =>
    intro hrun
    rcases litToCtorIfNat_cases env e with hid | ⟨n, rfl, hconv⟩
    · rw [show Setlec.litToCtorIfNat env e = e from hid] at ih
      exact ih hrun
    · cases g with
      | zero => exact nomatch hrun
      | succ g' =>
        rw [whnfCore_lit_id] at hrun
        obtain rfl := Except.ok.inj hrun
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
          ⟨n, rfl, rest⟩)))))
  | litStr s g₀ hg hs hr rest ih =>
    intro hrun
    cases g with
    | zero => exact nomatch hrun
    | succ g' =>
      rw [whnfCore_lit_id] at hrun
      obtain rfl := Except.ok.inj hrun
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr
        ⟨s, _, g₀, rfl, hs, hg, hr, rest⟩)))))
  | delta hu rest ih =>
    intro hrun
    obtain ⟨c, us, hfn, hkind⟩ := unfoldDefinition_inv hu
    have hW := whnfCore_nonrec_id hm hfn
      (fun cv mI rP rules hr => by
        rcases hkind with ⟨cv', v', h', hf⟩ | ⟨cv', v', hf⟩ <;>
          (rw [hf] at hr; exact nomatch hr)) hrun
    subst hW
    exact Or.inr (Or.inr (Or.inl ⟨_, hu, rest⟩))
  | natSucc x n hs hx hnl rest ihx ihr =>
    intro hrun
    have hW := whnfCore_nonrec_id hm
      (show (Expr.app (.const Setlec.natSuccName []) x).getAppFn
        = Expr.const Setlec.natSuccName [] from rfl)
      (fun cv mI rP rules hr => absurd hr (fun hr =>
        natLitSupported_succ_not_rec hs hr)) hrun
    subst hW
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨.lit (.natVal (n + 1)),
      Setlec.natSuccName, n, 0, rfl,
      fun cv mI rP rules hr => natLitSupported_succ_not_rec hs hr,
      Or.inr rfl, rest⟩)))
  | natU1 c x n hc hg hx hnl hres rest ihx ihr =>
    intro hrun
    have hc16 : c = Setlec.natPredName ∨ c = Setlec.natAddName ∨
        c = Setlec.natSubName ∨ c = Setlec.natMulName ∨
        c = Setlec.natPowName ∨ c = Setlec.natBeqName ∨
        c = Setlec.natBleName ∨ c = Setlec.natDivName ∨
        c = Setlec.natModName ∨ c = Setlec.natGcdName ∨
        c = Setlec.natLandName ∨ c = Setlec.natLorName ∨
        c = Setlec.natXorName ∨ c = Setlec.natShiftLeftName ∨
        c = Setlec.natShiftRightName ∨ c = Setlec.natLog2Name := by
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))))))))))
    have hW := whnfCore_nonrec_id hm
      (show (Expr.app (.const c []) x).getAppFn
        = Expr.const c [] from rfl)
      (fun cv mI rP rules hr => absurd hr (fun hr =>
        natOpGuard_not_rec hc16 hg hr)) hrun
    subst hW
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, c, n, 0, rfl,
      fun cv mI rP rules hr => natOpGuard_not_rec hc16 hg hr,
      Or.inl hres, rest⟩)))
  | natB c x y n₁ n₂ hc hg hx hy hnx hny hres rest ihx ihy ihr =>
    intro hrun
    have hc16 : c = Setlec.natPredName ∨ c = Setlec.natAddName ∨
        c = Setlec.natSubName ∨ c = Setlec.natMulName ∨
        c = Setlec.natPowName ∨ c = Setlec.natBeqName ∨
        c = Setlec.natBleName ∨ c = Setlec.natDivName ∨
        c = Setlec.natModName ∨ c = Setlec.natGcdName ∨
        c = Setlec.natLandName ∨ c = Setlec.natLorName ∨
        c = Setlec.natXorName ∨ c = Setlec.natShiftLeftName ∨
        c = Setlec.natShiftRightName ∨ c = Setlec.natLog2Name := by
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))
    have hW := whnfCore_nonrec_id hm
      (show (Expr.app (.app (.const c []) x) y).getAppFn
        = Expr.const c [] from rfl)
      (fun cv mI rP rules hr => absurd hr (fun hr =>
        natOpGuard_not_rec hc16 hg hr)) hrun
    subst hW
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, c, n₁, n₂, rfl,
      fun cv mI rP rules hr => natOpGuard_not_rec hc16 hg hr,
      Or.inl hres, rest⟩)))
  | appL x h rest ihh ihr =>
    intro hrun
    cases g with
    | zero => exact nomatch hrun
    | succ g' =>
    obtain ⟨f_act, hhead, hcase⟩ := whnfCore_app_decompose hrun
    rcases ihC g' (Nat.lt_succ_self g') h hhead with
      ⟨g₂, hg₂, hrun₂⟩ | hdead | ⟨u, hu, hrest_u⟩ |
      ⟨res, c, n₁, n₂, hhd, hnr, hprov, hrest_n⟩ |
      hlit | hfs | hps | hcs | hns
    · have hasm := whnfCore_app_assemble hm (y := x) hrun₂ hcase
      exact ihr (hm.2.2.1 (by omega : max g₂ g' + 1 ≤ g' + 1)
        hasm)
    · rcases hcase with ⟨n, ty, b, m, ta, heq, -, -, -⟩ |
        ⟨n, ty, b, m, ta, heq, -, -, rfl⟩ | ⟨hnl, hio⟩
      · exact absurd heq (DeadCore.not_lam hdead)
      · exact absurd heq (DeadCore.not_lam hdead)
      · rcases hio with ⟨e'', hio, -⟩ | ⟨hio, rfl⟩
        · rw [iotaRec_none_of_dead hdead] at hio
          exact nomatch hio
        · exact Or.inr (Or.inl (DeadCore.app hdead))
    · obtain ⟨c, us, hfnc, hkind⟩ := unfoldDefinition_inv hu
      rcases hcase with ⟨n, ty, b, m, ta, heq, -, -, -⟩ |
        ⟨n, ty, b, m, ta, heq, -, -, rfl⟩ | ⟨hnl, hio⟩
      · rw [heq] at hfnc
        simp only [Setlec.Expr.getAppFn] at hfnc
        exact nomatch hfnc
      · rw [heq] at hfnc
        simp only [Setlec.Expr.getAppFn] at hfnc
        exact nomatch hfnc
      · rcases hio with ⟨e'', hio, -⟩ | ⟨hio, rfl⟩
        · obtain ⟨c', us', cv, mI, rP, rules, hfn', hfc'⟩ :=
            iotaRec_fired_head hio
          rw [show (Expr.app f_act x).getAppFn = f_act.getAppFn
            from rfl, hfnc] at hfn'
          injection hfn' with h1 h2
          subst h1
          rcases hkind with ⟨cv', v', h', hf⟩ | ⟨cv', v', hf⟩ <;>
            (rw [hf] at hfc'; exact nomatch hfc')
        · exact Or.inr (Or.inr (Or.inl ⟨.app u x,
            unfoldDefinition_app hu,
            RawReach.appL x hrest_u rest⟩))
    · rcases hcase with ⟨n, ty, b, m, ta, heq, -, -, -⟩ |
        ⟨n, ty, b, m, ta, heq, -, -, rfl⟩ | ⟨hnl, hio⟩
      · rw [heq] at hhd
        simp only [Setlec.Expr.getAppFn] at hhd
        exact nomatch hhd
      · rw [heq] at hhd
        simp only [Setlec.Expr.getAppFn] at hhd
        exact nomatch hhd
      · rcases hio with ⟨e'', hio, -⟩ | ⟨hio, rfl⟩
        · obtain ⟨c', us', cv, mI, rP, rules, hfn', hfc'⟩ :=
            iotaRec_fired_head hio
          rw [show (Expr.app f_act x).getAppFn = f_act.getAppFn
            from rfl, hhd] at hfn'
          injection hfn' with h1 h2
          subst h1
          exact absurd hfc' (hnr cv mI rP rules)
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr ⟨f_act, x, res, c,
              n₁, n₂, hhd, hprov, ?_⟩)))))))))
          cases hargs : f_act.getAppArgs with
          | nil => exact Or.inr rfl
          | cons z zs =>
            refine Or.inl ?_
            rw [show (Expr.app f_act x).getAppArgs
              = f_act.getAppArgs ++ [x] from rfl, hargs]
            simp
    · rcases hcase with ⟨n, ty, b, m, ta, heq, -, -, -⟩ |
        ⟨n, ty, b, m, ta, heq, -, -, rfl⟩ | ⟨hnl, hio⟩
      · rcases hlit with ⟨n₀, rfl, -⟩ | ⟨s₀, t₀, g₀, rfl, -, -, -, -⟩ <;>
          exact nomatch heq
      · rcases hlit with ⟨n₀, rfl, -⟩ | ⟨s₀, t₀, g₀, rfl, -, -, -, -⟩ <;>
          exact nomatch heq
      · rcases hio with ⟨e'', hio, -⟩ | ⟨hio, rfl⟩
        · rcases hlit with ⟨n₀, rfl, -⟩ | ⟨s₀, t₀, g₀, rfl, -, -, -, -⟩ <;>
            (rw [iotaRec_none_of_fn_not_const (μ := μ)
              (by intro p q hh
                  simp [Setlec.Expr.getAppFn] at hh)] at hio
             exact nomatch hio)
        · rcases hlit with ⟨n₀, rfl, -⟩ | ⟨s₀, t₀, g₀, rfl, -, -, -, -⟩ <;>
            exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr
              ⟨_, rfl, by simp [Setlec.Expr.getAppArgs]⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hfs)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hps))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl hcs)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr hns)))))))
  | @projC sn i pe pe' wT h rest ihh ihr =>
    intro hrun
    cases g with
    | zero => exact nomatch hrun
    | succ g' =>
    obtain ⟨e₂w, e₃, hscrut, hlitp, hbranch⟩ :=
      Setlec.whnf_proj_inv (mode := μ) hrun
    cases g' with
    | zero => exact nomatch hscrut
    | succ g'' =>
    have hloopS : Setlec.whnfLoop (Setlec.pureFns μ env g'') env d
        Setlec.whnfLoopFuel pe = .ok e₂w := by
      have hs' := hscrut
      rw [Setlec.whnf_succ] at hs'
      exact hs'
    rcases ihL g'' (by omega) h hloopS with
      ⟨g₂, l₂, hg₂, hl₂, run₂⟩ | hdead | hres | hfs | hps | hcs |
      hns
    · have hw' : whnf μ env (g'' + 1) d pe' = .ok e₂w := by
        rw [Setlec.whnf_succ]
        exact whnfLoop_budget_mono hl₂ (whnfLoop_r_mono hm hg₂ run₂)
      exact ihr (whnfCore_proj_congr hscrut hw' hrun)
    · have he₃ : e₃ = e₂w := by
        rcases Setlec.projLitToCtorP_inv (mode := μ) hlitp with
          heq | ⟨s₀, hlit, -, -⟩
        · exact heq
        · exfalso
          rcases hdead with ⟨n, ty, b, m, h1, h2⟩ |
            ⟨sn', i', e₀, h1⟩ |
            ⟨c, us', cv, mI, rP, rules, h1, h2, h3⟩ | ⟨lv, h1, h2⟩
          · rw [hlit] at h1
            simp [Setlec.Expr.getAppFn] at h1
          · rw [hlit] at h1
            simp [Setlec.Expr.getAppFn] at h1
          · rw [hlit] at h1
            simp [Setlec.Expr.getAppFn] at h1
          · rw [hlit] at h2
            simp [Setlec.Expr.getAppArgs] at h2
      rw [he₃] at hbranch
      rcases hbranch with rfl |
        ⟨us₂, entry₂, hfn₂, hf₂, hnat₂, -, -, -, -, -⟩
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨sn, i, e₂w, rfl⟩)))
      · exfalso
        rcases hdead with ⟨n, ty, b, m, h1, h2⟩ |
          ⟨sn', i', e₀, h1⟩ |
          ⟨c, us', cv, mI, rP, rules, h1, h2, h3⟩ | ⟨lv, h1, h2⟩
        · rw [hfn₂] at h1
          exact nomatch h1
        · rw [hfn₂] at h1
          exact nomatch h1
        · rw [hfn₂] at h1
          have hce : Expr.const entry₂.ctor us₂ = .const c us' :=
            h1
          injection hce with hh1 hh2
          obtain ⟨cvj, nP, nF, hcj⟩ := hPC hf₂ hnat₂
          rw [hh1, h2] at hcj
          exact nomatch (Option.some.inj hcj)
        · rw [hfn₂] at h1
          exact nomatch h1
    · rcases hres with ⟨n₀, hWeq, hrs⟩ |
        ⟨s₀, t₀, g₀, hWeq, hsupp, hg₀, hrun₀, hrs⟩
      · subst hWeq
        have he₃ : e₃ = Expr.lit (.natVal n₀) := by
          rcases Setlec.projLitToCtorP_inv (mode := μ) hlitp with
            heq | ⟨s₁, hlit, -, -⟩
          · exact heq
          · exact nomatch hlit
        rw [he₃] at hbranch
        rcases hbranch with rfl |
          ⟨us₂, entry₂, hfn₂, -, -, -, -, -, -, -⟩
        · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨sn, i, _, rfl⟩)))
        · simp [Setlec.Expr.getAppFn] at hfn₂
      · subst hWeq
        by_cases hm₀ : pe' = Expr.lit (.strVal s₀)
        · cases g'' with
          | zero =>
            exfalso
            obtain ⟨n₁, hn₁⟩ := Setlec.whnfLoopFuel_succ
            rw [hn₁, whnfLoop_succ] at hloopS
            unfold Setlec.whnfStep at hloopS
            simp only [Bind.bind, Except.bind] at hloopS
            exact nomatch hloopS
          | succ g₃ =>
            subst hm₀
            have hw' : whnf μ env (g₃ + 1 + 1) d
                (Expr.lit (.strVal s₀))
                = .ok (Expr.lit (.strVal s₀)) :=
              whnf_lit_id (g := g₃)
            exact ihr (whnfCore_proj_congr hscrut hw' hrun)
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl (Or.inl ⟨sn, i, pe, Expr.lit (.strVal s₀),
              pe', g'' + 1, hscrut, ?_, hm₀⟩)))))))
          exact RawReach.litStr s₀ g₀ hg₀ hsupp hrun₀ hrs
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hfs)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hps))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl hcs)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr hns)))))))
  | iotaPlain c us cv mI rP rules rl cj usj hfn hc hlen hM hMfn hrl
      hml hnin rest ihM ihr =>
    intro hrun
    rename_i eS MS wS
    cases g with
    | zero => exact nomatch hrun
    | succ g' =>
    -- the subject is an application (nonempty spine)
    obtain ⟨S', last, rfl⟩ : ∃ S' last, eS = Expr.app S' last := by
      cases eS <;>
        first
          | (exact ⟨_, _, rfl⟩)
          | (exfalso
             simp [Setlec.Expr.getAppArgs] at hlen)
    obtain ⟨f_act, hhead, hcase⟩ := whnfCore_app_decompose hrun
    -- the inner spine is fire-proof: identity
    have hfn' : S'.getAppFn = Expr.const c us := hfn
    have hlen' : S'.getAppArgs.length = mI := by
      have := hlen
      rw [show (Expr.app S' last).getAppArgs
        = S'.getAppArgs ++ [last] from rfl,
        List.length_append] at this
      simp only [List.length_cons, List.length_nil] at this
      omega
    have hid : f_act = S' := by
      have hfeq : Setlec.Expr.mkAppN (.const c us) S'.getAppArgs
          = S' := by
        have he := Setlec.Expr.mkAppN_getApp S'
        rw [hfn'] at he
        exact he
      rcases whnfCore_rec_spine_inv (μ := μ) hm
        (as := S'.getAppArgs) (n := c) (us := us)
        (by rw [hfeq]; exact hhead) with heq |
        ⟨pre, post, g₀, e₀, h₀, hsplit, -, hio₀, -, -⟩
      · rw [heq, hfeq]
      · exfalso
        obtain ⟨c', us', cv', mI', rP', rules', hfn₀, hfc₀⟩ :=
          iotaRec_fired_head hio₀
        rw [Setlec.Expr.getAppFn_mkAppN] at hfn₀
        have hce : Expr.const c us = Expr.const c' us' := hfn₀
        injection hce with h1 h2
        subst h1
        rw [hc] at hfc₀
        injection hfc₀ with hci
        injection hci with e1 e2 e3 e4
        subst e2
        have hpre : pre.length = mI + 1 := by
          obtain ⟨cx, usx, cvx, mIx, rPx, rulesx, m0, m1, mj, cjx,
            usjx, cvjx, cnPx, cnFx, rrx, cbx, cbodyx, residx, crx,
            usrx, hfnx, hfcx, hlenx, -, -, -, -, -, -, -, -, -, -,
            -, -, -, -, -, -, -, -, -⟩ :=
            Setlec.iotaRec_inv (mode := μ)
              (by rw [Setlec.iotaRec_fold] at hio₀; exact hio₀)
          rw [Setlec.Expr.getAppFn_mkAppN] at hfnx
          have hcex : Expr.const c us = Expr.const cx usx := hfnx
          injection hcex with hx1 hx2
          subst hx1
          rw [hc] at hfcx
          injection hfcx with hcix
          injection hcix with ex1 ex2 ex3 ex4
          subst ex2
          rw [Setlec.Expr.getAppArgs_mkAppN] at hlenx
          simpa [Setlec.Expr.getAppArgs] using hlenx
        have : pre.length ≤ S'.getAppArgs.length := by
          rw [hsplit, List.length_append]
          omega
        omega
    rw [hid] at hcase
    rcases hcase with ⟨n, ty, b, m, ta, heq, -, -, -⟩ |
      ⟨n, ty, b, m, ta, heq, -, -, rfl⟩ | ⟨hnl, hio⟩
    · exfalso
      rw [heq] at hfn'
      simp [Setlec.Expr.getAppFn] at hfn'
    · exfalso
      rw [heq] at hfn'
      simp [Setlec.Expr.getAppFn] at hfn'
    · rcases hio with ⟨e''a, hio, hcont⟩ | ⟨hio, rfl⟩
      · by_cases he : e''a = (Setlec.Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            ((Expr.app S' last).getAppArgs.take rP
              ++ MS.getAppArgs.drop rl.ctorParams))
        · subst he
          exact ihr (hm.2.2.1 (Nat.le_succ g') hcont)
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨Expr.app S' last, MS,
              (Setlec.Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            ((Expr.app S' last).getAppArgs.take rP
              ++ MS.getAppArgs.drop rl.ctorParams)),
              c, us, cv, mI, rP,
              rules, g', some e''a, hfn, hc, hlen,
              hM, hio, ?_⟩)))))
          intro hcon
          exact he (Option.some.inj hcon)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨Expr.app S' last, MS,
            (Setlec.Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            ((Expr.app S' last).getAppArgs.take rP
              ++ MS.getAppArgs.drop rl.ctorParams)),
            c, us, cv, mI, rP,
            rules, g', none, hfn, hc, hlen, hM,
            hio, fun hcon => nomatch hcon⟩)))))
  | iotaK c us cv mI rP rl cvj cnP T usT cvT caps targs hfn hc hlen
      hM hcj hT hTi hK hml htb htw rest ihM ihr =>
    intro hrun
    rename_i eS MS wS
    cases g with
    | zero => exact nomatch hrun
    | succ g' =>
    -- the subject is an application (nonempty spine)
    obtain ⟨S', last, rfl⟩ : ∃ S' last, eS = Expr.app S' last := by
      cases eS <;>
        first
          | (exact ⟨_, _, rfl⟩)
          | (exfalso
             simp [Setlec.Expr.getAppArgs] at hlen)
    obtain ⟨f_act, hhead, hcase⟩ := whnfCore_app_decompose hrun
    -- the inner spine is fire-proof: identity
    have hfn' : S'.getAppFn = Expr.const c us := hfn
    have hlen' : S'.getAppArgs.length = mI := by
      have := hlen
      rw [show (Expr.app S' last).getAppArgs
        = S'.getAppArgs ++ [last] from rfl,
        List.length_append] at this
      simp only [List.length_cons, List.length_nil] at this
      omega
    have hid : f_act = S' := by
      have hfeq : Setlec.Expr.mkAppN (.const c us) S'.getAppArgs
          = S' := by
        have he := Setlec.Expr.mkAppN_getApp S'
        rw [hfn'] at he
        exact he
      rcases whnfCore_rec_spine_inv (μ := μ) hm
        (as := S'.getAppArgs) (n := c) (us := us)
        (by rw [hfeq]; exact hhead) with heq |
        ⟨pre, post, g₀, e₀, h₀, hsplit, -, hio₀, -, -⟩
      · rw [heq, hfeq]
      · exfalso
        obtain ⟨c', us', cv', mI', rP', rules', hfn₀, hfc₀⟩ :=
          iotaRec_fired_head hio₀
        rw [Setlec.Expr.getAppFn_mkAppN] at hfn₀
        have hce : Expr.const c us = Expr.const c' us' := hfn₀
        injection hce with h1 h2
        subst h1
        rw [hc] at hfc₀
        injection hfc₀ with hci
        injection hci with e1 e2 e3 e4
        subst e2
        have hpre : pre.length = mI + 1 := by
          obtain ⟨cx, usx, cvx, mIx, rPx, rulesx, m0, m1, mj, cjx,
            usjx, cvjx, cnPx, cnFx, rrx, cbx, cbodyx, residx, crx,
            usrx, hfnx, hfcx, hlenx, -, -, -, -, -, -, -, -, -, -,
            -, -, -, -, -, -, -, -, -⟩ :=
            Setlec.iotaRec_inv (mode := μ)
              (by rw [Setlec.iotaRec_fold] at hio₀; exact hio₀)
          rw [Setlec.Expr.getAppFn_mkAppN] at hfnx
          have hcex : Expr.const c us = Expr.const cx usx := hfnx
          injection hcex with hx1 hx2
          subst hx1
          rw [hc] at hfcx
          injection hfcx with hcix
          injection hcix with ex1 ex2 ex3 ex4
          subst ex2
          rw [Setlec.Expr.getAppArgs_mkAppN] at hlenx
          simpa [Setlec.Expr.getAppArgs] using hlenx
        have : pre.length ≤ S'.getAppArgs.length := by
          rw [hsplit, List.length_append]
          omega
        omega
    rw [hid] at hcase
    rcases hcase with ⟨n, ty, b, m, ta, heq, -, -, -⟩ |
      ⟨n, ty, b, m, ta, heq, -, -, rfl⟩ | ⟨hnl, hio⟩
    · exfalso
      rw [heq] at hfn'
      simp [Setlec.Expr.getAppFn] at hfn'
    · exfalso
      rw [heq] at hfn'
      simp [Setlec.Expr.getAppFn] at hfn'
    · rcases hio with ⟨e''a, hio, hcont⟩ | ⟨hio, rfl⟩
      · by_cases he : e''a = (Setlec.Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            ((Expr.app S' last).getAppArgs.take rP
              ++ (targs.take cnP).drop rl.ctorParams))
        · subst he
          exact ihr (hm.2.2.1 (Nat.le_succ g') hcont)
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨Expr.app S' last, MS,
              (Setlec.Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            ((Expr.app S' last).getAppArgs.take rP
              ++ (targs.take cnP).drop rl.ctorParams)),
              c, us, cv, mI, rP,
              [rl], g', some e''a, hfn, hc, hlen,
              hM, hio, ?_⟩)))))
          intro hcon
          exact he (Option.some.inj hcon)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨Expr.app S' last, MS,
            (Setlec.Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            ((Expr.app S' last).getAppArgs.take rP
              ++ (targs.take cnP).drop rl.ctorParams)),
            c, us, cv, mI, rP,
            [rl], g', none, hfn, hc, hlen, hM,
            hio, fun hcon => nomatch hcon⟩)))))
  | iotaEta c us ust cv mI rP rl cvj cnP cnF T usT cvT caps targs
      hfn hc hlen hM hcj hT hTi heta hec hml htb htw rest ihM ihr =>
    intro hrun
    rename_i eS MS wS
    cases g with
    | zero => exact nomatch hrun
    | succ g' =>
    -- the subject is an application (nonempty spine)
    obtain ⟨S', last, rfl⟩ : ∃ S' last, eS = Expr.app S' last := by
      cases eS <;>
        first
          | (exact ⟨_, _, rfl⟩)
          | (exfalso
             simp [Setlec.Expr.getAppArgs] at hlen)
    obtain ⟨f_act, hhead, hcase⟩ := whnfCore_app_decompose hrun
    -- the inner spine is fire-proof: identity
    have hfn' : S'.getAppFn = Expr.const c us := hfn
    have hlen' : S'.getAppArgs.length = mI := by
      have := hlen
      rw [show (Expr.app S' last).getAppArgs
        = S'.getAppArgs ++ [last] from rfl,
        List.length_append] at this
      simp only [List.length_cons, List.length_nil] at this
      omega
    have hid : f_act = S' := by
      have hfeq : Setlec.Expr.mkAppN (.const c us) S'.getAppArgs
          = S' := by
        have he := Setlec.Expr.mkAppN_getApp S'
        rw [hfn'] at he
        exact he
      rcases whnfCore_rec_spine_inv (μ := μ) hm
        (as := S'.getAppArgs) (n := c) (us := us)
        (by rw [hfeq]; exact hhead) with heq |
        ⟨pre, post, g₀, e₀, h₀, hsplit, -, hio₀, -, -⟩
      · rw [heq, hfeq]
      · exfalso
        obtain ⟨c', us', cv', mI', rP', rules', hfn₀, hfc₀⟩ :=
          iotaRec_fired_head hio₀
        rw [Setlec.Expr.getAppFn_mkAppN] at hfn₀
        have hce : Expr.const c us = Expr.const c' us' := hfn₀
        injection hce with h1 h2
        subst h1
        rw [hc] at hfc₀
        injection hfc₀ with hci
        injection hci with e1 e2 e3 e4
        subst e2
        have hpre : pre.length = mI + 1 := by
          obtain ⟨cx, usx, cvx, mIx, rPx, rulesx, m0, m1, mj, cjx,
            usjx, cvjx, cnPx, cnFx, rrx, cbx, cbodyx, residx, crx,
            usrx, hfnx, hfcx, hlenx, -, -, -, -, -, -, -, -, -, -,
            -, -, -, -, -, -, -, -, -⟩ :=
            Setlec.iotaRec_inv (mode := μ)
              (by rw [Setlec.iotaRec_fold] at hio₀; exact hio₀)
          rw [Setlec.Expr.getAppFn_mkAppN] at hfnx
          have hcex : Expr.const c us = Expr.const cx usx := hfnx
          injection hcex with hx1 hx2
          subst hx1
          rw [hc] at hfcx
          injection hfcx with hcix
          injection hcix with ex1 ex2 ex3 ex4
          subst ex2
          rw [Setlec.Expr.getAppArgs_mkAppN] at hlenx
          simpa [Setlec.Expr.getAppArgs] using hlenx
        have : pre.length ≤ S'.getAppArgs.length := by
          rw [hsplit, List.length_append]
          omega
        omega
    rw [hid] at hcase
    rcases hcase with ⟨n, ty, b, m, ta, heq, -, -, -⟩ |
      ⟨n, ty, b, m, ta, heq, -, -, rfl⟩ | ⟨hnl, hio⟩
    · exfalso
      rw [heq] at hfn'
      simp [Setlec.Expr.getAppFn] at hfn'
    · exfalso
      rw [heq] at hfn'
      simp [Setlec.Expr.getAppFn] at hfn'
    · rcases hio with ⟨e''a, hio, hcont⟩ | ⟨hio, rfl⟩
      · by_cases he : e''a = (Setlec.Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            ((Expr.app S' last).getAppArgs.take rP
              ++ (Setlec.etaFabArgs T ust targs MS
                caps.etaFields).drop rl.ctorParams))
        · subst he
          exact ihr (hm.2.2.1 (Nat.le_succ g') hcont)
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨Expr.app S' last, MS,
              (Setlec.Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            ((Expr.app S' last).getAppArgs.take rP
              ++ (Setlec.etaFabArgs T ust targs MS
                caps.etaFields).drop rl.ctorParams)),
              c, us, cv, mI, rP,
              [rl], g', some e''a, hfn, hc, hlen,
              hM, hio, ?_⟩)))))
          intro hcon
          exact he (Option.some.inj hcon)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨Expr.app S' last, MS,
            (Setlec.Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            ((Expr.app S' last).getAppArgs.take rP
              ++ (Setlec.etaFabArgs T ust targs MS
                caps.etaFields).drop rl.ctorParams)),
            c, us, cv, mI, rP,
            [rl], g', none, hfn, hc, hlen, hM,
            hio, fun hcon => nomatch hcon⟩)))))
  | @projFire sn i ES wS entry us hf hfn hnat hi hlenE rest ihr =>
    intro hrun
    cases g with
    | zero => exact nomatch hrun
    | succ g' =>
    obtain ⟨e₂w, e₃, hscrut, hlitp, hbranch⟩ :=
      Setlec.whnf_proj_inv (mode := μ) hrun
    -- the ctor-headed scrutinee is loop-inert
    obtain ⟨cvj, nP, nF, hcj⟩ := hPC hf hnat
    have hnr : ∀ cv' mI' rP' rules',
        env.find? entry.ctor ≠ some (.recInfo cv' mI' rP' rules') :=
      fun cv' mI' rP' rules' hr => by
        rw [hcj] at hr
        exact nomatch hr
    cases g' with
    | zero => exact nomatch hscrut
    | succ g'' =>
    rw [Setlec.whnf_succ] at hscrut
    have hloop : Setlec.whnfLoop (Setlec.pureFns μ env g'') env d
        Setlec.whnfLoopFuel ES = .ok e₂w := hscrut
    rcases hbud : Setlec.whnfLoopFuel with _ | l'
    · rw [hbud] at hloop
      exact nomatch hloop
    rw [hbud] at hloop
    obtain ⟨e₁, hwc, htri⟩ := whnfStep_decompose hloop
    rw [Setlec.whnfCore_def] at hwc
    have hid : e₁ = ES := whnfCore_nonrec_id hm hfn hnr hwc
    rcases htri with ⟨e₂n, hrn, -⟩ | ⟨hrn, u, hud, -⟩ |
      ⟨hrn, hud, hstop⟩
    · rw [hid] at hrn
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (Or.inr ⟨sn, i, ES, e₂n, g'', hrn⟩)))))))
    · exfalso
      rw [hid] at hud
      obtain ⟨c', us', hfnu, hkind⟩ := unfoldDefinition_inv hud
      rw [hfn] at hfnu
      injection hfnu with h1 h2
      subst h1
      rcases hkind with ⟨cv', v', h', hfu⟩ | ⟨cv', v', hfu⟩ <;>
        (rw [hcj] at hfu; exact nomatch hfu)
    · rw [hid] at hstop
      rw [hstop] at hlitp
      have he₃ : e₃ = ES := by
        rcases Setlec.projLitToCtorP_inv (mode := μ) hlitp with
          heq | ⟨s₀, hlit, -, -⟩
        · exact heq
        · exfalso
          rw [hlit] at hfn
          simp [Setlec.Expr.getAppFn] at hfn
      rw [he₃] at hbranch
      rcases hbranch with rfl |
        ⟨us₂, entry₂, hfn₂, hf₂, -, -, -, -, hred₂, -⟩
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨sn, i, _, rfl⟩)))
      · obtain rfl : entry₂ = entry := by
          rw [hf] at hf₂
          exact (Option.some.inj hf₂).symm
        exact ihr (hm.2.2.1 (by omega : g'' + 1 ≤ g'' + 1 + 1)
          hred₂)

/-- The loop out weakens in the budget index. -/
theorem LoopAlignOut.weaken_l {d G g l l' : Nat} {f' W : Expr}
    (hl : l ≤ l') (h : LoopAlignOut μ env d G g l f' W) :
    LoopAlignOut μ env d G g l' f' W := by
  rcases h with ⟨g₂, l₂, hg₂, hl₂, run₂⟩ | h | h | h | h | h | h
  · exact Or.inl ⟨g₂, l₂, hg₂, Nat.le_trans hl₂ hl, run₂⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

set_option maxHeartbeats 1600000 in
/-- **The loop alignment discharge at one knot fuel** — budget
induction consuming the core tier at the same fuel; the pendings
are the loop's own delta/nat steps. -/
theorem loopAlign_step {env : Env}
    (hm : KnotFuelMono μ env) {g : Nat}
    (hC : CoreAlignAt μ env g) : LoopAlignAt μ env g := by
  intro d G l
  induction l with
  | zero =>
    intro f f' W h hrun
    exact nomatch hrun
  | succ l ihl =>
    intro f f' W h hrun
    obtain ⟨e₁, hwc, htri⟩ := whnfStep_decompose hrun
    rw [Setlec.whnfCore_def] at hwc
    rcases hC h hwc with
      ⟨g₂, hg₂, run₂⟩ | hdead | ⟨u, hu, hrest_u⟩ |
      ⟨res, c, n₁, n₂, hhd, hnr, hprov, hrest_n⟩ | hres |
      hfs | hps | hcs | hns
    · refine Or.inl ⟨g, l + 1, Nat.le_refl g, Nat.le_refl _, ?_⟩
      rw [whnfLoop_succ]
      have run₂' : (Setlec.pureFns μ env g).whnfCore d f'
          = .ok e₁ := by
        rw [Setlec.whnfCore_def]
        exact hm.2.2.1 hg₂ run₂
      rcases htri with ⟨e₂, hrn, hk⟩ | ⟨hrn, e₂, hud, hk⟩ |
        ⟨hrn, hud, rfl⟩
      · exact whnfStep_assemble_nat run₂' hrn hk
      · exact whnfStep_assemble_delta run₂' hrn hud hk
      · exact whnfStep_assemble_stuck run₂' hrn hud
    · rcases htri with ⟨e₂, hrn, hk⟩ | ⟨hrn, e₂, hud, hk⟩ |
        ⟨hrn, hud, rfl⟩
      · exfalso
        rw [Setlec.reduceNat_fold] at hrn
        rcases reduceNat_decompose hrn with
          ⟨x, wx, n, heq, hsg, -, -, -⟩ |
          ⟨c, x, wx, n, heq, hcn, hgn, -, -, -⟩ |
          ⟨c, x, y, wx, wy, n₁', n₂', heq, hcn, hgn, -, -, -, -,
            -⟩ <;>
          subst heq <;>
          rcases hdead with ⟨n', ty', b', m', h1, h2⟩ |
            ⟨sn', i', e₀, h1⟩ |
            ⟨c', us', cv, mI, rP, rules, h1, h2, h3⟩ |
            ⟨lv, h1, h2⟩
        all_goals
          first
            | (simp [Setlec.Expr.getAppFn] at h1)
            | skip
        · obtain ⟨hx1, hx2⟩ := h1
          subst hx1
          exact natLitSupported_succ_not_rec hsg h2
        · obtain ⟨hx1, hx2⟩ := h1
          subst hx1
          refine natOpGuard_not_rec ?_ hgn h2
          rcases hcn with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr rfl))))))))))))))
        · obtain ⟨hx1, hx2⟩ := h1
          subst hx1
          refine natOpGuard_not_rec ?_ hgn h2
          rcases hcn with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl rfl)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl rfl))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inl rfl)))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inl rfl))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl rfl)))))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl rfl))))))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inl rfl)))))))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inl rfl))))))))))))))
      · exfalso
        obtain ⟨c, us, hfnu, hkind⟩ := unfoldDefinition_inv hud
        rcases hdead with ⟨n', ty', b', m', h1, h2⟩ |
          ⟨sn', i', e₀, h1⟩ |
          ⟨c', us', cv, mI, rP, rules, h1, h2, h3⟩ | ⟨lv, h1, h2⟩
        · rw [hfnu] at h1
          exact nomatch h1
        · rw [hfnu] at h1
          exact nomatch h1
        · rw [hfnu] at h1
          have hce : Expr.const c us = Expr.const c' us' := h1
          injection hce with hx1 hx2
          subst hx1
          rcases hkind with ⟨cv', v', h', hfu⟩ | ⟨cv', v', hfu⟩ <;>
            (rw [h2] at hfu; exact nomatch hfu)
        · rw [hfnu] at h1
          exact nomatch h1
      · exact Or.inr (Or.inl hdead)
    · rcases htri with ⟨e₂, hrn, hk⟩ | ⟨hrn, e₂, hud, hk⟩ |
        ⟨hrn, hud, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨e₁, u, e₂, g, hrn, hu⟩)))))))
      · rw [hu] at hud
        obtain rfl := Option.some.inj hud
        exact (ihl hrest_u hk).weaken_l (Nat.le_succ l)
      · rw [hu] at hud
        exact nomatch hud
    · rcases htri with ⟨e₂, hrn, hk⟩ | ⟨hrn, e₂, hud, hk⟩ |
        ⟨hrn, hud, rfl⟩
      · by_cases he : e₂ = res
        · subst he
          exact (ihl hrest_n hk).weaken_l (Nat.le_succ l)
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨e₁, res, c, g, some e₂, n₁, n₂, hhd,
              hprov, hrn, ?_⟩))))))
          intro hcon
          exact he (Option.some.inj hcon)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨e₁, res, c, g, none, n₁, n₂,
            hhd, hprov, hrn, fun hcon => nomatch hcon⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨W, res, c, g, none, n₁, n₂,
            hhd, hprov, hrn, fun hcon => nomatch hcon⟩))))))
    · rcases htri with ⟨e₂, hrn, hk⟩ | ⟨hrn, e₂, hud, hk⟩ |
        ⟨hrn, hud, rfl⟩
      · exfalso
        rw [Setlec.reduceNat_fold] at hrn
        rcases hres with ⟨n₀, rfl, -⟩ | ⟨s₀, t₀, g₀, rfl, -, -, -,
          -⟩ <;>
          (rcases reduceNat_decompose hrn with
            ⟨x, wx, n, heq, -, -, -, -⟩ |
            ⟨c', x, wx, n, heq, -, -, -, -, -⟩ |
            ⟨c', x, y, wx, wy, na, nb, heq, -, -, -, -, -, -,
              -⟩ <;>
            exact nomatch heq)
      · exfalso
        rcases hres with ⟨n₀, rfl, -⟩ | ⟨s₀, t₀, g₀, rfl, -, -, -,
          -⟩ <;>
          (obtain ⟨c', us', hfnu, -⟩ := unfoldDefinition_inv hud
           simp [Setlec.Expr.getAppFn] at hfnu)
      · exact Or.inr (Or.inr (Or.inl hres))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hfs)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hps))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        hcs)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        hns)))))

/-- **The alignment engine DISCHARGED** at every knot fuel (strong
induction on the knot — scrutinee whnfs run one fuel down, the
kernel's own discipline; the loop tier consumes the core tier at
the same fuel). -/
theorem alignAt {env : Env} (henv : EnvWF env)
    (hm : KnotFuelMono μ env) (hPC : ProjCtorWF env) :
    ∀ (g : Nat), CoreAlignAt μ env g ∧ LoopAlignAt μ env g := by
  intro g
  induction g using Nat.strongRecOn with
  | ind g IH =>
    have hC : CoreAlignAt μ env g :=
      coreAlign_step henv hm hPC (fun g' hg' => (IH g' hg').1)
        (fun g' hg' => (IH g' hg').2)
    exact ⟨hC, loopAlign_step hm hC⟩

end Discharge

end Setlec.SetR.Interp2
