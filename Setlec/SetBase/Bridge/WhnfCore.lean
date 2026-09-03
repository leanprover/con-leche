import Setlec.SetBase.WhnfCoreLeaf
import Setlec.SetBase.Bridge.Claims
import Setlec.Verify.Denote.Inst
import Setlec.Verify.Denote.InstSimp
import Setlec.Verify.Denote.Tele
import Setlec.Verify.Denote.Levels

/-!
# The reduction quarters of `CheckStepR` (task #148, T3, batches a/b/f)

`WhnfCoreClaimsR` and `WhnfClaimsR` at `fuel + 1`.  The case split is
`whnfCoreBody`'s, and the map from clause to rule is the design's §1.1
table read left to right:

| `whnfCoreBody` clause | rule | bridge input |
|---|---|---|
| leaves (`sort`, `fvar`, `forallE`, `lam`, `const`, `lit`) | `Red.refl` (R1) | the `pure e` branches |
| `.letE` | `Red.zeta` (R5) — **premise-free** | the clause itself |
| `.app`, λ head, certified | `Red.beta` (R4) | `whnf_app_inv`, β disjunct |
| `.app`, recursor head | `Red.iota` (R11) | `whnf_app_inv`, ι disjunct → `IotaStepR` |
| `.app`, stuck | `Red.appFn` (R3) | `whnf_app_inv`, stuck disjunct |
| `.proj` | `Red.projRed` (R6) | `whnf_proj_inv` → `ProjStepR` |

and the loop's three moves (`whnfStep`) are: `whnfCore` (a `Red`),
`reduceNat` (a `Red`, R8–R10 → `ReduceNatStepR`), and **delta — which
is not a rule at all**: `denote_delta_stepR` says the unfolding denotes
*identically*, so the loop's accumulated reduction is exactly as long as
the number of non-delta steps taken, however many constants were
unfolded along the way (design §7.2, R17).

Three clauses are named `Prop`s rather than proofs, at the checker's own
function boundaries (the house rule: an unproved step is a named `Prop`,
so every consumer of one is visible in the source — `CheckStepTT`,
`CheckDeclTT`, and now these).  They are the widest three, and they are
the later batches' subjects.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env} {fuel d : Nat}

/-! ## The leaf clauses

The six `whnfCoreR_*` `rfl` lemmas used to stand here.  THE SEPARATION's
S2 re-based them to `Setlec/SetBase/WhnfCoreLeaf.lean` (S1 deferred them
here by name): they say nothing about a model, both lanes simp with
them, and the graded lane was reading them through the 2U
`Step2/Whnf`.  Names, statements and `@[simp]` attributes unchanged;
this module imports them back. -/

/-- The leaf clauses satisfy the `whnfCore` claim: the reduct *is* the
subject, so the derivation is `Red.refl` and nothing has to be
re-denoted. -/
theorem whnfCore_leaf_claimR {cval : TConstVal} {φ : Name → Nat}
    {Δ : List VExpr} {e e' : Expr} {v : VExpr}
    (hleaf : (∃ u, e = .sort u) ∨ (∃ idx n ty, e = .fvar idx n ty) ∨
      (∃ n ty body bi, e = .forallE n ty body bi) ∨
      (∃ n ty body mb, e = .lam n ty body mb) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l))
    (h : whnfCore mode env (fuel + 1) d e = .ok e')
    (hv : denote cval env φ d e = some v) :
    ∃ v', denote cval env φ d e' = some v' ∧ Red mode env cval φ Δ v v' := by
  have he : e' = e := by
    rcases hleaf with ⟨u, rfl⟩ | ⟨idx, n, ty, rfl⟩ | ⟨n, ty, body, bi, rfl⟩ |
      ⟨n, ty, body, mb, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
      simp only [whnfCoreR_sort, whnfCoreR_fvar, whnfCoreR_forallE,
        whnfCoreR_lam, whnfCoreR_const, whnfCoreR_lit, Except.ok.injEq] at h <;>
      exact h.symm
  subst he
  exact ⟨v, hv, Red.refl⟩

/-! ## The zeta clause

`whnfCoreBody`'s `.letE` clause reduces to `b.instantiate1 v` and
recurses.  R5 is **premise-free** — no certificate, no typing, nothing
from the environment — because `denote` is structural: the `let`
denotes to `VExpr.letE`, its reduct to that term's own `inst`, and the
rule between them is the whole content. -/

/-- The zeta step: a `let` `Red`uces to its reduct, which denotes. -/
theorem denote_zeta_stepR {cval : TConstVal} {env : Env} {φ : Name → Nat}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {Δ : List VExpr} {d : Nat} {n : Name} {ty v b : Expr} {V : VExpr}
    (hfb : Expr.fvarsBelow d b) (hwv : Expr.WScoped d v)
    (hbv : v.looseBVarsBounded 0 = true)
    (hden : denote cval env φ d (.letE n ty v b) = some V) :
    ∃ W, denote cval env φ d (b.instantiate1 v) = some W ∧
      Red mode env cval φ Δ V W := by
  rw [denote_letE] at hden
  split at hden
  · next A xv hA hv =>
    split at hden
    · exact nomatch hden
    · next B hB =>
      obtain rfl : V = .letE A xv B := (Option.some.inj hden).symm
      refine ⟨VExpr.inst B xv, ?_, Red.zeta⟩
      rw [denote_beta (n := n) (ty := ty) hcl hfb hwv hbv hv 0, hB]
      rfl
  · exact nomatch hden

/-! ## The beta clause

The only reduction clause that consumes a certificate.  `whnf_app_inv`
hands back `inferTypeCore … a = .ok ta` and `isDefEqCore … ta ty =
.ok true`; the inference claim turns the first into an `Infer` for the
argument (up to `DefEq`), the equality claim turns the second into
`DefEq ⟦ta⟧ A`, and `DefEq.trans` composes the slack away — which is
exactly `Red.beta`'s premise pair, in the checker's own order.

**This is the slack design's first real test on a certificate site**,
and it composes on the nose: R4 takes `Infer Δ a ta` and
`DefEq Δ ta A`, i.e. the very pair, so the bridge does not even have to
push the slack anywhere — it *is* the rule's shape. -/

/-- The beta step: a certified redex `Red`uces to its contractum. -/
theorem denote_beta_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {n : Name} {ty body a ta : Expr}
    {A B x : VExpr}
    (hta : inferTypeCore mode env fuel d a = .ok ta)
    (hde : isDefEqCore mode env fuel d ta ty = .ok true)
    (hty : denote m.cval env φ d ty = some A)
    (hbody : denote m.cval env φ (d + 1)
      (body.instantiate1 (.fvar d n ty)) = some B)
    (hax : denote m.cval env φ d a = some x)
    (hfb : Expr.fvarsBelow d body)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a) (hCa : CtxOkR mode m.cval env φ d Δ a)
    (hwty : Expr.WScoped d ty) (hbty : ty.looseBVarsBounded 0 = true)
    (hLty : Expr.LeavesBounded ty)
    (hCty : CtxOkR mode m.cval env φ d Δ ty) :
    denote m.cval env φ d (body.instantiate1 a) = some (VExpr.inst B x) ∧
      Red mode env m.cval φ Δ (.app (.lam A B) x) (VExpr.inst B x) := by
  -- the certificate: the argument infers a type `DefEq` to the domain
  obtain ⟨x', tv, hix, hita, T', hxT, hTt⟩ := ihi hta hwa hba hLa hCa
  obtain rfl : x' = x := by rw [hix] at hax; exact Option.some.inj hax
  obtain ⟨hwta, hbta, hLta, hCta⟩ := frame_inferR m.wf hta hwa hba hLa hCa
  have hDeq : DefEq mode env m.cval φ Δ tv A :=
    ihd hde hwta hbta hLta hwty hbty hLty hCta hCty hita hty
  refine ⟨?_, Red.beta hxT (hTt.trans hDeq)⟩
  rw [denote_beta (n := n) (ty := ty) hcl hfb hwa hba hax 0, hbody]
  rfl

/-! ## The three named clause obligations

Stated at the checker's own function boundaries (`iotaRecP`,
`whnfCore` restricted to `.proj`, `reduceNatP`), which is where the
factoring rule allows an obligation to sit. -/

/-- **The iota clause** (batch g).  A fired recursor application
`Red`uces to its reduct, which carries the frame conditions the
recursive `whnfCore` call needs.  Its content is R11 + R12–R14, from
`iotaRec_inv` and `majorToCtor_inv`. -/
def IotaStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {e e'' : Expr} {v : VExpr},
    iotaRecP mode env fuel d e = .ok (some e'') →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → CtxOkR mode m.cval env φ d Δ e →
    denote m.cval env φ d e = some v →
    ∃ w, denote m.cval env φ d e'' = some w ∧
      Red mode env m.cval φ Δ v w ∧
      Expr.WScoped d e'' ∧ e''.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e'' ∧ CtxOkR mode m.cval env φ d Δ e''

/-- **The projection clause**, whole (batch e).  Stated at *clause*
granularity rather than reduct granularity for the reason the TT lane
records: the clause reduces its scrutinee with `whnf` *and* expands
string literals with `projLitToCtor` before the table is consulted, so
isolating the reduct would leave two more unproved steps outside the
obligation rather than one inside it.  Its content is R6 (+ R7 through
`projLitToCtorP_inv`). -/
def ProjStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {sn : Name} {i : Nat} {pe e' : Expr}
    {v : VExpr},
    whnfCore mode env (fuel + 1) d (.proj sn i pe) = .ok e' →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    CtxOkR mode m.cval env φ d Δ (.proj sn i pe) →
    denote m.cval env φ d (.proj sn i pe) = some v →
    ∃ v', denote m.cval env φ d e' = some v' ∧
      Red mode env m.cval φ Δ v v'

/-- **The literal-acceleration obligation** (batch f).  `reduceNat`
replaces an operation applied to literals by the literal of its value;
the rules are R8 (`natSucc`), R9 (`natOp1`) and R10 (`natOp2`), and
their side conditions are the guard plus the `denoteClosed` of the
computed result. -/
def ReduceNatStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {e e₂ : Expr} {v : VExpr},
    reduceNatP mode env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → CtxOkR mode m.cval env φ d Δ e →
    denote m.cval env φ d e = some v →
    ∃ w, denote m.cval env φ d e₂ = some w ∧
      Red mode env m.cval φ Δ v w ∧
      Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₂ ∧ CtxOkR mode m.cval env φ d Δ e₂

/-! ## The application clause

Three sub-cases, from `whnf_app_inv`: β (certified), ι (via
`IotaStepR`), or stuck.  All three start with the head's own reduction,
which is `Red.appFn` (R3) — the only congruence `Red` has, and the
reason R11's subject is the *original* spine (deviation D2). -/

/-- The `.app` clause of `whnfCore_claimsR`. -/
theorem whnfCore_app_claimR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hiota : IotaStepR (mode := mode) m φ fuel)
    (ihwc : WhnfCoreClaimsR mode m φ fuel)
    (ihd : DefEqClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {f a e' : Expr} {v : VExpr}
    (h : whnfCore mode env (fuel + 1) d (.app f a) = .ok e')
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOkR mode m.cval env φ d Δ (.app f a))
    (hv : denote m.cval env φ d (.app f a) = some v) :
    ∃ v', denote m.cval env φ d e' = some v' ∧
      Red mode env m.cval φ Δ v v' := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCf : CtxOkR mode m.cval env φ d Δ f :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCa : CtxOkR mode m.cval env φ d Δ a :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  rw [denote_app] at hv
  split at hv
  · next vf va hif hia =>
    obtain rfl : v = .app vf va := (Option.some.inj hv).symm
    obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
    obtain ⟨vf', hif', hDf, hwf', hbf', hLf', hCf'⟩ :=
      whnfCore_packageR m φ ihwc hwf hws.1 hb.1 hLf hCf hif
    have hiapp : denote m.cval env φ d (.app f' a)
        = some (VExpr.app vf' va) := by
      rw [denote_app, hif', hia]
    have hDapp : Red mode env m.cval φ Δ (VExpr.app vf va)
        (VExpr.app vf' va) := Red.appFn hDf
    have hwapp : Expr.WScoped d (.app f' a) := by
      simp only [Expr.WScoped]; exact ⟨hwf', hws.2⟩
    have hbapp : (Expr.app f' a).looseBVarsBounded 0 = true := by
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hbf', hb.2⟩
    have hLapp : Expr.LeavesBounded (.app f' a) := fun l hl => by
      simp only [Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hLf' l hl
      · exact hLa l hl
    have hCapp : CtxOkR mode m.cval env φ d Δ (.app f' a) := by
      refine ⟨hC.1, fun l hl => ?_⟩
      simp only [Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hCf'.2 l hl
      · exact hCa.2 l hl
    rcases hcase with ⟨n, ty, body, mm, rfl, hbeta, ta, hta, hde⟩ |
      ⟨e'', hio, hwe''⟩ | rfl
    · -- β
      rw [denote_lam] at hif'
      split at hif'
      · exact nomatch hif'
      · next A hty =>
        split at hif'
        · exact nomatch hif'
        · next B hbody =>
          obtain rfl : vf' = .lam A B := (Option.some.inj hif').symm
          simp only [Expr.WScoped] at hwf'
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbf'
          have hLty : Expr.LeavesBounded ty := fun l hl =>
            hLf' l (by simp [Expr.fvarLeaves, hl])
          have hCty : CtxOkR mode m.cval env φ d Δ ty :=
            CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCf'
          obtain ⟨hred, hDbeta⟩ :=
            denote_beta_stepR (Δ := Δ) m φ hcl ihd ihi hta hde hty
              hbody hia hwf'.2.fvarsBelow hws.2 hb.2 hLa hCa
              hwf'.1 hbf'.1 hLty hCty
          have hwred : Expr.WScoped d (body.instantiate1 a) :=
            Expr.WScoped.instantiate1_gen hws.2 0 hwf'.2
          have hbred : (body.instantiate1 a).looseBVarsBounded 0 = true :=
            Expr.looseBVarsBounded_instantiate1_gen hb.2 hbf'.2
          have hLred : Expr.LeavesBounded (body.instantiate1 a) :=
            fun l hl => by
              rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
              · exact hLf' l (by simp [Expr.fvarLeaves, h2])
              · exact hLa l h2
          have hCred : CtxOkR mode m.cval env φ d Δ (body.instantiate1 a) := by
            refine ⟨hC.1, fun l hl => ?_⟩
            rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
            · exact hCf'.2 l (by simp [Expr.fvarLeaves, h2])
            · exact hCa.2 l h2
          obtain ⟨w, hw, hDw⟩ := ihwc hbeta hwred hbred hLred hCred hred
          exact ⟨w, hw, (hDapp.trans hDbeta).trans hDw⟩
    · -- ι
      obtain ⟨w, hw, hDio, hwe, hbe, hLe, hCe⟩ :=
        hiota hio hwapp hbapp hLapp hCapp hiapp
      obtain ⟨w', hw', hDw'⟩ := ihwc hwe'' hwe hbe hLe hCe hw
      exact ⟨w', hw', (hDapp.trans hDio).trans hDw'⟩
    · -- stuck
      exact ⟨_, hiapp, hDapp⟩
  · exact nomatch hv

/-! ## The `whnfCore` step -/

/-- **`WhnfCoreClaimsR` at `fuel + 1`**, modulo the projection and iota
obligations.

`_ihw` is deliberately unconsumed here: the reduction-loop claim is
needed by exactly one clause — the projection clause reduces its
scrutinee with `whnf` — and that clause is `hproj`.  The binder stays so
that discharging `ProjStepR` does not change this signature. -/
theorem whnfCore_claimsR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hiota : IotaStepR (mode := mode) m φ fuel)
    (hproj : ProjStepR (mode := mode) m φ fuel)
    (ihwc : WhnfCoreClaimsR mode m φ fuel) (_ihw : WhnfClaimsR mode m φ fuel)
    (ihd : DefEqClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel) :
    WhnfCoreClaimsR mode m φ (fuel + 1) := by
  intro d e e' Δ h hws hb hLb hC v hv
  match e with
  | .sort u => exact whnfCore_leaf_claimR (Or.inl ⟨u, rfl⟩) h hv
  | .fvar idx n ty =>
    exact whnfCore_leaf_claimR (Or.inr (Or.inl ⟨idx, n, ty, rfl⟩)) h hv
  | .forallE n ty body bi =>
    exact whnfCore_leaf_claimR
      (Or.inr (Or.inr (Or.inl ⟨n, ty, body, bi, rfl⟩))) h hv
  | .lam n ty body mb =>
    exact whnfCore_leaf_claimR
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, ty, body, mb, rfl⟩)))) h hv
  | .const n us =>
    exact whnfCore_leaf_claimR
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, us, rfl⟩))))) h hv
  | .lit l =>
    exact whnfCore_leaf_claimR
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, rfl⟩))))) h hv
  | .bvar i =>
    rw [denote_bvar] at hv
    exact nomatch hv
  | .letE nn tt vv bb =>
    -- ζ: premise-free, so this clause needs no certificate at all
    rw [whnfCore_succ] at h
    simp only [whnfCoreBody, whnfCore_def] at h
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hfb : Expr.fvarsBelow d bb := hws.2.2.fvarsBelow
    obtain ⟨W, hW, hDeq⟩ :=
      denote_zeta_stepR (Δ := Δ) (mode := mode) hcl hfb hws.2.1 hb.1.2 hv
    have hwred : Expr.WScoped d (bb.instantiate1 vv) :=
      Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
    have hbred : (bb.instantiate1 vv).looseBVarsBounded 0 = true :=
      Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
    have hLred : Expr.LeavesBounded (bb.instantiate1 vv) := fun l hl => by
      rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
    have hCred : CtxOkR mode m.cval env φ d Δ (bb.instantiate1 vv) := by
      refine ⟨hC.1, fun l hl => ?_⟩
      rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
      · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
      · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
    obtain ⟨v', hv', hDeq'⟩ := ihwc h hwred hbred hLred hCred hW
    exact ⟨v', hv', hDeq.trans hDeq'⟩
  | .app f a =>
    exact whnfCore_app_claimR m φ hcl hiota ihwc ihd ihi h hws hb hLb hC hv
  | .proj sn i pe => exact hproj h hws hb hLb hC hv

/-! ## The delta step

`whnfStep`'s third move, and the cheapest clause in the whole bridge:
**the reduct denotes to the *same* term**.  `EnvR.defn_eq` says a
definition's valuation *is* its value's denotation, so unfolding is
invisible and the "equation" is `rfl` — which is why delta contributes
no rule to the family (design §7.2, R17) and why the loop's `Red` chain
is as long as the number of non-delta steps and no longer. -/

/-- The shared core of the two unfolding branches (`defnInfo` and
`thmInfo`): they differ only in which `EnvR` field supplies the value's
equation. -/
private theorem delta_coreR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    {d : Nat} {e : Expr} {n : Name} {us : List Level} {cv : ConstantVal}
    {value : Expr} {v : VExpr} {ci : ConstantInfo}
    (hfn : e.getAppFn = .const n us)
    (hfind : env.find? n = some ci)
    (hcvt : ci.toConstantVal = cv)
    (hlen : us.length = cv.levelParams.length)
    (hnofv : value.hasFvar = false)
    (hval : ∀ ψ : Name → Nat,
      denoteClosed m.cval env ψ value = some (m.cval ci.name ψ))
    (hv : denote m.cval env φ d e = some v) :
    denote m.cval env φ d
      (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
        e.getAppArgs) = some v := by
  have he : Expr.mkAppN e.getAppFn e.getAppArgs = e := Expr.mkAppN_getApp e
  rw [← he] at hv
  obtain ⟨vf, vs, hf, hsp, rfl⟩ := denote_mkAppN_inv hv
  rw [hfn, denote_const, hfind] at hf
  simp only [hcvt] at hf
  rw [if_pos hlen] at hf
  obtain rfl : vf = m.cval n (Level.substFn φ cv.levelParams us) :=
    (Option.some.inj hf).symm
  obtain rfl : ci.name = n := by
    rw [Env.find?] at hfind
    have := List.find?_some hfind
    simpa using this
  refine denote_mkAppN hsp ?_
  rw [denote_instLevels m.val_params]
  have hfb : Expr.fvarsBelow 0 value :=
    (Expr.WScoped.of_not_hasFvar hnofv).fvarsBelow
  rw [denote_lift hcl hfb d (Nat.zero_le d)]
  have hv0 := hval (Level.substFn φ cv.levelParams us)
  rw [denoteClosed] at hv0
  rw [hv0]
  simp only [Option.map_some, Nat.sub_zero]
  rw [VExpr.liftN_eq_self_of_closed (hcl _ _)]

/-- **The delta step.**  A definition's unfolding denotes identically. -/
theorem denote_delta_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    {d : Nat} {e e' : Expr} {v : VExpr}
    (h : unfoldDefinition env e = some e')
    (hv : denote m.cval env φ d e = some v) :
    denote m.cval env φ d e' = some v := by
  rw [unfoldDefinition] at h
  split at h
  · next n us hfn =>
    split at h
    · next cv value hint hfind =>
      split at h
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj h).symm
        exact delta_coreR m φ hcl hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, hd, -⟩ := m.wf _ (find?_mem hfind)
              exact (hd cv value hint rfl).1)
          (fun ψ => m.defn_eq cv value hint (find?_mem hfind) ψ) hv
      · exact nomatch h
    · next cv value hfind =>
      split at h
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj h).symm
        exact delta_coreR m φ hcl hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, -, -, ht⟩ := m.wf _ (find?_mem hfind)
              exact (ht cv value rfl).1)
          (fun ψ => m.thm_ok cv value (find?_mem hfind) ψ) hv
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-! ## The reduction loop

`whnfStep` is three moves — head-normalize, accelerate a literal, unfold
one definition — and `whnfLoop` iterates it on its own budget.  The
budget induction is structural: it consumes the `whnfCore` claim at the
same knot level, `ReduceNatStepR`, and `denote_delta_stepR`, and the
accumulated derivation is a `Red.trans` chain (design §7.2's "the loop
is `Red.trans` chaining in the bridge"). -/

/-- The budget induction: every iteration of the reduction loop is a
reduction of the denotation. -/
theorem whnfLoop_claimR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsR mode m φ fuel)
    (hnat : ReduceNatStepR (mode := mode) m φ fuel) :
    ∀ (budget : Nat) {d : Nat} {Δ : List VExpr} {e e' : Expr} {v : VExpr},
      whnfLoop (pureFns mode env fuel) env d budget e = .ok e' →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e → CtxOkR mode m.cval env φ d Δ e →
      denote m.cval env φ d e = some v →
      ∃ v', denote m.cval env φ d e' = some v' ∧
        Red mode env m.cval φ Δ v v' := by
  intro budget
  induction budget with
  | zero =>
    intro d Δ e e' v h
    rw [whnfLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d Δ e e' v h hws hb hLb hC hv
    rw [whnfLoop, whnfStep] at h
    simp only [Bind.bind, Except.bind, whnfCore_def] at h
    cases hwc : whnfCore mode env fuel d e with
    | error err => rw [hwc] at h; exact nomatch h
    | ok e₁ =>
    rw [hwc] at h
    dsimp only at h
    obtain ⟨v₁, hv₁, hD₁, hws₁, hb₁, hLb₁, hC₁⟩ :=
      whnfCore_packageR m φ ihwc hwc hws hb hLb hC hv
    cases hrn : reduceNatP mode env fuel d e₁ with
    | error err => rw [reduceNat_fold] at h; rw [hrn] at h; exact nomatch h
    | ok o =>
    rw [reduceNat_fold] at h
    rw [hrn] at h
    dsimp only at h
    match o, h with
    | some e₂, h =>
      obtain ⟨w, hw, hD₂, hws₂, hb₂, hLb₂, hC₂⟩ :=
        hnat hrn hws₁ hb₁ hLb₁ hC₁ hv₁
      obtain ⟨v', hv', hD₃⟩ := ih h hws₂ hb₂ hLb₂ hC₂ hw
      exact ⟨v', hv', (hD₁.trans hD₂).trans hD₃⟩
    | none, h =>
      dsimp only at h
      -- delta, which changes no denotation at all
      cases hud : unfoldDefinition env e₁ with
      | none => rw [hud] at h; exact ⟨v₁, (Except.ok.inj h) ▸ hv₁, hD₁⟩
      | some e₂ =>
        rw [hud] at h
        dsimp only at h
        have hw₂ : denote m.cval env φ d e₂ = some v₁ :=
          denote_delta_stepR m φ hcl hud hv₁
        obtain ⟨v', hv', hD₃⟩ :=
          ih h (unfoldDefinition_WScoped m.wf hud hws₁)
            (unfoldDefinition_looseBVars m.wf hud hb₁)
            (fun l hl => hLb₁ l (unfoldDefinition_fvarLeaves m.wf hud l hl))
            (CtxOkR.of_subset (unfoldDefinition_fvarLeaves m.wf hud) hC₁) hw₂
        exact ⟨v', hv', hD₁.trans hD₃⟩

/-- **`WhnfClaimsR` at `fuel + 1`.**  The reduction loop run at its own
budget; `whnfBody` *is* the loop. -/
theorem whnf_claimsR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsR mode m φ fuel)
    (hnat : ReduceNatStepR (mode := mode) m φ fuel) :
    WhnfClaimsR mode m φ (fuel + 1) := by
  intro d e e' Δ h hws hb hLb hC v hv
  rw [whnf_succ, whnfBody] at h
  exact whnfLoop_claimR m φ hcl ihwc hnat whnfLoopFuel h hws hb hLb hC hv

end Setlec.SetR
