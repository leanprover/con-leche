import Setlec.SetP.IndFireP

/-!
# The truthfulness transport, at the reading (task #161, IND TIER part 7)

`annotS`'s transpose (`Install/IndStagesS.lean:2740`), and the last
stage of the `annotS` cluster: the applied rule right-hand side is
hereditarily truthful.  Its λ-tower is read by
`instLamsAt_denotePTele`, the fired spine's layer memberships come from
`annotMemP`, and `lamTowerStepP` descends.

**One delta, and it is the P tier's shape rather than v1's.**
`annotMemS` hands its caller a *membership* — argument `k`'s value in
the λ-tower's `k`-th slot — because at v1 the statement tower's slot
and the λ-tower's slot are literally identified.  `annotMemP` hands an
**equation plus a grading** instead (the part-5 design: `CtxOkP`'s
per-leaf obligation is semantic), so the transport composes it with
the statement tower's own chain memberships.  The environments line up
by `chainP_tail`: `fun j => (chainP V ρ zs) (j + (K - k))` *is*
`chainP V ρ (zs.take k)` at every `k < K`, with no lemma beyond the
index arithmetic.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.Semantics (AVExpr)
open Setlec (CheckMode Env Expr Name Level DefEqListOk)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

set_option maxHeartbeats 3200000 in
/-- **The truthfulness transport, at the reading** (`annotS`). -/
theorem annotTransportP {m : EnvS2Core V env} {F : Nat}
    (hclaims : DefEqClaims2P μ m φ F)
    {K : Nat}
    -- the public frame
    {pfvs : List Expr} (hPlen : pfvs.length = K)
    (hPshape : ∀ (i : Nat) (x : Expr), pfvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hPws : ∀ x ∈ pfvs, Expr.WScoped K x)
    (hPleafClosed : ∀ l, (∃ x ∈ pfvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ pfvs)
    (hlbP : ∀ (i : Nat) (nm : Name) (ty : Expr),
      Expr.fvar i nm ty ∈ pfvs → ty.looseBVarsBounded 0 = true)
    -- the statement tower and the ambient context
    {Γs : List AVExpr} {Δa : List AVExpr} (hΔalen : Δa.length = K)
    (hΔaent : ∀ i, i < K →
      Δa[K - 1 - i]? = some (Γs.getD (K - 1 - i) default))
    -- the per-position identification (`annotPFrameEqP`)
    (hIdent : ∀ i, i < K → ∃ Bi : AVExpr,
      denoteP m.acval env φ K
        (Expr.fvarTypeD (pfvs.getD i default)) = some Bi ∧
      ∀ ρ' : Nat → V, Sat2 V Δa ρ' →
        AnnotOkP V ρ' Bi ∧
          interp2 V (fun j => ρ' (j + (K - i)))
              (Γs.getD (K - 1 - i) default) = interp2 V ρ' Bi)
    -- the rule's right-hand side and its λ-tower run
    {rhsA : Expr} (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    {Ra : AVExpr} (hRa : denoteP m.acval env φ 0 rhsA = some Ra)
    (hokRa : ∀ σ : Nat → V, AnnotOkP V σ Ra)
    {ldomsL : List Expr} {lrest2 : Expr}
    (hinstLam : Expr.instLamsAt pfvs rhsA = some (ldomsL, lrest2))
    (hdeLam : DefEqListOk μ F env K (pfvs.map Expr.fvarTypeD) ldomsL)
    -- the fired spine
    {zs : List AVExpr} {ρ : Nat → V} (hzslen : zs.length = K)
    (hsat : Sat2 V Δa (chainP V ρ zs))
    (hmemZ : ∀ k, k < K →
      interp2 V ρ (zs.getD k default)
        ∈ˢ interp2 V (chainP V ρ (zs.take k))
          (Γs.getD (K - 1 - k) default))
    (hzsAnnot : ∀ w ∈ zs, AnnotOkP V ρ w) :
    AnnotOkP V ρ (AVExpr.mkAppN Ra zs) := by
  -- the rule's λ-tower, read at the public frame
  obtain ⟨Γlam, C, htowerLam, hΓlamLen, hCden, hdoms⟩ :=
    instLamsAt_denotePTele (acval := m.acval) (env := env) (φ := φ)
      pfvs hinstLam
      (fun i x hx => by
        obtain ⟨nm, ty, hx'⟩ := hPshape i x hx
        exact ⟨nm, ty, by rw [hx', Nat.zero_add]⟩) hRa
  rw [hPlen] at htowerLam hΓlamLen
  have hdomsLam : ∀ (i : Nat) (x : Expr), ldomsL[i]? = some x →
      denoteP m.acval env φ i x = some (Γlam.getD (K - 1 - i) default) := by
    intro i x hx
    have h := hdoms i x hx
    rwa [Nat.zero_add, hPlen] at h
  -- the per-position identification, transported to the λ-tower
  have hmemLam : ∀ k, k < K →
      interp2 V ρ (zs.getD k default)
        ∈ˢ interp2 V (chainP V ρ (zs.take k))
          (Γlam.getD (K - 1 - k) default) := by
    intro k hk
    have henvk : (fun j => (chainP V ρ zs) (j + (K - k)))
        = chainP V ρ (zs.take k) := by
      have h := chainP_tail (V := V) (ρ := ρ) (ws := zs)
        (i := K - 1 - k) (by rw [hzslen]; omega)
      rw [hzslen] at h
      rw [show K - 1 - (K - 1 - k) = k from by omega] at h
      rw [← h]
      funext j
      congr 1
      omega
    obtain ⟨-, heq⟩ := annotMemP hclaims hPlen hPshape hPws
      hPleafClosed hlbP hΔalen hΔaent hIdent hrhsw hrhsb hokRa
      hinstLam htowerLam hdomsLam hdeLam k hk (chainP V ρ zs) hsat
    rw [henvk] at heq
    rw [← heq]
    exact hmemZ k hk
  -- descend the λ-tower along the fired spine
  obtain ⟨-, -, -, -, hok⟩ := lamTowerStepP (V := V) (C := C) K
    (Nat.le_refl _) htowerLam hzslen hmemLam (hokRa ρ)
  have hok' := hok hzsAnnot
  rwa [show zs.take K = zs from
    List.take_of_length_le (Nat.le_of_eq hzslen)] at hok'

end Setlec.SetP
