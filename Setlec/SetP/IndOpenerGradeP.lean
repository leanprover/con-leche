import Setlec.SetP.IndPinGradeP

/-!
# The applied reduct at the frame's own openers (task #161, IND TIER
part 8)

`reductP`'s third exposure, `hokApp`, discharged once and for all: the
rule's right-hand side applied to the *statement frame's own openers*
is hereditarily truthful at every satisfying environment.

The plain bottom (part 7) proves this inline.  The nested bottom
cannot afford to: `omega`'s case splitting over `List.take`/`drop`/
`append` length atoms is exponential in how many are in scope, the
nested spines put enough more of them there that the same block runs
two orders of magnitude slower, and this is the block with the most
arithmetic side conditions in the tier.  Extracting it is the fix that
scales — a stage lemma's context is exactly its premise set.
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
/-- **The applied reduct, graded at the frame's own openers** — the
truthfulness transport fired at the *opener* spine, which is exactly
`reductP`'s `hokApp` premise.

`reductP`'s docstring predicted this ("once the row lands, `hokApp` is
the truthfulness transport's own output at the frame's openers"), with
one cost it did not name: the opener chain `chainP V σ bvs` is **not**
`σ` — it agrees with `σ` below `K` and shifts above it — so two
environment congruences are owed.  Both are free once the statement
tower's slot `K - 1 - m` is known bounded by `m`
(`denote_bvarsBelow` on the erasure, via `denoteP_erase`), because
every environment the congruence touches sits below that bound:
`interp2_congr_below` crosses them.

Extracted from the plain bottom's inline block at part 8, because the
*nested* bottom cannot afford it inline: `omega`'s case splitting on
`List.take`/`drop`/`append` length atoms is exponential in the number
of such atoms in scope, and the nested bottom carries enough more of
them (the pin spines) that the same block costs two orders of
magnitude more there.  A stage lemma is the fix that scales — its
context is its premise set. -/
theorem annotOpenersP {m : EnvS2Core V env} {F : Nat}
    (hclaims : DefEqClaims2P μ m φ F)
    {f : Name → Name} (hroT : RenameOkP m.acval env f)
    {K : Nat}
    -- the statement frame and its tower
    {fvs : List Expr} (hfvslen : fvs.length = K)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped K x)
    (hlbFvs : ∀ (i : Nat) (nm : Name) (ty : Expr),
      Expr.fvar i nm ty ∈ fvs → ty.looseBVarsBounded 0 = true)
    {Γs : List AVExpr} (hΓslen : Γs.length = K)
    (hdomsS0 : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteP m.acval env φ i (Expr.fvarTypeD x)
        = some (Γs.getD (K - 1 - i) default))
    (hΔaent : ∀ i, i < K →
      Γs[K - 1 - i]? = some (Γs.getD (K - 1 - i) default))
    -- the public λ-frame (`annotTransportP`'s own premises)
    {pfvs : List Expr} (hPlen : pfvs.length = K)
    (hPshape : ∀ (i : Nat) (x : Expr), pfvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hPws : ∀ x ∈ pfvs, Expr.WScoped K x)
    (hPleafClosed : ∀ l, (∃ x ∈ pfvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ pfvs)
    (hlbP : ∀ (i : Nat) (nm : Name) (ty : Expr),
      Expr.fvar i nm ty ∈ pfvs → ty.looseBVarsBounded 0 = true)
    (hIdent : ∀ i, i < K → ∃ Bi : AVExpr,
      denoteP m.acval env φ K
        (Expr.fvarTypeD (pfvs.getD i default)) = some Bi ∧
      ∀ ρ' : Nat → V, Sat2 V Γs ρ' →
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
    (hdeLam : DefEqListOk μ F env K (pfvs.map Expr.fvarTypeD) ldomsL) :
    ∀ σ : Nat → V, Sat2 V Γs σ → ∀ ba : AVExpr,
      denoteP m.acval env φ K
        (Expr.mkAppN (rhsA.renameConsts f) fvs) = some ba →
      AnnotOkP V σ ba := by
  have hΓsBnd : ∀ mIdx, mIdx < K →
      VExpr.bvarsBelow mIdx (Γs.getD (K - 1 - mIdx) default).erase := by
    intro mIdx hmIdx
    rcases hx : fvs[mIdx]? with _ | x
    · rw [List.getElem?_eq_none_iff, hfvslen] at hx; omega
    obtain ⟨nm, ty, rfl⟩ := hshapeS mIdx x hx
    have hmem := List.mem_of_getElem? hx
    have hws : Expr.WScoped mIdx ty := by
      have h := hwsFvs _ hmem
      simp only [Expr.WScoped] at h
      exact h.2
    have hb := hlbFvs mIdx nm ty hmem
    have hden : denoteP m.acval env φ mIdx ty
        = some (Γs.getD (K - 1 - mIdx) default) := hdomsS0 mIdx _ hx
    exact denote_bvarsBelow m.cval_closed mIdx ty hws hb
      (denoteP_erase m.acval_erase mIdx ty hden)
  obtain ⟨bvs, hbvslen, hbvsel⟩ : ∃ bvs : List AVExpr,
      bvs.length = K ∧
      ∀ k, k < K →
        bvs[k]? = some (AVExpr.bvar (K - 1 - k)) := by
    refine ⟨(List.range (K)).map
        (fun j => AVExpr.bvar (K - 1 - j)),
      by rw [List.length_map, List.length_range], fun k hk => ?_⟩
    rw [List.getElem?_map, List.getElem?_range hk]
    rfl
  have hbvsgetD : ∀ k, k < K →
      bvs.getD k default = AVExpr.bvar (K - 1 - k) := by
    intro k hk
    rw [List.getD, hbvsel k hk]
    rfl
  have hspBvs : DenoteSpineP m.acval env φ
      (K) fvs bvs := by
    refine DenoteSpineP.of_getD fvs bvs (by rw [hfvslen, hbvslen]) ?_
    intro q hq
    rw [hfvslen] at hq
    rcases hx : fvs[q]? with _ | x
    · rw [List.getElem?_eq_none_iff, hfvslen] at hx; omega
    obtain ⟨nm, ty, rfl⟩ := hshapeS q x hx
    rw [show fvs.getD q default = Expr.fvar q nm ty from by
        rw [List.getD, hx]; rfl, hbvsgetD q hq]
    exact denoteP_fvar m.acval (K) q nm ty
  have hchainbvs : ∀ (τ : Nat → V) (i : Nat), i < K →
      chainP V τ bvs i = τ i := by
    intro τ i hi
    rw [chainP_lt (by rw [hbvslen]; exact hi), hbvslen,
      hbvsgetD (K - 1 - i) (by omega),
      show K - 1 - (K - 1 - i) = i from by omega]
    rfl
  have hRacl : ∀ k : Nat, Ra.liftN 1 k = Ra := fun k =>
    denoteP_closed m.acval_erase m.cval_closed
      hrhsw hrhsb hRa 1 k
  have hrhsRw : (rhsA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]; exact hrhsw
  have hRaK : denoteP m.acval env φ
      (K) (rhsA.renameConsts f) = some Ra := by
    refine denoteP_depth_of_closed m.acval_closed hrhsRw hRacl
      ?_ (K)
    rw [denoteP_renameConsts hroT]
    exact hRa
  have hbaEq : denoteP m.acval env φ
      (K) (Expr.mkAppN (rhsA.renameConsts f) fvs)
      = some (AVExpr.mkAppN Ra bvs) := denoteP_mkAppN_of fvs hRaK hspBvs
  intro σ hσ ba hba
  obtain rfl : ba = AVExpr.mkAppN Ra bvs :=
    Option.some.inj (hba.symm.trans hbaEq)
  have hsatB : Sat2 V Γs (chainP V σ bvs) := by
    intro i Aa hi
    have hiK : i < K := by
      rcases Nat.lt_or_ge i (K) with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by rw [hΓslen]; omega)] at hi
        exact nomatch hi
    obtain rfl : Aa = Γs.getD i default := by
      rw [List.getD, hi]
      rfl
    have hbnd : VExpr.bvarsBelow (K - 1 - i)
        (Γs.getD i default).erase := by
      have h := hΓsBnd (K - 1 - i) (by omega)
      rwa [show K - 1 - (K - 1 - i) = i from by omega] at h
    rw [hchainbvs σ i hiK,
      interp2_congr_below V (Γs.getD i default) (K - 1 - i)
        (fun j => chainP V σ bvs (j + i + 1)) (fun j => σ (j + i + 1))
        hbnd (fun j hj => hchainbvs σ (j + i + 1) (by omega))]
    exact hσ i _ hi
  have hmemZB : ∀ k, k < K →
      interp2 V σ (bvs.getD k default)
        ∈ˢ interp2 V (chainP V σ (bvs.take k))
          (Γs.getD (K - 1 - k) default) := by
    intro k hk
    have htklen : (bvs.take k).length = k := by
      rw [List.length_take, hbvslen]; omega
    rw [hbvsgetD k hk]
    show σ (K - 1 - k) ∈ˢ _
    rw [interp2_congr_below V (Γs.getD (K - 1 - k) default) k
      (chainP V σ (bvs.take k))
      (fun j => σ (j + (K - 1 - k) + 1)) (hΓsBnd k hk)
      (fun j hj => by
        rw [chainP_lt (by rw [htklen]; omega), htklen,
          show (bvs.take k).getD (k - 1 - j) default
            = AVExpr.bvar (K - 1 - (k - 1 - j)) from by
            rw [List.getD, List.getElem?_take_of_lt (by omega),
              hbvsel (k - 1 - j) (by omega)]
            rfl]
        show σ (K - 1 - (k - 1 - j)) = σ (j + (K - 1 - k) + 1)
        congr 1
        omega)]
    exact hσ (K - 1 - k) _ (hΔaent k hk)
  exact annotTransportP hclaims hPlen hPshape
    hPws hPleafClosed hlbP hΓslen hΔaent hIdent hrhsw hrhsb hRa hokRa hinstLam hdeLam hbvslen hsatB hmemZB
    (fun w hw => by
      obtain ⟨q, hq⟩ := List.getElem?_of_mem hw
      have hqlt : q < K := by
        have := (List.getElem?_eq_some_iff.mp hq).1
        rw [hbvslen] at this; exact this
      rw [hbvsel q hqlt] at hq
      obtain rfl : w = AVExpr.bvar (K - 1 - q) :=
        (Option.some.inj hq).symm
      exact ⟨by simp, by simp⟩)


end Setlec.SetP
