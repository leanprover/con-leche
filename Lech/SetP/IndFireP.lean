import Lech.SetP.IndAnnotMemP

/-!
# The firing stage, at the reading (task #161, IND TIER part 7)

`fireS`'s transpose (`Install/IndStagesS.lean:1108`): the checked
`iota_j` equation, fired at the zipped chain — the theorem's inhabitant
applied along the fit lands in the interpreted `Eq`-spine, the spine
computes to the truth set through `eq_lawP`, and `mem_eqv` reads the
equation off.

Three deltas against v1, all of them the P tier's own currency:

* **the slot's universe membership is read top-down, not along the
  chain.**  v1 calls `annotOkV_descend` — the descent along the *value
  chain* — to grade the statement's body at `chainE V ρ zs`.  Part 4
  recorded why that shape cannot be transposed (`IndGradeP.lean`: the
  chain step charges for the arguments' gradings, which
  `RecRuleLawP`'s interp-equality half does not have).  The route that
  works is the one `annotOkP_tower_slot` already takes —
  `annotOkP_tower_body` below descends **top-down along the satisfying
  environment**, spending `Sat2` and asking the arguments for nothing;
* **the `Eq` former's product is at a positive kind**, and that is a
  computation, not a hypothesis: the pinned type's outer binder carries
  `PropWhen.never`, so its bit is `pwBit φ .never = 1`
  (`denoteP_forallE` reads the bit off the binder meta).  The squash
  branch of the app package is then refuted exactly as the part-6 probe
  refutes it (`eq_pt_of_mem_piR_zero` + `not_pt_mem_piR_pos`), so
  `piR_dom_unique` applies with no side condition;
* **the sides pack is a pair of recorded runs, not a derivation
  bundle.**  `sidesMemP` is four lines: `IotaRuns` carries
  `inferTypeCore lhsS` and `isDefEqCore … αS` outright, and
  `InferClaims2P`/`DefEqClaims2P` convert them at the frame's own
  context.  v1's `sidesMemS` had to rebuild three `CtxOkR`s and fire
  the quantified-context packs; here `ctxOkP_of_walked_openers` has
  already produced the context the stages share.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  isDefEqCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The tower's body, graded top-down -/

/-- **A tower's body is graded at any satisfying environment**
(`annotOkP_tower_slot`'s companion, same induction, same reason): the
`.pi` split's extension environment is `cons (ρ' q) (fun j => ρ' (j + q + 1))
= fun j => ρ' (j + q)` on the nose, so the descent spends the
satisfaction and charges the arguments nothing.

This is what replaces v1's `annotOkV_descend` at the firing stage: that
lemma descends along the *value chain* and would need the fired spine
graded — the premise `RecRuleLawP`'s interp-equality half deliberately
does not carry. -/
theorem annotOkP_tower_body :
    ∀ (k : Nat) {T : AVExpr} {Γ : List AVExpr} {R : AVExpr},
      PiTeleP k T Γ R → ∀ {ρ' : Nat → V},
      AnnotOkP V (fun j => ρ' (j + k)) T →
      (∀ q, q < k →
        ρ' q ∈ˢ interp2 V (fun j => ρ' (j + q + 1)) (Γ.getD q default)) →
      AnnotOkP V ρ' R := by
  intro k
  induction k with
  | zero =>
    intro T Γ R h ρ' hokT _
    cases h
    exact hokT
  | succ k ih =>
    intro T Γ R h ρ' hokT hmem
    obtain ⟨u, v, A, B, Γ', rfl, rfl, htail⟩ := h.succ_inv
    have hΓ'len : Γ'.length = k := htail.length
    have hgetA : (Γ' ++ [A]).getD k default = A := by
      rw [List.getD, List.getElem?_append_right (by omega), hΓ'len]
      simp
    have hokT' : AnnotOkP V (fun j => ρ' (j + k + 1))
        (AVExpr.pi u v A B) := hokT
    have hmemk : ρ' k ∈ˢ interp2 V (fun j => ρ' (j + k + 1)) A := by
      have := hmem k (by omega)
      rwa [hgetA] at this
    have henv : cons (ρ' k) (fun j => ρ' (j + k + 1))
        = (fun j => ρ' (j + k)) := by
      funext j
      cases j with
      | zero =>
        show cons (ρ' k) (fun j => ρ' (j + k + 1)) 0 = ρ' (0 + k)
        rw [cons_zero]
        congr 1
        omega
      | succ j =>
        show cons (ρ' k) (fun j => ρ' (j + k + 1)) (j + 1)
          = ρ' (j + 1 + k)
        rw [cons_succ]
        show ρ' (j + k + 1) = ρ' (j + 1 + k)
        congr 1
        omega
    have hokB : AnnotOkP V (fun j => ρ' (j + k)) B := by
      refine ⟨?_, ?_⟩
      · have h := ((AnnotOk2_pi V (fun j => ρ' (j + k + 1)) u v A B)
          ▸ hokT'.1).2 (ρ' k) hmemk
        rwa [henv] at h
      · have h := ((AnnotValidV_pi V (fun j => ρ' (j + k + 1)) u v A B)
          ▸ hokT'.2).2.1 (ρ' k) hmemk
        rwa [henv] at h
    have hgetΓ' : ∀ q, q < k →
        (Γ' ++ [A]).getD q default = Γ'.getD q default := by
      intro q hq
      rw [List.getD, List.getD, List.getElem?_append_left (by omega)]
    exact ih htail hokB (fun q hq => by
      have := hmem q (by omega)
      rwa [hgetΓ' q hq] at this)

/-- **The tower's body, graded at a `Sat2`-satisfied context.** -/
theorem annotOkP_tower_body_sat {k : Nat} {T : AVExpr} {Γ : List AVExpr}
    {R : AVExpr} (htower : PiTeleP k T Γ R) {ρ' : Nat → V}
    (hokT : AnnotOkP V (fun j => ρ' (j + k)) T) (hsat : Sat2 V Γ ρ') :
    AnnotOkP V ρ' R := by
  have hΓlen : Γ.length = k := htower.length
  refine annotOkP_tower_body k htower hokT (fun q hq => ?_)
  refine hsat q (Γ.getD q default) ?_
  rw [List.getD]
  rcases hg : Γ[q]? with _ | A
  · rw [List.getElem?_eq_none_iff] at hg; omega
  · rfl

/-! ## Applying along a fit, value-headed -/

/-- **An inhabited telescope's residual is inhabited along a fit** —
`TeleFitV.appN_val` at the reading, weakened from "the application
lands in the residual" to "the residual is nonempty", which is
**strictly what the firing stage spends**: `mem_eqv` reads the equation
off *any* member of the truth value.

The weakening is not a convenience, it is what makes the transpose
possible.  v1 applies the theorem's inhabitant along the fit through
`app_mem_piC`, which has no regime; `app_mem_piR`'s squash branch needs
the codomain fibres to be truth values, and that fact rides
`AnnotValidV`'s `.pi` clause — which the fit's *substituted* tower
`B.inst a` cannot carry, because `AnnotValidV_inst` charges for the
substituted argument's own validity and `RecRuleLawP`'s
interp-equality half deliberately carries no grading of the fired
spine (the part-4 finding, `IndGradeP.lean`).  Nonemptiness needs
neither: at `v = 0` the product **is** the truth value of "every
fibre is inhabited" (`piR_zero`), so membership hands the fibre's
inhabitant over directly. -/
theorem teleFitPA_nonempty {ρ : Nat → V} :
    ∀ {T rest : AVExpr} {as : List AVExpr},
      TeleFitPA V ρ T as rest →
      (∃ x : V, x ∈ˢ interp2 V ρ T) →
      ∃ y : V, y ∈ˢ interp2 V ρ rest := by
  intro T rest as h
  induction h with
  | nil => exact id
  | @cons u v A B rest a as hmem htail ih =>
    intro hx
    obtain ⟨x, hx⟩ := hx
    rw [interp2_pi] at hx
    refine ih ?_
    rw [interp2_inst0]
    by_cases hv : v = 0
    · subst hv
      rw [piR_zero] at hx
      exact of_mem_truthVal hx _ hmem
    · exact ⟨_, app_mem_piR_pos hv hx hmem⟩

/-! ## The `Eq` former's firing key -/

/-- **What the firing stage needs of the environment** (`EqFormerKeyV`
at the reading): the pinned `Eq` former's leaf is closed, and inhabits
its own type's reading, graded. -/
def EqFormerKeyP {env : Env} (m : EnvS2Core V env) (φ : Name → Nat) :
    Prop :=
  ∀ us : List Level,
    us.length = eqA.toConstantVal.levelParams.length →
    ∀ T : AVExpr,
      denoteP m.acval env φ 0
        (eqA.toConstantVal.type.instantiateLevelParams
          eqA.toConstantVal.levelParams us) = some T →
      ∀ ρ : Nat → V,
        interp2 V ρ (m.acval eqName
            (Level.substFn φ eqA.toConstantVal.levelParams us))
          ∈ˢ interp2 V ρ T ∧ AnnotOkP V ρ T

/-- A stored `Eq` gives the firing key — the two `EnvS2PM` type fields
at the pinned constant. -/
theorem eqFormerKeyP {env : Env} (mp : EnvS2PM V μ env)
    (heqfE : env.find? eqName = some eqA) :
    EqFormerKeyP mp.base2 φ := by
  intro us _hlen T hT ρ
  have hmem := Lech.Semantics.Env.find?_mem heqfE
  have hname := Lech.Semantics.Env.find?_name heqfE
  have hT' : denoteP mp.base2.acval env
      (Level.substFn φ eqA.toConstantVal.levelParams us) 0
      eqA.toConstantVal.type = some T := by
    rw [← denotePInstLevels]
    exact hT
  refine ⟨?_, mp.type_okP eqA hmem _ T hT' ρ⟩
  have h := mp.mem_typeP eqA hmem
    (Level.substFn φ eqA.toConstantVal.levelParams us) T hT' ρ
  rwa [hname] at h

/-! ## The firing stage -/

set_option maxHeartbeats 3200000 in
/-- **The firing stage, at the reading** (`fireS`): the checked
equation, fired at the zipped chain.  The statement's residual is
inhabited along the fit (`teleFitPA_nonempty`), it computes to the
interpreted equation spine through `eq_lawP`, and `mem_eqv` reads the
equation off.

The equation slot's universe membership — v1's one place for
`annotOkV_descend` — is produced here by `annotOkP_tower_body_sat`
(top-down along the satisfying environment) plus graph rigidity of the
pinned `Eq` former, whose product is positive-kind because the stored
type's outer binder carries `PropWhen.never`. -/
theorem fireP {m : EnvS2Core V env} {ψ' : Name → Nat}
    (hkey : EqFormerKeyP m ψ') (heqlaw : EqLawP m)
    (heqfE : env.find? eqName = some eqA)
    {K : Nat}
    {Tstmt : AVExpr} {Γs : List AVExpr} {Rbody : AVExpr}
    (htowerS : PiTeleP K Tstmt Γs Rbody)
    (hstmtAnnot : ∀ σ : Nat → V, AnnotOkP V σ Tstmt)
    (hstmtInhab : ∀ σ : Nat → V, ∃ pv : V, pv ∈ˢ interp2 V σ Tstmt)
    {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    (hRbody : denoteP m.acval env ψ' K tbody = some Rbody)
    (htbody : tbody
      = Expr.mkAppN (.const eqName [ℓA]) [αS, lhsS, rhsS])
    {zs : List AVExpr} {ρ : Nat → V}
    (hsides : ∀ vα vL vR : AVExpr,
      denoteP m.acval env ψ' K αS = some vα →
      denoteP m.acval env ψ' K lhsS = some vL →
      denoteP m.acval env ψ' K rhsS = some vR →
      interp2 V (chainP V ρ zs) vL ∈ˢ interp2 V (chainP V ρ zs) vα ∧
        interp2 V (chainP V ρ zs) vR ∈ˢ interp2 V (chainP V ρ zs) vα)
    (hzslen : zs.length = K)
    (hsat : Sat2 V Γs (chainP V ρ zs))
    (hfit : TeleFitPA V ρ Tstmt zs
      (Lech.SetP.AVExpr.instSeq zs (K - 1) Rbody)) :
    ∃ vα vL vR : AVExpr,
      denoteP m.acval env ψ' K αS = some vα ∧
      denoteP m.acval env ψ' K lhsS = some vL ∧
      denoteP m.acval env ψ' K rhsS = some vR ∧
      interp2 V (chainP V ρ zs) vL
        = interp2 V (chainP V ρ zs) vR := by
  -- read the equation spine apart
  rw [htbody] at hRbody
  obtain ⟨vEq, vs3, hvEq, hsp3, rfl⟩ := denoteP_mkAppN_inv hRbody
  obtain ⟨vα, vL, vR, rfl, hvα, hvL, hvR⟩ : ∃ vα vL vR,
      vs3 = [vα, vL, vR] ∧
      denoteP m.acval env ψ' K αS = some vα ∧
      denoteP m.acval env ψ' K lhsS = some vL ∧
      denoteP m.acval env ψ' K rhsS = some vR := by
    cases hsp3 with
    | cons hα htail =>
      cases htail with
      | cons hL htail2 =>
        cases htail2 with
        | cons hR htail3 =>
          cases htail3 with
          | nil => exact ⟨_, _, _, rfl, hα, hL, hR⟩
  -- the head is the stored `Eq`'s annotated valuation
  have hvEq' : vEq = m.acval eqName
      (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA]) := by
    rw [denoteP_const heqfE
      (show ([ℓA] : List Level).length
        = eqA.toConstantVal.levelParams.length from rfl)] at hvEq
    exact (Option.some.inj hvEq).symm
  -- the statement body, graded at the fired chain (top-down)
  have hokBody : AnnotOkP V (chainP V ρ zs)
      (AVExpr.mkAppN vEq [vα, vL, vR]) :=
    annotOkP_tower_body_sat htowerS (hstmtAnnot _) hsat
  -- the pinned `Eq` type's reading at the stored level
  have hbit : pwBit ψ' Lech.PropWhen.never = 1 := rfl
  have hTden : denoteP m.acval env ψ' 0
      (eqA.toConstantVal.type.instantiateLevelParams
        eqA.toConstantVal.levelParams [ℓA])
      = some (.pi 0 1 (.sort (ℓA.eval ψ'))
          (.pi 0 1 (.bvar 0) (.pi 0 1 (.bvar 1) (.sort 0)))) := by
    have hinst : eqA.toConstantVal.type.instantiateLevelParams
        eqA.toConstantVal.levelParams [ℓA]
        = .forallE .anonymous (.sort ℓA)
            (.forallE .anonymous (.bvar 0)
              (.forallE .anonymous (.bvar 1)
                (.sort .zero) ⟨.default, .never⟩)
              ⟨.default, .never⟩) ⟨.default, .never⟩ := rfl
    have hb1 : (Expr.forallE .anonymous (.bvar 0)
        (.forallE .anonymous (.bvar 1)
          (.sort .zero) ⟨.default, .never⟩) ⟨.default, .never⟩).instantiate1
        (.fvar 0 .anonymous (.sort ℓA))
        = .forallE .anonymous
            (.fvar 0 .anonymous (.sort ℓA))
            (.forallE .anonymous
              (.fvar 0 .anonymous (.sort ℓA))
              (.sort .zero) ⟨.default, .never⟩)
            ⟨.default, .never⟩ := rfl
    have hb2 : (Expr.forallE .anonymous
        (.fvar 0 .anonymous (.sort ℓA))
        (.sort .zero) ⟨.default, .never⟩).instantiate1
        (.fvar 1 .anonymous
          (.fvar 0 .anonymous (.sort ℓA)))
        = .forallE .anonymous
            (.fvar 0 .anonymous (.sort ℓA))
            (.sort .zero) ⟨.default, .never⟩ := rfl
    have hb3 : (Expr.sort .zero).instantiate1
        (.fvar 2 .anonymous
          (.fvar 0 .anonymous (.sort ℓA)))
        = .sort .zero := rfl
    rw [hinst, denoteP_forallE, denoteP_sort, hb1, denoteP_forallE,
      denoteP_fvar, hb2, denoteP_forallE, denoteP_fvar, hb3,
      denoteP_sort]
    simp only [hbit]
    rfl
  have hmemEq := hkey [ℓA] rfl _ hTden (chainP V ρ zs)
  have hEqIn2 : interp2 V (chainP V ρ zs) vEq
      ∈ˢ piR 1 (univ (ℓA.eval ψ'))
        (fun x => interp2 V (cons x (chainP V ρ zs))
          (AVExpr.pi 0 1 (.bvar 0) (.pi 0 1 (.bvar 1) (.sort 0)))) := by
    have h3 := hmemEq.1
    rw [interp2_pi, interp2_sort] at h3
    rw [hvEq']
    exact h3
  -- the slot's universe membership, by graph rigidity
  have hαuniv : interp2 V (chainP V ρ zs) vα
      ∈ˢ (univ (ℓA.eval ψ') : V) := by
    have hokB2 := hokBody.1
    rw [show AVExpr.mkAppN vEq [vα, vL, vR]
        = .app (.app (.app vEq vα) vL) vR from rfl,
      AnnotOk2_app] at hokB2
    have h1 := hokB2.1
    rw [AnnotOk2_app] at h1
    have h2 := h1.1
    rw [AnnotOk2_app] at h2
    obtain ⟨-, -, v', A', B', hEqIn, hαIn, -⟩ := h2
    have hv' : v' ≠ 0 := by
      intro hz
      subst hz
      exact not_pt_mem_piR_pos (V := V) Nat.one_ne_zero
        (by rw [← eq_pt_of_mem_piR_zero hEqIn]; exact hEqIn2)
    have hAA : univ (ℓA.eval ψ') = A' :=
      piR_dom_unique Nat.one_ne_zero hv' hEqIn2 hEqIn
    rw [hAA]
    exact hαIn
  -- the sides' memberships, at the slot the rigidity just named
  obtain ⟨hLmem, hRmem⟩ := hsides vα vL vR hvα hvL hvR
  -- the residual computes to the interpreted equation
  have hEqcl : ∀ k : Nat, AVExpr.liftN 1 vEq k = vEq := by
    rw [hvEq']
    exact m.acval_closed _ _
  have hlaw := (heqlaw heqfE
    (Level.substFn ψ' eqA.toConstantVal.levelParams [ℓA])).1
  have hresid : interp2 V ρ
      (Lech.SetP.AVExpr.instSeq zs (K - 1)
        (AVExpr.mkAppN vEq [vα, vL, vR]))
      = eqv (interp2 V (chainP V ρ zs) vL)
        (interp2 V (chainP V ρ zs) vR) := by
    rw [show K - 1 = zs.length - 1 from by rw [hzslen],
      instSeqP_mkAppN, instSeqP_eq_self_of_closed hEqcl]
    show interp2 V ρ (AVExpr.mkAppN vEq
        [Lech.SetP.AVExpr.instSeq zs (zs.length - 1) vα,
         Lech.SetP.AVExpr.instSeq zs (zs.length - 1) vL,
         Lech.SetP.AVExpr.instSeq zs (zs.length - 1) vR]) = _
    show SetTheory.app (SetTheory.app (SetTheory.app
        (interp2 V ρ vEq)
        (interp2 V ρ (Lech.SetP.AVExpr.instSeq zs (zs.length - 1) vα)))
        (interp2 V ρ (Lech.SetP.AVExpr.instSeq zs (zs.length - 1) vL)))
        (interp2 V ρ (Lech.SetP.AVExpr.instSeq zs (zs.length - 1) vR))
      = _
    rw [interp2_instSeq, interp2_instSeq, interp2_instSeq, hvEq']
    exact hlaw ρ _ _ _ hαuniv hLmem hRmem
  -- fire: the residual is inhabited, and it is a truth value
  obtain ⟨y, hy⟩ := teleFitPA_nonempty hfit (hstmtInhab ρ)
  rw [hresid] at hy
  exact ⟨vα, vL, vR, hvα, hvL, hvR, mem_eqv hy⟩

/-! ## The certified sides' memberships -/

/-- **The certified sides' memberships, at the reading** (`sidesMemS`):
the recorded `checkIotaSidesTy` runs, converted at the frame's own
context, put both equation sides in the slot — and grade all three.

Where v1 rebuilds three `CtxOkR`s and fires quantified-context packs,
the P tier reads the two runs `IotaRuns` records straight through
`InferClaims2P`/`DefEqClaims2P`; the context is the stages' shared
one. -/
theorem sidesMemP {m : EnvS2Core V env} {F : Nat} {ψ' : Name → Nat}
    (hinfer : InferClaims2P μ m ψ' F) (hclaims : DefEqClaims2P μ m ψ' F)
    {d : Nat} {Δa : List AVExpr} {αS lhsS rhsS : Expr}
    (hctxα : CtxOkP m ψ' d Δa αS)
    (hctxL : CtxOkP m ψ' d Δa lhsS)
    (hctxR : CtxOkP m ψ' d Δa rhsS)
    (hwsα : Expr.WScoped d αS) (hbα : αS.looseBVarsBounded 0 = true)
    (hLα : Expr.LeavesBounded αS)
    (hwsL : Expr.WScoped d lhsS) (hbL : lhsS.looseBVarsBounded 0 = true)
    (hLL : Expr.LeavesBounded lhsS)
    (hwsR : Expr.WScoped d rhsS) (hbR : rhsS.looseBVarsBounded 0 = true)
    (hLR : Expr.LeavesBounded rhsS)
    {vα vL vR : AVExpr}
    (hvα : denoteP m.acval env ψ' d αS = some vα)
    (hvL : denoteP m.acval env ψ' d lhsS = some vL)
    (hvR : denoteP m.acval env ψ' d rhsS = some vR)
    -- the slot's own grading (the statement body's, descended)
    (hokα : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ vα)
    {tl tr : Expr}
    (hInfL : inferTypeCore μ env F d lhsS = .ok tl)
    (hDeqL : isDefEqCore μ env F d tl αS = .ok true)
    (hInfR : inferTypeCore μ env F d rhsS = .ok tr)
    (hDeqR : isDefEqCore μ env F d tr αS = .ok true)
    {tla tra : AVExpr}
    (htla : denoteP m.acval env ψ' d tl = some tla)
    (htra : denoteP m.acval env ψ' d tr = some tra)
    (hctxTl : CtxOkP m ψ' d Δa tl) (hctxTr : CtxOkP m ψ' d Δa tr)
    (hwsTl : Expr.WScoped d tl) (hbTl : tl.looseBVarsBounded 0 = true)
    (hLTl : Expr.LeavesBounded tl)
    (hwsTr : Expr.WScoped d tr) (hbTr : tr.looseBVarsBounded 0 = true)
    (hLTr : Expr.LeavesBounded tr) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ vL) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ vR) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ vL ∈ˢ interp2 V ρ vα ∧
        interp2 V ρ vR ∈ˢ interp2 V ρ vα := by
  obtain ⟨hokL, hokTl, hmemL⟩ :=
    hinfer hInfL hwsL hbL hLL hctxL hvL htla
  obtain ⟨hokR, hokTr, hmemR⟩ :=
    hinfer hInfR hwsR hbR hLR hctxR hvR htra
  refine ⟨hokL, hokR, fun ρ hρ => ⟨?_, ?_⟩⟩
  · have heq := hclaims hDeqL hwsTl hbTl hLTl hwsα hbα hLα hctxTl hctxα
      htla hvα hokTl hokα ρ hρ
    exact heq ▸ hmemL ρ hρ
  · have heq := hclaims hDeqR hwsTr hbTr hLTr hwsα hbα hLα hctxTr hctxα
      htra hvα hokTr hokα ρ hρ
    exact heq ▸ hmemR ρ hρ

end Lech.SetP
