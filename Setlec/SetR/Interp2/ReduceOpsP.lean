import Setlec.SetR.Interp2.NatEqsP
import Setlec.SetR.Interp2.CapstoneP
import Setlec.SetR.Interp2.ErasePwInv
import Setlec.SetR.Interp2.DivModP

/-!
# The compiler-trust identity law, established at `interp2` from the
recorded certificate run (task #161, ENDGAME D — the pin bundle's
last field)

The ENDGAME C seal named exactly one blocker for `DeclAxiomR`'s
`ofReduce*` branch: the innermost membership obligation is `op a = a`,
which is `EnvS.reduce_ops` (`ReduceOpsV`) — a **v1** field with no
`EnvS2PM` mirror, and none derivable (the transfer would be an
erasure factoring of `interp2` through `interp`, refuted at the very
λ-nodes the operation's leaf is made of).  `ReduceOpsP`
(`Annot/EnvS2P.lean`) is that mirror, and this file is its supplier.

## The route: the run-certificate move, fifth execution

`checkReducePin` runs the identity certificate and `ReducePinR`
**records the run** (`SetR/Decl.lean:270`):

> `isDefEqCore μ env F 1 (.app valA (reduceCertVar c)) (reduceCertVar c)
> = .ok true`

— `isDefEq` at depth `1`, applied side first, over the canonical
one-entry element context `reduceCertVar c = .fvar 0 _ (reduceElemTy c)`.
`DefEqClaims2P` at the **pre-insertion** environment turns that run
into an `interp2` equality of the two sides' readings, and the two
readings are `.app (A ψ) (.bvar 0)` and `.bvar 0`: the law falls out
by `interp2_app` and leaf closedness.

This is `NatEqsP.lean`'s species at a one-variable context instead of
two, and the element type is a stored *level-free constant*
(`reduceElemTy c`, whose `reduceElemOk` guard stores it), so the
context kit collapses to `elemAP`/`sat2_elemCtx` below.

## What the conversion costs: the gradings

`DefEqClaims2P` compares **graded** readings.  The certificate
variable's side is free (`AnnotOkP` of a `.bvar` is `True`); the
applied side's `AnnotOk2` app clause needs the *applied* membership

> `∃ v A' B', interp2 ρ (A ψ) ∈ˢ piR v A' B' ∧ x ∈ˢ A' ∧
>   (v = 0 → ∀ y ∈ˢ A', B' y ∈ˢ univZero)`

and every part of it is already established at the install:

* the pin fixes the stored type to `.forallE _ (.const E []) (.const E [])
  mb₀` **on the nose** below the binder meta — both erasures fix a
  `.const` (the `trustCompiler` branch's lesson, reused) — so the
  type's reading is `.pi 0 (pwBit ψ mb₀.pw) (acval E ψ) (acval E ψ)`
  and `interp2` of it is a `piR` over the element set;
* the `piR` membership is the constant's own `mem_typeP` obligation
  (`hmemA`, which `harvestOpaqueP` proves anyway);
* the `v = 0` fibre clause is the type reading's **`AnnotValidV` `pi`
  third component** — `htyOk`'s own content.  So **no bit is needed**:
  the regime datum `mb₀.pw` stays abstract throughout, exactly as the
  literal tier found (`NatEqsP.lean`'s "no bit positivity is ever
  needed"), and the doctrine that bits are never taken from a
  metatheorem is not even approached.

The preservation half is `reduceOpsP_cons_fresh` (`DivModP.lean`,
beside its `eq_lawP` sibling — the law mentions two stored leaves, so
it crosses every cons that is neither of them).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## The one-entry element context -/

/-- The element type's leaf at an assignment (the reduce operations'
element inductives — `Nat`, `Bool` — are stored level-free, so the
spelling is the plain assignment). -/
def elemAP {env : Env} (m : EnvS2Core V env) (c : Name)
    (ψ : Name → Nat) : AVExpr :=
  m.acval (Setlec.reduceElemName c) ψ

/-- The certificate's context: one slot, the element type. -/
def elemCtx {env : Env} (m : EnvS2Core V env) (c : Name)
    (ψ : Name → Nat) : List AVExpr :=
  [elemAP m c ψ]

/-- One element member satisfies the one-variable context (the leaf
reading collapses by closedness). -/
theorem sat2_elemCtx (m : EnvS2Core V env) {c : Name} {ψ : Name → Nat}
    {ρ : Nat → V} {x : V} (hx : x ∈ˢ interp2 V ρ (elemAP m c ψ)) :
    Sat2 V (elemCtx m c ψ) (cons x ρ) := by
  intro i Aa hi
  match i with
  | 0 =>
    obtain rfl : elemAP m c ψ = Aa := by simpa [elemCtx] using hi
    show x ∈ˢ interp2 V _ (m.acval (Setlec.reduceElemName c) ψ)
    rw [acval_interp2_closedC m _ ψ _ ρ]
    exact hx

/-! ## The pinned operation type, inverted -/

/-- **The reduce operation's pinned type, inverted through both
erasures.**  The domain and the codomain are the *same* bare constant,
and both erasures fix a `.const`, so the pin leaves exactly the binder
name and the binder meta free — and neither is ever read below. -/
theorem reduceOp_shapeS {c : Name} {type' : Expr}
    (hc : c ∈ Setlec.reduceOpNames)
    (h : type'.erasePw.eraseNames
      = (Setlec.reduceOpCvA c).type.erasePw.eraseNames) :
    ∃ n₀ mb₀, type' = .forallE n₀ (Setlec.reduceElemTy c)
      (Setlec.reduceElemTy c) mb₀ := by
  have hcases : c = Setlec.reduceNatName ∨ c = Setlec.reduceBoolName := by
    simpa [Setlec.reduceOpNames] using hc
  have hshape : (Setlec.reduceOpCvA c).type.erasePw.eraseNames
      = .forallE Setlec.Name.anonymous
          (Setlec.reduceElemTy c) (Setlec.reduceElemTy c)
          ⟨.default, .never⟩ := by
    rcases hcases with rfl | rfl <;>
      simp [Setlec.reduceOpCvA, Setlec.reduceNatCvA,
        Setlec.reduceBoolCvA, Setlec.reduceElemTy, Setlec.reduceNatName,
        Setlec.reduceBoolName, Setlec.natName, Setlec.boolName,
        Expr.erasePw, Expr.eraseNames]
  rw [hshape] at h
  obtain ⟨n', ty', b', m', rfl, hty', hb'⟩ := erasePwNames_forallE_invS h
  have hE : Setlec.reduceElemTy c
      = .const (Setlec.reduceElemName c) [] := by
    rcases hcases with rfl | rfl <;>
      simp [Setlec.reduceElemTy, Setlec.reduceElemName,
        Setlec.reduceNatName, Setlec.reduceBoolName, Setlec.natName,
        Setlec.boolName]
  rw [hE] at hty' hb'
  obtain rfl := erasePwNames_const_invS hty'
  obtain rfl := erasePwNames_const_invS hb'
  exact ⟨n', m', by rw [hE]⟩

/-- **The element inductive is stored level-free.**  `reduceElemOk`'s
two branches: the pinned `Nat` basis, and a `Bool` matching its shape
pin (whose `levelParams` conjunct `matchesPin` compares on the
nose). -/
theorem reduceElem_storedS {c : Name} (hc : c ∈ Setlec.reduceOpNames)
    (h : Setlec.reduceElemOk env c = true) :
    ∃ ciE, env.find? (Setlec.reduceElemName c) = some ciE ∧
      ciE.toConstantVal.levelParams = [] := by
  have hcases : c = Setlec.reduceNatName ∨ c = Setlec.reduceBoolName := by
    simpa [Setlec.reduceOpNames] using hc
  rcases hcases with rfl | rfl
  · rw [show Setlec.reduceElemName Setlec.reduceNatName
        = Setlec.natName from by simp [Setlec.reduceElemName]]
    simp only [Setlec.reduceElemOk, reduceIte, decide_eq_true_eq] at h
    exact ⟨Setlec.natA, h, rfl⟩
  · rw [show Setlec.reduceElemName Setlec.reduceBoolName
        = Setlec.boolName from by
      simp [Setlec.reduceElemName, Setlec.reduceNatName,
        Setlec.reduceBoolName]]
    simp only [Setlec.reduceElemOk,
      if_neg (show Setlec.reduceBoolName ≠ Setlec.reduceNatName from by
        simp [Setlec.reduceNatName, Setlec.reduceBoolName])] at h
    cases hfB : env.find? Setlec.boolName with
    | none => rw [hfB] at h; exact nomatch h
    | some ciB =>
      rw [hfB] at h
      cases ciB with
      | indInfo cvB caps =>
        refine ⟨.indInfo cvB caps, rfl, ?_⟩
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          decide_eq_true_eq] at h
        exact h.1.2
      | _ => exact nomatch h

/-! ## The certificate variable's syntactic package -/

/-- The certificate variable's leaf list: one leaf at index `0`, whose
annotation is the element type (a bare constant, so the hereditary
recursion stops there). -/
theorem reduceCertVar_fvarLeaves (c : Name) :
    (Setlec.reduceCertVar c).fvarLeaves
      = [(0, Setlec.Name.anonymous.str "a", Setlec.reduceElemTy c)] := by
  have hE : Setlec.reduceElemTy c
      = .const (Setlec.reduceElemName c) [] := by
    unfold Setlec.reduceElemTy Setlec.reduceElemName
    split <;> simp [Setlec.natName, Setlec.boolName]
  simp [Setlec.reduceCertVar, hE, Expr.fvarLeaves]

/-! ## The establishment -/

/-- **`ReduceOpsP` at a compiler-trust opaque's own install.**  The
recorded identity-certificate run, converted through `DefEqClaims2P` at
the pre-insertion environment over the one-entry element context; every
other stored reduce operation crosses by `reduceOpsP_entry_cons`.  See
the module docstring for the route and for why no regime bit is ever
read. -/
theorem reduceOpsP_install (hμ : μ.verified = true)
    (mp : EnvS2PM V μ env) {F : Nat}
    {cv : ConstantVal} {value type' value' : Expr}
    {A Ta : (Name → Nat) → AVExpr}
    (hfresh : env.find? cv.name = none)
    (hvf' : value'.hasFvar = false)
    (hbv' : value'.looseBVarsBounded 0 = true)
    (hannv : Setlec.annotateCore μ env F 0 value = .ok value')
    (hA : ∀ ψ : Name → Nat,
      denoteP mp.base2.acval env ψ 0 value' = some (A ψ))
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValidV V ρ (A ψ))
    (hTa : ∀ ψ : Name → Nat,
      denoteP mp.base2.acval env ψ 0 type' = some (Ta ψ))
    (hTaOk : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkP V ρ (Ta ψ))
    (hmemA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp2 V ρ (A ψ) ∈ˢ interp2 V ρ (Ta ψ))
    (hred : Setlec.reduceOpNames.contains cv.name = true →
      ReducePinR μ F env
        ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩
        mp.base2.base.cval cv.name value)
    (m₂ : EnvS2Core V
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval cv.name A) :
    ReduceOpsP m₂ := by
  intro c hcN cvR hf₂ hpin
  by_cases hne : c = cv.name
  case neg =>
    exact reduceOpsP_entry_cons mp.reduce_ops
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩) (A := A)
      hfresh m₂ hac hcN hne hf₂ hpin
  subst hne
  -- the recorded certificate, and its annotated subject
  obtain ⟨-, helemOk, -, valA, pinA, hannA, -, hrun, -⟩ :=
    hred (List.contains_iff_mem.mpr hcN)
  obtain rfl : valA = value' := Except.ok.inj (hannA.symm.trans hannv)
  -- the element inductive is stored, level-free, and is not the cons
  obtain ⟨ciE, hfE, hlpE⟩ := reduceElem_storedS hcN helemOk
  have hneE : Setlec.reduceElemName cv.name ≠ cv.name := by
    intro h; rw [h, hfresh] at hfE; exact nomatch hfE
  have hEty : Setlec.reduceElemTy cv.name
      = .const (Setlec.reduceElemName cv.name) [] := by
    unfold Setlec.reduceElemTy Setlec.reduceElemName
    split <;> simp [Setlec.natName, Setlec.boolName]
  have hdenE : ∀ (ψ : Name → Nat) (d : Nat),
      denoteP mp.base2.acval env ψ d (Setlec.reduceElemTy cv.name)
        = some (mp.base2.acval (Setlec.reduceElemName cv.name) ψ) := by
    intro ψ d
    rw [hEty]
    exact denoteP_levelless_const hfE hlpE
  -- the two leaf moves
  have hmoveE : m₂.acval (Setlec.reduceElemName cv.name)
      = mp.base2.acval (Setlec.reduceElemName cv.name) := by
    rw [hac]; exact acvalWith_ne hneE
  have hmoveC : m₂.acval cv.name = A := by
    rw [hac]; exact acvalWith_self
  -- `A` is a leaf, hence environment-blind
  have hclA : ∀ ρ₁ ρ₂ : Nat → V, ∀ ψ : Name → Nat,
      interp2 V ρ₁ (A ψ) = interp2 V ρ₂ (A ψ) := by
    intro ρ₁ ρ₂ ψ
    have h := acval_interp2_closedC m₂ cv.name ψ ρ₁ ρ₂
    rwa [hmoveC] at h
  -- the stored entry is the pinned type, and the pin fixes its shape
  rw [Setlec.Env.find?_cons, if_pos (show (ConstantInfo.axiomInfo
    ⟨cv.name, cv.levelParams, type'⟩).name = cv.name from rfl)] at hf₂
  obtain rfl : cvR = ⟨cv.name, cv.levelParams, type'⟩ :=
    (ConstantInfo.axiomInfo.inj (Option.some.inj hf₂)).symm
  simp only [ConstantVal.matchesPin, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hpin
  obtain ⟨n₀, mb₀, htyShape⟩ := reduceOp_shapeS hcN hpin.2
  subst htyShape
  -- the type's reading: a one-step `.pi` over the element leaf
  have hinst : (Setlec.reduceElemTy cv.name).instantiate1
        (.fvar 0 n₀ (Setlec.reduceElemTy cv.name))
      = Setlec.reduceElemTy cv.name :=
    Expr.instantiate1_eq_self (by rw [hEty]; rfl)
  have hTaShape : ∀ ψ : Name → Nat,
      Ta ψ = .pi 0 (pwBit ψ mb₀.pw)
        (mp.base2.acval (Setlec.reduceElemName cv.name) ψ)
        (mp.base2.acval (Setlec.reduceElemName cv.name) ψ) := by
    intro ψ
    have h := hTa ψ
    rw [show denoteP mp.base2.acval env ψ 0
          (Expr.forallE n₀ (Setlec.reduceElemTy cv.name)
            (Setlec.reduceElemTy cv.name) mb₀)
        = some (.pi 0 (pwBit ψ mb₀.pw)
            (mp.base2.acval (Setlec.reduceElemName cv.name) ψ)
            (mp.base2.acval (Setlec.reduceElemName cv.name) ψ)) from by
      rw [denoteP_forallE, hdenE ψ 0, hinst, hdenE ψ 1]; rfl] at h
    exact (Option.some.inj h).symm
  -- the certificate variable's syntactic and context packages
  have hvLeaves : valA.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf'
  have hcertLeaves := reduceCertVar_fvarLeaves cv.name
  have hwsV : ∀ d : Nat, Expr.WScoped d valA :=
    fun d => Expr.WScoped.of_not_hasFvar hvf'
  have hwsCert : Expr.WScoped 1 (Setlec.reduceCertVar cv.name) := by
    rw [Setlec.reduceCertVar, hEty]
    simp [Expr.WScoped]
  have hbCert : (Setlec.reduceCertVar cv.name).looseBVarsBounded 0 = true := by
    rw [Setlec.reduceCertVar]; rfl
  have hLCert : Expr.LeavesBounded (Setlec.reduceCertVar cv.name) := by
    intro l hl
    rw [hcertLeaves] at hl
    obtain rfl : l = (0, Setlec.Name.anonymous.str "a",
        Setlec.reduceElemTy cv.name) := by simpa using hl
    rw [hEty]; rfl
  have hwsApp : Expr.WScoped 1
      (Expr.app valA (Setlec.reduceCertVar cv.name)) := by
    rw [Expr.WScoped]
    exact ⟨hwsV 1, hwsCert⟩
  have hbApp : Expr.looseBVarsBounded 0
      (Expr.app valA (Setlec.reduceCertVar cv.name)) = true := by
    rw [show Expr.looseBVarsBounded 0
        (Expr.app valA (Setlec.reduceCertVar cv.name))
      = (Expr.looseBVarsBounded 0 valA &&
          Expr.looseBVarsBounded 0 (Setlec.reduceCertVar cv.name))
      from rfl, hbv', hbCert]
    rfl
  have hLApp : Expr.LeavesBounded
      (Expr.app valA (Setlec.reduceCertVar cv.name)) := by
    intro l hl
    rw [show (Expr.app valA (Setlec.reduceCertVar cv.name)).fvarLeaves
        = valA.fvarLeaves ++ (Setlec.reduceCertVar cv.name).fvarLeaves
        from by rw [Expr.fvarLeaves], hvLeaves, List.nil_append] at hl
    exact hLCert l hl
  have hctxCert : ∀ ψ : Name → Nat,
      CtxOkP mp.base2 ψ 1 (elemCtx mp.base2 cv.name ψ)
        (Setlec.reduceCertVar cv.name) := by
    intro ψ
    refine ⟨rfl, fun l hl => ?_⟩
    rw [hcertLeaves] at hl
    obtain rfl : l = (0, Setlec.Name.anonymous.str "a",
        Setlec.reduceElemTy cv.name) := by simpa using hl
    refine ⟨Nat.zero_lt_one, by rw [hEty]; trivial,
      mp.base2.acval (Setlec.reduceElemName cv.name) ψ,
      elemAP mp.base2 cv.name ψ, hdenE ψ 1, rfl, fun ρ' _ => ?_,
      fun ρ' _ => ⟨mp.base2.acval_ok2 _ ψ ρ', mp.acval_validV _ ψ ρ'⟩⟩
    exact acval_interp2_closedC mp.base2 _ ψ _ _
  have hctxApp : ∀ ψ : Name → Nat,
      CtxOkP mp.base2 ψ 1 (elemCtx mp.base2 cv.name ψ)
        (Expr.app valA (Setlec.reduceCertVar cv.name)) := by
    intro ψ
    refine ⟨rfl, fun l hl => ?_⟩
    rw [show (Expr.app valA (Setlec.reduceCertVar cv.name)).fvarLeaves
        = valA.fvarLeaves ++ (Setlec.reduceCertVar cv.name).fvarLeaves
        from by rw [Expr.fvarLeaves], hvLeaves, List.nil_append] at hl
    exact (hctxCert ψ).2 l hl
  -- the two sides' readings at the certificate's depth
  have hdenCert : ∀ ψ : Name → Nat,
      denoteP mp.base2.acval env ψ 1 (Setlec.reduceCertVar cv.name)
        = some (.bvar 0) := by
    intro ψ
    rw [Setlec.reduceCertVar, denoteP_fvar]
  have hdenV1 : ∀ ψ : Name → Nat,
      denoteP mp.base2.acval env ψ 1 valA = some (A ψ) := fun ψ =>
    denoteP_depth_of_closed mp.base2.acval_closed hvf'
      (fun k => hAclosed ψ k) (hA ψ) 1
  have hdenApp : ∀ ψ : Name → Nat,
      denoteP mp.base2.acval env ψ 1
          (Expr.app valA (Setlec.reduceCertVar cv.name))
        = some (.app (A ψ) (.bvar 0)) := by
    intro ψ
    rw [denoteP_app, hdenV1 ψ, hdenCert ψ]
    rfl
  -- the claims at the prefix environment
  have hclaims := fun ψ =>
    checkSoundAtP (V := V) hμ (TierInputsAtP.ofSem mp ψ) F
  refine ⟨?_, fun ψ ρ x hx => ?_⟩
  · rw [Setlec.Env.find?_cons, if_neg (fun h => hneE h.symm), hfE]; rfl
  obtain ⟨-, -, ihd, -⟩ := hclaims ψ
  rw [hmoveE] at hx
  rw [hmoveC]
  -- the certificate variable's slot membership, at any satisfying `ρ'`
  have hslot : ∀ ρ' : Nat → V, Sat2 V (elemCtx mp.base2 cv.name ψ) ρ' →
      ρ' 0 ∈ˢ interp2 V ρ' (mp.base2.acval (Setlec.reduceElemName cv.name) ψ) := by
    intro ρ' hsat
    have h : ρ' 0 ∈ˢ interp2 V (fun j => ρ' (j + 0 + 1))
        (mp.base2.acval (Setlec.reduceElemName cv.name) ψ) :=
      hsat 0 (elemAP mp.base2 cv.name ψ) rfl
    rwa [acval_interp2_closedC mp.base2 _ ψ _ ρ'] at h
  -- the gradings: the bare variable is free, the applied side is the
  -- constant's own `mem_typeP`/`type_okP` content
  have hgradeCert : ∀ ρ' : Nat → V, Sat2 V (elemCtx mp.base2 cv.name ψ) ρ' →
      AnnotOkP V ρ' (.bvar 0) := by
    intro ρ' _
    exact ⟨by simp, by simp⟩
  have hgradeApp : ∀ ρ' : Nat → V, Sat2 V (elemCtx mp.base2 cv.name ψ) ρ' →
      AnnotOkP V ρ' (.app (A ψ) (.bvar 0)) := by
    intro ρ' hsat
    have hfib : (fun y => interp2 V (cons y ρ')
          (mp.base2.acval (Setlec.reduceElemName cv.name) ψ))
        = fun _ : V => interp2 V ρ'
            (mp.base2.acval (Setlec.reduceElemName cv.name) ψ) :=
      funext fun y => acval_interp2_closedC mp.base2 _ ψ _ ρ'
    have hm := hmemA ψ ρ'
    rw [hTaShape ψ, interp2_pi, hfib] at hm
    have hv := (hTaOk ψ ρ').2
    rw [hTaShape ψ, AnnotValidV_pi] at hv
    refine ⟨⟨hAok ψ ρ', by simp, ?_⟩, ⟨hAvalid ψ ρ', by simp⟩⟩
    refine ⟨pwBit ψ mb₀.pw,
      interp2 V ρ' (mp.base2.acval (Setlec.reduceElemName cv.name) ψ),
      fun _ => interp2 V ρ'
        (mp.base2.acval (Setlec.reduceElemName cv.name) ψ),
      hm, hslot ρ' hsat, fun h0 y hy => ?_⟩
    have := hv.2.2 h0 y hy
    rwa [acval_interp2_closedC mp.base2 _ ψ _ ρ'] at this
  -- the run, converted
  have heq := ihd (d := 1)
    (a := Expr.app valA (Setlec.reduceCertVar cv.name))
    (b := Setlec.reduceCertVar cv.name) (Δa := elemCtx mp.base2 cv.name ψ)
    hrun hwsApp hbApp hLApp hwsCert hbCert hLCert
    (hctxApp ψ) (hctxCert ψ) (hdenApp ψ) (hdenCert ψ)
    hgradeApp hgradeCert (cons x ρ) (sat2_elemCtx mp.base2 hx)
  rw [interp2_app, interp2_bvar] at heq
  show SetTheory.app (interp2 V ρ (A ψ)) x = x
  rw [hclA ρ (cons x ρ) ψ]
  exact heq

end Setlec.SetR.Interp2
