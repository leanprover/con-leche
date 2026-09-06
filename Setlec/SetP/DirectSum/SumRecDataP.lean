import Setlec.SetP.DirectSum.SumRecReadP
import Setlec.SetP.DirectSum.SumDataP
import Setlec.SetP.Direct.DirectRecDataP

/-!
# The sum recursor's data (task #175 sum-types)

`SumRecData`: the generated sum recursor type's reading, peeled — the
`RecData` of the single-constructor route with `n` minor entries and
the core `motive t` spelled under the motive and `n` minors; read off
the generated type by `sumRecData_of`, and rule `j`'s reading and
grading by `sumRuleData_of`.  The constructors' data is carried as one
function of the position (`ctorDataList`).
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectSumParts
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- The elimination level of a direct sum block. -/
def sumElimLevel (p : DirectSumParts) : Level :=
  Setlec.directElimLevel p.elim p.large

theorem sumElimLevel_eq (p : DirectSumParts) :
    sumElimLevel p = if p.large then .param p.elim else .zero := rfl

/-! ## The constructors' data, positionally -/

/-- The constructor data list from a position-indexed data function. -/
def ctorDataList (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)) (ψ : Name → Nat) :
    List (ConstantVal × Nat) → Nat → List (Name × Nat × List (Nat × Nat × AVExpr))
  | [], _ => []
  | c :: cs, j => (c.1.name, c.2, dsF j ψ) :: ctorDataList dsF ψ cs (j + 1)

theorem ctorDataList_length (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr))
    (ψ : Name → Nat) : ∀ (cs : List (ConstantVal × Nat)) (j : Nat),
      (ctorDataList dsF ψ cs j).length = cs.length
  | [], _ => rfl
  | _ :: cs, j => by simp [ctorDataList, ctorDataList_length dsF ψ cs (j + 1)]

theorem ctorDataList_getElem? (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr))
    (ψ : Name → Nat) : ∀ (cs : List (ConstantVal × Nat)) (j i : Nat),
      (ctorDataList dsF ψ cs j)[i]? = cs[i]?.map fun c => (c.1.name, c.2, dsF (j + i) ψ)
  | [], _, _ => by simp [ctorDataList]
  | c :: cs, j, 0 => by simp [ctorDataList]
  | c :: cs, j, i + 1 => by
    simp only [ctorDataList, List.getElem?_cons_succ]
    rw [ctorDataList_getElem? dsF ψ cs (j + 1) i, show j + 1 + i = j + (i + 1) from by omega]

theorem ctorDataList_params {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {ψ₁ ψ₂ : Name → Nat} : ∀ {cs : List (ConstantVal × Nat)} {j : Nat},
      (∀ i, i < cs.length → dsF (j + i) ψ₁ = dsF (j + i) ψ₂) →
      ctorDataList dsF ψ₁ cs j = ctorDataList dsF ψ₂ cs j
  | [], _, _ => rfl
  | _ :: cs, j, h => by
    simp only [ctorDataList]
    rw [show j = j + 0 from rfl, h 0 (by simp), Nat.add_zero]
    congr 1
    exact ctorDataList_params fun i hi => by
      rw [show j + 1 + i = j + (i + 1) from by omega]
      exact h (i + 1) (by simpa using hi)

/-- What the readings need of every constructor at its position:
stored, at the block's level parameters, its telescope strips, and its
data. -/
def CtorFactsAt {env : Env} (m : EnvS2Core V env) (T : Name) (lps : List Name) (nP : Nat)
    (resSort : Level) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr))
    (j : Nat) (cA : ConstantVal × Nat) : Prop :=
  env.find? cA.1.name = some (.ctorInfo cA.1 nP cA.2) ∧
  cA.1.levelParams = lps ∧
  (cA.1.type.stripPis (nP + cA.2)).isSome = true ∧
  CtorData m T cA.1 nP cA.2 resSort (dsF j)

/-- The constructors' reading premises, from their facts. -/
theorem ctorReads_of {m : EnvS2Core V env} {T : Name} {lps : List Name} {nP : Nat}
    {resSort : Level} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)} (ψ : Name → Nat) :
    ∀ {cs : List (ConstantVal × Nat)} {j : Nat},
      (∀ i cA, cs[i]? = some cA → CtorFactsAt m T lps nP resSort dsF (j + i) cA) →
      CtorReads m ψ lps nP (cs.map fun c => (c.1.name, c.2, c.1.type)) (ctorDataList dsF ψ cs j)
  | [], _, _ => .nil
  | c :: cs, j, h => by
    obtain ⟨hf, hlps, hstrip, hCD⟩ := h 0 c rfl
    rw [Nat.add_zero] at hCD
    obtain ⟨hCf, -, -, hCb, -⟩ := m.wf _ (Setlec.Semantics.Env.find?_mem hf)
    simp only [ConstantInfo.toConstantVal] at hCf hCb
    refine .cons ⟨rfl, rfl, ⟨_, hf, hlps⟩, hCf, hCb, hstrip, ⟨_, hCD.read ψ⟩, hCD.len ψ⟩ ?_
    exact ctorReads_of ψ fun i cA hi => by
      have := h (i + 1) cA (by simpa using hi)
      rwa [show j + (i + 1) = j + 1 + i from by omega] at this

/-! ## The recursor's data -/

/-- **The sum recursor type's reading, peeled.** -/
structure SumRecData {env : Env} (m : EnvS2Core V env) (cvR : ConstantVal)
    (nP n : Nat) (elimL : Level)
    (rds : (Name → Nat) → List (Nat × Nat × AVExpr)) : Prop where
  read : ∀ ψ : Name → Nat, denoteP m.acval env ψ 0 cvR.type
    = some (mkPisAV (rds ψ) (.app (.bvar (n + 1)) (.bvar 0)))
  len : ∀ ψ : Name → Nat, (rds ψ).length = nP + n + 2
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AVExpr), d ∈ rds ψ →
    (elimL.eval ψ = 0 ↔ d.2.1 = 0)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOkP V ρ (mkPisAV (rds ψ) (.app (.bvar (n + 1)) (.bvar 0)))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (rds ψ)
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvR.levelParams, ψ₁ p = ψ₂ p) →
    rds ψ₁ = rds ψ₂

/-- The recursor's data crosses a cons whose slot does not mention the
stored recursor. -/
theorem SumRecData.cross {m : EnvS2Core V env} {cvR : ConstantVal}
    {nP n : Nat} {elimL : Level}
    {rds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (h : SumRecData m cvR nP n elimL rds)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none) (hat : ConsCrossAt c₀ cvR.type)
    (hcb : ConstsBound env cvR.type)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    SumRecData m₂ cvR nP n elimL rds where
  read ψ := by
    rw [hac]
    exact denoteP_cons_mono hfresh hat ψ 0 hcb (h.read ψ)
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params

/-- The sum recursor's binder data at the block. -/
def sumRdsAV {env : Env} (m : EnvS2Core V env) (p : DirectSumParts)
    (pps : (Name → Nat) → List (Nat × Nat × AVExpr))
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)) (ctorsA : List (ConstantVal × Nat))
    (ψ : Name → Nat) : List (Nat × Nat × AVExpr) :=
  sumRecDataAV m p.cvT.name ψ p.nP (sumElimLevel p) (pps ψ) (ctorDataList dsF ψ ctorsA 0)

theorem mem_sumRecDataAV {m : EnvS2Core V env} {T : Name} {ψ : Name → Nat} {nP : Nat}
    {ℓ : Level} {pps : List (Nat × Nat × AVExpr)}
    {cds : List (Name × Nat × List (Nat × Nat × AVExpr))} {d : Nat × Nat × AVExpr}
    (hd : d ∈ sumRecDataAV m T ψ nP ℓ pps cds) : d.2.1 = pwBit ψ (Level.zeronessOf ℓ) := by
  simp only [sumRecDataAV, List.mem_append, List.mem_singleton] at hd
  rcases hd with ((h | rfl) | h) | rfl
  · exact mem_rebit h
  · rfl
  · exact mem_sumMinorsData h
  · rfl

/-- **The recursor's data**, read off the generated type: the reading
is syntactic (`denoteP_directRecTy_sum`), the bits are the elimination
datum's, the grading is the fabricated type's own inference run. -/
theorem sumRecData_of (hμ : μ.verifiedChecks = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectSumParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr} {caps : IndCaps}
    (hRec : Setlec.checkDirectSumRec (Setlec.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hcf : ∀ j cA, ctorsA[j]? = some cA →
      CtorFactsAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.resSort dsF j cA) :
    SumRecData mp.base2 cvRa p.nP ctorsA.length (sumElimLevel p) (sumRdsAV mp.base2 p pps dsF ctorsA) := by
  obtain ⟨cvRi, recTy, sty, u, -, hgen, htp, -, hbt, hRf, hsty, -, -, -, rfl⟩ :=
    Setlec.checkDirectSumRec_shape hRec
  obtain ⟨hTf, -, -, -⟩ := mp.base2.wf _ (Setlec.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf
  have hcr : ∀ ψ, CtorReads mp.base2 ψ p.cvT.levelParams p.nP
      (ctorsA.map fun c => (c.1.name, c.2, c.1.type)) (ctorDataList dsF ψ ctorsA 0) :=
    fun ψ => ctorReads_of ψ (j := 0) fun i cA hi => by rw [Nat.zero_add]; exact hcf i cA hi
  have hread : ∀ ψ : Name → Nat, denoteP mp.base2.acval env ψ 0 recTy
      = some (mkPisAV (sumRdsAV mp.base2 p pps dsF ctorsA ψ)
          (.app (.bvar (ctorsA.length + 1)) (.bvar 0))) := fun ψ => by
    have := denoteP_directRecTy_sum hfT hlpsT (hcr ψ) hgen hTf hopT (hFD.read ψ) (hFD.len ψ)
    rwa [ctorDataList_length] at this
  have hw : Expr.WScoped 0 recTy := Expr.WScoped.of_not_hasFvar hRf
  have hL : Expr.LeavesBounded recTy := Expr.LeavesBounded.of_not_hasFvar hRf
  have hnil : recTy.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hRf
  have hlen : ∀ ψ, (sumRdsAV mp.base2 p pps dsF ctorsA ψ).length = p.nP + ctorsA.length + 2 := by
    intro ψ
    simp only [sumRdsAV, sumRecDataAV, List.length_append, rebit_length, hFD.len ψ,
      List.length_singleton, sumMinorsData_length, ctorDataList_length]
    omega
  refine ⟨hread, hlen, ?_, ?_, ?_, ?_⟩
  · intro ψ d hd
    rw [mem_sumRecDataAV hd, pwBit_eq_zero_iff, Setlec.PropWhen.zeronessOf_sound, beq_iff_eq]
  · intro ψ ρ
    have hc := claimsAtP_of hμ mp ψ F
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hsty hw hbt hL (CtxOkP.nil hnil) (hread ψ)
    exact hokT ρ (Sat2_nil V ρ)
  · intro ψ
    have hst := stripPisAV_mkPisAV (sumRdsAV mp.base2 p pps dsF ctorsA ψ)
      (AVExpr.app (.bvar (ctorsA.length + 1)) (.bvar 0))
    exact (stripPisAV_below hst (bvarsBelow_of_reading hw hbt (hread ψ))).1
  · intro ψ₁ ψ₂ hφ
    have h2 := hread ψ₂
    have h1 : denoteP mp.base2.acval env ψ₂ 0 recTy
        = some (mkPisAV (sumRdsAV mp.base2 p pps dsF ctorsA ψ₁)
            (.app (.bvar (ctorsA.length + 1)) (.bvar 0))) := by
      rw [← denoteP_params_ext mp.base2 hφ 0 recTy htp]
      exact hread ψ₁
    exact (mkPisAV_inj (by rw [hlen ψ₁, hlen ψ₂]) (Option.some.inj (h1.symm.trans h2))).1

/-- **Rule `j`'s data**: its right-hand side (stored at position `j`),
its scoping, its reading at every assignment, graded by its own
inference run. -/
theorem sumRuleData_of (hμ : μ.verifiedChecks = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectSumParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr} {caps : IndCaps}
    (hRec : Setlec.checkDirectSumRec (Setlec.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hcf : ∀ j cA, ctorsA[j]? = some cA →
      CtorFactsAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.resSort dsF j cA)
    {j : Nat} {cA : ConstantVal × Nat} (hj : ctorsA[j]? = some cA) :
    ∃ rhs : Expr, rhss[j]? = some rhs ∧
      rhs.constsResolve env = true ∧ rhs.hasFvar = false ∧
      (∀ ψ : Name → Nat, denoteP mp.base2.acval env ψ 0 rhs
        = some (mkLamsAV (sumRuleDataAV mp.base2 p.cvT.name ψ p.nP (sumElimLevel p) (pps ψ)
            (ctorDataList dsF ψ ctorsA 0) (dsF j ψ)) (sumRuleCoreAV cA.2 ctorsA.length j))) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        AnnotOkP V ρ (mkLamsAV (sumRuleDataAV mp.base2 p.cvT.name ψ p.nP (sumElimLevel p) (pps ψ)
            (ctorDataList dsF ψ ctorsA 0) (dsF j ψ)) (sumRuleCoreAV cA.2 ctorsA.length j))) := by
  obtain ⟨cvRi, recTy, sty, u, -, -, -, -, -, -, -, -, -, hrules, -⟩ :=
    Setlec.checkDirectSumRec_shape hRec
  obtain ⟨hTf, -, -, -⟩ := mp.base2.wf _ (Setlec.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf
  have hjn : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨-, hall⟩ := Setlec.checkDirectSumRules_inv hrules
  obtain ⟨rhs, hrhs, hgen, -, hres, hbr, hrf, rhsTy, hrty⟩ := hall j (by simpa using hjn)
  rw [Nat.zero_add] at hgen
  have hcr : ∀ ψ, CtorReads mp.base2 ψ p.cvT.levelParams p.nP
      (ctorsA.map fun c => (c.1.name, c.2, c.1.type)) (ctorDataList dsF ψ ctorsA 0) :=
    fun ψ => ctorReads_of ψ (j := 0) fun i cA hi => by rw [Nat.zero_add]; exact hcf i cA hi
  have hjd : ∀ ψ, (ctorDataList dsF ψ ctorsA 0)[j]? = some (cA.1.name, cA.2, dsF j ψ) := by
    intro ψ
    rw [ctorDataList_getElem?, hj, Nat.zero_add]
    rfl
  have hread : ∀ ψ : Name → Nat, denoteP mp.base2.acval env ψ 0 rhs
      = some (mkLamsAV (sumRuleDataAV mp.base2 p.cvT.name ψ p.nP (sumElimLevel p) (pps ψ)
          (ctorDataList dsF ψ ctorsA 0) (dsF j ψ)) (sumRuleCoreAV cA.2 ctorsA.length j)) := by
    intro ψ
    have := denoteP_directRecRhs_sum hfT hlpsT (hcr ψ) hgen hTf hopT (hFD.read ψ) (hFD.len ψ)
      (hjd ψ)
    rwa [ctorDataList_length] at this
  refine ⟨rhs, hrhs, hres, hrf, hread, fun ψ ρ => ?_⟩
  have hw : Expr.WScoped 0 rhs := Expr.WScoped.of_not_hasFvar hrf
  have hL : Expr.LeavesBounded rhs := Expr.LeavesBounded.of_not_hasFvar hrf
  have hnil : rhs.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hrf
  have hc := claimsAtP_of hμ mp ψ F
  obtain ⟨-, -, hokR, -, -⟩ := hc.inferRow hrty hw hbr hL (CtxOkP.nil hnil) (hread ψ)
  exact hokR ρ (Sat2_nil V ρ)

end Setlec.SetP
