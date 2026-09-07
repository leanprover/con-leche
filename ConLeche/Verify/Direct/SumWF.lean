import Lech.Verify.Direct.DirectWF
import Lech.Verify.Direct.SumInv

/-!
# The direct sum install: environment well-formedness (task #175
sum-types, indexed)

`EnvWF` for the environments `checkDirectSum` walks through, read off
the stages' own guards (as `DirectWF.lean` for the structure route):
the former's cons, the constructors' conses (`consSumCtors`, each a
checked constant), the recursor's cons with its rules (each rule's
right-hand side scoped by `checkDirectSumRules`, never `.nested`).
Task #175 indexed: the recursor's cons is generic over its major index
and rule prefix (`p.majorIdx`/`p.rulePrefix` at the install).
-/

namespace Lech

variable {mode : CheckMode}

/-- Stage 1 at the run level. -/
theorem direct_sum_ind_wf {env env₁ : Env} (henv : EnvWF env)
    {p p' : DirectSumParts} {cvTa : ConstantVal} {F : Nat}
    (h : checkDirectSumInd (fueledOps mode F) env p = .ok (env₁, cvTa, p')) :
    EnvWF env₁ ∧ cvTa.type.hasFvar = false := by
  obtain ⟨cvT, s, -, -, hccv, rfl, rfl, -⟩ := checkDirectSumInd_shape h
  exact ⟨envWF_cons_ind henv hccv, (checkConstantVal_typeWF hccv).1⟩

/-- A constructor's run at the former's environment: its type is
closed and bounded. -/
theorem direct_sum_ctor_typeWF {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvC cvTa cvCa : ConstantVal}
    {nF : Nat} {F : Nat}
    (h : checkDirectSumCtor (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok cvCa) :
    cvCa.type.hasFvar = false ∧ cvCa.type.allLevelParamsDefined cvCa.levelParams = true ∧
    cvCa.type.constsResolve env = true ∧ cvCa.type.looseBVarsBounded 0 = true := by
  obtain ⟨hccv, -, -⟩ := checkDirectSumCtor_shape h
  exact checkConstantVal_typeWF hccv

/-- The constructors' conses keep well-formedness: every consed
constructor's type resolves at the environment it is consed onto
(resolution is monotone along the conses). -/
theorem envWF_consSumCtors {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      EnvWF env →
      (∀ c ∈ ctorsA, c.1.type.hasFvar = false ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true) →
      EnvWF (consSumCtors nP ctorsA env)
  | [], _, henv, _ => henv
  | c :: cs, env, henv, hall => by
    simp only [consSumCtors]
    obtain ⟨htf, htp, htr, htb⟩ := hall c List.mem_cons_self
    refine envWF_consSumCtors ?_ ?_
    · exact EnvWF.cons henv (directConstWF htf htp (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
    · intro c' hc'
      obtain ⟨h1, h2, h3, h4⟩ := hall c' (List.mem_cons_of_mem _ hc')
      exact ⟨h1, h2, Expr.constsResolve_mono h3, h4⟩

/-- The recursor stage's stored pieces, as its own guards checked
them. -/
theorem checkDirectSumRec_facts {env : Env} {p : DirectSumParts}
    {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {F : Nat}
    (h : checkDirectSumRec (fueledOps mode F) env p cvTa ctorsA = .ok (cvRa, rhss)) :
    cvRa.name = p.cvR.name ∧ cvRa.levelParams = p.cvR.levelParams ∧
    (cvRa.type.hasFvar = false ∧
      cvRa.type.allLevelParamsDefined cvRa.levelParams = true ∧
      cvRa.type.constsResolve env = true ∧
      cvRa.type.looseBVarsBounded 0 = true) ∧
    rhss.length = ctorsA.length ∧
    ∀ rhs ∈ rhss, rhs.hasFvar = false ∧
      rhs.allLevelParamsDefined cvRa.levelParams = true ∧
      rhs.constsResolve env = true ∧
      rhs.looseBVarsBounded 0 = true := by
  obtain ⟨cvRi, recTy, sty, u, -, -, hlp, hres, hbv, hfv, -, -, -, hrules, rfl⟩ :=
    checkDirectSumRec_shape h
  obtain ⟨hlen, hall⟩ := checkDirectSumRules_inv hrules
  refine ⟨rfl, rfl, ⟨hfv, hlp, hres, hbv⟩, by simpa using hlen, ?_⟩
  intro rhs hrhs
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hrhs
  have hi' : i < (ctorsA.map fun c => (c.1.name, c.2, c.1.type)).length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨rhs', hget, -, hlp', hres', hbv', hfv', -⟩ := hall i hi'
  obtain rfl := Option.some.inj (hi.symm.trans hget)
  exact ⟨hfv', hlp', hres', hbv'⟩

/-- The stored rules carry the generated right-hand sides and are
never `.nested`. -/
theorem directSumRules_mem {nP mI rP : Nat} {recTy : Expr} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {r : RecRule},
      r ∈ directSumRules nP mI rP recTy ctorsA rhss →
      r.rhs ∈ rhss ∧ ∀ lvls pins, r.fire ≠ .nested lvls pins
  | [], _, r, h => by simp [directSumRules] at h
  | _ :: _, [], r, h => by simp [directSumRules] at h
  | c :: cs, rhs :: rhss, r, h => by
    simp only [directSumRules, List.mem_cons] at h
    rcases h with rfl | h
    · refine ⟨List.mem_cons_self, fun lvls pins => ?_⟩
      show (if Expr.recRulePlain recTy mI rP nP then RecRuleFire.plain else .inert) ≠ _
      split <;> simp
    · obtain ⟨hm, hf⟩ := directSumRules_mem h
      exact ⟨List.mem_cons_of_mem _ hm, hf⟩

/-- Stage 3 at the run level: the recursor cons with its rules is
well-formed. -/
theorem direct_sum_rec_wf {env : Env} (henv : EnvWF env)
    {p : DirectSumParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr} {F : Nat} {mI rP : Nat}
    (h : checkDirectSumRec (fueledOps mode F) env p cvTa ctorsA = .ok (cvRa, rhss)) :
    EnvWF ⟨.recInfo cvRa mI rP (directSumRules p.nP mI rP cvRa.type ctorsA rhss)
      :: env.consts⟩ := by
  obtain ⟨-, -, ⟨htf, htp, htr, htb⟩, -, hall⟩ := checkDirectSumRec_facts h
  refine EnvWF.cons henv (directConstWF htf htp
    (Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq) ?_)
  intro cvR' mI' rP' rules' heq r hr
  injection heq with e1 e2 e3 e4
  subst e1
  subst e4
  obtain ⟨hmem, hfire⟩ := directSumRules_mem hr
  obtain ⟨hrfv, hrlp, hrres, hrbv⟩ := hall r.rhs hmem
  refine ⟨hrfv, hrlp, Expr.constsResolve_mono hrres, hrbv, ?_⟩
  intro lvls pins hf
  exact absurd hf (hfire lvls pins)

end Lech
