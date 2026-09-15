module

public import ConLeche.Verify.Inductives.MutualInv
public import ConLeche.Verify.Inductives.SumWF

public section

/-!
# The mutual install: environment well-formedness (task #278)

`EnvWF` for the environments `checkMutual` walks through, read off the
stages' own guards as `SumWF.lean`/`FixWF.lean` read the fixpoint
route's: the formers' conses (each a checked constant with the block's
capability record `{}`), the constructors' conses
(`consMutualCtors`), the `k` recursors stored as a group with their
rules, and the structure-like members' projection tables.

The recursors' stage is the one novelty.  A mutual rule mentions the
SIBLING recursors, so its right-hand side is scoped at the environment
holding all `k` rule-less provisions (`provisionMutualRecs`) and not
at the prefix its own cons sits on — which is no obstacle, because
`EnvWF` asks `ConstWF` of every stored constant *at the whole
environment*: the provision and the store cons the same `k` names in
the same order onto the same environment, so they find exactly the
same names (`provisionMutualRecs_store_le`) and resolution carries
over.  The walk over the final environment is therefore one
`envWF_of_le` and not a chain of `EnvWF.cons`.
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## Monotone extension -/

/-- One constant's well-formedness is monotone under lookup-preserving
extension (`EnvWF.cons`'s tail half, at an arbitrary extension). -/
theorem ConstWF.le {envA envB : Env} {c : ConstantInfo}
    (hf : ∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true)
    (hc : ConstWF envA c) : ConstWF envB c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩ := hc
  refine ⟨h1, h2, Expr.constsResolve_le hf h3, h4, fun cv value hint heq =>
    let ⟨g1, g2, g3, g4⟩ := h5 cv value hint heq
    ⟨g1, g2, Expr.constsResolve_le hf g3, g4⟩, ?_,
    fun tbl heq =>
      let ⟨g0, g⟩ := h8 tbl heq
      ⟨g0, fun i bd hb =>
        let ⟨g1, g2, g3, g4⟩ := g i bd hb
        ⟨g1, g2, Expr.constsResolve_le hf g3, g4⟩⟩, h9⟩
  intro cv mI rP rules heq r hr
  obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv mI rP rules heq r hr
  refine ⟨g1, g2, Expr.constsResolve_le hf g3, g4, ?_⟩
  intro lvls pins hfr
  obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hfr
  exact ⟨n1, n2, fun pin hpin =>
    let ⟨p1, p2, p3, p4⟩ := n3 pin hpin
    ⟨p1, p2, Expr.constsResolve_le hf p3, p4⟩, n4⟩

/-- **Well-formedness of a whole extension**: every constant of the
extended environment is either one of the old ones (carried over by
monotonicity) or well-formed at the extended environment itself.  The
mutual recursors' group store needs this shape: a rule mentions the
sibling recursors, so the group is well-formed together and not one
cons at a time. -/
theorem envWF_of_le {env envOut : Env} (henv : EnvWF env)
    (hle : ∀ n, (env.find? n).isSome = true → (envOut.find? n).isSome = true)
    (hsplit : ∀ c ∈ envOut.consts, c ∈ env.consts ∨ ConstWF envOut c) :
    EnvWF envOut := by
  intro c hc
  rcases hsplit c hc with hm | hw
  · exact ConstWF.le hle (henv c hm)
  · exact hw

/-- A cons finds everything its base finds. -/
theorem find?_isSome_cons {c : ConstantInfo} {env : Env} {n : Name}
    (h : (env.find? n).isSome = true) :
    (Env.find? ⟨c :: env.consts⟩ n).isSome = true := by
  rw [Env.find?_cons]
  split
  · rfl
  · exact h

/-- Two conses of the same name over lookup-comparable environments
stay lookup-comparable. -/
theorem find?_isSome_cons_mono {c c' : ConstantInfo} {env env' : Env}
    (hn : c.name = c'.name)
    (hf : ∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) :
    ∀ n, (Env.find? ⟨c :: env.consts⟩ n).isSome = true →
      (Env.find? ⟨c' :: env'.consts⟩ n).isSome = true := by
  intro n h
  rw [Env.find?_cons] at h
  rw [Env.find?_cons, ← hn]
  split
  · rfl
  · next hne =>
    rw [if_neg hne] at h
    exact hf n h

/-! ## Stage 1: the formers -/

/-- The type-slot `ConstWF` facts of every checked former, AT THE
PRE-BLOCK ENVIRONMENT (where the whole stage runs). -/
theorem mutualFormerChecks_typeWF {nP F : Nat} {l : List (ConstantVal × Nat)} {env : Env}
    {fms : List MutualFormerA}
    (h : mutualFormerChecks (fueledOps mode F) env nP l = .ok fms) :
    ∀ f ∈ fms, f.cvTa.type.hasFvar = false ∧
      f.cvTa.type.allLevelParamsDefined f.cvTa.levelParams = true ∧
      f.cvTa.type.constsResolve env = true ∧
      f.cvTa.type.looseBVarsBounded 0 = true := by
  intro f hf
  obtain ⟨cv', hccv'⟩ := mutualFormerChecks_checked h f hf
  exact checkConstantVal_typeWF hccv'

/-- The formers' conses keep well-formedness: every member's type
resolves at the pre-block environment, and resolution is monotone
along the conses (the members' names need not be compared — `EnvWF` is
about the constants' own data). -/
theorem envWF_consMutualFormers :
    ∀ {fms : List MutualFormerA} {env : Env},
      EnvWF env →
      (∀ f ∈ fms, f.cvTa.type.hasFvar = false ∧
        f.cvTa.type.allLevelParamsDefined f.cvTa.levelParams = true ∧
        f.cvTa.type.constsResolve env = true ∧
        f.cvTa.type.looseBVarsBounded 0 = true) →
      EnvWF (consMutualFormers fms env)
  | [], _, henv, _ => henv
  | f :: fs, env, henv, hall => by
    simp only [consMutualFormers]
    obtain ⟨htf, htp, htr, htb⟩ := hall f List.mem_cons_self
    refine envWF_consMutualFormers ?_ ?_
    · exact EnvWF.cons henv (structConstWF htf htp (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
        (by intro tbl hh; exact ConstantInfo.noConfusion hh)
        (IndCapsWF.of_caps (fun hu => absurd hu (by decide))
          (fun he => absurd he (by decide))))
    · intro f' hf'
      obtain ⟨h1, h2, h3, h4⟩ := hall f' (List.mem_cons_of_mem _ hf')
      exact ⟨h1, h2, Expr.constsResolve_mono h3, h4⟩

/-- The formers' stage keeps the environment well-formed: every member
is a checked constant, consed with the block's (empty) capability
record. -/
theorem envWF_mutualFormers {nP F : Nat} {l : List (ConstantVal × Nat)}
    {env env' : Env} {fms : List MutualFormerA}
    (henv : EnvWF env)
    (h : mutualFormers (fueledOps mode F) nP l env = .ok (env', fms)) :
    EnvWF env' := by
  obtain ⟨hchecks, rfl⟩ := mutualFormers_inv h
  exact envWF_consMutualFormers henv (mutualFormerChecks_typeWF hchecks)

/-! ## Stage 3: the constructors -/

/-- A name fresh above the constructors' conses is fresh below them. -/
theorem consMutualCtors_find?_none {nP : Nat} {n : Name} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      (consMutualCtors nP ctorsA env).find? n = none → env.find? n = none
  | [], _, h => h
  | c :: cs, env, h => by
    simp only [consMutualCtors] at h
    have h' := consMutualCtors_find?_none h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- The constructors' conses keep well-formedness: every consed
constructor's type resolves at the environment it is consed onto
(resolution is monotone along the conses). -/
theorem envWF_consMutualCtors {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      EnvWF env →
      (∀ c ∈ ctorsA, c.1.type.hasFvar = false ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true) →
      EnvWF (consMutualCtors nP ctorsA env)
  | [], _, henv, _ => henv
  | c :: cs, env, henv, hall => by
    simp only [consMutualCtors]
    obtain ⟨htf, htp, htr, htb⟩ := hall c List.mem_cons_self
    refine envWF_consMutualCtors ?_ ?_
    · exact EnvWF.cons henv (structConstWF htf htp (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
    · intro c' hc'
      obtain ⟨h1, h2, h3, h4⟩ := hall c' (List.mem_cons_of_mem _ hc')
      exact ⟨h1, h2, Expr.constsResolve_mono h3, h4⟩

/-- A constructor's run at the formers' environment: its type is
closed, level-defined, resolving and bounded. -/
theorem mutual_ctor_typeWF {env : Env} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal} {nF F : Nat} {sorts : List Level}
    (h : checkMutualCtor (fueledOps mode F) env memberNames T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok (cvCa, sorts)) :
    cvCa.type.hasFvar = false ∧ cvCa.type.allLevelParamsDefined cvCa.levelParams = true ∧
    cvCa.type.constsResolve env = true ∧ cvCa.type.looseBVarsBounded 0 = true := by
  obtain ⟨⟨_, hccv⟩, -, -⟩ := checkMutualCtor_shape h
  exact checkConstantVal_typeWF hccv

/-- Every annotated constructor of the block carries the four type-slot
facts at the formers' environment. -/
theorem checkMutualCtors_typeWF {env : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {isProp : Bool} {F : Nat} {cs : List MutualCtor} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)}
    (h : checkMutualCtors (fueledOps mode F) env b fms isProp cs = .ok (ctorsA, sortss)) :
    ∀ c ∈ ctorsA, c.1.type.hasFvar = false ∧
      c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
      c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true := by
  obtain ⟨hlen, -, hall⟩ := checkMutualCtors_inv h
  intro c hc
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  have hj' : j < cs.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  obtain ⟨-, _, -, hrun⟩ := hall j cs[j] c (List.getElem?_eq_getElem hj') hj
  exact mutual_ctor_typeWF hrun

/-! ## Stage 4: the recursors -/

/-- The stored rules carry the generated right-hand sides and are
never `.nested` (`sumRules_mem` at a mutual block). -/
theorem mutualRules_mem {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ {l : List (MutualCtor × Expr)} {r : RecRule},
      r ∈ mutualRules find? recName nP mI rP recTy l →
      (∃ cr ∈ l, r.rhs = cr.2) ∧ ∀ lvls pins, r.fire ≠ .nested lvls pins
  | [], r, h => by simp [mutualRules] at h
  | cr :: cs, r, h => by
    simp only [mutualRules, List.mem_cons] at h
    rcases h with rfl | h
    · refine ⟨⟨cr, List.mem_cons_self, rfl⟩, fun lvls pins => ?_⟩
      show (if Expr.recRulePlain recTy mI rP nP then RecRuleFire.plain else .inert) ≠ _
      split <;> simp
    · obtain ⟨⟨cr', hm, he⟩, hf⟩ := mutualRules_mem h
      exact ⟨⟨cr', List.mem_cons_of_mem _ hm, he⟩, hf⟩

/-- Every stored rule of a mutual recursor carries the two rescue bits
its own install-time lookup computes. -/
theorem mutualRules_bits {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ {l : List (MutualCtor × Expr)} {r : RecRule},
      r ∈ mutualRules find? recName nP mI rP recTy l →
      r.k = recRuleKOf find? r.ctor ∧ r.eta = recRuleEtaOf find? recName r.ctor
  | [], r, h => by simp [mutualRules] at h
  | _ :: cs, r, h => by
    simp only [mutualRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl, rfl⟩
    · exact mutualRules_bits h

/-- One member's generated rules, by membership. -/
theorem checkMutualMemberRules_mem {envR : Env} {b : MutualBlock}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4} {mIdx : Nat}
    {streamRec : Option (ConstantVal × List RecRule)} {rules : List (MutualCtor × Expr)}
    (h : checkMutualMemberRules (m := CheckM) envR b formers4 ctors4 mIdx streamRec
      = .ok rules)
    {cr : MutualCtor × Expr} (hm : cr ∈ rules) :
    cr.2.hasFvar = false ∧ cr.2.allLevelParamsDefined b.rlps = true ∧
    cr.2.constsResolve envR = true ∧ cr.2.looseBVarsBounded 0 = true := by
  obtain ⟨-, hlen, hall⟩ := checkMutualMemberRules_inv h
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  have hi' : i < (b.ownCtors mIdx).length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨J, c, rhs, -, hget, -, hlp, hres, hbv, hfv⟩ := hall i hi'
  obtain rfl := Option.some.inj (hi.symm.trans hget)
  exact ⟨hfv, hlp, hres, hbv⟩

/-- The store finds everything the environment it is built on finds. -/
theorem storeMutualRecs_le {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} (n : Name),
      (env.find? n).isSome = true →
      ((storeMutualRecs env₂ b fms rulesOf l env).find? n).isSome = true
  | [], _, _, h => h
  | (cvRa, mIdx) :: rest, env, n, h => by
    simp only [storeMutualRecs]
    exact storeMutualRecs_le n (find?_isSome_cons h)

/-- **The provision and the store cons the same names**: the `k`
rule-less recursors and the `k` recursors with their rules are consed
in the same order onto lookup-comparable environments, so a rule
scoped at the provision resolves at the store. -/
theorem provisionMutualRecs_store_le {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ {l : List (ConstantVal × Nat)} {env env' : Env},
      (∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) →
      ∀ n, ((provisionMutualRecs b fms l env).find? n).isSome = true →
        ((storeMutualRecs env₂ b fms rulesOf l env').find? n).isSome = true
  | [], _, _, hf, n, h => hf n h
  | (cvRa, mIdx) :: rest, env, env', hf, n, h => by
    simp only [provisionMutualRecs] at h
    simp only [storeMutualRecs]
    refine provisionMutualRecs_store_le (l := rest)
      (env := ⟨.recInfo cvRa (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix []
        :: env.consts⟩)
      (env' := ⟨.recInfo cvRa (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
        (mutualRules env₂.find? cvRa.name b.nP
          (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix cvRa.type
          (rulesOf.getD mIdx [])) :: env'.consts⟩) ?_ n h
    exact find?_isSome_cons_mono rfl hf

/-- The store's constants: the environment's own, or one of the `k`
recursors. -/
theorem storeMutualRecs_mem {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {c : ConstantInfo},
      c ∈ (storeMutualRecs env₂ b fms rulesOf l env).consts →
      c ∈ env.consts ∨ ∃ cvRa mIdx, (cvRa, mIdx) ∈ l ∧
        c = .recInfo cvRa (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
          (mutualRules env₂.find? cvRa.name b.nP
            (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix cvRa.type
            (rulesOf.getD mIdx []))
  | [], _, _, h => Or.inl h
  | (cvRa, mIdx) :: rest, env, c, h => by
    simp only [storeMutualRecs] at h
    rcases storeMutualRecs_mem h with hm | ⟨cvRa', mIdx', hmem, rfl⟩
    · rcases List.mem_cons.mp hm with rfl | hm'
      · exact Or.inr ⟨cvRa, mIdx, List.mem_cons_self, rfl⟩
      · exact Or.inl hm'
    · exact Or.inr ⟨cvRa', mIdx', List.mem_cons_of_mem _ hmem, rfl⟩

/-- **Stage 4 at the run level**: the `k` recursors stored as a group
with their rules keep the environment well-formed. -/
theorem mutual_recs_wf {env₂ : Env} (henv₂ : EnvWF env₂) {b : MutualBlock}
    {fms : List MutualFormerA} {formers4 : List MutualFormer} {ctors4 : List MutualCtor4}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {cvRas : List ConstantVal}
    {rulesOf : List (List (MutualCtor × Expr))} {F : Nat}
    (hrectys : checkMutualRecTys (fueledOps mode F) env₂ b formers4 ctors4 streamRecs b.k
      = .ok cvRas)
    (hrules : checkMutualAllRules (m := CheckM)
      (provisionMutualRecs b fms cvRas.zipIdx env₂) b formers4 ctors4 streamRecs b.k
      = .ok rulesOf) :
    EnvWF (storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂) := by
  obtain ⟨hlenR, hallR⟩ := checkMutualRecTys_inv hrectys
  obtain ⟨hlenU, hallU⟩ := checkMutualAllRules_inv hrules
  refine envWF_of_le henv₂ (fun n => storeMutualRecs_le n) ?_
  intro c hc
  rcases storeMutualRecs_mem hc with hm | ⟨cvRa, mIdx, hmem, rfl⟩
  · exact Or.inl hm
  right
  -- the member's index and its recursor's own stage
  have hget : cvRas[mIdx]? = some cvRa := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  have hlt : mIdx < b.k := by
    have := (List.getElem?_eq_some_iff.mp hget).1
    omega
  obtain ⟨cvRa', hget', hrec⟩ := hallR mIdx hlt
  obtain rfl := Option.some.inj (hget.symm.trans hget')
  obtain ⟨recTy, sty, u, -, hlp, hres, hbv, hfv, -, -, -, rfl⟩ :=
    checkMutualRecTy_shape hrec
  -- the member's rules
  obtain ⟨rl, hrlget, hrl⟩ := hallU mIdx hlt
  have hrlD : rulesOf.getD mIdx [] = rl := by
    rw [List.getD_eq_getElem?_getD, hrlget]; rfl
  rw [hrlD]
  refine structConstWF hfv hlp
    (Expr.constsResolve_le (fun n => storeMutualRecs_le n) hres) hbv
    (fun _ _ _ heq => nomatch heq) ?_
  intro cvR' mI' rP' rules' heq r hr
  injection heq with e1 e2 e3 e4
  subst e1
  subst e4
  obtain ⟨⟨cr, hcr, hrhs⟩, hfire⟩ := mutualRules_mem hr
  obtain ⟨hrfv, hrlp, hrres, hrbv⟩ := checkMutualMemberRules_mem hrl hcr
  refine ⟨by rw [hrhs]; exact hrfv, by rw [hrhs]; exact hrlp, ?_, by rw [hrhs]; exact hrbv, ?_⟩
  · rw [hrhs]
    exact Expr.constsResolve_le (provisionMutualRecs_store_le (fun _ h => h)) hrres
  · intro lvls pins hf
    exact absurd hf (hfire lvls pins)

/-! ## Stage 5: the projection tables -/

/-- One member's table stage keeps the environment well-formed. -/
theorem mutualMemberTable_wf {b : MutualBlock} {f : MutualFormerA}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} {mIdx : Nat}
    {env env' : Env} (henv : EnvWF env)
    (h : mutualMemberTable (m := CheckM) b f ctorsA sortss mIdx env = .ok env') :
    EnvWF env' := by
  rcases mutualMemberTable_inv h with rfl | ⟨J, c, -, -, htbl⟩
  · exact henv
  · exact direct_table_wf henv htbl

/-- Stage 5 at the run level. -/
theorem mutualTables_wf {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} :
    ∀ {l : List (MutualFormerA × Nat)} {env env' : Env},
      EnvWF env →
      mutualTables (m := CheckM) b ctorsA sortss l env = .ok env' →
      EnvWF env'
  | [], env, env', henv, h => by
    obtain rfl := mutualTables_nil_inv h
    exact henv
  | (f, mIdx) :: rest, env, env', henv, h => by
    obtain ⟨envI, hI, hrest⟩ := mutualTables_inv h
    exact mutualTables_wf (mutualMemberTable_wf henv hI) hrest

/-! ## The install -/

/-- **The mutual core keeps the environment well-formed.** -/
theorem checkMutualCore_wf {env envOut : Env} (henv : EnvWF env) {b : MutualBlock}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {F : Nat}
    (h : checkMutualCore (fueledOps mode F) env b streamRecs = .ok envOut) :
    EnvWF envOut := by
  obtain ⟨-, -, -, -, env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4,
    cvRas, rulesOf, hformers, -, -, -, -, hctors, -, -, -, hrectys, hrules, htbl⟩ :=
    checkMutualCore_inv h
  have henv₁ : EnvWF env₁ := envWF_mutualFormers henv hformers
  have henv₂ : EnvWF (consMutualCtors b.nP ctorsA env₁) :=
    envWF_consMutualCtors henv₁ (checkMutualCtors_typeWF hctors)
  exact mutualTables_wf (mutual_recs_wf henv₂ hrectys hrules) htbl

/-- **The recognised mutual block's install keeps the environment
well-formed.** -/
theorem checkMutual_wf {env envOut : Env} (henv : EnvWF env) {p : MutualParts} {F : Nat}
    (h : checkMutual (fueledOps mode F) env p = .ok envOut) : EnvWF envOut :=
  checkMutualCore_wf henv (checkMutual_inv h).2

end ConLeche
