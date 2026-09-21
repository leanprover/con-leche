module

public import ConLeche.Verify.Inductives.FixWF
public import ConLeche.Verify.Inductives.BlockInv

public section

/-!
# The uniform install: environment well-formedness at k members
(the uniform inductive route, milestone M4)

`EnvWF` for the environments `checkBlock` walks through — `FixWF.lean`
and `SumWF.lean` at k members:

* **the k formers consed at once** (`envWF_consBlockInds`,
  `direct_block_inds_wf`), each with ITS capability record at the
  block's `is_rec` verdict; the record names the parameter count as its
  arity (`blockCapsAt_arity`, `blockCaps_arity`), which is what makes
  `IndCapsWF` hold at every former's cons;
* **the N constructors consed, member by member**
  (`envWF_consBlockCtors`, `direct_block_ctors_wf`);
* **the k recursors consed with their rules** (`envWF_consBlockRecs`),
  each rule's right-hand side scoped by the recursor stage at the
  environment holding that recursor's RULE-LESS cons — which finds
  exactly the names the stored cons finds; the rules themselves are
  `sumRules`' per member, so `sumRules_mem`/`sumRules_bits`
  (`SumWF.lean`) are the block's rule facts unchanged;
* **the projection tables** (`direct_block_tables_wf`).

`checkBlockRec_facts` is the recursor stage's WF contract: at ONE
member it is the existing generate-and-compare's
(`checkNativeRec_facts`), at two or more the stage declines, so the
contract holds at every k.  Milestone M5 re-proves it for the CHECK
that replaces the stage.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

/-! ## The capability record's arity -/

/-- **The block's capability record names the parameter count as its
arity** (`nativeCapsAt_arity` at a member): what establishes
`IndCapsWF` at every former's cons. -/
theorem blockCapsAt_arity (p : BlockShape) (mi : Nat) (isRec : Bool) :
    ((blockCapsAt p mi isRec).unitlike = true → (blockCapsAt p mi isRec).unitParams = p.nP) ∧
    ((blockCapsAt p mi isRec).eta = true → (blockCapsAt p mi isRec).etaParams = p.nP) := by
  unfold blockCapsAt
  split
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- `blockCapsAt_arity` at the classified verdict. -/
theorem blockCaps_arity (p : BlockParts) (mi : Nat) :
    ((blockCaps p mi).unitlike = true → (blockCaps p mi).unitParams = p.nP) ∧
    ((blockCaps p mi).eta = true → (blockCaps p mi).etaParams = p.nP) :=
  blockCapsAt_arity p.toBlockShape mi (blockIsRec p.kinds)

/-! ## Stage 1: the k formers consed at once -/

/-- Resolution carries along the members' formers' conses. -/
theorem constsResolve_consBlockInds {p₁ : BlockShape} {isRec : Bool} {e : Expr} :
    ∀ {cvTas : List ConstantVal} {i : Nat} {env : Env},
      e.constsResolve env = true →
      e.constsResolve (consBlockInds p₁ isRec cvTas i env) = true
  | [], _, _, h => h
  | _ :: _, _, _, h => by
    simp only [consBlockInds]
    exact constsResolve_consBlockInds (Expr.constsResolve_mono h)

/-- **The k formers' conses keep well-formedness**: each stored former
is a checked constant whose telescope strips at the parameter count,
which is the capability record's arity. -/
theorem envWF_consBlockInds {p₁ : BlockShape} {isRec : Bool} :
    ∀ {cvTas : List ConstantVal} {i : Nat} {env : Env},
      EnvWF env →
      (∀ cvTa ∈ cvTas, cvTa.type.hasFvar = false ∧
        cvTa.type.allLevelParamsDefined cvTa.levelParams = true ∧
        cvTa.type.constsResolve env = true ∧
        cvTa.type.looseBVarsBounded 0 = true ∧
        (cvTa.type.stripPis p₁.nP).isSome = true) →
      EnvWF (consBlockInds p₁ isRec cvTas i env)
  | [], _, _, henv, _ => henv
  | cvTa :: rest, i, env, henv, hall => by
    simp only [consBlockInds]
    refine envWF_consBlockInds ?_ ?_
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hall cvTa List.mem_cons_self
      refine EnvWF.cons henv (structConstWF h1 h2 (Expr.constsResolve_mono h3) h4
        (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
        (by intro tbl hh; exact ConstantInfo.noConfusion hh) ?_)
      refine IndCapsWF.of_caps ?_ ?_
      · intro hu; rw [(blockCapsAt_arity p₁ i isRec).1 hu]; exact h5
      · intro he; rw [(blockCapsAt_arity p₁ i isRec).2 he]; exact h5
    · intro cvTa' hc'
      obtain ⟨h1, h2, h3, h4, h5⟩ := hall cvTa' (List.mem_cons_of_mem _ hc')
      exact ⟨h1, h2, Expr.constsResolve_mono h3, h4, h5⟩

/-- **Stage 1 at the run level**: the environment holding the k formers
is well-formed, and every annotated former's type is closed. -/
theorem direct_block_inds_wf {env envI : Env} (henv : EnvWF env)
    {p : BlockParts} {isRec : Bool} {cvTas : List ConstantVal} {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, cvTas, p₁)) :
    EnvWF envI ∧ ∀ cvTa ∈ cvTas, cvTa.type.hasFvar = false := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, rfl, rfl, rfl, hq, hcvs, -⟩ :=
    checkBlockInds_shape h
  have key : ∀ cvTa ∈ cvTa0 :: cvs.map (·.1),
      cvTa.type.hasFvar = false ∧
      cvTa.type.allLevelParamsDefined cvTa.levelParams = true ∧
      cvTa.type.constsResolve env = true ∧
      cvTa.type.looseBVarsBounded 0 = true ∧
      (cvTa.type.stripPis (p.toBlockShape.withSort s0).nP).isSome = true := by
    intro cvTa hcv
    have step : ∀ (ms : MemberShape) (s : Level),
        checkBlockTele (fueledOps mode F) env p.nP ms = .ok (cvTa, s) →
        cvTa.type.hasFvar = false ∧
        cvTa.type.allLevelParamsDefined cvTa.levelParams = true ∧
        cvTa.type.constsResolve env = true ∧
        cvTa.type.looseBVarsBounded 0 = true ∧
        (cvTa.type.stripPis (p.toBlockShape.withSort s0).nP).isSome = true := by
      intro ms s hte
      obtain ⟨cvT, -, -, hccv, bs, hstrip⟩ := checkBlockTele_shape hte
      obtain ⟨g1, g2, g3, g4⟩ := checkConstantVal_typeWF hccv
      refine ⟨g1, g2, g3, g4, ?_⟩
      refine stripPis_isSome_of_le (n := p.nP + ms.nIdx) (Nat.le_add_right _ _) ?_
      rw [hstrip]; rfl
    simp only [List.mem_cons] at hcv
    rcases hcv with rfl | hcv
    · exact step ms0 s0 hq
    · obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hcv
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hq'
      obtain ⟨hlen, hall⟩ := checkBlockTeles_inv hcvs
      have hil : i < rest.length := by
        rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨q', hq'', hte⟩ := hall i rest[i] (List.getElem?_eq_getElem hil)
      obtain rfl := Option.some.inj (hi.symm.trans hq'')
      exact step rest[i] q.2 hte
  exact ⟨envWF_consBlockInds henv key, fun cvTa hcv => (key cvTa hcv).1⟩

/-! ## Stage 1b: the constructors consed, member by member -/

/-- Resolution carries along one member's constructors' conses. -/
theorem constsResolve_consSumCtors {nP : Nat} {e : Expr} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      e.constsResolve env = true → e.constsResolve (consSumCtors nP ctorsA env) = true
  | [], _, h => h
  | _ :: _, _, h => by
    simp only [consSumCtors]
    exact constsResolve_consSumCtors (Expr.constsResolve_mono h)

/-- Resolution carries along all the members' constructors' conses. -/
theorem constsResolve_consBlockCtors {nP : Nat} {e : Expr} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env : Env},
      e.constsResolve env = true → e.constsResolve (consBlockCtors nP ctorsAs env) = true
  | [], _, h => h
  | _ :: _, _, h => by
    simp only [consBlockCtors]
    exact constsResolve_consBlockCtors (constsResolve_consSumCtors h)

/-- **The members' constructors' conses keep well-formedness**
(`envWF_consSumCtors` at k members). -/
theorem envWF_consBlockCtors {nP : Nat} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env : Env},
      EnvWF env →
      (∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, c.1.type.hasFvar = false ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true) →
      EnvWF (consBlockCtors nP ctorsAs env)
  | [], _, henv, _ => henv
  | ctorsA :: rest, env, henv, hall => by
    simp only [consBlockCtors]
    refine envWF_consBlockCtors
      (envWF_consSumCtors henv (hall ctorsA List.mem_cons_self)) ?_
    intro ctorsA' hc' c hc
    obtain ⟨h1, h2, h3, h4⟩ := hall ctorsA' (List.mem_cons_of_mem _ hc') c hc
    exact ⟨h1, h2, constsResolve_consSumCtors h3, h4⟩

/-- **Stage 1b at the run level**: the environment holding the k
formers and all the constructors is well-formed. -/
theorem direct_block_ctors_wf {env₀ env₁ : Env} (henv : EnvWF env₁)
    {q : BlockShape} {l : List (MemberShape × ConstantVal)}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    {nP F : Nat}
    (h : checkBlockCtors (fueledOps mode F) env₀ env₁ q l = .ok (ctorsAs, sortsss)) :
    EnvWF (consBlockCtors nP ctorsAs env₁) := by
  obtain ⟨hlen, -, hall⟩ := checkBlockCtors_inv h
  refine envWF_consBlockCtors henv ?_
  intro ctorsA hcA c hc
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hcA
  have hil : i < l.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨ctorsA', sortss, hcA', -, hcs⟩ := hall i l[i] (List.getElem?_eq_getElem hil)
  obtain rfl := Option.some.inj (hi.symm.trans hcA')
  obtain ⟨-, -, hallc⟩ := checkSumCtors_inv hcs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  have hjl : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjl' : j < l[i].1.ctors.length := by
    obtain ⟨hlc, -, -⟩ := checkSumCtors_inv hcs
    omega
  obtain ⟨-, sorts, -, hctor⟩ :=
    hallc j l[i].1.ctors[j] c (List.getElem?_eq_getElem hjl') hj
  exact direct_sum_ctor_typeWF hctor

/-! ## The recursor stage's well-formedness contract -/

/-- **The recursor stage's stored pieces**, as its own guards checked
them: at ONE member the existing generate-and-compare's
(`checkNativeRec_facts`), at two or more members the stage declines, so
the contract holds at every k.  Milestone M5 re-proves it for the CHECK
that replaces the stage. -/
theorem checkBlockRec_facts {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRec (fueledOps mode F) env p cvTas ctorsAs = .ok rs) :
    ∀ r ∈ rs, r.1.type.hasFvar = false ∧
      r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
      r.1.type.constsResolve env = true ∧
      r.1.type.looseBVarsBounded 0 = true ∧
      ∀ rhs ∈ r.2.1, rhs.hasFvar = false ∧
        rhs.allLevelParamsDefined r.1.levelParams = true ∧
        (∃ mI rP, rhs.constsResolve
          ⟨.recInfo r.1 mI rP [] :: env.consts⟩ = true) ∧
        rhs.looseBVarsBounded 0 = true := by
  unfold checkBlockRec at h
  split at h
  case h_2 =>
    exfalso
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals exact nomatch h
  case h_1 =>
  simp only [bind, Except.bind] at h
  split at h
  case isFalse => exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  case isTrue =>
  obtain ⟨r0, hrec, h⟩ := exceptBind_ok h
  obtain ⟨cvRa, rhss⟩ := r0
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨-, -, ⟨htf, htp, htr, htb⟩, -, hall⟩ := checkNativeRec_facts hrec
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  refine ⟨htf, htp, htr, htb, ?_⟩
  intro rhs hrhs
  obtain ⟨g1, g2, g3, g4⟩ := hall rhs hrhs
  exact ⟨g1, g2, ⟨_, _, g3⟩, g4⟩

/-! ## The k recursors consed with their rules -/

/-- A name found above one cons is found above two. -/
theorem find?_isSome_cons_under {a b : ConstantInfo} {env : Env} (n : Name)
    (h : (Env.find? ⟨a :: env.consts⟩ n).isSome = true) :
    (Env.find? ⟨a :: b :: env.consts⟩ n).isSome = true := by
  rw [Env.find?_cons] at h
  show (Env.find? ⟨a :: (Env.mk (b :: env.consts)).consts⟩ n).isSome = true
  rw [Env.find?_cons]
  split at h
  · next hn => rw [if_pos hn]; simp
  · next hn =>
    rw [if_neg hn, Env.find?_cons]
    split <;> simp_all

/-- **The k recursors' conses keep well-formedness**: every rule's
right-hand side is scoped at the environment holding that recursor's
rule-less cons, which finds exactly the names the stored cons finds,
and no stored rule is `.nested` (`sumRules_mem`). -/
theorem envWF_consBlockRecs {find? : Name → Option ConstantInfo} {nP rP : Nat} :
    ∀ {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {env : Env},
      EnvWF env →
      (∀ r ∈ rs, r.1.type.hasFvar = false ∧
        r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
        r.1.type.constsResolve env = true ∧
        r.1.type.looseBVarsBounded 0 = true ∧
        ∀ rhs ∈ r.2.1, rhs.hasFvar = false ∧
          rhs.allLevelParamsDefined r.1.levelParams = true ∧
          (∃ mI rP', rhs.constsResolve ⟨.recInfo r.1 mI rP' [] :: env.consts⟩ = true) ∧
          rhs.looseBVarsBounded 0 = true) →
      EnvWF (consBlockRecs find? nP rP rs env)
  | [], _, henv, _ => henv
  | (cvRa, rhss, nIdx, ctorsA) :: rest, env, henv, hall => by
    simp only [consBlockRecs]
    refine envWF_consBlockRecs ?_ ?_
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hall (cvRa, rhss, nIdx, ctorsA) List.mem_cons_self
      refine EnvWF.cons henv (structConstWF h1 h2 (Expr.constsResolve_mono h3) h4
        (fun _ _ _ heq => nomatch heq) ?_)
      intro cvR' mI' rP' rules' heq r hr
      injection heq with e1 e2 e3 e4
      subst e1
      subst e4
      obtain ⟨hmem, hfire⟩ := sumRules_mem hr
      obtain ⟨g1, g2, ⟨mI₀, rP₀, g3⟩, g4⟩ := h5 r.rhs hmem
      refine ⟨g1, g2, Expr.constsResolve_of_find
        (find?_isSome_cons_same (c := .recInfo cvRa mI₀ rP₀ [])
          (c' := .recInfo cvRa (rP + nIdx) rP
            (sumRules find? cvRa.name nP (rP + nIdx) rP cvRa.type ctorsA rhss)) rfl) g3,
        g4, ?_⟩
      intro lvls pins hf
      exact absurd hf (hfire lvls pins)
    · intro r hr
      obtain ⟨h1, h2, h3, h4, h5⟩ := hall r (List.mem_cons_of_mem _ hr)
      refine ⟨h1, h2, Expr.constsResolve_mono h3, h4, ?_⟩
      intro rhs hrhs
      obtain ⟨g1, g2, ⟨mI₀, rP₀, g3⟩, g4⟩ := h5 rhs hrhs
      exact ⟨g1, g2, ⟨mI₀, rP₀,
        Expr.constsResolve_of_find (fun n hn => find?_isSome_cons_under n hn) g3⟩, g4⟩

/-! ## The projection tables -/

/-- **The tables at the run level**: a table is consed at every
structure-like member and nothing at any other, and either keeps
well-formedness. -/
theorem direct_block_tables_wf {q : BlockShape} :
    ∀ {l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))}
      {env env₂ : Env},
      EnvWF env → checkBlockTables (m := CheckM) q l env = .ok env₂ → EnvWF env₂
  | [], env, env₂, henv, h => by
    simp only [checkBlockTables, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ henv
  | (ms, ctorsA, sortss) :: rest, env, env₂, henv, h => by
    unfold checkBlockTables at h
    obtain ⟨env', henv', h⟩ := exceptBind_ok h
    refine direct_block_tables_wf ?_ h
    revert henv'
    split
    · split
      · intro hh; exact direct_table_wf henv hh
      · intro hh
        simp only [pure, Except.pure, Except.ok.injEq] at hh
        exact hh ▸ henv
    · intro hh
      simp only [pure, Except.pure, Except.ok.injEq] at hh
      exact hh ▸ henv

/-! ## The whole install -/

/-- **`EnvWF` through the whole uniform install**: the k formers, the
N constructors, the k recursors with their rules, and the projection
tables. -/
theorem direct_block_wf {env env₂ : Env} (henv : EnvWF env)
    {p₀ : BlockParts} {isRec b : Bool} {q : BlockPass Env} {F : Nat}
    (hP : checkBlockPass (fueledOps mode F) env p₀ isRec = .ok (q, b))
    (h : checkBlockTail (m := CheckM) (fueledOps mode F) env q = .ok env₂) :
    EnvWF env₂ := by
  obtain ⟨p₁, kinds, hInd, hCtors, -, hp, -⟩ := checkBlockPass_inv hP
  obtain ⟨isorts, rs, -, -, -, hRec, hTbl⟩ := checkBlockTail_inv h
  have h1 : EnvWF q.env₁ := (direct_block_inds_wf henv hInd).1
  have h2 : EnvWF (consBlockCtors q.p.nP q.ctorsAs q.env₁) :=
    direct_block_ctors_wf h1 hCtors
  have h3 : EnvWF (consBlockRecs (consBlockCtors q.p.nP q.ctorsAs q.env₁).find?
      q.p.nP q.p.rulePrefix rs (consBlockCtors q.p.nP q.ctorsAs q.env₁)) :=
    envWF_consBlockRecs h2 (checkBlockRec_facts hRec)
  exact direct_block_tables_wf h3 hTbl

end ConLeche
