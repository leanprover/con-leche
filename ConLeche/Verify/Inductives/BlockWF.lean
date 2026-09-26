module

public import ConLeche.Verify.Inductives.SumWF
import ConLeche.Verify.Inductives.SumInv
import ConLeche.Kernel.Inductives.FieldTele
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Shift
import ConLeche.Verify.Inductives.SumRec

public section

/-!
# The uniform install: environment well-formedness at k members
(the uniform inductive route, milestone M4)

`EnvWF` for the environments `checkBlock` walks through — `FixWF.lean`
and `SumWF.lean` at k members:

* **the k formers consed at once** (`envWF_consBlockInds`,
  `direct_block_inds_wf`), each with ITS capability record at the
  block's `is_rec` verdict; the record names the parameter count as its
  arity (`blockCapsAt_arity`), which is what makes
  `IndCapsWF` hold at every former's cons;
* **the N constructors consed, member by member**
  (`envWF_consBlockCtors`, `direct_block_ctors_wf`);
* **the k recursors consed at once, with their rules**
  (`envWF_consBlockRecs`), each rule's right-hand side scoped by the
  recursor stage at the BARE-`k` environment — the one holding all `k`
  RULE-LESS recursors, which finds exactly the names the stored cons
  finds (`find?_consBlockRecs_of_bare`); the rules themselves are
  `sumRules`' per recursor, so `sumRules_mem`/`sumRules_bits`
  (`SumWF.lean`) are the block's rule facts unchanged.

`recStage_facts` is the recursor stage's WF contract; it and
every other inversion of the recursor CHECK read the stage's run
records (`Verify/Inductives/BlockRecRun.lean`).

**Why the recursors are consed SIMULTANEOUSLY** (milestone M6's entry
cost): the CHECK's rules are MUTUALLY recursive — a rule of `rec_0`
may name `rec_1` — so a right-hand side resolves at the environment
holding ALL `k` rule-less recursors and at no environment holding
`rec_0` alone.  `EnvWF`'s recursor clause is checked at the
environment each constant is consed into, so the one-at-a-time
`EnvWF.cons` induction cannot close at `k ≥ 2`; `EnvWF E` is
`∀ c ∈ E.consts, ConstWF E c`, which is provable at the FINAL
environment directly (`mem_consBlockRecs`, `ConstWF.mono`).
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

/-! ## The capability record's arity -/

/-- **The block's capability record names the parameter count as its
arity**: what establishes
`IndCapsWF` at every former's cons. -/
theorem blockCapsAt_arity (p : BlockShape) (mi : Nat) (isRec : Bool) :
    ((blockCapsAt p mi isRec).unitlike = true → (blockCapsAt p mi isRec).unitParams = p.nP) ∧
    ((blockCapsAt p mi isRec).eta = true → (blockCapsAt p mi isRec).etaParams = p.nP) := by
  unfold blockCapsAt
  split
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-! ## Stage 1: the k formers consed at once -/

/-- **One former's cons keeps well-formedness**: the stored former is a
checked constant whose telescope strips at the parameter count, which is
the capability record's arity. -/
theorem envWF_cons_blockInd {p₁ : BlockShape} {isRec : Bool} {i : Nat} {env : Env}
    {cvTa : ConstantVal} (henv : EnvWF env)
    (h1 : cvTa.type.hasFvar = false)
    (h2 : cvTa.type.allLevelParamsDefined cvTa.levelParams = true)
    (h3 : cvTa.type.constsResolve env = true)
    (h4 : cvTa.type.looseBVarsBounded 0 = true)
    (h5 : (cvTa.type.stripPis p₁.nP).isSome = true) :
    EnvWF ⟨.indInfo cvTa (blockCapsAt p₁ i isRec) :: env.consts⟩ := by
  refine EnvWF.cons henv (structConstWF h1 h2 (Expr.constsResolve_mono h3) h4
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (by intro tbl hh; exact ConstantInfo.noConfusion hh) ?_)
  refine IndCapsWF.of_caps ?_ ?_
  · intro hu; rw [(blockCapsAt_arity p₁ i isRec).1 hu]; exact h5
  · intro he; rw [(blockCapsAt_arity p₁ i isRec).2 he]; exact h5

/-- **The k formers' conses keep well-formedness.** -/
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
      exact envWF_cons_blockInd henv h1 h2 h3 h4 h5
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

/-! ## The CHECK, inverted (lane V2 scratch) -/

local syntax "close_throw" term : tactic
local macro_rules
  | `(tactic| close_throw $h:term) =>
    `(tactic| first
        | exact nomatch $h
        | exact absurd $h (by
            simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            exact fun hh => nomatch hh)
        | exact absurd $h
            (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-- A checked constant keeps the record's name and level parameters:
only its type is replaced, by the annotated one. -/
theorem checkConstantVal_lps {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : checkConstantVal (fueledOps mode F) env cv = .ok cvA) :
    cvA.name = cv.name ∧ cvA.levelParams = cv.levelParams := by
  unfold checkConstantVal at h
  by_cases h1 : (env.find? cv.name).isSome = true
  · rw [if_pos h1] at h; close_throw h
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [if_pos h2] at h; close_throw h
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [if_pos h3] at h; close_throw h
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; close_throw h
  rw [if_pos h4] at h
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [if_neg h5] at h; close_throw h
  rw [if_pos h5] at h
  by_cases h6 : cv.type.hasFvar = true
  · rw [if_pos h6] at h; close_throw h
  rw [if_neg h6] at h
  obtain ⟨type, _, h⟩ := exceptBind_ok h
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams type = true
  case neg => rw [if_neg h7] at h; close_throw h
  rw [if_pos h7] at h
  by_cases h8 : Expr.constsResolve env type = true
  case neg => rw [if_neg h8] at h; close_throw h
  rw [if_pos h8] at h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

/-- **The conformance seam reads through** (lane CONF1): a stage
followed by a reject-only check (`thenConform`) succeeded only if the
stage did, with the same result.  This is the ONE fact the proofs need
about the unverified recursor conformance check
(`checkBlockRecConform`): they never peel it. -/
theorem thenConform_ok {α : Type} {stage : CheckM α} {conform : CheckM Unit} {r : α}
    (h : thenConform stage conform = .ok r) : stage = .ok r := by
  unfold thenConform at h
  obtain ⟨a, hs, h⟩ := exceptBind_ok h
  obtain ⟨u, -, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact hs

/-- **The recursor stage read back to the CHECK**: `checkBlockRec`
succeeded only if the check (`checkBlockRecT`, the target check) did,
with the same result (the conformance check after it only rejects). -/
theorem checkBlockRecT_of_rec {ops : CheckerOps CheckM} {env : Env} {p : BlockParts}
    {nst nested conf : Bool} {aux : NestNodes}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs ctorsN : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (h : checkBlockRec ops env p nst nested conf aux block cvTas ctorsAs ctorsN = .ok out) :
    checkBlockRecT ops env p nst nested aux block cvTas ctorsAs = .ok out :=
  thenConform_ok h

/-! ## The k recursors consed with their rules, SIMULTANEOUSLY -/

/-- Well-formedness of a stored constant transfers along a lookup
dominance: every clause of `ConstWF` depends on the environment only
through `constsResolve`, and the capability arities not at all. -/
theorem ConstWF.mono {envA envB : Env}
    (hf : ∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true)
    {c : ConstantInfo} (h : ConstWF envA c) : ConstWF envB c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩ := h
  refine ⟨h1, h2, Expr.constsResolve_le hf h3, h4, fun cv value hint heq =>
    let ⟨g1, g2, g3, g4⟩ := h5 cv value hint heq
    ⟨g1, g2, Expr.constsResolve_le hf g3, g4⟩, ?_,
    fun tbl heq =>
      let ⟨g0, g⟩ := h8 tbl heq
      ⟨g0, fun i b hb =>
        let ⟨g1, g2, g3, g4⟩ := g i b hb
        ⟨g1, g2, Expr.constsResolve_le hf g3, g4⟩⟩, h9⟩
  intro cv mI rP rules heq r hr
  obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv mI rP rules heq r hr
  refine ⟨g1, g2, Expr.constsResolve_le hf g3, g4, ?_⟩
  intro lvls pins hfr
  obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hfr
  exact ⟨n1, n2, fun pin hpin =>
    let ⟨p1, p2, p3, p4⟩ := n3 pin hpin
    ⟨p1, p2, Expr.constsResolve_le hf p3, p4⟩, n4⟩

/-- Conses of the SAME name over dominating environments dominate. -/
theorem find?_cons_mono {c c' : ConstantInfo} {envA envB : Env} (hn : c.name = c'.name)
    (hf : ∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true) :
    ∀ n, (Env.find? ⟨c :: envA.consts⟩ n).isSome = true →
      (Env.find? ⟨c' :: envB.consts⟩ n).isSome = true := by
  intro n h
  rw [Env.find?_cons] at h
  rw [Env.find?_cons, ← hn]
  split at h
  · next hh => rw [if_pos hh]; simp
  · next hh => rw [if_neg hh]; exact hf n h

/-! ### The recursors' cons, generic in the STORED RULES (lane NESTIND, session 14)

The install conses the checked family in two forms: `consBlockRecs`
(every rule `sumRules`' at the block's parameter count — the switch-off
route) and `consBlockRecsT` (each recursor's rules at ITS major,
`.nested` at an outside one — the switch-on route).  Both are
`consBlockRecsR` at a rules function `R` (the recursor's absolute
position and its stored datum ↦ its rule list): `consBlockRecs_eq_R`
here, `consBlockRecsT_eq_R` (`RecStage.lean`).  Every fact about the
cons below is proved ONCE at `R`; the facts about the RULES are
premises, discharged per instance. -/

/-- **The recursors consed with their rules, at a rules function `R`.** -/
@[expose] def consBlockRecsR
    (R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List RecRule)
    (q : BlockShape) :
    Nat → List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) → Env → Env
  | _, [], env => env
  | m, r :: rest, env =>
    consBlockRecsR R q (m + 1) rest
      ⟨.recInfo r.1 (q.majorIdxAt m) (q.rulePrefixAt m) (R m r) :: env.consts⟩

/-- The switch-off route's rules function: `sumRules` at the block's
parameter count. -/
@[expose] def sumRulesR (find? : Name → Option ConstantInfo) (q : BlockShape) (nP : Nat) :
    Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List RecRule :=
  fun m r => sumRules find? r.1.name nP (q.majorIdxAt m) (q.rulePrefixAt m) r.1.type r.2.2.2 r.2.1

/-- **`consBlockRecs` is the generic cons at `sumRulesR`.** -/
theorem consBlockRecs_eq_R (find? : Name → Option ConstantInfo) (q : BlockShape) (nP : Nat) :
    ∀ (m : Nat) (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
      (env : Env),
      consBlockRecs find? q nP m rs env = consBlockRecsR (sumRulesR find? q nP) q m rs env
  | _, [], _ => rfl
  | m, (cvRa, rhss, nIdx, ctorsA) :: rest, env => by
    simp only [consBlockRecs, consBlockRecsR]
    exact consBlockRecs_eq_R find? q nP (m + 1) rest _

/-- **The stored rules' SHAPE at a rules function**: every rule the cons
stores for the recursor at position `j` is the `i`-th constructor's, at
the `i`-th right-hand side, with the constructor's parameter count
`nPc j` and the firing `fireOf j r`, its two rescue bits read by
`recRuleBits` at `find?`.  Both routes' rules have it
(`recRulesShape_sum`; `recRulesShape_tgt`, `RecStage.lean`). -/
@[expose] def RecRulesShape (find? : Name → Option ConstantInfo)
    (R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List RecRule)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (nPc : Nat → Nat)
    (fireOf : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → RecRuleFire) :
    Prop :=
  ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rs[j]? = some r →
    ∀ rl ∈ R j r, ∃ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA ∧ r.2.1[i]? = some rhs ∧
      rl = recRuleBits find? r.1.name
        { ctor := cA.1.name, nfields := cA.2, ctorParams := nPc j,
          fire := fireOf j r, rhs := rhs, paramsBlind := true }

/-- The switch-off route's rules have the shape, at the block's
parameter count and `sumRules`' firing. -/
theorem recRulesShape_sum (find? : Name → Option ConstantInfo) (q : BlockShape) (nP : Nat)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) :
    RecRulesShape find? (sumRulesR find? q nP) rs (fun _ => nP)
      (fun j r => if Expr.recRulePlain r.1.type (q.majorIdxAt j) (q.rulePrefixAt j) nP
        then .plain else .inert) :=
  fun _ _ _ _ hrl => sumRules_getElem? hrl

/-- The recursors' cons finds everything the environment below it
finds. -/
theorem find?_consBlockRecsR_le
    {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List RecRule}
    {q : BlockShape} :
    ∀ {m : Nat} {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
      {env : Env} (n : Name),
      (env.find? n).isSome = true →
      ((consBlockRecsR R q m rs env).find? n).isSome = true
  | _, [], _, _, h => h
  | _, _ :: _, env, n, h => by
    simp only [consBlockRecsR]
    refine find?_consBlockRecsR_le n ?_
    rw [Env.find?_cons]
    split <;> simp_all

/-- The recursors' cons finds everything the environment below it
finds (`sumRulesR`). -/
theorem find?_consBlockRecs_le {find? : Name → Option ConstantInfo} {q : BlockShape} {nP : Nat}
    {m : Nat} {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {env : Env} (n : Name) (h : (env.find? n).isSome = true) :
    ((consBlockRecs find? q nP m rs env).find? n).isSome = true := by
  rw [consBlockRecs_eq_R]; exact find?_consBlockRecsR_le n h

/-- **The bare-`k` environment finds no name the stored one does not**:
`consBlockRecsBare` and `consBlockRecsR` cons the same names in the same
order, and resolution reads the environment through its names alone.
This is what carries the new stage's rule scoping — stated at the
environment holding all `k` RULE-LESS recursors — to the environment
the rules are STORED in. -/
theorem find?_consBlockRecsR_of_bare
    {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List RecRule}
    {q : BlockShape} :
    ∀ {m : Nat} {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
      {envA envB : Env},
      (∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true) →
      ∀ n, ((consBlockRecsBare q m (rs.map fun r => (r.1, r.2.2.1)) envA).find? n).isSome = true →
        ((consBlockRecsR R q m rs envB).find? n).isSome = true
  | _, [], _, _, hf, n, h => hf n h
  | m, r0 :: rest, envA, envB, hf, n, h => by
    simp only [List.map_cons, consBlockRecsBare] at h
    simp only [consBlockRecsR]
    refine find?_consBlockRecsR_of_bare
      (envA := ⟨.recInfo r0.1 (q.majorIdxAt m) (q.rulePrefixAt m) [] :: envA.consts⟩) ?_ n h
    exact find?_cons_mono rfl hf

/-- **What the recursors' cons holds**: the `k` recursor records, each
with its rules at its absolute position, and what was stored below
them. -/
theorem mem_consBlockRecsR
    {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List RecRule}
    {q : BlockShape} :
    ∀ {m : Nat} {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
      {env : Env} {c : ConstantInfo},
      c ∈ (consBlockRecsR R q m rs env).consts →
      c ∈ env.consts ∨ ∃ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
        rs[j]? = some r ∧
        c = .recInfo r.1 (q.majorIdxAt (m + j)) (q.rulePrefixAt (m + j)) (R (m + j) r)
  | _, [], _, _, h => Or.inl h
  | m, r0 :: rest, env, c, h => by
    simp only [consBlockRecsR] at h
    rcases mem_consBlockRecsR h with h' | ⟨j, r, hr, hj⟩
    · rcases List.mem_cons.mp h' with rfl | h'
      · exact Or.inr ⟨0, r0, rfl, by rw [Nat.add_zero]⟩
      · exact Or.inl h'
    · refine Or.inr ⟨j + 1, r, by simpa using hr, ?_⟩
      rw [show m + (j + 1) = m + 1 + j by omega]
      exact hj

/-- **The k recursors' cons keeps well-formedness — SIMULTANEOUSLY.**

The `k` rule-carrying records are consed onto one environment and
every one of them is checked against the FINAL one: `EnvWF E` is
`∀ c ∈ E.consts, ConstWF E c`, so nothing forces a per-record
intermediate environment, and nothing could — a rule of `rec_0` may
name `rec_1`, so it resolves only where all `k` recursors stand.  Its
scoping hypothesis is therefore stated at the BARE-`k` environment,
which finds exactly the names the stored cons finds
(`find?_consBlockRecsR_of_bare`).  The rules' own facts are the premise
`hrules`: each stored rule's right-hand side is one the stage scoped, and
a `.nested` rule's pins satisfy `EnvWF`'s clause at the environment
below. -/
theorem envWF_consBlockRecsR
    {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List RecRule}
    {q : BlockShape}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {env : Env}
    (henv : EnvWF env)
    (hall : ∀ r ∈ rs, r.1.type.hasFvar = false ∧
      r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
      r.1.type.constsResolve env = true ∧
      r.1.type.looseBVarsBounded 0 = true ∧
      ∀ rhs ∈ r.2.1, rhs.hasFvar = false ∧
        rhs.allLevelParamsDefined r.1.levelParams = true ∧
        rhs.constsResolve (consBlockRecsBare q 0 (rs.map fun r => (r.1, r.2.2.1)) env) = true ∧
        rhs.looseBVarsBounded 0 = true)
    (hrules : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ rl ∈ R j r,
        rl.rhs ∈ r.2.1 ∧
        ∀ lvls pins, rl.fire = .nested lvls pins →
          q.rulePrefixAt j ≤ q.majorIdxAt j ∧
          (∀ l ∈ lvls, l.allParamsDefined r.1.levelParams = true) ∧
          (∀ pin ∈ pins, pin.hasFvar = false ∧
            pin.allLevelParamsDefined r.1.levelParams = true ∧
            pin.constsResolve env = true ∧
            pin.looseBVarsBounded (q.rulePrefixAt j) = true) ∧
          ∃ pre dom body bm D,
            r.1.type.stripPis (q.majorIdxAt j) = some (pre, .forallE dom body bm) ∧
            dom.getAppFn = .const D lvls ∧
            dom.getAppArgs =
              pins.map (Expr.liftLooseBVars (q.majorIdxAt j - q.rulePrefixAt j) 0) ++
                (List.range (q.majorIdxAt j - q.rulePrefixAt j)).map
                  (fun i => Expr.bvar (q.majorIdxAt j - q.rulePrefixAt j - 1 - i))) :
    EnvWF (consBlockRecsR R q 0 rs env) := by
  have hdomEnv : ∀ n, (env.find? n).isSome = true →
      ((consBlockRecsR R q 0 rs env).find? n).isSome = true :=
    fun n hn => find?_consBlockRecsR_le n hn
  have hdomBare : ∀ n,
      ((consBlockRecsBare q 0 (rs.map fun r => (r.1, r.2.2.1)) env).find? n).isSome = true →
      ((consBlockRecsR R q 0 rs env).find? n).isSome = true :=
    find?_consBlockRecsR_of_bare (fun _ hn => hn)
  intro c hc
  rcases mem_consBlockRecsR hc with hc' | ⟨j, r, hr, rfl⟩
  · exact ConstWF.mono hdomEnv (henv c hc')
  · rw [Nat.zero_add]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hall r (List.mem_of_getElem? hr)
    refine structConstWF h1 h2 (Expr.constsResolve_le hdomEnv h3) h4
      (fun _ _ _ heq => nomatch heq) ?_
    intro cvR' mI' rP' rules' heq rl hrl
    injection heq with e1 e2 e3 e4
    subst e1 e2 e3 e4
    obtain ⟨hmem, hfire⟩ := hrules j r hr rl hrl
    obtain ⟨g1, g2, g3, g4⟩ := h5 rl.rhs hmem
    refine ⟨g1, g2, Expr.constsResolve_le hdomBare g3, g4, ?_⟩
    intro lvls pins hf
    obtain ⟨n1, n2, n3, n4⟩ := hfire lvls pins hf
    exact ⟨n1, n2, fun pin hpin =>
      let ⟨p1, p2, p3, p4⟩ := n3 pin hpin
      ⟨p1, p2, Expr.constsResolve_le hdomEnv p3, p4⟩, n4⟩

/-- **The k recursors' cons keeps well-formedness** at `sumRulesR`: the
rules are `sumRules`' per recursor, so `sumRules_mem` is the block's
rule fact unchanged (never `.nested`). -/
theorem envWF_consBlockRecs {find? : Name → Option ConstantInfo} {q : BlockShape} {nP : Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {env : Env}
    (henv : EnvWF env)
    (hall : ∀ r ∈ rs, r.1.type.hasFvar = false ∧
      r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
      r.1.type.constsResolve env = true ∧
      r.1.type.looseBVarsBounded 0 = true ∧
      ∀ rhs ∈ r.2.1, rhs.hasFvar = false ∧
        rhs.allLevelParamsDefined r.1.levelParams = true ∧
        rhs.constsResolve (consBlockRecsBare q 0 (rs.map fun r => (r.1, r.2.2.1)) env) = true ∧
        rhs.looseBVarsBounded 0 = true) :
    EnvWF (consBlockRecs find? q nP 0 rs env) := by
  rw [consBlockRecs_eq_R]
  refine envWF_consBlockRecsR henv hall fun j r _ rl hrl => ?_
  obtain ⟨hmem, hfire⟩ := sumRules_mem hrl
  exact ⟨hmem, fun lvls pins hf => absurd hf (hfire lvls pins)⟩

/-! ## The literal guards across the recursors' cons

The recursors' cons must not change what a `Nat` or `String` literal
READS.  Both guards decide that by looking fixed names up in the store
(`litGuardNames`), and the stage refuses a recursor under any of them
(`blockRecNamesUnreserved`, inverted as `checkBlockRecPins_reserved`),
so every one of those lookups crosses the cons untouched.

Without the stage's check the `String` guard is only MONOTONE, and
refutably so: `listConsTyOk` asks for a constant `List.cons.{p} :
∀ (α : Type p) (h : α) (t : List.{p} α), List.{p} α`, and a block
declaring `List : Type p → Type p` with a recursor NAMED `List.cons`
of exactly that type would flip `strLitSupported` from `false` to
`true` across its own recursor stage. -/

/-- **A name no recursor of the block carries reads through the cons
unchanged.** -/
theorem find?_consBlockRecsR_of_ne
    {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List RecRule}
    {q : BlockShape} {n : Name} :
    ∀ {m : Nat} {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
      {env : Env},
      (∀ r ∈ rs, n ≠ r.1.name) →
      (consBlockRecsR R q m rs env).find? n = env.find? n
  | _, [], _, _ => rfl
  | m, r0 :: rest, env, hne => by
    rw [consBlockRecsR,
      find?_consBlockRecsR_of_ne (fun r hr => hne r (List.mem_cons_of_mem _ hr)),
      Env.find?_cons, if_neg (fun h => hne r0 List.mem_cons_self h.symm)]

/-- `find?_consBlockRecsR_of_ne` at `sumRulesR`. -/
theorem find?_consBlockRecs_of_ne {find? : Name → Option ConstantInfo}
    {q : BlockShape} {nP : Nat} {n : Name} {m : Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {env : Env}
    (hne : ∀ r ∈ rs, n ≠ r.1.name) :
    (consBlockRecs find? q nP m rs env).find? n = env.find? n := by
  rw [consBlockRecs_eq_R]; exact find?_consBlockRecsR_of_ne hne

/-- A name a literal guard looks up is no recursor of a CHECKED
block. -/
theorem ne_of_reservedRecName
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {n : Name}
    (hnres : ∀ r ∈ rs, reservedRecName r.1.name = false)
    (hn : reservedRecName n = true) : ∀ r ∈ rs, n ≠ r.1.name := by
  intro r hr hh
  rw [hh, hnres r hr] at hn
  exact nomatch hn

/-- **The `Nat`-literal guard is CONGRUENT across the recursors'
cons.** -/
theorem natLitSupported_consBlockRecsR
    {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List RecRule}
    {q : BlockShape}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {env : Env}
    (hnres : ∀ r ∈ rs, reservedRecName r.1.name = false) :
    natLitSupported (consBlockRecsR R q 0 rs env) = natLitSupported env := by
  unfold natLitSupported
  rw [find?_consBlockRecsR_of_ne (ne_of_reservedRecName hnres (by decide)),
    find?_consBlockRecsR_of_ne (ne_of_reservedRecName (n := natZeroName) hnres (by decide)),
    find?_consBlockRecsR_of_ne (ne_of_reservedRecName (n := natSuccName) hnres (by decide))]

/-- `natLitSupported_consBlockRecsR` at `sumRulesR`. -/
theorem natLitSupported_consBlockRecs {find? : Name → Option ConstantInfo}
    {q : BlockShape} {nP : Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {env : Env}
    (hnres : ∀ r ∈ rs, reservedRecName r.1.name = false) :
    natLitSupported (consBlockRecs find? q nP 0 rs env) = natLitSupported env := by
  rw [consBlockRecs_eq_R]; exact natLitSupported_consBlockRecsR hnres

/-- **The `String`-literal guard is CONGRUENT across the recursors'
cons** — the equation the model's reading law needs, and the reason
`blockRecNamesUnreserved` is checked at all. -/
theorem strLitSupported_consBlockRecsR
    {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List RecRule}
    {q : BlockShape}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {env : Env}
    (hnres : ∀ r ∈ rs, reservedRecName r.1.name = false) :
    strLitSupported (consBlockRecsR R q 0 rs env) = strLitSupported env := by
  unfold strLitSupported
  rw [natLitSupported_consBlockRecsR hnres,
    find?_consBlockRecsR_of_ne (ne_of_reservedRecName (n := stringName) hnres (by decide)),
    find?_consBlockRecsR_of_ne (ne_of_reservedRecName (n := stringOfListName) hnres (by decide)),
    find?_consBlockRecsR_of_ne (ne_of_reservedRecName (n := listName) hnres (by decide)),
    find?_consBlockRecsR_of_ne (ne_of_reservedRecName (n := listNilName) hnres (by decide)),
    find?_consBlockRecsR_of_ne (ne_of_reservedRecName (n := listConsName) hnres (by decide)),
    find?_consBlockRecsR_of_ne (ne_of_reservedRecName (n := charName) hnres (by decide)),
    find?_consBlockRecsR_of_ne (ne_of_reservedRecName (n := charOfNatName) hnres (by decide))]

/-- `strLitSupported_consBlockRecsR` at `sumRulesR`. -/
theorem strLitSupported_consBlockRecs {find? : Name → Option ConstantInfo}
    {q : BlockShape} {nP : Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {env : Env}
    (hnres : ∀ r ∈ rs, reservedRecName r.1.name = false) :
    strLitSupported (consBlockRecs find? q nP 0 rs env) = strLitSupported env := by
  rw [consBlockRecs_eq_R]; exact strLitSupported_consBlockRecsR hnres

/-! ## The block's η invariant, established -/

/-- A `Nodup` concatenation of per-element lists has DISJOINT members
at distinct positions (the shape `BlockShape.allCtors` has: the
members' constructor lists, concatenated). -/
private theorem flatten_disjoint_of_nodup {α : Type _} {β : Type _} [DecidableEq β]
    {f : α → List β} :
    ∀ {L : List α}, ((L.map f).flatten).Nodup →
      ∀ {i j : Nat} {a b : α}, i ≠ j → L[i]? = some a → L[j]? = some b →
      ∀ x ∈ f a, ∀ y ∈ f b, x ≠ y
  | [], _, i, _, _, _, _, hi, _ => by simp at hi
  | a₀ :: L, hnd, i, j, a, b, hij, hi, hj => by
    simp only [List.map_cons, List.flatten_cons] at hnd
    obtain ⟨-, hnd', hcross⟩ := List.nodup_append.mp hnd
    have hin : ∀ {q : Nat} {c : α}, L[q]? = some c → ∀ y ∈ f c, y ∈ (L.map f).flatten := by
      intro q c hq y hy
      exact List.mem_flatten.mpr ⟨f c, List.mem_map.mpr ⟨c, List.mem_of_getElem? hq, rfl⟩, hy⟩
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 0, j + 1 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [List.getElem?_cons_succ] at hj
      exact fun x hx y hy => hcross x hx y (hin hj y hy)
    | i + 1, 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [List.getElem?_cons_succ] at hi
      exact fun x hx y hy => fun hh => hcross y hy x (hin hi x hx) hh.symm
    | i + 1, j + 1 =>
      simp only [List.getElem?_cons_succ] at hi hj
      exact flatten_disjoint_of_nodup hnd' (fun hh => hij (by omega)) hi hj

/-- **The constructor names of the block member called `n`** — `[]` off
the block, and at a member its own list (the block's member names are
distinct).  This is `BlockEtaInv`'s `ctorsOf` at a block. -/
def BlockShape.ctorNamesAt (p : BlockShape) (n : Name) : List Name :=
  (p.members.filter (fun ms => ms.cvT.name == n)).flatMap (fun ms => ms.ctors.map (·.1.name))

theorem BlockShape.mem_ctorNamesAt {p : BlockShape} {ms : MemberShape} {c : ConstantVal × Nat}
    (hms : ms ∈ p.members) (hc : c ∈ ms.ctors) : c.1.name ∈ p.ctorNamesAt ms.cvT.name := by
  rw [BlockShape.ctorNamesAt, List.mem_flatMap]
  exact ⟨ms, List.mem_filter.mpr ⟨hms, by simp⟩, List.mem_map.mpr ⟨c, hc, rfl⟩⟩

theorem BlockShape.ctorNamesAt_mem {p : BlockShape} {n n' : Name}
    (h : n' ∈ p.ctorNamesAt n) :
    ∃ ms ∈ p.members, ms.cvT.name = n ∧ ∃ c ∈ ms.ctors, c.1.name = n' := by
  rw [BlockShape.ctorNamesAt, List.mem_flatMap] at h
  obtain ⟨ms, hms, hc⟩ := h
  obtain ⟨hms', hname⟩ := List.mem_filter.mp hms
  obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hc
  exact ⟨ms, hms', by simpa using hname, c, hc', rfl⟩

/-- **A member's η constructor is one of ITS OWN constructors**: the
capability record claims η only where the member has exactly one
constructor, and names that one. -/
theorem blockCapsAt_etaCtor_mem {p₁ : BlockShape} {isRec : Bool} {j : Nat} {ms : MemberShape}
    (hms : p₁.members[j]? = some ms) (he : (blockCapsAt p₁ j isRec).eta = true) :
    (blockCapsAt p₁ j isRec).etaCtor ∈ p₁.ctorNamesAt ms.cvT.name := by
  have hgetD : p₁.members.getD j default = ms := by
    rw [List.getD_eq_getElem?_getD, hms, Option.getD_some]
  match hcs : ms.ctors with
  | [c] =>
    have : (blockCapsAt p₁ j isRec).etaCtor = c.1.name := by
      rw [blockCapsAt, hgetD, hcs]
    rw [this]
    exact BlockShape.mem_ctorNamesAt (List.mem_of_getElem? hms) (by rw [hcs]; exact List.mem_cons_self)
  | [] => rw [blockCapsAt, hgetD, hcs] at he; exact nomatch he
  | c :: c' :: cs => rw [blockCapsAt, hgetD, hcs] at he; exact nomatch he

/-- **A `.indInfo` found after the `k` formers' conses** is one of them,
with ITS capability record, or was stored before the block. -/
theorem find?_consBlockInds_indInfo {p₁ : BlockShape} {isRec : Bool} :
    ∀ {cvTas : List ConstantVal} {i : Nat} {env : Env} {T' : Name}
      {cvT : ConstantVal} {caps : IndCaps},
      (consBlockInds p₁ isRec cvTas i env).find? T' = some (.indInfo cvT caps) →
      (∃ j, cvTas[j]? = some cvT ∧ cvT.name = T' ∧ caps = blockCapsAt p₁ (i + j) isRec) ∨
      env.find? T' = some (.indInfo cvT caps)
  | [], _, _, _, _, _, h => Or.inr h
  | cvTa :: rest, i, env, T', cvT, caps, h => by
    simp only [consBlockInds] at h
    rcases find?_consBlockInds_indInfo h with ⟨j, hj, hname, hcaps⟩ | h'
    · exact Or.inl ⟨j + 1, hj, hname, by rw [hcaps, show i + 1 + j = i + (j + 1) from by omega]⟩
    · rw [ConLeche.Env.find?_cons] at h'
      split at h'
      · next heq =>
        obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj h')
        exact Or.inl ⟨0, rfl, heq, by rw [Nat.add_zero]⟩
      · exact Or.inr h'

/-- **`BlockEtaInv`'s second conjunct at the `k` formers' cons**: every
stored member's η constructor is one of that member's own constructors.
The members' names are fresh before the block, so a stored `.indInfo`
at a member's name IS that member's cons. -/
theorem blockEtaInv_snd_consBlockInds {p₁ : BlockShape} {isRec : Bool}
    {cvTas : List ConstantVal} {env : Env} {names : List Name}
    (hfresh : ∀ T' ∈ names, env.find? T' = none)
    (hms : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      ∃ ms, p₁.members[j]? = some ms ∧ ms.cvT.name = cvTa.name) :
    ∀ (T' : Name) (cvT : ConstantVal) (caps : IndCaps),
      (consBlockInds p₁ isRec cvTas 0 env).find? T' = some (.indInfo cvT caps) →
      T' ∈ names → caps.eta = true → caps.etaCtor ∈ p₁.ctorNamesAt T' := by
  intro T' cvT caps hf hmem hcape
  rcases find?_consBlockInds_indInfo hf with ⟨j, hj, rfl, rfl⟩ | h'
  · obtain ⟨ms, hmsj, hname⟩ := hms j cvT hj
    rw [Nat.zero_add] at hcape ⊢
    rw [← hname]
    exact blockCapsAt_etaCtor_mem hmsj hcape
  · rw [hfresh T' hmem] at h'; exact nomatch h'

/-- **A member's constructor completes no OTHER member's η family.**
The block's constructor names are distinct (`DeclBlockRun`'s conjunct
0) and `allCtors` is the members' lists concatenated, so distinct
members' constructor names are disjoint; `BlockEtaInv.other`'s `hout`
is that disjointness at the member being consed. -/
theorem blockCtorNames_out {p₁ : BlockShape}
    (hnd : (p₁.allCtors.map (·.1.name)).Nodup)
    {m : Nat} {msm : MemberShape} (hm : p₁.members[m]? = some msm)
    {n : Name} (hn : n ∈ msm.ctors.map (·.1.name))
    (T'' : Name) (_hT : T'' ∈ p₁.memberNames) (hne : T'' ≠ msm.cvT.name) :
    n ∉ p₁.ctorNamesAt T'' := by
  intro hmem
  obtain ⟨ms, hms, hmsn, c, hc, hcn⟩ := BlockShape.ctorNamesAt_mem hmem
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hms
  have hjm : j ≠ m := by
    intro hh
    subst hh
    obtain rfl : ms = msm := Option.some.inj (hj.symm.trans hm)
    exact hne hmsn.symm
  have hflat : ((p₁.members.map (fun ms => ms.ctors.map (·.1.name))).flatten).Nodup := by
    have : p₁.allCtors.map (·.1.name)
        = (p₁.members.map (fun ms => ms.ctors.map (·.1.name))).flatten := by
      rw [BlockShape.allCtors, List.map_flatten, List.map_map]
      rfl
    rwa [this] at hnd
  exact flatten_disjoint_of_nodup hflat hjm hj hm c.1.name
    (List.mem_map.mpr ⟨c, hc, rfl⟩) n hn hcn

/-! ## The family's shared rule PREFIX (the ruling of 2026-09-22)

Stage (b') compares every recursor's opened rule prefix with the FIRST
one's, binder by binder, up to defeq.  What the model needs of it is
the per-position `isDefEq`, at the two openings — the fact that lets
it identify the classes' prefix domains and so put a guarded call's
predecessor in the CALLEE's class (the lane's `hpref'`). -/

/-- **`checkBlockDefEqList`, inverted**: the lists have the same length
and every position is defeq at the stage's depth. -/
theorem checkBlockDefEqList_inv {env : Env} {F depth : Nat} {what : String} :
    ∀ {as bs : List Expr},
      checkBlockDefEqList (fueledOps mode F) env depth what as bs = .ok () →
      as.length = bs.length ∧
      ∀ l, l < as.length →
        isDefEqCore mode env F depth (as.getD l default) (bs.getD l default) = .ok true
  | [], [], _ => ⟨rfl, fun l hl => absurd hl (Nat.not_lt_zero l)⟩
  | [], _ :: _, h => by
    simp only [checkBlockDefEqList, throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  | _ :: _, [], h => by
    simp only [checkBlockDefEqList, throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  | a :: as, b :: bs, h => by
    rw [checkBlockDefEqList] at h
    simp only [fueledOps_isDefEq] at h
    obtain ⟨c, hc, h⟩ := exceptBind_ok h
    by_cases hcb : c = true
    case neg =>
      rw [Bool.not_eq_true] at hcb
      subst hcb
      simp only [Bool.false_eq_true, if_false, throw, throwThe, MonadExceptOf.throw,
        Bind.bind, Except.bind] at h
      exact nomatch h
    subst hcb
    simp only [if_pos, Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨hlen, hall⟩ := checkBlockDefEqList_inv h
    refine ⟨by simp [hlen], fun l hl => ?_⟩
    cases l with
    | zero => simpa using hc
    | succ l => simpa using hall l (by simpa using hl)

end ConLeche
