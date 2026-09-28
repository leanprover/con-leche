module

public import ConLeche.Verify.Inductives.BlockRecRun
public import ConLeche.Verify.ProjSlots
import ConLeche.Verify.CheckerF
import ConLeche.Verify.Extend.Inversions
public import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.NestedRuleSyn
import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The recursor stage's KIND-FREE facts

The recursor stage is the classification-free target
check (`checkBlockRecT`, `targetRecCheck` at the constructors' index).
Every proof about the stage reads ONE record of what that check
guarantees about the family it stores — `RecStage` — and never unfolds
the check:

* the records' pins (the level parameters, the reserved names, the
  name set);
* per recursor, stage (b)'s entry (`RecTyEntry`, the type checked
  against its MAJOR member: the former's parameters, the major at the
  index binders, the conclusion's sort), and the family's agreements
  (`RecFamFacts`: the counting guard, the elimination-level pin, the
  index domains, the shared rule prefix);
* the stored family's shape (lengths, the bridge from the checked
  constants to the stored ones, each recursor's constructors);
* per rule, the rule's λ-TOWER (`RuleTower`: annotated, resolved,
  typed at the rule-less recursors' environment, its binders the
  recursor's prefix and the constructor's fields, binder by binder).

Nothing here names a field kind or an `ih` frame: those belong to the
check's own records (`TargetRuleRun`), which the model reads for the
rule contract.  The record is produced from the target check's run
(`recStage_of_targetG`, `RecStageRun.lean`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-- The rule-less recursors' index at the pure index is the pure one. -/
theorem consBlockRecsBareF_mkFEnv (p : BlockShape) :
    ∀ (m : Nat) (cvRas : List (ConstantVal × Nat)) (env : Env),
      consBlockRecsBareF p m cvRas (mkFEnv env) = mkFEnv (consBlockRecsBare p m cvRas env)
  | _, [], _ => rfl
  | m, (cvRa, nIdx) :: rest, env => by
    simp only [consBlockRecsBareF, consBlockRecsBare, push_mkFEnv]
    exact consBlockRecsBareF_mkFEnv p (m + 1) rest _

/-! ## The records -/

/-- **One rule's λ-tower, as checked**: the stream's right-hand side
`rhs` annotated into `out` (the STORED rule) at the rule-less recursors'
environment `envR`, typed there, its λ-tower compared binder by binder
with the recursor type's prefix and the constructor's fields at the
constructors' environment `envT`. -/
structure RuleTower (mode : CheckMode) (F : Nat) (envR envT : Env) (p : BlockShape)
    (recTys : List Expr) (ri : Nat) (cvR : ConstantVal) (cA : ConstantVal × Nat)
    (rhs out : Expr) : Type where
  recTy : Expr
  tyR : Expr
  rbs : List (Expr × BinderMeta)
  body : Expr
  fvsPref : List Expr
  oPref : Expr
  cpref : List Expr
  crest : Expr
  fvsF : List Expr
  cbody : Expr
  ldoms : List Expr
  lrest : Expr
  concl : Expr
  hrecTy : recTys[ri]? = some recTy
  hbv : rhs.looseBVarsBounded 0 = true
  hfv : rhs.hasFvar = false
  hann : annotateCore mode envR F 0 rhs = .ok out
  hlp : out.allLevelParamsDefined cvR.levelParams = true
  hres : out.constsResolve envR = true
  htyR : inferTypeCore mode envR F 0 out = .ok tyR
  hstrip : Expr.stripLams (p.rulePrefixAt ri + cA.2) out = some (rbs, body)
  hpw : ∀ b ∈ rbs, b.2.pw = Level.zeronessOf (structElimLevel p.elim p.large)
  hpref : openPisAtFvars (p.rulePrefixAt ri) recTy 0 = some (fvsPref, oPref)
  hcpar : Expr.instPisAt (fvsPref.take p.nP) cA.1.type = some (cpref, crest)
  hfld : openPisAtFvars cA.2 crest (p.rulePrefixAt ri) = some (fvsF, cbody)
  hlams : Expr.instLamsAt (fvsPref ++ fvsF) out = some (ldoms, lrest)
  /-- the λ-domains resolve at the constructors' environment -/
  hldomsRes : ∀ t ∈ ldoms, t.constsResolve envT = true
  hG2len : ((fvsPref ++ fvsF).map Expr.fvarTypeD).length = ldoms.length
  hG2 : ∀ l, l < ((fvsPref ++ fvsF).map Expr.fvarTypeD).length →
    isDefEqCore mode envT F (p.rulePrefixAt ri + cA.2)
      (((fvsPref ++ fvsF).map Expr.fvarTypeD).getD l default) (ldoms.getD l default) = .ok true
  /-- the recursor's conclusion at the prefix, the constructor's result
  indices and the constructed element -/
  hconcl : Expr.instPisAtLift
      (fvsPref ++ cbody.getAppArgs.drop p.nP ++
        [Expr.mkAppN (.const cA.1.name (p.lps.map .param)) (fvsPref.take p.nP ++ fvsF)])
      recTy = some concl

/-- **One rule's stored right-hand side, at ANY major**:
the stream's `rhs` annotated into `out` at the rule-less recursors'
environment, closed, its level parameters the recursor's, its constants
resolved there. -/
structure RuleOutOk (mode : CheckMode) (F : Nat) (envR : Env) (cvR : ConstantVal)
    (rhs out : Expr) : Prop where
  hbv : rhs.looseBVarsBounded 0 = true
  hfv : rhs.hasFvar = false
  hann : annotateCore mode envR F 0 rhs = .ok out
  hlp : out.allLevelParamsDefined cvR.levelParams = true
  hres : out.constsResolve envR = true
  htyR : ∃ tyR, inferTypeCore mode envR F 0 out = .ok tyR

namespace RuleOutOk

variable {F : Nat} {envR : Env} {cvR : ConstantVal} {rhs out : Expr}

theorem out_noFvar (R : RuleOutOk mode F envR cvR rhs out) : out.hasFvar = false :=
  Expr.not_hasFvar_of_fvarsBelow_zero
    ((annotateCore_WScoped F rhs R.hann (Expr.WScoped.of_not_hasFvar R.hfv)).fvarsBelow)

theorem out_bounded (R : RuleOutOk mode F envR cvR rhs out) :
    out.looseBVarsBounded 0 = true :=
  annotateCore_looseBVars F rhs R.hann R.hbv

end RuleOutOk

/-- **The recursor records' pins**: the level parameters, no reserved
name, the name set `{T_m.rec}`. -/
structure RecPinsOk (p : BlockShape) : Prop where
  lps : blockRecLpsOk p = true
  unreserved : blockRecNamesUnreserved p = true
  nameSet : blockRecNameSetOk p = true

/-- **A checked block carries one recursor per member, named
`T_m.rec`** (official's naming, for conformance): as many recursors as
members, each named for a member and each member named by one. -/
theorem recPins_names {p : BlockShape} (h : RecPinsOk p) :
    p.recs.length = p.members.length ∧
    (∀ rc ∈ p.recs, ∃ ms ∈ p.members, rc.cvR.name = ms.cvT.name.str "rec") ∧
    (∀ ms ∈ p.members, ∃ rc ∈ p.recs, rc.cvR.name = ms.cvT.name.str "rec") := by
  have hset := h.nameSet
  unfold blockRecNameSetOk at hset
  simp only [Bool.and_eq_true, beq_iff_eq, List.length_map] at hset
  obtain ⟨⟨hlen, hwant⟩, hgot⟩ := hset
  refine ⟨hlen, ?_, ?_⟩
  · intro rc hrc
    have hmem := List.elem_iff.mp
      (List.all_eq_true.mp hgot rc.cvR.name (List.mem_map_of_mem hrc))
    obtain ⟨ms, hms, hn⟩ := List.mem_map.mp hmem
    exact ⟨ms, hms, hn.symm⟩
  · intro ms hms
    have hmem := List.elem_iff.mp
      (List.all_eq_true.mp hwant (ms.cvT.name.str "rec") (List.mem_map_of_mem hms))
    obtain ⟨rc, hrc, hn⟩ := List.mem_map.mp hmem
    exact ⟨rc, hrc, hn⟩

/-- The auxiliary records' names (a record whose major is not a member). -/
@[expose] def recAuxGot (p : BlockShape) : List Name :=
  (p.recs.filter fun rc => !(rc.tgt < p.k)).map (·.cvR.name)

/-- The names `targetRecPins` generates for the auxiliary records:
`T_0.rec_1 … T_0.rec_n`, `T_0` the block's first member. -/
@[expose] def recAuxWant (p : BlockShape) : List Name :=
  (List.range (p.recs.filter fun rc => !(rc.tgt < p.k)).length).map fun i =>
    ((p.memberNames.head?).getD .anonymous).str s!"rec_{i + 1}"

/-- **The recursor records' pins at a block with auxiliary recursors**:
the name set is pinned at the MEMBER-targeting records
(`rc.tgt < k`) only — what `targetRecPins` checks at every block. -/
structure RecPinsF (p : BlockShape) : Prop where
  lps : blockRecLpsOk p = true
  unreserved : blockRecNamesUnreserved p = true
  nameSet : blockRecNameSetOk { p with recs := p.recs.filter fun rc => rc.tgt < p.k } = true
  /-- the auxiliary records' names are the generated `T_0.rec_1 … T_0.rec_n`,
  as a set (`targetRecPins`' fourth check) -/
  auxNames : ((recAuxGot p).length == (recAuxWant p).length &&
    (recAuxWant p).all ((recAuxGot p).contains ·) &&
    (recAuxGot p).all ((recAuxWant p).contains ·)) = true

/-- At a family whose every record targets a member the two pins agree. -/
theorem RecPinsF.toOk {p : BlockShape} (h : RecPinsF p) (hall : ∀ rc ∈ p.recs, rc.tgt < p.k) :
    RecPinsOk p := by
  refine ⟨h.lps, h.unreserved, ?_⟩
  have hown : p.recs.filter (fun rc => rc.tgt < p.k) = p.recs :=
    List.filter_eq_self.mpr fun rc hrc => decide_eq_true (hall rc hrc)
  have := h.nameSet
  rw [hown] at this
  exact this

/-- **The family's agreements**, over stage (b)'s list: the counting
half of the elimination guard, the elimination-level PIN, the index
binder domains (each recursor's against its major member's index
telescope) and the shared rule prefix. -/
structure RecFamFacts (mode : CheckMode) (F : Nat) (env : Env) (p : BlockShape)
    (cvTas : List ConstantVal) (cvRus : List (ConstantVal × Nat × Level))
    (mem : Nat → Prop) : Prop where
  /-- the block declares a family -/
  k_pos : 0 < p.k
  /-- the counting half of the elimination guard -/
  small : blockLargeElimAllowed p false = true ∨
    ∀ u ∈ cvRus.map (·.2.2), Level.isEquiv u Level.zero = some true
  /-- the elimination-level PIN -/
  pin : ∀ u ∈ cvRus.map (·.2.2),
    Level.isEquiv u (structElimLevel p.elim p.large) = some true
  /-- the index binder domains -/
  idxDoms : ∀ i, i < cvRus.length → mem i → ∃ (cvR : ConstantVal) (nIdx : Nat) (u : Level)
      (cvTa : ConstantVal) (fvs tfvs : List Expr) (concl trest : Expr),
    cvRus[i]? = some (cvR, nIdx, u) ∧
    cvTas[p.recTgtAt i]? = some cvTa ∧
    openPisAtFvars (p.majorIdxAt i + 1) cvR.type 0 = some (fvs, concl) ∧
    openPisParamsIdx p.nP nIdx (p.rulePrefixAt i) cvTa.type = some (tfvs, trest) ∧
    ((tfvs.drop p.nP).map Expr.fvarTypeD).length
      = (((fvs.drop (p.rulePrefixAt i)).take nIdx).map Expr.fvarTypeD).length ∧
    ∀ q, q < ((tfvs.drop p.nP).map Expr.fvarTypeD).length →
      isDefEqCore mode env F (p.majorIdxAt i)
        (((tfvs.drop p.nP).map Expr.fvarTypeD).getD q default)
        ((((fvs.drop (p.rulePrefixAt i)).take nIdx).map Expr.fvarTypeD).getD q default)
        = .ok true
  /-- the shared rule prefix -/
  prefixAgree : checkBlockRecPrefixAgree (fueledOps mode F) env p (cvRus.map (·.1)) = .ok ()

/-- **The recursor stage, as checked** — its kind-free facts.  `env` is
the constructors' environment, `rs` the stored family (install format).
`mem` says at which recursors the MAJOR is a member of
the block: the member-shaped facts (`tyEntry`, `ctorsAt`, `ruleTower`,
the index domains) are recorded there only; everything else holds at
every recursor, an auxiliary one (an outside major) included.
`RecStageOk` is the case `mem := fun _ => True`. -/
structure RecStage (mode : CheckMode) (F : Nat) (env : Env) (p : BlockParts)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (mem : Nat → Prop) : Type where
  /-- stage (b)'s list: the checked constant, its major's index count,
  its conclusion's sort -/
  cvRus : List (ConstantVal × Nat × Level)
  /-- (a) the records' pins -/
  pins : RecPinsF p.toBlockShape
  /-- (b') the family's agreements -/
  fam : RecFamFacts mode F env p.toBlockShape cvTas cvRus mem
  lenT : cvRus.length = p.recs.length
  len : rs.length = p.recs.length
  /-- the stored records are stage (b)'s -/
  stored : rs.map (fun r => (r.1, r.2.2.1)) = cvRus.map (fun q => (q.1, q.2.1))
  /-- (b) every recursor's type, at any major -/
  tyGen : ∀ i, i < p.recs.length → ∃ rc cvRi nIdx u, p.recs[i]? = some rc ∧
    cvRus[i]? = some (cvRi, nIdx, u) ∧
    Nonempty (RecTyGen mode F env p.toBlockShape false i rc cvRi nIdx u)
  /-- (b) every MEMBER-major recursor's type -/
  tyEntry : ∀ i, i < p.recs.length → mem i → ∃ rc cvRi nIdx u, p.recs[i]? = some rc ∧
    cvRus[i]? = some (cvRi, nIdx, u) ∧
    Nonempty (RecTyEntry mode F env p.toBlockShape false cvTas i rc cvRi nIdx u)
  /-- each stored recursor carries its member's constructors -/
  ctorsAt : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    mem i → rs[i]? = some r → ∃ ms, p.members[p.toBlockShape.recTgtAt i]? = some ms ∧
    ctorsAs[p.toBlockShape.recTgtAt i]? = some r.2.2.2 ∧ r.2.2.2.length = ms.ctors.length
  /-- one stored rule per constructor -/
  rulesLenAt : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    rs[i]? = some r → r.2.1.length = r.2.2.2.length
  /-- (c) every stored rule, annotated at the rule-less recursors -/
  ruleOut : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) (i : Nat)
    (rhs : Expr), rs[c]? = some r → r.2.1[i]? = some rhs →
    ∃ rc rhs0, p.recs[c]? = some rc ∧ rc.rhss[i]? = some rhs0 ∧
      RuleOutOk mode F (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env)
        rc.cvR rhs0 rhs
  /-- (c) every stored MEMBER-major rule's λ-tower -/
  ruleTower : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) (i : Nat)
    (cA : ConstantVal × Nat) (rhs : Expr), mem c →
    rs[c]? = some r → r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
    ∃ rc rhs0, p.recs[c]? = some rc ∧ rc.rhss[i]? = some rhs0 ∧
      Nonempty (RuleTower mode F
        (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env) env
        p.toBlockShape (rs.map (·.1.type)) c rc.cvR cA rhs0 rhs)

/-- The stage's facts at the member-major recursors `mem`, as a
proposition. -/
@[expose] def RecStageG (mode : CheckMode) (F : Nat) (env : Env) (p : BlockParts)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (mem : Nat → Prop) : Prop :=
  Nonempty (RecStage mode F env p cvTas ctorsAs rs mem)

/-- The stage's facts, as a proposition (what the model's statements
take in place of the kernel run): every major a member. -/
@[expose] def RecStageOk (mode : CheckMode) (F : Nat) (env : Env) (p : BlockParts)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) : Prop :=
  RecStageG mode F env p cvTas ctorsAs rs fun _ => True

namespace RecStage

variable {F : Nat} {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {mem : Nat → Prop}

/-- **The bridge at an index**: stage (b)'s entry at a stored
recursor is its checked constant, with the same index count. -/
theorem stored_at (R : RecStage mode F env p cvTas ctorsAs rs mem) {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[i]? = some r) :
    ∃ u, R.cvRus[i]? = some (r.1, r.2.2.1, u) := by
  have hil : i < R.cvRus.length := by
    rw [R.lenT, ← R.len]; exact (List.getElem?_eq_some_iff.mp hr).1
  refine ⟨R.cvRus[i].2.2, ?_⟩
  have h := congrArg (·[i]?) R.stored
  simp only [List.getElem?_map, hr, List.getElem?_eq_getElem hil, Option.map_some,
    Option.some.injEq, Prod.mk.injEq] at h
  rw [List.getElem?_eq_getElem hil, h.1, h.2]

/-- The bridge at an index, at the constant alone. -/
theorem stored_fst (R : RecStage mode F env p cvTas ctorsAs rs mem) {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[i]? = some r) :
    (R.cvRus.map (·.1))[i]? = some r.1 := by
  obtain ⟨u, hcu⟩ := R.stored_at hr
  rw [List.getElem?_map, hcu]; rfl


/-- The `(c, i)`-th rule's λ-tower at a MEMBER-major recursor. -/
theorem ruleAtG (R : RecStage mode F env p cvTas ctorsAs rs mem) {c : Nat} (hm : mem c)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) :
    ∃ rc rhs0, p.recs[c]? = some rc ∧ rc.rhss[i]? = some rhs0 ∧
      Nonempty (RuleTower mode F
        (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env) env
        p.toBlockShape (rs.map (·.1.type)) c rc.cvR cA rhs0 rhs) :=
  R.ruleTower c r i cA rhs hm hr hcA hrhs

/-- **Every constructor has its rule.** -/
theorem rulesLen (R : RecStage mode F env p cvTas ctorsAs rs mem)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) : r.2.1.length = r.2.2.2.length :=
  R.rulesLenAt c r hr

/-- **Stage (b)'s major-free entry at a STORED recursor** (any major). -/
theorem tyGenAt (R : RecStage mode F env p cvTas ctorsAs rs mem) {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[i]? = some r) :
    ∃ rc u, p.recs[i]? = some rc ∧ R.cvRus[i]? = some (r.1, r.2.2.1, u) ∧
      Nonempty (RecTyGen mode F env p.toBlockShape false i rc r.1 r.2.2.1 u) := by
  obtain ⟨u, hcu⟩ := R.stored_at hr
  have hil : i < p.recs.length := by rw [← R.len]; exact (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨rc, cvRi, nIdx, u', hrc, hcu', ⟨E⟩⟩ := R.tyGen i hil
  rw [hcu] at hcu'
  obtain ⟨rfl, rfl, rfl⟩ : r.1 = cvRi ∧ r.2.2.1 = nIdx ∧ u = u' := by
    simpa using hcu'
  exact ⟨rc, u, hrc, hcu, ⟨E⟩⟩

/-- Stage (b)'s entry at a stored MEMBER-major recursor. -/
theorem tyAtG (R : RecStage mode F env p cvTas ctorsAs rs mem) {i : Nat} (hm : mem i)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[i]? = some r) :
    ∃ rc u, p.recs[i]? = some rc ∧ R.cvRus[i]? = some (r.1, r.2.2.1, u) ∧
      Nonempty (RecTyEntry mode F env p.toBlockShape false cvTas i rc r.1 r.2.2.1 u) := by
  obtain ⟨u, hcu⟩ := R.stored_at hr
  have hil : i < p.recs.length := by rw [← R.len]; exact (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨rc, cvRi, nIdx, u', hrc, hcu', ⟨E⟩⟩ := R.tyEntry i hil hm
  rw [hcu] at hcu'
  obtain ⟨rfl, rfl, rfl⟩ : r.1 = cvRi ∧ r.2.2.1 = nIdx ∧ u = u' := by
    simpa using hcu'
  exact ⟨rc, u, hrc, hcu, ⟨E⟩⟩

/-- **A stored rule is annotated at the rule-less recursors** (any major). -/
theorem ruleOutOf (R : RecStage mode F env p cvTas ctorsAs rs mem)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {rhs : Expr} (hrhs : rhs ∈ r.2.1) :
    ∃ (i : Nat) (rc : RecShape) (rhs0 : Expr),
      r.2.1[i]? = some rhs ∧ p.recs[c]? = some rc ∧
      RuleOutOk mode F (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env)
        rc.cvR rhs0 rhs := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hrhs
  obtain ⟨rc, rhs0, hrc, -, hQ⟩ := R.ruleOut c r i rhs hr hi
  exact ⟨i, rc, rhs0, hi, hrc, hQ⟩

/-- **The pins at `mem := fun _ => True`**: every major a member, every record
targets one, so the name set is pinned at the whole family. -/
theorem pinsOk (R : RecStage mode F env p cvTas ctorsAs rs fun _ => True) :
    RecPinsOk p.toBlockShape := by
  refine R.pins.toOk fun rc hrc => ?_
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hrc
  have hil : i < p.recs.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨rc', cvRi, nIdx, u, hrc', -, ⟨E⟩⟩ := R.tyEntry i hil trivial
  obtain rfl := Option.some.inj (hi.symm.trans hrc')
  have hT : p.toBlockShape.recTgtAt i = rc.tgt := by
    simp only [BlockShape.recTgtAt, List.getD_eq_getElem?_getD]
    have hi2 : p.toBlockShape.recs[i]? = some rc := hi
    rw [hi2]; rfl
  have := (List.getElem?_eq_some_iff.mp E.hms).1
  rw [hT] at this
  exact this

end RecStage

/-! ## The base inversions, read off the record -/

section Base

variable {F : Nat} {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}


/-- **Stage (b)'s major-free record at a STORED recursor** (any major). -/
theorem recStageG_tyGen {mem : Nat → Prop} (h : RecStageG mode F env p cvTas ctorsAs rs mem)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) :
    ∃ rc u, p.recs[i]? = some rc ∧
      Nonempty (RecTyGen mode F env p.toBlockShape false i rc r.1 r.2.2.1 u) := by
  obtain ⟨R⟩ := h
  obtain ⟨rc, u, hrc, -, E⟩ := R.tyGenAt hr
  exact ⟨rc, u, hrc, E⟩

/-- **Stage (b)'s record at a STORED MEMBER-major recursor.** -/
theorem recStageG_tyAt {mem : Nat → Prop} (h : RecStageG mode F env p cvTas ctorsAs rs mem)
    {i : Nat} (hm : mem i) {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) :
    ∃ rc u, p.recs[i]? = some rc ∧
      Nonempty (RecTyEntry mode F env p.toBlockShape false cvTas i rc r.1 r.2.2.1 u) := by
  obtain ⟨R⟩ := h
  obtain ⟨rc, u, hrc, -, E⟩ := R.tyAtG hm hr
  exact ⟨rc, u, hrc, E⟩

/-- **The CHECK's own well-formedness contract**: every stored
recursor type is a CHECKED constant's, and every stored rule is the
ANNOTATED stream right-hand side, scoped at the BARE-`k` environment. -/
theorem recStage_facts {mem : Nat → Prop} (h : RecStageG mode F env p cvTas ctorsAs rs mem) :
    ∀ r ∈ rs, r.1.type.hasFvar = false ∧
      r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
      r.1.type.constsResolve env = true ∧
      r.1.type.looseBVarsBounded 0 = true ∧
      ∀ rhs ∈ r.2.1, rhs.hasFvar = false ∧
        rhs.allLevelParamsDefined r.1.levelParams = true ∧
        rhs.constsResolve
          (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env) = true ∧
        rhs.looseBVarsBounded 0 = true := by
  obtain ⟨R⟩ := h
  intro r hr
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hr
  obtain ⟨rc, u, hrc, -, ⟨E⟩⟩ := R.tyGenAt hc
  obtain ⟨g1, g2, g3, g4⟩ := checkConstantVal_typeWF E.hcv
  refine ⟨g1, g2, g3, g4, fun rhs hrhs => ?_⟩
  obtain ⟨i, rc', rhs0, -, hrc', Q⟩ := R.ruleOutOf hc hrhs
  obtain rfl := Option.some.inj (hrc.symm.trans hrc')
  exact ⟨Q.out_noFvar, by rw [E.lps_eq]; exact Q.hlp, Q.hres, Q.out_bounded⟩

/-- **The CHECK's stored recursors take no guarded name.** -/
theorem recStage_reserved {mem : Nat → Prop} (h : RecStageG mode F env p cvTas ctorsAs rs mem) :
    ∀ r ∈ rs, reservedRecName r.1.name = false := by
  obtain ⟨R⟩ := h
  intro r hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  obtain ⟨rc, u, hrc, -, ⟨E⟩⟩ := R.tyGenAt hi
  rw [E.name_eq]
  have := List.all_eq_true.mp R.pins.unreserved rc (List.mem_of_getElem? hrc)
  exact eq_of_beq (by simpa using this)


/-- The stage's recursor names: the pins at the member-targeting
records. -/
theorem recStageG_recNames {mem : Nat → Prop} (h : RecStageG mode F env p cvTas ctorsAs rs mem) :
    RecPinsF p.toBlockShape ∧ rs.length = p.recs.length ∧
    ∀ i, i < p.recs.length → ∃ rc r, p.recs[i]? = some rc ∧ rs[i]? = some r ∧
      r.1.name = rc.cvR.name ∧
      checkConstantVal (fueledOps mode F) env rc.cvR = .ok r.1 ∧
      p.nP ≤ p.toBlockShape.rulePrefixAt i ∧
      ∃ nIdx, p.toBlockShape.majorIdxAt i = p.toBlockShape.rulePrefixAt i + nIdx := by
  obtain ⟨R⟩ := h
  refine ⟨R.pins, R.len, fun i hil => ?_⟩
  have hi' : i < rs.length := by rw [R.len]; exact hil
  have hr : rs[i]? = some rs[i] := List.getElem?_eq_getElem hi'
  obtain ⟨rc, u, hrc, -, ⟨E⟩⟩ := R.tyGenAt hr
  exact ⟨rc, _, hrc, hr, E.name_eq, E.hcv, E.nP_le, _, E.mI_eq⟩

/-- **The stored recursors' name facts and `hnoTy`**, from the
per-recursor `checkConstantVal` run: freshness at the constructors'
environment, the two name guards, and — because the stored type is the
ANNOTATED one — every `.proj` node of it sits at a stored table slot. -/
theorem recStage_cvFacts {mem : Nat → Prop} (h : RecStageG mode F env p cvTas ctorsAs rs mem) :
    ∀ r ∈ rs,
      env.find? r.1.name = none ∧
      reservedBasisNames.contains r.1.name = false ∧
      r.1.name.isProjFnShape = false ∧
      ∀ (T : Name) (i : Nat), env.findProj? T i = none → Expr.NoProjAt T i r.1.type := by
  obtain ⟨-, hlenR, hall⟩ := recStageG_recNames h
  intro r hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  have hil : i < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨rc, r', hrc, hr', hname, hcv, -, -⟩ := hall i hil
  obtain rfl := Option.some.inj (hi.symm.trans hr')
  obtain ⟨hfresh, hres, hpsh, -, -, hfv, type, -, -, hann, -, -, -, -, hcv'⟩ :=
    checkConstantVal_inv hcv
  have htype : r.1.type = type := by rw [hcv']
  refine ⟨by rw [hname]; exact hfresh, by rw [hname]; exact hres,
    by rw [hname]; exact hpsh, fun T i hslot => ?_⟩
  rw [htype]
  exact annotateCore_noProjAt mode hann hfv hslot

end Base

/-! ## The stored constructors' lengths -/

section Ctors

variable {p : BlockParts} {ctorsAs : List (List (ConstantVal × Nat))}

/-- Each member's stored constructors, one for one with its declared
ones: the constructors' stage's name-and-arity record gives the lengths. -/
theorem ctorsLen_of_names
    (hnames : ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
      = p.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2)))) :
    ∀ (t : Nat) (ms : MemberShape) (ctorsA : List (ConstantVal × Nat)),
      p.members[t]? = some ms → ctorsAs[t]? = some ctorsA → ctorsA.length = ms.ctors.length := by
  intro t ms ctorsA hms hct
  have h := congrArg (·[t]?) hnames
  simp only [List.getElem?_map, hms, hct, Option.map_some, Option.some.injEq] at h
  have := congrArg List.length h
  simpa using this

end Ctors

/-- **The pigeonhole**: a list as long as a `Nodup` list it covers is
itself `Nodup`. -/
theorem nodup_of_covering {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {L M : List α}, M.Nodup → M ⊆ L → L.length ≤ M.length → L.Nodup
  | [], _, _, _, _ => List.nodup_nil
  | a :: L', M, hM, hML, hlen => by
    have hdup : a ∉ L' := by
      intro ha
      have hsub : M ⊆ L' := by
        intro x hx
        rcases List.mem_cons.mp (hML hx) with rfl | h
        · exact ha
        · exact h
      have := List.Nodup.length_le_of_subset hM hsub
      simp only [List.length_cons] at hlen
      omega
    refine List.nodup_cons.mpr ⟨hdup, ?_⟩
    by_cases hmem : a ∈ M
    · refine nodup_of_covering (M := M.erase a) (List.Nodup.erase a hM) ?_ ?_
      · intro x hx
        rcases List.mem_cons.mp (hML (List.mem_of_mem_erase hx)) with rfl | h
        · exact absurd hx (List.Nodup.not_mem_erase hM)
        · exact h
      · rw [List.length_erase_of_mem hmem]
        simp only [List.length_cons] at hlen
        omega
    · exfalso
      have hsub : M ⊆ L' := by
        intro x hx
        rcases List.mem_cons.mp (hML hx) with rfl | h
        · exact absurd hx hmem
        · exact h
      have := List.Nodup.length_le_of_subset hM hsub
      simp only [List.length_cons] at hlen
      omega

/-- **The recursor NAME-SET check makes the recursors' names
distinct**, given the members' own (the pigeonhole). -/
theorem blockRecNameSetOk_nodup {p : BlockShape} (h : blockRecNameSetOk p = true)
    (hnd : (p.members.map (·.cvT.name)).Nodup) : (p.recs.map (·.cvR.name)).Nodup := by
  unfold blockRecNameSetOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.length_map] at h
  obtain ⟨⟨hlen, hwant⟩, -⟩ := h
  have hM : (p.members.map fun ms => ms.cvT.name.str "rec").Nodup := by
    have : (p.members.map fun ms => ms.cvT.name.str "rec")
        = (p.members.map (·.cvT.name)).map (fun n => n.str "rec") := by
      rw [List.map_map]; rfl
    rw [this]
    refine List.Pairwise.map _ (fun x y hxy hh => ?_) hnd
    exact hxy (by injection hh)
  refine nodup_of_covering hM ?_ (by simp [hlen])
  intro x hx
  exact List.elem_iff.mp (List.all_eq_true.mp hwant x hx)

end ConLeche
