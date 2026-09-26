module

public import ConLeche.Verify.Inductives.RecCheckRun
public import ConLeche.Verify.Inductives.BlockRecRun
public import ConLeche.Verify.ProjSlots
import ConLeche.Verify.CheckerF
import ConLeche.Verify.Extend.Inversions
public import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.NestedRuleSyn
import ConLeche.Verify.Inductives.SumRec
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The recursor stage's KIND-FREE facts (lane RECLIB, B1)

The uniform route's recursor stage is the classification-free target
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
(`recStage_of_targetG`).
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

/-- **One rule's stored right-hand side, at ANY major** (lane NESTIND):
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

/-- **The recursor records' pins at a block with auxiliary recursors**
(lane NESTIND): the name set is pinned at the MEMBER-targeting records
(`rc.tgt < k`) only — what `targetRecPins` checks at every block. -/
structure RecPinsF (p : BlockShape) : Prop where
  lps : blockRecLpsOk p = true
  unreserved : blockRecNamesUnreserved p = true
  nameSet : blockRecNameSetOk { p with recs := p.recs.filter fun rc => rc.tgt < p.k } = true
  /-- the auxiliary records' names are the generated `T_0.rec_1 … T_0.rec_n`,
  as a set (lane RECREST: `targetRecPins`' fourth check, recorded) -/
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
`mem` (lane NESTIND) says at which recursors the MAJOR is a member of
the block: the member-shaped facts (`tyEntry`, `ctorsAt`, `ruleTower`,
the index domains) are recorded there only; everything else holds at
every recursor, an auxiliary one (an outside major) included.  The
uniform route's stage is `mem := fun _ => True` (`RecStageOk`). -/
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
proposition (lane NESTIND). -/
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

/-- **The uniform route's pins**: every major a member, every record
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

/-! ## The producer: the target check's run -/

section Producer

variable {F : Nat} {env : Env} {p : BlockParts} {block : List ConstantInfo}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

/-- `targetRecPins`, inverted. -/
theorem targetRecPins_inv {q : BlockShape}
    (h : targetRecPins (m := CheckM) q block = .ok ()) : RecPinsF q := by
  unfold targetRecPins at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  by_cases h1 : blockRecLpsOk q = true
  case neg => simp only [h1] at h; exact nomatch h
  by_cases h2 : blockRecNamesUnreserved q = true
  case neg => simp only [h1, h2] at h; exact nomatch h
  by_cases h3 : blockRecNameSetOk { q with recs := q.recs.filter fun rc => rc.tgt < q.k } = true
  case neg => simp only [h1, h2, h3] at h; exact nomatch h
  by_cases h4 : ((recAuxGot q).length == (recAuxWant q).length &&
      (recAuxWant q).all ((recAuxGot q).contains ·) &&
      (recAuxGot q).all ((recAuxWant q).contains ·)) = true
  case neg =>
    simp only [recAuxGot, recAuxWant] at h4
    simp only [h1, h2, h3, h4] at h; exact nomatch h
  exact ⟨h1, h2, h3, h4⟩

/-- **A member major's facts**, off a `TargetTyEntry` (the uniform
route): the member the record names, its shape and constructors, the
checked former that the parameters were compared against. -/
theorem TargetTyEntry.member_facts_of {fe : FEnv} {q : BlockShape} {outside nested : Bool}
    {rc : RecShape} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : TargetTyEntry mode F fe q outside nested cvTas ctorsAs rc cvRi M u)
    (hMs : M.member.isSome = true) :
    ∃ ms, M.member = some rc.tgt ∧ q.members[rc.tgt]? = some ms ∧ M.nIdx = ms.nIdx ∧
      M.nPc = q.nP ∧ ctorsAs[rc.tgt]? = some M.ctors ∧ cvTas[rc.tgt]? = some E.cvTP ∧
      E.maj.fvarTypeD.getAppFn = .const ms.cvT.name (q.lps.map .param) ∧
      E.maj.fvarTypeD.getAppArgs.take q.nP = E.fvs.take q.nP := by
  obtain ⟨cvTP, fvs, concl, tfvs, trest, maj, idoms, sty, hcv, hroom, hle, hopen, hmaj, major,
    htgt, hcvTP, _, _, _, _, _, _, _, _, _, _, _, _⟩ := E
  cases major with
  | member I t ms ctorsA hfn ht hms hctors hpar =>
    simp only [Option.all_some, beq_iff_eq] at htgt
    subst htgt
    simp only [Option.elim_some] at hcvTP
    have hI : ms.cvT.name = I := by
      have hlt := (List.findIdx?_eq_some_iff_getElem.mp ht)
      obtain ⟨hlt, hget, -⟩ := hlt
      have hmem : q.memberNames[rc.tgt]'hlt = ms.cvT.name := by
        have hlt' : rc.tgt < q.members.length := (List.getElem?_eq_some_iff.mp hms).1
        have hms' : q.members[rc.tgt]'hlt' = ms := (List.getElem?_eq_some_iff.mp hms).2
        simp only [BlockShape.memberNames, List.getElem_map, hms']
      rw [hmem] at hget
      exact eq_of_beq hget
    refine ⟨ms, rfl, hms, rfl, rfl, hctors, hcvTP, ?_, hpar⟩
    rw [hfn, hI]
  | outside => simp at hMs

/-- At a member major, any `outside`, the major's parameters are the
recursor type's first `nP` openers. -/
theorem targetDs_eq_prefTake_of {fe : FEnv} {q : BlockShape} {outside nested : Bool}
    {rc : RecShape} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : TargetTyEntry mode F fe q outside nested cvTas ctorsAs rc cvRi M u)
    (hMs : M.member.isSome = true) {fvsPref : List Expr} {oP : Expr}
    (hpref : openPisAtFvars rc.rP cvRi.type 0 = some (fvsPref, oP)) :
    M.ds = fvsPref.take q.nP := by
  rw [TargetTyEntry.ds_eq_of E hMs]
  obtain ⟨o', ho'⟩ := openPisAtFvars_prefix rc.rP (rc.mI + 1) _ 0 (by have := E.hle; omega) E.hopen
  rw [hpref] at ho'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj ho')
  rw [List.take_take, Nat.min_eq_left E.hroom]

/-- A stored entry of the check's output, at its index. -/
theorem tgtRs_getElem? {out : List (ConstantVal × TargetMajor × List Expr)} {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[i]? = some r) :
    ∃ t, out[i]? = some t ∧ r = (t.1, t.2.2, t.2.1.nIdx, t.2.1.ctors) := by
  simp only [tgtRs, List.getElem?_map] at hr
  cases ho : out[i]? with
  | none => rw [ho] at hr; exact nomatch hr
  | some t => rw [ho] at hr; exact ⟨t, rfl, (Option.some.inj hr).symm⟩

/-- **The run at a stored recursor**: its record, stage (b)'s entry, its
rules' run, and the stored entry — the checked constant, the annotated
rules, the major's index count and constructors. -/
theorem targetRecRun_at {fe : FEnv} {q : BlockShape} {outside nested : Bool}
    (R : TargetRecRun mode F fe q outside nested block cvTas ctorsAs out) {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[i]? = some r) :
    ∃ (rc : RecShape) (cvRi : ConstantVal) (M : TargetMajor) (u : Level) (rhssA : List Expr),
      q.recs[i]? = some rc ∧ R.tys[i]? = some (cvRi, M, u) ∧
      out[i]? = some (cvRi, M, rhssA) ∧ r = (cvRi, rhssA, M.nIdx, M.ctors) ∧
      rc.rhss.length = M.ctors.length ∧
      TargetRulesRun mode F (consBlockRecsBareF q 0 (R.tys.map fun t => (t.1, t.2.1.nIdx)) fe) fe
        q (cvTas.map (·.type)) (targetFamilyOf q R.tys) cvRi rc.rP M M.ctors rc.rhss rhssA ∧
      Nonempty (TargetTyEntry mode F fe q outside nested cvTas ctorsAs rc cvRi M u) := by
  obtain ⟨hlenT, hallT⟩ := targetRecTys_run R.htys
  obtain ⟨hlenO, hallO⟩ := targetRecsRules_run R.rules
  obtain ⟨t', ht', rfl⟩ := tgtRs_getElem? hr
  have hj : i < q.recs.length := by
    have := (List.getElem?_eq_some_iff.mp ht').1
    rw [hlenO] at this; omega
  obtain ⟨rc, hrc⟩ : ∃ rc, q.recs[i]? = some rc := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨cvRi, M, u, ht, E⟩ := hallT i rc hrc
  obtain ⟨rhssA, ho, hlenR, RR⟩ := hallO i rc (cvRi, M, u) hrc ht
  obtain rfl := Option.some.inj (ht'.symm.trans ho)
  exact ⟨rc, cvRi, M, u, rhssA, hrc, ht, ho, rfl, hlenR, RR, E⟩

/-- Recursor `i`'s record readings. -/
theorem recShape_at {q : BlockShape} {i : Nat} {rc : RecShape} (hrc : q.recs[i]? = some rc) :
    q.recTgtAt i = rc.tgt ∧ q.majorIdxAt i = rc.mI ∧ q.rulePrefixAt i = rc.rP := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [BlockShape.recTgtAt, BlockShape.majorIdxAt, BlockShape.rulePrefixAt,
      List.getD_eq_getElem?_getD, hrc, Option.getD_some]

/-- The large-elimination guard at a nested block implies the plain one. -/
theorem blockLargeElimAllowed_plain {q : BlockShape} {nested : Bool}
    (h : blockLargeElimAllowed q nested = true) : blockLargeElimAllowed q false = true := by
  cases nested
  · exact h
  · simp only [blockLargeElimAllowed, Bool.or_eq_true, Bool.and_eq_true, Bool.not_true,
      Bool.false_eq_true, and_false, false_and, or_false] at h
    simp [blockLargeElimAllowed, h]

/-- **Stage (b)'s major-free entry, from the target check's** (any major). -/
theorem recTyGen_of_target {q : BlockShape} {outside nested : Bool} {i : Nat} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level} (hrc : q.recs[i]? = some rc)
    (E : TargetTyEntry mode F (mkFEnv env) q outside nested cvTas ctorsAs rc cvRi M u) :
    Nonempty (RecTyGen mode F env q false i rc cvRi M.nIdx u) := by
  obtain ⟨-, hM, hR⟩ := recShape_at hrc
  have hmI := E.hmI
  have hcv : checkConstantVal (fueledOps mode F) env rc.cvR = .ok cvRi := by
    rw [← checkConstantValF_eq]; exact E.hcv
  refine ⟨{
    fvs := E.fvs, concl := E.concl, maj := E.maj, sty := E.sty, hcv := hcv,
    hroom := (by rw [hR]; exact E.hroom), hmI' := (by rw [hM, hR, hmI]),
    hopen := (by rw [hM]; exact E.hopen), hmaj := (by rw [hM]; exact E.hmaj),
    hsty := (by rw [hM]; exact E.hsty), hu := (by rw [hM]; exact E.hu),
    hsmall := (by
      rw [hM]
      rcases E.hsmall with h | h
      · exact .inl (blockLargeElimAllowed_plain h)
      · exact .inr h) }⟩

/-- **Stage (b)'s entry, from the target check's**: the type checked
against its major member (any `outside`, a member major). -/
theorem recTyEntry_of_targetG {q : BlockShape} {outside nested : Bool} {i : Nat}
    {rc : RecShape} {cvRi : ConstantVal}
    {M : TargetMajor} {u : Level} (hrc : q.recs[i]? = some rc)
    (E : TargetTyEntry mode F (mkFEnv env) q outside nested cvTas ctorsAs rc cvRi M u)
    (hMs : M.member.isSome = true) :
    Nonempty (RecTyEntry mode F env q false cvTas i rc cvRi M.nIdx u) := by
  obtain ⟨hT, hM, hR⟩ := recShape_at hrc
  obtain ⟨ms, hMm, hms, hnIdx, hnPc, -, hcvTa, hfn, hpar⟩ := E.member_facts_of hMs
  have hmI := E.hmI
  have htl : E.tfvs.length = q.nP := Verify.openPisAtFvars_length _ E.hopenT
  have hcv : checkConstantVal (fueledOps mode F) env rc.cvR = .ok cvRi := by
    rw [← checkConstantValF_eq]; exact E.hcv
  refine ⟨{
    ms := ms, cvTa := E.cvTP, fvs := E.fvs, concl := E.concl, tfvs := E.tfvs,
    trest := E.trest, maj := E.maj, sty := E.sty,
    hms := (by rw [hT]; exact hms), hcvTa := (by rw [hT]; exact hcvTa), hcv := hcv,
    hnIdx := hnIdx, hroom := (by rw [hR]; exact E.hroom),
    hmI := (by rw [hM, hR, hmI, hnIdx]), hopen := (by rw [hM]; exact E.hopen),
    hopenT := E.hopenT, htfvs := htl,
    hparams := fun l hl => E.hparams l (by rw [List.length_map, htl]; exact hl),
    hmaj := (by rw [hM]; exact E.hmaj), hmajFn := hfn,
    hmajLen := (by rw [E.hmajLen, hnPc, hnIdx]),
    hmajParams := hpar,
    hmajIdx := (by
      rw [← hnPc, E.hmajIdx, hR, hmI, ← hnIdx, Nat.add_sub_cancel_left]),
    hsty := (by rw [hM]; exact E.hsty), hu := (by rw [hM]; exact E.hu),
    hsmall := (by
      rw [hM]
      rcases E.hsmall with h | h
      · exact .inl (blockLargeElimAllowed_plain h)
      · exact .inr h) }⟩

/-- **The recursors whose CHECKED major is a member of the block** (lane
NESTIND): the stage's `mem` at the target check's output. -/
@[expose] def tgtMemAt (out : List (ConstantVal × TargetMajor × List Expr)) (i : Nat) : Prop :=
  (out[i]?).all (fun t => t.2.1.member.isSome) = true

/-- The stage record weakens along its `mem`. -/
def RecStage.mono {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {mem mem' : Nat → Prop} (R : RecStage mode F env p cvTas ctorsAs rs mem)
    (h : ∀ i, mem' i → mem i) : RecStage mode F env p cvTas ctorsAs rs mem' :=
  { R with
    fam := { R.fam with idxDoms := fun i hi hm => R.fam.idxDoms i hi (h i hm) }
    tyEntry := fun i hi hm => R.tyEntry i hi (h i hm)
    ctorsAt := fun i r hm hr => R.ctorsAt i r (h i hm) hr
    ruleTower := fun c r i cA rhs hm => R.ruleTower c r i cA rhs (h c hm) }

/-- **The stage record, from the target check's run, at ANY majors**
(lane NESTIND): the member-shaped facts at the recursors whose checked
major is a member (`tgtMemAt out`), the rest at every recursor.
`hctorsLen`: each member's checked constructors are its declared ones,
one for one (the constructors' stage). -/
theorem recStage_of_targetG {outside nested : Bool}
    (R : TargetRecRun mode F (mkFEnv env) p.toBlockShape outside nested block cvTas ctorsAs out)
    (hctorsLen : ∀ (t : Nat) (ms : MemberShape) (ctorsA : List (ConstantVal × Nat)),
      p.members[t]? = some ms → ctorsAs[t]? = some ctorsA → ctorsA.length = ms.ctors.length) :
    RecStageG mode F env p cvTas ctorsAs (tgtRs out) (tgtMemAt out) := by
  obtain ⟨hlenT, hallT⟩ := targetRecTys_run R.htys
  obtain ⟨hlenO, hallO⟩ := targetRecsRules_run R.rules
  have hpinsF := targetRecPins_inv R.pins
  have hlenT' : R.tys.length = p.recs.length := hlenT
  have hlenOut : (tgtRs out).length = p.recs.length := by
    simp only [tgtRs, List.length_map, hlenO, hlenT']
    exact Nat.min_self _
  -- the major at a position, member or not
  have hmemAt : ∀ (i : Nat) (rc : RecShape) (cvRi : ConstantVal) (M : TargetMajor) (u : Level),
      p.recs[i]? = some rc → R.tys[i]? = some (cvRi, M, u) → tgtMemAt out i →
      M.member.isSome = true := by
    intro i rc cvRi M u hrc ht hm
    obtain ⟨rhssA, ho, -, -⟩ := hallO i rc (cvRi, M, u) hrc ht
    simp only [tgtMemAt, ho, Option.all_some] at hm
    exact hm
  have hbare := targetRecRun_bare_eq R
  have hfeR : consBlockRecsBareF p.toBlockShape 0 (R.tys.map fun t => (t.1, t.2.1.nIdx))
      (mkFEnv env) = mkFEnv (consBlockRecsBare p.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) env) := by
    rw [consBlockRecsBareF_mkFEnv, hbare]
  refine ⟨{
    cvRus := R.tys.map fun t => (t.1, t.2.1.nIdx, t.2.2),
    pins := hpinsF,
    fam := ?_, lenT := (by rw [List.length_map]; exact hlenT'), len := hlenOut,
    stored := ?_, tyGen := ?_, tyEntry := ?_, ctorsAt := ?_, rulesLenAt := ?_,
    ruleOut := ?_, ruleTower := ?_ }⟩
  · -- the family's agreements
    have hus : (R.tys.map fun t => (t.1, t.2.1.nIdx, t.2.2)).map (·.2.2) = R.tys.map (·.2.2) := by
      simp [List.map_map, Function.comp_def]
    have hcs : (R.tys.map fun t => (t.1, t.2.1.nIdx, t.2.2)).map (·.1) = R.tys.map (·.1) := by
      simp [List.map_map, Function.comp_def]
    refine ⟨R.small.1, ?_, ?_, ?_, ?_⟩
    · rw [hus]
      rcases R.small.2 with h | h
      · exact .inl (blockLargeElimAllowed_plain h)
      · exact .inr h
    · rw [hus]; exact R.pin
    · intro i hi hm
      rw [List.length_map, hlenT'] at hi
      obtain ⟨rc, hrc⟩ : ∃ rc, p.recs[i]? = some rc := ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨cvRi, M, u, ht, ⟨E⟩⟩ := hallT i rc hrc
      obtain ⟨hT, hM, hR⟩ := recShape_at (q := p.toBlockShape) hrc
      obtain ⟨ms, hMm, hms, hnIdx, hnPc, -, hcvTa, -⟩ :=
        E.member_facts_of (hmemAt i rc cvRi M u hrc ht hm)
      obtain ⟨cvTa, tfs, trest, hcvTa', hopI, hidoms⟩ := targetIdxDoms_member hMm E.hidoms
      have hil := E.hidxLen
      have hix := E.hidx
      rw [hidoms] at hil hix
      have hsub : rc.mI - rc.rP = M.nIdx := by rw [E.hmI]; omega
      rw [hsub] at hil hix
      refine ⟨cvRi, M.nIdx, u, cvTa, E.fvs, tfs, E.concl, trest, ?_, ?_, ?_, ?_,
        by rw [hR]; exact hil, ?_⟩
      · simp only [List.getElem?_map, ht, Option.map_some]
      · rw [hT]; exact hcvTa'
      · rw [hM]; exact E.hopen
      · rw [hR]; exact hopI
      · intro q hq
        rw [hM, hR]
        exact hix q hq
    · rw [hcs]; exact R.prefixAgree
  · -- the stored records are stage (b)'s
    rw [← hbare]
    simp [List.map_map, Function.comp_def]
  · -- stage (b) at every recursor, major-free
    intro i hi
    obtain ⟨rc, hrc⟩ : ∃ rc, p.recs[i]? = some rc := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨cvRi, M, u, ht, ⟨E⟩⟩ := hallT i rc hrc
    refine ⟨rc, cvRi, M.nIdx, u, hrc, ?_, recTyGen_of_target (q := p.toBlockShape) hrc E⟩
    simp only [List.getElem?_map, ht, Option.map_some]
  · -- stage (b) at every member-major recursor
    intro i hi hm
    obtain ⟨rc, hrc⟩ : ∃ rc, p.recs[i]? = some rc := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨cvRi, M, u, ht, ⟨E⟩⟩ := hallT i rc hrc
    refine ⟨rc, cvRi, M.nIdx, u, hrc, ?_,
      recTyEntry_of_targetG (q := p.toBlockShape) hrc E (hmemAt i rc cvRi M u hrc ht hm)⟩
    simp only [List.getElem?_map, ht, Option.map_some]
  · -- each stored member-major recursor's constructors
    intro i r hm hr
    obtain ⟨rc, cvRi, M, u, rhssA, hrc, ht, -, rfl, -, -, ⟨E⟩⟩ := targetRecRun_at R hr
    obtain ⟨hT, -, -⟩ := recShape_at (q := p.toBlockShape) hrc
    obtain ⟨ms, -, hms, -, -, hctors, -⟩ := E.member_facts_of (hmemAt i rc cvRi M u hrc ht hm)
    rw [hT]
    exact ⟨ms, hms, hctors, hctorsLen _ _ _ hms hctors⟩
  · -- one stored rule per constructor
    intro i r hr
    obtain ⟨rc, cvRi, M, u, rhssA, -, -, -, rfl, -, RR, -⟩ := targetRecRun_at R hr
    exact RR.len
  · -- every stored rule, annotated
    intro c r i rhs hr hrhs
    obtain ⟨rc, cvRi, M, u, rhssA, hrc, -, -, rfl, hlenR, RR, ⟨E⟩⟩ := targetRecRun_at R hr
    simp only at hrhs
    have hiA : i < M.ctors.length := by
      rw [← RR.len]; exact (List.getElem?_eq_some_iff.mp hrhs).1
    have hcA : M.ctors[i]? = some M.ctors[i] := List.getElem?_eq_getElem hiA
    obtain ⟨rhs0, hrhs0⟩ : ∃ rhs0, rc.rhss[i]? = some rhs0 :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenR]; exact hiA)⟩
    obtain ⟨o, hoi, hrun⟩ := RR.rule i _ rhs0 hcA hrhs0
    obtain rfl : rhs = o := Option.some.inj (hrhs.symm.trans hoi)
    obtain ⟨Q⟩ := targetRule_run hrun
    rw [hfeR] at Q
    have hlp : cvRi.levelParams = rc.cvR.levelParams :=
      (checkConstantVal_lps (by rw [← checkConstantValF_eq]; exact E.hcv)).2
    refine ⟨rc, rhs0, hrc, hrhs0, ⟨Q.hbv, Q.hfv, Q.hann, by rw [← hlp]; exact Q.hlp, ?_,
      Q.tyR, Q.htyR⟩⟩
    have h := Q.hres
    simp only [StructWalkers.plain, constsResolveF_eq] at h
    exact h
  · -- every stored member-major rule's λ-tower
    intro c r i cA rhs hm hr hcA hrhs
    obtain ⟨rc, cvRi, M, u, rhssA, hrc, ht, ho, rfl, hlenR, RR, ⟨E⟩⟩ := targetRecRun_at R hr
    have hMs := hmemAt c rc cvRi M u hrc ht hm
    obtain ⟨-, -, hR⟩ := recShape_at (q := p.toBlockShape) hrc
    obtain ⟨ms, hMm, -, -, -, -, -⟩ := E.member_facts_of hMs
    simp only at hcA hrhs
    obtain ⟨rhs0, hrhs0⟩ : ∃ rhs0, rc.rhss[i]? = some rhs0 :=
      ⟨_, List.getElem?_eq_getElem (by
        rw [hlenR]; exact (List.getElem?_eq_some_iff.mp hcA).1)⟩
    obtain ⟨o, hoi, hrun⟩ := RR.rule i cA rhs0 hcA hrhs0
    obtain rfl : rhs = o := Option.some.inj (hrhs.symm.trans hoi)
    obtain ⟨Q⟩ := targetRule_run hrun
    rw [hfeR] at Q
    have hlp : cvRi.levelParams = rc.cvR.levelParams :=
      (checkConstantVal_lps (by rw [← checkConstantValF_eq]; exact E.hcv)).2
    have hds := targetDs_eq_prefTake_of E hMs Q.hpref
    obtain ⟨hnPc, hlvls⟩ := targetTyEntry_major_of E hMs
    have hct : targetCtorAt M cA.1 = cA.1.type := by simp [targetCtorAt, hMm]
    have hc := Q.hcrest
    rw [hct, hds, instPisWith_eq_instPisAt] at hc
    obtain ⟨cpref, hcpar⟩ : ∃ cpref, Expr.instPisAt (Q.fvsPref.take p.nP) cA.1.type
        = some (cpref, Q.crest) := by
      cases hq : Expr.instPisAt (Q.fvsPref.take p.nP) cA.1.type with
      | none => rw [hq] at hc; exact nomatch hc
      | some pr =>
        rw [hq] at hc
        exact ⟨pr.1, by rw [← Option.some.inj hc]⟩
    have hrecTy : ((tgtRs out).map (·.1.type))[c]? = some cvRi.type := by
      simp only [tgtRs, List.map_map, List.getElem?_map, ho, Option.map_some,
        Function.comp_def]
    refine ⟨rc, rhs0, hrc, hrhs0, ⟨{
      recTy := cvRi.type, tyR := Q.tyR, rbs := Q.rbs, body := Q.body, fvsPref := Q.fvsPref, oPref := Q.oPref, cpref := cpref, crest := Q.crest,
      fvsF := Q.fvsF, cbody := Q.cbody, ldoms := Q.ldoms, lrest := Q.lrest, concl := Q.concl,
      hrecTy := hrecTy, hbv := Q.hbv, hfv := Q.hfv, hann := Q.hann,
      hlp := (by rw [← hlp]; exact Q.hlp),
      hres := (by
        have h := Q.hres
        simp only [StructWalkers.plain, constsResolveF_eq] at h
        exact h),
      htyR := Q.htyR, hstrip := (by rw [hR]; exact Q.hstrip), hpw := Q.hpw,
      hpref := (by rw [hR]; exact Q.hpref), hcpar := hcpar,
      hfld := (by rw [hR]; exact Q.hfld), hlams := Q.hlams,
      hldomsRes := fun t ht => (by
        have h := Q.hldomsRes t ht
        simp only [StructWalkers.plain, constsResolveF_eq] at h
        exact h),
      hG2len := Q.hG2len, hG2 := fun l hl => (by rw [hR]; exact Q.hG2 l hl),
      hconcl := (by
        have hc := Q.hconcl
        rw [hnPc, hlvls, hds] at hc
        exact hc) }⟩⟩


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


end Producer

/-! ## The cons at the majors, generic in the rules (lane NESTIND, session 14)

`consBlockRecsT` is the generic cons `consBlockRecsR` (`BlockWF.lean`) at
`tgtRulesR`: each recursor's rules at ITS major, read off the absolute
position. -/

/-- The switch-on route's rules function: each recursor's stored rules
at its major `Ms m` (`tgtStoredRules`). -/
@[expose] def tgtRulesR (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (q : BlockShape) (Ms : Nat → TargetMajor) :
    Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List RecRule :=
  fun m r => tgtStoredRules find? resolves r.1 (q.majorIdxAt m) (q.rulePrefixAt m) (Ms m) r.2.1

/-- The checked majors by absolute position. -/
@[expose] def tgtMajorsOf (out : List (ConstantVal × TargetMajor × List Expr)) :
    Nat → TargetMajor :=
  fun m => (out.getD m default).2.1

/-- `consBlockRecsT` is the generic cons at `tgtRulesR`, from any start. -/
theorem consBlockRecsT_eq_R_gen (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (q : BlockShape) (Ms : Nat → TargetMajor) :
    ∀ (m : Nat) (out : List (ConstantVal × TargetMajor × List Expr)) (env : Env),
      (∀ (i : Nat) (t : ConstantVal × TargetMajor × List Expr), out[i]? = some t →
        Ms (m + i) = t.2.1) →
      consBlockRecsT find? resolves q m out env
        = consBlockRecsR (tgtRulesR find? resolves q Ms) q m (tgtRs out) env
  | _, [], _, _ => rfl
  | m, (cv, M, rhss) :: rest, env, hMs => by
    have h0 : Ms m = M := by simpa using hMs 0 _ rfl
    simp only [consBlockRecsT, tgtRs, List.map_cons, consBlockRecsR, tgtRulesR, h0]
    exact consBlockRecsT_eq_R_gen find? resolves q Ms (m + 1) rest _
      (fun i t ht => by
        have := hMs (i + 1) t (by simpa using ht)
        rwa [show m + (i + 1) = m + 1 + i by omega] at this)

/-- **`consBlockRecsT` is the generic cons at `tgtRulesR`.** -/
theorem consBlockRecsT_eq_R (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (q : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) (env : Env) :
    consBlockRecsT find? resolves q 0 out env
      = consBlockRecsR (tgtRulesR find? resolves q (tgtMajorsOf out)) q 0 (tgtRs out) env :=
  consBlockRecsT_eq_R_gen find? resolves q _ 0 out env fun i t ht => by
    simp [tgtMajorsOf, List.getD_eq_getElem?_getD, ht]

/-- The switch-on route's firing at position `j`: `.nested` (or
`.inert`) as `auxRuleFireR` reads it at an OUTSIDE major, `sumRules`'
test at a member one. -/
@[expose] def tgtFireOf (resolves : Expr → Bool) (q : BlockShape) (Ms : Nat → TargetMajor)
    (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) : RecRuleFire :=
  match (Ms j).member with
  | none => auxRuleFireR resolves r.1 (q.majorIdxAt j) (q.rulePrefixAt j) (Ms j).nPc
  | some _ => if Expr.recRulePlain r.1.type (q.majorIdxAt j) (q.rulePrefixAt j) (Ms j).nPc
      then .plain else .inert

/-- **A `.nested` firing is an outside major's reading**, with its
guards (`nestedRuleSyn_inv`): `EnvWF`'s clause at `resolves`. -/
theorem tgtFireOf_nested {resolves : Expr → Bool} {q : BlockShape} {Ms : Nat → TargetMajor}
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    {lvls : List Level} {pins : List Expr}
    (h : tgtFireOf resolves q Ms j r = .nested lvls pins) :
    q.rulePrefixAt j ≤ q.majorIdxAt j ∧
    (∀ l ∈ lvls, l.allParamsDefined r.1.levelParams = true) ∧
    (∀ pin ∈ pins, pin.hasFvar = false ∧
      pin.allLevelParamsDefined r.1.levelParams = true ∧
      resolves pin = true ∧
      pin.looseBVarsBounded (q.rulePrefixAt j) = true) ∧
    ∃ pre dom body bm D,
      r.1.type.stripPis (q.majorIdxAt j) = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (q.majorIdxAt j - q.rulePrefixAt j) 0) ++
          (List.range (q.majorIdxAt j - q.rulePrefixAt j)).map
            (fun i => Expr.bvar (q.majorIdxAt j - q.rulePrefixAt j - 1 - i)) := by
  unfold tgtFireOf at h
  split at h
  · simp only [auxRuleFireR] at h
    split at h
    · rename_i lvls' pins' hsyn
      injection h with h1 h2
      subst h1 h2
      obtain ⟨h1, h2, h3, pre, dom, body, bm, D, hs, hfn, hargs, -⟩ := nestedRuleSyn_inv hsyn
      exact ⟨h1, h2, h3, pre, dom, body, bm, D, hs, hfn, hargs⟩
    · exact nomatch h
  · split at h <;> exact nomatch h

/-- **The switch-on route's rules have the shape**, at each major's
parameter count and `tgtFireOf`. -/
theorem recRulesShape_tgt (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (q : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) :
    RecRulesShape find? (tgtRulesR find? resolves q (tgtMajorsOf out)) (tgtRs out)
      (fun j => (tgtMajorsOf out j).nPc) (tgtFireOf resolves q (tgtMajorsOf out)) := by
  intro j r hr rl hrl
  obtain ⟨t, ht, rfl⟩ : ∃ t, out[j]? = some t ∧ r = (t.1, t.2.2, t.2.1.nIdx, t.2.1.ctors) := by
    simp only [tgtRs, List.getElem?_map] at hr
    cases ho : out[j]? with
    | none => rw [ho] at hr; exact nomatch hr
    | some t => rw [ho] at hr; exact ⟨t, rfl, (Option.some.inj hr).symm⟩
  have hM : tgtMajorsOf out j = t.2.1 := by
    simp [tgtMajorsOf, List.getD_eq_getElem?_getD, ht]
  simp only [tgtRulesR, tgtStoredRules, hM] at hrl
  simp only [tgtFireOf, hM]
  cases hm : t.2.1.member with
  | some _ =>
    rw [hm] at hrl
    exact sumRules_getElem? hrl
  | none =>
    rw [hm] at hrl
    simp only [List.mem_map] at hrl
    obtain ⟨rl0, hrl0, rfl⟩ := hrl
    obtain ⟨i, cA, rhs, hcA, hrhs, rfl⟩ := sumRules_getElem? hrl0
    exact ⟨i, cA, rhs, hcA, hrhs, rfl⟩

end ConLeche
