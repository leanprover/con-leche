module

public import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.CheckerF
public import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.DirectGen

public section

/-!
# The recursor stage's KIND-FREE facts

The recursor stage is the generated one (`genRecCheck` at the
constructors' index, `recStage_of_gen`, `Model/Inductives/GenRecStage.lean`).
Every proof about the stage reads ONE record of what the stage
guarantees about the family it stores — `RecStage` — and never unfolds
it:

* the records' pins (the level parameters, the reserved names, the
  name set);
* the family's agreements (`RecFamFacts`: the counting guard, the
  elimination-level pin, the shared rule prefix);
* the stored family's shape (lengths, the bridge from the checked
  constants to the stored ones);
* every stored rule, checked at the rule-less recursors (`RuleOutOk`).

Nothing here names a field kind or an `ih` frame: those belong to the
check's own records (`TargetRuleRun`), which the model reads for the
rule contract.  The record is produced from the generated stage's run
(`recStage_of_gen`).
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

/-- **One rule's stored right-hand side, at ANY major**: `out`, stored
at the rule-less recursors' environment `envR` — closed, its level
parameters the recursor's, its constants resolved and its type inferred
there (a generated rule stored as generated). -/
structure RuleOutOk (mode : CheckMode) (F : Nat) (envR : Env) (cvR : ConstantVal)
    (out : Expr) : Prop where
  hbv : out.looseBVarsBounded 0 = true
  hfv : out.hasFvar = false
  hlp : out.allLevelParamsDefined cvR.levelParams = true
  hres : out.constsResolve envR = true
  htyR : ∃ tyR, inferTypeCore mode false envR F 0 out = .ok tyR

namespace RuleOutOk

variable {F : Nat} {envR : Env} {cvR : ConstantVal} {rhs out : Expr}

end RuleOutOk

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

/-- **The family's rule prefix, shared SYNTACTICALLY** (a generated
family): every recursor type, opened at the first recursor's rule
prefix, has the first recursor's opened binder domains, and every
recursor's prefix has that length. -/
@[expose] def RecPrefixSame (p : BlockShape) (cvRs : List ConstantVal) : Prop :=
  ∀ cv0, cvRs[0]? = some cv0 → ∃ (fvs0 : List Expr) (o0 : Expr),
    openPisAtFvars (p.rulePrefixAt 0) cv0.type 0 = some (fvs0, o0) ∧
    ∀ (i : Nat) (cv : ConstantVal), cvRs[i]? = some cv →
      p.rulePrefixAt i = p.rulePrefixAt 0 ∧
      ∃ (fvs : List Expr) (o : Expr),
        openPisAtFvars (p.rulePrefixAt 0) cv.type 0 = some (fvs, o) ∧
        fvs.map Expr.fvarTypeD = fvs0.map Expr.fvarTypeD

/-- **The family's agreements**, over stage (b)'s list: the counting
half of the elimination guard, the elimination-level PIN, and the
shared rule prefix. -/
structure RecFamFacts (mode : CheckMode) (F : Nat) (env : Env) (p : BlockShape)
    (cvTas : List ConstantVal) (cvRus : List (ConstantVal × Nat × Level)) : Prop where
  /-- the block declares a family -/
  k_pos : 0 < p.k
  /-- the counting half of the elimination guard -/
  small : blockLargeElimAllowed p false = true ∨
    ∀ u ∈ cvRus.map (·.2.2), Level.isEquiv u Level.zero = some true
  /-- the elimination-level PIN -/
  pin : ∀ u ∈ cvRus.map (·.2.2),
    Level.isEquiv u (structElimLevel p.elim p.large) = some true
  /-- the shared rule prefix, shared syntactically (a generated family) -/
  prefixAgree : RecPrefixSame p (cvRus.map (·.1))

/-- **The recursor stage, as checked** — its kind-free facts.  `env` is
the constructors' environment, `rs` the stored family (install format).
Every fact holds at every recursor, an auxiliary one (an outside
major) included. -/
structure RecStage (mode : CheckMode) (F : Nat) (env : Env) (p : BlockParts)
    (cvTas : List ConstantVal)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) : Type where
  /-- stage (b)'s list: the checked constant, its major's index count,
  its conclusion's sort -/
  cvRus : List (ConstantVal × Nat × Level)
  /-- (a) the records' pins -/
  pins : RecPinsF p.toBlockShape
  /-- (b') the family's agreements -/
  fam : RecFamFacts mode F env p.toBlockShape cvTas cvRus
  lenT : cvRus.length = p.recs.length
  len : rs.length = p.recs.length
  /-- the stored records are stage (b)'s -/
  stored : rs.map (fun r => (r.1, r.2.2.1)) = cvRus.map (fun q => (q.1, q.2.1))
  /-- (b) every recursor's type, at any major -/
  tyGen : ∀ i, i < p.recs.length → ∃ rc cvRi nIdx u, p.recs[i]? = some rc ∧
    cvRus[i]? = some (cvRi, nIdx, u) ∧
    Nonempty (RecTyGen mode F env p.toBlockShape false i rc cvRi nIdx u)
  /-- one stored rule per constructor -/
  rulesLenAt : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    rs[i]? = some r → r.2.1.length = r.2.2.2.length
  /-- (c) every stored rule, checked at the rule-less recursors -/
  ruleOut : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) (i : Nat)
    (rhs : Expr), rs[c]? = some r → r.2.1[i]? = some rhs →
    ∃ rc, p.recs[c]? = some rc ∧
      RuleOutOk mode F (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env)
        rc.cvR rhs

/-- The stage's facts, as a proposition. -/
@[expose] def RecStageG (mode : CheckMode) (F : Nat) (env : Env) (p : BlockParts)
    (cvTas : List ConstantVal)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) : Prop :=
  Nonempty (RecStage mode F env p cvTas rs)

namespace RecStage

variable {F : Nat} {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}

/-- **The bridge at an index**: stage (b)'s entry at a stored
recursor is its checked constant, with the same index count. -/
theorem stored_at (R : RecStage mode F env p cvTas rs) {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[i]? = some r) :
    ∃ u, R.cvRus[i]? = some (r.1, r.2.2.1, u) := by
  have hil : i < R.cvRus.length := by
    rw [R.lenT, ← R.len]; exact (List.getElem?_eq_some_iff.mp hr).1
  refine ⟨R.cvRus[i].2.2, ?_⟩
  have h := congrArg (·[i]?) R.stored
  simp only [List.getElem?_map, hr, List.getElem?_eq_getElem hil, Option.map_some,
    Option.some.injEq, Prod.mk.injEq] at h
  rw [List.getElem?_eq_getElem hil, h.1, h.2]

/-- **Every constructor has its rule.** -/
theorem rulesLen (R : RecStage mode F env p cvTas rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) : r.2.1.length = r.2.2.2.length :=
  R.rulesLenAt c r hr

/-- **Stage (b)'s major-free entry at a STORED recursor** (any major). -/
theorem tyGenAt (R : RecStage mode F env p cvTas rs) {i : Nat}
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

/-- **A stored rule is checked at the rule-less recursors** (any major). -/
theorem ruleOutOf (R : RecStage mode F env p cvTas rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {rhs : Expr} (hrhs : rhs ∈ r.2.1) :
    ∃ (i : Nat) (rc : RecShape),
      r.2.1[i]? = some rhs ∧ p.recs[c]? = some rc ∧
      RuleOutOk mode F (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env)
        rc.cvR rhs := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hrhs
  obtain ⟨rc, hrc, hQ⟩ := R.ruleOut c r i rhs hr hi
  exact ⟨i, rc, hi, hrc, hQ⟩

end RecStage

/-! ## The base inversions, read off the record -/

section Base

variable {F : Nat} {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}

/-- **Stage (b)'s major-free record at a STORED recursor** (any major). -/
theorem recStageG_tyGen (h : RecStageG mode F env p cvTas rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) :
    ∃ rc u, p.recs[i]? = some rc ∧
      Nonempty (RecTyGen mode F env p.toBlockShape false i rc r.1 r.2.2.1 u) := by
  obtain ⟨R⟩ := h
  obtain ⟨rc, u, hrc, -, E⟩ := R.tyGenAt hr
  exact ⟨rc, u, hrc, E⟩

/-- **The CHECK's own well-formedness contract**: every stored
recursor type is a CHECKED constant's, and every stored rule's
right-hand side is closed, at the recursor's level parameters, and
resolves at the BARE-`k` environment. -/
theorem recStage_facts (h : RecStageG mode F env p cvTas rs) :
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
  refine ⟨E.hcv.noFvar, E.hcv.lpsDef, E.hcv.resolves, E.hcv.bounded, fun rhs hrhs => ?_⟩
  obtain ⟨i, rc', -, hrc', Q⟩ := R.ruleOutOf hc hrhs
  obtain rfl := Option.some.inj (hrc.symm.trans hrc')
  exact ⟨Q.hfv, by rw [E.lps_eq]; exact Q.hlp, Q.hres, Q.hbv⟩

/-- **The CHECK's stored recursors take no guarded name.** -/
theorem recStage_reserved (h : RecStageG mode F env p cvTas rs) :
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
theorem recStageG_recNames (h : RecStageG mode F env p cvTas rs) :
    RecPinsF p.toBlockShape ∧ rs.length = p.recs.length ∧
    ∀ i, i < p.recs.length → ∃ rc r, p.recs[i]? = some rc ∧ rs[i]? = some r ∧
      r.1.name = rc.cvR.name ∧
      (∃ cv0, cv0.name = rc.cvR.name ∧ cv0.levelParams = rc.cvR.levelParams ∧
        ConstChecked mode F env cv0 r.1) ∧
      p.nP ≤ p.toBlockShape.rulePrefixAt i ∧
      ∃ nIdx, p.toBlockShape.majorIdxAt i = p.toBlockShape.rulePrefixAt i + nIdx := by
  obtain ⟨R⟩ := h
  refine ⟨R.pins, R.len, fun i hil => ?_⟩
  have hi' : i < rs.length := by rw [R.len]; exact hil
  have hr : rs[i]? = some rs[i] := List.getElem?_eq_getElem hi'
  obtain ⟨rc, u, hrc, -, ⟨E⟩⟩ := R.tyGenAt hr
  exact ⟨rc, _, hrc, hr, E.name_eq, ⟨E.cv0, E.hcv0.1, E.hcv0.2, E.hcv⟩, E.nP_le, _, E.mI_eq⟩

/-- **The stored recursors' name facts**, from the per-recursor check
(`ConstChecked`): freshness at the constructors' environment and the
two name guards. -/
theorem recStage_cvFacts (h : RecStageG mode F env p cvTas rs) :
    ∀ r ∈ rs,
      env.find? r.1.name = none ∧
      reservedBasisNames.contains r.1.name = false := by
  obtain ⟨-, hlenR, hall⟩ := recStageG_recNames h
  intro r hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  have hil : i < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨rc, r', hrc, hr', hname, ⟨cv0, hn0, -, hcv⟩, -, -⟩ := hall i hil
  obtain rfl := Option.some.inj (hi.symm.trans hr')
  have hname' : r.1.name = cv0.name := by rw [hname, hn0]
  refine ⟨by rw [hname']; exact hcv.fresh, by rw [hname']; exact hcv.unreserved⟩

/-- A recursor takes no certified operation's name. -/
theorem recStage_opName (h : RecStageG mode F env p cvTas rs) :
    ∀ r ∈ rs, natOpName r.1.name = false := by
  intro r hr
  have hn := recStage_reserved h r hr
  simp only [reservedRecName, Bool.or_eq_false_iff] at hn
  simp only [natOpName, Bool.or_eq_false_iff]
  exact ⟨hn.1.1.1.1.2, hn.1.1.1.2⟩

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

end Producer

/-! ## The cons at the majors, generic in the rules

`consBlockRecsT` is the generic cons `consBlockRecsR` (`BlockWF.lean`) at
`tgtRulesR`: each recursor's rules at ITS major, read off the absolute
position. -/

/-- The install's rules function: each recursor's stored rules
at its major `Ms m` (`tgtStoredRules`). -/
@[expose] def tgtRulesR
    (q : BlockShape) (Ms : Nat → TargetMajor) :
    Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → Bool × List RecRule :=
  fun m r => (recKExpected q (Ms m), tgtStoredRules (q.rulePrefixAt m) (Ms m) r.2.1)

/-- The checked majors by absolute position. -/
@[expose] def tgtMajorsOf (out : List (ConstantVal × TargetMajor × List Expr)) :
    Nat → TargetMajor :=
  fun m => (out.getD m default).2.1

/-- `consBlockRecsT` is the generic cons at `tgtRulesR`, from any start. -/
theorem consBlockRecsT_eq_R_gen (q : BlockShape) (Ms : Nat → TargetMajor) :
    ∀ (m : Nat) (out : List (ConstantVal × TargetMajor × List Expr)) (env : Env),
      (∀ (i : Nat) (t : ConstantVal × TargetMajor × List Expr), out[i]? = some t →
        Ms (m + i) = t.2.1) →
      consBlockRecsT q m out env
        = consBlockRecsR (tgtRulesR q Ms) q m (tgtRs out) env
  | _, [], _, _ => rfl
  | m, (cv, M, rhss) :: rest, env, hMs => by
    have h0 : Ms m = M := by simpa using hMs 0 _ rfl
    simp only [consBlockRecsT, tgtRs, List.map_cons, consBlockRecsR, tgtRulesR, h0]
    exact consBlockRecsT_eq_R_gen q Ms (m + 1) rest _
      (fun i t ht => by
        have := hMs (i + 1) t (by simpa using ht)
        rwa [show m + (i + 1) = m + 1 + i by omega] at this)

/-- **`consBlockRecsT` is the generic cons at `tgtRulesR`.** -/
theorem consBlockRecsT_eq_R (q : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) (env : Env) :
    consBlockRecsT q 0 out env
      = consBlockRecsR (tgtRulesR q (tgtMajorsOf out)) q 0 (tgtRs out) env :=
  consBlockRecsT_eq_R_gen q _ 0 out env fun i t ht => by
    simp [tgtMajorsOf, List.getD_eq_getElem?_getD, ht]

/-- The install's firing at position `j` (the generic `fireOf` shape,
`RecRulesShape`; the recursor itself is not read): `auxRuleFire` at an
OUTSIDE major, `.plain` at a member one. -/
@[expose] def tgtFireOf (q : BlockShape) (Ms : Nat → TargetMajor)
    (j : Nat) (_r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) : RecRuleFire :=
  match (Ms j).member with
  | none => auxRuleFire (Ms j) (q.rulePrefixAt j)
  | some _ => .plain

/-- **A `.nested` firing is an outside major's datum**: its levels and
pins are `auxRuleFire`'s. -/
theorem tgtFireOf_nested_eq {q : BlockShape} {Ms : Nat → TargetMajor}
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    {lvls : List Level} {pins : List Expr}
    (h : tgtFireOf q Ms j r = .nested lvls pins) :
    (Ms j).member = none ∧ lvls = (Ms j).lvls ∧
      pins = (Ms j).ds.map (Expr.abstractPrefix (q.rulePrefixAt j) 0) := by
  unfold tgtFireOf at h
  split at h
  · rename_i hm
    simp only [auxRuleFire, RecRuleFire.nested.injEq] at h
    exact ⟨hm, h.1.symm, h.2.symm⟩
  · exact nomatch h

/-- **At an outside major the rules fire `.nested`**, at `auxRuleFire`'s
datum. -/
theorem tgtFireOf_of_out {q : BlockShape} {Ms : Nat → TargetMajor}
    {j : Nat} (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
    (hm : (Ms j).member = none) :
    tgtFireOf q Ms j r
      = .nested (Ms j).lvls ((Ms j).ds.map (Expr.abstractPrefix (q.rulePrefixAt j) 0)) := by
  simp only [tgtFireOf, hm, auxRuleFire]

/-- **The install's rules have the shape**, at each major's
parameter count and `tgtFireOf`. -/
theorem recRulesShape_tgt
    (q : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) :
    RecRulesShape (tgtRulesR q (tgtMajorsOf out)) (tgtRs out)
      (tgtFireOf q (tgtMajorsOf out)) := by
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
