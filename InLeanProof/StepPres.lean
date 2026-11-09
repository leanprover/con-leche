module

public import InLeanProof.EnvBodiesPres
public import InLeanProof.IndPres
public import InLeanProof.IndShape
public import InLeanProof.QuotPres
/- `ConstantInfo.isInductive`/`isCtor` (read by `storedBlock`) are not exposed. -/
import all Lean.Declaration

/-!
# The steps' side conditions (task #451, lane P3c)

* **`ProjBodiesInRange` is kept by every step** (`projBodiesInRange_group`,
  `projBodiesInRange_one`).  For a structure already stored nothing changes:
  its constructor is stored (`CtorsStored`, from `EnvPresI`), so a group of
  fresh names changes neither lookup `findProj?` makes.  For a structure the
  group declares, InLean's inductive check tests its bodies' range on the
  extended environment (`FEnv.projBodiesInRange`, an internal error
  otherwise; `checkInductiveC_ok` reads it off an accepted run).  At the start
  it holds of every environment that declares no structure
  (`projBodiesInRange_of_none`, e.g. the empty one), so `ssimI_of_pres` needs
  it of no environment the theorem reaches.
* **The generator's constants are the stored block's** (`mem_storedBlock`):
  `checkInductiveC` refuses a generated constant that is no former,
  constructor or recursor (`isBlockConst`), so `IndGroupPresBP`'s premise
  holds of what an accepted run adds.
* **`Quot.sound`'s step** (`presI_quotSound`): `checkAxiomC` matches the
  axiom against the pin instantiated at the axiom's own level name
  (`quotSoundHit`, twin of `quotPinHit .sound`), which is what con-leche
  installs (`quotAt .sound`); `checkAxiomC_quotSound` reads it, the name's
  freshness and the added constant off an accepted run.
* **The inductive check** (`BlockPresObl`'s premise): `checkIndDeclC_ok` (an
  accepted check is a recognised block whose generated entries agree and whose
  block check passed; the shapeless branch and a parameter mismatch throw),
  and `basisNameHit_toBlock` (con-leche's pinned-name test on the translated
  block is InLean's, which the reserved names' check reads).
-/

public section

namespace InLeanProof

open Lean InLean

variable {fe : InLean.FEnv} {L : ConLeche.Env}

/-! ## The projection bodies' range -/

/-- **A stored former's constructors are stored**, unless it is a member of
the block being checked (`EntryRelI`'s former clause). -/
@[expose] def CtorsStored (fe : InLean.FEnv) : Prop :=
  ∀ T v, fe.find? T = some (.inductInfo v) → fe.isPending v.name = false →
    ∀ c ∈ v.ctors, (fe.find? c).isSome

theorem ctorsStored_of_pres (hP : EnvPresI fe L) : CtorsStored fe := by
  intro T v h hnp c hc
  obtain ⟨cci, -, hr⟩ := hP.entry T _ h
  cases cci <;> simp only [EntryRelI] at hr
  rcases hr.2.2 with h' | h'
  · rw [hnp] at h'; cases h'
  · exact h' c hc

/-- **What the check says of one table**: every body `findProj?` gives rise
to is in range. -/
theorem inRange_of_projBodiesInRange {T : Name} {i : Nat} {e : ProjEntry} {b : Expr}
    (hc : fe.projBodiesInRange T = true) (h : fe.findProj? T i = some e)
    (hb : projBodyAt e.structName e.numParams e.idx e.ctorType = some b) : EO.inRange b = true := by
  unfold InLean.FEnv.findProj? at h
  cases ht : fe.findTable? T with
  | none => rw [ht] at h; cases h
  | some t =>
  rw [ht] at h
  unfold InLean.FEnv.findTable? at ht
  unfold InLean.FEnv.projBodiesInRange at hc
  split at ht
  next v hT =>
    simp only [hT] at hc
    split at ht
    · cases ht
    split at ht
    next c hcs =>
      simp only [hcs] at hc
      split at ht
      next hI =>
        simp only [hI, ↓reduceIte] at hc
        split at ht
        next cv hcv =>
          simp only [hcv] at hc
          split at ht
          next hp =>
            simp only [hp, ↓reduceIte, List.all_eq_true] at hc
            simp only [Option.some.injEq] at ht
            subst ht
            by_cases hi : i < cv.numFields
            · simp only [hi, ↓reduceIte, Option.some.injEq] at h
              subst h
              have := hc i (List.mem_range.2 hi)
              simp only [InLean.TableView.entry] at hb
              rw [hb] at this
              exact this
            · simp [hi] at h
          · cases ht
        · cases ht
      · cases ht
    · cases ht
  · cases ht

/-- **Every environment without a structure** has its bodies in range. -/
theorem projBodiesInRange_of_none (h : ∀ T i, fe.findProj? T i = none) : ProjBodiesInRange fe := by
  intro T i e he
  rw [h T i] at he; cases he

/-- The lookups after adding fresh, distinct constants, through `FEnv.find?`. -/
theorem feFind_foldl_out (hlaws : EnvLaws) {cs : List Lean.ConstantInfo}
    (hfresh : ∀ ci ∈ cs, fe.env.find? ci.name = none) (hnd : (cs.map (·.name)).Nodup)
    {n : Name} (hn : n ∉ cs.map (·.name)) :
    ({ fe with env := cs.foldl InLean.addConst fe.env } : InLean.FEnv).find? n = fe.find? n :=
  FEnv.find?_congr (fe := fe) (fe' := { fe with env := cs.foldl InLean.addConst fe.env }) rfl rfl
    ((find_foldl_addConst hlaws cs fe.env hfresh hnd).2 n hn)

/-- **A stored structure's table reads as before** a group of fresh names. -/
theorem findTable_foldl_old (hlaws : EnvLaws) (hcs : CtorsStored fe) {cs : List Lean.ConstantInfo}
    (hfresh : ∀ ci ∈ cs, fe.env.find? ci.name = none) (hnd : (cs.map (·.name)).Nodup)
    {T : Name} (hT : T ∉ cs.map (·.name)) :
    ({ fe with env := cs.foldl InLean.addConst fe.env } : InLean.FEnv).findTable? T =
      fe.findTable? T := by
  unfold InLean.FEnv.findTable?
  rw [feFind_foldl_out hlaws hfresh hnd hT]
  cases hTf : fe.find? T with
  | none => rfl
  | some ci =>
    cases ci with
    | inductInfo v =>
      show (if fe.isPending v.name = true then none else _) =
        (if fe.isPending v.name = true then none else _)
      cases hnp : fe.isPending v.name
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hv : v.ctors with
        | nil => rfl
        | cons c rest =>
          cases rest with
          | cons _ _ => rfl
          | nil =>
            have hc : c ∉ cs.map (·.name) := by
              intro hm
              obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hm
              obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hcs T v hTf hnp ci.name (by simp [hv]))
              have := FEnv.env_of_find hx
              rw [hfresh ci hci] at this; cases this
            simp only [feFind_foldl_out hlaws hfresh hnd hc]
      · rfl
    | _ => rfl

/-- **A stored structure's projections read as before** a group of fresh names. -/
theorem findProj_foldl_old (hlaws : EnvLaws) (hcs : CtorsStored fe) {cs : List Lean.ConstantInfo}
    (hfresh : ∀ ci ∈ cs, fe.env.find? ci.name = none) (hnd : (cs.map (·.name)).Nodup)
    {T : Name} (hT : T ∉ cs.map (·.name)) (i : Nat) :
    ({ fe with env := cs.foldl InLean.addConst fe.env } : InLean.FEnv).findProj? T i =
      fe.findProj? T i := by
  unfold InLean.FEnv.findProj?
  rw [findTable_foldl_old hlaws hcs hfresh hnd hT]

/-- **A group of fresh, distinct constants keeps the bodies' range**, given
the check on the extended environment at the group's own names. -/
theorem projBodiesInRange_group (hlaws : EnvLaws) (hR : ProjBodiesInRange fe) (hcs : CtorsStored fe)
    {cs : List Lean.ConstantInfo} (hfresh : ∀ ci ∈ cs, fe.env.find? ci.name = none)
    (hnd : (cs.map (·.name)).Nodup)
    (hchk : ∀ ci ∈ cs,
      ({ fe with env := cs.foldl InLean.addConst fe.env } : InLean.FEnv).projBodiesInRange ci.name = true) :
    ProjBodiesInRange { fe with env := cs.foldl InLean.addConst fe.env } := by
  intro T i e h b hb
  by_cases hT : T ∈ cs.map (·.name)
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hT
    exact (RangeOk_of_inRange (inRange_of_projBodiesInRange (hchk ci hci) h hb)).1
  · rw [findProj_foldl_old hlaws hcs hfresh hnd hT] at h
    exact hR T i e h b hb

/-- The check holds at a name whose constant is no former. -/
theorem projBodiesInRange_notInd {T : Name} (h : ∀ v, fe.find? T ≠ some (.inductInfo v)) :
    fe.projBodiesInRange T = true := by
  unfold InLean.FEnv.projBodiesInRange
  split
  · rename_i v hv; exact absurd hv (h v)
  · rfl

/-- **One fresh constant that is no former keeps the bodies' range** (every
step but an inductive block's). -/
theorem projBodiesInRange_one (hlaws : EnvLaws) (hR : ProjBodiesInRange fe) (hcs : CtorsStored fe)
    {ci : Lean.ConstantInfo} (hfresh : fe.env.find? ci.name = none) (hnotInd : ∀ v, ci ≠ .inductInfo v) :
    ProjBodiesInRange { fe with env := InLean.addConst fe.env ci } := by
  have h := projBodiesInRange_group (cs := [ci]) hlaws hR hcs (by simpa using hfresh) (by simp) ?_
  · exact h
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    apply projBodiesInRange_notInd
    intro v hv
    have hv' := FEnv.env_of_find hv
    have := (find_foldl_addConst hlaws [c] fe.env (by simpa using hfresh) (by simp)).1 c (by simp)
    rw [this, Option.some.injEq] at hv'
    exact hnotInd v hv'

/-! ## The generator's constants -/

/-- **A block constant is in the stored block.** -/
theorem mem_storedBlock {consts : Array Lean.ConstantInfo} {ci : Lean.ConstantInfo}
    (hci : ci ∈ consts.toList) (hb : isBlockConst ci = true) : ci ∈ storedBlock consts := by
  unfold storedBlock
  simp only [Array.toList_append, List.mem_append, Array.mem_toList_iff, Array.mem_filter]
  rw [Array.mem_toList_iff] at hci
  cases ci <;> simp_all [isBlockConst, Lean.ConstantInfo.isInductive, Lean.ConstantInfo.isCtor]

/-- `IndGroupPresBP`'s premise from the check. -/
theorem storedBlock_all {consts : Array Lean.ConstantInfo} (h : consts.all isBlockConst = true) :
    ∀ ci ∈ consts.toList, ci ∈ storedBlock consts := by
  intro ci hci
  rw [Array.all_eq_true_iff_forall_mem] at h
  exact mem_storedBlock hci (h ci (Array.mem_toList_iff.1 hci))

theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

theorem except_ok_bind {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

/-- **What an accepted inductive declaration says of its constants**: block
constants only, in range, closed, fresh in the environment and distinct, safe
when the block is, every projection body the extended environment reads at
their names in range, every body of the block's structures in range;
and a safe block's check accepted the stored block from the empty state (the
generator runs in a state of its own). -/
theorem checkInductiveC_ok {μ : CheckMode} {fe : InLean.FEnv} {lps : List Name} {nP : Nat}
    {types : List InductiveType} {u : Bool} {s s' : CState} {a : Added}
    (h : (checkInductiveC μ fe lps nP types u).run s = .ok (a, s')) :
    a.consts.all isBlockConst = true ∧ a.consts.all constInRange = true ∧
    a.consts.all constClosed = true ∧
    a.consts.all (fun ci => (fe.env.find? ci.name).isNone) = true ∧
    (u || a.consts.all safeConst) = true ∧
    a.consts.all (fun ci =>
      ({ fe with env := a.consts.foldl InLean.addConst fe.env } : InLean.FEnv).projBodiesInRange ci.name) =
      true ∧ projBodiesAllOk a.consts = true ∧
    namesNodup (a.consts.toList.map (·.name)) = true ∧ a.consts.all constGround = true ∧
    (u = false → (checkIndDeclC μ fe (storedBlock a.consts) nP).run {} = .ok ((), s')) := by
  unfold checkInductiveC at h
  generalize (((Ind.genInductive μ lps nP types u).run
    { env := fe.env, coreAxioms := fe.coreAxioms, limits := fe.limits }).run' {}).run' {} = g at h
  rw [StateT.run_bind, StateT.run_lift] at h
  cases g with
  | error e => cases h
  | ok gen =>
    rw [except_ok_bind, pure_bind] at h
    generalize checkUnsafeBlock μ fe gen.consts = X at h
    -- one guard at a time: a failed guard's branch closes at once
    cases u <;>
    cases h1 : gen.consts.all isBlockConst <;>
    (try simp only [h1, ↓reduceIte, Bool.false_eq_true, throw, throwThe, MonadExceptOf.throw,
      StateT.run_bind, StateT.run_lift, Function.comp, except_error_bind, reduceCtorEq] at h) <;>
    cases h2 : gen.consts.all constInRange <;>
    (try simp only [h2, ↓reduceIte, Bool.false_eq_true,
      StateT.run_bind, StateT.run_lift, except_error_bind, reduceCtorEq] at h) <;>
    cases h7 : gen.consts.all constClosed <;>
    (try simp only [h7, ↓reduceIte, Bool.false_eq_true,
      StateT.run_bind, StateT.run_lift, except_error_bind, reduceCtorEq] at h) <;>
    cases h9 : gen.consts.all constGround <;>
    (try simp only [h9, ↓reduceIte, Bool.false_eq_true,
      StateT.run_bind, StateT.run_lift, except_error_bind, reduceCtorEq] at h) <;>
    cases h4 : gen.consts.all (fun ci => (fe.env.find? ci.name).isNone) <;>
    (try simp only [h4, ↓reduceIte, Bool.false_eq_true,
      StateT.run_bind, StateT.run_lift, except_error_bind, reduceCtorEq] at h) <;>
    cases h8 : namesNodup (gen.consts.toList.map (·.name)) <;>
    (try simp only [h8, ↓reduceIte, Bool.false_eq_true,
      StateT.run_bind, StateT.run_lift, except_error_bind, reduceCtorEq] at h) <;>
    cases h5 : gen.consts.all safeConst <;>
    (try simp only [h5, Bool.or_false, Bool.or_true, ↓reduceIte, Bool.false_eq_true,
      StateT.run_bind, StateT.run_lift, except_error_bind, reduceCtorEq] at h) <;>
    cases h3 : gen.consts.all (fun ci =>
      ({ fe with env := gen.consts.foldl InLean.addConst fe.env } : InLean.FEnv).projBodiesInRange
        ci.name) <;>
    (try simp only [h3, ↓reduceIte, Bool.false_eq_true,
      StateT.run_bind, StateT.run_lift, except_error_bind, reduceCtorEq] at h) <;>
    cases h6 : projBodiesAllOk gen.consts <;>
    (try simp only [h6, ↓reduceIte, Bool.false_eq_true,
      StateT.run_bind, StateT.run_lift, except_error_bind, reduceCtorEq] at h)
    all_goals
      rw [show StateT.run (set ({} : CState) : CheckCM Unit) s = Except.ok ((), {}) from rfl,
        except_ok_bind] at h
    · split at h
      · rw [StateT.run_bind] at h
        cases hy : (checkIndDeclC μ fe (storedBlock gen.consts) nP).run {} with
        | error e => rw [hy, except_error_bind] at h; cases h
        | ok q =>
          rw [hy, except_ok_bind] at h
          obtain ⟨⟨⟩, q2⟩ := q
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
          exact ⟨h1, h2, h7, h4, by simp [h5], h3, h6, h8, h9, fun _ => hy⟩
      · simp only [StateT.run_bind, StateT.run_lift, except_error_bind, reduceCtorEq] at h
    all_goals
      cases hx : StateT.run X ((), ({} : CState)).snd with
      | error e => rw [hx, except_error_bind] at h; cases h
      | ok q =>
        rw [hx, except_ok_bind] at h
        obtain rfl := (Prod.mk.inj (Except.ok.inj h)).1
        exact ⟨h1, h2, h7, h4, by simp, h3, h6, h8, h9, nofun⟩

/-- **An accepted inductive declaration keeps the bodies' range** (its
constants fresh and distinct, as P4 has them). -/
theorem projBodiesInRange_ind (hlaws : EnvLaws) (hR : ProjBodiesInRange fe) (hcs : CtorsStored fe)
    {μ : CheckMode} {lps : List Name} {nP : Nat} {types : List InductiveType} {u : Bool}
    {s s' : CState} {a : Added} (h : (checkInductiveC μ fe lps nP types u).run s = .ok (a, s'))
    (hfresh : ∀ ci ∈ a.consts.toList, fe.env.find? ci.name = none)
    (hnd : (a.consts.toList.map (·.name)).Nodup) :
    ProjBodiesInRange { fe with env := a.consts.foldl InLean.addConst fe.env } := by
  obtain ⟨-, -, -, -, -, h3, -, -, -, -⟩ := checkInductiveC_ok h
  rw [← Array.foldl_toList] at h3 ⊢
  refine projBodiesInRange_group hlaws hR hcs hfresh hnd ?_
  intro ci hci
  rw [Array.all_eq_true_iff_forall_mem] at h3
  exact h3 ci (Array.mem_toList_iff.1 hci)

/-- **`IndGroupPresBP`'s projection-bodies premise from an accepted inductive
declaration.** -/
theorem projBodiesAllOk_of_checkInductiveC {μ : CheckMode} {lps : List Name} {nP : Nat}
    {types : List InductiveType} {u : Bool} {s s' : CState} {a : Added}
    (h : (checkInductiveC μ fe lps nP types u).run s = .ok (a, s')) :
    projBodiesAllOk a.consts = true :=
  (checkInductiveC_ok h).2.2.2.2.2.2.1

/-- **`IndGroupPresBP`'s block premise from an accepted inductive declaration.** -/
theorem storedBlock_of_checkInductiveC {μ : CheckMode} {lps : List Name} {nP : Nat}
    {types : List InductiveType} {u : Bool} {s s' : CState} {a : Added}
    (h : (checkInductiveC μ fe lps nP types u).run s = .ok (a, s')) :
    ∀ ci ∈ a.consts.toList, ci ∈ storedBlock a.consts :=
  storedBlock_all (checkInductiveC_ok h).1

/-- **`IndGroupPresBP`'s freshness premise from an accepted inductive
declaration**: its constants' names are fresh in Lean's environment. -/
theorem fresh_of_checkInductiveC {μ : CheckMode} {lps : List Name} {nP : Nat}
    {types : List InductiveType} {u : Bool} {s s' : CState} {a : Added}
    (h : (checkInductiveC μ fe lps nP types u).run s = .ok (a, s')) :
    ∀ ci ∈ a.consts.toList, fe.env.find? ci.name = none := by
  intro ci hci
  have h3 := (checkInductiveC_ok h).2.2.2.1
  rw [Array.all_eq_true_iff_forall_mem] at h3
  simpa using h3 ci (Array.mem_toList_iff.1 hci)

/-- **The block's terms closed, from an accepted inductive declaration**
(`checkIndDeclC_sim`'s `CIClosed` premise). -/
theorem closed_of_checkInductiveC {μ : CheckMode} {lps : List Name} {nP : Nat}
    {types : List InductiveType} {u : Bool} {s s' : CState} {a : Added}
    (h : (checkInductiveC μ fe lps nP types u).run s = .ok (a, s')) :
    ∀ ci ∈ a.consts.toList, CIClosed ci := by
  intro ci hci
  have h3 := (checkInductiveC_ok h).2.2.1
  rw [Array.all_eq_true_iff_forall_mem] at h3
  exact CIClosed_of_constClosed (h3 ci (Array.mem_toList_iff.1 hci))

/-- **`IndGroupPresBP`'s visibility premise from an accepted safe inductive
declaration**: its constants are safe, so a check sees each one whose name
is not `sorryAx` (which `InLean.checkDecl` refuses at con-leche's policy,
`sorryAxSquat`). -/
theorem sees_of_checkInductiveC {μ : CheckMode} {lps : List Name} {nP : Nat}
    {types : List InductiveType} {s s' : CState} {a : Added}
    (h : (checkInductiveC μ fe lps nP types false).run s = .ok (a, s'))
    (hsorry : ∀ ci ∈ a.consts.toList, ci.name ≠ InLean.sorryAxName) :
    ∀ ci ∈ a.consts.toList, fe.sees ci.name ci = true := by
  intro ci hci
  have h4 := (checkInductiveC_ok h).2.2.2.2.1
  simp only [Bool.false_or, Array.all_eq_true_iff_forall_mem] at h4
  exact sees_safe (h4 ci (Array.mem_toList_iff.1 hci)) fun hn => absurd hn (hsorry ci hci)

/-! ## `Quot.sound` -/

/-- **What an accepted `Quot.sound` says**: the pin hit at the axiom's own
level name, the name fresh, the axiom added. -/
theorem checkAxiomC_quotSound {μ : CheckMode} {cfg : Config} {v : AxiomVal} {s s' : CState}
    {a : Added} (h : (checkAxiomC μ cfg fe v).run s = .ok (a, s'))
    (hn : v.name = InLean.quotSoundName) :
    a.consts = #[.axiomInfo v] ∧ quotSoundHit v.name v.levelParams v.type = true ∧
      fe.env.find? v.name = none := by
  unfold checkAxiomC at h
  have hn' : (v.name == InLean.quotSoundName) = true := by simp [hn]
  simp only [hn', ↓reduceIte] at h
  cases h1 : quotSoundHit v.name v.levelParams v.type <;>
  cases h2 : (quotPredsOk fe && (fe.find? quotName).isSome && (fe.find? quotMkName).isSome) <;>
  cases h3 : fe.env.find? v.name <;>
  simp [h1, h2, h3, StateT.run, bind, StateT.bind, pure, StateT.pure, throw, throwThe,
    MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure] at h
  exact ⟨by rw [← h.1], rfl, rfl⟩

/-- **The `Quot.sound` step keeps the relation**: InLean's pin hit at the
axiom's level name makes the axiom con-leche's `quotAt .sound` at its record. -/
theorem presI_quotSound (hlaws : EnvLaws) (hP : EnvPresI fe L) {v : AxiomVal}
    {d : ConLeche.Declaration} (hd : toDecl [.axiomInfo v] = some d)
    (hfresh : fe.env.find? v.name = none) (hr : Expr.RangeOk v.type)
    (hsafe : v.isUnsafe = false)
    (hhit : quotSoundHit v.name v.levelParams v.type = true) :
    EnvPresI { fe with env := InLean.addConst fe.env (.axiomInfo v) }
      (L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d)) := by
  simp only [toDecl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hd
  obtain ⟨cv, hcv, rfl⟩ := hd
  have hrel := CVRel_of_toCV hcv hr
  unfold quotSoundHit at hhit
  simp only [Bool.and_eq_true, beq_iff_eq] at hhit
  obtain ⟨⟨hn, hlen⟩, hcl⟩ := hhit
  obtain ⟨lp, hlp⟩ : ∃ lp, v.levelParams = [lp] := by
    match hv : v.levelParams, hlen with
    | [lp], _ => exact ⟨lp, rfl⟩
  have hname : cv.name = ConLeche.quotSoundName := by
    rw [hrel.1, ← toName_quotSoundName]; exact congrArg toName hn
  simp only [ConLeche.declConstants, ConLeche.declTables, hname, ↓reduceIte]
  -- the pin's reading at the axiom's level name
  rw [hlp] at hcl
  have hst := storedT_instantiateLevelParams quotSoundPin.lps (R := quotSoundPin.type)
    (us := [.param lp]) (by decide) (by decide) (by decide) rfl rfl
    (by simp [depthS]) (by simp only [maxDepthS, List.foldr, depthS]; decide)
  have hty : toExprC v.type = toExprC (EO.instantiateLevelParams quotSoundPin.type quotSoundPin.lps
      [.param lp]) := toExpr_of_clEq _ hcl
  have hcvT : cv.type = (ConLeche.quotSoundA.toConstantVal.atLps cv.levelParams).type := by
    have h1 := hrel.2.2.2.2
    rw [hty, hst.2.2, Option.some.injEq] at h1
    rw [← h1, hrel.2.1, hlp]
    rfl
  have hq : ConLeche.quotAt .sound cv =
      .axiomInfo (ConLeche.quotSoundA.toConstantVal.atLps cv.levelParams) := rfl
  have hnm : ConLeche.quotSoundName = toName v.name := by rw [← toName_quotSoundName, hn]
  refine presI_one (ci := .axiomInfo v) hlaws hP hfresh (fun _ h => by cases h)
    (.inr ⟨_, rfl, by rw [hq]; exact hnm, ?_, ?_⟩)
  · rw [hq]
    refine ⟨hnm, hrel.2.1, ?_⟩
    rw [← hcvT]; exact hrel.2.2
  · refine sees_safe (by simp [InLean.safeConst, Lean.ConstantInfo.isUnsafe, hsafe]) fun hs => ?_
    have : v.name = InLean.sorryAxName := hs
    rw [hn] at this; exact absurd (congrArg toName this) (by decide)

/-! ## The inductive check's branches -/

/-- A program ending in a throw is never accepted. -/
theorem run_bind_throw {β α : Type} {x : CheckCM β} {s : CState} {r : α × CState} (e : CheckError)
    (f : β → CheckCM α) (hf : ∀ b, f b = throw e) : (x >>= f).run s ≠ .ok r := by
  intro h
  rw [StateT.run_bind] at h
  cases hx : x.run s with
  | error e' => rw [hx, except_error_bind] at h; cases h
  | ok q =>
    rw [hx, except_ok_bind, hf] at h
    simp only [throw, throwThe, MonadExceptOf.throw, StateT.run_lift, Function.comp,
      except_error_bind, reduceCtorEq] at h

/-- **What an accepted inductive check says**: a recognised block whose
generated entries agree with its shape and whose block check passed (a pinned
basis block included).  A block that cannot be read and a parameter mismatch throw. -/
theorem checkIndDeclC_ok {μ : CheckMode} {block : List Lean.ConstantInfo} {nP : Nat}
    {s s' : CState} (h : (checkIndDeclC μ fe block nP).run s = .ok ((), s')) :
    indParamsOk nP block = true ∧
      ∃ p, InLean.readBlock nP block = .ok p ∧ ∃ s₁,
        (genEntriesAgree p block).run s = .ok ((), s₁) ∧
        (checkBlockKS μ fe block p).run s₁ = .ok ((), s') := by
  unfold checkIndDeclC at h
  cases hpo : indParamsOk nP block
  · simp [hpo, StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map, Except.map] at h
  · simp only [hpo, ↓reduceIte] at h
    refine ⟨rfl, ?_⟩
    cases hs : InLean.readBlock nP block with
    | error e =>
      rw [hs] at h
      simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map,
        Except.map] at h
    | ok p =>
      rw [hs] at h
      simp only at h
      rw [StateT.run_bind] at h
      refine ⟨p, rfl, ?_⟩
      cases hg : (genEntriesAgree p block).run s with
      | error e => rw [hg, except_error_bind] at h; cases h
      | ok q =>
        obtain ⟨⟨⟩, s₁⟩ := q
        rw [hg, except_ok_bind] at h
        exact ⟨s₁, rfl, h⟩

/-! ## The pinned names through the translation -/

/-- InLean's pinned kinds as con-leche's. -/
theorem toBlockRecord_name {c : Lean.ConstantInfo} {r : ConLeche.ConstantInfo}
    (h : toBlockRecord c = some r) : r.name = toName c.name := by
  cases c <;> simp only [toBlockRecord, toCV, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, reduceCtorEq] at h
  all_goals first
    | (obtain ⟨cv, ⟨t, -, rfl⟩, rfl⟩ := h; rfl)
    | (obtain ⟨cv, ⟨t, -, rfl⟩, rs, -, rfl⟩ := h; rfl)

theorem toBlock_names : ∀ {block : List Lean.ConstantInfo} {cb : List ConLeche.ConstantInfo},
    toBlock block = some cb → cb.map (·.name) = (block.map (·.name)).map toName
  | [], cb, h => by simp only [toBlock, Option.some.injEq] at h; subst h; rfl
  | c :: cs, cb, h => by
    simp only [toBlock, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs, hrs, rfl⟩ := h
    simp only [List.map_cons, toBlockRecord_name hr, toBlock_names hrs]

/-- **The pinned names agree**: con-leche's `basisNameHit` on the
translated block is InLean's, kind by kind. -/
theorem basisNameHit_toBlock {block : List Lean.ConstantInfo} {cb : List ConLeche.ConstantInfo}
    (h : toBlock block = some cb) :
    ConLeche.basisNameHit cb = (InLean.basisNameHit block).map trKind := by
  have hn := toBlock_names h
  have key : ∀ k, ((ConLeche.BasisKind.decls (trKind k)).map (·.name) == cb.map (·.name)) =
      (k.decls.map (·.name) == block.map (·.name)) := by
    intro k; rw [decls_names_tr, hn, map_toName_beq]
  unfold ConLeche.basisNameHit InLean.basisNameHit
  have e := key .eqK; have n := key .natK; have em := key .emptyK; have f := key .falseK
  simp only [trKind] at e n em f
  simp only [List.find?_cons, List.find?_nil, e, n, em, f]
  generalize (InLean.BasisKind.eqK.decls.map (·.name) == block.map (·.name)) = b1
  generalize (InLean.BasisKind.natK.decls.map (·.name) == block.map (·.name)) = b2
  generalize (InLean.BasisKind.emptyK.decls.map (·.name) == block.map (·.name)) = b3
  generalize (InLean.BasisKind.falseK.decls.map (·.name) == block.map (·.name)) = b4
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl

end InLeanProof
