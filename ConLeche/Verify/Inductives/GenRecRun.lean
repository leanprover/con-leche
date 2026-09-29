module

import ConLeche.Kernel.Inductives.BlockTail
public import ConLeche.Verify.Inductives.RecCheckRun
public import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.CheckerF
import ConLeche.Verify.InferProjSlots

public section

/-!
# The GENERATED recursor stage's RUN RECORDS

ONE inversion per stage of the generated recursor stage
(`ConLeche/Kernel/Inductives/GenRec.lean`, `genRecCheck`), each returning
a record with NAMED fields.  Every proof about the stage reads these
records and never unfolds a stage.

| stage | kernel function | record / inversion |
|---|---|---|
| the stream's recursor types | `classStreamRecs` | `classStreamRecs_run` |
| the classes as majors | `classMajors` | `classMajors_run` |
| the classes' table entries | `classesNfs` | `classesNfs_run` |
| one constructor's datum, `ih`s, node agreement | `classCtorOf` | `ClassCtorRun` / `classCtorOf_run` |
| every class's constructors | `classesCtors` | `classesCtors_run` |
| one recursor's generated type | `classRecTyOk` | `ClassRecTyRun` / `classRecTyOk_run` |
| every recursor's generated type | `classRecTysOk` | `classRecTysOk_run` |
| one generated rule | `classRuleOk` | `ClassRuleRun` / `classRuleOk_run` |
| every generated rule | `classRecsRulesOk` | `classRecsRulesOk_run` |
| the classes, in the pass | `checkBlockClasses` | `ClassesRun` / `checkBlockClasses_run` |
| the whole stage | `genRecCheck` | `GenStageRun` / `genRecCheck_run` |
| the stage with the pass's classes and walk | — | `GenRecRun` / `genRecRun_of` |

The records are stated at the fueled pure instantiation
(`ShadowOps.fueled mode F`).  What the UNVERIFIED pre-pass returned
(`ClassRead`) appears as data only: nothing is proved about how it was
read.
-/

namespace ConLeche

variable {mode : CheckMode}

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

/-! ## Guards -/

/-! ## The stream's recursor types -/

/-- **`classStreamRecs`, inverted**: every stream recursor constant,
checked. -/
theorem classStreamRecs_run {fe : FEnv} {F : Nat} :
    ∀ {recs : List RecShape} {cvs : List ConstantVal},
      classStreamRecs (fueledOps mode F) fe recs = .ok cvs →
      cvs.length = recs.length ∧
      ∀ (i : Nat) (rc : RecShape), recs[i]? = some rc →
        ∃ cv, cvs[i]? = some cv ∧ checkConstantValF (fueledOps mode F) fe rc.cvR = .ok cv
  | [], cvs, h => by
    simp only [classStreamRecs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i rc hi => nomatch hi⟩
  | rc :: rcs, cvs, h => by
    unfold classStreamRecs at h
    obtain ⟨cv, hcv, h⟩ := exceptBind_ok h
    obtain ⟨cvs', hcvs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := classStreamRecs_run hcvs
    refine ⟨by simp [hlen], fun i rc' hi => ?_⟩
    cases i with
    | zero =>
      obtain rfl : rc = rc' := by simpa using hi
      exact ⟨cv, rfl, hcv⟩
    | succ i => simpa using hall i rc' (by simpa using hi)

/-! ## The classes -/

/-- **One class, checked as a major**: `targetMajorOf`'s arm at the
class key's application. -/
structure ClassMajorRun (mode : CheckMode) (F : Nat) (fe : FEnv) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs : List Expr) (key : ClassKey)
    (M : TargetMajor) : Type where
  major : TargetMajorRun fe p ctorsAs pfvs pfvs (Expr.mkAppN (.const key.ind key.lvls) key.ds) M
  hmaj : targetMajorOf (m := CheckM) fe p ctorsAs pfvs pfvs
    (Expr.mkAppN (.const key.ind key.lvls) key.ds) = .ok M

/-- **`classMajors`, inverted**: one checked major per class key. -/
theorem classMajors_run {fe : FEnv} {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs : List Expr} {F : Nat} :
    ∀ {keys : List ClassKey} {Ms : List TargetMajor},
      classMajors (fueledOps mode F) fe p ctorsAs pfvs keys = .ok Ms →
      Ms.length = keys.length ∧
      ∀ (i : Nat) (key : ClassKey), keys[i]? = some key →
        ∃ M, Ms[i]? = some M ∧ Nonempty (ClassMajorRun mode F fe p ctorsAs pfvs key M)
  | [], Ms, h => by
    simp only [classMajors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i key hi => nomatch hi⟩
  | key :: keys, Ms, h => by
    unfold classMajors at h
    obtain ⟨M, hM, h⟩ := exceptBind_ok h
    obtain ⟨u, -, h⟩ := exceptBind_ok h
    obtain ⟨Ms', hMs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := classMajors_run hMs
    refine ⟨by simp [hlen], fun i key' hi => ?_⟩
    cases i with
    | zero =>
      obtain rfl : key = key' := by simpa using hi
      obtain ⟨⟨R⟩, -⟩ := targetMajorOf_run hM
      exact ⟨M, rfl, ⟨⟨R, hM⟩⟩⟩
    | succ i => simpa using hall i key' (by simpa using hi)

/-- **The class check moves between environments** that agree on every
stored inductive of the first: its lookup and its constructor reading
(`targetMajorOf` reads the environment nowhere else). -/
@[expose] def ClassEnvAgree (p : BlockShape) (fe₁ fe : FEnv) : Prop :=
  ∀ I cv caps, I ∉ p.memberNames → fe₁.find? I = some (.indInfo cv caps) →
    fe.find? I = fe₁.find? I ∧ targetCtorsOf fe I = targetCtorsOf fe₁ I

theorem targetOutsideInst_congr {fe fe' : FEnv} {I : Name} (h : fe.find? I = fe'.find? I)
    (us : List Level) (ds : List Expr) :
    targetOutsideInst (m := CheckM) fe I us ds = targetOutsideInst (m := CheckM) fe' I us ds := by
  unfold targetOutsideInst
  rw [h]

theorem targetCtorsOf_indInfo {fe : FEnv} {I : Name} {q : Nat × List (ConstantVal × Nat)}
    (h : targetCtorsOf fe I = some q) : ∃ cv caps, fe.find? I = some (.indInfo cv caps) := by
  unfold targetCtorsOf nestContainer at h
  dsimp only at h
  split at h
  · rename_i cv caps hf
    exact ⟨cv, caps, hf⟩
  · exact nomatch h

/-- **`targetMajorOf` moved between agreeing environments.** -/
theorem targetMajorOf_transport {fe₁ fe : FEnv} {p : BlockShape} (hag : ClassEnvAgree p fe₁ fe)
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs fvs : List Expr} {mty : Expr}
    {M : TargetMajor}
    (h : targetMajorOf (m := CheckM) fe₁ p ctorsAs pfvs fvs mty = .ok M) :
    targetMajorOf (m := CheckM) fe p ctorsAs pfvs fvs mty = .ok M := by
  obtain ⟨⟨R⟩, hpf⟩ := targetMajorOf_run h
  cases R with
  | member I t ms ctorsA hfn ht hms hctors hpar nfs =>
    unfold targetMajorOf at h ⊢
    rw [hfn] at h ⊢
    simp only [ht] at h ⊢
    exact h
  | outside I us nPc nIdx ctors sI hfn ht hnq hct hdsLen hdsSc hment hinst hsort nfs =>
    obtain ⟨cv, caps, hf⟩ := targetCtorsOf_indInfo hct
    have hI : I ∉ p.memberNames := fun hm => by
      have := List.findIdx?_eq_none_iff.mp ht I hm
      simp at this
    obtain ⟨hfind, hctors⟩ := hag I cv caps hI hf
    have hct' : targetCtorsOf fe I = some (nPc, ctors) := by rw [hctors, hct]
    have hinst' := (targetOutsideInst_congr hfind us _).trans hinst
    unfold targetMajorOf at h ⊢
    rw [hfn] at h ⊢
    simp only [ht] at h ⊢
    have hq : (I == quotName) = false := by simpa using hnq
    simp only [hq, hct, hct', Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [hinst] at h
    rw [hinst']
    exact h

/-- A class checked as a major, moved between agreeing environments. -/
theorem ClassMajorRun.transport {fe₁ fe : FEnv} {p : BlockShape} (hag : ClassEnvAgree p fe₁ fe)
    {F : Nat} {ctorsAs : List (List (ConstantVal × Nat))} {pfvs : List Expr}
    {key : ClassKey} {M : TargetMajor} (C : ClassMajorRun mode F fe₁ p ctorsAs pfvs key M) :
    Nonempty (ClassMajorRun mode F fe p ctorsAs pfvs key M) := by
  have h := targetMajorOf_transport hag C.hmaj
  obtain ⟨⟨R⟩, -⟩ := targetMajorOf_run h
  exact ⟨⟨R, h⟩⟩

/-! ## The class keys and the classes, in the pass -/

/-- **`classKeyOf`, inverted**: the key moved to the canonical
parameters, every parameter closed below them, and annotated at depth
`nP`. -/
theorem classKeyOf_run {env : Env} {nP : Nat} {params : List Expr} {k k' : ClassKey}
    {F : Nat} (h : classKeyOf (fueledOps mode F) env nP params k = .ok k') :
    k'.ind = k.ind ∧ k'.lvls = k.lvls ∧
    (∀ x ∈ (classKeyCanon params k).ds, x.bvarB = 0 ∧ x.fvarB ≤ nP) ∧
    (classKeyCanon params k).ds.mapM ((fueledOps mode F).annotate env nP) = .ok k'.ds := by
  unfold classKeyOf at h
  simp only at h
  by_cases hg : ((classKeyCanon params k).ds.all fun x => x.bvarB == 0 && x.fvarB ≤ nP) = true
  case neg => rw [if_neg hg] at h; close_throw h
  rw [if_pos hg] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨ds, hds, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨rfl, rfl, fun x hx => ?_, hds⟩
  have := List.all_eq_true.mp hg x hx
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact this

/-- **The classes, read and checked** (`checkBlockClasses`, in the pass):
the pre-pass's reading `rd` of the stream's raw recursor types, the keys
made checkable `keys`, the classes `Ms` checked as majors at `fe₁`, one
per member. -/
structure ClassesRun (mode : CheckMode) (F : Nat) (fe₁ : FEnv) (env₁ : Env) (p : BlockShape)
    (params : List Expr) (ctorsAs : List (List (ConstantVal × Nat))) (rd : ClassRead)
    (Ms : List TargetMajor) : Type where
  keys : List ClassKey
  hrd : classRead p.nP (classNPcOf p fe₁) p.recs = some rd
  hkeys : rd.classes.mapM (classKeyOf (fueledOps mode F) env₁ p.nP params) = .ok keys
  hMs : classMajors (fueledOps mode F) fe₁ p ctorsAs params keys = .ok Ms
  hone : ∀ t, t < p.k → (Ms.filter (·.member == some t)).length = 1

theorem checkBlockClasses_run {fe₁ : FEnv} {env₁ : Env} {p : BlockShape} {params : List Expr}
    {ctorsAs : List (List (ConstantVal × Nat))} {rd : ClassRead} {Ms : List TargetMajor}
    {F : Nat}
    (h : checkBlockClasses (fueledOps mode F) fe₁ env₁ p params ctorsAs = .ok (rd, Ms)) :
    Nonempty (ClassesRun mode F fe₁ env₁ p params ctorsAs rd Ms) := by
  unfold checkBlockClasses at h
  obtain ⟨rd', hrd, h⟩ := exceptBind_ok h
  obtain ⟨keys, hkeys, h⟩ := exceptBind_ok h
  obtain ⟨Ms', hMs, h⟩ := exceptBind_ok h
  by_cases hone : ((List.range p.k).all fun t =>
      (Ms'.filter (·.member == some t)).length == 1) = true
  case neg => rw [if_neg hone] at h; close_throw h
  rw [if_pos hone] at h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hone
  exact ⟨⟨keys, unwrapOr_ok hrd, hkeys, hMs, hone⟩⟩

theorem mapM_ok_length {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → l'.length = l.length
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, -, h⟩ := exceptBind_ok h
    obtain ⟨bs, hbs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [mapM_ok_length hbs]

theorem mapM_ok_getElem? {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' →
      ∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, l'[i]? = some b ∧ f a = .ok b
  | [], _, _, _, _, hi => nomatch hi
  | a :: l, l', h, i, a', hi => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    obtain ⟨bs, hbs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases i with
    | zero =>
      obtain rfl : a = a' := by simpa using hi
      exact ⟨b, rfl, hb⟩
    | succ i => simpa using mapM_ok_getElem? hbs i a' (by simpa using hi)

/-- **`classesNfs`, inverted**: the same classes, each with its table
entries (`targetMajorNfs`). -/
theorem classesNfs_run {env : Env} {p : BlockShape} {formerTys : List Expr}
    {tbl : List NestCtorNf} {F : Nat} :
    ∀ {Ms₀ Ms : List TargetMajor},
      classesNfs (fueledOps mode F) env p formerTys tbl Ms₀ = .ok Ms →
      Ms.length = Ms₀.length ∧
      ∀ (i : Nat) (M₀ : TargetMajor), Ms₀[i]? = some M₀ →
        ∃ nfs, Ms[i]? = some { M₀ with nfs := nfs } ∧
          targetMajorNfs (fueledOps mode F) env p formerTys M₀.pfvs M₀.lvls M₀.ds M₀.ctors tbl
            = .ok nfs
  | [], Ms, h => by
    simp only [classesNfs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i M₀ hi => nomatch hi⟩
  | M :: Ms₀, Ms, h => by
    unfold classesNfs at h
    obtain ⟨es, hes, h⟩ := exceptBind_ok h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := classesNfs_run hrest
    refine ⟨by simp [hlen], fun i M₀ hi => ?_⟩
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      exact ⟨es, rfl, hes⟩
    | succ i => simpa using hall i M₀ (by simpa using hi)

/-! ## One class's constructors -/

/-- **One constructor of class `c`, as `classCtorOf` ran**: its entries
`E` in the class's table, the first the datum `e0`; the minor premise's
slot `s` and `ih`s; the datum's opened fields; the generator's kinds
(`classFieldsOf`); node agreement at every entry (`classFieldsAgree`). -/
structure ClassCtorRun (mode : CheckMode) (F : Nat) (env : Env) (p : BlockShape)
    (formerTys : List Expr) (rd : ClassRead) (Ms : List TargetMajor) (c : Nat)
    (cA : ConstantVal × Nat) (x : ClassCtor) : Type where
  E : List NestCtorNf
  e0 : NestCtorNf
  s : Nat
  ihs : List (Nat × Nat)
  fvs : List Expr
  o : Expr
  hE : E = (Ms.getD c default).nfs.filter (·.ctor == cA.1.name)
  he0 : E.head? = some e0
  hslot : classMinorSlot (m := CheckM) rd c cA.1.name = .ok (s, ihs)
  hopen : openPisAtFvars cA.2 e0.ty (p.nP + p.k) = some (fvs, o)
  hkinds : classFieldsOf (m := CheckM) p cA.1.name ihs 0 fvs = .ok x.kinds
  hna : classFieldsAgree (fueledOps mode F) env p formerTys Ms fvs cA.1.name E 0 x.kinds = .ok ()
  hD : instPisWith (Ms.getD c default).ds (targetCtorAt (Ms.getD c default) cA.1) = some x.tyD
  hx : x = ⟨cA.1, cA.2, x.kinds, x.tyD, e0.ty⟩

/-- **`classCtorOf`, inverted.** -/
theorem classCtorOf_run {env : Env} {p : BlockShape} {formerTys : List Expr} {rd : ClassRead}
    {Ms : List TargetMajor} {c : Nat} {cA : ConstantVal × Nat} {x : ClassCtor} {F : Nat}
    (h : classCtorOf (fueledOps mode F) env p formerTys rd Ms c cA = .ok x) :
    Nonempty (ClassCtorRun mode F env p formerTys rd Ms c cA x) := by
  unfold classCtorOf at h
  obtain ⟨e0, he0, h⟩ := exceptBind_ok h
  obtain ⟨⟨s, ihs⟩, hslot, h⟩ := exceptBind_ok h
  obtain ⟨⟨fvs, o⟩, hopen, h⟩ := exceptBind_ok h
  simp only at h
  obtain ⟨kinds, hkinds, h⟩ := exceptBind_ok h
  obtain ⟨u', hna, h⟩ := exceptBind_ok h
  obtain ⟨tyD, hD, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨{
    E := _, e0 := e0, s := s, ihs := ihs, fvs := fvs, o := o, hE := rfl,
    he0 := unwrapOr_ok he0, hslot := hslot, hopen := unwrapOr_ok hopen,
    hkinds := hkinds,
    hna := by cases u'; exact hna, hD := unwrapOr_ok hD, hx := rfl }⟩

/-- **`classCtorsOf`, inverted**: one run per constructor of the class. -/
theorem classCtorsOf_run {env : Env} {p : BlockShape} {formerTys : List Expr} {rd : ClassRead}
    {Ms : List TargetMajor} {c : Nat} {F : Nat} :
    ∀ {cs : List (ConstantVal × Nat)} {xs : List ClassCtor},
      classCtorsOf (fueledOps mode F) env p formerTys rd Ms c cs = .ok xs →
      xs.length = cs.length ∧
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ x, xs[j]? = some x ∧ Nonempty (ClassCtorRun mode F env p formerTys rd Ms c cA x)
  | [], xs, h => by
    simp only [classCtorsOf, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun j cA hj => nomatch hj⟩
  | cA :: cs, xs, h => by
    unfold classCtorsOf at h
    obtain ⟨x, hx, h⟩ := exceptBind_ok h
    obtain ⟨xs', hxs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := classCtorsOf_run hxs
    refine ⟨by simp [hlen], fun j cA' hj => ?_⟩
    cases j with
    | zero =>
      obtain rfl : cA = cA' := by simpa using hj
      exact ⟨x, rfl, classCtorOf_run hx⟩
    | succ j => simpa using hall j cA' (by simpa using hj)

/-- **`classesCtors`, inverted**: per class (from `c₀` on) its
constructors, one run each. -/
theorem classesCtors_run {env : Env} {p : BlockShape} {formerTys : List Expr} {rd : ClassRead}
    {Ms : List TargetMajor} {F : Nat} :
    ∀ {c₀ : Nat} {Ms' : List TargetMajor} {xss : List (List ClassCtor)},
      classesCtors (fueledOps mode F) env p formerTys rd Ms c₀ Ms' = .ok xss →
      xss.length = Ms'.length ∧
      ∀ (i : Nat) (M : TargetMajor), Ms'[i]? = some M →
        ∃ xs, xss[i]? = some xs ∧
          classCtorsOf (fueledOps mode F) env p formerTys rd Ms (c₀ + i) M.ctors = .ok xs
  | _, [], xss, h => by
    simp only [classesCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i M hi => nomatch hi⟩
  | c₀, M :: Ms', xss, h => by
    unfold classesCtors at h
    obtain ⟨xs, hxs, h⟩ := exceptBind_ok h
    obtain ⟨xss', hxss, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := classesCtors_run hxss
    refine ⟨by simp [hlen], fun i M' hi => ?_⟩
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      exact ⟨xs, rfl, by simpa using hxs⟩
    | succ i =>
      obtain ⟨xs', h1, h2⟩ := hall i M' (by simpa using hi)
      exact ⟨xs', by simpa using h1, by rw [show c₀ + (i + 1) = c₀ + 1 + i by omega]; exact h2⟩

/-! ## The generated types -/

/-- **`classConstOk`, inverted** (at `mkFEnv env`) — `checkConstantVal_inv`
without the annotation step: the guards, and the inference of the type
AS STORED (the returned constant is the input). -/
theorem classConstOk_inv {env : Env} {cv cv' : ConstantVal} {F : Nat}
    (h : classConstOk (fueledOps mode F) (mkFEnv env) cv = .ok cv') :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    cv.name.isProjFnShape = false ∧
    Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    cv.type.allLevelParamsDefined cv.levelParams = true ∧
    cv.type.constsResolve env = true ∧
    ∃ stype u,
      inferTypeCore mode env F 0 cv.type = .ok stype ∧
      ensureSortCore mode env F 0 stype = .ok u ∧
      cv' = cv := by
  unfold classConstOk at h
  simp only [mkFEnv_find?, constsResolveF_eq, mkFEnv_env] at h
  by_cases hfind : (env.find? cv.name).isSome = true
  case pos => rw [if_pos hfind] at h; close_throw h
  rw [if_neg hfind] at h
  by_cases hres : reservedBasisNames.contains cv.name = true
  case pos => rw [if_pos hres] at h; close_throw h
  rw [if_neg hres] at h
  by_cases hpsh : cv.name.isProjFnShape = true
  case pos => rw [if_pos hpsh] at h; close_throw h
  rw [if_neg hpsh] at h
  by_cases hnd : Name.nodup cv.levelParams = true
  case neg => rw [if_neg (by simpa using hnd)] at h; close_throw h
  rw [if_pos (by simpa using hnd)] at h
  by_cases hlb : cv.type.looseBVarsBounded 0 = true
  case neg => rw [if_neg (by simpa using hlb)] at h; close_throw h
  rw [if_pos (by simpa using hlb)] at h
  by_cases hfv : cv.type.hasFvar = true
  case pos => rw [if_pos hfv] at h; close_throw h
  rw [if_neg hfv] at h
  by_cases hlp : cv.type.allLevelParamsDefined cv.levelParams = true
  case neg => rw [if_neg (by simpa using hlp)] at h; close_throw h
  rw [if_pos (by simpa using hlp)] at h
  by_cases hcr : cv.type.constsResolve env = true
  case neg => rw [if_neg (by simpa using hcr)] at h; close_throw h
  rw [if_pos (by simpa using hcr)] at h
  obtain ⟨stype, hst, h⟩ := exceptBind_ok h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  refine ⟨?_, by simpa using hres, by simpa using hpsh, hnd, hlb, by simpa using hfv, hlp, hcr,
    stype, u, hst, hu, h.symm⟩
  revert hfind; cases env.find? cv.name <;> simp

/-- The stored constant of a `classConstOk` run is well formed
(`checkConstantVal_typeWF`'s twin). -/
theorem classConstOk_typeWF {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : classConstOk (fueledOps mode F) (mkFEnv env) cv = .ok cvA) :
    cvA.type.hasFvar = false ∧
    cvA.type.allLevelParamsDefined cvA.levelParams = true ∧
    cvA.type.constsResolve env = true ∧
    cvA.type.looseBVarsBounded 0 = true := by
  obtain ⟨-, -, -, -, hlb, hfv, hlp, hcr, -, -, -, -, rfl⟩ := classConstOk_inv h
  exact ⟨hfv, hlp, hcr, hlb⟩

/-- **A `classConstOk` run's facts** (`ConstChecked`): the guards and the
inference are the run's; the stored type is the checked one, and its
empty-slot freshness is the full inference's (`inferTypeCore_noProjAt`:
a successful inference of a closed subject names only occupied slots —
the generated type is stored without an annotation pass). -/
theorem classConstOk_checked {env : Env} {cv0 cv : ConstantVal} {F : Nat}
    (h : classConstOk (fueledOps mode F) (mkFEnv env) cv0 = .ok cv) :
    ConstChecked mode F env cv0 cv := by
  obtain ⟨hfr, hres, hps, hnd, hlb, hfv, hlp, hcr, stype, u, hinf, hsort, rfl⟩ :=
    classConstOk_inv h
  exact {
    name := rfl, lps := rfl, fresh := hfr, unreserved := hres, notProjShape := hps,
    nodup := hnd, bounded := hlb, noFvar := hfv, lpsDef := hlp, resolves := hcr,
    sorted := ⟨stype, u, hinf, hsort⟩,
    noProj := fun _ _ hslot => inferTypeCore_noProjAt hinf hfv hslot }

/-- **One recursor's generated type, as `classRecTyOk` ran**: the record's
member, rule prefix and major index are the generated ones; the
generated type `gty` checked as a constant under the record's name and
level parameters (`classConstOk`: no annotation — the stored type IS the
generated one, `classConstOk_inv`) is the STORED constant `cvG`.  (The comparison with the
stream's type is reject-only: nothing is read from it.) -/
structure ClassRecTyRun (mode : CheckMode) (F : Nat) (fe : FEnv) (g : ClassGen) (k : Nat)
    (rc : RecShape) (c : Nat) (cvG : ConstantVal) : Type where
  gty : Expr
  htgt : rc.tgt = (g.cls.getD c default).member.getD k
  hrP : rc.rP = g.nP + g.slots.length
  hmI : rc.mI = rc.rP + (g.cls.getD c default).nIdx
  hgty : classGenRecTy g c = some gty
  hcv : classConstOk (fueledOps mode F) fe { rc.cvR with type := gty } = .ok cvG

/-- **`classRecTyOk`, inverted.** -/
theorem classRecTyOk_run {fe : FEnv} {g : ClassGen} {k : Nat} {rc : RecShape}
    {cvRi : ConstantVal} {c : Nat} {cvG : ConstantVal} {F : Nat}
    (h : classRecTyOk (fueledOps mode F) fe g k rc cvRi c = .ok cvG) :
    Nonempty (ClassRecTyRun mode F fe g k rc c cvG) := by
  unfold classRecTyOk at h
  simp only at h
  by_cases h1 : (rc.tgt == (g.cls.getD c default).member.getD k) = true
  case neg => rw [if_neg h1] at h; close_throw h
  rw [if_pos h1] at h
  by_cases h2 : (rc.rP == g.nP + g.slots.length && rc.mI == rc.rP + (g.cls.getD c default).nIdx)
    = true
  case neg => rw [if_neg h2] at h; close_throw h
  rw [if_pos h2] at h
  obtain ⟨gty, hgty, h⟩ := exceptBind_ok h
  obtain ⟨cv, hcv, h⟩ := exceptBind_ok h
  obtain ⟨b, -, h⟩ := exceptBind_ok h
  by_cases hb : b = true
  case neg => rw [if_neg hb] at h; close_throw h
  rw [if_pos hb] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq, Bool.and_eq_true] at h1 h2
  exact ⟨{
    gty := gty, htgt := h1, hrP := h2.1, hmI := h2.2, hgty := unwrapOr_ok hgty,
    hcv := hcv }⟩

/-- **`classRecTysOk`, inverted**: one generated type per recursor, at the
recursor's class. -/
theorem classRecTysOk_run {fe : FEnv} {g : ClassGen} {k : Nat} {F : Nat} :
    ∀ {recs : List RecShape} {cvs : List ConstantVal} {cls : List Nat} {cvGs : List ConstantVal},
      classRecTysOk (fueledOps mode F) fe g k recs cvs cls = .ok cvGs →
      cvGs.length = recs.length ∧
      ∀ (i : Nat) (rc : RecShape), recs[i]? = some rc →
        ∃ c cvG, cls[i]? = some c ∧ cvGs[i]? = some cvG ∧
          Nonempty (ClassRecTyRun mode F fe g k rc c cvG)
  | [], _, _, cvGs, h => by
    simp only [classRecTysOk, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i rc hi => nomatch hi⟩
  | rc :: rcs, cv :: cvs, c :: cs, cvGs, h => by
    unfold classRecTysOk at h
    obtain ⟨x, hx, h⟩ := exceptBind_ok h
    obtain ⟨xs, hxs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := classRecTysOk_run hxs
    refine ⟨by simp [hlen], fun i rc' hi => ?_⟩
    cases i with
    | zero =>
      obtain rfl : rc = rc' := by simpa using hi
      exact ⟨c, x, rfl, rfl, classRecTyOk_run hx⟩
    | succ i => simpa using hall i rc' (by simpa using hi)
  | _ :: _, [], _, cvGs, h => by
    simp [classRecTysOk, throw, throwThe, MonadExceptOf.throw] at h
  | _ :: _, _ :: _, [], cvGs, h => by
    simp [classRecTysOk, throw, throwThe, MonadExceptOf.throw] at h

/-! ## The generated rules -/

/-- **One generated rule, as `classRuleOk` ran**: the generated term
`gen` closed and STORED as generated (`out = gen`: the generator writes
its binder data), its level parameters the recursor's, resolved and
inferred at the rule-less recursors' environment; its λ-telescope `n`
long, the λ-domains resolving at the constructors' environment and
carrying the family's datum. -/
structure ClassRuleRun (mode : CheckMode) (F : Nat) (w : StructWalkers) (feT feR : FEnv)
    (cvR : ConstantVal) (pw : PropWhen) (n : Nat) (gen out : Expr) : Type where
  rbs : List (Expr × BinderMeta)
  body : Expr
  tyR : Expr
  hbv : gen.looseBVarsBounded 0 = true
  hfv : gen.hasFvar = false
  hout : out = gen
  hlp : out.allLevelParamsDefined cvR.levelParams = true
  hres : w.resolve feR out = true
  htyR : (fueledOps mode F).inferType feR.env 0 out = .ok tyR
  hstrip : out.stripLams n = some (rbs, body)
  hdoms : ∀ b ∈ rbs, w.resolve feT b.1 = true
  hpw : ∀ b ∈ rbs, b.2.pw = pw

/-- **`classRuleOk`, inverted.** -/
theorem classRuleOk_run {w : StructWalkers} {feT feR : FEnv} {cvR : ConstantVal} {pw : PropWhen}
    {n : Nat} {gen out : Expr} {F : Nat}
    (h : classRuleOk (fueledOps mode F) w feT feR cvR pw n gen = .ok out) :
    Nonempty (ClassRuleRun mode F w feT feR cvR pw n gen out) := by
  unfold classRuleOk at h
  by_cases hcl : (gen.looseBVarsBounded 0 && !gen.hasFvar) = true
  case neg => rw [if_neg hcl] at h; close_throw h
  rw [if_pos hcl] at h
  simp only at h
  by_cases hlp : gen.allLevelParamsDefined cvR.levelParams = true
  case neg => rw [if_neg hlp] at h; close_throw h
  rw [if_pos hlp] at h
  by_cases hres : w.resolve feR gen = true
  case neg => rw [if_neg hres] at h; close_throw h
  rw [if_pos hres] at h
  obtain ⟨tyR, htyR, h⟩ := exceptBind_ok h
  obtain ⟨⟨rbs, body⟩, hstrip, h⟩ := exceptBind_ok h
  simp only at h
  by_cases hdoms : (rbs.all fun b => w.resolve feT b.1) = true
  case neg => rw [if_neg hdoms] at h; close_throw h
  rw [if_pos hdoms] at h
  by_cases hpw : (rbs.all fun b => b.2.pw == pw) = true
  case neg => rw [if_neg hpw] at h; close_throw h
  rw [if_pos hpw] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcl
  simp only [List.all_eq_true, beq_iff_eq] at hdoms hpw
  exact ⟨{
    rbs := rbs, body := body, tyR := tyR, hbv := hcl.1, hfv := hcl.2, hout := rfl,
    hlp := hlp, hres := hres, htyR := htyR, hstrip := unwrapOr_ok hstrip, hdoms := hdoms,
    hpw := hpw }⟩

/-- **`classRulesOk`, inverted**: one generated rule per constructor of
the class. -/
theorem classRulesOk_run {w : StructWalkers} {feT feR : FEnv} {g : ClassGen}
    {recOf : Nat → Option Name} {cvR : ConstantVal} {pw : PropWhen} {c : Nat} {F : Nat} :
    ∀ {xs : List ClassCtor} {rhss : List Expr},
      classRulesOk (fueledOps mode F) w feT feR g recOf cvR pw c xs = .ok rhss →
      rhss.length = xs.length ∧
      ∀ (j : Nat) (x : ClassCtor), xs[j]? = some x →
        ∃ gen rhs, rhss[j]? = some rhs ∧
          classGenRule g recOf (cvR.levelParams.map .param) c x = some gen ∧
          Nonempty (ClassRuleRun mode F w feT feR cvR pw (g.nP + g.slots.length + x.nF)
            gen rhs)
  | [], rhss, h => by
    simp only [classRulesOk, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun j x hj => nomatch hj⟩
  | x :: xs, rhss, h => by
    unfold classRulesOk at h
    obtain ⟨gen, hgen, h⟩ := exceptBind_ok h
    obtain ⟨r, hr, h⟩ := exceptBind_ok h
    obtain ⟨rs, hrs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := classRulesOk_run hrs
    refine ⟨by simp [hlen], fun j x' hj => ?_⟩
    cases j with
    | zero =>
      obtain rfl : x = x' := by simpa using hj
      exact ⟨gen, r, rfl, unwrapOr_ok hgen, classRuleOk_run hr⟩
    | succ j => simpa using hall j x' (by simpa using hj)

/-- **`classRecsRulesOk`, inverted**: per recursor, its generated constant,
its class and its rules. -/
theorem classRecsRulesOk_run {w : StructWalkers} {feT feR : FEnv} {g : ClassGen}
    {recOf : Nat → Option Name} {pw : PropWhen} {F : Nat} :
    ∀ {cvGs : List ConstantVal} {cls : List Nat}
      {out : List (ConstantVal × TargetMajor × List Expr)},
      classRecsRulesOk (fueledOps mode F) w feT feR g recOf pw cvGs cls = .ok out →
      out.length = min cvGs.length cls.length ∧
      ∀ (i : Nat) (cvG : ConstantVal) (c : Nat), cvGs[i]? = some cvG → cls[i]? = some c →
        ∃ rhss, out[i]? = some (cvG, g.cls.getD c default, rhss) ∧
          classRulesOk (fueledOps mode F) w feT feR g recOf cvG pw c (g.ctors.getD c [])
            = .ok rhss
  | [], _, out, h => by
    simp only [classRecsRulesOk, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨by simp, fun i cvG c hi => nomatch hi⟩
  | _ :: _, [], out, h => by
    simp only [classRecsRulesOk, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨by simp, fun i cvG c _ hc => nomatch hc⟩
  | cvG :: cvs, c :: cs, out, h => by
    unfold classRecsRulesOk at h
    obtain ⟨rhss, hrhss, h⟩ := exceptBind_ok h
    obtain ⟨xs, hxs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := classRecsRulesOk_run hxs
    refine ⟨by simp [hlen, Nat.succ_min_succ], fun i cvG' c' hi hc => ?_⟩
    cases i with
    | zero =>
      obtain rfl : cvG = cvG' := by simpa using hi
      obtain rfl : c = c' := by simpa using hc
      exact ⟨rhss, rfl, hrhss⟩
    | succ i => simpa using hall i cvG' c' (by simpa using hi) (by simpa using hc)

/-! ## The whole stage -/

/-- The generator's input as `genRecCheck` builds it (the prefix computed
by the caller). -/
@[expose] def genRecGen (p : BlockShape) (params : List Expr) (Ms : List TargetMajor)
    (formerTysC : List Expr) (rd : ClassRead) (ctors : List (List ClassCtor))
    (pre : List (Expr × BinderMeta)) : ClassGen :=
  ⟨p.nP, params, Ms, formerTysC, rd.slots, ctors, structElimLevel p.elim p.large, pre⟩

/-- **The generated recursor stage, as run** — every bind of
`genRecCheck` named, on the pass's canonical parameters `params`, table
`tbl` and classes (`rd`, `Ms₀`).  `Ms` the classes with their table
entries; `ctors` the generator's constructors; `g` the generator; `cvGs`
the generated (stored) recursor constants; `out` the stored family. -/
structure GenStageRun (mode : CheckMode) (F : Nat) (fe : FEnv) (p : BlockShape)
    (nestedBit : Bool) (params : List Expr) (tbl : List NestCtorNf) (rd : ClassRead)
    (Ms₀ : List TargetMajor) (cvTas : List ConstantVal) (block : List ConstantInfo)
    (out : List (ConstantVal × TargetMajor × List Expr)) : Type where
  cvRis : List ConstantVal
  Ms : List TargetMajor
  ctors : List (List ClassCtor)
  formerTysC : List Expr
  pre : List (Expr × BinderMeta)
  cvGs : List ConstantVal
  /-- the records' pins -/
  pins : targetRecPins (m := CheckM) p block = .ok ()
  /-- the stream's recursor types, checked -/
  hcvRis : classStreamRecs (fueledOps mode F) fe p.recs = .ok cvRis
  /-- the elimination guard -/
  hk : 0 < p.k
  helim : (p.large && !blockLargeElimAllowed p (nestedBit || Ms₀.any (·.member.isNone))) = false
  /-- every class's table entries -/
  hMs : classesNfs (fueledOps mode F) fe.env p (cvTas.map (·.type)) tbl Ms₀ = .ok Ms
  /-- per class and constructor: datum, `ih`s, node agreement -/
  hctors : classesCtors (fueledOps mode F) fe.env p (cvTas.map (·.type)) rd Ms 0 Ms = .ok ctors
  /-- no minor premise beyond the classes' constructors -/
  hminors : (rd.slots.filter ClassSlot.isMinor).length = (ctors.map List.length).sum
  /-- the classes' formers -/
  hformer : Ms.mapM (classFormerTy (m := CheckM) fe cvTas) = .ok formerTysC
  /-- the shared prefix -/
  hpre : ClassGen.prefixBinders (genRecGen p params Ms formerTysC rd ctors []) = some pre
  /-- the generated types -/
  hcvGs : classRecTysOk (fueledOps mode F) fe (genRecGen p params Ms formerTysC rd ctors pre)
    p.k p.recs cvRis rd.recCls = .ok cvGs
  /-- the generated rules -/
  hrules : classRecsRulesOk (fueledOps mode F) .plain fe (classFeR p Ms cvGs rd.recCls fe)
    (genRecGen p params Ms formerTysC rd ctors pre) (classRecOf rd.recCls cvGs)
    (Level.zeronessOf (structElimLevel p.elim p.large)) cvGs rd.recCls = .ok out

/-- The generator of a stage run. -/
@[expose] def GenStageRun.g {F : Nat} {fe : FEnv} {p : BlockShape} {nestedBit : Bool}
    {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor}
    {cvTas : List ConstantVal} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : GenStageRun mode F fe p nestedBit params tbl rd Ms₀ cvTas block out) : ClassGen :=
  genRecGen p params R.Ms R.formerTysC rd R.ctors R.pre

/-- **The generated recursor stage, inverted** — the ONE unfolding of
`genRecCheck`. -/
theorem genRecCheck_run {fe : FEnv} {p : BlockShape} {nestedBit : Bool} {params : List Expr}
    {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor}
    {cvTas : List ConstantVal} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : genRecCheck (ShadowOps.fueled mode F) fe p nestedBit params tbl rd Ms₀ cvTas block
      = .ok out) :
    Nonempty (GenStageRun mode F fe p nestedBit params tbl rd Ms₀ cvTas block out) := by
  unfold genRecCheck at h
  obtain ⟨u0, hpins, h⟩ := exceptBind_ok h
  obtain ⟨cvRis, hcvRis, h⟩ := exceptBind_ok h
  by_cases hk : 0 < p.k
  case neg => rw [if_neg hk] at h; close_throw h
  rw [if_pos hk] at h
  by_cases helim : (p.large && !blockLargeElimAllowed p (nestedBit || Ms₀.any (·.member.isNone)))
    = true
  case pos => rw [if_pos helim] at h; close_throw h
  rw [if_neg helim] at h
  obtain ⟨Ms, hMs, h⟩ := exceptBind_ok h
  obtain ⟨ctors, hctors, h⟩ := exceptBind_ok h
  by_cases hminors : ((rd.slots.filter ClassSlot.isMinor).length ==
      (ctors.map List.length).sum) = true
  case neg => rw [if_neg hminors] at h; close_throw h
  rw [if_pos hminors] at h
  obtain ⟨formerTysC, hformer, h⟩ := exceptBind_ok h
  obtain ⟨pre, hpre, h⟩ := exceptBind_ok h
  obtain ⟨cvGs, hcvGs, h⟩ := exceptBind_ok h
  obtain ⟨u7, -, h⟩ := exceptBind_ok h
  obtain ⟨out', hout, h⟩ := exceptBind_ok h
  obtain ⟨u8, -, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [Bool.not_eq_true] at helim
  exact ⟨{
    cvRis := cvRis, Ms := Ms, ctors := ctors, formerTysC := formerTysC, pre := pre,
    cvGs := cvGs, pins := by cases u0; exact hpins, hcvRis := hcvRis,
    hk := hk, helim := helim, hMs := hMs, hctors := hctors,
    hminors := by simpa using hminors, hformer := hformer,
    hpre := unwrapOr_ok hpre, hcvGs := hcvGs, hrules := hout }⟩

/-- **The install's recursor stage, inverted**: `checkBlockRec` at the
fueled operations IS the generated stage at `ShadowOps.fueled`. -/
theorem checkBlockRec_run {env : Env} {p : BlockParts} {nested : Bool} {params : List Expr}
    {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : checkBlockRec (fueledOps mode F) env p nested params tbl rd Ms₀ block cvTas
      = .ok out) :
    Nonempty (GenStageRun mode F (mkFEnv env) p.toBlockShape nested params tbl rd Ms₀ cvTas
      block out) :=
  genRecCheck_run h

/-- **The generated recursor stage with the pass's classes and walk** —
the record every proof about the family reads: the pass's context
(`blockNestCtx`), its classes (`checkBlockClasses`, at the formers'
environment `fe₁`; `majC`: each also a checked major at the constructors'
environment `fe`), the positivity check's walk of every outside class
from the root frame's state `pos` (`nestSeeds`), and the stage's run on
the resulting table. -/
structure GenRecRun (mode : CheckMode) (F : Nat) (fe₁ : FEnv) (env₁ : Env) (fe : FEnv)
    (p : BlockShape) (nestedBit : Bool) (pos : NestState) (cvTas : List ConstantVal)
    (block : List ConstantInfo) (ctorsAs : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × TargetMajor × List Expr)) : Type where
  cvRis : List ConstantVal
  rd : ClassRead
  ctx : NestCtx
  holes : List Expr
  keys : List ClassKey
  Ms₀ : List TargetMajor
  st : NestState
  Ms : List TargetMajor
  ctors : List (List ClassCtor)
  formerTysC : List Expr
  pre : List (Expr × BinderMeta)
  cvGs : List ConstantVal
  /-- the records' pins -/
  pins : targetRecPins (m := CheckM) p block = .ok ()
  /-- the stream's recursor types, checked -/
  hcvRis : classStreamRecs (fueledOps mode F) fe p.recs = .ok cvRis
  /-- the pre-pass on the stream's RAW recursor types (UNVERIFIED: data only) -/
  hrd : classRead p.nP (classNPcOf p fe₁) p.recs = some rd
  /-- the block's canonical parameters and holes (the positivity check's context) -/
  hctx : blockNestCtx (m := CheckM) p cvTas fe₁.find? = .ok (ctx, holes)
  /-- the class keys, moved to the canonical parameters and annotated -/
  hkeys : rd.classes.mapM (classKeyOf (fueledOps mode F) env₁ p.nP ctx.params) = .ok keys
  /-- the classes, each a checked major over the canonical parameters -/
  hMs₀ : classMajors (fueledOps mode F) fe₁ p ctorsAs ctx.params keys = .ok Ms₀
  /-- each class, a checked major at the constructors' environment too -/
  majC : ∀ (i : Nat) (key : ClassKey), keys[i]? = some key →
    ∃ M, Ms₀[i]? = some M ∧ Nonempty (ClassMajorRun mode F fe p ctorsAs ctx.params key M)
  /-- one class per member -/
  hone : ∀ t, t < p.k → (Ms₀.filter (·.member == some t)).length = 1
  /-- the elimination guard -/
  hk : 0 < p.k
  helim : (p.large && !blockLargeElimAllowed p (nestedBit || Ms₀.any (·.member.isNone))) = false
  /-- the outside classes, walked at the formers' environment from the root frame's state -/
  hst : nestSeeds (fueledOps mode F) env₁ ctx (classSeeds ctx holes Ms₀) pos = .ok st
  /-- every class's table entries -/
  hMs : classesNfs (fueledOps mode F) fe.env p (cvTas.map (·.type)) st.ctorNfs.toList Ms₀ = .ok Ms
  /-- per class and constructor: datum, `ih`s, node agreement -/
  hctors : classesCtors (fueledOps mode F) fe.env p (cvTas.map (·.type)) rd Ms 0 Ms = .ok ctors
  /-- no minor premise beyond the classes' constructors -/
  hminors : (rd.slots.filter ClassSlot.isMinor).length = (ctors.map List.length).sum
  /-- the classes' formers -/
  hformer : Ms.mapM (classFormerTy (m := CheckM) fe cvTas) = .ok formerTysC
  /-- the shared prefix -/
  hpre : ClassGen.prefixBinders (genRecGen p ctx.params Ms formerTysC rd ctors []) = some pre
  /-- the generated types -/
  hcvGs : classRecTysOk (fueledOps mode F) fe (genRecGen p ctx.params Ms formerTysC rd ctors pre)
    p.k p.recs cvRis rd.recCls = .ok cvGs
  /-- the generated rules -/
  hrules : classRecsRulesOk (fueledOps mode F) .plain fe (classFeR p Ms cvGs rd.recCls fe)
    (genRecGen p ctx.params Ms formerTysC rd ctors pre) (classRecOf rd.recCls cvGs)
    (Level.zeronessOf (structElimLevel p.elim p.large)) cvGs rd.recCls = .ok out

/-- The generator of a run. -/
@[expose] def GenRecRun.g {F : Nat} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
    {nestedBit : Bool} {pos : NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : GenRecRun mode F fe₁ env₁ fe p nestedBit pos cvTas block ctorsAs out) :
    ClassGen :=
  genRecGen p R.ctx.params R.Ms R.formerTysC R.rd R.ctors R.pre

/-- **The record from the pass and the stage**: the context, the classes
and the walk of the outside classes are the pass's; the stage ran on the
walk's table.  `hag`: the formers' and the constructors' environments
agree on every stored inductive (the classes' check moves between them). -/
theorem genRecRun_of {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
    (hag : ClassEnvAgree p fe₁ fe) {nestedBit : Bool} {pos : NestState} {cvTas : List ConstantVal}
    {block : List ConstantInfo} {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    {ctx : NestCtx} {holes : List Expr} {rd : ClassRead} {Ms₀ : List TargetMajor}
    {st : NestState}
    (hctx : blockNestCtx (m := CheckM) p cvTas fe₁.find? = .ok (ctx, holes))
    (hcls : checkBlockClasses (fueledOps mode F) fe₁ env₁ p ctx.params ctorsAs = .ok (rd, Ms₀))
    (hst : nestSeeds (fueledOps mode F) env₁ ctx (classSeeds ctx holes Ms₀) pos = .ok st)
    (h : genRecCheck (ShadowOps.fueled mode F) fe p nestedBit ctx.params st.ctorNfs.toList rd
      Ms₀ cvTas block = .ok out) :
    Nonempty (GenRecRun mode F fe₁ env₁ fe p nestedBit pos cvTas block ctorsAs out) := by
  obtain ⟨C⟩ := checkBlockClasses_run hcls
  obtain ⟨S⟩ := genRecCheck_run h
  obtain ⟨-, hall⟩ := classMajors_run C.hMs
  exact ⟨{
    cvRis := S.cvRis, rd := rd, ctx := ctx, holes := holes, keys := C.keys, Ms₀ := Ms₀, st := st,
    Ms := S.Ms, ctors := S.ctors, formerTysC := S.formerTysC, pre := S.pre, cvGs := S.cvGs,
    pins := S.pins, hcvRis := S.hcvRis, hrd := C.hrd, hctx := hctx, hkeys := C.hkeys,
    hMs₀ := C.hMs,
    majC := fun i key hk => by
      obtain ⟨M, hM, ⟨R⟩⟩ := hall i key hk
      exact ⟨M, hM, R.transport hag⟩,
    hone := C.hone, hk := S.hk, helim := S.helim, hst := hst, hMs := S.hMs,
    hctors := S.hctors, hminors := S.hminors, hformer := S.hformer, hpre := S.hpre,
    hcvGs := S.hcvGs, hrules := S.hrules }⟩

/-- **Every class checked as a major at the constructors' environment**:
`classMajors_run`'s shape, over the run's keys. -/
theorem GenRecRun.majors {F : Nat} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
    {nestedBit : Bool} {pos : NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : GenRecRun mode F fe₁ env₁ fe p nestedBit pos cvTas block ctorsAs out) :
    R.Ms₀.length = R.keys.length ∧
      ∀ (i : Nat) (key : ClassKey), R.keys[i]? = some key →
        ∃ M, R.Ms₀[i]? = some M ∧ Nonempty (ClassMajorRun mode F fe p ctorsAs R.ctx.params key M) :=
  ⟨(classMajors_run R.hMs₀).1, R.majC⟩

/-- The run's keys are the pre-pass's classes, one each. -/
theorem GenRecRun.keys_length {F : Nat} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
    {nestedBit : Bool} {pos : NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : GenRecRun mode F fe₁ env₁ fe p nestedBit pos cvTas block ctorsAs out) :
    R.keys.length = R.rd.classes.length :=
  mapM_ok_length R.hkeys

/-- **The stored recursors are fresh**: every generated constant was
checked (`classConstOk`) at the constructors' environment, whose first
guard is its name's absence there. -/
theorem genRecCheck_out_fresh {env : Env} {p : BlockShape} {nestedBit : Bool}
    {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor}
    {cvTas : List ConstantVal} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : genRecCheck (ShadowOps.fueled mode F) (mkFEnv env) p nestedBit params tbl rd Ms₀ cvTas
      block = .ok out) :
    ∀ o ∈ out, env.find? o.1.name = none := by
  obtain ⟨R⟩ := genRecCheck_run h
  have hcvGs := R.hcvGs
  have hrules := R.hrules
  obtain ⟨hlenG, hallG⟩ := classRecTysOk_run hcvGs
  obtain ⟨hlenO, hallO⟩ := classRecsRulesOk_run hrules
  intro o ho
  obtain ⟨i, hoi⟩ := List.getElem?_of_mem ho
  have hil : i < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hoi).1; rw [hlenO] at this; omega
  obtain ⟨c, cvG, hc, hG, ⟨T⟩⟩ := hallG i p.recs[i] (List.getElem?_eq_getElem hil)
  obtain ⟨rhss, hoi', -⟩ := hallO i cvG c hG hc
  rw [hoi] at hoi'
  obtain rfl := Option.some.inj hoi'
  obtain ⟨hfr, -, -, -, -, -, -, -, -, -, -, -, hcv⟩ := classConstOk_inv T.hcv
  have hn : cvG.name = p.recs[i].cvR.name := by rw [hcv]
  show env.find? cvG.name = none
  rw [hn]
  exact hfr

end ConLeche
