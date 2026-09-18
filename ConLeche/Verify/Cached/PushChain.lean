module

public import ConLeche.Verify.Cached.AgreeFloor
public import ConLeche.Verify.EnvBound
import ConLeche.Verify.EnvWF
import ConLeche.Verify.CheckerF
-- the read-back's inversions (task #315 M8): the nested assemblies read
-- the SCRATCH index through `auxStored?`, and what it reads is what the
-- scratch install's own skeleton pins
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedAuxInv
-- the elimination's and the restore's name facts: the auxiliary block's
-- member count and member names, and K.39 as a theorem
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedRecNames
-- member m's auxiliary constructors are its own (task #315 M8)
import ConLeche.Verify.Inductives.NestedCopyGlue
-- the read-back's table field, both ways (task #315 M8)
import ConLeche.Verify.Inductives.NestedRecDoor

public section

/-!
# Every accepted install is a chain of fresh pushes (task #253)

The two-phase driver (`checkDeclsTwoPhase`, `ConLeche/Cached/ParsedC.lean`)
checks each recorded value against a PREFIX VIEW of the final
environment, `feFinal.restrictTo vis`, and the prefix view's `find?` is
the truncated environment's only under name uniqueness
(`mkFEnv_find?_visibleBelow`, `ConLeche/Verify/EnvBound.lean`).  Name
uniqueness is an install-time invariant: every push a driver step
performs is guarded by a lookup — `checkConstantValC`'s duplicate
guard, `checkMemberValF`'s, `installBasisDeclF`'s, the projection
name-family guards — so this file proves, once and OPERATIONALLY (no
environment well-formedness, no simulation: the final-value discipline
of `ConLeche/Verify/Cached/AgreeFloor.lean`), that an accepted step
returns `PushChain env fe'`: a canonical index whose constants extend
`env` by fresh names.  Chained from the empty environment, that is
`NodupNames` of every environment a driver ever holds, and the
suffix relation between the environment a declaration was installed at
and the final one.
-/

namespace ConLeche.Cached

open ConLeche

variable {pins : List NatOpPinSet}

/-! ## Fresh chains -/

/-- `fe'` extends `env` by a chain of pushes, each of a name fresh at the
environment it was pushed onto: `fe'` is canonical, `env.consts` is a
suffix of its constants, and name uniqueness carries over. -/
@[expose] def PushChain (env : Env) (fe' : FEnv) : Prop :=
  fe' = mkFEnv fe'.env ∧ (∃ new, fe'.env.consts = new ++ env.consts) ∧
  (NodupNames env → NodupNames fe'.env)

theorem PushChain.refl (env : Env) : PushChain env (mkFEnv env) :=
  ⟨rfl, ⟨[], rfl⟩, id⟩

theorem PushChain.canon {env : Env} {fe : FEnv} (h : PushChain env fe) :
    fe = mkFEnv fe.env := h.1

/-- **A CHAIN IS A SKELETON STATEMENT ABOUT ITSELF** (task #315 M8):
`PushChain`'s first conjunct *is* canonicity, and a skeleton claim at
the index's own environment is then reflexivity.  This is why the push
assembly for a scratch install needs **no new hypothesis** to read
what the install stored: the walk's lemmas (`…_skels`, and everything
`SkelIs.find?`/`SkelIs.isSome` derives from them) ask for `SkelIs`,
and the push proof already carries a chain — it does not have to be
handed the index's canonicity from outside, nor to re-establish it at
the stage boundaries. -/
theorem PushChain.skelIs {env : Env} {fe : FEnv} (h : PushChain env fe) :
    SkelIs fe (envSkels fe.env) :=
  SkelIs.self (canon_self h.1)

/-- A canonical index is a chain from its own environment. -/
theorem PushChain.self {fe : FEnv} (h : fe = mkFEnv fe.env) : PushChain fe.env fe :=
  ⟨h, ⟨[], rfl⟩, id⟩

theorem PushChain.find? {env : Env} {fe : FEnv} (h : PushChain env fe)
    (n : Name) : fe.find? n = fe.env.find? n := by
  have h1 := h.1
  calc fe.find? n = (mkFEnv fe.env).find? n := by rw [← h1]
    _ = fe.env.find? n := mkFEnv_find? _ n

/-- A lookup that fails names no stored constant. -/
theorem Env.find?_none_notin {env : Env} {n : Name} (h : env.find? n = none) :
    n ∉ env.consts.map (·.name) := by
  intro hmem
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
  unfold Env.find? at h
  exact (List.find?_eq_none.mp h) c hc (beq_self_eq_true _)

theorem PushChain.push {env : Env} {fe : FEnv} (h : PushChain env fe)
    {ci : ConstantInfo} (hfresh : fe.find? ci.name = none) :
    PushChain env (fe.push ci) := by
  obtain ⟨hc, ⟨new, hnew⟩, hnd⟩ := h
  refine ⟨?_, ⟨ci :: new, ?_⟩, ?_⟩
  · calc fe.push ci = (mkFEnv fe.env).push ci := by rw [← hc]
      _ = mkFEnv (fe.push ci).env := push_mkFEnv fe.env ci
  · show ci :: fe.env.consts = _
    rw [hnew]
    rfl
  · intro hnd₀
    show ((ci :: fe.env.consts).map (·.name)).Nodup
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, hnd hnd₀⟩
    rw [PushChain.find? ⟨hc, ⟨new, hnew⟩, hnd⟩] at hfresh
    exact Env.find?_none_notin hfresh

theorem PushChain.trans {env : Env} {fe₁ fe₂ : FEnv} (h₁ : PushChain env fe₁)
    (h₂ : PushChain fe₁.env fe₂) : PushChain env fe₂ := by
  obtain ⟨hc₁, ⟨new₁, hnew₁⟩, hnd₁⟩ := h₁
  obtain ⟨hc₂, ⟨new₂, hnew₂⟩, hnd₂⟩ := h₂
  exact ⟨hc₂, ⟨new₂ ++ new₁, by rw [hnew₂, hnew₁, List.append_assoc]⟩,
    fun h => hnd₂ (hnd₁ h)⟩

/-- A list of names, pairwise distinct and all fresh at `env`: pushing
constants of these names in this order is a fresh chain. -/
def FreshNames (env : Env) (ns : List Name) : Prop :=
  ns.Nodup ∧ ∀ n ∈ ns, env.find? n = none

theorem FreshNames.nil (env : Env) : FreshNames env [] :=
  ⟨List.nodup_nil, fun _ h => nomatch h⟩

/-- After pushing the head's constant, the tail is fresh at the
extended environment. -/
theorem FreshNames.step {env : Env} {c : ConstantInfo} {ns : List Name}
    (h : FreshNames env (c.name :: ns)) : FreshNames ⟨c :: env.consts⟩ ns := by
  obtain ⟨hnd, hfr⟩ := h
  rw [List.nodup_cons] at hnd
  refine ⟨hnd.2, fun n hn => ?_⟩
  rw [Env.find?_cons, if_neg (fun he => hnd.1 (by rw [he]; exact hn))]
  exact hfr n (List.mem_cons_of_mem _ hn)

/-- Freshness at the extended environment, with the head fresh at the
base, is freshness of the whole list at the base. -/
theorem FreshNames.cons_of {env : Env} {c : ConstantInfo} {ns : List Name}
    (hc : env.find? c.name = none) (h : FreshNames ⟨c :: env.consts⟩ ns) :
    FreshNames env (c.name :: ns) := by
  obtain ⟨hnd, hfr⟩ := h
  have hne : ∀ n ∈ ns, c.name ≠ n ∧ env.find? n = none := by
    intro n hn
    have := hfr n hn
    rw [Env.find?_cons] at this
    by_cases he : c.name = n
    · rw [if_pos he] at this; exact nomatch this
    · rw [if_neg he] at this; exact ⟨he, this⟩
  refine ⟨List.nodup_cons.mpr ⟨fun hm => (hne _ hm).1 rfl, hnd⟩, ?_⟩
  intro n hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hc
  · exact (hne n hn).2

/-! ## The generic stage helpers keep the name and record the guard -/

theorem checkConstantValF_fresh (ops : CheckerOps CheckCM) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (checkConstantValF ops fe cv)
      (fun cvA => cvA.name = cv.name ∧ fe.find? cv.name = none) := by
  unfold checkConstantValF
  yields
  all_goals exact Yields.pure ⟨rfl, Option.not_isSome_iff_eq_none.mp (by assumption)⟩

theorem checkMemberValF_fresh (ops : CheckerOps CheckCM)
    (blockNames : List Name) (fe : FEnv) (cv : ConstantVal) :
    Yields (checkMemberValF ops blockNames fe cv)
      (fun cvA => cvA.name = cv.name ∧ fe.find? cv.name = none) := by
  unfold checkMemberValF
  refine Yields.bind' (checkConstantValF_fresh ops fe cv) fun cvA hcvA => ?_
  yields
  all_goals (apply Yields.pure; exact hcvA)

theorem checkConstantValC_fresh (mode : CheckMode) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (checkConstantValC mode fe cv)
      (fun p => p.1.name = cv.name ∧ fe.find? cv.name = none) := by
  unfold checkConstantValC
  yields
  all_goals exact Yields.pure ⟨rfl, Option.not_isSome_iff_eq_none.mp (by assumption)⟩

/-! ## The value kinds -/

theorem checkDefnValC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) {cvA : ConstantVal} (hfr : fe.find? cvA.name = none)
    (jty value : Expr) (hint : ReducibilityHint) :
    Yields (checkDefnValC mode fe cvA jty value hint)
      (fun fe' => PushChain env fe') := by
  unfold checkDefnValC
  yields
  all_goals (apply Yields.pure; exact h.push hfr)

theorem checkThmValC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) {cvA : ConstantVal} (hfr : fe.find? cvA.name = none)
    (jty value : Expr) :
    Yields (checkThmValC mode fe cvA jty value)
      (fun fe' => PushChain env fe') := by
  unfold checkThmValC
  yields
  all_goals (apply Yields.pure; exact h.push hfr)

theorem checkOpaqueValC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) {cvA : ConstantVal} (hfr : fe.find? cvA.name = none)
    (jty value : Expr) :
    Yields (checkOpaqueValC mode fe cvA jty value)
      (fun fe' => PushChain env fe') := by
  unfold checkOpaqueValC
  yields
  all_goals (apply Yields.pure; exact h.push hfr)

/-! ## The modeled route -/

theorem checkIndMemberS_push (mode : CheckMode) (blockNames : List Name)
    (caps : IndCaps) {env : Env} {fe : FEnv} (h : PushChain env fe)
    (ci : ConstantInfo) :
    Yields (checkIndMemberS mode blockNames caps fe ci)
      (fun fe' => PushChain env fe') := by
  unfold checkIndMemberS
  ybind
  refine Yields.bind'
    (checkMemberValF_fresh (sharedOpsC mode fe) blockNames fe ci.toConstantVal)
    fun cvA hcvA => ?_
  obtain ⟨hn, hfr⟩ := hcvA
  cases ci with
  | indInfo cvI capsI =>
    refine Yields.pure (h.push ?_)
    show fe.find? cvA.name = none
    rw [hn]; exact hfr
  | ctorInfo cvI nP nF =>
    refine Yields.pure (h.push ?_)
    show fe.find? cvA.name = none
    rw [hn]; exact hfr
  | _ => exact Yields.ofThrow

theorem provisionRecsS_fresh (mode : CheckMode) (blockNames : List Name) :
    ∀ (recs : List ConstantInfo) {env : Env} (feAcc : FEnv),
      PushChain env feAcc →
      Yields (provisionRecsS mode blockNames feAcc recs)
        (fun p => FreshNames feAcc.env (p.2.map (·.1.name)))
  | [], env, feAcc, _ => by
    unfold provisionRecsS
    exact Yields.pure (FreshNames.nil _)
  | ci :: rest, env, feAcc, h => by
    unfold provisionRecsS
    cases ci with
    | recInfo cv mI rP rules =>
      ybind
      refine Yields.bind'
        (checkMemberValF_fresh (sharedOpsC mode feAcc) blockNames feAcc _)
        fun cvA hcvA => ?_
      obtain ⟨hn, hfr⟩ := hcvA
      have hfr' : feAcc.find? cvA.name = none := by rw [hn]; exact hfr
      -- K.55's guard is a pure Bool: the throwing branch yields nothing
      refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
      try simp only []
      refine Yields.bind'
        (provisionRecsS_fresh mode blockNames rest
          (feAcc.push (.recInfo cvA mI rP [])) (h.push hfr'))
        fun q hq => ?_
      obtain ⟨feSelf, others⟩ := q
      refine Yields.pure ?_
      rw [h.find?] at hfr'
      exact FreshNames.cons_of (c := .recInfo cvA mI rP []) hfr' hq
    | _ => exact Yields.ofThrow

/-- The recursor group's install fold: the provisioned names are pushed
in order onto the group's base index. -/
theorem recFold_push (mode : CheckMode) (blockNames : List Name)
    (fe₂ feSelf : FEnv) (f : Name → Name) :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule)) {env : Env}
      (acc : FEnv), PushChain env acc →
      FreshNames acc.env (checked.map (·.1.name)) →
      Yields (checked.foldlM (fun (acc : FEnv) c => do
          let rules' ← checkIotaRulesF mode (sharedOpsC mode feSelf) fe₂ feSelf
            f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules'))) acc)
        (fun acc' => PushChain env acc')
  | [], env, acc, h, _ => by
    simp only [List.foldlM_nil]
    exact Yields.pure h
  | c :: cs, env, acc, h, hf => by
    simp only [List.foldlM_cons]
    have hfr : acc.find? c.1.name = none := by
      rw [h.find?]
      exact hf.2 _ (by simp)
    refine Yields.bind' (Q := fun acc' => ∃ rules',
        acc' = acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules'))
      (Yields.bind fun rules' => Yields.pure ⟨rules', rfl⟩) fun acc' hacc' => ?_
    obtain ⟨rules', rfl⟩ := hacc'
    exact recFold_push mode blockNames fe₂ feSelf f cs _ (h.push hfr)
      (FreshNames.step (c := .recInfo c.1 c.2.1 c.2.2.1 rules') hf)

theorem checkIndRecsS_push (mode : CheckMode) (blockNames : List Name)
    {env : Env} {fe₂ : FEnv} (h : PushChain env fe₂)
    (recs : List ConstantInfo) :
    Yields (checkIndRecsS mode blockNames fe₂ recs)
      (fun fe' => PushChain env fe') := by
  unfold checkIndRecsS
  simp only []
  split
  · exact Yields.pure h
  · split
    · refine Yields.bind'
        (provisionRecsS_fresh mode blockNames recs fe₂ h) fun q hq => ?_
      obtain ⟨feSelf, checked⟩ := q
      ybind
      exact recFold_push mode blockNames fe₂ feSelf _ checked fe₂ h hq
    · exact Yields.ofThrowBind

theorem checkProjLookupsF_fresh (fe : FEnv) (T ctorName : Name)
    (lps : List Name) (nP nF i : Nat) :
    Yields (checkProjLookupsF (m := CheckCM) fe T ctorName lps nP nF i)
      (fun _ => fe.find? (projFnName T i) = none) := by
  unfold checkProjLookupsF
  yields
  all_goals (apply Yields.pure; exact Option.isNone_iff_eq_none.mp (by assumption))

theorem checkProjFnS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) :
    Yields (checkProjFnS mode fe T ctorName lps nP nF i)
      (fun fe' => PushChain env fe') := by
  unfold checkProjFnS
  refine Yields.bind' (checkProjLookupsF_fresh fe T ctorName lps nP nF i)
    fun pr hfr => ?_
  yields
  all_goals (apply Yields.pure; exact h.push hfr)

theorem installProjFnStepS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) :
    Yields (installProjFnStepS mode T ctorName lps nP nF fe i)
      (fun fe' => PushChain env fe') := by
  unfold installProjFnStepS
  split
  · ybind
    exact checkProjFnS_push mode h T ctorName lps nP nF i
  · exact Yields.pure h

/-- The members-then-recursors phase, shared by both arms of
`checkIndDeclSF`'s block match. -/
theorem indBase_push (mode : CheckMode) (blockNames : List Name)
    (caps : IndCaps) {env : Env} {fe : FEnv} (h : PushChain env fe)
    (nonrecs recs : List ConstantInfo) :
    Yields (do
        let fe₂ ← nonrecs.foldlM (checkIndMemberS mode blockNames caps) fe
        checkIndRecsS mode blockNames fe₂ recs)
      (fun fe' => PushChain env fe') := by
  refine Yields.bind'
    (Yields.foldlM_rel (R := fun fe (_ : Unit) => PushChain env fe)
      (g := fun u _ => u)
      (fun acc ci _ hacc => checkIndMemberS_push mode blockNames caps hacc ci)
      nonrecs fe () h) fun fe₂ h₂ => ?_
  exact checkIndRecsS_push mode blockNames h₂ recs

theorem checkIndDeclSF_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (block : List ConstantInfo) :
    Yields (checkIndDeclSF mode fe block)
      (fun fe' => PushChain env fe') := by
  unfold checkIndDeclSF
  simp only []
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue =>
    split
    case h_1 cvT capsT cvC nP nF hI hC =>
      ybind
      refine Yields.bind'
        (Yields.foldlM_rel (R := fun fe (_ : Unit) => PushChain env fe)
          (g := fun u _ => u)
          (fun acc ci _ hacc => checkIndMemberS_push mode _ _ hacc ci) _ fe () h)
        fun fe₂ h₂ => ?_
      refine Yields.bind' (checkIndRecsS_push mode _ h₂ _) fun fe₃ h₃ => ?_
      split
      case isFalse => exact Yields.ofThrowBind
      case isTrue =>
        split
        case isFalse => exact Yields.ofThrowBind
        case isTrue =>
          split
          · exact Yields.foldlM_rel (R := fun fe (_ : Unit) => PushChain env fe)
              (g := fun u _ => u)
              (fun acc i _ hacc =>
                installProjFnStepS_push mode hacc cvT.name cvC.name
                  cvT.levelParams nP nF i) (List.range nF) fe₃ () h₃
          · exact Yields.pure h₃
    case h_2 => exact indBase_push mode _ _ h _ _

/-! ## The fixpoint route -/

theorem checkSumIndF_push {env : Env} {fe : FEnv} (h : PushChain env fe)
    (ops : CheckerOps CheckCM) (p : InductiveShape)
    (capsOf : InductiveShape → IndCaps) :
    Yields (checkSumIndF ops fe p capsOf)
      (fun r => PushChain env r.1 ∧ ∃ s, r.2.2 = p.withSort s) := by
  unfold checkSumIndF
  refine Yields.bind' (checkConstantValF_fresh ops fe p.cvT) fun cvTa₀ h₀ => ?_
  obtain ⟨hn₀, hfr⟩ := h₀
  refine Yields.bind' (checkSumTeleF_name ops fe p.cvT _ cvTa₀) fun r hn => ?_
  obtain ⟨cvTa, s⟩ := r
  have hn' : cvTa.name = p.cvT.name := by
    rcases hn with h1 | h1
    · exact h1.trans hn₀
    · exact h1
  yields
  all_goals
    (refine Yields.pure ⟨h.push ?_, s, rfl⟩
     show fe.find? cvTa.name = none
     rw [hn']; exact hfr)

theorem checkSumCtorF_fresh (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    Yields (checkSumCtorF ops fe₀ fe T lps nP nIdx rs isProp large cvC nF cvTa)
      (fun r => r.1.name = cvC.name ∧ fe.find? cvC.name = none) := by
  unfold checkSumCtorF
  refine Yields.bind' (checkConstantValF_fresh ops fe cvC) fun cvCa₀ h₀ => ?_
  obtain ⟨hn₀, hfr⟩ := h₀
  refine Yields.bind' (normCtorValF_name ops fe T nP nF cvC cvCa₀ hn₀) fun cvCa hn => ?_
  yields
  all_goals (apply Yields.pure; exact ⟨hn, hfr⟩)

theorem checkSumCtorsF_fresh (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    ∀ (cs : List (ConstantVal × Nat)),
      Yields (checkSumCtorsF ops fe₀ fe T lps nP nIdx rs isProp large cvTa cs)
        (fun r => r.1.map (·.1.name) = cs.map (·.1.name) ∧
          ∀ c ∈ r.1, fe.find? c.1.name = none)
  | [] => Yields.pure ⟨rfl, fun _ hc => nomatch hc⟩
  | c :: cs => by
    unfold checkSumCtorsF
    refine Yields.bind' (checkSumCtorF_fresh ops fe₀ fe T lps nP nIdx rs isProp
      large c.1 c.2 cvTa) fun q hq => ?_
    obtain ⟨cvCa, sorts⟩ := q
    obtain ⟨hn, hfr⟩ := hq
    refine Yields.bind' (checkSumCtorsF_fresh ops fe₀ fe T lps nP nIdx rs isProp
      large cvTa cs) fun rest hrest => ?_
    obtain ⟨rest, srest⟩ := rest
    obtain ⟨hrest, hfrs⟩ := hrest
    have hn' : cvCa.name = c.1.name := hn
    have hrest' : rest.map (·.1.name) = cs.map (·.1.name) := hrest
    refine Yields.pure ⟨by simp [hn', hrest'], ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · show fe.find? cvCa.name = none
      rw [hn]; exact hfr
    · exact hfrs d hd

/-- The constructors' conses: a fresh chain from the former's index. -/
theorem consSumCtorsF_push (nP : Nat) :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env} {fe : FEnv},
      PushChain env fe → FreshNames fe.env (ctorsA.map (·.1.name)) →
      PushChain env (consSumCtorsF nP ctorsA fe)
  | [], _, _, h, _ => h
  | c :: cs, env, fe, h, hf => by
    have hfr : fe.find? c.1.name = none := by
      rw [h.find?]
      exact hf.2 _ (by simp)
    exact consSumCtorsF_push nP (ctorsA := cs) (h.push hfr)
      (FreshNames.step (c := .ctorInfo c.1 nP c.2) hf)

theorem checkNativeRecF_fresh (ops : CheckerOps CheckCM) {w : StructWalkers}
    (fe : FEnv) (p : NativeParts) (cvTa : ConstantVal)
    (ctorsA : List (ConstantVal × Nat)) :
    Yields (checkNativeRecF ops w fe p cvTa ctorsA)
      (fun r => r.1.name = p.cvR.name ∧ fe.find? p.cvR.name = none) := by
  unfold checkNativeRecF
  refine Yields.letFun ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  try simp only []
  refine Yields.letFun ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  try simp only []
  refine Yields.letFun ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  try simp only []
  refine Yields.bind' (checkConstantValF_fresh ops fe p.cvR) fun cvRi hcv => ?_
  yields
  all_goals (apply Yields.pure; exact ⟨rfl, hcv.2⟩)

theorem checkStructProjTableF_push {w : StructWalkers} {env : Env} {fe : FEnv}
    (h : PushChain env fe) (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal) :
    Yields (checkStructProjTableF (m := CheckCM) w T C lps nP nF resSort guards
        off cvCa fe)
      (fun fe' => PushChain env fe') := by
  unfold checkStructProjTableF
  yields
  all_goals exact Yields.pure (h.push (Option.isNone_iff_eq_none.mp (by assumption)))

theorem checkNativeTableF_push {w : StructWalkers} {env : Env} {fe : FEnv}
    (h : PushChain env fe) (p : NativeParts) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) :
    Yields (checkNativeTableF (m := CheckCM) w p ctorsA sortss fe)
      (fun fe' => PushChain env fe') := by
  unfold checkNativeTableF
  split
  · split
    · exact checkStructProjTableF_push h _ _ _ _ _ _ _ _ _
    · exact Yields.pure h
  · exact Yields.pure h

/-- One pass (task #268): the former's cons keeps the chain, the
constructors are the block's by name and fresh at its environment. -/
theorem checkNativePassS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (p : NativeParts) (isRec : Bool) :
    Yields (checkNativePassS mode fe p isRec)
      (fun r => PushChain env r.1.env₁ ∧ r.1.p.ctors = p.ctors ∧
        r.1.ctorsA.map (·.1.name) = r.1.p.ctors.map (·.1.name) ∧
        ∀ c ∈ r.1.ctorsA, r.1.env₁.find? c.1.name = none) := by
  unfold checkNativePassS
  refine Yields.bind' (checkSumIndF_push h _ p.toInductiveShape
    (fun p₁ => nativeCapsAt p₁ isRec)) fun r₁ h₁ => ?_
  obtain ⟨fe₁, cvTa, p₁⟩ := r₁
  obtain ⟨h₁, s, hps⟩ := h₁
  try simp only [] at hps
  subst hps
  try simp only []
  ybind
  refine Yields.bind' (checkSumCtorsF_fresh _ fe₁ fe₁ _ _ _ _ _ _ _ cvTa _) fun r hr => ?_
  obtain ⟨ctorsA, sortss⟩ := r
  obtain ⟨hns, hfrs⟩ := hr
  try simp only []
  refine Yields.bind fun kinds => ?_
  refine Yields.pure ⟨h₁, ?_, ?_, hfrs⟩
  · simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
  · rw [hns]
    simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]

/-- The install after the pass keeps the chain. -/
theorem checkNativeTailS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    {q : NativePass FEnv} (h₁ : PushChain env q.env₁)
    (hnd : (q.p.ctors.map (·.1.name)).Nodup)
    (hns : q.ctorsA.map (·.1.name) = q.p.ctors.map (·.1.name))
    (hfrs : ∀ c ∈ q.ctorsA, q.env₁.find? c.1.name = none) :
    Yields (checkNativeTailS mode fe q) (fun fe' => PushChain env fe') := by
  unfold checkNativeTailS
  -- the elimination restriction, on the completed record
  try apply Yields.letFun
  refine Yields.ofDecCases (fun _ => ?elim) (fun _ => Yields.ofThrowBind)
  case elim =>
  ybind
  refine Yields.bind fun _isorts => ?_
  try simp only []
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue hk =>
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue _ =>
  ybind
  have hbase : PushChain env (consSumCtorsF q.p.nP q.ctorsA q.env₁) := by
    refine consSumCtorsF_push q.p.nP h₁ ⟨?_, ?_⟩
    · rw [hns]; exact hnd
    · intro n hn
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
      rw [← h₁.find?]
      exact hfrs c hc
  refine Yields.bind' (checkNativeRecF_fresh _ (consSumCtorsF q.p.nP q.ctorsA q.env₁) q.p q.cvTa
    q.ctorsA) fun r₃ h₃ => ?_
  obtain ⟨cvRa, rhss⟩ := r₃
  obtain ⟨hnR, hfrR⟩ := h₃
  try simp only [] at hnR hfrR
  try simp only []
  have hpush := hbase.push (ci := .recInfo cvRa q.p.majorIdx q.p.rulePrefix
    (sumRules (consSumCtorsF q.p.nP q.ctorsA q.env₁).find? cvRa.name
      q.p.nP q.p.majorIdx q.p.rulePrefix cvRa.type q.ctorsA rhss))
    (by show (consSumCtorsF q.p.nP q.ctorsA q.env₁).find? cvRa.name = none
        rw [hnR]; exact hfrR)
  refine Yields.bind' (checkNativeTableF_push hpush q.p q.ctorsA q.sortss) fun fe' h' => ?_
  yields
  all_goals (apply Yields.pure; exact h')

theorem checkNativeS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (p : NativeParts) :
    Yields (checkNativeS mode fe p) (fun fe' => PushChain env fe') := by
  unfold checkNativeS
  -- the front guard: the distinct constructor names
  try apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hnd => ?main)
  case main =>
  ybind
  -- the pass at the syntactic reading, and again where it overshot
  refine Yields.bind' (checkNativePassS_push mode h p (nativeRawRec p)) fun r hr => ?_
  obtain ⟨q, settled⟩ := r
  obtain ⟨h₁, hpC, hns, hfrs⟩ := hr
  try simp only [] at h₁ hpC hns hfrs
  try simp only []
  cases settled with
  | true =>
    simp only [↓reduceIte]
    exact checkNativeTailS_push mode h₁ (by rw [hpC]; exact hnd) hns hfrs
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  ybind
  refine Yields.bind' (checkNativePassS_push mode h p (nativeIsRec q.p.kinds)) fun r' hr' => ?_
  obtain ⟨q', settled'⟩ := r'
  obtain ⟨h₁', hpC', hns', hfrs'⟩ := hr'
  try simp only [] at h₁' hpC' hns' hfrs'
  try simp only []
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue _ =>
  exact checkNativeTailS_push mode h₁' (by rw [hpC']; exact hnd) hns' hfrs'

/-! ## The mutual route (task #278) -/

private theorem map_fst_zipIdx {α β : Type} (f : α → β) :
    ∀ (l : List α) (n : Nat), (l.zipIdx n).map (fun c => f c.1) = l.map f
  | [], _ => rfl
  | a :: l, n => by
      simp only [List.zipIdx_cons, List.map_cons, List.cons.injEq, true_and]
      exact map_fst_zipIdx f l (n + 1)

private theorem fst_mem_of_mem_zipIdx {α : Type} : ∀ {l : List α} {n : Nat} {c : α × Nat},
    c ∈ l.zipIdx n → c.1 ∈ l
  | [], _, _, h => by simp at h
  | a :: l, n, c, h => by
      rw [List.zipIdx_cons] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (fst_mem_of_mem_zipIdx h)

/-- The block's constructors have distinct names. -/
private theorem nodup_ctors_of_blockNames {b : MutualBlock} (h : b.blockNames.Nodup) :
    (b.ctors.map (·.cv.name)).Nodup := by
  unfold MutualBlock.blockNames at h
  exact (List.nodup_append.mp (List.nodup_append.mp h).1).2.1

/-- The block's members have distinct names. -/
private theorem nodup_members_of_blockNames {b : MutualBlock} (h : b.blockNames.Nodup) :
    (b.formers.map (·.1.name)).Nodup := by
  unfold MutualBlock.blockNames MutualBlock.memberNames at h
  exact (List.nodup_append.mp (List.nodup_append.mp h).1).1

/-- … and so do its recursors. -/
private theorem nodup_recs_of_blockNames {b : MutualBlock} (h : b.blockNames.Nodup) :
    ((List.range b.k).map b.recName).Nodup := by
  unfold MutualBlock.blockNames at h
  exact (List.nodup_append.mp h).2.1

/-- The recogniser's recursor pin, at one member: the stream's record
is the generated recursor's name. -/
private theorem mutualRecPin_name {p : MutualParts} (h : mutualRecPinOk p = true) {m : Nat}
    {x : ConstantVal × List RecRule}
    (hx : (p.members.map fun mb => (mb.cvR, mb.rules))[m]? = some x) :
    x.1.name = p.toBlock.recName m := by
  have hm : m < p.members.length := by
    have := List.getElem?_eq_some_iff.mp hx
    simpa using this.1
  have hmem : p.members[m]? = some p.members[m] := List.getElem?_eq_getElem hm
  have hxv : x = (p.members[m].cvR, p.members[m].rules) := by
    rw [List.getElem?_map, hmem] at hx
    simpa using hx.symm
  have hall := (List.all_eq_true.mp h) m (List.mem_range.mpr (by simpa [MutualParts.k] using hm))
  rw [hmem] at hall
  simp only [Bool.and_eq_true, beq_iff_eq] at hall
  rw [hxv]
  show p.members[m].cvR.name = _
  rw [hall.1.1.1.1]
  show _ = ((p.members.map (fun (mb : MutualMember) => (mb.cv, mb.nIdx))).getD m
    default).1.name.str "rec"
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hmem]
  rfl

/-! ### The stages

The four environment transitions of the mutual install are fresh
chains for the same reasons the fixpoint route's are: the formers and
the constructors are checked by `checkConstantValF` at the index they
are pushed onto, the projection tables carry their own freshness
guard, and the block's own shape guard (`mutualShapeOk`) supplies the
distinctness the folds need.  The RECURSORS are the one place where
the check and the push are not at the same name: the stage checks the
STREAM's record and stores the GENERATED constant, so the name pin of
the recogniser (`mutualRecPinOk`, `mutualParts?_recPinned` above) is
what ties the two together. -/

/-- **The recogniser stores the pin it computed**: a recognised block's
`recPinned` bit IS `mutualRecPinOk` of the record, which is what ties
the recursor stage's freshness check (on the stream's record) to the
constant the install stores (the generated one). -/
theorem mutualParts?_recPinned {nP : Nat} {block : List ConstantInfo} {p : MutualParts}
    (h : mutualParts? nP block = some p) : p.recPinned = mutualRecPinOk p := by
  unfold mutualParts? at h
  simp only [] at h
  repeat (split at h <;> first | contradiction | skip)
  all_goals (injection h with h; subst h; rfl)

/-- The block's shape guard: its declaration names are distinct. -/
theorem mutualShapeOk_nodup (b : MutualBlock) :
    Yields (mutualShapeOk (m := CheckCM) b) (fun _ => b.blockNames.Nodup) := by
  unfold mutualShapeOk
  yields
  all_goals (apply Yields.pure; assumption)

/-- The block's shape guard, second reading: its constructors are
grouped by the member they return. -/
theorem mutualShapeOk_grouped (b : MutualBlock) :
    Yields (mutualShapeOk (m := CheckCM) b) (fun _ => mutualCtorsGrouped b.ctors = true) := by
  unfold mutualShapeOk
  yields
  all_goals (apply Yields.pure; assumption)

/-- The formers' checks: every member's name is the declared one and
is fresh at the block's starting index (the stage checks them ALL
there — official's `check_inductive_types` runs before
`declare_inductive_types`). -/
theorem mutualFormerChecksS_fresh (mode : CheckMode) (nP : Nat) :
    ∀ (fs : List (ConstantVal × Nat)) {fe : FEnv},
      Yields (mutualFormerChecksS mode fe nP false fs)
        (fun fms => fms.map (·.cvTa.name) = fs.map (·.1.name) ∧
          ∀ f ∈ fms, fe.find? f.cvTa.name = none)
  | [], _ => by
      unfold mutualFormerChecksS
      exact Yields.pure ⟨rfl, fun _ hf => nomatch hf⟩
  | (cv, nIdx) :: fs, fe => by
      unfold mutualFormerChecksS
      refine Yields.bind' (checkConstantValF_fresh (sharedOpsC mode fe) fe cv) fun cvTa₀ h₀ => ?_
      obtain ⟨hn₀, hfr⟩ := h₀
      refine Yields.bind' (checkSumTeleF_name (sharedOpsC mode fe) fe cv (nP + nIdx) cvTa₀)
        fun r hn => ?_
      obtain ⟨cvTa, s⟩ := r
      have hn' : cvTa.name = cv.name := by
        rcases hn with h1 | h1
        · exact h1.trans hn₀
        · exact h1
      ybind
      split
      split
      case isFalse => exact Yields.ofThrowBind
      case isTrue =>
      refine Yields.bind' (mutualFormerChecksS_fresh mode nP fs (fe := fe)) fun fms hq => ?_
      refine Yields.pure ⟨by simp [hn', hq.1], fun f hf => ?_⟩
      rcases List.mem_cons.mp hf with rfl | hf
      · show fe.find? cvTa.name = none
        rw [hn']; exact hfr
      · exact hq.2 f hf

/-- The formers' conses: a fresh chain from the block's starting
index. -/
theorem consMutualFormersF_push :
    ∀ {fms : List MutualFormerA} {env : Env} {fe : FEnv},
      PushChain env fe → FreshNames fe.env (fms.map (·.cvTa.name)) →
      PushChain env (consMutualFormersF fms fe)
  | [], _, _, h, _ => h
  | f :: fs, env, fe, h, hf => by
    have hfr : fe.find? f.cvTa.name = none := by
      rw [h.find?]
      exact hf.2 _ (by simp)
    exact consMutualFormersF_push (fms := fs) (h.push hfr)
      (FreshNames.step (c := .indInfo f.cvTa {}) hf)

/-- The formers' stage is a fresh chain: the members' names are the
block's, distinct by the shape guard, and every one of them is fresh
at the index the whole stage runs at. -/
theorem mutualFormersS_push (mode : CheckMode) (nP : Nat)
    (fs : List (ConstantVal × Nat)) {env : Env} {fe : FEnv} (h : PushChain env fe)
    (hnd : (fs.map (·.1.name)).Nodup) :
    Yields (mutualFormersS mode nP fs false fe) (fun r => PushChain env r.1) := by
  unfold mutualFormersS
  ybind
  refine Yields.bind' (mutualFormerChecksS_fresh mode nP fs (fe := fe)) fun fms hq => ?_
  refine Yields.pure (consMutualFormersF_push h ⟨by rw [hq.1]; exact hnd, ?_⟩)
  intro n hn
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
  rw [← h.find?]
  exact hq.2 f hf

/-- One constructor is checked at the environment it is pushed onto. -/
theorem checkMutualCtorF_fresh (ops : CheckerOps CheckCM) (w : StructWalkers) (fe : FEnv)
    (memberNames : List Name) (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level)
    (isProp large : Bool) (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    Yields (checkMutualCtorF ops w fe memberNames T lps nP nIdx rs isProp large cvC nF cvTa)
      (fun r => r.1.name = cvC.name ∧ fe.find? cvC.name = none) := by
  unfold checkMutualCtorF
  refine Yields.bind' (checkConstantValF_fresh ops fe cvC) fun cvCa₀ h₀ => ?_
  obtain ⟨hn₀, hfr⟩ := h₀
  refine Yields.bind' (normCtorValMF_name ops fe memberNames nP nF cvC cvCa₀ false hn₀)
    fun cvCa hn => ?_
  yields
  all_goals (apply Yields.pure; exact ⟨hn, hfr⟩)

/-- Every stored constructor is fresh at the formers' environment. -/
theorem checkMutualCtorsF_fresh (ops : CheckerOps CheckCM) (w : StructWalkers) (fe : FEnv)
    (b : MutualBlock) (fms : List MutualFormerA) (isProp : Bool) :
    ∀ (cs : List MutualCtor),
      Yields (checkMutualCtorsF ops w fe b fms isProp false cs)
        (fun r => ∀ c ∈ r.1, fe.find? c.1.name = none)
  | [] => Yields.pure (fun _ hc => nomatch hc)
  | c :: cs => by
    unfold checkMutualCtorsF
    refine Yields.bind' (checkMutualCtorF_fresh ops w fe b.memberNames _ b.lps b.nP _ _
      isProp b.large c.cv c.nF _) fun q hq => ?_
    obtain ⟨cvCa, sorts⟩ := q
    obtain ⟨hn, hfr⟩ := hq
    refine Yields.bind' (checkMutualCtorsF_fresh ops w fe b fms isProp cs) fun rest hrest => ?_
    obtain ⟨rest, srest⟩ := rest
    refine Yields.pure ?_
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · show fe.find? cvCa.name = none
      rw [hn]; exact hfr
    · exact hrest d hd

/-- The constructors' conses: a fresh chain from the formers' index. -/
theorem consMutualCtorsF_push (nP : Nat) :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env} {fe : FEnv},
      PushChain env fe → FreshNames fe.env (ctorsA.map (·.1.name)) →
      PushChain env (consMutualCtorsF nP ctorsA fe)
  | [], _, _, h, _ => h
  | c :: cs, env, fe, h, hf => by
    have hfr : fe.find? c.1.name = none := by
      rw [h.find?]
      exact hf.2 _ (by simp)
    exact consMutualCtorsF_push nP (ctorsA := cs) (h.push hfr)
      (FreshNames.step (c := .ctorInfo c.1 nP c.2) hf)

/-- One recursor: the stage checks the STREAM's record, so its
freshness is the GENERATED name's exactly when the two names agree
(the recogniser's pin). -/
theorem checkMutualRecTyF_fresh (ops : CheckerOps CheckCM) (w : StructWalkers) (fe : FEnv)
    (b : MutualBlock) (formers4 : List MutualFormer) (ctors4 : List MutualCtor4)
    (mIdx : Nat) (cvR : ConstantVal) (hnm : cvR.name = b.recName mIdx) :
    Yields (checkMutualRecTyF ops w fe b formers4 ctors4 mIdx (some cvR))
      (fun cvRa => fe.find? cvRa.name = none) := by
  unfold checkMutualRecTyF
  ybind
  split
  case h_2 => rename_i hne; exact absurd rfl (hne cvR)
  case h_1 =>
  rename_i cvR' heq
  injection heq with heq
  subst heq
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue =>
  ybind
  ybind
  refine Yields.bind' (checkConstantValF_fresh ops fe cvR) fun cvRi hcv => ?_
  yields
  all_goals
    (refine Yields.pure ?_
     show fe.find? (b.recName mIdx) = none
     rw [← hnm]
     exact hcv.2)

/-- The `k` recursor types are all fresh at the constructors'
environment. -/
theorem checkMutualRecTysF_fresh (ops : CheckerOps CheckCM) (w : StructWalkers) (fe : FEnv)
    (b : MutualBlock) (formers4 : List MutualFormer) (ctors4 : List MutualCtor4)
    (rs : List (ConstantVal × List RecRule))
    (hnm : ∀ m x, rs[m]? = some x → x.1.name = b.recName m) :
    ∀ (k : Nat), k ≤ rs.length →
      Yields (checkMutualRecTysF ops w fe b formers4 ctors4 (some rs) k)
        (fun cvRas => ∀ cv ∈ cvRas, fe.find? cv.name = none)
  | 0, _ => by
      unfold checkMutualRecTysF
      exact Yields.pure (fun _ hc => nomatch hc)
  | k + 1, hk => by
      unfold checkMutualRecTysF
      refine Yields.bind' (checkMutualRecTysF_fresh ops w fe b formers4 ctors4 rs hnm k
        (by omega)) fun earlier hearlier => ?_
      obtain ⟨x, hx⟩ : ∃ x, rs[k]? = some x :=
        ⟨rs[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have hstream : (some rs).bind (fun rs => (rs[k]?).map (·.1)) = some x.1 := by
        simp [hx]
      rw [hstream]
      refine Yields.bind' (checkMutualRecTyF_fresh ops w fe b formers4 ctors4 k x.1
        (hnm k x hx)) fun cvRa hcvRa => ?_
      refine Yields.pure ?_
      intro cv hcv
      rcases List.mem_append.mp hcv with hcv | hcv
      · exact hearlier cv hcv
      · rw [List.mem_singleton.mp hcv]; exact hcvRa

/-- The recursor group's conses: a fresh chain from the constructors'
index. -/
theorem storeMutualRecsF_push (fe₂ : FEnv) (b : MutualBlock) (fms : List MutualFormerA)
    (rulesOf : List (List (MutualCtor × Expr))) :
    ∀ (l : List (ConstantVal × Nat)) {env : Env} {fe : FEnv},
      PushChain env fe → FreshNames fe.env (l.map (·.1.name)) →
      PushChain env (storeMutualRecsF fe₂ b fms rulesOf l fe)
  | [], _, _, h, _ => h
  | (cvRa, mIdx) :: rest, env, fe, h, hf => by
    have hfr : fe.find? cvRa.name = none := by
      rw [h.find?]
      exact hf.2 _ (by simp)
    exact storeMutualRecsF_push fe₂ b fms rulesOf rest (h.push hfr)
      (FreshNames.step (c := .recInfo cvRa (b.rulePrefix + (fms.getD mIdx default).nIdx)
        b.rulePrefix (mutualRules fe₂.find? cvRa.name b.nP
          (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix cvRa.type
          (rulesOf.getD mIdx []))) hf)

/-- The projection tables carry their own freshness guard. -/
theorem mutualTablesF_push (w : StructWalkers) (b : MutualBlock)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level)) :
    ∀ (l : List (MutualFormerA × Nat)) {env : Env} {fe : FEnv}, PushChain env fe →
      Yields (mutualTablesF (m := CheckCM) w b ctorsA sortss l fe)
        (fun fe' => PushChain env fe')
  | [], _, _, h => by
      unfold mutualTablesF
      exact Yields.pure h
  | (f, mIdx) :: rest, env, fe, h => by
    unfold mutualTablesF
    refine Yields.bind' (Q := fun fe' => PushChain env fe') ?_ fun fe' h' => ?_
    · unfold mutualMemberTableF
      cases b.ownCtors mIdx with
      | nil => exact Yields.pure h
      | cons x xs =>
        cases xs with
        | nil =>
          obtain ⟨J, c⟩ := x
          cases hn : f.nIdx with
          | zero => exact checkStructProjTableF_push h _ _ _ _ _ _ _ _ _
          | succ n => exact Yields.pure h
        | cons y ys => exact Yields.pure h
    · exact mutualTablesF_push w b ctorsA sortss rest h'

/-- The mutual core is a fresh chain, given the recursors' name pin. -/
theorem checkMutualCoreS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (b : MutualBlock) (rs : List (ConstantVal × List RecRule))
    (hlen : b.k ≤ rs.length)
    (hnm : ∀ m x, rs[m]? = some x → x.1.name = b.recName m) :
    Yields (checkMutualCoreS mode fe b (some rs) false) (fun fe' => PushChain env fe') := by
  unfold checkMutualCoreS
  simp only []
  refine Yields.bind' (mutualShapeOk_nodup b) fun _ hnd => ?_
  refine Yields.bind' (mutualFormersS_push mode b.nP b.formers h
    (nodup_members_of_blockNames hnd)) fun r h₁ => ?_
  obtain ⟨fe₁, fms⟩ := r
  simp only [] at h₁ ⊢
  ybind
  ybind
  ybind
  ybind
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue =>
  refine Yields.bind'
    (Yields.and (checkMutualCtorsF_fresh (sharedOpsC mode fe₁) structWalkersC fe₁ b fms _ b.ctors)
      (checkMutualCtorsF_names (sharedOpsC mode fe₁) structWalkersC fe₁ b fms _ false b.ctors))
    fun r hr => ?_
  obtain ⟨ctorsA, sortss⟩ := r
  obtain ⟨hfrs, hctors⟩ := hr
  simp only [] at hfrs hctors ⊢
  ybind
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue =>
  -- the constructors' conses
  have hnames : ctorsA.map (·.1.name) = b.ctors.map (·.cv.name) := by
    have := congrArg (List.map Prod.fst) hctors
    simpa [List.map_map, Function.comp_def] using this
  have h₂ : PushChain env (consMutualCtorsF b.nP ctorsA fe₁) := by
    refine consMutualCtorsF_push b.nP h₁ ⟨?_, ?_⟩
    · rw [hnames]
      exact nodup_ctors_of_blockNames hnd
    · intro n hn
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
      rw [← h₁.find?]
      exact hfrs c hc
  ybind
  refine Yields.bind'
    (Yields.and (checkMutualRecTysF_fresh (sharedOpsC mode _) structWalkersC _ b _ _ rs hnm b.k
      hlen) (checkMutualRecTysF_names (sharedOpsC mode _) structWalkersC _ b _ _ (some rs) b.k))
    fun cvRas hcvRas => ?_
  obtain ⟨hfrR, hnR⟩ := hcvRas
  ybind
  ybind
  refine Yields.bind' (mutualTablesF_push structWalkersC b ctorsA sortss fms.zipIdx
    (storeMutualRecsF_push (consMutualCtorsF b.nP ctorsA fe₁) b fms _ cvRas.zipIdx h₂ ⟨?_, ?_⟩))
    fun fe' h' => ?_
  · rw [show cvRas.zipIdx.map (fun c => c.1.name) = cvRas.map (·.name) from
      map_fst_zipIdx (·.name) cvRas 0, hnR]
    exact nodup_recs_of_blockNames hnd
  · intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    rw [← h₂.find?]
    exact hfrR c.1 (fst_mem_of_mem_zipIdx hc)
  · yields
    all_goals (apply Yields.pure; exact h')

/-- The recognised mutual block is a fresh chain. -/
theorem checkMutualS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (p : MutualParts) (hpin : p.recPinned = mutualRecPinOk p) :
    Yields (checkMutualS mode fe p) (fun fe' => PushChain env fe') := by
  unfold checkMutualS
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue hrp =>
  refine checkMutualCoreS_push mode h p.toBlock _ ?_ ?_
  · simp [MutualBlock.k, MutualParts.toBlock]
  · intro m x hx
    exact mutualRecPin_name (by rw [← hpin]; exact hrp) hx

/-- **THE READ-BACK'S FORMER CARRIES ITS KEY'S NAME** (task #315 M8):
`auxStored?` looks the member up by the block's own name, and what the
lookup returns carries that name — which the SKELETON pins, so a walk
that never sees the scratch install's run gets it anyway. -/
theorem auxStoredAll_cvTa_name {feAux : FEnv} {sk : List InstallSkel}
    (hsk : SkelIs feAux sk) {b : MutualBlock} {stored : List AuxStored}
    (hst : auxStoredAll feAux.env b b.k = some stored) :
    ∀ (m : Nat) (a : AuxStored), stored[m]? = some a →
      ∃ cv : ConstantVal, b.formers[m]? = some (cv, a.nIdx) ∧ a.cvTa.name = cv.name := by
  intro m a ha
  obtain ⟨-, hget⟩ := auxStoredAll_get hst
  obtain ⟨cv, hfm, hfind⟩ := auxStored?_inv (hget m a ha)
  exact ⟨cv, hfm, skels_find?_name hsk hfind⟩

/-- **AND ITS CONSTRUCTORS CARRY THEIRS**, by the same lookup and the
same pin. -/
theorem auxStoredAll_ctor_name {feAux : FEnv} {sk : List InstallSkel}
    (hsk : SkelIs feAux sk) {b : MutualBlock} {stored : List AuxStored}
    (hst : auxStoredAll feAux.env b b.k = some stored) :
    ∀ (m : Nat) (a : AuxStored), stored[m]? = some a →
      ∀ (j : Nat) (c : ConstantVal × Nat × Nat), a.ctors[j]? = some c →
        ∃ (J : Nat) (mc : MutualCtor), (b.ownCtors m)[j]? = some (J, mc) ∧
          c.1.name = mc.cv.name := by
  intro m a ha j c hc
  obtain ⟨-, hget⟩ := auxStoredAll_get hst
  obtain ⟨-, hall⟩ := auxStored?_ctors (hget m a ha)
  obtain ⟨J, mc, hown, hfind⟩ := hall j c hc
  exact ⟨J, mc, hown, skels_find?_name hsk hfind⟩

/-- **AND ITS CONSTRUCTORS' NUMBERS TOO** (task #315 M8): the same
lookup, read against the scratch install's own skeleton, gives the
block's parameter count and the constructor's declared field count —
the two numbers the restored constructor's cons carries. -/
theorem auxStoredAll_ctor_data {feAux : FEnv} {sk : List InstallSkel} {b : MutualBlock}
    (hsk : SkelIs feAux (mutualBlockSkels b sk)) (hnd : b.blockNames.Nodup)
    {stored : List AuxStored} (hst : auxStoredAll feAux.env b b.k = some stored) :
    ∀ (m : Nat) (a : AuxStored), stored[m]? = some a →
      ∀ (j : Nat) (c : ConstantVal × Nat × Nat), a.ctors[j]? = some c →
        ∃ (J : Nat) (mc : MutualCtor), (b.ownCtors m)[j]? = some (J, mc) ∧
          c.1.name = mc.cv.name ∧ c.2.1 = b.nP ∧ c.2.2 = mc.nF := by
  intro m a ha j c hc
  obtain ⟨-, hget⟩ := auxStoredAll_get hst
  obtain ⟨-, hall⟩ := auxStored?_ctors (hget m a ha)
  obtain ⟨J, mc, hown, hfind⟩ := hall j c hc
  have hskf := hsk.env_find? mc.cv.name
  rw [hfind] at hskf
  obtain ⟨h1, h2⟩ := mutualBlockSkels_ctor_data hnd (ownCtors_getElem?_ctors hown).1
    (by simpa using hskf.symm)
  exact ⟨J, mc, hown, skels_find?_name hsk hfind, h1, h2⟩

/-! ## The nested route's four conses (task #315 M8)

`checkNestedS` pushes through four cons functions and nothing else, and
the SCRATCH install's index is discarded — the restored block is consed
onto the PRE-BLOCK index.  Each of the four is the exact twin of its
mutual counterpart above, so each is a fresh chain given the names'
freshness at the index it is consed onto. -/

theorem consNestedFormersF_push :
    ∀ {as : List AuxStored} {env : Env} {fe : FEnv},
      PushChain env fe → FreshNames fe.env (as.map (·.cvTa.name)) →
      PushChain env (consNestedFormersF as fe)
  | [], _, _, h, _ => h
  | a :: rest, env, fe, h, hf => by
    have hfr : fe.find? a.cvTa.name = none := by
      rw [h.find?]
      exact hf.2 _ (by simp)
    exact consNestedFormersF_push (as := rest) (h.push hfr)
      (FreshNames.step (c := .indInfo a.cvTa a.caps) hf)

theorem consNestedCtorsF_push :
    ∀ {cs : List (ConstantVal × Nat × Nat)} {env : Env} {fe : FEnv},
      PushChain env fe → FreshNames fe.env (cs.map (·.1.name)) →
      PushChain env (consNestedCtorsF cs fe)
  | [], _, _, h, _ => h
  | (cv, nP, nF) :: rest, env, fe, h, hf => by
    have hfr : fe.find? cv.name = none := by
      rw [h.find?]
      exact hf.2 _ (by simp)
    exact consNestedCtorsF_push (cs := rest) (h.push hfr)
      (FreshNames.step (c := .ctorInfo cv nP nF) hf)

theorem provisionNestedRecsF_push :
    ∀ {rs : List (ConstantVal × Nat × Nat)} {env : Env} {fe : FEnv},
      PushChain env fe → FreshNames fe.env (rs.map (·.1.name)) →
      PushChain env (provisionNestedRecsF rs fe)
  | [], _, _, h, _ => h
  | (cv, mI, rP) :: rest, env, fe, h, hf => by
    have hfr : fe.find? cv.name = none := by
      rw [h.find?]
      exact hf.2 _ (by simp)
    exact provisionNestedRecsF_push (rs := rest) (h.push hfr)
      (FreshNames.step (c := .recInfo cv mI rP []) hf)

theorem storeNestedRecsF_push :
    ∀ {rs : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env} {fe : FEnv},
      PushChain env fe → FreshNames fe.env (rs.map (·.1.name)) →
      PushChain env (storeNestedRecsF rs fe)
  | [], _, _, h, _ => h
  | (cv, mI, rP, rules) :: rest, env, fe, h, hf => by
    have hfr : fe.find? cv.name = none := by
      rw [h.find?]
      exact hf.2 _ (by simp)
    exact storeNestedRecsF_push (rs := rest) (h.push hfr)
      (FreshNames.step (c := .recInfo cv mI rP rules) hf)

/-- The names a row map keeps: a `zip` truncates and the row map keeps
the constant, so the stored names are a sublist of the checked ones. -/
private theorem zip_rows_names_sublist {β γ : Type} (g : ConstantVal × β → ConstantVal × γ)
    (hg : ∀ x, (g x).1 = x.1) :
    ∀ (cvs : List ConstantVal) (l : List β),
      (((cvs.zip l).map g).map (·.1.name)).Sublist (cvs.map (·.name))
  | [], _ => by simp
  | _ :: _, [] => by simp
  | cv :: cvs, x :: l => by
      simp only [List.zip_cons_cons, List.map_cons, hg]
      exact (zip_rows_names_sublist g hg cvs l).cons_cons cv.name

/-- A lifted `Except` yields its own answer. -/
theorem Yields.ofNestedLift {α : Type} {r : Except CheckError α} :
    Yields (nestedLift (m := CheckCM) r) (fun a => r = .ok a) := by
  cases r with
  | error e => intro s a s' hr; exact nomatch hr
  | ok x =>
    intro s a s' hr
    have hx : a = x := by
      unfold ConLeche.nestedLift at hr
      simp only [Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      exact hr.1.symm
    rw [hx]

/-- The scratch install's shape check, read out of the whole call: the
block's names are pairwise distinct, whatever else the install does. -/
theorem checkMutualCoreS_nodup (mode : CheckMode) (fe : FEnv) (b : MutualBlock)
    (sr : Option (List (ConstantVal × List RecRule))) (g : Bool) :
    Yields (checkMutualCoreS mode fe b sr g) (fun _ => b.blockNames.Nodup) := by
  unfold checkMutualCoreS
  simp only []
  refine Yields.bind' (mutualShapeOk_nodup b) fun _ hnd => ?_
  exact fun _ _ _ _ => hnd

/-- The same call's grouping guard: a constructor is listed under the
member it returns, which is what turns a position `(m, j)` of the
read-back into the global index `ownOffset m + j`. -/
theorem checkMutualCoreS_grouped (mode : CheckMode) (fe : FEnv) (b : MutualBlock)
    (sr : Option (List (ConstantVal × List RecRule))) (g : Bool) :
    Yields (checkMutualCoreS mode fe b sr g) (fun _ => mutualCtorsGrouped b.ctors = true) := by
  unfold checkMutualCoreS
  simp only []
  refine Yields.bind' (mutualShapeOk_grouped b) fun _ hgr => ?_
  exact fun _ _ _ _ => hgr

/-- The pre-normalisation front door REFUSES a taken name, so a success
is the name's freshness at the index it was checked against. -/
theorem checkConstantValPreF_fresh (ops : CheckerOps CheckCM) (fe : FEnv) (cv : ConstantVal) :
    Yields (checkConstantValPreF ops fe cv) (fun _ => fe.find? cv.name = none) := by
  unfold checkConstantValPreF
  yields
  all_goals (apply Yields.pure; exact Option.not_isSome_iff_eq_none.mp (by assumption))

/-- Every restored constructor is fresh at the index the restore checked
it against — which is ONE index for all of them (`fe₁`), so the
assembly's remaining duty is the name list's own `Nodup`. -/
theorem restoreCtorsF_fresh (ops : CheckerOps CheckCM) (fe : FEnv) (R : RestoreTbl)
    (lps : List Name) :
    ∀ (cs : List (ConstantVal × Nat × Nat)),
      Yields (restoreCtorsF ops fe R lps cs)
        (fun cs' => ∀ c ∈ cs', fe.find? c.1.name = none)
  | [] => by unfold restoreCtorsF; exact Yields.pure (fun _ h => nomatch h)
  | (cvCa, nP, nF) :: rest => by
    unfold restoreCtorsF
    ybind
    refine Yields.bind' (Yields.and
      (checkConstantValPreF_fresh ops fe { cvCa with levelParams := lps, type := _ })
      (checkConstantValPreF_name ops fe { cvCa with levelParams := lps, type := _ }))
      fun cvA hA => ?_
    obtain ⟨hfr, hnm⟩ := hA
    refine Yields.bind' (restoreCtorsF_fresh ops fe R lps rest) fun cs' hcs => ?_
    refine Yields.pure ?_
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · rw [hnm]; exact hfr
    · exact hcs c hc'

/-- Every restored recursor type is fresh at the index the restore
checked it against (`fe₂`), positionally. -/
theorem restoreRecTysF_fresh (ops : CheckerOps CheckCM) (fe : FEnv) (R : RestoreTbl)
    (lps : List Name) :
    ∀ (names : List Name) (as : List AuxStored),
      Yields (restoreRecTysF ops fe R lps names as)
        (fun cvs => ∀ cv ∈ cvs, fe.find? cv.name = none)
  | _, [] => by unfold restoreRecTysF; exact Yields.pure (fun _ h => nomatch h)
  | names, a :: rest => by
    unfold restoreRecTysF
    ybind
    refine Yields.bind' (Yields.and
      (checkConstantValPreF_fresh ops fe
        ⟨names.headD a.cvRa.name, a.cvRa.levelParams, _⟩)
      (checkConstantValPreF_name ops fe
        ⟨names.headD a.cvRa.name, a.cvRa.levelParams, _⟩)) fun cvA hA => ?_
    obtain ⟨hfr, hnm⟩ := hA
    refine Yields.bind' (restoreRecTysF_fresh ops fe R lps (names.drop 1) rest)
      fun cvs hcvs => ?_
    refine Yields.pure ?_
    intro cv hcv
    rcases List.mem_cons.mp hcv with rfl | hcv'
    · rw [hnm]; exact hfr
    · exact hcvs cv hcv'

theorem nestedMemberTableF_push {w : StructWalkers} {env : Env} {fe : FEnv}
    (h : PushChain env fe) (T : Name) (tbl? : Option ProjTable)
    (cs : List (ConstantVal × Nat × Nat)) :
    Yields (nestedMemberTableF (m := CheckCM) w T tbl? cs fe)
      (fun fe' => PushChain env fe') := by
  unfold nestedMemberTableF
  match tbl?, cs with
  | none, _ => exact Yields.pure h
  | some _, [] => exact Yields.pure h
  | some _, [(cvCa, nP, nF)] => exact checkStructProjTableF_push h _ _ _ _ _ _ _ _ _
  | some _, _ :: _ :: _ => exact Yields.pure h

theorem nestedTablesF_push (w : StructWalkers) :
    ∀ (l : List (Name × Option ProjTable × List (ConstantVal × Nat × Nat)))
      {env : Env} {fe : FEnv}, PushChain env fe →
      Yields (nestedTablesF (m := CheckCM) w l fe) (fun fe' => PushChain env fe')
  | [], _, _, h => by
      unfold nestedTablesF
      exact Yields.pure h
  | (T, tbl?, cs) :: rest, env, fe, h => by
    unfold nestedTablesF
    refine Yields.bind' (nestedMemberTableF_push h T tbl? cs) fun fe' h' => ?_
    exact nestedTablesF_push w rest h'

/-- A `Nodup` transported along a POSITIONAL naming bridge: if the
`m`-th element of `l` is named as the `m`-th element of `l'`, then `l`'s
names are distinct as soon as `l'`'s are.  This is how the read-back's
lists inherit the scratch block's `blockNames.Nodup`. -/
private theorem nodup_map_of_index_eq {α β : Type} {l : List α} {l' : List β}
    {f : α → Name} {g : β → Name}
    (hb : ∀ (m : Nat) (a : α), l[m]? = some a → ∃ c, l'[m]? = some c ∧ f a = g c)
    (hnd : (l'.map g).Nodup) : (l.map f).Nodup := by
  refine List.pairwise_iff_getElem.mpr ?_
  intro i j hi hj hij
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map]
  obtain ⟨ci, hci, hfi⟩ := hb i l[i] (List.getElem?_eq_getElem hi)
  obtain ⟨cj, hcj, hfj⟩ := hb j l[j] (List.getElem?_eq_getElem hj)
  obtain ⟨hi', hci'⟩ := List.getElem?_eq_some_iff.mp hci
  obtain ⟨hj', hcj'⟩ := List.getElem?_eq_some_iff.mp hcj
  have hnd' := List.pairwise_iff_getElem.mp hnd i j
    (by simpa using hi') (by simpa using hj') hij
  simp only [List.getElem_map] at hnd'
  rw [hfi, hfj, ← hci', ← hcj']
  exact hnd'

/-- **THE NESTED ROUTE'S PUSH CHAIN** (task #315 M8): `checkNestedS`
grows the index by four cons functions and nothing else — the restored
formers, the restored constructors, the restored recursors with their
rules, and the structure-like members' projection tables.  The SCRATCH
install's index is discarded (the restored block is consed onto the
PRE-BLOCK index), and the rule-less provision is a side branch the
rules are checked at, so neither reaches the output.

Three of the four cons points need the consed names pairwise distinct,
and all three distinctness facts come out of the SCRATCH install's own
shape check (`b.blockNames.Nodup`, read out of the whole call by
`checkMutualCoreS_nodup`):

* the formers', through the read-back's positional naming
  (`auxStoredAll_cvTa_name`);
* the constructors', through the same read-back at the constructors
  (`auxStoredAll_ctor_name`) and the block's grouping guard, which
  turns a position `(m, j)` into the global index `ownOffset m + j`
  (`restoredCtors_nodup_of_key`);
* the recursors', through `restoredRecNames_nodup_of` — K.39 as a
  THEOREM rather than as its `certOnly` Bool, which is `true` in
  trusted mode and could not serve a chain that must hold in every
  mode.

**No hypothesis is taken.**  The read-back's naming facts are stated
over the scratch index's SKELETON, and a `PushChain` is a skeleton
statement about itself (`PushChain.skelIs`), so the walk can read the
scratch install's data without being handed anything. -/
theorem checkNestedS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (p : NestedParts) :
    Yields (checkNestedS mode fe p) (fun fe' => PushChain env fe') := by
  unfold checkNestedS
  try ylet
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hg1 => ?_)
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hg2 => ?_)
  ybind
  refine Yields.bind' (nestedAnnotFormersF_names _ _ _ _) fun fmsA hfmsA => ?_
  ybind
  ybind
  refine Yields.bind' Yields.ofNestedLift fun st hst0 => ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hcnt => ?_)
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hfresh => ?_)
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hcont => ?_)
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  refine Yields.bind' Yields.ofUnwrapOr fun b hb => ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  refine Yields.bind' (Yields.and (Yields.and (checkMutualCoreS_nodup mode fe b none true)
      (checkMutualCoreS_grouped mode fe b none true))
    (checkMutualCoreS_skels mode h.skelIs b none true)) fun feAux hAux => ?_
  obtain ⟨⟨hnd, hgr⟩, hsk⟩ := hAux
  refine Yields.bind' Yields.ofUnwrapOr fun stored hst => ?_
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  ybind
  ybind
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hmem => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  -- (1) THE RESTORED FORMERS' CONS: fresh at the PRE-BLOCK index by the
  -- route's own guard, distinct because the scratch block's names are
  have htake : ∀ (m : Nat) (a : AuxStored), (List.take p.k stored)[m]? = some a →
      stored[m]? = some a := by
    intro m a ha
    rw [List.getElem?_take] at ha
    split at ha
    · exact ha
    · exact absurd ha (by simp)
  have hbridge := auxStoredAll_cvTa_name hsk hst
  have hndM : ((List.take p.k stored).map (·.cvTa.name)).Nodup := by
    refine nodup_map_of_index_eq (l' := b.formers) (g := fun f => f.1.name) ?_
      (nodup_members_of_blockNames hnd)
    intro m a ha
    obtain ⟨cv, hfm, hnm⟩ := hbridge m a (htake m a ha)
    exact ⟨(cv, a.nIdx), hfm, hnm⟩
  have hfrM : ∀ n ∈ (List.take p.k stored).map (fun a => a.cvTa.name), fe.env.find? n = none := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
    have hall := (List.all_eq_true.mp hmem) a ha
    simp only [Bool.and_eq_true] at hall
    rw [← h.find?]
    exact Option.isNone_iff_eq_none.mp (by simpa using hall.2)
  have h₁ : PushChain env (consNestedFormersF (List.take p.k stored) fe) :=
    consNestedFormersF_push h ⟨hndM, hfrM⟩
  apply Yields.letFun
  ybind
  ybind
  ybind
  ybind
  ybind
  -- (2) THE RESTORED CONSTRUCTORS' CONS: each restored constructor is
  -- checked at the formers' index it is pushed onto, and the names are
  -- the scratch block's own — so the block's `Nodup` is the list's
  refine Yields.bind' (Yields.mapM_getElem
    (fun a : AuxStored => Yields.and (restoreCtorsF_fresh _ _ _ _ a.ctors)
      (restoreCtorsF_names _ _ _ _ a.ctors)) _) fun ctorsR hctorsR => ?_
  have hbridgeC := auxStoredAll_ctor_name hsk hst
  have hndC : (ctorsR.flatten.map (·.1.name)).Nodup := by
    refine restoredCtors_nodup_of_key (b := b) (N := b.ctors.map (·.cv.name))
      (nodup_ctors_of_blockNames hnd) ?_
    intro mm j l c hl hc
    obtain ⟨a, ha, -, hnames⟩ := hctorsR.2 mm l hl
    obtain ⟨c', hc', heq⟩ := getElem?_of_map_eq hnames hc
    have hname : c.1.name = c'.1.name := congrArg (·.1) heq
    obtain ⟨J, mc, hown, hnm⟩ := hbridgeC mm a (htake mm a ha) j c' hc'
    obtain ⟨hctor, -⟩ := ownCtors_getElem?_ctors hown
    refine ⟨(List.getElem?_eq_some_iff.mp hown).1, ?_⟩
    rw [List.getElem?_map, ← ownCtors_getElem?_idx hgr hown, hctor, hname, hnm]
    rfl
  have hfrC : ∀ n ∈ ctorsR.flatten.map (fun c => c.1.name),
      (consNestedFormersF (List.take p.k stored) fe).env.find? n = none := by
    intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
    obtain ⟨mm, hmm⟩ := List.getElem?_of_mem hl
    obtain ⟨-, -, hfresh, -⟩ := hctorsR.2 mm l hmm
    rw [← h₁.find?]
    exact hfresh c hcl
  have h₂ : PushChain env
      (consNestedCtorsF ctorsR.flatten (consNestedFormersF (List.take p.k stored) fe)) :=
    consNestedCtorsF_push h₁ ⟨hndC, hfrC⟩
  -- (3) THE RESTORED RECURSORS' CONS: the names are the route's own
  -- (`T_m.rec` and the mimics'), and they are distinct because the
  -- block's members are — K.39's content, which a `certOnly` Bool
  -- could not supply (it is `true` in trusted mode)
  have hlenS : stored.length = p.k + p.numNested := by
    rw [(auxStoredAll_get hst).1,
      auxBlock_k_count_of (by
        have := congrArg List.length hfmsA
        simpa [NestedParts.k] using this) hst0 hb]
    exact congrArg (p.k + ·) (by simpa using hcnt)
  have hndP : p.memberNames.Nodup := by
    rw [← auxBlock_memberNames_of hfmsA hst0 hb]
    exact (List.take_sublist p.k b.memberNames).nodup
      ((List.nodup_append.mp (List.nodup_append.mp hnd).1).1)
  have hndRec := restoredRecNames_nodup_of hndP p.numNested
  apply Yields.letFun
  ybind
  refine Yields.bind' (Yields.and (restoreRecTysF_fresh _ _ _ _ _ (List.take p.k stored))
    (restoreRecTysF_names _ _ _ _ _ (List.take p.k stored)
      (by simp only [List.length_take, List.length_map, List.length_range]; omega)))
    fun cvRms hcvRms => ?_
  refine Yields.bind' (Yields.and (restoreRecTysF_fresh _ _ _ _ _ (List.drop p.k stored))
    (restoreRecTysF_names _ _ _ _ _ (List.drop p.k stored)
      (by simp only [List.length_drop, List.length_map, List.length_range, hlenS]; omega)))
    fun cvRns hcvRns => ?_
  obtain ⟨hfrM, hnmM⟩ := hcvRms
  obtain ⟨hfrN, hnmN⟩ := hcvRns
  have hndStore : ((cvRms.map (·.name)) ++ (cvRns.map (·.name))).Nodup := by
    rw [hnmM, hnmN]
    exact ((List.take_sublist _ _).append (List.take_sublist _ _)).nodup hndRec
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  ybind
  ybind
  ybind
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  rename_i rulesM rulesN _
  -- the stored group's names are a sublist of the restored types' own
  have hsub3 := ((zip_rows_names_sublist
      (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2))
      (fun _ => rfl) cvRms ((List.take p.k stored).zip rulesM)).append
    (zip_rows_names_sublist
      (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2))
      (fun _ => rfl) cvRns ((List.drop p.k stored).zip rulesN)))
  have h₃ : PushChain env (storeNestedRecsF
      ((cvRms.zip ((List.take p.k stored).zip rulesM)).map
          (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2))
        ++ (cvRns.zip ((List.drop p.k stored).zip rulesN)).map
          (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2)))
      (consNestedCtorsF ctorsR.flatten (consNestedFormersF (List.take p.k stored) fe))) := by
    refine storeNestedRecsF_push h₂ ⟨?_, ?_⟩
    · rw [List.map_append]
      exact hsub3.nodup hndStore
    · intro n hn
      rw [List.map_append] at hn
      rw [← h₂.find?]
      rcases List.mem_append.mp (hsub3.subset hn) with hm | hm
      · obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp hm
        exact hfrM cv hcv
      · obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp hm
        exact hfrN cv hcv
  apply Yields.letFun
  ybind
  refine Yields.bind' (nestedTablesF_push structWalkersC _ h₃) fun fe₄ h₄ => ?_
  ybind
  ybind
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  ybind
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  exact Yields.pure h₄

/-! ## The nested route's skeleton (task #315 M8) -/

/-- Post-check (c) at one recursor, read for the rules' constructor
names: the restored rules carry the RECORD's constructors. -/
theorem nestedRecOkF_ctors (ops : CheckerOps CheckCM) (fe : FEnv) (nP k n : Nat)
    (sr : ConstantVal × List RecRule) (own : List (Nat × Nat)) (cvRa : ConstantVal)
    (rules : List RecRule) :
    Yields (nestedRecOkF ops fe nP k n sr own cvRa rules)
      (fun _ => rules.map (·.ctor) = sr.2.map (·.ctor)) := by
  unfold nestedRecOkF
  obtain ⟨cvR, srules⟩ := sr
  simp only []
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  ybind
  ybind
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  refine Yields.ofDecCases (fun _ => Yields.ofThrow) (fun hok => ?_)
  exact Yields.pure (nestedRulesOk_ctors (by simpa using hok))

/-- … and over the whole row list. -/
theorem nestedRecsOkF_ctors (ops : CheckerOps CheckCM) (fe : FEnv) (nP k n : Nat) :
    ∀ (rows : List ((ConstantVal × List RecRule) × List (Nat × Nat) × ConstantVal ×
        List RecRule)),
      Yields (nestedRecsOkF ops fe nP k n rows)
        (fun _ => ∀ (i : Nat) r, rows[i]? = some r →
          r.2.2.2.map (·.ctor) = r.1.2.map (·.ctor))
  | [] => by unfold nestedRecsOkF; exact Yields.pure (by intro i r hr; simp at hr)
  | (sr, own, cvRa, rules) :: rest => by
    unfold nestedRecsOkF
    refine Yields.bind' (nestedRecOkF_ctors ops fe nP k n sr own cvRa rules) fun _ hhead => ?_
    refine Yields.mono (nestedRecsOkF_ctors ops fe nP k n rest) ?_
    intro _ hrest i r hr
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hr; subst hr; exact hhead
    | succ j => exact hrest j r (by simpa using hr)

/-- **THE NESTED ROUTE'S SKELETON** (task #315 M8). -/
theorem checkNestedS_skels (mode : CheckMode) {fe : FEnv} {sk : List InstallSkel}
    (h : SkelIs fe sk) (p : NestedParts) :
    Yields (checkNestedS mode fe p) (fun fe' => SkelIs fe' (nestedSkels p sk)) := by
  unfold checkNestedS
  try ylet
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  ybind
  refine Yields.bind' (nestedAnnotFormersF_names _ _ _ _) fun fmsA hfmsA => ?_
  ybind
  refine Yields.bind' (nestedAnnotCtorsF_names _ _ _) fun ctorsA hctorsA => ?_
  refine Yields.bind' Yields.ofNestedLift fun st hst0 => ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hcnt => ?_)
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  refine Yields.bind' Yields.ofUnwrapOr fun b hb => ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hidx => ?_)
  refine Yields.bind' (Yields.and (Yields.and (checkMutualCoreS_nodup mode fe b none true)
      (checkMutualCoreS_grouped mode fe b none true))
    (checkMutualCoreS_skels mode h b none true)) fun feAux hAux => ?_
  obtain ⟨⟨hnd, hgr⟩, hsk⟩ := hAux
  refine Yields.bind' Yields.ofUnwrapOr fun stored hst => ?_
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  ybind
  ybind
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  -- the read-back's positional facts, and the two length readings
  have htake : ∀ (m : Nat) (a : AuxStored), (List.take p.k stored)[m]? = some a →
      stored[m]? = some a := by
    intro m a ha
    rw [List.getElem?_take] at ha
    split at ha
    · exact ha
    · exact absurd ha (by simp)
  have hlenS : stored.length = p.k + p.numNested := by
    rw [(auxStoredAll_get hst).1,
      auxBlock_k_count_of (by
        have := congrArg List.length hfmsA
        simpa [NestedParts.k] using this) hst0 hb]
    exact congrArg (p.k + ·) (by simpa using hcnt)
  have hlenM : (List.take p.k stored).length = p.k := by
    rw [List.length_take, hlenS]; omega
  -- (1) THE RESTORED FORMERS' NAMES ARE THE BLOCK'S OWN
  have hnamesM : (List.take p.k stored).map (fun a => a.cvTa.name) = p.memberNames := by
    rw [← auxBlock_memberNames_of hfmsA hst0 hb]
    refine List.ext_getElem? ?_
    intro m
    rw [List.getElem?_map]
    by_cases hm : m < p.k
    · have hmS : m < (List.take p.k stored).length := by rw [hlenM]; exact hm
      have hs : (List.take p.k stored)[m]? = some (List.take p.k stored)[m] :=
        List.getElem?_eq_getElem hmS
      obtain ⟨cv, hfm, hnm⟩ := auxStoredAll_cvTa_name hsk hst m _ (htake m _ hs)
      have hRHS : (List.take p.k b.memberNames)[m]? = some cv.name := by
        rw [List.getElem?_take, if_pos hm]
        simp only [MutualBlock.memberNames, List.getElem?_map, hfm]
        rfl
      rw [hs, hRHS]
      exact congrArg some hnm
    · rw [List.getElem?_eq_none_iff.mpr (by rw [hlenM]; omega),
        List.getElem?_eq_none_iff.mpr (by rw [List.length_take]; omega)]
      rfl
  have h₁ : SkelIs (consNestedFormersF (List.take p.k stored) fe)
      (nestedIndSkels (List.take p.k stored) sk) := consNestedFormersF_skels h
  apply Yields.letFun
  ybind
  ybind
  ybind
  ybind
  ybind
  refine Yields.bind' (Yields.mapM_getElem
    (fun a : AuxStored => restoreCtorsF_names _ _ _ _ a.ctors) _) fun ctorsR hctorsR => ?_
  -- (2) EACH MEMBER'S RESTORED CONSTRUCTORS ARE ITS OWN, WITH THE
  -- BLOCK'S PARAMETER COUNT AND THE DECLARED FIELD COUNTS
  have hbridgeC := auxStoredAll_ctor_name hsk hst
  have hnP : b.nP = p.nP := (auxBlock_fields hb).1
  have hmember : ∀ (m : Nat) (l : List (ConstantVal × Nat × Nat)), ctorsR[m]? = some l →
      l.map (fun c => (c.1.name, c.2.1, c.2.2))
        = (p.ctors.filter (fun c => c.member == m)).map
            (fun c => (c.cv.name, p.nP, c.nF)) := by
    intro m l hl
    obtain ⟨a, ha, hnames⟩ := hctorsR.2 m l hl
    have hmlt : m < p.k := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      rw [hlenM] at this; exact this
    have hlenT : (nestedTypes0 p fmsA ctorsA).length = p.k := by
      rw [nestedTypes0_length]
      have := congrArg List.length hfmsA
      simpa [NestedParts.k] using this
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, (nestedTypes0 p fmsA ctorsA)[m]? = some t₀ :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenT]; exact hmlt)⟩
    have hpairs := auxBlock_ownCtors_pairs hctorsA hst0 hb hgr ht₀
    have hstored := (auxStoredAll_get hst).2 m a (htake m a ha)
    rw [hnames]
    refine List.ext_getElem? ?_
    intro j
    rw [List.getElem?_map, List.getElem?_map]
    cases hc : a.ctors[j]? with
    | some c =>
      obtain ⟨J, mc, hown, hn, h1, h2⟩ :=
        auxStoredAll_ctor_data hsk hnd hst m a (htake m a ha) j c hc
      obtain ⟨c', hc', heq⟩ := getElem?_of_map_eq hpairs hown
      rw [hc']
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      have e1 : mc.cv.name = c'.cv.name := congrArg Prod.fst heq
      have e2 : mc.nF = c'.nF := congrArg Prod.snd heq
      exact ⟨by rw [hn, e1], by rw [h1, hnP], by rw [h2, e2]⟩
    | none =>
      have hj : a.ctors.length ≤ j := List.getElem?_eq_none_iff.mp hc
      have hl2 : a.ctors.length = (b.ownCtors m).length := (auxStored?_ctors hstored).1
      have hl3 : (b.ownCtors m).length
          = (p.ctors.filter (fun c => c.member == m)).length := by
        have := congrArg List.length hpairs; simpa using this
      rw [List.getElem?_eq_none_iff.mpr (by omega)]
      rfl
  have h₂ : SkelIs (consNestedCtorsF ctorsR.flatten
      (consNestedFormersF (List.take p.k stored) fe))
      (nestedCtorSkels ctorsR.flatten (nestedIndSkels (List.take p.k stored) sk)) :=
    consNestedCtorsF_skels h₁
  apply Yields.letFun
  ybind
  refine Yields.bind' (restoreRecTysF_names _ _ _ _ _ (List.take p.k stored)
    (by simp only [List.length_take, List.length_map, List.length_range]; omega))
    fun cvRms hcvRms => ?_
  refine Yields.bind' (restoreRecTysF_names _ _ _ _ _ (List.drop p.k stored)
    (by simp only [List.length_drop, List.length_map, List.length_range, hlenS]; omega))
    fun cvRns hcvRns => ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  ybind
  refine Yields.bind' (Yields.mapM_length _) fun rulesM hlenRM => ?_
  refine Yields.bind' (Yields.mapM_length _) fun rulesN hlenRN => ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  ybind
  have h₃ : SkelIs (storeNestedRecsF
      ((cvRms.zip ((List.take p.k stored).zip rulesM)).map
          (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2))
        ++ (cvRns.zip ((List.drop p.k stored).zip rulesN)).map
          (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2)))
      (consNestedCtorsF ctorsR.flatten (consNestedFormersF (List.take p.k stored) fe)))
      (nestedRecSkels
        ((cvRms.zip ((List.take p.k stored).zip rulesM)).map
            (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2))
          ++ (cvRns.zip ((List.drop p.k stored).zip rulesN)).map
            (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2)))
        (nestedCtorSkels ctorsR.flatten (nestedIndSkels (List.take p.k stored) sk))) :=
    storeNestedRecsF_skels h₂
  obtain ⟨preR, hpreR⟩ := nestedSkels_append (List.take p.k stored) ctorsR.flatten
    ((cvRms.zip ((List.take p.k stored).zip rulesM)).map
        (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2))
      ++ (cvRns.zip ((List.drop p.k stored).zip rulesN)).map
        (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2))) sk
  refine Yields.bind' (Yields.and (nestedTablesF_skels structWalkersC _ h₃)
    (nestedTablesF_fresh structWalkersC (sk := sk) (pre := preR) _
      (by rw [← hpreR]; exact h₃))) fun fe₄ hfe₄ => ?_
  obtain ⟨hsk₄, hfresh₄⟩ := hfe₄
  ybind
  ybind
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hcount => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hnums => ?_)
  apply Yields.letFun
  refine Yields.bind' (nestedRecsOkF_ctors _ _ _ _ _ _) fun _ hrules => ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  refine Yields.pure ?_
  -- the four transports from the read-back's lists to the block record's
  have hmemName : ∀ i, i < p.k → p.memberNames[i]? = some (p.formers.getD i default).1.name := by
    intro i hi
    have hi' : i < p.formers.length := by simpa [NestedParts.k] using hi
    simp only [NestedParts.memberNames, List.getElem?_map, List.getElem?_eq_getElem hi',
      List.getD_eq_getElem?_getD, Option.map_some]
    rfl
  have hE1 : nestedIndSkels (List.take p.k stored) sk
      = (List.range p.k).foldl
        (fun acc m => InstallSkel.ind (p.formers.getD m default).1.name :: acc) sk := by
    unfold nestedIndSkels
    refine foldl_step_congr (F := fun (a : AuxStored) acc => InstallSkel.ind a.cvTa.name :: acc)
      (G := fun (m : Nat) acc => InstallSkel.ind (p.formers.getD m default).1.name :: acc)
      (by rw [hlenM, List.length_range]) ?_ sk
    intro i a m ha hm acc
    obtain ⟨cv, hn, hnm⟩ := getElem?_of_map_eq hnamesM ha
    have hmi : m = i := by
      have := List.getElem?_eq_some_iff.mp hm
      simpa using this.2.symm
    subst hmi
    have hget : p.formers.getD m default = cv := by
      rw [List.getD_eq_getElem?_getD, hn]; rfl
    rw [hnm, hget]
  have hE2 : ∀ X, nestedCtorSkels ctorsR.flatten X
      = (List.range p.k).foldl (fun acc m => nestedCtorSkelsAt p m acc) X := by
    intro X
    rw [nestedCtorSkels_flatten]
    refine foldl_step_congr
      (F := fun (l : List (ConstantVal × Nat × Nat)) acc => nestedCtorSkels l acc)
      (G := fun (m : Nat) acc => nestedCtorSkelsAt p m acc)
      (by rw [hctorsR.1, hlenM, List.length_range]) ?_ X
    intro i l m hl hm acc
    have hmi : m = i := by
      have := List.getElem?_eq_some_iff.mp hm
      simpa using this.2.symm
    subst hmi
    have hkey := hmember m l hl
    have e1 : ∀ (xs : List (ConstantVal × Nat × Nat)) (acc : List InstallSkel),
        xs.foldl (fun acc c => InstallSkel.ctor c.1.name c.2.1 c.2.2 :: acc) acc
          = (xs.map (fun c => (c.1.name, c.2.1, c.2.2))).foldl
              (fun acc t => InstallSkel.ctor t.1 t.2.1 t.2.2 :: acc) acc := by
      intro xs acc; rw [List.foldl_map]
    have e2 : ∀ (xs : List MutualCtor) (acc : List InstallSkel),
        xs.foldl (fun acc c => InstallSkel.ctor c.cv.name p.nP c.nF :: acc) acc
          = (xs.map (fun c => (c.cv.name, p.nP, c.nF))).foldl
              (fun acc t => InstallSkel.ctor t.1 t.2.1 t.2.2 :: acc) acc := by
      intro xs acc; rw [List.foldl_map]
    show nestedCtorSkels l acc = nestedCtorSkelsAt p m acc
    unfold nestedCtorSkels nestedCtorSkelsAt
    rw [e1, e2, hkey]
  -- (3a) the restored member recursors: name, argument sums, rule constructors
  have hlenCM : cvRms.length = p.k := by
    have := congrArg List.length hcvRms
    simp only [List.length_map, List.length_take, List.length_range, hlenM] at this
    omega
  have hnameM : ∀ (i : Nat) (cv : ConstantVal), cvRms[i]? = some cv →
      cv.name = (p.formers.getD i default).1.name.str "rec" := by
    intro i cv hi
    have hlt : i < p.k := by
      have := (List.getElem?_eq_some_iff.mp hi).1; rw [hlenCM] at this; exact this
    have h1 : (cvRms.map (fun c => c.name))[i]? = some cv.name := by
      rw [List.getElem?_map, hi]; rfl
    rw [hcvRms] at h1
    rw [List.getElem?_take, if_pos (by rw [hlenM]; exact hlt), List.getElem?_map,
      List.getElem?_range hlt] at h1
    simpa using h1.symm
  have hnumsM : ∀ (i : Nat) (a : AuxStored), (List.take p.k stored)[i]? = some a →
      p.memberRecNums.getD i (0, 0) = (a.mI, a.rP) := by
    intro i a hi
    have hnums' : p.memberRecNums
        = (List.take p.k stored).map (fun a => (a.mI, a.rP)) := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hnums
      exact hnums.1
    rw [hnums', List.getD_eq_getElem?_getD, List.getElem?_map, hi]
    rfl
  have hlenRM' : rulesM.length = p.k := by
    rw [hlenRM, List.length_zip, hlenCM, hlenM]; omega
  have hcount' : p.memberRecs.length = cvRms.length ∧ p.mimicRecs.length = cvRns.length := by
    simp only [Bool.and_eq_true, beq_iff_eq] at hcount
    exact hcount
  have hrulesM : ∀ (i : Nat) (rs : List RecRule), rulesM[i]? = some rs →
      rs.map (fun r => r.ctor) = (p.memberRecs.getD i default).2.map (fun r => r.ctor) := by
    intro i rs hrs
    have hlt : i < p.k := by
      have := (List.getElem?_eq_some_iff.mp hrs).1; rw [hlenRM'] at this; exact this
    have hmr : i < p.memberRecs.length := by rw [hcount'.1, hlenCM]; exact hlt
    obtain ⟨sr, hsr⟩ : ∃ sr, p.memberRecs[i]? = some sr := ⟨_, List.getElem?_eq_getElem hmr⟩
    obtain ⟨cv, hcv⟩ : ∃ cv, cvRms[i]? = some cv :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenCM]; exact hlt)⟩
    have hrow : (((p.memberRecs.zip cvRms).zip rulesM).zipIdx)[i]? = some (((sr, cv), rs), i) := by
      rw [List.getElem?_zipIdx,
        zip_getElem?_of _ _ i (sr, cv) rs (zip_getElem?_of _ _ i sr cv hsr hcv) hrs]
      simp
    have hmRows : i < ((p.memberRecs.zip cvRms).zip rulesM).zipIdx.length := by
      simp only [List.length_zipIdx, List.length_zip, hlenCM, hlenRM']
      omega
    have hidx := hrules i _ (by
      rw [List.getElem?_append_left (by simpa using hmRows), List.getElem?_map, hrow]
      rfl)
    simp only at hidx
    rw [hidx, List.getD_eq_getElem?_getD, hsr]
    rfl
  have hE3a : ∀ X, nestedRecSkels ((cvRms.zip ((List.take p.k stored).zip rulesM)).map
        (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2))) X
      = (List.range p.k).foldl (fun acc m => InstallSkel.recr
          ((p.formers.getD m default).1.name.str "rec")
          (p.memberRecNums.getD m (0, 0)).1 (p.memberRecNums.getD m (0, 0)).2
          ((p.memberRecs.getD m default).2.map (fun r => r.ctor)) :: acc) X := by
    intro X
    show List.foldl _ X _ = _
    refine foldl_step_congr
      (F := fun (r : ConstantVal × Nat × Nat × List RecRule) acc =>
        InstallSkel.recr r.1.name r.2.1 r.2.2.1 (r.2.2.2.map (fun x => x.ctor)) :: acc)
      (G := fun (m : Nat) acc => InstallSkel.recr
        ((p.formers.getD m default).1.name.str "rec")
        (p.memberRecNums.getD m (0, 0)).1 (p.memberRecNums.getD m (0, 0)).2
        ((p.memberRecs.getD m default).2.map (fun r => r.ctor)) :: acc)
      ?hlen ?hstep X
    case hlen =>
      simp only [List.length_map, List.length_zip, List.length_range]
      omega
    case hstep =>
    intro i r m hr hm acc
    have hmi : m = i := by
      have := List.getElem?_eq_some_iff.mp hm
      simpa using this.2.symm
    subst hmi
    rw [List.getElem?_map] at hr
    obtain ⟨x, hx, hrx⟩ := Option.map_eq_some_iff.mp hr
    obtain ⟨hcv, hrest⟩ := zip_getElem? _ _ m x hx
    obtain ⟨ha, hrs⟩ := zip_getElem? _ _ m x.2 hrest
    subst hrx
    rw [hnameM m x.1 hcv, hnumsM m x.2.1 ha, hrulesM m x.2.2 hrs]
  -- (3b) the mimics, by the same three readings
  have hlenD : (List.drop p.k stored).length = p.numNested := by
    rw [List.length_drop, hlenS]; omega
  have hlenCN : cvRns.length = p.numNested := by
    have := congrArg List.length hcvRns
    simp only [List.length_map, List.length_take, List.length_range, hlenD] at this
    omega
  have hlenRN' : rulesN.length = p.numNested := by
    rw [hlenRN, List.length_zip, hlenCN, hlenD]; omega
  have hnameN : ∀ (j : Nat) (cv : ConstantVal), cvRns[j]? = some cv →
      cv.name = p.mimicRecName j := by
    intro j cv hj
    have hlt : j < p.numNested := by
      have := (List.getElem?_eq_some_iff.mp hj).1; rw [hlenCN] at this; exact this
    have h1 : (cvRns.map (fun c => c.name))[j]? = some cv.name := by
      rw [List.getElem?_map, hj]; rfl
    rw [hcvRns] at h1
    rw [List.getElem?_take, if_pos (by rw [hlenD]; exact hlt), List.getElem?_map,
      List.getElem?_range hlt] at h1
    simpa using h1.symm
  have hnumsN : ∀ (j : Nat) (a : AuxStored), (List.drop p.k stored)[j]? = some a →
      p.mimicRecNums.getD j (0, 0) = (a.mI, a.rP) := by
    intro j a hj
    have hnums' : p.mimicRecNums
        = (List.drop p.k stored).map (fun a => (a.mI, a.rP)) := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hnums
      exact hnums.2
    rw [hnums', List.getD_eq_getElem?_getD, List.getElem?_map, hj]
    rfl
  have hrulesN : ∀ (j : Nat) (rs : List RecRule), rulesN[j]? = some rs →
      rs.map (fun r => r.ctor) = (p.mimicRecs.getD j default).2.map (fun r => r.ctor) := by
    intro j rs hrs
    have hlt : j < p.numNested := by
      have := (List.getElem?_eq_some_iff.mp hrs).1; rw [hlenRN'] at this; exact this
    have hmr : j < p.mimicRecs.length := by rw [hcount'.2, hlenCN]; exact hlt
    obtain ⟨sr, hsr⟩ : ∃ sr, p.mimicRecs[j]? = some sr := ⟨_, List.getElem?_eq_getElem hmr⟩
    obtain ⟨cv, hcv⟩ : ∃ cv, cvRns[j]? = some cv :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenCN]; exact hlt)⟩
    have hrow : (((p.mimicRecs.zip cvRns).zip rulesN).zipIdx)[j]? = some (((sr, cv), rs), j) := by
      rw [List.getElem?_zipIdx,
        zip_getElem?_of _ _ j (sr, cv) rs (zip_getElem?_of _ _ j sr cv hsr hcv) hrs]
      simp
    have hlenMRows : ((p.memberRecs.zip cvRms).zip rulesM).zipIdx.length = p.k := by
      simp only [List.length_zipIdx, List.length_zip, hlenCM, hlenRM', hcount'.1]
      omega
    have hidx := hrules (p.k + j) _ (by
      rw [List.getElem?_append_right (by simp only [List.length_map, hlenMRows]; omega),
        List.length_map, hlenMRows, show p.k + j - p.k = j from by omega,
        List.getElem?_map, hrow]
      rfl)
    simp only at hidx
    rw [hidx, List.getD_eq_getElem?_getD, hsr]
    rfl
  have hE3b : ∀ Y, nestedRecSkels ((cvRns.zip ((List.drop p.k stored).zip rulesN)).map
        (fun x : ConstantVal × AuxStored × List RecRule => (x.1, x.2.1.mI, x.2.1.rP, x.2.2))) Y
      = (List.range p.numNested).foldl (fun acc j => InstallSkel.recr (p.mimicRecName j)
          (p.mimicRecNums.getD j (0, 0)).1 (p.mimicRecNums.getD j (0, 0)).2
          ((p.mimicRecs.getD j default).2.map (fun r => r.ctor)) :: acc) Y := by
    intro Y
    show List.foldl _ Y _ = _
    refine foldl_step_congr
      (F := fun (r : ConstantVal × Nat × Nat × List RecRule) acc =>
        InstallSkel.recr r.1.name r.2.1 r.2.2.1 (r.2.2.2.map (fun x => x.ctor)) :: acc)
      (G := fun (j : Nat) acc => InstallSkel.recr (p.mimicRecName j)
        (p.mimicRecNums.getD j (0, 0)).1 (p.mimicRecNums.getD j (0, 0)).2
        ((p.mimicRecs.getD j default).2.map (fun r => r.ctor)) :: acc)
      ?hlen ?hstep Y
    case hlen =>
      simp only [List.length_map, List.length_zip, List.length_range]
      omega
    case hstep =>
    intro i r j hr hj acc
    have hji : j = i := by
      have := List.getElem?_eq_some_iff.mp hj
      simpa using this.2.symm
    subst hji
    rw [List.getElem?_map] at hr
    obtain ⟨x, hx, hrx⟩ := Option.map_eq_some_iff.mp hr
    obtain ⟨hcv, hrest⟩ := zip_getElem? _ _ j x hx
    obtain ⟨ha, hrs⟩ := zip_getElem? _ _ j x.2 hrest
    subst hrx
    rw [hnameN j x.1 hcv, hnumsN j x.2.1 ha, hrulesN j x.2.2 hrs]
  -- (4) THE TABLES: the restored table is consed exactly where the
  -- RECORD says the member is structure-like.  The member's index count
  -- is the record's by the block's own check; the table's presence is
  -- the scratch install's skeleton, with the pre-block branch refuted by
  -- the restore's own freshness guard
  have hidxAt : ∀ (i : Nat), i < p.k →
      (b.formers.getD i default).2 = (p.formers.getD i default).2 := by
    intro i hi
    have hmap : p.formers.map (fun f => f.2) = (b.formers.take p.k).map (fun f => f.2) := by
      simpa using hidx
    have hpi : i < p.formers.length := by simpa [NestedParts.k] using hi
    obtain ⟨y, hy, hxy⟩ := getElem?_of_map_eq hmap (List.getElem?_eq_getElem hpi)
    have hby : b.formers[i]? = some y := by
      rw [List.getElem?_take, if_pos hi] at hy; exact hy
    rw [List.getD_eq_getElem?_getD, hby, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hpi]
    exact hxy.symm
  -- the table's presence at member `i`, both ways
  have hmemNd : b.memberNames.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
  have hbUniq : ∀ (i j : Nat), i < b.formers.length → j < b.formers.length →
      (b.formers.getD i default).1.name = (b.formers.getD j default).1.name → i = j := by
    intro i j hi hj hn
    have hget : ∀ (t : Nat) (ht : t < b.formers.length),
        b.memberNames[t]? = some (b.formers.getD t default).1.name := by
      intro t ht
      simp only [MutualBlock.memberNames, List.getElem?_map,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
      rfl
    have h1 := hget i hi
    have h2 := hget j hj
    rw [hn] at h1
    rw [List.Nodup, List.pairwise_iff_getElem] at hmemNd
    obtain ⟨hil, hiv⟩ := List.getElem?_eq_some_iff.mp h1
    obtain ⟨hjl, hjv⟩ := List.getElem?_eq_some_iff.mp h2
    rcases Nat.lt_trichotomy i j with hlt | hlt | hlt
    · exact absurd (hiv.trans hjv.symm) (hmemNd i j hil hjl hlt)
    · exact hlt
    · exact absurd (hjv.trans hiv.symm) (hmemNd j i hjl hil hlt)
  have htblAt : ∀ (i : Nat) (a : AuxStored) (cs : List (ConstantVal × Nat × Nat))
      (c : ConstantVal × Nat × Nat), i < p.k → (List.take p.k stored)[i]? = some a →
      ctorsR[i]? = some cs → cs = [c] →
      (a.tbl.isSome = true ↔ (p.formers.getD i default).2 = 0) := by
    intro i a cs c hi ha hcs hcs1
    have hstored := (auxStoredAll_get hst).2 i a (htake i a ha)
    obtain ⟨cv, hfm, htbl⟩ := auxStored?_tbl_eq hstored
    have hib : i < b.formers.length := (List.getElem?_eq_some_iff.mp hfm).1
    have hfmGetD : b.formers.getD i default = (cv, a.nIdx) := by
      rw [List.getD_eq_getElem?_getD, hfm]; rfl
    have hcvname : cv.name = (p.formers.getD i default).1.name := by
      obtain ⟨cv'', hn'', hnm''⟩ := getElem?_of_map_eq hnamesM ha
      have hgetD : p.formers.getD i default = cv'' := by
        rw [List.getD_eq_getElem?_getD, hn'']; rfl
      obtain ⟨cv', hfm', hnm⟩ := auxStoredAll_cvTa_name hsk hst i a (htake i a ha)
      have hcc : cv = cv' := by
        rw [hfm] at hfm'
        have := Option.some.inj hfm'
        simpa using congrArg Prod.fst this
      rw [hgetD, ← hnm'', hcc, ← hnm]
    have hownLen : (b.ownCtors i).length = 1 := by
      have hkey := hmember i cs hcs
      rw [hcs1] at hkey
      obtain ⟨t₀, ht₀⟩ : ∃ t₀, (nestedTypes0 p fmsA ctorsA)[i]? = some t₀ := by
        refine ⟨_, List.getElem?_eq_getElem ?_⟩
        rw [nestedTypes0_length]
        have hlf := congrArg List.length hfmsA
        simp only [List.length_map] at hlf
        simpa [NestedParts.k] using (hlf ▸ hi)
      have hpairs := auxBlock_ownCtors_pairs hctorsA hst0 hb hgr ht₀
      have h1 := congrArg List.length hpairs
      have h2 := congrArg List.length hkey
      simp only [List.length_map, List.length_cons, List.length_nil] at h1 h2
      omega
    have hrowmem : ∀ t : ProjTable, a.tbl = some t →
        ((p.formers.getD i default).1.name, some t, cs) ∈
          (((List.take p.k stored).zip ctorsR).zipIdx.map
            (fun x : (AuxStored × List (ConstantVal × Nat × Nat)) × Nat =>
              ((p.formers.getD x.2 default).1.name, x.1.1.tbl, x.1.2))) := by
      intro t ht
      refine List.mem_map.mpr ⟨((a, cs), i), ?_, by rw [ht]⟩
      exact List.mk_mem_zipIdx_iff_getElem?.mpr (zip_getElem?_of _ _ i a cs ha hcs)
    constructor
    · intro hsome
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
      have hfind : feAux.env.find? (projTableName cv.name) = some (.projInfo t) := by
        rw [htbl] at ht
        split at ht
        · rename_i tt hft; rw [hft]; simpa using ht
        · exact nomatch ht
      have hskf := hsk.env_find? (projTableName cv.name)
      rw [hfind] at hskf
      rcases mutualBlockSkels_proj_cases (by simpa using hskf.symm) with
        ⟨m', hm', hnm', hown', hidx'⟩ | hsk0
      · have hmi : m' = i := hbUniq m' i hm' hib (by rw [hnm', hfmGetD])
        subst hmi
        rw [← hidxAt m' hi, hidx']
      · exfalso
        have hnone := hfresh₄ _ t c (by rw [← hcs1]; exact hrowmem t ht)
        rw [hcvname] at hsk0
        rw [hnone] at hsk0
        exact nomatch hsk0
    · intro hzero
      have hhit := mutualBlockSkels_proj_hit (b := b) (sk := sk) (m := i)
        (T := cv.name) hib (by rw [hfmGetD]) hownLen
        (by rw [← hidxAt i hi] at hzero; exact hzero)
      have hskf := hsk.env_find? (projTableName cv.name)
      rw [hhit] at hskf
      cases hfind : feAux.env.find? (projTableName cv.name) with
      | none => rw [hfind] at hskf; exact nomatch hskf
      | some ci =>
        rw [hfind] at hskf
        obtain ⟨tbl, rfl, -⟩ := proj_of_ciSkel (by simpa using hskf)
        rw [htbl, hfind]
        rfl
  have hE4 : ∀ Z, (((List.take p.k stored).zip ctorsR).zipIdx.map
        (fun x : (AuxStored × List (ConstantVal × Nat × Nat)) × Nat =>
          ((p.formers.getD x.2 default).1.name, x.1.1.tbl, x.1.2))).foldl
        (fun acc t => nestedTableSkel t.1 t.2.1 t.2.2 acc) Z
      = (List.range p.k).foldl (fun acc m => nestedTableSkelAt p m acc) Z := by
    intro Z
    refine foldl_step_congr
      (F := fun (t : Name × Option ProjTable × List (ConstantVal × Nat × Nat)) acc =>
        nestedTableSkel t.1 t.2.1 t.2.2 acc)
      (G := fun (m : Nat) acc => nestedTableSkelAt p m acc) ?hlen ?hstep Z
    case hlen =>
      simp only [List.length_map, List.length_zipIdx, List.length_zip, List.length_range,
        hlenM, hctorsR.1]
      omega
    case hstep =>
    intro i t m ht hm acc
    have hmi : m = i := by
      have := List.getElem?_eq_some_iff.mp hm
      simpa using this.2.symm
    subst hmi
    rw [List.getElem?_map] at ht
    obtain ⟨x, hx, hrx⟩ := Option.map_eq_some_iff.mp ht
    rw [List.getElem?_zipIdx] at hx
    obtain ⟨y, hy, hxy⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨ha, hcs⟩ := zip_getElem? _ _ m y hy
    have hlt : m < p.k := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      rw [hlenM] at this; exact this
    subst hxy
    subst hrx
    have hkey := hmember m y.2 hcs
    have hlenEq : y.2.length = (p.ctors.filter (fun c => c.member == m)).length := by
      have := congrArg List.length hkey; simpa using this
    show nestedTableSkel _ y.1.tbl y.2 acc = nestedTableSkelAt p m acc
    simp only [Nat.zero_add]
    unfold nestedTableSkel nestedTableSkelAt
    rcases hcsv : y.2 with _ | ⟨c0, cs'⟩ <;>
      rcases hfv : p.ctors.filter (fun c => c.member == m) with _ | ⟨c1, fs'⟩ <;>
      rw [hfv] <;>
      simp only [hcsv, hfv, List.length_cons, List.length_nil] at hlenEq
    · cases y.1.tbl <;> rfl
    · exact absurd hlenEq (by simp)
    · exact absurd hlenEq (by simp)
    · rcases cs' with _ | ⟨c2, cs''⟩ <;> rcases fs' with _ | ⟨c3, fs''⟩ <;>
        simp only [List.length_cons, List.length_nil] at hlenEq
      · -- both singletons: the tables' presence decides, and it is the
        -- record's index count by `htblAt`
        have hiff := htblAt m y.1 y.2 c0 hlt ha hcs hcsv
        cases htb : y.1.tbl with
        | none =>
          have : ¬ ((p.formers.getD m default).2 = 0) := by
            intro h0
            have := hiff.mpr h0
            rw [htb] at this
            exact nomatch this
          simp only []
          rw [if_neg (by simpa using this)]
        | some tt =>
          have h0 : (p.formers.getD m default).2 = 0 := hiff.mp (by rw [htb]; rfl)
          simp only []
          rw [if_pos (by simpa using h0)]
      · exact absurd hlenEq (by simp)
      · exact absurd hlenEq (by simp)
      · cases y.1.tbl <;> rfl
  rw [nestedRecSkels_append, hE1, hE2, hE3a, hE3b, hE4] at hsk₄
  unfold nestedSkels
  exact hsk₄

/-! ## The declaration clause and the two drivers' steps -/

theorem installBasisDeclF_push {env : Env} {fe : FEnv} (h : PushChain env fe)
    (ci : ConstantInfo) :
    Yields (installBasisDeclF (m := CheckCM) fe ci)
      (fun fe' => PushChain env fe') := by
  unfold installBasisDeclF
  yields
  all_goals exact Yields.pure (h.push (Option.isNone_iff_eq_none.mp (by assumption)))

/-- The pinned-block install pushes onto the chain (task #293: three of
`checkDeclC`'s arms share this body). -/
theorem checkBasisDeclC_push {env : Env} {fe : FEnv}
    (h : PushChain env fe) (kind : BasisKind) :
    Yields (checkBasisDeclC mode fe kind) (fun fe' => PushChain env fe') := by
  have hfold : ∀ (fe' : FEnv), PushChain env fe' →
      Yields (kind.declsA.foldlM installBasisDeclF fe')
        (fun x => PushChain env x) :=
    fun fe' h' =>
      Yields.foldlM_rel (R := fun fe (_ : Unit) => PushChain env fe)
        (g := fun u _ => u)
        (fun acc ci _ hacc => installBasisDeclF_push hacc ci)
        kind.declsA fe' () h'
  -- the fold by its OWN rule, then K.49's gate (which only throws)
  have htail : Yields
      (do
        let fe₂ ← kind.declsA.foldlM installBasisDeclF fe
        unless certOnly mode (basisOwnMimicsOk fe₂.env kind.declsA) do
          throw (CheckError.internal "basis: the pinned block carries a mimic recursor")
        pure fe₂)
      (fun fe' => PushChain env fe') := by
    refine Yields.bind' (hfold fe h) (fun fe₂ hfe₂ => ?_)
    yields
    all_goals exact Yields.pure hfe₂
  unfold checkBasisDeclC
  refine Yields.letFun ?_
  repeat' first
    | exact htail
    | yields_step

theorem checkDeclC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (pd : Declaration) :
    Yields (checkDeclC mode pins fe pd) (fun fe' => PushChain env fe') := by
  unfold checkDeclC
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    obtain ⟨hp, hfr⟩ := hp
    simp only []
    have key : Yields (checkDefnValC mode fe cvA jty value hint)
        (fun fe' => PushChain env fe') :=
      checkDefnValC_push mode h (by show fe.find? cvA.name = none; rw [hp]; exact hfr)
        jty value hint
    split
    · refine Yields.bind' key fun fe2 h2 => ?_
      yields
      all_goals (apply Yields.pure; exact h2)
    · exact key
  | thmDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    obtain ⟨hp, hfr⟩ := hp
    exact checkThmValC_push mode h
      (by show fe.find? cvA.name = none; rw [hp]; exact hfr) jty value
  | opaqueDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    obtain ⟨hp, hfr⟩ := hp
    simp only []
    have key : Yields (checkOpaqueValC mode fe cvA jty value)
        (fun fe' => PushChain env fe') :=
      checkOpaqueValC_push mode h
        (by show fe.find? cvA.name = none; rw [hp]; exact hfr) jty value
    split
    · refine Yields.bind' key fun fe2 h2 => ?_
      yields
      all_goals (apply Yields.pure; exact h2)
    · exact key
  | axiomDecl cv =>
    simp only []
    -- task #293: `Quot.sound` is compared with the pin and pushes
    -- nothing
    split
    · split
      · exact Yields.pure h
      · exact Yields.ofThrow
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    obtain ⟨hp, hfr⟩ := hp
    simp only []
    have hfrA : fe.find? cvA.name = none := by rw [hp]; exact hfr
    by_cases ht : cvA.name = sorryAxName
    · rw [if_neg (by rw [tolerated_not_std fe cvA ht]; exact Bool.false_ne_true),
        if_neg (tolerated_ne_trust ht), if_neg (tolerated_ne_ofReduce ht),
        if_neg (tolerated_ne_std ht), if_pos ht]
      exact Yields.pure h
    · rw [if_neg ht]
      yields
      all_goals first
        | (apply Yields.pure; exact h.push hfrA)
        | exact absurd (by assumption) ht
  | basisDecl kind => exact checkBasisDeclC_push h kind
  | quotDecl k cv =>
    -- task #293: the `type` record installs the pinned block, the other
    -- members install nothing
    simp only []
    cases k <;>
      (split
       · first
         | exact checkBasisDeclC_push h .quotK
         | exact Yields.pure h
       · exact Yields.ofThrow)
  | indDecl block nP =>
    simp only []
    -- task #293: a block the fold recognises as a pinned one installs
    -- the pin
    split
    · exact checkBasisDeclC_push h _
    · split
      · cases nativeParts? nP block with
        | none =>
          cases hmp : mutualParts? nP block with
          | none => exact checkIndDeclSF_push mode h block
          | some q => exact checkMutualS_push mode h q (mutualParts?_recPinned hmp)
        | some p => exact checkNativeS_push mode h p
      · exact Yields.ofThrow

theorem checkDeclStepC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (pd : Declaration) :
    Yields (checkDeclStepC mode pins fe pd) (fun fe' => PushChain env fe') := by
  unfold checkDeclStepC
  ybind
  exact checkDeclC_push mode h pd

/-- Phase A's step body: a fresh chain, and the pending records grow
by at most the one it may push. -/
theorem annotStepC_push (mode : CheckMode) (i : Nat) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (pend : Array PendingCheck) (pd : Declaration) :
    Yields (annotStepC mode pins i fe pend pd)
      (fun r => PushChain env r.1 ∧ ∃ new, r.2.toList = pend.toList ++ new) := by
  have hord : ∀ pd', Yields (do pure (← checkDeclStepC mode pins fe pd', pend) :
      CheckCM (FEnv × Array PendingCheck))
      (fun r => PushChain env r.1 ∧ ∃ new, r.2.toList = pend.toList ++ new) :=
    fun pd' => Yields.bind' (checkDeclStepC_push mode h pd') fun fe' h' =>
      Yields.pure ⟨h', [], by simp⟩
  unfold annotStepC
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    split
    · exact hord _
    · refine Yields.bind' (annotValueC_fresh mode fe cv value true) fun r hr => ?_
      obtain ⟨cvA, jty, jv⟩ := r
      obtain ⟨hp, hfr⟩ := hr
      exact Yields.pure ⟨h.push (by show fe.find? cvA.name = none; rw [hp]; exact hfr), _,
        Array.toList_push⟩
  | thmDecl cv value =>
    simp only []
    ybind
    refine Yields.bind' (annotConstantValC_fresh mode fe cv) fun p hr => ?_
    obtain ⟨cvA, jty⟩ := p
    obtain ⟨hp, hfr⟩ := hr
    ybind
    exact Yields.pure ⟨h.push (by show fe.find? cvA.name = none; rw [hp]; exact hfr), _,
      Array.toList_push⟩
  | opaqueDecl cv value =>
    simp only []
    split
    · exact hord _
    · refine Yields.bind' (annotValueC_fresh mode fe cv value false) fun r hr => ?_
      obtain ⟨cvA, jty, jv⟩ := r
      obtain ⟨hp, hfr⟩ := hr
      exact Yields.pure ⟨h.push (by show fe.find? cvA.name = none; rw [hp]; exact hfr), _,
        Array.toList_push⟩
  | axiomDecl cv => exact hord _
  | basisDecl kind => exact hord _
  | quotDecl k cv => exact hord _
  | indDecl block nP => exact hord _

/-- **Phase A is a fresh chain**: from a canonical index, an accepting
run returns a canonical index whose constants extend the start by
fresh names, and the pending records extend the start's. -/
theorem installRun_trace (mode : CheckMode) {ds : List Declaration} {env : Env}
    {p : Nat × FEnv × Array PendingCheck} {s : CState}
    {q : Nat × FEnv × Array PendingCheck} {s' : CState}
    (h : InstallRun mode pins ds p s q s') (hp : PushChain env p.2.1) :
    PushChain env q.2.1 ∧ ∃ new, q.2.2.toList = p.2.2.toList ++ new := by
  induction h with
  | nil p s => exact ⟨hp, [], by simp⟩
  | @cons pd ds p p₁ q s s₁ s' hstep rest ih =>
    obtain ⟨fe₁, pend₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    obtain ⟨h₁, new₁, hpend₁⟩ :=
      annotStepC_push mode p.1 hp p.2.2 _ s (fe₁, pend₁) _ hstepC
    obtain ⟨h₂, new₂, hpend₂⟩ := ih h₁
    exact ⟨h₂, new₁ ++ new₂, by rw [hpend₂, hpend₁, List.append_assoc]⟩

end ConLeche.Cached
