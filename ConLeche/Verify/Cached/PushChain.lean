module

public import ConLeche.Verify.Cached.AgreeFloor
public import ConLeche.Verify.EnvBound
import ConLeche.Verify.EnvWF
import ConLeche.Verify.CheckerF

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
  exact checkNativeTableF_push hpush q.p q.ctorsA q.sortss

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

/-- Two readings of the same action. -/
theorem Yields.and {α : Type} {m : CheckCM α} {P Q : α → Prop}
    (hP : Yields m P) (hQ : Yields m Q) : Yields m (fun a => P a ∧ Q a) :=
  fun s a s' hr => ⟨hP s a s' hr, hQ s a s' hr⟩

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

/-- The formers' checks: every member's name is the declared one and
is fresh at the block's starting index (the stage checks them ALL
there — official's `check_inductive_types` runs before
`declare_inductive_types`). -/
theorem mutualFormerChecksS_fresh (mode : CheckMode) (nP : Nat) :
    ∀ (fs : List (ConstantVal × Nat)) {fe : FEnv},
      Yields (mutualFormerChecksS mode fe nP fs)
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
    Yields (mutualFormersS mode nP fs fe) (fun r => PushChain env r.1) := by
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
  refine Yields.bind' (normCtorValMF_name ops fe memberNames nP nF cvC cvCa₀ hn₀)
    fun cvCa hn => ?_
  yields
  all_goals (apply Yields.pure; exact ⟨hn, hfr⟩)

/-- Every stored constructor is fresh at the formers' environment. -/
theorem checkMutualCtorsF_fresh (ops : CheckerOps CheckCM) (w : StructWalkers) (fe : FEnv)
    (b : MutualBlock) (fms : List MutualFormerA) (isProp : Bool) :
    ∀ (cs : List MutualCtor),
      Yields (checkMutualCtorsF ops w fe b fms isProp cs)
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
    Yields (checkMutualCoreS mode fe b (some rs)) (fun fe' => PushChain env fe') := by
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
      (checkMutualCtorsF_names (sharedOpsC mode fe₁) structWalkersC fe₁ b fms _ b.ctors))
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
  refine Yields.mono (mutualTablesF_push structWalkersC b ctorsA sortss fms.zipIdx
    (storeMutualRecsF_push (consMutualCtorsF b.nP ctorsA fe₁) b fms _ cvRas.zipIdx h₂ ⟨?_, ?_⟩))
    (fun _ h' => h')
  · rw [show cvRas.zipIdx.map (fun c => c.1.name) = cvRas.map (·.name) from
      map_fst_zipIdx (·.name) cvRas 0, hnR]
    exact nodup_recs_of_blockNames hnd
  · intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    rw [← h₂.find?]
    exact hfrR c.1 (fst_mem_of_mem_zipIdx hc)

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
    Yields (checkBasisDeclC fe kind) (fun fe' => PushChain env fe') := by
  have hfold : ∀ (fe' : FEnv), PushChain env fe' →
      Yields (kind.declsA.foldlM installBasisDeclF fe')
        (fun x => PushChain env x) :=
    fun fe' h' =>
      Yields.foldlM_rel (R := fun fe (_ : Unit) => PushChain env fe)
        (g := fun u _ => u)
        (fun acc ci _ hacc => installBasisDeclF_push hacc ci)
        kind.declsA fe' () h'
  unfold checkBasisDeclC
  yields
  all_goals exact hfold fe h

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
