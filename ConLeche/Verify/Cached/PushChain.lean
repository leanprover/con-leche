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
    (h : PushChain env fe) (nPd : Nat) (block : List ConstantInfo) :
    Yields (checkIndDeclSF mode fe nPd block)
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

theorem checkStructProjTableF_push {w : StructWalkers} {env : Env} {fe : FEnv}
    (h : PushChain env fe) (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal) :
    Yields (checkStructProjTableF (m := CheckCM) w T C lps nP nF resSort guards
        off cvCa fe)
      (fun fe' => PushChain env fe') := by
  unfold checkStructProjTableF
  yields
  all_goals exact Yields.pure (h.push (Option.isNone_iff_eq_none.mp (by assumption)))

/-! ## The uniform route at k members (lane FLIP1)

The k-ary install pushes the k formers, then every member's
constructors, then the k recursors, then a table per structure-like
member.  Every push is fresh: the formers and the constructors by their
own stages' lookups and the install's distinct-name guard, the
recursors by the type stage's lookup (at the constructors' index) and —
for the k names among themselves — by the recursor NAME-SET check
(`blockRecNameSetOk`), which with the members' own distinct names is a
pigeonhole.  Unlike the skeleton, the chain does not depend on which
recursor stage the gate selects: both arms are closed. -/

/-- The formers' conses: a fresh chain. -/
theorem consBlockIndsF_push (p₁ : BlockShape) (isRec : Bool) {env : Env} :
    ∀ {cvTas : List ConstantVal} {i : Nat} {fe : FEnv}, PushChain env fe →
      FreshNames fe.env (cvTas.map (·.name)) →
      PushChain env (consBlockIndsF p₁ isRec cvTas i fe)
  | [], _, _, h, _ => h
  | cvTa :: rest, i, fe, h, hf => by
    have hfr : fe.find? cvTa.name = none := by
      rw [h.find?]; exact hf.2 _ (by simp)
    exact consBlockIndsF_push p₁ isRec (cvTas := rest) (i := i + 1)
      (h.push (ci := .indInfo cvTa (blockCapsAt p₁ i isRec)) hfr)
      (FreshNames.step (c := .indInfo cvTa (blockCapsAt p₁ i isRec)) hf)

/-- One pass at k members: the formers' conses keep the chain, and the
constructors are the block's by name, fresh at the formers'
environment. -/
theorem checkBlockPassS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (p₀ : BlockParts) (isRec : Bool)
    (hnd : (p₀.members.map (·.cvT.name)).Nodup) :
    Yields (checkBlockPassS mode fe p₀ isRec)
      (fun r => PushChain env r.1.env₁ ∧ r.1.p.members = p₀.members ∧
        (r.1.ctorsAs.flatten.map (·.1.name)) = p₀.allCtors.map (·.1.name) ∧
        ∀ c ∈ r.1.ctorsAs.flatten, r.1.env₁.find? c.1.name = none) := by
  unfold checkBlockPassS
  refine Yields.bind' (checkBlockIndsF_fresh _ fe p₀ isRec) fun r₁ h₁ => ?_
  obtain ⟨fe₁, cvTas, p₁⟩ := r₁
  obtain ⟨⟨s, hps⟩, hfe₁, hn, hfr⟩ := h₁
  try simp only [] at hps hfe₁ hn hfr
  subst hps
  try simp only []
  have h₁ : PushChain env fe₁ := by
    rw [hfe₁]
    refine consBlockIndsF_push _ isRec h ⟨by rw [hn]; exact hnd, ?_⟩
    intro n hn'
    rw [hn] at hn'
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hn'
    rw [← h.find?]
    exact hfr ms hms
  ybind
  have hlen : (p₀.members.zip cvTas).map (fun x => x.1) = p₀.members := by
    have := congrArg List.length hn
    simp only [List.length_map] at this
    rw [List.map_fst_zip (by omega)]
  refine Yields.bind fun ctx => ?_
  refine Yields.bind' (checkBlockCtorsF_fresh _ fe₁ fe₁ _ _ _) fun r hr => ?_
  obtain ⟨ctorsAs, sortsss⟩ := r
  obtain ⟨hns, -, hfrs⟩ := hr
  try simp only []
  refine Yields.bind fun kinds => ?_
  refine Yields.pure ⟨h₁, rfl, ?_, ?_⟩
  · simp only [BlockParts.complete_members, BlockShape.withSort_members] at hns
    have := congrArg (fun l => (l.map (List.map Prod.fst)).flatten) hns
    simp only [List.map_map, Function.comp_def] at this
    simp only [List.map_flatten, BlockShape.allCtors]
    rw [this]
    conv => rhs; rw [← hlen]
    simp only [List.map_map, Function.comp_def]
  · intro c hc
    obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
    exact hfrs cs hcs c hc

/-- **The pigeonhole**: a list as long as a `Nodup` list it covers is
itself `Nodup` (the Verify-tier twin of the model's
`nodup_of_subset_length`, `Model/Inductives/BlockRecAssembly.lean`). -/
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

/-- The recursor stage stores fresh, distinct names: the target check
stores one recursor per record, under the record's name, fresh at the
constructors' index (the type stage's lookup) and pairwise distinct
(the name-set check, `blockRecNameSetOk_nodup`) — through the
reject-only conformance check after it. -/
theorem checkBlockRecS_fresh (mode : CheckMode) (fe : FEnv) (p : BlockParts)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat)))
    (hnd : (p.members.map (·.cvT.name)).Nodup) :
    Yields (checkBlockRecS mode fe p block cvTas ctorsAs)
      (fun rs => (rs.map (·.1.name)).Nodup ∧ ∀ r ∈ rs, fe.find? r.1.name = none) := by
  unfold checkBlockRecS
  refine Yields.thenConform (Yields.bind' (targetRecCheck_member (shadowOpsC mode) fe
    p.toBlockShape false block cvTas ctorsAs) fun out hout => Yields.pure ?_)
  obtain ⟨hset, hlen, hall⟩ := hout
  have hnames : (tgtRs out).map (·.1.name) = p.recs.map (·.cvR.name) := by
    apply List.ext_getElem?
    intro j
    simp only [tgtRs, List.map_map, List.getElem?_map]
    cases hj : p.recs[j]? with
    | none =>
      have : out[j]? = none := by
        rw [List.getElem?_eq_none_iff] at hj ⊢
        have : p.toBlockShape.recs.length = p.recs.length := rfl
        omega
      simp [this]
    | some rc =>
      obtain ⟨o, hoj, hname, -⟩ := hall j rc hj
      simp [hoj, hname]
  refine ⟨by rw [hnames]; exact blockRecNameSetOk_nodup hset hnd, ?_⟩
  intro r hr
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hr
  simp only [tgtRs, List.getElem?_map] at hj
  cases hoj : out[j]? with
  | none => rw [hoj] at hj; exact nomatch hj
  | some o =>
    rw [hoj] at hj
    obtain rfl := Option.some.inj hj
    have hjl : j < p.recs.length := by
      have := (List.getElem?_eq_some_iff.mp hoj).1
      have h2 : p.toBlockShape.recs.length = p.recs.length := rfl
      omega
    obtain ⟨o', hoj', hname, hfr, -⟩ := hall j p.recs[j] (List.getElem?_eq_getElem hjl)
    rw [hoj] at hoj'
    obtain rfl := Option.some.inj hoj'
    show fe.find? o.1.name = none
    rw [hname]; exact hfr

/-- The recursors' conses: a fresh chain. -/
theorem consBlockRecsF_push (find? : Name → Option ConstantInfo) (q : BlockShape) (nP : Nat)
    {env : Env} :
    ∀ {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {m : Nat}
      {fe : FEnv}, PushChain env fe → FreshNames fe.env (rs.map (·.1.name)) →
      PushChain env (consBlockRecsF find? q nP m rs fe)
  | [], _, _, h, _ => h
  | (cvRa, rhss, nIdx, ctorsA) :: rest, m, fe, h, hf => by
    have hfr : fe.find? cvRa.name = none := by
      rw [h.find?]; exact hf.2 _ (by simp)
    let ci : ConstantInfo := .recInfo cvRa (q.majorIdxAt m) (q.rulePrefixAt m)
      (sumRules find? cvRa.name nP (q.majorIdxAt m) (q.rulePrefixAt m) cvRa.type ctorsA rhss)
    exact consBlockRecsF_push find? q nP (rs := rest) (m := m + 1) (h.push (ci := ci) hfr)
      (FreshNames.step (c := ci) hf)

/-- The projection tables: every push is guarded by its own lookup. -/
theorem checkBlockTablesF_push {w : StructWalkers} (p : BlockShape) {env : Env} :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) {fe : FEnv},
      PushChain env fe →
      Yields (checkBlockTablesF (m := CheckCM) w p l fe) (fun fe' => PushChain env fe')
  | [], _, h => Yields.pure h
  | (ms, ctorsA, sortss) :: rest, fe, h => by
    unfold checkBlockTablesF
    have key : Yields
        (match ctorsA, sortss with
         | [cA], [sorts] =>
           if ms.nIdx == 0 then
             checkStructProjTableF (m := CheckCM) w ms.cvT.name cA.1.name p.lps p.nP cA.2
               p.resSort (structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 fe
           else pure fe
         | _, _ => pure fe) (fun fe' => PushChain env fe') := by
      split
      · split
        · exact checkStructProjTableF_push h _ _ _ _ _ _ _ _ _
        · exact Yields.pure h
      · exact Yields.pure h
    exact Yields.bind' key fun fe' h' => checkBlockTablesF_push p rest h'

/-- The install after the pass keeps the chain, at either setting of
the recursor stage's gate. -/
theorem checkBlockTailS_push (mode : CheckMode) {env : Env}
    {block : List ConstantInfo} {q : BlockPass FEnv} (h₁ : PushChain env q.env₁)
    (hndC : (q.ctorsAs.flatten.map (·.1.name)).Nodup)
    (hndM : (q.p.members.map (·.cvT.name)).Nodup)
    (hfrs : ∀ c ∈ q.ctorsAs.flatten, q.env₁.find? c.1.name = none) :
    Yields (checkBlockTailS mode block q) (fun fe' => PushChain env fe') := by
  unfold checkBlockTailS
  dsimp only
  split
  · exact Yields.ofThrowBind
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  have h₂ : PushChain env (consBlockCtorsF q.p.nP q.ctorsAs q.env₁) := by
    rw [consBlockCtorsF_flatten]
    refine consSumCtorsF_push q.p.nP h₁ ⟨hndC, ?_⟩
    intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    rw [← h₁.find?]
    exact hfrs c hc
  refine Yields.bind' (checkBlockRecS_fresh mode _ q.p block q.cvTas q.ctorsAs hndM)
    fun rs hrs => ?_
  refine checkBlockTablesF_push _ _ (consBlockRecsF_push _ _ _ h₂ ⟨hrs.1, ?_⟩)
  intro n hn
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hn
  rw [← h₂.find?]
  exact hrs.2 r hr

/-- **The uniform install at k members keeps the chain**, at either
setting of the recursor stage's gate. -/
theorem checkBlockKS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (block : List ConstantInfo) (p : BlockParts) :
    Yields (checkBlockKS mode fe block p) (fun fe' => PushChain env fe') := by
  unfold checkBlockKS
  try apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hnd => ?main)
  case main =>
  ybind
  have hndC : (p.allCtors.map (·.1.name)).Nodup := hnd.1
  have hndM : (p.members.map (·.cvT.name)).Nodup := hnd.2
  refine Yields.bind' (checkBlockPassS_push mode h p (blockRawRec p) hndM) fun r hr => ?_
  obtain ⟨q, settled⟩ := r
  obtain ⟨h₁, hm, hns, hfrs⟩ := hr
  try simp only [] at h₁ hm hns hfrs
  try simp only []
  cases settled with
  | true =>
    simp only [↓reduceIte]
    exact checkBlockTailS_push mode h₁ (by rw [hns]; exact hndC) (by rw [hm]; exact hndM) hfrs
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  ybind
  refine Yields.bind' (checkBlockPassS_push mode h p (nestIsRec q.kinds) hndM)
    fun r' hr' => ?_
  obtain ⟨q', settled'⟩ := r'
  obtain ⟨h₁', hm', hns', hfrs'⟩ := hr'
  try simp only [] at h₁' hm' hns' hfrs'
  try simp only []
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue _ =>
  exact checkBlockTailS_push mode h₁' (by rw [hns']; exact hndC) (by rw [hm']; exact hndM) hfrs'

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
      · cases hbp : blockParts? nP block with
        | none => exact checkIndDeclSF_push mode h _ block
        | some p => exact checkBlockKS_push mode h block p
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
