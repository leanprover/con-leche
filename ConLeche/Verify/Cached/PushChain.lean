module

public import ConLeche.Verify.Cached.AgreeFloor
public import ConLeche.Verify.EnvBound
import ConLeche.Verify.Inductives.StoredRecsInv
import ConLeche.Verify.EnvWF
import ConLeche.Verify.CheckerF

public section

/-!
# Every accepted install is a chain of fresh pushes (task #253)

The two-phase driver (`checkDecls`, `ConLeche/Cached/Installed.lean`)
checks each recorded value against a PREFIX VIEW of the final
environment, `feFinal.restrictTo vis`, and the prefix view's `find?` is
the truncated environment's only under name uniqueness
(`mkFEnv_find?_visibleBelow`, `ConLeche/Verify/EnvBound.lean`).  Name
uniqueness is an install-time invariant: every push a driver step
performs is guarded by a lookup — `checkConstantValC`'s duplicate
guard, `installBasisDeclF`'s — and every table install by a lookup of
its structure — so this file proves, once and OPERATIONALLY (no
environment well-formedness, no simulation: the final-value discipline
of `ConLeche/Verify/Cached/AgreeFloor.lean`), that an accepted step
returns `PushChain env fe'`: a canonical index whose constants extend
`env` by fresh names, and whose tables extend `env`'s by tables of
structures `env` does not store.  Chained from the empty environment, that is
`NodupNames` of every environment a driver ever holds, and the
suffix relation between the environment a declaration was installed at
and the final one.
-/

namespace ConLeche.Cached

open ConLeche

variable {pins : List NatOpPinSet}

/-! ## Fresh chains -/

/-- `fe'` extends `env` by a chain of pushes, each of a name fresh at the
environment it was pushed onto, and of table installs, each of a
structure not in `env` (task #362: a step installs tables for its own
structures only): `fe'` is canonical, `env.consts` is a suffix of its
constants and `env.tables` of its tables, and name uniqueness carries
over. -/
@[expose] def PushChain (env : Env) (fe' : FEnv) : Prop :=
  fe' = mkFEnv fe'.env ∧ (∃ new, fe'.env.consts = new ++ env.consts) ∧
  (NodupNames env → NodupNames fe'.env) ∧
  (∃ newQ, fe'.env.tables = newQ ++ env.tables ∧ ∀ t ∈ newQ, env.find? t.structName = none)

theorem PushChain.refl (env : Env) : PushChain env (mkFEnv env) :=
  ⟨rfl, ⟨[], rfl⟩, id, ⟨[], rfl, fun _ h => nomatch h⟩⟩

theorem PushChain.canon {env : Env} {fe : FEnv} (h : PushChain env fe) :
    fe = mkFEnv fe.env := h.1

/-- A canonical index is a chain from its own environment. -/
theorem PushChain.self {fe : FEnv} (h : fe = mkFEnv fe.env) : PushChain fe.env fe :=
  ⟨h, ⟨[], rfl⟩, id, ⟨[], rfl, fun _ h => nomatch h⟩⟩

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
  obtain ⟨hc, ⟨new, hnew⟩, hnd, hQ⟩ := h
  refine ⟨?_, ⟨ci :: new, ?_⟩, ?_, hQ⟩
  · calc fe.push ci = (mkFEnv fe.env).push ci := by rw [← hc]
      _ = mkFEnv (fe.push ci).env := push_mkFEnv fe.env ci
  · show ci :: fe.env.consts = _
    rw [hnew]
    rfl
  · intro hnd₀
    show ((ci :: fe.env.consts).map (·.name)).Nodup
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, hnd hnd₀⟩
    rw [PushChain.find? ⟨hc, ⟨new, hnew⟩, hnd, hQ⟩] at hfresh
    exact Env.find?_none_notin hfresh

/-- A name the chain's end does not find, its start does not find
either. -/
theorem PushChain.find?_none {env : Env} {fe : FEnv} (h : PushChain env fe) {n : Name}
    (hn : fe.find? n = none) : env.find? n = none := by
  obtain ⟨new, hnew⟩ := h.2.1
  rw [h.find?] at hn
  unfold Env.find? at hn ⊢
  rw [hnew, List.find?_append] at hn
  cases h' : env.consts.find? (·.name == n) with
  | none => rfl
  | some c => rw [h'] at hn; cases new.find? (·.name == n) <;> simp at hn

/-- A table install of a structure not in the chain's start. -/
theorem PushChain.pushTable {env : Env} {fe : FEnv} (h : PushChain env fe)
    {t : ProjTable} (hfresh : env.find? t.structName = none) :
    PushChain env (fe.pushTable t) := by
  obtain ⟨hc, hnew, hnd, ⟨newQ, hQ, hQf⟩⟩ := h
  refine ⟨?_, hnew, hnd, ⟨t :: newQ, ?_, ?_⟩⟩
  · calc fe.pushTable t = (mkFEnv fe.env).pushTable t := by rw [← hc]
      _ = mkFEnv (fe.pushTable t).env := rfl
  · show t :: fe.env.tables = _
    rw [hQ]; rfl
  · intro t' ht'
    rcases List.mem_cons.mp ht' with rfl | hm
    · exact hfresh
    · exact hQf t' hm

/-- A list of names, pairwise distinct and all fresh at `env`: pushing
constants of these names in this order is a fresh chain. -/
def FreshNames (env : Env) (ns : List Name) : Prop :=
  ns.Nodup ∧ ∀ n ∈ ns, env.find? n = none

/-- After pushing the head's constant, the tail is fresh at the
extended environment. -/
theorem FreshNames.step {env : Env} {c : ConstantInfo} {ns : List Name}
    (h : FreshNames env (c.name :: ns)) : FreshNames ⟨c :: env.consts, env.tables⟩ ns := by
  obtain ⟨hnd, hfr⟩ := h
  rw [List.nodup_cons] at hnd
  refine ⟨hnd.2, fun n hn => ?_⟩
  rw [Env.find?_cons, ite_eq_right (fun he => hnd.1 (by rw [he]; exact hn))]
  exact hfr n (List.mem_cons_of_mem _ hn)

/-! ## The generic stage helpers keep the name and record the guard -/

theorem checkConstantValC_fresh (mode : CheckMode) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (checkConstantValC mode fe cv)
      (fun _ => fe.find? cv.name = none) := by
  unfold checkConstantValC
  yields
  all_goals exact Yields.pure (Option.not_isSome_iff_eq_none.mp (by assumption))

/-! ## The constructors' conses -/

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
    (h : PushChain env fe) (T C : Name) (hT : env.find? T = none) (lps : List Name)
    (nP nF : Nat) (resSort : Level) (cvCa : ConstantVal) :
    Yields (checkStructProjTableF (m := CheckCM) w T C lps nP nF resSort cvCa fe)
      (fun fe' => PushChain env fe') := by
  unfold checkStructProjTableF
  yields
  all_goals exact Yields.pure (h.pushTable hT)

/-! ## The block install at k members

The k-ary install pushes the k formers, then every member's
constructors, then the k recursors, then a table per structure-like
member.  Every push is fresh: the formers and the constructors by their
own stages' lookups and the install's distinct-name guard, the
recursors by the type stage's lookup (at the constructors' index) and —
for the k names among themselves — by the recursor NAME-SET check
(`blockRecNameSetOk`), which with the members' own distinct names is a
pigeonhole. -/

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
      (fun r => PushChain env r.env₁ ∧ r.p.members = p₀.members ∧
        (r.ctorsAs.flatten.map (·.1.name)) = p₀.allCtors.map (·.1.name) ∧
        (∀ c ∈ r.ctorsAs.flatten, r.env₁.find? c.1.name = none) ∧
        ∀ ms ∈ p₀.members, env.find? ms.cvT.name = none) := by
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
  refine Yields.bind' (checkBlockCtorsF_fresh _ fe₁ fe₁ _ _) fun r hr => ?_
  obtain ⟨ctorsAs, sortsss⟩ := r
  obtain ⟨hns, -, hfrs⟩ := hr
  try simp only []
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun kinds => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.pure ⟨h₁, rfl, ?_, ?_, fun ms hms => h.find?_none (hfr ms hms)⟩
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

/-- The recursor stage stores fresh, distinct names: the generated stage
stores one recursor per record, under the record's name, fresh at the
constructors' index (the generated constant's lookup) and pairwise
distinct (the record pins). -/
theorem genRecCheckS_fresh (mode : CheckMode) (fe : FEnv)
    (p : BlockParts) (nested : Bool) (params : List Expr) (tbl : List NestCtorNf)
    (rd : ClassRead) (Ms₀ : List TargetMajor)
    (block : List ConstantInfo) (cvTas : List ConstantVal) :
    Yields (genRecCheck (shadowOpsC mode) fe p.toBlockShape nested params tbl rd Ms₀ cvTas block)
      (fun out => (out.map (·.1.name)).Nodup ∧ ∀ o ∈ out, fe.find? o.1.name = none) := by
  refine Yields.mono (genRecCheck_names (shadowOpsC mode) fe
    p.toBlockShape nested params tbl rd Ms₀ cvTas block) fun out hout => ?_
  obtain ⟨hnd, hlen, hall⟩ := hout
  have hnames : out.map (·.1.name) = p.recs.map (·.cvR.name) := by
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_map]
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
  refine ⟨by rw [hnames]; exact hnd, ?_⟩
  intro o ho
  obtain ⟨j, hoj⟩ := List.getElem?_of_mem ho
  have hjl : j < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hoj).1
    have h2 : p.toBlockShape.recs.length = p.recs.length := rfl
    omega
  obtain ⟨o', hoj', hname, hfr⟩ := hall j p.recs[j] (List.getElem?_eq_getElem hjl)
  rw [hoj] at hoj'
  obtain rfl := Option.some.inj hoj'
  rw [hname]; exact hfr

/-- The recursors' pushes at their majors: a fresh chain. -/
theorem pushAll_blockRecInfosTF_push (q : BlockShape) {env : Env} :
    ∀ {out : List (ConstantVal × TargetMajor × List Expr)} {m : Nat}
      {fe : FEnv}, PushChain env fe → FreshNames fe.env (out.map (·.1.name)) →
      PushChain env (FEnv.pushAll (blockRecInfosTF q m out) fe)
  | [], _, _, h, _ => h
  | (cv, M, rhss) :: rest, m, fe, h, hf => by
    have hfr : fe.find? cv.name = none := by
      rw [h.find?]; exact hf.2 _ (by simp)
    let ci : ConstantInfo := .recInfo cv (q.majorIdxAt m) (q.rulePrefixAt m)
      (recKExpected q M) (tgtStoredRules (q.rulePrefixAt m) M rhss)
    exact pushAll_blockRecInfosTF_push q (out := rest) (m := m + 1)
      (h.push (ci := ci) hfr) (FreshNames.step (c := ci) hf)

/-- The projection tables: every install is of a member, a structure the
block's own step pushed. -/
theorem checkBlockTablesF_push {w : StructWalkers} (p : BlockShape) {env : Env} :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) {fe : FEnv},
      PushChain env fe → (∀ x ∈ l, env.find? x.1.cvT.name = none) →
      Yields (checkBlockTablesF (m := CheckCM) w p l fe) (fun fe' => PushChain env fe')
  | [], _, h, _ => Yields.pure h
  | (ms, ctorsA, sortss) :: rest, fe, h, hl => by
    unfold checkBlockTablesF
    have key : Yields
        (match ctorsA, sortss with
         | [cA], [_] =>
           if ms.nIdx == 0 then
             checkStructProjTableF (m := CheckCM) w ms.cvT.name cA.1.name p.lps p.nP cA.2
               p.resSort cA.1 fe
           else pure fe
         | _, _ => pure fe) (fun fe' => PushChain env fe') := by
      split
      · split
        · exact checkStructProjTableF_push h _ _ (hl _ List.mem_cons_self) _ _ _ _ _
        · exact Yields.pure h
      · exact Yields.pure h
    exact Yields.bind' key fun fe' h' =>
      checkBlockTablesF_push p rest h' fun x hx => hl x (List.mem_cons_of_mem _ hx)

/-- The install after the pass keeps the chain. -/
theorem checkBlockTailS_push (mode : CheckMode) {env : Env}
    {block : List ConstantInfo} {q : BlockPass FEnv} (h₁ : PushChain env q.env₁)
    (hndC : (q.ctorsAs.flatten.map (·.1.name)).Nodup)
    (hfrs : ∀ c ∈ q.ctorsAs.flatten, q.env₁.find? c.1.name = none)
    (hmem : ∀ ms ∈ q.p.members, env.find? ms.cvT.name = none) :
    Yields (checkBlockTailS mode block q) (fun fe' => PushChain env fe') := by
  obtain ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, params, rd, cls, tbl⟩ := q
  dsimp only at h₁ hndC hfrs ⊢
  unfold checkBlockTailS
  dsimp only
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  have h₂ : PushChain env (consBlockCtorsF p.nP ctorsAs env₁) := by
    rw [consBlockCtorsF_flatten]
    refine consSumCtorsF_push p.nP h₁ ⟨hndC, ?_⟩
    intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    rw [← h₁.find?]
    exact hfrs c hc
  refine Yields.bind' (Yields.and (genRecCheckS_fresh mode _ p _ _ _ _ _ block cvTas)
      (genRecCheck_names (shadowOpsC mode) _ p.toBlockShape _ _ _ _ _ cvTas block))
    fun out hrs => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  have hnm := storedOut_map_name (recs := p.recs) hrs.2.2.1
  refine checkBlockTablesF_push _ _ (pushAll_blockRecInfosTF_push _ h₂ ⟨?_, ?_⟩)
    (fun x hx => hmem x.1 (List.of_mem_zip hx).1)
  · rw [hnm]; exact hrs.1.1
  intro n hn
  rw [hnm] at hn
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hn
  rw [← h₂.find?]
  exact hrs.1.2 r hr

/-- **The uniform install at k members keeps the chain**. -/
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
  refine Yields.bind' (checkBlockPassS_push mode h p (blockRawRec p) hndM) fun q hr => ?_
  obtain ⟨h₁, hm, hns, hfrs, hmem⟩ := hr
  try simp only [] at h₁ hm hns hfrs hmem
  try simp only []
  exact checkBlockTailS_push mode h₁ (by rw [hns]; exact hndC) hfrs (hm ▸ hmem)

/-! ## The declaration clause and the two drivers' steps -/

theorem installBasisDeclF_push {env : Env} {fe : FEnv} (h : PushChain env fe)
    (ci : ConstantInfo) :
    Yields (installBasisDeclF (m := CheckCM) fe ci)
      (fun fe' => PushChain env fe') := by
  unfold installBasisDeclF
  yields
  all_goals exact Yields.pure (h.push (Option.isNone_iff_eq_none.mp (by assumption)))

/-- A pinned block's install pushes onto the chain. -/
theorem checkBasisBlockC_push {env : Env} {fe : FEnv}
    (h : PushChain env fe) (kind : BasisKind) (block : List ConstantInfo) :
    Yields (checkBasisBlockC fe kind block) (fun fe' => PushChain env fe') := by
  have hfold : ∀ (fe' : FEnv), PushChain env fe' →
      Yields ((kind.atBlock block).foldlM installBasisDeclF fe')
        (fun x => PushChain env x) :=
    fun fe' h' =>
      Yields.foldlM_rel (R := fun fe (_ : Unit) => PushChain env fe)
        (g := fun u _ => u)
        (fun acc ci _ hacc => installBasisDeclF_push hacc ci)
        (kind.atBlock block) fe' () h'
  unfold checkBasisBlockC
  yields
  all_goals exact hfold fe h

/-- A quotient record's install pushes onto the chain. -/
theorem checkQuotRecordC_push {env : Env} {fe : FEnv}
    (h : PushChain env fe) (k : QuotKind) (cv : ConstantVal) :
    Yields (checkQuotRecordC fe k cv) (fun fe' => PushChain env fe') := by
  unfold checkQuotRecordC
  yields
  all_goals exact installBasisDeclF_push h _

theorem checkDeclC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (pd : Declaration) :
    Yields (checkDeclC mode pins fe pd) (fun fe' => PushChain env fe') := by
  unfold checkDeclC
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun _ hfr => ?_
    split
    · -- the pinned arm: certified against the overlay, pushed last
      refine Yields.bind' (checkDefnValCI_shape mode fe cv value hint) fun ci hci => ?_
      obtain ⟨v, rfl⟩ := hci
      yields
      all_goals (apply Yields.pure; exact h.push hfr)
    · exact Yields.ofThrow
  | thmDecl cv value => exact Yields.ofThrow
  | opaqueDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun _ hfr => ?_
    split
    · -- the pinned arm: certified against the overlay, pushed last
      refine Yields.bind' (checkOpaqueValCI_shape mode fe cv value) fun ci hci => ?_
      subst hci
      yields
      all_goals (apply Yields.pure; exact h.push hfr)
    · exact Yields.ofThrow
  | axiomDecl cv =>
    simp only []
    split
    · exact checkQuotRecordC_push h .sound cv
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun _ hfr => ?_
    by_cases ht : cv.name = sorryAxName
    · rw [ite_eq_right (by rw [tolerated_not_std fe cv ht]; exact Bool.false_ne_true),
        ite_eq_right (tolerated_ne_trust ht), ite_eq_right (tolerated_ne_ofReduce ht),
        ite_eq_right (tolerated_ne_std ht), ite_eq_left ht]
      exact Yields.pure h
    · rw [ite_eq_right ht]
      yields
      all_goals first
        | (apply Yields.pure; exact h.push hfr)
        | exact absurd (by assumption) ht
  | quotDecl k cv => exact checkQuotRecordC_push h k cv
  | indDecl block nP =>
    simp only []
    unfold checkIndDeclC
    split
    · exact checkBasisBlockC_push h _ _
    · split
      · cases hbp : blockParts? nP block with
        | none => exact Yields.bind fun _ => Yields.ofThrow
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
theorem installStepC_push (mode : CheckMode) (i : Nat) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (pend : Array PendingCheck) (pd : Declaration) :
    Yields (installStepC mode pins i fe pend pd)
      (fun r => PushChain env r.1 ∧ ∃ new, r.2.toList = pend.toList ++ new) := by
  have hord : ∀ pd', Yields (do pure (← checkDeclStepC mode pins fe pd', pend) :
      CheckCM (FEnv × Array PendingCheck))
      (fun r => PushChain env r.1 ∧ ∃ new, r.2.toList = pend.toList ++ new) :=
    fun pd' => Yields.bind' (checkDeclStepC_push mode h pd') fun fe' h' =>
      Yields.pure ⟨h', [], by simp⟩
  unfold installStepC
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    split
    · exact hord _
    · refine Yields.bind' (installGuardsC_fresh fe cv value) fun _ hfr => ?_
      exact Yields.pure ⟨h.push hfr, _, Array.toList_push⟩
  | thmDecl cv value =>
    simp only []
    ybind
    refine Yields.bind' (installHeaderC_fresh fe cv) fun _ hfr => ?_
    exact Yields.pure ⟨h.push hfr, _, Array.toList_push⟩
  | opaqueDecl cv value =>
    simp only []
    split
    · exact hord _
    · refine Yields.bind' (installGuardsC_fresh fe cv value) fun _ hfr => ?_
      exact Yields.pure ⟨h.push hfr, _, Array.toList_push⟩
  | axiomDecl cv => exact hord _
  | quotDecl k cv => exact hord _
  | indDecl block nP => exact hord _

/-- **Phase A is a fresh chain**: from a canonical index, an accepting
run returns a canonical index whose constants extend the start by
fresh names, and the pending records extend the start's. -/
theorem installRun_trace (mode : CheckMode) {ds : List Declaration} {env : Env}
    {p : Nat × FEnv × Array PendingCheck}
    {q : Nat × FEnv × Array PendingCheck}
    (h : InstallRun mode pins ds p q) (hp : PushChain env p.2.1) :
    PushChain env q.2.1 ∧ ∃ new, q.2.2.toList = p.2.2.toList ++ new := by
  induction h with
  | nil p => exact ⟨hp, [], by simp⟩
  | @cons pd ds p p₁ q hstep rest ih =>
    obtain ⟨fe₁, pend₁, s₁, rfl, hstepC⟩ := installDeclStep_ok hstep
    obtain ⟨h₁, new₁, hpend₁⟩ :=
      installStepC_push mode p.1 hp p.2.2 _ {} (fe₁, pend₁) _ hstepC
    obtain ⟨h₂, new₂, hpend₂⟩ := ih h₁
    exact ⟨h₂, new₁ ++ new₂, by rw [hpend₂, hpend₁, List.append_assoc]⟩

end ConLeche.Cached
