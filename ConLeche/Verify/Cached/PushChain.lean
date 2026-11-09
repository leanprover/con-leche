module

import ConLeche.Verify.Cached.IndBlockC
import ConLeche.Verify.Inductives.BlockShapeInv
import ConLeche.Verify.Inductives.DirectInv
public import ConLeche.Verify.Cached.DeclPushes
public import ConLeche.Verify.EnvBound
import ConLeche.Verify.EnvWF
import ConLeche.Verify.CheckerF
import ConLeche.Verify.Cached.WalkersC
import ConLeche.Verify.Cached.IndPositivityC

public section

/-!
# Every accepted step is a chain of fresh pushes (task #253)

A record's job reads the stream's index (`ConLeche/Cached/StreamIndex.lean`), where a name's first
entry wins, and the fold's index, where its newest does; the two answer alike only under name
uniqueness (`viewTwin`, `ConLeche/Verify/Cached/StreamIndex.lean`).  Name uniqueness holds along
the fold: every push a step performs is guarded by a lookup — `checkConstantValC`'s duplicate
guard, `installBasisDeclF`'s — and every table install by a lookup of
its structure — so this file proves, once and OPERATIONALLY (no
environment well-formedness, no simulation: the final-value discipline
of `ConLeche/Verify/Cached/DeclPushes.lean`), that an accepted step
returns `PushChain env fe'`: a canonical index whose constants extend
`env` by fresh names, and whose tables extend `env`'s by tables of
structures `env` does not store.  Chained from the empty environment, that is
`NodupNames` of every environment the fold ever holds, and the
suffix relation between the environment a declaration was checked at
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
  fe' = mkFEnv fe'.env ∧
  (∃ new, fe'.env.consts = new ++ env.consts ∧ (new.map (·.name)).Nodup ∧
    ∀ c ∈ new, env.find? c.name = none) ∧
  (NodupNames env → NodupNames fe'.env) ∧
  (∃ newQ, fe'.env.tables = newQ ++ env.tables ∧ ∀ t ∈ newQ, env.find? t.structName = none)

theorem PushChain.refl (env : Env) : PushChain env (mkFEnv env) :=
  ⟨rfl, ⟨[], rfl, List.nodup_nil, fun _ h => nomatch h⟩, id, ⟨[], rfl, fun _ h => nomatch h⟩⟩

theorem PushChain.canon {env : Env} {fe : FEnv} (h : PushChain env fe) :
    fe = mkFEnv fe.env := h.1

/-- A canonical index is a chain from its own environment. -/
theorem PushChain.self {fe : FEnv} (h : fe = mkFEnv fe.env) : PushChain fe.env fe :=
  ⟨h, ⟨[], rfl, List.nodup_nil, fun _ h => nomatch h⟩, id, ⟨[], rfl, fun _ h => nomatch h⟩⟩

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

/-- A name the chain's end does not find, its start does not find
either. -/
theorem PushChain.find?_none {env : Env} {fe : FEnv} (h : PushChain env fe) {n : Name}
    (hn : fe.find? n = none) : env.find? n = none := by
  obtain ⟨new, hnew, -, -⟩ := h.2.1
  rw [h.find?] at hn
  unfold Env.find? at hn ⊢
  rw [hnew, List.find?_append] at hn
  cases h' : env.consts.find? (·.name == n) with
  | none => rfl
  | some c => rw [h'] at hn; cases new.find? (·.name == n) <;> simp at hn

theorem PushChain.push {env : Env} {fe : FEnv} (h : PushChain env fe)
    {ci : ConstantInfo} (hfresh : fe.find? ci.name = none) :
    PushChain env (fe.push ci) := by
  have hstart := PushChain.find?_none h hfresh
  have hf := PushChain.find? h ci.name
  obtain ⟨hc, ⟨new, hnew, hnn, hnf⟩, hnd, hQ⟩ := h
  have hfresh' := hfresh
  rw [hf] at hfresh'
  have hnot := Env.find?_none_notin hfresh'
  refine ⟨?_, ⟨ci :: new, ?_, ?_, ?_⟩, ?_, hQ⟩
  · calc fe.push ci = (mkFEnv fe.env).push ci := by rw [← hc]
      _ = mkFEnv (fe.push ci).env := push_mkFEnv fe.env ci
  · show ci :: fe.env.consts = _
    rw [hnew]
    rfl
  · rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨fun hm => hnot ?_, hnn⟩
    rw [hnew, List.map_append]
    exact List.mem_append_left _ hm
  · intro c hc'
    rcases List.mem_cons.mp hc' with rfl | hm
    · exact hstart
    · exact hnf c hm
  · intro hnd₀
    show ((ci :: fe.env.consts).map (·.name)).Nodup
    rw [List.map_cons]
    exact List.nodup_cons.mpr ⟨hnot, hnd hnd₀⟩

/-- What a push onto a canonical index does not find, the index does not, and it is not the name
pushed. -/
theorem find?_none_push {fe : FEnv} {ci : ConstantInfo} {n : Name} (hc : fe = mkFEnv fe.env)
    (h : (fe.push ci).find? n = none) : ci.name ≠ n ∧ fe.find? n = none := by
  have hp : fe.push ci = mkFEnv ⟨ci :: fe.env.consts, fe.env.tables⟩ := by
    conv => lhs; rw [hc]
    exact push_mkFEnv _ _
  rw [hp, mkFEnv_find?, Env.find?_cons] at h
  by_cases he : ci.name = n
  · rw [ite_eq_left he] at h
    exact nomatch h
  · rw [ite_eq_right he] at h
    refine ⟨he, ?_⟩
    rw [hc, mkFEnv_find?]
    exact h

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
    (cv : ConstantVal) {a : Bool} :
    Yields (checkConstantValC mode fe cv a)
      (fun _ => fe.find? cv.name = none) := by
  unfold checkConstantValC
  yields
  all_goals exact Yields.pure (Option.not_isSome_iff_eq_none.mp (by assumption))

/-! ## The constructors' conses -/

/-! ## The block install at k members

A block pushes its formers, then every member's constructors, then its
recursors, then a table per structure-like member.  Every push is fresh:
the formers and the constructors by their own stages' lookups and the
block's distinct-name guard, the recursors by the type stage's lookup (at
the constructors' index) and —
for the k names among themselves — by the recursor NAME-SET check
(`blockRecNameSetOk`), which with the members' own distinct names is a
pigeonhole. -/

/-- The formers' conses: a fresh chain. -/
theorem consBlockIndsF_push (p₁ : BlockShape) (isRec : Bool) {env : Env} :
    ∀ {formers : List ConstantVal} {i : Nat} {fe : FEnv}, PushChain env fe →
      FreshNames fe.env (formers.map (·.name)) →
      PushChain env (consBlockIndsF p₁ isRec formers i fe)
  | [], _, _, h, _ => h
  | cvTa :: rest, i, fe, h, hf => by
    have hfr : fe.find? cvTa.name = none := by
      rw [h.find?]; exact hf.2 _ (by simp)
    exact consBlockIndsF_push p₁ isRec (formers := rest) (i := i + 1)
      (h.push (ci := .indInfo cvTa (blockCapsAt p₁ i isRec)) hfr)
      (FreshNames.step (c := .indInfo cvTa (blockCapsAt p₁ i isRec)) hf)

/-- What the formers' environment does not find, its start does not, and it is no former. -/
theorem consBlockIndsF_find?_none (p₁ : BlockShape) (isRec : Bool) {n : Name} :
    ∀ {cvs : List ConstantVal} {i : Nat} {fe : FEnv}, fe = mkFEnv fe.env →
      (consBlockIndsF p₁ isRec cvs i fe).find? n = none →
      n ∉ cvs.map (·.name) ∧ fe.find? n = none
  | [], _, _, _, h => ⟨by simp, h⟩
  | cv :: rest, i, fe, hc, h => by
    have hc' : fe.push (.indInfo cv (blockCapsAt p₁ i isRec)) =
        mkFEnv (fe.push (.indInfo cv (blockCapsAt p₁ i isRec))).env := by
      conv => lhs; rw [hc]
      exact push_mkFEnv _ _
    obtain ⟨h₁, h₂⟩ := consBlockIndsF_find?_none p₁ isRec (cvs := rest) hc' h
    obtain ⟨hne, hfe⟩ := find?_none_push hc h₂
    refine ⟨?_, hfe⟩
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨fun e => hne e.symm, h₁⟩

/-- What the constructors' environment does not find, its start does not, and it is no
constructor. -/
theorem consSumCtorsF_find?_none (nP : Nat) {n : Name} :
    ∀ {cs : List (ConstantVal × Nat)} {fe : FEnv}, fe = mkFEnv fe.env →
      (consSumCtorsF nP cs fe).find? n = none →
      n ∉ cs.map (·.1.name) ∧ fe.find? n = none
  | [], _, _, h => ⟨by simp, h⟩
  | c :: cs, fe, hc, h => by
    have hc' : fe.push (.ctorInfo c.1 nP c.2) = mkFEnv (fe.push (.ctorInfo c.1 nP c.2)).env := by
      conv => lhs; rw [hc]
      exact push_mkFEnv _ _
    obtain ⟨h₁, h₂⟩ := consSumCtorsF_find?_none nP (cs := cs) hc' h
    obtain ⟨hne, hfe⟩ := find?_none_push hc h₂
    refine ⟨?_, hfe⟩
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨fun e => hne e.symm, h₁⟩

/-- One pass at k members: the formers' conses keep the chain, and the
constructors are the block's by name, fresh at the formers'
environment. -/
theorem checkBlockPassS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (p₀ : BlockShape) (isRec : Bool)
    (hdn : p₀.members.map (·.declared.name) = p₀.members.map (·.cvT.name))
    (hnd : (p₀.members.map (·.cvT.name)).Nodup) :
    Yields (checkBlockPassS mode fe p₀ isRec)
      (fun r => PushChain env r.env₁ ∧ r.p.members = p₀.members ∧ r.p.recs = p₀.recs ∧
        r.p.nP = p₀.nP ∧
        (∀ c ∈ p₀.allCtors, r.env₁.find? c.1.name = none) ∧
        (∀ ms ∈ p₀.members, fe.find? ms.cvT.name = none) ∧
        ∀ n, r.env₁.find? n = none → n ∉ p₀.members.map (·.cvT.name) ∧ fe.find? n = none) := by
  unfold checkBlockPassS
  simp only [checkBlockIndsC_eq, checkBlockCtorsC_eq, checkBlockClassesC_eq, blockNestCtxC_eq,
    checkBlockPositivityC_eq, nestSeedsC_eq, classSeedsC_eq]
  refine Yields.bind' (checkBlockIndsF_fresh _ fe p₀ isRec) fun r₁ h₁ => ?_
  obtain ⟨fe₁, p₁⟩ := r₁
  obtain ⟨⟨s, hps⟩, hfe₁, hfr⟩ := h₁
  try simp only [] at hps hfe₁ hfr
  subst hps
  try simp only []
  have h₁ : PushChain env fe₁ := by
    rw [hfe₁]
    have hdn' : ((p₀.members.map (·.declared)).map (·.name)) = p₀.members.map (·.cvT.name) := by
      rw [List.map_map]; exact hdn
    refine consBlockIndsF_push _ isRec h ⟨by rw [hdn']; exact hnd, ?_⟩
    intro n hn'
    rw [hdn'] at hn'
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hn'
    rw [← h.find?]
    exact hfr ms hms
  ybind
  refine Yields.bind' (checkBlockCtorsF_fresh _ fe₁ fe₁ _ _) fun _ hfrs => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun kinds => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.pure ⟨h₁, rfl, rfl, rfl, ?_, hfr, fun n hn => ?_⟩
  · intro c hc
    obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hcs
    exact hfrs ms hms c hc
  · have hn' : (consBlockIndsF (p₀.withSort s) isRec (p₀.members.map (·.declared)) 0
        fe).find? n = none := by rw [← hfe₁]; exact hn
    obtain ⟨hm₁, hm₂⟩ := consBlockIndsF_find?_none _ isRec h.canon hn'
    refine ⟨?_, hm₂⟩
    rw [List.map_map] at hm₁
    show n ∉ p₀.members.map (·.cvT.name)
    rw [← hdn]
    exact hm₁

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

/-- The cached generated stage's run says the records' names are distinct and fresh at the
constructors' index (the generated constant's lookup and the record pins). -/
theorem genRecCheck_recFresh (mode : CheckMode) (fe : FEnv)
    (p : BlockShape) (nested : Bool) (params : List Expr) (tbl : List NestCtorNf)
    (rd : ClassRead) (Ms₀ : List TargetMajor)
    (block : List ConstantInfo) :
    Yields (genRecCheckC mode fe p nested params tbl rd Ms₀ block)
      (fun _ => (p.recs.map (·.cvR.name)).Nodup ∧ ∀ rc ∈ p.recs, fe.find? rc.cvR.name = none) := by
  refine Yields.mono (genRecCheckC_names mode fe
    p nested params tbl rd Ms₀ block) fun out hout => ?_
  obtain ⟨hnd, -, hall⟩ := hout
  refine ⟨hnd, fun rc hrc => ?_⟩
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hrc
  obtain ⟨-, -, -, hfr⟩ := hall j rc hj
  exact hfr

/-- Pushes of fresh, distinct names: a fresh chain. -/
theorem PushChain.pushAll {env : Env} :
    ∀ {L : List ConstantInfo} {fe : FEnv}, PushChain env fe → FreshNames fe.env (L.map (·.name)) →
      PushChain env (FEnv.pushAll L fe)
  | [], _, h, _ => h
  | c :: L, fe, h, hf => by
    have hfr : fe.find? c.name = none := by
      rw [h.find?]; exact hf.2 _ (by simp)
    exact PushChain.pushAll (L := L) (h.push hfr) (FreshNames.step (c := c) hf)

/-- Table installs of structures not in the chain's start: a fresh chain. -/
theorem PushChain.pushTables {env : Env} :
    ∀ {Q : List ProjTable} {fe : FEnv}, PushChain env fe →
      (∀ t ∈ Q, env.find? t.structName = none) → PushChain env (FEnv.pushTables Q fe)
  | [], _, h, _ => h
  | t :: Q, _, h, hQ =>
    PushChain.pushTables (Q := Q) (h.pushTable (hQ t List.mem_cons_self))
      fun t' ht' => hQ t' (List.mem_cons_of_mem _ ht')

/-- The names of a block's constants. -/
theorem blockConstants_names (p : BlockShape) :
    (blockConstants p).map (·.name) =
      p.members.map (·.declared.name) ++ p.allCtors.map (·.1.name) ++ p.recs.map (·.cvR.name) := by
  have hF : ∀ (l : List ConstantVal) (i : Nat) (caps : Nat → IndCaps),
      (l.zipIdx i |>.map fun (x : ConstantVal × Nat) =>
        ConstantInfo.indInfo x.1 (caps x.2)).map (·.name) = l.map (·.name) := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons a l ih =>
      intro i caps
      simp only [List.zipIdx_cons, List.map_cons]
      exact congrArg (a.name :: ·) (ih (i + 1) caps)
  have hR : ∀ l : List RecShape, (blockRecs p l).map (·.name) = l.map (·.cvR.name) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => exact congrArg (a.cvR.name :: ·) ih
  unfold blockConstants blockFormers blockCtors
  simp only [List.map_append]
  rw [hF _ 0 (fun i => blockCapsAt p i (blockIsRec p)), hR]
  simp [List.map_map, Function.comp_def, BlockShape.allCtors]
  rfl

/-- The checks after the pass: the recursors' names are distinct and fresh at the constructors'
index. -/
theorem checkBlockTailS_fresh (mode : CheckMode) {block : List ConstantInfo} {q : BlockPass FEnv}
    {Q : List ProjTable} :
    Yields (checkBlockTailS mode block q Q) (fun _ =>
      (q.p.recs.map (·.cvR.name)).Nodup ∧
      ∀ rc ∈ q.p.recs, (consBlockCtorsF q.p.nP q.p.memberCtors q.env₁).find? rc.cvR.name = none) := by
  obtain ⟨env₁, p, kinds, params, rd, cls, tbl⟩ := q
  unfold checkBlockTailS
  dsimp only
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  exact Yields.bind' (genRecCheck_recFresh mode _ p _ _ _ _ _ block) fun _ hrs =>
    Yields.const hrs

/-- A block's install keeps the chain, its members' declared names standing where the
recogniser read them. -/
theorem checkBlockKS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (block : List ConstantInfo) (p : BlockShape)
    (hd : ∀ ms ∈ p.members, ms.declared = ms.cvT) :
    Yields (checkBlockKS mode fe block p) (fun fe' => PushChain env fe') := by
  unfold checkBlockKS
  rw [blockTablesC_eq, blockIsRecC_eq, blockConstantsC_eq]
  try apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hnd => ?nb)
  case nb =>
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?main)
  case main =>
  have hndC : (p.allCtors.map (·.1.name)).Nodup := hnd.1
  have hndM : (p.members.map (·.cvT.name)).Nodup := hnd.2
  refine Yields.bind' (reduceMembersS_same mode fe p.nP p.members) fun ms hms => ?_
  ybind
  obtain ⟨e₁, e₂, e₃⟩ := sameMembers_names hms hd
  have hCt : ({ p with members := ms } : BlockShape).allCtors = p.allCtors := by
    show (ms.map (·.ctors)).flatten = (p.members.map (·.ctors)).flatten
    rw [e₃]
  refine Yields.bind' (checkBlockPassS_push mode h { p with members := ms } (blockIsRec p) e₂
    (by show (ms.map _).Nodup; rw [e₁]; exact hndM)) fun q hr => ?_
  obtain ⟨h₁, hm, hrec, hnp, hfrs₀, hfrMs, hmem⟩ := hr
  try simp only [] at h₁ hm hrec hnp hfrs₀ hfrMs hmem
  try simp only []
  have hflat : q.p.memberCtors.flatten = ({ p with members := ms } : BlockShape).allCtors := by
    show (q.p.members.map (·.ctors)).flatten = _
    rw [hm]
    rfl
  have hns : q.p.memberCtors.flatten.map (·.1.name) =
      ({ p with members := ms } : BlockShape).allCtors.map (·.1.name) := by rw [hflat]
  have hfrs : ∀ c ∈ q.p.memberCtors.flatten, q.env₁.find? c.1.name = none := by
    rw [hflat]; exact hfrs₀
  refine Yields.bind' Yields.unwrapOr fun Q hQ => ?_
  refine Yields.bind' (checkBlockTailS_fresh mode) fun _ hrs => Yields.pure ?_
  have hrecs : q.p.recs = p.recs := hrec
  have hnP : q.p.nP = p.nP := hnp
  rw [hrecs] at hrs
  obtain ⟨hndR, hfrR⟩ := hrs
  have hCan₁ : q.env₁ = mkFEnv q.env₁.env := h₁.canon
  -- what the constructors' index does not find
  have hC : ∀ n, (consBlockCtorsF q.p.nP q.p.memberCtors q.env₁).find? n = none →
      n ∉ p.allCtors.map (·.1.name) ∧ n ∉ p.members.map (·.cvT.name) ∧ fe.find? n = none := by
    intro n hn
    rw [consBlockCtorsF_flatten] at hn
    obtain ⟨h₃, h₄⟩ := consSumCtorsF_find?_none q.p.nP hCan₁ hn
    obtain ⟨h₅, h₆⟩ := hmem n h₄
    refine ⟨by rw [← hCt, ← hns]; exact h₃, ?_, h₆⟩
    show n ∉ p.members.map _
    rw [← e₁]
    exact h₅
  have hdnP : p.members.map (·.declared.name) = p.members.map (·.cvT.name) := by
    refine List.map_congr_left fun m hm => ?_
    rw [hd m hm]
  unfold FEnv.pushDelta
  refine PushChain.pushTables (PushChain.pushAll h ⟨?_, ?_⟩) fun t ht => ?_
  · rw [blockConstants_names, hdnP, List.nodup_append, List.nodup_append]
    refine ⟨⟨hndM, hndC, fun a ha b hb => ?_⟩, hndR, fun a ha b hb => ?_⟩
    · rintro rfl
      obtain ⟨c, hc, hca⟩ := List.mem_map.mp hb
      have hc' : a ∈ q.p.memberCtors.flatten.map (·.1.name) := by rw [hns, hCt]; exact hb
      obtain ⟨c', hc'm, hc'e⟩ := List.mem_map.mp hc'
      have := hfrs c' hc'm
      rw [hc'e] at this
      refine (hmem a this).1 ?_
      show a ∈ ms.map _
      rw [e₁]
      exact ha
    · rintro rfl
      obtain ⟨rc, hrc, hn⟩ := List.mem_map.mp hb
      have hf := hfrR rc hrc
      rw [hn] at hf
      obtain ⟨h₃, h₄, -⟩ := hC _ hf
      rcases List.mem_append.mp ha with hm | hm
      · exact h₄ hm
      · exact h₃ hm
  · intro n hn
    have hfe : fe.find? n = none := by
      rw [blockConstants_names, hdnP] at hn
      rcases List.mem_append.mp hn with hn | hn
      · rcases List.mem_append.mp hn with hn | hn
        · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
          have hm' : m.cvT.name ∈ ms.map (·.cvT.name) := by rw [e₁]; exact List.mem_map_of_mem hm
          obtain ⟨m', hm'm, he⟩ := List.mem_map.mp hm'
          rw [← he]
          exact hfrMs m' hm'm
        · have hc' : n ∈ q.p.memberCtors.flatten.map (·.1.name) := by rw [hns, hCt]; exact hn
          obtain ⟨c', hc'm, rfl⟩ := List.mem_map.mp hc'
          exact (hmem _ (hfrs c' hc'm)).2
      · obtain ⟨rc, hrc, rfl⟩ := List.mem_map.mp hn
        exact (hC _ (hfrR rc hrc)).2.2
    rw [← h.find?]
    exact hfe
  · obtain ⟨m, hm, hn⟩ := blockTables_names _ _ Q hQ t ht
    rw [hn, hd m hm]
    have hm' : m.cvT.name ∈ ms.map (·.cvT.name) := by rw [e₁]; exact List.mem_map_of_mem hm
    obtain ⟨m', hm'm, he⟩ := List.mem_map.mp hm'
    rw [← he]
    exact h.find?_none (hfrMs m' hm'm)

/-! ## The declaration clause and the two drivers' steps -/

theorem installBasisDeclF_push {env : Env} {fe : FEnv} (h : PushChain env fe)
    (ci : ConstantInfo) :
    Yields (installBasisDeclF (m := CheckCM) fe ci)
      (fun fe' => PushChain env fe') := by
  unfold installBasisDeclF
  yields
  all_goals exact Yields.pure (h.push (Option.isNone_iff_eq_none.mp (by assumption)))

/-- A quotient record's install pushes onto the chain. -/
theorem checkQuotRecordC_push {env : Env} {fe : FEnv}
    (h : PushChain env fe) (k : QuotKind) (cv : ConstantVal) :
    Yields (checkQuotRecordC fe k cv) (fun fe' => PushChain env fe') := by
  unfold checkQuotRecordC
  yields
  all_goals exact installBasisDeclF_push h _

theorem checkDeclKindC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (pd : Declaration) :
    Yields (checkDeclKindC mode pins fe pd) (fun fe' => PushChain env fe') := by
  unfold checkDeclKindC
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun _ hfr => ?_
    -- certified against the overlay, pushed last
    refine Yields.bind' (checkDefnValCI_shape mode fe cv value hint) fun ci hci => ?_
    subst hci
    yields
    all_goals (apply Yields.pure; exact h.push hfr)
  | thmDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun _ hfr => ?_
    refine Yields.bind' (checkThmValCI_shape mode fe cv value) fun ci hci => ?_
    subst hci
    exact Yields.pure (h.push hfr)
  | opaqueDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun _ hfr => ?_
    refine Yields.bind' (checkOpaqueValCI_shape mode fe cv value) fun ci hci => ?_
    subst hci
    yields
    all_goals (apply Yields.pure; exact h.push hfr)
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
    · cases hbp : readBlock nP block with
      | error e => exact Yields.ofThrow
      | ok p => exact checkBlockKS_push mode h block p (ConLeche.readBlock_declared (by assumption))
    · exact Yields.ofThrow

theorem checkDeclC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (pd : Declaration) :
    Yields (checkDeclC mode pins fe pd) (fun fe' => PushChain env fe') := by
  unfold checkDeclC
  refine Yields.bind' (checkDeclKindC_push mode h pd) fun fe₂ h₂ => ?_
  yields
  all_goals exact Yields.pure h₂

theorem checkDeclStepC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (pd : Declaration) :
    Yields (checkDeclStepC mode pins fe pd) (fun fe' => PushChain env fe') := by
  unfold checkDeclStepC
  ybind
  exact checkDeclC_push mode h pd

/-- **An accepting run is a fresh chain**: from a canonical index, it returns a canonical index
whose constants extend the start by fresh names. -/
theorem declsRun_chain (mode : CheckMode) {ds : List Declaration} {env : Env} {p q : Nat × FEnv}
    (h : DeclsRun mode pins maxNatSize ds p q) (hp : PushChain env p.2) : PushChain env q.2 := by
  induction h with
  | nil p => exact hp
  | @cons pd ds p p₁ q hstep rest ih =>
    obtain ⟨fe₁, s₁, rfl, hstepC⟩ := declStep_ok hstep
    exact ih (checkDeclStepC_push mode hp pd _ fe₁ s₁ hstepC)

end ConLeche.Cached
