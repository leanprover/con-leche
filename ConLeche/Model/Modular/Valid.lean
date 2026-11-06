module

public import ConLeche.Model.Modular.Read
public import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.StreamIndex
public import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Model.StreamConsts

public section

/-!
# The local checks give a context read from its sources

The derivation half of the amalgamation (`Model/Modular/Read.lean`): a module whose context and
whose sources pass the local checks (`LocalOk`, `ConLeche/Modular.lean`) has a context read from
its sources (`CtxRead`), with each name's source the own environment of the module it is read
from and the part read alike `readsAlike`.

Every environment here is the stream of a list of records (`streamEnv`): a module's context of its
context records, its own environment of those and its own records.  A name such an environment
stores is installed by one record, with that record's tables.  The key fact is the **owner**: a
context name is read from the module that declared it among its own records (`InterfaceOk` presents
only own records), so the context's copy is that record's constant or its statement, and the
module's key for it is the owner's key for its own constant.  Two copies of a name under one key
are then copies of one owner's constant (a home key) or two proofs of one statement (a proof key),
which is what makes them alike.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Cached ConLeche.Modular ConLeche.Model ConLeche.Verify

/-! ## Streams of records -/

/-- The constants a list of records installs, oldest first. -/
@[expose] def recsC (L : List Declaration) : List ConstantInfo := L.flatMap declConstants

theorem streamEnv_consts_base (L : List Declaration) (env : Env) :
    (streamEnv L env).consts = (recsC L).reverse ++ env.consts := by
  induction L generalizing env with
  | nil => rfl
  | cons d L ih =>
    simp only [streamEnv, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [recsC, Env.pushDelta, List.reverse_append, List.append_assoc]

theorem streamEnv_tables_base (L : List Declaration) (env : Env) :
    (streamEnv L env).tables = (L.flatMap declTables).reverse ++ env.tables := by
  induction L generalizing env with
  | nil => rfl
  | cons d L ih =>
    simp only [streamEnv, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [Env.pushDelta, List.reverse_append, List.append_assoc]

theorem streamEnv_empty_consts (L : List Declaration) :
    (streamEnv L).consts = (recsC L).reverse := by
  simpa [Env.empty] using streamEnv_consts_base L Env.empty

theorem streamEnv_empty_tables (L : List Declaration) :
    (streamEnv L).tables = (L.flatMap declTables).reverse := by
  simpa [Env.empty] using streamEnv_tables_base L Env.empty

theorem tables_sublist (L : List Declaration) :
    ((L.flatMap declTables).map (·.structName)).Sublist ((recsC L).map (·.name)) := by
  induction L with
  | nil => exact .refl _
  | cons pd L ih =>
    simp only [recsC, List.flatMap_cons, List.map_append] at ih ⊢
    exact (declTables_sublist pd).append ih

theorem streamEnv_append (A B : List Declaration) :
    streamEnv B (streamEnv A) = streamEnv (A ++ B) := by
  simp [streamEnv, List.foldl_append]

theorem mem_recsC {L : List Declaration} {ci : ConstantInfo} :
    ci ∈ recsC L ↔ ∃ e ∈ L, ci ∈ declConstants e := by
  simp [recsC]

/-- Names unique in a stream, as a list fact. -/
theorem nodup_recs {L : List Declaration} (h : NodupNames (streamEnv L)) :
    ((recsC L).map (·.name)).Nodup := by
  unfold NodupNames at h
  rw [streamEnv_empty_consts, List.map_reverse] at h
  exact (List.reverse_perm _).nodup_iff.mp h

/-- **A record's constant is stored at its name.** -/
theorem streamEnv_find?_of_mem {L : List Declaration} (h : NodupNames (streamEnv L))
    {e : Declaration} (he : e ∈ L) {ci : ConstantInfo} (hci : ci ∈ declConstants e) :
    (streamEnv L).find? ci.name = some ci := by
  apply find?_of_mem_nodup h
  rw [streamEnv_empty_consts, List.mem_reverse]
  exact mem_recsC.mpr ⟨e, he, hci⟩

/-- **A stored constant is a record's.** -/
theorem streamEnv_find?_some {L : List Declaration} {n : Name} {ci : ConstantInfo}
    (h : (streamEnv L).find? n = some ci) :
    ∃ e ∈ L, ci ∈ declConstants e ∧ ci.name = n := by
  have hm := ConLeche.Env.find?_mem h
  rw [streamEnv_empty_consts, List.mem_reverse] at hm
  obtain ⟨e, he, hci⟩ := mem_recsC.mp hm
  exact ⟨e, he, hci, ConLeche.Env.find?_name h⟩

/-- A name stored in a stream is a record's. -/
theorem streamEnv_isSome {L : List Declaration} {n : Name}
    (h : ((streamEnv L).find? n).isSome = true) :
    ∃ e ∈ L, ∃ ci ∈ declConstants e, ci.name = n ∧ (streamEnv L).find? n = some ci := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨e, he, hm, hn⟩ := streamEnv_find?_some hci
  exact ⟨e, he, ci, hm, hn, hci⟩

/-- In a name-unique stream, a name belongs to one record. -/
theorem recs_unique {L : List Declaration} (h : ((recsC L).map (·.name)).Nodup)
    {e e' : Declaration} {i i' : Nat} (hi : L[i]? = some e) (hi' : L[i']? = some e')
    {n : Name} (hn : n ∈ (declConstants e).map (·.name)) (hn' : n ∈ (declConstants e').map (·.name)) :
    i = i' := by
  induction L generalizing i i' with
  | nil => simp at hi
  | cons a L ih =>
    simp only [recsC, List.flatMap_cons, List.map_append] at h
    have h2 : ((recsC L).map (·.name)).Nodup := (List.nodup_append.mp h).2.1
    have hdis := (List.nodup_append.mp h).2.2
    have hmemL : ∀ {j : Nat} {x : Declaration}, L[j]? = some x →
        n ∈ (declConstants x).map (·.name) → n ∈ (recsC L).map (·.name) := by
      intro j x hj hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map.mpr ⟨c, mem_recsC.mpr ⟨x, List.mem_of_getElem? hj, hc⟩, rfl⟩
    cases i with
    | zero =>
      cases i' with
      | zero => rfl
      | succ j' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact absurd rfl (hdis _ hn _ (hmemL hi' hn'))
    | succ j =>
      cases i' with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi'
        subst hi'
        exact absurd rfl (hdis _ hn' _ (hmemL hi hn))
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hi hi'
        rw [ih h2 hi hi']

/-- The tables of the records before a name's record do not name it. -/
theorem tables_find?_none {L : List Declaration} {n : Name}
    (h : n ∉ (recsC L).map (·.name)) :
    (L.flatMap declTables).find? (·.structName == n) = none := by
  rw [List.find?_eq_none]
  intro t ht hb
  simp only [beq_iff_eq] at hb
  subst hb
  apply h
  exact (tables_sublist L).subset (List.mem_map.mpr ⟨t, ht, rfl⟩)

/-- **A stored name's table is its record's.** -/
theorem streamEnv_findTable? {L : List Declaration} (h : NodupNames (streamEnv L))
    {e : Declaration} (he : e ∈ L) {n : Name} (hn : n ∈ (declConstants e).map (·.name)) :
    (streamEnv L).findTable? n = (declTables e).find? (·.structName == n) := by
  have hnd := nodup_recs h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
  unfold Env.findTable?
  rw [streamEnv_find?_of_mem h he hc]
  simp only [Option.isSome_some, ↓reduceIte]
  rw [streamEnv_empty_tables,
    find?_reverse_of_nodup (fun t : ProjTable => t.structName) c.name ((tables_sublist L).nodup hnd)]
  obtain ⟨A, B, rfl⟩ := List.append_of_mem he
  have hi : (A ++ e :: B)[A.length]? = some e := by simp
  have hnotA : c.name ∉ (recsC A).map (·.name) := by
    intro hm
    obtain ⟨c', hc', heq⟩ := List.mem_map.mp hm
    obtain ⟨x, hx, hcx⟩ := mem_recsC.mp hc'
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    have hjA := (List.getElem?_eq_some_iff.mp hj).1
    have hj' : (A ++ e :: B)[j]? = some x := by rw [List.getElem?_append_left hjA]; exact hj
    have := recs_unique hnd hj' hi (List.mem_map.mpr ⟨c', hcx, heq⟩) hn
    omega
  have hnotB : c.name ∉ (recsC B).map (·.name) := by
    intro hm
    obtain ⟨c', hc', heq⟩ := List.mem_map.mp hm
    obtain ⟨x, hx, hcx⟩ := mem_recsC.mp hc'
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    have hj' : (A ++ e :: B)[A.length + 1 + j]? = some x := by
      rw [List.getElem?_append_right (by omega)]
      simpa [Nat.add_assoc, Nat.add_comm 1 j, Nat.add_sub_cancel_left] using hj
    have := recs_unique hnd hj' hi (List.mem_map.mpr ⟨c', hcx, heq⟩) hn
    omega
  rw [List.flatMap_append, List.find?_append, tables_find?_none hnotA, List.flatMap_cons,
    List.find?_append, tables_find?_none hnotB]
  cases (declTables e).find? (·.structName == c.name) <;> rfl

/-! ## What an accepting run says of its records -/

theorem checkConstantValC_unreserved (mode : CheckMode) (fe : FEnv) (cv : ConstantVal) {a : Bool} :
    Yields (checkConstantValC mode fe cv a)
      (fun _ => reservedBasisNames.contains cv.name = false) := by
  unfold checkConstantValC
  yields
  all_goals exact Yields.pure (Bool.eq_false_iff.mpr (by assumption))

/-- **An accepted value-kind record is at an unreserved name.** -/
theorem checkDeclStepC_unreserved {mode : CheckMode} {pins : List NatOpPinSet} {fe : FEnv}
    {d : Declaration} {s : CState} {r : FEnv × CState}
    (h : checkDeclStepC mode pins fe d s = .ok r) :
    ∀ cv, ((∃ v hint, d = .defnDecl cv v hint) ∨ (∃ v, d = .thmDecl cv v) ∨
      (∃ v, d = .opaqueDecl cv v)) → reservedBasisNames.contains cv.name = false := by
  intro cv hd
  have hY : Yields (checkDeclStepC mode pins fe d)
      (fun _ => reservedBasisNames.contains cv.name = false) := by
    unfold checkDeclStepC
    ybind
    unfold checkDeclC
    rcases hd with ⟨v, hint, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ <;>
    · simp only []
      exact Yields.bind' (checkConstantValC_unreserved mode fe cv) fun _ h => Yields.const h
  exact hY s r.1 r.2 h

/-- **Every record of an accepting run passed its check.** -/
theorem declsRun_checked {mode : CheckMode} {pins : List NatOpPinSet} {ds : List Declaration}
    {p q : Nat × FEnv} (h : DeclsRun mode pins ds p q) :
    ∀ d ∈ ds, ∃ fe r, checkDeclStepC mode pins fe d {} = .ok r := by
  induction h with
  | nil => exact fun _ h => nomatch h
  | @cons pd ds p p₁ q hstep rest ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨fe₁, s₁, -, hC⟩ := declStep_ok hstep
      exact ⟨_, _, hC⟩
    · exact ih d hd

/-- **An accepting run pushes a fresh chain.** -/
theorem declsRun_chain {mode : CheckMode} {pins : List NatOpPinSet} {ds : List Declaration}
    {p q : Nat × FEnv} (h : DeclsRun mode pins ds p q) {env : Env} :
    PushChain env p.2 → PushChain env q.2 := by
  induction h with
  | nil => exact id
  | @cons pd ds p p₁ q hstep rest ih =>
    intro hc
    obtain ⟨fe₁, s₁, rfl, hC⟩ := declStep_ok hstep
    exact ih (checkDeclStepC_push (pins := pins) mode hc pd {} fe₁ s₁ hC)

/-! ## A module's environments -/

section
variable {mode : CheckMode} {pins : List NatOpPinSet} {dev : Nat → Module}

theorem Module.own_eq (m : Module) : m.own = streamEnv (m.ctx ++ m.decls) := by
  unfold Module.own Module.context
  exact streamEnv_append _ _

theorem Module.context_eq (m : Module) : m.context = streamEnv m.ctx := rfl

/-- **An importer's own records are fresh**: its own environment pushes them, name-unique and
fresh, on its context. -/
theorem ImportOk.chain {j : Nat} (h : ImportOk mode pins dev j) :
    NodupNames (dev j).own ∧
      (∀ ci ∈ recsC (dev j).decls, (dev j).context.find? ci.name = none) ∧
      ∀ d ∈ (dev j).decls, ∃ fe r, checkDeclStepC mode pins fe d {} = .ok r := by
  obtain ⟨q, hq⟩ := h.accepted
  have hch := declsRun_chain hq (PushChain.refl (dev j).context)
  have henv : q.2.env = (dev j).own := by
    rw [declsRun_env mode hq]; rfl
  obtain ⟨-, ⟨new, hnew, -, hfr⟩, hnd, -⟩ := hch
  rw [henv] at hnew hnd
  have hnew' : new = (recsC (dev j).decls).reverse := by
    have h2 := streamEnv_consts_base (dev j).decls (dev j).context
    rw [show streamEnv (dev j).decls (dev j).context = (dev j).own from rfl, hnew] at h2
    exact List.append_cancel_right h2
  refine ⟨hnd h.nodup, fun ci hci => hfr ci ?_, declsRun_checked hq⟩
  rw [hnew']; exact List.mem_reverse.mpr hci

end

section
variable {pins : List NatOpPinSet} {dev : Nat → Module}

theorem own_find?_of_context {j : Nat} (hnd : NodupNames (dev j).own) {x : Name} {ci : ConstantInfo}
    (h : (dev j).context.find? x = some ci) : (dev j).own.find? x = some ci := by
  have hm := ConLeche.Env.find?_mem h
  rw [← ConLeche.Env.find?_name h]
  apply find?_of_mem_nodup hnd
  show ci ∈ (streamEnv (dev j).decls (dev j).context).consts
  rw [streamEnv_consts_base]
  exact List.mem_append_right _ hm

theorem own_find?_of_decl {j : Nat} (hnd : NodupNames (dev j).own) {d : Declaration}
    (hd : d ∈ (dev j).decls) {ci : ConstantInfo} (hci : ci ∈ declConstants d) :
    (dev j).own.find? ci.name = some ci := by
  rw [Module.own_eq] at hnd ⊢
  exact streamEnv_find?_of_mem hnd (List.mem_append_right _ hd) hci

/-- **A stored own name is a context name or an own record's.** -/
theorem own_find?_cases {mode : CheckMode} {j : Nat} (hok : ImportOk mode pins dev j)
    {x : Name} {ci : ConstantInfo} (h : (dev j).own.find? x = some ci) :
    (dev j).context.find? x = some ci ∨
      ((dev j).context.find? x = none ∧ ∃ d ∈ (dev j).decls, ci ∈ declConstants d) := by
  have hm : ci ∈ (streamEnv (dev j).decls (dev j).context).consts := ConLeche.Env.find?_mem h
  rw [← ConLeche.Env.find?_name h]
  rw [streamEnv_consts_base] at hm
  rcases List.mem_append.mp hm with hm | hm
  · have hr := List.mem_reverse.mp hm
    exact .inr ⟨(ImportOk.chain hok).2.1 ci hr, mem_recsC.mp hr⟩
  · exact .inl (find?_of_mem_nodup hok.nodup hm)

/-- **The owner of a context name**: the module it is read from declared it among its own
records; the context's copy refines the owner's constant, under the owner's key, with its
table. -/
theorem owner {i : Nat} (hi : ImportOk .verified pins dev i) {x : Name} {ciC : ConstantInfo}
    (hsI : InterfaceOk dev ((dev i).src x)) (hsK : ImportOk .verified pins dev ((dev i).src x))
    (hx : (dev i).context.find? x = some ciC) :
    ∃ ciO, (dev ((dev i).src x)).own.find? x = some ciO ∧
      (dev ((dev i).src x)).context.find? x = none ∧
      (∃ p ∈ (dev ((dev i).src x)).decls, ciO ∈ declConstants p) ∧ Refines ciC ciO ∧
      (dev i).key x = (dev ((dev i).src x)).ownKey ((dev i).src x) x ciO ∧
      (dev i).context.findTable? x = (dev ((dev i).src x)).own.findTable? x := by
  generalize hs : (dev i).src x = s at hsI hsK ⊢
  obtain ⟨e, he, hce, hnm⟩ := streamEnv_find?_some (L := (dev i).ctx) hx
  have hxe : x ∈ declNames e := List.mem_map.mpr ⟨ciC, hce, hnm⟩
  have hei : e ∈ (dev s).iface := hs ▸ hi.presented e he x hxe
  obtain ⟨p, hp, hpres⟩ := hsI.presents e hei
  obtain ⟨hndO, hfr, -⟩ := ImportOk.chain hsK
  have hpL : p ∈ (dev s).ctx ++ (dev s).decls := List.mem_append_right _ hp
  have hndL : NodupNames (streamEnv ((dev s).ctx ++ (dev s).decls)) := by
    rw [← Module.own_eq]; exact hndO
  have htabC : ∀ {L : List Declaration}, e ∈ L → NodupNames (streamEnv L) →
      (streamEnv L).findTable? x = (declTables e).find? (·.structName == x) :=
    fun h1 h2 => streamEnv_findTable? h2 h1 hxe
  -- the owner's constant, its key and its table
  have fin : ∀ ciO, ciO ∈ declConstants p → ciO.name = x → Refines ciC ciO →
      declTables e = declTables p →
      ∃ ciO, (dev s).own.find? x = some ciO ∧ (dev s).context.find? x = none ∧
        (∃ p ∈ (dev s).decls, ciO ∈ declConstants p) ∧ Refines ciC ciO ∧
        (dev i).key x = (dev s).ownKey s x ciO ∧
        (dev i).context.findTable? x = (dev s).own.findTable? x := by
    intro ciO hO hOn hR ht
    have hfO : (dev s).own.find? x = some ciO := by
      rw [← hOn]; exact own_find?_of_decl hndO hp hO
    have hfC : (dev s).context.find? x = none := by
      rw [← hOn]; exact hfr ciO (mem_recsC.mpr ⟨p, hp, hO⟩)
    refine ⟨ciO, hfO, hfC, ⟨p, hp, hO⟩, hR, ?_, ?_⟩
    · rw [hi.key_context x (by rw [hx]; rfl), hs]
      exact hsK.key_own x ciO hfO hfC
    · rw [Module.context_eq, htabC he hi.nodup, Module.own_eq, ht,
        streamEnv_findTable? hndL hpL (by rw [← hOn]; exact List.mem_map_of_mem hO)]
  rcases hpres with ⟨hc, ht⟩ | hst
  · exact fin ciC (hc ▸ hce) hnm (.inl rfl) ht
  · subst hst
    have hunres : ∀ cv, ((∃ v hint, p = .defnDecl cv v hint) ∨ (∃ v, p = .thmDecl cv v) ∨
        (∃ v, p = .opaqueDecl cv v)) → ciC ∈ declConstants (.axiomDecl cv) → ciC = .axiomInfo cv := by
      intro cv hk hm
      obtain ⟨fe, r, hr⟩ := (ImportOk.chain hsK).2.2 p hp
      have hres := checkDeclStepC_unreserved hr cv hk
      have hq : cv.name ≠ quotSoundName := by
        intro h; rw [h] at hres; exact absurd hres (by decide)
      simp only [declConstants, hq, ↓reduceIte] at hm
      split at hm
      · exact absurd hm (List.not_mem_nil)
      · exact List.mem_singleton.mp hm
    cases p with
    | defnDecl cv v hint =>
      obtain rfl := hunres cv (.inl ⟨v, hint, rfl⟩) hce
      exact fin (.defnInfo cv v hint) List.mem_cons_self hnm (.inr ⟨rfl, rfl⟩) rfl
    | thmDecl cv v =>
      obtain rfl := hunres cv (.inr (.inl ⟨v, rfl⟩)) hce
      exact fin (.thmInfo cv) List.mem_cons_self hnm (.inr ⟨rfl, rfl⟩) rfl
    | opaqueDecl cv v =>
      obtain rfl := hunres cv (.inr (.inr ⟨v, rfl⟩)) hce
      exact fin (.axiomInfo cv) List.mem_cons_self hnm (.inl rfl) rfl
    | axiomDecl cv => exact fin ciC hce hnm (.inl rfl) rfl
    | quotDecl k cv => exact fin ciC hce hnm (.inl rfl) rfl
    | indDecl b nP => exact fin ciC hce hnm (.inl rfl) rfl

end

end ConLeche.Model.Modular
