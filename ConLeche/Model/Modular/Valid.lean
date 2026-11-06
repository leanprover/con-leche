module

public import ConLeche.Model.Modular.Read
public import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.StreamIndex
import ConLeche.Verify.Cached.DeclPushes
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
      (dev i).context.findTable? x = (dev ((dev i).src x)).own.findTable? x ∧
      (x ∈ reduceOpNames → ciC = ciO) := by
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
      declTables e = declTables p → (x ∈ reduceOpNames → ciC = ciO) →
      ∃ ciO, (dev s).own.find? x = some ciO ∧ (dev s).context.find? x = none ∧
        (∃ p ∈ (dev s).decls, ciO ∈ declConstants p) ∧ Refines ciC ciO ∧
        (dev i).key x = (dev s).ownKey s x ciO ∧
        (dev i).context.findTable? x = (dev s).own.findTable? x ∧
        (x ∈ reduceOpNames → ciC = ciO) := by
    intro ciO hO hOn hR ht hred
    have hfO : (dev s).own.find? x = some ciO := by
      rw [← hOn]; exact own_find?_of_decl hndO hp hO
    have hfC : (dev s).context.find? x = none := by
      rw [← hOn]; exact hfr ciO (mem_recsC.mpr ⟨p, hp, hO⟩)
    refine ⟨ciO, hfO, hfC, ⟨p, hp, hO⟩, hR, ?_, ?_, hred⟩
    · rw [hi.key_context x (by rw [hx]; rfl), hs]
      exact hsK.key_own x ciO hfO hfC
    · rw [Module.context_eq, htabC he hi.nodup, Module.own_eq, ht,
        streamEnv_findTable? hndL hpL (by rw [← hOn]; exact List.mem_map_of_mem hO)]
  rcases hpres with ⟨hc, ht⟩ | ⟨hst, hnr⟩
  · exact fin ciC (hc ▸ hce) hnm (.inl rfl) ht fun _ => rfl
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
        fun h => absurd h (hnr x (by rw [← hnm]; exact List.mem_singleton_self _))
    | thmDecl cv v =>
      obtain rfl := hunres cv (.inr (.inl ⟨v, rfl⟩)) hce
      exact fin (.thmInfo cv) List.mem_cons_self hnm (.inr ⟨rfl, rfl⟩) rfl
        fun h => absurd h (hnr x (by rw [← hnm]; exact List.mem_singleton_self _))
    | opaqueDecl cv v =>
      obtain rfl := hunres cv (.inr (.inr ⟨v, rfl⟩)) hce
      exact fin (.axiomInfo cv) List.mem_cons_self hnm (.inl rfl) rfl fun _ => rfl
    | axiomDecl cv => exact fin ciC hce hnm (.inl rfl) rfl fun _ => rfl
    | quotDecl k cv => exact fin ciC hce hnm (.inl rfl) rfl fun _ => rfl
    | indDecl b nP => exact fin ciC hce hnm (.inl rfl) rfl fun _ => rfl

/-- A context name's table in the own environment is its context table. -/
theorem own_findTable?_of_context {j : Nat} (hnd : NodupNames (dev j).own)
    (hndC : NodupNames (dev j).context) {x : Name} (hx : ((dev j).context.find? x).isSome = true) :
    (dev j).own.findTable? x = (dev j).context.findTable? x := by
  obtain ⟨e, he, ci, hci, hn, -⟩ := streamEnv_isSome (L := (dev j).ctx) hx
  have hxe : x ∈ (declConstants e).map (·.name) := List.mem_map.mpr ⟨ci, hci, hn⟩
  rw [Module.own_eq] at hnd ⊢
  rw [Module.context_eq, streamEnv_findTable? hnd (List.mem_append_left _ he) hxe,
    streamEnv_findTable? hndC he hxe]

/-- **The owner of a stored name**, in any module of a development passing the local checks: the
module that declared it among its own records, whose constant the stored copy refines, under
that module's key, with its table. -/
theorem ownerOf {i : Nat} (hok : ∀ j ≤ i, LocalOk .verified pins dev j) {j : Nat} (hj : j ≤ i)
    {x : Name} {ci : ConstantInfo} (hx : (dev j).own.find? x = some ci) :
    ∃ t ≤ j, ∃ ciO, (dev t).own.find? x = some ciO ∧ (dev t).context.find? x = none ∧
      (∃ p ∈ (dev t).decls, ciO ∈ declConstants p) ∧ Refines ci ciO ∧
      (dev j).key x = (dev t).ownKey t x ciO ∧
      (dev j).own.findTable? x = (dev t).own.findTable? x := by
  have hK := (hok j hj).importOk
  rcases own_find?_cases hK hx with hc | ⟨hc, p, hp, hci⟩
  · have hlt := hK.src_lt x (by rw [hc]; rfl)
    have hs := hok ((dev j).src x) (by omega)
    obtain ⟨ciO, h1, h2, h3, h4, h5, h6, -⟩ := owner hK hs.iface hs.importOk hc
    exact ⟨_, by omega, ciO, h1, h2, h3, h4, h5,
      (own_findTable?_of_context (ImportOk.chain hK).1 hK.nodup (by rw [hc]; rfl)).trans h6⟩
  · exact ⟨j, Nat.le_refl j, ci, hx, hc, ⟨p, hp, hci⟩, .inl rfl, hK.key_own x ci hx hc, rfl⟩

theorem flagsOk_mem {mode : CheckMode} {proofs : Name → Bool} :
    ∀ {E : Env} {ds : List Declaration}, FlagsOk mode pins proofs E ds →
    ∀ d ∈ ds, ∀ n ∈ declNames d, proofs n = true → ∃ E', ProofDecl mode pins E' d := by
  intro E ds h
  induction h with
  | nil => exact fun _ h => nomatch h
  | cons hflag rest ih =>
    intro d hd n hn hp
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨_, hflag n hn hp⟩
    · exact ih d hd n hn hp

/-- A proof's record is a value kind: its constants are statement kinds, and it has no table. -/
theorem ProofDecl.kinds {mode : CheckMode} {E : Env} {d : Declaration}
    (h : ProofDecl mode pins E d) :
    (∀ ci ∈ declConstants d, ci.isStmtKind = true) ∧ declTables d = [] := by
  cases d with
  | defnDecl cv v hint => exact ⟨fun ci hci => by rw [List.mem_singleton.mp hci]; rfl, rfl⟩
  | thmDecl cv v => exact ⟨fun ci hci => by rw [List.mem_singleton.mp hci]; rfl, rfl⟩
  | opaqueDecl cv v => exact ⟨fun ci hci => by rw [List.mem_singleton.mp hci]; rfl, rfl⟩
  | axiomDecl _ => exact h.elim
  | quotDecl _ _ => exact h.elim
  | indDecl _ _ => exact h.elim

theorem Refines.stmtKind {ci ci' : ConstantInfo} (h : Refines ci ci') (h' : ci'.isStmtKind = true) :
    ci.isStmtKind = true := by
  rcases h with rfl | ⟨rfl, -⟩
  · exact h'
  · rfl

theorem refines_alike {ci ci' ciO : ConstantInfo} (h : Refines ci ciO) (h' : Refines ci' ciO) :
    Alike ci ci' := by
  rcases h with rfl | ⟨rfl, hk⟩
  · exact (h'.alike).symm
  · rcases h' with rfl | ⟨rfl, -⟩
    · exact .inr ⟨rfl, rfl, hk⟩
    · exact .inl rfl

/-- **Two copies under one key are alike, with one table.** -/
theorem copies_alike {i : Nat} (hok : ∀ j ≤ i, LocalOk .verified pins dev j) {j j' : Nat}
    (hj : j ≤ i) (hj' : j' ≤ i) {x : Name} {ci ci' : ConstantInfo}
    (h : (dev j).own.find? x = some ci) (h' : (dev j').own.find? x = some ci')
    (hk : (dev j).key x = (dev j').key x) :
    Alike ci ci' ∧ (dev j).own.findTable? x = (dev j').own.findTable? x := by
  obtain ⟨t, ht, ciO, hO, -, ⟨p, hp, hcp⟩, hR, hkey, htab⟩ := ownerOf hok hj h
  obtain ⟨t', ht', ciO', hO', -, ⟨p', hp', hcp'⟩, hR', hkey', htab'⟩ := ownerOf hok hj' h'
  rw [hkey, hkey'] at hk
  unfold Module.ownKey at hk
  -- a proof's record has statement kinds and no table
  have hproof : ∀ {t : Nat} {p : Declaration} {ciO : ConstantInfo}, t ≤ i →
      p ∈ (dev t).decls → ciO ∈ declConstants p → ciO.name = x → (dev t).proofs x = true →
      ciO.isStmtKind = true ∧ (dev t).own.findTable? x = none := by
    intro t p ciO ht hp hcp hn hpr
    have hK := (hok t ht).importOk
    obtain ⟨E', hpd⟩ := flagsOk_mem hK.flags p hp x (List.mem_map.mpr ⟨ciO, hcp, hn⟩) hpr
    obtain ⟨hk1, hk2⟩ := ProofDecl.kinds hpd
    refine ⟨hk1 ciO hcp, ?_⟩
    have hnd := (ImportOk.chain hK).1
    rw [Module.own_eq] at hnd ⊢
    rw [streamEnv_findTable? hnd (List.mem_append_right _ hp)
      (List.mem_map.mpr ⟨ciO, hcp, hn⟩), hk2]
    rfl
  have hn : ciO.name = x := ConLeche.Env.find?_name hO
  have hn' : ciO'.name = x := ConLeche.Env.find?_name hO'
  split at hk <;> split at hk
  · -- two proofs of one statement
    rename_i hpr hpr'
    obtain ⟨hs, hT⟩ := hproof (by omega) hp hcp hn hpr
    obtain ⟨hs', hT'⟩ := hproof (by omega) hp' hcp' hn' hpr'
    injection hk with hk
    injection hk with hl hty
    refine ⟨.inr ⟨?_, hR.stmtKind hs, hR'.stmtKind hs'⟩, by rw [htab, htab', hT, hT']⟩
    rw [hR.alike.cv, hR'.alike.cv]
    have hc1 : ciO.toConstantVal.name = ciO'.toConstantVal.name := by
      show ciO.name = ciO'.name
      rw [hn, hn']
    cases h1 : ciO.toConstantVal
    cases h2 : ciO'.toConstantVal
    rw [h1, h2] at hc1 hl hty
    simp_all
  · exact nomatch hk
  · exact nomatch hk
  · -- one home
    injection hk with htt
    subst htt
    rw [hO] at hO'
    obtain rfl := Option.some.inj hO'
    exact ⟨refines_alike hR hR', by rw [htab, htab']⟩

/-! ## The reading at a module -/

/-- The lookup in a filtered environment. -/
theorem find?_filter_name {l : List ConstantInfo} {t : List ProjTable} {q : Name → Bool}
    {n : Name} :
    (⟨l.filter fun c => q c.toConstantVal.name, []⟩ : Env).find? n =
      if q n = true then (⟨l, t⟩ : Env).find? n else none := by
  induction l with
  | nil => split <;> rfl
  | cons c l ih =>
    have e1 : ∀ (cs : List ConstantInfo) (ts : List ProjTable),
        (⟨cs, ts⟩ : Env).find? n = cs.find? (·.name == n) := fun _ _ => rfl
    rw [e1] at ih ⊢
    rw [e1, List.filter_cons]
    by_cases hc : c.name = n
    · have hc' : c.toConstantVal.name = n := hc
      by_cases hq : q n = true
      · simp [hc', hq, hc]
      · have hqf : q c.toConstantVal.name = false := by rw [hc']; simpa using hq
        rw [ite_eq_right hq] at ih ⊢
        simpa [hqf] using ih
    · have hc' : (c.name == n) = false := by simpa using hc
      split <;> simp only [List.find?_cons, hc'] <;> exact ih

/-- **What module `i` reads alike from module `b`**: the names its context stores under `b`'s key,
at `b`'s copies. -/
theorem readsAlike_find? {i b : Nat} {d : Name} :
    (readsAlike dev i b).find? d =
      if ((dev i).context.find? d).isSome = true ∧ (dev i).key d = (dev b).key d then
        (dev b).own.find? d else none := by
  have h := find?_filter_name (l := (dev b).own.consts) (t := (dev b).own.tables) (n := d)
    (q := fun n => ((dev i).context.find? n).isSome && (dev i).key n == (dev b).key n)
  refine h.trans ?_
  by_cases hq : ((dev i).context.find? d).isSome = true ∧ (dev i).key d = (dev b).key d
  · rw [ite_eq_left (show _ = true by simp [hq.1, hq.2]), ite_eq_left hq]
  · rw [ite_eq_right (show ¬ _ = true by simpa using hq), ite_eq_right hq]

/-- **The reading at a module passing the local checks** (the fields of `CtxRead` that need no
record). -/
theorem reading_basic {i : Nat} (hok : ∀ j ≤ i, LocalOk .verified pins dev j) :
    let E := fun n => (dev ((dev i).src n)).own
    let R := fun n => readsAlike dev i ((dev i).src n)
    (∀ n ci, (dev i).context.find? n = some ci → ∃ ci', (E n).find? n = some ci' ∧ Refines ci ci') ∧
    (∀ n d ci, (R n).find? d = some ci → (E n).find? d = some ci ∧
      ((dev i).context.find? d).isSome = true) ∧
    (∀ n, ((dev i).context.find? n).isSome = true → ((R n).find? n).isSome = true) ∧
    (∀ n d, ((dev i).context.find? n).isSome = true → ((R n).find? d).isSome = true →
      (∃ ciC ciE, (dev i).context.find? d = some ciC ∧ (E n).find? d = some ciE ∧ Alike ciC ciE) ∧
      (dev i).context.findTable? d = (E n).findTable? d) := by
  intro E R
  have hK := (hok i (Nat.le_refl i)).importOk
  have hndO := (ImportOk.chain hK).1
  have hsrc : ∀ n, ((dev i).context.find? n).isSome = true → (dev i).src n ≤ i := fun n h =>
    Nat.le_of_lt (hK.src_lt n h)
  refine ⟨fun n ci h => ?_, fun n d ci h => ?_, fun n h => ?_, fun n d hn hd => ?_⟩
  · have hs := hok _ (hsrc n (by rw [h]; rfl))
    obtain ⟨ciO, h1, -, -, h4, -⟩ := owner hK hs.iface hs.importOk h
    exact ⟨ciO, h1, h4⟩
  · have h' := h
    simp only [R, readsAlike_find?] at h'
    split at h'
    · next hc => exact ⟨h', hc.1⟩
    · exact nomatch h'
  · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
    have hs := hok _ (hsrc n h)
    obtain ⟨ciO, h1, -⟩ := owner hK hs.iface hs.importOk hci
    simp only [R, readsAlike_find?]
    rw [ite_eq_left (show _ ∧ _ from ⟨h, hK.key_context n h⟩), h1]; rfl
  · have hd' := hd
    simp only [R, readsAlike_find?] at hd'
    split at hd'
    · next hc =>
      obtain ⟨ciC, hC⟩ := Option.isSome_iff_exists.mp hc.1
      obtain ⟨ciE, hE⟩ := Option.isSome_iff_exists.mp hd'
      have hsn := hsrc n hn
      obtain ⟨ha, ht⟩ := copies_alike hok (Nat.le_refl i) hsn (own_find?_of_context hndO hC) hE hc.2
      refine ⟨⟨ciC, ciE, hC, hE, ha⟩, ?_⟩
      rw [← own_findTable?_of_context hndO hK.nodup hc.1]
      exact ht
    · exact nomatch hd'

/-- **What a context constant's laws read is read alike** (`CtxRead.scope`): its record's reads
(`ImportOk.reads`), with the former's table its record's. -/
theorem reading_scope {i : Nat} (hK : ImportOk .verified pins dev i) {n : Name} {ci : ConstantInfo}
    (h : (dev i).context.find? n = some ci) :
    EntryScopedP (fun d => ((readsAlike dev i ((dev i).src n)).find? d).isSome = true)
      (dev i).context n ci := by
  obtain ⟨e, he, hce, hnm⟩ := streamEnv_find?_some (L := (dev i).ctx) h
  have hxe : n ∈ declNames e := List.mem_map.mpr ⟨ci, hce, hnm⟩
  obtain ⟨hents, htabs⟩ := hK.reads e he n hxe
  obtain ⟨h1, h2, h3, h4, h5⟩ := hents ci hce
  have hR := fun {x : Expr} (hx : x.constsResolve (readsAlike dev i ((dev i).src n)) = true) =>
    (Expr.constsResolve_iff _).mp hx
  refine ⟨hR h1, fun cv v hh he' => hR (h2 cv v hh he'),
    fun cv mI rP isK rules he' r hr => ?_, fun cv caps he' => ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := h3 cv mI rP isK rules he' r hr
    exact ⟨hR a, b, fun lvls pins hf q hq => hR (c lvls pins hf q hq)⟩
  · obtain ⟨a, b⟩ := h4 cv caps he'
    refine ⟨a, b, fun t ht => ?_⟩
    have ht' : (declTables e).find? (·.structName == n) = some t := by
      rw [← streamEnv_findTable? hK.nodup he hxe]; exact ht
    obtain ⟨c1, c2⟩ := htabs t (List.mem_of_find?_eq_some ht')
    exact ⟨c1, fun b hb => hR (c2 b hb)⟩
  · intro d hd; rw [← hnm] at hd; exact h5 d hd

/-- **A context constant at a `reduce*` name is its source's.** -/
theorem reading_reduce {i : Nat} (hok : ∀ j ≤ i, LocalOk .verified pins dev j) {n : Name}
    {ci : ConstantInfo} (h : (dev i).context.find? n = some ci) (hr : n ∈ reduceOpNames) :
    (dev ((dev i).src n)).own.find? n = some ci := by
  have hK := (hok i (Nat.le_refl i)).importOk
  have hs := hok ((dev i).src n) (Nat.le_of_lt (hK.src_lt n (by rw [h]; rfl)))
  obtain ⟨ciO, h1, -, -, -, -, -, h7⟩ := owner hK hs.iface hs.importOk h
  rw [h1, h7 hr]

/-! ## What a record's constants say of its names -/

/-- A pinned block's formers list only the block's names as constructors (checked per kind). -/
@[expose] def pinCtorsOk (pins : List ConstantInfo) : Bool :=
  pins.all fun pin => match pin with
    | .indInfo _ caps => caps.ctors.all fun x => (pins.map (·.name)).contains x
    | _ => true

theorem pinCtorsOk_basis : ∀ kind ∈ [BasisKind.eqK, .natK, .emptyK, .falseK],
    pinCtorsOk kind.decls = true := by decide

theorem atLps_indInfo {pin : ConstantInfo} {ps : List Name} {cv : ConstantVal} {caps : IndCaps}
    (h : pin.atLps ps = .indInfo cv caps) : ∃ cv', pin = .indInfo cv' caps := by
  cases pin <;> simp [ConstantInfo.atLps] at h
  case indInfo cv' caps' => exact ⟨cv', by rw [h.2]⟩

theorem quotPins_noCtors : BasisKind.quotK.decls.all (fun pin => match pin with
    | .indInfo _ caps => caps.ctors.isEmpty
    | _ => true) = true := by decide

theorem quotPin_mem (k : QuotKind) : quotPin k ∈ BasisKind.quotK.decls := by
  cases k <;> decide

theorem blockRecs_not_ind (p : BlockShape) :
    ∀ (l : List RecShape) {cv : ConstantVal} {caps : IndCaps}, .indInfo cv caps ∉ blockRecs p l
  | [], _, _, h => nomatch h
  | rc :: rest, cv, caps, h => by
    simp only [blockRecs, List.mem_cons] at h
    rcases h with h | h
    · exact nomatch h
    · exact blockRecs_not_ind p rest h

/-- A quotient record's constant lists no constructor. -/
theorem quotAt_ctors {k : QuotKind} {ps : ConstantVal} {cv : ConstantVal} {caps : IndCaps}
    (h : quotAt k ps = .indInfo cv caps) : caps.ctors = [] := by
  obtain ⟨cvp, hp⟩ := atLps_indInfo h
  have := List.all_eq_true.mp quotPins_noCtors _ (quotPin_mem k)
  rw [hp] at this
  simpa using this

/-- **A former's constructors are its record's names.** -/
theorem declConstants_ctors {e : Declaration} {cv : ConstantVal} {caps : IndCaps}
    (h : .indInfo cv caps ∈ declConstants e) :
    ∀ x ∈ caps.ctors, x ∈ (declConstants e).map (·.name) := by
  intro x hx
  cases e with
  | indDecl block nP =>
    simp only [declConstants] at h ⊢
    split at h
    · next kind hk =>
      have hn := List.find?_some hk
      simp only [beq_iff_eq] at hn
      have hmem : kind ∈ [BasisKind.eqK, .natK, .emptyK, .falseK] := List.mem_of_find?_eq_some hk
      have hnames := atBlock_names kind.decls block hn
      show x ∈ (kind.atBlock block).map (·.name)
      unfold BasisKind.atBlock
      rw [hnames]
      obtain ⟨j, hj⟩ := List.getElem?_of_mem h
      obtain ⟨pin, c, hpin, -, hpe⟩ := List.getElem?_zipWith_eq_some.mp hj
      obtain ⟨cv', rfl⟩ := atLps_indInfo hpe
      have hpin : ConstantInfo.indInfo cv' caps ∈ kind.decls := List.mem_of_getElem? hpin
      have hok := pinCtorsOk_basis kind hmem
      unfold pinCtorsOk at hok
      have := List.all_eq_true.mp hok _ hpin
      simp only [List.all_eq_true, List.contains_iff_mem] at this
      exact this x hx
    · split at h
      · next p hp =>
        simp only [blockConstants, List.mem_append] at h
        rcases h with (h | h) | h
        · unfold blockFormers at h
          obtain ⟨⟨cvm, i⟩, hi, he⟩ := List.mem_map.mp h
          simp only [ConstantInfo.indInfo.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hlt : i < p.members.length := by
            have := List.mem_zipIdx hi
            simp at this
            omega
          rw [blockConstants_names]
          refine List.mem_append_left _ (List.mem_append_right _ ?_)
          have hsub : ∀ ms ∈ p.members, ∀ c ∈ ms.ctors, c ∈ p.allCtors := fun ms hms c hc =>
            List.mem_flatten.mpr ⟨ms.ctors, List.mem_map.mpr ⟨ms, hms, rfl⟩, hc⟩
          have hm : p.members.getD i default ∈ p.members := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
            exact List.getElem_mem _
          have hcs : ∀ x ∈ (blockCapsAt p i (blockIsRec p)).ctors,
              x ∈ (p.members.getD i default).ctors.map (·.1.name) := by
            unfold blockCapsAt
            split <;> simp_all
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (hcs x hx)
          exact List.mem_map.mpr ⟨c, hsub _ hm c hc, rfl⟩
        · unfold blockCtors at h
          obtain ⟨c, -, he⟩ := List.mem_map.mp h
          exact nomatch he
        · exact absurd h (blockRecs_not_ind p p.recs)
      · exact absurd h (List.not_mem_nil)
  | quotDecl k cv' =>
    simp only [declConstants, List.mem_singleton] at h
    rw [quotAt_ctors h.symm] at hx
    exact absurd hx (List.not_mem_nil)
  | defnDecl _ _ _ => simp [declConstants] at h
  | thmDecl _ _ => simp [declConstants] at h
  | opaqueDecl _ _ => simp [declConstants] at h
  | axiomDecl cv' =>
    simp only [declConstants] at h
    split at h
    · rw [quotAt_ctors (List.mem_singleton.mp h).symm] at hx
      exact absurd hx (List.not_mem_nil)
    · split at h <;> simp at h

theorem blockTables_member (p : BlockShape) :
    ∀ (l : List MemberShape) {t : ProjTable}, t ∈ blockTables p l →
      ∃ ms ∈ l, t.structName = ms.declared.name
  | [], _, h => nomatch h
  | ms :: rest, t, h => by
    simp only [blockTables] at h
    split at h
    · split at h
      · rcases List.mem_cons.mp h with rfl | h
        · exact ⟨ms, List.mem_cons_self, rfl⟩
        · obtain ⟨m, hm, he⟩ := blockTables_member p rest h
          exact ⟨m, List.mem_cons_of_mem _ hm, he⟩
      · obtain ⟨m, hm, he⟩ := blockTables_member p rest h
        exact ⟨m, List.mem_cons_of_mem _ hm, he⟩
    · obtain ⟨m, hm, he⟩ := blockTables_member p rest h
      exact ⟨m, List.mem_cons_of_mem _ hm, he⟩

/-- **A record's table is one of its formers'.** -/
theorem declTables_former {e : Declaration} {t : ProjTable} (ht : t ∈ declTables e) :
    ∃ cv caps, .indInfo cv caps ∈ declConstants e ∧ cv.name = t.structName := by
  cases e with
  | indDecl block nP =>
    simp only [declTables, declConstants] at ht ⊢
    split at ht
    · exact absurd ht (List.not_mem_nil)
    · split at ht
      · next p hp =>
        obtain ⟨ms, hms, he⟩ := blockTables_member p p.members ht
        obtain ⟨i, hi⟩ := List.getElem_of_mem hms
        refine ⟨ms.declared, blockCapsAt p i (blockIsRec p), ?_, he.symm⟩
        simp only [blockConstants, blockFormers, List.mem_append]
        refine .inl (.inl (List.mem_map.mpr ⟨(ms.declared, i), ?_, rfl⟩))
        rw [List.mem_zipIdx_iff_getElem?]
        obtain ⟨hlt, rfl⟩ := hi
        simp [List.getElem?_eq_getElem hlt]
      · exact absurd ht (List.not_mem_nil)
  | _ => simp [declTables] at ht

theorem find?_of_mem_nodupKey {α : Type} (f : α → Name) {L : List α} (hnd : (L.map f).Nodup)
    {t : α} (ht : t ∈ L) : L.find? (f · == f t) = some t := by
  induction L with
  | nil => exact absurd ht (List.not_mem_nil)
  | cons a L ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ht with rfl | ht
    · simp
    · have hne : f a ≠ f t := fun h => hnd.1 (h ▸ List.mem_map_of_mem ht)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih hnd.2 ht

/-- **A stream's tables are its formers'**, each found at its structure. -/
theorem stream_tables_mem {L : List Declaration} (hnd : NodupNames (streamEnv L))
    {t : ProjTable} (ht : t ∈ (streamEnv L).tables) :
    (streamEnv L).findTable? t.structName = some t ∧
      ∃ cv caps, (streamEnv L).find? t.structName = some (.indInfo cv caps) := by
  rw [streamEnv_empty_tables, List.mem_reverse] at ht
  obtain ⟨e, he, hte⟩ := List.mem_flatMap.mp ht
  obtain ⟨cv, caps, hci, hname⟩ := declTables_former hte
  have hfind := streamEnv_find?_of_mem hnd he hci
  have hn : (ConstantInfo.indInfo cv caps).name = t.structName := hname
  rw [hn] at hfind
  refine ⟨?_, cv, caps, hfind⟩
  have hxe : t.structName ∈ (declConstants e).map (·.name) :=
    List.mem_map.mpr ⟨_, hci, hn⟩
  rw [streamEnv_findTable? hnd he hxe]
  have hrec := nodup_recs hnd
  have hnde : ((declConstants e).map (·.name)).Nodup := by
    unfold recsC at hrec
    obtain ⟨A, B, rfl⟩ := List.append_of_mem he
    simp only [List.flatMap_append, List.flatMap_cons, List.map_append] at hrec
    exact (List.nodup_append.mp (List.nodup_append.mp hrec).2.1).1
  exact find?_of_mem_nodupKey (·.structName) ((declTables_sublist e).nodup hnde) hte

/-! ## An inductive copy arrives with its record -/

theorem not_ind_of_stmt {ci : ConstantInfo} (h : ci.isStmtKind = true) : ci.isIndKind = false := by
  cases ci <;> simp_all [ConstantInfo.isStmtKind, ConstantInfo.isIndKind]

/-- An inductive record's names are never flagged proofs. -/
theorem not_flagged_of_ind {j : Nat} (hK : ImportOk .verified pins dev j) {p : Declaration}
    (hp : p ∈ (dev j).decls) {ci : ConstantInfo} (hci : ci ∈ declConstants p)
    (hk : ci.isIndKind = true) {c : ConstantInfo} (hc : c ∈ declConstants p) :
    (dev j).proofs c.name = false := by
  cases h : (dev j).proofs c.name with
  | false => rfl
  | true =>
    obtain ⟨E', hpd⟩ := flagsOk_mem hK.flags p hp c.name (List.mem_map_of_mem hc) h
    have := not_ind_of_stmt ((ProofDecl.kinds hpd).1 ci hci)
    rw [hk] at this; exact nomatch this

/-- An own record's constant, not flagged, is under the module's home key. -/
theorem key_of_own {j : Nat} (hK : ImportOk .verified pins dev j) {p : Declaration}
    (hp : p ∈ (dev j).decls) {c : ConstantInfo} (hc : c ∈ declConstants p)
    (hpr : (dev j).proofs c.name = false) :
    (dev j).own.find? c.name = some c ∧ (dev j).context.find? c.name = none ∧
      (dev j).key c.name = .home j := by
  obtain ⟨hnd, hfr, -⟩ := ImportOk.chain hK
  have h1 := own_find?_of_decl hnd hp hc
  have h2 := hfr c (mem_recsC.mpr ⟨p, hp, hc⟩)
  refine ⟨h1, h2, ?_⟩
  rw [hK.key_own _ c h1 h2]
  simp [Module.ownKey, hpr]

/-- **The record of an inductive copy**: a module's copy of an inductive kind is installed by a
record equal (in constants and tables) to its owner's own record, every constant of which it
stores under the owner's home key; a context record also reads what it reads as the owner. -/
theorem indRecord {i : Nat} (hok : ∀ j ≤ i, LocalOk .verified pins dev j) {j : Nat} (hj : j ≤ i)
    {x : Name} {ci : ConstantInfo} (hx : (dev j).own.find? x = some ci) (hk : ci.isIndKind = true) :
    ∃ t ≤ j, ∃ p ∈ (dev t).decls, ∃ r : Declaration, ci ∈ declConstants r ∧
      declConstants r = declConstants p ∧ declTables r = declTables p ∧
      (∀ c ∈ declConstants r, (dev j).own.find? c.name = some c ∧ (dev j).key c.name = .home t) ∧
      ((r ∈ (dev j).ctx ∧ RecordScoped (readsAlike dev j t) r) ∨ (t = j ∧ r ∈ (dev j).decls)) := by
  have hK := (hok j hj).importOk
  obtain ⟨hndO, -, -⟩ := ImportOk.chain hK
  rcases own_find?_cases hK hx with hc | ⟨-, p, hp, hcp⟩
  · obtain ⟨e, he, hce, hnm⟩ := streamEnv_find?_some (L := (dev j).ctx) hc
    have hxe : x ∈ declNames e := List.mem_map.mpr ⟨ci, hce, hnm⟩
    have hlt := hK.src_lt x (by rw [hc]; rfl)
    have hs := hok ((dev j).src x) (by omega)
    obtain ⟨p, hp, hpres⟩ := hs.iface.presents e (hK.presented e he x hxe)
    -- an inductive copy's record is its owner's record itself
    have heq : declConstants e = declConstants p ∧ declTables e = declTables p := by
      rcases hpres with h | ⟨rfl, -⟩
      · exact h
      · cases p with
        | defnDecl cv v hint | thmDecl cv v | opaqueDecl cv v =>
          exfalso
          obtain ⟨fe, r, hr⟩ := (ImportOk.chain hs.importOk).2.2 _ hp
          have hres := checkDeclStepC_unreserved hr cv (by simp)
          have hq : cv.name ≠ quotSoundName := by
            intro h; rw [h] at hres; exact absurd hres (by decide)
          simp only [stmtOf, declConstants, hq, ↓reduceIte] at hce
          split at hce
          · exact absurd hce (List.not_mem_nil)
          · rw [List.mem_singleton.mp hce] at hk; exact nomatch hk
        | axiomDecl _ | quotDecl _ _ | indDecl _ _ => exact ⟨rfl, rfl⟩
    refine ⟨(dev j).src x, by omega, p, hp, e, hce, heq.1, heq.2, fun c hc' => ?_,
      .inl ⟨he, by simpa using hK.reads e he x hxe⟩⟩
    have hcp : c ∈ declConstants p := heq.1 ▸ hc'
    have hcf : (dev j).context.find? c.name = some c :=
      streamEnv_find?_of_mem hK.nodup he hc'
    refine ⟨own_find?_of_context hndO hcf, ?_⟩
    have hsrc : (dev j).src c.name = (dev j).src x :=
      hK.one_src e he c.name (List.mem_map_of_mem hc') x hxe
    rw [hK.key_context c.name (by rw [hcf]; rfl), hsrc]
    exact (key_of_own hs.importOk hp hcp
      (not_flagged_of_ind hs.importOk hp (heq.1 ▸ hce) hk hcp)).2.2
  · refine ⟨j, Nat.le_refl j, p, hp, p, hcp, rfl, rfl, fun c hc' => ?_, .inr ⟨rfl, hp⟩⟩
    obtain ⟨h1, -, h3⟩ := key_of_own hK hp hc' (not_flagged_of_ind hK hp hcp hk hc')
    exact ⟨h1, h3⟩

end

end ConLeche.Model.Modular
