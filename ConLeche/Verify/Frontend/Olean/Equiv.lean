module

public import ConLeche.Verify.Frontend.Olean.Engine

public section

/-!
# The fast decoder is the specification (task #371)

**`decodeModuleSpec_eq_fast : @decodeModuleSpec = @decodeModuleFast`**:
on every region, from every root pointer, the fast olean decoder
(`ConLeche/Frontend/Olean/Fast.lean`) returns exactly what the
specification (`ConLeche/Frontend/Olean/Spec.lean`) returns — the same
module, or failure on the same inputs.  No hypothesis about the bytes:
both sides define the reading.  The theorem is `@[csimp]`: the driver
(`ConLeche/Driver/Run.lean`) passes `decodeModuleSpec` to the reader,
and the compiler substitutes the fast decoder on the strength of the
equality.  Nothing is `implemented_by`.

The proof: both read the same skeletons (`moduleSkel`, `constSkel`,
shared code), and the fast decoder's memo answers every name and
expression root with the specification's value when the two passes
succeed, while a failing pass means some root does not read
(`runPasses_spec`, `ConLeche/Verify/Frontend/Olean/Engine.lean`) — and
then the specification fails too, at that root.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## `Option` traversals -/

theorem listMapM_congr {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.mapM_cons]
    rw [h x (by simp), listMapM_congr l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem mapM_none {α β : Type} {f : α → Option β} :
    ∀ (l : List α), (∃ x ∈ l, f x = none) → l.mapM f = none
  | [], ⟨_, h, _⟩ => by simp at h
  | x :: l, ⟨y, hy, hn⟩ => by
    simp only [List.mapM_cons]
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · simp [hn]
    · rw [mapM_none l ⟨y, hy, hn⟩]
      cases f x <;> rfl

theorem mapM_bind {α β γ : Type} (f : α → Option β) (g : β → Option γ) :
    ∀ (l : List α), l.mapM (fun x => f x >>= g) = l.mapM f >>= fun bs => bs.mapM g
  | [] => rfl
  | x :: l => by
    have ih := mapM_bind f g l
    simp only [List.mapM_cons, ih]
    cases hx : f x with
    | none => rfl
    | some b =>
      cases hl : List.mapM f l with
      | none =>
        simp only [bind, Option.bind]
        cases g b <;> simp
      | some bs =>
        simp only [bind, Option.bind, pure, List.mapM_cons]

/-! ## Constants -/

theorem CEntryF.mapM_congr {N E N' E' : Type} {fn fn' : N → Option N'} {fe fe' : E → Option E'}
    (c : CEntryF N E)
    (hn : ∀ x ∈ c.names, fn x = fn' x) (he : ∀ x ∈ c.exprs, fe x = fe' x) :
    c.mapM fn fe = c.mapM fn' fe' := by
  rcases c with ⟨name, lps, type, kind⟩
  have hk : kind.mapM fn fe = kind.mapM fn' fe' := by
    cases kind <;> simp only [CKindF.mapM]
    case defn v h s => rw [he v (by simp [CEntryF.exprs])]
    case thm v all =>
      rw [he v (by simp [CEntryF.exprs]),
        listMapM_congr all (fun x hx => hn x (by simp [CEntryF.names, hx]))]
    case opaq v u => rw [he v (by simp [CEntryF.exprs])]
    case induct np ni all cs nn a b c =>
      rw [listMapM_congr all (fun x hx => hn x (by simp [CEntryF.names, hx])),
        listMapM_congr cs (fun x hx => hn x (by simp [CEntryF.names, hx]))]
    case ctor ind ci np nf u => rw [hn ind (by simp [CEntryF.names])]
    case recur all np ni nmo nmi rules k u =>
      have hr : (rules.mapM fun (c, n, e) => do
            let c ← fn c
            let e ← fe e
            pure (c, n, e)) =
          (rules.mapM fun (c, n, e) => do
            let c ← fn' c
            let e ← fe' e
            pure (c, n, e)) :=
        listMapM_congr rules (fun ⟨cn, nf, e⟩ hx => by
          have h1 := hn cn (List.mem_append_right _ (List.mem_append_right _
            (List.mem_map_of_mem (f := fun x : N × Nat × E => x.1) hx)))
          have h2 := he e (List.mem_cons_of_mem _
            (List.mem_map_of_mem (f := fun x : N × Nat × E => x.2.2) hx))
          simp only [h1, h2])
      rw [listMapM_congr all (fun x hx => hn x (by simp [CEntryF.names, hx])), hr]
  simp only [CEntryF.mapM, hk]
  rw [hn name (by simp [CEntryF.names]), he type (by simp [CEntryF.exprs]),
    listMapM_congr lps (fun x hx => hn x (by simp [CEntryF.names, hx]))]

theorem listMapM_some {α β : Type} {f : α → Option β} :
    ∀ (l : List α) {bs : List β}, l.mapM f = some bs → ∀ x ∈ l, (f x).isSome
  | [], _, _, x, hx => by simp at hx
  | y :: l, bs, h, x, hx => by
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hy : f y with
    | none => rw [hy] at h; cases h
    | some b =>
      rw [hy] at h
      cases hl : List.mapM f l with
      | none => rw [hl] at h; cases h
      | some bs' =>
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [hy]
        · exact listMapM_some l hl x hx

theorem bind_some_left {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem CEntryF.mapM_some {N E N' E' : Type} {fn : N → Option N'} {fe : E → Option E'}
    (c : CEntryF N E) {d : CEntryF N' E'} (h : c.mapM fn fe = some d) :
    (∀ x ∈ c.names, (fn x).isSome) ∧ (∀ x ∈ c.exprs, (fe x).isSome) := by
  rcases c with ⟨name, lps, type, kind⟩
  simp only [CEntryF.mapM] at h
  obtain ⟨n', hn', h⟩ := bind_some_left h
  obtain ⟨lps', hl', h⟩ := bind_some_left h
  obtain ⟨t', ht', h⟩ := bind_some_left h
  obtain ⟨k', hk', _⟩ := bind_some_left h
  have hlps := listMapM_some lps hl'
  have base : ∀ x, x = name ∨ x ∈ lps → (fn x).isSome := by
    rintro x (rfl | hx)
    · simp [hn']
    · exact hlps x hx
  cases kind with
  | ax u =>
    refine ⟨fun x hx => base x (by simpa [CEntryF.names] using hx), fun x hx => ?_⟩
    simp only [CEntryF.exprs, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp [ht']
  | quot q =>
    refine ⟨fun x hx => base x (by simpa [CEntryF.names] using hx), fun x hx => ?_⟩
    simp only [CEntryF.exprs, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp [ht']
  | defn v hh sf =>
    simp only [CKindF.mapM] at hk'
    obtain ⟨v', hv', _⟩ := bind_some_left hk'
    refine ⟨fun x hx => base x (by simpa [CEntryF.names] using hx), fun x hx => ?_⟩
    simp only [CEntryF.exprs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [ht', hv']
  | opaq v uu =>
    simp only [CKindF.mapM] at hk'
    obtain ⟨v', hv', _⟩ := bind_some_left hk'
    refine ⟨fun x hx => base x (by simpa [CEntryF.names] using hx), fun x hx => ?_⟩
    simp only [CEntryF.exprs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [ht', hv']
  | thm v all =>
    simp only [CKindF.mapM] at hk'
    obtain ⟨v', hv', hk'⟩ := bind_some_left hk'
    obtain ⟨all', ha', _⟩ := bind_some_left hk'
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [CEntryF.names, List.cons_append, List.mem_cons, List.mem_append] at hx
      rcases hx with h | h | h
      · exact base x (Or.inl h)
      · exact base x (Or.inr h)
      · exact listMapM_some all ha' x h
    · simp only [CEntryF.exprs, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [ht', hv']
  | induct np ni all cs nn a b c =>
    simp only [CKindF.mapM] at hk'
    obtain ⟨all', ha', hk'⟩ := bind_some_left hk'
    obtain ⟨cs', hc', _⟩ := bind_some_left hk'
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [CEntryF.names, List.cons_append, List.mem_cons, List.mem_append] at hx
      rcases hx with h | h | h | h
      · exact base x (Or.inl h)
      · exact base x (Or.inr h)
      · exact listMapM_some all ha' x h
      · exact listMapM_some cs hc' x h
    · simp only [CEntryF.exprs, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; simp [ht']
  | ctor ind ci np nf uu =>
    simp only [CKindF.mapM] at hk'
    obtain ⟨i', hi', _⟩ := bind_some_left hk'
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [CEntryF.names, List.cons_append, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h
      · exact base x (Or.inl h)
      · exact base x (Or.inr h)
      · subst h; simp [hi']
    · simp only [CEntryF.exprs, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; simp [ht']
  | recur all np ni nmo nmi rules kk uu =>
    simp only [CKindF.mapM] at hk'
    obtain ⟨all', ha', hk'⟩ := bind_some_left hk'
    obtain ⟨rules', hr', _⟩ := bind_some_left hk'
    have hrs := listMapM_some rules hr'
    have hrule : ∀ x ∈ rules, (fn x.1).isSome ∧ (fe x.2.2).isSome := by
      intro ⟨cn, nf, e⟩ hx
      have := hrs _ hx
      simp only at this
      cases h1 : fn cn with
      | none => rw [h1] at this; simp [bind, Option.bind] at this
      | some _ =>
        cases h2 : fe e with
        | none => rw [h1, h2] at this; simp [bind, Option.bind] at this
        | some _ => simp
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [CEntryF.names, List.cons_append, List.mem_cons, List.mem_append,
        List.mem_map] at hx
      rcases hx with h | h | h | ⟨y, hy, rfl⟩
      · exact base x (Or.inl h)
      · exact base x (Or.inr h)
      · exact listMapM_some all ha' x h
      · exact (hrule y hy).1
    · simp only [CEntryF.exprs, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · simp [ht']
      · exact (hrule y hy).2

/-! ## The module -/

theorem isSome_iff_exists' {α : Type} {o : Option α} : o.isSome ↔ ∃ a, o = some a := by
  cases o <;> simp

/-- The specification, its constants read skeletons first. -/
theorem decodeModuleSpec_skels (r : Region) (root : UInt64) (consts : Bool) :
    decodeModuleSpec r root consts = (do
      let sk ← moduleSkel r root
      let skels ← if consts then sk.consts.mapM (constSkel r) else pure []
      let imports ← sk.imports.mapM (nameP r)
      let constants ← skels.mapM (CEntryF.mapM (nameP r) (exprP r))
      pure ⟨sk.isModule, imports.toArray, constants.toArray⟩) := by
  unfold decodeModuleSpec
  cases moduleSkel r root with
  | none => rfl
  | some sk =>
    simp only [bind, Option.bind]
    cases consts with
    | false =>
      simp only [Bool.false_eq_true, ite_false, pure]
      cases sk.imports.mapM (nameP r) <;> rfl
    | true =>
      simp only [ite_true]
      have hc : sk.consts.mapM (constSpec r) =
          sk.consts.mapM (constSkel r) >>= fun skels =>
            skels.mapM (CEntryF.mapM (nameP r) (exprP r)) :=
        mapM_bind (constSkel r) (CEntryF.mapM (nameP r) (exprP r)) sk.consts
      rw [hc]
      cases sk.imports.mapM (nameP r) <;> cases sk.consts.mapM (constSkel r) <;> rfl

theorem decode_inner (r : Region) (sk : ModSkel) (skels : List (CEntryF UInt64 UInt64)) :
    (do
      let st ← runPasses r (sk.imports ++ skels.flatMap CEntryF.names) (skels.flatMap CEntryF.exprs)
      let imports ← sk.imports.mapM (st.nameOf r)
      let constants ← skels.mapM (CEntryF.mapM (st.nameOf r) (st.exprOf r))
      pure (ModDecoded.mk sk.isModule imports.toArray constants.toArray)) =
    (do
      let imports ← sk.imports.mapM (nameP r)
      let constants ← skels.mapM (CEntryF.mapM (nameP r) (exprP r))
      pure (ModDecoded.mk sk.isModule imports.toArray constants.toArray)) := by
  have h := runPasses_spec r (sk.imports ++ skels.flatMap CEntryF.names)
    (skels.flatMap CEntryF.exprs)
  cases hrp : runPasses r (sk.imports ++ skels.flatMap CEntryF.names)
      (skels.flatMap CEntryF.exprs) with
  | some st =>
    rw [hrp] at h
    obtain ⟨hn, he⟩ := h
    have hi : sk.imports.mapM (st.nameOf r) = sk.imports.mapM (nameP r) :=
      listMapM_congr _ fun v hv => hn v (List.mem_append_left _ hv)
    have hc : skels.mapM (CEntryF.mapM (st.nameOf r) (st.exprOf r)) =
        skels.mapM (CEntryF.mapM (nameP r) (exprP r)) :=
      listMapM_congr _ fun c hc => CEntryF.mapM_congr c
        (fun v hv => hn v (List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hc, hv⟩)))
        (fun v hv => he v (List.mem_flatMap.mpr ⟨c, hc, hv⟩))
    simp only [bind, Option.bind, hi, hc]
  | none =>
    rw [hrp] at h
    simp only [bind, Option.bind]
    cases hi : sk.imports.mapM (nameP r) with
    | none => rfl
    | some is =>
      cases hcs : skels.mapM (CEntryF.mapM (nameP r) (exprP r)) with
      | none => rfl
      | some cs =>
        exfalso; apply h
        have hall := listMapM_some skels hcs
        have hent : ∀ c ∈ skels, (∀ x ∈ c.names, (nameP r x).isSome) ∧
            (∀ x ∈ c.exprs, (exprP r x).isSome) := by
          intro c hc
          obtain ⟨d, hd⟩ := isSome_iff_exists'.mp (hall c hc)
          exact CEntryF.mapM_some c hd
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · rcases List.mem_append.mp hv with hv | hv
          · exact listMapM_some _ hi v hv
          · obtain ⟨c, hc, hvc⟩ := List.mem_flatMap.mp hv
            exact (hent c hc).1 v hvc
        · obtain ⟨c, hc, hvc⟩ := List.mem_flatMap.mp hv
          exact (hent c hc).2 v hvc

theorem decodeModuleFast_eq (r : Region) (root : UInt64) (consts : Bool) :
    decodeModuleFast r root consts = decodeModuleSpec r root consts := by
  rw [decodeModuleSpec_skels]
  unfold decodeModuleFast
  cases moduleSkel r root with
  | none => rfl
  | some sk =>
    simp only [bind, Option.bind]
    cases consts with
    | false =>
      simp only [Bool.false_eq_true, ite_false, pure]
      exact decode_inner r sk []
    | true =>
      simp only [ite_true]
      cases sk.consts.mapM (constSkel r) with
      | none => rfl
      | some skels => exact decode_inner r sk skels

/-- **THE theorem: the driver's olean decoder is its specification**,
on every region and every root — and the compiler runs the fast one. -/
@[csimp] theorem decodeModuleSpec_eq_fast : @decodeModuleSpec = @decodeModuleFast := by
  funext r root consts
  exact (decodeModuleFast_eq r root consts).symm

end ConLeche.Frontend.Olean
