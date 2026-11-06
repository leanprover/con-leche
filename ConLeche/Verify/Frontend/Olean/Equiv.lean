module

public import ConLeche.Frontend.Olean.Fast
import ConLeche.Verify.Frontend.Olean.Engine

public section

/-!
# The fast decoder is the specification (task #371)

**`parseMany_eq : parseMany r addrs = addrs.mapM (decodeAt r)`**:
on every region, from every list of addresses, the fast olean decoder
(`ConLeche/Frontend/Olean/Fast.lean`) with its one memo returns exactly what the
specification (`ConLeche/Frontend/Olean/Spec.lean`) returns: the same
module, or failure on the same inputs, so each succeeds exactly where the
other does.  No hypothesis about the bytes: both sides define the reading.
The reader calls the fast decoder by name; nothing is `implemented_by` and
nothing is `@[csimp]`.

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

/-- `decodeAt`, past the name table's check, its constants read skeletons first. -/
theorem decodeAt_skels (r : Region) (a : UInt64) (hn : constNamesOk r a = true) :
    decodeAt r a = moduleSkel r a >>= fun sk =>
      sk.consts.mapM (constSkel r) >>= fun cs => sk.read (nameP r) (exprP r) cs := by
  unfold decodeAt
  rw [hn]
  show (do
      let sk ← moduleSkel r a
      let imports ← sk.imports.mapM (ImportF.mapM (nameP r))
      let constants ← sk.consts.mapM (constSpec r)
      pure (ModDecoded.mk sk.isModule imports.toArray constants.toArray)) = _
  cases moduleSkel r a with
  | none => rfl
  | some sk =>
    simp only [bind, Option.bind, ModSkel.read]
    have hc : sk.consts.mapM (constSpec r) =
        sk.consts.mapM (constSkel r) >>= fun skels =>
          skels.mapM (CEntryF.mapM (nameP r) (exprP r)) :=
      mapM_bind (constSkel r) (CEntryF.mapM (nameP r) (exprP r)) sk.consts
    rw [hc]
    cases sk.imports.mapM (ImportF.mapM (nameP r)) <;> cases sk.consts.mapM (constSkel r) <;> rfl

/-- An import read by a function that agrees on its name. -/
theorem ImportF.mapM_congr {f g : UInt64 → Option Name} (i : ImportF UInt64)
    (h : f i.module = g i.module) : i.mapM f = i.mapM g := by
  simp only [ImportF.mapM, h]

/-- Two steps per element are two `mapM`s, the second over the pairs. -/
theorem mapM_bind_zip {α β γ : Type} (f : α → Option β) (g : α → β → Option γ) :
    ∀ xs : List α, xs.mapM (fun x => f x >>= g x) =
      xs.mapM f >>= fun ys => (xs.zip ys).mapM fun p => g p.1 p.2
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, mapM_bind_zip f g xs]
    cases f x with
    | none => rfl
    | some y =>
      simp only [bind, Option.bind]
      cases hg : g x y with
      | none =>
        cases xs.mapM f with
        | none => rfl
        | some ys => simp [hg, List.mapM_cons, bind, Option.bind]
      | some z =>
        cases xs.mapM f with
        | none => rfl
        | some ys => simp [hg, List.mapM_cons, bind, Option.bind]

theorem mapM_bind_two {α β γ : Type} (f : α → Option β) (g : β → Option γ) (xs : List α) :
    (xs.mapM f >>= fun ys => ys.mapM g) = xs.mapM (fun x => f x >>= g) :=
  (mapM_bind f g xs).symm

/-- What a module's value needs of the pointers read, on two readers. -/
theorem ModSkel.read_congr {nm nm' : UInt64 → Option Name} {ex ex' : UInt64 → Option Expr}
    (sk : ModSkel) (cs : List (CEntryF UInt64 UInt64))
    (hi : ∀ i ∈ sk.imports, nm i.module = nm' i.module)
    (hn : ∀ c ∈ cs, ∀ v ∈ c.names, nm v = nm' v) (he : ∀ c ∈ cs, ∀ v ∈ c.exprs, ex v = ex' v) :
    sk.read nm ex cs = sk.read nm' ex' cs := by
  have h1 : sk.imports.mapM (ImportF.mapM nm) = sk.imports.mapM (ImportF.mapM nm') :=
    listMapM_congr _ fun i hm => ImportF.mapM_congr i (hi i hm)
  have h2 : cs.mapM (CEntryF.mapM nm ex) = cs.mapM (CEntryF.mapM nm' ex') :=
    listMapM_congr _ fun c hc => CEntryF.mapM_congr c (hn c hc) (he c hc)
  simp only [ModSkel.read, h1, h2]

/-- What a module's value read says of its pointers. -/
theorem ModSkel.read_some {nm : UInt64 → Option Name} {ex : UInt64 → Option Expr} {sk : ModSkel}
    {cs : List (CEntryF UInt64 UInt64)} {d : ModDecoded} (h : sk.read nm ex cs = some d) :
    (∀ i ∈ sk.imports, (nm i.module).isSome) ∧ (∀ c ∈ cs, ∀ v ∈ c.names, (nm v).isSome) ∧
      ∀ c ∈ cs, ∀ v ∈ c.exprs, (ex v).isSome := by
  simp only [ModSkel.read] at h
  obtain ⟨is, hi, h⟩ := bind_some_left h
  obtain ⟨es, he, -⟩ := bind_some_left h
  have hall := listMapM_some cs he
  have hent : ∀ c ∈ cs, (∀ x ∈ c.names, (nm x).isSome) ∧ (∀ x ∈ c.exprs, (ex x).isSome) := by
    intro c hc
    obtain ⟨d, hd⟩ := isSome_iff_exists'.mp (hall c hc)
    exact CEntryF.mapM_some c hd
  refine ⟨fun i hm => ?_, fun c hc => (hent c hc).1, fun c hc => (hent c hc).2⟩
  have := listMapM_some _ hi i hm
  simp only [ImportF.mapM, bind, Option.bind] at this
  cases hx : nm i.module <;> simp_all

theorem mapM_length_eq {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.length = ys.length
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, -, h⟩ := bind_some_left h
    obtain ⟨ys', hys, h⟩ := bind_some_left h
    cases h
    simp [mapM_length_eq hys]

theorem mapM_zip_inner (r : Region) (sks : List ModSkel) (css : List (List (CEntryF UInt64 UInt64)))
    (hz : sks.length = css.length) :
    (runPasses r (sks.flatMap (fun sk => sk.imports.map (·.module)) ++ css.flatten.flatMap CEntryF.names)
        (css.flatten.flatMap CEntryF.exprs) >>= fun st =>
      (sks.zip css).mapM fun p => p.1.read (st.nameOf r) (st.exprOf r) p.2) =
    (sks.zip css).mapM fun p => p.1.read (nameP r) (exprP r) p.2 := by
  have h := runPasses_spec r (sks.flatMap (fun sk => sk.imports.map (·.module)) ++
    css.flatten.flatMap CEntryF.names) (css.flatten.flatMap CEntryF.exprs)
  cases hrp : runPasses r (sks.flatMap (fun sk => sk.imports.map (·.module)) ++
      css.flatten.flatMap CEntryF.names) (css.flatten.flatMap CEntryF.exprs) with
  | some st =>
    rw [hrp] at h
    obtain ⟨hn, he⟩ := h
    simp only [bind, Option.bind]
    apply listMapM_congr
    rintro ⟨sk, cs⟩ hp
    have hsk : sk ∈ sks := (List.of_mem_zip hp).1
    have hcs : cs ∈ css := (List.of_mem_zip hp).2
    refine ModSkel.read_congr sk cs (fun i hi => hn _ (List.mem_append_left _ ?_))
      (fun c hc v hv => hn _ (List.mem_append_right _ ?_)) (fun c hc v hv => he _ ?_)
    · exact List.mem_flatMap.mpr ⟨sk, hsk, List.mem_map_of_mem hi⟩
    · exact List.mem_flatMap.mpr ⟨c, List.mem_flatten.mpr ⟨cs, hcs, hc⟩, hv⟩
    · exact List.mem_flatMap.mpr ⟨c, List.mem_flatten.mpr ⟨cs, hcs, hc⟩, hv⟩
  | none =>
    rw [hrp] at h
    simp only [bind, Option.bind]
    symm
    cases hm : (sks.zip css).mapM fun p => p.1.read (nameP r) (exprP r) p.2 with
    | none => rfl
    | some ds =>
      exfalso
      apply h
      -- every member is read by the specification
      have hmem : ∀ {sk : ModSkel} {cs}, (sk, cs) ∈ sks.zip css →
          ((∀ i ∈ sk.imports, (nameP r i.module).isSome) ∧
            (∀ c ∈ cs, ∀ v ∈ c.names, (nameP r v).isSome) ∧
            ∀ c ∈ cs, ∀ v ∈ c.exprs, (exprP r v).isSome) := by
        intro sk cs hp
        obtain ⟨d, hd⟩ := isSome_iff_exists'.mp (listMapM_some _ hm (sk, cs) hp)
        exact ModSkel.read_some hd
      have hl : ∀ sk ∈ sks, ∃ cs, (sk, cs) ∈ sks.zip css := by
        intro sk hsk
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hsk
        have hi' : i < (sks.zip css).length := by simp; omega
        exact ⟨css[i]'(by omega), by simpa using List.getElem_mem hi'⟩
      have hr : ∀ cs ∈ css, ∃ sk, (sk, cs) ∈ sks.zip css := by
        intro cs hcs
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcs
        have hi' : i < (sks.zip css).length := by simp; omega
        exact ⟨sks[i]'(by omega), by simpa using List.getElem_mem hi'⟩
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨sk, hsk, hv⟩ := List.mem_flatMap.mp hv
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
          obtain ⟨cs, hp⟩ := hl sk hsk
          exact (hmem hp).1 i hi
        · obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp hv
          obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
          obtain ⟨sk, hp⟩ := hr cs hcs
          exact (hmem hp).2.1 c hc v hv
      · obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp hv
        obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
        obtain ⟨sk, hp⟩ := hr cs hcs
        exact (hmem hp).2.2 c hc v hv

/-- **The fast decoder is the specification**, on every region and every list of
addresses, so each succeeds exactly where the other does. -/
theorem parseMany_eq (r : Region) (addrs : List UInt64) :
    parseMany r addrs = addrs.mapM (decodeAt r) := by
  unfold parseMany
  cases hall : addrs.all (constNamesOk r) with
  | false =>
    show none = _
    symm
    cases hm : addrs.mapM (decodeAt r) with
    | none => rfl
    | some ds =>
      exfalso
      have hn : ∀ a ∈ addrs, constNamesOk r a = true := by
        intro a ha
        obtain ⟨d, hd⟩ := isSome_iff_exists'.mp (listMapM_some _ hm a ha)
        unfold decodeAt at hd
        cases hc : constNamesOk r a with
        | false => rw [hc] at hd; cases hd
        | true => rfl
      have : addrs.all (constNamesOk r) = true := List.all_eq_true.mpr hn
      rw [hall] at this
      cases this
  | true =>
    have hn : ∀ a ∈ addrs, constNamesOk r a = true := List.all_eq_true.mp hall
    have h1 : addrs.mapM (decodeAt r) = addrs.mapM (fun a => moduleSkel r a >>= fun sk =>
        sk.consts.mapM (constSkel r) >>= fun cs => sk.read (nameP r) (exprP r) cs) :=
      listMapM_congr _ fun a ha => decodeAt_skels r a (hn a ha)
    rw [h1, ← mapM_bind_two]
    show (addrs.mapM (moduleSkel r) >>= _) = _
    cases hs : addrs.mapM (moduleSkel r) with
    | none => rfl
    | some sks =>
      show (sks.mapM (fun sk => sk.consts.mapM (constSkel r)) >>= _) =
        sks.mapM (fun sk => sk.consts.mapM (constSkel r) >>= fun cs =>
          sk.read (nameP r) (exprP r) cs)
      rw [mapM_bind_zip (fun sk : ModSkel => sk.consts.mapM (constSkel r))
        (fun sk cs => sk.read (nameP r) (exprP r) cs) sks]
      cases hc : sks.mapM (fun sk => sk.consts.mapM (constSkel r)) with
      | none => rfl
      | some css => exact mapM_zip_inner r sks css (mapM_length_eq hc)

/-- **The `ModuleData` at one address**, fast, is the specification's. -/
theorem parseAt_eq_spec (r : Region) (a : UInt64) : parseAt r a = decodeAt r a := by
  unfold parseAt
  rw [parseMany_eq]
  simp only [List.mapM_cons, List.mapM_nil, bind, Option.bind, pure]
  cases decodeAt r a <;> rfl

/-! ## A few statements, from their roots -/

/-- **The statements of some constants are what the specification reads**
of them, on every region and every list of constants. -/
theorem stmtsFast_eq (r : Region) (sks : List (CEntryF UInt64 UInt64)) :
    stmtsFast r sks = sks.mapM (stmtP r) := by
  have h := runPasses_spec r (sks.flatMap fun s => s.name :: s.levelParams) (sks.map (·.type))
  unfold stmtsFast
  cases hrp : runPasses r (sks.flatMap fun s => s.name :: s.levelParams) (sks.map (·.type)) with
  | some st =>
    rw [hrp] at h
    obtain ⟨hn, he⟩ := h
    simp only [bind, Option.bind]
    apply listMapM_congr
    intro s hs
    have hn1 : st.nameOf r s.name = nameP r s.name :=
      hn _ (List.mem_flatMap.mpr ⟨s, hs, List.mem_cons_self⟩)
    have hl : s.levelParams.mapM (st.nameOf r) = s.levelParams.mapM (nameP r) :=
      listMapM_congr _ fun v hv => hn v (List.mem_flatMap.mpr ⟨s, hs, List.mem_cons_of_mem _ hv⟩)
    have he1 : st.exprOf r s.type = exprP r s.type := he _ (List.mem_map_of_mem hs)
    rw [hn1, hl, he1]; rfl
  | none =>
    rw [hrp] at h
    simp only [bind, Option.bind]
    symm
    cases hm : sks.mapM (stmtP r) with
    | none => rfl
    | some cs =>
      exfalso; apply h
      have hall := listMapM_some sks hm
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · obtain ⟨s, hs, hvs⟩ := List.mem_flatMap.mp hv
        obtain ⟨c, hc⟩ := isSome_iff_exists'.mp (hall s hs)
        simp only [stmtP, bind, Option.bind] at hc
        rcases List.mem_cons.mp hvs with rfl | hvl
        · cases hx : nameP r s.name <;> simp_all
        · cases hx : nameP r s.name <;> simp only [hx] at hc
          · cases hc
          cases hy : s.levelParams.mapM (nameP r) <;> simp only [hy] at hc
          · cases hc
          exact listMapM_some _ hy v hvl
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hv
        obtain ⟨c, hc⟩ := isSome_iff_exists'.mp (hall s hs)
        simp only [stmtP, bind, Option.bind] at hc
        cases hx : nameP r s.name <;> simp only [hx] at hc
        · cases hc
        cases hy : s.levelParams.mapM (nameP r) <;> simp only [hy] at hc
        · cases hc
        cases hz : exprP r s.type <;> simp_all

end ConLeche.Frontend.Olean
