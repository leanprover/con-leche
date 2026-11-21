module

public import ConLeche.Driver.Graph
public import ConLeche.Frontend.Olean.Snapshot
public import ConLeche.Verify.Frontend.Olean.Files
import ConLeche.Verify.Frontend.Olean.Reads

/-!
# The import graph check, in the model (task #467)

`checkGraphG_ok`: every outcome of `Graph.checkGraphG` on a snapshot that is an exit 0 gives the
closure as a list `C` of modules with their imports, each module's imports those its header read
answers on the snapshot (`moduleImports`, the read every reader of the module makes), and a rank
function `rk`, one-to-one on `C`, every import edge of a module of `C` going to a module of `C` of
a smaller rank, and every module of `C` in the roots' import closure by the headers
(`HdrClosure`, `graphOf_closure`).  The witness is the computed order; the proof uses only its validation
(`verdict_none`), not Kahn's algorithm.  `checkGraphG_closure`: every module of the closure of
the roots by the specification (`Olean.InClosure`, over the private views' imports) is in `C`.
-/

public section

namespace ConLeche.Driver.Graph

open ConLeche ConLeche.Frontend.Olean

variable {sp : Roots} {fs : FS} {extra : Name → Array ImportRec}

/-- **A module of a closure, as the graph check reads it**: its imports are what its header read
answers on the snapshot, followed by the imports the run adds to it (`extra`; a compared
challenge's solution, task #608). -/
@[expose] def NodeOk (sp : Roots) (fs : FS) (extra : Name → Array ImportRec) (e : Node) :
    Prop :=
  ∃ imps, ModelIO.CanGive (moduleImports sp e.1) fs (.ok imps) ∧ e.2 = imps ++ extra e.1

/-- With no import added, a module's imports are its header's. -/
theorem NodeOk.plain {e : Node} (h : NodeOk sp fs (fun _ => #[]) e) :
    ModelIO.CanGive (moduleImports sp e.1) fs (.ok e.2) := by
  obtain ⟨imps, h, he⟩ := h
  rw [he, Array.append_empty]
  exact h

/-- **A header read that answers** is `moduleImports`' answer, with the run's imports added. -/
theorem hdrOf_ok {T : Roots} {m : Name} {e : Node} {hs hs' : HS}
    (h : (hdrOf T extra m : ModelIO _) fs hs (.ok (.ok e)) hs') :
    e.1 = m ∧ ∃ imps, ModelIO.CanGive (moduleImports T m) fs (.ok imps) ∧ e.2 = imps ++ extra m := by
  simp only [hdrOf, ModelIO.bind_ok] at h
  obtain ⟨x, hs₁, hx, h⟩ := h
  rcases x with err | imps
  · simp only [ModelIO.bind_ok] at h
    obtain ⟨b, _, -, h⟩ := h
    cases b <;> simp at h
  · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    subst h
    exact ⟨rfl, imps, ⟨hs, hs₁, hx⟩, rfl⟩

theorem expand_mem : ∀ (rs : List Node) (seen : Std.HashSet Name) (out : Array Node)
    (next : Array Name), ∀ e ∈ (expand seen out next rs).2.1.toList, e ∈ out.toList ∨ e ∈ rs
  | [], _, _, _, e, he => Or.inl he
  | (m, imps) :: rest, seen, out, next, e, he => by
    simp only [expand] at he
    rcases expand_mem rest _ _ _ e he with h | h
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- A header read through roots read off the snapshot is one on the search path. -/
theorem hdrOf_sub {T : Roots} (hT : T.Ok fs) (hp : T.bare = sp) {m : Name} {e : Node} {hs hs' : HS}
    (h : (hdrOf T extra m : ModelIO _) fs hs (.ok (.ok e)) hs') :
    e.1 = m ∧ NodeOk sp fs extra e := by
  obtain ⟨h1, imps, h2, he⟩ := hdrOf_ok h
  have := (moduleImports_sub hT m).canGive h2
  rw [hp] at this
  subst h1
  exact ⟨rfl, imps, this, he⟩

/-- **Every module the walk returns has the imports its header read answers**, and the roots
it resolved are read off the snapshot. -/
theorem closureLevels_good {jobs : Nat} :
    ∀ (fuel : Nat) (lvl : List Name) (seen : Std.HashSet Name) (out C : Array Node)
      (T T' : Roots), T.Ok fs → T.bare = sp →
      (∀ e ∈ out.toList, NodeOk sp fs extra e) →
      ∀ {hs hs' : HS}, (closureLevels T extra jobs fuel lvl seen out : ModelIO _) fs hs
        (.ok (.ok (C, T'))) hs' →
      (∀ e ∈ C.toList, NodeOk sp fs extra e) ∧
        T'.Ok fs ∧ T'.bare = sp
  | _, [], _, out, C, T, T', hT, hp, hout, _, _, h => by
    simp only [closureLevels, ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    exact ⟨hout, hT, hp⟩
  | 0, _ :: _, _, _, _, _, _, _, _, _, _, _, h => by rw [closureLevels] at h; simp at h
  | fuel + 1, x :: xs, seen, out, C, T, T', hT, hp, hout, _, _, h => by
    simp only [closureLevels, ModelIO.bind_ok] at h
    obtain ⟨T₁, _, hT₁, r, _, hr, h⟩ := h
    obtain ⟨hT₁ok, hT₁p⟩ := Roots.foldResolve_ok _ hT hT₁
    rcases r with err | rs
    · simp at h
    · have hr' : (mapExcept (hdrOf T₁ extra) (x :: xs) : ModelIO _) fs _ (.ok (.ok rs)) _ := hr
      obtain ⟨-, hrs⟩ := mapExcept_ok₂ (g := Prod.fst) (g' := id)
        (Q := fun _ y => NodeOk sp fs extra y)
        (fun m y _ _ hy => by
          obtain ⟨h1, h2⟩ := hdrOf_sub hT₁ok (hT₁p.trans hp) hy
          exact ⟨h1, h2⟩) hr'
      refine closureLevels_good fuel _ _ _ C T₁ T' hT₁ok (hT₁p.trans hp) ?_ h
      intro e he
      rcases expand_mem rs seen out #[] e he with h1 | h1
      · exact hout e h1
      · obtain ⟨_, -, hm⟩ := hrs e h1
        exact hm

/-! ## The validation -/

theorem rankLt_iff {a b : Option Nat} :
    rankLt a b = true ↔ ∃ x y, a = some x ∧ b = some y ∧ x < y := by
  cases a <;> cases b <;> simp [rankLt]

theorem namesOf_contains_go {a : Name} :
    ∀ (C : List Node) (s : Std.HashSet Name),
      (C.foldl (fun s e => s.insert e.1) s).contains a = true → a ∈ C.map (·.1) ∨ s.contains a = true
  | [], _, h => Or.inr h
  | e :: C, s, h => by
    rcases namesOf_contains_go C _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with rfl | h
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr h

theorem namesOf_contains {C : List Node} {a : Name} (h : (namesOf C).contains a = true) :
    a ∈ C.map (·.1) := by
  rcases namesOf_contains_go C {} h with h | h
  · exact h
  · simp at h

theorem namesOf_mono_go {a : Name} :
    ∀ (C : List Node) (s : Std.HashSet Name), s.contains a = true →
      (C.foldl (fun s e => s.insert e.1) s).contains a = true
  | [], _, h => h
  | _ :: C, s, h => namesOf_mono_go C _ (by simp [Std.HashSet.contains_insert, h])

/-- Every module of a closure is in its names' set. -/
theorem namesOf_of_mem {C : List Node} {a : Name} (h : a ∈ C.map (·.1)) :
    (namesOf C).contains a = true := by
  unfold namesOf
  suffices H : ∀ (C : List Node) (s : Std.HashSet Name), a ∈ C.map (·.1) →
      (C.foldl (fun s e => s.insert e.1) s).contains a = true from H C {} h
  intro C
  induction C with
  | nil => intro s h; simp at h
  | cons e C ih =>
    intro s h
    simp only [List.map_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact namesOf_mono_go C _ (by simp)
    · exact ih _ h

/-- **What a verdict of none says**: the numbering is topological on the closure. -/
theorem verdict_none {roots : List Name} {C : List Node} {rk : Name → Option Nat}
    (h : verdict roots C rk = none) :
    (∀ r ∈ roots, r ∈ C.map (·.1)) ∧
    (∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rankLt (rk i.module) (rk e.1) = true) ∧
    (∀ e ∈ C, (rk e.1).isSome = true) ∧
    (C.map fun e => rk e.1).Nodup := by
  unfold verdict at h
  simp only at h
  split at h
  · cases h
  rename_i hroots
  split at h
  · cases h
  rename_i hrk
  split at h
  · cases h
  rename_i hdist
  split at h
  · cases h
  rename_i hedge
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hdist
  refine ⟨?_, ?_, ?_, ((distinctGo_iff _ _).1 hdist).1⟩
  · intro r hr
    have := List.find?_eq_none.1 (by
      cases hf : roots.find? (fun x => !(namesOf C).contains x) with
      | none => rfl
      | some x => exact absurd hf (hroots x)) r hr
    simp only [Bool.not_eq_true', Bool.not_eq_false] at this
    exact namesOf_contains this
  · intro e he i hi
    have hn : C.find? (fun e => !e.2.all (edgeOk (namesOf C) rk e.1)) = none := by
      cases hf : C.find? (fun e => !e.2.all (edgeOk (namesOf C) rk e.1)) with
      | none => rfl
      | some x => exact absurd hf (hedge x.1 x.2)
    have := List.find?_eq_none.1 hn e he
    simp only [Bool.not_eq_true', Bool.not_eq_false, Array.all_eq_true'] at this
    have hi' := this i hi
    simp only [edgeOk, Bool.and_eq_true] at hi'
    exact ⟨namesOf_contains hi'.1, hi'.2⟩
  · intro e he
    have hn : C.find? (fun e => (rk e.1).isNone) = none := by
      cases hf : C.find? (fun e => (rk e.1).isNone) with
      | none => rfl
      | some x => exact absurd hf (hrk x.1 x.2)
    have := List.find?_eq_none.1 hn e he
    simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using this

/-- **A verdict of none gives a rank function**, with the ranks as numbers. -/
theorem verdict_rank {roots : List Name} {C : List Node} {rk : Name → Option Nat}
    (h : verdict roots C rk = none) :
    ∃ r : Name → Nat,
      (∀ x ∈ roots, x ∈ C.map (·.1)) ∧
      (∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ r i.module < r e.1) ∧
      (C.map fun e => r e.1).Nodup := by
  obtain ⟨h1, h2, h3, h4⟩ := verdict_none h
  have hsome : ∀ e ∈ C, ∃ k, rk e.1 = some k := fun e he => Option.isSome_iff_exists.1 (h3 e he)
  refine ⟨fun n => (rk n).getD 0, h1, ?_, ?_⟩
  · intro e he i hi
    obtain ⟨hm, hl⟩ := h2 e he i hi
    obtain ⟨x, y, hx, hy, hxy⟩ := rankLt_iff.1 hl
    exact ⟨hm, by simp [hx, hy, hxy]⟩
  · unfold List.Nodup at h4 ⊢
    rw [List.pairwise_map] at h4 ⊢
    refine h4.imp_of_mem fun {e e'} he he' hne heq => hne ?_
    obtain ⟨k, hk⟩ := hsome e he
    obtain ⟨k', hk'⟩ := hsome e' he'
    simp only [hk, hk', Option.getD_some] at heq
    rw [hk, hk', heq]

/-! ## The check -/

/-- **The graph checked, in the model**: if an outcome of `graphOf` on a snapshot `fs` is a
closure `C`, there is a list `C` of modules with their imports — the closure — and a rank
function `rk` such that

* each module's imports are what its header read answers on the snapshot (`moduleImports`; the
  imports of every view of it read there, `moduleImports_of_view`);
* every root, and every import of a module of `C`, is a module of `C`;
* every import edge goes to a smaller rank, and `rk` is one-to-one on `C`.

So `C` ordered by `rk` numbers the closure with each module after everything it imports, by
edges of every kind; in particular the graph is acyclic. -/
theorem graphOf_ok (hsp : sp.bare = sp) {roots : List Name} {jobs : Nat} {C : Array Node}
    {T : Roots} {hs hs' : HS} (h : (graphOf sp roots jobs extra : ModelIO _) fs hs (.ok (.ok (C, T))) hs') :
    ∃ rk : Name → Nat,
      (∀ e ∈ C.toList, NodeOk sp fs extra e) ∧
      (∀ r ∈ roots, r ∈ C.toList.map (·.1)) ∧
      (∀ e ∈ C.toList, ∀ i ∈ e.2, i.module ∈ C.toList.map (·.1) ∧ rk i.module < rk e.1) ∧
      (C.toList.map fun e => rk e.1).Nodup ∧ T.Ok fs ∧ T.bare = sp := by
  simp only [graphOf, ModelIO.bind_ok] at h
  obtain ⟨x, _, hx, h⟩ := h
  rcases x with err | ⟨C', T'⟩
  · simp at h
  · simp only at h
    cases hc : cycleOf (depsOf (indexOf C') C') (kahn (depsOf (indexOf C') C')) with
    | some cyc => simp [hc] at h
    | none =>
      simp only [hc] at h
      cases hv : verdict roots C'.toList (rankOf (indexOf C') (ranksOf C'.size (kahn (depsOf (indexOf C') C')))) with
      | some e => simp [hv] at h
      | none =>
        simp only [hv, ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, -⟩ := h
        obtain ⟨hgood, hT, hTp⟩ :=
          closureLevels_good _ _ _ _ _ _ _ (hsp ▸ Roots.ok_bare fs sp) hsp (by simp) hx
        obtain ⟨rk, h1, h2, h3⟩ := verdict_rank hv
        exact ⟨rk, hgood, h1, h2, h3, hT, hTp⟩

/-! ## The closure the walk returns is the headers' import closure -/

/-- **A node's import, of its header or added**: in the closure of roots that hold every added
import's module. -/
theorem _root_.ConLeche.Frontend.Olean.HdrClosure.of_node {roots : List Name} {e : Node} (he : NodeOk sp fs extra e)
    (hx : ∀ m, ∀ i ∈ extra m, i.module ∈ roots) (hm : HdrClosure sp fs roots e.1)
    {i : ImportRec} (hi : i ∈ e.2) : HdrClosure sp fs roots i.module := by
  obtain ⟨imps, h, he⟩ := he
  rw [he, Array.mem_append] at hi
  rcases hi with hi | hi
  · exact .step hm h hi
  · exact .root (hx _ i hi)

theorem expand_next : ∀ (rs : List Node) (seen : Std.HashSet Name) (out : Array Node)
    (next : Array Name), ∀ x ∈ (expand seen out next rs).2.2.toList,
      x ∈ next.toList ∨ ∃ e ∈ rs, ∃ i ∈ e.2, i.module = x
  | [], _, _, _, x, hx => Or.inl hx
  | (m, imps) :: rest, seen, out, next, x, hx => by
    simp only [expand] at hx
    rcases expand_next rest _ _ _ x hx with h | h
    · rw [← Array.foldl_toList] at h
      suffices H : ∀ (l : List ImportRec) (s : Std.HashSet Name) (nx : Array Name),
          x ∈ (l.foldl (fun (sn : Std.HashSet Name × Array Name) i =>
            if sn.1.contains i.module then sn else (sn.1.insert i.module, sn.2.push i.module))
            (s, nx)).2.toList → x ∈ nx.toList ∨ ∃ i ∈ l, i.module = x by
        rcases H _ seen next h with h' | ⟨i, hi, hx'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨(m, imps), List.mem_cons_self, i, Array.mem_toList_iff.1 hi, hx'⟩
      intro l
      induction l with
      | nil => intro s nx h; exact Or.inl h
      | cons i l ih =>
        intro s nx h
        simp only [List.foldl_cons] at h
        split at h
        · rcases ih _ _ h with h' | ⟨j, hj, hx'⟩
          · exact Or.inl h'
          · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hx'⟩
        · rcases ih _ _ h with h' | ⟨j, hj, hx'⟩
          · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h'
            rcases h' with h' | rfl
            · exact Or.inl h'
            · exact Or.inr ⟨i, List.mem_cons_self, rfl⟩
          · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hx'⟩
    · obtain ⟨e, he, i, hi, hx'⟩ := h
      exact Or.inr ⟨e, List.mem_cons_of_mem _ he, i, hi, hx'⟩

/-- **Every module the walk returns is in the roots' import closure.** -/
theorem closureLevels_closure {jobs : Nat} {roots : List Name}
    (hx : ∀ m, ∀ i ∈ extra m, i.module ∈ roots) :
    ∀ (fuel : Nat) (lvl : List Name) (seen : Std.HashSet Name) (out C : Array Node)
      (T T' : Roots), T.Ok fs → T.bare = sp →
      (∀ x ∈ lvl, HdrClosure sp fs roots x) → (∀ e ∈ out.toList, HdrClosure sp fs roots e.1) →
      ∀ {hs hs' : HS}, (closureLevels T extra jobs fuel lvl seen out : ModelIO _) fs hs
        (.ok (.ok (C, T'))) hs' →
      ∀ e ∈ C.toList, HdrClosure sp fs roots e.1
  | _, [], _, out, C, _, _, _, _, _, hout, _, _, h => by
    simp only [closureLevels, ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    exact hout
  | 0, _ :: _, _, _, _, _, _, _, _, _, _, _, _, h => by rw [closureLevels] at h; simp at h
  | fuel + 1, x :: xs, seen, out, C, T, T', hT, hp, hlvl, hout, _, _, h => by
    simp only [closureLevels, ModelIO.bind_ok] at h
    obtain ⟨T₁, _, hT₁, r, _, hr, h⟩ := h
    obtain ⟨hT₁ok, hT₁p⟩ := Roots.foldResolve_ok _ hT hT₁
    rcases r with err | rs
    · simp at h
    · have hr' : (mapExcept (hdrOf T₁ extra) (x :: xs) : ModelIO _) fs _ (.ok (.ok rs)) _ := hr
      obtain ⟨-, hrs⟩ := mapExcept_ok₂ (g := Prod.fst) (g' := id)
        (Q := fun m y => y.1 = m ∧ NodeOk sp fs extra y)
        (fun m y _ _ hy => by
          obtain ⟨h1, h2⟩ := hdrOf_sub hT₁ok (hT₁p.trans hp) hy
          exact ⟨h1, h1, h2⟩) hr'
      have hrsC : ∀ e ∈ rs, HdrClosure sp fs roots e.1 := fun e he => by
        obtain ⟨m, hm, h1, -⟩ := hrs e he
        rw [h1]; exact hlvl m hm
      refine closureLevels_closure hx fuel _ _ _ C T₁ T' hT₁ok (hT₁p.trans hp) (fun y hy => ?_)
        (fun e he => ?_) h
      · rcases expand_next rs seen out #[] y hy with h1 | ⟨e, he, i, hi, rfl⟩
        · simp at h1
        · obtain ⟨_, -, -, hm⟩ := hrs e he
          exact HdrClosure.of_node hm hx (hrsC e he) hi
      · rcases expand_mem rs seen out #[] e he with h1 | h1
        · exact hout e h1
        · exact hrsC e h1

theorem dedup_mem {xs : List Name} : ∀ x ∈ (dedup xs).1, x ∈ xs := by
  intro x hx
  unfold dedup at hx
  suffices H : ∀ (l : List Name) (s : Std.HashSet Name) (acc : Array Name),
      x ∈ (l.foldl (fun (sa : Std.HashSet Name × Array Name) y =>
        if sa.1.contains y then sa else (sa.1.insert y, sa.2.push y)) (s, acc)).2.toList →
      x ∈ acc.toList ∨ x ∈ l by
    rcases H xs {} #[] hx with h | h
    · simp at h
    · exact h
  intro l
  induction l with
  | nil => intro s acc h; exact Or.inl h
  | cons y l ih =>
    intro s acc h
    simp only [List.foldl_cons] at h
    split at h
    · rcases ih _ _ h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')
    · rcases ih _ _ h with h' | h'
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h'
        rcases h' with h' | rfl
        · exact Or.inl h'
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h')

/-- **The graph check's closure is the roots' import closure by the headers.** -/
theorem graphOf_closure (hsp : sp.bare = sp) {roots roots' : List Name} {jobs : Nat}
    {C : Array Node} {T : Roots} (hr : ∀ r ∈ roots, r ∈ roots') (hx : ∀ m, ∀ i ∈ extra m, i.module ∈ roots')
    {hs hs' : HS} (h : (graphOf sp roots jobs extra : ModelIO _) fs hs (.ok (.ok (C, T))) hs') :
    ∀ e ∈ C.toList, HdrClosure sp fs roots' e.1 := by
  simp only [graphOf, ModelIO.bind_ok] at h
  obtain ⟨x, _, hx', h⟩ := h
  rcases x with err | ⟨C', T'⟩
  · simp at h
  · simp only at h
    have hC : C' = C := by
      cases hc : cycleOf (depsOf (indexOf C') C') (kahn (depsOf (indexOf C') C')) with
      | some cyc => simp [hc] at h
      | none =>
        simp only [hc] at h
        cases hv : verdict roots C'.toList
            (rankOf (indexOf C') (ranksOf C'.size (kahn (depsOf (indexOf C') C')))) with
        | some e => simp [hv] at h
        | none =>
          simp only [hv, ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
          exact h.1.1.symm
    subst hC
    exact closureLevels_closure hx _ _ _ _ _ _ _ (hsp ▸ Roots.ok_bare fs sp) hsp
      (fun y hy => .root (hr _ (dedup_mem y hy))) (by simp) hx'

/-- **An exit 0 of the graph check**: its closure, with `graphOf_ok`'s facts. -/
theorem checkGraphG_ok (hsp : sp.bare = sp) {roots roots' : List Name} {jobs : Nat}
    (hr : ∀ r ∈ roots, r ∈ roots') (hxt : ∀ m, ∀ i ∈ extra m, i.module ∈ roots')
    {hs hs' : HS} (h : (checkGraphG sp roots jobs extra : ModelIO UInt8) fs hs (.ok 0) hs') :
    ∃ C : List Node, ∃ rk : Name → Nat,
      (∀ e ∈ C, NodeOk sp fs extra e) ∧
      (∀ r ∈ roots, r ∈ C.map (·.1)) ∧
      (∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1) ∧
      (C.map fun e => rk e.1).Nodup ∧ (∀ e ∈ C, HdrClosure sp fs roots' e.1) := by
  suffices H : ModelIO.AllOk (checkGraphG sp roots jobs extra) fs hs (fun c => c = 0 →
      ∃ C : List Node, ∃ rk : Name → Nat,
        (∀ e ∈ C, NodeOk sp fs extra e) ∧
        (∀ r ∈ roots, r ∈ C.map (·.1)) ∧
        (∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1) ∧
        (C.map fun e => rk e.1).Nodup ∧ (∀ e ∈ C, HdrClosure sp fs roots' e.1)) from H 0 hs' h rfl
  simp only [checkGraphG, ModelIO.allOk_bind]
  intro x _ hx
  rcases x with err | ⟨C, T⟩
  · simp only [diagLine, ModelIO.allOk_liftIO_bind, ModelIO.allOk_pure]
    exact fun _ h0 => absurd h0 (CheckError.exitCode_ne_zero _)
  · simp only [outLine, ModelIO.allOk_liftIO_bind, ModelIO.allOk_pure]
    obtain ⟨rk, h1, h2, h3, h4, -⟩ := graphOf_ok hsp hx
    exact fun _ _ => ⟨C.toList, rk, h1, h2, h3, h4, graphOf_closure hsp hr hxt hx⟩

/-- **The closure by the specification is in `C`**: where every module of `C` has the imports
its header read answers and every import of one is in `C`, every module of the roots' closure
(`InClosure`: a root, or an import of the private view of a module of it) is a module of `C`. -/
theorem checkGraphG_closure {roots : Array Name} {C : List Node}
    (hgood : ∀ e ∈ C, NodeOk sp fs extra e)
    (hroots : ∀ r ∈ roots.toList, r ∈ C.map (·.1))
    (hedges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1)) {m : Name}
    (h : InClosure sp fs roots m) : m ∈ C.map (·.1) := by
  induction h with
  | root hm => exact hroots _ (Array.mem_toList_iff.mpr hm)
  | @step m d i _ hv hi ih =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ih
    obtain ⟨_, _, hrv⟩ := readView_of_viewOf hv
    obtain ⟨imps, hgi, he2⟩ := hgood e he
    have hg := (moduleImports_of_view hrv).eq hgi
    have : d.imports = imps := by simpa using hg.symm
    exact hedges e he i (by rw [he2]; exact Array.mem_append_left _ (this ▸ hi))


end ConLeche.Driver.Graph
