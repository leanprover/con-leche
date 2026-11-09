module

public import ConLeche.Frontend.Olean.Records
import ConLeche.Verify.Frontend.Olean.Merge
import Std.Data.HashSet.Lemmas

/-!
# The emission of a closure's merged constants

`Emit.Sub`: the walk only adds to its tables, and a record it pushed stays.

`emitLoop_spec`: every record comes from stored constants (`RecFrom`), each constant named by
a `visit` that is stored and not filtered out ends visited.

`emitLoop_covers`: where the stored constants' blocks agree (`blocksOk`, the check before the
walk), a visited constant that is not filtered out is declared by a record, and that record is
its own: `declsOf_thm` (a theorem constant's record is its theorem), `declsOf_from` (every
declaration comes from stored constants).
-/

public section

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## The tables -/

/-- **The walk only adds.** -/
structure Emit.Sub (a b : Emit) : Prop where
  names : ∀ (i : Nat) (v : Name), a.names[i]? = some v → b.names[i]? = some v
  exprs : ∀ (i : Nat) (v : Expr), a.exprs[i]? = some v → b.exprs[i]? = some v
  out : ∀ r ∈ a.out, r ∈ b.out

theorem Emit.Sub.refl (a : Emit) : Emit.Sub a a := ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h⟩

theorem Emit.Sub.trans {a b c : Emit} (h1 : Emit.Sub a b) (h2 : Emit.Sub b c) : Emit.Sub a c :=
  ⟨fun i v h => h2.names i v (h1.names i v h), fun i v h => h2.exprs i v (h1.exprs i v h),
    fun r h => h2.out r (h1.out r h)⟩

/-- A constant's name, level parameters and type in the tables. -/
@[expose] def CvOf (em : Emit) (cv : CVRec) (c : CEntry) : Prop :=
  em.names[cv.name]? = some c.name ∧ cv.levelParams.map (em.names[·]?) = c.levelParams.map some ∧
    em.exprs[cv.type]? = some c.type

theorem CvOf.mono {a b : Emit} (h : Emit.Sub a b) {cv : CVRec} {c : CEntry} (hc : CvOf a cv c) :
    CvOf b cv c := by
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨h.names _ _ h1, ?_, h.exprs _ _ h3⟩
  rw [← h2]
  apply List.map_congr_left
  intro i hi
  have : a.names[i]? ∈ cv.levelParams.map (a.names[·]?) := List.mem_map_of_mem hi
  rw [h2] at this
  obtain ⟨n, -, hn⟩ := List.mem_map.mp this
  rw [← hn]
  exact h.names i n hn.symm

theorem Emit.name_spec (st : Emit) (n : Name) :
    Emit.Sub st (st.name n).1 ∧ (st.name n).1.names[(st.name n).2]? = some n ∧
      (st.name n).1.visited = st.visited ∧ (st.name n).1.out = st.out := by
  obtain ⟨v, ns, es, o⟩ := st
  refine ⟨⟨fun i x h => ?_, fun _ _ h => h, fun _ h => h⟩, ?_, rfl, rfl⟩
  · simp only [Emit.name]
    rw [Array.getElem?_push]
    have : i ≠ ns.size := by
      intro he
      subst he
      simp at h
    simpa [this] using h
  · simp [Emit.name]

theorem Emit.expr_spec (st : Emit) (e : Expr) :
    Emit.Sub st (st.expr e).1 ∧ (st.expr e).1.exprs[(st.expr e).2]? = some e ∧
      (st.expr e).1.visited = st.visited ∧ (st.expr e).1.out = st.out := by
  obtain ⟨v, ns, es, o⟩ := st
  refine ⟨⟨fun _ _ h => h, fun i x h => ?_, fun _ h => h⟩, ?_, rfl, rfl⟩
  · simp only [Emit.expr]
    rw [Array.getElem?_push]
    have : i ≠ es.size := by
      intro he
      subst he
      simp at h
    simpa [this] using h
  · simp [Emit.expr]

/-- The names of a list pushed into the table, their indices gathered. -/
theorem names_fold (ns : List Name) : ∀ (st : Emit) (acc : Array Nat),
    let r := ns.foldl (fun (st, acc) p =>
      let (st, i) := st.name p; (st, acc.push i)) (st, acc)
    Emit.Sub st r.1 ∧ r.1.visited = st.visited ∧ r.1.out = st.out ∧
      r.2.toList.map (r.1.names[·]?) = acc.toList.map (r.1.names[·]?) ++ ns.map some := by
  induction ns with
  | nil =>
    intro st acc
    exact ⟨Emit.Sub.refl _, rfl, rfl, by simp⟩
  | cons n ns ih =>
    intro st acc
    obtain ⟨h1, h2, h3, h4⟩ := Emit.name_spec st n
    obtain ⟨g1, g2, g3, g4⟩ := ih (st.name n).1 (acc.push (st.name n).2)
    simp only [List.foldl_cons]
    refine ⟨h1.trans g1, g2.trans h3, g3.trans h4, ?_⟩
    rw [g4]
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append]
    congr 2
    exact g1.names _ _ h2

theorem Emit.push_spec (st : Emit) (d : DeclRec) :
    Emit.Sub st (st.push d) ∧ (st.push d).visited = st.visited ∧ (st.push d).out = st.out.push d := by
  obtain ⟨v, ns, es, o⟩ := st
  exact ⟨⟨fun _ _ h => h, fun _ _ h => h, fun r h => Array.mem_push.mpr (.inl h)⟩, rfl, rfl⟩

theorem Emit.cv_spec (st : Emit) (c : CEntry) :
    Emit.Sub st (st.cv c).1 ∧ CvOf (st.cv c).1 (st.cv c).2 c ∧ (st.cv c).1.visited = st.visited ∧
      (st.cv c).1.out = st.out := by
  obtain ⟨h1, h2, h3, h4⟩ := Emit.name_spec st c.name
  obtain ⟨g1, g2, g3, g4⟩ := names_fold c.levelParams (st.name c.name).1 #[]
  dsimp only at g1 g2 g3 g4
  generalize hF : c.levelParams.foldl (fun (st, acc) p =>
      let (st, i) := st.name p; (st, acc.push i)) ((st.name c.name).1, (#[] : Array Nat)) = F at g1 g2 g3 g4
  obtain ⟨k1, k2, k3, k4⟩ := Emit.expr_spec F.1 c.type
  have hcv : st.cv c = ((F.1.expr c.type).1, ⟨(st.name c.name).2, F.2.toList, (F.1.expr c.type).2⟩) := by
    subst hF
    rfl
  rw [hcv]
  refine ⟨(h1.trans g1).trans k1, ⟨?_, ?_, k2⟩, ?_, ?_⟩
  · exact k1.names _ _ (g1.names _ _ h2)
  · simp only at g4 ⊢
    have := g4
    simp only [List.map_nil, List.nil_append] at this
    rw [← this]
    apply List.map_congr_left
    intro i hi
    have hm : F.1.names[i]? ∈ F.2.toList.map (F.1.names[·]?) := List.mem_map_of_mem hi
    rw [this] at hm
    obtain ⟨n, -, hn⟩ := List.mem_map.mp hm
    rw [← hn]
    exact k1.names i n hn.symm
  · simp only [k3, g2, h3]
  · simp only [k4, g3, h4]

/-! ## The records -/

/-- A record declares a name. -/
@[expose] def Declares (em : Emit) (n : Name) : DeclRec → Prop
  | .ax cv _ | .defn cv .. | .thm cv _ | .opaq cv .. | .quot cv _ => em.names[cv.name]? = some n
  | .ind ts cs rs =>
    (∃ t ∈ ts, em.names[t.cv.name]? = some n) ∨ (∃ t ∈ cs, em.names[t.cv.name]? = some n) ∨
      ∃ t ∈ rs, em.names[t.cv.name]? = some n

/-- A name some record declares. -/
@[expose] def Has (em : Emit) (n : Name) : Prop := ∃ r ∈ em.out, Declares em n r

theorem Declares.mono {a b : Emit} (h : Emit.Sub a b) {n : Name} :
    ∀ {r : DeclRec}, Declares a n r → Declares b n r
  | .ax _ _, h' => h.names _ _ h'
  | .defn _ _ _ _, h' => h.names _ _ h'
  | .thm _ _, h' => h.names _ _ h'
  | .opaq _ _ _, h' => h.names _ _ h'
  | .quot _ _, h' => h.names _ _ h'
  | .ind _ _ _, .inl ⟨t, ht, h'⟩ => .inl ⟨t, ht, h.names _ _ h'⟩
  | .ind _ _ _, .inr (.inl ⟨t, ht, h'⟩) => .inr (.inl ⟨t, ht, h.names _ _ h'⟩)
  | .ind _ _ _, .inr (.inr ⟨t, ht, h'⟩) => .inr (.inr ⟨t, ht, h.names _ _ h'⟩)

theorem Has.mono {a b : Emit} (h : Emit.Sub a b) {n : Name} : Has a n → Has b n
  | ⟨r, hr, hd⟩ => ⟨r, h.out r hr, hd.mono h⟩

/-- **A record that is one constant's**, by the tables. -/
@[expose] def RecOf (em : Emit) (c : CEntry) : DeclRec → Prop
  | .ax cv u => CvOf em cv c ∧ c.kind = .ax u
  | .defn cv i h s => CvOf em cv c ∧ ∃ v, em.exprs[i]? = some v ∧ c.kind = .defn v h s
  | .thm cv i => CvOf em cv c ∧ ∃ v all, em.exprs[i]? = some v ∧ c.kind = .thm v all
  | .opaq cv i u => CvOf em cv c ∧ ∃ v, em.exprs[i]? = some v ∧ c.kind = .opaq v u
  | .quot cv k => CvOf em cv c ∧ c.kind = .quot k
  | .ind .. => False

/-- A constant the merge holds under its name. -/
@[expose] def Stored (mg : Merged) (c : CEntry) : Prop := mg.map[c.name]? = some c

/-- **A record made of constants the merge holds**. -/
@[expose] def RecFrom (mg : Merged) (em : Emit) : DeclRec → Prop
  | .ind ts cts rs =>
    (∀ t ∈ ts, ∃ c, Stored mg c ∧ CvOf em t.cv c ∧ c.kind.tag = 5) ∧
    (∀ t ∈ cts, ∃ c, Stored mg c ∧ CvOf em t.cv c ∧ c.kind.tag = 6) ∧
    (∀ t ∈ rs, ∃ c, Stored mg c ∧ CvOf em t.cv c ∧ c.kind.tag = 7)
  | r => ∃ c, Stored mg c ∧ RecOf em c r

theorem RecOf.mono {a b : Emit} (h : Emit.Sub a b) {c : CEntry} :
    ∀ {r : DeclRec}, RecOf a c r → RecOf b c r
  | .ax _ _, ⟨h1, h2⟩ => ⟨h1.mono h, h2⟩
  | .defn _ _ _ _, ⟨h1, v, h2, h3⟩ => ⟨h1.mono h, v, h.exprs _ _ h2, h3⟩
  | .thm _ _, ⟨h1, v, all, h2, h3⟩ => ⟨h1.mono h, v, all, h.exprs _ _ h2, h3⟩
  | .opaq _ _ _, ⟨h1, v, h2, h3⟩ => ⟨h1.mono h, v, h.exprs _ _ h2, h3⟩
  | .quot _ _, ⟨h1, h2⟩ => ⟨h1.mono h, h2⟩
  | .ind .., h' => h'.elim

theorem RecFrom.mono {mg : Merged} {a b : Emit} (h : Emit.Sub a b) :
    ∀ {r : DeclRec}, RecFrom mg a r → RecFrom mg b r
  | .ax _ _, ⟨c, h1, h2⟩ => ⟨c, h1, RecOf.mono h h2⟩
  | .defn _ _ _ _, ⟨c, h1, h2⟩ => ⟨c, h1, RecOf.mono h h2⟩
  | .thm _ _, ⟨c, h1, h2⟩ => ⟨c, h1, RecOf.mono h h2⟩
  | .opaq _ _ _, ⟨c, h1, h2⟩ => ⟨c, h1, RecOf.mono h h2⟩
  | .quot _ _, ⟨c, h1, h2⟩ => ⟨c, h1, RecOf.mono h h2⟩
  | .ind _ _ _, ⟨h1, h2, h3⟩ => by
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · obtain ⟨c, x, y, z⟩ := h1 t ht
      exact ⟨c, x, y.mono h, z⟩
    · obtain ⟨c, x, y, z⟩ := h2 t ht
      exact ⟨c, x, y.mono h, z⟩
    · obtain ⟨c, x, y, z⟩ := h3 t ht
      exact ⟨c, x, y.mono h, z⟩

theorem RecOf.declares {em : Emit} {c : CEntry} : ∀ {r : DeclRec}, RecOf em c r → Declares em c.name r
  | .ax _ _, h => h.1.1
  | .defn _ _ _ _, h => h.1.1
  | .thm _ _, h => h.1.1
  | .opaq _ _ _, h => h.1.1
  | .quot _ _, h => h.1.1
  | .ind .., h => h.elim

/-- **One constant's record.** -/
theorem Emit.one_spec (st : Emit) (c : CEntry) :
    Emit.Sub st (st.one c) ∧ (st.one c).visited = st.visited ∧
      (∀ r ∈ (st.one c).out, r ∈ st.out ∨ RecOf (st.one c) c r) ∧
      (c.kind.tag < 5 → Has (st.one c) c.name) := by
  obtain ⟨h1, h2, h3, h4⟩ := Emit.cv_spec st c
  generalize hC : st.cv c = C at h1 h2 h3 h4
  have hone : st.one c = (let (st, d) : Emit × Option DeclRec := match c.kind with
      | .ax u => (C.1, some (.ax C.2 u))
      | .defn v h s => let (st, i) := C.1.expr v; (st, some (.defn C.2 i h s))
      | .thm v _ => let (st, i) := C.1.expr v; (st, some (.thm C.2 i))
      | .opaq v u => let (st, i) := C.1.expr v; (st, some (.opaq C.2 i u))
      | .quot k => (C.1, some (.quot C.2 k))
      | _ => (C.1, none)
    match d with
    | some d => st.push d
    | none => st) := by
    subst hC
    rfl
  rw [hone]
  have pushed : ∀ {t : Nat} (e : Emit) (d : DeclRec), Emit.Sub C.1 e → e.visited = st.visited →
      e.out = st.out → RecOf (e.push d) c d →
      Emit.Sub st (e.push d) ∧ (e.push d).visited = st.visited ∧
        (∀ r ∈ (e.push d).out, r ∈ st.out ∨ RecOf (e.push d) c r) ∧
        (t < 5 → Has (e.push d) c.name) := by
    intro t e d hs hv ho hr
    obtain ⟨p1, p2, p3⟩ := Emit.push_spec e d
    refine ⟨(h1.trans hs).trans p1, p2.trans hv, fun r hm => ?_,
      fun _ => ⟨d, by rw [p3]; exact Array.mem_push.mpr (.inr rfl), hr.declares⟩⟩
    rw [p3, ho] at hm
    rcases Array.mem_push.mp hm with hm | rfl
    · exact .inl hm
    · exact .inr hr
  cases hk : c.kind with
  | ax u =>
    simp only
    obtain ⟨p1, -, -⟩ := Emit.push_spec C.1 (.ax C.2 u)
    exact pushed C.1 (.ax C.2 u) (Emit.Sub.refl _) h3 h4 ⟨h2.mono p1, hk⟩
  | defn v h s =>
    simp only
    obtain ⟨e1, e2, e3, e4⟩ := Emit.expr_spec C.1 v
    obtain ⟨p1, -, -⟩ := Emit.push_spec (C.1.expr v).1 (.defn C.2 (C.1.expr v).2 h s)
    exact pushed _ (.defn C.2 (C.1.expr v).2 h s) e1 (e3.trans h3) (e4.trans h4)
      ⟨(h2.mono e1).mono p1, v, p1.exprs _ _ e2, hk⟩
  | thm v all =>
    simp only
    obtain ⟨e1, e2, e3, e4⟩ := Emit.expr_spec C.1 v
    obtain ⟨p1, -, -⟩ := Emit.push_spec (C.1.expr v).1 (.thm C.2 (C.1.expr v).2)
    exact pushed _ (.thm C.2 (C.1.expr v).2) e1 (e3.trans h3) (e4.trans h4)
      ⟨(h2.mono e1).mono p1, v, all, p1.exprs _ _ e2, hk⟩
  | opaq v u =>
    simp only
    obtain ⟨e1, e2, e3, e4⟩ := Emit.expr_spec C.1 v
    obtain ⟨p1, -, -⟩ := Emit.push_spec (C.1.expr v).1 (.opaq C.2 (C.1.expr v).2 u)
    exact pushed _ (.opaq C.2 (C.1.expr v).2 u) e1 (e3.trans h3) (e4.trans h4)
      ⟨(h2.mono e1).mono p1, v, p1.exprs _ _ e2, hk⟩
  | quot k =>
    simp only
    obtain ⟨p1, -, -⟩ := Emit.push_spec C.1 (.quot C.2 k)
    exact pushed C.1 (.quot C.2 k) (Emit.Sub.refl _) h3 h4 ⟨h2.mono p1, hk⟩
  | induct _ _ _ _ _ _ _ _ =>
    simp only
    exact ⟨h1, h3, fun r hm => .inl (h4 ▸ hm), by simp [CKindF.tag]⟩
  | ctor _ _ _ _ _ =>
    simp only
    exact ⟨h1, h3, fun r hm => .inl (h4 ▸ hm), by simp [CKindF.tag]⟩
  | recur _ _ _ _ _ _ _ _ =>
    simp only
    exact ⟨h1, h3, fun r hm => .inl (h4 ▸ hm), by simp [CKindF.tag]⟩

/-- A fold that adds to the tables, gathering what it says of each constant. -/
theorem block_fold {α : Type} {Q : Emit → α → Prop}
    (hQ : ∀ {a b : Emit} {x : α}, Emit.Sub a b → Q a x → Q b x)
    {f : Emit × Array α → CEntry → Emit × Array α} {l : List CEntry}
    (hf : ∀ st acc c, c ∈ l → Emit.Sub st (f (st, acc) c).1 ∧ (f (st, acc) c).1.visited = st.visited ∧
      (f (st, acc) c).1.out = st.out ∧ ∀ x ∈ (f (st, acc) c).2, x ∈ acc ∨ Q (f (st, acc) c).1 x)
    (st : Emit) (acc : Array α) (ha : ∀ x ∈ acc, Q st x) :
    Emit.Sub st (l.foldl f (st, acc)).1 ∧ (l.foldl f (st, acc)).1.visited = st.visited ∧
      (l.foldl f (st, acc)).1.out = st.out ∧ ∀ x ∈ (l.foldl f (st, acc)).2, Q (l.foldl f (st, acc)).1 x := by
  induction l generalizing st acc with
  | nil => exact ⟨Emit.Sub.refl _, rfl, rfl, ha⟩
  | cons c l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := hf st acc c List.mem_cons_self
    generalize hx : f (st, acc) c = x at h1 h2 h3 h4
    obtain ⟨g1, g2, g3, g4⟩ := ih (fun st acc c hc => hf st acc c (List.mem_cons_of_mem _ hc)) x.1 x.2
      (fun y hy => by
        rcases h4 y hy with h5 | h5
        · exact hQ h1 (ha y h5)
        · exact h5)
    exact ⟨h1.trans g1, g2.trans h2, g3.trans h3, g4⟩

theorem Emit.names'_spec (st : Emit) (ns : List Name) :
    Emit.Sub st (st.names' ns).1 ∧ (st.names' ns).1.visited = st.visited ∧ (st.names' ns).1.out = st.out :=
  let h := names_fold ns st #[]
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem ruleStep_fold (rules : List (Name × Nat × Expr)) : ∀ (st : Emit) (acc : Array RuleRec),
    Emit.Sub st (rules.foldl Emit.ruleStep (st, acc)).1 ∧
      (rules.foldl Emit.ruleStep (st, acc)).1.visited = st.visited ∧
      (rules.foldl Emit.ruleStep (st, acc)).1.out = st.out := by
  induction rules with
  | nil => intro st acc; exact ⟨Emit.Sub.refl _, rfl, rfl⟩
  | cons x rules ih =>
    intro st acc
    obtain ⟨cn, nf, rhs⟩ := x
    obtain ⟨h1, -, h3, h4⟩ := Emit.name_spec st cn
    obtain ⟨g1, -, g3, g4⟩ := Emit.expr_spec (st.name cn).1 rhs
    obtain ⟨k1, k3, k4⟩ := ih (st.name cn).1 |> fun _ => ih ((st.name cn).1.expr rhs).1
      (acc.push { ctor := (st.name cn).2, nfields := nf, rhs := ((st.name cn).1.expr rhs).2 })
    exact ⟨(h1.trans g1).trans k1, k3.trans (g3.trans h3), k4.trans (g4.trans h4)⟩

/-- **A block's record.** -/
theorem Emit.block_spec (mg : Merged) (st : Emit) (tys ctors recs : List CEntry)
    (ht : ∀ c ∈ tys, Stored mg c) (hc : ∀ c ∈ ctors, Stored mg c) (hr : ∀ c ∈ recs, Stored mg c) :
    Emit.Sub st (st.block tys ctors recs) ∧ (st.block tys ctors recs).visited = st.visited ∧
      ∀ r ∈ (st.block tys ctors recs).out, r ∈ st.out ∨ RecFrom mg (st.block tys ctors recs) r := by
  have F1 := block_fold (Q := fun em (t : IndTypeRec) => ∃ c, Stored mg c ∧ CvOf em t.cv c ∧ c.kind.tag = 5)
    (fun h ⟨c, x, y, z⟩ => ⟨c, x, y.mono h, z⟩) (f := Emit.tyStep) (l := tys)
    (by
      intro st acc c hm
      unfold Emit.tyStep
      cases hk : c.kind with
      | induct np ni all cs nn ir iu irf =>
        obtain ⟨h1, h2, h3, h4⟩ := Emit.cv_spec st c
        obtain ⟨g1, g3, g4⟩ := Emit.names'_spec (st.cv c).1 cs
        refine ⟨h1.trans g1, g3.trans h3, g4.trans h4, fun x hx => ?_⟩
        rcases Array.mem_push.mp hx with hx | rfl
        · exact .inl hx
        · exact .inr ⟨c, ht c hm, h2.mono g1, by simp [hk, CKindF.tag]⟩
      | ax _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | defn _ _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | thm _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | opaq _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | quot _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | ctor _ _ _ _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | recur _ _ _ _ _ _ _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩)
    st #[] (by simp)
  generalize hF1 : tys.foldl Emit.tyStep (st, #[]) = X1 at F1
  obtain ⟨a1, a2, a3, a4⟩ := F1
  have F2 := block_fold (Q := fun em (t : IndCtorRec) => ∃ c, Stored mg c ∧ CvOf em t.cv c ∧ c.kind.tag = 6)
    (fun h ⟨c, x, y, z⟩ => ⟨c, x, y.mono h, z⟩) (f := Emit.ctorStep) (l := ctors)
    (by
      intro st acc c hm
      unfold Emit.ctorStep
      cases hk : c.kind with
      | ctor ind cidx np nf iu =>
        obtain ⟨h1, h2, h3, h4⟩ := Emit.cv_spec st c
        obtain ⟨g1, -, g3, g4⟩ := Emit.name_spec (st.cv c).1 ind
        refine ⟨h1.trans g1, g3.trans h3, g4.trans h4, fun x hx => ?_⟩
        rcases Array.mem_push.mp hx with hx | rfl
        · exact .inl hx
        · exact .inr ⟨c, hc c hm, h2.mono g1, by simp [hk, CKindF.tag]⟩
      | ax _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | defn _ _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | thm _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | opaq _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | quot _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | induct _ _ _ _ _ _ _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | recur _ _ _ _ _ _ _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩)
    X1.1 #[] (by simp)
  generalize hF2 : ctors.foldl Emit.ctorStep (X1.1, #[]) = X2 at F2
  obtain ⟨b1, b2, b3, b4⟩ := F2
  have F3 := block_fold (Q := fun em (t : IndRecRec) => ∃ c, Stored mg c ∧ CvOf em t.cv c ∧ c.kind.tag = 7)
    (fun h ⟨c, x, y, z⟩ => ⟨c, x, y.mono h, z⟩) (f := Emit.recStep) (l := recs)
    (by
      intro st acc c hm
      unfold Emit.recStep
      cases hk : c.kind with
      | recur all np ni nmo nmi rules k iu =>
        obtain ⟨h1, h2, h3, h4⟩ := Emit.cv_spec st c
        obtain ⟨g1, g3, g4⟩ := ruleStep_fold rules (st.cv c).1 #[]
        refine ⟨h1.trans g1, g3.trans h3, g4.trans h4, fun x hx => ?_⟩
        rcases Array.mem_push.mp hx with hx | rfl
        · exact .inl hx
        · exact .inr ⟨c, hr c hm, h2.mono g1, by simp [hk, CKindF.tag]⟩
      | ax _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | defn _ _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | thm _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | opaq _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | quot _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | induct _ _ _ _ _ _ _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩
      | ctor _ _ _ _ _ => exact ⟨Emit.Sub.refl _, rfl, rfl, fun x hx => .inl hx⟩)
    X2.1 #[] (by simp)
  generalize hF3 : recs.foldl Emit.recStep (X2.1, #[]) = X3 at F3
  obtain ⟨c1, c2, c3, c4⟩ := F3
  have hb : st.block tys ctors recs = X3.1.push (.ind X1.2.toList X2.2.toList X3.2.toList) := by
    subst hF3 hF2 hF1
    rfl
  rw [hb]
  obtain ⟨p1, p2, p3⟩ := Emit.push_spec X3.1 (.ind X1.2.toList X2.2.toList X3.2.toList)
  have hS23 := b1.trans c1
  refine ⟨((a1.trans b1).trans c1).trans p1, p2.trans (c2.trans (b2.trans a2)), fun r hm => ?_⟩
  rw [p3, c3, b3, a3] at hm
  rcases Array.mem_push.mp hm with hm | rfl
  · exact .inl hm
  · refine .inr ⟨fun t ht' => ?_, fun t ht' => ?_, fun t ht' => ?_⟩
    · obtain ⟨c, x, y, z⟩ := a4 t (by simpa using ht')
      exact ⟨c, x, (y.mono hS23).mono p1, z⟩
    · obtain ⟨c, x, y, z⟩ := b4 t (by simpa using ht')
      exact ⟨c, x, (y.mono c1).mono p1, z⟩
    · obtain ⟨c, x, y, z⟩ := c4 t (by simpa using ht')
      exact ⟨c, x, y.mono p1, z⟩

/-- A fold that adds to the tables keeps what each step gathered. -/
theorem fold_has {α : Type} {f : Emit × Array α → CEntry → Emit × Array α} (nameOf : α → Nat)
    (P : CEntry → Prop)
    (hf : ∀ st acc c, Emit.Sub st (f (st, acc) c).1 ∧ (∀ x ∈ acc, x ∈ (f (st, acc) c).2) ∧
      (P c → ∃ x ∈ (f (st, acc) c).2, (f (st, acc) c).1.names[nameOf x]? = some c.name))
    (l : List CEntry) (st : Emit) (acc : Array α) :
    Emit.Sub st (l.foldl f (st, acc)).1 ∧ (∀ x ∈ acc, x ∈ (l.foldl f (st, acc)).2) ∧
      ∀ c ∈ l, P c → ∃ x ∈ (l.foldl f (st, acc)).2, (l.foldl f (st, acc)).1.names[nameOf x]? = some c.name := by
  induction l generalizing st acc with
  | nil => exact ⟨Emit.Sub.refl _, fun _ h => h, by simp⟩
  | cons c l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := hf st acc c
    generalize hx : f (st, acc) c = X at h1 h2 h3
    obtain ⟨g1, g2, g3⟩ := ih X.1 X.2
    refine ⟨h1.trans g1, fun x hx' => g2 x (h2 x hx'), fun d hd hp => ?_⟩
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨x, hx1, hx2⟩ := h3 hp
      exact ⟨x, g2 x hx1, g1.names _ _ hx2⟩
    · exact g3 d hd hp

theorem Emit.tyStep_has (st : Emit) (acc : Array IndTypeRec) (c : CEntry) :
    Emit.Sub st (Emit.tyStep (st, acc) c).1 ∧ (∀ x ∈ acc, x ∈ (Emit.tyStep (st, acc) c).2) ∧
      (c.kind.tag = 5 → ∃ x ∈ (Emit.tyStep (st, acc) c).2,
        (Emit.tyStep (st, acc) c).1.names[x.cv.name]? = some c.name) := by
  unfold Emit.tyStep
  cases hk : c.kind with
  | induct np ni all cs nn ir iu irf =>
    obtain ⟨h1, h2, -, -⟩ := Emit.cv_spec st c
    obtain ⟨g1, -, -⟩ := Emit.names'_spec (st.cv c).1 cs
    exact ⟨h1.trans g1, fun x hx => Array.mem_push.mpr (.inl hx),
      fun _ => ⟨_, Array.mem_push.mpr (.inr rfl), g1.names _ _ h2.1⟩⟩
  | _ => exact ⟨Emit.Sub.refl _, fun _ h => h, by simp [CKindF.tag]⟩

theorem Emit.ctorStep_has (st : Emit) (acc : Array IndCtorRec) (c : CEntry) :
    Emit.Sub st (Emit.ctorStep (st, acc) c).1 ∧ (∀ x ∈ acc, x ∈ (Emit.ctorStep (st, acc) c).2) ∧
      (c.kind.tag = 6 → ∃ x ∈ (Emit.ctorStep (st, acc) c).2,
        (Emit.ctorStep (st, acc) c).1.names[x.cv.name]? = some c.name) := by
  unfold Emit.ctorStep
  cases hk : c.kind with
  | ctor ind cidx np nf iu =>
    obtain ⟨h1, h2, -, -⟩ := Emit.cv_spec st c
    obtain ⟨g1, -, -, -⟩ := Emit.name_spec (st.cv c).1 ind
    exact ⟨h1.trans g1, fun x hx => Array.mem_push.mpr (.inl hx),
      fun _ => ⟨_, Array.mem_push.mpr (.inr rfl), g1.names _ _ h2.1⟩⟩
  | _ => exact ⟨Emit.Sub.refl _, fun _ h => h, by simp [CKindF.tag]⟩

theorem Emit.recStep_has (st : Emit) (acc : Array IndRecRec) (c : CEntry) :
    Emit.Sub st (Emit.recStep (st, acc) c).1 ∧ (∀ x ∈ acc, x ∈ (Emit.recStep (st, acc) c).2) ∧
      (c.kind.tag = 7 → ∃ x ∈ (Emit.recStep (st, acc) c).2,
        (Emit.recStep (st, acc) c).1.names[x.cv.name]? = some c.name) := by
  unfold Emit.recStep
  cases hk : c.kind with
  | recur all np ni nmo nmi rules k iu =>
    obtain ⟨h1, h2, -, -⟩ := Emit.cv_spec st c
    obtain ⟨g1, -, -⟩ := ruleStep_fold rules (st.cv c).1 #[]
    exact ⟨h1.trans g1, fun x hx => Array.mem_push.mpr (.inl hx),
      fun _ => ⟨_, Array.mem_push.mpr (.inr rfl), g1.names _ _ h2.1⟩⟩
  | _ => exact ⟨Emit.Sub.refl _, fun _ h => h, by simp [CKindF.tag]⟩

theorem Emit.block_sub (st : Emit) (tys ctors recs : List CEntry) :
    Emit.Sub st (st.block tys ctors recs) := by
  obtain ⟨a1, -, -⟩ := fold_has (fun x : IndTypeRec => x.cv.name) (fun _ => False) (by
    intro st acc c
    obtain ⟨h1, h2, -⟩ := Emit.tyStep_has st acc c
    exact ⟨h1, h2, False.elim⟩) tys st #[]
  generalize hF1 : tys.foldl Emit.tyStep (st, #[]) = X1 at a1
  obtain ⟨b1, -, -⟩ := fold_has (fun x : IndCtorRec => x.cv.name) (fun _ => False) (by
    intro st acc c
    obtain ⟨h1, h2, -⟩ := Emit.ctorStep_has st acc c
    exact ⟨h1, h2, False.elim⟩) ctors X1.1 #[]
  generalize hF2 : ctors.foldl Emit.ctorStep (X1.1, #[]) = X2 at b1
  obtain ⟨c1, -, -⟩ := fold_has (fun x : IndRecRec => x.cv.name) (fun _ => False) (by
    intro st acc c
    obtain ⟨h1, h2, -⟩ := Emit.recStep_has st acc c
    exact ⟨h1, h2, False.elim⟩) recs X2.1 #[]
  generalize hF3 : recs.foldl Emit.recStep (X2.1, #[]) = X3 at c1
  have hb : st.block tys ctors recs = X3.1.push (.ind X1.2.toList X2.2.toList X3.2.toList) := by
    subst hF3 hF2 hF1
    rfl
  rw [hb]
  exact ((a1.trans b1).trans c1).trans (Emit.push_spec _ _).1

/-- **A block's record declares its parts**, those of the right kind. -/
theorem Emit.block_has (st : Emit) (tys ctors recs : List CEntry) :
    (∀ c ∈ tys, c.kind.tag = 5 → Has (st.block tys ctors recs) c.name) ∧
    (∀ c ∈ ctors, c.kind.tag = 6 → Has (st.block tys ctors recs) c.name) ∧
    (∀ c ∈ recs, c.kind.tag = 7 → Has (st.block tys ctors recs) c.name) := by
  obtain ⟨a1, -, a3⟩ := fold_has (fun x : IndTypeRec => x.cv.name) (fun c => c.kind.tag = 5) Emit.tyStep_has tys st #[]
  generalize hF1 : tys.foldl Emit.tyStep (st, #[]) = X1 at a1 a3
  obtain ⟨b1, -, b3⟩ := fold_has (fun x : IndCtorRec => x.cv.name) (fun c => c.kind.tag = 6) Emit.ctorStep_has ctors X1.1 #[]
  generalize hF2 : ctors.foldl Emit.ctorStep (X1.1, #[]) = X2 at b1 b3
  obtain ⟨c1, -, c3⟩ := fold_has (fun x : IndRecRec => x.cv.name) (fun c => c.kind.tag = 7) Emit.recStep_has recs X2.1 #[]
  generalize hF3 : recs.foldl Emit.recStep (X2.1, #[]) = X3 at c1 c3
  have hb : st.block tys ctors recs = X3.1.push (.ind X1.2.toList X2.2.toList X3.2.toList) := by
    subst hF3 hF2 hF1
    rfl
  rw [hb]
  obtain ⟨p1, -, p3⟩ := Emit.push_spec X3.1 (.ind X1.2.toList X2.2.toList X3.2.toList)
  have hin : DeclRec.ind X1.2.toList X2.2.toList X3.2.toList ∈
      (X3.1.push (.ind X1.2.toList X2.2.toList X3.2.toList)).out := by
    rw [p3]
    exact Array.mem_push.mpr (.inr rfl)
  refine ⟨fun c hc ht => ?_, fun c hc ht => ?_, fun c hc ht => ?_⟩
  · obtain ⟨x, hx, hn⟩ := a3 c hc ht
    exact ⟨_, hin, .inl ⟨x, by simpa using hx, p1.names _ _ (c1.names _ _ (b1.names _ _ hn))⟩⟩
  · obtain ⟨x, hx, hn⟩ := b3 c hc ht
    exact ⟨_, hin, .inr (.inl ⟨x, by simpa using hx, p1.names _ _ (c1.names _ _ hn)⟩)⟩
  · obtain ⟨x, hx, hn⟩ := c3 c hc ht
    exact ⟨_, hin, .inr (.inr ⟨x, by simpa using hx, p1.names _ _ hn⟩)⟩

/-! ## The walk -/

/-- Stack items' constants are stored. -/
@[expose] def WorkOk (mg : Merged) : Work → Prop
  | .visit _ => True
  | .one c => Stored mg c
  | .quot cs => ∀ c ∈ cs, Stored mg c
  | .block ts cs rs => (∀ c ∈ ts, Stored mg c) ∧ (∀ c ∈ cs, Stored mg c) ∧ ∀ c ∈ rs, Stored mg c

/-- What a stretch of the walk does. -/
abbrev WalkGoal (mg : Merged) (st : Emit) (stack : List Work) (e : Emit) : Prop :=
  Emit.Sub st e ∧ (∀ k, st.visited.contains k = true → e.visited.contains k = true) ∧
    (∀ r ∈ e.out, RecFrom mg e r) ∧
    ∀ n, Work.visit n ∈ stack → ∀ c, mg.map[n]? = some c → c.skipped = false →
      e.visited.contains n = true

theorem Emit.mark_spec (st : Emit) (n : Name) :
    Emit.Sub st (st.mark n) ∧ (st.mark n).out = st.out ∧
      (∀ k, st.visited.contains k = true → (st.mark n).visited.contains k = true) ∧
      (st.mark n).visited.contains n = true := by
  obtain ⟨v, ns, es, o⟩ := st
  refine ⟨⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h⟩, rfl, fun k hk => ?_, ?_⟩
  · simp only [Emit.mark, Std.HashSet.contains_insert, Bool.or_eq_true]
    exact .inr hk
  · simp [Emit.mark]

/-- Constants marked. -/
theorem Emit.marks_spec (cs : List CEntry) : ∀ st : Emit,
    Emit.Sub st (cs.foldl (fun st x => st.mark x.name) st) ∧
      (cs.foldl (fun st x => st.mark x.name) st).out = st.out ∧
      ∀ k, st.visited.contains k = true →
        (cs.foldl (fun st x => st.mark x.name) st).visited.contains k = true := by
  induction cs with
  | nil => intro st; exact ⟨Emit.Sub.refl _, rfl, fun _ h => h⟩
  | cons c cs ih =>
    intro st
    obtain ⟨h1, h2, h3, -⟩ := Emit.mark_spec st c.name
    obtain ⟨g1, g2, g3⟩ := ih (st.mark c.name)
    exact ⟨h1.trans g1, g2.trans h2, fun k hk => g3 k (h3 k hk)⟩

/-- Constants' records. -/
theorem Emit.ones_spec (mg : Merged) (cs : List CEntry) : ∀ st : Emit, (∀ c ∈ cs, Stored mg c) →
    (∀ r ∈ st.out, RecFrom mg st r) →
    Emit.Sub st (cs.foldl Emit.one st) ∧ (cs.foldl Emit.one st).visited = st.visited ∧
      ∀ r ∈ (cs.foldl Emit.one st).out, RecFrom mg (cs.foldl Emit.one st) r := by
  induction cs with
  | nil => intro st _ ho; exact ⟨Emit.Sub.refl _, rfl, ho⟩
  | cons c cs ih =>
    intro st hc ho
    obtain ⟨h1, h2, h3, -⟩ := Emit.one_spec st c
    obtain ⟨g1, g2, g3⟩ := ih (st.one c) (fun x hx => hc x (List.mem_cons_of_mem _ hx)) (fun r hr => by
      rcases h3 r hr with h4 | h4
      · exact RecFrom.mono h1 (ho r h4)
      · cases r with
        | ind _ _ _ => exact h4.elim
        | ax _ _ => exact ⟨c, hc c List.mem_cons_self, h4⟩
        | defn _ _ _ _ => exact ⟨c, hc c List.mem_cons_self, h4⟩
        | thm _ _ => exact ⟨c, hc c List.mem_cons_self, h4⟩
        | opaq _ _ _ => exact ⟨c, hc c List.mem_cons_self, h4⟩
        | quot _ _ => exact ⟨c, hc c List.mem_cons_self, h4⟩)
    exact ⟨h1.trans g1, g2.trans h2, g3⟩

/-- A `visit` that marks and goes on with what the stack has become. -/
theorem walk_mark {mg : Merged} {s0 s1 e : Emit} {n : Name} {stack' rest : List Work}
    (ih : (∀ w ∈ stack', WorkOk mg w) → (∀ r ∈ s1.out, RecFrom mg s1 r) → WalkGoal mg s1 stack' e)
    (hs : Emit.Sub s0 s1) (ho : s1.out = s0.out)
    (hm : ∀ k, s0.visited.contains k = true → s1.visited.contains k = true)
    (hn : s1.visited.contains n = true) (hrest : ∀ m, Work.visit m ∈ rest → Work.visit m ∈ stack')
    (hw : ∀ w ∈ stack', WorkOk mg w) (hO : ∀ r ∈ s0.out, RecFrom mg s0 r) :
    WalkGoal mg s0 (Work.visit n :: rest) e := by
  obtain ⟨g1, g2, g3, g4⟩ := ih hw (fun r hr => RecFrom.mono hs (hO r (ho ▸ hr)))
  refine ⟨hs.trans g1, fun k hk => g2 k (hm k hk), g3, fun m hm' c hc hsk => ?_⟩
  rcases List.mem_cons.mp hm' with h | h
  · cases h
    exact g2 _ hn
  · exact g4 m (hrest m h) c hc hsk

theorem visits_ok {mg : Merged} {cs : List CEntry} {w : Work}
    (h : w ∈ Work.usesOf cs) : WorkOk mg w := by
  obtain ⟨c, -, h⟩ := List.mem_flatMap.mp h
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
  trivial

theorem Emit.ones_eq (st : Emit) (cs : List CEntry) : st.ones cs = cs.foldl Emit.one st := rfl

theorem emitLoop_spec (mg : Merged) (recMap : Std.HashMap Name (Array Name))
    (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n) (stack : List Work) (st : Emit) :
    (∀ w ∈ stack, WorkOk mg w) → (∀ r ∈ st.out, RecFrom mg st r) →
    WalkGoal mg st stack (emitLoop mg recMap stack st) := by
  have mapStored : ∀ {x : Name} {c : CEntry}, mg.map[x]? = some c → Stored mg c := by
    intro x c h
    unfold Stored
    rw [hN x c h]
    exact h
  have one : ∀ {s0 : Emit} {n : Name} {c : CEntry} {rest extra : List Work} {e : Emit},
      mg.map[n]? = some c → (∀ w ∈ extra, WorkOk mg w) →
      (∀ w ∈ Work.visit n :: rest, WorkOk mg w) → (∀ r ∈ s0.out, RecFrom mg s0 r) →
      ((∀ w ∈ extra ++ Work.one c :: rest, WorkOk mg w) → (∀ r ∈ (s0.mark n).out, RecFrom mg (s0.mark n) r) →
        WalkGoal mg (s0.mark n) (extra ++ Work.one c :: rest) e) →
      WalkGoal mg s0 (Work.visit n :: rest) e := by
    intro s0 n c rest extra e hc hx hw ho ih
    obtain ⟨m1, m2, m3, m4⟩ := Emit.mark_spec s0 n
    refine walk_mark ih m1 m2 m3 m4 (fun m hm => by simp [hm]) (fun w hm => ?_) ho
    rcases List.mem_append.mp hm with hm | hm
    · exact hx w hm
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact mapStored hc
      · exact hw w (List.mem_cons_of_mem _ hm)
  fun_induction emitLoop mg recMap stack st
  all_goals intro hw ho
  case case1 st => exact ⟨Emit.Sub.refl _, fun _ h => h, ho, fun n hn => by simp at hn⟩
  case case2 st c rest ih =>
    obtain ⟨h1, h2, h3, -⟩ := Emit.one_spec st c
    have hc : Stored mg c := hw _ List.mem_cons_self
    obtain ⟨g1, g2, g3, g4⟩ := ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) (fun r hr => by
      rcases h3 r hr with h4 | h4
      · exact RecFrom.mono h1 (ho r h4)
      · cases r with
        | ind _ _ _ => exact h4.elim
        | ax _ _ => exact ⟨c, hc, h4⟩
        | defn _ _ _ _ => exact ⟨c, hc, h4⟩
        | thm _ _ => exact ⟨c, hc, h4⟩
        | opaq _ _ _ => exact ⟨c, hc, h4⟩
        | quot _ _ => exact ⟨c, hc, h4⟩)
    refine ⟨h1.trans g1, fun k hk => g2 k (h2 ▸ hk), g3, fun m hm => ?_⟩
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    · exact g4 m hm
  case case3 st cs rest ih =>
    obtain ⟨h1, h2, h3⟩ := Emit.ones_spec mg cs st (hw _ List.mem_cons_self) ho
    obtain ⟨g1, g2, g3, g4⟩ := ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) h3
    refine ⟨h1.trans g1, fun k hk => g2 k (h2 ▸ hk), g3, fun m hm => ?_⟩
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    · exact g4 m hm
  case case4 st ts cs rs rest ih =>
    obtain ⟨b1, b2, b3⟩ : WorkOk mg (Work.block ts cs rs) := hw _ List.mem_cons_self
    obtain ⟨h1, h2, h3⟩ := Emit.block_spec mg st ts cs rs b1 b2 b3
    obtain ⟨g1, g2, g3, g4⟩ := ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) (fun r hr => by
      rcases h3 r hr with h4 | h4
      · exact RecFrom.mono h1 (ho r h4)
      · exact h4)
    refine ⟨h1.trans g1, fun k hk => g2 k (h2 ▸ hk), g3, fun m hm => ?_⟩
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    · exact g4 m hm
  case case5 st n rest hv ih =>
    obtain ⟨g1, g2, g3, g4⟩ := ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) ho
    refine ⟨g1, g2, g3, fun m hm c hc hsk => ?_⟩
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
      exact g2 _ hv
    · exact g4 m hm c hc hsk
  case case6 st n rest hv hc ih =>
    obtain ⟨g1, g2, g3, g4⟩ := ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) ho
    refine ⟨g1, g2, g3, fun m hm c hc' hsk => ?_⟩
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
      rw [hc] at hc'
      cases hc'
    · exact g4 m hm c hc' hsk
  case case7 st n rest hv c hc hs ih =>
    obtain ⟨g1, g2, g3, g4⟩ := ih (fun w hm => hw w (List.mem_cons_of_mem _ hm)) ho
    refine ⟨g1, g2, g3, fun m hm c' hc' hsk => ?_⟩
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
      rw [hc] at hc'
      cases hc'
      rw [hs] at hsk
      cases hsk
    · exact g4 m hm c' hc' hsk
  case case8 s0 n rest hv c hc hs s1 _ hk ih =>
    exact one hc (fun w hm => visits_ok hm) hw ho ih
  case case9 s0 n rest hv c hc hs s1 _ _ _ hk ih =>
    exact one hc (fun w hm => visits_ok hm) hw ho ih
  case case10 s0 n rest hv c hc hs s1 _ _ hk ih =>
    exact one hc (fun w hm => visits_ok hm) hw ho ih
  case case11 s0 n rest hv c hc hs s1 _ _ hk ih =>
    exact one hc (fun w hm => visits_ok hm) hw ho ih
  case case12 s0 n rest hv c hc hs s1 _ hk qs s2 ih =>
    obtain ⟨m1, m2, m3, m4⟩ := Emit.mark_spec s0 n
    obtain ⟨q1, q2, q3⟩ := Emit.marks_spec qs s1
    refine walk_mark (s1 := s2) ih (m1.trans q1) (q2.trans m2) (fun k hk' => q3 k (m3 k hk')) (q3 _ m4)
      (fun m hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)) (fun w hm => ?_) ho
    rcases List.mem_cons.mp hm with rfl | hm
    · trivial
    rcases List.mem_cons.mp hm with rfl | hm
    · intro x hx
      obtain ⟨y, -, hy⟩ := List.mem_filterMap.mp hx
      exact mapStored hy
    · exact hw w (List.mem_cons_of_mem _ hm)
  case case13 s0 n rest hv c hc hs s1 _ _ _ _ _ hk ih =>
    obtain ⟨m1, m2, m3, m4⟩ := Emit.mark_spec s0 n
    refine walk_mark ih m1 m2 m3 m4 (fun m hm => List.mem_cons_of_mem _ hm) (fun w hm => ?_) ho
    rcases List.mem_cons.mp hm with rfl | hm
    · trivial
    · exact hw w (List.mem_cons_of_mem _ hm)
  case case14 s0 n rest hv c hc hs s1 all _ _ _ _ _ _ _ hk ih =>
    obtain ⟨m1, m2, m3, m4⟩ := Emit.mark_spec s0 n
    refine walk_mark ih m1 m2 m3 m4 (fun m hm => List.mem_append_right _ hm) (fun w hm => ?_) ho
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hm
      trivial
    · exact hw w (List.mem_cons_of_mem _ hm)
  case case15 s0 n rest hv c hc hs s1 _ _ _ _ _ _ _ _ hk tys cts recs s2 ih =>
    obtain ⟨m1, m2, m3, m4⟩ := Emit.mark_spec s0 n
    obtain ⟨q1, q2, q3⟩ := Emit.marks_spec (tys ++ cts ++ recs) s1
    have hT : ∀ x ∈ tys, Stored mg x := by
      intro x hx
      obtain ⟨y, -, hy⟩ := List.mem_filterMap.mp hx
      exact mapStored hy
    have hC : ∀ x ∈ cts, Stored mg x := by
      intro x hx
      obtain ⟨t, -, hx⟩ := List.mem_flatMap.mp hx
      split at hx
      · obtain ⟨y, -, hy⟩ := List.mem_filterMap.mp hx
        exact mapStored hy
      · simp at hx
    have hR : ∀ x ∈ recs, Stored mg x := by
      intro x hx
      obtain ⟨y, -, hy⟩ := List.mem_filterMap.mp hx
      exact mapStored hy
    refine walk_mark (s1 := s2) (stack' := Work.usesOf (tys ++ cts ++ recs) ++ Work.block tys cts recs :: rest)
      ih (m1.trans q1) (q2.trans m2) (fun k hk' => q3 k (m3 k hk')) (q3 _ m4)
      (fun m hm => List.mem_append_right _ (List.mem_cons_of_mem _ hm)) (fun w hm => ?_) ho
    rcases List.mem_append.mp hm with hm | hm
    · exact visits_ok hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨hT, hC, hR⟩
    · exact hw w (List.mem_cons_of_mem _ hm)

/-- **The walk from its roots**: every record comes from stored constants, and every root
stored and not filtered out is visited. -/
theorem emitAll_spec {mg : Merged} (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n)
    (rs : Array Name) :
    (∀ r ∈ (emitAll mg rs).out, RecFrom mg (emitAll mg rs) r) ∧
      ∀ n ∈ rs, ∀ c, mg.map[n]? = some c → c.skipped = false →
        (emitAll mg rs).visited.contains n = true := by
  unfold emitAll
  obtain ⟨-, -, h3, h4⟩ := emitLoop_spec mg (recMapOf mg) hN (rs.toList.map Work.visit) {}
    (fun w hw => by
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hw
      trivial)
    (fun r hr => by simp at hr)
  exact ⟨h3, fun n hn c hc hsk => h4 n (List.mem_map.mpr ⟨n, by simpa using hn, rfl⟩) c hc hsk⟩

/-! ## The blocks -/

/-- An inductive type of that block and those constructors. -/
@[expose] def IsInd (c : CEntry) (all cs : List Name) : Prop :=
  ∃ np ni nn ir iu irf, c.kind = .induct np ni all cs nn ir iu irf

/-- A constructor of that type. -/
@[expose] def IsCtor (c : CEntry) (ind : Name) : Prop :=
  ∃ cidx np nf iu, c.kind = .ctor ind cidx np nf iu

/-- A recursor of that block. -/
@[expose] def IsRec (c : CEntry) (all : List Name) : Prop :=
  ∃ np ni nmo nmi rules k iu, c.kind = .recur all np ni nmo nmi rules k iu

/-- **The stored constants' blocks agree.** -/
structure BlocksGood (mg : Merged) : Prop where
  ind : ∀ {n : Name} {c : CEntry} {all cs : List Name}, mg.map[n]? = some c → IsInd c all cs → n ∈ all ∧
    (∀ x ∈ all, ∃ m cs', mg.map[x]? = some m ∧ IsInd m all cs' ∧ m.skipped = c.skipped) ∧
    (∀ x ∈ cs, ∃ m, mg.map[x]? = some m ∧ IsCtor m n ∧ m.skipped = c.skipped)
  ctor : ∀ {n : Name} {c : CEntry} {ind : Name}, mg.map[n]? = some c → IsCtor c ind →
    ∃ m all cs, mg.map[ind]? = some m ∧ IsInd m all cs ∧ n ∈ cs
  recur : ∀ {n : Name} {c : CEntry} {all : List Name}, mg.map[n]? = some c → IsRec c all →
    ∃ t rest m cs, all = t :: rest ∧ mg.map[t]? = some m ∧ IsInd m all cs ∧ m.skipped = c.skipped
  quot : ∀ {n : Name} {c : CEntry} {k : String}, mg.map[n]? = some c → c.kind = .quot k →
    c ∈ quotConstants mg ∧ ∀ q ∈ quotConstants mg, q.kind.tag = 4

theorem IsInd.unique {c : CEntry} {a a' b b' : List Name} (h : IsInd c a b) (h' : IsInd c a' b') :
    a = a' ∧ b = b' := by
  obtain ⟨_, _, _, _, _, _, h1⟩ := h
  obtain ⟨_, _, _, _, _, _, h2⟩ := h'
  rw [h1] at h2
  cases h2
  exact ⟨rfl, rfl⟩

/-- A `forM` that succeeds succeeds on each element. -/
theorem forM_ok {f : Name → Except CheckError Unit} : ∀ {l : List Name}, l.forM f = .ok () →
    ∀ x ∈ l, f x = .ok ()
  | [], _, x, hx => by simp at hx
  | y :: l, hl, x, hx => by
    have hl' : (f y >>= fun _ => l.forM f) = Except.ok () := hl
    cases hy : f y with
    | error e => simp [hy, bind, Except.bind] at hl'
    | ok u =>
      rw [hy] at hl'
      rcases List.mem_cons.mp hx with rfl | hx
      · cases u; exact hy
      · exact forM_ok hl' x hx

theorem blockMemberOk_ok {mg : Merged} {n x : Name} {all : List Name} {sk : Bool}
    (h : blockMemberOk mg n all sk x = .ok ()) :
    ∃ m cs', mg.map[x]? = some m ∧ IsInd m all cs' ∧ m.skipped = sk := by
  unfold blockMemberOk at h
  split at h
  · cases h
  · rename_i m hm
    split at h
    · rename_i all' cs _ _ _ _ hk
      split at h
      · rename_i h1
        split at h
        · rename_i h2
          obtain rfl : all' = all := by simpa using h1
          exact ⟨m, _, hm, ⟨_, _, _, _, _, _, hk⟩, by simpa using h2⟩
        · cases h
      · cases h
    · cases h

theorem blockCtorOk_ok {mg : Merged} {n x : Name} {sk : Bool} (h : blockCtorOk mg n sk x = .ok ()) :
    ∃ m, mg.map[x]? = some m ∧ IsCtor m n ∧ m.skipped = sk := by
  unfold blockCtorOk at h
  split at h
  · cases h
  · rename_i m hm
    split at h
    · rename_i ind _ _ _ _ hk
      split at h
      · rename_i h1
        split at h
        · rename_i h2
          obtain rfl : ind = n := by simpa using h1
          exact ⟨m, hm, ⟨_, _, _, _, hk⟩, by simpa using h2⟩
        · cases h
      · cases h
    · cases h

/-- **`blocksOk` says the blocks agree.** -/
theorem blocksOk_good {mg : Merged} (h : blocksOk mg = .ok ())
    (hO : ∀ n, n ∈ mg.order ↔ mg.map.contains n = true) : BlocksGood mg := by
  have step : ∀ {n c}, mg.map[n]? = some c → blockStep mg n = .ok () := by
    intro n c hc
    refine forM_ok h n (by simpa using (hO n).2 (contains_of_getElem hc))
  refine ⟨fun {n c all cs} hc hk => ?_, fun {n c ind} hc hk => ?_, fun {n c all} hc hk => ?_,
    fun {n c k} hc hk => ?_⟩
  · have hs := step hc
    obtain ⟨_, _, _, _, _, _, hk⟩ := hk
    simp only [blockStep, hc, hk] at hs
    split at hs
    · rename_i h1
      split at hs
      · cases hs
      · rename_i h2
        exact ⟨by simpa using h1, fun x hx => blockMemberOk_ok (forM_ok h2 x hx),
          fun x hx => blockCtorOk_ok (forM_ok hs x hx)⟩
    · cases hs
  · have hs := step hc
    obtain ⟨_, _, _, _, hk⟩ := hk
    simp only [blockStep, hc, hk] at hs
    split at hs
    · cases hs
    · rename_i t ht
      split at hs
      · rename_i all cs _ _ _ _ hk'
        split at hs
        · rename_i h1
          exact ⟨t, all, cs, ht, ⟨_, _, _, _, _, _, hk'⟩, by simpa using h1⟩
        · cases hs
      · cases hs
  · have hs := step hc
    obtain ⟨_, _, _, _, _, _, _, hk⟩ := hk
    simp only [blockStep, hc, hk] at hs
    split at hs
    · cases hs
    · rename_i t rest
      split at hs
      · cases hs
      · rename_i m hm
        split at hs
        · rename_i all' cs _ _ _ _ hk'
          split at hs
          · rename_i h1
            split at hs
            · rename_i h2
              obtain rfl : all' = t :: rest := by simpa using h1
              exact ⟨t, rest, m, cs, rfl, hm, ⟨_, _, _, _, _, _, hk'⟩, by simpa using h2⟩
            · cases hs
          · cases hs
        · cases hs
  · have hs := step hc
    simp only [blockStep, hc, hk] at hs
    split at hs
    · rename_i h1
      split at hs
      · rename_i h2
        refine ⟨?_, fun q hq => by simpa using List.all_eq_true.mp h2 q hq⟩
        have hn : n ∈ quotNames := by simpa using h1
        exact List.mem_filterMap.mpr ⟨n, hn, hc⟩
      · cases hs
    · cases hs

/-! ## The recursors of a block -/

theorem recMapAdd_mem (n i k r : Name) (m : Std.HashMap Name (Array Name)) :
    r ∈ ((recMapAdd n m i)[k]?).getD #[] ↔ r ∈ (m[k]?).getD #[] ∨ (i = k ∧ r = n) := by
  unfold recMapAdd
  rw [Std.HashMap.getElem?_alter]
  by_cases hik : i = k
  · subst hik
    simp only [beq_self_eq_true, ↓reduceIte]
    cases hm : m[i]? with
    | none => simp
    | some a =>
      simp only [Option.getD_some, true_and]
      by_cases ha : a.contains n = true
      · simp only [ha, ↓reduceIte]
        refine ⟨.inl, ?_⟩
        rintro (h | rfl)
        · exact h
        · simpa using ha
      · have hn : ¬ n ∈ a := by simpa using ha
        simp [hn, Array.mem_push]
  · have : (i == k) = false := by simpa using hik
    simp [this, hik]

theorem recMapAdds_mem (n k r : Name) (all : List Name) : ∀ m : Std.HashMap Name (Array Name),
    r ∈ ((all.foldl (recMapAdd n) m)[k]?).getD #[] ↔ r ∈ (m[k]?).getD #[] ∨ (k ∈ all ∧ r = n) := by
  induction all with
  | nil => intro m; simp
  | cons i all ih =>
    intro m
    simp only [List.foldl_cons, ih, recMapAdd_mem, List.mem_cons]
    constructor
    · rintro ((h | ⟨rfl, rfl⟩) | ⟨h1, rfl⟩)
      · exact .inl h
      · exact .inr ⟨.inl rfl, rfl⟩
      · exact .inr ⟨.inr h1, rfl⟩
    · rintro (h | ⟨rfl | h1, rfl⟩)
      · exact .inl (.inl h)
      · exact .inl (.inr ⟨rfl, rfl⟩)
      · exact .inr ⟨h1, rfl⟩

theorem recMapOf_go (mg : Merged) (k r : Name) (l : List Name) (m : Std.HashMap Name (Array Name)) :
    r ∈ ((l.foldl (recMapStep mg) m)[k]?).getD #[] ↔
      r ∈ (m[k]?).getD #[] ∨ (r ∈ l ∧ ∃ c all, mg.map[r]? = some c ∧ IsRec c all ∧ k ∈ all) := by
  induction l generalizing m with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    have hstep : r ∈ ((recMapStep mg m x)[k]?).getD #[] ↔
        r ∈ (m[k]?).getD #[] ∨ (r = x ∧ ∃ c all, mg.map[r]? = some c ∧ IsRec c all ∧ k ∈ all) := by
      unfold recMapStep
      split
      · rename_i all _ _ _ _ _ _ _ hk
        rw [recMapAdds_mem]
        obtain ⟨c, hc, hck⟩ := Option.map_eq_some_iff.mp hk
        constructor
        · rintro (h | ⟨h1, rfl⟩)
          · exact .inl h
          · exact .inr ⟨rfl, c, all, hc, ⟨_, _, _, _, _, _, _, hck⟩, h1⟩
        · rintro (h | ⟨rfl, c', all', hc', ⟨_, _, _, _, _, _, _, hk'⟩, h1⟩)
          · exact .inl h
          · rw [hc] at hc'
            cases hc'
            rw [hck] at hk'
            cases hk'
            exact .inr ⟨h1, rfl⟩
      · rename_i hk
        constructor
        · exact .inl
        · rintro (h | ⟨rfl, c', all', hc', ⟨a1, a2, a3, a4, a5, a6, a7, hk'⟩, h1⟩)
          · exact h
          · exact (hk all' a1 a2 a3 a4 a5 a6 a7 (by simp [hc', hk'])).elim
    rw [hstep]
    constructor
    · rintro ((h | ⟨rfl, h⟩) | ⟨h1, h⟩)
      · exact .inl h
      · exact .inr ⟨.inl rfl, h⟩
      · exact .inr ⟨.inr h1, h⟩
    · rintro (h | ⟨rfl | h1, h⟩)
      · exact .inl (.inl h)
      · exact .inl (.inr ⟨rfl, h⟩)
      · exact .inr ⟨h1, h⟩

/-- **`recMapOf`**: under a name, the recursors of the order whose block lists it. -/
theorem recMapOf_mem (mg : Merged) (k r : Name) :
    r ∈ ((recMapOf mg)[k]?).getD #[] ↔
      r ∈ mg.order ∧ ∃ c all, mg.map[r]? = some c ∧ IsRec c all ∧ k ∈ all := by
  unfold recMapOf
  rw [← Array.foldl_toList, recMapOf_go]
  simp

/-! ## Visited means declared -/

/-- What a stack item will declare when it runs. -/
@[expose] def Will (n : Name) : Work → Prop
  | .visit _ => False
  | .one c => c.name = n ∧ c.kind.tag < 5
  | .quot cs => ∃ c ∈ cs, c.name = n ∧ c.kind.tag < 5
  | .block ts cs rs => (∃ c ∈ ts, c.name = n ∧ c.kind.tag = 5) ∨ (∃ c ∈ cs, c.name = n ∧ c.kind.tag = 6) ∨
      ∃ c ∈ rs, c.name = n ∧ c.kind.tag = 7

/-- Declared, or will be. -/
@[expose] def Done (st : Emit) (stack : List Work) (n : Name) : Prop :=
  Has st n ∨ ∃ w ∈ stack, Will n w

/-- `n` is a constructor or recursor of the inductive type `m`, which is not filtered out. -/
@[expose] def BlockPart (mg : Merged) (n m : Name) : Prop :=
  ∃ cm all cs c, mg.map[m]? = some cm ∧ IsInd cm all cs ∧ cm.skipped = false ∧ mg.map[n]? = some c ∧
    (IsCtor c m ∨ IsRec c all)

/-- **The walk's invariant**: a visited constant is declared, will be by the stack, or is part
of an inductive type that is visited or to be visited; and all parts of a visited type are
declared or will be. -/
structure CoverInv (mg : Merged) (st : Emit) (stack : List Work) : Prop where
  vis : ∀ n c, st.visited.contains n = true → mg.map[n]? = some c → c.skipped = false →
    Done st stack n ∨ ∃ m, BlockPart mg n m ∧ (st.visited.contains m = true ∨ Work.visit m ∈ stack)
  parts : ∀ m, st.visited.contains m = true → ∀ n, BlockPart mg n m → Done st stack n

theorem Done.mono {st st' : Emit} {stack stack' : List Work} {n : Name} (hS : Emit.Sub st st')
    (hs : ∀ w ∈ stack, w ∈ stack') (h : Done st stack n) : Done st' stack' n := by
  rcases h with h | ⟨w, hw, h⟩
  · exact .inl (h.mono hS)
  · exact .inr ⟨w, hs w hw, h⟩

/-- A stack item that is no `visit` ran. -/
theorem CoverInv.pop {mg : Merged} {st st' : Emit} {w : Work} {rest : List Work}
    (hi : CoverInv mg st (w :: rest)) (hS : Emit.Sub st st') (hv : st'.visited = st.visited)
    (hw : ∀ n, Will n w → Has st' n) (hnv : ∀ m, w ≠ Work.visit m) : CoverInv mg st' rest := by
  have done : ∀ {n}, Done st (w :: rest) n → Done st' rest n := by
    rintro n (h | ⟨w', hm, h⟩)
    · exact .inl (h.mono hS)
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact .inl (hw n h)
      · exact .inr ⟨w', hm, h⟩
  refine ⟨fun n c hn hc hs => ?_, fun m hm n hp => ?_⟩
  · rw [hv] at hn
    rcases hi.vis n c hn hc hs with h | ⟨m, hp, h⟩
    · exact .inl (done h)
    · refine .inr ⟨m, hp, ?_⟩
      rcases h with h | h
      · exact .inl (hv ▸ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact absurd rfl (hnv m)
        · exact .inr h
  · rw [hv] at hm
    exact done (hi.parts m hm n hp)

/-- A `visit` that had nothing to do: of a type already visited, or of no type. -/
theorem CoverInv.skip {mg : Merged} {st : Emit} {n : Name} {rest : List Work}
    (hi : CoverInv mg st (Work.visit n :: rest))
    (hn : st.visited.contains n = true ∨ ∀ x, ¬ BlockPart mg x n) : CoverInv mg st rest := by
  have done : ∀ {k}, Done st (Work.visit n :: rest) k → Done st rest k := by
    rintro k (h | ⟨w', hm, h⟩)
    · exact .inl h
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact h.elim
      · exact .inr ⟨w', hm, h⟩
  refine ⟨fun k c hk hc hs => ?_, fun m hm k hp => done (hi.parts m hm k hp)⟩
  rcases hi.vis k c hk hc hs with h | ⟨m, hp, h⟩
  · exact .inl (done h)
  · refine .inr ⟨m, hp, ?_⟩
    rcases h with h | h
    · exact .inl h
    · rcases List.mem_cons.mp h with he | h
      · cases he
        rcases hn with hn | hn
        · exact .inl hn
        · exact (hn _ hp).elim
      · exact .inr h

/-- A `visit` that marked and went on with what the stack has become. -/
theorem CoverInv.step {mg : Merged} {st st' : Emit} {n : Name} {rest stack' : List Work}
    (hi : CoverInv mg st (Work.visit n :: rest)) (hS : Emit.Sub st st')
    (hrest : ∀ w ∈ rest, w ∈ stack')
    (hmono : ∀ k, st.visited.contains k = true → st'.visited.contains k = true)
    (hn : st'.visited.contains n = true)
    (hnew : ∀ k c, st'.visited.contains k = true → st.visited.contains k = false →
      mg.map[k]? = some c → c.skipped = false →
      Done st' stack' k ∨ ∃ m, BlockPart mg k m ∧ (st'.visited.contains m = true ∨ Work.visit m ∈ stack'))
    (hparts : ∀ m, st'.visited.contains m = true → st.visited.contains m = false →
      ∀ x, BlockPart mg x m → Done st' stack' x) : CoverInv mg st' stack' := by
  have done : ∀ {k}, Done st (Work.visit n :: rest) k → Done st' stack' k := by
    rintro k (h | ⟨w', hm, h⟩)
    · exact .inl (h.mono hS)
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact h.elim
      · exact .inr ⟨w', hrest _ hm, h⟩
  refine ⟨fun k c hk hc hs => ?_, fun m hm k hp => ?_⟩
  · cases hb : st.visited.contains k with
    | false => exact hnew k c hk hb hc hs
    | true =>
      rcases hi.vis k c hb hc hs with h | ⟨m, hp, h⟩
      · exact .inl (done h)
      · refine .inr ⟨m, hp, ?_⟩
        rcases h with h | h
        · exact .inl (hmono _ h)
        · rcases List.mem_cons.mp h with he | h
          · cases he
            exact .inl hn
          · exact .inr (hrest _ h)
  · cases hb : st.visited.contains m with
    | false => exact hparts m hm hb k hp
    | true => exact done (hi.parts m hb k hp)

/-- Marked after some constants: marked before, or one of them. -/
theorem Emit.marks_mem (cs : List CEntry) : ∀ (st : Emit) (k : Name),
    (cs.foldl (fun st x => st.mark x.name) st).visited.contains k = true →
      st.visited.contains k = true ∨ ∃ c ∈ cs, c.name = k := by
  induction cs with
  | nil => intro st k h; exact .inl h
  | cons c cs ih =>
    intro st k h
    rcases ih _ k h with h | ⟨d, hd, h⟩
    · rw [Emit.mark_contains] at h
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with rfl | h
      · exact .inr ⟨c, List.mem_cons_self, rfl⟩
      · exact .inl h
    · exact .inr ⟨d, List.mem_cons_of_mem _ hd, h⟩

/-- Every marked constant of the list is marked. -/
theorem Emit.marks_self (cs : List CEntry) : ∀ (st : Emit), ∀ c ∈ cs,
    (cs.foldl (fun st x => st.mark x.name) st).visited.contains c.name = true := by
  induction cs with
  | nil => intro st c hc; simp at hc
  | cons d cs ih =>
    intro st c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact (Emit.marks_spec cs _).2.2 _ (Emit.mark_self _ _)
    · exact ih _ c hc

theorem Emit.ones_sub (cs : List CEntry) : ∀ st : Emit, Emit.Sub st (cs.foldl Emit.one st) := by
  induction cs with
  | nil => intro st; exact Emit.Sub.refl _
  | cons c cs ih => intro st; exact (Emit.one_spec st c).1.trans (ih _)

theorem Emit.ones_has (cs : List CEntry) : ∀ st : Emit, ∀ c ∈ cs, c.kind.tag < 5 →
    Has (cs.foldl Emit.one st) c.name := by
  induction cs with
  | nil => intro st c hc; simp at hc
  | cons d cs ih =>
    intro st c hc ht
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ((Emit.one_spec st c).2.2.2 ht).mono (Emit.ones_sub cs _)
    · exact ih _ c hc ht

/-- **Visited means declared**: where the stored constants' blocks agree, a constant the walk
visited and that is not filtered out is declared by a record. -/
theorem emitLoop_covers (mg : Merged) (hG : BlocksGood mg)
    (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n)
    (hO : ∀ n, n ∈ mg.order ↔ mg.map.contains n = true) (stack : List Work) (st : Emit) :
    CoverInv mg st stack → ∀ n c, (emitLoop mg (recMapOf mg) stack st).visited.contains n = true →
      mg.map[n]? = some c → c.skipped = false → Has (emitLoop mg (recMapOf mg) stack st) n := by
  have notPart : ∀ {x m c}, mg.map[m]? = some c → c.kind.tag ≠ 5 → ¬ BlockPart mg x m := by
    rintro x m c hc ht ⟨cm, all, cs, _, h1, ⟨_, _, _, _, _, _, h2⟩, -⟩
    rw [hc] at h1
    cases h1
    simp [h2, CKindF.tag] at ht
  have noPartNone : ∀ {x m}, mg.map[m]? = none → ¬ BlockPart mg x m := by
    rintro x m hc ⟨cm, all, cs, _, h1, -⟩
    rw [hc] at h1
    cases h1
  have noPartSkip : ∀ {x m c}, mg.map[m]? = some c → c.skipped = true → ¬ BlockPart mg x m := by
    rintro x m c hc hs ⟨cm, all, cs, _, h1, -, h3, -⟩
    rw [hc] at h1
    cases h1
    rw [hs] at h3
    cases h3
  -- a visit of a constant that is no inductive type and no block part: its record is pending
  have plain : ∀ {s0 : Emit} {n : Name} {c : CEntry} {rest extra : List Work},
      mg.map[n]? = some c → c.kind.tag < 5 → s0.visited.contains n = false →
      CoverInv mg s0 (Work.visit n :: rest) →
      CoverInv mg (s0.mark n) (extra ++ Work.one c :: rest) := by
    intro s0 n c rest extra hc ht hv hi
    obtain ⟨m1, -, m3, m4⟩ := Emit.mark_spec s0 n
    have hnew : ∀ k, (s0.mark n).visited.contains k = true → s0.visited.contains k = false → k = n := by
      intro k hk hb
      rw [Emit.mark_contains, hb] at hk
      exact (by simpa using hk : n = k).symm
    refine hi.step m1 (fun w hw => List.mem_append_right _ (List.mem_cons_of_mem _ hw)) m3 m4 ?_ ?_
    · intro k _ hk hb _ _
      obtain rfl := hnew k hk hb
      exact .inl (.inr ⟨_, List.mem_append_right _ List.mem_cons_self, hN _ _ hc, ht⟩)
    · intro k hk hb x
      obtain rfl := hnew k hk hb
      exact notPart hc (by omega) |>.elim
  fun_induction emitLoop mg (recMapOf mg) stack st
  all_goals intro hi k d hk hd hs
  case case1 st =>
    rcases hi.vis k d hk hd hs with h | ⟨m, hp, h⟩
    · rcases h with h | ⟨w, hw, -⟩
      · exact h
      · cases hw
    · rcases h with h | h
      · rcases hi.parts m h k hp with h | ⟨w, hw, -⟩
        · exact h
        · cases hw
      · cases h
  case case2 st c rest ih =>
    obtain ⟨h1, h2, -, h4⟩ := Emit.one_spec st c
    refine ih (hi.pop h1 h2 ?_ (by simp)) k d hk hd hs
    rintro n ⟨rfl, ht⟩
    exact h4 ht
  case case3 st cs rest ih =>
    have hv : (st.ones cs).visited = st.visited := Emit.foldl_one_visited' cs st
    refine ih (hi.pop (Emit.ones_sub cs st) hv ?_ (by simp)) k d hk hd hs
    rintro n ⟨c, hc, rfl, ht⟩
    exact Emit.ones_has cs st c hc ht
  case case4 st ts cs rs rest ih =>
    obtain ⟨b1, b2, b3⟩ := Emit.block_has st ts cs rs
    have hb := Emit.block_sub st ts cs rs
    refine ih (hi.pop hb (Emit.block_visited _ _ _ _) ?_ (by simp)) k d hk hd hs
    rintro n (⟨c, hc, rfl, ht⟩ | ⟨c, hc, rfl, ht⟩ | ⟨c, hc, rfl, ht⟩)
    · exact b1 c hc ht
    · exact b2 c hc ht
    · exact b3 c hc ht
  case case5 st n rest hv ih =>
    exact ih (hi.skip (.inl hv)) k d hk hd hs
  case case6 st n rest hv hc ih =>
    exact ih (hi.skip (.inr fun x => noPartNone hc)) k d hk hd hs
  case case7 st n rest hv c hc hsk ih =>
    exact ih (hi.skip (.inr fun x => noPartSkip hc hsk)) k d hk hd hs
  case case8 s0 n rest hv c hc hsk s1 _ hkind ih =>
    exact ih (plain hc (by simp [hkind, CKindF.tag]) (by simpa using hv) hi) k d hk hd hs
  case case9 s0 n rest hv c hc hsk s1 _ _ _ hkind ih =>
    exact ih (plain hc (by simp [hkind, CKindF.tag]) (by simpa using hv) hi) k d hk hd hs
  case case10 s0 n rest hv c hc hsk s1 _ _ hkind ih =>
    exact ih (plain hc (by simp [hkind, CKindF.tag]) (by simpa using hv) hi) k d hk hd hs
  case case11 s0 n rest hv c hc hsk s1 _ _ hkind ih =>
    exact ih (plain hc (by simp [hkind, CKindF.tag]) (by simpa using hv) hi) k d hk hd hs
  case case12 s0 n rest hv c hc hsk s1 q hkind qs s2 ih =>
    obtain ⟨hqc, hqk⟩ := hG.quot hc hkind
    obtain ⟨m1, -, m3, -⟩ := Emit.mark_spec s0 n
    obtain ⟨q1, -, q3⟩ := Emit.marks_spec qs s1
    have hn0 : s2.visited.contains n = true := by
      have := Emit.marks_self qs s1 c hqc
      rwa [hN _ _ hc] at this
    have hnew : ∀ x, s2.visited.contains x = true → s0.visited.contains x = false →
        ∃ q ∈ qs, q.name = x := by
      intro x hx hb
      rcases Emit.marks_mem qs s1 x hx with h | h
      · rw [Emit.mark_contains, hb] at h
        have : n = x := by simpa using h
        subst this
        exact ⟨c, hqc, hN _ _ hc⟩
      · exact h
    refine ih (hi.step (m1.trans q1) (fun w hw => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      (fun x hx => q3 x (m3 x hx)) hn0 ?_ ?_) k d hk hd hs
    · intro x _ hx hb _ _
      obtain ⟨y, hy, rfl⟩ := hnew x hx hb
      refine .inl (.inr ⟨Work.quot qs, List.mem_cons_of_mem _ List.mem_cons_self, y, hy, rfl, ?_⟩)
      rw [hqk y hy]
      decide
    · intro x hx hb z
      obtain ⟨y, hy, rfl⟩ := hnew x hx hb
      obtain ⟨w, -, hw⟩ := List.mem_filterMap.mp hy
      have hyy : mg.map[y.name]? = some y := by
        have := hN _ _ hw
        subst this
        exact hw
      exact (notPart hyy (by rw [hqk y hy]; decide)).elim
  case case13 s0 n rest hv c hc hsk s1 ind _ _ _ _ hkind ih =>
    obtain ⟨m1, -, m3, m4⟩ := Emit.mark_spec s0 n
    have hnew : ∀ x, (s0.mark n).visited.contains x = true → s0.visited.contains x = false → x = n := by
      intro x hx hb
      rw [Emit.mark_contains, hb] at hx
      exact (by simpa using hx : n = x).symm
    refine ih (hi.step m1 (fun w hw => List.mem_cons_of_mem _ hw) m3 m4 ?_ ?_) k d hk hd hs
    · intro x y hx hb hy hsy
      obtain rfl := hnew x hx hb
      rw [hc] at hy
      cases hy
      have hC : IsCtor c ind := ⟨_, _, _, _, hkind⟩
      obtain ⟨t, all, cs, ht, hI, hmem⟩ := hG.ctor hc hC
      obtain ⟨-, -, h3⟩ := hG.ind ht hI
      obtain ⟨c', hc', -, hsk'⟩ := h3 x hmem
      rw [hc] at hc'
      cases hc'
      exact .inr ⟨ind, ⟨t, all, cs, c, ht, hI, by rw [← hsk', hsy], hc, .inl hC⟩,
        .inr List.mem_cons_self⟩
    · intro x hx hb z
      obtain rfl := hnew x hx hb
      exact (notPart hc (by simp [hkind, CKindF.tag])).elim
  case case14 s0 n rest hv c hc hsk s1 all _ _ _ _ _ _ _ hkind ih =>
    obtain ⟨m1, -, m3, m4⟩ := Emit.mark_spec s0 n
    have hnew : ∀ x, (s0.mark n).visited.contains x = true → s0.visited.contains x = false → x = n := by
      intro x hx hb
      rw [Emit.mark_contains, hb] at hx
      exact (by simpa using hx : n = x).symm
    refine ih (hi.step m1 (fun w hw => List.mem_append_right _ hw) m3 m4 ?_ ?_) k d hk hd hs
    · intro x y hx hb hy hsy
      obtain rfl := hnew x hx hb
      rw [hc] at hy
      cases hy
      have hR : IsRec c all := ⟨_, _, _, _, _, _, _, hkind⟩
      obtain ⟨t, tl, m, cs, rfl, ht, hI, hsk'⟩ := hG.recur hc hR
      refine .inr ⟨t, ⟨m, _, cs, c, ht, hI, by rw [hsk', hsy], hc, .inr hR⟩, .inr ?_⟩
      exact List.mem_append_left _ (List.mem_map.mpr ⟨t, List.mem_cons_self, rfl⟩)
    · intro x hx hb z
      obtain rfl := hnew x hx hb
      exact (notPart hc (by simp [hkind, CKindF.tag])).elim
  case case15 s0 n rest hv c hc hsk s1 _ _ all cs _ _ _ _ hkind tys cts recs s2 ih =>
    have hI : IsInd c all cs := ⟨_, _, _, _, _, _, hkind⟩
    obtain ⟨hself, hmem, hctors⟩ := hG.ind hc hI
    obtain ⟨m1, -, m3, -⟩ := Emit.mark_spec s0 n
    obtain ⟨q1, -, q3⟩ := Emit.marks_spec (tys ++ cts ++ recs) s1
    -- the block's parts, by kind
    have hT : ∀ x ∈ tys, ∃ y cs', y ∈ all ∧ x.name = y ∧ mg.map[y]? = some x ∧ IsInd x all cs' := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := List.mem_filterMap.mp hx
      obtain ⟨m, cs', hm, hI', -⟩ := hmem y hy
      rw [hm] at hxy
      cases hxy
      exact ⟨y, cs', hy, hN _ _ hm, hm, hI'⟩
    have hC : ∀ x ∈ cts, x.kind.tag = 6 := by
      intro x hx
      obtain ⟨t, ht, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨y, cs', hy, -, hm, hI'⟩ := hT t ht
      obtain ⟨_, _, _, _, _, _, hk'⟩ := hI'
      simp only [hk'] at hx
      obtain ⟨z, hz, hxz⟩ := List.mem_filterMap.mp hx
      obtain ⟨-, -, h3⟩ := hG.ind hm ⟨_, _, _, _, _, _, hk'⟩
      obtain ⟨m', hm', ⟨_, _, _, _, hk''⟩, -⟩ := h3 z hz
      rw [hm'] at hxz
      cases hxz
      simp [hk'', CKindF.tag]
    have hR : ∀ x ∈ recs, x.kind.tag = 7 := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := List.mem_filterMap.mp hx
      obtain ⟨-, c', all', hc', ⟨_, _, _, _, _, _, _, hk'⟩, -⟩ := (recMapOf_mem mg n y).mp (by simpa using hy)
      rw [hc'] at hxy
      cases hxy
      simp [hk', CKindF.tag]
    have hc0 : c ∈ tys := List.mem_filterMap.mpr ⟨n, hself, hc⟩
    have hnew : ∀ x, s2.visited.contains x = true → s0.visited.contains x = false →
        ∃ y ∈ tys ++ cts ++ recs, y.name = x := by
      intro x hx hb
      rcases Emit.marks_mem _ s1 x hx with h | h
      · rw [Emit.mark_contains, hb] at h
        have : n = x := by simpa using h
        subst this
        exact ⟨c, by simp [hc0], hN _ _ hc⟩
      · exact h
    have hblock : ∀ y ∈ tys ++ cts ++ recs, Will y.name (Work.block tys cts recs) := by
      intro y hy
      simp only [List.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · obtain ⟨_, _, -, -, -, _, _, _, _, _, _, hk'⟩ := hT y hy
        exact .inl ⟨y, hy, rfl, by simp [hk', CKindF.tag]⟩
      · exact .inr (.inl ⟨y, hy, rfl, hC y hy⟩)
      · exact .inr (.inr ⟨y, hy, rfl, hR y hy⟩)
    have hmemB : Work.block tys cts recs ∈ Work.usesOf (tys ++ cts ++ recs) ++ Work.block tys cts recs :: rest :=
      List.mem_append_right _ List.mem_cons_self
    have hn0 : s2.visited.contains n = true := by
      have := Emit.marks_self _ s1 c (by simp [hc0] : c ∈ tys ++ cts ++ recs)
      rwa [hN _ _ hc] at this
    refine ih (hi.step (m1.trans q1)
      (fun w hw => List.mem_append_right _ (List.mem_cons_of_mem _ hw))
      (fun x hx => q3 x (m3 x hx)) hn0 ?_ ?_) k d hk hd hs
    · intro x _ hx hb _ _
      obtain ⟨y, hy, rfl⟩ := hnew x hx hb
      exact .inl (.inr ⟨_, hmemB, hblock y hy⟩)
    · rintro m hx hb z ⟨cm, all', cs', cz, hcm, hIm, -, hcz, hzk⟩
      obtain ⟨y, hy, rfl⟩ := hnew m hx hb
      -- the type `m` is a member of the block
      have hyT : y ∈ tys := by
        obtain ⟨_, _, _, _, _, _, hkm⟩ := hIm
        simp only [List.mem_append] at hy
        rcases hy with (hy | hy) | hy
        · exact hy
        · have htag := hC y hy
          obtain ⟨t, ht, hx⟩ := List.mem_flatMap.mp hy
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hk'⟩ := hT t ht
          simp only [hk'] at hx
          obtain ⟨z', -, hxz⟩ := List.mem_filterMap.mp hx
          obtain rfl := hN _ _ hxz
          rw [hxz] at hcm
          cases hcm
          simp [hkm, CKindF.tag] at htag
        · have htag := hR y hy
          obtain ⟨y', -, hxy⟩ := List.mem_filterMap.mp hy
          obtain rfl := hN _ _ hxy
          rw [hxy] at hcm
          cases hcm
          simp [hkm, CKindF.tag] at htag
      obtain ⟨u, csu, hu, hyu, hmu, hIu⟩ := hT y hyT
      subst hyu
      have hyc : y = cm := Option.some.inj (hmu.symm.trans hcm)
      subst hyc
      obtain ⟨rfl, rfl⟩ := IsInd.unique hIu hIm
      rcases hzk with hzc | hzr
      · -- a constructor of `m`: it is listed by `m`
        obtain ⟨t, all2, cs2, ht, hI2, hl⟩ := hG.ctor hcz hzc
        have hyt : y = t := Option.some.inj (hmu.symm.trans ht)
        subst hyt
        obtain ⟨-, rfl⟩ := IsInd.unique hIu hI2
        obtain ⟨_, _, _, _, _, _, hk1⟩ := hIu
        have hzcts : cz ∈ cts := List.mem_flatMap.mpr ⟨y, hyT, by
          simp only [hk1]
          exact List.mem_filterMap.mpr ⟨z, hl, hcz⟩⟩
        have hzn := hN _ _ hcz
        exact .inr ⟨_, hmemB, hzn ▸ hblock cz (by simp [hzcts])⟩
      · -- a recursor of the block: found under `n`, a member
        have hzo : z ∈ mg.order := (hO z).2 (contains_of_getElem hcz)
        have hzm : z ∈ ((recMapOf mg)[n]?).getD #[] :=
          (recMapOf_mem mg n z).mpr ⟨hzo, cz, all, hcz, hzr, hself⟩
        have hzrecs : cz ∈ recs := List.mem_filterMap.mpr ⟨z, by simpa using hzm, hcz⟩
        have hzn := hN _ _ hcz
        exact .inr ⟨_, hmemB, hzn ▸ hblock cz (by simp [hzrecs])⟩

/-- **The walk from its roots**: a constant it visited and that is not filtered out is
declared by a record. -/
theorem emitAll_covers {mg : Merged} (hG : BlocksGood mg)
    (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n)
    (hO : ∀ n, n ∈ mg.order ↔ mg.map.contains n = true) (rs : Array Name) {n : Name} {c : CEntry}
    (hv : (emitAll mg rs).visited.contains n = true) (hc : mg.map[n]? = some c)
    (hs : c.skipped = false) : Has (emitAll mg rs) n := by
  refine emitLoop_covers mg hG hN hO _ {} ⟨?_, ?_⟩ n c hv hc hs
  · intro k _ hk
    simp at hk
  · intro k hk
    simp at hk

/-! ## The declarations -/

theorem declsGo_spec {em : Emit} : ∀ (rs : List DeclRec) (k : Nat) (acc ds : Array Declaration),
    declsGo em k rs acc = .ok ds →
    (∀ d ∈ acc, d ∈ ds) ∧ (∀ r ∈ rs, ∃ d, declOfF em.nm em.lv em.ex r = .ok (.inl d) ∧ d ∈ ds) ∧
      ∀ d ∈ ds, d ∈ acc ∨ ∃ r ∈ rs, declOfF em.nm em.lv em.ex r = .ok (.inl d)
  | [], _, acc, ds, h => by
    simp only [declsGo, Except.ok.injEq] at h
    subst h
    exact ⟨fun _ h => h, by simp, fun _ h => .inl h⟩
  | r :: rs, k, acc, ds, h => by
    simp only [declsGo] at h
    split at h
    · rename_i d hd
      obtain ⟨h1, h2, h3⟩ := declsGo_spec rs (k + 1) (acc.push d) ds h
      refine ⟨fun x hx => h1 x (Array.mem_push.mpr (.inl hx)), fun x hx => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨d, hd, h1 d (Array.mem_push.mpr (.inr rfl))⟩
        · exact h2 x hx
      · rcases h3 x hx with h4 | ⟨y, hy, h4⟩
        · rcases Array.mem_push.mp h4 with h5 | rfl
          · exact .inl h5
          · exact .inr ⟨r, List.mem_cons_self, hd⟩
        · exact .inr ⟨y, List.mem_cons_of_mem _ hy, h4⟩
    · cases h
    · cases h

theorem declsOf_spec {em : Emit} {ds : Array Declaration} (h : declsOf em = .ok ds) :
    (∀ r ∈ em.out, ∃ d, declOfF em.nm em.lv em.ex r = .ok (.inl d) ∧ d ∈ ds) ∧
      ∀ d ∈ ds, ∃ r ∈ em.out, declOfF em.nm em.lv em.ex r = .ok (.inl d) := by
  obtain ⟨-, h2, h3⟩ := declsGo_spec em.out.toList 0 #[] ds h
  refine ⟨fun r hr => h2 r (by simpa using hr), fun d hd => ?_⟩
  rcases h3 d hd with h4 | ⟨r, hr, h4⟩
  · simp at h4
  · exact ⟨r, by simpa using hr, h4⟩

theorem mapM_nm {em : Emit} : ∀ {l : List Nat} {ns : List Name},
    l.map (em.names[·]?) = ns.map some → l.mapM em.nm = .ok ns
  | [], ns, h => by
    cases ns with
    | nil => rfl
    | cons _ _ => simp at h
  | i :: l, ns, h => by
    cases ns with
    | nil => simp at h
    | cons n ns =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hi : em.nm i = .ok n := by simp [Emit.nm, h.1, pure, Except.pure]
      simp [List.mapM_cons, hi, mapM_nm h.2, bind, Except.bind, pure, Except.pure]

/-- A record's statement read back. -/
theorem cvOfF_of {em : Emit} {cv : CVRec} {c : CEntry} (h : CvOf em cv c) :
    cvOfF em.nm em.lv em.ex cv = .ok ⟨c.name, c.levelParams, c.type⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  have hn : em.nm cv.name = .ok c.name := by simp [Emit.nm, h1, pure, Except.pure]
  have ht : em.ex cv.type = .ok c.type := by simp [Emit.ex, h3, pure, Except.pure]
  simp [cvOfF, hn, ht, mapM_nm h2, bind, Except.bind, pure, Except.pure]

/-- **A declared name's record is its own constant's.** -/
theorem rec_of_declares {mg : Merged} {em : Emit} {n : Name} {c : CEntry} {r : DeclRec}
    (hc : mg.map[n]? = some c) (hf : RecFrom mg em r) (hd : Declares em n r) :
    match r with
    | .ind .. => c.kind.tag = 5 ∨ c.kind.tag = 6 ∨ c.kind.tag = 7
    | r => RecOf em c r := by
  have same : ∀ {c' : CEntry} {i : Nat}, Stored mg c' → em.names[i]? = some c'.name →
      em.names[i]? = some n → c' = c := by
    intro c' i h1 h2 h3
    rw [h2] at h3
    have : c'.name = n := Option.some.inj h3
    unfold Stored at h1
    rw [this, hc] at h1
    exact (Option.some.inj h1).symm
  cases r with
  | ax cv u =>
    obtain ⟨c', h1, h2⟩ := hf
    obtain rfl := same h1 h2.1.1 hd
    exact h2
  | defn cv i h s =>
    obtain ⟨c', h1, h2⟩ := hf
    obtain rfl := same h1 h2.1.1 hd
    exact h2
  | thm cv i =>
    obtain ⟨c', h1, h2⟩ := hf
    obtain rfl := same h1 h2.1.1 hd
    exact h2
  | opaq cv i u =>
    obtain ⟨c', h1, h2⟩ := hf
    obtain rfl := same h1 h2.1.1 hd
    exact h2
  | quot cv k =>
    obtain ⟨c', h1, h2⟩ := hf
    obtain rfl := same h1 h2.1.1 hd
    exact h2
  | ind ts cs rs =>
    obtain ⟨f1, f2, f3⟩ := hf
    rcases hd with ⟨t, ht, hd⟩ | ⟨t, ht, hd⟩ | ⟨t, ht, hd⟩
    · obtain ⟨c', h1, h2, h3⟩ := f1 t ht
      obtain rfl := same h1 h2.1 hd
      exact .inl h3
    · obtain ⟨c', h1, h2, h3⟩ := f2 t ht
      obtain rfl := same h1 h2.1 hd
      exact .inr (.inl h3)
    · obtain ⟨c', h1, h2, h3⟩ := f3 t ht
      obtain rfl := same h1 h2.1 hd
      exact .inr (.inr h3)

/-- **A theorem of the closure is checked**: a theorem constant the merge holds, among the
roots, has its theorem record among the declarations, with its own statement and proof. -/
theorem declsOf_thm {mg : Merged} {rs : Array Name} {ds : Array Declaration} {n : Name} {c : CEntry}
    {v : Expr} {all : List Name} (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n)
    (hO : ∀ n, n ∈ mg.order ↔ mg.map.contains n = true)
    (hd : declsOf (emitAll mg rs) = .ok ds) (hb : blocksOk mg = .ok ())
    (hrs : n ∈ rs) (hc : mg.map[n]? = some c) (hk : c.kind = .thm v all) :
    Declaration.thmDecl ⟨c.name, c.levelParams, c.type⟩ v ∈ ds := by
  obtain ⟨h1, h2⟩ := emitAll_spec hN rs
  have hsk : c.skipped = false := by simp [CEntry.skipped, hk, CKindF.skipped]
  obtain ⟨r, hr, hdc⟩ := emitAll_covers (blocksOk_good hb hO) hN hO rs (h2 n hrs c hc hsk) hc hsk
  have hR := rec_of_declares hc (h1 r hr) hdc
  obtain ⟨d, hd1, hd2⟩ := (declsOf_spec hd).1 r hr
  cases r with
  | ax cv u => obtain ⟨-, h⟩ := hR; rw [hk] at h; cases h
  | defn cv i h s => obtain ⟨-, _, -, h⟩ := hR; rw [hk] at h; cases h
  | opaq cv i u => obtain ⟨-, _, -, h⟩ := hR; rw [hk] at h; cases h
  | quot cv q => obtain ⟨-, h⟩ := hR; rw [hk] at h; cases h
  | ind ts cs rs' =>
    simp only [hk, CKindF.tag] at hR
    omega
  | thm cv i =>
    obtain ⟨h3, v', all', h4, h5⟩ := hR
    rw [hk] at h5
    cases h5
    have hex : (emitAll mg rs).ex i = .ok v := by simp [Emit.ex, h4, pure, Except.pure]
    simp only [declOfF, cvOfF_of h3, hex, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Sum.inl.injEq] at hd1
    subst hd1
    exact hd2

/-- The declaration a constant that is no part of an inductive block stands for. -/
@[expose] def entryDecl (c : CEntry) : Option Declaration :=
  let cv : ConstantVal := ⟨c.name, c.levelParams, c.type⟩
  match c.kind with
  | .ax _ => some (.axiomDecl cv)
  | .defn v h "safe" => some (.defnDecl cv v (match h with
      | .«abbrev» => .«abbrev»
      | .«opaque» => .«opaque»
      | .regular n => .regular n))
  | .thm v _ => some (.thmDecl cv v)
  | .opaq v _ => some (.opaqueDecl cv v)
  | .quot "type" => some (.quotDecl .type cv)
  | .quot "ctor" => some (.quotDecl .ctor cv)
  | .quot "lift" => some (.quotDecl .lift cv)
  | .quot "ind" => some (.quotDecl .ind cv)
  | _ => none

/-- **Nothing is added**: every declaration is the one a stored constant stands for, or an
inductive block's whose every member, constructor and recursor is a stored constant of that
kind, by the record's own statement. -/
theorem declsOf_from {mg : Merged} {rs : Array Name} {ds : Array Declaration}
    (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n)
    (hd : declsOf (emitAll mg rs) = .ok ds) {d : Declaration} (hm : d ∈ ds) :
    (∃ c, Stored mg c ∧ entryDecl c = some d) ∨
      ∃ ts cts rcs, RecFrom mg (emitAll mg rs) (.ind ts cts rcs) ∧
        declOfF (emitAll mg rs).nm (emitAll mg rs).lv (emitAll mg rs).ex (.ind ts cts rcs) = .ok (.inl d) := by
  obtain ⟨h1, -⟩ := emitAll_spec hN rs
  obtain ⟨r, hr, hd1⟩ := (declsOf_spec hd).2 d hm
  have hf := h1 r hr
  cases r with
  | ind ts cts rcs => exact .inr ⟨ts, cts, rcs, hf, hd1⟩
  | ax cv u =>
    obtain ⟨c, hs, h3, h4⟩ := hf
    refine .inl ⟨c, hs, ?_⟩
    simp only [declOfF, cvOfF_of h3, bind, Except.bind] at hd1
    cases u with
    | true => simp [pure, Except.pure] at hd1
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at hd1
      subst hd1
      simp [entryDecl, h4]
  | defn cv i h s =>
    obtain ⟨c, hs, h3, v, h4, h5⟩ := hf
    refine .inl ⟨c, hs, ?_⟩
    have hex : (emitAll mg rs).ex i = .ok v := by simp [Emit.ex, h4, pure, Except.pure]
    simp only [declOfF, cvOfF_of h3, bind, Except.bind] at hd1
    by_cases hsafe : s = "safe"
    · subst hsafe
      simp only [hex, pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at hd1
      subst hd1
      simp only [entryDecl, h5]
      cases h <;> rfl
    · split at hd1
      · exact absurd rfl hsafe
      · simp [pure, Except.pure] at hd1
  | thm cv i =>
    obtain ⟨c, hs, h3, v, all, h4, h5⟩ := hf
    refine .inl ⟨c, hs, ?_⟩
    have hex : (emitAll mg rs).ex i = .ok v := by simp [Emit.ex, h4, pure, Except.pure]
    simp only [declOfF, cvOfF_of h3, hex, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Sum.inl.injEq] at hd1
    subst hd1
    simp [entryDecl, h5]
  | opaq cv i u =>
    obtain ⟨c, hs, h3, v, h4, h5⟩ := hf
    refine .inl ⟨c, hs, ?_⟩
    have hex : (emitAll mg rs).ex i = .ok v := by simp [Emit.ex, h4, pure, Except.pure]
    simp only [declOfF, cvOfF_of h3, hex, bind, Except.bind] at hd1
    cases u with
    | true => simp [pure, Except.pure] at hd1
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at hd1
      subst hd1
      simp [entryDecl, h5]
  | quot cv q =>
    obtain ⟨c, hs, h3, h4⟩ := hf
    refine .inl ⟨c, hs, ?_⟩
    simp only [declOfF, cvOfF_of h3, bind, Except.bind] at hd1
    split at hd1
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at hd1
         subst hd1
         simp [entryDecl, h4])
      | (cases hd1; done)

end ConLeche.Frontend.Olean
