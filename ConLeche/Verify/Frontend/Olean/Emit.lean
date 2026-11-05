module

public import ConLeche.Frontend.Olean.Records
import Std.Data.HashSet.Lemmas

/-!
# The emission of a closure's merged constants

`Emit.Sub`: the walk only adds to its tables, and a record it pushed stays.

`emitLoop_spec`: every record comes from stored constants (`RecFrom`), each constant named by
a `visit` that is stored and not filtered out ends visited.

`coverageOk`, the emission's input check, then says a visited constant is declared by a
record, and that record is its own: `declsOf_thm` (a theorem constant's record is its
theorem), `declsOf_from` (every declaration comes from stored constants).
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

/-- **One constant's record.** -/
theorem Emit.one_spec (st : Emit) (c : CEntry) :
    Emit.Sub st (st.one c) ∧ (st.one c).visited = st.visited ∧
      ∀ r ∈ (st.one c).out, r ∈ st.out ∨ RecOf (st.one c) c r := by
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
  have pushed : ∀ (e : Emit) (d : DeclRec), Emit.Sub C.1 e → e.visited = st.visited →
      e.out = st.out → RecOf (e.push d) c d →
      Emit.Sub st (e.push d) ∧ (e.push d).visited = st.visited ∧
        ∀ r ∈ (e.push d).out, r ∈ st.out ∨ RecOf (e.push d) c r := by
    intro e d hs hv ho hr
    obtain ⟨p1, p2, p3⟩ := Emit.push_spec e d
    refine ⟨(h1.trans hs).trans p1, p2.trans hv, fun r hm => ?_⟩
    rw [p3, ho] at hm
    rcases Array.mem_push.mp hm with hm | rfl
    · exact .inl hm
    · exact .inr hr
  cases hk : c.kind with
  | ax u =>
    simp only
    obtain ⟨p1, -, -⟩ := Emit.push_spec C.1 (.ax C.2 u)
    exact pushed C.1 _ (Emit.Sub.refl _) h3 h4 ⟨h2.mono p1, hk⟩
  | defn v h s =>
    simp only
    obtain ⟨e1, e2, e3, e4⟩ := Emit.expr_spec C.1 v
    obtain ⟨p1, -, -⟩ := Emit.push_spec (C.1.expr v).1 (.defn C.2 (C.1.expr v).2 h s)
    exact pushed _ _ e1 (e3.trans h3) (e4.trans h4)
      ⟨(h2.mono e1).mono p1, v, p1.exprs _ _ e2, hk⟩
  | thm v all =>
    simp only
    obtain ⟨e1, e2, e3, e4⟩ := Emit.expr_spec C.1 v
    obtain ⟨p1, -, -⟩ := Emit.push_spec (C.1.expr v).1 (.thm C.2 (C.1.expr v).2)
    exact pushed _ _ e1 (e3.trans h3) (e4.trans h4)
      ⟨(h2.mono e1).mono p1, v, all, p1.exprs _ _ e2, hk⟩
  | opaq v u =>
    simp only
    obtain ⟨e1, e2, e3, e4⟩ := Emit.expr_spec C.1 v
    obtain ⟨p1, -, -⟩ := Emit.push_spec (C.1.expr v).1 (.opaq C.2 (C.1.expr v).2 u)
    exact pushed _ _ e1 (e3.trans h3) (e4.trans h4)
      ⟨(h2.mono e1).mono p1, v, p1.exprs _ _ e2, hk⟩
  | quot k =>
    simp only
    obtain ⟨p1, -, -⟩ := Emit.push_spec C.1 (.quot C.2 k)
    exact pushed C.1 _ (Emit.Sub.refl _) h3 h4 ⟨h2.mono p1, hk⟩
  | induct _ _ _ _ _ _ _ _ =>
    simp only
    exact ⟨h1, h3, fun r hm => .inl (h4 ▸ hm)⟩
  | ctor _ _ _ _ _ =>
    simp only
    exact ⟨h1, h3, fun r hm => .inl (h4 ▸ hm)⟩
  | recur _ _ _ _ _ _ _ _ =>
    simp only
    exact ⟨h1, h3, fun r hm => .inl (h4 ▸ hm)⟩

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
    obtain ⟨h1, h2, h3⟩ := Emit.one_spec st c
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
    obtain ⟨h1, h2, h3⟩ := Emit.one_spec st c
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
  generalize Array.foldl _ _ mg.order = recMap
  obtain ⟨-, -, h3, h4⟩ := emitLoop_spec mg recMap hN (rs.toList.map Work.visit) {}
    (fun w hw => by
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hw
      trivial)
    (fun r hr => by simp at hr)
  exact ⟨h3, fun n hn c hc hsk => h4 n (List.mem_map.mpr ⟨n, by simpa using hn, rfl⟩) c hc hsk⟩

/-! ## What a record declares -/

/-- A record declares a name. -/
@[expose] def Declares (em : Emit) (n : Name) : DeclRec → Prop
  | .ax cv _ | .defn cv .. | .thm cv _ | .opaq cv .. | .quot cv _ => em.names[cv.name]? = some n
  | .ind ts cs rs =>
    (∃ t ∈ ts, em.names[t.cv.name]? = some n) ∨ (∃ t ∈ cs, em.names[t.cv.name]? = some n) ∨
      ∃ t ∈ rs, em.names[t.cv.name]? = some n

theorem declared_nm {em : Emit} {cv : CVRec} {s : Std.HashSet Name} {n : Name}
    (h : (match em.names[cv.name]? with
      | some m => s.insert m
      | none => s).contains n = true) :
    s.contains n = true ∨ em.names[cv.name]? = some n := by
  split at h
  · rename_i m hm
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact .inr hm
    · exact .inl h
  · exact .inl h

theorem declared_list {α : Type} {em : Emit} (cvOf : α → CVRec) {n : Name} (l : List α) :
    ∀ s : Std.HashSet Name,
      (l.foldl (fun s t => match em.names[(cvOf t).name]? with
        | some m => s.insert m
        | none => s) s).contains n = true →
      s.contains n = true ∨ ∃ t ∈ l, em.names[(cvOf t).name]? = some n := by
  induction l with
  | nil => intro s h; exact .inl h
  | cons x l ih =>
    intro s h
    rcases ih _ h with h1 | ⟨t, ht, h1⟩
    · rcases declared_nm h1 with h2 | h2
      · exact .inl h2
      · exact .inr ⟨x, List.mem_cons_self, h2⟩
    · exact .inr ⟨t, List.mem_cons_of_mem _ ht, h1⟩

/-- **A declared name has its record.** -/
theorem declared_rec {em : Emit} {n : Name} (h : em.declared.contains n = true) :
    ∃ r ∈ em.out, Declares em n r := by
  unfold Emit.declared at h
  rw [← Array.foldl_toList] at h
  have key : ∀ (l : List DeclRec) (s : Std.HashSet Name),
      (l.foldl (fun s d => match d with
        | .ax cv _ | .defn cv .. | .thm cv _ | .opaq cv .. | .quot cv _ =>
          match em.names[cv.name]? with
          | some m => s.insert m
          | none => s
        | .ind ts cs rs =>
          let s := ts.foldl (fun s t => match em.names[t.cv.name]? with
            | some m => s.insert m
            | none => s) s
          let s := cs.foldl (fun s c => match em.names[c.cv.name]? with
            | some m => s.insert m
            | none => s) s
          rs.foldl (fun s r => match em.names[r.cv.name]? with
            | some m => s.insert m
            | none => s) s) s).contains n = true →
      s.contains n = true ∨ ∃ r ∈ l, Declares em n r := by
    intro l
    induction l with
    | nil => intro s h; exact .inl h
    | cons d l ih =>
      intro s h
      rcases ih _ h with h1 | ⟨r, hr, h1⟩
      · cases d with
        | ax cv _ =>
          rcases declared_nm h1 with h2 | h2
          · exact .inl h2
          · exact .inr ⟨_, List.mem_cons_self, h2⟩
        | defn cv _ _ _ =>
          rcases declared_nm h1 with h2 | h2
          · exact .inl h2
          · exact .inr ⟨_, List.mem_cons_self, h2⟩
        | thm cv _ =>
          rcases declared_nm h1 with h2 | h2
          · exact .inl h2
          · exact .inr ⟨_, List.mem_cons_self, h2⟩
        | opaq cv _ _ =>
          rcases declared_nm h1 with h2 | h2
          · exact .inl h2
          · exact .inr ⟨_, List.mem_cons_self, h2⟩
        | quot cv _ =>
          rcases declared_nm h1 with h2 | h2
          · exact .inl h2
          · exact .inr ⟨_, List.mem_cons_self, h2⟩
        | ind ts cs rs =>
          rcases declared_list IndRecRec.cv rs _ h1 with h2 | h2
          · rcases declared_list IndCtorRec.cv cs _ h2 with h3 | h3
            · rcases declared_list IndTypeRec.cv ts _ h3 with h4 | h4
              · exact .inl h4
              · exact .inr ⟨_, List.mem_cons_self, .inl h4⟩
            · exact .inr ⟨_, List.mem_cons_self, .inr (.inl h3)⟩
          · exact .inr ⟨_, List.mem_cons_self, .inr (.inr h2)⟩
      · exact .inr ⟨r, List.mem_cons_of_mem _ hr, h1⟩
  rcases key _ _ h with h1 | ⟨r, hr, h1⟩
  · simp at h1
  · exact ⟨r, by simpa using hr, h1⟩

/-- **The emission's input check**: a constant of the order that was visited and is not
filtered out is declared. -/
theorem coverageOk_declared {mg : Merged} {em : Emit} {n : Name} {c : CEntry}
    (h : coverageOk mg em = .ok ()) (hn : n ∈ mg.order) (hc : mg.map[n]? = some c)
    (hsk : c.skipped = false) (hv : em.visited.contains n = true) :
    em.declared.contains n = true := by
  unfold coverageOk at h
  have key : ∀ l : List Name, l.forM (coverStep mg em em.declared) = Except.ok () → ∀ x ∈ l,
      coverStep mg em em.declared x = .ok () := by
    intro l
    induction l with
    | nil => intro _ x hx; simp at hx
    | cons y l ih =>
      intro hl x hx
      have hl' : (coverStep mg em em.declared y >>= fun _ =>
          l.forM (coverStep mg em em.declared)) = Except.ok () := hl
      cases hy : coverStep mg em em.declared y with
      | error e => simp [hy, bind, Except.bind] at hl'
      | ok u =>
        rw [hy] at hl'
        rcases List.mem_cons.mp hx with rfl | hx
        · cases u; exact hy
        · exact ih hl' x hx
  have hs := key _ h n (by simpa using hn)
  unfold coverStep at hs
  rw [hc] at hs
  simp only [hsk, hv, Bool.not_false, Bool.and_self, ↓reduceIte] at hs
  by_cases hd : em.declared.contains n = true
  · exact hd
  · simp [hd, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs

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
    (hd : declsOf (emitAll mg rs) = .ok ds) (hcov : coverageOk mg (emitAll mg rs) = .ok ())
    (hrs : n ∈ rs) (hord : n ∈ mg.order) (hc : mg.map[n]? = some c) (hk : c.kind = .thm v all) :
    Declaration.thmDecl ⟨c.name, c.levelParams, c.type⟩ v ∈ ds := by
  obtain ⟨h1, h2⟩ := emitAll_spec hN rs
  have hsk : c.skipped = false := by simp [CEntry.skipped, hk, CKindF.skipped]
  obtain ⟨r, hr, hdc⟩ := declared_rec (coverageOk_declared hcov hord hc hsk (h2 n hrs c hc hsk))
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
