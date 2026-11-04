module

public import ConLeche.Frontend.Olean.Merge
public import ConLeche.Frontend.Scan.Types
public import Std.Data.HashSet.Lemmas

@[expose] public section

/-!
# Reading `.olean` files: the merged constants in lean4export's order

lean4export's `dumpConstant` walk: every constant whose name is not internal
is a root, every constant is emitted after the constants its type and value
mention, an inductive block as one record with its constructors and
recursors, the quotient package as its four records after `Eq`, unsafe and
partial constants left out.  The walk is iterative (`Work` items on an
explicit stack).  Its output is the record stream in the stream reader's own
syntax (`DeclRec`, `ConLeche/Frontend/Scan/Types.lean`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- Lean's `Name.isInternal`: some component starts with `_`. -/
def Name.isInternal : Name → Bool
  | .str p s => s.front == '_' || Name.isInternal p
  | .num p _ => Name.isInternal p
  | .anonymous => false

/-- One step of the emission walk. -/
inductive Work where
  | visit (n : Name)
  | one (c : CEntry)
  | quot (cs : List CEntry)
  | block (tys ctors recs : List CEntry)

/-- The emitter's output: the record stream in the stream reader's
syntax (`DeclRec`, indices into the two tables). -/
structure Emit where
  visited : Std.HashSet Name := {}
  names : Array Name := #[]
  exprs : Array Expr := #[]
  out : Array DeclRec := #[]

/-! The updates below take the field out of the record before changing
it, so that the array or set is changed at reference count 1 (the
`DS.mark` in `ConLeche/Frontend/Olean/Fast.lean` says why). -/

def Emit.name (st : Emit) (n : Name) : Emit × Nat :=
  let { visited, names, exprs, out } := st
  let i := names.size
  ({ visited, names := names.push n, exprs, out }, i)

def Emit.expr (st : Emit) (e : Expr) : Emit × Nat :=
  let { visited, names, exprs, out } := st
  let i := exprs.size
  ({ visited, names, exprs := exprs.push e, out }, i)

def Emit.push (st : Emit) (d : DeclRec) : Emit :=
  let { visited, names, exprs, out } := st
  { visited, names, exprs, out := out.push d }

def Emit.mark (st : Emit) (n : Name) : Emit :=
  let { visited, names, exprs, out } := st
  { visited := visited.insert n, names, exprs, out }

def Emit.cv (st : Emit) (c : CEntry) : Emit × CVRec :=
  let (st, n) := st.name c.name
  let (st, lps) := c.levelParams.foldl (fun (st, acc) p =>
    let (st, i) := st.name p; (st, acc.push i)) (st, #[])
  let (st, t) := st.expr c.type
  (st, ⟨n, lps.toList, t⟩)

def Emit.names' (st : Emit) (ns : List Name) : Emit × List Nat :=
  let (st, acc) := ns.foldl (fun (st, acc) p =>
    let (st, i) := st.name p; (st, acc.push i)) (st, #[])
  (st, acc.toList)

/-- **One constant's record.** -/
def Emit.one (st : Emit) (c : CEntry) : Emit :=
  let (st, cv) := st.cv c
  let (st, d) : Emit × Option DeclRec := match c.kind with
    | .ax u => (st, some (.ax cv u))
    | .defn v h s => let (st, i) := st.expr v; (st, some (.defn cv i h s))
    | .thm v _ => let (st, i) := st.expr v; (st, some (.thm cv i))
    | .opaq v u => let (st, i) := st.expr v; (st, some (.opaq cv i u))
    | .quot k => (st, some (.quot cv k))
    | _ => (st, none)
  match d with
  | some d => st.push d
  | none => st

/-- **An inductive block's record**: lean4export's `inductive` object. -/
def Emit.block (st : Emit) (tys ctors recs : List CEntry) : Emit :=
  let (st, ts) := tys.foldl (fun (st, acc) c =>
    match c.kind with
    | .induct np ni _ cs nn ir iu irf =>
      let (st, cv) := st.cv c
      let (st, cs) := st.names' cs
      (st, acc.push { cv, ctors := cs, isRec := ir, isReflexive := irf, isUnsafe := iu,
                      numIndices := ni, numNested := nn, numParams := np : IndTypeRec })
    | _ => (st, acc)) (st, #[])
  let (st, cts) := ctors.foldl (fun (st, acc) c =>
    match c.kind with
    | .ctor ind cidx np nf iu =>
      let (st, cv) := st.cv c
      let (st, ii) := st.name ind
      (st, acc.push { cv, isUnsafe := iu, numFields := nf, numParams := np,
                      cidx := some cidx, induct := some ii : IndCtorRec })
    | _ => (st, acc)) (st, #[])
  let (st, rs) := recs.foldl (fun (st, acc) c =>
    match c.kind with
    | .recur _ np ni nmo nmi rules k iu =>
      let (st, cv) := st.cv c
      let (st, rr) := rules.foldl (fun (st, acc) (cn, nf, rhs) =>
        let (st, ci) := st.name cn
        let (st, ri) := st.expr rhs
        (st, acc.push ({ ctor := ci, nfields := nf, rhs := ri } : RuleRec))) (st, #[])
      (st, acc.push { cv, isUnsafe := iu, k, numIndices := ni, numMinors := nmi,
                      numMotives := nmo, numParams := np, rules := rr.toList : IndRecRec })
    | _ => (st, acc)) (st, #[])
  st.push (.ind ts.toList cts.toList rs.toList)

/-! ### The emission walk terminates (task #421)

The walk's measure is the merged closure's names not yet visited, then
the stack's length: a `visit` of a name of the closure not yet visited
marks it; every other step pops one item and marks nothing new (the
record builders keep the visited set). -/

theorem Emit.name_visited (st : Emit) (n : Name) : (st.name n).1.visited = st.visited := by
  cases st; rfl
theorem Emit.expr_visited (st : Emit) (e : Expr) : (st.expr e).1.visited = st.visited := by
  cases st; rfl
theorem Emit.push_visited (st : Emit) (d : DeclRec) : (st.push d).visited = st.visited := by
  cases st; rfl

theorem Emit.foldl_visited {α β : Type} (f : Emit × β → α → Emit × β)
    (hf : ∀ s a, (f s a).1.visited = s.1.visited) (l : List α) (s : Emit × β) :
    (l.foldl f s).1.visited = s.1.visited := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons]; rw [ih, hf]

theorem Emit.cv_visited (st : Emit) (c : CEntry) : (st.cv c).1.visited = st.visited := by
  simp only [Emit.cv]
  rw [Emit.expr_visited, Emit.foldl_visited, Emit.name_visited]
  intro s a; exact Emit.name_visited _ _

theorem Emit.names'_visited (st : Emit) (ns : List Name) : (st.names' ns).1.visited = st.visited := by
  simp only [Emit.names']
  rw [Emit.foldl_visited]
  intro s a; exact Emit.name_visited _ _

theorem Emit.one_visited (st : Emit) (c : CEntry) : (st.one c).visited = st.visited := by
  simp only [Emit.one]
  split <;> rename_i h <;> split at h <;> simp_all [Emit.push_visited, Emit.expr_visited, Emit.cv_visited]

theorem Emit.block_visited (st : Emit) (tys ctors recs : List CEntry) :
    (st.block tys ctors recs).visited = st.visited := by
  simp only [Emit.block, Emit.push_visited]
  rw [Emit.foldl_visited, Emit.foldl_visited, Emit.foldl_visited]
  · intro s c; split <;> simp [Emit.cv_visited, Emit.names'_visited]
  · intro s c; split <;> simp [Emit.cv_visited, Emit.name_visited]
  · intro s c; split
    · simp only
      rw [Emit.foldl_visited, Emit.cv_visited]
      intro s r; simp [Emit.expr_visited, Emit.name_visited]
    · rfl

theorem Emit.foldl_one_visited {α : Type} (g : α → CEntry) (cs : List α) (st : Emit) :
    (cs.foldl (fun s x => s.one (g x)) st).visited = st.visited := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih => simp only [List.foldl_cons]; rw [ih, Emit.one_visited]

theorem Emit.mark_contains (st : Emit) (n k : Name) :
    (st.mark n).visited.contains k = (n == k || st.visited.contains k) := by
  cases st; exact Std.HashSet.contains_insert

theorem Emit.foldl_mark_mono {α : Type} (f : α → Name) (l : List α) (st : Emit) (k : Name)
    (h : st.visited.contains k = true) :
    (l.foldl (fun st x => st.mark (f x)) st).visited.contains k = true := by
  induction l generalizing st with
  | nil => exact h
  | cons a l ih => exact ih _ (by rw [Emit.mark_contains, h, Bool.or_true])

/-- The emission walk's measure: the merged closure's names not yet visited. -/
def Emit.unvisited (mg : Merged) (st : Emit) : Nat :=
  (mg.map.keys.filter (!st.visited.contains ·)).length

theorem Emit.filter_length_mono {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x, q x = true → p x = true) : (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons y ys ih =>
    simp only [List.filter_cons]
    by_cases hqy : q y = true
    · simp [hqy, h y hqy]; omega
    · by_cases hpy : p y = true <;> simp [hqy, hpy] <;> omega

theorem Emit.filter_length_strict {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x, q x = true → p x = true) {x : α} (hx : x ∈ l) (hp : p x = true) (hq : q x = false) :
    (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · simp only [List.filter_cons, hp, hq]
      simp only [ite_true, Bool.false_eq_true, ite_false, List.length_cons]
      exact Nat.lt_succ_of_le (Emit.filter_length_mono ys p q h)
    · have := ih hx
      simp only [List.filter_cons]
      by_cases hqy : q y = true
      · simp [hqy, h y hqy]; omega
      · by_cases hpy : p y = true <;> simp [hqy, hpy] <;> omega

theorem Emit.unvisited_le {mg : Merged} {st st' : Emit}
    (h : ∀ k, st.visited.contains k = true → st'.visited.contains k = true) :
    Emit.unvisited mg st' ≤ Emit.unvisited mg st := by
  apply Emit.filter_length_mono
  intro k hk; cases hs : st.visited.contains k
  · rfl
  · simp [h k hs] at hk

theorem Emit.unvisited_lt {mg : Merged} {st st' : Emit} {n : Name} {c : CEntry}
    (hc : mg.map[n]? = some c) (hv : st.visited.contains n = false)
    (hn : st'.visited.contains n = true)
    (h : ∀ k, st.visited.contains k = true → st'.visited.contains k = true) :
    Emit.unvisited mg st' < Emit.unvisited mg st := by
  apply Emit.filter_length_strict _ _ _ _ (x := n)
  · rw [Std.HashMap.mem_keys]; exact Std.HashMap.mem_iff_isSome_getElem?.2 (by simp [hc])
  · simp [hv]
  · simp [hn]
  · intro k hk; cases hs : st.visited.contains k
    · rfl
    · simp [h k hs] at hk

theorem Emit.mark_self (st : Emit) (n : Name) : (st.mark n).visited.contains n = true := by
  rw [Emit.mark_contains]; simp

theorem Emit.mark_mono {st : Emit} {k : Name} (n : Name) (h : st.visited.contains k = true) :
    (st.mark n).visited.contains k = true := by
  rw [Emit.mark_contains, h, Bool.or_true]

theorem Emit.lex_of_le {a a' b b' : Nat} (h1 : a' ≤ a) (h2 : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases Nat.lt_or_eq_of_le h1 with h | rfl
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h2

/-- **The emission walk** (lean4export's `dumpConstant`, iterative):
`visit n` emits `n`'s record after its dependencies.  Well-founded on
the names not yet visited, then the stack (`Emit.unvisited`). -/
def emitLoop (mg : Merged) (recMap : Std.HashMap Name (Array Name))
    (stack : List Work) (st : Emit) : Emit :=
  match stack with
  | [] => st
  | .one c :: rest => emitLoop mg recMap rest (st.one c)
  | .quot cs :: rest => emitLoop mg recMap rest (cs.foldl Emit.one st)
  | .block ts cs rs :: rest => emitLoop mg recMap rest (st.block ts cs rs)
  | .visit n :: rest =>
    if _hv : st.visited.contains n then emitLoop mg recMap rest st else
    match _hc : mg.map[n]? with
    | none => emitLoop mg recMap rest st
    | some c =>
      if c.skipped then emitLoop mg recMap rest st else
      let st := st.mark n
      let visits (cs : List CEntry) : List Work :=
        cs.flatMap fun c => c.uses.toList.map Work.visit
      match c.kind with
      | .ax _ | .defn .. | .thm .. | .opaq .. =>
        emitLoop mg recMap (visits [c] ++ Work.one c :: rest) st
      | .quot _ =>
        let qs := [mkN ["Quot"], mkN ["Quot", "mk"], mkN ["Quot", "lift"], mkN ["Quot", "ind"]].filterMap (mg.map[·]?)
        let st := qs.foldl (fun st q => st.mark q.name) st
        emitLoop mg recMap (Work.visit (mkN ["Eq"]) :: Work.quot qs :: rest) st
      | .ctor ind .. => emitLoop mg recMap (Work.visit ind :: rest) st
      | .recur all .. => emitLoop mg recMap (all.map Work.visit ++ rest) st
      | .induct _ _ all _ _ _ _ _ =>
        let tys : List CEntry := all.filterMap (mg.map[·]?)
        let ctors := tys.flatMap fun t => match t.kind with
          | .induct _ _ _ cs _ _ _ _ => cs.filterMap (mg.map[·]?)
          | _ => []
        let recs : List CEntry := ((recMap[n]?).getD #[]).toList.filterMap (mg.map[·]?)
        let st := (tys ++ ctors ++ recs).foldl
          (fun st x => st.mark x.name) st
        emitLoop mg recMap (visits (tys ++ ctors ++ recs) ++ Work.block tys ctors recs :: rest) st
termination_by (Emit.unvisited mg st, stack.length)
decreasing_by
  all_goals first
    | exact Emit.lex_of_le (Nat.le_refl _) (by simp)
    | exact Emit.lex_of_le (Emit.unvisited_le fun k hk => by rwa [Emit.one_visited]) (by simp)
    | exact Emit.lex_of_le (Emit.unvisited_le fun k hk => by rwa [Emit.foldl_one_visited]) (by simp)
    | exact Emit.lex_of_le (Emit.unvisited_le fun k hk => by rwa [Emit.block_visited]) (by simp)
    | exact Prod.Lex.left _ _ (Emit.unvisited_lt _hc (by simpa using _hv) (Emit.mark_self _ _)
        fun k hk => Emit.mark_mono _ hk)
    | exact Prod.Lex.left _ _ (Emit.unvisited_lt _hc (by simpa using _hv)
        (Emit.foldl_mark_mono _ _ _ _ (Emit.mark_self _ _))
        fun k hk => Emit.foldl_mark_mono _ _ _ _ (Emit.mark_mono _ hk))

/-- **The record stream of the merged closure.** -/
def emitAll (mg : Merged) : Emit :=
  let recMap := mg.order.foldl (fun (m : Std.HashMap Name (Array Name)) n =>
    match (mg.map[n]?).map (·.kind) with
    | some (CKindF.recur all ..) =>
      all.foldl (fun m i => m.alter i fun
        | none => some #[n]
        | some a => some (if a.contains n then a else a.push n)) m
    | _ => m) {}
  let roots := mg.order.filter (!Name.isInternal ·)
  emitLoop mg recMap (roots.toList.map .visit) {}

/-! ## The coverage of the emission -/

/-- The names an emitted record declares. -/
def Emit.declared (em : Emit) : Std.HashSet Name :=
  let nm (cv : CVRec) (s : Std.HashSet Name) : Std.HashSet Name :=
    match em.names[cv.name]? with
    | some n => s.insert n
    | none => s
  em.out.foldl (init := {}) fun s d => match d with
    | .ax cv _ | .defn cv .. | .thm cv _ | .opaq cv .. | .quot cv _ => nm cv s
    | .ind ts cs rs =>
      let s := ts.foldl (fun s t => nm t.cv s) s
      let s := cs.foldl (fun s c => nm c.cv s) s
      rs.foldl (fun s r => nm r.cv s) s

/-- **Every constant the walk reached is in an emitted record**
(task #383): the walk's `visit` of a constructor or recursor emits its
inductive block, and a block takes its members, constructors and
recursors from the constants by name; a constructor its block does not
list, a recursor no member of its block finds, or a block naming a
member or constructor that is not stored would otherwise be dropped
without a word.  Every constant the walk reached and did not skip
(`CEntry.skipped`) must be declared by an emitted record, and every
inductive type's block members and constructors must be stored, the
members must agree on the block and the constructors name their type,
and a recursor's block must be its first member's; a violation is
malformed input. -/
def coverageOk (mg : Merged) (em : Emit) : Except CheckError Unit := do
  let decl := em.declared
  for n in mg.order do
    if let some c := mg.map[n]? then
      if !c.skipped && em.visited.contains n then
        unless decl.contains n do
          throw (.internal s!"the constant {n} is in no emitted record (a constructor or \
            recursor its inductive block does not have)")
        -- the data that decides which constants form one block (task
        -- #383), which a reader could take from `all`, from `ctors` or
        -- from a constructor's `induct`: they must agree.  The other
        -- fields are the record builder's (`validateIndF`) and the
        -- installer's.
        let bad (what : String) : CheckError := .internal s!"the inductive data of {n}: {what}"
        match c.kind with
        | .induct _ _ all cs _ _ _ _ =>
          unless all.contains n do throw (bad "its block does not list it")
          for x in all do
            match ((mg.map[x]?).map (·.kind) : Option CKind) with
            | some (.induct _ _ all' ..) =>
              unless all' == all do throw (bad s!"its block member {x} names another block")
            | some _ => throw (bad s!"its block member {x} is not an inductive type")
            | none => throw (bad s!"its block member {x} is not stored")
          for x in cs do
            match ((mg.map[x]?).map (·.kind) : Option CKind) with
            | some (.ctor ind ..) =>
              unless ind == n do throw (bad s!"its constructor {x} names another type")
            | some _ => throw (bad s!"its constructor {x} is not a constructor")
            | none => throw (bad s!"its constructor {x} is not stored")
        | .recur all .. =>
          match all.head? with
          | none => throw (bad "the recursor names no block")
          | some t =>
            match ((mg.map[t]?).map (·.kind) : Option CKind) with
            | some (.induct _ _ all' ..) =>
              unless all' == all do throw (bad s!"the recursor's block is not {t}'s")
            | _ => throw (bad s!"the recursor's block member {t} is not a stored inductive type")
        | _ => pure ()

end ConLeche.Frontend.Olean
