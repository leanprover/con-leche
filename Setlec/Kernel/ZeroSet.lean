import Setlec.Kernel.Level

/-!
# `ZeroSet`/`ZPropWhen`: the canonical zero-ness datum (task #161, P5 candidate)

This module is a **side module**: nothing in the checker consumes it
yet.  It is the prepared *canonical* representation of the binder
annotation datum that `Setlec.PropWhen` (`Kernel/Expr.lean`) holds in
free form — a parameter set as a sorted, duplicate-free list, wrapped
in a subtype so that the representation invariant travels with the
value (the `Std.HashMap` pattern of `CLAUDE.md`: the structure carries
its invariant, downstream never re-proves it).

**Why it exists.**  The landed free datum stores `ps : List Name`
unordered and with duplicates, so *syntactic* equality is finer than
predicate equality and every comparison site must use the containment
test `PropWhen.equiv` (task #161 amendment 2).  With the canonical
form the two collapse: `ZPropWhen`-equality **is** zero-ness agreement
at every valuation (`Verify/ZeroSet.lean`, `eq_iff_holds`), so `=`,
`decide`, `BEq` and the derived `Hashable` all decide the semantic
question.  Amendment 2's counterexample to a *normalizing* `substPW`
does not apply here: it falsified normalization applied to
*non-canonical inputs* (`instantiateLevelParams_self` re-sorted a
hand-written meta).  Every `ZeroSet` is canonical by construction, so
`substPW_self` holds again (`Verify/ZeroSet.lean`, `substPWZ_self`),
while the definedness hypothesis of the composition law — which is
representation-independent — stays.

**Interface discipline.**  The main proof is meant to consume the
datum ONLY through the operations and laws mirrored here, one for one,
from the landed free API (`empty`/`singleton`/`ofList`/`union`/`mem`/
`subset`; `holds`, `inter`, `bindZ`, `zeronessOf`, `substPW`,
`paramsDefined`, `hasParams`, `equiv`).  Swapping the representation
then means re-instantiating that inventory, not re-auditing the
consistency proof.  The bridge `toFree`/`ofFree` (with the transport
lemmas in `Setlec/Verify/ZeroSet.lean`) lets the swap be staged.

Layering: this file is implementation tier (it imports only
`Setlec.Kernel.Level`) and carries exactly the invariant-preservation
proofs the definitions need; the law battery lives in
`Setlec/Verify/ZeroSet.lean`, which states it against the *same*
`Level.eval`/`holds` semantics as the landed battery.
-/

namespace Setlec

/-! ## A total order on names

There is no order on `Setlec.Name` in the tree (the `NNode` arena keys
by interned index, the level arena stores raw names), so the canonical
form needs one.  `Name.cmp` is the structural lexicographic order —
the same shape as `Lean.Name.quickLt` minus the hash short-cut, which
would make the order dependent on hashing.  Constructor order is
`anonymous < str < num`; equal constructors compare the prefix first,
then the payload with the core `Ord` instances (`String`/`Nat`), whose
`Std.TransCmp`/`Std.LawfulEqCmp` instances supply the payload half of
every law below. -/

namespace Name

/-- Structural lexicographic comparison of names. -/
def cmp : Name → Name → Ordering
  | .anonymous, .anonymous => .eq
  | .anonymous, .str _ _ => .lt
  | .anonymous, .num _ _ => .lt
  | .str _ _, .anonymous => .gt
  | .num _ _, .anonymous => .gt
  | .str _ _, .num _ _ => .lt
  | .num _ _, .str _ _ => .gt
  | .str p s, .str q t => (cmp p q).then (compare s t)
  | .num p m, .num q n => (cmp p q).then (compare m n)

/-- Strict less-than on names (`cmp` reading `lt`). -/
def blt (a b : Name) : Bool := (cmp a b) == .lt

theorem blt_eq_true {a b : Name} : blt a b = true ↔ cmp a b = .lt := by
  simp [blt]

theorem cmp_self : ∀ a : Name, cmp a a = .eq
  | .anonymous => rfl
  | .str p s => by
    simp [cmp, cmp_self p, Ordering.then, Std.ReflCmp.compare_self]
  | .num p n => by
    simp [cmp, cmp_self p, Ordering.then, Std.ReflCmp.compare_self]

theorem eq_of_cmp : ∀ {a b : Name}, cmp a b = .eq → a = b
  | .anonymous, .anonymous, _ => rfl
  | .str p s, .str q t, h => by
    rw [cmp, Ordering.then_eq_eq] at h
    rw [eq_of_cmp h.1, Std.LawfulEqCmp.compare_eq_iff_eq.mp h.2]
  | .num p m, .num q n, h => by
    rw [cmp, Ordering.then_eq_eq] at h
    rw [eq_of_cmp h.1, Std.LawfulEqCmp.compare_eq_iff_eq.mp h.2]

theorem cmp_swap : ∀ a b : Name, cmp a b = (cmp b a).swap
  | .anonymous, .anonymous => rfl
  | .anonymous, .str _ _ => rfl
  | .anonymous, .num _ _ => rfl
  | .str _ _, .anonymous => rfl
  | .num _ _, .anonymous => rfl
  | .str _ _, .num _ _ => rfl
  | .num _ _, .str _ _ => rfl
  | .str p s, .str q t => by
    rw [cmp, cmp, Ordering.swap_then, ← cmp_swap p q,
      ← Std.OrientedCmp.eq_swap (cmp := compare)]
  | .num p m, .num q n => by
    rw [cmp, cmp, Ordering.swap_then, ← cmp_swap p q,
      ← Std.OrientedCmp.eq_swap (cmp := compare)]

theorem cmp_trans : ∀ {a b c : Name}, cmp a b = .lt → cmp b c = .lt →
    cmp a c = .lt
  | .anonymous, .str _ _, .str _ _, _, _ => rfl
  | .anonymous, .str _ _, .num _ _, _, _ => rfl
  | .anonymous, .num _ _, .num _ _, _, _ => rfl
  | .str _ _, .num _ _, .num _ _, _, _ => rfl
  | .anonymous, .anonymous, _, h, _ => by simp [cmp] at h
  | .str p s, .str q t, .num _ _, _, _ => rfl
  | .str p s, .str q t, .str r u, h1, h2 => by
    rw [cmp, Ordering.then_eq_lt] at h1 h2 ⊢
    rcases h1 with h1 | ⟨h1, hs⟩
    · rcases h2 with h2 | ⟨h2, _⟩
      · exact Or.inl (cmp_trans h1 h2)
      · exact Or.inl (eq_of_cmp h2 ▸ h1)
    · rcases h2 with h2 | ⟨h2, ht⟩
      · exact Or.inl (eq_of_cmp h1 ▸ h2)
      · have hpq : p = q := eq_of_cmp h1
        have hqr : q = r := eq_of_cmp h2
        subst hpq; subst hqr
        exact Or.inr ⟨cmp_self p, Std.TransCmp.lt_trans hs ht⟩
  | .num p m, .num q n, .num r k, h1, h2 => by
    rw [cmp, Ordering.then_eq_lt] at h1 h2 ⊢
    rcases h1 with h1 | ⟨h1, hs⟩
    · rcases h2 with h2 | ⟨h2, _⟩
      · exact Or.inl (cmp_trans h1 h2)
      · exact Or.inl (eq_of_cmp h2 ▸ h1)
    · rcases h2 with h2 | ⟨h2, ht⟩
      · exact Or.inl (eq_of_cmp h1 ▸ h2)
      · have hpq : p = q := eq_of_cmp h1
        have hqr : q = r := eq_of_cmp h2
        subst hpq; subst hqr
        exact Or.inr ⟨cmp_self p, Std.TransCmp.lt_trans hs ht⟩

theorem blt_irrefl (a : Name) : blt a a = false := by
  simp [blt, cmp_self]

theorem blt_trans {a b c : Name} (h1 : blt a b = true) (h2 : blt b c = true) :
    blt a c = true :=
  blt_eq_true.mpr (cmp_trans (blt_eq_true.mp h1) (blt_eq_true.mp h2))

theorem blt_asymm {a b : Name} (h : blt a b = true) : blt b a = false := by
  have h' : cmp a b = .lt := blt_eq_true.mp h
  have : cmp b a = .gt := by
    rw [cmp_swap b a, h']; rfl
  simp [blt, this]

theorem ne_of_blt {a b : Name} (h : blt a b = true) : a ≠ b := by
  intro he
  rw [he, blt_irrefl] at h
  exact Bool.false_ne_true h

/-- Trichotomy: names are linearly ordered by `blt`. -/
theorem blt_trichotomy (a b : Name) :
    a = b ∨ blt a b = true ∨ blt b a = true := by
  cases h : cmp a b with
  | eq => exact Or.inl (eq_of_cmp h)
  | lt => exact Or.inr (Or.inl (blt_eq_true.mpr h))
  | gt =>
    refine Or.inr (Or.inr (blt_eq_true.mpr ?_))
    rw [cmp_swap b a, h]; rfl

end Name

/-! ## The sorted-list layer

The invariant is one `Chain'`-style predicate: `ascending` says every
head is strictly below *all* of its tail, which is sortedness and
duplicate-freeness in a single clause. -/

namespace ZeroSet

/-- Is every element of `l` strictly greater than `n`? -/
def gtAll (n : Name) (l : List Name) : Bool := l.all fun m => n.blt m

/-- Strictly ascending: sorted **and** duplicate-free, in one clause. -/
def ascending : List Name → Bool
  | [] => true
  | n :: rest => gtAll n rest && ascending rest

theorem gtAll_iff {n : Name} {l : List Name} :
    gtAll n l = true ↔ ∀ m ∈ l, n.blt m = true := by
  simp [gtAll]

theorem ascending_cons {n : Name} {l : List Name} :
    ascending (n :: l) = true ↔ gtAll n l = true ∧ ascending l = true := by
  simp [ascending]

/-- The ordered merge of two ascending lists — the union of the two
sets, still ascending (`ascending_mergeRaw`). -/
def mergeRaw : List Name → List Name → List Name
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs =>
    match Name.cmp a b with
    | .lt => a :: mergeRaw as (b :: bs)
    | .eq => a :: mergeRaw as bs
    | .gt => b :: mergeRaw (a :: as) bs
termination_by as bs => as.length + bs.length

@[simp] theorem mem_mergeRaw : ∀ (as bs : List Name) {n : Name},
    n ∈ mergeRaw as bs ↔ n ∈ as ∨ n ∈ bs := by
  intro as bs
  fun_induction mergeRaw as bs with
  | case1 bs => simp
  | case2 a as => simp
  | case3 a as b bs hc ih =>
    intro n; simp only [List.mem_cons, ih]; grind
  | case4 a as b bs hc ih =>
    intro n
    have hab : a = b := Name.eq_of_cmp hc
    simp only [List.mem_cons, ih, hab]; grind
  | case5 a as b bs hc ih =>
    intro n; simp only [List.mem_cons, ih]; grind

theorem gtAll_mergeRaw {n : Name} {as bs : List Name}
    (ha : gtAll n as = true) (hb : gtAll n bs = true) :
    gtAll n (mergeRaw as bs) = true :=
  gtAll_iff.mpr fun m hm =>
    match (mem_mergeRaw as bs).mp hm with
    | .inl h => gtAll_iff.mp ha m h
    | .inr h => gtAll_iff.mp hb m h

theorem ascending_mergeRaw : ∀ {as bs : List Name}, ascending as = true →
    ascending bs = true → ascending (mergeRaw as bs) = true := by
  intro as bs
  fun_induction mergeRaw as bs with
  | case1 bs => intro _ h; simpa using h
  | case2 a as => intro h1 _; simpa using h1
  | case3 a as b bs hc ih =>
    intro h1 h2
    rw [ascending_cons] at h1
    rw [ascending_cons]
    refine ⟨gtAll_mergeRaw h1.1 (gtAll_iff.mpr ?_), ih h1.2 h2⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Name.blt_eq_true.mpr hc
    · exact Name.blt_trans (Name.blt_eq_true.mpr hc)
        (gtAll_iff.mp (ascending_cons.mp h2).1 m hm)
  | case4 a as b bs hc ih =>
    intro h1 h2
    have hab : a = b := Name.eq_of_cmp hc
    rw [ascending_cons] at h1
    rw [ascending_cons]
    exact ⟨gtAll_mergeRaw h1.1 (hab ▸ (ascending_cons.mp h2).1),
      ih h1.2 (ascending_cons.mp h2).2⟩
  | case5 a as b bs hc ih =>
    intro h1 h2
    have hba : b.blt a = true := by
      refine Name.blt_eq_true.mpr ?_
      rw [Name.cmp_swap b a, hc]; rfl
    rw [ascending_cons] at h2
    rw [ascending_cons]
    refine ⟨gtAll_mergeRaw (gtAll_iff.mpr ?_) h2.1, ih h1 h2.2⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hba
    · exact Name.blt_trans hba (gtAll_iff.mp (ascending_cons.mp h1).1 m hm)

end ZeroSet

/-- A canonical set of level-parameter names: a strictly ascending list
(sorted and duplicate-free — `ZeroSet.ascending`), so that equal sets
are *equal values*.  The invariant travels with the value; consumers
never re-establish it. -/
structure ZeroSet where
  /-- The elements, strictly ascending. -/
  names : List Name
  /-- The representation invariant. -/
  asc : ZeroSet.ascending names = true

namespace ZeroSet

/-- Two `ZeroSet`s with the same underlying list are equal (the proof
field is a `Prop`). -/
theorem eq_of_names : ∀ {a b : ZeroSet}, a.names = b.names → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- Decidable equality, decided on the list alone (P5 concern: the
`Prop` field blocks `deriving DecidableEq`, and a decision procedure
that looked at proofs would not compute; here equal lists give equal
values by `eq_of_names`, so this *is* set equality — see
`Verify/ZeroSet.lean`, `eq_iff_holds`). -/
instance : DecidableEq ZeroSet := fun a b =>
  if h : a.names = b.names then .isTrue (eq_of_names h)
  else .isFalse fun he => h (by rw [he])

/-- `BEq` **is** the `DecidableEq` (P5 concern: comparison sites that
today call `PropWhen.equiv` may call `==` once the representation is
canonical — `Verify/ZeroSet.lean`'s `eq_iff_holds` is the licence). -/
instance : BEq ZeroSet := instBEqOfDecidableEq

/-- Hash the underlying list; canonicity makes it a hash of the
*set* (P5 concern: `ENode`'s derived `Hashable` includes the binder
meta, so equal data must hash equally — with the free datum that holds
only up to `equiv`). -/
instance : Hashable ZeroSet := ⟨fun s => hash s.names⟩

/-- Show the underlying list (P5 concern: error messages and `#guard`
output; the proof field is not printable). -/
instance : Repr ZeroSet := ⟨fun s p => reprPrec s.names p⟩

/-- The empty set — "always zero". -/
def empty : ZeroSet := ⟨[], rfl⟩

instance : Inhabited ZeroSet := ⟨empty⟩

/-- The one-element set. -/
def singleton (n : Name) : ZeroSet := ⟨[n], rfl⟩

/-- Membership (decidable). -/
def mem (s : ZeroSet) (n : Name) : Bool := s.names.contains n

/-- Union: the ordered merge, canonical again by
`ascending_mergeRaw`. -/
def union (a b : ZeroSet) : ZeroSet :=
  ⟨mergeRaw a.names b.names, ascending_mergeRaw a.asc b.asc⟩

/-- Canonicalize a raw list: sort and deduplicate, by folding the
singletons together. -/
def ofList (l : List Name) : ZeroSet :=
  l.foldr (fun n s => (singleton n).union s) empty

/-- Subset test. -/
def subset (a b : ZeroSet) : Bool := a.names.all b.mem

/-- Is the set empty (the "always zero" datum)? -/
def isEmpty (s : ZeroSet) : Bool := s.names.isEmpty

/-! ### Defining equations -/

@[simp] theorem names_empty : empty.names = [] := rfl

@[simp] theorem names_singleton (n : Name) : (singleton n).names = [n] := rfl

@[simp] theorem names_union (a b : ZeroSet) :
    (a.union b).names = mergeRaw a.names b.names := rfl

@[simp] theorem ofList_nil : ofList [] = empty := rfl

@[simp] theorem ofList_cons (n : Name) (l : List Name) :
    ofList (n :: l) = (singleton n).union (ofList l) := rfl

@[simp] theorem mem_def (s : ZeroSet) (n : Name) :
    s.mem n = s.names.contains n := rfl

@[simp] theorem subset_def (a b : ZeroSet) :
    a.subset b = a.names.all b.mem := rfl

end ZeroSet

/-! ## The canonical datum

`ZPropWhen` mirrors `Setlec.PropWhen` constructor for constructor; the
only change is that the parameter set is a `ZeroSet`. -/

/-- The zero-ness datum of a binder's codomain sort, canonically
represented: either the sort is never zero, or it is zero exactly when
every parameter of a canonical `ZeroSet` is zero. -/
inductive ZPropWhen where
  /-- The codomain sort is never zero. -/
  | never
  /-- Zero exactly when every parameter in `s` is zero. -/
  | ifAllZero (s : ZeroSet)
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : BEq ZPropWhen := instBEqOfDecidableEq

namespace ZPropWhen

/-- Does the datum hold at a valuation — is the codomain sort zero
there?  Mirrors `PropWhen.holds`. -/
def holds (φ : Name → Nat) : ZPropWhen → Bool
  | .never => false
  | .ifAllZero s => s.names.all fun n => φ n == 0

/-- The same reading against an arbitrary parameter predicate — the
form the `bindZ` law needs (`holds φ = holdsP (φ · == 0)`). -/
def holdsP (P : Name → Bool) : ZPropWhen → Bool
  | .never => false
  | .ifAllZero s => s.names.all P

/-- The datum's parameters (`[]` for `never`, which mentions none) —
the list every "footprint" law quantifies over. -/
def parameters : ZPropWhen → List Name
  | .never => []
  | .ifAllZero s => s.names

/-- Does the datum mention any level parameter?  Mirrors
`PropWhen.hasParams`. -/
def hasParams : ZPropWhen → Bool
  | .never => false
  | .ifAllZero s => !s.isEmpty

/-- Are all parameters of the datum among `params`?  Mirrors
`PropWhen.paramsDefined`. -/
def paramsDefined (params : List Name) : ZPropWhen → Bool
  | .never => true
  | .ifAllZero s => s.names.all params.contains

/-- Intersection of two zero-ness predicates (the `max` rule):
`never` absorbs, sets unite.  Mirrors `PropWhen.inter` — with the
*canonical* union in place of list append. -/
def inter : ZPropWhen → ZPropWhen → ZPropWhen
  | .never, _ => .never
  | _, .never => .never
  | .ifAllZero a, .ifAllZero b => .ifAllZero (a.union b)

/-- Substitute each parameter by a whole datum and intersect — the
monadic bind of the zero-ness reading.  Mirrors `PropWhen.bindZ`;
canonical on output because `inter` is. -/
def bindZ (f : Name → ZPropWhen) : ZPropWhen → ZPropWhen
  | .never => .never
  | .ifAllZero s => go s.names
where
  /-- The fold over the parameter list. -/
  go : List Name → ZPropWhen
  | [] => .ifAllZero .empty
  | n :: rest => (f n).inter (go rest)

/-- Zero-ness agreement at every valuation.  Mirrors
`PropWhen.equiv` — but on canonical data it *is* equality
(`Verify/ZeroSet.lean`, `equiv_eq_beq`/`eq_iff_holds`), which is the
point of the representation. -/
def equiv (p q : ZPropWhen) : Bool := p == q

end ZPropWhen

namespace Level

/-- The zero-ness datum of a level, canonical.  Mirrors
`Level.zeronessOf`. -/
def zeronessOfZ : Level → ZPropWhen
  | .zero => .ifAllZero .empty
  | .succ _ => .never
  | .param n => .ifAllZero (.singleton n)
  | .max a b => (zeronessOfZ a).inter (zeronessOfZ b)
  | .imax _ b => zeronessOfZ b

/-- Push a level-parameter substitution through a canonical datum.
Mirrors `Level.substPW`. -/
def substPWZ (ks : List Name) (vs : List Level) (pw : ZPropWhen) :
    ZPropWhen :=
  pw.bindZ fun n => zeronessOfZ (subst.go ks vs n)

end Level

/-! ## Bridge to the landed free representation

`toFree` forgets canonicity; `ofFree` restores it.  The transport
lemmas (`Verify/ZeroSet.lean`) make the eventual swap stageable: any
free-side fact transfers along `toFree`, and any canonical-side fact
along `ofFree`. -/

namespace ZPropWhen

/-- Forget the invariant: the canonical datum as a free one. -/
def toFree : ZPropWhen → PropWhen
  | .never => .never
  | .ifAllZero s => .ifAllZero s.names

/-- Canonicalize a free datum. -/
def ofFree (pw : PropWhen) : ZPropWhen :=
  match pw.toList? with
  | none => .never
  | some ps => .ifAllZero (ZeroSet.ofList ps)

@[simp] theorem ofFree_never : ofFree .never = .never := rfl

@[simp] theorem ofFree_ifAllZero (ps : List Name) :
    ofFree (PropWhen.ifAllZero ps) = .ifAllZero (ZeroSet.ofList ps) := by
  simp [ofFree]

end ZPropWhen

end Setlec
