module

public import ConLeche.Verify.Inductives.NestedLedger

public section

/-!
# The cross-copy reference relation and its order (task #279 M-B′ step 3f)

The forward fold `ψ_A` of a copy `A` (DESIGN §M.3, §M.17) transports a
`J`-ordinary field that is aux-recursive into another copy `A'` by
`ψ_{A'}`, so the spellings are defined by recursion over the copies
along a REFERENCE relation.  DESIGN §M.22 records that this relation
has no syntactic well-founded measure (a parameter-headed field puts a
pin component's head on top of the target's pin; on the raw terms the
relation is not even acyclic — kinding is what excludes the cycles)
and that the honest source of the order is the kernel: it computes the
relation from the elimination's result and emits a topological order,
declining a cyclic block.  This module states that contract ONCE, in
the vocabulary both sides share (`ElimState`, the pin list, the copies'
processed constructor types), so that the kernel's computation and the
model's fold consume the same definition:

* `Expr.Sub` — the subterm relation along the positions the replace
  walk visits (no edge into an `fvar`'s annotation, none the walk does
  not take);
* `CopyRef grp k st j j'` — pin `j`'s copy refers to pin `j'`'s: a
  processed constructor of the copy mentions the target copy's name;
  the target is outside the source's mint group (`grp j = (j₀, n)`,
  the group's base and size in the pin list — the elimination's own
  bookkeeping, `mkCopies_spec`); and no pin of the source's group is a
  subterm of the target's pin (the exclusion that keeps a container's
  references through its OWN mimics out of the relation: a mimic's pin
  contains a group pin, §M.17);
* `TopoOrder R n order` — a permutation of the copy indices along
  which every reference points backwards, and `TopoOrder.ref_mem_take`
  — at position `i` of the order every reference of the copy there is
  among the first `i` entries — the ONE fact the fold over `order`
  consumes.

The relation is a SUPERSET of what `ψ` needs (`R_ψ`: the
`J`-ordinary, aux-recursive references), and that inclusion is the
bridge the ψ spelling states in the datum's vocabulary (DESIGN §M.22).
-/

namespace ConLeche

/-! ## The walk's subterm relation -/

/-- The positions `replaceAllNested` visits: the term itself, both
sides of an application, a binder's domain and body, a `let`'s three
parts, a projection's subject.  NOT an `fvar`'s annotation (the walk
returns an `fvar` unchanged). -/
inductive Expr.Sub : Expr → Expr → Prop
  | refl (e : Expr) : Sub e e
  | appF {e f a : Expr} : Sub e f → Sub e (.app f a)
  | appA {e f a : Expr} : Sub e a → Sub e (.app f a)
  | lamT {e ty b : Expr} {m : BinderMeta} : Sub e ty → Sub e (.lam ty b m)
  | lamB {e ty b : Expr} {m : BinderMeta} : Sub e b → Sub e (.lam ty b m)
  | piT {e ty b : Expr} {m : BinderMeta} : Sub e ty → Sub e (.forallE ty b m)
  | piB {e ty b : Expr} {m : BinderMeta} : Sub e b → Sub e (.forallE ty b m)
  | letT {e ty v b : Expr} : Sub e ty → Sub e (.letE ty v b)
  | letV {e ty v b : Expr} : Sub e v → Sub e (.letE ty v b)
  | letB {e ty v b : Expr} : Sub e b → Sub e (.letE ty v b)
  | proj {e x : Expr} {s : Name} {i : Nat} : Sub e x → Sub e (.proj s i x)

theorem Expr.Sub.trans {e₁ e₂ e₃ : Expr} (h₁ : Expr.Sub e₁ e₂) (h₂ : Expr.Sub e₂ e₃) :
    Expr.Sub e₁ e₃ := by
  induction h₂ with
  | refl => exact h₁
  | appF _ ih => exact .appF ih
  | appA _ ih => exact .appA ih
  | lamT _ ih => exact .lamT ih
  | lamB _ ih => exact .lamB ih
  | piT _ ih => exact .piT ih
  | piB _ ih => exact .piB ih
  | letT _ ih => exact .letT ih
  | letV _ ih => exact .letV ih
  | letB _ ih => exact .letB ih
  | proj _ ih => exact .proj ih

/-- An application spine's prefix is a subterm of the spine. -/
theorem Expr.Sub.mkAppN_prefix (f : Expr) :
    ∀ (l₁ l₂ : List Expr), Expr.Sub (Expr.mkAppN f l₁) (Expr.mkAppN f (l₁ ++ l₂)) := by
  intro l₁ l₂
  induction l₂ generalizing f l₁ with
  | nil => rw [List.append_nil]; exact .refl _
  | cons a as ih =>
    have h := ih f (l₁ ++ [a])
    rw [List.append_assoc, List.singleton_append] at h
    refine Expr.Sub.trans ?_ h
    rw [Expr.mkAppN_append_one]
    exact .appF (.refl _)

/-- A subterm mentions what its subterm mentions. -/
theorem Expr.Sub.mentionsConst {T : Name} {e e' : Expr} (h : Expr.Sub e e')
    (hm : e.mentionsConst T = true) : e'.mentionsConst T = true := by
  induction h with
  | refl => exact hm
  | appF _ ih => simp [Expr.mentionsConst, ih]
  | appA _ ih => simp [Expr.mentionsConst, ih]
  | lamT _ ih => simp [Expr.mentionsConst, ih]
  | lamB _ ih => simp [Expr.mentionsConst, ih]
  | piT _ ih => simp [Expr.mentionsConst, ih]
  | piB _ ih => simp [Expr.mentionsConst, ih]
  | letT _ ih => simp [Expr.mentionsConst, ih]
  | letV _ ih => simp [Expr.mentionsConst, ih]
  | letB _ ih => simp [Expr.mentionsConst, ih]
  | proj _ ih => simp [Expr.mentionsConst, ih]

/-! ## The reference relation -/

/-- **Pin `j`'s copy refers to pin `j'`'s** (DESIGN §M.22).  `k` is the
block's own member count (the copies are `st.types[k + j]`), `grp j =
(j₀, n)` the mint group of pin `j` — base and size in the pin list.
A processed constructor of the source copy mentions the target copy's
name; the target is outside the source's group; no pin of the source's
group is a subterm of the target's pin. -/
def CopyRef (grp : Nat → Nat × Nat) (k : Nat) (st : ElimState) (j j' : Nat) : Prop :=
  ∃ (t t' : AuxType) (q' : NestedPin),
    st.types[k + j]? = some t ∧ st.types[k + j']? = some t' ∧ st.pins[j']? = some q' ∧
    (∃ c ∈ t.ctors, (c.2.1).mentionsConst t'.name = true) ∧
    ¬ ((grp j).1 ≤ j' ∧ j' < (grp j).1 + (grp j).2) ∧
    ∀ (i : Nat) (g : NestedPin), i < (grp j).2 → st.pins[(grp j).1 + i]? = some g →
      ¬ Expr.Sub g.pin q'.pin

/-- The relation's targets are pins. -/
theorem CopyRef.target_lt {grp : Nat → Nat × Nat} {k : Nat} {st : ElimState} {j j' : Nat}
    (h : CopyRef grp k st j j') : j' < st.pins.length := by
  unfold CopyRef at h
  obtain ⟨t, t', q', h1, h2, h3, h4, h5, h6⟩ := h
  exact (List.getElem?_eq_some_iff.mp h3).1

/-! ## A topological order -/

/-- **A topological order of the copies** along `R`: a permutation of
`0 … n-1` in which every reference points to an EARLIER entry. -/
structure TopoOrder (R : Nat → Nat → Prop) (n : Nat) (order : List Nat) : Prop where
  nodup : order.Nodup
  complete : ∀ j, j < n → j ∈ order
  bounded : ∀ j ∈ order, j < n
  lt_of_ref : ∀ j j', R j j' → j' ∈ order ∧ order.idxOf j' < order.idxOf j

namespace TopoOrder

variable {R : Nat → Nat → Prop} {n : Nat} {order : List Nat}

/-- **What the fold consumes**: at position `i` of the order, every
reference of the copy there is among the first `i` entries — already
built when the fold reaches it. -/
theorem ref_mem_take (h : TopoOrder R n order) {i j j' : Nat}
    (hi : order[i]? = some j) (hR : R j j') : j' ∈ order.take i := by
  obtain ⟨hmem, hlt⟩ := h.lt_of_ref j j' hR
  obtain ⟨hilen, hij⟩ := List.getElem?_eq_some_iff.mp hi
  have hidx : order.idxOf j = i := by
    rw [← hij]
    exact h.nodup.idxOf_getElem i hilen
  rw [hidx] at hlt
  have hlt' : order.idxOf j' < order.length := List.idxOf_lt_length_iff.mpr hmem
  refine List.mem_of_getElem? (i := order.idxOf j') ?_
  rw [List.getElem?_take_of_lt hlt, List.getElem?_eq_getElem hlt', List.getElem_idxOf hlt']

end TopoOrder

end ConLeche
