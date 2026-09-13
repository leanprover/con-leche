module

public import ConLeche.Verify.Inductives.NestedLedger
public import ConLeche.Verify.Inductives.NestedOrderK

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

/-! ## The fold over the order

`ψ` is one term per copy, each built from the terms of the copies it
refers to.  Along a topological order that is a LEFT FOLD over the
list with a table of the terms built so far — no well-founded
recursion, no measure: `TopoOrder.ref_mem_take` says every reference
of the copy at position `i` is among the first `i` entries, which are
already in the table. -/

/-- The table after the order's entries, in order: entry `j` is
`step tbl j` at the table `tbl` the earlier entries left. -/
def orderFold {α : Type} (step : (Nat → α) → Nat → α) : List Nat → (Nat → α) → (Nat → α)
  | [], tbl => tbl
  | j :: rest, tbl => orderFold step rest (fun j' => if j' = j then step tbl j else tbl j')

/-- **The fold's invariant**: a per-entry property `P` that each step
establishes for its copy FROM the property at the copies it refers
to holds of every entry of the folded table.  Stated over a split
`pre ++ rest` of the order (the entries already folded and those to
come) for the induction; the caller takes `pre = []`. -/
theorem orderFold_spec {α : Type} {R : Nat → Nat → Prop} {n : Nat}
    (step : (Nat → α) → Nat → α) (P : Nat → α → Prop)
    (hstep : ∀ (tbl : Nat → α) (j : Nat), (∀ j', R j j' → P j' (tbl j')) → P j (step tbl j)) :
    ∀ {pre rest : List Nat} (tbl : Nat → α), TopoOrder R n (pre ++ rest) →
      (∀ j ∈ pre, P j (tbl j)) → ∀ j ∈ pre ++ rest, P j (orderFold step rest tbl j) := by
  intro pre rest
  induction rest generalizing pre with
  | nil =>
    intro tbl _ hpre j hj
    rw [List.append_nil] at hj
    exact hpre j hj
  | cons j₀ rest ih =>
    intro tbl h hpre
    have hsplit : pre ++ j₀ :: rest = (pre ++ [j₀]) ++ rest := by simp
    rw [hsplit] at h ⊢
    have hj₀ : (pre ++ [j₀] ++ rest)[pre.length]? = some j₀ := by
      rw [List.getElem?_append_left (by simp), List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hnotin : j₀ ∉ pre := by
      intro hmem
      have hnd := h.nodup
      rw [List.append_assoc, List.nodup_append] at hnd
      exact hnd.2.2 j₀ hmem j₀ (List.mem_append_left rest (List.mem_singleton.mpr rfl)) rfl
    show ∀ j ∈ pre ++ [j₀] ++ rest, P j (orderFold step rest (fun j' => if j' = j₀ then step tbl j₀ else tbl j') j)
    refine ih (pre := pre ++ [j₀]) _ h ?_
    intro j hj
    rw [List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · have hne : j ≠ j₀ := fun heq => hnotin (heq ▸ hj)
      simp only [hne, if_false]
      exact hpre j hj
    · simp only [if_true]
      refine hstep tbl j fun j' hR => ?_
      have hmem := h.ref_mem_take hj₀ hR
      rw [List.take_append_of_le_length (by simp), List.take_left' rfl] at hmem
      exact hpre j' hmem


/-! ## The bridge to the kernel's computation (task #279 K.6 / §M.24)

The kernel decides the relation (`copyRefB`, clause for clause) and
checks its emitted order against `topoOrderOk`, whose four conjuncts
are `TopoOrder`'s fields; `Verify/Inductives/NestedOrderK.lean` reads
them back at the `Bool` relation.  What closes the gap is ONE lemma —
`subB` decides `Sub`, hence `copyRefB` decides `CopyRef` — and then
`TopoOrder (CopyRef …) n order` is the four fields. -/

/-- **`subB` decides `Sub`.** -/
theorem Expr.subB_iff_Sub (pat : Expr) : ∀ (e : Expr), Expr.subB pat e = true ↔ Expr.Sub pat e := by
  intro e
  constructor
  · induction e with
    | app f a ihf iha =>
      intro h
      rcases subB_cases h with h | ⟨f', a', heq, h⟩ | ⟨_, _, _, heq, _⟩ | ⟨_, _, _, heq, _⟩ |
        ⟨_, _, _, heq, _⟩ | ⟨_, _, _, heq, _⟩
      · exact h ▸ .refl _
      · cases heq
        rcases h with h | h
        · exact .appF (ihf h)
        · exact .appA (iha h)
      all_goals exact nomatch heq
    | lam ty b m iht ihb =>
      intro h
      rcases subB_cases h with h | ⟨_, _, heq, _⟩ | ⟨_, _, _, heq, h⟩ | ⟨_, _, _, heq, _⟩ |
        ⟨_, _, _, heq, _⟩ | ⟨_, _, _, heq, _⟩
      · exact h ▸ .refl _
      · exact nomatch heq
      · cases heq
        rcases h with h | h
        · exact .lamT (iht h)
        · exact .lamB (ihb h)
      all_goals exact nomatch heq
    | forallE ty b m iht ihb =>
      intro h
      rcases subB_cases h with h | ⟨_, _, heq, _⟩ | ⟨_, _, _, heq, _⟩ | ⟨_, _, _, heq, h⟩ |
        ⟨_, _, _, heq, _⟩ | ⟨_, _, _, heq, _⟩
      · exact h ▸ .refl _
      · exact nomatch heq
      · exact nomatch heq
      · cases heq
        rcases h with h | h
        · exact .piT (iht h)
        · exact .piB (ihb h)
      all_goals exact nomatch heq
    | letE ty v b iht ihv ihb =>
      intro h
      rcases subB_cases h with h | ⟨_, _, heq, _⟩ | ⟨_, _, _, heq, _⟩ | ⟨_, _, _, heq, _⟩ |
        ⟨_, _, _, heq, h⟩ | ⟨_, _, _, heq, _⟩
      · exact h ▸ .refl _
      · exact nomatch heq
      · exact nomatch heq
      · exact nomatch heq
      · cases heq
        rcases h with h | h | h
        · exact .letT (iht h)
        · exact .letV (ihv h)
        · exact .letB (ihb h)
      · exact nomatch heq
    | proj s i x ihx =>
      intro h
      rcases subB_cases h with h | ⟨_, _, heq, _⟩ | ⟨_, _, _, heq, _⟩ | ⟨_, _, _, heq, _⟩ |
        ⟨_, _, _, heq, _⟩ | ⟨_, _, _, heq, h⟩
      · exact h ▸ .refl _
      · exact nomatch heq
      · exact nomatch heq
      · exact nomatch heq
      · exact nomatch heq
      · cases heq
        exact .proj (ihx h)
    | _ =>
      intro h
      rcases subB_cases h with h | ⟨_, _, heq, _⟩ | ⟨_, _, _, heq, _⟩ | ⟨_, _, _, heq, _⟩ |
        ⟨_, _, _, heq, _⟩ | ⟨_, _, _, heq, _⟩
      · exact h ▸ .refl _
      all_goals exact nomatch heq
  · intro h
    induction h with
    | refl => exact subB_self _
    | appF _ ih => exact subB_app_left ih
    | appA _ ih => exact subB_app_right ih
    | lamT _ ih => exact subB_lam_dom ih
    | lamB _ ih => exact subB_lam_body ih
    | piT _ ih => exact subB_pi_dom ih
    | piB _ ih => exact subB_pi_body ih
    | letT _ ih => exact subB_let_ty ih
    | letV _ ih => exact subB_let_val ih
    | letB _ ih => exact subB_let_body ih
    | proj _ ih => exact subB_proj ih

/-- **`copyRefB` decides `CopyRef`** — the lemma K.6 asked for. -/
theorem copyRef_iff (grp : Nat → Nat × Nat) (k : Nat) (st : ElimState) (j j' : Nat) :
    CopyRef grp k st j j' ↔ copyRefB grp k st j j' = true := by
  unfold CopyRef copyRefB
  cases h1 : st.types[k + j]? with
  | none => simp
  | some t =>
  cases h2 : st.types[k + j']? with
  | none => simp
  | some t' =>
  cases h3 : st.pins[j']? with
  | none => simp
  | some q' =>
  simp only [Option.some.injEq, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    List.mem_range]
  constructor
  · rintro ⟨t₁, t'₁, q'₁, rfl, rfl, rfl, hm, hg, hsub⟩
    refine ⟨⟨hm, by simp; omega⟩, fun i hi => ?_⟩
    cases hp : st.pins[(grp j).1 + i]? with
    | none => rfl
    | some g =>
      show (!Expr.subB g.pin q'.pin) = true
      cases hsb : Expr.subB g.pin q'.pin with
      | false => rfl
      | true => exact absurd ((Expr.subB_iff_Sub _ _).mp hsb) (hsub i g hi hp)
  · rintro ⟨⟨hm, hg⟩, hsub⟩
    refine ⟨t, t', q', rfl, rfl, rfl, hm, by simp at hg; intro h; omega, fun i g hi hp hs => ?_⟩
    have := hsub i hi
    rw [hp] at this
    change (!Expr.subB g.pin q'.pin) = true at this
    rw [(Expr.subB_iff_Sub _ _).mpr hs] at this
    exact absurd this (by decide)

/-- The relation's sources are pins too, given the ledger's count. -/
theorem CopyRef.source_lt {grp : Nat → Nat × Nat} {k : Nat} {st : ElimState} {j j' : Nat}
    (hlen : st.types.length = k + st.pins.length) (h : CopyRef grp k st j j') :
    j < st.pins.length := by
  unfold CopyRef at h
  obtain ⟨t, t', q', h1, -, -, -, -, -⟩ := h
  have := (List.getElem?_eq_some_iff.mp h1).1
  omega

/-- **The kernel's order is a `TopoOrder` along `CopyRef`** — the run
relation's conjunct (`nestedTopoOrder … = .ok order`), read through
`copyRef_iff` into the four fields. -/
theorem topoOrder_of_run {st : ElimState} {order : List Nat} {k : Nat}
    (hlen : st.types.length = k + st.pins.length)
    (h : nestedTopoOrder (ElimState.grp st) k st = .ok order) :
    TopoOrder (CopyRef (ElimState.grp st) k st) st.pins.length order :=
  ⟨nestedTopoOrder_nodup h, nestedTopoOrder_complete h, nestedTopoOrder_bounded h,
    fun _ _ hR => nestedTopoOrder_ref h (hR.source_lt hlen) hR.target_lt
      ((copyRef_iff _ _ _ _ _).mp hR)⟩

end ConLeche
