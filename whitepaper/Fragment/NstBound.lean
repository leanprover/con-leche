module

public import Fragment.Access

@[expose] public section

/-!
# SCAFFOLDING — the old inductive-closure law as a theorem (nested lane)

The fragment used to take the closed family of an inductive block
from a law, **inductive closure** (`IndLibCompat.lean`): for any list
of constructor telescopes some family of members of the universe is
closed under every bounded instance of every constructor.  That law
is now a **theorem** (`inductive_closure`, below), proved from the
accessibility theorem `closed_of_acc` (`Access.lean`): the operator
that collects the tagged tuples of the bounded instances is
accessible with a bound built along the telescopes, so it has a
closed family in the universe.

This file keeps the OLD telescopes of sets (`TeleS`, `TeleX`,
`TeleX.FitsB`) under the namespace `Fragment.IndSpec.Nst`, for the NESTED lane
of the fragment, which still consumes the old construction.  It is
scaffolding: when the nested lane is ported onto the new operators it
goes.

**The operator** `op n cs` sends a family `W` to the family whose
fibre at `i` is the set of `tag j (tuple fs)` over all constructors
`cs[j] = (t, tgt)` and all values `fs` fitting `t` relative to `W`
(`FitsB`) with `tgt fs = i`; it is built as a set by recursion on the
telescope with `famUnion`, guarded by the universe conditions `FitsB`
demands (`ctorSet`, `mem_ctorSet`, `mem_op`).

**The bound** `bnd n t` is built along the telescope: an `ord` field
glues the rest's bound over its (small) domain, a `recur` field
contributes one code, a `refl` field the set of tuples of values
fitting its telescope (`fitSet`); the two parts are kept apart by
`pcons` with distinct first components.  **The support** of an element
`tag j (tuple fs)` is the relation `Supp t fs` from codes to
occurrences: a `recur` value `(i, v)` at its one code, and for a `refl`
field `f` the occurrences `(tgt ys, f ys)` for every fitting `ys` at
the code `tuple ys`.  The four facts about it — a code of the support
lies in the bound (`Supp_mem_bnd`), a code has one occurrence
(`Supp_fun`), the support lies in `W` (`Supp_inFam`), and the instance
fits every family containing the support (`FitsB_of_Supp`, through
the re-typing lemma `mem_pi_of_appN`) — are accessibility
(`op_acc`).
-/

namespace Fragment.IndSpec.Nst
open SetLib UnivLib IndLib

universe u

/-! ## Telescopes of sets and constructor telescopes -/

/-- A dependent telescope of sets, outermost first: each set may
depend on the values of the earlier ones. -/
inductive TeleS (V : Type u) : Type u where
  /-- The empty telescope. -/
  | nil : TeleS V
  /-- A set, then a telescope depending on a member of it. -/
  | cons (A : V) (B : V → TeleS V) : TeleS V

namespace TeleS

variable {V : Type u} [SetLib V]

/-- Values fitting a telescope (outermost first). -/
def Fits : TeleS V → List V → Prop
  | nil, [] => True
  | cons A B, v :: vs => v ∈ˢ A ∧ Fits (B v) vs
  | _, _ => False

/-- The nested function space over a telescope, into fibres indexed by
the values. -/
def pi : TeleS V → (List V → V) → V
  | nil, F => F []
  | cons A B, F => piSet A fun v => pi (B v) fun vs => F (v :: vs)

/-- Every set met along fitting values is a member of `univ n`. -/
def Bounded (n : Nat) : TeleS V → Prop
  | nil => True
  | cons A B => A ∈ˢ univ n ∧ ∀ v, v ∈ˢ A → Bounded n (B v)

end TeleS

/-- **A constructor telescope** relative to a family over an index
type `ι`, outermost first: an *ordinary* field with a domain, the rest
depending on its value; a field *in the family* at an index (`recur`:
what a container field, and the member field of a container, is read
as); a field that is a *function* from a telescope of sets into the
family at targets depending on the arguments (`refl`: a reflexive
field of the block, with the empty telescope when it is recursive).
After either the rest does not depend on the value (con-leche's
`structUsedLater` guard run by `nestCtors`, `Positivity.lean:1247`). -/
inductive TeleX (ι : Type u) (V : Type u) : Type u where
  /-- No more fields. -/
  | nil : TeleX ι V
  /-- An ordinary field. -/
  | ord (A : V) (rest : V → TeleX ι V) : TeleX ι V
  /-- A field in the family at `i`. -/
  | recur (i : ι) (rest : TeleX ι V) : TeleX ι V
  /-- A field that is a function over `tele` into the family at `tgt`
  of the arguments (a reflexive field). -/
  | refl (tele : TeleS V) (tgt : List V → ι) (rest : TeleX ι V) : TeleX ι V

namespace TeleX

variable {ι : Type u} {V : Type u} [SetLib V]

/-- **A bounded instance** of a constructor telescope relative to a
family `W`: values (outermost first) fitting it, every domain met a
member of `univ n`, `recur` values in `W` at their index, `refl`
values in the function space into `W` at the targets. -/
def FitsB (n : Nat) (W : ι → V) : TeleX ι V → List V → Prop
  | nil, [] => True
  | ord A rest, v :: vs => A ∈ˢ univ n ∧ v ∈ˢ A ∧ FitsB n W (rest v) vs
  | recur i rest, v :: vs => v ∈ˢ W i ∧ FitsB n W rest vs
  | refl tele tgt rest, v :: vs =>
    tele.Bounded n ∧ v ∈ˢ tele.pi (fun ys => W (tgt ys)) ∧ FitsB n W rest vs
  | _, _ => False

end TeleX

/-! ## Telescopes of sets: application, fitting values, re-typing -/

section TeleS

variable {V : Type u} [IndLib V]

/-- Iterated application of a function along a list of arguments. -/
def appN : V → List V → V
  | f, [] => f
  | f, y :: ys => appN (app f y) ys

/-- A member of the function space over a telescope, applied along
fitting values, lands in the fibre at those values. -/
theorem appN_mem_pi : ∀ (tele : TeleS V) {F : List V → V} {f : V} {ys : List V},
    f ∈ˢ tele.pi F → tele.Fits ys → appN f ys ∈ˢ F ys
  | .nil, _, _, [], hf, _ => hf
  | .nil, _, _, _ :: _, _, hys => hys.elim
  | .cons _ _, _, _, [], _, hys => hys.elim
  | .cons _ B, F, _, y :: _, hf, hys =>
    appN_mem_pi (B y) (F := fun vs => F (y :: vs)) (app_mem_piSet hf hys.1) hys.2

/-- **Re-typing**: a member of the function space over a telescope
whose applications along fitting values all lie in other fibres is a
member of the space into those fibres — by η and introduction, level
by level. -/
theorem mem_pi_of_appN : ∀ (tele : TeleS V) {F F' : List V → V} {f : V},
    f ∈ˢ tele.pi F → (∀ ys, tele.Fits ys → appN f ys ∈ˢ F' ys) → f ∈ˢ tele.pi F'
  | .nil, _, _, _, _, h => h [] trivial
  | .cons A B, F, F', f, hf, h => by
    simp only [TeleS.pi] at hf ⊢
    rw [← graph_app_eq hf]
    refine graph_mem_piSet fun x hx => ?_
    exact mem_pi_of_appN (B x) (app_mem_piSet hf hx) fun ys hys => h (x :: ys) ⟨hx, hys⟩

/-- The values fitting a bounded telescope are members of the
universe. -/
theorem TeleS.Fits.mem_univ {n : Nat} (hn : n ≠ 0) :
    ∀ {tele : TeleS V} {ys : List V}, tele.Bounded n → tele.Fits ys →
      ∀ y, y ∈ ys → y ∈ˢ (univ n : V)
  | .nil, [], _, _, _, hy => (List.not_mem_nil hy).elim
  | .nil, _ :: _, _, hys, _, _ => hys.elim
  | .cons _ _, [], _, hys, _, _ => hys.elim
  | .cons A B, y :: ys, hb, hys, z, hz => by
    rcases List.mem_cons.mp hz with rfl | hz
    · exact univ_trans hn hb.1 hys.1
    · exact TeleS.Fits.mem_univ hn (hb.2 y hys.1) hys.2 z hz

/-- The function space over a bounded telescope into fibres in the
universe is a member of the universe. -/
theorem TeleS.pi_mem_univ {n : Nat} (hn : n ≠ 0) :
    ∀ (tele : TeleS V) (F : List V → V), tele.Bounded n →
      (∀ ys, tele.Fits ys → F ys ∈ˢ (univ n : V)) → tele.pi F ∈ˢ (univ n : V)
  | .nil, _, _, hF => hF [] trivial
  | .cons _ B, _, hb, hF =>
    piSet_mem_univ hn hb.1 fun v hv =>
      TeleS.pi_mem_univ hn (B v) _ (hb.2 v hv) fun ys hys => hF (v :: ys) ⟨hv, hys⟩

/-- **The codes of the fitting values** of a telescope: the set of
`k ys` over the `ys` fitting it (used with `k = tuple`), built with
`famUnion` along the telescope. -/
noncomputable def fitSet : TeleS V → (List V → V) → V
  | .nil, k => sing (k [])
  | .cons A B, k => famUnion A fun v => fitSet (B v) fun ys => k (v :: ys)

theorem mem_fitSet : ∀ (tele : TeleS V) (k : List V → V) {z : V},
    z ∈ˢ fitSet tele k ↔ ∃ ys, tele.Fits ys ∧ z = k ys
  | .nil, k, z => by
    simp only [fitSet, mem_sing]
    constructor
    · intro h; exact ⟨[], trivial, h⟩
    · rintro ⟨ys, hys, h⟩
      cases ys with
      | nil => exact h
      | cons _ _ => exact hys.elim
  | .cons A B, k, z => by
    simp only [fitSet, mem_famUnion]
    constructor
    · rintro ⟨v, hv, h⟩
      obtain ⟨ys, hys, rfl⟩ := (mem_fitSet (B v) _).mp h
      exact ⟨v :: ys, ⟨hv, hys⟩, rfl⟩
    · rintro ⟨ys, hys, rfl⟩
      cases ys with
      | nil => exact hys.elim
      | cons v ys => exact ⟨v, hys.1, (mem_fitSet (B v) _).mpr ⟨ys, hys.2, rfl⟩⟩

theorem fitSet_mem_univ {n : Nat} (hn : n ≠ 0) :
    ∀ (tele : TeleS V) (k : List V → V), tele.Bounded n →
      (∀ ys, tele.Fits ys → k ys ∈ˢ (univ n : V)) → fitSet tele k ∈ˢ (univ n : V)
  | .nil, _, _, hk => sing_mem_univ hn (hk [] trivial)
  | .cons _ B, _, hb, hk =>
    famUnion_mem_univ hn hb.1 fun v hv =>
      fitSet_mem_univ hn (B v) _ (hb.2 v hv) fun ys hys => hk (v :: ys) ⟨hv, hys⟩

end TeleS

/-! ## The operator -/

section Op

variable {V : Type u} [IndLib V] {ι : Type u}

open Classical in
/-- **The set of a constructor telescope's instances**, with a
continuation: the set of `k fs` over the values `fs` fitting the
telescope relative to `W`.  A `famUnion` over the domain at every
field, guarded by the universe conditions `FitsB` demands (an `ord`
domain in the universe, a `refl` telescope bounded) so that the set is
in the universe. -/
noncomputable def ctorSet (n : Nat) (W : ι → V) : TeleX ι V → (List V → V) → V
  | .nil, k => k []
  | .ord A rest, k =>
    if A ∈ˢ (univ n : V) then famUnion A fun v => ctorSet n W (rest v) fun vs => k (v :: vs)
    else empty
  | .recur i rest, k => famUnion (W i) fun v => ctorSet n W rest fun vs => k (v :: vs)
  | .refl tele tgt rest, k =>
    if tele.Bounded n then
      famUnion (tele.pi fun ys => W (tgt ys)) fun v => ctorSet n W rest fun vs => k (v :: vs)
    else empty

theorem mem_ctorSet {n : Nat} {W : ι → V} : ∀ (t : TeleX ι V) (k : List V → V) {x : V},
    x ∈ˢ ctorSet n W t k ↔ ∃ fs, TeleX.FitsB n W t fs ∧ x ∈ˢ k fs
  | .nil, k, x => by
    simp only [ctorSet]
    constructor
    · intro h; exact ⟨[], trivial, h⟩
    · rintro ⟨fs, hfs, h⟩
      cases fs with
      | nil => exact h
      | cons _ _ => exact hfs.elim
  | .ord A rest, k, x => by
    simp only [ctorSet]
    by_cases hA : A ∈ˢ (univ n : V)
    · rw [if_pos hA, mem_famUnion]
      constructor
      · rintro ⟨v, hv, h⟩
        obtain ⟨vs, hvs, hx⟩ := (mem_ctorSet (rest v) _).mp h
        exact ⟨v :: vs, ⟨hA, hv, hvs⟩, hx⟩
      · rintro ⟨fs, hfs, hx⟩
        cases fs with
        | nil => exact hfs.elim
        | cons v vs => exact ⟨v, hfs.2.1, (mem_ctorSet (rest v) _).mpr ⟨vs, hfs.2.2, hx⟩⟩
    · rw [if_neg hA]
      constructor
      · intro h; exact absurd h (not_mem_empty x)
      · rintro ⟨fs, hfs, -⟩
        cases fs with
        | nil => exact hfs.elim
        | cons v vs => exact absurd hfs.1 hA
  | .recur i rest, k, x => by
    simp only [ctorSet]
    rw [mem_famUnion]
    constructor
    · rintro ⟨v, hv, h⟩
      obtain ⟨vs, hvs, hx⟩ := (mem_ctorSet rest _).mp h
      exact ⟨v :: vs, ⟨hv, hvs⟩, hx⟩
    · rintro ⟨fs, hfs, hx⟩
      cases fs with
      | nil => exact hfs.elim
      | cons v vs => exact ⟨v, hfs.1, (mem_ctorSet rest _).mpr ⟨vs, hfs.2, hx⟩⟩
  | .refl tele tgt rest, k, x => by
    simp only [ctorSet]
    by_cases hb : tele.Bounded n
    · rw [if_pos hb, mem_famUnion]
      constructor
      · rintro ⟨v, hv, h⟩
        obtain ⟨vs, hvs, hx⟩ := (mem_ctorSet rest _).mp h
        exact ⟨v :: vs, ⟨hb, hv, hvs⟩, hx⟩
      · rintro ⟨fs, hfs, hx⟩
        cases fs with
        | nil => exact hfs.elim
        | cons v vs => exact ⟨v, hfs.2.1, (mem_ctorSet rest _).mpr ⟨vs, hfs.2.2, hx⟩⟩
    · rw [if_neg hb]
      constructor
      · intro h; exact absurd h (not_mem_empty x)
      · rintro ⟨fs, hfs, -⟩
        cases fs with
        | nil => exact hfs.elim
        | cons v vs => exact absurd hfs.1 hb

/-- The values of a bounded instance are members of the universe. -/
theorem TeleX.FitsB.mem_univ {n : Nat} {W : ι → V} (hn : n ≠ 0) (hW : InUniv n W) :
    ∀ {t : TeleX ι V} {fs : List V}, TeleX.FitsB n W t fs → ∀ x, x ∈ fs → x ∈ˢ (univ n : V)
  | .nil, [], _, _, hx => (List.not_mem_nil hx).elim
  | .nil, _ :: _, hfs, _, _ => hfs.elim
  | .ord _ _, [], hfs, _, _ => hfs.elim
  | .ord A rest, v :: vs, hfs, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact univ_trans hn hfs.1 hfs.2.1
    · exact TeleX.FitsB.mem_univ hn hW hfs.2.2 x hx
  | .recur _ _, [], hfs, _, _ => hfs.elim
  | .recur i rest, v :: vs, hfs, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact univ_trans hn (hW i) hfs.1
    · exact TeleX.FitsB.mem_univ hn hW hfs.2 x hx
  | .refl _ _ _, [], hfs, _, _ => hfs.elim
  | .refl tele tgt rest, v :: vs, hfs, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact univ_trans hn (TeleS.pi_mem_univ hn tele _ hfs.1 fun ys _ => hW (tgt ys)) hfs.2.1
    · exact TeleX.FitsB.mem_univ hn hW hfs.2.2 x hx

theorem ctorSet_mem_univ {n : Nat} {W : ι → V} (hn : n ≠ 0) (hW : InUniv n W) :
    ∀ (t : TeleX ι V) (k : List V → V),
      (∀ fs, TeleX.FitsB n W t fs → k fs ∈ˢ (univ n : V)) → ctorSet n W t k ∈ˢ (univ n : V)
  | .nil, _, hk => hk [] trivial
  | .ord A rest, k, hk => by
    simp only [ctorSet]
    by_cases hA : A ∈ˢ (univ n : V)
    · rw [if_pos hA]
      exact famUnion_mem_univ hn hA fun v hv =>
        ctorSet_mem_univ hn hW (rest v) _ fun vs hvs => hk (v :: vs) ⟨hA, hv, hvs⟩
    · rw [if_neg hA]; exact empty_mem_univ n
  | .recur i rest, k, hk => by
    simp only [ctorSet]
    exact famUnion_mem_univ hn (hW i) fun v hv =>
      ctorSet_mem_univ hn hW rest _ fun vs hvs => hk (v :: vs) ⟨hv, hvs⟩
  | .refl tele tgt rest, k, hk => by
    simp only [ctorSet]
    by_cases hb : tele.Bounded n
    · rw [if_pos hb]
      exact famUnion_mem_univ hn (TeleS.pi_mem_univ hn tele _ hb fun ys _ => hW (tgt ys))
        fun v hv => ctorSet_mem_univ hn hW rest _ fun vs hvs => hk (v :: vs) ⟨hb, hv, hvs⟩
    · rw [if_neg hb]; exact empty_mem_univ n

open Classical in
/-- The fibre at `i` of one constructor with tag `j`: the tagged
tuples of its instances whose target is `i`. -/
noncomputable def ctorFibre (n : Nat) (W : ι → V) (j : Nat) (c : TeleX ι V × (List V → ι))
    (i : ι) : V :=
  ctorSet n W c.1 fun fs => if c.2 fs = i then sing (tag j (tuple fs)) else empty

theorem mem_ctorFibre {n : Nat} {W : ι → V} {j : Nat} {c : TeleX ι V × (List V → ι)} {i : ι}
    {x : V} : x ∈ˢ ctorFibre n W j c i ↔
      ∃ fs, TeleX.FitsB n W c.1 fs ∧ c.2 fs = i ∧ x = tag j (tuple fs) := by
  unfold ctorFibre
  rw [mem_ctorSet]
  constructor
  · rintro ⟨fs, hfs, hx⟩
    by_cases hi : c.2 fs = i
    · rw [if_pos hi, mem_sing] at hx; exact ⟨fs, hfs, hi, hx⟩
    · rw [if_neg hi] at hx; exact absurd hx (not_mem_empty x)
  · rintro ⟨fs, hfs, hi, rfl⟩
    exact ⟨fs, hfs, by rw [if_pos hi]; exact mem_sing.mpr rfl⟩

theorem ctorFibre_mem_univ {n : Nat} {W : ι → V} (hn : n ≠ 0) (hW : InUniv n W) (j : Nat)
    (c : TeleX ι V × (List V → ι)) (i : ι) : ctorFibre n W j c i ∈ˢ (univ n : V) := by
  refine ctorSet_mem_univ hn hW _ _ fun fs hfs => ?_
  by_cases hi : c.2 fs = i
  · rw [if_pos hi]
    exact sing_mem_univ hn (tag_mem_univ hn (tuple_mem_univ hn (hfs.mem_univ hn hW)))
  · rw [if_neg hi]; exact empty_mem_univ n

/-- The fibres of the constructors from tag `j` on, united. -/
noncomputable def opFrom (n : Nat) (W : ι → V) :
    Nat → List (TeleX ι V × (List V → ι)) → ι → V
  | _, [], _ => empty
  | j, c :: cs, i => binUnion (ctorFibre n W j c i) (opFrom n W (j + 1) cs i)

/-- **The operator of a list of constructor telescopes**: the fibre at
`i` collects the tagged tuples `tag j (tuple fs)` of the instances
`fs` of the constructor `cs[j]` relative to `W` whose target is `i`. -/
noncomputable def op (n : Nat) (cs : List (TeleX ι V × (List V → ι))) (W : ι → V) : ι → V :=
  opFrom n W 0 cs

theorem mem_opFrom {n : Nat} {W : ι → V} :
    ∀ (j₀ : Nat) (cs : List (TeleX ι V × (List V → ι))) {i : ι} {x : V},
      x ∈ˢ opFrom n W j₀ cs i ↔
        ∃ (j : Nat) (c : TeleX ι V × (List V → ι)) (fs : List V), cs[j]? = some c ∧
          TeleX.FitsB n W c.1 fs ∧ c.2 fs = i ∧ x = tag (j₀ + j) (tuple fs)
  | _, [], i, x => by
    simp only [opFrom, List.getElem?_nil]
    constructor
    · intro h; exact absurd h (not_mem_empty x)
    · rintro ⟨_, _, _, h, -⟩; exact nomatch h
  | j₀, c :: cs, i, x => by
    simp only [opFrom]
    rw [mem_binUnion, mem_ctorFibre, mem_opFrom (j₀ + 1) cs]
    constructor
    · rintro (⟨fs, hfs, hi, hx⟩ | ⟨j, c', fs, hj, hfs, hi, hx⟩)
      · exact ⟨0, c, fs, rfl, hfs, hi, hx⟩
      · exact ⟨j + 1, c', fs, by rw [List.getElem?_cons_succ]; exact hj, hfs, hi, by
          rw [show j₀ + (j + 1) = j₀ + 1 + j by omega]; exact hx⟩
    · rintro ⟨j, c', fs, hj, hfs, hi, hx⟩
      cases j with
      | zero =>
        rw [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        exact Or.inl ⟨fs, hfs, hi, hx⟩
      | succ j =>
        rw [List.getElem?_cons_succ] at hj
        exact Or.inr ⟨j, c', fs, hj, hfs, hi, by
          rw [show j₀ + 1 + j = j₀ + (j + 1) by omega]; exact hx⟩

/-- **The members of the operator's fibre**: the tagged tuples of the
bounded instances with that target. -/
theorem mem_op {n : Nat} {cs : List (TeleX ι V × (List V → ι))} {W : ι → V} {i : ι} {x : V} :
    x ∈ˢ op n cs W i ↔
      ∃ (j : Nat) (c : TeleX ι V × (List V → ι)) (fs : List V), cs[j]? = some c ∧
        TeleX.FitsB n W c.1 fs ∧ c.2 fs = i ∧ x = tag j (tuple fs) := by
  unfold op
  rw [mem_opFrom]
  simp only [Nat.zero_add]

theorem opFrom_mem_univ {n : Nat} {W : ι → V} (hn : n ≠ 0) (hW : InUniv n W) :
    ∀ (j₀ : Nat) (cs : List (TeleX ι V × (List V → ι))) (i : ι),
      opFrom n W j₀ cs i ∈ˢ (univ n : V)
  | _, [], _ => empty_mem_univ n
  | j₀, c :: cs, i =>
    binUnion_mem_univ hn (ctorFibre_mem_univ hn hW j₀ c i) (opFrom_mem_univ hn hW (j₀ + 1) cs i)

/-- The operator maps families in the universe to families in the
universe. -/
theorem op_maps {n : Nat} (hn : n ≠ 0) (cs : List (TeleX ι V × (List V → ι))) :
    MapsFam n (op n cs) := fun _ hW i => opFrom_mem_univ hn hW 0 cs i

end Op

/-! ## The bound and the support -/

section Bound

variable {V : Type u} [IndLib V] {ι : Type u}

theorem nat_mem_univ {n : Nat} (hn : n ≠ 0) (k : Nat) : (nat k : V) ∈ˢ univ n :=
  univ_trans hn (omega_mem_univ hn) (mem_omega.mpr ⟨k, rfl⟩)

theorem pt_mem_univ {n : Nat} (hn : n ≠ 0) : (pt : V) ∈ˢ univ n :=
  univ_trans hn (one_mem_univ n) (mem_one.mpr rfl)

open Classical in
/-- **The bound of a constructor telescope**: the codes of the
occurrences any instance's support can use.  An `ord` field glues the
rest's bound over its domain (a code is `pcons v b`, `v` in the
domain, `b` in the rest's bound at `v`); a `recur` field has the one
code `pcons (nat 0) pt`; a `refl` field has the codes
`pcons (nat 0) (tuple ys)` for the `ys` fitting its telescope; after
either, the rest's codes are tagged apart as `pcons (nat 1) b`.
Guarded like `ctorSet`, so that the bound is in the universe. -/
noncomputable def bnd (n : Nat) : TeleX ι V → V
  | .nil => empty
  | .ord A rest =>
    if A ∈ˢ (univ n : V) then famUnion A fun v => image (pcons v) (bnd n (rest v)) else empty
  | .recur _ rest => binUnion (sing (pcons (nat 0) pt)) (image (pcons (nat 1)) (bnd n rest))
  | .refl tele _ rest =>
    if tele.Bounded n then
      binUnion (image (pcons (nat 0)) (fitSet tele tuple)) (image (pcons (nat 1)) (bnd n rest))
    else empty

theorem bnd_mem_univ {n : Nat} (hn : n ≠ 0) : ∀ t : TeleX ι V, bnd n t ∈ˢ (univ n : V)
  | .nil => empty_mem_univ n
  | .ord A rest => by
    simp only [bnd]
    by_cases hA : A ∈ˢ (univ n : V)
    · rw [if_pos hA]
      exact famUnion_mem_univ hn hA fun v hv =>
        image_mem_univ hn (bnd_mem_univ hn (rest v)) fun b hb =>
          pcons_mem_univ hn (univ_trans hn hA hv) (univ_trans hn (bnd_mem_univ hn (rest v)) hb)
    · rw [if_neg hA]; exact empty_mem_univ n
  | .recur _ rest => by
    simp only [bnd]
    refine binUnion_mem_univ hn (sing_mem_univ hn (pcons_mem_univ hn (nat_mem_univ hn 0)
      (pt_mem_univ hn))) ?_
    exact image_mem_univ hn (bnd_mem_univ hn rest) fun b hb =>
      pcons_mem_univ hn (nat_mem_univ hn 1) (univ_trans hn (bnd_mem_univ hn rest) hb)
  | .refl tele _ rest => by
    simp only [bnd]
    by_cases hb : tele.Bounded n
    · rw [if_pos hb]
      have hfit : fitSet tele tuple ∈ˢ (univ n : V) :=
        fitSet_mem_univ hn tele _ hb fun ys hys => tuple_mem_univ hn (hys.mem_univ hn hb)
      refine binUnion_mem_univ hn ?_ ?_
      · exact image_mem_univ hn hfit fun z hz =>
          pcons_mem_univ hn (nat_mem_univ hn 0) (univ_trans hn hfit hz)
      · exact image_mem_univ hn (bnd_mem_univ hn rest) fun b hb =>
          pcons_mem_univ hn (nat_mem_univ hn 1) (univ_trans hn (bnd_mem_univ hn rest) hb)
    · rw [if_neg hb]; exact empty_mem_univ n

/-- The bound of a list of constructor telescopes: the union of the
bounds. -/
noncomputable def bndList (n : Nat) : List (TeleX ι V × (List V → ι)) → V
  | [] => empty
  | c :: cs => binUnion (bnd n c.1) (bndList n cs)

theorem bndList_mem_univ {n : Nat} (hn : n ≠ 0) :
    ∀ cs : List (TeleX ι V × (List V → ι)), bndList n cs ∈ˢ (univ n : V)
  | [] => empty_mem_univ n
  | c :: cs => binUnion_mem_univ hn (bnd_mem_univ hn c.1) (bndList_mem_univ hn cs)

theorem bnd_sub_bndList {n : Nat} {c : TeleX ι V × (List V → ι)} :
    ∀ {cs : List (TeleX ι V × (List V → ι))}, c ∈ cs → bnd n c.1 ⊆ˢ bndList n cs
  | [], h => (List.not_mem_nil h).elim
  | c' :: cs, h => by
    simp only [bndList]
    rcases List.mem_cons.mp h with rfl | h
    · exact fun a ha => mem_binUnion.mpr (Or.inl ha)
    · exact fun a ha => mem_binUnion.mpr (Or.inr (bnd_sub_bndList h a ha))

/-- **The support of an instance**: the relation from codes to
occurrences `(index, value)` of the family the instance uses — a
`recur` value at the code `pcons (nat 0) pt`, a `refl` value `f`
applied along every fitting `ys` at the code `pcons (nat 0) (tuple ys)`,
the rest's support behind `pcons v` (`ord`) or `pcons (nat 1)`
(`recur`, `refl`). -/
def Supp : TeleX ι V → List V → V → ι × V → Prop
  | .ord _ rest, v :: vs, a, o => ∃ b, a = pcons v b ∧ Supp (rest v) vs b o
  | .recur i rest, v :: vs, a, o =>
    (a = pcons (nat 0) pt ∧ o = (i, v)) ∨ ∃ b, a = pcons (nat 1) b ∧ Supp rest vs b o
  | .refl tele tgt rest, v :: vs, a, o =>
    (∃ ys, tele.Fits ys ∧ a = pcons (nat 0) (tuple ys) ∧ o = (tgt ys, appN v ys)) ∨
      ∃ b, a = pcons (nat 1) b ∧ Supp rest vs b o
  | _, _, _, _ => False

theorem nat_zero_ne_one : (nat 0 : V) ≠ nat 1 := fun h => Nat.zero_ne_one (nat_inj h)

/-- A code of the support of a bounded instance lies in the bound. -/
theorem Supp_mem_bnd {n : Nat} {W : ι → V} :
    ∀ {t : TeleX ι V} {fs : List V} {a : V} {o : ι × V},
      TeleX.FitsB n W t fs → Supp t fs a o → a ∈ˢ bnd n t
  | .nil, [], _, _, _, h => h.elim
  | .nil, _ :: _, _, _, hfs, _ => hfs.elim
  | .ord _ _, [], _, _, hfs, _ => hfs.elim
  | .ord A rest, v :: vs, a, o, hfs, h => by
    obtain ⟨b, rfl, hb⟩ := h
    simp only [bnd]
    rw [if_pos hfs.1, mem_famUnion]
    exact ⟨v, hfs.2.1, mem_image.mpr ⟨b, Supp_mem_bnd hfs.2.2 hb, rfl⟩⟩
  | .recur _ _, [], _, _, hfs, _ => hfs.elim
  | .recur i rest, v :: vs, a, o, hfs, h => by
    simp only [bnd]
    rw [mem_binUnion]
    rcases h with ⟨rfl, -⟩ | ⟨b, rfl, hb⟩
    · exact Or.inl (mem_sing.mpr rfl)
    · exact Or.inr (mem_image.mpr ⟨b, Supp_mem_bnd hfs.2 hb, rfl⟩)
  | .refl _ _ _, [], _, _, hfs, _ => hfs.elim
  | .refl tele tgt rest, v :: vs, a, o, hfs, h => by
    simp only [bnd]
    rw [if_pos hfs.1, mem_binUnion]
    rcases h with ⟨ys, hys, rfl, -⟩ | ⟨b, rfl, hb⟩
    · exact Or.inl (mem_image.mpr ⟨tuple ys, (mem_fitSet tele _).mpr ⟨ys, hys, rfl⟩, rfl⟩)
    · exact Or.inr (mem_image.mpr ⟨b, Supp_mem_bnd hfs.2.2 hb, rfl⟩)

/-- A code has at most one occurrence: the codes are injective. -/
theorem Supp_fun : ∀ {t : TeleX ι V} {fs : List V} {a : V} {o o' : ι × V},
    Supp t fs a o → Supp t fs a o' → o = o'
  | .nil, [], _, _, _, h, _ => h.elim
  | .nil, _ :: _, _, _, _, h, _ => h.elim
  | .ord _ _, [], _, _, _, h, _ => h.elim
  | .ord A rest, v :: vs, a, o, o', h, h' => by
    obtain ⟨b, rfl, hb⟩ := h
    obtain ⟨b', hb'e, hb'⟩ := h'
    obtain ⟨-, rfl⟩ := pcons_inj hb'e
    exact Supp_fun hb hb'
  | .recur _ _, [], _, _, _, h, _ => h.elim
  | .recur i rest, v :: vs, a, o, o', h, h' => by
    rcases h with ⟨rfl, rfl⟩ | ⟨b, rfl, hb⟩
    · rcases h' with ⟨-, rfl⟩ | ⟨b', hb'e, -⟩
      · rfl
      · exact absurd (pcons_inj hb'e).1 nat_zero_ne_one
    · rcases h' with ⟨hb'e, -⟩ | ⟨b', hb'e, hb'⟩
      · exact absurd (pcons_inj hb'e).1 nat_zero_ne_one.symm
      · obtain ⟨-, rfl⟩ := pcons_inj hb'e
        exact Supp_fun hb hb'
  | .refl _ _ _, [], _, _, _, h, _ => h.elim
  | .refl tele tgt rest, v :: vs, a, o, o', h, h' => by
    rcases h with ⟨ys, -, rfl, rfl⟩ | ⟨b, rfl, hb⟩
    · rcases h' with ⟨ys', -, hys'e, rfl⟩ | ⟨b', hb'e, -⟩
      · obtain ⟨-, hys⟩ := pcons_inj hys'e
        rw [tuple_inj hys]
      · exact absurd (pcons_inj hb'e).1 nat_zero_ne_one
    · rcases h' with ⟨ys', -, hb'e, -⟩ | ⟨b', hb'e, hb'⟩
      · exact absurd (pcons_inj hb'e).1 nat_zero_ne_one.symm
      · obtain ⟨-, rfl⟩ := pcons_inj hb'e
        exact Supp_fun hb hb'

/-- The support of a bounded instance relative to `W` lies in `W`. -/
theorem Supp_inFam {n : Nat} {W : ι → V} :
    ∀ {t : TeleX ι V} {fs : List V} {a : V} {o : ι × V},
      TeleX.FitsB n W t fs → Supp t fs a o → InFam W o
  | .nil, [], _, _, _, h => h.elim
  | .nil, _ :: _, _, _, hfs, _ => hfs.elim
  | .ord _ _, [], _, _, hfs, _ => hfs.elim
  | .ord A rest, v :: vs, a, o, hfs, h => by
    obtain ⟨b, -, hb⟩ := h
    exact Supp_inFam hfs.2.2 hb
  | .recur _ _, [], _, _, hfs, _ => hfs.elim
  | .recur i rest, v :: vs, a, o, hfs, h => by
    rcases h with ⟨-, rfl⟩ | ⟨b, -, hb⟩
    · exact hfs.1
    · exact Supp_inFam hfs.2 hb
  | .refl _ _ _, [], _, _, hfs, _ => hfs.elim
  | .refl tele tgt rest, v :: vs, a, o, hfs, h => by
    rcases h with ⟨ys, hys, -, rfl⟩ | ⟨b, -, hb⟩
    · exact appN_mem_pi tele hfs.2.1 hys
    · exact Supp_inFam hfs.2.2 hb

/-- **An instance fits every family containing its support**: the
domains and the `ord` values are unchanged, a `recur` value is the
occurrence at its code, a `refl` value is re-typed into the function
space over the new family from its applications (`mem_pi_of_appN`). -/
theorem FitsB_of_Supp {n : Nat} {W W' : ι → V} :
    ∀ {t : TeleX ι V} {fs : List V}, TeleX.FitsB n W t fs →
      (∀ a o, Supp t fs a o → InFam W' o) → TeleX.FitsB n W' t fs
  | .nil, [], _, _ => trivial
  | .nil, _ :: _, hfs, _ => hfs.elim
  | .ord _ _, [], hfs, _ => hfs.elim
  | .ord _ _, v :: _, hfs, h =>
    ⟨hfs.1, hfs.2.1, FitsB_of_Supp hfs.2.2 fun b o hb => h (pcons v b) o ⟨b, rfl, hb⟩⟩
  | .recur _ _, [], hfs, _ => hfs.elim
  | .recur i _, v :: _, hfs, h =>
    ⟨h (pcons (nat 0) pt) (i, v) (Or.inl ⟨rfl, rfl⟩),
      FitsB_of_Supp hfs.2 fun b o hb => h (pcons (nat 1) b) o (Or.inr ⟨b, rfl, hb⟩)⟩
  | .refl _ _ _, [], hfs, _ => hfs.elim
  | .refl tele tgt _, v :: _, hfs, h =>
    ⟨hfs.1,
      mem_pi_of_appN tele hfs.2.1 fun ys hys =>
        h (pcons (nat 0) (tuple ys)) (tgt ys, appN v ys) (Or.inl ⟨ys, hys, rfl, rfl⟩),
      FitsB_of_Supp hfs.2.2 fun b o hb => h (pcons (nat 1) b) o (Or.inr ⟨b, rfl, hb⟩)⟩

/-- **The operator is accessible** with the bound of the list: an
element `tag j (tuple fs)` of a fibre has the support `Supp c.1 fs`,
indexed by codes in `bnd n c.1 ⊆ bndList n cs`, and is produced from
every family in the universe containing it. -/
theorem op_acc {n : Nat} (cs : List (TeleX ι V × (List V → ι))) :
    AccFam n (op n cs) (bndList n cs) := by
  intro W _ j x hx
  obtain ⟨j', c, fs, hc, hfs, hi, rfl⟩ := mem_op.mp hx
  classical
  refine ⟨sep (bnd n c.1) fun a => ∃ o, Supp c.1 fs a o,
    fun a => if h : ∃ o, Supp c.1 fs a o then Classical.choose h else (j, pt), ?_, ?_, ?_⟩
  · exact sep_sub.trans (bnd_sub_bndList (List.mem_of_getElem? hc))
  · intro a ha
    obtain ⟨-, h⟩ := mem_sep.mp ha
    show InFam W (if h : ∃ o, Supp c.1 fs a o then Classical.choose h else (j, pt))
    rw [dif_pos h]
    exact Supp_inFam hfs (Classical.choose_spec h)
  · intro W' _ hsup
    refine mem_op.mpr ⟨j', c, fs, hc, ?_, hi, rfl⟩
    refine FitsB_of_Supp hfs fun a o hao => ?_
    have h : ∃ o, Supp c.1 fs a o := ⟨o, hao⟩
    have this : InFam W' (if h : ∃ o, Supp c.1 fs a o then Classical.choose h else (j, pt)) :=
      hsup a (mem_sep.mpr ⟨Supp_mem_bnd hfs hao, h⟩)
    rw [dif_pos h] at this
    rwa [Supp_fun hao (Classical.choose_spec h)]

end Bound

/-! ## The closure theorem -/

/-- **Inductive closure** (the old law of `IndLibCompat`, now a
theorem): for every list of constructor telescopes with their target
indices, some family of members of `univ n` is closed under every
bounded instance of every constructor — the tagged tuple of the
instance's values is a member of the family at the constructor's
target.  The family is the closed family `closed_of_acc` gives for
the accessible operator `op n cs`. -/
theorem inductive_closure {V : Type u} [IndLib V] {ι : Type u} {n : Nat} (hn : n ≠ 0)
    (cs : List (TeleX ι V × (List V → ι))) :
    ∃ W : ι → V, (∀ i, Mem (W i) (univ n)) ∧
      ∀ (j : Nat) (c : TeleX ι V × (List V → ι)) (fs : List V), cs[j]? = some c →
        TeleX.FitsB n W c.1 fs → Mem (tag j (tuple fs)) (W (c.2 fs)) := by
  obtain ⟨L, hL, hcl⟩ := closed_of_acc hn (bndList_mem_univ hn cs) (op_maps hn cs) (op_acc cs)
  exact ⟨L, hL, fun j c fs hc hfs => hcl _ _ (mem_op.mpr ⟨j, c, fs, hc, hfs, rfl, rfl⟩)⟩

end Fragment.IndSpec.Nst
