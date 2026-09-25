module

public import Fragment.Level

@[expose] public section

/-!
# The annotation datum `PropWhen`

Every binder of the fragment (`lam`, `pi` in `Syntax.lean`) carries a
datum `pw : PropWhen` saying *when its body is a proposition*: never,
or exactly when a given set of level parameters are all zero.  It is
the reading of the zero-ness predicate `{φ | eval φ v = 0}` of the
body's sort `v`, and `Level.zeroness` computes it (below).  The datum
is what the interpretation reads at a binder (`Interp.lean`) — never a
sort, never a semantic value — and what type inference checks
(`Infer.pi`/`Infer.lam` in `Rules.lean`).

This mirrors `ConLeche/Kernel/PropWhen.lean`, including its one design
point: the datum is **canonical**, so that `=` on data is agreement of
the readouts at every valuation (`PropWhen.eq_iff`).  The parameter
set is a strictly ascending list, and every producer normalises.
-/

namespace Fragment

/-! ## Canonical parameter sets -/

/-- Strictly ascending in the order of names — a canonical
representative of a finite set of names. -/
def Ascending (ps : List Name) : Prop := ps.Pairwise (fun a b => compare a b = .lt)

/-- Sorted insertion without duplicates. -/
def insertName (n : Name) : List Name → List Name
  | [] => [n]
  | m :: ms =>
    match compare n m with
    | .lt => n :: m :: ms
    | .eq => m :: ms
    | .gt => m :: insertName n ms

theorem mem_insertName {k n : Name} : ∀ {ms : List Name},
    k ∈ insertName n ms ↔ k = n ∨ k ∈ ms
  | [] => by simp [insertName]
  | m :: ms => by
    unfold insertName
    split
    · simp
    · rename_i h
      have : n = m := Std.LawfulEqCmp.eq_of_compare h
      subst this
      simp
    · simp only [List.mem_cons, mem_insertName]
      constructor
      · rintro (h | h | h) <;> simp [h]
      · rintro (h | h | h) <;> simp [h]

theorem ascending_insertName {n : Name} : ∀ {ms : List Name},
    Ascending ms → Ascending (insertName n ms)
  | [], _ => by simp [insertName, Ascending]
  | m :: ms, h => by
    unfold Ascending at h
    rw [List.pairwise_cons] at h
    obtain ⟨hm, hms⟩ := h
    unfold insertName
    split
    · rename_i hlt
      unfold Ascending
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, hm, hms⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hlt
      · exact Std.TransCmp.lt_trans hlt (hm b hb)
    · exact List.pairwise_cons.mpr ⟨hm, hms⟩
    · rename_i hgt
      unfold Ascending
      rw [List.pairwise_cons]
      refine ⟨?_, ascending_insertName hms⟩
      intro b hb
      rcases mem_insertName.mp hb with rfl | hb
      · exact Std.OrientedCmp.lt_of_gt hgt
      · exact hm b hb

/-- Two ascending lists with the same members are the same list — the
canonicity theorem. -/
theorem Ascending.ext : ∀ {as bs : List Name}, Ascending as → Ascending bs →
    (∀ n, n ∈ as ↔ n ∈ bs) → as = bs
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => by simp at h; exact ((h b).1 rfl).elim
  | a :: _, [], _, _, h => by simp at h; exact ((h a).1 rfl).elim
  | a :: as, b :: bs, ha, hb, h => by
    unfold Ascending at ha hb
    rw [List.pairwise_cons] at ha hb
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).mp (List.mem_cons_self)) with hab | hab
      · exact hab
      rcases List.mem_cons.mp ((h b).mpr (List.mem_cons_self)) with hba | hba
      · exact hba.symm
      have := Std.TransCmp.lt_trans (ha.1 b hba) (hb.1 a hab)
      rw [Std.ReflOrd.compare_self] at this
      exact absurd this (by decide)
    subst hab
    have htail : as = bs := by
      refine Ascending.ext ha.2 hb.2 fun n => ⟨fun hn => ?_, fun hn => ?_⟩
      · rcases List.mem_cons.mp ((h n).mp (List.mem_cons_of_mem a hn)) with rfl | hn'
        · have := ha.1 n hn
          rw [Std.ReflOrd.compare_self] at this
          exact absurd this (by decide)
        · exact hn'
      · rcases List.mem_cons.mp ((h n).mpr (List.mem_cons_of_mem a hn)) with rfl | hn'
        · have := hb.1 n hn
          rw [Std.ReflOrd.compare_self] at this
          exact absurd this (by decide)
        · exact hn'
    rw [htail]

/-- A canonical finite set of level-parameter names. -/
structure ParamSet where
  /-- The names, strictly ascending. -/
  list : List Name
  /-- The canonicity invariant. -/
  ascending : Ascending list
  deriving DecidableEq

namespace ParamSet

instance : Membership Name ParamSet := ⟨fun s n => n ∈ s.list⟩

theorem mem_def {n : Name} {s : ParamSet} : n ∈ s ↔ n ∈ s.list := Iff.rfl

/-- The empty set. -/
def empty : ParamSet := ⟨[], List.Pairwise.nil⟩

/-- Insertion. -/
def insert (n : Name) (s : ParamSet) : ParamSet :=
  ⟨insertName n s.list, ascending_insertName s.ascending⟩

/-- The singleton. -/
def single (n : Name) : ParamSet := insert n empty

/-- Union. -/
def union (s t : ParamSet) : ParamSet := t.list.foldr insert s

@[simp] theorem not_mem_empty (n : Name) : ¬ n ∈ empty := by simp [mem_def, empty]

@[simp] theorem mem_insert {k n : Name} {s : ParamSet} :
    k ∈ insert n s ↔ k = n ∨ k ∈ s := mem_insertName

@[simp] theorem mem_single {k n : Name} : k ∈ single n ↔ k = n := by
  simp [single]

theorem mem_foldr_insert {k : Name} (s : ParamSet) : ∀ ns : List Name,
    k ∈ ns.foldr insert s ↔ k ∈ s ∨ k ∈ ns
  | [] => by simp
  | n :: ns => by
    simp only [List.foldr_cons, mem_insert, mem_foldr_insert s ns, List.mem_cons]
    exact or_left_comm

theorem mem_union {k : Name} {s t : ParamSet} :
    k ∈ union s t ↔ k ∈ s ∨ k ∈ t := by
  rw [union, mem_foldr_insert]; rfl

/-- Sets with the same members are equal. -/
theorem ext {s t : ParamSet} (h : ∀ n, n ∈ s ↔ n ∈ t) : s = t := by
  obtain ⟨sl, hs⟩ := s
  obtain ⟨tl, ht⟩ := t
  have : sl = tl := Ascending.ext hs ht h
  subst this
  rfl

end ParamSet

/-! ## The datum -/

/-- **When a binder's body is a proposition**: never, or exactly at the
valuations where every parameter of the set is zero.  (`whenZero ∅` is
"always".) -/
inductive PropWhen where
  /-- The body is never a proposition — the *graph regime*, where the
  β rule needs no certificate (`Red.betaGate`). -/
  | never
  /-- The body is a proposition exactly when these level parameters
  are all zero. -/
  | whenZero (ps : ParamSet)
  deriving DecidableEq

namespace PropWhen

/-- The readout at a valuation: is the body a proposition here? -/
def holds (pw : PropWhen) (φ : Name → Nat) : Bool :=
  match pw with
  | never => false
  | whenZero ps => ps.list.all fun n => φ n == 0

@[simp] theorem holds_never (φ : Name → Nat) : holds never φ = false := rfl

theorem holds_whenZero {ps : ParamSet} {φ : Name → Nat} :
    holds (whenZero ps) φ = true ↔ ∀ n ∈ ps, φ n = 0 := by
  simp [holds, ParamSet.mem_def]

/-- "Always a proposition". -/
def always : PropWhen := whenZero ParamSet.empty

@[simp] theorem holds_always (φ : Name → Nat) : holds always φ = true := by
  simp [always, holds, ParamSet.empty]

/-- The conjunction of two data: a proposition when both are. -/
def inter : PropWhen → PropWhen → PropWhen
  | never, _ => never
  | _, never => never
  | whenZero s, whenZero t => whenZero (s.union t)

theorem holds_inter (a b : PropWhen) (φ : Name → Nat) :
    holds (inter a b) φ = (holds a φ && holds b φ) := by
  cases a with
  | never => simp [inter]
  | whenZero s =>
    cases b with
    | never => simp [inter]
    | whenZero t =>
      simp only [inter]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, holds_whenZero, ParamSet.mem_union]
      constructor
      · intro h
        exact ⟨fun n hn => h n (Or.inl hn), fun n hn => h n (Or.inr hn)⟩
      · rintro ⟨h1, h2⟩ n (hn | hn)
        · exact h1 n hn
        · exact h2 n hn

/-- **Canonicity**: two data are equal exactly when their readouts agree
at every valuation.  So the checker compares annotations with `=`, and
that comparison is semantic. -/
theorem eq_iff (a b : PropWhen) : a = b ↔ ∀ φ : Name → Nat, holds a φ = holds b φ := by
  constructor
  · rintro rfl _; rfl
  · intro h
    cases a with
    | never =>
      cases b with
      | never => rfl
      | whenZero t =>
        have := h fun _ => 0
        simp [holds] at this
    | whenZero s =>
      cases b with
      | never =>
        have := h fun _ => 0
        simp [holds] at this
      | whenZero t =>
        congr 1
        apply ParamSet.ext
        intro n
        have hn := h fun m => if m = n then 1 else 0
        rw [Bool.eq_iff_iff] at hn
        simp only [holds_whenZero] at hn
        -- `n ∉ s ↔ n ∉ t` at the valuation that is `1` exactly at `n`
        have key : ∀ u : ParamSet,
            (∀ m ∈ u, (if m = n then 1 else 0) = 0) ↔ ¬ n ∈ u := by
          intro u
          constructor
          · intro hu hnu
            have := hu n hnu
            simp at this
          · intro hnu m hm
            have : m ≠ n := fun hmn => hnu (hmn ▸ hm)
            simp [this]
        rw [key, key] at hn
        exact ⟨fun h1 => Classical.byContradiction fun h2 => hn.mpr h2 h1,
          fun h1 => Classical.byContradiction fun h2 => hn.mp h2 h1⟩

end PropWhen

/-! ## The zero-ness of a level, as a datum -/

namespace Level

/-- **The zero-ness datum of a level**: the reading of `{φ | eval φ l = 0}`.
A `succ` is never zero; a `max` is zero when both sides are; an `imax`
is zero exactly when its second argument is (`imaxNat_eq_zero_iff`).
Mirrors `Level.zeronessOf` (`ConLeche/Kernel/Level.lean`). -/
def zeroness : Level → PropWhen
  | zero => .always
  | succ _ => .never
  | param n => .whenZero (ParamSet.single n)
  | max a b => (zeroness a).inter (zeroness b)
  | imax _ b => zeroness b

/-- **Exactness**: the datum reads `true` exactly where the level
evaluates to zero. -/
theorem holds_zeroness (φ : Name → Nat) : ∀ l : Level,
    (zeroness l).holds φ = true ↔ eval φ l = 0
  | zero => by simp [zeroness]
  | succ l => by simp [zeroness]
  | param n => by simp [zeroness, PropWhen.holds_whenZero]
  | max a b => by
    simp only [zeroness, PropWhen.holds_inter, Bool.and_eq_true, holds_zeroness φ a,
      holds_zeroness φ b, eval_max]
    omega
  | imax a b => by
    simp only [zeroness, holds_zeroness φ b, eval_imax, imaxNat_eq_zero_iff]

/-- The `Bool`-equation form of exactness. -/
theorem holds_zeroness_eq (φ : Name → Nat) (l : Level) :
    (zeroness l).holds φ = (eval φ l == 0) := by
  rw [Bool.eq_iff_iff, holds_zeroness, beq_iff_eq]

/-- Zero-ness is decided by `eval`, so it is invariant under level
substitution up to the composed valuation (`PropWhen.substL` below is
the datum-level counterpart). -/
theorem holds_zeroness_subst (φ : Name → Nat) (ps : List Name) (ls : List Level)
    (l : Level) :
    (zeroness (subst ps ls l)).holds φ = (zeroness l).holds (substVal φ ps ls) := by
  apply Bool.eq_iff_iff.mpr
  rw [holds_zeroness, holds_zeroness, eval_subst]

end Level

namespace PropWhen

/-- **Level substitution on a datum**: instantiating the declaration's
parameters `ps` at levels `ls`, "all of `qs` zero" becomes "each
substitute of a `q ∈ qs` zero" — the conjunction of the substitutes'
zero-ness data.  Mirrors `Level.substPW` (`ConLeche/Kernel/Level.lean`). -/
def substL (ps : List Name) (ls : List Level) : PropWhen → PropWhen
  | never => never
  | whenZero qs =>
    qs.list.foldr (fun q acc => (Level.zeroness (Level.lookupLevel ps ls q)).inter acc) always

theorem holds_foldr_inter (f : Name → PropWhen) (φ : Name → Nat) : ∀ qs : List Name,
    holds (qs.foldr (fun q acc => (f q).inter acc) always) φ = qs.all fun q => holds (f q) φ
  | [] => by simp
  | q :: qs => by simp [holds_inter, holds_foldr_inter f φ qs]

/-- The substituted datum reads under `φ` as the original reads under
the composed valuation. -/
theorem holds_substL (φ : Name → Nat) (ps : List Name) (ls : List Level) :
    ∀ pw : PropWhen, (substL ps ls pw).holds φ = pw.holds (Level.substVal φ ps ls)
  | never => rfl
  | whenZero qs => by
    rw [substL, holds_foldr_inter]
    simp only [Level.holds_zeroness_eq]
    rfl

end PropWhen

end Fragment
