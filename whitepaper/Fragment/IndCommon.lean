module

public import Fragment.IndLib
public import Fragment.Ctx
public import Fragment.IsModel

@[expose] public section

/-!
# The model of an inductive block: the common pieces

What the model of a block (`IndSem.lean`) and the readers of its
generated syntax (`Read.lean`) use before any family is built — the
closed base environment and the environment of parameter values, the
valuation of the block's level parameters, the regime and the result
universe, index expressions read as index values, a constructor's
value (the point at a proposition, the tagged tuple above), the
reading of a field list (the value and the earlier values at a
position), the replacement of recursive values by the point and the
block-level hypotheses stated with it (`NoRecDep`: no field reads an
earlier recursive field), the class of a nested block read in the
model, and the small list and valuation lemmas.  Nothing here depends
on how the family is constructed.
-/

namespace Fragment
open SetLib UnivLib IndLib

universe u

variable {V : Type u} [IndLib V]

/-! ## Small pieces -/

/-- The point applied to anything is the point. -/
theorem appList_pt : ∀ vs : List V, appList (pt : V) vs = pt
  | [] => rfl
  | v :: vs => by rw [appList_cons, app_pt, appList_pt vs]
/-- A relation holding pairwise along two lists of one length. -/
def ListRel {α β : Type _} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: l₁, b :: l₂ => R a b ∧ ListRel R l₁ l₂
  | _, _ => False

theorem ListRel.mono {α β : Type _} {R R' : α → β → Prop} (h : ∀ a b, R a b → R' a b) :
    ∀ {l₁ : List α} {l₂ : List β}, ListRel R l₁ l₂ → ListRel R' l₁ l₂
  | [], [], _ => trivial
  | _ :: _, _ :: _, hr => ⟨h _ _ hr.1, ListRel.mono h hr.2⟩
  | [], _ :: _, hr => hr.elim
  | _ :: _, [], hr => hr.elim

theorem ListRel.map {α β : Type _} {R : α → β → Prop} {f : α → β} :
    ∀ {l₁ : List α}, (∀ a ∈ l₁, R a (f a)) → ListRel R l₁ (l₁.map f)
  | [], _ => trivial
  | a :: _, h => ⟨h a List.mem_cons_self, ListRel.map fun a' ha' => h a' (List.mem_cons_of_mem a ha')⟩

theorem ListRel.unique {α β : Type _} {R R' : α → β → Prop}
    (h : ∀ a b b', R a b → R' a b' → b = b') :
    ∀ {l : List α} {bs bs' : List β}, ListRel R l bs → ListRel R' l bs' → bs = bs'
  | [], [], [], _, _ => rfl
  | a :: _, b :: _, b' :: _, h1, h2 => by
    rw [h a b b' h1.1 h2.1, ListRel.unique h h1.2 h2.2]
  | [], _ :: _, _, h1, _ => h1.elim
  | [], [], _ :: _, _, h2 => h2.elim
  | _ :: _, [], _, h1, _ => h1.elim
  | _ :: _, _ :: _, [], _, h2 => h2.elim
theorem lookup_zip_map (ps : List Name) (f : Name → Nat) (n : Name) :
    (ps.zip (ps.map f)).lookup n = if n ∈ ps then some (f n) else none := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons, List.mem_cons]
    by_cases h : n = p
    · subst h; simp
    · have : (n == p) = false := by simpa using h
      simp [this, ih, h]

theorem valOf_map (ps : List Name) (f : Name → Nat) :
    valOf ps (ps.map f) = fun n => if n ∈ ps then f n else 0 := by
  funext n
  simp only [valOf, lookup_zip_map]
  split <;> rfl

theorem lookup_zip_none {α : Type _} {ps : List Name} {n : Name} (h : n ∉ ps) (ls : List α) :
    (ps.zip ls).lookup n = none := by
  induction ps generalizing ls with
  | nil => simp
  | cons p ps ih =>
    cases ls with
    | nil => simp
    | cons l ls =>
      simp only [List.mem_cons, not_or] at h
      simp only [List.zip_cons_cons, List.lookup_cons]
      have : (n == p) = false := by simpa using h.1
      rw [this]
      exact ih h.2 ls

/-- Re-reading the valuation through the parameters gives it back. -/
theorem valOf_map_valOf (ps : List Name) (ls : List Nat) :
    valOf ps (ps.map (valOf ps ls)) = valOf ps ls := by
  rw [valOf_map]
  funext n
  split
  · rfl
  · rename_i h
    simp [valOf, lookup_zip_none h]

/-- Two valuations agreeing on `ps` read alike through `ps`. -/
theorem valOf_map_congr (ps : List Name) {f g : Name → Nat} (h : ∀ n ∈ ps, f n = g n) :
    valOf ps (ps.map f) = valOf ps (ps.map g) := by
  rw [valOf_map, valOf_map]
  funext n
  split
  · exact h n ‹_›
  · rfl

/-- At a parameter of `ps`, the positional valuation of the evaluated
levels is the substituted valuation: both read the first occurrence. -/
theorem valOf_map_eval (φ : Name → Nat) :
    ∀ {ps : List Name} {ls : List Level}, ls.length = ps.length → ∀ {n : Name}, n ∈ ps →
      valOf ps (ls.map (Level.eval φ)) n = Level.substVal φ ps ls n
  | [], _, _, _, hn => by simp at hn
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | p :: ps, l :: ls, hlen, n, hn => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [valOf, Level.substVal, Level.lookupLevel, List.map_cons, List.zip_cons_cons,
      List.lookup_cons]
    by_cases h : n = p
    · subst h
      simp
    · have hb : (n == p) = false := by simpa using h
      have ih := valOf_map_eval φ hlen (List.mem_of_ne_of_mem h hn)
      simp only [valOf, Level.substVal, Level.lookupLevel] at ih
      simpa [hb] using ih
/-- The graph relation's shape: parameters, motive, minors, indices,
witness, value. -/
abbrev RecP (V : Type u) := List V → V → List V → List V → V → V → Prop

/-- The environment of parameter values. -/
def envP (ps : List V) : Nat → V := consList ps base

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat)

/-- The valuation of the block's level parameters at `ls`. -/
def ψ : Name → Nat := valOf S.lparams ls

/-- The result universe. -/
def u₀ : Nat := S.sort.eval (S.ψ ls)

/-- **The regime**: is the result sort zero here? -/
def z : Bool := decide (S.u₀ ls = 0)

theorem z_iff : S.z ls = true ↔ S.u₀ ls = 0 := decide_eq_true_iff

/-- Index expressions (a spine, outermost first) read under an
environment, as index values (innermost first). -/
noncomputable def idxVals (env : Nat → V) (es : List Expr) : List V := (es.map (interp M (S.ψ ls) env)).reverse
/-! ## The class of a nested block, read in the model

A container field's domain is the class `K.{lsK} args[nested]`: the
container's set — **already in the model**, assigned to `K` when `K`
was installed — applied to the class's arguments, with a set `X` at
the nested position.  In the family's operator `X` is the fibre of
the *approximant* at the nested occurrence's index expressions (`IndSem.lean`,
`fieldSet`), and the operator is accessible (hence monotone) because
the class is, in `X` (`ContClause`, which the installation establishes
from the container's positivity and the nested case of accessibility,
`NestSem.lean`). -/

/-- The class's arguments as values (outermost first), with `X` at
the nested position: the other arguments read under the parameters
(they are closed under them). -/
noncomputable def classArgsV (N : NestInfo) (ps : List V) (X : V) : List V :=
  (N.args.take N.p).map (interp M (S.ψ ls) (envP ps)) ++ [X] ++
    (N.args.drop N.p).map (interp M (S.ψ ls) (envP ps))

/-- The container's levels at the block's valuation. -/
def lsK (N : NestInfo) : List Nat := N.lsK.map (Level.eval (S.ψ ls))

/-- **The admissible part of a set**: at a proposition the set itself;
above it the members that are neither the point nor a member of it —
a strict set (`adm_mem_typeU`), so a member of the nested parameter's
domain `Sort u`, a set of types, and the set itself on a
set of tagged values (`adm_eq_self`), such as a fibre of the family.
The class reads the container's set at admissible sets only: there it
is a graph applied inside its domain. -/
def adm (X : V) : V := if S.z ls then X else sep X fun x => x ≠ pt ∧ ¬ x ∈ˢ pt

/-- **The class at a parameter set**: the container's set in the model,
applied to the class's arguments with the admissible part of `X` at
the nested position. -/
noncomputable def classSet (N : NestInfo) (ps : List V) (X : V) : V :=
  appList (M N.K.name (S.lsK ls N)) (S.classArgsV M ls N ps (S.adm ls X))

theorem mem_adm {X x : V} : x ∈ˢ S.adm ls X ↔ x ∈ˢ X ∧ (S.z ls = false → x ≠ pt ∧ ¬ x ∈ˢ pt) := by
  unfold adm
  cases S.z ls
  · simp [mem_sep]
  · simp

theorem adm_true (hz : S.z ls = true) (X : V) : S.adm ls X = X := by
  unfold adm; rw [hz]; rfl

theorem adm_sub (X : V) : S.adm ls X ⊆ˢ X := fun _ h => ((S.mem_adm ls).mp h).1

theorem adm_mono {X Y : V} (h : X ⊆ˢ Y) : S.adm ls X ⊆ˢ S.adm ls Y := fun x hx => by
  rw [mem_adm] at hx ⊢
  exact ⟨h x hx.1, hx.2⟩

/-- On a set none of whose members is the point or a member of it (a
set of tagged values), the admissible part is the set. -/
theorem adm_eq_self {X : V} (h : ∀ x, x ∈ˢ X → x ≠ pt ∧ ¬ x ∈ˢ pt) : S.adm ls X = X :=
  ext fun x => by
    rw [mem_adm]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun _ => h x hx⟩⟩

theorem adm_mem_univ {X : V} (hX : X ∈ˢ (univ (S.u₀ ls) : V)) : S.adm ls X ∈ˢ (univ (S.u₀ ls) : V) := by
  unfold adm
  split
  · exact hX
  · exact sep_mem_univ hX

/-- **The admissible part is a type** of the result universe. -/
theorem adm_mem_typeU {X : V} (hX : X ∈ˢ (univ (S.u₀ ls) : V)) :
    S.adm ls X ∈ˢ (typeU (S.u₀ ls) : V) := by
  cases hz : S.z ls with
  | true =>
    have h0 := (S.z_iff ls).mp hz
    unfold adm
    rw [hz, ite_eq_left rfl, h0, mem_typeU_zero]
    rw [h0] at hX
    exact hX
  | false =>
    have h0 : S.u₀ ls ≠ 0 := fun h => by rw [(S.z_iff ls).mpr h] at hz; cases hz
    refine (mem_typeU_pos h0).mpr ⟨S.adm_mem_univ ls hX, Or.inr ⟨fun he => ?_, fun hp => ?_⟩⟩
    · obtain ⟨z, hz'⟩ := exists_mem_pt (V := V)
      have := hz'
      rw [← he, mem_adm] at this
      exact (this.2 hz).2 hz'
    · exact ((S.mem_adm ls).mp hp).2 hz |>.1 rfl

/-- **The admissible part is a type**, wherever it is read: at a
proposition the set is a truth value, above it the part is strict. -/
theorem IsTy_adm {X : V} (hX : S.z ls = true → X ∈ˢ (univ 0 : V)) : IsTy (S.adm ls X) := by
  cases hz : S.z ls with
  | true => rw [S.adm_true ls hz]; exact Or.inl (hX hz)
  | false =>
    refine Or.inr ⟨fun he => ?_, fun hp => ?_⟩
    · obtain ⟨z, hz'⟩ := exists_mem_pt (V := V)
      have := hz'
      rw [← he, mem_adm] at this
      exact (this.2 hz).2 hz'
    · exact ((S.mem_adm ls).mp hp).2 hz |>.1 rfl

/-- **Above a proposition the admissible part is strict** (task #342
F1): its members are neither the point nor a member of it, so it is
not the point (which has a member) and does not hold it. -/
theorem strict_adm (hz : S.z ls = false) (X : V) : Strict (S.adm ls X) := by
  refine ⟨fun he => ?_, fun hp => ((S.mem_adm ls).mp hp).2 hz |>.1 rfl⟩
  obtain ⟨z, hz'⟩ := exists_mem_pt (V := V)
  have := hz'
  rw [← he, mem_adm] at this
  exact (this.2 hz).2 hz'

/-- A member of an admissible part that is a member of another set is
a member of that set's admissible part. -/
theorem mem_adm_of {X X' x : V} (hx : x ∈ˢ S.adm ls X) (hx' : x ∈ˢ X') : x ∈ˢ S.adm ls X' :=
  (S.mem_adm ls).mpr ⟨hx', ((S.mem_adm ls).mp hx).2⟩

/-- **The body of a reflexive field's function space**: the family's fibre —
its admissible part under at least one binder.  The
function space is read by values (`SetLib.piV`), and over an arbitrary family
in the universe a fibre `{pt}` would put a Type-sorted field's function space
in the propositional regime; the admissible part, a strict set above a
proposition, keeps it a function space wherever its domain is
inhabited, so the field's set grows with the family (`piCtx_retype`).
On the block's own family the fibres are admissible already. -/
def reflBody (tele : List Expr) (X : V) : V := if tele = [] then X else S.adm ls X

@[simp] theorem reflBody_nil (X : V) : S.reflBody ls [] X = X := rfl

theorem reflBody_sub (tele : List Expr) (X : V) : S.reflBody ls tele X ⊆ˢ X := by
  unfold reflBody; split
  · exact fun _ h => h
  · exact S.adm_sub ls X

theorem mem_reflBody_of {tele : List Expr} {X X' x : V} (hx : x ∈ˢ S.reflBody ls tele X)
    (hx' : x ∈ˢ X') : x ∈ˢ S.reflBody ls tele X' := by
  unfold reflBody at hx ⊢; split
  · exact hx'
  · rename_i h; rw [ite_eq_right h] at hx; exact S.mem_adm_of ls hx hx'

theorem IsTy_reflBody {tele : List Expr} (ht : tele ≠ []) {X : V}
    (hX : S.z ls = true → X ∈ˢ (univ 0 : V)) : IsTy (S.reflBody ls tele X) := by
  unfold reflBody; rw [ite_eq_right ht]; exact S.IsTy_adm ls hX

theorem reflBody_eq_self (tele : List Expr) {X : V} (h : S.adm ls X = X) :
    S.reflBody ls tele X = X := by
  unfold reflBody; split
  · rfl
  · exact h

theorem reflBody_mem_univ (tele : List Expr) {X : V} (hX : X ∈ˢ (univ (S.u₀ ls) : V)) :
    S.reflBody ls tele X ∈ˢ (univ (S.u₀ ls) : V) := by
  unfold reflBody; split
  · exact hX
  · exact S.adm_mem_univ ls hX

/-- The nested occurrence's index values at the parameters (its index expressions
are closed under them). -/
noncomputable def memberIdx (N : NestInfo) (ps : List V) : List V := S.idxVals M ls (envP ps) N.idx

/-- **The container's parameter values at a parameter set** (innermost
first): the class's arguments with `X` at the nested position —
the parameters the container's own family is read at. -/
noncomputable def psK (N : NestInfo) (ps : List V) (X : V) : List V := (S.classArgsV M ls N ps X).reverse

/-- The number of the container's constructors (`0` for a plain
block): the block's constructors are tagged after them, so that the
block and its class can share one closure (`ctorsX`). -/
def nKS : Nat :=
  match S.nest with
  | some N => N.nK
  | none => 0

/-- The tag of the block's constructor `j`. -/
def tagOf (j : Nat) : Nat := S.nKS + j
/-- **A constructor's value** at its fields: the point at a
proposition, the tagged tuple above. -/
def ctorVal (j : Nat) (fs : List V) : V := if S.z ls then pt else tag (S.tagOf j) (tuple fs.reverse)
/-- The value of the field with `k` earlier fields. -/
def fieldVal (fs : List V) (k : Nat) : V := fs.getD (fs.length - 1 - k) pt

/-- The values of the `k` earlier fields. -/
def earlier (fs : List V) (k : Nat) : List V := fs.drop (fs.length - k)
theorem fieldVal_cons {v : V} {fs : List V} {k : Nat} (hk : k < fs.length) :
    fieldVal (v :: fs) k = fieldVal fs k := by
  simp only [fieldVal, List.length_cons]
  rw [show fs.length + 1 - 1 - k = (fs.length - 1 - k) + 1 by omega, List.getD_cons_succ]

omit [IndLib V] in
theorem earlier_cons {v : V} {fs : List V} {k : Nat} (hk : k ≤ fs.length) :
    earlier (v :: fs) k = earlier fs k := by
  simp only [earlier, List.length_cons]
  rw [show fs.length + 1 - k = (fs.length - k) + 1 by omega, List.drop_succ_cons]
/-- **No field reads an earlier recursive field** (the block-level
hypothesis). -/
def NoRecDep : Prop :=
  ∀ c ∈ S.ctors, ∀ i f, c.fields[i]? = some f → fieldNoRecDep (c.fields.drop (i + 1)) f
/-- No container field: a plain block's constructors. -/
def NoCont : Prop := ∀ c ∈ S.ctors, ∀ f ∈ c.fields, f.isCont = false
/-- The minor for constructor `j` among the minors (innermost first). -/
def minorAt (mins : List V) (j : Nat) : V := mins.getD (S.n - 1 - j) pt
/-- A container field in a plain block is impossible. -/
theorem noCont_absurd {c : CtorSpec} (hnc : S.NoCont) (hcm : c ∈ S.ctors) {i : Nat}
    (hf : c.fields[i]? = some .container) : False := by
  have := hnc c hcm _ (List.mem_of_getElem? hf)
  simp [Field.isCont] at this

/-- A recursive position of a constructor is a reflexive (or
container) field at that position. -/
theorem _root_.Fragment.mem_recFields {c : CtorSpec} {kf : Nat × Field} (h : kf ∈ c.recFields) :
    c.fields[c.fields.length - 1 - kf.1]? = some kf.2 ∧ kf.1 < c.fields.length ∧ kf.2.isRec = true := by
  simp only [CtorSpec.recFields, List.mem_filterMap, List.mem_range] at h
  obtain ⟨k, hk, hkf⟩ := h
  revert hkf
  split
  · rename_i f hf
    split
    · rename_i hrec
      intro hkf
      simp only [Option.some.injEq] at hkf
      subst hkf
      exact ⟨hf, hk, hrec⟩
    · intro h; simp at h
  · intro h; simp at h
/-- The constructor of a name, with its number. -/
def ctorOf? (n : Name) : Option (Nat × CtorSpec) :=
  (List.range S.n).findSome? fun j =>
    match S.ctors[j]? with
    | some c => if c.name = n then some (j, c) else none
    | none => none

end IndSpec

end Fragment
