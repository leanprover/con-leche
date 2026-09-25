module

public import Fragment.IndLib
public import Fragment.Ctx

@[expose] public section

/-!
# The model of an inductive block

What the type former, the constructors and the recursor of a block
(`IndSpec`, `Decl.lean`) denote, and the laws about it that are pure
set theory — no derivation, no environment.  Everything here is at a
fixed list of concrete levels `ls` for the block's parameters; the
valuation is `valOf S.lparams ls` (`IndSpec.ψ`).

* **The family** is a predicate `Mem ps is x` on parameter values,
  index values (both innermost first) and a candidate member: the
  least fixed point (`Lfp`, `IndLib.lean`) of the operator `step`,
  which says "`x` is a tagged tuple `tag j (tuple fs)` of fields (in
  order) fitting constructor `j`'s telescope at `ps`, with `is` the
  constructor's index expressions read under the fields".  A field
  fits an *ordinary* domain when it is a member of that domain's set;
  a *recursive* domain when it is a member of the **fibre** of the
  family at the field's index expressions; a *reflexive* domain when
  it is a member of the product over the field's telescope into those
  fibres.  The fibre reads the **regime** `z` (is the result sort zero
  at this valuation?): at a proposition it is the truth value "some
  `x` is a member" (`fibreR`), above it the members of a bounding set
  that satisfy `Mem` — so a member of a propositional family is always
  the point, and a member of a type-valued one is the tagged tuple
  itself.  The bounding set is the family the library's inductive
  closure law supplies for the block's constructor telescopes
  (`bound`); it is what makes a fibre a *member* of the universe
  (`Fam_mem_univ`), and the constructor values land in it because
  every instance the checker admits is a bounded one
  (`ctorVal_mem_Fam`).  The type former's set (`famSet`) is the graph
  over the parameter and index contexts whose value is the fibre.
* **A constructor's** set (`ctorSet`) is the abstraction over its
  parameters and fields of `ctorVal j fs`: the point at a proposition,
  the tagged tuple above.
* **The recursor** is a function of the parameters, the motive, the
  minors, the indices and the major, `recSem`.  Its **graph**
  `RecGraph` is a second least fixed point: "the value at the tagged
  tuple of `fs` is minor `j` applied to the fields and to the
  inductive hypotheses, where each hypothesis is the recursor's value
  at the field (through its own telescope at a reflexive field)".  The
  graph is **single-valued** (`RecGraph_fun`, by induction over the
  graph — tags and tuples are injective) and **total** on the family
  (`RecGraph_total`, by induction over the family), which is the
  recursion theorem; `recFn` chooses the value.  At a propositional
  family the major is the point and carries no fields; the recursor's
  value there is the value at a **witness** of the fibre (`pick`),
  which is unique under the subsingleton criterion (`Uniq`) — exactly
  what the checker demands of a large eliminator on a proposition —
  and the ι law follows (`recSem_eq`).  The recursor's **typing**,
  that its value lies in the motive at the indices and the major, is
  again induction over the family, given the minors' typing
  (`recSem_mem`).

Con-leche: the least pre-fixed family `lfpFamSet`
(`ConLeche/SetTheory/Derive/LfpFam.lean`) over the constructor-tower
functor (`ConLeche/Semantics/Tower/FixLeafI.lean`), the tagged tuples
of `ConLeche/SetModel/TaggedSum.lean` and `TupleTower.lean`, the
closed member from the container theorem
(`ConLeche/SetModel/Container.lean`), and the recursor as a fixed
point of its unfolding (`ConLeche/Semantics/Tower/FixRecI.lean`) with
`recGraph` (`ConLeche/SetModel/RecGraph.lean`) for the recursive
squash regime.
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V]

/-! ## Small pieces -/

/-- The closed base environment: every variable the point. -/
def base : Nat → V := fun _ => pt

/-- **A fibre at a regime**: at a proposition (`z = true`) the truth
value "`P` has a member", above it the members of `U` satisfying
`P`. -/
def fibreR (z : Bool) (U : V) (P : V → Prop) : V :=
  if z then truthVal (∃ x, P x) else sep U P

theorem mem_fibreR_true {U : V} {P : V → Prop} {x : V} :
    x ∈ˢ fibreR true U P ↔ x = pt ∧ ∃ y, P y := by
  simp [fibreR, mem_truthVal]

theorem mem_fibreR_false {U : V} {P : V → Prop} {x : V} :
    x ∈ˢ fibreR false U P ↔ x ∈ˢ U ∧ P x := by
  simp [fibreR, mem_sep]

theorem fibreR_mono {z : Bool} {U : V} {P Q : V → Prop} (h : ∀ x, P x → Q x) :
    fibreR z U P ⊆ˢ fibreR z U Q := by
  intro x hx
  cases z
  · rw [mem_fibreR_false] at hx ⊢; exact ⟨hx.1, h x hx.2⟩
  · rw [mem_fibreR_true] at hx ⊢; exact ⟨hx.1, hx.2.imp h⟩

/-- A fibre is in the universe: a truth value is in `univ 0`, a
separated part of a member of a positive universe is in it. -/
theorem fibreR_mem_univ {z : Bool} {n : Nat} {U : V} {P : V → Prop} (h : z = true ↔ n = 0)
    (hU : z = false → U ∈ˢ (univ n : V)) : fibreR z U P ∈ˢ (univ n : V) := by
  cases z
  · exact sep_mem_univ (fun h0 => by simp [h0] at h) (hU rfl)
  · rw [h.mp rfl]; exact truthVal_mem_univ_zero _

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

/-- The valuation of level parameters at a list of concrete levels,
positionally; a parameter not in the list is `0`. -/
def valOf (ps : List Name) (ls : List Nat) : Name → Nat :=
  fun n => ((ps.zip ls).lookup n).getD 0

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

theorem lookup_zip_none {ps : List Name} {n : Name} (h : n ∉ ps) (ls : List Nat) :
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

/-- A family predicate: parameters, indices, candidate member. -/
abbrev FamP (V : Type u) := List V → List V → V → Prop

/-- The graph relation's shape: parameters, motive, minors, indices,
witness, value. -/
abbrev RecP (V : Type u) := List V → V → List V → List V → V → V → Prop

/-- The environment of parameter values. -/
def envP (ps : List V) : Nat → V := consList ps base

/-- A telescope of expressions (outermost first), read under an
environment as a telescope of sets. -/
def toTeleS (M : Name → List Nat → V) (φ : Name → Nat) : (Nat → V) → List Expr → TeleS V
  | _, [] => .nil
  | ρ, T :: rest => .cons (interp M φ ρ T) fun y => toTeleS M φ (cons y ρ) rest

/-- The product over a context is monotone in its body. -/
theorem piCtx_sub (M : Name → List Nat → V) (φ : Name → Nat) {p : Bool} {ρ : Nat → V}
    {Γ : List Expr} {F G : (Nat → V) → V}
    (h : ∀ vs, FitsVals M φ ρ Γ vs → F (consList vs ρ) ⊆ˢ G (consList vs ρ)) :
    piCtx M φ p ρ Γ F ⊆ˢ piCtx M φ p ρ Γ G := by
  induction Γ generalizing F G with
  | nil => exact h [] trivial
  | cons A Γ ih =>
    simp only [piCtx_cons]
    refine ih fun vs hvs => piR_mono fun x hx => ?_
    exact h (x :: vs) ⟨hvs, hx⟩

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat)

/-- The valuation of the block's level parameters at `ls`. -/
def ψ : Name → Nat := valOf S.lparams ls

/-- **The regime**: is the result sort zero here? -/
def z : Bool := S.pw.holds (S.ψ ls)

/-- The result universe. -/
def u₀ : Nat := S.sort.eval (S.ψ ls)

theorem z_iff : S.z ls = true ↔ S.u₀ ls = 0 := Level.holds_zeroness _ _

/-- Index expressions (a spine, outermost first) read under an
environment, as index values (innermost first). -/
def idxVals (env : Nat → V) (es : List Expr) : List V := (es.map (interp M (S.ψ ls) env)).reverse

/-! ## The family -/

/-- The set a field ranges over, relative to a family predicate `P`
and a bounding family `B`, at parameters `ps` and the earlier field
values `fs`. -/
def fieldSet (B : List V → List V → V) (P : FamP V) (ps fs : List V) : Field → V
  | .ordinary A => interp M (S.ψ ls) (consList fs (envP ps)) A
  | .recursive es =>
    let is := S.idxVals M ls (consList fs (envP ps)) es
    fibreR (S.z ls) (B ps is) (P ps is)
  | .reflexive tele es =>
    piCtx M (S.ψ ls) (S.z ls) (consList fs (envP ps)) tele fun ρ' =>
      let is := S.idxVals M ls ρ' es
      fibreR (S.z ls) (B ps is) (P ps is)

/-- Field values fitting a constructor's fields (both innermost
first) relative to `B` and `P`. -/
def FitsFields (B : List V → List V → V) (P : FamP V) (ps : List V) : List Field → List V → Prop
  | [], [] => True
  | f :: fs, v :: vs => FitsFields B P ps fs vs ∧ v ∈ˢ S.fieldSet M ls B P ps vs f
  | _, _ => False

/-- **The operator** whose least fixed point is the family: `x` is the
tagged tuple of fields fitting some constructor, and `is` are that
constructor's index expressions read under the fields. -/
def step (B : List V → List V → V) (P : FamP V) (ps is : List V) (x : V) : Prop :=
  ∃ j c fs, S.ctors[j]? = some c ∧ S.FitsFields M ls B P ps c.fields fs ∧
    is = S.idxVals M ls (consList fs (envP ps)) c.idx ∧ x = tag j (tuple fs.reverse)

/-- The operator on triples. -/
def stepT (B : List V → List V → V) (P : List V × List V × V → Prop) (t : List V × List V × V) : Prop :=
  S.step M ls B (fun ps is x => P (ps, is, x)) t.1 t.2.1 t.2.2

/-! ### The bounding family -/

/-- A field telescope read as a constructor telescope of sets at the
parameters, the earlier values accumulated (innermost first, the
point at recursive positions — nothing after a recursive field reads
its value). -/
def toTeleX (ps : List V) : List Field → List V → TeleX (List V) V
  | [], _ => .nil
  | .ordinary A :: rest, fs' =>
    .ord (interp M (S.ψ ls) (consList fs' (envP ps)) A) fun v => toTeleX ps rest (v :: fs')
  | .recursive es :: rest, fs' =>
    .recur (S.idxVals M ls (consList fs' (envP ps)) es) (toTeleX ps rest (pt :: fs'))
  | .reflexive tele es :: rest, fs' =>
    .refl (toTeleS M (S.ψ ls) (consList fs' (envP ps)) tele.reverse)
      (fun ys => S.idxVals M ls (consList ys.reverse (consList fs' (envP ps))) es)
      (toTeleX ps rest (pt :: fs'))

/-- The block's constructors as constructor telescopes with their
targets, at the parameters. -/
def ctorsX (ps : List V) : List (TeleX (List V) V × (List V → List V)) :=
  S.ctors.map fun c =>
    (S.toTeleX M ls ps c.fields.reverse [],
      fun fsO => S.idxVals M ls (consList fsO.reverse (envP ps)) c.idx)

/-- **The bounding family** at the parameters: what the inductive
closure law supplies for the block's constructors (the point where
the result sort is zero: no bound is needed there). -/
noncomputable def bound (ps : List V) : List V → V :=
  open Classical in if h : S.u₀ ls ≠ 0 then Classical.choose (inductive_closure h (S.ctorsX M ls ps)) else fun _ => pt

theorem bound_spec (ps : List V) (h : S.u₀ ls ≠ 0) :
    (∀ is, S.bound M ls ps is ∈ˢ (univ (S.u₀ ls) : V)) ∧
      ∀ (j : Nat) c (fs : List V), (S.ctorsX M ls ps)[j]? = some c →
        TeleX.FitsB (S.u₀ ls) (S.bound M ls ps) c.1 fs →
        tag j (tuple fs) ∈ˢ S.bound M ls ps (c.2 fs) := by
  unfold bound
  rw [dif_pos h]
  exact Classical.choose_spec (inductive_closure h (S.ctorsX M ls ps))

/-- **The family**, as a predicate: the least fixed point of `step`. -/
noncomputable def Mem (ps is : List V) (x : V) : Prop := Lfp (S.stepT M ls (S.bound M ls)) (ps, is, x)

/-- **The fibre** of the family at parameters and indices. -/
noncomputable def Fam (ps is : List V) : V := fibreR (S.z ls) (S.bound M ls ps is) (S.Mem M ls ps is)

/-- **A constructor's value** at its fields: the point at a
proposition, the tagged tuple above. -/
def ctorVal (j : Nat) (fs : List V) : V := if S.z ls then pt else tag j (tuple fs.reverse)

/-! ### Monotonicity and the fixed-point laws -/

theorem fieldSet_mono {B : List V → List V → V} {P Q : FamP V}
    (h : ∀ ps is x, P ps is x → Q ps is x) (ps fs : List V) :
    ∀ f : Field, S.fieldSet M ls B P ps fs f ⊆ˢ S.fieldSet M ls B Q ps fs f
  | .ordinary _ => Sub.refl _
  | .recursive _ => fibreR_mono (h _ _)
  | .reflexive tele es => by
    simp only [fieldSet]
    exact piCtx_sub M _ fun _ _ => fibreR_mono (h _ _)

theorem FitsFields_mono {B : List V → List V → V} {P Q : FamP V}
    (h : ∀ ps is x, P ps is x → Q ps is x) (ps : List V) :
    ∀ {fields : List Field} {fs : List V},
      S.FitsFields M ls B P ps fields fs → S.FitsFields M ls B Q ps fields fs
  | [], [], _ => trivial
  | _ :: _, _ :: fs, hf =>
    ⟨FitsFields_mono h ps hf.1, S.fieldSet_mono M ls h ps fs _ _ hf.2⟩
  | [], _ :: _, hf => hf.elim
  | _ :: _, [], hf => hf.elim

theorem stepT_mono (B : List V → List V → V) : Mono (S.stepT M ls B) := by
  intro P Q h t hs
  obtain ⟨j, c, fs, hc, hfit, his, hx⟩ := hs
  exact ⟨j, c, fs, hc, S.FitsFields_mono M ls (fun ps is x => h (ps, is, x)) _ hfit, his, hx⟩

/-- Introduction: a step from members is a member. -/
theorem Mem_intro {ps is : List V} {x : V} (h : S.step M ls (S.bound M ls) (S.Mem M ls) ps is x) :
    S.Mem M ls ps is x :=
  Lfp.closed (S.stepT_mono M ls _) h

/-- Inversion: a member is a step from members. -/
theorem Mem_elim {ps is : List V} {x : V} (h : S.Mem M ls ps is x) :
    S.step M ls (S.bound M ls) (S.Mem M ls) ps is x :=
  Lfp.unfold (S.stepT_mono M ls _) h

/-- Induction over the family. -/
theorem Mem_ind {P : FamP V}
    (h : ∀ ps is x, S.step M ls (S.bound M ls) (fun ps is x => S.Mem M ls ps is x ∧ P ps is x) ps is x →
      P ps is x)
    {ps is : List V} {x : V} (hm : S.Mem M ls ps is x) : P ps is x :=
  Lfp.induction (S.stepT_mono M ls _) (P := fun t => P t.1 t.2.1 t.2.2)
    (fun t ht => h t.1 t.2.1 t.2.2 ht) hm

/-- A member of a propositional fibre is the point; of a type-valued
one, a member of the family. -/
theorem mem_Fam_true {ps is : List V} {t : V} (hz : S.z ls = true) :
    t ∈ˢ S.Fam M ls ps is ↔ t = pt ∧ ∃ x, S.Mem M ls ps is x := by
  simp only [Fam, hz]; exact mem_fibreR_true

theorem mem_Fam_false {ps is : List V} {t : V} (hz : S.z ls = false) :
    t ∈ˢ S.Fam M ls ps is ↔ t ∈ˢ S.bound M ls ps is ∧ S.Mem M ls ps is t := by
  simp only [Fam, hz]; exact mem_fibreR_false

theorem Mem_of_mem_Fam_false {ps is : List V} {t : V} (hz : S.z ls = false)
    (h : t ∈ˢ S.Fam M ls ps is) : S.Mem M ls ps is t := ((S.mem_Fam_false M ls hz).mp h).2

/-- **The fibre is in the result universe.** -/
theorem Fam_mem_univ (ps is : List V) : S.Fam M ls ps is ∈ˢ (univ (S.u₀ ls) : V) :=
  fibreR_mem_univ (S.z_iff ls) fun hz =>
    (S.bound_spec M ls ps fun h0 => by simp [(S.z_iff ls).mpr h0] at hz).1 is

/-! ### Reading the fields -/

/-- The value of the field with `k` earlier fields. -/
def fieldVal (fs : List V) (k : Nat) : V := fs.getD (fs.length - 1 - k) pt

/-- The values of the `k` earlier fields. -/
def earlier (fs : List V) (k : Nat) : List V := fs.drop (fs.length - k)

theorem FitsFields_length {B : List V → List V → V} {P : FamP V} {ps : List V} :
    ∀ {fields : List Field} {fs : List V}, S.FitsFields M ls B P ps fields fs →
      fs.length = fields.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [FitsFields_length h.1]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem fieldVal_cons {v : V} {fs : List V} {k : Nat} (hk : k < fs.length) :
    fieldVal (v :: fs) k = fieldVal fs k := by
  simp only [fieldVal, List.length_cons]
  rw [show fs.length + 1 - 1 - k = (fs.length - 1 - k) + 1 by omega, List.getD_cons_succ]

omit [IndLib V] in
theorem earlier_cons {v : V} {fs : List V} {k : Nat} (hk : k ≤ fs.length) :
    earlier (v :: fs) k = earlier fs k := by
  simp only [earlier, List.length_cons]
  rw [show fs.length + 1 - k = (fs.length - k) + 1 by omega, List.drop_succ_cons]

/-- Each field of a fitting list is a member of its domain at the
earlier fields. -/
theorem FitsFields_get {B : List V → List V → V} {P : FamP V} {ps : List V} :
    ∀ {fields : List Field} {fs : List V}, S.FitsFields M ls B P ps fields fs →
      ∀ {k : Nat} {f : Field}, fields[fields.length - 1 - k]? = some f → k < fields.length →
        fieldVal fs k ∈ˢ S.fieldSet M ls B P ps (earlier fs k) f
  | [], [], _, k, _, _, hk => by simp at hk
  | f' :: fields, v :: fs, hf, k, f, h, hk => by
    have hlen := S.FitsFields_length M ls hf.1
    by_cases hkl : k = fields.length
    · subst hkl
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self, List.getElem?_cons_zero,
        Option.some.injEq] at h
      subst h
      simp only [fieldVal, earlier, List.length_cons, hlen, Nat.add_sub_cancel, Nat.sub_self,
        List.getD_cons_zero]
      rw [show fields.length + 1 - fields.length = 1 by omega, List.drop_succ_cons, List.drop_zero]
      exact hf.2
    · have hk' : k < fields.length := by simp at hk; omega
      have : fields.length + 1 - 1 - k = (fields.length - 1 - k) + 1 := by omega
      simp only [List.length_cons, this, List.getElem?_cons_succ] at h
      rw [fieldVal_cons (by omega), earlier_cons (by omega)]
      exact FitsFields_get hf.1 h hk'
  | [], _ :: _, hf, _, _, _, _ => hf.elim
  | _ :: _, [], hf, _, _, _, _ => hf.elim

/-! ### Constructor values are in the fibre

Above a proposition a constructor value must be shown a member of the
bounding family: the fitting fields are a bounded instance of the
constructor's telescope.  Two facts about the block are needed, both
supplied by the checker (`Install.lean`): the domains met along a
fitting instance are members of the universe (`DomsBounded` — the
universe bound on fields), and no domain or index expression reads an
earlier recursive field (`NoRecDep` — the value at a recursive
position is replaced by the point when the telescope is read). -/

/-- Replace the values at recursive positions by the point. -/
def junkRec : List Field → List V → List V
  | f :: fields, v :: vs => (if f.isRec then pt else v) :: junkRec fields vs
  | _, vs => vs

/-- **No field reads an earlier recursive field** (the block-level
hypothesis). -/
def NoRecDep : Prop :=
  ∀ c ∈ S.ctors, ∀ i f, c.fields[i]? = some f → fieldNoRecDep (c.fields.drop (i + 1)) f

/-- **The domains met along a fitting instance are members of the
result universe** (the block-level hypothesis, above a proposition):
an ordinary domain at the earlier fields, and every entry of a
reflexive field's telescope. -/
noncomputable def DomsBounded (ps : List V) : Prop :=
  S.z ls = false → ∀ c ∈ S.ctors, ∀ fs, S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs →
    ∀ k f, c.fields[c.fields.length - 1 - k]? = some f → k < c.fields.length →
      match f with
      | .ordinary A => interp M (S.ψ ls) (consList (earlier fs k) (envP ps)) A ∈ˢ (univ (S.u₀ ls) : V)
      | .reflexive tele _ =>
        TeleS.Bounded (S.u₀ ls) (toTeleS M (S.ψ ls) (consList (earlier fs k) (envP ps)) tele.reverse)
      | .recursive _ => True

theorem junkRec_length : ∀ (fields : List Field) (fs : List V), (junkRec fields fs).length = fs.length
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: fields, _ :: fs => by simp [junkRec, junkRec_length fields fs]

theorem junkRec_cons (f : Field) (fields : List Field) (v : V) (fs : List V) :
    junkRec (f :: fields) (v :: fs) = (if f.isRec then pt else v) :: junkRec fields fs := rfl

/-- The junked values agree with the values at every non-recursive
position. -/
theorem consList_junkRec_eq (ρ : Nat → V) :
    ∀ (fields : List Field) (fs : List V) (i : Nat),
      (∀ f, fields[i]? = some f → f.isRec = false) →
      consList (junkRec fields fs) ρ i = consList fs ρ i
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | f :: _, _ :: _, 0, h => by
    have := h f rfl
    simp [junkRec_cons, this]
  | _ :: fields, _ :: fs, i + 1, h => by
    simp only [junkRec_cons, consList_cons, cons_succ]
    exact consList_junkRec_eq ρ fields fs i fun f' hf' => h f' hf'

/-- An expression that reads no recursive earlier field reads alike
under the values and under the junked values (`d` own binders on
top). -/
theorem interp_junkRec {fields : List Field} {fs ys : List V} {d : Nat} (ρ : Nat → V) (e : Expr)
    (hy : ys.length = d)
    (h : ∀ i f, fields[i]? = some f → f.isRec = true → e.usesVar (d + i) = false) :
    interp M (S.ψ ls) (consList ys (consList (junkRec fields fs) ρ)) e
      = interp M (S.ψ ls) (consList ys (consList fs ρ)) e := by
  apply interp_usesVar
  intro j hj
  by_cases hjd : j < d
  · rw [consList_lt (by omega), consList_lt (by omega)]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + d := ⟨j - d, by omega⟩
    rw [← hy, consList_ge, consList_ge]
    apply consList_junkRec_eq
    intro f hf
    cases hr : f.isRec with
    | false => rfl
    | true =>
      exfalso
      have := h i f hf hr
      rw [Nat.add_comm] at hj
      simp [this] at hj

theorem toTeleS_congr {ρ ρ' : Nat → V} :
    ∀ (L : List Expr), (∀ (t : Nat) (T : Expr), L[t]? = some T →
      ∀ ys : List V, ys.length = t → interp M (S.ψ ls) (consList ys ρ) T = interp M (S.ψ ls) (consList ys ρ') T) →
      toTeleS M (S.ψ ls) ρ L = toTeleS M (S.ψ ls) ρ' L
  | [], _ => rfl
  | T :: L, h => by
    simp only [toTeleS]
    have h0 := h 0 T rfl [] rfl
    simp only [consList_nil] at h0
    rw [h0]
    congr 1
    funext y
    apply toTeleS_congr L
    intro t T' hT ys hys
    have := h (t + 1) T' (by simpa using hT) (ys ++ [y]) (by simp [hys])
    simpa [consList_append] using this

/-- The nested product over a telescope of expressions is the nested
function space over the telescope of sets it reads as (above a
proposition; values outermost first). -/
theorem TeleS_pi_toTeleS_append (A : Expr) :
    ∀ (L : List Expr) (ρ : Nat → V) (F : List V → V),
      TeleS.pi (toTeleS M (S.ψ ls) ρ (L ++ [A])) F
        = TeleS.pi (toTeleS M (S.ψ ls) ρ L) fun ys =>
            piSet (interp M (S.ψ ls) (consList ys.reverse ρ) A) fun x => F (ys ++ [x])
  | [], ρ, F => by simp [toTeleS, TeleS.pi]
  | T :: L, ρ, F => by
    simp only [List.cons_append, toTeleS, TeleS.pi]
    congr 1
    funext y
    rw [TeleS_pi_toTeleS_append A L (cons y ρ)]
    congr 1
    funext ys
    simp [consList_append]

theorem piCtx_false_eq_pi :
    ∀ (Γ : List Expr) (ρ : Nat → V) (G : (Nat → V) → V),
      piCtx M (S.ψ ls) false ρ Γ G
        = TeleS.pi (toTeleS M (S.ψ ls) ρ Γ.reverse) fun ys => G (consList ys.reverse ρ)
  | [], _, _ => rfl
  | A :: Γ, ρ, G => by
    simp only [piCtx_cons, List.reverse_cons]
    rw [TeleS_pi_toTeleS_append, piCtx_false_eq_pi Γ ρ]
    congr 1
    funext ys
    simp [piR_false]

theorem toTeleS_fits_length {ρ : Nat → V} :
    ∀ {L : List Expr} {ys : List V}, (toTeleS M (S.ψ ls) ρ L).Fits ys → ys.length = L.length
  | [], [], _ => rfl
  | _ :: L, _ :: ys, h => by simp [toTeleS_fits_length (L := L) (ys := ys) h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem _root_.Fragment.TeleS.pi_mono {F G : List V → V} :
    ∀ (T : TeleS V), (∀ ys, T.Fits ys → F ys ⊆ˢ G ys) → T.pi F ⊆ˢ T.pi G
  | .nil, h => h [] trivial
  | .cons A B, h => by
    simp only [TeleS.pi]
    refine piSet_mono fun v hv => ?_
    exact TeleS.pi_mono (B v) fun ys hys => h (v :: ys) ⟨hv, hys⟩

/-- A field's fit is read off the whole list. -/
theorem FitsFields_middle {B : List V → List V → V} {P : FamP V} {ps : List V} {f : Field} :
    ∀ {L : List Field} {done : List Field} {vsL : List V} {v : V} {fsDone : List V},
      vsL.length = L.length →
      S.FitsFields M ls B P ps (L ++ f :: done) (vsL ++ v :: fsDone) →
      v ∈ˢ S.fieldSet M ls B P ps fsDone f
  | [], _, [], _, _, _, h => h.2
  | _ :: L, done, _ :: vsL, v, fsDone, hl, h =>
    FitsFields_middle (L := L) (by simpa using hl) h.1
  | [], _, _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, _, [], _, _, hl, _ => by simp at hl

/-- **A fitting instance is a bounded instance** of the constructor's
telescope of sets (above a proposition), given that no field reads an
earlier recursive one and that the domains met are members. -/
theorem FitsB_of_FitsFields (hz : S.z ls = false) {c : CtorSpec} {ps fs : List V}
    (hfit : S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs)
    (hnr : ∀ i f, c.fields[i]? = some f → fieldNoRecDep (c.fields.drop (i + 1)) f)
    (hb : ∀ k f, c.fields[c.fields.length - 1 - k]? = some f → k < c.fields.length →
      match f with
      | .ordinary A => interp M (S.ψ ls) (consList (earlier fs k) (envP ps)) A ∈ˢ (univ (S.u₀ ls) : V)
      | .reflexive tele _ =>
        TeleS.Bounded (S.u₀ ls) (toTeleS M (S.ψ ls) (consList (earlier fs k) (envP ps)) tele.reverse)
      | .recursive _ => True) :
    ∀ (L done : List Field) (vsO fsDone : List V), vsO.length = L.length →
      c.fields = L.reverse ++ done → fs = vsO.reverse ++ fsDone →
      TeleX.FitsB (S.u₀ ls) (S.bound M ls ps) (S.toTeleX M ls ps L (junkRec done fsDone)) vsO
  | [], done, [], fsDone, _, hc, hfs => by simp [toTeleX, TeleX.FitsB]
  | f :: L, done, v :: vs, fsDone, hl, hc, hfs => by
    have hl' : vs.length = L.length := by simpa using hl
    have hc' : c.fields = L.reverse ++ f :: done := by simpa [List.append_assoc] using hc
    have hfs' : fs = vs.reverse ++ v :: fsDone := by simpa [List.append_assoc] using hfs
    have hlen := S.FitsFields_length M ls hfit
    have hfv : v ∈ˢ S.fieldSet M ls (S.bound M ls) (S.Mem M ls) ps fsDone f := by
      rw [hc', hfs'] at hfit
      exact S.FitsFields_middle M ls (by simpa using hl') hfit
    -- the field's position and its earlier fields
    have hpos : c.fields[c.fields.length - 1 - done.length]? = some f := by
      rw [hc']
      have : (L.reverse ++ f :: done).length - 1 - done.length = L.reverse.length := by
        simp only [List.length_append, List.length_reverse, List.length_cons]; omega
      rw [this, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    have hklt : done.length < c.fields.length := by
      rw [hc']; simp only [List.length_append, List.length_reverse, List.length_cons]; omega
    have hdl : fsDone.length = done.length := by
      rw [hfs', hc'] at hlen; simp at hlen; omega
    have hearlier : earlier fs done.length = fsDone := by
      rw [hfs', earlier]
      have : (vs.reverse ++ v :: fsDone).length - done.length = vs.reverse.length + 1 := by
        simp only [List.length_append, List.length_reverse, List.length_cons]; omega
      rw [this, ← List.drop_drop, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length]
      rfl
    have hdrop : c.fields.drop (c.fields.length - 1 - done.length + 1) = done := by
      rw [hc']
      have : (L.reverse ++ f :: done).length - 1 - done.length + 1 = L.reverse.length + 1 := by
        simp only [List.length_append, List.length_reverse, List.length_cons]; omega
      rw [this, ← List.drop_drop, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length]
      rfl
    have hnr' := hnr _ f hpos
    rw [hdrop] at hnr'
    have hb' := hb done.length f hpos hklt
    rw [hearlier] at hb'
    have ih := FitsB_of_FitsFields hz hfit hnr hb L (f :: done) vs (v :: fsDone) hl' hc' hfs'
    cases f with
    | ordinary A =>
      simp only [toTeleX, TeleX.FitsB]
      have hA : interp M (S.ψ ls) (consList (junkRec done fsDone) (envP ps)) A
          = interp M (S.ψ ls) (consList fsDone (envP ps)) A :=
        S.interp_junkRec M ls (envP ps) A (ys := []) rfl fun i f' hf' hr => by
          simpa using hnr' i f' hf' hr
      rw [hA]
      refine ⟨hb', hfv, ?_⟩
      simpa [junkRec_cons, Field.isRec] using ih
    | recursive es =>
      simp only [toTeleX, TeleX.FitsB]
      have hes : S.idxVals M ls (consList (junkRec done fsDone) (envP ps)) es
          = S.idxVals M ls (consList fsDone (envP ps)) es := by
        simp only [idxVals]
        congr 1
        apply List.map_congr_left
        intro e he
        exact S.interp_junkRec M ls (envP ps) e (ys := []) rfl
          fun i f' hf' hr => by simpa using hnr' i f' hf' hr e he
      rw [hes]
      simp only [fieldSet, hz] at hfv
      refine ⟨(mem_fibreR_false.mp hfv).1, ?_⟩
      simpa [junkRec_cons, Field.isRec] using ih
    | reflexive tele es =>
      simp only [toTeleX, TeleX.FitsB]
      have hT : toTeleS M (S.ψ ls) (consList (junkRec done fsDone) (envP ps)) tele.reverse
          = toTeleS M (S.ψ ls) (consList fsDone (envP ps)) tele.reverse := by
        apply S.toTeleS_congr M ls
        intro t T hT ys hys
        have ht : t < tele.length := by
          have := List.getElem?_eq_some_iff.mp hT
          simpa using this.1
        rw [List.getElem?_reverse ht] at hT
        exact S.interp_junkRec M ls (envP ps) T hys fun i f' hf' hr => by
          have := (hnr' i f' hf' hr).1 (tele.length - 1 - t) T hT
          rwa [show tele.length - 1 - (tele.length - 1 - t) = t by omega] at this
      rw [hT]
      refine ⟨hb', ?_, ?_⟩
      · simp only [fieldSet, hz] at hfv
        rw [S.piCtx_false_eq_pi M ls tele] at hfv
        refine TeleS.pi_mono _ (fun ys hys => ?_) _ hfv
        have hyl : ys.length = tele.length := by
          have := S.toTeleS_fits_length M ls hys; simpa using this
        have hes : S.idxVals M ls (consList ys.reverse (consList (junkRec done fsDone) (envP ps))) es
            = S.idxVals M ls (consList ys.reverse (consList fsDone (envP ps))) es := by
          simp only [idxVals]
          congr 1
          apply List.map_congr_left
          intro e he
          exact S.interp_junkRec M ls (envP ps) e (ys := ys.reverse) (d := tele.length)
            (by simp [hyl]) fun i f' hf' hr => (hnr' i f' hf' hr).2 e he
        rw [hes]
        intro x hx
        exact (mem_fibreR_false.mp hx).1
      · simpa [junkRec_cons, Field.isRec] using ih
  | [], _, _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, _, [], _, hl, _, _ => by simp at hl

/-- **A constructor's value is in the fibre** at its index expressions
when its fields fit. -/
theorem ctorVal_mem_Fam {j : Nat} {c : CtorSpec} {ps fs : List V} (hc : S.ctors[j]? = some c)
    (hfit : S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs)
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) :
    S.ctorVal ls j fs ∈ˢ S.Fam M ls ps (S.idxVals M ls (consList fs (envP ps)) c.idx) := by
  have hmem : S.Mem M ls ps (S.idxVals M ls (consList fs (envP ps)) c.idx)
      (tag j (tuple fs.reverse)) :=
    S.Mem_intro M ls ⟨j, c, fs, hc, hfit, rfl, rfl⟩
  unfold ctorVal
  cases hz : S.z ls
  · rw [mem_Fam_false _ _ _ hz]
    refine ⟨?_, hmem⟩
    have hn : S.u₀ ls ≠ 0 := fun h0 => by simp [(S.z_iff ls).mpr h0] at hz
    have hcx : (S.ctorsX M ls ps)[j]? = some (S.toTeleX M ls ps c.fields.reverse [],
        fun fsO => S.idxVals M ls (consList fsO.reverse (envP ps)) c.idx) := by
      simp [ctorsX, hc]
    have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
    have hB := S.FitsB_of_FitsFields M ls hz hfit (hnr c hcm) (hb hz c hcm fs hfit)
      c.fields.reverse [] fs.reverse [] (by simp [S.FitsFields_length M ls hfit]) (by simp) (by simp)
    dsimp only [junkRec] at hB
    have := (S.bound_spec M ls ps hn).2 j _ fs.reverse hcx hB
    simpa using this
  · rw [mem_Fam_true _ _ _ hz]
    exact ⟨rfl, _, hmem⟩

/-! ## The recursor -/

/-- A witness of the fibre: some member of the family at `ps`, `is`,
or the point when there is none. -/
noncomputable def pick (ps is : List V) : V :=
  open Classical in if h : ∃ x, S.Mem M ls ps is x then Classical.choose h else pt

theorem Mem_pick {ps is : List V} (h : ∃ x, S.Mem M ls ps is x) :
    S.Mem M ls ps is (S.pick M ls ps is) := by
  unfold pick; rw [dif_pos h]; exact Classical.choose_spec h

/-- **The witness the recursor recurses on**: at a proposition the
major is the point and carries nothing, so the fibre's witness stands
in; above, the major itself. -/
noncomputable def wit (ps is : List V) (t : V) : V := if S.z ls then S.pick M ls ps is else t

/-- The member of the fibre a witness stands for: the point at a
proposition, the witness itself above. -/
def memb (x : V) : V := if S.z ls then pt else x

/-- **Uniqueness of witnesses**: at a proposition the fibre has at most
one member of the family — what the subsingleton criterion buys
(`Install.lean`). -/
noncomputable def Uniq : Prop :=
  S.z ls = true → ∀ ps : List V, FitsVals M (S.ψ ls) base S.params ps →
    ∀ (is : List V) (x x' : V), S.Mem M ls ps is x → S.Mem M ls ps is x' → x = x'

/-- The witness of a fitting recursive field is a member of the
family at the field's indices — and, given uniqueness, has every
property some member has. -/
theorem wit_of_fibre {ps is : List V} {v : V} {P : FamP V} (hu : S.Uniq M ls)
    (hp : FitsVals M (S.ψ ls) base S.params ps)
    (hv : v ∈ˢ fibreR (S.z ls) (S.bound M ls ps is) fun x => S.Mem M ls ps is x ∧ P ps is x) :
    S.Mem M ls ps is (S.wit M ls ps is v) ∧ P ps is (S.wit M ls ps is v) ∧
      S.memb ls (S.wit M ls ps is v) = v := by
  unfold wit memb
  cases hz : S.z ls
  · rw [hz] at hv; exact ⟨(mem_fibreR_false.mp hv).2.1, (mem_fibreR_false.mp hv).2.2, rfl⟩
  · rw [hz] at hv
    obtain ⟨rfl, y, hy, hP⟩ := mem_fibreR_true.mp hv
    have hpk := S.Mem_pick M ls ⟨y, hy⟩
    rw [hu hz ps hp _ _ _ hpk hy]
    exact ⟨hy, hP, rfl⟩


variable (q : Bool)

/-- **An inductive hypothesis' value** relative to a graph `R`: at a
recursive field, `R`'s value at the field's index expressions and the
witness of the field; at a reflexive field, the abstraction over the
field's telescope of those values. -/
noncomputable def IhOk (R : RecP V) (ps : List V) (m : V) (mins fs : List V) : Nat × Field → V → Prop
  | (k, .recursive es), ih =>
    let is := S.idxVals M ls (consList (earlier fs k) (envP ps)) es
    R ps m mins is (S.wit M ls ps is (fieldVal fs k)) ih
  | (k, .reflexive tele es), ih =>
    let env := consList (earlier fs k) (envP ps)
    ∃ g : (Nat → V) → V, ih = lamCtx M (S.ψ ls) q env tele g ∧
      ∀ ys, FitsVals M (S.ψ ls) env tele ys →
        let is := S.idxVals M ls (consList ys env) es
        R ps m mins is (S.wit M ls ps is (appList (fieldVal fs k) ys.reverse)) (g (consList ys env))
  | (_, .ordinary _), _ => False

/-- The minor for constructor `j` among the minors (innermost first). -/
def minorAt (mins : List V) (j : Nat) : V := mins.getD (S.n - 1 - j) pt

/-- **The operator** whose least fixed point is the recursor's graph:
at the tagged tuple of fitting fields, the value is the constructor's
minor at the fields and the inductive hypotheses. -/
noncomputable def rstep (R : RecP V) (ps : List V) (m : V) (mins is : List V) (x v : V) : Prop :=
  ∃ j c fs ihs, S.ctors[j]? = some c ∧ S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs ∧
    is = S.idxVals M ls (consList fs (envP ps)) c.idx ∧ x = tag j (tuple fs.reverse) ∧
    ListRel (S.IhOk M ls q R ps m mins fs) c.recFields ihs ∧
    v = appList (S.minorAt mins j) (fs.reverse ++ ihs)

/-- The operator on sextuples. -/
noncomputable def rstepT (R : List V × V × List V × List V × V × V → Prop)
    (t : List V × V × List V × List V × V × V) : Prop :=
  S.rstep M ls q (fun ps m mins is x v => R (ps, m, mins, is, x, v))
    t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2

/-- **The recursor's graph**: the least fixed point of `rstep`. -/
noncomputable def RecGraph (ps : List V) (m : V) (mins is : List V) (x v : V) : Prop :=
  Lfp (S.rstepT M ls q) (ps, m, mins, is, x, v)

theorem IhOk_mono {R R' : RecP V} (h : ∀ ps m mins is x v, R ps m mins is x v → R' ps m mins is x v)
    (ps : List V) (m : V) (mins fs : List V) :
    ∀ (kf : Nat × Field) (ih : V),
      S.IhOk M ls q R ps m mins fs kf ih → S.IhOk M ls q R' ps m mins fs kf ih := by
  intro kf ih hh
  match kf, hh with
  | (_, .ordinary _), hh => exact hh.elim
  | (_, .recursive _), hh => exact h _ _ _ _ _ _ hh
  | (_, .reflexive _ _), ⟨g, hg, hall⟩ => exact ⟨g, hg, fun ys hys => h _ _ _ _ _ _ (hall ys hys)⟩

theorem rstepT_mono : Mono (S.rstepT M ls q) := by
  intro R R' h t hs
  obtain ⟨j, c, fs, ihs, hc, hfit, his, hx, hihs, hv⟩ := hs
  exact ⟨j, c, fs, ihs, hc, hfit, his, hx,
    ListRel.mono (S.IhOk_mono M ls q (fun ps m mins is x v => h (ps, m, mins, is, x, v)) _ _ _ _)
      hihs, hv⟩

theorem RecGraph_intro {ps : List V} {m : V} {mins is : List V} {x v : V}
    (h : S.rstep M ls q (S.RecGraph M ls q) ps m mins is x v) :
    S.RecGraph M ls q ps m mins is x v :=
  Lfp.closed (S.rstepT_mono M ls q) h

theorem RecGraph_elim {ps : List V} {m : V} {mins is : List V} {x v : V}
    (h : S.RecGraph M ls q ps m mins is x v) :
    S.rstep M ls q (S.RecGraph M ls q) ps m mins is x v :=
  Lfp.unfold (S.rstepT_mono M ls q) h

theorem RecGraph_ind {P : RecP V}
    (h : ∀ ps m mins is x v,
      S.rstep M ls q (fun ps m mins is x v => S.RecGraph M ls q ps m mins is x v ∧ P ps m mins is x v)
        ps m mins is x v → P ps m mins is x v)
    {ps : List V} {m : V} {mins is : List V} {x v : V} (hg : S.RecGraph M ls q ps m mins is x v) :
    P ps m mins is x v :=
  Lfp.induction (S.rstepT_mono M ls q)
    (P := fun t => P t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2)
    (fun _ ht => h _ _ _ _ _ _ ht) hg

/-- **Single-valuedness of the graph**: tags and tuples are injective,
so two values at one witness come from one constructor and one list of
fields, and their inductive hypotheses agree by induction. -/
theorem RecGraph_fun {ps : List V} {m : V} {mins is : List V} {x v v' : V}
    (h : S.RecGraph M ls q ps m mins is x v) (h' : S.RecGraph M ls q ps m mins is x v') : v = v' := by
  refine S.RecGraph_ind M ls q
    (P := fun ps m mins is x v => ∀ v', S.RecGraph M ls q ps m mins is x v' → v = v') ?_ h v' h'
  intro ps m mins is x v hs v' h'
  obtain ⟨j, c, fs, ihs, hc, -, -, hx, hihs, hv⟩ := hs
  obtain ⟨j', c', fs', ihs', hc', -, -, hx', hihs', hv'⟩ := S.RecGraph_elim M ls q h'
  subst hx
  obtain ⟨rfl, hfs⟩ := tag_inj hx'
  have := List.reverse_inj.mp (tuple_inj hfs)
  subst this
  rw [hc] at hc'
  cases hc'
  subst hv hv'
  congr 2
  refine ListRel.unique ?_ hihs hihs'
  intro kf ih ih' h1 h2
  match kf, h1, h2 with
  | (_, .ordinary _), h1, _ => exact h1.elim
  | (_, .recursive _), h1, h2 => exact h1.2 _ h2
  | (_, .reflexive _ _), ⟨_, hg1, hg⟩, ⟨_, hg1', hg'⟩ =>
    rw [hg1, hg1']
    exact lamCtx_congr M _ fun ys hys => (hg ys hys).2 _ (hg' ys hys)

/-- **The recursor's value**: the one the graph relates, if any. -/
noncomputable def recFn (ps : List V) (m : V) (mins is : List V) (x : V) : V :=
  open Classical in
  if h : ∃ v, S.RecGraph M ls q ps m mins is x v then Classical.choose h else pt

theorem recFn_eq {ps : List V} {m : V} {mins is : List V} {x v : V}
    (h : S.RecGraph M ls q ps m mins is x v) : S.recFn M ls q ps m mins is x = v := by
  unfold recFn
  rw [dif_pos ⟨v, h⟩]
  exact S.RecGraph_fun M ls q (Classical.choose_spec ⟨v, h⟩) h

theorem RecGraph_recFn {ps : List V} {m : V} {mins is : List V} {x : V}
    (h : ∃ v, S.RecGraph M ls q ps m mins is x v) :
    S.RecGraph M ls q ps m mins is x (S.recFn M ls q ps m mins is x) := by
  obtain ⟨v, hv⟩ := h
  rw [S.recFn_eq M ls q hv]; exact hv

/-- **The recursor's semantic value** at parameters, motive, minors,
indices and the major: the graph's value at the witness. -/
noncomputable def recSem (ps : List V) (m : V) (mins is : List V) (t : V) : V :=
  S.recFn M ls q ps m mins is (S.wit M ls ps is t)

/-- **The inductive hypotheses' semantic values**, one per recursive
or reflexive field: the recursor at the field (through its telescope
at a reflexive field). -/
noncomputable def ihSem (ps : List V) (m : V) (mins fs : List V) : Nat × Field → V
  | (k, .recursive es) =>
    S.recSem M ls q ps m mins (S.idxVals M ls (consList (earlier fs k) (envP ps)) es) (fieldVal fs k)
  | (k, .reflexive tele es) =>
    let env := consList (earlier fs k) (envP ps)
    lamCtx M (S.ψ ls) q env tele fun ρ' =>
      S.recSem M ls q ps m mins (S.idxVals M ls ρ' es)
        (appList (fieldVal fs k) (readEnv tele.length ρ').reverse)
  | (_, .ordinary _) => pt

/-- A recursive position of a constructor is a recursive or reflexive
field at that position. -/
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

/-- **Totality of the graph on the family** (with single-valuedness,
the recursion theorem): by induction over the family, the inductive
hypotheses exist because the fields' witnesses are members with
values. -/
theorem RecGraph_total (hu : S.Uniq M ls) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) {is : List V} {x : V} (hm : S.Mem M ls ps is x)
    (m : V) (mins : List V) : ∃ v, S.RecGraph M ls q ps m mins is x v := by
  revert m mins
  suffices key : ∀ ps' is x, S.Mem M ls ps' is x → ps' = ps →
      ∀ m mins, ∃ v, S.RecGraph M ls q ps' m mins is x v from key ps is x hm rfl
  intro ps' is x hm
  refine S.Mem_ind M ls (P := fun ps' is x => ps' = ps → ∀ m mins, ∃ v, S.RecGraph M ls q ps' m mins is x v) ?_ hm
  intro ps' is x hs hps
  subst ps'
  intro m mins
  obtain ⟨j, c, fs, hc, hfit, his, hx⟩ := hs
  have hfitM := S.FitsFields_mono M ls (fun _ _ _ h => h.1) ps hfit
  suffices hihs : ListRel (S.IhOk M ls q (S.RecGraph M ls q) ps m mins fs) c.recFields
      (c.recFields.map (S.ihSem M ls q ps m mins fs)) from
    ⟨_, S.RecGraph_intro M ls q ⟨j, c, fs, _, hc, hfitM, his, hx, hihs, rfl⟩⟩
  refine ListRel.map ?_
  intro kf hkf
  obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
  have hget := S.FitsFields_get M ls hfit hf hk
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | recursive es =>
    dsimp only [fieldSet] at hget
    obtain ⟨-, hP, -⟩ := S.wit_of_fibre M ls hu hp
      (P := fun a is x => a = ps → ∀ m mins, ∃ v, S.RecGraph M ls q a m mins is x v) hget
    exact S.RecGraph_recFn M ls q (hP rfl m mins)
  | reflexive tele es =>
    dsimp only [fieldSet] at hget
    dsimp only [IhOk, ihSem]
    refine ⟨_, rfl, ?_⟩
    intro ys hys
    have hlen := FitsVals_length M _ hys
    have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys fun hz _ _ => by
      simp only [hz, fibreR, if_true]; exact truthVal_mem_univ_zero _
    obtain ⟨-, hP, -⟩ := S.wit_of_fibre M ls hu hp
      (P := fun a is x => a = ps → ∀ m mins, ∃ v, S.RecGraph M ls q a m mins is x v) hmem
    simp only [readEnv_consList hlen]
    exact S.RecGraph_recFn M ls q (hP rfl m mins)

/-- The inductive hypotheses' semantic values are what the graph
demands. -/
theorem IhOk_ihSem (hu : S.Uniq M ls) {ps : List V} (hp : FitsVals M (S.ψ ls) base S.params ps)
    {c : CtorSpec} {fs : List V}
    (hfit : S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs) (m : V) (mins : List V) :
    ListRel (S.IhOk M ls q (S.RecGraph M ls q) ps m mins fs) c.recFields
      (c.recFields.map (S.ihSem M ls q ps m mins fs)) := by
  refine ListRel.map ?_
  intro kf hkf
  obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
  have hget := S.FitsFields_get M ls hfit hf hk
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | recursive es =>
    simp only [fieldSet] at hget
    have hget' : fieldVal fs k ∈ˢ fibreR (S.z ls) (S.bound M ls ps _)
        fun x => S.Mem M ls ps _ x ∧ True :=
      fibreR_mono (fun _ h => ⟨h, trivial⟩) _ hget
    obtain ⟨hw, -, -⟩ := S.wit_of_fibre M ls hu hp (P := fun _ _ _ => True) hget'
    exact S.RecGraph_recFn M ls q (S.RecGraph_total M ls q hu hp hw m mins)
  | reflexive tele es =>
    simp only [fieldSet] at hget
    dsimp only [IhOk, ihSem]
    refine ⟨_, rfl, ?_⟩
    intro ys hys
    have hlen := FitsVals_length M _ hys
    have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys fun hz _ _ => by
      simp only [hz, fibreR, if_true]; exact truthVal_mem_univ_zero _
    have hmem' : appList (fieldVal fs k) ys.reverse ∈ˢ fibreR (S.z ls) (S.bound M ls ps _)
        fun x => S.Mem M ls ps _ x ∧ True :=
      fibreR_mono (fun _ h => ⟨h, trivial⟩) _ hmem
    obtain ⟨hw, -, -⟩ := S.wit_of_fibre M ls hu hp (P := fun _ _ _ => True) hmem'
    simp only [readEnv_consList hlen]
    exact S.RecGraph_recFn M ls q (S.RecGraph_total M ls q hu hp hw m mins)

/-- **The ι equation**: at a constructor value whose fields fit, the
recursor is the minor at the fields and the inductive hypotheses'
values.  At a proposition the constructor value is the point and the
recursor looks at the fibre's witness, which by uniqueness is the
tagged tuple of these very fields. -/
theorem recSem_eq (hu : S.Uniq M ls) {j : Nat} {c : CtorSpec} {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) {fs : List V} (hc : S.ctors[j]? = some c)
    (hfit : S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs) (m : V) (mins : List V) :
    S.recSem M ls q ps m mins (S.idxVals M ls (consList fs (envP ps)) c.idx) (S.ctorVal ls j fs)
      = appList (S.minorAt mins j)
          (fs.reverse ++ c.recFields.map (S.ihSem M ls q ps m mins fs)) := by
  have hmem : S.Mem M ls ps (S.idxVals M ls (consList fs (envP ps)) c.idx)
      (tag j (tuple fs.reverse)) :=
    S.Mem_intro M ls ⟨j, c, fs, hc, hfit, rfl, rfl⟩
  have hwit : S.wit M ls ps (S.idxVals M ls (consList fs (envP ps)) c.idx) (S.ctorVal ls j fs)
      = tag j (tuple fs.reverse) := by
    unfold wit ctorVal
    cases hz : S.z ls
    · rfl
    · exact hu hz ps hp _ _ _ (S.Mem_pick M ls ⟨_, hmem⟩) hmem
  unfold recSem
  rw [hwit]
  exact S.recFn_eq M ls q (S.RecGraph_intro M ls q
    ⟨j, c, fs, _, hc, hfit, rfl, rfl, S.IhOk_ihSem M ls q hu hp hfit m mins, rfl⟩)

/-! ### The recursor's typing -/

/-- An inductive hypothesis' value lies in the motive at the field's
indices and the field (through the telescope at a reflexive field). -/
noncomputable def IhTyped (ps : List V) (m : V) (fs : List V) : Nat × Field → V → Prop
  | (k, .recursive es), ih =>
    ih ∈ˢ appList m ((S.idxVals M ls (consList (earlier fs k) (envP ps)) es).reverse ++ [fieldVal fs k])
  | (k, .reflexive tele es), ih =>
    let env := consList (earlier fs k) (envP ps)
    ih ∈ˢ piCtx M (S.ψ ls) q env tele fun ρ' =>
      appList m ((S.idxVals M ls ρ' es).reverse ++
        [appList (fieldVal fs k) (readEnv tele.length ρ').reverse])
  | (_, .ordinary _), _ => True

/-- **A minor's typing**: at fitting fields and typed inductive
hypotheses, the minor's value lies in the motive at the constructor's
index expressions and its value. -/
noncomputable def MinorOk (ps : List V) (m : V) (mins : List V) (j : Nat) (c : CtorSpec) : Prop :=
  ∀ fs, S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs →
    ∀ ihs, ListRel (S.IhTyped M ls q ps m fs) c.recFields ihs →
      appList (S.minorAt mins j) (fs.reverse ++ ihs) ∈ˢ
        appList m ((S.idxVals M ls (consList fs (envP ps)) c.idx).reverse ++ [S.ctorVal ls j fs])

/-- **The recursor's typing**: at a member of the fibre, the
recursor's value lies in the motive at the indices and the member —
by induction over the family, from the minors' typing. -/
theorem recSem_mem (hu : S.Uniq M ls) {ps : List V} (hp : FitsVals M (S.ψ ls) base S.params ps)
    (m : V) (mins : List V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOk M ls q ps m mins j c)
    {is : List V} {t : V} (ht : t ∈ˢ S.Fam M ls ps is) :
    S.recSem M ls q ps m mins is t ∈ˢ appList m (is.reverse ++ [t]) := by
  -- the witness is a member with the major as its member
  have hw : S.Mem M ls ps is (S.wit M ls ps is t) ∧ S.memb ls (S.wit M ls ps is t) = t := by
    have ht' : t ∈ˢ fibreR (S.z ls) (S.bound M ls ps is) fun x => S.Mem M ls ps is x ∧ True :=
      fibreR_mono (fun _ h => ⟨h, trivial⟩) _ ht
    have := S.wit_of_fibre M ls hu hp (P := fun _ _ _ => True) ht'
    exact ⟨this.1, this.2.2⟩
  unfold recSem
  generalize S.wit M ls ps is t = x at hw ⊢
  suffices key : ∀ ps' is x, S.Mem M ls ps' is x → ps' = ps →
      S.recFn M ls q ps m mins is x ∈ˢ appList m (is.reverse ++ [S.memb ls x]) by
    have := key ps is x hw.1 rfl
    rwa [hw.2] at this
  intro ps' is x hm
  refine S.Mem_ind M ls
    (P := fun ps' is x => ps' = ps →
      S.recFn M ls q ps m mins is x ∈ˢ appList m (is.reverse ++ [S.memb ls x]))
    ?_ hm
  intro ps' is x hs hps
  subst hps
  obtain ⟨j, c, fs, hc, hfit, his, hx⟩ := hs
  have hfitM := S.FitsFields_mono M ls (fun _ _ _ h => h.1) ps' hfit
  subst his hx
  have hget' : ∀ {k : Nat} {f : Field}, c.fields[c.fields.length - 1 - k]? = some f →
      k < c.fields.length → fieldVal fs k ∈ˢ S.fieldSet M ls (S.bound M ls)
        (fun a is x => S.Mem M ls a is x ∧ (a = ps' →
          S.recFn M ls q ps' m mins is x ∈ˢ appList m (is.reverse ++ [S.memb ls x]))) ps'
        (earlier fs k) f :=
    fun hf hk => S.FitsFields_get M ls hfit hf hk
  rw [S.recFn_eq M ls q (S.RecGraph_intro M ls q
    ⟨j, c, fs, _, hc, hfitM, rfl, rfl, S.IhOk_ihSem M ls q hu hp hfitM m mins, rfl⟩)]
  have hmemb : S.memb ls (tag j (tuple fs.reverse)) = S.ctorVal ls j fs := rfl
  rw [hmemb]
  refine hmin j c hc fs hfitM _ (ListRel.map ?_)
  intro kf hkf
  obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
  have hget := hget' hf hk
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | recursive es =>
    dsimp only [fieldSet] at hget
    obtain ⟨-, hP, hmb⟩ := S.wit_of_fibre M ls hu hp (P := fun a is x => a = ps' →
      S.recFn M ls q ps' m mins is x ∈ˢ appList m (is.reverse ++ [S.memb ls x])) hget
    dsimp only [IhTyped, ihSem, recSem]
    have := hP rfl
    rwa [hmb] at this
  | reflexive tele es =>
    dsimp only [fieldSet] at hget
    dsimp only [IhTyped, ihSem]
    refine lamCtx_mem_piCtx M _ ?_
    intro ys hys
    have hlen := FitsVals_length M _ hys
    have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys fun hz _ _ => by
      simp only [hz, fibreR, if_true]; exact truthVal_mem_univ_zero _
    obtain ⟨-, hP, hmb⟩ := S.wit_of_fibre M ls hu hp (P := fun a is x => a = ps' →
      S.recFn M ls q ps' m mins is x ∈ˢ appList m (is.reverse ++ [S.memb ls x])) hmem
    simp only [readEnv_consList hlen, recSem]
    have := hP rfl
    rwa [hmb] at this

/-! ## The sets of the stored constants

The former, the constructors and the recursor as sets: graphs over the
generated contexts (`Decl.lean`), read in the model as it grows — the
constructors' contexts mention the former, the recursor's mention the
constructors. -/

/-- **The type former's set** at `ls`: the graph over the index and
parameter contexts whose value is the fibre. -/
noncomputable def famSet : V :=
  lamCtx M (S.ψ ls) false base (S.indices ++ S.params) fun ρ' =>
    S.Fam M ls (readEnv S.nP (shiftE S.nI 0 ρ')) (readEnv S.nI ρ')

/-- The model with the type former added. -/
noncomputable def M₁ : Name → List Nat → V :=
  fun n ls' => if n = S.name then S.famSet M ls' else M n ls'

/-- **A constructor's set**: the abstraction over the parameters and
fields (read in the model with the former) of the constructor's
value. -/
noncomputable def ctorSet (j : Nat) (c : CtorSpec) : V :=
  lamCtx (S.M₁ M) (S.ψ ls) (S.z ls) base (S.fieldCtx c.fields ++ S.params) fun ρ' =>
    S.ctorVal ls j (readEnv c.fields.length ρ')

/-- The constructor of a name, with its number. -/
def ctorOf? (n : Name) : Option (Nat × CtorSpec) :=
  (List.range S.n).findSome? fun j =>
    match S.ctors[j]? with
    | some c => if c.name = n then some (j, c) else none
    | none => none

/-- The model with the former and the constructors added. -/
noncomputable def M₂ : Name → List Nat → V :=
  fun n ls' =>
    match S.ctorOf? n with
    | some (j, c) => S.ctorSet M ls' j c
    | none => S.M₁ M n ls'

/-- **The recursor's set** at its own levels `lsr` (the elimination
level in front, if large): the abstraction over its context — the
parameters, the motive, the minors, the indices, the major — of the
recursor's semantic value, the family read at the block's levels. -/
noncomputable def recSet (lsr : List Nat) : V :=
  let ψr := valOf S.recLparams lsr
  let ls := S.lparams.map ψr
  let q := S.q.holds ψr
  lamCtx (S.M₂ M) ψr q base
    (S.famVars (S.n + 1) :: S.indicesAt (S.n + 1) ++ S.minorsCtx ++ [S.motiveTy] ++ S.params)
    fun ρ' =>
      S.recSem M ls q (readEnv S.nP (shiftE (1 + S.nI + S.n + 1) 0 ρ')) (ρ' (1 + S.nI + S.n))
        (readEnv S.n (shiftE (1 + S.nI) 0 ρ')) (readEnv S.nI (shiftE 1 0 ρ')) (ρ' 0)

/-- **The model of the installed block**: the recursor on top. -/
noncomputable def M₃ : Name → List Nat → V :=
  fun n ls' => if n = S.recName then S.recSet M ls' else S.M₂ M n ls'

end IndSpec

end Fragment
