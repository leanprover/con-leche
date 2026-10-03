module

public import Fragment.IndLib
public import Fragment.Ctx

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
  · exact sep_mem_univ (hU rfl)
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
/-- A family predicate: parameters, indices, candidate member. -/
abbrev FamP (V : Type u) := List V → List V → V → Prop

/-- The graph relation's shape: parameters, motive, minors, indices,
witness, value. -/
abbrev RecP (V : Type u) := List V → V → List V → List V → V → V → Prop

/-- The environment of parameter values. -/
def envP (ps : List V) : Nat → V := consList ps base
/-- The product over a context is monotone in its body; at a
proposition the larger body must be a truth value. -/
theorem piCtx_sub (M : Name → List Nat → V) (φ : Name → Nat) {p : Bool} {ρ : Nat → V}
    {Γ : List Expr} {F G : (Nat → V) → V}
    (h : ∀ vs, FitsVals M φ ρ Γ vs → F (consList vs ρ) ⊆ˢ G (consList vs ρ))
    (hG : p = true → ∀ vs, FitsVals M φ ρ Γ vs → G (consList vs ρ) ∈ˢ (univ 0 : V)) :
    piCtx M φ p ρ Γ F ⊆ˢ piCtx M φ p ρ Γ G := by
  induction Γ generalizing F G with
  | nil => exact h [] trivial
  | cons A Γ ih =>
    simp only [piCtx_cons]
    refine ih (fun vs hvs => piR_mono (fun x hx => h (x :: vs) ⟨hvs, hx⟩)
      fun hp x hx => hG hp (x :: vs) ⟨hvs, hx⟩) fun hp _ _ => by subst hp; exact piR_true_mem_univ_zero

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
/-! ## The class of a nested block, read in the model

A container field's domain is the class `K.{lsK} args[member]`: the
container's set — **already in the model**, assigned to `K` when `K`
was installed — applied to the class's arguments, with a set `X` at
the member's position.  In the family's operator `X` is the fibre of
the *approximant* at the member's index expressions (`IndSem.lean`,
`fieldSet`), and the operator is monotone and accessible because the
class is, in `X` (`ContClause`, which the installation establishes
from the container's positivity and the leastness of its fixed
point, `NestSem.lean`). -/

/-- The class's arguments as values (outermost first), with `X` at
the member's position: the other arguments read under the parameters
(they are closed under them). -/
def classArgsV (N : NestInfo) (ps : List V) (X : V) : List V :=
  (N.args.take N.p).map (interp M (S.ψ ls) (envP ps)) ++ [X] ++
    (N.args.drop N.p).map (interp M (S.ψ ls) (envP ps))

/-- The container's levels at the block's valuation. -/
def lsK (N : NestInfo) : List Nat := N.lsK.map (Level.eval (S.ψ ls))

/-- **The class at a member set**: the container's set in the model,
applied to the class's arguments with `X` at the member's position. -/
def classSet (N : NestInfo) (ps : List V) (X : V) : V :=
  appList (M N.K.name (S.lsK ls N)) (S.classArgsV M ls N ps X)

/-- The member's index values at the parameters (its index expressions
are closed under them). -/
def memberIdx (N : NestInfo) (ps : List V) : List V := S.idxVals M ls (envP ps) N.idx

/-- **The container's parameter values at a member set** (innermost
first): the class's arguments with `X` at the member's position —
the parameters the container's own family is read at. -/
def psK (N : NestInfo) (ps : List V) (X : V) : List V := (S.classArgsV M ls N ps X).reverse

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
/-- Replace the values at recursive positions by the point. -/
def junkRec : List Field → List V → List V
  | f :: fields, v :: vs => (if f.isRec then pt else v) :: junkRec fields vs
  | _, vs => vs

/-- **No field reads an earlier recursive field** (the block-level
hypothesis). -/
def NoRecDep : Prop :=
  ∀ c ∈ S.ctors, ∀ i f, c.fields[i]? = some f → fieldNoRecDep (c.fields.drop (i + 1)) f
/-- No container field: a plain block's constructors. -/
def NoCont : Prop := ∀ c ∈ S.ctors, ∀ f ∈ c.fields, f.isCont = false
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
