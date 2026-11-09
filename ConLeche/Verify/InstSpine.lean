module

import ConLeche.Verify.Subst
import ConLeche.Verify.InstList
public import ConLeche.Verify.Leaves
public import ConLeche.Verify.InstLevels

public section

/-!
# Syntactic kit for `Expr.instSpine`

`Expr.instSpine` (kernel) instantiates a telescope-context expression
at an argument spine; it is definitionally the verification's
`instSeq`.  The nested-auxiliary iota path fabricates
`instSpine args pin` comparands at fire time, so the scoping /
shift-invariance / resolution walks need the usual preservation
lemmas, plus the `instSeq` bridge for the model layer.
-/

namespace ConLeche

open Expr

/-- `Expr.instSpine` is the verification's `instSeq`. -/
theorem Expr.instSpine_eq_instSeq :
    ∀ (args : List Expr) (t : Nat) (e : Expr),
      Expr.instSpine args t e = instSeq args t e
  | [], _, _ => rfl
  | _ :: as, t, _e => Expr.instSpine_eq_instSeq as (t - 1) _

/-- `shiftFrom` commutes with `instSpine` (arguments shifted
pointwise). -/
theorem shiftFrom_instSpine {p : Nat} :
    ∀ (args : List Expr) (t : Nat) (e : Expr),
      shiftFrom p (Expr.instSpine args t e) =
        Expr.instSpine (args.map (shiftFrom p)) t (shiftFrom p e)
  | [], _, _ => rfl
  | a :: as, t, e => by
    show shiftFrom p (Expr.instSpine as (t - 1) (e.instantiate1 a t)) = _
    rw [shiftFrom_instSpine as (t - 1) _, shiftFrom_instantiate1_gen]
    rfl

/-- `instSpine` keeps terms well-scoped: a closed (fvar-free) base
instantiated at well-scoped arguments is well-scoped. -/
theorem instSpine_WScoped {d : Nat} :
    ∀ {args : List Expr} (t : Nat) {e : Expr}, WScoped d e →
      (∀ a ∈ args, WScoped d a) →
      WScoped d (Expr.instSpine args t e)
  | [], _, _, he, _ => he
  | a :: _as, t, _e, he, hargs =>
    instSpine_WScoped (t - 1)
      (WScoped.instantiate1_gen (hargs a List.mem_cons_self) t he)
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))

/-- A full-telescope `instSpine` at bvar-closed arguments closes the
base: a term bounded by `args.length` binders instantiated at the
whole spine is bvar-closed. -/
theorem instSpine_closed :
    ∀ {args : List Expr} {e : Expr},
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      e.looseBVarsBounded args.length = true →
      (Expr.instSpine args (args.length - 1) e).looseBVarsBounded 0
        = true
  | [], e, _, he => he
  | a :: as, e, hargs, he => by
    show (Expr.instSpine as ((a :: as).length - 1 - 1)
        (e.instantiate1 a ((a :: as).length - 1))).looseBVarsBounded 0
      = true
    have hlen : (a :: as).length - 1 = as.length := by
      simp only [List.length_cons, Nat.add_sub_cancel]
    rw [hlen]
    have h1 : (e.instantiate1 a as.length).looseBVarsBounded as.length
        = true :=
      looseBVarsBounded_instantiate1_gen (k := as.length)
        (hargs a List.mem_cons_self)
        (by simpa [List.length_cons] using he)
    exact instSpine_closed
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha')) h1

/-- The fvar leaves of an `instSpine` come from the base or the
arguments. -/
theorem fvarLeaves_instSpine :
    ∀ {args : List Expr} (t : Nat) {e : Expr} {l},
      l ∈ (Expr.instSpine args t e).fvarLeaves →
      l ∈ e.fvarLeaves ∨ ∃ a ∈ args, l ∈ a.fvarLeaves
  | [], _, _, _, hl => Or.inl hl
  | a :: as, t, e, l, hl => by
    rcases fvarLeaves_instSpine (t - 1) hl with hl' | ⟨a', ha', hla'⟩
    · rcases fvarLeaves_instantiate1 e t hl' with hl'' | hl''
      · exact Or.inl hl''
      · exact Or.inr ⟨a, List.mem_cons_self, hl''⟩
    · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', hla'⟩

/-! ## The firing comparands under shifts -/

/-- The level comparand of a rule does not depend on the argument
spine. -/
theorem recFireComparands_fst_congr (rl : RecRule) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args args' : List Expr)
    (mI : Nat) :
    (recFireComparands rl cnP lps us cvjLps args mI).1 =
      (recFireComparands rl cnP lps us cvjLps args' mI).1 := by
  cases hf : rl.fire <;> simp [recFireComparands, hf]

/-- The parameter comparand commutes with `shiftFrom` on the argument
spine (the stored instantiations of a nested rule are fvar-free). -/
theorem recFireComparands_snd_shift {p : Nat} (rl : RecRule)
    (lps : List Name) (us : List Level) (cvjLps : List Name)
    (args : List Expr) (mI : Nat)
    (hpins : ∀ lvls pins, rl.fire = .nested lvls pins →
      ∀ pin ∈ pins, pin.hasFvar = false) :
    (recFireComparands rl cnP lps us cvjLps
        (args.map (shiftFrom p)) mI).2 =
      ((recFireComparands rl cnP lps us cvjLps args mI).2).map
        (shiftFrom p) := by
  cases hf : rl.fire with
  | nested lvls pins =>
    simp only [recFireComparands, hf, List.map_map]
    refine List.map_congr_left ?_
    intro pin hpin
    show Expr.instSpine ((args.map (shiftFrom p)).take mI) (mI - 1)
        (pin.instantiateLevelParams lps us) =
      shiftFrom p (Expr.instSpine (args.take mI) (mI - 1)
        (pin.instantiateLevelParams lps us))
    rw [shiftFrom_instSpine, List.map_take,
      shiftFrom_eq_self_of_not_hasFvar (by
        rw [hasFvar_instantiateLevelParams]
        exact hpins lvls pins hf pin hpin)]
  | plain =>
    simp only [recFireComparands, hf, List.map_take]
  | levels lvls =>
    simp only [recFireComparands, hf, List.map_take]

/-- The parameter comparand's entries are well-scoped at the ambient
depth (arguments well-scoped; a nested rule's stored instantiations
fvar-free). -/
theorem recFireComparands_snd_WScoped {d : Nat} (rl : RecRule)
    (lps : List Name) (us : List Level) (cvjLps : List Name)
    (args : List Expr) (mI : Nat)
    (hargs : ∀ a ∈ args, WScoped d a)
    (hpins : ∀ lvls pins, rl.fire = .nested lvls pins →
      ∀ pin ∈ pins, pin.hasFvar = false) :
    ∀ x ∈ (recFireComparands rl cnP lps us cvjLps args mI).2,
      WScoped d x := by
  cases hf : rl.fire with
  | nested lvls pins =>
    intro x hx
    simp only [recFireComparands, hf, List.mem_map] at hx
    obtain ⟨pin, hpin, rfl⟩ := hx
    exact instSpine_WScoped _
      (WScoped.of_not_hasFvar (by
        rw [hasFvar_instantiateLevelParams]
        exact hpins lvls pins hf pin hpin))
      (fun a ha => hargs a (List.mem_of_mem_take ha))
  | plain =>
    intro x hx
    simp only [recFireComparands, hf] at hx
    exact hargs x (List.mem_of_mem_take hx)
  | levels lvls =>
    intro x hx
    simp only [recFireComparands, hf] at hx
    exact hargs x (List.mem_of_mem_take hx)

/-- A telescope that strips syntactically admits any instantiation
walk of matching length.  A statement about `Expr` alone, and what the
install layer needs: the projection bottom constructs its
constructor/recursor `instPisAt` runs from the checker's `stripPis`
pins rather than from a stored run. -/
theorem instPisAt_isSome_of_stripPis :
    ∀ (args : List Expr) {e : Expr},
      (e.stripPis args.length).isSome = true →
      (Expr.instPisAt args e).isSome = true
  | [], e, _ => by simp [Expr.instPisAt]
  | a :: as, e, h => by
    match e, h with
    | .forallE dom body, h =>
      simp only [List.length_cons, Expr.stripPis, Option.isSome_map] at h
      have h' : ((body.instantiate1 a).stripPis as.length).isSome = true :=
        Expr.stripPis_instantiate1_isSome as.length 0 h
      have := instPisAt_isSome_of_stripPis as h'
      simp only [Expr.instPisAt, Option.isSome_map]
      exact this

/-! ## The rule-shape residue

The `V`-free facts about `recFireComparands` that the recursor-group
installs read. -/

/-- The fire comparand levels of a plain rule. -/
theorem recFireComparands_plain {rl : RecRule} {lps : List Name}
    {us : List Level} {cvjLps : List Name} {args : List Expr} {rP : Nat}
    (h : RecRule.fire rl = .plain) :
    (recFireComparands rl cnP lps us cvjLps args rP).1 =
      cvjLps.map fun p => Level.subst lps us (.param p) := by
  unfold recFireComparands
  rw [h]

/-! ## Two scoping facts the cached call-discipline needs

Read by the cached discipline (`Verify/Cached/DiscC*.lean`). -/

/-- A list of well-scoped expressions has a well-scoped `getD`. -/
theorem wscoped_getD {d : Nat} :
    ∀ {l : List Expr}, (∀ x ∈ l, WScoped d x) → ∀ (n : Nat),
      WScoped d (l.getD n (.bvar 0)) := by
  intro l
  induction l with
  | nil => intro _ n; simp [List.getD, WScoped]
  | cons x xs ih =>
    intro h n
    cases n with
    | zero => exact h x (List.mem_cons_self ..)
    | succ n =>
      simpa [List.getD] using
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) n

/-- A level-instantiated `fvar`-free expression (e.g. a stored type or
rule right-hand side) is well-scoped at any depth. -/
theorem wscoped_instLevels_of_not_hasFvar {e : Expr}
    (h : e.hasFvar = false) (ps : List Name) (us : List Level) {d : Nat} :
    WScoped d (e.instantiateLevelParams ps us) :=
  WScoped.of_not_hasFvar (by rw [hasFvar_instantiateLevelParams]; exact h)

/-! ## The field telescope of a unit-like instance (task #515)

`unitFieldTele` (`Kernel/CoreDefs.lean`) drops a stored constructor
type's parameter binders and instantiates them with the instance's
arguments in one pass; it is the `instSpine` of the arguments. -/

/-- Bulk instantiation at a reversed spine is the spine's `instSpine`. -/
theorem instantiateList_reverse_eq_instSpine :
    ∀ (args : List Expr) (e : Expr),
      e.instantiateList args.reverse = Expr.instSpine args (args.length - 1) e
  | [], e => Expr.instantiateList_nil e 0
  | a :: as, e =>
    (Expr.instSpine_eq_instantiateList (a :: as) as.length e (by simp)).symm

/-- `unitFieldTele` is the `instSpine` of the peeled body. -/
theorem unitFieldTele_eq (cty : Expr) (n : Nat) (args : List Expr) :
    unitFieldTele cty n args =
      (Expr.peelPis n cty).map (Expr.instSpine args (args.length - 1)) := by
  unfold unitFieldTele
  congr 1
  funext body
  exact instantiateList_reverse_eq_instSpine args body

/-- A peel of an fvar-free telescope is fvar-free. -/
theorem hasFvar_peelPis : ∀ {n : Nat} {e r : Expr}, e.hasFvar = false →
    Expr.peelPis n e = some r → r.hasFvar = false
  | 0, e, r, he, h => by
    simp only [Expr.peelPis, Option.some.injEq] at h; exact h ▸ he
  | n + 1, .forallE _ b, r, he, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at he
    exact hasFvar_peelPis he.2 h
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _, _, _, h
  | _ + 1, .letE _ _ _, _, _, h | _ + 1, .lit _, _, _, h
  | _ + 1, .proj _ _ _, _, _, h => nomatch h

/-- The field telescope of an fvar-free constructor type commutes with the
shift (the arguments shifted pointwise). -/
theorem unitFieldTele_shiftFrom {p : Nat} {cty : Expr} (hc : cty.hasFvar = false)
    (n : Nat) (args : List Expr) :
    unitFieldTele cty n (args.map (shiftFrom p)) =
      (unitFieldTele cty n args).map (shiftFrom p) := by
  rw [unitFieldTele_eq, unitFieldTele_eq]
  cases hb : Expr.peelPis n cty with
  | none => rfl
  | some body =>
    simp only [Option.map_some, List.length_map, shiftFrom_instSpine,
      shiftFrom_eq_self_of_not_hasFvar (hasFvar_peelPis hc hb)]

/-- The field telescope of an fvar-free constructor type at well-scoped
arguments is well-scoped. -/
theorem unitFieldTele_WScoped {d : Nat} {cty tele : Expr} {n : Nat} {args : List Expr}
    (hc : cty.hasFvar = false) (hargs : ∀ a ∈ args, WScoped d a)
    (h : unitFieldTele cty n args = some tele) : WScoped d tele := by
  rw [unitFieldTele_eq] at h
  cases hb : Expr.peelPis n cty with
  | none => rw [hb] at h; exact nomatch h
  | some body =>
    rw [hb] at h
    obtain rfl := Option.some.inj h
    exact instSpine_WScoped _ (WScoped.of_not_hasFvar (hasFvar_peelPis hc hb)) hargs

end ConLeche

