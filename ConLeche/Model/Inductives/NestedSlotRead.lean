module

public import ConLeche.Model.Annot.EnvModel
public import ConLeche.Model.Annot.Bit
public import ConLeche.Verify.Subst
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.WellDenotedTransport
public section

/-!
# The nested slot's reading law (X.1) — task #315 M6

DESIGN §DR.2, cherry-picked: the nested-slot arm's assembly reads a
pin's components at the members' leaves as their ABSTRACTION at the
frame holding the leaves' values.

`denoteMeta` bakes a constant's leaf in (`acval T ψ` at every `.const T`
node), so a run's readings cannot be re-opened at the family variable
`X`; the device of this module is to read the slot's SYNTAX with the
block's members ABSTRACTED to fresh variables and to spell the family
in the variables' slots.

* **§1 The abstraction** (`Expr.absConstAt`, `Expr.absMembersGo`): a
  constant's every occurrence at the block's own levels becomes an
  `fvar` at a fresh level (the members at `nP … nP + k - 1`, above the
  parameter openers), and `Expr.substFvarAt` puts it back
  (`Expr.instMembersGo_absMembersGo`).
* **§2 The reading law (X.1)** (`denoteMeta_absMembers`): the reading
  of a term at the model equals the reading of its abstraction at the
  frame whose fresh slots hold the leaves' values — `denoteMeta_substFvarAt`
  (`Model/Annot/BitInst.lean`) folded over the members, `interp_inst`
  at cut `0`.  This is the direction the leaf's typing needs: at the
  fixed point the slot reads as the restored constructor's field.
-/

namespace ConLeche.Expr

open ConLeche (Name Level)

/-! ## §1 The abstraction of a constant to a fresh variable -/

/-- Replace every `.const T us` by `.fvar l ty` (the annotations of
existing variables are not descended into, as in `abstract1`). -/
@[expose] def absConstAt (T : Name) (us : List Level) (l : Nat) (ty : Expr) : Expr → Expr
  | .const n us' => if n = T ∧ us' = us then .fvar l ty else .const n us'
  | .app f a => .app (absConstAt T us l ty f) (absConstAt T us l ty a)
  | .lam t b m => .lam (absConstAt T us l ty t) (absConstAt T us l ty b) m
  | .forallE t b m => .forallE (absConstAt T us l ty t) (absConstAt T us l ty b) m
  | .letE t v b => .letE (absConstAt T us l ty t) (absConstAt T us l ty v) (absConstAt T us l ty b)
  | .proj s i e => .proj s i (absConstAt T us l ty e)
  | .bvar i => .bvar i
  | .fvar idx ty' => .fvar idx ty'
  | .sort u => .sort u
  | .lit v => .lit v

/-- The abstraction, undone: substituting the constant back for the
fresh variable is the identity on a term whose variables lie below
the fresh level. -/
theorem substFvarAt_absConstAt {T : Name} {us : List Level} {l : Nat} {ty : Expr} :
    ∀ {e : Expr}, fvarsBelow l e →
      substFvarAt l (.const T us) (absConstAt T us l ty e) = e := by
  intro e
  induction e with
  | const n us' =>
    intro _
    simp only [absConstAt]
    split
    · next h =>
      obtain ⟨rfl, rfl⟩ := h
      simp [substFvarAt]
    · simp [substFvarAt]
  | fvar idx ty' =>
    intro h
    simp only [fvarsBelow] at h
    simp only [absConstAt, substFvarAt]
    rw [if_neg (by omega), if_neg (by omega)]
  | _ => intro h; simp_all [absConstAt, substFvarAt, fvarsBelow]

theorem fvarsBelow_absConstAt {T : Name} {us : List Level} {l : Nat} {ty : Expr} :
    ∀ {e : Expr}, fvarsBelow l e → fvarsBelow (l + 1) (absConstAt T us l ty e) := by
  intro e
  induction e with
  | const n us' =>
    intro _
    simp only [absConstAt]
    split <;> simp [fvarsBelow]
  | fvar idx ty' => intro h; simp only [fvarsBelow] at h ⊢; simp [absConstAt, fvarsBelow]; omega
  | _ => intro h; simp_all [absConstAt, fvarsBelow]

theorem looseBVarsBounded_absConstAt {T : Name} {us : List Level} {l : Nat} {ty : Expr} :
    ∀ {e : Expr} {k : Nat}, e.looseBVarsBounded k = true →
      (absConstAt T us l ty e).looseBVarsBounded k = true := by
  intro e
  induction e with
  | const n us' => intro k _; simp only [absConstAt]; split <;> simp [looseBVarsBounded]
  | _ => intro k h; simp_all [absConstAt, looseBVarsBounded]

/-- A leaf of the abstraction is a leaf of the term or the fresh
variable's own. -/
theorem fvarLeaves_absConstAt {T : Name} {us : List Level} {l : Nat} {ty : Expr} :
    ∀ {e : Expr} {x : Nat × Expr}, x ∈ (absConstAt T us l ty e).fvarLeaves →
      x ∈ e.fvarLeaves ∨ x ∈ (l, ty) :: ty.fvarLeaves := by
  intro e
  induction e with
  | const n us' =>
    intro x hx
    simp only [absConstAt] at hx
    split at hx
    · exact Or.inr (by simpa [fvarLeaves] using hx)
    · simp [fvarLeaves] at hx
  | app f a ihf iha =>
    intro x hx
    simp only [absConstAt, fvarLeaves, List.mem_append] at hx ⊢
    rcases hx with h | h
    · rcases ihf h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases iha h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | lam t b m iht ihb =>
    intro x hx
    simp only [absConstAt, fvarLeaves, List.mem_append] at hx ⊢
    rcases hx with h | h
    · rcases iht h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases ihb h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | forallE t b m iht ihb =>
    intro x hx
    simp only [absConstAt, fvarLeaves, List.mem_append] at hx ⊢
    rcases hx with h | h
    · rcases iht h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases ihb h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | letE t v b iht ihv ihb =>
    intro x hx
    simp only [absConstAt, fvarLeaves, List.mem_append] at hx ⊢
    rcases hx with (h | h) | h
    · rcases iht h with h' | h'
      · exact Or.inl (Or.inl (Or.inl h'))
      · exact Or.inr h'
    · rcases ihv h with h' | h'
      · exact Or.inl (Or.inl (Or.inr h'))
      · exact Or.inr h'
    · rcases ihb h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | proj s i e ih =>
    intro x hx
    simp only [absConstAt, fvarLeaves] at hx ⊢
    exact ih hx
  | fvar idx ty' => intro x hx; exact Or.inl hx
  | _ => intro x hx; simp [absConstAt, fvarLeaves] at hx

theorem absConstAt_mkAppN {T : Name} {us : List Level} {l : Nat} {ty : Expr} :
    ∀ (as : List Expr) (f : Expr),
      absConstAt T us l ty (mkAppN f as) = mkAppN (absConstAt T us l ty f) (as.map (absConstAt T us l ty))
  | [], _ => rfl
  | a :: as, f => by
    simp only [mkAppN, List.map]
    exact absConstAt_mkAppN as (.app f a)

theorem absConstAt_const_ne {T : Name} {us : List Level} {l : Nat} {ty : Expr} {n : Name}
    {us' : List Level} (h : n ≠ T) : absConstAt T us l ty (.const n us') = .const n us' := by
  simp [absConstAt, h]

/-- The members abstracted in turn: member `m` of the list at level
`l + m`. -/
@[expose] def absMembersGo (us : List Level) : Nat → List (Name × Expr) → Expr → Expr
  | _, [], e => e
  | l, (T, ty) :: rest, e => absMembersGo us (l + 1) rest (absConstAt T us l ty e)

/-- The members put back, innermost (highest level) first. -/
@[expose] def instMembersGo (us : List Level) : Nat → List (Name × Expr) → Expr → Expr
  | _, [], e => e
  | l, (T, _) :: rest, e => substFvarAt l (.const T us) (instMembersGo us (l + 1) rest e)

theorem instMembersGo_absMembersGo {us : List Level} :
    ∀ (L : List (Name × Expr)) (l : Nat) {e : Expr}, fvarsBelow l e →
      instMembersGo us l L (absMembersGo us l L e) = e
  | [], _, _, _ => rfl
  | (T, ty) :: rest, l, e, h => by
    simp only [absMembersGo, instMembersGo]
    rw [instMembersGo_absMembersGo rest (l + 1) (fvarsBelow_absConstAt h)]
    exact substFvarAt_absConstAt h

theorem fvarsBelow_absMembersGo {us : List Level} :
    ∀ (L : List (Name × Expr)) (l : Nat) {e : Expr}, fvarsBelow l e →
      fvarsBelow (l + L.length) (absMembersGo us l L e)
  | [], _, _, h => h
  | (T, ty) :: rest, l, e, h => by
    simp only [absMembersGo, List.length_cons]
    rw [show l + (rest.length + 1) = l + 1 + rest.length by omega]
    exact fvarsBelow_absMembersGo rest (l + 1) (fvarsBelow_absConstAt h)

theorem looseBVarsBounded_absMembersGo {us : List Level} :
    ∀ (L : List (Name × Expr)) (l : Nat) {e : Expr} {k : Nat}, e.looseBVarsBounded k = true →
      (absMembersGo us l L e).looseBVarsBounded k = true
  | [], _, _, _, h => h
  | (T, ty) :: rest, l, e, k, h => by
    simp only [absMembersGo]
    exact looseBVarsBounded_absMembersGo rest (l + 1) (looseBVarsBounded_absConstAt h)

theorem absMembersGo_mkAppN {us : List Level} :
    ∀ (L : List (Name × Expr)) (l : Nat) (as : List Expr) (f : Expr),
      absMembersGo us l L (mkAppN f as)
        = mkAppN (absMembersGo us l L f) (as.map (absMembersGo us l L))
  | [], _, as, f => by simp [absMembersGo]
  | (T, ty) :: rest, l, as, f => by
    simp only [absMembersGo]
    rw [absConstAt_mkAppN, absMembersGo_mkAppN rest (l + 1), List.map_map]
    rfl

theorem absMembersGo_const_ne {us : List Level} :
    ∀ (L : List (Name × Expr)) (l : Nat) {n : Name} {us' : List Level},
      (∀ x ∈ L, x.1 ≠ n) → absMembersGo us l L (.const n us') = .const n us'
  | [], _, _, _, _ => rfl
  | (T, ty) :: rest, l, n, us', h => by
    simp only [absMembersGo]
    rw [absConstAt_const_ne (fun h' => h (T, ty) List.mem_cons_self h'.symm)]
    exact absMembersGo_const_ne rest (l + 1) fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- A leaf of the abstraction is a leaf of the term or a fresh
variable's (with its annotation's leaves). -/
theorem fvarLeaves_absMembersGo {us : List Level} :
    ∀ (L : List (Name × Expr)) (l : Nat) {e : Expr} {x : Nat × Expr},
      x ∈ (absMembersGo us l L e).fvarLeaves →
      x ∈ e.fvarLeaves ∨ ∃ i T ty, L[i]? = some (T, ty) ∧ x ∈ (l + i, ty) :: ty.fvarLeaves
  | [], _, _, _, h => Or.inl h
  | (T, ty) :: rest, l, e, x, h => by
    simp only [absMembersGo] at h
    rcases fvarLeaves_absMembersGo rest (l + 1) h with h' | ⟨i, T', ty', hi, hx⟩
    · rcases fvarLeaves_absConstAt h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr ⟨0, T, ty, rfl, by simpa using h''⟩
    · exact Or.inr ⟨i + 1, T', ty', by simpa using hi, by rw [show l + (i + 1) = l + 1 + i by omega]; exact hx⟩

/-- Substituting a closed term for the top variable lowers the bound. -/
theorem fvarsBelow_substFvarAt {p : Nat} {a : Expr} (ha : fvarsBelow p a) :
    ∀ {e : Expr}, fvarsBelow (p + 1) e → fvarsBelow p (substFvarAt p a e) := by
  intro e
  induction e with
  | fvar idx ty =>
    intro h
    simp only [fvarsBelow] at h
    simp only [substFvarAt]
    split
    · exact ha
    · rw [if_neg (by omega)]
      simp only [fvarsBelow]
      omega
  | _ => intro h; simp_all [substFvarAt, fvarsBelow]

theorem fvarsBelow_instMembersGo {us : List Level} :
    ∀ (L : List (Name × Expr)) (l : Nat) {e : Expr}, fvarsBelow (l + L.length) e →
      fvarsBelow l (instMembersGo us l L e)
  | [], _, _, h => h
  | (T, ty) :: rest, l, e, h => by
    simp only [instMembersGo]
    refine fvarsBelow_substFvarAt (by simp [fvarsBelow]) ?_
    refine fvarsBelow_instMembersGo rest (l + 1) ?_
    rw [show l + 1 + rest.length = l + (rest.length + 1) by omega]
    exact h

end ConLeche.Expr

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]

/-! ## §2 The reading law (X.1) -/

/-- The leaves instantiated into the fresh slots, innermost first. -/
@[expose] def instLeavesGo : List AnnotTerm → AnnotTerm → AnnotTerm
  | [], a => a
  | x :: xs, a => (instLeavesGo xs a).inst x 0

/-- A constant's leaf at a level list (the reading of `.const T us`,
`denoteMeta_const`). -/
@[expose] def leafOf (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat)
    (us : List Level) (T : Name) : AnnotTerm :=
  match env.find? T with
  | some ci => acval T (Level.substFn φ ci.toConstantVal.levelParams us)
  | none => .prf

omit [SetTheory V] in
theorem denoteMeta_const_leafOf {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {us : List Level} {T : Name} {ci : ConstantInfo}
    (hf : env.find? T = some ci) (hlen : us.length = ci.toConstantVal.levelParams.length)
    (d : Nat) :
    denoteMeta acval env φ d (.const T us) = some (leafOf acval env φ us T) := by
  rw [denoteMeta_const hf hlen]
  simp [leafOf, hf]

/-- **The members put back, read** (`denoteMeta_substFvarAt` folded):
the reading of the instantiated term at depth `l` is the reading of
the abstracted term at depth `l + k` with the leaves instantiated into
the fresh slots. -/
theorem denoteMeta_instMembersGo {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {us : List Level}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (L : List (Name × Expr)) (l : Nat) {e : Expr},
      (∀ x ∈ L, ∃ ci : ConstantInfo, env.find? x.1 = some ci ∧
        us.length = ci.toConstantVal.levelParams.length) →
      Expr.fvarsBelow (l + L.length) e →
      denoteMeta acval env φ l (Expr.instMembersGo us l L e)
        = (denoteMeta acval env φ (l + L.length) e).map
            (instLeavesGo (L.map fun x => leafOf acval env φ us x.1))
  | [], l, e, _, _ => by
    simp only [Expr.instMembersGo, List.length_nil, Nat.add_zero, List.map_nil]
    cases denoteMeta acval env φ l e <;> rfl
  | (T, ty) :: rest, l, e, hf, hfb => by
    obtain ⟨ci, hci, hlen⟩ := hf (T, ty) List.mem_cons_self
    simp only [Expr.instMembersGo, List.map_cons]
    have hfb' : Expr.fvarsBelow (l + 1 + rest.length) e := by
      rw [show l + 1 + rest.length = l + (rest.length + 1) by omega]; exact hfb
    have hsub := denoteMeta_substFvarAt (env := env) (φ := φ) hacl hainst (p := l)
      (a := .const T us) (x := leafOf acval env φ us T) (by simp [Expr.WScoped])
      (by simp [Expr.looseBVarsBounded]) (denoteMeta_const_leafOf hci hlen l)
      (Expr.instMembersGo us (l + 1) rest e) l (Nat.le_refl l)
      (Expr.fvarsBelow_instMembersGo rest (l + 1) hfb')
    rw [hsub, Nat.sub_self,
      denoteMeta_instMembersGo hacl hainst rest (l + 1)
        (fun x hx => hf x (List.mem_cons_of_mem _ hx)) hfb',
      Option.map_map, show l + 1 + rest.length = l + (rest.length + 1) by omega]
    rfl

/-- The instantiated leaves read as the frame extended by their
values (closed leaves: the value is frame-independent). -/
theorem interp_instLeavesGo :
    ∀ (xs : List AnnotTerm) (a : AnnotTerm) (ρ : Nat → V),
      (∀ x ∈ xs, ∀ k, x.liftN 1 k = x) →
      interp V ρ (instLeavesGo xs a) = interp V (consList (xs.map (interp V ρ)) ρ) a
  | [], _, _, _ => rfl
  | x :: xs, a, ρ, hcl => by
    simp only [instLeavesGo, List.map_cons, consList]
    rw [interp_inst, instE_zero, shiftE_zero_zero,
      interp_instLeavesGo xs a _ (fun y hy => hcl y (List.mem_cons_of_mem _ hy))]
    congr 2
    refine List.map_congr_left fun y hy => ?_
    have h := hcl y (List.mem_cons_of_mem _ hy) 0
    calc interp V (cons (interp V ρ x) ρ) y
        = interp V (cons (interp V ρ x) ρ) (y.liftN 1 0) := by rw [h]
      _ = interp V ρ y := by rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero]

/-- **(X.1) The abstracted reading at the leaves' values is the
reading** (DESIGN §DR.2 (a)): a term over variables below `l` whose
members are stored reads at the model as its abstraction — the
members at fresh variables `l … l + k - 1` — read at depth `l + k`
and interpreted at the frame whose fresh slots hold the members'
leaves' values.  At the fixed point this identifies the composed
functor's nested slot with the restored constructor's field. -/
theorem denoteMeta_absMembers {env : Env} (m : EnvModel V env) {φ : Name → Nat} {us : List Level}
    (L : List (Name × Expr)) (l : Nat) {e : Expr} {ea : AnnotTerm}
    (hf : ∀ x ∈ L, ∃ ci : ConstantInfo, env.find? x.1 = some ci ∧
      us.length = ci.toConstantVal.levelParams.length)
    (hfb : Expr.fvarsBelow l e)
    (hea : denoteMeta m.acval env φ l e = some ea) :
    ∃ ea' : AnnotTerm,
      denoteMeta m.acval env φ (l + L.length) (Expr.absMembersGo us l L e) = some ea' ∧
      ∀ ρ : Nat → V,
        interp V ρ ea
          = interp V (consList ((L.map fun x => leafOf m.acval env φ us x.1).map (interp V ρ)) ρ) ea' := by
  have h := denoteMeta_instMembersGo (acval := m.acval) (env := env) (φ := φ) (us := us)
    m.acval_closed (fun n ψ y k => acval_inst_self m n ψ y k) L l
    (e := Expr.absMembersGo us l L e) hf (Expr.fvarsBelow_absMembersGo (us := us) L l hfb)
  rw [Expr.instMembersGo_absMembersGo L l hfb, hea] at h
  cases hea' : denoteMeta m.acval env φ (l + L.length) (Expr.absMembersGo us l L e) with
  | none => rw [hea'] at h; exact nomatch h
  | some ea' =>
    rw [hea'] at h
    obtain rfl := Option.some.inj h
    refine ⟨ea', rfl, fun ρ => ?_⟩
    refine interp_instLeavesGo _ ea' ρ fun x hx k => ?_
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    unfold leafOf
    cases env.find? y.1 with
    | none => rfl
    | some ci => exact m.acval_closed _ _ k

end ConLeche.Model
