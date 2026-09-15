module

public import ConLeche.Model.Inductives.DirectRun
public import ConLeche.Model.Inductives.StructRows
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.IndReduct
import ConLeche.Model.Steps.IotaRows
public section

/-!
# The DIRECT nested route at the run — (X): the nested slot at the X-frame (task #314 DR-2)

DESIGN §DR.2.  The composed functor of the direct route reads a nested
slot — a constructor field whose domain is a container application at
the block's members, `List (Tree α)` — at the X-FRAME: the frame where
the members are read as the family variable `X`.  `denoteMeta` bakes a
constant's leaf in (`acval T ψ` at every `.const T` node), so the run's
readings cannot be re-opened at `X`; the device of this module is to
read the slot's SYNTAX with the members ABSTRACTED to fresh variables
and to spell the family in the variables' slots.

* **§1 The abstraction** (`Expr.absConstAt`, `absMembersGo`): a
  constant's every occurrence at the block's own levels becomes an
  `fvar` at a fresh level (the members at `nP … nP + k - 1`, above the
  parameter openers), and `Expr.substFvarAt` puts it back
  (`instMembersGo_absMembersGo`).
* **§2 The reading law (X.1)** (`denoteMeta_absMembers`): the reading
  of a term at the model equals the reading of its abstraction at the
  frame whose fresh slots hold the leaves' values — `denoteMeta_substFvarAt`
  (`Model/Annot/BitInst.lean`) folded over the members, `interp_inst`
  at cut `0`.  This is the direction the leaf's typing needs: at the
  fixed point the slot reads as the restored constructor's field.
* **§3 The fit at every member value (X.2)**: `NestedPinsAbsOk`, the
  spec of the kernel record K.27 (the pins' components type-checked
  with the members abstracted, at the PRE-BLOCK environment), NAMED
  here and consumed by `pinFitAbs_of_run`: the abstracted components
  fit the container's parameter telescope at EVERY frame satisfying
  the members' former types — in particular at the family variable,
  which is what the composed functor's laws are stated over.  DESIGN
  §DR.2 (b) is the finding that no fact of today's run gives this: the
  kernel compares the member's sort with the container's parameter
  sort INSIDE the pin's inference, and a claim about the whole pin
  reads that comparison off at the leaf only.
-/

namespace ConLeche.Expr

open ConLeche (Name Level)

/-! ## §1 The abstraction of a constant to a fresh variable -/

/-- Replace every `.const T us` by `.fvar l ty` (the annotations of
existing variables are not descended into, as in `abstract1`). -/
def absConstAt (T : Name) (us : List Level) (l : Nat) (ty : Expr) : Expr → Expr
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
def absMembersGo (us : List Level) : Nat → List (Name × Expr) → Expr → Expr
  | _, [], e => e
  | l, (T, ty) :: rest, e => absMembersGo us (l + 1) rest (absConstAt T us l ty e)

/-- The members put back, innermost (highest level) first. -/
def instMembersGo (us : List Level) : Nat → List (Name × Expr) → Expr → Expr
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
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule NestedPin ElimState
  ContainerInfo ContainerMember CheckMode)

universe w

variable {V : Type w} [SetTheory V]

/-! ## §2 The reading law (X.1) -/

/-- The leaves instantiated into the fresh slots, innermost first. -/
def instLeavesGo : List AnnotTerm → AnnotTerm → AnnotTerm
  | [], a => a
  | x :: xs, a => (instLeavesGo xs a).inst x 0

/-- A constant's leaf at a level list (the reading of `.const T us`,
`denoteMeta_const`). -/
def leafOf (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat)
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

/-! ## §3 K.27 — the pins' components at ABSTRACTED members (a kernel record REQUEST), and its consumer -/

/-- **The abstracted pin**: the pin's term with every member
`T_m.{lps}` replaced by the variable `nP + m`, annotated by the
member's annotated former type (`fmsA`, K.12). -/
def absPin (p : ConLeche.NestedParts) (fmsA : List ConstantVal) (q : NestedPin) : Expr :=
  Expr.absMembersGo (p.lps.map Level.param) p.nP (p.memberNames.zip (fmsA.map (·.type))) q.pin

/-- **K.27 (a kernel record REQUEST, DESIGN §DR.2 (c))**: every pin's
abstracted term is given a type at the PRE-BLOCK environment by
inference at depth `nP + k` — `nestedPinsOk`'s check with the members
as VARIABLES instead of constants.  Its `_inv` twin is this statement
(the shape of `nestedPinsOk_inv`); consumed by `pinFitAbs_of_run`. -/
@[expose] def NestedPinsAbsOk (μ : CheckMode) (F : Nat) (env : Env) (p : ConLeche.NestedParts)
    (fmsA : List ConstantVal) (pins : List NestedPin) : Prop :=
  ∀ q ∈ pins, ∃ ty : Expr,
    ConLeche.inferTypeCore μ env F (p.nP + p.k) (absPin p fmsA q) = .ok ty

/-- `spineFit_of_wellDenotedV_mkAppN_lam` (`StructEntryKit.lean`) at a
PREFIX of the tower: the arguments of a graded application spine fit
the λ-tower's leading domains. -/
theorem spineFit_of_wellDenotedV_mkAppN_lam_prefix :
    ∀ {lds : List (Nat × AnnotTerm)} {b f : AnnotTerm} {args : List AnnotTerm} {ρ σ : Nat → V},
      (∀ d ∈ lds, d.1 ≠ 0) →
      WellDenotedV V ρ (AnnotTerm.mkAppN f args) →
      interp V ρ f = interp V σ (mkLamsAV lds b) →
      args.length ≤ lds.length →
      SpineFit σ ((lds.take args.length).map (·.2)) (args.map (interp V ρ))
  | _, _, _, [], _, _, _, _, _, _ => trivial
  | [], _, _, _ :: _, _, _, _, _, _, hlen => by simp at hlen
  | d :: lds, b, f, a :: args, ρ, σ, hnz, hok, hval, hlen => by
    simp only [List.length_cons, List.take_succ_cons, List.map_cons, SpineFit]
    rw [AnnotTerm.mkAppN_cons] at hok
    have hokApp := WellDenotedV_mkAppN_head args hok
    obtain ⟨-, -, v, A, B, hf, ha, -⟩ := (WellDenoted_app V ρ f a) ▸ hokApp.1
    have hd : d.1 ≠ 0 := hnz d List.mem_cons_self
    rw [hval] at hf
    simp only [mkLamsAV, interp_lam] at hf
    rw [lamR_pos hd] at hf
    have hv : v ≠ 0 := by
      intro hv0
      rw [hv0, piR_zero] at hf
      exact graph_ne_pt (eq_pt_of_mem_truthVal hf)
    rw [piR_pos hv] at hf
    have hmem : interp V ρ a ∈ˢ interp V σ d.2 := graph_dom_of_mem_piSet hf _ ha
    refine ⟨hmem, ?_⟩
    refine spineFit_of_wellDenotedV_mkAppN_lam_prefix (b := b)
      (fun d' hd' => hnz d' (List.mem_cons_of_mem _ hd')) hok ?_ (by simpa using hlen)
    rw [interp_app, hval]
    simp only [mkLamsAV, interp_lam]
    rw [app_lamR_pos hd hmem]

/-- A former checked at the front door reads at the model, graded at
every frame, closed (its reading is lift-invariant and reads the same
at every depth). -/
theorem formerType_reads {μ : CheckMode} (hμ : μ.verifiedChecks = true) {env : Env}
    (mp : EnvModelM V μ env) {F : Nat} {cv cvTa : ConstantVal}
    (hff : ConLeche.FormerFront μ F env cv cvTa) (φ : Name → Nat) :
    ∃ ta : AnnotTerm,
      denoteMeta mp.base2.acval env φ 0 cvTa.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ k, ta.liftN 1 k = ta) ∧
      (∀ d, denoteMeta mp.base2.acval env φ d cvTa.type = some ta) ∧
      ∀ ρ ρ' : Nat → V, interp V ρ ta = interp V ρ' ta := by
  obtain ⟨stype, u, hst, hens⟩ := hff.infer
  have hnf := hff.noFvar
  have hbt := hff.bounded
  have hw : Expr.WScoped 0 cvTa.type := Expr.WScoped.of_not_hasFvar hnf
  have hL : Expr.LeavesBounded cvTa.type := Expr.LeavesBounded.of_not_hasFvar hnf
  have hnil : cvTa.type.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf
  obtain ⟨ta, hta⟩ := acceptedReads_of mp.base2 φ hst hw hbt hL
  have hc := claimsAt_of hμ mp φ F
  have hcl : ∀ k, ta.liftN 1 k = ta := fun k =>
    denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed hnf hbt hta 1 k
  have hbel : Term.bvarsBelow 0 ta.erase :=
    denote_closed mp.base2.cval_closed hnf hbt (denoteMeta_erase mp.base2.acval_erase 0 _ hta)
  refine ⟨ta, hta, fun ρ => (hc.sortRow hst hens hw hbt hL (CtxOk.nil hnil) hta ρ (Sat_nil V ρ)).1,
    hcl, denoteMeta_depth_of_closed mp.base2.acval_closed hnf hcl hta, fun ρ ρ' => ?_⟩
  exact interp_closed V hbel ρ ρ'

omit [SetTheory V] in
/-- A list of witnesses, positionally. -/
theorem exists_list_of_forall {α β : Type} {P : α → β → Prop} :
    ∀ (l : List α), (∀ x ∈ l, ∃ y, P x y) →
      ∃ ys : List β, ys.length = l.length ∧ ∀ (i : Nat) (x : α), l[i]? = some x →
        ∃ y, ys[i]? = some y ∧ P x y
  | [], _ => ⟨[], rfl, fun i x hx => nomatch hx⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hlen, hall⟩ := exists_list_of_forall l fun x' hx' => h x' (List.mem_cons_of_mem _ hx')
    refine ⟨y :: ys, by simp [hlen], fun i x' hx' => ?_⟩
    cases i with
    | zero =>
      obtain rfl : x = x' := by simpa using hx'
      exact ⟨y, rfl, hy⟩
    | succ i => exact hall i x' (by simpa using hx')

/-- The head of `nestedTypes0` is the first annotated former. -/
theorem nestedTypes0_head {p : ConLeche.NestedParts} {fmsA ctorsA : List ConstantVal}
    {t₀ : ConLeche.AuxType} (h : (ConLeche.nestedTypes0 p fmsA ctorsA).head? = some t₀) :
    ∃ cvT, fmsA[0]? = some cvT ∧ t₀.type = cvT.type := by
  cases fmsA with
  | nil => simp [ConLeche.nestedTypes0] at h
  | cons cvT rest =>
    refine ⟨cvT, rfl, ?_⟩
    simp only [ConLeche.nestedTypes0, List.zipIdx_cons, List.map_cons, List.head?_cons,
      Option.some.injEq] at h
    rw [← h]

set_option maxHeartbeats 1600000 in
/-- **(X.2) The abstracted components fit the container's parameter
telescope at every member value** — the consumer of K.27 (DESIGN
§DR.2 (c)).  At every pin of a nested run: the pin is `J.{lvls} Ds`
with `J` a stored container member of a group with a datum at the
pre-block model (`hrep`), its abstracted components read at the
pre-block model at depth `nP + k`, and at EVERY frame satisfying the
context `Δ` — the members' former types (closed) above the block's
parameter openers — the readings fit `J`'s parameter telescope and
the application `⟦J⟧ DsX` is graded.  The frame ranges over every
value of the members in their former types: the family variable's
curried tower is one, which is what the composed functor's laws
consume; the members' leaves are another (with (X.1) this is the
restored constructor's field at the fixed point). -/
theorem pinFitAbs_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat} {env : Env}
    (mp : EnvModelM V μ env) {p : ConLeche.NestedParts} {fmsA ctorsA : List ConstantVal}
    {st : ElimState} {t₀ : ConLeche.AuxType} {params : List Expr} {body : Expr}
    (hannF : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p.nP
      p.formers = .ok fmsA)
    (hannC : ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st)
    (ht₀ : (ConLeche.nestedTypes0 p fmsA ctorsA).head? = some t₀)
    (hop : ConLeche.openPisAtFvars p.nP t₀.type 0 = some (params, body))
    (hrep : ContainersRepPre env mp.base2)
    (hK27 : NestedPinsAbsOk μ F env p fmsA st.pins) (φ : Name → Nat) :
    ∃ Δ : List AnnotTerm, Δ.length = p.nP + p.k ∧
      -- the context's member entries are the members' former types' readings, closed
      (∀ (m : Nat) (cvT : ConstantVal), fmsA[m]? = some cvT →
        ∃ ta, denoteMeta mp.base2.acval env φ 0 cvT.type = some ta ∧ Δ[p.k - 1 - m]? = some ta ∧
          ∀ ρ ρ' : Nat → V, interp V ρ ta = interp V ρ' ta) ∧
      ∀ q ∈ st.pins, ∃ (I : Name) (ci : ContainerInfo) (mm : Nat) (J : ContainerMember)
        (lvls : List Level) (Ds : List Expr) (cvTJ : ConstantVal) (capsJ : IndCaps)
        (dJ : IndRepData V) (DsX : List AnnotTerm),
        ConLeche.containerInfo? env I = some ci ∧ ci.members[mm]? = some J ∧
        q.container = J.name ∧ q.pin = Expr.mkAppN (.const J.name lvls) Ds ∧
        Ds.length = dJ.nP ∧ mm < dJ.k ∧ dJ.kReal = dJ.k ∧
        env.find? J.name = some (.indInfo cvTJ capsJ) ∧
        lvls.length = cvTJ.levelParams.length ∧
        (∃ (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
          IndRep mp.base2 J.name cvTJ cvR mI rP rules dJ mm) ∧
        DenoteMetaSpine mp.base2.acval env φ (p.nP + p.k)
          (Ds.map (Expr.absMembersGo (p.lps.map Level.param) p.nP
            (p.memberNames.zip (fmsA.map (·.type))))) DsX ∧
        ∀ ρ : Nat → V, Sat V Δ ρ →
          WellDenotedV V ρ (AnnotTerm.mkAppN
            (mp.base2.acval J.name (Level.substFn φ cvTJ.levelParams lvls)) DsX) ∧
          SpineFit ρ (((dJ.ppsM mm (Level.substFn φ cvTJ.levelParams lvls)).take dJ.nP).map (·.2.2))
            (DsX.map (interp V ρ)) ∧
          Sat V (dJ.params (Level.substFn φ cvTJ.levelParams lvls)).reverse
            (consList (DsX.map (interp V ρ)) ρ) := by
  -- ## the formers: read at the pre-block model, closed
  obtain ⟨hkF, hfront⟩ := ConLeche.nestedAnnotFormers_inv hannF
  have hk : fmsA.length = p.k := hkF
  obtain ⟨tas, hlenTas, htas⟩ := exists_list_of_forall
    (P := fun (cvT : ConstantVal) (ta : AnnotTerm) =>
      denoteMeta mp.base2.acval env φ 0 cvT.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧ (∀ k, ta.liftN 1 k = ta) ∧
      (∀ d, denoteMeta mp.base2.acval env φ d cvT.type = some ta) ∧
      ∀ ρ ρ' : Nat → V, interp V ρ ta = interp V ρ' ta)
    fmsA (fun cvT hcvT => by
      obtain ⟨m, hm⟩ := List.getElem?_of_mem hcvT
      obtain ⟨cv, nIdx, -, hff⟩ := hfront m cvT hm
      exact formerType_reads hμ mp hff φ)
  -- the members' names are fresh, their annotated types closed
  have hfresh : ∀ (m : Nat) (cvT : ConstantVal), fmsA[m]? = some cvT →
      env.find? cvT.name = none ∧ cvT.type.hasFvar = false ∧
      cvT.type.looseBVarsBounded 0 = true ∧ p.memberNames[m]? = some cvT.name := by
    intro m cvT hm
    obtain ⟨cv, nIdx, hl, hff⟩ := hfront m cvT hm
    refine ⟨by rw [hff.name]; exact hff.fresh, hff.noFvar, hff.bounded, ?_⟩
    simp only [ConLeche.NestedParts.memberNames, List.getElem?_map, hl, Option.map_some, hff.name]
  -- ## the head former, opened at the pre-block model
  obtain ⟨cvT₀, hcvT₀, ht₀ty⟩ := nestedTypes0_head ht₀
  obtain ⟨ta₀, -, hta₀, hok₀, -, -, -⟩ := htas 0 cvT₀ hcvT₀
  obtain ⟨-, hnf₀, hb₀, -⟩ := hfresh 0 cvT₀ hcvT₀
  obtain ⟨Γ, R, -, hopened⟩ := opened_of (V := V) (m := mp.base2) (φ := φ) hop
    (by rw [ht₀ty]; exact hnf₀) (by rw [ht₀ty]; exact hb₀) (by rw [ht₀ty]; exact hta₀)
    (fun ρ => hok₀ ρ)
  have hΓlen : Γ.length = p.nP := hopened.len
  have hlenP : params.length = p.nP := openPisAtFvars_length p.nP hop
  -- the pins' leaves are the openers
  have hpo : PinsAtOpeners st params :=
    pinsAtOpeners_of_run mp hannC helim ht₀ (by rw [ht₀ty]; exact hnf₀) hop
  -- ## the context: the members' types above the openers' entries
  let us : List Level := p.lps.map Level.param
  let L : List (Name × Expr) := p.memberNames.zip (fmsA.map (·.type))
  have hLlen : L.length = p.k := by
    simp only [L, List.length_zip, List.length_map, hk, ConLeche.NestedParts.memberNames,
      ConLeche.NestedParts.k, Nat.min_self]
  let Δ : List AnnotTerm := tas.reverse ++ Γ
  have hΔlen : Δ.length = p.nP + p.k := by
    simp only [Δ, List.length_append, List.length_reverse, hlenTas, hk, hΓlen]; omega
  refine ⟨Δ, hΔlen, fun m cvT hm => ?_, fun q hq => ?_⟩
  · obtain ⟨ta, hta, hread, -, -, -, hcl⟩ := htas m cvT hm
    have hm' : m < p.k := by rw [← hk]; exact (List.getElem?_eq_some_iff.mp hm).1
    refine ⟨ta, hread, ?_, hcl⟩
    simp only [Δ]
    rw [List.getElem?_append_left (by simp [hlenTas, hk]; omega), List.getElem?_reverse
      (by simp [hlenTas, hk]; omega)]
    simp only [hlenTas, hk]
    rw [show p.k - 1 - (p.k - 1 - m) = m by omega]
    exact hta
  · -- ## the pin's shape
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hq
    have hjlt : j < st.pins.length := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨t₀', params', body', pbs, body₀, ht₀', hop', -, I, ci, i, j₀, J, lvls, Ds, q', copy,
      st₁, st₂, cs', hci, hJ, -, -, hq', hqc, hqp, -, -, -, hDsB, -, -, hDsLen, -⟩ :=
      ConLeche.elimNested_copy helim hjlt
    obtain rfl : q = q' := Option.some.inj (hj.symm.trans hq')
    obtain rfl : t₀ = t₀' := Option.some.inj (ht₀.symm.trans ht₀')
    rw [hop] at hop'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hop')
    -- the container's datum at the pre-block model
    obtain ⟨dJ, -, hkR, hnPJ, hlenM, -, -, -, -, -, hmem⟩ := hrep I ci hci
    obtain ⟨cvTJ, cvR, capsJ, mI, rP, rules, hfJ, -, hJlps, -, -, -, hrepJ⟩ := hmem i J hJ
    have hmm : i < dJ.k := by rw [← hlenM]; exact (List.getElem?_eq_some_iff.mp hJ).1
    -- `J` is not a member of the block
    have hJne : ∀ x ∈ L, x.1 ≠ J.name := by
      intro x hx hxn
      obtain ⟨m, hm⟩ := List.getElem?_of_mem hx
      obtain ⟨n, ty⟩ := x
      obtain ⟨hn, hty⟩ := List.getElem?_zip_eq_some.mp hm
      rw [List.getElem?_map] at hty
      cases hc : fmsA[m]? with
      | none => rw [hc] at hty; exact nomatch hty
      | some cvT =>
        obtain ⟨hfr, -, -, hname⟩ := hfresh m cvT hc
        rw [hname] at hn
        obtain rfl := Option.some.inj hn
        simp only at hxn
        rw [hxn, hfJ] at hfr
        exact nomatch hfr
    -- ## the abstracted pin: its scope, leaves, reading
    have habs : absPin p fmsA q = Expr.mkAppN (.const J.name lvls) (Ds.map (Expr.absMembersGo us p.nP L)) := by
      simp only [absPin, hqp]
      rw [Expr.absMembersGo_mkAppN, Expr.absMembersGo_const_ne L p.nP hJne]
    -- the member variables
    let mems : List Expr := (List.range p.k).map fun m =>
      Expr.fvar (p.nP + m) ((fmsA.map (·.type)).getD m default)
    let fvs : List Expr := params ++ mems
    have hmemsLen : mems.length = p.k := by simp [mems]
    have hmems : ∀ (m : Nat), m < p.k → ∃ cvT, fmsA[m]? = some cvT ∧
        mems[m]? = some (Expr.fvar (p.nP + m) cvT.type) := by
      intro m hm
      obtain ⟨cvT, hcvT⟩ : ∃ cvT, fmsA[m]? = some cvT :=
        ⟨_, List.getElem?_eq_getElem (by rw [hk]; exact hm)⟩
      refine ⟨cvT, hcvT, ?_⟩
      simp only [mems, List.getElem?_map, List.getElem?_range hm, Option.map_some,
        List.getD_eq_getElem?_getD, List.getElem?_map, hcvT, Option.getD_some]
    -- the leaves of the abstracted pin are the openers and the member variables
    have hleaves : ∀ l ∈ (absPin p fmsA q).fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
      intro l hl
      simp only [absPin] at hl
      rcases Expr.fvarLeaves_absMembersGo L p.nP hl with hl' | ⟨m, T, ty, hLm, hl'⟩
      · exact List.mem_append_left _ (hpo q hq l hl')
      · obtain ⟨-, hty⟩ := List.getElem?_zip_eq_some.mp hLm
        rw [List.getElem?_map] at hty
        obtain ⟨cvT, hcvT, rfl, hm⟩ : ∃ cvT, fmsA[m]? = some cvT ∧ ty = cvT.type ∧ m < p.k := by
          cases hc : fmsA[m]? with
          | none => rw [hc] at hty; exact nomatch hty
          | some cvT =>
            rw [hc] at hty
            exact ⟨cvT, rfl, (Option.some.inj hty).symm,
              by rw [← hk]; exact (List.getElem?_eq_some_iff.mp hc).1⟩
        obtain ⟨-, hnf, -, -⟩ := hfresh m cvT hcvT
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
        subst hl'
        obtain ⟨cvT', hcvT', hmem'⟩ := hmems m hm
        rw [hcvT] at hcvT'
        obtain rfl := Option.some.inj hcvT'
        exact List.mem_append_right _ (List.mem_of_getElem? hmem')
    have hfvsWS : ∀ x ∈ fvs, Expr.WScoped (p.nP + p.k) x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨i', hi'⟩ := List.getElem?_of_mem hx
        obtain ⟨⟨ty, rfl⟩, hws, -, -, -⟩ := hopened.var i' x hi'
        simp only [Expr.WScoped]
        exact ⟨by have := (List.getElem?_eq_some_iff.mp hi').1; omega, hws⟩
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
        have hm' : m < p.k := List.mem_range.mp hm
        obtain ⟨cvT, hcvT, hmem'⟩ := hmems m hm'
        have hty : (fmsA.map (·.type)).getD m default = cvT.type := by
          simp [List.getD_eq_getElem?_getD, hcvT]
        obtain ⟨-, hnf, -, -⟩ := hfresh m cvT hcvT
        simp only [Expr.WScoped]
        exact ⟨by omega, by rw [hty]; exact Expr.WScoped.of_not_hasFvar hnf⟩
    have hwsA : Expr.WScoped (p.nP + p.k) (absPin p fmsA q) :=
      ConLeche.WScoped_of_leaves hfvsWS _ hleaves
    have hbA : (absPin p fmsA q).looseBVarsBounded 0 = true := by
      simp only [absPin]
      refine Expr.looseBVarsBounded_absMembersGo L p.nP ?_
      rw [hqp]
      exact ConLeche.looseBVarsBounded_mkAppN rfl hDsB
    have hLA : Expr.LeavesBounded (absPin p fmsA q) := by
      intro l hl
      have hmemF := hleaves l hl
      rcases List.mem_append.mp hmemF with hx | hx
      · obtain ⟨i', hi'⟩ := List.getElem?_of_mem hx
        obtain ⟨⟨ty, hty⟩, -, hb, -, -⟩ := hopened.var i' _ hi'
        exact hb
      · obtain ⟨m, hm, hx⟩ := List.mem_map.mp hx
        have hm' : m < p.k := List.mem_range.mp hm
        obtain ⟨cvT, hcvT, -⟩ := hmems m hm'
        have hty : (fmsA.map (·.type)).getD m default = cvT.type := by
          simp [List.getD_eq_getElem?_getD, hcvT]
        obtain ⟨-, -, hb, -⟩ := hfresh m cvT hcvT
        rw [hty] at hx
        have : l.2 = cvT.type := (Expr.fvar.inj hx).2.symm
        rw [this]; exact hb
    obtain ⟨ty, hinf⟩ := hK27 q hq
    obtain ⟨ea, hea⟩ := acceptedReads_of mp.base2 φ hinf hwsA hbA hLA
    -- ## the context is well-formed at the abstracted pin
    let Aa : Nat → AnnotTerm := fun i' =>
      if i' < p.nP then Γ.getD (p.nP - 1 - i') default else tas.getD (i' - p.nP) default
    have hC : CtxOk mp.base2 φ (p.nP + p.k) Δ (absPin p fmsA q) := by
      refine ctxOk_of_openers mp.base2.acval_closed (k := p.nP + p.k) (fvs := fvs) (Aa := Aa)
        (n := p.nP + p.k) hΔlen ?_ hfvsWS ?_ hleaves ?_ ?_ ?_
      · -- the variables are indexed by position
        intro i' x hx
        by_cases hi' : i' < p.nP
        · rw [List.getElem?_append_left (by omega)] at hx
          exact (hopened.var i' x hx).1
        · rw [List.getElem?_append_right (by omega), hlenP] at hx
          obtain ⟨cvT, -, hmem'⟩ := hmems (i' - p.nP) (by
            have := (List.getElem?_eq_some_iff.mp hx).1; rw [hmemsLen] at this; exact this)
          rw [hmem'] at hx
          exact ⟨cvT.type, by rw [← Option.some.inj hx, show p.nP + (i' - p.nP) = i' by omega]⟩
      · -- the annotations read at their own depths
        intro i' x hx
        by_cases hi' : i' < p.nP
        · rw [List.getElem?_append_left (by omega)] at hx
          simp only [Aa, if_pos hi']
          exact hopened.doms i' x hx
        · rw [List.getElem?_append_right (by omega), hlenP] at hx
          have hlt : i' - p.nP < p.k := by
            have := (List.getElem?_eq_some_iff.mp hx).1; rw [hmemsLen] at this; exact this
          obtain ⟨cvT, hcvT, hmem'⟩ := hmems (i' - p.nP) hlt
          rw [hmem'] at hx
          obtain rfl := Option.some.inj hx
          obtain ⟨ta, hta, -, -, -, hdep, -⟩ := htas _ cvT hcvT
          simp only [Aa, if_neg hi', Expr.fvarTypeD]
          rw [List.getD_eq_getElem?_getD, hta, Option.getD_some]
          exact hdep _
      · intro l hl; have := hfvsWS _ (hleaves l hl); simp only [Expr.WScoped] at this; exact this.1
      · -- the entries
        intro i' hi'
        simp only [Δ, Aa]
        split
        · next h =>
          rw [List.getElem?_append_right (by simp [hlenTas, hk]; omega)]
          simp only [List.length_reverse, hlenTas, hk]
          rw [show p.nP + p.k - 1 - i' - p.k = p.nP - 1 - i' by omega]
          rw [List.getD_eq_getElem?_getD]
          cases hg : Γ[p.nP - 1 - i']? with
          | none => rw [List.getElem?_eq_none_iff] at hg; omega
          | some g => rfl
        · next h =>
          rw [List.getElem?_append_left (by simp [hlenTas, hk]; omega), List.getElem?_reverse
            (by simp [hlenTas, hk]; omega)]
          simp only [hlenTas, hk]
          rw [show p.k - 1 - (p.nP + p.k - 1 - i') = i' - p.nP by omega, List.getD_eq_getElem?_getD]
          cases hg : tas[i' - p.nP]? with
          | none => rw [List.getElem?_eq_none_iff] at hg; omega
          | some g => rfl
      · -- the entries are graded under the earlier ones
        intro i' hi' ρ hρ
        simp only [Aa]
        split
        · next h =>
          have hdrop := Sat_drop hρ (p.nP + p.k - i')
          have hΔdrop : Δ.drop (p.nP + p.k - i') = Γ.drop (p.nP - i') := by
            simp only [Δ]
            rw [show p.nP + p.k - i' = tas.reverse.length + (p.nP - i') by
              simp [hlenTas, hk]; omega, ← List.drop_drop, List.drop_left' rfl]
          rw [hΔdrop] at hdrop
          have := hopened.okΓ i' h (fun j => ρ (j + (p.nP + p.k - i'))) hdrop
          have hfun : (fun j => ρ (j + (p.nP + p.k - 1 - i') + 1))
              = (fun j => ρ (j + (p.nP + p.k - i'))) := funext fun j => by congr 1; omega
          rw [hfun]
          exact this
        · next h =>
          have hlt : i' - p.nP < p.k := by omega
          obtain ⟨cvT, hcvT, -⟩ := hmems (i' - p.nP) hlt
          obtain ⟨ta, hta, -, hok, -, -, -⟩ := htas _ cvT hcvT
          rw [List.getD_eq_getElem?_getD, hta, Option.getD_some]
          exact hok _
    -- ## the inference row
    have hc := claimsAt_of hμ mp φ F
    obtain ⟨-, -, hokEa, -, -⟩ := hc.inferRow hinf hwsA hbA hLA hC hea
    -- ## the reading's shape: the container's leaf at the abstracted components
    rw [habs] at hea
    obtain ⟨fa, DsX, hfa, hDsX, rfl⟩ := denoteMeta_mkAppN_inv hea
    obtain ⟨hlvls, rfl⟩ := denoteMeta_const_arity hfJ hfa
    have hDsXlen : DsX.length = dJ.nP := by rw [← hDsX.length, List.length_map, hDsLen, hnPJ]
    -- ## the fit, from the leaf's λ-shape
    have hFF := dJ.formerFacts_of_indRep hrepJ hkR (Level.substFn φ cvTJ.levelParams lvls) hmm
    obtain ⟨B, hleaf⟩ := hrepJ.leafShape i (by rw [hkR]; exact hmm) (Level.substFn φ cvTJ.levelParams lvls)
    rw [hrepJ.member] at hleaf
    refine ⟨I, ci, i, J, lvls, Ds, cvTJ, capsJ, dJ, DsX, hci, hJ, hqc, hqp, by rw [hDsLen, hnPJ],
      hmm, hkR, hfJ, hlvls, ⟨cvR, mI, rP, rules, hrepJ⟩, hDsX, fun ρ hρ => ?_⟩
    have hok := hokEa ρ hρ
    have hfit : SpineFit ρ (((dJ.ppsM i (Level.substFn φ cvTJ.levelParams lvls)).take dJ.nP).map (·.2.2))
        (DsX.map (interp V ρ)) := by
      have h := spineFit_of_wellDenotedV_mkAppN_lam_prefix (σ := ρ)
        (lds := (dJ.ppsM i (Level.substFn φ cvTJ.levelParams lvls)).map
          fun d => (dJ.w (Level.substFn φ cvTJ.levelParams lvls) + 1, d.2.2))
        (b := B) (fun d hd => by
          obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd; exact Nat.succ_ne_zero _)
        hok (by
          show interp V ρ (mp.base2.acval J.name (Level.substFn φ cvTJ.levelParams lvls)) = _
          rw [hleaf]; rfl)
        (by rw [List.length_map, hFF.1, hDsXlen]; omega)
      rw [hDsXlen, ← List.map_take, List.map_map] at h
      exact h
    refine ⟨hok, hfit, ?_⟩
    have hsat := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hfit
    rw [List.append_nil] at hsat
    exact (hrepJ.paramsIffM i (by rw [hkR]; exact hmm) _ _).mpr hsat

end ConLeche.Model
