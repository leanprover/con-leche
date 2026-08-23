import Setlec.Model.DirectVal

/-!
# The dependent-pair tower of a simple structure

A simple structure (non-recursive, single constructor, index-free)
with fields `f₀ : F₀, …, f_{n-1} : F_{n-1}` and result sort `s` is
modelled, at each parameter instantiation, by the **iterated dependent
pair set** over the interpreted field telescope, closed off by the
singleton:

    ⟦T p⃗⟧ = Σ (x₀ ∈ ⟦F₀⟧) Σ (x₁ ∈ ⟦F₁[x₀]⟧) … {∗}

— the very tower the `lean-inductive-models` preprocessor builds
syntactically out of `PSigma'`/`PUnit`, here built directly out of
`SetTheory.sigmaSet`.  The constructor is the iterated Kuratowski pair
(`tupleV`), field `i` is the `i`-th iterated second-then-first
projection (`projV`).

Everything is stated at a **nonzero** structure sort `w ≠ 0`: the
direct install path narrows the recognised class to structures whose
result sort is provably nonzero (`Level.isNeverZero`), so the `Prop`
collapse of `sigmaSet` — which destroys `projV i (tupleV f⃗) = f_i`
whenever a `Prop` structure carries data fields — never arises.  See
DESIGN.md, "Direct install of simple structures".

The three facts the install consumes:

* `sigmaTowerV_mem_univ` — the tower is small (formation);
* `tupleV_mem` / `projV_tupleV` — introduction and the iota equation;
* `sigmaTowerV_split` — every member *is* the tuple of its own
  projections, and those projections fit the field telescope: the
  structure-eta law, and what makes the recursor's motive
  `⟦motive x⟧` reachable from `⟦motive (C p⃗ f⃗)⟧`.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}
variable {cval : ConstVal V}

open SetTheory Expr

/-- The field telescope is interpretable binder by binder and every
domain is small for the structure's own sort `w` (the official
kernel's per-field universe bound, `resultLevel ≥ sort-of(field)`;
lean4lean `Inductive/Add.lean:225-228`). -/
def FieldTele (V : Type u) [SetTheory V] (cval : ConstVal V) (env : Env)
    (φ : Name → Nat) (w : Nat) : Nat → Nat → (Nat → V) → Expr → Prop
  | 0, _, _, _ => True
  | k + 1, d, ρ, .forallE n dom body _ =>
    ∃ A, interpExpr V cval env φ d ρ dom = some A ∧ A ∈ˢ (univ w : V) ∧
      ∀ x, x ∈ˢ A →
        FieldTele V cval env φ w k (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n dom))
  | _ + 1, _, _, _ => False

/-- The iterated dependent-pair set over the first `k` binders of the
field telescope `ty`, at the structure's sort `w`. -/
noncomputable def sigmaTowerV (V : Type u) [SetTheory V]
    (cval : ConstVal V) (env : Env) (φ : Name → Nat) (w : Nat) :
    Nat → Nat → (Nat → V) → Expr → V
  | 0, _, _, _ => unitSet
  | k + 1, d, ρ, .forallE n dom body _ =>
    sigmaSet w ((interpExpr V cval env φ d ρ dom).getD SetTheory.empty)
      (fun x => sigmaTowerV V cval env φ w k (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n dom)))
  | _ + 1, _, _, _ => SetTheory.empty

theorem sigmaTowerV_forallE (w k d : Nat) (ρ : Nat → V) (n : Name)
    (dom body : Expr) (m : BinderMeta) :
    sigmaTowerV V cval env φ w (k + 1) d ρ (.forallE n dom body m) =
      sigmaSet w ((interpExpr V cval env φ d ρ dom).getD SetTheory.empty)
        (fun x => sigmaTowerV V cval env φ w k (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n dom))) := rfl

/-- The iterated pair, closed off by the proof point. -/
noncomputable def tupleV : List V → V
  | [] => pt
  | x :: xs => spair x (tupleV xs)

/-- Field `i` of an iterated pair. -/
noncomputable def projV : Nat → V → V
  | 0, t => sfst t
  | i + 1, t => projV i (ssnd t)

theorem projV_succ (i : Nat) (t : V) : projV (i + 1) t = projV i (ssnd t) := rfl

/-! ### Formation -/

theorem sigmaTowerV_mem_univ :
    ∀ {w k d : Nat} {ρ : Nat → V} {ty : Expr},
      FieldTele V cval env φ w k d ρ ty →
      sigmaTowerV V cval env φ w k d ρ ty ∈ˢ (univ w : V) := by
  intro w k
  induction k with
  | zero => intro d ρ ty _; exact unitSet_mem_univ w
  | succ k ih =>
    intro d ρ ty h
    match ty with
    | .forallE n dom body m =>
      obtain ⟨A, hA, hAu, hrest⟩ := h
      rw [sigmaTowerV_forallE, hA]
      dsimp only [Option.getD]
      have h2 := sigma_mem_univ (u := w) (v := w) (A := A)
        (B := fun x => sigmaTowerV V cval env φ w k (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n dom)))
        hAu (fun x hx => ih (hrest x hx))
      have hm : Nat.max w w = w := by simp
      rw [hm] at h2
      exact h2
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ => exact h.elim

/-! ### Introduction and the iota equation -/

theorem tupleV_mem :
    ∀ {w k d : Nat} {ρ : Nat → V} {ty : Expr} {fs : List V}
      {d' : Nat} {ρ' : Nat → V} {rest : Expr},
      w ≠ 0 → FieldTele V cval env φ w k d ρ ty →
      TeleFit V cval env φ d ρ ty fs d' ρ' rest → fs.length = k →
      tupleV fs ∈ˢ sigmaTowerV V cval env φ w k d ρ ty := by
  intro w k
  induction k with
  | zero =>
    intro d ρ ty fs d' ρ' rest _ _ _ hlen
    obtain rfl : fs = [] := List.eq_nil_of_length_eq_zero hlen
    exact pt_mem_unitSet
  | succ k ih =>
    intro d ρ ty fs d' ρ' rest hw hfld hfit hlen
    cases hfit with
    | nil => exact absurd hlen (by simp)
    | @cons d ρ n dom body m x fs d₂ ρ₂ rest A hdom hx hfit =>
      obtain ⟨A', hA', -, hrest⟩ := hfld
      obtain rfl : A' = A := by rw [hdom] at hA'; exact (Option.some.inj hA').symm
      rw [sigmaTowerV_forallE, hdom]
      dsimp only [Option.getD]
      exact spair_mem hw hx
        (ih hw (hrest x hx) hfit (by simpa using hlen))

theorem projV_tupleV :
    ∀ (i : Nat) (fs : List V), i < fs.length →
      projV i (tupleV fs) = fs.getD i SetTheory.empty := by
  intro i
  induction i with
  | zero =>
    intro fs h
    match fs with
    | x :: fs => rw [tupleV, projV, sfst_spair]; rfl
    | [] => exact absurd h (by simp)
  | succ i ih =>
    intro fs h
    match fs with
    | x :: fs =>
      rw [tupleV, projV_succ, ssnd_spair]
      rw [ih fs (by simpa using h)]
      rfl
    | [] => exact absurd h (by simp)

/-! ### Eta: every member is the tuple of its own projections -/

theorem sigmaTowerV_split :
    ∀ {w k d : Nat} {ρ : Nat → V} {ty : Expr} {t : V},
      w ≠ 0 → FieldTele V cval env φ w k d ρ ty →
      t ∈ˢ sigmaTowerV V cval env φ w k d ρ ty →
      ∃ d' ρ' rest,
        TeleFit V cval env φ d ρ ty
          ((List.range k).map fun i => projV i t) d' ρ' rest ∧
        tupleV ((List.range k).map fun i => projV i t) = t := by
  intro w k
  induction k with
  | zero =>
    intro d ρ ty t _ _ ht
    exact ⟨d, ρ, ty, TeleFit.nil, (mem_unitSet_iff.mp ht).symm⟩
  | succ k ih =>
    intro d ρ ty t hw hfld ht
    match ty with
    | .forallE n dom body m =>
      obtain ⟨A, hA, -, hrest⟩ := hfld
      rw [sigmaTowerV_forallE, hA] at ht
      dsimp only [Option.getD] at ht
      obtain ⟨a, b, ha, hb, -, hpair⟩ := mem_sigma_elim ht
      obtain rfl : t = spair a b := hpair hw
      obtain ⟨d', ρ', rest, hfit, htup⟩ := ih hw (hrest a ha) hb
      have hmap : ((List.range (k + 1)).map fun i => projV i (spair a b)) =
          a :: ((List.range k).map fun i => projV i b) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1
        · rw [projV, sfst_spair]
        · exact List.map_congr_left (fun i _ => by
            simp only [Function.comp_apply, projV_succ, ssnd_spair])
      refine ⟨d', ρ', rest, ?_, ?_⟩
      · rw [hmap]
        exact TeleFit.cons hA ha hfit
      · rw [hmap, tupleV, htup]
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ => exact hfld.elim

end Setlec
