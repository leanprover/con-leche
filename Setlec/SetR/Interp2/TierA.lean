import Setlec.SetR.Interp2.Kit

/-!
# The tier-A interface: what the `λ` node must carry (task #151, tier B)

Tier A landed `Setlec/SetR/Annot/Syntax.lean` with

```
| lam (u : Nat) (ty body : AVExpr)     -- `ty`'s sort
| pi  (u v : Nat) (ty body : AVExpr)   -- `ty`'s sort and `body`'s sort
```

faithfully to `Setlec/SetR/Rel.lean`'s premises: I6 (∀-formation) has
*two* `DefEq … (.sort _)` premises, I7 (λ) has *one*, and it is the
domain's.

**The `pi` annotation is exactly what tier B needs.  The `lam`
annotation is the wrong one.**  A λ's regime is decided by its
*codomain* — an abstraction is squashed iff the product it inhabits is
a proposition iff the body's type has sort `0` — and the domain's sort
`u` says nothing about that.  (`u` is not wrong, just not sufficient:
`interp2` reads it nowhere, tier C may.)

`lam_cod_sort_needed` below is the mechanized form of the claim.  It
refutes the existence of *any* λ-clause of the shape a structural,
environment-free interpretation can have — a function of the node's
annotation, the domain's value and the body's fibre function — that is
sound at both regimes.  The witness is one term shape at two
codomains: the constantly-canonical-proof function on `{•}`, which must
be the proof point when its codomain is `Prop` and must be a graph when
its codomain is a type.  Both typings are available with *identical*
`(u, ⟦A⟧, x ↦ ⟦b⟧)`, so no clause on that data can serve both.

**The fix is one numeral**: `lam (u v : Nat) (ty body : AVExpr)`, with
`v` the sort of the body's type, and `interp2`'s clause becomes
`lamR v ⟦ty⟧ (fun x => ⟦body⟧ₓ)` — which is what
`Interp2/Syntax.lean`'s provisional node already carries.  The premise
is not in I7 as stated; supplying it means I7 gains the body-sort
premise its ∀-formation sibling I6 already has (`Infer Δ' B tB` and
`DefEq Δ' tB (.sort v)` for the opened body).  That is also why the
kernel's λ-codomain `ensureSort` — which the #100 de-gating plan lists
for deletion — is **load-bearing for tier B** and must not be dropped:
see `Setlec/SetR/DESIGN.md`, tier B, finding F4.

Until that lands, `Interp2/*` stays on its own provisional `AVExpr`
(`Interp2/Syntax.lean`), which differs from tier A's in exactly two
places: the extra `lam` numeral, and the absent `const` case (a
separate landing, see DESIGN).
-/

namespace Setlec.SetR.Interp2

open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The λ node needs its codomain sort.**  There is no function `L`
of a λ node's *domain-side* data — the annotation `u`, the domain value
`A`, and the body's fibre function `F` — that lands in the product at
every codomain regime.

This is precisely the shape a structural, environment-free
interpretation's λ clause has (`interp2`'s is
`fun ρ u A b => L u (interp2 ρ A) (fun x => interp2 (cons x ρ) b)`), so
the refutation applies to any such interpretation over tier A's current
`AVExpr`.

The witness: `A = {•}`, `F = fun _ => •`, `B = fun _ => {•}` — a
correct fibre assignment.  Read at `v = 0` it forces `L 0 {•} F = •`
(proof irrelevance); read at `v = 1` it forces `L 0 {•} F ≠ •` (a
graph).  The two readings share every argument of `L`. -/
theorem lam_cod_sort_needed (L : Nat → V → (V → V) → V)
    (hL : ∀ (u v : Nat) (A : V) (F B : V → V),
      (∀ x, x ∈ˢ A → F x ∈ˢ B x) → L u A F ∈ˢ piR v A B) : False := by
  have hFB : ∀ x, x ∈ˢ (unitSet : V) →
      (fun _ : V => (pt : V)) x ∈ˢ (fun _ : V => (unitSet : V)) x :=
    fun _ _ => pt_mem_unitSet
  have h0 := hL 0 0 unitSet (fun _ => pt) (fun _ => unitSet) hFB
  have h1 := hL 0 1 unitSet (fun _ => pt) (fun _ => unitSet) hFB
  exact (mem_piR_pos (by decide) h1).2.2.2 (eq_pt_of_mem_piR_zero h0)

/-- The positive half, for contrast: with the codomain sort available
the λ clause *is* sound at both regimes, uniformly and with the same
premise — `lamR` is such an `L` once it is given `v`. -/
theorem lamR_sound_at_every_regime (_u v : Nat) (A : V) (F B : V → V)
    (hFB : ∀ x, x ∈ˢ A → F x ∈ˢ B x) : lamR v A F ∈ˢ piR v A B :=
  lamR_mem hFB

end Setlec.SetR.Interp2
