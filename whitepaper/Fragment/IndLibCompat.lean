module

public import Fragment.IndLib

@[expose] public section

/-!
# COMPATIBILITY — the old inductive-closure law (to be deleted)

The fragment used to take the closed family of an inductive block
from a law of its library, **inductive closure**: for any list of
constructor telescopes (`TeleX`) some family of members of the
universe is closed under every bounded instance of every constructor.
By the ruling of 2026-10-03 (`whitepaper/PLAN.md`) that law is gone:
the closed family is a theorem, `closed_of_acc` (`Access.lean`), from
the operator's accessibility, and the family is the least fixed point
inside the set theory (`lfpFamSet`, `LfpSet.lean`).

Until the environment section is rewritten onto them, this file keeps
the old law and the telescopes it is stated with, as an extension
`IndLibCompat` of the library, so the fragment keeps building at every
landing.  The environment section (`IndSem.lean` onwards) assumes
`IndLibCompat` for now; when its last use of `inductive_closure` goes,
this file goes with it and `[IndLibCompat V]` reverts to `[IndLib V]`.
-/

namespace Fragment
open SetLib

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

/-- **DEPRECATED** — the library with the old inductive-closure law.
Every use is to be replaced by `closed_of_acc` (`Access.lean`). -/
class IndLibCompat (V : Type u) extends IndLib V where
  /-- **Inductive closure** (the old law): for every list of
  constructor telescopes with their target indices, some family of
  members of `univ n` is closed under every bounded instance of every
  constructor — the tagged tuple of the instance's values is a member
  of the family at the constructor's target. -/
  inductive_closure : ∀ {ι : Type u} {n : Nat}, n ≠ 0 →
    ∀ cs : List (TeleX ι V × (List V → ι)),
      ∃ W : ι → V, (∀ i, Mem (W i) (univ n)) ∧
        ∀ (j : Nat) (c : TeleX ι V × (List V → ι)) (fs : List V), cs[j]? = some c →
          TeleX.FitsB n W c.1 fs → Mem (tag j (tuple fs)) (W (c.2 fs))

end Fragment
