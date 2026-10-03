module

public import Fragment.NstIndSem

@[expose] public section

/-!
# Uniqueness of witnesses under the subsingleton criterion

At a proposition the recursor's value at the point is read off a
*witness* of the fibre (`pick`, `IndSem.lean`), and the ι law needs
that witness to be the only member of the family at those indices
(`Uniq`).  This file states the criterion the checker applies to a
large eliminator on a proposition — the **subsingleton criterion**,
semantically — and proves that it delivers `Uniq`.

The criterion says: at most one constructor, and every field of a
fitting instance is either the point (its domain is a proposition,
so it carries no information) or is one of the constructor's index
expressions (so its value is fixed by the indices).  Two members at
one index are then the same tagged tuple: the same tag (there is
only one constructor), and the same fields — each field is either
the point in both or is read off the shared index values.

Con-leche: the syntactic criterion is `SubsingletonField`
(`Decl.lean`); its soundness for the fragment is what
`Install.lean` discharges.
-/

namespace Fragment.IndSpec.Nst open Fragment.NestInfo (nPK nK memberVar isMember Positive memberLevel)
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V]

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat)

/-- **The subsingleton criterion, semantically**: at a proposition,
at most one constructor, and every field of a fitting instance is
the point (its domain is a proposition) or is read off the
constructor's index expressions (the field's variable is one of
them). -/
def Subsingleton : Prop :=
  S.ctors.length ≤ 1 ∧
  ∀ c ∈ S.ctors, ∀ ps : List V, FitsVals M (S.ψ ls) base S.params ps → ∀ fs : List V,
    S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs →
    ∀ k, k < c.fields.length →
      fieldVal fs k = pt ∨ Expr.bvar (c.fields.length - 1 - k) ∈ c.idx

/-- The field with `k` earlier fields, when `k` is in range, is the
list's entry at the mirrored position. -/
theorem fieldVal_eq_getElem {fs : List V} {k p : Nat} (hp : p < fs.length)
    (hk : fs.length - 1 - k = p) : fieldVal fs k = fs[p] := by
  unfold fieldVal
  rw [hk]
  exact (List.getElem_eq_getD pt).symm

/-- **Uniqueness from the subsingleton criterion**: two members of
the family at one index are equal — each is the tagged tuple of
fields every one of which is the point or one of the (shared) index
values. -/
theorem uniq_of_subsingleton (hsub : S.Subsingleton M ls) : S.Uniq M ls := by
  intro _ ps hpf is x x' hx hx'
  obtain ⟨j, c, fs, hc, hfit, his, rfl⟩ := S.Mem_elim M ls hx
  obtain ⟨j', c', fs', hc', hfit', his', rfl⟩ := S.Mem_elim M ls hx'
  -- at most one constructor: both tags are `0` and both constructors are `ctors[0]`
  obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hc
  obtain ⟨hj', -⟩ := List.getElem?_eq_some_iff.mp hc'
  have h0 : j = 0 := by have := hsub.1; omega
  have h0' : j' = 0 := by have := hsub.1; omega
  subst h0 h0'
  have hcc : c = c' := Option.some.inj (hc.symm.trans hc')
  subst hcc
  have hmem : c ∈ S.ctors := List.mem_of_getElem? hc
  -- both field lists have the constructor's length
  have hlen := S.FitsFields_length M ls hfit
  have hlen' := S.FitsFields_length M ls hfit'
  -- the index expressions read under either list agree (the index values are shared)
  have hmap : c.idx.map (interp M (S.ψ ls) (consList fs (envP ps)))
      = c.idx.map (interp M (S.ψ ls) (consList fs' (envP ps))) := by
    have := his.symm.trans his'
    simpa only [idxVals, List.reverse_inj] using this
  -- so the field lists agree position by position
  suffices hfs : fs = fs' by rw [hfs]
  apply List.ext_getElem (by omega)
  intro p hp hp'
  by_cases hb : Expr.bvar p ∈ c.idx
  · -- the field is an index expression: read it off the shared index values
    have h := List.map_inj_left.mp hmap _ hb
    simp only [interp_bvar] at h
    rwa [consList_lt hp, consList_lt hp'] at h
  · -- otherwise the criterion makes it the point on both sides
    have hk : c.fields.length - 1 - (c.fields.length - 1 - p) = p := by omega
    have h1 := hsub.2 c hmem ps hpf fs hfit (c.fields.length - 1 - p) (by omega)
    have h2 := hsub.2 c hmem ps hpf fs' hfit' (c.fields.length - 1 - p) (by omega)
    rw [hk] at h1 h2
    rw [fieldVal_eq_getElem hp (by omega)] at h1
    rw [fieldVal_eq_getElem hp' (by omega)] at h2
    rw [h1.resolve_right hb, h2.resolve_right hb]

end IndSpec

end Fragment.IndSpec.Nst
