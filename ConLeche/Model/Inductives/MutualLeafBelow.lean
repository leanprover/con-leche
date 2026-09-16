module

public import ConLeche.Model.Inductives.MutualChains
public section

/-!
# The mutual leaf's closedness (task #315)

Two facts the mutual block's former stage reads off the leaf
(`Semantics/Tower/MutualLeafI.lean`): a Π-telescope built by
concatenation is bounded when its halves are, and the TAG type
`tagTyAV` is bounded at the parameters when every member's index
chain is.  Task #278 kept them with the auxiliary recursor's binder
data; nothing here mentions that tier, so they live on their own.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

omit [SetTheory V] in
theorem domsBelow_append {k : Nat} :
    ∀ {ds ds' : List (Nat × Nat × AnnotTerm)}, DomsBelow k ds → DomsBelow (k + ds.length) ds' →
      DomsBelow k (ds ++ ds')
  | [], _, _, h' => by simpa using h'
  | d :: ds, ds', h, h' => by
    refine ⟨h.1, domsBelow_append h.2 ?_⟩
    rw [List.length_cons, show k + (ds.length + 1) = k + 1 + ds.length by omega] at h'
    exact h'

omit [SetTheory V] in
/-- The tag type is bounded at the parameters when every member's index
chain is. -/
theorem tagTyAV_below {W nP : Nat} {Idss : List (List AnnotTerm)}
    (h : ∀ Ids ∈ Idss, FieldsBelow nP Ids) :
    Term.bvarsBelow nP (tagTyAV W Idss).erase := by
  unfold tagTyAV
  refine sumBodyAV_below fun Fs hFs => ?_
  obtain ⟨Ids, hIds, rfl⟩ := List.mem_map.mp hFs
  exact FieldsBelow_append_idxEq (h Ids hIds) (fun e he => nomatch he)

end ConLeche.Model
