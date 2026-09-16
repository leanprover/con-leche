module

public import ConLeche.Model.Inductives.NestedRecFibre
public import ConLeche.Model.Inductives.NestedRecWalk
public import ConLeche.Verify.Inductives.NestedRecCtorPin
public section

/-!
# The copy constructor's agreement at the tail (task #315, M7-2, PLAN-M7 §1c)

`RestoreAgree.ctor` (`Model/Inductives/NestedRecWalk.lean`) is the
walk's leaf agreement at a `ctorPins` key: the restore rewrites a
copy's constructor `aux_q.c` applied to the block's parameters into the
CONTAINER's constructor `J.c` applied to the pin's components, and the
two readings must interpret alike wherever the restored one is graded.

This file states the two definitions the walk's shape and its leaf
agreements are phrased with at the tail's data (`nestedArity`, the key
arities; `NestedCtorPinNames`, the restore's name round-trip — K.35,
the kernel record's model face) and proves the agreement itself
(`NestedTailIn.ctorArm`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock MutualFormer MutualCtor4 AuxStored ElimState NestedPin IndCaps
  AuxType ContainerInfo ContainerMember ContainerCtor fueledOps BinderMeta PropWhen RestoreTbl)

universe w

/-! ## B0 — the two definitions the walk is stated with -/

/-- The key arities the walk's shape `AuxAppsOk` and its leaf
agreements use: a pin key's copy index count, a constructor pin key's
field count. -/
@[expose] def nestedArity (p : NestedParts) (st : ElimState) (pinsS : List PinSyn) :
    Name → Option Nat :=
  fun n =>
    match (st.pins.zipIdx.find? fun (q, _) => q.aux == n) with
    | some (_, j) => some (pinsS.getD j default).nIdx
    | none =>
      match ((st.types.drop p.k).flatMap (·.ctors)).find? fun c => c.1 == n with
      | some c => some c.2.2
      | none => none

/-- **K.35 (requested)**: the restore's constructor names round-trip —
the copy's constructor `replacePrefix J aux cc.name` restored by
`replacePrefix aux J` is the container's `cc.name` again.  True
whenever the auxiliary name is not a prefix of a stored constructor's
name, which nothing checks; stated as the kernel record's model face
until it lands. -/
@[expose] def NestedCtorPinNames (env : Env) (_p : NestedParts) (st : ElimState) : Prop :=
  ∀ (q : Nat) (qn : NestedPin), st.pins[q]? = some qn →
    ∀ (ci : ContainerInfo) (J : ContainerMember), ConLeche.containerInfo? env qn.container = some ci →
      J ∈ ci.members → J.name = qn.container →
      ∀ cc ∈ J.ctors, Name.replacePrefix qn.aux qn.container (Name.replacePrefix J.name qn.aux cc.name) = cc.name

/-! ### The arity, read at a copy constructor -/

/-- With the keys pairwise distinct, a member with the sought key IS
the `find?`. -/
private theorem find?_key_of_nodup {α : Type} (f : α → Name) {n : Name} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ a ∈ l, f a = n →
      l.find? (fun x => f x == n) = some a
  | [], _, a, ha, _ => absurd ha (by simp)
  | x :: l, hnd, a, ha, hfa => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    split
    · rename_i hx
      rcases List.mem_cons.mp ha with rfl | ha'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨a, ha', hfa.trans (beq_iff_eq.mp hx).symm⟩) hnd.1
    · rename_i hx
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact absurd (beq_iff_eq.mpr hfa) (by simp [hx])
      · exact find?_key_of_nodup f hnd.2 a ha' hfa

/-- **THE ARITY AT A COPY'S CONSTRUCTOR** is its field count: the pin
keys miss (a copy's constructor name is no copy's TYPE name) and the
copies' constructors, listed once each, answer at their own name. -/
theorem nestedArity_ctor {p : NestedParts} {st : ElimState} {pinsS : List PinSyn}
    {j : Nat} {t : AuxType} {jc : Nat} {c : Name × Expr × Nat}
    (hnotpin : ∀ q' ∈ st.pins, q'.aux ≠ c.1)
    (ht : st.types[p.k + j]? = some t) (hc : t.ctors[jc]? = some c)
    (hnd : (((st.types.drop p.k).flatMap (·.ctors)).map (·.1)).Nodup) :
    nestedArity p st pinsS c.1 = some c.2.2 := by
  have hnone : (st.pins.zipIdx.find? fun (q, _) => q.aux == c.1) = none := by
    refine List.find?_eq_none.mpr fun x hx => ?_
    obtain ⟨q, i⟩ := x
    show ¬ ((q.aux == c.1) = true)
    exact fun hh => hnotpin q (List.fst_mem_of_mem_zipIdx hx) (beq_iff_eq.mp hh)
  have htm : t ∈ st.types.drop p.k := by
    refine List.mem_of_getElem? (i := j) ?_
    rw [List.getElem?_drop]
    exact ht
  have hcm : c ∈ (st.types.drop p.k).flatMap (·.ctors) :=
    List.mem_flatMap.mpr ⟨t, htm, List.mem_of_getElem? hc⟩
  have hfind := find?_key_of_nodup (·.1) hnd c hcm rfl
  simp only [nestedArity, hnone, hfind]

end ConLeche.Model
