module

public import ConLeche.Model.Inductives.NestedRecFibre
public import ConLeche.Model.Inductives.NestedRecWalk
public import ConLeche.Verify.Inductives.NestedRecCtorPin
import ConLeche.Verify.Inductives.NestedElimInv
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

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

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

section Run

variable {env : Env} {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {envOut : Env}
  {st : ElimState} {b : MutualBlock} {envAux : Env} {stored : List AuxStored}
  {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms cvRns : List ConstantVal}
  {rulesM rulesN : List (List RecRule)} {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}
  {mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
    (ConLeche.consMutualFormers (fms.take p.k) env))}

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)
local notation "ENV₂" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))
local notation "ENVA" =>
  (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

local notation "DA" => (mutualBlockModel (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xFvsF xrestF eissF tssF)

local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

variable (I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN
  fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF
  tssF dsR xFvsR pinsS mp₂)
include I


/-- The syntactic inversion at a constructor-pin key. -/
theorem NestedTailIn.ctorPinInv (hnames : NestedCtorPinNames env p st)
    {n : Name} {pin : Expr} {newName : Name}
    (hfind : (ConLeche.restoreTbl p st).ctorPins.find? (fun q => q.1 == n)
      = some (n, pin, newName)) :
    ∃ (q : Nat) (qn : NestedPin) (t : AuxType) (jc : Nat) (c : Name × Expr × Nat)
      (ci : ContainerInfo) (J : ContainerMember) (cc : ContainerCtor),
      st.pins[q]? = some qn ∧ st.types[p.k + q]? = some t ∧ t.ctors[jc]? = some c ∧
      t.name = qn.aux ∧ c.1 = n ∧ pin = Expr.abstractRange qn.pin 0 p.nP 0 ∧
      q < pinsS.length ∧
      ConLeche.containerInfo? env qn.container = some ci ∧ J ∈ ci.members ∧
      J.name = qn.container ∧ J.ctors[jc]? = some cc ∧ cc.name = newName ∧
      cc.nFields = c.2.2 := by
  obtain ⟨q, qn, t, jc, c, hqn, ht, hc, hn, hpin, hnn⟩ :=
    ConLeche.restoreTbl_ctorPins_find? hfind
  -- the pins and the types are aligned
  have hlen0 : (ConLeche.nestedTypes0 p fmsA ctorsA₀).length = p.k := by
    rw [ConLeche.nestedTypes0_length, ConLeche.nestedAnnotFormers_length I.hfA]
    rfl
  have hal := ConLeche.elimNested_aligned hlen0 I.helim
  have htn : t.name = qn.aux := by
    obtain ⟨t₁, ht₁, h₁⟩ := hal.2 q qn hqn
    rwa [Option.some.inj (ht₁.symm.trans ht)] at h₁
  have hq : q < pinsS.length := by
    rw [I.out.stage.pinsLen]
    exact (List.getElem?_eq_some_iff.mp hqn).1
  -- the copy's source
  obtain ⟨t₀, pbs, body, -, -, hsrc⟩ := ConLeche.nestedCopySrcOk_inv I.hsrc
  obtain ⟨t₂, Jn, lvls, Ds, ci, J, cpy, ht₂, -, hJn, -, hci, hJf, hJname, hmk, -, -, hmap⟩ :=
    hsrc q qn hqn
  have ht2 : t₂ = t := Option.some.inj (ht₂.symm.trans ht)
  rw [ht2] at hmk hmap
  obtain ⟨-, -, -, -, hclen, hcc⟩ := ConLeche.mkCopy_inv hmk
  have hJmem : J ∈ ci.members := List.mem_of_find?_eq_some hJf
  -- the constructor at `jc`, on the container's side
  have hjlt : jc < t.ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  have hlen2 : cpy.ctors.length = t.ctors.length := by
    have := congrArg List.length hmap
    simpa using this
  have hjJ : jc < J.ctors.length := by omega
  obtain ⟨cc, hccj⟩ : ∃ cc, J.ctors[jc]? = some cc := ⟨_, List.getElem?_eq_getElem hjJ⟩
  obtain ⟨cI, -, hcpyj⟩ := hcc jc cc hccj
  have hpos : (Name.replacePrefix J.name t.name cc.name, cc.nFields) = (c.1, c.2.2) := by
    have h1 : (cpy.ctors.map (fun x => (x.1, x.2.2)))[jc]?
        = some (Name.replacePrefix J.name t.name cc.name, cc.nFields) := by
      rw [List.getElem?_map, hcpyj]; rfl
    have h2 : (t.ctors.map (fun x => (x.1, x.2.2)))[jc]? = some (c.1, c.2.2) := by
      rw [List.getElem?_map, hc]; rfl
    rw [hmap] at h1
    exact Option.some.inj (h1.symm.trans h2)
  simp only [Prod.mk.injEq] at hpos
  rw [hJn] at hci hJname
  refine ⟨q, qn, t, jc, c, ci, J, cc, hqn, ht, hc, htn, hn, hpin, hq, hci, hJmem, hJname,
    hccj, ?_, hpos.2⟩
  rw [hnn, ← hn, ← hpos.1, htn]
  exact (hnames q qn hqn ci J hci hJmem hJname cc (List.mem_of_getElem? hccj)).symm


end Run

end ConLeche.Model
