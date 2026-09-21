module

public import ConLeche.Verify.Inductives.NestedGroupInv
public import ConLeche.Verify.Inductives.NestedCopyKinds

public section

/-!
# A ROOT group's `ordF`-right targets leave the instance (task #315 WIDE, lane DOM)

The WIDE route's per-instance step spends the copies' entries through
`CopyEntryOut.ord` alone, and `nestedPinsEntryOrd_of`
(`Model/Inductives/NestedEntryOrd.lean`) discharges those from the rank
induction's own hypothesis PROVIDED the target of an `ordF`-right field
is in the induction's scope `S` — which asks, among other things, that
the target lie in ANOTHER instance than the source.

**At an arbitrary mint group that is FALSE** (DESIGN's WIDE (f3) row:
`tests/e2e/nested_p04.ndjson` accepts a block with two not-own edges
whose endpoints carry equal instance labels).  **At the instance's ROOT
group it is this theorem**, and its four links are:

* (i) **K.66** (`nestedOrdOutsideOk_at`'s second conjunct) — the target
  is outside the source's MINT GROUP;
* (ii) **K.75 clause (2)** — the target is outside the instance-map
  image of EVERY member of the source's mint group.  K.62
  (`nestedOrdOutsideOk_at`'s first conjunct) says this at the source
  pin alone, which is not enough: the contradiction below is closed
  against an arbitrary member of the root group, which clause (1)
  hands over and about which K.62-at-the-pin says nothing;
* (iii) **the roots table is a function of the instance**
  (`nestedPinRootGroup_congr`);
* (iv) **K.75 clause (1)** — every pin of an instance is a member of
  its root group or lies in the instance-map image of one of that
  group's members.

Clauses (1) and (2) are carried as HYPOTHESES here, in the run's
vocabulary: the Bools that record them are not on this branch (their
text is in DESIGN's WIDE (f4) row, measured at zero fires on the shadow
suite, `init-full` and Mathlib in both modes).
-/

namespace ConLeche

/-- The members of ONE mint group share their group's size: K.29 reads
both groups' entry at their common base pin. -/
theorem nestedGroups_grpSize_eq {env : Env} {p : NestedParts} {st : ElimState}
    (h : nestedGroupsOk env p st = true) {q r : Nat}
    (hq : q < st.pins.length) (hr : r < st.pins.length)
    (hbase : (st.pins.getD q default).grpBase = (st.pins.getD r default).grpBase) :
    (st.pins.getD q default).grpSize = (st.pins.getD r default).grpSize := by
  have hgq : st.pins[q]? = some (st.pins.getD q default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; rfl
  have hgr : st.pins[r]? = some (st.pins.getD r default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]; rfl
  obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi, _, _, _, hmemq⟩ :=
    nestedGroupsOk_inv h q (st.pins.getD q default) hgq
  obtain ⟨_, _, _, _, _, _, _, _, hlo', hhi', _, _, _, hmemr⟩ :=
    nestedGroupsOk_inv h r (st.pins.getD r default) hgr
  obtain ⟨qi, _, _, hqi, _, _, _, _, hqsz, _⟩ := hmemq 0 (by omega)
  obtain ⟨ri, _, _, hri, _, _, _, _, hrsz, _⟩ := hmemr 0 (by omega)
  rw [Nat.add_zero, hbase] at hqi
  rw [Nat.add_zero] at hri
  rw [hqi] at hri
  obtain rfl : qi = ri := Option.some.inj hri
  omega

/-- **AT A PIN OF THE INSTANCE'S ROOT GROUP, AN `ordF`-RIGHT TARGET IS
IN ANOTHER INSTANCE** (task #315 WIDE, lane DOM).

`s` is a pin whose own mint group IS its instance's root group
(`hrootGrp`), and `(s, t, false)` is one of `nestedPinEdges`' rows — a
field the container calls ORDINARY and the block's rewrite made
recursive.  Then `t`'s instance label differs from `s`'s, which is the
rank induction's scope.

The proof is the contradiction: were the labels equal, `t`'s root group
would be `s`'s (iii), so clause (1) would put `t` in the root group
itself — refuted by (i) and K.29's contiguity — or in the instance-map
image of one of the root group's members — refuted by (ii). -/
theorem nestedPinOutLabel {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored} {s t : Nat}
    (hK29 : nestedGroupsOk env p st = true)
    (hK62 : nestedOrdOutsideOk env p b st stored = true)
    (hK75pool : ∀ q, q < st.pins.length → ∀ g,
      (nestedPinRootGroup env p b st stored).getD q none = some g →
      (st.pins.getD q default).grpBase = g ∨
        ∃ i, i < st.pins.length ∧ (st.pins.getD i default).grpBase = g ∧
          ∃ mi, nestedInstMapAt env st i = some mi ∧ mi.contains q = true)
    (hK75grp : ∀ d, d < (st.pins.getD s default).grpSize →
      ∀ mi, nestedInstMapAt env st ((st.pins.getD s default).grpBase + d) = some mi →
        mi.contains t = false)
    {edges : List (Nat × Nat × Bool)}
    (hedges : nestedPinEdges env p b st stored = some edges)
    (hs : s < st.pins.length) (ht : t < st.pins.length)
    (hmem : (s, t, false) ∈ edges)
    (hrootGrp : (nestedPinRootGroup env p b st stored).getD s none
      = some (st.pins.getD s default).grpBase) :
    (nestedPinInstOf env p b st stored).getD t 0
      ≠ (nestedPinInstOf env p b st stored).getD s 0 := by
  intro hlab
  have hgs : st.pins[s]? = some (st.pins.getD s default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; rfl
  have hgt : st.pins[t]? = some (st.pins.getD t default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl
  -- (i)+(K.62): the target is outside the source's own map and outside its mint group
  obtain ⟨_, _, _, hout⟩ := nestedOrdOutsideOk_at hK62 hedges hs hgs hmem rfl
  -- (iii): the roots table is a function of the instance
  have hrt : (nestedPinRootGroup env p b st stored).getD t none
      = some (st.pins.getD s default).grpBase := by
    rw [nestedPinRootGroup_congr ht hs hlab]; exact hrootGrp
  -- K.29 at `t`: the pin lies in its own group
  obtain ⟨_, _, _, _, _, _, _, _, htlo, hthi, _, _, _, _⟩ :=
    nestedGroupsOk_inv hK29 t (st.pins.getD t default) hgt
  rcases hK75pool t ht _ hrt with hA | ⟨i, hi, hib, mi, hmi, hcon⟩
  · -- (iv) arm 1: `t` would be a member of the root group itself
    have hsz := nestedGroups_grpSize_eq hK29 ht hs hA
    omega
  · -- (iv) arm 2: `t` would lie in a root-group member's instance-map image
    obtain ⟨_, _, _, _, _, _, _, _, hilo, hihi, _, _, _, _⟩ :=
      nestedGroupsOk_inv hK29 i (st.pins.getD i default)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    have hsz := nestedGroups_grpSize_eq hK29 hi hs hib
    have hid : i = (st.pins.getD s default).grpBase + (i - (st.pins.getD s default).grpBase) := by
      omega
    have := hK75grp (i - (st.pins.getD s default).grpBase) (by omega) mi (by rw [← hid]; exact hmi)
    rw [this] at hcon
    exact Bool.noConfusion hcon

end ConLeche
