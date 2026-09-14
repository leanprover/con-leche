module

public import ConLeche.Model.Inductives.WhnfContentRun
public import ConLeche.Model.Inductives.GroupExclusionRun
public import ConLeche.Model.Inductives.CopyWalkFactsAssembly
import ConLeche.Verify.Inductives.NestedCopyStored
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedLeaves
import ConLeche.Verify.Inductives.NestedFields

public section

/-!
# The `whnf` arm's content AT THE RUN (task #279 M-D′ D2, DESIGN §M.49)

`WhnfContentRun.lean` proves `WhnfContent`'s reading conjunct at ONE
field (`whnfContent_field`) from the container-side readings at the
formers' model `mp₁`, the restored field's reading and the field's
`WhnfField`.  This module assembles it AT THE RUN: at
`env₁ = consNestedFormers (stored.take p.k) env` and
`R = restoreTbl p st` every input is a fact `DeclNestedRun` carries —
the formers' model itself (`nestedFormersModel`), the head former's
parameter openers' readings and the container's instantiated
constructor's, both transferred DOWN from the scratch environment
(`denoteMeta_down_blind`), the entries' grading, the restored field's
reading by the copy's own field kind (`restoreI_eq_self` at an
unfired field, `restoredField_read_copy` at a fired one) and the group
exclusion (K.23 through `groupExclusion_of_K23`).

Two environment-shape facts are the Verify tier's
(`Verify/Inductives/NestedProj.lean`): the scratch install's new
projection tables are the block's members' (fresh at `env`), and the
pins carry no projection node at a slot of a name fresh at `env`.

The two container lemmas below travel with this module because the
exclusion is read here; `CopyWalkFactsRunAssembly.lean` imports them.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType NestedPin ElimState ContainerCtor AuxStored)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A recovered group holds its own name -/

omit [SetTheory V] in
/-- **`containerInfo?` recovers a group holding the name it was looked
up at** (the `names.contains I` guard, through the members' `mapM`). -/
theorem containerInfo?_self_mem {env : Env} {I : Name} {ci : ContainerInfo}
    (h : ConLeche.containerInfo? env I = some ci) :
    ∃ (i : Nat) (J : ContainerMember), ci.members[i]? = some J ∧ J.name = I := by
  unfold ConLeche.containerInfo? at h
  split at h
  · exact nomatch h
  simp only [ConLeche.bindOption_eq_some_iff] at h
  obtain ⟨cT, hfT, h⟩ := h
  split at h
  · next cvT caps =>
    simp only [ConLeche.bindOption_eq_some_iff] at h
    obtain ⟨cR, hfR, h⟩ := h
    split at h
    · next cvR mI rP rules =>
      split at h
      · next hle =>
        simp only [ConLeche.bindOption_eq_some_iff] at h
        obtain ⟨nP, hnP, h⟩ := h
        obtain ⟨pp, hstrip, h⟩ := h
        obtain ⟨bsR, recBody⟩ := pp
        simp only at h
        split at h
        · next hnames =>
          simp only [ConLeche.bindOption_eq_some_iff] at h
          obtain ⟨members, hmapM, h⟩ := h
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true] at hnames
          have hIn : I ∈ ConLeche.containerMembersGo env nP (rP + 1) 0 recBody := by
            have := hnames.1
            simpa using this
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hIn
          obtain ⟨hlen, hall⟩ := optionMapM_getElem? hmapM
          obtain ⟨J, hJ, hf⟩ := hall i I hi
          refine ⟨i, J, hJ, ?_⟩
          simp only [ConLeche.bindOption_eq_some_iff] at hf
          obtain ⟨cC, hfC, hf⟩ := hf
          split at hf
          · next cvC capsC =>
            simp only [ConLeche.bindOption_eq_some_iff] at hf
            obtain ⟨cRc, hfRc, hf⟩ := hf
            split at hf
            · next cvRc mIc rPc rulesC =>
              split at hf
              · simp only [ConLeche.bindOption_eq_some_iff] at hf
                obtain ⟨ctors, hctors, hf⟩ := hf
                simp only [Option.some.injEq] at hf
                rw [← hf]
              · exact nomatch hf
            · exact nomatch hf
          · exact nomatch hf
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

omit [SetTheory V] in
/-- **A group the pins cover recovers itself at every member** (K.15's
`containerGroupOk`, at the run): the group's own name is a member
(`containerInfo?_self_mem`), the pins carry every member's group, and
`nestedContainersOk` checked the facts at every pin's container. -/
theorem containerGroupOk_of_pins {env : Env} {st : ElimState} {ci : ContainerInfo} {I : Name}
    {base : Nat} (hcont : ConLeche.nestedContainersOk env st.pins = true)
    (hci : ConLeche.containerInfo? env I = some ci)
    (hgrp : ∀ (i' : Nat) (J' : ContainerMember), ci.members[i']? = some J' →
      ∃ q', st.pins[base + i']? = some q' ∧ q'.container = J'.name) :
    ConLeche.containerGroupOk env ci = true := by
  obtain ⟨i, J, hJ, hn⟩ := containerInfo?_self_mem hci
  obtain ⟨q', hq', hq'c⟩ := hgrp i J hJ
  obtain ⟨-, hall⟩ := ConLeche.nestedContainersOk_inv' hcont
  obtain ⟨ci₀, hci₀, hok⟩ := hall q' (List.mem_of_getElem? hq')
  rw [hq'c, hn, hci] at hci₀
  obtain rfl := Option.some.inj hci₀
  exact hok


/-! ## K.21's record, read (task #279) -/

/-- `Name.nodup` decides `List.Nodup`. -/
theorem nodup_of_nameNodup : ∀ {l : List Name}, ConLeche.Name.nodup l = true → l.Nodup
  | [], _ => List.nodup_nil
  | n :: ns, h => by
    rw [ConLeche.Name.nodup, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    refine List.nodup_cons.mpr ⟨fun hn => ?_, nodup_of_nameNodup h.2⟩
    rw [← List.contains_iff_mem, h.1] at hn
    exact Bool.noConfusion hn

omit [SetTheory V] in
/-- **K.21's record at a pinned container** (task #279 K.21): the
install decided `Name.nodup J.lps` at every member of every pin's group
(`nestedContainersOk`'s `containerFactsOk`), the group recovered at a
pin's own container holds that container as a member
(`containerInfo?_self_mem`), and `containerInfo?` reads a member's
level parameters off the stored constant — so the stored container's
`levelParams` are distinct.  What the model lane carried as the named
`ContainerLpsNodup`. -/
theorem containerLps_nodup_of_pin {env : Env} {pins : List NestedPin} {q : NestedPin}
    {n : Name} {cv : ConstantVal} {caps : IndCaps}
    (hcont : ConLeche.nestedContainersOk env pins = true)
    (hq : q ∈ pins) (hqc : q.container = n)
    (hfind : env.find? n = some (.indInfo cv caps)) :
    cv.levelParams.Nodup := by
  unfold ConLeche.nestedContainersOk at hcont
  rw [Bool.and_eq_true, List.all_eq_true] at hcont
  have h := hcont.2 q hq
  cases hci : ConLeche.containerInfo? env q.container with
  | none => rw [hci] at h; exact nomatch h
  | some ci =>
    rw [hci] at h
    obtain ⟨iSelf, J, hJ, hJn⟩ := containerInfo?_self_mem hci
    unfold ConLeche.containerFactsOk at h
    rw [Bool.and_eq_true, List.all_eq_true] at h
    have hJa := h.2 J (List.mem_of_getElem? hJ)
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hJa
    obtain ⟨⟨cvC, capsC, hfC, -, hlpsC⟩, -⟩ :=
      ConLeche.containerInfo?_stored hci J (List.mem_of_getElem? hJ)
    rw [hJn, hqc, hfind] at hfC
    obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfC)
    rw [← hlpsC]
    exact nodup_of_nameNodup hJa.1.1.1

end ConLeche.Model
