module

public import ConLeche.Model.Inductives.WhnfContentRun
public import ConLeche.Model.Inductives.GroupExclusionRun
public import ConLeche.Model.Inductives.CopyWalkFactsAssembly
import ConLeche.Verify.Inductives.NestedCopyStored
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedLeaves
import ConLeche.Verify.Inductives.NestedFields
import ConLeche.Verify.Inductives.NestedProj

public section

/-!
# The `whnf` arm's content AT THE RUN: the run-level reads (task #279
M-D′ D2, DESIGN §M.49)

`WhnfContentRun.lean` proves `WhnfContent`'s reading conjunct at ONE
field (`whnfContent_field`) from the container-side readings at the
formers' model `mp₁`, the restored field's reading and the field's
`WhnfField`.  This module collects what the RUN supplies for that
assembly at `env₁ = consNestedFormers (stored.take p.k) env` and
`R = restoreTbl p st`:

* **`nestedTbl_fresh_of_run`** — the scratch environment's projection
  tables beyond `env₁`'s are the auxiliary block's members', whose
  names are fresh before the block (the `.proj` side condition of the
  DOWNWARD reading transfer, `denoteMeta_down_blind`);
* **`containerLps_nodup_of_pin`** — K.21's record at a pinned
  container, which retired the model lane's `ContainerLpsNodup`;
* **`containerInfo?_self_mem`** and **`containerGroupOk_of_pins`** —
  a recovered group holds the name it was looked up at, hence
  `containerGroupOk` at every group the pins cover.  They live here
  because the group exclusion is read at BOTH assemblies;
  `CopyWalkFactsRunAssembly.lean` imports them.

The run-level assembly `whnfContent_of_run` itself is NOT here.  What
blocked it in §M.49 no longer does: the DOWNWARD reading transfer asked
`LitGuardsMono envAux env₁` — refutable for this pair, since a block
CONSTRUCTOR can complete the string support at the scratch environment
and not at the formers' — and task #310 made that a condition on the
SUBJECT instead (`litsResolve env₁`, beside the blind mentions).  The
assembly waits on the inputs §M.49 lists in order: the formers' model
at the run, the two transfers, `hreadP`/`hreadC`/`hrest` and the group
exclusion.
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


/-! ## The scratch environment's new projection slots (task #309) -/

omit [SetTheory V] in
/-- **The scratch environment's tables beyond the formers' environment's
are the auxiliary block's members'**, whose names are fresh before the
block (DESIGN §M.47 item 6): `checkMutualCore_findProj_fresh` decides it
at `env`, and the formers' conses only ADD lookups (K.20's freshness),
so a slot empty at `env₁` is empty at `env`. -/
theorem nestedTbl_fresh_of_run {μ : CheckMode} {F : Nat} {env envAux : Env}
    {b : MutualBlock} {p : ConLeche.NestedParts} {stored : List AuxStored}
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hK20 : (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone)
      = true) :
    ∀ (sn : Name) (i : Nat),
      (ConLeche.consNestedFormers (stored.take p.k) env).findProj? sn i = none →
      (envAux.findProj? sn i).isSome = true → env.find? sn = none := by
  have hx : ConLeche.Semantics.FreshEtaExt env
      (ConLeche.consNestedFormers (stored.take p.k) env) :=
    ConLeche.Semantics.consNestedFormers_freshExt hK20
  intro sn i h1 h2
  refine ConLeche.checkMutualCore_findProj_fresh hcore ?_ h2
  cases hf : env.findProj? sn i with
  | none => rfl
  | some entry =>
    obtain ⟨tbl, hf0, hi, rfl⟩ := ConLeche.Env.findProj?_some hf
    rw [ConLeche.Env.findProj?_of_table (hx.find?_some hf0) hi] at h1
    exact nomatch h1

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
