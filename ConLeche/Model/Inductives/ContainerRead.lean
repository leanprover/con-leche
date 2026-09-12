module

public import ConLeche.Model.IndRep
import ConLeche.Verify.Inductives.ContainerWalk

public section

/-!
# The kernel's container reading is the datum's group (task #279 M-B′ step 3a)

The nested elimination reads a container `J`'s block off its stored
recursor with `containerInfo?` (`Kernel/Inductives/NestedParts.lean`):
the parameter count off a constructor record, the `all` group off the
motive binders of `J.rec`, each member's constructors off its
recursor's rules with their stored types and field counts.  The
representation clause (`IndRep`, `Model/IndRep.lean`) records the same
data semantically — and, since M-B′ step 3a, syntactically enough:
`RecReadAt`'s motive walk, the members' level parameters, the real
members' distinct names, the real/copy split of the constructors and
the real members' recursor names.  `IndRep.containerInfo?_eq` puts the
two together: **what the kernel reads for `J` is the datum's real
members in order, each with the datum's constructors of that member**,
so the copies the elimination mints (`mkCopy`, the ledger of
`Verify/Inductives/NestedLedger.lean`) are the datum's members
instantiated at the pins — the bridge the fold spellings of M-B′ step
3b stand on.

The premises are the ones under which the datum's readings are live:
a block with parameters (`nP ≠ 0`), a recursor with rules stored as
such, and a container that is not `Quot` (which `containerInfo?`
excludes by name).
-/

namespace ConLeche.Model

open ConLeche

variable {V : Type w} [SetTheory V]

omit [SetTheory V] in
/-- `mapM` over `Option` succeeds when every element does, pointwise. -/
theorem mapM_some_of {α β : Type _} {g : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, ∃ y, g x = some y) →
      ∃ l' : List β, l.mapM g = some l' ∧ l'.length = l.length ∧
        ∀ (i : Nat) (x : α), l[i]? = some x → ∃ y, l'[i]? = some y ∧ g x = some y
  | [], _ => ⟨[], rfl, rfl, fun i x h => by simp at h⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨l', hl', hlen, hall⟩ := mapM_some_of xs (fun z hz => h z (List.mem_cons_of_mem _ hz))
    refine ⟨y :: l', ?_, by simp [hlen], fun i z hz => ?_⟩
    · rw [List.mapM_cons, hy, hl']; rfl
    · cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hz
        subst hz
        exact ⟨y, rfl, hy⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hz ⊢
        exact hall i z hz

omit [SetTheory V] in
/-- `mapM` over `Option` at a pointwise-known function. -/
theorem mapM_eq_some_map {α β : Type _} {g : α → Option β} {g' : α → β} :
    ∀ (l : List α), (∀ x ∈ l, g x = some (g' x)) → l.mapM g = some (l.map g')
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, h x List.mem_cons_self,
      mapM_eq_some_map xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

/-- A member's constructor among `ctorsAll` sits in `ctorsA` (task #279
M-B′ step 3a: `memsReal`). -/
theorem IndRep.memberCtorsAll_mem_ctorsA {env : Env} {m : EnvModel V env} {T : Name}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {d : IndRepData V} {mm : Nat}
    (h : IndRep m T cvT cvR mI rP rules d mm) {t : Nat} (ht : t < d.kReal)
    {cA : ConstantVal × Nat} (hcA : cA ∈ d.memberCtorsAll t) :
    ∃ j, d.ctorsA[j]? = some cA ∧ d.mems j = t := by
  unfold IndRepData.memberCtorsAll at hcA
  obtain ⟨⟨cA', j⟩, hmem, rfl⟩ := List.mem_map.mp hcA
  obtain ⟨hz, hmemt⟩ := List.mem_filter.mp hmem
  have hj : d.ctorsAll[j]? = some cA' := List.mk_mem_zipIdx_iff_getElem?.mp hz
  have hmt : d.mems j = t := by simpa using hmemt
  have hjl : j < d.nAll := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simpa [IndRepData.ctorsAll, IndRepData.nAll] using this
  have hjA : j < d.ctorsA.length := (h.memsReal j hjl).mp (hmt ▸ ht)
  refine ⟨j, ?_, hmt⟩
  unfold IndRepData.ctorsAll at hj
  rwa [List.getElem?_append_left hjA] at hj

/-- **The kernel's container reading is the datum's group.**  At a
stored inductive `T` with parameters whose recursor carries rules,
`containerInfo? env T` succeeds with the datum's parameter count and
one member per REAL member of the datum, in order: the member's name,
the block's level parameters, its stored type, and its constructors of
the datum (`memberCtorsAll`) with their stored types and field
counts. -/
theorem IndRep.containerInfo?_eq {env : Env} {m : EnvModel V env} {T : Name}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {d : IndRepData V} {mm : Nat}
    (h : IndRep m T cvT cvR mI rP rules d mm) (hnP : d.nP ≠ 0) (hne : rules ≠ [])
    {caps : IndCaps} (hfT : env.find? T = some (.indInfo cvT caps))
    (hfR : env.find? cvR.name = some (.recInfo cvR mI rP rules)) (hQ : T ≠ quotName) :
    ∃ members : List ContainerMember,
      containerInfo? env T = some ⟨d.nP, members⟩ ∧ members.length = d.kReal ∧
      ∀ t, t < d.kReal → ∃ M : ContainerMember, members[t]? = some M ∧
        M.name = d.memberName t ∧ M.lps = cvT.levelParams ∧
        (∃ (cv : ConstantVal) (caps' : IndCaps),
          env.find? (d.memberName t) = some (.indInfo cv caps') ∧
          cv.levelParams = M.lps ∧ cv.type = M.type) ∧
        M.ctors = (d.memberCtorsAll t).map fun cA => ⟨cA.1.name, cA.1.type, cA.2⟩ := by
  have hRR := h.rulesRead hnP hne hfR
  have hmmk : mm < d.k := Nat.lt_of_lt_of_le h.memReal h.kRealLe
  -- the datum's recursor at `mm` is the stored one; its walk
  obtain ⟨cvR', mI', rP', rules', hf', -, -, -, -, -, -, bs, body, hs, hwalk⟩ := hRR mm hmmk
  rw [h.recName, hfR] at hf'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj hf')
  have hnames : containerMembersGo env d.nP (rP + 1) 0 body
      = (List.range d.kReal).map d.memberName :=
    hwalk env fun t ht => h.membersFound t (Nat.lt_of_lt_of_le ht h.kRealLe)
  -- the parameter count, off the first rule's constructor record
  obtain ⟨r, rs, rfl⟩ : ∃ r rs, rules = r :: rs := by
    cases rules with
    | nil => exact absurd rfl hne
    | cons r rs => exact ⟨r, rs, rfl⟩
  have hr : r.ctor ∈ (d.memberCtors mm).map (·.1.name) := by
    rw [← h.rules hne]
    exact List.mem_map_of_mem List.mem_cons_self
  obtain ⟨cA₀, hcA₀, hcAn₀⟩ := List.mem_map.mp hr
  obtain ⟨j₀, hj₀⟩ : ∃ j, d.ctorsA[j]? = some cA₀ := by
    unfold IndRepData.memberCtors at hcA₀
    obtain ⟨⟨cA', j⟩, hmem, rfl⟩ := List.mem_map.mp hcA₀
    exact ⟨j, List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hmem).1⟩
  obtain ⟨hfC₀, -, -⟩ := h.ctors j₀ cA₀ hj₀
  -- one member's reading
  have hmember : ∀ t, t < d.kReal →
      ∃ M : ContainerMember,
        (do
          let .indInfo cvC _ := (← env.find? (d.memberName t)) | none
          let .recInfo _ _ rPc rulesC := (← env.find? ((d.memberName t).str "rec")) | none
          if rPc == rP && cvC.levelParams == cvT.levelParams then
            let ctors ← rulesC.mapM fun r =>
              match env.find? r.ctor with
              | some (.ctorInfo cvc nPc nF) =>
                if nPc == d.nP then some ⟨r.ctor, cvc.type, nF⟩ else none
              | _ => none
            some ⟨d.memberName t, cvC.levelParams, cvC.type, ctors⟩
          else none : Option ContainerMember) = some M ∧
        M.name = d.memberName t ∧ M.lps = cvT.levelParams ∧
        (∃ (cv : ConstantVal) (caps' : IndCaps),
          env.find? (d.memberName t) = some (.indInfo cv caps') ∧
          cv.levelParams = M.lps ∧ cv.type = M.type) ∧
        M.ctors = (d.memberCtorsAll t).map fun cA => ⟨cA.1.name, cA.1.type, cA.2⟩ := by
    intro t ht
    have htk : t < d.k := Nat.lt_of_lt_of_le ht h.kRealLe
    obtain ⟨cvC, capsC, hfC⟩ := h.membersFound t htk
    have hlpsC : cvC.levelParams = cvT.levelParams := h.membersLps t htk cvC capsC hfC
    obtain ⟨cvRt, mIt, rPt, rulest, hft, -, -, hrPt, -, hmap, hrl, -⟩ := hRR t htk
    rw [h.recNamesReal t ht] at hft
    -- the constructors' records
    have hctors : rulest.mapM (fun r =>
        match env.find? r.ctor with
        | some (.ctorInfo cvc nPc nF) =>
          if nPc == d.nP then some ⟨r.ctor, cvc.type, nF⟩ else none
        | _ => none)
        = some ((d.memberCtorsAll t).map fun cA => (⟨cA.1.name, cA.1.type, cA.2⟩ : ContainerCtor)) := by
      have hstored : ∀ cA ∈ d.memberCtorsAll t,
          env.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2) := by
        intro cA hcA
        obtain ⟨j, hj, -⟩ := h.memberCtorsAll_mem_ctorsA ht hcA
        exact (h.ctors j cA hj).1
      rw [mapM_eq_some_map rulest (g' := fun r =>
        match env.find? r.ctor with
        | some (.ctorInfo cvc _ nF) => (⟨r.ctor, cvc.type, nF⟩ : ContainerCtor)
        | _ => default)]
      · congr 1
        have h1 : rulest.map (fun r =>
            match env.find? r.ctor with
            | some (.ctorInfo cvc _ nF) => (⟨r.ctor, cvc.type, nF⟩ : ContainerCtor)
            | _ => default) = (rulest.map (·.ctor)).map (fun C =>
            match env.find? C with
            | some (.ctorInfo cvc _ nF) => (⟨C, cvc.type, nF⟩ : ContainerCtor)
            | _ => default) := by
          rw [List.map_map]; rfl
        rw [h1, hmap, List.map_map]
        refine List.map_congr_left fun cA hcA => ?_
        show (match env.find? cA.1.name with
          | some (.ctorInfo cvc _ nF) => (⟨cA.1.name, cvc.type, nF⟩ : ContainerCtor)
          | _ => default) = _
        rw [hstored cA hcA]
      · intro r' hr'
        have hn : r'.ctor ∈ (d.memberCtorsAll t).map (·.1.name) := by
          rw [← hmap]; exact List.mem_map_of_mem hr'
        obtain ⟨cA, hcA, hcAn⟩ := List.mem_map.mp hn
        show (match env.find? r'.ctor with
          | some (.ctorInfo cvc nPc nF) =>
            if nPc == d.nP then some (⟨r'.ctor, cvc.type, nF⟩ : ContainerCtor) else none
          | _ => none) = some (match env.find? r'.ctor with
          | some (.ctorInfo cvc _ nF) => (⟨r'.ctor, cvc.type, nF⟩ : ContainerCtor)
          | _ => default)
        rw [← hcAn, hstored cA hcA]
        simp
    refine ⟨⟨d.memberName t, cvC.levelParams, cvC.type,
      (d.memberCtorsAll t).map fun cA => ⟨cA.1.name, cA.1.type, cA.2⟩⟩, ?_, rfl, hlpsC,
      ⟨cvC, capsC, hfC, rfl, rfl⟩, rfl⟩
    simp only [hfC, hft, bind, Option.bind, hrPt, h.rP, hlpsC, beq_self_eq_true, Bool.and_self,
      ↓reduceIte, hctors]
  -- the whole reading
  obtain ⟨members, hmapM, hlen, hall⟩ :=
    mapM_some_of (g := fun C => (do
      let .indInfo cvC _ := (← env.find? C) | none
      let .recInfo _ _ rPc rulesC := (← env.find? (C.str "rec")) | none
      if rPc == rP && cvC.levelParams == cvT.levelParams then
        let ctors ← rulesC.mapM fun r =>
          match env.find? r.ctor with
          | some (.ctorInfo cvc nPc nF) =>
            if nPc == d.nP then some ⟨r.ctor, cvc.type, nF⟩ else none
          | _ => none
        some ⟨C, cvC.levelParams, cvC.type, ctors⟩
      else none : Option ContainerMember))
      ((List.range d.kReal).map d.memberName) (fun C hC => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hC
        obtain ⟨M, hM, -⟩ := hmember t (List.mem_range.mp ht)
        exact ⟨M, hM⟩)
  refine ⟨members, ?_, by rw [hlen, List.length_map, List.length_range], fun t ht => ?_⟩
  · -- the computation
    have hRn : cvR.name = T.str "rec" := by
      rw [← h.recName, h.recNamesReal mm h.memReal, h.member]
    rw [hRn] at hfR
    rw [hcAn₀] at hfC₀
    have hcontains : ((List.range d.kReal).map d.memberName).contains T = true := by
      rw [List.contains_iff_mem, ← h.member]
      exact List.mem_map_of_mem (List.mem_range.mpr h.memReal)
    have hrPmI : rP ≤ mI := by rw [h.rP, h.mI]; omega
    simp only [bind] at hmapM
    unfold containerInfo?
    rw [beq_eq_false_iff_ne.mpr hQ]
    simp only [Bool.false_eq_true, ↓reduceIte, hfT, hfR, bind, Option.bind_some, hrPmI,
      List.head?_cons, hfC₀, hs, hnames, hcontains, Bool.true_and,
      decide_eq_true h.memberNodup]
    exact congrArg (fun o : Option (List ContainerMember) =>
      o.bind fun members => some (⟨d.nP, members⟩ : ContainerInfo)) hmapM
  · obtain ⟨M, hM, hname, hlps, hcv, hctors⟩ := hmember t ht
    obtain ⟨M', hM', hg⟩ := hall t (d.memberName t) (by
      rw [List.getElem?_map, List.getElem?_range ht]; rfl)
    refine ⟨M', hM', ?_⟩
    obtain rfl : M = M' := Option.some.inj (hM.symm.trans hg)
    exact ⟨hname, hlps, hcv, hctors⟩

/-- **The consumer's form**: whatever `containerInfo?` returned for a
stored inductive `T` with a live datum IS the datum's group (the
`Quot` exclusion is discharged by the success itself). -/
theorem IndRep.containerInfo?_inv {env : Env} {m : EnvModel V env} {T : Name}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {d : IndRepData V} {mm : Nat}
    (h : IndRep m T cvT cvR mI rP rules d mm) (hnP : d.nP ≠ 0) (hne : rules ≠ [])
    {caps : IndCaps} (hfT : env.find? T = some (.indInfo cvT caps))
    (hfR : env.find? cvR.name = some (.recInfo cvR mI rP rules))
    {ci : ContainerInfo} (hci : containerInfo? env T = some ci) :
    ci.nP = d.nP ∧ ci.members.length = d.kReal ∧
      ∀ t, t < d.kReal → ∃ M : ContainerMember, ci.members[t]? = some M ∧
        M.name = d.memberName t ∧ M.lps = cvT.levelParams ∧
        (∃ (cv : ConstantVal) (caps' : IndCaps),
          env.find? (d.memberName t) = some (.indInfo cv caps') ∧
          cv.levelParams = M.lps ∧ cv.type = M.type) ∧
        M.ctors = (d.memberCtorsAll t).map fun cA => ⟨cA.1.name, cA.1.type, cA.2⟩ := by
  have hQ : T ≠ quotName := by
    intro hTq
    unfold containerInfo? at hci
    rw [if_pos (beq_iff_eq.mpr hTq)] at hci
    exact nomatch hci
  obtain ⟨members, hmem, hlen, hall⟩ := h.containerInfo?_eq hnP hne hfT hfR hQ
  rw [hmem] at hci
  obtain rfl := Option.some.inj hci
  exact ⟨rfl, hlen, hall⟩

end ConLeche.Model
