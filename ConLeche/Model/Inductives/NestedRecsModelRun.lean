module

public import ConLeche.Model.Inductives.NestedCtorsModelRun
public import ConLeche.Model.Inductives.NestedRecStage
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedFacts
import ConLeche.Verify.Inductives.NestedMention
import ConLeche.Verify.Inductives.NestedRecsWF
import ConLeche.Verify.Inductives.NestedRecNames
import ConLeche.Verify.Inductives.NestedCtorNames

public section

/-!
# The restored recursors' model at the run (task #279 M-D′ D4, DESIGN §M.57)

The nested install's third stage stores the block's `p.k + n` restored
recursors — the real members' `T_t.rec` and the mimics' `T₀.rec_j` —
in the mutual route's two moves: the rule-less provision
`envR = provisionNestedRecs provs env₂`, at which every restored rule is
scoped, and the store `env₃ = storeNestedRecs stores env₂` of the same
names with their rules.  `NestedRecStage.lean` is the model of that
chain, generic in the leaves; this module is its instantiation AT THE
RUN, consumer-first:

* **`nestedProvs`/`nestedStores`** — the two lists as `checkNested`
  zips them, so that the run's environments are literally
  `provisionNestedRecs (nestedProvs …) env₂` and
  `storeNestedRecs (nestedStores …) env₂`;
* **`nestedProvs_entry`** — every provisioned recursor's front door at
  `env₂` (`restoreRecTys` runs `checkConstantValPre` there, K.19: fresh,
  unreserved, not projection-shaped, the type scoped and resolving, its
  sort inferred) together with its NAME (the member's `<T_t>.rec` or
  the mimic's `p.mimicRecName j`) and its auxiliary record
  (`restoreRecTys_id`: the level parameters the auxiliary recursor's,
  the type its restore, `mI`/`rP` the record's);
* **`nestedProvs_names`** — the names, as a list: the members' under
  `.rec`, then the mimics'; distinct by the block's own name discipline
  for the members and by `Nat.repr` for the mimics
  (`NestedRecNames.lean`);
* **`restoredRecTy_reads`** — a restored recursor type READS at the
  constructors' model `mp₂`, graded — the front door's inference through
  the claims (`acceptedReads_of`, `ClaimsAt.sortRow`), exactly as D3
  got its `hokTy` for free; the SHAPE of the reading (the auxiliary
  tower with the copies' families restored) is D4's next step;
* **`storeNestedRecs_envExt`** — the store is an extension of the
  constructors' environment (`IndReps.ext`'s premise).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  AuxStored NestedParts ElimState AuxType)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The provision and the store, as the install zips them -/

/-- **The rule-less provision's entries**: the members' restored
recursors with the auxiliary records' `mI`/`rP`, then the mimics'
(`checkNested`'s `provisions`). -/
@[expose] def nestedProvs (cvRms cvRns : List ConstantVal) (stored : List AuxStored) (k : Nat) :
    List (ConstantVal × Nat × Nat) :=
  (cvRms.zip ((stored.take k).map fun (a : AuxStored) => (a.mI, a.rP)))
    ++ (cvRns.zip ((stored.drop k).map fun (a : AuxStored) => (a.mI, a.rP)))

/-- **The store's entries**: the provision's, with the restored rules. -/
@[expose] def nestedStores (cvRms cvRns : List ConstantVal) (stored : List AuxStored)
    (rulesM rulesN : List (List RecRule)) (k : Nat) :
    List (ConstantVal × Nat × Nat × List RecRule) :=
  (cvRms.zip ((stored.take k).zip rulesM)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
    ++ (cvRns.zip ((stored.drop k).zip rulesN)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))

/-! ## One restored recursor, off its front door -/

/-- **One restored recursor's record**, positionally: the entry of the
restore run at position `i` is named as the caller listed there, carries
the auxiliary recursor's level parameters and the restore of its type,
and went through the pre-annotated front door at `env` — as itself. -/
theorem restoreRecTys_entry {μ : CheckMode} {F : Nat} {env : Env} {R : ConLeche.RestoreTbl}
    {lps : List Name} {names : List Name} {l : List AuxStored} {cvs : List ConstantVal}
    (h : ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env R lps names l
      = .ok cvs)
    {i : Nat} {a : AuxStored} (ha : l[i]? = some a) {nm : Name} (hnm : names[i]? = some nm) :
    ∃ cvA : ConstantVal, cvs[i]? = some cvA ∧ cvA.name = nm ∧
      cvA.levelParams = a.cvRa.levelParams ∧
      ConLeche.restoreNested R a.cvRa.type = .ok cvA.type ∧
      ConLeche.checkConstantValPre (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env cvA
        = .ok cvA := by
  obtain ⟨-, hall⟩ := ConLeche.restoreRecTys_inv h
  obtain ⟨ty, cvA, hty, hpre, hget⟩ := hall i a ha
  have hid := ConLeche.checkConstantValPre_ok hpre
  have hhead : (names.drop i).headD a.cvRa.name = nm := by
    rw [List.headD_eq_head?_getD, List.head?_drop, hnm]; rfl
  rw [hhead] at hpre hid
  subst hid
  exact ⟨_, hget, rfl, rfl, hty, hpre⟩

/-! ## The provision's entries at the run -/

/-- **The name of the real member `t`** of the elimination's block is
the declared former's (`nestedRecNameFacts`' reading, factored out). -/
theorem nestedMemberName_eq {F : Nat} {env : Env} {p : NestedParts} {st : ElimState}
    {fmsA ctorsA : List ConstantVal}
    (hannF : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p.nP
      p.formers = .ok fmsA)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st)
    {t : Nat} (ht : t < p.k) {ty : AuxType} (hty : st.types[t]? = some ty) :
    ty.name = (p.formers.getD t default).1.name := by
  have hfmsLen : fmsA.length = p.k := (ConLeche.nestedAnnotFormers_inv hannF).1
  have h1 := ConLeche.elimNested_name_lt helim (t := t)
    (by rw [ConLeche.nestedTypes0_length, hfmsLen]; exact ht)
  rw [hty, ConLeche.nestedTypes0_getElem?] at h1
  obtain ⟨cvTa, hcvTa⟩ : ∃ cvTa, fmsA[t]? = some cvTa :=
    ⟨_, List.getElem?_eq_getElem (by rw [hfmsLen]; exact ht)⟩
  rw [hcvTa] at h1
  simp only [Option.map_some, Option.some.injEq] at h1
  obtain ⟨cv, nIdx, hl, hff⟩ := (ConLeche.nestedAnnotFormers_inv hannF).2 t cvTa hcvTa
  rw [h1, hff.name, List.getD_eq_getElem?_getD, hl]
  rfl

/-- **The real members' declared names are distinct**: they are the
first `p.k` of the auxiliary block's member names, and the block's names
are (`checkMutualCore`'s first conjunct). -/
theorem nestedMemberNames_nodup {F : Nat} {env envAux : Env} {p : NestedParts} {st : ElimState}
    {b : MutualBlock} {fmsA ctorsA : List ConstantVal}
    (hannF : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p.nP
      p.formers = .ok fmsA)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st)
    (hb : ConLeche.auxBlock p st = some b) (hlenSt : st.types.length = p.k + st.pins.length)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux) :
    ((List.range p.k).map fun t => (p.formers.getD t default).1.name).Nodup := by
  have hNd := ConLeche.nestedBlockNames_nodup hcore
  unfold ConLeche.MutualBlock.blockNames at hNd
  have hNdM : b.memberNames.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp hNd).1).1
  have hkb : b.k = st.types.length := ConLeche.auxBlock_k hb
  have hlenM : b.memberNames.length = b.k := by
    simp [ConLeche.MutualBlock.memberNames, ConLeche.MutualBlock.k]
  have heq : b.memberNames.take p.k = (List.range p.k).map fun t => (p.formers.getD t default).1.name := by
    refine List.ext_getElem? fun t => ?_
    rw [List.getElem?_map]
    by_cases ht : t < p.k
    · rw [List.getElem?_take_of_lt ht, List.getElem?_range ht]
      obtain ⟨ty, hty⟩ : ∃ ty, st.types[t]? = some ty :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨nIdx, hform, -⟩ := (ConLeche.auxBlock_former hb).2 t ty hty
      unfold ConLeche.MutualBlock.memberNames
      rw [List.getElem?_map, hform, Option.map_some, Option.map_some,
        nestedMemberName_eq hannF helim ht hty]
    · rw [List.getElem?_eq_none_iff.mpr (by rw [List.length_take]; omega),
        List.getElem?_eq_none_iff.mpr (by rw [List.length_range]; omega)]
      rfl
  rw [← heq]
  exact hNdM.sublist (List.take_sublist _ _)

/-- **Every provisioned recursor's front door and record**: the entry
at position `i` went through `checkConstantValPre` at `env₂` as itself,
is named the member's `<T_i>.rec` (`i < p.k`) or the mimic's
`p.mimicRecName (i - p.k)`, and carries the auxiliary record's level
parameters, `mI`, `rP` and the restore of its type. -/
theorem nestedProvs_entry {μ : CheckMode} {F : Nat} {env₂ : Env} {p : NestedParts} {st : ElimState}
    {stored : List AuxStored} {cvRms cvRns : List ConstantVal}
    (hrm : ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env₂
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
        (stored.take p.k) = .ok cvRms)
    (hrn : ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env₂
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.numNested).map p.mimicRecName) (stored.drop p.k) = .ok cvRns)
    (hlenT : (stored.take p.k).length = p.k) (hlenD : (stored.drop p.k).length = p.numNested) :
    cvRms.length = p.k ∧ cvRns.length = p.numNested ∧
    ∀ (i : Nat) (x : ConstantVal × Nat × Nat), (nestedProvs cvRms cvRns stored p.k)[i]? = some x →
      ConLeche.checkConstantValPre (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env₂ x.1
        = .ok x.1 ∧
      ∃ a : AuxStored,
        (i < p.k → x.1.name = (p.formers.getD i default).1.name.str "rec" ∧
          (stored.take p.k)[i]? = some a) ∧
        (p.k ≤ i → x.1.name = p.mimicRecName (i - p.k) ∧ (stored.drop p.k)[i - p.k]? = some a) ∧
        x.1.levelParams = a.cvRa.levelParams ∧
        ConLeche.restoreNested (ConLeche.restoreTbl p st) a.cvRa.type = .ok x.1.type ∧
        x.2.1 = a.mI ∧ x.2.2 = a.rP := by
  have hlenM : cvRms.length = p.k := by rw [(ConLeche.restoreRecTys_inv hrm).1, hlenT]
  have hlenN : cvRns.length = p.numNested := by rw [(ConLeche.restoreRecTys_inv hrn).1, hlenD]
  refine ⟨hlenM, hlenN, ?_⟩
  intro i x hx
  have hzipM : (cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP))).length = p.k := by
    rw [List.length_zip, List.length_map, hlenM, hlenT, Nat.min_self]
  unfold nestedProvs at hx
  by_cases hi : i < p.k
  · rw [List.getElem?_append_left (by rw [hzipM]; exact hi)] at hx
    obtain ⟨hget, hmap⟩ := List.getElem?_zip_eq_some.mp hx
    rw [List.getElem?_map] at hmap
    obtain ⟨a, ha, hax⟩ := Option.map_eq_some_iff.mp hmap
    obtain ⟨cvA, hcvA, hname, hlps, hty, hpre⟩ := restoreRecTys_entry hrm ha
      (nm := (p.formers.getD i default).1.name.str "rec")
      (by rw [List.getElem?_map, List.getElem?_range hi]; rfl)
    obtain rfl : x.1 = cvA := Option.some.inj (hget.symm.trans hcvA)
    refine ⟨hpre, a, fun _ => ⟨hname, ha⟩, fun h => absurd hi (Nat.not_lt.mpr h), hlps, hty, ?_, ?_⟩
    · rw [← hax]
    · rw [← hax]
  · have hi' : p.k ≤ i := Nat.not_lt.mp hi
    rw [List.getElem?_append_right (by rw [hzipM]; exact hi'), hzipM] at hx
    obtain ⟨hget, hmap⟩ := List.getElem?_zip_eq_some.mp hx
    rw [List.getElem?_map] at hmap
    obtain ⟨a, ha, hax⟩ := Option.map_eq_some_iff.mp hmap
    have hin : i - p.k < p.numNested := by
      have := (List.getElem?_eq_some_iff.mp hget).1
      omega
    obtain ⟨cvA, hcvA, hname, hlps, hty, hpre⟩ := restoreRecTys_entry hrn ha
      (nm := p.mimicRecName (i - p.k))
      (by rw [List.getElem?_map, List.getElem?_range hin]; rfl)
    obtain rfl : x.1 = cvA := Option.some.inj (hget.symm.trans hcvA)
    refine ⟨hpre, a, fun h => absurd h hi, fun _ => ⟨hname, ha⟩, hlps, hty, ?_, ?_⟩
    · rw [← hax]
    · rw [← hax]

/-- **The provision's names, as a list**: the members' under `.rec`,
then the mimics'. -/
theorem nestedProvs_names {μ : CheckMode} {F : Nat} {env₂ : Env} {p : NestedParts} {st : ElimState}
    {stored : List AuxStored} {cvRms cvRns : List ConstantVal}
    (hrm : ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env₂
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
        (stored.take p.k) = .ok cvRms)
    (hrn : ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env₂
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.numNested).map p.mimicRecName) (stored.drop p.k) = .ok cvRns)
    (hlenT : (stored.take p.k).length = p.k) (hlenD : (stored.drop p.k).length = p.numNested) :
    (nestedProvs cvRms cvRns stored p.k).map (·.1.name)
      = ((List.range p.k).map fun t => (p.formers.getD t default).1.name).map (fun T => T.str "rec")
        ++ (List.range p.numNested).map p.mimicRecName := by
  obtain ⟨hlenM, hlenN, hentry⟩ := nestedProvs_entry hrm hrn hlenT hlenD
  have hlenP : (nestedProvs cvRms cvRns stored p.k).length = p.k + p.numNested := by
    unfold nestedProvs
    rw [List.length_append, List.length_zip, List.length_zip, List.length_map, List.length_map,
      hlenM, hlenN, hlenT, hlenD, Nat.min_self, Nat.min_self]
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_map]
  by_cases hi : i < p.k + p.numNested
  · obtain ⟨x, hx⟩ : ∃ x, (nestedProvs cvRms cvRns stored p.k)[i]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, a, hlt, hge, -⟩ := hentry i x hx
    rw [hx, Option.map_some]
    by_cases hik : i < p.k
    · rw [List.getElem?_append_left (by simp; exact hik), List.getElem?_map, List.getElem?_map,
        List.getElem?_range hik, (hlt hik).1]
      rfl
    · have hik' : p.k ≤ i := Nat.not_lt.mp hik
      rw [List.getElem?_append_right (by simp; exact hik'), List.getElem?_map,
        List.getElem?_range (by simp; omega), (hge hik').1]
      simp
  · rw [List.getElem?_eq_none_iff.mpr (by omega), List.getElem?_eq_none_iff.mpr (by simp; omega)]
    rfl

/-! ## The store is an extension -/

/-- **The recursors' store extends the constructors' environment** (the
Model tier's `EnvExt`): fresh, distinct, non-table conses. -/
theorem storeNestedRecs_envExt :
    ∀ {rs : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env},
      (∀ r ∈ rs, env.find? r.1.name = none) → (rs.map (·.1.name)).Nodup →
      EnvExt env (ConLeche.storeNestedRecs rs env)
  | [], env, _, _ => EnvExt.refl env
  | r :: rs, env, hfresh, hnd => by
    obtain ⟨cvRa, mI, rP, rules⟩ := r
    simp only [ConLeche.storeNestedRecs]
    have hnd' : cvRa.name ∉ rs.map (·.1.name) ∧ (rs.map (·.1.name)).Nodup := by
      simpa using List.nodup_cons.mp hnd
    refine (EnvExt.cons (c₀ := .recInfo cvRa mI rP rules) (hfresh _ List.mem_cons_self)
      (fun _ h => nomatch h)).trans (storeNestedRecs_envExt ?_ hnd'.2)
    intro r' hr'
    rw [ConLeche.Env.find?_cons, if_neg ?_]
    · exact hfresh r' (List.mem_cons_of_mem _ hr')
    · intro heq
      refine hnd'.1 ?_
      rw [show cvRa.name = r'.1.name from heq]
      exact List.mem_map_of_mem hr'

/-! ## The restored recursor types read, graded -/

/-- **A restored recursor type reads at the model of the environment
its front door ran at, graded**: the front door's inference
(`checkConstantValPre_front`) through the claims (`acceptedReads_of`,
`ClaimsAt.sortRow`).  The reading's SHAPE is D4's next step. -/
theorem restoredRecTy_reads {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat} {env₂ : Env}
    (mp₂ : EnvModelM V μ env₂) {cvR : ConstantVal}
    (hpre : ConLeche.checkConstantValPre (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env₂ cvR
      = .ok cvR) :
    ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mp₂.base2.acval env₂ ψ 0 cvR.type = some ta ∧ ∀ ρ : Nat → V, WellDenotedV V ρ ta := by
  intro ψ
  obtain ⟨-, -, -, -, hbt, hnf, -, -, -, ⟨stype, u, hst, hens⟩, -⟩ :=
    ConLeche.checkConstantValPre_front hpre
  have hw : Expr.WScoped 0 cvR.type := Expr.WScoped.of_not_hasFvar hnf
  have hL : Expr.LeavesBounded cvR.type := Expr.LeavesBounded.of_not_hasFvar hnf
  have hnil : cvR.type.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf
  obtain ⟨ta, hta⟩ := acceptedReads_of mp₂.base2 ψ hst hw hbt hL
  have hc := claimsAt_of hμ mp₂ ψ F
  exact ⟨ta, hta, fun ρ => (hc.sortRow hst hens hw hbt hL (CtxOk.nil hnil) hta ρ (Sat_nil V ρ)).1⟩

/-! ## The store's entries, by membership -/

omit [SetTheory V] in
/-- A store entry is a member's or a mimic's, positionally. -/
theorem nestedStores_mem {cvRms cvRns : List ConstantVal} {stored : List AuxStored}
    {rulesM rulesN : List (List RecRule)} {k : Nat} {r : ConstantVal × Nat × Nat × List RecRule}
    (hr : r ∈ nestedStores cvRms cvRns stored rulesM rulesN k) :
    (∃ (i : Nat) (cv : ConstantVal) (a : AuxStored) (rs : List RecRule),
      (cvRms.zip ((stored.take k).zip rulesM))[i]? = some (cv, a, rs) ∧ r = (cv, a.mI, a.rP, rs)) ∨
    (∃ (i : Nat) (cv : ConstantVal) (a : AuxStored) (rs : List RecRule),
      (cvRns.zip ((stored.drop k).zip rulesN))[i]? = some (cv, a, rs) ∧ r = (cv, a.mI, a.rP, rs)) := by
  unfold nestedStores at hr
  rcases List.mem_append.mp hr with h | h
  · obtain ⟨⟨cv, a, rs⟩, hmem, rfl⟩ := List.mem_map.mp h
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
    exact Or.inl ⟨i, cv, a, rs, hi, rfl⟩
  · obtain ⟨⟨cv, a, rs⟩, hmem, rfl⟩ := List.mem_map.mp h
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
    exact Or.inr ⟨i, cv, a, rs, hi, rfl⟩

/-! ## D4's clause at a model of the constructors' environment -/

/-- **The model of `env₃` off a model of `env₂`, under D4's remaining
premises** (DESIGN §M.57).  The first conjunct is PROVED at the run
(`restoredRecTy_reads`): every restored recursor type reads at `mp₂`,
graded.  The second is the consumer of the premises still NAMED, each
stated at the run's own environments:

* `hleaves` — the leaves' content: for the leaves `Aof` (to be spelt
  from the auxiliary recursors' leaves conjugated by ψ/ψ⁻¹) and the
  readings `taOf`, `NestedCtorLeaf mp₂` at every provisioned recursor
  (D4's next step; `okTy` is free by the first conjunct);
* `hctorStored` — every stored rule's constructor is stored at `env₂`
  (K.24: `restoreRules` is to positively resolve the restored
  constructor name — official's `env.get` throws there);
* `hrepP`/`hrepS` — the real members' representations (D5's): rule-less
  at `mp₂`, and with the restored rules at every carrier of the store
  agreeing with the provision's leaves;
* `hlaws` — the rule laws at the store (D4's semantic core: the members'
  from the auxiliary ι and R2, the mimics' from ψ's ι and R2).

The conclusion: a model of `env₃ = storeNestedRecs (nestedStores …)
env₂` carrying the leaves at the recursors' names and `mp₂`'s leaves
elsewhere. -/
@[expose] def NestedRecsModelAt {μ : CheckMode} {env₂ : Env} (p : NestedParts)
    (stored : List AuxStored) (cvRms cvRns : List ConstantVal) (rulesM rulesN : List (List RecRule))
    (d : IndRepData V) (mp₂ : EnvModelM V μ env₂) : Prop :=
  (∀ (i : Nat) (x : ConstantVal × Nat × Nat), (nestedProvs cvRms cvRns stored p.k)[i]? = some x →
    ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mp₂.base2.acval env₂ ψ 0 x.1.type = some ta ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
  ∀ (Aof taOf : Nat → (Name → Nat) → AnnotTerm),
    -- NAMED: the leaves' content at every provisioned recursor
    (∀ (i : Nat) (x : ConstantVal × Nat × Nat), (nestedProvs cvRms cvRns stored p.k)[i]? = some x →
      NestedCtorLeaf mp₂ x.1 (Aof i) (taOf i)) →
    -- NAMED (K.24): every stored rule's constructor is stored
    (∀ r ∈ nestedStores cvRms cvRns stored rulesM rulesN p.k, ∀ rl ∈ r.2.2.2,
      ∃ cvj cnP cnF, env₂.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF)) →
    -- NAMED (D5): the real members' representations, rule-less at `mp₂`
    (∀ t, t < p.k → ∀ x : ConstantVal × Nat × Nat, (nestedProvs cvRms cvRns stored p.k)[t]? = some x →
      ∃ (cvT : ConstantVal) (caps : IndCaps) (dT : IndRepData V),
        env₂.find? (d.memberName t) = some (.indInfo cvT caps) ∧
        IndRep mp₂.base2 (d.memberName t) cvT x.1 x.2.1 x.2.2 [] dT t) →
    -- NAMED (D5): the real members' representations with the restored
    -- rules, at every carrier of the store agreeing with the provision
    (∀ t, t < p.k → ∀ r : ConstantVal × Nat × Nat × List RecRule,
      (nestedStores cvRms cvRns stored rulesM rulesN p.k)[t]? = some r →
      ∀ m₃ : EnvModel V (ConLeche.storeNestedRecs (nestedStores cvRms cvRns stored rulesM rulesN p.k) env₂),
        (∀ (i : Nat) (x : ConstantVal × Nat × Nat), (nestedProvs cvRms cvRns stored p.k)[i]? = some x →
          m₃.acval x.1.name = Aof i) →
        (∀ n : Name, (∀ x ∈ nestedProvs cvRms cvRns stored p.k, n ≠ x.1.name) →
          m₃.acval n = mp₂.base2.acval n) →
        ∃ (cvT : ConstantVal) (caps : IndCaps) (dT : IndRepData V),
          (ConLeche.storeNestedRecs (nestedStores cvRms cvRns stored rulesM rulesN p.k) env₂).find?
              (d.memberName t) = some (.indInfo cvT caps) ∧
          IndRep m₃ (d.memberName t) cvT r.1 r.2.1 r.2.2.1 r.2.2.2 dT t) →
    -- NAMED (D4): the rule laws at the store
    (∀ m₃ : EnvModel V (ConLeche.storeNestedRecs (nestedStores cvRms cvRns stored rulesM rulesN p.k) env₂),
      (∀ (i : Nat) (x : ConstantVal × Nat × Nat), (nestedProvs cvRms cvRns stored p.k)[i]? = some x →
        m₃.acval x.1.name = Aof i) →
      (∀ n : Name, (∀ x ∈ nestedProvs cvRms cvRns stored p.k, n ≠ x.1.name) →
        m₃.acval n = mp₂.base2.acval n) →
      ∀ (φ : Name → Nat) (r : ConstantVal × Nat × Nat × List RecRule),
        r ∈ nestedStores cvRms cvRns stored rulesM rulesN p.k →
        ∀ rl ∈ r.2.2.2, RecRule.fire rl ≠ .inert →
          RecRuleLaw m₃ φ r.1.name r.1 r.2.1 r.2.2.1 rl) →
    ∃ mp₃ : EnvModelM V μ (ConLeche.storeNestedRecs (nestedStores cvRms cvRns stored rulesM rulesN p.k) env₂),
      (∀ (i : Nat) (x : ConstantVal × Nat × Nat), (nestedProvs cvRms cvRns stored p.k)[i]? = some x →
        mp₃.base2.acval x.1.name = Aof i) ∧
      (∀ n : Name, (∀ x ∈ nestedProvs cvRms cvRns stored p.k, n ≠ x.1.name) →
        mp₃.base2.acval n = mp₂.base2.acval n)

set_option maxHeartbeats 1600000 in
/-- **D4's clause off the run's facts**: at a model `mp₂` of the
constructors' environment, from the restore stages' runs (the recursor
types at `env₂`, the rules at the provision), the block's shape and the
auxiliary datum's member names.  The chain is `nestedRecsModel` at:
the provision's front-door facts (`nestedProvs_entry`), the names
distinct (`nestedProvs_names`, `nestedRecNames_nodup`), the store's
`EnvWF` (`nested_recs_wf`), the rules' rescue bits the provision's
(`restoreRules_shape`); the representation clause's obligations from
the members' representations crossing the provision (`IndRep.cross`)
and, at the store, `IndReps.ext` over the constructors' environment's
clause with the members' representations with rules
(`hrepS`) — a mimic's recursor is never `T.rec`-named
(`mimicRecName_ne_str_rec`), so it owes nothing there. -/
theorem nestedRecsModel_of_facts {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envAux : Env} {p : NestedParts} {st : ElimState} {b : MutualBlock}
    {stored : List AuxStored} {ctorsR : List (List (ConstantVal × Nat × Nat))}
    {cvRms cvRns : List ConstantVal} {rulesM rulesN : List (List RecRule)}
    {fmsA ctorsA : List ConstantVal}
    (hannF : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p.nP
      p.formers = .ok fmsA)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st)
    (hb : ConLeche.auxBlock p st = some b) (hlenSt : st.types.length = p.k + st.pins.length)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hstoredA : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hcnt : st.pins.length = p.numNested)
    (hrm : ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten (ConLeche.consNestedFormers (stored.take p.k) env))
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
        (stored.take p.k) = .ok cvRms)
    (hrn : ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten (ConLeche.consNestedFormers (stored.take p.k) env))
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.numNested).map p.mimicRecName) (stored.drop p.k) = .ok cvRns)
    (hrulesM : (cvRms.zip (stored.take p.k)).mapM (fun (cvRa, a) =>
        ConLeche.restoreRules (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.provisionNestedRecs
            ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consNestedFormers (stored.take p.k) env)))
          (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules)
      = .ok rulesM)
    (hrulesN : (cvRns.zip (stored.drop p.k)).mapM (fun (cvRa, a) =>
        ConLeche.restoreRules (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.provisionNestedRecs
            ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consNestedFormers (stored.take p.k) env)))
          (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules)
      = .ok rulesN)
    {mpAux : EnvModelM V μ envAux} {d : IndRepData V} (hreps : MutualBlockReps mpAux.base2 b d)
    (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
      (ConLeche.consNestedFormers (stored.take p.k) env)))
    (hE₂ : ConLeche.EtaFamiliesClosed (ConLeche.consNestedCtors ctorsR.flatten
      (ConLeche.consNestedFormers (stored.take p.k) env))) :
    NestedRecsModelAt p stored cvRms cvRns rulesM rulesN d mp₂ := by
  -- ## the block's shape
  have hkb : b.k = st.types.length := ConLeche.auxBlock_k hb
  obtain ⟨-, -, -, -, -, -, hnames, -⟩ := hreps
  have hmemName : ∀ t, t < p.k → d.memberName t = (p.formers.getD t default).1.name := by
    intro t ht
    obtain ⟨ty, hty⟩ : ∃ ty, st.types[t]? = some ty :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [memberName_eq_type hb hnames hty (by omega), nestedMemberName_eq hannF helim ht hty]
  have hstoredLen : stored.length = b.k := (ConLeche.auxStoredAll_inv hstoredA).1
  have hlenT : (stored.take p.k).length = p.k := List.length_take_of_le (by omega)
  have hlenD : (stored.drop p.k).length = p.numNested := by
    rw [List.length_drop, hstoredLen, hkb, hlenSt, ← hcnt]; omega
  obtain ⟨hlenM, hlenN, hentry⟩ := nestedProvs_entry hrm hrn hlenT hlenD
  -- ## the store's shape
  have hRM : rulesM.length = cvRms.length := by
    rw [(ConLeche.mapM_except_inv hrulesM).1, List.length_zip, hlenM, hlenT, Nat.min_self]
  have hRN : rulesN.length = cvRns.length := by
    rw [(ConLeche.mapM_except_inv hrulesN).1, List.length_zip, hlenN, hlenD, Nat.min_self]
  have hsp : (nestedStores cvRms cvRns stored rulesM rulesN p.k).map (fun r => (r.1, r.2.1, r.2.2.1))
      = nestedProvs cvRms cvRns stored p.k := by
    unfold nestedStores nestedProvs
    exact ConLeche.nested_stores_provs (by rw [hlenM, hlenT]) hRM (by rw [hlenN, hlenD]) hRN
  have hwf₃ : ConLeche.EnvWF (ConLeche.storeNestedRecs
      (nestedStores cvRms cvRns stored rulesM rulesN p.k)
      (ConLeche.consNestedCtors ctorsR.flatten (ConLeche.consNestedFormers (stored.take p.k) env))) := by
    unfold nestedStores
    exact ConLeche.nested_recs_wf mp₂.base2.wf hrm hrn hrulesM hrulesN
  have hnd : ((nestedProvs cvRms cvRns stored p.k).map (·.1.name)).Nodup := by
    rw [nestedProvs_names hrm hrn hlenT hlenD]
    exact ConLeche.nestedRecNames_nodup (nestedMemberNames_nodup hannF helim hb hlenSt hcore)
      p.numNested
  -- ## the rules' rescue bits are the provision's
  have hbits : ∀ r ∈ nestedStores cvRms cvRns stored rulesM rulesN p.k, ∀ rl ∈ r.2.2.2,
      (rl.k = true → ConLeche.recRuleKOf
        (ConLeche.provisionNestedRecs (nestedProvs cvRms cvRns stored p.k)
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consNestedFormers (stored.take p.k) env))).find? rl.ctor = true) ∧
      (rl.eta = true → ConLeche.recRuleEtaOf
        (ConLeche.provisionNestedRecs (nestedProvs cvRms cvRns stored p.k)
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consNestedFormers (stored.take p.k) env))).find? r.1.name rl.ctor = true) := by
    intro r hr rl hrl
    unfold nestedProvs
    rcases nestedStores_mem hr with ⟨i, cv, a, rs, hi, rfl⟩ | ⟨i, cv, a, rs, hi, rfl⟩
    · obtain ⟨hcv, hzip⟩ := List.getElem?_zip_eq_some.mp hi
      obtain ⟨ha, hrs⟩ := List.getElem?_zip_eq_some.mp hzip
      obtain ⟨-, hall⟩ := ConLeche.mapM_except_inv hrulesM
      obtain ⟨ab, rs', hab, hrs', hrun⟩ := hall i (by
        rw [List.length_zip, hlenM, hlenT, Nat.min_self]
        have := (List.getElem?_eq_some_iff.mp hcv).1
        omega)
      obtain ⟨hab₁, hab₂⟩ := List.getElem?_zip_eq_some.mp hab
      obtain rfl : ab.1 = cv := Option.some.inj (hab₁.symm.trans hcv)
      obtain rfl : ab.2 = a := Option.some.inj (hab₂.symm.trans ha)
      obtain rfl : rs = rs' := Option.some.inj (hrs.symm.trans hrs')
      obtain ⟨hlenO, hpos⟩ := ConLeche.restoreRules_shape hrun
      dsimp only at hrl
      obtain ⟨l, hl⟩ := List.getElem?_of_mem hrl
      obtain ⟨rl₀, hrl₀⟩ : ∃ rl₀, ab.2.rules[l]? = some rl₀ := ⟨_, List.getElem?_eq_getElem (by
        have := (List.getElem?_eq_some_iff.mp hl).1
        omega)⟩
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk, heta⟩ := hpos l rl₀ rl hrl₀ hl
      exact ⟨fun h => by rw [hk] at h; exact h, fun h => by rw [heta] at h; exact h⟩
    · obtain ⟨hcv, hzip⟩ := List.getElem?_zip_eq_some.mp hi
      obtain ⟨ha, hrs⟩ := List.getElem?_zip_eq_some.mp hzip
      obtain ⟨-, hall⟩ := ConLeche.mapM_except_inv hrulesN
      obtain ⟨ab, rs', hab, hrs', hrun⟩ := hall i (by
        rw [List.length_zip, hlenN, hlenD, Nat.min_self]
        have := (List.getElem?_eq_some_iff.mp hcv).1
        omega)
      obtain ⟨hab₁, hab₂⟩ := List.getElem?_zip_eq_some.mp hab
      obtain rfl : ab.1 = cv := Option.some.inj (hab₁.symm.trans hcv)
      obtain rfl : ab.2 = a := Option.some.inj (hab₂.symm.trans ha)
      obtain rfl : rs = rs' := Option.some.inj (hrs.symm.trans hrs')
      obtain ⟨hlenO, hpos⟩ := ConLeche.restoreRules_shape hrun
      dsimp only at hrl
      obtain ⟨l, hl⟩ := List.getElem?_of_mem hrl
      obtain ⟨rl₀, hrl₀⟩ : ∃ rl₀, ab.2.rules[l]? = some rl₀ := ⟨_, List.getElem?_eq_getElem (by
        have := (List.getElem?_eq_some_iff.mp hl).1
        omega)⟩
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk, heta⟩ := hpos l rl₀ rl hrl₀ hl
      exact ⟨fun h => by rw [hk] at h; exact h, fun h => by rw [heta] at h; exact h⟩
  -- ## the clause
  refine ⟨fun i x hx => restoredRecTy_reads hμ mp₂ (hentry i x hx).1, ?_⟩
  intro Aof taOf hleaves hctorStored hrepP hrepS hlaws
  have hfacts : ∀ (i : Nat) (x : ConstantVal × Nat × Nat),
      (nestedProvs cvRms cvRns stored p.k)[i]? = some x →
      (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consNestedFormers (stored.take p.k) env)).find? x.1.name = none ∧
      RestoredCtorStatic x.1 ∧
      x.1.type.constsResolve (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consNestedFormers (stored.take p.k) env)) = true ∧
      NestedCtorLeaf mp₂ x.1 (Aof i) (taOf i) := by
    intro i x hx
    obtain ⟨hpre, -⟩ := hentry i x hx
    obtain ⟨hfr, hnres, hpshape⟩ := ConLeche.checkConstantValPre_names hpre
    obtain ⟨htf, hlp, htr, hbt⟩ := ConLeche.checkConstantValPre_typeWF hpre
    exact ⟨hfr, ⟨hnres, hpshape, htf, hlp, hbt⟩, htr, hleaves i x hx⟩
  refine nestedRecsModel mp₂ hE₂ hsp hwf₃ hnd Aof taOf hfacts
    (fun {env'} m' =>
      EnvExt (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consNestedFormers (stored.take p.k) env)) env' ∧
      (∀ (i : Nat) (x : ConstantVal × Nat × Nat), (nestedProvs cvRms cvRns stored p.k)[i]? = some x →
        x.1.type.constsResolve env' = true) ∧
      ∀ t, t < p.k → ∀ x : ConstantVal × Nat × Nat, (nestedProvs cvRms cvRns stored p.k)[t]? = some x →
        ∃ (cvT : ConstantVal) (caps : IndCaps) (dT : IndRepData V),
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consNestedFormers (stored.take p.k) env)).find? (d.memberName t)
              = some (.indInfo cvT caps) ∧
          IndRep m' (d.memberName t) cvT x.1 x.2.1 x.2.2 [] dT t)
    ⟨EnvExt.refl _, fun i x hx => (hfacts i x hx).2.2.1, hrepP⟩ ?_ ?_ hctorStored hbits ?_ ?_
  · -- the invariant crosses a fresh recursor's cons
    intro i x hx env' m' hfr hinv m₂ hac
    obtain ⟨hx₁, hres, hrep⟩ := hinv
    refine ⟨hx₁.trans (EnvExt.cons hfr (fun _ h => nomatch h)),
      fun j y hy => Expr.constsResolve_mono (hres j y hy), fun t ht y hy => ?_⟩
    obtain ⟨cvT, caps, dT, hfT, hr⟩ := hrep t ht y hy
    exact ⟨cvT, caps, dT, hfT, hr.cross (c₀ := .recInfo x.1 x.2.1 x.2.2 []) hfr
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) (hx₁.find hfT) m₂ hac
      (ConsCrossAt.ofNtc fun _ h => nomatch h)
      (constsBound_of_constsResolve _ (hres t y hy)) (fun hne => absurd rfl hne)⟩
  · -- the representation clause at a provisioned cons
    intro i x hx env' mp' hfr hinv m₂ hac
    obtain ⟨hx₁, hres, hrep⟩ := hinv
    intro cvR mI rP rules hc T hT
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
    obtain ⟨-, a, hlt, hge, -⟩ := hentry i x hx
    by_cases hi : i < p.k
    · obtain ⟨hname, -⟩ := hlt hi
      have hTeq : T = d.memberName i := by
        rw [hmemName i hi]
        have h := hT
        rw [hname] at h
        exact (Name.str.inj h).1.symm
      subst hTeq
      obtain ⟨cvT, caps, dT, hfT, hr⟩ := hrep i hi x hx
      refine Or.inl ⟨cvT, caps, dT, i, ConLeche.Env.find?_cons_of_fresh hfr (hx₁.find hfT), ?_⟩
      exact hr.cross (c₀ := .recInfo x.1 x.2.1 x.2.2 []) hfr
        (ConsCrossEnv.ofNtc fun _ h => nomatch h) (hx₁.find hfT) m₂ hac
        (ConsCrossAt.ofNtc fun _ h => nomatch h) (constsBound_of_constsResolve _ (hres i x hx))
        (fun hne => absurd rfl hne)
    · exact absurd ((hge (Nat.not_lt.mp hi)).1.symm.trans hT)
        (p.mimicRecName_ne_str_rec T (i - p.k))
  · -- the rule laws, at the carrier's valuation
    intro acv hl ho m₃ hac φ r hr rl hrl hf
    exact hlaws m₃ (by rw [hac]; exact hl) (by rw [hac]; exact ho) φ r hr rl hrl hf
  · -- the representation clause at the store
    intro mpP hinvP hleafP hoffP m₃ hac
    have hfreshS : ∀ r ∈ nestedStores cvRms cvRns stored rulesM rulesN p.k,
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env)).find? r.1.name = none := by
      intro r hr
      have hmem : (r.1, r.2.1, r.2.2.1) ∈ nestedProvs cvRms cvRns stored p.k := by
        rw [← hsp]; exact List.mem_map_of_mem hr
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
      exact (hfacts i _ hi).1
    have hndS : ((nestedStores cvRms cvRns stored rulesM rulesN p.k).map (·.1.name)).Nodup := by
      have h : (nestedStores cvRms cvRns stored rulesM rulesN p.k).map (·.1.name)
          = (nestedProvs cvRms cvRns stored p.k).map (·.1.name) := by
        rw [← hsp, List.map_map]; rfl
      rw [h]; exact hnd
    refine IndReps.ext (storeNestedRecs_envExt hfreshS hndS) ?_ mp₂.ind_reps ?_
    · intro n hn
      rw [hac]
      refine (hoffP n fun x hx heq => ?_).symm
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      have h0 := (hfacts i x hi).1
      rw [heq, h0] at hn
      exact nomatch hn
    · intro n cvR mI rP rules hf₃ hf₂ T hn
      rcases ConLeche.Model.storeNestedRecs_find?_inv hf₃ with h₂ | ⟨r, hr, hc, hname⟩
      · rw [hf₂] at h₂; exact nomatch h₂
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
        have hpi : (nestedProvs cvRms cvRns stored p.k)[i]? = some (r.1, r.2.1, r.2.2.1) := by
          rw [← hsp, List.getElem?_map, hi]; rfl
        obtain ⟨-, a, hlt, hge, -⟩ := hentry i _ hpi
        by_cases hik : i < p.k
        · obtain ⟨hnm, -⟩ := hlt hik
          have hTeq : T = d.memberName i := by
            rw [hmemName i hik]
            have h := hname.trans hn
            rw [hnm] at h
            exact (Name.str.inj h).1.symm
          subst hTeq
          obtain ⟨cvT, caps, dT, hfT, hrep⟩ := hrepS i hik r hi m₃
            (by rw [hac]; exact hleafP) (by rw [hac]; exact hoffP)
          exact Or.inl ⟨cvT, caps, dT, i, hfT, hrep⟩
        · exact absurd ((hge (Nat.not_lt.mp hik)).1.symm.trans (hname.trans hn))
            (p.mimicRecName_ne_str_rec T (i - p.k))

/-! ## The model of `env₃` off the run -/

set_option maxHeartbeats 1600000 in
/-- **The model of `env₃ = storeNestedRecs (nestedStores …) env₂` off
`DeclNestedRun`** (M-D′ D4, consumer-first): the run's restore stages
exposed (the recursor types, the rules, the tables on the store — what
D6 consumes), the constructors' model `mp₂` as D3 builds it
(`nestedCtorsModel_of_run`'s route, under its three premises kept
verbatim — `ContainersRep`, `BridgeSyntax` at every assignment's pin
data, `hvia`), and at it D4's clause `NestedRecsModelAt`: the restored
recursor types read graded, and the model of `env₃` under the
remaining premises named there (DESIGN §M.57). -/
theorem nestedRecsModel_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env) (stored : List AuxStored)
      (ctorsR : List (List (ConstantVal × Nat × Nat))) (cvRms cvRns : List ConstantVal)
      (rulesM rulesN : List (List RecRule)) (order : List Nat),
      ConLeche.auxBlock p st = some b ∧
      ConLeche.nestedTopoOrder (ElimState.grp st) p.k st = .ok order ∧
      st.types.length = p.k + st.pins.length ∧
      st.pins.length = p.numNested ∧
      (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors) = .ok ctorsR ∧
      ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten (ConLeche.consNestedFormers (stored.take p.k) env))
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
        (stored.take p.k) = .ok cvRms ∧
      ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten (ConLeche.consNestedFormers (stored.take p.k) env))
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.numNested).map p.mimicRecName) (stored.drop p.k) = .ok cvRns ∧
      (cvRms.zip (stored.take p.k)).mapM (fun (cvRa, a) =>
        ConLeche.restoreRules (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.provisionNestedRecs (nestedProvs cvRms cvRns stored p.k)
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consNestedFormers (stored.take p.k) env)))
          (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules)
        = .ok rulesM ∧
      (cvRns.zip (stored.drop p.k)).mapM (fun (cvRa, a) =>
        ConLeche.restoreRules (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.provisionNestedRecs (nestedProvs cvRms cvRns stored p.k)
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consNestedFormers (stored.take p.k) env)))
          (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules)
        = .ok rulesN ∧
      -- the tables on the store: `env₄ = envOut` (D6's stage)
      ConLeche.nestedTables (m := ConLeche.CheckM)
        (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
          ((p.formers.getD mIdx default).1.name, a.tbl, cs))
        (ConLeche.storeNestedRecs (nestedStores cvRms cvRns stored rulesM rulesN p.k)
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consNestedFormers (stored.take p.k) env))) = .ok envOut ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
        CtorsChecked μ F env b true d ∧ AuxBlockAgree F mp mpAux b true d ∧
        ∃ (params : List Expr) (pbs : List (Expr × ConLeche.BinderMeta)),
          (ContainersRep env envAux mpAux.base2 →
            -- NAMED (D3, unchanged): the bridge's syntactic half at every
            -- assignment's pin data
            (∀ (ψ : Name → Nat) (cd : Nat → CopyData V),
              (∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j) →
              BridgeSyntax d st p.k st.pins.length cd (auxOfsOf st p.k cd)) →
            -- NAMED (D3, unchanged): the transports are graded at every
            -- restored constructor's leaf frame
            (∀ (ψ : Name → Nat) (cd : Nat → CopyData V),
              (∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j) →
              ∀ (J : Nat) (cA : ConstantVal × Nat), d.ctorsA[J]? = some cA → d.mems J < p.k →
              ∀ (ρ : Nat → V) (ps fs : List V), ps.length = d.nP → fs.length = cA.2 →
              SpineFit ρ ((d.dsRestored mpAux.base2 ψ p.k J
                (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
                (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA)).map (·.2.2)) (ps ++ fs) →
              ∀ i, i < cA.2 → d.copyPos p.k J i →
                WellDenotedV V (consList (ps ++ fs) ρ)
                  (viaEntryAV (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order
                    (fun _ => .sort 0) (d.tgtsR J i - p.k)) cA.2 0 i 0
                    ((d.tssR J ψ).getD i []) ((d.eissR J ψ).getD i []))) →
            ∃ (mp₁ : EnvModelM V μ (ConLeche.consNestedFormers (stored.take p.k) env))
              (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
                (ConLeche.consNestedFormers (stored.take p.k) env))),
              ConLeche.EtaFamiliesClosed (ConLeche.consNestedCtors ctorsR.flatten
                (ConLeche.consNestedFormers (stored.take p.k) env)) ∧
              (∀ n : Name, (env.find? n).isSome = true → mp₁.base2.acval n = mp.base2.acval n) ∧
              (∀ t, t < p.k → mp₁.base2.acval (d.memberName t) = mpAux.base2.acval (d.memberName t)) ∧
              (∀ n : Name, (∀ c ∈ ctorsR.flatten, n ≠ c.1.name) →
                mp₂.base2.acval n = mp₁.base2.acval n) ∧
              -- D4's clause at the constructors' model
              NestedRecsModelAt p stored cvRms cvRns rulesM rulesN d mp₂) := by
  obtain ⟨st, b, envAux, params, pbs, fmsA, ctorsA, stored, order, hb, helim, hord, hlenSt, hfreshC,
    hcontC, hparamsLen, hcore, hstoredA, hpc, hK20, hK23, hK17, hpo, hmo, hhead, hfreshRec, hpinsNP,
    hrest, mpAux, d, hreps, hchk, hag, hpins⟩ := pinFacts_of_run hμ mp hE h
  obtain ⟨-, -, hannF, hannC, hcnt, -, ctorsR, cvRms, cvRns, rulesM, rulesN, hctors, hrm, hrn,
    hrulesM, hrulesN, htables, -, -, -⟩ := hrest
  refine ⟨st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, order, hb, hord, hlenSt, hcnt,
    hctors, hrm, hrn, hrulesM, hrulesN, htables, mpAux, d, hreps, hchk, hag, params, pbs, ?_⟩
  intro hcr hsyn hvia
  have hkp : p.k ≤ b.k := by rw [ConLeche.auxBlock_k hb, hlenSt]; omega
  obtain ⟨mp₁, hE₁, hagReal, hagPre, hag₁, hF, hrealStored⟩ := nestedFormersModel mp hE hcore hstoredA
    (fun t ht => (hfreshRec t ht).1) hK20 hkp mpAux d hreps hag
  -- ## the content at every assignment (D3)
  have hper : ∀ ψ : Name → Nat, ∀ c ∈ ctorsR.flatten, ∃ A ta : AnnotTerm,
      Term.bvarsBelow 0 A.erase ∧ (∀ ρ : Nat → V, WellDenoted V ρ A) ∧
      (∀ ρ : Nat → V, AnnotValid V ρ A) ∧
      denoteMeta mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env) ψ 0 c.1.type
        = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧ ∀ ρ : Nat → V, interp V ρ A ∈ˢ interp V ρ ta := by
    intro ψ
    obtain ⟨cd, hcd⟩ := hpins hcr ψ
    exact nestedCtorLeaf_of_run hμ mp hb helim hord hlenSt hfreshC hcontC hparamsLen hcore hstoredA
      hpc hK20 hK23 hK17 hpo hmo hhead (fun t ht => (hfreshRec t ht).1) hpinsNP hannF hannC hctors
      hreps hchk hcd (hsyn ψ cd hcd) (hvia ψ cd hcd) mp₁ hF hag₁ hrealStored
  -- ## the restored constructors' front door: the level parameters are the block's
  have hpre : ∀ c ∈ ctorsR.flatten,
      ConLeche.checkConstantValPre (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consNestedFormers (stored.take p.k) env) c.1 = .ok c.1 := by
    intro c hc
    obtain ⟨cs, hcs, hcin⟩ := List.mem_flatten.mp hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcs
    obtain ⟨hlen, hall⟩ := ConLeche.mapM_except_inv hctors
    obtain ⟨a, cs', ha, hcs', hrun⟩ := hall j (by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega)
    rw [hj] at hcs'
    have hcc : cs = cs' := by simpa using hcs'
    rw [hcc] at hcin
    exact ConLeche.restoreCtors_pre hrun c hcin
  have hlpsC : ∀ c ∈ ctorsR.flatten, c.1.levelParams = p.lps := by
    intro c hc
    obtain ⟨-, -, -, -, -, -, -, -, hlps, -, -⟩ :=
      restoredCtor_pos hb hlenSt hstoredA hctors hreps hchk c hc
    exact hlps
  -- ## the leaves and readings, canonicalised (D3)
  let Aof : Nat → (Name → Nat) → AnnotTerm := fun i ψ =>
    if hi : i < ctorsR.flatten.length then
      Classical.choose (hper (canonLps p.lps ψ) _ (List.getElem_mem hi))
    else .sort 0
  let taOf : Nat → (Name → Nat) → AnnotTerm := fun i ψ =>
    if hi : i < ctorsR.flatten.length then
      Classical.choose (Classical.choose_spec (hper (canonLps p.lps ψ) _ (List.getElem_mem hi)))
    else .sort 0
  have hleaf : ∀ (i : Nat) (c : ConstantVal × Nat × Nat), ctorsR.flatten[i]? = some c →
      NestedCtorLeaf mp₁ c.1 (Aof i) (taOf i) := by
    intro i c hc
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
    have hmem : ctorsR.flatten[i] ∈ ctorsR.flatten := List.getElem_mem hi
    have hA : ∀ ψ, Aof i ψ = Classical.choose (hper (canonLps p.lps ψ) _ hmem) := fun ψ => by
      show (if hi : i < ctorsR.flatten.length then _ else _) = _
      rw [dif_pos hi]
    have hta : ∀ ψ, taOf i ψ
        = Classical.choose (Classical.choose_spec (hper (canonLps p.lps ψ) _ hmem)) := fun ψ => by
      show (if hi : i < ctorsR.flatten.length then _ else _) = _
      rw [dif_pos hi]
    have hspec : ∀ ψ, Term.bvarsBelow 0 (Aof i ψ).erase ∧
        (∀ ρ : Nat → V, WellDenoted V ρ (Aof i ψ)) ∧ (∀ ρ : Nat → V, AnnotValid V ρ (Aof i ψ)) ∧
        denoteMeta mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env)
          (canonLps p.lps ψ) 0 ctorsR.flatten[i].1.type = some (taOf i ψ) ∧
        (∀ ρ : Nat → V, WellDenotedV V ρ (taOf i ψ)) ∧
        ∀ ρ : Nat → V, interp V ρ (Aof i ψ) ∈ˢ interp V ρ (taOf i ψ) := fun ψ => by
      rw [hA, hta]
      exact Classical.choose_spec (Classical.choose_spec (hper (canonLps p.lps ψ) _ hmem))
    obtain ⟨-, -, -, -, -, -, hlpR, -, -, -, -⟩ :=
      ConLeche.checkConstantValPre_front (hpre _ hmem)
    rw [hlpsC _ hmem] at hlpR
    refine ⟨fun ψ => (hspec ψ).1, fun ψ₁ ψ₂ hagr => ?_, fun ψ ρ => (hspec ψ).2.1 ρ,
      fun ψ ρ => (hspec ψ).2.2.1 ρ, fun ψ => ?_, fun ψ ρ => (hspec ψ).2.2.2.2.1 ρ,
      fun ψ ρ => (hspec ψ).2.2.2.2.2 ρ⟩
    · rw [hA, hA]
      rw [hlpsC _ hmem] at hagr
      have hc' : canonLps p.lps ψ₁ = canonLps p.lps ψ₂ := canonLps_ext hagr
      simp only [hc']
    · rw [denoteMeta_params_ext mp₁.base2 (canonLps_agree p.lps ψ) 0 _ hlpR]
      exact (hspec ψ).2.2.2.1
  obtain ⟨mp₂, hE₂, hagC, -⟩ := nestedCtorsModel mp₁ hE₁ hcore hstoredA hctors Aof taOf hleaf
  -- ## D4's clause
  exact ⟨mp₁, mp₂, hE₂, hagPre, hagReal, hagC,
    nestedRecsModel_of_facts hμ hannF helim hb hlenSt hcore hstoredA hcnt hrm hrn hrulesM hrulesN
      hreps mp₂ hE₂⟩

end ConLeche.Model
