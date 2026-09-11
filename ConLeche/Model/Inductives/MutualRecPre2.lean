module

public import ConLeche.Model.Inductives.MutualRecPre
public import ConLeche.Model.Inductives.FixRecLeaf
import ConLeche.Model.Inductives.FixLeafOk
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only (`PropWhen.never.isNever`). -/
import all ConLeche.Kernel.PropWhen
public section

/-!
# The auxiliary recursor's premise (task #278, M2.3b)

`FixPre` for the auxiliary recursor's binder data
(`auxRecDataAV`, `MutualRecPre.lean`).  The fixpoint route derives its
premise from the CHECKER's typing of the stored generated recursor
type (`fixPre_of` in `FixStageRec.lean`); the auxiliary recursor has no
stored type, so every clause is proved SEMANTICALLY here:

* **closedness** — the tag tupler and a tagged tuple are bounded at the
  parameter frame (`tagTuplerAV_below`, `tagTupleAV_below`), and with
  them the whole binder data (`auxRecDataAV_below`), the minors through
  a generic `minorAVAtRM_below`;
* **grading, validity and universe** of every binder domain, along the
  walks `fixPre_ofL` asks for;
* **assembly** — `auxFixPre_of` and `auxRecLeafFacts`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Closedness: the toolkit -/

omit [SetTheory V] in
/-- Re-bitting binder data does not move its domains. -/
theorem domsBelow_rebit {b k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)}, DomsBelow k (rebit b ds) ↔ DomsBelow k ds
  | [] => Iff.rfl
  | _ :: ds => by
    rw [rebit_cons]
    show _ ∧ DomsBelow (k + 1) (rebit b ds) ↔ _ ∧ DomsBelow (k + 1) ds
    rw [domsBelow_rebit (ds := ds)]

omit [SetTheory V] in
/-- Lifted binder data are bounded at the lifted depth. -/
theorem domsBelow_liftDoms {n : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {K j : Nat}, DomsBelow K ds →
      DomsBelow (K + n) (liftDoms n j ds)
  | [], _, _, _ => trivial
  | d :: ds, K, j, h => by
    refine ⟨?_, ?_⟩
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN n _ _ _ h.1
    · have := domsBelow_liftDoms (n := n) (ds := ds) (K := K + 1) (j := j + 1) h.2
      rwa [show K + 1 + n = K + n + 1 from by omega] at this

/-! ## Closedness: the tag objects -/

omit [SetTheory V] in
/-- **The tag tupler is closed at the parameter frame** when every
member's index chain is. -/
theorem tagTuplerAV_below {W nP m : Nat} {Idss : List (List AnnotTerm)}
    (h : ∀ Ids ∈ Idss, FieldsBelow nP Ids) :
    Term.bvarsBelow nP (tagTuplerAV W m Idss).erase := by
  have hIds : FieldsBelow nP (Idss.getD m []) := by
    rw [List.getD_eq_getElem?_getD]
    cases hm : Idss[m]? with
    | none => exact trivial
    | some Ids => exact h Ids (List.mem_of_getElem? hm)
  unfold tagTuplerAV
  refine sumMkAV_below (nP := 0) (domsBelow_tuplerData hIds) hIds
    (fun Fs' hFs' => uChains_below h Fs' hFs') ?_
  simp [tuplerData]

omit [SetTheory V] in
/-- **A tagged tuple is closed** at the frame its index expressions
are scoped in. -/
theorem tagTupleAV_below {W nP m d : Nat} {Idss : List (List AnnotTerm)} {Es : List AnnotTerm}
    (h : ∀ Ids ∈ Idss, FieldsBelow nP Ids)
    (hEs : ∀ E ∈ Es, Term.bvarsBelow (nP + d) E.erase) :
    Term.bvarsBelow (nP + d) (tagTupleAV W m d Idss Es).erase := by
  unfold tagTupleAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN ?_ ?_
  · rw [AnnotTerm.erase_liftN]
    exact VExprAux.bvarsBelow_liftN d _ _ _ (tagTuplerAV_below h)
  · intro a ha
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
    exact hEs E hE

/-! ## Closedness: the minors -/

omit [SetTheory V] in
/-- An ih binder's domain is bounded at its own depth: the telescope
moved to the ih frame, the motive at the moved index expressions and
the field applied to the telescope's variables. -/
theorem ihDomAVM_below {mot nF o i l nP : Nat} (ho : 0 < o) (hi : i < nF)
    {tl : List (Nat × Nat × AnnotTerm)} (hT : DomsBelow (nP + i) tl)
    {Eis : List AnnotTerm} (hE : ∀ E ∈ Eis, Term.bvarsBelow (nP + i + tl.length) E.erase) :
    Term.bvarsBelow (nP + o + nF + l) (ihDomAVM mot nF o i l tl Eis).erase := by
  unfold ihDomAVM
  refine mkPisAV_below_of ?_ ?_
  · have := ihTeleAtGo_below (K := nP + i) (nF := nF) (o := o) (i := i) (l := l) (k := 0)
      (tl := tl) (by simpa using hT)
    exact domsBelow_mono (by omega) this
  · rw [ihTeleAtR_length, AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN
      (show nF + o - 1 + l + tl.length - mot < nP + o + nF + l + tl.length by omega) ?_
    intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    rcases List.mem_append.mp ha' with ha' | ha'
    · obtain ⟨E, hE', rfl⟩ := List.mem_map.mp ha'
      refine Term.bvarsBelow.mono
        (show nP + i + tl.length + (nF - i + l) + o ≤ nP + o + nF + l + tl.length by omega) ?_
      exact ihIdxAtM_below (hE E hE')
    · rw [List.mem_singleton] at ha'
      subst ha'
      rw [AnnotTerm.erase_mkAppN]
      refine VExprAux.bvarsBelow_mkAppN
        (show nF - 1 - i + l + tl.length < nP + o + nF + l + tl.length by omega) ?_
      intro a'' ha''
      obtain ⟨a₃, ha₃, rfl⟩ := List.mem_map.mp ha''
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha₃
      rw [List.mem_range] at hq
      show tl.length - 1 - q < nP + o + nF + l + tl.length
      omega

omit [SetTheory V] in
/-- **The ih binders' Π-tower is bounded** at the field frame. -/
theorem ihPisAVM_below {moti : Nat → Nat} {nF o b nP : Nat} (ho : 0 < o)
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)}
    (hT : ∀ i, DomsBelow (nP + i) (tls.getD i []))
    (hE : ∀ i, ∀ E ∈ Eiss.getD i [], Term.bvarsBelow (nP + i + (tls.getD i []).length) E.erase) :
    ∀ (is : List Nat) (l : Nat) (body : AnnotTerm), (∀ i ∈ is, i < nF) →
      Term.bvarsBelow (nP + o + nF + l + is.length) body.erase →
      Term.bvarsBelow (nP + o + nF + l) (ihPisAVM moti nF o b tls Eiss is l body).erase
  | [], l, body, _, hb => by
    show Term.bvarsBelow (nP + o + nF + l) body.erase
    exact hb
  | i :: is, l, body, hlt, hb => by
    simp only [ihPisAVM, AnnotTerm.erase_pi, Term.bvarsBelow]
    refine ⟨?_, ?_⟩
    · have := ihDomAVM_below (mot := moti i) (nP := nP) (l := l) ho (hlt i List.mem_cons_self)
        (tl := rebit b (tls.getD i [])) (Eis := Eiss.getD i [])
        (domsBelow_rebit.mpr (hT i)) (by rw [rebit_length]; exact hE i)
      exact this
    · have := ihPisAVM_below (moti := moti) (nF := nF) (b := b) ho hT hE is (l + 1) body
        (fun i' hi' => hlt i' (List.mem_cons_of_mem _ hi'))
        (by rw [show nP + o + nF + (l + 1) + is.length = nP + o + nF + l + (i :: is).length from by
              simp only [List.length_cons]; omega]
            exact hb)
      rwa [show nP + o + nF + (l + 1) = nP + o + nF + l + 1 from by omega] at this

/-- **A minor premise's domain is bounded** at its own depth
`nP + o`. -/
theorem minorAVAtRM_below {mot : Nat} {moti : Nat → Nat} {m : EnvModel V env} {C : Name}
    {ψ : Name → Nat} {nP nF b o : Nat} (ho : 0 < o)
    {ds : List (Nat × Nat × AnnotTerm)} (hds : DomsBelow 0 ds) (hlenDs : ds.length = nP + nF)
    {Es : List AnnotTerm} (hEs : ∀ E ∈ Es, Term.bvarsBelow (nP + nF) E.erase)
    (hCcl : Term.bvarsBelow 0 (m.acval C ψ).erase)
    {ris : List Nat} (hris : ∀ i ∈ ris, i < nF)
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)}
    (hT : ∀ i, DomsBelow (nP + i) (tls.getD i []))
    (hE : ∀ i, ∀ E ∈ Eiss.getD i [], Term.bvarsBelow (nP + i + (tls.getD i []).length) E.erase) :
    Term.bvarsBelow (nP + o) (minorAVAtRM mot moti m C ψ nP nF b o ds Es ris tls Eiss).erase := by
  unfold minorAVAtRM
  refine mkPisAV_below_of ?_ ?_
  · refine domsBelow_rebit.mpr (domsBelow_liftDoms ?_)
    have := DomsBelow.drop nP hds
    rwa [Nat.zero_add] at this
  · rw [rebit_length, liftDoms_length, List.length_drop, hlenDs, Nat.add_sub_cancel_left]
    refine ihPisAVM_below ho hT hE ris 0 _ hris ?_
    rw [AnnotTerm.erase_liftN]
    refine VExprAux.bvarsBelow_liftN ris.length _ _ _ ?_
    rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (show nF + o - 1 - mot < nP + o + nF by omega) ?_
    intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    rcases List.mem_append.mp ha' with ha' | ha'
    · obtain ⟨E, hE', rfl⟩ := List.mem_map.mp ha'
      rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN o E.erase (nP + nF) nF (hEs E hE')
      exact Term.bvarsBelow.mono (show nP + nF + o ≤ nP + o + nF by omega) this
    · rw [List.mem_singleton] at ha'
      subst ha'
      rw [AnnotTerm.erase_mkAppN]
      refine VExprAux.bvarsBelow_mkAppN (Term.bvarsBelow.mono (Nat.zero_le _) hCcl) ?_
      intro a'' ha''
      obtain ⟨a₃, ha₃, rfl⟩ := List.mem_map.mp ha''
      rcases List.mem_append.mp ha₃ with ha₃ | ha₃
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha₃
        rw [List.mem_range] at hq
        show nP + o + nF - 1 - q < nP + o + nF
        omega
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha₃
        rw [List.mem_range] at hq
        show nF - 1 - q < nP + o + nF
        omega

/-! ## Closedness: the motive, the major and the minor block -/

omit [SetTheory V] in
/-- **The motive's domain is closed at the parameter frame**. -/
theorem motiveAVIL_below {L : AnnotTerm} {ψ : Name → Nat} {nP nIdx : Nat} {elimL : Level}
    {ips : List (Nat × Nat × AnnotTerm)} (hL : Term.bvarsBelow 0 L.erase)
    (hips : DomsBelow nP ips) (hlenI : ips.length = nIdx) :
    Term.bvarsBelow nP (motiveAVIL L ψ nP nIdx elimL ips).erase := by
  unfold motiveAVIL
  refine mkPisAV_below_of (domsBelow_rebit.mpr hips) ?_
  rw [rebit_length, hlenI]
  simp only [AnnotTerm.erase_pi, AnnotTerm.erase_sort, Term.bvarsBelow]
  refine ⟨?_, trivial⟩
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (Term.bvarsBelow.mono (Nat.zero_le _) hL) ?_
  intro a ha
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  rcases List.mem_append.mp ha' with ha' | ha'
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha'
    rw [List.mem_range] at hq
    show nP + nIdx - 1 - q < nP + nIdx
    omega
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha'
    rw [List.mem_range] at hq
    show nIdx - 1 - q < nP + nIdx
    omega

omit [SetTheory V] in
/-- **The major's domain is closed at its own depth**. -/
theorem majorAVAtL_below {L : AnnotTerm} {nP nIdx n : Nat} (hL : Term.bvarsBelow 0 L.erase) :
    Term.bvarsBelow (nP + 1 + n + nIdx) (majorAVAtL L nP nIdx n).erase := by
  unfold majorAVAtL
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (Term.bvarsBelow.mono (Nat.zero_le _) hL) ?_
  intro a ha
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  rcases List.mem_append.mp ha' with ha' | ha'
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha'
    rw [List.mem_range] at hq
    show nP + 1 + n + nIdx - 1 - q < nP + 1 + n + nIdx
    omega
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha'
    rw [List.mem_range] at hq
    show nIdx - 1 - q < nP + 1 + n + nIdx
    omega

/-- **The minor block is closed** when every minor is at its own
depth. -/
theorem domsBelow_fixMinorsDataM {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (mots : Nat → Nat) (tgts : Nat → Nat → Nat) (cds : List CtorDatumR) (o : Nat),
      (∀ j cd, cds[j]? = some cd →
        Term.bvarsBelow (nP + (o + j))
          (minorAVAtRM (mots j) (tgts j) m cd.1 ψ nP cd.2.1 b (o + j) cd.2.2.1 cd.2.2.2.1
            cd.2.2.2.2.1 cd.2.2.2.2.2.2 cd.2.2.2.2.2.1).erase) →
      DomsBelow (nP + o) (fixMinorsDataM mots tgts m ψ nP b cds o)
  | _, _, [], _, _ => trivial
  | mots, tgts, (C, nF, ds, Es, ris, Eiss, tls) :: cs, o, h => by
    refine ⟨h 0 _ rfl, ?_⟩
    have := domsBelow_fixMinorsDataM (m := m) (ψ := ψ) (nP := nP) (b := b)
      (fun J => mots (J + 1)) (fun J => tgts (J + 1)) cs (o + 1) ?_
    · rwa [show nP + (o + 1) = nP + o + 1 from by omega] at this
    · intro j cd hcd
      have := h (j + 1) cd (by simpa using hcd)
      rwa [show o + (j + 1) = o + 1 + j from by omega] at this

theorem domsBelow_fixMinorsData {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat}
    (cds : List CtorDatumR) (o : Nat)
    (h : ∀ j cd, cds[j]? = some cd →
      Term.bvarsBelow (nP + (o + j))
        (minorAVAtR m cd.1 ψ nP cd.2.1 b (o + j) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1
          cd.2.2.2.2.2.2 cd.2.2.2.2.2.1).erase) :
    DomsBelow (nP + o) (fixMinorsData m ψ nP b cds o) :=
  domsBelow_fixMinorsDataM _ _ cds o h

/-! ## The raw constructor data's closedness -/

omit [SetTheory V] in
/-- The entries of a `List.range`-indexed list. -/
theorem getD_range_map {α : Type _} (f : Nat → α) (k : Nat) (d : α) {i : Nat} :
    ((List.range k).map f).getD i d = if i < k then f i else d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < k
  · rw [List.getElem?_range hi, if_pos hi]; rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi), if_neg hi]; rfl

/-- **The closedness facts of one RAW constructor datum** — the shape
`FixCtorDataI` records: its leaf, its field data and their count, its
index expressions at the field frame, its recursive positions, and its
slots' telescopes and index expressions. -/
structure RawCtorBelow (nP : Nat) {V : Type w} [SetTheory V] {env : Env} (m : EnvModel V env)
    (ψ : Name → Nat) (cd : CtorDatumR) : Prop where
  leaf : Term.bvarsBelow 0 (m.acval cd.1 ψ).erase
  doms : DomsBelow 0 cd.2.2.1
  len : cd.2.2.1.length = nP + cd.2.1
  esBelow : ∀ E ∈ cd.2.2.2.1, Term.bvarsBelow (nP + cd.2.1) E.erase
  recIdxBnd : ∀ i ∈ cd.2.2.2.2.1, i < cd.2.1
  tssBelow : ∀ i, DomsBelow (nP + i) (cd.2.2.2.2.2.2.getD i [])
  eissBelow : ∀ i, ∀ E ∈ cd.2.2.2.2.2.1.getD i [],
    Term.bvarsBelow (nP + i + (cd.2.2.2.2.2.2.getD i []).length) E.erase

/-- **A tagged constructor datum's minor is closed** at its own depth:
its one index expression and its slots' are tagged tuples over the raw
ones (the datum is `auxCtorDatum W Idss mem tgts cd`, spelled out). -/
theorem auxCtorDatum_minor_below {m : EnvModel V env} {ψ : Name → Nat} {W nP b o mem : Nat}
    {tgts : Nat → Nat} {Idss : List (List AnnotTerm)} (ho : 0 < o)
    (hIdss : ∀ Ids ∈ Idss, FieldsBelow nP Ids) {cd : CtorDatumR}
    (h : RawCtorBelow nP m ψ cd) :
    Term.bvarsBelow (nP + o)
      (minorAVAtR m cd.1 ψ nP cd.2.1 b o cd.2.2.1
        [tagTupleAV W mem cd.2.1 Idss cd.2.2.2.1] cd.2.2.2.2.1 cd.2.2.2.2.2.2
        ((List.range cd.2.1).map fun i =>
          [tagTupleAV W (tgts i) (i + (cd.2.2.2.2.2.2.getD i []).length) Idss
            (cd.2.2.2.2.2.1.getD i [])])).erase := by
  refine minorAVAtRM_below ho h.doms h.len ?_ h.leaf h.recIdxBnd h.tssBelow ?_
  · intro E hE
    rw [List.mem_singleton] at hE
    subst hE
    exact tagTupleAV_below hIdss h.esBelow
  · intro i E hE
    rw [getD_range_map] at hE
    split at hE
    · rw [List.mem_singleton] at hE
      subst hE
      have harith : nP + i + (cd.2.2.2.2.2.2.getD i []).length
          = nP + (i + (cd.2.2.2.2.2.2.getD i []).length) := by omega
      rw [harith]
      refine tagTupleAV_below hIdss (fun E hE' => ?_)
      rw [← harith]
      exact h.eissBelow i E hE'
    · exact nomatch hE

/-- The tagged datum's components, by definition. -/
theorem auxCtorDatum_parts (W : Nat) (Idss : List (List AnnotTerm)) (mem : Nat)
    (tgts : Nat → Nat) (cd : CtorDatumR) :
    (auxCtorDatum W Idss mem tgts cd).1 = cd.1 ∧
      (auxCtorDatum W Idss mem tgts cd).2.1 = cd.2.1 ∧
      (auxCtorDatum W Idss mem tgts cd).2.2.1 = cd.2.2.1 ∧
      (auxCtorDatum W Idss mem tgts cd).2.2.2.1 = [tagTupleAV W mem cd.2.1 Idss cd.2.2.2.1] ∧
      (auxCtorDatum W Idss mem tgts cd).2.2.2.2.1 = cd.2.2.2.2.1 ∧
      (auxCtorDatum W Idss mem tgts cd).2.2.2.2.2.1 =
        ((List.range cd.2.1).map fun i =>
          [tagTupleAV W (tgts i) (i + (cd.2.2.2.2.2.2.getD i []).length) Idss
            (cd.2.2.2.2.2.1.getD i [])]) ∧
      (auxCtorDatum W Idss mem tgts cd).2.2.2.2.2.2 = cd.2.2.2.2.2.2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## Closedness: the auxiliary binder data -/

/-- **The auxiliary recursor's binder data is closed.** -/
theorem auxRecDataAV_below {m : EnvModel V env} {ψ : Name → Nat} {W w nP : Nat} {elimL : Level}
    {pps : List (Nat × Nat × AnnotTerm)} {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)} {mems : Nat → Nat} {tgts : Nat → Nat → Nat}
    {cds : List CtorDatumR}
    (hp : DomsBelow 0 pps) (hlenP : pps.length = nP)
    (hIdss : ∀ Ids ∈ Idss, FieldsBelow nP Ids)
    (hchains : ∀ chain ∈ chainsXI W (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess',
      FieldsBelow (nP + 2) chain)
    (hcds : ∀ (j : Nat) (cd : CtorDatumR), cds[j]? = some cd → RawCtorBelow nP m ψ cd) :
    DomsBelow 0 (auxRecDataAV m ψ W w nP elimL pps Idss rss tlss Eiss' Fss₀ Ess' mems tgts cds) := by
  have hL : Term.bvarsBelow 0 (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess').erase :=
    auxFormerAV_below hp hlenP hIdss hchains
  have hips : DomsBelow nP (tagIps W Idss) := ⟨tagTyAV_below hIdss, trivial⟩
  have hn : (auxCtorData W Idss mems tgts cds).length = cds.length :=
    auxCtorData_length W Idss mems tgts cds
  -- the minor block
  have hmin : DomsBelow (nP + 1)
      (fixMinorsData m ψ nP (pwBit ψ (Level.zeronessOf elimL))
        (auxCtorData W Idss mems tgts cds) 1) := by
    refine domsBelow_fixMinorsData _ 1 ?_
    intro j cd' hj
    rw [auxCtorData_getElem?] at hj
    cases hcd : cds[j]? with
    | none => rw [hcd] at hj; exact nomatch hj
    | some cd =>
      rw [hcd, Option.map_some, Option.some.injEq] at hj
      subst hj
      exact auxCtorDatum_minor_below (by omega) hIdss (hcds j cd hcd)
  unfold auxRecDataAV fixRecDataAVL
  refine domsBelow_append (domsBelow_append (domsBelow_append (domsBelow_append
    (domsBelow_rebit.mpr hp) ?_) ?_) ?_) ?_
  · rw [rebit_length, hlenP, Nat.zero_add]
    exact ⟨motiveAVIL_below hL hips rfl, trivial⟩
  · rw [List.length_append, rebit_length, hlenP, List.length_singleton, Nat.zero_add]
    exact hmin
  · rw [List.length_append, List.length_append, rebit_length, hlenP, List.length_singleton,
      fixMinorsData_length, hn, Nat.zero_add]
    refine domsBelow_rebit.mpr ?_
    have := domsBelow_liftDoms (n := cds.length + 1) (j := 0) hips
    rwa [show nP + (cds.length + 1) = nP + 1 + cds.length from by omega] at this
  · rw [List.length_append, List.length_append, List.length_append, rebit_length, hlenP,
      List.length_singleton, fixMinorsData_length, hn, rebit_length, liftDoms_length,
      Nat.zero_add]
    refine ⟨?_, trivial⟩
    have := majorAVAtL_below (L := auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess')
      (nP := nP) (nIdx := 1) (n := cds.length) hL
    exact this

/-! ## The slots' tagged index expressions -/

/-- **What the auxiliary family's slot index expressions are**: every
entry of `Eiss'` is a tagged tuple over raw expressions scoped at the
slot's own frame (`mutualEiss`'s shape, membership-wise, so that the
out-of-range entries are the empty list). -/
def AuxSlotTagged (W nP : Nat) (Idss : List (List AnnotTerm))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm))) :
    Prop :=
  ∀ j i, ∀ E ∈ (Eiss'.getD j []).getD i [],
    ∃ (mm : Nat) (Es : List AnnotTerm),
      (∀ E' ∈ Es, Term.bvarsBelow (nP + i + ((tlss.getD j []).getD i []).length) E'.erase) ∧
      E = tagTupleAV W mm (i + ((tlss.getD j []).getD i []).length) Idss Es

omit [SetTheory V] in
/-- **`FixPre`'s `hEbelow` at the tagged slots.** -/
theorem auxEbelow_of {W nP : Nat} {Idss : List (List AnnotTerm)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    (hIdss : ∀ Ids ∈ Idss, FieldsBelow nP Ids) (h : AuxSlotTagged W nP Idss tlss Eiss') :
    ∀ j i, ∀ E ∈ (Eiss'.getD j []).getD i [],
      Term.bvarsBelow (nP + i + ((tlss.getD j []).getD i []).length) E.erase := by
  intro j i E hE
  obtain ⟨mm, Es, hEs, rfl⟩ := h j i E hE
  have harith : nP + i + ((tlss.getD j []).getD i []).length
      = nP + (i + ((tlss.getD j []).getD i []).length) := by omega
  rw [harith]
  refine tagTupleAV_below hIdss (fun E' hE' => ?_)
  rw [← harith]
  exact hEs E' hE'

end ConLeche.Model
