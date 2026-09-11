module

public import ConLeche.Model.Inductives.MutualRecPre
public import ConLeche.Model.Inductives.FixRecLeaf
import ConLeche.Model.Inductives.FixLeafOk
import ConLeche.Model.Inductives.FixIntro
import ConLeche.Model.Inductives.FixRecLaw
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

/-! ## Universe placement: the toolkit -/

omit [SetTheory V] in
theorem max_ne_zero_right {u v : Nat} (hv : v ≠ 0) : Nat.max u v ≠ 0 := by
  have h1 : v ≤ Nat.max u v := Nat.le_max_right u v
  omega

omit [SetTheory V] in
theorem zero_iff_max {u v : Nat} (hv : v ≠ 0) : v = 0 ↔ Nat.max u v = 0 := by
  have h1 : v ≤ Nat.max u v := Nat.le_max_right u v
  omega

omit [SetTheory V] in
theorem max_max_self (u v : Nat) : Nat.max u (Nat.max u v) = Nat.max u v :=
  Nat.max_eq_right (Nat.le_max_left u v)

/-- A nested product over a graded telescope lands in the join of the
telescope's universe and its body's. -/
theorem piTele_mem_univ_max {u v : Nat} (hu : u ≠ 0) (hv : v ≠ 0) {B : List V → V} :
    ∀ (Fs : List AnnotTerm) {σ : Nat → V} {acc : List V},
      FieldsOkB u σ Fs →
      (∀ as, SpineFit σ Fs as → B (acc ++ as) ∈ˢ (univ (Nat.max u v) : V)) →
      piTele v (teleOfFields σ Fs) B acc ∈ˢ (univ (Nat.max u v) : V)
  | [], _, _, _, hB => by simpa [piTele] using hB [] trivial
  | F :: Fs, σ, acc, hF, hB => by
    obtain ⟨-, hbnd, hrest⟩ := hF
    simp only [teleOfFields_cons, piTele]
    rw [piR_congr_bit (zero_iff_max (u := u) hv)]
    have := piR_mem_univ (u := u) (v := Nat.max u v) (hbnd hu) fun a ha =>
      piTele_mem_univ_max hu hv Fs (acc := acc ++ [a]) (hrest a ha) fun as hsp => by
        have := hB (a :: as) ⟨ha, hsp⟩
        rwa [List.append_assoc, List.singleton_append]
    rwa [if_neg (max_ne_zero_right (u := u) hv), max_max_self u v] at this

/-- The minor space over a graded field chain lands in the join of the
chain's universe and its conclusion's. -/
theorem minorSpI_mem_univ_max {u v : Nat} (hu : u ≠ 0) (hv : v ≠ 0) {c : List V → V} :
    ∀ (Fs : List AnnotTerm) {ρf : Nat → V} {acc : List V},
      FieldsOkB u ρf Fs →
      (∀ as, SpineFit ρf Fs as → c (acc ++ as) ∈ˢ (univ (Nat.max u v) : V)) →
      minorSpI v c Fs ρf acc ∈ˢ (univ (Nat.max u v) : V)
  | [], _, _, _, hc => by simpa [minorSpI] using hc [] trivial
  | F :: Fs, ρf, acc, hF, hc => by
    obtain ⟨-, hbnd, hrest⟩ := hF
    show piR v (interp V ρf F) (fun a => minorSpI v c Fs (cons a ρf) (acc ++ [a]))
      ∈ˢ (univ (Nat.max u v) : V)
    rw [piR_congr_bit (zero_iff_max (u := u) hv)]
    have := piR_mem_univ (u := u) (v := Nat.max u v) (hbnd hu) fun a ha =>
      minorSpI_mem_univ_max hu hv Fs (acc := acc ++ [a]) (hrest a ha) fun as hsp => by
        have := hc (a :: as) ⟨ha, hsp⟩
        rwa [List.append_assoc, List.singleton_append]
    rwa [if_neg (max_ne_zero_right (u := u) hv), max_max_self u v] at this

/-- The ih tower over domains and a conclusion in one universe stays
there. -/
theorem ihSpL_mem_univ {t v : Nat} (ht : t ≠ 0) (hv : v ≠ 0) {C : V} (hC : C ∈ˢ (univ t : V)) :
    ∀ As : List V, (∀ A ∈ As, A ∈ˢ (univ t : V)) → ihSpL v C As ∈ˢ (univ t : V)
  | [], _ => hC
  | A :: As, hAs => by
    show piR v A (fun _ => ihSpL v C As) ∈ˢ (univ t : V)
    rw [piR_congr_bit (show v = 0 ↔ t = 0 by omega)]
    have := piR_mem_univ (u := t) (v := t) (hAs A List.mem_cons_self)
      fun _ _ => ihSpL_mem_univ ht hv hC As fun A' hA' => hAs A' (List.mem_cons_of_mem _ hA')
    rwa [if_neg ht, show Nat.max t t = t from Nat.max_self t] at this

/-- **A Π-tower over graph-regime binders lands in the universe** its
domains and its body do. -/
theorem interp_mkPisAV_mem_univ {t : Nat} (ht : t ≠ 0) {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      (∀ d ∈ gds, d.2.1 ≠ 0) →
      FieldsOkB t σ (gds.map (·.2.2)) →
      (∀ as, SpineFit σ (gds.map (·.2.2)) as → interp V (consList as σ) R ∈ˢ (univ t : V)) →
      interp V σ (mkPisAV gds R) ∈ˢ (univ t : V)
  | [], σ, _, _, hR => by simpa [mkPisAV, consList] using hR [] trivial
  | d :: gds, σ, hb, hF, hR => by
    rw [List.map_cons] at hF
    obtain ⟨-, hbnd, hrest⟩ := hF
    simp only [mkPisAV, interp_pi]
    rw [piR_congr_bit (show d.2.1 = 0 ↔ t = 0 by have := hb d List.mem_cons_self; omega)]
    have := piR_mem_univ (u := t) (v := t) (hbnd ht) fun a ha =>
      interp_mkPisAV_mem_univ ht (fun d' hd' => hb d' (List.mem_cons_of_mem _ hd')) (hrest a ha)
        fun as hsp => by
          have := hR (a :: as) ⟨ha, hsp⟩
          rwa [consList_cons] at this
    rwa [if_neg ht, show Nat.max t t = t from Nat.max_self t] at this

/-! ## The former's leaf, applied -/

theorem AnnotValid_mkAppN {ρ : Nat → V} :
    ∀ {args : List AnnotTerm} {f : AnnotTerm}, AnnotValid V ρ f →
      (∀ a ∈ args, AnnotValid V ρ a) → AnnotValid V ρ (AnnotTerm.mkAppN f args)
  | [], _, hf, _ => hf
  | a :: args, f, hf, ha => by
    show AnnotValid V ρ (AnnotTerm.mkAppN (.app f a) args)
    refine AnnotValid_mkAppN ?_ fun a' ha' => ha a' (List.mem_cons_of_mem _ ha')
    rw [AnnotValid_app]
    exact ⟨hf, ha a List.mem_cons_self⟩

/-- **The former leaf's typing** — the one input the mutual data
cannot produce on its own: a CLOSED leaf, graded and valid at every
frame, inhabiting its Π-type at the frame below the parameters, whose
binders are all in the graph regime. -/
structure LeafTyping {V : Type w} [SetTheory V] (L : AnnotTerm) (u : Nat)
    (gds : List (Nat × Nat × AnnotTerm)) (ρ₀ : Nat → V) : Prop where
  ok : ∀ σ : Nat → V, WellDenotedV V σ L
  mem : ∀ σ : Nat → V, interp V σ L ∈ˢ interp V ρ₀ (mkPisAV gds (.sort u))
  bits : ∀ d ∈ gds, d.2.1 ≠ 0

/-- **The former's leaf applied to the parameter variables and an
index spine is graded and valid**, at any frame over the parameter
frame. -/
theorem leafApp_facts {L : AnnotTerm} {nP nIdx u : Nat}
    {pps ips : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP)
    {ρp : Nat → V} (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hL : LeafTyping L u (pps ++ ips) (fun k => ρp (k + nP)))
    {as₀ as : List V} (hlenAs : as.length = nIdx)
    (hspAs : SpineFit ρp (ips.map (·.2.2)) as) :
    WellDenotedV V (consList as (consList as₀ ρp))
      (AnnotTerm.mkAppN L (paramBvarsAt nP (nP + (as₀.length + nIdx)) ++ fieldBvars nIdx)) := by
  have hlenPs : ((pps.map (·.2.2))).length = nP := by rw [List.length_map, hlenP]
  -- the parameter spine
  have hspP : SpineFit (fun j => ρp (j + nP)) (pps.map (·.2.2)) ((List.range nP).reverse.map ρp) := by
    have := spineFit_of_sat (Ds := pps.map (·.2.2)) (Δ₀ := []) (ρ := ρp)
      (by rw [List.append_nil]; exact hsatP)
    rwa [hlenPs] at this
  have hcl : consList ((List.range nP).reverse.map ρp) (fun j => ρp (j + nP)) = ρp :=
    consList_range_reverse nP ρp
  have hsp : SpineFit (fun j => ρp (j + nP)) ((pps ++ ips).map (·.2.2))
      ((List.range nP).reverse.map ρp ++ as) := by
    rw [List.map_append]
    refine SpineFit.append hspP ?_
    rw [hcl]; exact hspAs
  -- the arguments' values
  have hσ : ∀ j, consList as (consList as₀ ρp) (j + (as₀.length + nIdx)) = ρp j := by
    intro j
    rw [show j + (as₀.length + nIdx) = (j + as₀.length) + as.length from by omega,
      consList_apply_add, consList_apply_add]
  have hargs : (paramBvarsAt nP (nP + (as₀.length + nIdx)) ++ fieldBvars nIdx).map
        (interp V (consList as (consList as₀ ρp)))
      = (List.range nP).reverse.map ρp ++ as := by
    rw [List.map_append, map_paramBvarsAt_interp hσ]
    congr 1
    show ((List.range nIdx).map fun k => AnnotTerm.bvar (nIdx - 1 - k)).map
      (interp V (consList as (consList as₀ ρp))) = as
    exact map_fieldBvars_interp hlenAs _
  have hchain : AppChainOk (interp V (consList as (consList as₀ ρp)) L)
      ((paramBvarsAt nP (nP + (as₀.length + nIdx)) ++ fieldBvars nIdx).map
        (interp V (consList as (consList as₀ ρp)))) := by
    rw [hargs]
    exact appChainOk_of_mkPisAV' (m := u + 1) (C := .sort u)
      (fun d hd => ⟨fun h => absurd h (Nat.succ_ne_zero u), fun h => absurd h (hL.bits d hd)⟩)
      (fun h => absurd h (Nat.succ_ne_zero u)) (hL.mem _) hsp
  have hargsOk : ∀ a ∈ paramBvarsAt nP (nP + (as₀.length + nIdx)) ++ fieldBvars nIdx,
      WellDenoted V (consList as (consList as₀ ρp)) a ∧
        AnnotValid V (consList as (consList as₀ ρp)) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
      exact ⟨trivial, trivial⟩
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
      exact ⟨trivial, trivial⟩
  exact ⟨(mkAppN_wellDenoted_of_chain (hL.ok _).1 (fun a ha => (hargsOk a ha).1) hchain).1,
    AnnotValid_mkAppN (hL.ok _).2 fun a ha => (hargsOk a ha).2⟩

/-! ## The motive, the index binder and the major -/

/-- **The auxiliary motive space's universe**: the join of the tag's,
the fibres' and the elimination level's successor. -/
theorem auxMotSp_mem_univ {ℓ W w : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss Ess' : List (List AnnotTerm)}
    (hT : TagOk W ρp Idss)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess') :
    auxMotSp ℓ W w ρp Idss rss tlss Eiss' Fss Ess'
      ∈ˢ (univ (Nat.max W (Nat.max w (ℓ + 1))) : V) := by
  unfold auxMotSp
  rw [piR_congr_bit (zero_iff_max (u := w) (Nat.succ_ne_zero ℓ))]
  have hinner : ∀ i, i ∈ˢ tagSet W ρp Idss →
      piR (ℓ + 1) (auxFib W w ρp Idss rss tlss Eiss' Fss Ess' i) (fun _ => (univ ℓ : V))
        ∈ˢ (univ (Nat.max w (ℓ + 1)) : V) := by
    intro i hi
    have := piR_mem_univ (u := w) (v := ℓ + 1) (auxFib_univ hT hok hi) (fun _ _ => univ_mem_univ ℓ)
    rwa [if_neg (Nat.succ_ne_zero ℓ)] at this
  have := piR_mem_univ (u := W) (v := Nat.max w (ℓ + 1)) (tagTyAV_facts hT).2.1 hinner
  rwa [if_neg (max_ne_zero_right (u := w) (Nat.succ_ne_zero ℓ))] at this

/-- **The auxiliary motive's domain**: graded, valid, and in the join
universe. -/
theorem auxMotive_facts {ψ : Name → Nat} {elimL : Level} {ℓ W w nP : Nat}
    (hℓ : elimL.eval ψ = ℓ) {pps : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP)
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)} {ρp : Nat → V}
    (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hT : TagOk W ρp Idss) (hTV : SumFieldsValid ρp Idss)
    (hX : XChainsOk W w ρp (auxIds W Idss) rss tlss Eiss' Fss₀ Ess')
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess')
    (hcl : Term.bvarsBelow 0 (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess').erase)
    (hL : LeafTyping (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess') w (pps ++ tagIps W Idss)
      (fun k => ρp (k + nP))) :
    WellDenotedV V ρp
        (motiveAVIL (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess') ψ nP 1 elimL
          (tagIps W Idss)) ∧
      interp V ρp
        (motiveAVIL (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess') ψ nP 1 elimL
          (tagIps W Idss)) ∈ˢ (univ (Nat.max W (Nat.max w (ℓ + 1))) : V) := by
  have hb0 : pwBit ψ PropWhen.never ≠ 0 := pwBit_ne_zero_of_isNever rfl ψ
  have hIdx : IdxOk W ρp (auxIds W Idss) := auxIds_idxOk hT
  have htagV : AnnotValid V ρp (tagTyAV W Idss) := sumBodyAV_validV (uChains_validV hTV)
  -- the body, at a fitting tag spine
  have hbody : ∀ as : List V, SpineFit ρp ((tagIps W Idss).map (·.2.2)) as →
      WellDenotedV V (consList as ρp)
        (AnnotTerm.mkAppN (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess')
          (paramBvarsAt nP (nP + 1) ++ fieldBvars 1)) := by
    intro as hsp
    have hlenAs : as.length = 1 := by rw [hsp.length_eq]; rfl
    have := leafApp_facts (u := w) (as₀ := []) hlenP hsatP hL hlenAs
      (by rw [tagIps_doms] at hsp ⊢; exact hsp)
    simpa using this
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold motiveAVIL
    refine WellDenoted_mkPisAV_of (w := W) (by rw [rebit_map_dom, tagIps_doms]; exact hIdx.1)
      fun as hsp => ?_
    rw [rebit_map_dom] at hsp
    rw [WellDenoted_pi]
    exact ⟨(hbody as hsp).1, fun _ _ => trivial⟩
  · unfold motiveAVIL
    refine AnnotValid_mkPisAV_of (w := W) (fun d hd => by
        rw [mem_rebit hd]
        exact ⟨fun h => absurd h hb0, fun h => absurd h hT.1⟩)
      (by rw [rebit_map_dom, tagIps_doms]; exact ⟨htagV, fun _ _ => trivial⟩)
      (fun as hsp => ?_) (fun h0 => absurd h0 hT.1)
    rw [rebit_map_dom] at hsp
    rw [AnnotValid_pi]
    exact ⟨(hbody as hsp).2, fun _ _ => trivial, fun h0 => absurd h0 hb0⟩
  · rw [auxMotive_interp hℓ hlenP hsatP hT hX hcl]
    exact auxMotSp_mem_univ hT hok

/-- **The lifted tag binder**: graded, valid, and in the tag's
universe, at any frame over the parameter frame. -/
theorem auxIdxBinder_facts {W d : Nat} {Idss : List (List AnnotTerm)} {ρp σ : Nat → V}
    (hfr : shiftE d 0 σ = ρp) (hT : TagOk W ρp Idss) (hTV : SumFieldsValid ρp Idss) :
    WellDenotedV V σ ((tagTyAV W Idss).liftN d 0) ∧
      interp V σ ((tagTyAV W Idss).liftN d 0) ∈ˢ (univ W : V) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [WellDenoted_liftN, hfr]; exact (tagTyAV_facts hT).2.2
  · rw [AnnotValid_liftN, hfr]; exact sumBodyAV_validV (uChains_validV hTV)
  · rw [interp_liftN, hfr, (tagTyAV_facts hT).1]; exact (tagTyAV_facts hT).2.1

/-- **The major's domain**: graded, valid, and in the block's
universe, at a K-frame. -/
theorem auxMajor_facts {W w nP n : Nat} {pps : List (Nat × Nat × AnnotTerm)}
    (hlenP : pps.length = nP) {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)} {ρp : Nat → V}
    (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hT : TagOk W ρp Idss)
    (hX : XChainsOk W w ρp (auxIds W Idss) rss tlss Eiss' Fss₀ Ess')
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess')
    (hcl : Term.bvarsBelow 0 (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess').erase)
    (hL : LeafTyping (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess') w (pps ++ tagIps W Idss)
      (fun k => ρp (k + nP)))
    {M : V} {ms is : List V} (hlenM : ms.length = n)
    (hfit : SpineFit ρp (auxIds W Idss) is) :
    WellDenotedV V (consList is (consList ms (cons M ρp)))
        (majorAVAtL (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess') nP 1 n) ∧
      interp V (consList is (consList ms (cons M ρp)))
        (majorAVAtL (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess') nP 1 n)
          ∈ˢ (univ w : V) := by
  have hlenIs : is.length = 1 := by rw [hfit.length_eq]; rfl
  obtain ⟨i, rfl, hi⟩ := spineFit_singleton (D := tagTyAV W Idss) hfit
  rw [(tagTyAV_facts hT).1] at hi
  have hleafT := auxFormer_hleafT (nP := nP) hcl ρp
  have hfit' : SpineFit ρp ((tagIps W Idss).map (·.2.2)) [i] := by
    rw [tagIps_doms]; exact hfit
  refine ⟨?_, ?_⟩
  · have hthis := leafApp_facts (u := w) (as₀ := M :: ms) (ips := tagIps W Idss) hlenP hsatP hL
      hlenIs hfit'
    have harith : nP + 1 + n + 1 = nP + ((M :: ms).length + 1) := by
      rw [List.length_cons, hlenM]; omega
    show WellDenotedV V (consList [i] (consList ms (cons M ρp)))
      (AnnotTerm.mkAppN (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess')
        (paramBvarsAt nP (nP + 1 + n + 1) ++ fieldBvars 1))
    rw [harith]
    exact hthis
  · rw [interp_majorAVAtL (ips := tagIps W Idss) (nIdx := 1) hlenP
      (show (tagIps W Idss).length = 1 from rfl) hsatP
      (by rw [tagIps_doms]; exact hX) hleafT hlenM hfit']
    rw [tagIps_doms]
    have hmem : auxTup W i ∈ˢ idxSet W ρp (auxIds W Idss) := auxTup_mem hT hi
    exact famSpace_app (by rw [← lfpFamSpace_eq]; exact auxFamI_mem_space hT hok) hmem

/-! ## The minors: the tag tupler's validity -/

/-- **The tag tupler is bit-valid** at the parameter frame. -/
theorem tagTuplerAV_validV {W m : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    (hTV : SumFieldsValid ρp Idss) {Ids : List AnnotTerm} (hm : Idss[m]? = some Ids) :
    AnnotValid V ρp (tagTuplerAV W m Idss) := by
  have hg : Idss.getD m [] = Ids := by rw [List.getD_eq_getElem?_getD, hm]; rfl
  have hIdsV : FieldsValid ρp Ids := hTV Ids (List.mem_of_getElem? hm)
  unfold tagTuplerAV
  rw [hg]
  show AnnotValid V ρp (mkLamsC W (tuplerData W Ids) _)
  refine mkLamsC_validV (underTowerValid_of_fields (u := W) hIdsV fun bs hsp => ?_)
  exact sumInj_validV_at_fields (uChains_validV hTV) hIdsV hsp

/-- **A tagged tuple is bit-valid** at the frame its index expressions
are scoped in. -/
theorem tagTupleAV_validV {W m d : Nat} {ρp τ : Nat → V} {Idss : List (List AnnotTerm)}
    (hTV : SumFieldsValid ρp Idss) {Ids : List AnnotTerm} (hm : Idss[m]? = some Ids)
    (hfr : shiftE d 0 τ = ρp) {Es : List AnnotTerm} (hEv : ∀ E ∈ Es, AnnotValid V τ E) :
    AnnotValid V τ (tagTupleAV W m d Idss Es) := by
  unfold tagTupleAV
  refine AnnotValid_mkAppN ?_ hEv
  rw [AnnotValid_liftN, hfr]
  exact tagTuplerAV_validV hTV hm

/-! ## The minors: the ih binders -/

omit [SetTheory V] in
/-- The motive variable at an ih frame reads the motive. -/
theorem ihMotVar_at {nF o l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (as : List V) :
    consList as (consList ihs (consList fs (consList ms (cons M ρp))))
        (nF + o - 1 + l + as.length) = M := by
  rw [consList_apply_add, show nF + o - 1 + l = (nF + o - 1) + ihs.length from by omega,
    consList_apply_add, show nF + o - 1 = (o - 1) + fs.length from by omega, consList_apply_add,
    show o - 1 = 0 + ms.length from by omega, consList_apply_add]
  rfl

/-- The field variable at an ih frame reads the field. -/
theorem ihFieldVar_at {nF l i : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i < nF) (as : List V) :
    consList as (consList ihs (consList fs (consList ms (cons M ρp))))
        (nF - 1 - i + l + as.length) = fs.getD i pt := by
  rw [consList_apply_add, show nF - 1 - i + l = (nF - 1 - i) + ihs.length from by omega,
    consList_apply_add, consList_apply_lt' fs _ (by omega),
    show fs.length - 1 - (nF - 1 - i) = i from by omega]

/-- **The auxiliary motive's two-step application chain**: the tag
element, then the fibre's element. -/
theorem auxMot_chain {ℓ W w : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss₀ Ess' : List (List AnnotTerm)} {M t x : V}
    (hM : M ∈ˢ auxMotSp ℓ W w ρp Idss rss tlss Eiss' Fss₀ Ess')
    (ht : t ∈ˢ tagSet W ρp Idss)
    (hx : x ∈ˢ auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess' t) :
    AppChainOk M [t, x] ∧ SetTheory.app (SetTheory.app M t) x ∈ˢ (univ ℓ : V) := by
  have hMt : SetTheory.app M t
      ∈ˢ piR (ℓ + 1) (auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess' t) fun _ => (univ ℓ : V) :=
    app_mem_piR_pos (Nat.succ_ne_zero ℓ) hM ht
  refine ⟨?_, app_mem_piR_pos (Nat.succ_ne_zero ℓ) hMt hx⟩
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  match k with
  | 0 =>
    exact ⟨ℓ + 1, tagSet W ρp Idss,
      fun i => piR (ℓ + 1) (auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess' i) fun _ => (univ ℓ : V),
      hM, ht, fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩
  | 1 =>
    exact ⟨ℓ + 1, auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess' t, fun _ => (univ ℓ : V),
      hMt, hx, fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩
  | _ + 2 => omega

/-- **An ih binder's domain at a tagged slot** is graded and valid, and
its body at every fitting telescope spine is in the elimination
level's universe. -/
theorem ihDomTag_facts {ℓ W w b nF o i l : Nat} (hbz : ℓ = 0 ↔ b = 0)
    {ρp : Nat → V} {M : V} {ms : List V} (hms : ms.length + 1 = o)
    {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i < nF)
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)}
    (hT : TagOk W ρp Idss) (hTV : SumFieldsValid ρp Idss)
    (hM : M ∈ˢ auxMotSp ℓ W w ρp Idss rss tlss Eiss' Fss₀ Ess')
    {tl : List (Nat × Nat × AnnotTerm)} {tgt : Nat} {Es : List AnnotTerm}
    (htlOk : FieldsOkB w (consList (fs.take i) ρp) (tl.map (·.2.2)))
    (htlV : FieldsValid (consList (fs.take i) ρp) (tl.map (·.2.2)))
    (hslot : ∀ bs : List V, SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) bs →
      (∀ E ∈ Es, WellDenotedV V (consList bs (consList (fs.take i) ρp)) E) ∧
      (∃ Ids, Idss[tgt]? = some Ids ∧
        SpineFit ρp Ids (Es.map (interp V (consList bs (consList (fs.take i) ρp))))) ∧
      AppChainOk (fs.getD i pt) bs ∧
      bs.foldl SetTheory.app (fs.getD i pt) ∈ˢ
        auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess'
          (inj tgt (mkTower (Es.map (interp V (consList bs (consList (fs.take i) ρp))) ++ [pt])))) :
    WellDenotedV V (consList ihs (consList fs (consList ms (cons M ρp))))
        (ihDomAVM 0 nF o i l (rebit b tl) [tagTupleAV W tgt (i + tl.length) Idss Es]) ∧
      ∀ bs : List V, SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) bs →
        interp V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))
          (AnnotTerm.mkAppN (.bvar (nF + o - 1 + l + tl.length))
            ([tagTupleAV W tgt (i + tl.length) Idss Es].map (ihIdxAtM nF o i l tl.length) ++
              [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + tl.length))
                (teleVarsAV tl.length)])) ∈ˢ (univ ℓ : V) := by
  have hbody : ∀ bs : List V, SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) bs →
      WellDenoted V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))
          (AnnotTerm.mkAppN (.bvar (nF + o - 1 + l + tl.length))
            ([tagTupleAV W tgt (i + tl.length) Idss Es].map (ihIdxAtM nF o i l tl.length) ++
              [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + tl.length)) (teleVarsAV tl.length)])) ∧
        AnnotValid V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))
          (AnnotTerm.mkAppN (.bvar (nF + o - 1 + l + tl.length))
            ([tagTupleAV W tgt (i + tl.length) Idss Es].map (ihIdxAtM nF o i l tl.length) ++
              [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + tl.length)) (teleVarsAV tl.length)])) ∧
        interp V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))
          (AnnotTerm.mkAppN (.bvar (nF + o - 1 + l + tl.length))
            ([tagTupleAV W tgt (i + tl.length) Idss Es].map (ihIdxAtM nF o i l tl.length) ++
              [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + tl.length))
                (teleVarsAV tl.length)])) ∈ˢ (univ ℓ : V) := by
    intro bs hsp
    obtain ⟨hEok, ⟨Ids, hIds, hspIdx⟩, hchainF, hxmem⟩ := hslot bs hsp
    have hlenBs : bs.length = tl.length := by rw [hsp.length_eq, List.length_map]
    have hfr : shiftE (i + tl.length) 0 (consList bs (consList (fs.take i) ρp)) = ρp := by
      rw [← consList_append, show i + tl.length = (fs.take i ++ bs).length from by
        rw [List.length_append, List.length_take, hlenBs]; omega, shiftE_consList]
    have htag := tagTupleAV_facts hT hIds hfr (fun E hE => (hEok E hE).1) hspIdx
    have ht : inj tgt (mkTower (Es.map (interp V (consList bs (consList (fs.take i) ρp))) ++ [pt]))
        ∈ˢ tagSet W ρp Idss := tagTuple_mem hT hIds hspIdx
    obtain ⟨hchain, huniv⟩ := auxMot_chain hM ht hxmem
    -- the casts from the telescope's length to the spine's
    have hcastE : ihIdxAtM nF o i l tl.length (tagTupleAV W tgt (i + tl.length) Idss Es)
        = ihIdxAtM nF o i l bs.length (tagTupleAV W tgt (i + tl.length) Idss Es) := by
      rw [hlenBs]
    have hcastV : teleVarsAV tl.length = teleVarsAV bs.length := by rw [hlenBs]
    have hcastF : nF - 1 - i + l + tl.length = nF - 1 - i + l + bs.length := by rw [hlenBs]
    have hcastM : nF + o - 1 + l + tl.length = nF + o - 1 + l + bs.length := by rw [hlenBs]
    have hE'v : interp V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l tl.length (tagTupleAV W tgt (i + tl.length) Idss Es))
          = inj tgt (mkTower (Es.map (interp V (consList bs (consList (fs.take i) ρp))) ++ [pt])) := by
      rw [hcastE, interp_ihIdxAtM hms hfs hihs (Nat.le_of_lt hi) bs _, htag.1]
    have hE'ok : WellDenoted V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l tl.length (tagTupleAV W tgt (i + tl.length) Idss Es)) := by
      rw [hcastE, WellDenoted_ihIdxAtM hms hfs hihs (Nat.le_of_lt hi) bs _]
      exact htag.2
    have hE'val : AnnotValid V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l tl.length (tagTupleAV W tgt (i + tl.length) Idss Es)) := by
      rw [hcastE, AnnotValid_ihIdxAtM hms hfs hihs (Nat.le_of_lt hi) bs _]
      exact tagTupleAV_validV hTV hIds hfr fun E hE => (hEok E hE).2
    have hvars : (teleVarsAV tl.length).map
        (interp V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))) = bs := by
      rw [hcastV]
      show ((List.range bs.length).map fun k => AnnotTerm.bvar (bs.length - 1 - k)).map
        (interp V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))) = bs
      exact map_fieldBvars_interp rfl _
    have hfv : interp V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))
        (.bvar (nF - 1 - i + l + tl.length)) = fs.getD i pt := by
      rw [interp_bvar, hcastF]
      exact ihFieldVar_at hfs hihs hi bs
    have hf := mkAppN_wellDenoted_of_chain (args := teleVarsAV tl.length)
      (f := (.bvar (nF - 1 - i + l + tl.length)))
      (σ := consList bs (consList ihs (consList fs (consList ms (cons M ρp))))) trivial
      (fun a ha => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
        exact trivial)
      (by rw [hvars, hfv]; exact hchainF)
    have hfval : interp V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))
        (AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + tl.length)) (teleVarsAV tl.length))
          = bs.foldl SetTheory.app (fs.getD i pt) := by
      rw [hf.2, hvars, hfv]
    have hMv : interp V (consList bs (consList ihs (consList fs (consList ms (cons M ρp)))))
        (.bvar (nF + o - 1 + l + tl.length)) = M := by
      rw [interp_bvar, hcastM]
      exact ihMotVar_at hms hfs hihs bs
    have hargsv : ([tagTupleAV W tgt (i + tl.length) Idss Es].map (ihIdxAtM nF o i l tl.length) ++
          [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + tl.length)) (teleVarsAV tl.length)]).map
        (interp V (consList bs (consList ihs (consList fs (consList ms (cons M ρp))))))
          = [inj tgt (mkTower (Es.map (interp V (consList bs (consList (fs.take i) ρp))) ++ [pt])),
             bs.foldl SetTheory.app (fs.getD i pt)] := by
      simp only [List.map_cons, List.map_nil, List.singleton_append]
      rw [hE'v, hfval]
    have happ := mkAppN_wellDenoted_of_chain
      (args := [tagTupleAV W tgt (i + tl.length) Idss Es].map (ihIdxAtM nF o i l tl.length) ++
        [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + tl.length)) (teleVarsAV tl.length)])
      (f := (.bvar (nF + o - 1 + l + tl.length)))
      (σ := consList bs (consList ihs (consList fs (consList ms (cons M ρp))))) trivial
      (fun a ha => by
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
          rw [List.mem_singleton] at hE
          subst hE
          exact hE'ok
        · rw [List.mem_singleton] at ha
          subst ha
          exact hf.1)
      (by rw [hargsv, hMv]; exact hchain)
    refine ⟨happ.1, ?_, ?_⟩
    · refine AnnotValid_mkAppN trivial fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
        rw [List.mem_singleton] at hE
        subst hE
        exact hE'val
      · rw [List.mem_singleton] at ha
        subst ha
        exact AnnotValid_mkAppN trivial fun a' ha' => by
          obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha'
          exact trivial
    · rw [happ.2, hargsv, hMv]
      exact huniv
  -- the telescope's spine, transported
  have hspTr : ∀ bs : List V,
      SpineFit (consList ihs (consList fs (consList ms (cons M ρp))))
        ((ihTeleAtR nF o i l (rebit b tl)).map (·.2.2)) bs →
      SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) bs := by
    intro bs hsp
    have h : SpineFit (consList ihs (consList fs (consList ms (cons M ρp))))
        ((ihTeleAtGo nF o i l ([] : List V).length tl).map (·.2.2)) bs := by
      show SpineFit _ ((ihTeleAtGo nF o i l 0 tl).map (·.2.2)) bs
      have : (ihTeleAtR nF o i l (rebit b tl)).map (·.2.2)
          = (ihTeleAtGo nF o i l 0 tl).map (·.2.2) := by
        show (ihTeleAtGo nF o i l 0 (rebit b tl)).map (·.2.2) = _
        rw [ihTeleAtGo_rebit, rebit_map_dom]
      rw [this] at hsp
      exact hsp
    exact (spineFit_ihTeleAtGo hms hfs hihs (Nat.le_of_lt hi) tl [] bs).mp h
  refine ⟨⟨?_, ?_⟩, fun bs hsp => (hbody bs hsp).2.2⟩
  · unfold ihDomAVM
    rw [rebit_length]
    refine WellDenoted_mkPisAV_of (w := w) ?_ fun bs hsp => (hbody bs (hspTr bs hsp)).1
    show FieldsOkB w _ ((ihTeleAtGo nF o i l 0 (rebit b tl)).map (·.2.2))
    rw [ihTeleAtGo_rebit, rebit_map_dom]
    exact fieldsOkB_ihTeleAtGo hms hfs hihs (Nat.le_of_lt hi) tl [] htlOk
  · unfold ihDomAVM
    rw [rebit_length]
    refine AnnotValid_mkPisAV_of (w := ℓ) ?_ ?_
      (fun bs hsp => (hbody bs (hspTr bs hsp)).2.1) ?_
    · intro d hd
      have hteq : ihTeleAtR nF o i l (rebit b tl) = rebit b (ihTeleAtGo nF o i l 0 tl) := by
        show ihTeleAtGo nF o i l 0 (rebit b tl) = _
        rw [ihTeleAtGo_rebit]
      have hd' : d ∈ rebit b (ihTeleAtGo nF o i l 0 tl) := by rwa [hteq] at hd
      rw [mem_rebit hd']
      exact hbz.symm
    · show FieldsValid _ ((ihTeleAtGo nF o i l 0 (rebit b tl)).map (·.2.2))
      rw [ihTeleAtGo_rebit, rebit_map_dom]
      exact fieldsValid_ihTeleAtGo hms hfs hihs (Nat.le_of_lt hi) tl [] htlV
    · intro h0 bs hsp
      have := (hbody bs (hspTr bs hsp)).2.2
      rw [h0, univ_zero] at this
      exact this

end ConLeche.Model
