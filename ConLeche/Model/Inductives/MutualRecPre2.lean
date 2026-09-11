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

/-! ## The minors: the ih tower -/

/-- **What one recursive slot provides** at a field spine: its
telescope is graded and valid, its index expression is the ONE tagged
tuple, whose value at every fitting telescope spine is a tag element,
and the field applied to the telescope's values lies in the auxiliary
fibre there. -/
def SlotTagOk (W w i : Nat) (ρp : Nat → V) (fs : List V) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss₀ Ess' : List (List AnnotTerm))
    (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) : Prop :=
  FieldsOkB w (consList (fs.take i) ρp) (tl.map (·.2.2)) ∧
  FieldsValid (consList (fs.take i) ρp) (tl.map (·.2.2)) ∧
  ∃ (tgt : Nat) (Es : List AnnotTerm),
    Eis = [tagTupleAV W tgt (i + tl.length) Idss Es] ∧
    ∀ bs : List V, SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) bs →
      (∀ E ∈ Es, WellDenotedV V (consList bs (consList (fs.take i) ρp)) E) ∧
      (∃ Ids, Idss[tgt]? = some Ids ∧
        SpineFit ρp Ids (Es.map (interp V (consList bs (consList (fs.take i) ρp))))) ∧
      AppChainOk (fs.getD i pt) bs ∧
      bs.foldl SetTheory.app (fs.getD i pt) ∈ˢ
        auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess'
          (inj tgt (mkTower (Es.map (interp V (consList bs (consList (fs.take i) ρp))) ++ [pt])))

/-- **An ih binder's domain lands in the minors' universe.** -/
theorem ihDomTag_univ {ℓ W w b nF o i l : Nat} (hbz : ℓ = 0 ↔ b = 0) (hw0 : w = 0 → ℓ = 0)
    {ρp : Nat → V} {M : V} {ms : List V} (hms : ms.length + 1 = o)
    {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l) (hi : i < nF)
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)}
    (hT : TagOk W ρp Idss)
    (hM : M ∈ˢ auxMotSp ℓ W w ρp Idss rss tlss Eiss' Fss₀ Ess')
    {tl : List (Nat × Nat × AnnotTerm)} {tgt : Nat} {Es : List AnnotTerm}
    (htlOk : FieldsOkB w (consList (fs.take i) ρp) (tl.map (·.2.2)))
    (hslot : ∀ bs : List V, SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) bs →
      (∀ E ∈ Es, WellDenotedV V (consList bs (consList (fs.take i) ρp)) E) ∧
      (∃ Ids, Idss[tgt]? = some Ids ∧
        SpineFit ρp Ids (Es.map (interp V (consList bs (consList (fs.take i) ρp))))) ∧
      AppChainOk (fs.getD i pt) bs ∧
      bs.foldl SetTheory.app (fs.getD i pt) ∈ˢ
        auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess'
          (inj tgt (mkTower (Es.map (interp V (consList bs (consList (fs.take i) ρp))) ++ [pt])))) :
    interp V (consList ihs (consList fs (consList ms (cons M ρp))))
        (ihDomAVM 0 nF o i l (rebit b tl) [tagTupleAV W tgt (i + tl.length) Idss Es])
      ∈ˢ (univ (if ℓ = 0 then 0 else Nat.max w ℓ) : V) := by
  have hval : interp V (consList ihs (consList fs (consList ms (cons M ρp))))
      (ihDomAVM 0 nF o i l (rebit b tl) [tagTupleAV W tgt (i + tl.length) Idss Es])
      = piTele ℓ (teleOfFields (consList (fs.take i) ρp) (tl.map (·.2.2)))
          (fun as => SetTheory.app
            (([tagTupleAV W tgt (i + tl.length) Idss Es].map
              (interp V (consList as (consList (fs.take i) ρp)))).foldl SetTheory.app M)
            (as.foldl SetTheory.app (fs.getD i pt))) [] := by
    have h := interp_ihDomAV (ℓ := ℓ) (o := o) (i := i) (l := l) (ms := ms) (M := M) (ρp := ρp)
      (fs := fs) (ihs := ihs) hms hfs hihs hi
      (tl := rebit b tl) (fun d hd => by rw [mem_rebit hd]; exact hbz.symm)
      [tagTupleAV W tgt (i + tl.length) Idss Es]
    rwa [rebit_map_dom] at h
  have hB : ∀ as : List V, SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) as →
      SetTheory.app
        (([tagTupleAV W tgt (i + tl.length) Idss Es].map
          (interp V (consList as (consList (fs.take i) ρp)))).foldl SetTheory.app M)
        (as.foldl SetTheory.app (fs.getD i pt)) ∈ˢ (univ ℓ : V) := by
    intro as hsp
    obtain ⟨hEok, ⟨Ids, hIds, hspIdx⟩, -, hxmem⟩ := hslot as hsp
    have hlenAs : as.length = tl.length := by rw [hsp.length_eq, List.length_map]
    have hfr : shiftE (i + tl.length) 0 (consList as (consList (fs.take i) ρp)) = ρp := by
      rw [← consList_append, show i + tl.length = (fs.take i ++ as).length from by
        rw [List.length_append, List.length_take, hlenAs]; omega, shiftE_consList]
    have htag := tagTupleAV_facts hT hIds hfr (fun E hE => (hEok E hE).1) hspIdx
    have ht := tagTuple_mem hT hIds hspIdx
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [htag.1]
    exact (auxMot_chain hM ht hxmem).2
  rw [hval]
  by_cases h0 : ℓ = 0
  · rw [if_pos h0, univ_zero, h0]
    refine piTele_zero_mem_univZero fun as hfit => ?_
    rw [List.nil_append]
    have := hB as (fitsS_teleOfFields.mp hfit)
    rwa [h0, univ_zero] at this
  · rw [if_neg h0]
    refine piTele_mem_univ_max (u := w) (v := ℓ) (fun hw => h0 (hw0 hw)) h0 _ htlOk
      fun as hsp => ?_
    rw [List.nil_append]
    exact univ_mono (Nat.le_max_right w ℓ) _ (hB as hsp)

/-- **The ih binders' Π-tower at tagged slots**: graded, valid, and in
the minors' universe. -/
theorem ihPisTag_facts {ℓ W w b nF o : Nat} (hbz : ℓ = 0 ↔ b = 0) (hw0 : w = 0 → ℓ = 0)
    {ρp : Nat → V} {M : V} {ms : List V} (hms : ms.length + 1 = o)
    {fs : List V} (hfs : fs.length = nF)
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)}
    (hT : TagOk W ρp Idss) (hTV : SumFieldsValid ρp Idss)
    (hM : M ∈ˢ auxMotSp ℓ W w ρp Idss rss tlss Eiss' Fss₀ Ess')
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)} :
    ∀ (is : List Nat) (l : Nat) (ihs : List V) (body : AnnotTerm),
      ihs.length = l → (∀ i ∈ is, i < nF) →
      (∀ i ∈ is,
        SlotTagOk W w i ρp fs Idss rss tlss Eiss' Fss₀ Ess' (tls.getD i []) (Eiss.getD i [])) →
      (∀ ihs' : List V, ihs'.length = l + is.length →
        WellDenotedV V (consList ihs' (consList fs (consList ms (cons M ρp)))) body ∧
        interp V (consList ihs' (consList fs (consList ms (cons M ρp)))) body
          ∈ˢ (univ (if ℓ = 0 then 0 else Nat.max w ℓ) : V)) →
      WellDenotedV V (consList ihs (consList fs (consList ms (cons M ρp))))
          (ihPisAVM (fun _ => 0) nF o b tls Eiss is l body) ∧
        interp V (consList ihs (consList fs (consList ms (cons M ρp))))
          (ihPisAVM (fun _ => 0) nF o b tls Eiss is l body)
            ∈ˢ (univ (if ℓ = 0 then 0 else Nat.max w ℓ) : V)
  | [], l, ihs, body, hihs, _, _, hbody => by
    show WellDenotedV V _ body ∧ _
    exact hbody ihs (by simp [hihs])
  | i :: is, l, ihs, body, hihs, hlt, hslots, hbody => by
    have hi : i < nF := hlt i List.mem_cons_self
    obtain ⟨htlOk, htlV, tgt, Es, hEq, hslot⟩ := hslots i List.mem_cons_self
    have hdom := ihDomTag_facts (b := b) (o := o) (l := l) hbz hms hfs hihs hi hT hTV hM
      htlOk htlV hslot
    have hdomU := ihDomTag_univ (b := b) (o := o) (l := l) hbz hw0 hms hfs hihs hi hT hM
      htlOk hslot
    have hstep : ∀ x : V,
        x ∈ˢ interp V (consList ihs (consList fs (consList ms (cons M ρp))))
          (ihDomAVM 0 nF o i l (rebit b (tls.getD i [])) (Eiss.getD i [])) →
        WellDenotedV V (consList (ihs ++ [x]) (consList fs (consList ms (cons M ρp))))
            (ihPisAVM (fun _ => 0) nF o b tls Eiss is (l + 1) body) ∧
          interp V (consList (ihs ++ [x]) (consList fs (consList ms (cons M ρp))))
            (ihPisAVM (fun _ => 0) nF o b tls Eiss is (l + 1) body)
              ∈ˢ (univ (if ℓ = 0 then 0 else Nat.max w ℓ) : V) := by
      intro x _
      refine ihPisTag_facts hbz hw0 hms hfs hT hTV hM is (l + 1) (ihs ++ [x]) body
        (by simp [hihs]) (fun i' hi' => hlt i' (List.mem_cons_of_mem _ hi'))
        (fun i' hi' => hslots i' (List.mem_cons_of_mem _ hi')) ?_
      intro ihs' hl
      exact hbody ihs' (by rw [hl, List.length_cons]; omega)
    show (WellDenoted V _ (.pi 0 b _ _) ∧ AnnotValid V _ (.pi 0 b _ _)) ∧ _
    rw [hEq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [WellDenoted_pi]
      refine ⟨hdom.1.1, fun x hx => ?_⟩
      rw [consList_snoc']
      exact ((hstep x (by rw [hEq]; exact hx)).1).1
    · rw [AnnotValid_pi]
      refine ⟨hdom.1.2, fun x hx => ?_, fun hb0 x hx => ?_⟩
      · rw [consList_snoc']
        exact ((hstep x (by rw [hEq]; exact hx)).1).2
      · have h0 : ℓ = 0 := hbz.mpr hb0
        have := (hstep x (by rw [hEq]; exact hx)).2
        rw [if_pos h0, univ_zero] at this
        rw [consList_snoc']
        exact this
    · rw [show ihPisAVM (fun _ => 0) nF o b tls Eiss (i :: is) l body
        = .pi 0 b (ihDomAVM 0 nF o i l (rebit b (tls.getD i [])) (Eiss.getD i []))
            (ihPisAVM (fun _ => 0) nF o b tls Eiss is (l + 1) body) from rfl, hEq, interp_pi]
      by_cases h0 : ℓ = 0
      · rw [if_pos h0, univ_zero, hbz.mp h0]
        exact piR_zero_mem_univZero
      · have hb0 : b ≠ 0 := fun h => h0 (hbz.mpr h)
        rw [if_neg h0, piR_congr_bit (show b = 0 ↔ Nat.max w ℓ = 0 from
          ⟨fun h => absurd h hb0, fun h => absurd h (max_ne_zero_right (u := w) h0)⟩)]
        have hdomU' : interp V (consList ihs (consList fs (consList ms (cons M ρp))))
            (ihDomAVM 0 nF o i l (rebit b (tls.getD i []))
              [tagTupleAV W tgt (i + (tls.getD i []).length) Idss Es])
              ∈ˢ (univ (Nat.max w ℓ) : V) := by
          have h := hdomU
          rwa [if_neg h0] at h
        have hstep' : ∀ x : V, x ∈ˢ interp V (consList ihs (consList fs (consList ms (cons M ρp))))
              (ihDomAVM 0 nF o i l (rebit b (tls.getD i []))
                [tagTupleAV W tgt (i + (tls.getD i []).length) Idss Es]) →
            interp V (cons x (consList ihs (consList fs (consList ms (cons M ρp)))))
              (ihPisAVM (fun _ => 0) nF o b tls Eiss is (l + 1) body)
                ∈ˢ (univ (Nat.max w ℓ) : V) := by
          intro x hx
          have h := (hstep x (by rw [hEq]; exact hx)).2
          rw [if_neg h0] at h
          rw [consList_snoc']
          exact h
        have h := piR_mem_univ (u := Nat.max w ℓ) (v := Nat.max w ℓ) hdomU' hstep'
        rwa [if_neg (max_ne_zero_right (u := w) h0),
          show Nat.max (Nat.max w ℓ) (Nat.max w ℓ) = Nat.max w ℓ from Nat.max_self _] at h

/-! ## The minors: the conclusion -/

/-- **The constructor leaf at the block's variables reads its value**
(the `ctorValI` half of `interp_minorConcAV`, on its own). -/
theorem interp_ctorAppAV {m : EnvModel V env} {ψ : Name → Nat} {C : Name} {nP nF w j o : Nat}
    {ρp : Nat → V} {ms : List V} {M : V} (hms : ms.length + 1 = o)
    {ds : List (Nat × Nat × AnnotTerm)} (hlenDs : ds.length = nP + nF)
    {Fss : List (List AnnotTerm)}
    (hleafC : m.acval C ψ = sumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss))
    (hclC : Term.bvarsBelow 0 (m.acval C ψ).erase)
    (hFsj : Fss[j]? = some ((ds.drop nP).map (·.2.2)))
    (hokB : SumFieldsOkB w ρp Fss)
    (hsatC : Sat V (((ds.take nP).map (·.2.2)).reverse) ρp)
    {as : List V} (hsp : SpineFit ρp ((ds.drop nP).map (·.2.2)) as) :
    interp V (consList as (consList ms (cons M ρp)))
        (AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF))
      = ctorValI w j as := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hlenAs : as.length = nF := by rw [hsp.length_eq, hlenFs]
  have hσ : ∀ k, consList as (consList ms (cons M ρp)) (k + (o + nF)) = ρp k := by
    intro k
    rw [show k + (o + nF) = (k + o) + as.length from by omega, consList_apply_add,
      show k + o = (k + 1) + ms.length from by omega, consList_apply_add]
    rfl
  have hleafC' : m.acval C ψ
      = sumMkAV w j (ds.take nP ++ ds.drop nP) ((ds.drop nP).map (·.2.2)) (uChains Fss) := by
    rw [hleafC, List.take_append_drop]
  rw [interp_mkAppN,
    ← List.foldl_map (f := interp V (consList as (consList ms (cons M ρp)))) (g := SetTheory.app),
    List.map_append, show nP + o + nF = nP + (o + nF) from by omega,
    map_paramBvarsAt_interp hσ,
    show fieldBvars nF = (List.range nF).map (fun k => AnnotTerm.bvar (nF - 1 - k)) from rfl,
    map_fieldBvars_interp hlenAs, interp_closed (V := V) hclC _ (fun k => ρp (k + nP)), hleafC']
  have hlenP' : ((((ds.take nP).map (·.2.2)))).length = nP := by simp [hlenDs]
  have hsp₁ := spineFit_of_sat (Δ₀ := []) (Ds := (ds.take nP).map (·.2.2))
    (by rw [List.append_nil]; exact hsatC)
  rw [hlenP'] at hsp₁
  unfold ctorValI
  rcases Nat.eq_zero_or_pos w with hw0 | hwpos
  · rw [hw0, sumMkAV_zero, foldl_app_pt_sum, if_pos rfl]
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
    rw [sumMkAV_fold hw' hsp₁ (by rw [consList_range_reverse]; exact hsp)
      (by rw [consList_range_reverse]; exact SumFieldsOkB_uChains hokB)
      (by rw [uChains_getElem?, hFsj]; rfl), if_neg hw']

/-- **The minor's conclusion at a tagged constructor**: the motive at
the tagged index tuple, applied to the constructor's value — graded,
valid, and in the elimination level's universe. -/
theorem minorConcTag_facts {m : EnvModel V env} {ψ : Name → Nat} {C : Name}
    {ℓ W w nP nF o mem : Nat} {ρp : Nat → V} {M : V} {ms : List V} (hms : ms.length + 1 = o)
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)}
    (hT : TagOk W ρp Idss) (hTV : SumFieldsValid ρp Idss)
    (hM : M ∈ˢ auxMotSp ℓ W w ρp Idss rss tlss Eiss' Fss₀ Ess')
    {ds : List (Nat × Nat × AnnotTerm)} (hlenDs : ds.length = nP + nF) {Es₀ : List AnnotTerm}
    (hEs : ∀ fs : List V, SpineFit ρp ((ds.drop nP).map (·.2.2)) fs →
      (∀ E ∈ Es₀, WellDenotedV V (consList fs ρp) E) ∧
      ∃ Ids, Idss[mem]? = some Ids ∧ SpineFit ρp Ids (Es₀.map (interp V (consList fs ρp))))
    (hctorOk : ∀ fs : List V, SpineFit ρp ((ds.drop nP).map (·.2.2)) fs →
      WellDenotedV V (consList fs (consList ms (cons M ρp)))
        (AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)))
    (hctorVal : ∀ fs : List V, SpineFit ρp ((ds.drop nP).map (·.2.2)) fs →
      interp V (consList fs (consList ms (cons M ρp)))
          (AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF))
        ∈ˢ auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess'
            (inj mem (mkTower (Es₀.map (interp V (consList fs ρp)) ++ [pt]))))
    {fs : List V} (hsp : SpineFit ρp ((ds.drop nP).map (·.2.2)) fs) :
    WellDenotedV V (consList fs (consList ms (cons M ρp)))
        (AnnotTerm.mkAppN (.bvar (nF + o - 1))
          (([tagTupleAV W mem nF Idss Es₀].map fun E => E.liftN o nF) ++
            [AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)])) ∧
      interp V (consList fs (consList ms (cons M ρp)))
        (AnnotTerm.mkAppN (.bvar (nF + o - 1))
          (([tagTupleAV W mem nF Idss Es₀].map fun E => E.liftN o nF) ++
            [AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)]))
          ∈ˢ (univ ℓ : V) := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hlenAs : fs.length = nF := by rw [hsp.length_eq, hlenFs]
  have hshM : shiftE o 0 (consList ms (cons M ρp)) = ρp := by
    rw [← hms]; exact shiftE_minors rfl
  have hshF : shiftE o nF (consList fs (consList ms (cons M ρp))) = consList fs ρp := by
    rw [← hlenAs, shiftE_consList_len, hshM]
  obtain ⟨hEok, Ids, hIds, hspIdx⟩ := hEs fs hsp
  have hfrT : shiftE nF 0 (consList fs ρp) = ρp := by rw [← hlenAs]; exact shiftE_consList fs ρp
  have htag := tagTupleAV_facts hT hIds hfrT (fun E hE => (hEok E hE).1) hspIdx
  have ht := tagTuple_mem hT hIds hspIdx
  obtain ⟨hchain, huniv⟩ := auxMot_chain hM ht (hctorVal fs hsp)
  have hMval : consList fs (consList ms (cons M ρp)) (nF + o - 1) = M := by
    rw [show nF + o - 1 = (o - 1) + fs.length from by omega, consList_apply_add,
      show o - 1 = 0 + ms.length from by omega, consList_apply_add]
    rfl
  have hE1ok : WellDenotedV V (consList fs (consList ms (cons M ρp)))
      ((tagTupleAV W mem nF Idss Es₀).liftN o nF) := by
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_liftN, hshF]; exact htag.2
    · rw [AnnotValid_liftN, hshF]
      exact tagTupleAV_validV hTV hIds hfrT fun E hE => (hEok E hE).2
  have hE1v : interp V (consList fs (consList ms (cons M ρp)))
      ((tagTupleAV W mem nF Idss Es₀).liftN o nF)
      = inj mem (mkTower (Es₀.map (interp V (consList fs ρp)) ++ [pt])) := by
    rw [interp_liftN, hshF, htag.1]
  have hargsv : (([tagTupleAV W mem nF Idss Es₀].map fun E => E.liftN o nF) ++
        [AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)]).map
      (interp V (consList fs (consList ms (cons M ρp))))
      = [inj mem (mkTower (Es₀.map (interp V (consList fs ρp)) ++ [pt])),
         interp V (consList fs (consList ms (cons M ρp)))
           (AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF))] := by
    simp only [List.map_cons, List.map_nil, List.singleton_append]
    rw [hE1v]
  have happ := mkAppN_wellDenoted_of_chain
    (args := ([tagTupleAV W mem nF Idss Es₀].map fun E => E.liftN o nF) ++
      [AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)])
    (f := (.bvar (nF + o - 1)))
    (σ := consList fs (consList ms (cons M ρp))) trivial
    (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
        rw [List.mem_singleton] at hE
        subst hE
        exact hE1ok.1
      · rw [List.mem_singleton] at ha
        subst ha
        exact (hctorOk fs hsp).1)
    (by rw [hargsv, interp_bvar, hMval]; exact hchain)
  refine ⟨⟨happ.1, ?_⟩, ?_⟩
  · refine AnnotValid_mkAppN trivial fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_singleton] at hE
      subst hE
      exact hE1ok.2
    · rw [List.mem_singleton] at ha
      subst ha
      exact (hctorOk fs hsp).2
  · rw [happ.2, hargsv, interp_bvar, hMval]
    exact huniv

/-! ## The minors -/

omit [SetTheory V] in
/-- Lifted binder data's domains are the lifted domains. -/
theorem liftDoms_map_dom (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k : Nat),
      (liftDoms n k ds).map (·.2.2) = liftFields n k (ds.map (·.2.2))
  | [], _ => rfl
  | d :: ds, k => by
    simp only [liftDoms, List.map_cons, liftFields_cons, liftDoms_map_dom n ds (k + 1)]

/-- A graded field chain stays graded in a bigger universe (the bound
moves up; the zero regime has none). -/
theorem FieldsOkB_mono {u u' : Nat} (hu : u ≠ 0) (hle : u ≤ u') :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsOkB u ρ Fs → FieldsOkB u' ρ Fs
  | [], _, _ => trivial
  | _ :: _, _, h =>
    ⟨h.1, fun _ => univ_mono hle _ (h.2.1 hu), fun a ha => FieldsOkB_mono hu hle (h.2.2 a ha)⟩

/-- **A minor premise's domain at a tagged constructor**: graded,
valid, and in the minors' universe `if ℓ = 0 then 0 else max w ℓ`. -/
theorem minorTag_facts {m : EnvModel V env} {ψ : Name → Nat} {C : Name}
    {ℓ W w b nP nF j mem : Nat} (hbz : ℓ = 0 ↔ b = 0) (hw0 : w = 0 → ℓ = 0)
    {ρp : Nat → V} {M : V} {ms : List V} (hlenM : ms.length = j)
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)}
    (hT : TagOk W ρp Idss) (hTV : SumFieldsValid ρp Idss)
    (hM : M ∈ˢ auxMotSp ℓ W w ρp Idss rss tlss Eiss' Fss₀ Ess')
    {ds : List (Nat × Nat × AnnotTerm)} (hlenDs : ds.length = nP + nF)
    (hFok : FieldsOkB w ρp ((ds.drop nP).map (·.2.2)))
    (hFV : FieldsValid ρp ((ds.drop nP).map (·.2.2)))
    {Es₀ : List AnnotTerm}
    (hEs : ∀ fs : List V, SpineFit ρp ((ds.drop nP).map (·.2.2)) fs →
      (∀ E ∈ Es₀, WellDenotedV V (consList fs ρp) E) ∧
      ∃ Ids, Idss[mem]? = some Ids ∧ SpineFit ρp Ids (Es₀.map (interp V (consList fs ρp))))
    (hctorOk : ∀ fs : List V, SpineFit ρp ((ds.drop nP).map (·.2.2)) fs →
      WellDenotedV V (consList fs (consList ms (cons M ρp)))
        (AnnotTerm.mkAppN (m.acval C ψ)
          (paramBvarsAt nP (nP + (1 + j) + nF) ++ fieldBvars nF)))
    (hctorVal : ∀ fs : List V, SpineFit ρp ((ds.drop nP).map (·.2.2)) fs →
      interp V (consList fs (consList ms (cons M ρp)))
          (AnnotTerm.mkAppN (m.acval C ψ)
            (paramBvarsAt nP (nP + (1 + j) + nF) ++ fieldBvars nF))
        ∈ˢ auxFib W w ρp Idss rss tlss Eiss' Fss₀ Ess'
            (inj mem (mkTower (Es₀.map (interp V (consList fs ρp)) ++ [pt]))))
    (hslots : ∀ fs : List V, SpineFit ρp ((ds.drop nP).map (·.2.2)) fs →
      ∀ i ∈ recIdx (rss.getD j []) nF,
        SlotTagOk W w i ρp fs Idss rss tlss Eiss' Fss₀ Ess'
          ((tlss.getD j []).getD i []) ((Eiss'.getD j []).getD i [])) :
    WellDenotedV V (consList ms (cons M ρp))
        (minorAVAtR m C ψ nP nF b (1 + j) ds [tagTupleAV W mem nF Idss Es₀]
          (recIdx (rss.getD j []) nF) (tlss.getD j []) (Eiss'.getD j [])) ∧
      interp V (consList ms (cons M ρp))
        (minorAVAtR m C ψ nP nF b (1 + j) ds [tagTupleAV W mem nF Idss Es₀]
          (recIdx (rss.getD j []) nF) (tlss.getD j []) (Eiss'.getD j []))
          ∈ˢ (univ (if ℓ = 0 then 0 else Nat.max w ℓ) : V) := by
  have ho : ms.length + 1 = 1 + j := by omega
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hshM : shiftE (1 + j) 0 (consList ms (cons M ρp)) = ρp := by
    rw [← ho]; exact shiftE_minors rfl
  have hdomsOk : FieldsOkB w (consList ms (cons M ρp))
      ((rebit b (liftDoms (1 + j) 0 (ds.drop nP))).map (·.2.2)) := by
    rw [rebit_map_dom, liftDoms_map_dom]
    exact FieldsOkB_liftFields.mpr (by rw [hshM]; exact hFok)
  have hdomsV : FieldsValid (consList ms (cons M ρp))
      ((rebit b (liftDoms (1 + j) 0 (ds.drop nP))).map (·.2.2)) := by
    rw [rebit_map_dom, liftDoms_map_dom]
    exact FieldsValid_liftFields.mpr (by rw [hshM]; exact hFV)
  have hspTr : ∀ fs : List V,
      SpineFit (consList ms (cons M ρp))
        ((rebit b (liftDoms (1 + j) 0 (ds.drop nP))).map (·.2.2)) fs →
      SpineFit ρp ((ds.drop nP).map (·.2.2)) fs := by
    intro fs hsp
    rw [rebit_map_dom, liftDoms_map_dom, spineFit_liftFields, hshM] at hsp
    exact hsp
  have hbodyFacts : ∀ fs : List V, SpineFit ρp ((ds.drop nP).map (·.2.2)) fs →
      WellDenotedV V (consList fs (consList ms (cons M ρp)))
          (ihPisAVM (fun _ => 0) nF (1 + j) b (tlss.getD j []) (Eiss'.getD j [])
            (recIdx (rss.getD j []) nF) 0
            ((AnnotTerm.mkAppN (.bvar (nF + (1 + j) - 1))
              (([tagTupleAV W mem nF Idss Es₀].map fun E => E.liftN (1 + j) nF) ++
                [AnnotTerm.mkAppN (m.acval C ψ)
                  (paramBvarsAt nP (nP + (1 + j) + nF) ++ fieldBvars nF)])).liftN
              (recIdx (rss.getD j []) nF).length 0)) ∧
        interp V (consList fs (consList ms (cons M ρp)))
          (ihPisAVM (fun _ => 0) nF (1 + j) b (tlss.getD j []) (Eiss'.getD j [])
            (recIdx (rss.getD j []) nF) 0
            ((AnnotTerm.mkAppN (.bvar (nF + (1 + j) - 1))
              (([tagTupleAV W mem nF Idss Es₀].map fun E => E.liftN (1 + j) nF) ++
                [AnnotTerm.mkAppN (m.acval C ψ)
                  (paramBvarsAt nP (nP + (1 + j) + nF) ++ fieldBvars nF)])).liftN
              (recIdx (rss.getD j []) nF).length 0))
            ∈ˢ (univ (if ℓ = 0 then 0 else Nat.max w ℓ) : V) := by
    intro fs hsp
    have hlenAs : fs.length = nF := by rw [hsp.length_eq, hlenFs]
    refine ihPisTag_facts hbz hw0 ho hlenAs hT hTV hM (recIdx (rss.getD j []) nF) 0 [] _ rfl
      (fun i hi => (mem_recIdx.mp hi).1) (hslots fs hsp) ?_
    intro ihs' hl
    rw [Nat.zero_add] at hl
    have hsh : shiftE (recIdx (rss.getD j []) nF).length 0
        (consList ihs' (consList fs (consList ms (cons M ρp))))
        = consList fs (consList ms (cons M ρp)) := by
      rw [← hl]; exact shiftE_consList ihs' _
    obtain ⟨hcOk, hcU⟩ := minorConcTag_facts ho hT hTV hM hlenDs hEs hctorOk hctorVal hsp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [WellDenoted_liftN, hsh]; exact hcOk.1
    · rw [AnnotValid_liftN, hsh]; exact hcOk.2
    · rw [interp_liftN, hsh]
      by_cases h0 : ℓ = 0
      · rw [if_pos h0, ← h0]; exact hcU
      · rw [if_neg h0]; exact univ_mono (Nat.le_max_right w ℓ) _ hcU
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold minorAVAtR minorAVAtRM
    exact WellDenoted_mkPisAV_of (w := w) hdomsOk
      fun fs hsp => ((hbodyFacts fs (hspTr fs hsp)).1).1
  · unfold minorAVAtR minorAVAtRM
    refine AnnotValid_mkPisAV_of (w := ℓ) (fun d hd => by rw [mem_rebit hd]; exact hbz.symm)
      hdomsV (fun fs hsp => ((hbodyFacts fs (hspTr fs hsp)).1).2) ?_
    intro h0 fs hsp
    have h := (hbodyFacts fs (hspTr fs hsp)).2
    rwa [if_pos h0, univ_zero] at h
  · unfold minorAVAtR minorAVAtRM
    by_cases h0 : ℓ = 0
    · rw [if_pos h0, univ_zero]
      refine interp_mkPisAV_mem_univZero (fun d hd => by rw [mem_rebit hd]; exact hbz.mp h0) ?_
      intro hnil
      have hsp0 : SpineFit (consList ms (cons M ρp))
          ((rebit b (liftDoms (1 + j) 0 (ds.drop nP))).map (·.2.2)) [] := by
        rw [hnil]; trivial
      have h := (hbodyFacts [] (hspTr [] hsp0)).2
      rw [if_pos h0, univ_zero] at h
      exact h
    · rw [if_neg h0]
      have hw : w ≠ 0 := fun hw => h0 (hw0 hw)
      refine interp_mkPisAV_mem_univ (t := Nat.max w ℓ) (max_ne_zero_right (u := w) h0)
        (fun d hd => by rw [mem_rebit hd]; exact fun h => h0 (hbz.mpr h))
        (FieldsOkB_mono hw (Nat.le_max_left w ℓ) hdomsOk) fun fs hsp => ?_
      have h := (hbodyFacts fs (hspTr fs hsp)).2
      rwa [if_neg h0] at h

/-! ## Assembly: the binder data's entries, along the walk -/

/-- The binder data's entries along every fitting walk: graded, valid,
and (in the graph regime) in the recursor's sort. -/
def EntriesOk (V : Type w) [SetTheory V] (s : Nat) :
    (Nat → V) → List (Nat × Nat × AnnotTerm) → Prop
  | _, [] => True
  | ρ, d :: ds => WellDenotedV V ρ d.2.2 ∧ (s ≠ 0 → interp V ρ d.2.2 ∈ˢ (univ s : V)) ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 → EntriesOk V s (cons a ρ) ds

theorem entriesOk_append {s : Nat} :
    ∀ {ds₁ ds₂ : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}, EntriesOk V s ρ ds₁ →
      (∀ as : List V, SpineFit ρ (ds₁.map (·.2.2)) as → EntriesOk V s (consList as ρ) ds₂) →
      EntriesOk V s ρ (ds₁ ++ ds₂)
  | [], _, _, _, h => by simpa using h [] trivial
  | d :: ds₁, ds₂, ρ, h, h₂ => by
    refine ⟨h.1, h.2.1, fun a ha => entriesOk_append (h.2.2 a ha) fun as hsp => ?_⟩
    have h' := h₂ (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at h'

theorem EntriesOk.fieldsOkB {s : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}, EntriesOk V s ρ ds →
      FieldsOkB s ρ (ds.map (·.2.2))
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1.1, h.2.1, fun a ha => EntriesOk.fieldsOkB (h.2.2 a ha)⟩

theorem EntriesOk.fieldsValid {s : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}, EntriesOk V s ρ ds →
      FieldsValid ρ (ds.map (·.2.2))
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1.2, fun a ha => EntriesOk.fieldsValid (h.2.2 a ha)⟩

/-- An entry's facts at a fitting prefix spine. -/
theorem entriesOk_at {s : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}, EntriesOk V s ρ ds →
      ∀ (k : Nat) (d : Nat × Nat × AnnotTerm), ds[k]? = some d →
        ∀ as : List V, SpineFit ρ ((ds.map (·.2.2)).take k) as →
          WellDenotedV V (consList as ρ) d.2.2 ∧
            (s ≠ 0 → interp V (consList as ρ) d.2.2 ∈ˢ (univ s : V))
  | [], _, _, _, _, hk, _, _ => nomatch hk
  | d' :: ds, ρ, h, 0, d, hk, as, hsp => by
    obtain rfl := Option.some.inj hk
    match as, hsp with
    | [], _ => exact ⟨h.1, h.2.1⟩
    | _ :: _, hsp => exact hsp.elim
  | d' :: ds, ρ, h, k + 1, d, hk, as, hsp => by
    match as, hsp with
    | [], hsp => exact hsp.elim
    | a :: as, hsp =>
      have h' := entriesOk_at (h.2.2 a hsp.1) k d (by simpa using hk) as hsp.2
      rwa [← consList_cons] at h'

/-- The entries' facts in `okΓ`'s prefix form. -/
theorem prefix_of_entriesOk {s : Nat} {rds : List (Nat × Nat × AnnotTerm)}
    (h : ∀ ρb : Nat → V, EntriesOk V s ρb rds) :
    ∀ (k : Nat) (d : Nat × Nat × AnnotTerm), rds[k]? = some d → ∀ σ : Nat → V,
      Sat V (((rds.take k).map (·.2.2)).reverse) σ →
      WellDenotedV V σ d.2.2 ∧ (s ≠ 0 → interp V σ d.2.2 ∈ˢ (univ s : V)) := by
  intro k d hk σ hσ
  have hkl : k < rds.length := (List.getElem?_eq_some_iff.mp hk).1
  have hL : (((rds.take k).map (·.2.2))).length = k := by
    rw [List.length_map, List.length_take]; omega
  have hsp := spineFit_of_sat (Ds := (rds.take k).map (·.2.2)) (Δ₀ := []) (ρ := σ)
    (by rw [List.append_nil]; exact hσ)
  rw [hL] at hsp
  have hcl := consList_range_reverse k σ
  have h' := entriesOk_at (h (fun i => σ (i + k))) k d hk ((List.range k).reverse.map σ)
    (by rw [← List.map_take]; exact hsp)
  rwa [hcl] at h'

/-- The minor block's entries, from the per-datum facts. -/
theorem entriesOk_fixMinorsData {m : EnvModel V env} {ψ : Name → Nat} {s nP b : Nat} {M : V}
    {ρp : Nat → V} :
    ∀ (cds : List CtorDatumR) (o off : Nat) (ms : List V), ms.length = off →
      (∀ (i : Nat) (cd : CtorDatumR), cds[i]? = some cd → ∀ ms' : List V, ms'.length = off + i →
        WellDenotedV V (consList ms' (cons M ρp))
          (minorAVAtR m cd.1 ψ nP cd.2.1 b (o + i) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1
            cd.2.2.2.2.2.2 cd.2.2.2.2.2.1) ∧
        (s ≠ 0 → interp V (consList ms' (cons M ρp))
          (minorAVAtR m cd.1 ψ nP cd.2.1 b (o + i) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1
            cd.2.2.2.2.2.2 cd.2.2.2.2.2.1) ∈ˢ (univ s : V))) →
      EntriesOk V s (consList ms (cons M ρp)) (fixMinorsData m ψ nP b cds o)
  | [], _, _, _, _, _ => trivial
  | (C, nF, ds, Es, ris, Eiss, tls) :: cs, o, off, ms, hms, h => by
    obtain ⟨hok, huniv⟩ := h 0 _ rfl ms (by omega)
    refine ⟨hok, huniv, fun a _ => ?_⟩
    rw [consList_snoc']
    refine entriesOk_fixMinorsData cs (o + 1) (off + 1) (ms ++ [a]) (by simp [hms]) ?_
    intro i cd hcd ms' hlen
    have h' := h (i + 1) cd (by simpa using hcd) ms' (by omega)
    rwa [show o + (i + 1) = o + 1 + i from by omega] at h'

/-! ## Assembly: the recursor's sort -/

/-- **The auxiliary recursor's sort**: zero at a `Prop` elimination,
and otherwise the join of the parameters' levels, the tag's, the
block's and the elimination level's successor. -/
@[expose] def auxRecSort (p W w ℓ : Nat) : Nat :=
  if ℓ = 0 then 0 else Nat.max (Nat.max p W) (Nat.max w (ℓ + 1))

theorem auxRecSort_zero_iff (p W w ℓ : Nat) : auxRecSort p W w ℓ = 0 ↔ ℓ = 0 := by
  unfold auxRecSort
  by_cases h0 : ℓ = 0
  · rw [if_pos h0]; exact ⟨fun _ => h0, fun _ => rfl⟩
  · rw [if_neg h0]
    refine ⟨fun h => absurd h ?_, fun h => absurd h h0⟩
    exact max_ne_zero_right (u := Nat.max p W) (max_ne_zero_right (u := w) (Nat.succ_ne_zero ℓ))

theorem auxRecSort_ge (p W w ℓ : Nat) (h0 : ℓ ≠ 0) :
    p ≤ auxRecSort p W w ℓ ∧ W ≤ auxRecSort p W w ℓ ∧ w ≤ auxRecSort p W w ℓ ∧
      ℓ + 1 ≤ auxRecSort p W w ℓ := by
  unfold auxRecSort
  rw [if_neg h0]
  exact ⟨Nat.le_trans (Nat.le_max_left p W) (Nat.le_max_left _ _),
    Nat.le_trans (Nat.le_max_right p W) (Nat.le_max_left _ _),
    Nat.le_trans (Nat.le_max_left w (ℓ + 1)) (Nat.le_max_right _ _),
    Nat.le_trans (Nat.le_max_right w (ℓ + 1)) (Nat.le_max_right _ _)⟩

/-! ## Assembly: the block's facts at a parameter valuation -/

/-- **What the mutual data give at one parameter frame**: the tag and
the chains, the auxiliary former's typing, and the minors' grading
(which `minorTag_facts` discharges from the constructors' data). -/
structure AuxFrameOk {V : Type w} [SetTheory V] {env : Env} (m : EnvModel V env) (ψ : Name → Nat)
    (ℓ W wB b nP : Nat) (pps : List (Nat × Nat × AnnotTerm)) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss₀ Ess' : List (List AnnotTerm))
    (cds : List CtorDatumR) (ρp : Nat → V) : Prop where
  tag : TagOk W ρp Idss
  tagValid : SumFieldsValid ρp Idss
  chains : FixChainsOkI W wB ρp (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess'
  xchains : XChainsOk W wB ρp (auxIds W Idss) rss tlss Eiss' Fss₀ Ess'
  former : LeafTyping (auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess') wB
    (pps ++ tagIps W Idss) (fun k => ρp (k + nP))
  minors : ∀ (j : Nat) (cd : CtorDatumR), cds[j]? = some cd →
    ∀ M : V, M ∈ˢ auxMotSp ℓ W wB ρp Idss rss tlss Eiss' Fss₀ Ess' →
    ∀ ms : List V, ms.length = j →
      WellDenotedV V (consList ms (cons M ρp))
        (minorAVAtR m cd.1 ψ nP cd.2.1 b (1 + j) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1
          cd.2.2.2.2.2.2 cd.2.2.2.2.2.1) ∧
      interp V (consList ms (cons M ρp))
        (minorAVAtR m cd.1 ψ nP cd.2.1 b (1 + j) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1
          cd.2.2.2.2.2.2 cd.2.2.2.2.2.1) ∈ˢ (univ (if ℓ = 0 then 0 else Nat.max wB ℓ) : V)

/-- **The auxiliary binder data's entries, along every walk**: each
domain is graded, valid, and (in the graph regime) in the recursor's
sort. -/
theorem auxRecData_entriesOk {m : EnvModel V env} {ψ : Name → Nat} {elimL : Level}
    {ℓ W wB b nP s : Nat} (hℓ : elimL.eval ψ = ℓ)
    (hb : pwBit ψ (Level.zeronessOf elimL) = b)
    (hs0 : s = 0 ↔ ℓ = 0) (hsW : ℓ ≠ 0 → W ≤ s) (hsw : ℓ ≠ 0 → wB ≤ s) (hsℓ : ℓ ≠ 0 → ℓ + 1 ≤ s)
    {pps : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP)
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)} {cds : List CtorDatumR}
    (hclL : Term.bvarsBelow 0 (auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess').erase)
    (hpps : ∀ ρb : Nat → V, EntriesOk V s ρb (rebit b pps))
    (hfrm : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      AuxFrameOk m ψ ℓ W wB b nP pps Idss rss tlss Eiss' Fss₀ Ess' cds ρp) :
    ∀ ρb : Nat → V,
      EntriesOk V s ρb
        (fixRecDataAVL m ψ (auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess') nP 1 elimL pps
          (tagIps W Idss) cds) := by
  intro ρb
  unfold fixRecDataAVL
  rw [hb]
  refine entriesOk_append (entriesOk_append (entriesOk_append
    (entriesOk_append (hpps ρb) ?_) ?_) ?_) ?_
  · -- the motive
    intro ps hsp
    rw [rebit_map_dom] at hsp
    have hsatP : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) := by
      have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρb) hsp
      rwa [List.append_nil] at h
    have hF := hfrm _ hsatP
    obtain ⟨hmok, hmu⟩ := auxMotive_facts hℓ hlenP hsatP hF.tag hF.tagValid hF.xchains hF.chains
      hclL hF.former
    refine ⟨hmok, fun hsne => ?_, fun _ _ => trivial⟩
    have h0 : ℓ ≠ 0 := fun h => hsne (hs0.mpr h)
    refine univ_mono ?_ _ hmu
    have h1 := hsW h0
    have h2 := hsw h0
    have h3 := hsℓ h0
    have h4 : Nat.max wB (ℓ + 1) ≤ s := Nat.max_le.mpr ⟨h2, h3⟩
    exact Nat.max_le.mpr ⟨h1, h4⟩
  · -- the minors
    intro as hsp
    rw [List.map_append] at hsp
    obtain ⟨ps, mM, rfl, hspP, hspM⟩ := spineFit_append_inv hsp
    rw [rebit_map_dom] at hspP
    obtain ⟨M, rfl, hM⟩ := spineFit_singleton (by simpa using hspM)
    have hsatP : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) := by
      have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρb) hspP
      rwa [List.append_nil] at h
    have hF := hfrm _ hsatP
    have hMsp : M ∈ˢ auxMotSp ℓ W wB (consList ps ρb) Idss rss tlss Eiss' Fss₀ Ess' := by
      rw [auxMotive_interp hℓ hlenP hsatP hF.tag hF.xchains hclL] at hM
      exact hM
    have hframe : consList (ps ++ [M]) ρb = cons M (consList ps ρb) := by
      rw [consList_append, consList_cons, consList_nil]
    rw [hframe]
    refine entriesOk_fixMinorsData cds 1 0 [] rfl fun i cd hcd ms' hlen => ?_
    obtain ⟨hok, hu⟩ := hF.minors i cd hcd M hMsp ms' (by omega)
    refine ⟨hok, fun hsne => ?_⟩
    have h0 : ℓ ≠ 0 := fun h => hsne (hs0.mpr h)
    rw [if_neg h0] at hu
    exact univ_mono (Nat.max_le.mpr ⟨hsw h0, Nat.le_trans (Nat.le_succ ℓ) (hsℓ h0)⟩) _ hu
  · -- the tag binder
    intro as hsp
    rw [List.map_append, List.map_append] at hsp
    obtain ⟨as₁, ms, rfl, hsp₁, hspM⟩ := spineFit_append_inv hsp
    obtain ⟨ps, mM, rfl, hspP, hspMot⟩ := spineFit_append_inv hsp₁
    rw [rebit_map_dom] at hspP
    obtain ⟨M, rfl, -⟩ := spineFit_singleton (by simpa using hspMot)
    have hsatP : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) := by
      have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρb) hspP
      rwa [List.append_nil] at h
    have hF := hfrm _ hsatP
    have hlenMs : ms.length = cds.length := by
      rw [hspM.length_eq, List.length_map, fixMinorsData_length]
    have hframe : consList (ps ++ [M] ++ ms) ρb = consList ms (cons M (consList ps ρb)) := by
      rw [consList_append, consList_append, consList_cons, consList_nil]
    rw [hframe]
    have hsh : shiftE (cds.length + 1) 0 (consList ms (cons M (consList ps ρb)))
        = consList ps ρb := by
      rw [← hlenMs]; exact shiftE_minors rfl
    obtain ⟨hok, hu⟩ := auxIdxBinder_facts (d := cds.length + 1) hsh hF.tag hF.tagValid
    refine ⟨hok, fun hsne => ?_, fun _ _ => trivial⟩
    have h0 : ℓ ≠ 0 := fun h => hsne (hs0.mpr h)
    exact univ_mono (hsW h0) _ hu
  · -- the major
    intro as hsp
    rw [List.map_append, List.map_append, List.map_append] at hsp
    obtain ⟨as₂, is, rfl, hsp₂, hspI⟩ := spineFit_append_inv hsp
    obtain ⟨as₁, ms, rfl, hsp₁, hspM⟩ := spineFit_append_inv hsp₂
    obtain ⟨ps, mM, rfl, hspP, hspMot⟩ := spineFit_append_inv hsp₁
    rw [rebit_map_dom] at hspP
    obtain ⟨M, rfl, -⟩ := spineFit_singleton (by simpa using hspMot)
    have hsatP : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) := by
      have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρb) hspP
      rwa [List.append_nil] at h
    have hF := hfrm _ hsatP
    have hlenMs : ms.length = cds.length := by
      rw [hspM.length_eq, List.length_map, fixMinorsData_length]
    have hframe : consList (ps ++ [M] ++ ms) ρb = consList ms (cons M (consList ps ρb)) := by
      rw [consList_append, consList_append, consList_cons, consList_nil]
    rw [hframe] at hspI
    have hframe4 : consList (ps ++ [M] ++ ms ++ is) ρb
        = consList is (consList ms (cons M (consList ps ρb))) := by
      rw [consList_append, consList_append, consList_append, consList_cons, consList_nil]
    rw [hframe4]
    rw [rebit_map_dom, spineFit_liftDoms_iff] at hspI
    have hsh : shiftE (cds.length + 1) 0 (consList ms (cons M (consList ps ρb)))
        = consList ps ρb := by
      rw [← hlenMs]; exact shiftE_minors rfl
    rw [hsh, tagIps_doms] at hspI
    obtain ⟨hok, hu⟩ := auxMajor_facts hlenP hsatP hF.tag hF.xchains hF.chains hclL hF.former
      hlenMs hspI
    refine ⟨hok, fun hsne => ?_, fun _ _ => trivial⟩
    have h0 : ℓ ≠ 0 := fun h => hsne (hs0.mpr h)
    exact univ_mono (hsw h0) _ hu

/-! ## Assembly: the recursor's conclusion -/

/-- **The recursor's conclusion at a full fitting spine**: the motive
at the tag index, applied to the major — graded, valid, and in the
elimination level's universe. -/
theorem auxConc_facts {m : EnvModel V env} {ψ : Name → Nat} {elimL : Level}
    {ℓ W wB b nP n : Nat} (hℓ : elimL.eval ψ = ℓ)
    (hb : pwBit ψ (Level.zeronessOf elimL) = b)
    {pps : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP)
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Fss Ess' : List (List AnnotTerm)} {cds : List CtorDatumR} (hn : cds.length = n)
    (hclL : Term.bvarsBelow 0 (auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess').erase)
    (hfrm : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      AuxFrameOk m ψ ℓ W wB b nP pps Idss rss tlss Eiss' Fss₀ Ess' cds ρp)
    (hminorRead : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ j cd, cds[j]? = some cd → ∀ (M : V) (ms : List V), ms.length = j →
        interp V (consList ms (cons M ρp))
            (minorAVAtR m cd.1 ψ nP cd.2.1 b (1 + j) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1
              cd.2.2.2.2.2.2 cd.2.2.2.2.2.1)
          = minorSpI ℓ (fun fs => ihSpL ℓ (concI wB ρp M (Ess'.getD j []) j fs)
              (ihDomsI ℓ ρp M rss tlss Eiss' (fun j' => (Fss.getD j' []).length) j fs))
            (Fss.getD j []) ρp [])
    (ρb : Nat → V) (as' : List V)
    (hsp : SpineFit ρb
      ((fixRecDataAVL m ψ (auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess') nP 1 elimL pps
        (tagIps W Idss) cds).map (·.2.2)) as') :
    WellDenotedV V (consList as' ρb) (recConcAV n 1) ∧
      interp V (consList as' ρb) (recConcAV n 1) ∈ˢ (univ ℓ : V) := by
  have hdoms : ((fixRecDataAVL m ψ (auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess') nP 1 elimL
        pps (tagIps W Idss) cds).map (·.2.2))
      = (((pps.map (·.2.2) ++
            [motiveAVIL (auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess') ψ nP 1 elimL
              (tagIps W Idss)]) ++
          (fixMinorsData m ψ nP b cds 1).map (·.2.2)) ++
          (liftDoms (cds.length + 1) 0 (tagIps W Idss)).map (·.2.2)) ++
        [majorAVAtL (auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess') nP 1 cds.length] := by
    unfold fixRecDataAVL
    rw [hb]
    simp only [List.map_append, List.map_cons, List.map_nil, rebit_map_dom]
  rw [hdoms] at hsp
  obtain ⟨as, ts, rfl, hsp', hspT⟩ := spineFit_append_inv hsp
  obtain ⟨t, rfl, ht⟩ := spineFit_singleton hspT
  obtain ⟨ps, M, ms, is, rfl, hlenPs, hlenMs, hlenIs, hρp, hM, -, hfit⟩ :=
    fixSpine_splitL (L := auxFormerAV W wB pps Idss rss tlss Eiss' Fss₀ Ess') (elimL := elimL)
      (b := b) (ℓ := ℓ) (w := wB) (Fss := Fss) (Ess := Ess') (rss := rss) (tlss := tlss)
      (Eiss := Eiss') hlenP (show (tagIps W Idss).length = 1 from rfl) rfl hminorRead ρb as hsp'
  have hF := hfrm _ hρp
  have hMsp : M ∈ˢ auxMotSp ℓ W wB (consList ps ρb) Idss rss tlss Eiss' Fss₀ Ess' := by
    rw [auxMotive_interp hℓ hlenP hρp hF.tag hF.xchains hclL] at hM
    exact hM
  rw [tagIps_doms] at hfit
  obtain ⟨i, rfl, hi⟩ := spineFit_singleton (D := tagTyAV W Idss) hfit
  rw [(tagTyAV_facts hF.tag).1] at hi
  -- the frames
  have hkf : consList (ps ++ [M] ++ ms ++ [i]) ρb
      = consList [i] (consList ms (cons M (consList ps ρb))) := by
    rw [consList_append, consList_append, consList_append, consList_cons, consList_nil]
    rfl
  have hmaj : t ∈ˢ auxFib W wB (consList ps ρb) Idss rss tlss Eiss' Fss₀ Ess' i := by
    rw [hkf] at ht
    rw [interp_majorAVAtL (ips := tagIps W Idss) (nIdx := 1) hlenP
      (show (tagIps W Idss).length = 1 from rfl) hρp (by rw [tagIps_doms]; exact hF.xchains)
      (auxFormer_hleafT (nP := nP) hclL (consList ps ρb)) hlenMs
      (by rw [tagIps_doms]; exact hfit)] at ht
    rw [tagIps_doms] at ht
    exact ht
  -- the conclusion's frame
  have hfrτ : consList (ps ++ [M] ++ ms ++ [i] ++ [t]) ρb
      = cons t (consList [i] (consList ms (cons M (consList ps ρb)))) := by
    rw [consList_append, hkf, consList_cons, consList_nil]
  rw [hfrτ]
  obtain ⟨hchain2, huniv⟩ := auxMot_chain hMsp hi hmaj
  have hchain1 : AppChainOk M [i] := by
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    match k with
    | 0 =>
      exact ⟨ℓ + 1, tagSet W (consList ps ρb) Idss,
        fun x => piR (ℓ + 1) (auxFib W wB (consList ps ρb) Idss rss tlss Eiss' Fss₀ Ess' x)
          fun _ => (univ ℓ : V),
        hMsp, hi, fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩
    | _ + 1 => omega
  have hfrS : RecFrameS 1 (consList [i] (consList ms (cons M (consList ps ρb))))
      (cons t (consList [i] (consList ms (cons M (consList ps ρb))))) := by
    show shiftE 1 0 _ = _
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  have hvars : (idxVarsAV 1 1).map
      (interp V (cons t (consList [i] (consList ms (cons M (consList ps ρb)))))) = [i] := by
    rw [map_idxVarsAV_interp hfrS, frameIdx_consList (nIdx := 1) rfl]
  have hMv : interp V (cons t (consList [i] (consList ms (cons M (consList ps ρb)))))
      (.bvar (1 + 1 + n)) = M := by
    rw [interp_bvar, show 1 + 1 + n = (n + ([i] : List V).length) + 1 from by simp; omega, cons_succ,
      consList_apply_add, show n = 0 + ms.length from by omega, consList_apply_add]
    rfl
  have hinner := mkAppN_wellDenoted_of_chain (args := idxVarsAV 1 1) (f := (.bvar (1 + 1 + n)))
    (σ := cons t (consList [i] (consList ms (cons M (consList ps ρb))))) trivial
    (fun a ha => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
      exact trivial)
    (by rw [hvars, hMv]; exact hchain1)
  have hinnerV : interp V (cons t (consList [i] (consList ms (cons M (consList ps ρb)))))
      (AnnotTerm.mkAppN (.bvar (1 + 1 + n)) (idxVarsAV 1 1)) = SetTheory.app M i := by
    rw [hinner.2, hvars, hMv]
    rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show WellDenoted V _ (.app (AnnotTerm.mkAppN (.bvar (1 + 1 + n)) (idxVarsAV 1 1)) (.bvar 0))
    rw [WellDenoted_app]
    refine ⟨hinner.1, trivial, ℓ + 1,
      auxFib W wB (consList ps ρb) Idss rss tlss Eiss' Fss₀ Ess' i, fun _ => (univ ℓ : V), ?_,
      by rw [interp_bvar]; exact hmaj, fun h0 => absurd h0 (Nat.succ_ne_zero ℓ)⟩
    rw [hinnerV]
    exact app_mem_piR_pos (Nat.succ_ne_zero ℓ) hMsp hi
  · show AnnotValid V _ (.app (AnnotTerm.mkAppN (.bvar (1 + 1 + n)) (idxVarsAV 1 1)) (.bvar 0))
    rw [AnnotValid_app]
    refine ⟨AnnotValid_mkAppN trivial fun a ha => ?_, trivial⟩
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
    exact trivial
  · rw [recConcAV_at (n := n) (nIdx := 1) [i] rfl t]
    have hMn : consList ms (cons M (consList ps ρb)) n = M := by
      rw [show n = 0 + ms.length from by omega, consList_apply_add]
      rfl
    rw [hMn]
    simpa using huniv

end ConLeche.Model
