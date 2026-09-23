module

public import ConLeche.Model.Inductives.FixChains
public import ConLeche.SetModel.Container
public import ConLeche.Semantics.Tower.FixSquashI
public section

/-!
# The closure witness of the fixpoint route's family functor (task #202, Stage B)

The family functor `fixFunVI` of a recursive block is a container in
the sense of `ConLeche/SetModel/Container.lean`: an element of its fibre
at a tuple is a tagged tuple `inj j (mkTower (fs ++ [pt]))` whose
recursive slots hold nested functions over the fields' telescopes into
the family's fibres; its SHAPE is the shadow tuple — the recursive
slots replaced by the shadow value (the chain facts read every domain,
telescope and index expression at frames whose recursive slots hold an
arbitrary value: `ChainFacts.nb`/`nbT`/`nbE`/`nbEs`, the kernel's
`structUsedLater` guard) — its POSITIONS are the recursive fields'
telescope spines (tagged by the field's position), its TARGETS the
calls' index tuples, and the builder curries a function on spines back
into the slots (`lamTower`).  `container_closed_exists` then yields the
closed member family `fixFunVI_closed_exists` needs, for every block —
finitary or not, any sort — replacing the ω-iterate and the top-family
witnesses.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Shadow spines -/

/-- The shadow spine of a field spine from position `i` on: the
recursive slots hold the shadow value. -/
@[expose] noncomputable def shadowOfGo (nP : Nat) (ks : List RecFieldKind) : Nat → List V → List V
  | _, [] => []
  | i, a :: as => (if recAt nP ks (nP + i) then shadowVal else a) :: shadowOfGo nP ks (i + 1) as

/-- The shadow spine of a field spine. -/
@[expose] noncomputable def shadowOf (nP : Nat) (ks : List RecFieldKind) (fs : List V) : List V := shadowOfGo nP ks 0 fs

theorem shadowOfGo_length (nP : Nat) (ks : List RecFieldKind) :
    ∀ (i : Nat) (fs : List V), (shadowOfGo nP ks i fs).length = fs.length
  | _, [] => rfl
  | i, _ :: fs => by simp [shadowOfGo, shadowOfGo_length nP ks (i + 1) fs]

theorem shadowOf_length (nP : Nat) (ks : List RecFieldKind) (fs : List V) :
    (shadowOf nP ks fs).length = fs.length := shadowOfGo_length nP ks 0 fs

theorem shadowOfGo_getD (nP : Nat) (ks : List RecFieldKind) :
    ∀ (i : Nat) (fs : List V) (l : Nat), l < fs.length →
      (shadowOfGo nP ks i fs).getD l pt = if recAt nP ks (nP + (i + l)) then shadowVal else fs.getD l pt
  | _, [], _, hl => absurd hl (Nat.not_lt_zero _)
  | i, a :: fs, 0, _ => by simp [shadowOfGo]
  | i, a :: fs, l + 1, hl => by
    simp only [shadowOfGo, List.getD_cons_succ]
    rw [shadowOfGo_getD nP ks (i + 1) fs l (by simpa using hl),
      show i + 1 + l = i + (l + 1) from by omega]

theorem shadowOf_getD {nP : Nat} {ks : List RecFieldKind} {fs : List V} {l : Nat} (hl : l < fs.length) :
    (shadowOf nP ks fs).getD l pt = if recAt nP ks (nP + l) then shadowVal else fs.getD l pt := by
  unfold shadowOf
  rw [shadowOfGo_getD nP ks 0 fs l hl, Nat.zero_add]

theorem shadowRel_shadowOf (nP : Nat) (ks : List RecFieldKind) (fs : List V) :
    ShadowRel nP ks fs (shadowOf nP ks fs) :=
  ⟨shadowOf_length nP ks fs, fun l hl hr => by rw [shadowOf_getD hl, if_neg hr]⟩

theorem shadowOfGo_append (nP : Nat) (ks : List RecFieldKind) :
    ∀ (i : Nat) (fs gs : List V),
      shadowOfGo nP ks i (fs ++ gs) = shadowOfGo nP ks i fs ++ shadowOfGo nP ks (i + fs.length) gs
  | _, [], _ => by simp [shadowOfGo]
  | i, a :: fs, gs => by
    simp only [List.cons_append, shadowOfGo, List.length_cons, shadowOfGo_append nP ks (i + 1) fs gs]
    rw [show i + 1 + fs.length = i + (fs.length + 1) from by omega]

theorem shadowOfGo_take (nP : Nat) (ks : List RecFieldKind) :
    ∀ (o : Nat) (fs : List V) (i : Nat),
      (shadowOfGo nP ks o fs).take i = shadowOfGo nP ks o (fs.take i)
  | _, [], _ => by simp [shadowOfGo]
  | o, a :: fs, 0 => rfl
  | o, a :: fs, i + 1 => by
    simp only [shadowOfGo, List.take_succ_cons]
    rw [shadowOfGo_take nP ks (o + 1) fs i]

theorem shadowOf_take (nP : Nat) (ks : List RecFieldKind) (fs : List V) (i : Nat) :
    (shadowOf nP ks fs).take i = shadowOf nP ks (fs.take i) :=
  shadowOfGo_take nP ks 0 fs i

/-! ## Graded field chains from pointwise facts -/

/-- **The shadow fields are graded** (at a positive sort): the ordinary
domains by the chain facts at shadow spines, the recursive slots
`Sort 0` — a member of every positive universe. -/
theorem shadowFs_okB {w nP nF nIdx : Nat} (hw : w ≠ 0) {ρp : Nat → V}
    {ks : List RecFieldKind} {tls : List (List (Nat × Nat × AnnotTerm))} {Fs : List AnnotTerm}
    {Eis : List (List AnnotTerm)} {Es : List AnnotTerm}
    (hC : ChainFactsS w nP nF nIdx ρp ks tls Fs Eis Es) :
    FieldsOkB w ρp (shadowFs nP ks nF Fs) := by
  refine fieldsOkB_of_pointwise fun i hi as hsp => ?_
  rw [shadowFs_length] at hi
  have hget : (shadowFs nP ks nF Fs).getD i default
      = if recAt nP ks (nP + i) then .sort 0 else Fs.getD i default := by
    rw [List.getD_eq_getElem?_getD, shadowFs_getElem? hi]; rfl
  rw [hget]
  by_cases hr : recAt nP ks (nP + i)
  · rw [if_pos hr]
    refine ⟨trivial, fun _ => ?_⟩
    rw [interp_sort]
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    exact univ_mono (Nat.succ_le_succ (Nat.zero_le w')) _ (univ_mem_univ 0)
  · rw [if_neg hr]
    obtain ⟨hok, hmem⟩ := hC.gr i hi as hsp
    exact ⟨hok, fun hw' => hmem hr hw'⟩

/-! ## The shapes: the shadow tuples -/

/-- The shadow field lists of all constructors. -/
def shadowFss (nP : Nat) (ksF : Nat → List RecFieldKind) (Fss : List (List AnnotTerm)) :
    List (List AnnotTerm) :=
  (List.range Fss.length).map fun j => shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])

theorem shadowFss_length (nP : Nat) (ksF : Nat → List RecFieldKind) (Fss : List (List AnnotTerm)) :
    (shadowFss nP ksF Fss).length = Fss.length := by simp [shadowFss]

theorem shadowFss_getElem? (nP : Nat) (ksF : Nat → List RecFieldKind) (Fss : List (List AnnotTerm))
    {j : Nat} (hj : j < Fss.length) :
    (shadowFss nP ksF Fss)[j]? = some (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])) := by
  simp [shadowFss, List.getElem?_range hj]

/-- **The shape set at a tuple**: the shadow tuples of the constructors
whose index values are the tuple's. -/
noncomputable def shapeSet (u w nP : Nat) (ρp : Nat → V) (Ids : List AnnotTerm)
    (ksF : Nat → List RecFieldKind) (Fss Ess : List (List AnnotTerm)) (t : V) : V :=
  sep (sumSet w (sumFibre w ρp (uChains (shadowFss nP ksF Fss)))) fun a =>
    ∃ j as', j < Fss.length ∧ a = inj j (mkTower (as' ++ [pt])) ∧
      as'.length = (Fss.getD j []).length ∧
      idxValsAt ρp (Ess.getD j []) as' = isOfW u Ids.length t

/-- The tag of a tagged tuple. -/
noncomputable def shapeTag (a : V) : Nat := natIdx (sfst a)

/-- The fields of a tagged tuple. -/
noncomputable def shapeFields (nF : Nat) (a : V) : List V := projList nF (ssnd a)

theorem shapeTag_inj (j : Nat) (x : V) : shapeTag (inj j x) = j := by
  unfold shapeTag inj
  rw [sfst_spair, natIdx_vnat]

theorem shapeFields_inj (j : Nat) (as bs : List V) :
    shapeFields as.length (inj j (mkTower (as ++ bs))) = as := by
  unfold shapeFields inj
  rw [ssnd_spair, projList_mkTower_append]

/-- **Membership in the shape set** (positive sort): a shadow tuple of
some constructor, its spine fitting the shadow fields, its index values
the tuple's. -/
theorem mem_shapeSet {u w nP : Nat} (hw : w ≠ 0) {ρp : Nat → V} {Ids : List AnnotTerm}
    {ksF : Nat → List RecFieldKind} {Fss Ess : List (List AnnotTerm)} {t a : V} :
    a ∈ˢ shapeSet u w nP ρp Ids ksF Fss Ess t ↔
      ∃ j as', j < Fss.length ∧ a = inj j (mkTower (as' ++ [pt])) ∧
        SpineFit ρp (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])) as' ∧
        idxValsAt ρp (Ess.getD j []) as' = isOfW u Ids.length t := by
  unfold shapeSet
  rw [mem_sep]
  constructor
  · rintro ⟨hsum, j, as', hj, rfl, hlen, hidx⟩
    obtain ⟨j', a', ha', heq⟩ := sumSet_elim hw hsum
    obtain ⟨rfl, rfl⟩ := inj_inj heq
    rw [sumFibre_of_getElem? (by rw [uChains_getElem?, shadowFss_getElem? nP ksF Fss hj]; rfl)] at ha'
    obtain ⟨hfit, -, -, -⟩ := restricted_member_elim hw ha'
    have hl : (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])).length = as'.length := by
      rw [shadowFs_length, hlen]
    rw [hl, projList_mkTower_append] at hfit
    exact ⟨j, as', hj, rfl, hfit, hidx⟩
  · rintro ⟨j, as', hj, rfl, hfit, hidx⟩
    have hlen : as'.length = (Fss.getD j []).length := by
      rw [hfit.length_eq, shadowFs_length]
    refine ⟨?_, j, as', hj, rfl, hlen, hidx⟩
    refine inj_mem hw ?_
    rw [sumFibre_of_getElem? (by rw [uChains_getElem?, shadowFss_getElem? nP ksF Fss hj]; rfl)]
    refine mkTower_mem hw (fitsS_teleOfFields.mpr (SpineFit.append hfit ?_))
    show (pt : V) ∈ˢ interp V (consList as' ρp) (idxEqAV []) ∧ True
    rw [idxEqAV_interp, truthVal_eq_unitSet (EqAll_nil _)]
    exact ⟨pt_mem_unitSet, trivial⟩

/-- **The shape set is a member**: the shadow chains are graded. -/
theorem shapeSet_mem {u w nP nIdx : Nat} (hw : w ≠ 0) {ρp : Nat → V} {Ids : List AnnotTerm}
    {ksF : Nat → List RecFieldKind} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}
    (hC : ∀ j, j < Fss.length → ChainFactsS w nP (Fss.getD j []).length nIdx ρp (ksF j)
      (tlss.getD j []) (Fss.getD j []) (Eiss.getD j []) (Ess.getD j []))
    (t : V) : shapeSet u w nP ρp Ids ksF Fss Ess t ∈ˢ (univ w : V) := by
  unfold shapeSet
  refine univ_sep_mem (sumSet_univ_of_okB (SumFieldsOkB_uChains ?_))
  intro Fs hFs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs
  have hjn : j < Fss.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1; rwa [shadowFss_length] at this
  rw [shadowFss_getElem? nP ksF Fss hjn] at hj
  obtain rfl := Option.some.inj hj
  exact shadowFs_okB hw (hC j hjn)

/-! ## Members: application, tuples, λ-towers -/

theorem app_mem_univ {w : Nat} (hw : w ≠ 0) {f a : V} (hf : f ∈ˢ (univ w : V)) :
    app f a ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  unfold app
  split
  · exact hU.pt_mem (empty_mem_univ w)
  · exact hU.sUnion_mem (hU.sep_mem (hU.sUnion_mem (hU.sUnion_mem hf)))

theorem kpair_comp_mem {w : Nat} (hw : w ≠ 0) {a b : V} (h : kpair a b ∈ˢ (univ w : V)) :
    a ∈ˢ (univ w : V) ∧ b ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  unfold kpair at h
  exact ⟨hU.transitive (hU.transitive h (mem_upair_left _ _)) (mem_sing.mpr rfl),
    hU.transitive (hU.transitive h (mem_upair_right _ _)) (mem_upair_right a b)⟩

theorem spair_comp_mem {w : Nat} (hw : w ≠ 0) {a b : V} (h : spair a b ∈ˢ (univ w : V)) :
    a ∈ˢ (univ w : V) ∧ b ∈ˢ (univ w : V) := by
  rw [spair_eq_kpair] at h
  exact kpair_comp_mem hw h

theorem spair_mem_univ {w : Nat} (hw : w ≠ 0) {a b : V} (ha : a ∈ˢ (univ w : V))
    (hb : b ∈ˢ (univ w : V)) : spair a b ∈ˢ (univ w : V) := by
  rw [spair_eq_kpair]
  exact (univ_isTGUniverse hw).kpair_mem ha ha hb

theorem mkTower_comp_mem {w : Nat} (hw : w ≠ 0) :
    ∀ {L : List V}, mkTower L ∈ˢ (univ w : V) → ∀ x, x ∈ L → x ∈ˢ (univ w : V)
  | [], _, _, hx => nomatch hx
  | a :: L, h, x, hx => by
    obtain ⟨ha, hL⟩ := spair_comp_mem hw (show spair a (mkTower L) ∈ˢ (univ w : V) from h)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact mkTower_comp_mem hw hL x hx

theorem mkTower_mem_univ {w : Nat} (hw : w ≠ 0) :
    ∀ {L : List V}, (∀ x, x ∈ L → x ∈ˢ (univ w : V)) → mkTower L ∈ˢ (univ w : V)
  | [], _ => (univ_isTGUniverse hw).pt_mem (empty_mem_univ w)
  | a :: L, h => by
    show spair a (mkTower L) ∈ˢ _
    exact spair_mem_univ hw (h a List.mem_cons_self)
      (mkTower_mem_univ hw fun x hx => h x (List.mem_cons_of_mem a hx))

theorem vnat_mem_univ {w : Nat} (hw : w ≠ 0) (j : Nat) : (vnat j : V) ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  exact (univ_isTGUniverse hw).transitive (omega_mem_univ_succ w') (vnat_mem_omega j)

theorem inj_mem_univ {w : Nat} (hw : w ≠ 0) {j : Nat} {x : V} (hx : x ∈ˢ (univ w : V)) :
    inj j x ∈ˢ (univ w : V) :=
  spair_mem_univ hw (vnat_mem_univ hw j) hx

theorem inj_comp_mem {w : Nat} (hw : w ≠ 0) {j : Nat} {x : V} (h : inj j x ∈ˢ (univ w : V)) :
    x ∈ˢ (univ w : V) :=
  (spair_comp_mem hw h).2

/-- A λ-tower over graded binder data with member values is a member. -/
theorem lamTower_mem_univ {w : Nat} (hw : w ≠ 0) {g : (Nat → V) → V} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      FieldsOkB w ρ (tl.map (·.2.2)) →
      (∀ bs, SpineFit ρ (tl.map (·.2.2)) bs → g (consList bs ρ) ∈ˢ (univ w : V)) →
      lamTower w ρ tl g ∈ˢ (univ w : V)
  | [], ρ, _, hg => by simpa [lamTower] using hg [] trivial
  | d :: tl, ρ, hF, hg => by
    have hU := univ_isTGUniverse (V := V) hw
    show lamR w (interp V ρ d.2.2) (fun a => lamTower w (cons a ρ) tl g) ∈ˢ _
    rw [List.map_cons] at hF
    rw [lamR_pos hw]
    unfold graph
    refine hU.image_mem (hF.2.1 hw) fun a ha => ?_
    refine hU.kpair_mem (hF.2.1 hw) (hU.transitive (hF.2.1 hw) ha) ?_
    refine lamTower_mem_univ hw (hF.2.2 a ha) fun bs hbs => ?_
    have := hg (a :: bs) ⟨ha, hbs⟩
    rwa [consList_cons] at this

/-- λ-towers over frames agreeing off excluded slots, whose domains
mention none, agree when the bodies agree at corresponding leaves. -/
theorem lamTower_congr_exclP {Q : Nat → Prop} {m : Nat} {g : (Nat → V) → V} :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) {d : Nat}, (∀ q, Q q → q < d) → ∀ {σ σ' : Nat → V},
      AgreeOff (exclP Q d) σ σ' →
      (∀ k dd, tl[k]? = some dd → NoBVar (exclP Q (d + k)) dd.2.2) →
      (∀ bs, SpineFit σ (tl.map (·.2.2)) bs → g (consList bs σ) = g (consList bs σ')) →
      lamTower m σ tl g = lamTower m σ' tl g
  | [], _, _, σ, σ', _, _, hg => by simpa [lamTower] using hg [] trivial
  | dd :: tl, d, hQ, σ, σ', hag, hnb, hg => by
    show lamR m (interp V σ dd.2.2) (fun a => lamTower m (cons a σ) tl g)
      = lamR m (interp V σ' dd.2.2) (fun a => lamTower m (cons a σ') tl g)
    have hnb0 : NoBVar (exclP Q d) dd.2.2 := by simpa using hnb 0 dd rfl
    rw [← interp_congr_noBVar dd.2.2 hnb0 hag]
    refine lamR_congr fun a ha => ?_
    refine lamTower_congr_exclP tl (fun q hq => Nat.lt_succ_of_lt (hQ q hq))
      (agreeOff_exclP_cons hQ hag a) ?_ ?_
    · intro k d' hk
      have := hnb (k + 1) d' (by simpa using hk)
      rwa [show d + (k + 1) = d + 1 + k from by omega] at this
    · intro bs hbs
      have := hg (a :: bs) ⟨ha, hbs⟩
      simpa [consList_cons] using this

omit [SetTheory V] in
theorem frameIdx_cons_consList (a : V) (bs : List V) (ρ : Nat → V) :
    frameIdx (bs.length + 1) (consList bs (cons a ρ)) = a :: bs := by
  have := frameIdx_consList' (a :: bs) ρ
  rwa [List.length_cons, consList_cons] at this

/-- **Eta for a slot's value**: a member of the nested product is the
λ-tower of its spine folds. -/
theorem piTele_eta {w : Nat} (hw : w ≠ 0) {B : List V → V} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V} {f : V},
      f ∈ˢ piTele w (teleOfFields ρ (tl.map (·.2.2))) B acc →
      lamTower w ρ tl (fun σ => (frameIdx tl.length σ).foldl SetTheory.app f) = f
  | [], _, _, _, _ => by simp [lamTower, frameIdx]
  | d :: tl, ρ, acc, f, hf => by
    rw [List.map_cons] at hf
    simp only [teleOfFields, piTele] at hf
    show lamR w (interp V ρ d.2.2) (fun a => lamTower w (cons a ρ) tl
      (fun σ => (frameIdx (tl.length + 1) σ).foldl SetTheory.app f)) = f
    refine Eq.trans ?_ (lamR_eta hf)
    refine lamR_congr fun a ha => ?_
    have hfa := app_mem_piR_pos hw hf ha
    rw [← piTele_eta hw hfa]
    refine lamTower_congr_leaves fun bs hbs => ?_
    have hlen : bs.length = tl.length := by rw [hbs.length_eq, List.length_map]
    rw [← hlen, frameIdx_cons_consList, frameIdx_consList', List.foldl_cons]

theorem spineFit_take_prefix {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) {i : Nat} (hi : i ≤ Fs.length) :
    SpineFit ρ (Fs.take i) (as.take i) := by
  have h' : SpineFit ρ (Fs.take i ++ Fs.drop i) as := by rw [List.take_append_drop]; exact h
  obtain ⟨as₁, as₂, heq, h1, -⟩ := spineFit_append_inv h'
  have hl : as₁.length = i := by
    rw [h1.length_eq, List.length_take]; exact Nat.min_eq_left hi
  have : as.take i = as₁ := by
    rw [heq, List.take_append, List.take_of_length_le (Nat.le_of_eq hl), hl, Nat.sub_self,
      List.take_zero, List.append_nil]
  rw [this]
  exact h1

theorem recAt_iff_rsOf {nP i : Nat} {ks : List RecFieldKind} (hi : i < ks.length) :
    recAt nP ks (nP + i) ↔ (rsOf ks).getD i false = true := by
  rw [rsOf_getD_iff hi]
  unfold recAt
  rw [Nat.add_sub_cancel_left]
  exact ⟨fun h => h.2, fun h => ⟨Nat.le_add_right _ _, h⟩⟩

/-! ## The positions, the targets, the builder -/

/-- The tags of the recursive positions. -/
noncomputable def recTags (rs : List Bool) (nF : Nat) : V :=
  sep omega fun k => ∃ i, i ∈ recIdx rs nF ∧ k = vnat i

theorem mem_recTags {rs : List Bool} {nF : Nat} {k : V} :
    k ∈ˢ recTags rs nF ↔ ∃ i, i ∈ recIdx rs nF ∧ k = vnat i := by
  unfold recTags
  rw [mem_sep]
  exact ⟨fun h => h.2, fun ⟨i, hi, hk⟩ => ⟨by rw [hk]; exact vnat_mem_omega i, i, hi, hk⟩⟩

theorem recTags_mem {w : Nat} (hw : w ≠ 0) (rs : List Bool) (nF : Nat) :
    recTags rs nF ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  exact univ_sep_mem (omega_mem_univ_succ w')

/-- The spine set of a telescope at a prefix. -/
@[expose] noncomputable def spineSet (w : Nat) (ρp : Nat → V) (tl : List (Nat × Nat × AnnotTerm)) (as : List V) :
    V :=
  towerSet w (teleOfFields (consList as ρp) (tl.map (·.2.2)))

/-- The positions of a shape: the recursive fields' spines, tagged. -/
@[expose] noncomputable def posSet (w : Nat) (ρp : Nat → V) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Fss : List (List AnnotTerm)) (a : V) : V :=
  sigmaPairs (recTags (rss.getD (shapeTag a) []) (Fss.getD (shapeTag a) []).length) fun k =>
    spineSet w ρp ((tlss.getD (shapeTag a) []).getD (natIdx k) [])
      ((shapeFields (Fss.getD (shapeTag a) []).length a).take (natIdx k))

/-- The target of a position: the call's index tuple. -/
@[expose] noncomputable def posTgt (u : Nat) (ρp : Nat → V) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss : List (List (List AnnotTerm))) (Fss : List (List AnnotTerm)) (a p : V) : V :=
  tupW u (((Eiss.getD (shapeTag a) []).getD (natIdx (sfst p)) []).map
    (interp V (consList (projList ((tlss.getD (shapeTag a) []).getD (natIdx (sfst p)) []).length (ssnd p))
      (consList ((shapeFields (Fss.getD (shapeTag a) []).length a).take (natIdx (sfst p))) ρp))))

/-- The builder: the tuple with the recursive slots holding the curried
function on spines. -/
@[expose] noncomputable def mkShape (w : Nat) (ρp : Nat → V) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Fss : List (List AnnotTerm)) (a g : V) : V :=
  inj (shapeTag a) (mkTower (((List.range (Fss.getD (shapeTag a) []).length).map fun i =>
    if (rss.getD (shapeTag a) []).getD i false then
      lamTower w (consList ((shapeFields (Fss.getD (shapeTag a) []).length a).take i) ρp)
        ((tlss.getD (shapeTag a) []).getD i []) fun σ =>
          app g (kpair (vnat i) (mkTower (frameIdx ((tlss.getD (shapeTag a) []).getD i []).length σ)))
    else (shapeFields (Fss.getD (shapeTag a) []).length a).getD i pt) ++ [pt]))

/-! ## Shadow transports over the target-blind facts -/

/-- The moved telescope's `NoBVar` facts in the domain-list form. -/
theorem nbT_mapS {w nP nF nIdx : Nat} {ρp : Nat → V} {ks : List RecFieldKind}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Fs : List AnnotTerm}
    {Eis : List (List AnnotTerm)} {Es : List AnnotTerm}
    (hC : ChainFactsS w nP nF nIdx ρp ks tls Fs Eis Es) {i : Nat} (hik : i < nF)
    (hr : recAt nP ks (nP + i)) :
    ∀ q F, ((tls.getD i []).map (·.2.2))[q]? = some F →
      NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i + q)) F := by
  intro q F hq
  rw [List.getElem?_map] at hq
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hq
  exact hC.nbT i hik hr q d hd

/-- The index values are read at the shadow spine. -/
theorem idxValsAt_shadowS {w nP nF nIdx : Nat} {ρp : Nat → V} {ks : List RecFieldKind}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Fs : List AnnotTerm}
    {Eis : List (List AnnotTerm)} {Es : List AnnotTerm}
    (hC : ChainFactsS w nP nF nIdx ρp ks tls Fs Eis Es) {fs : List V} (hlen : fs.length = nF) :
    idxValsAt ρp Es (shadowOf nP ks fs) = idxValsAt ρp Es fs := by
  unfold idxValsAt
  apply List.map_congr_left
  intro E hE
  have hnb := hC.nbEs E hE
  rw [← hlen] at hnb
  exact (interp_congr_noBVar E hnb (agreeOff_shadow (shadowRel_shadowOf nP ks fs) ρp)).symm

section Block

variable {u w nP : Nat} (hw : w ≠ 0) {ρp : Nat → V} {Ids : List AnnotTerm} (hI : IdxOk u ρp Ids)
  {ksF : Nat → List RecFieldKind} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
  {Fss Ess : List (List AnnotTerm)}
  (hrss : ∀ j, j < Fss.length → rss.getD j [] = rsOf (ksF j))
  (hC : ∀ j, j < Fss.length → ChainFacts u w nP (Fss.getD j []).length ρp Ids (ksF j)
    (tlss.getD j []) (Fss.getD j []) (Eiss.getD j []) (Ess.getD j []))
include hw hrss hC

omit hrss hC in
theorem shapeSet_data {t a : V} (ha : a ∈ˢ shapeSet u w nP ρp Ids ksF Fss Ess t) :
    ∃ j as', j < Fss.length ∧ a = inj j (mkTower (as' ++ [pt])) ∧
      as'.length = (Fss.getD j []).length ∧
      SpineFit ρp (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])) as' ∧
      idxValsAt ρp (Ess.getD j []) as' = isOfW u Ids.length t ∧
      shapeTag a = j ∧ shapeFields (Fss.getD j []).length a = as' := by
  obtain ⟨j, as', hj, rfl, hfit, hidx⟩ := (mem_shapeSet hw).mp ha
  have hlen : as'.length = (Fss.getD j []).length := by rw [hfit.length_eq, shadowFs_length]
  refine ⟨j, as', hj, rfl, hlen, hfit, hidx, shapeTag_inj j _, ?_⟩
  rw [← hlen]
  exact shapeFields_inj j as' [pt]

/-! ## The element decomposition -/

omit [SetTheory V] hw hrss hC in
theorem agreeOff_symm {P : Nat → Prop} {σ σ' : Nat → V} (h : AgreeOff P σ σ') : AgreeOff P σ' σ :=
  fun i hi => (h i hi).symm

end Block

end ConLeche.Model
