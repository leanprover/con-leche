module

public import ConLeche.Semantics.Tower.SumTower
import ConLeche.Semantics.Univ

@[expose] public section

/-!
# The index-tuple kit of an indexed family

The index tuple (`tupW`, its set `idxSet`, its spelled type `idxTyAV`)
and the family type `I → Sort w` (`famTyAV`); frame and spine
arithmetic; the Π-tower grading (`WellDenoted_mkPisAV_of`/`_inv`); the
ih frame (`ihIdxAtM`, `ihTeleAtR`); and the subsingleton criterion's
spines read off index tuples (`srcVals_of_fit`, `isOfW_tupW`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The index tuple -/

/-- The index tuple's value: the point at index level `0`, the tuple
tower above. -/
noncomputable def tupW (u : Nat) (is : List V) : V := if u = 0 then pt else mkTower is

theorem tupW_zero (is : List V) : tupW 0 is = (pt : V) := if_pos rfl
theorem tupW_pos {u : Nat} (hu : u ≠ 0) (is : List V) : tupW u is = mkTower is := if_neg hu

/-- The index-tuple set at a parameter frame. -/
noncomputable def idxSet (u : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) : V :=
  towerSet u (teleOfFields ρp Ids)

/-- The index tuple type, spelled at the parameter frame. -/
def idxTyAV (u : Nat) (Ids : List AnnotTerm) : AnnotTerm := towerBodyAV u Ids


/-- The index telescope's grading, with the bound in both regimes (the
index domains' sorts are at most `u`, so the tuple type is a graph-regime
tower even at `u = 0` where `FieldsOkB` alone asks for no bound). -/
def IdxOk (u : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) : Prop :=
  FieldsOkB u ρp Ids ∧ FieldsBound u ρp Ids

theorem idxTyAV_facts {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    interp V ρp (idxTyAV u Ids) = idxSet u ρp Ids ∧
      idxSet u ρp Ids ∈ˢ (univ u : V) ∧ WellDenoted V ρp (idxTyAV u Ids) :=
  ⟨towerBodyAV_interp (fun _ => h.2), towerSet_univ_of_okB (fun _ => h.2), towerBodyAV_wellDenoted h.1⟩

/-- A fitting index spine's tuple is in the tuple set. -/
theorem tupW_mem {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {is : List V}
    (hsp : SpineFit ρp Ids is) : tupW u is ∈ˢ idxSet u ρp Ids := by
  unfold tupW idxSet
  split
  · next hu => exact hu ▸ pt_mem_tower (fitsS_teleOfFields.mpr hsp)
  · next hu => exact mkTower_mem hu (fitsS_teleOfFields.mpr hsp)


theorem foldl_app_pt' : ∀ (ts : List V), ts.foldl SetTheory.app (pt : V) = pt
  | [] => rfl
  | t :: ts => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt' ts


/-! ## The family type -/

/-- `I → Sort w`, spelled. -/
def famTyAV (u w : Nat) (Ids : List AnnotTerm) : AnnotTerm :=
  .pi u (w + 1) (idxTyAV u Ids) (.sort w)

theorem famTyAV_facts {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    interp V ρp (famTyAV u w Ids) = lfpFamSpace V w (idxSet u ρp Ids) ∧
      lfpFamSpace V w (idxSet u ρp Ids) ∈ˢ (univ (Nat.max u (w + 1)) : V) ∧
      WellDenoted V ρp (famTyAV u w Ids) := by
  obtain ⟨hv, hu, hok⟩ := idxTyAV_facts h
  refine ⟨?_, ?_, ?_⟩
  · unfold famTyAV lfpFamSpace
    rw [interp_pi, hv]
    rfl
  · unfold lfpFamSpace
    have := piR_mem_univ (u := u) (v := w + 1) hu (fun _ _ => univ_mem_univ w)
    rwa [if_neg (Nat.succ_ne_zero w)] at this
  · unfold famTyAV
    rw [WellDenoted_pi]
    exact ⟨hok, fun _ _ => trivial⟩


omit [SetTheory V] in

omit [SetTheory V] in
theorem frameIdx_succ (n : Nat) (ρ : Nat → V) : frameIdx (n + 1) ρ = ρ n :: frameIdx n ρ := by
  unfold frameIdx
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  show ρ (n + 1 - 1 - 0) :: _ = _
  rw [show n + 1 - 1 - 0 = n from rfl]
  congr 1
  apply List.map_congr_left
  intro l _
  show ρ (n + 1 - 1 - (l + 1)) = ρ (n - 1 - l)
  rw [show n + 1 - 1 - (l + 1) = n - 1 - l from by omega]

omit [SetTheory V] in
/-- The index tuple of a consed spine. -/
theorem frameIdx_consList' : ∀ (is : List V) (ρ : Nat → V),
    frameIdx is.length (consList is ρ) = is
  | [], _ => rfl
  | a :: as, ρ => by
    rw [consList_cons, List.length_cons, frameIdx_succ, frameIdx_consList' as (cons a ρ)]
    congr 1
    have := consList_apply_add as (cons a ρ) 0
    rw [Nat.zero_add] at this
    exact this

omit [SetTheory V] in
/-- A frame is its index tuple over its shift. -/
theorem consList_frameIdx : ∀ (n : Nat) (ρ : Nat → V),
    consList (frameIdx n ρ) (shiftE n 0 ρ) = ρ
  | 0, ρ => by
    show consList [] (shiftE 0 0 ρ) = ρ
    rw [consList_nil, shiftE_zero_zero]
  | n + 1, ρ => by
    have hfr : frameIdx (n + 1) ρ = ρ n :: frameIdx n ρ := frameIdx_succ n ρ
    have hsh : cons (ρ n) (shiftE (n + 1) 0 ρ) = shiftE n 0 ρ := by
      funext i
      cases i with
      | zero => show ρ n = ρ (0 + n); rw [Nat.zero_add]
      | succ i =>
        show ρ (i + (n + 1)) = ρ (i + 1 + n)
        rw [show i + (n + 1) = i + 1 + n from by omega]
    rw [hfr, consList_cons, hsh]
    exact consList_frameIdx n ρ

/-! ## The X-frame kit -/


omit [SetTheory V] in
theorem Xframe_X (ρp : Nat → V) (as : List V) (t X : V) :
    consList as (cons t (cons X ρp)) (as.length + 1) = X := by
  have := consList_apply_add as (cons t (cons X ρp)) 1
  rw [Nat.add_comm] at this
  exact this

omit [SetTheory V] in
theorem Xframe_t (ρp : Nat → V) (as : List V) (t X : V) :
    consList as (cons t (cons X ρp)) as.length = t := by
  have := consList_apply_add as (cons t (cons X ρp)) 0
  rw [Nat.zero_add] at this
  exact this

section Slot

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm}


/-! ## The index tuple's retraction -/

/-- At index level `0` every index value is the point. -/
theorem spineFit_pt_of_bound0 {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm} {as : List V}, FieldsBound 0 ρ Fs → SpineFit ρ Fs as →
      ∀ l, l < as.length → as.getD l pt = pt
  | [], [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | [], _ :: _, _, hsp, _, _ => hsp.elim
  | _ :: _, [], _, hsp, _, _ => hsp.elim
  | F :: Fs, a :: as, hb, hsp, l, hl => by
    cases l with
    | zero =>
      have h0 : interp V ρ F ∈ˢ (univZero : V) := by
        have := hb.1; rwa [univ_zero] at this
      exact eq_pt_of_mem_univZero h0 hsp.1
    | succ l =>
      exact spineFit_pt_of_bound0 (hb.2 a hsp.1) hsp.2 l (by simpa using hl)


/-- **The index tuple's retraction**, at both regimes. -/
theorem projS_tupW (hI : IdxOk u ρp Ids) {is : List V} (hsp : SpineFit ρp Ids is) {l : Nat}
    (hl : l < Ids.length) : projS l (tupW u is) = is.getD l pt := by
  have hislen : is.length = Ids.length := hsp.length_eq
  by_cases hu : u = 0
  · subst hu
    rw [tupW_zero, projS_pt, spineFit_pt_of_bound0 hI.2 hsp l (by omega)]
  · rw [tupW_pos hu, projS_mkTower l is (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]


end Slot

/-! ## Π-tower grading -/

section Fam

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}

omit [SetTheory V] in
theorem consList_snoc' (a : V) (as : List V) (ρ : Nat → V) :
    cons a (consList as ρ) = consList (as ++ [a]) ρ := by
  rw [consList_append]; rfl


-- `u` (the slot's tuple level) is unused by the fit itself; kept for uniformity


/-- **A Π-tower is graded** when its domains are along the telescope
and its body is at every fitting spine. -/
theorem WellDenoted_mkPisAV_of {w : Nat} {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      FieldsOkB w σ (gds.map (·.2.2)) →
      (∀ as, SpineFit σ (gds.map (·.2.2)) as → WellDenoted V (consList as σ) R) →
      WellDenoted V σ (mkPisAV gds R)
  | [], _, _, hR => by simpa [mkPisAV, consList] using hR [] trivial
  | d :: gds, σ, hF, hR => by
    rw [List.map_cons] at hF
    obtain ⟨hok, -, hrest⟩ := hF
    simp only [mkPisAV, WellDenoted_pi]
    refine ⟨hok, fun x hx => ?_⟩
    refine WellDenoted_mkPisAV_of (hrest x hx) fun as hsp => ?_
    have := hR (x :: as) ⟨hx, hsp⟩
    rwa [consList_cons] at this


end Fam


/-!
## The ih frame

A field's index expressions and telescope moved to an ih frame
(`ihIdxAtM`, `ihTeleAtR`).
-/


open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Field sources among the index expressions -/

/-- The source of field `j` among the constructor's index expressions:
the first index position whose expression is the field's variable
(`none` when the field is not an index — a `Prop` field under the
subsingleton criterion). -/
def srcOfEs (Es : List AnnotTerm) (nF j : Nat) : Option Nat :=
  (List.range Es.length).find? fun l =>
    match Es.getD l default with
    | .bvar k => k = nF - 1 - j
    | _ => false

/-- The sources of all `nF` fields. -/
def srcList (Es : List AnnotTerm) (nF : Nat) : List (Option Nat) :=
  (List.range nF).map (srcOfEs Es nF)

open ConLeche.Term (Term)

namespace FixKI

variable {ℓ w u nP : Nat} {ρ₀ : Nat → V} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {rds : List (Nat × Nat × AnnotTerm)}

/-- The `l`-th value of a fitting spine is in the `l`-th domain at the
prefix. -/
theorem spineFit_getD_mem' {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm} {as : List V} {l : Nat}, SpineFit ρ Fs as → l < Fs.length →
      as.getD l pt ∈ˢ interp V (consList (as.take l) ρ) (Fs.getD l default)
  | [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, [], _, h, _ => h.elim
  | F :: Fs, a :: as, 0, h, _ => by simpa using h.1
  | F :: Fs, a :: as, l + 1, h, hl => by
    simp only [List.getD_cons_succ, List.take_succ_cons, consList_cons]
    exact spineFit_getD_mem' (Fs := Fs) (as := as) (l := l) h.2 (by simpa using hl)

end FixKI

section WalkFrames

variable {u w : Nat} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}

omit [SetTheory V] in
/-- The index tuple of a K-frame over a bottom. -/
theorem frameIdx_of (nIdx : Nat) {as is : List V} (hilen : is.length = nIdx) (ρb : Nat → V) :
    frameIdx nIdx (consList (as ++ is) ρb) = is := by
  rw [consList_append, ← hilen]
  exact frameIdx_consList' is _

end WalkFrames

section Rec

variable {ℓ w u nP s : Nat} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {rds : List (Nat × Nat × AnnotTerm)}

/-- A spine fitting a chain fits a prefix of it. -/
theorem spineFit_prefix {ρ : Nat → V} {Ds : List AnnotTerm} {as bs : List V}
    (h : SpineFit ρ Ds (as ++ bs)) : SpineFit ρ (Ds.take as.length) as := by
  have hlen : (as ++ bs).length = Ds.length := h.length_eq
  have hsplit : Ds = Ds.take as.length ++ Ds.drop as.length := (List.take_append_drop _ _).symm
  rw [hsplit] at h
  obtain ⟨as₁, as₂, heq, h1, -⟩ := spineFit_append_split h
  have hl₁ : as₁.length = as.length := by
    rw [h1.length_eq, List.length_take]
    rw [List.length_append] at hlen
    omega
  obtain ⟨rfl, -⟩ := List.append_inj heq hl₁.symm
  exact h1

end Rec


/-!
## Spines read off index tuples

The squash regime's subsingleton criterion: a constructor's data
fields are index expressions, so its spine is READ OFF THE INDICES —
the source lists `srcList`/`srcOfEs`, their values `srcVals`, and the
decoding `isOfW` of an index tuple back into its spine (`isOfW_tupW`).
-/

open ConLeche.SetModel ConLeche.SetTheory
open SetTheory ConLeche.SetTheory.Tower

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Frame kit -/

/-! ## The sources -/

omit [SetTheory V] in
theorem srcList_length (Es : List AnnotTerm) (nF : Nat) : (srcList Es nF).length = nF := by
  simp [srcList]

theorem srcVals_length (is : List V) (src : List (Option Nat)) : (srcVals is src).length = src.length := by
  simp [srcVals]

omit [SetTheory V] in
/-- A source position's expression is the field's variable. -/
theorem srcOfEs_some {Es : List AnnotTerm} {nF j l : Nat} (h : srcOfEs Es nF j = some l) :
    l < Es.length ∧ Es.getD l default = .bvar (nF - 1 - j) := by
  unfold srcOfEs at h
  refine ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), ?_⟩
  have hp := List.find?_some h
  revert hp
  cases Es.getD l default <;> simp

omit [SetTheory V] in
/-- At an unsourced field no index expression is the field's variable. -/
theorem srcOfEs_none {Es : List AnnotTerm} {nF j l : Nat} (h : srcOfEs Es nF j = none)
    (hl : Es[l]? = some (.bvar (nF - 1 - j))) : False := by
  unfold srcOfEs at h
  have hlt : l < Es.length := (List.getElem?_eq_some_iff.mp hl).1
  have := List.find?_eq_none.mp h l (List.mem_range.mpr hlt)
  rw [List.getD_eq_getElem?_getD, hl, Option.getD_some] at this
  simp at this

/-- **The subsingleton criterion**: a spine fitting the fields whose
index values are the tuple is the source spine (an index-sourced field
is the index's value, the other fields are `Prop`s — points). -/
theorem srcVals_of_fit {ρp : Nat → V} {Fs Es : List AnnotTerm}
    (hprop : ∀ j, j < Fs.length → srcOfEs Es Fs.length j = none →
      ∀ fs : List V, SpineFit ρp (Fs.take j) fs →
        interp V (consList fs ρp) (Fs.getD j default) ∈ˢ (univZero : V))
    {fs is : List V} (hfit : SpineFit ρp Fs fs) (hidx : idxValsAt ρp Es fs = is) :
    fs = srcVals is (srcList Es Fs.length) := by
  have hlen : fs.length = Fs.length := hfit.length_eq
  apply List.ext_getElem
  · rw [srcVals_length, srcList_length, hlen]
  intro j h1 h2
  rw [srcVals_length, srcList_length] at h2
  have hfj : fs[j] = fs.getD j pt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  rw [hfj]
  cases hs : srcOfEs Es Fs.length j with
  | some l =>
    simp only [srcVals, srcList, List.getElem_map, List.getElem_range, hs]
    obtain ⟨hl, hE⟩ := srcOfEs_some hs
    subst hidx
    show fs.getD j pt = (Es.map (interp V (consList fs ρp))).getD l pt
    have hr : (Es.map (interp V (consList fs ρp))).getD l pt = interp V (consList fs ρp) Es[l] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]; rfl
    have hEl : Es[l] = AnnotTerm.bvar (Fs.length - 1 - j) := by
      rw [← hE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl
    rw [hr, hEl, interp_bvar, consList_getD_of_lt fs ρp _ (by omega),
      show fs.length - 1 - (Fs.length - 1 - j) = j from by omega]
  | none =>
    simp only [srcVals, srcList, List.getElem_map, List.getElem_range, hs]
    have hmem := FixKI.spineFit_getD_mem' hfit h2
    have hsp : SpineFit ρp (Fs.take j) (fs.take j) := by
      have := spineFit_prefix (as := fs.take j) (bs := fs.drop j) (by rw [List.take_append_drop]; exact hfit)
      rwa [List.length_take, hlen, Nat.min_eq_left (Nat.le_of_lt h2)] at this
    exact eq_pt_of_mem_univZero (hprop j h2 hs _ hsp) hmem

/-! ## The squash data at a tuple -/

/-- The index spine of a tuple (at level `0` every index is a proof). -/
noncomputable def isOfW (u nIdx : Nat) (t : V) : List V :=
  if u = 0 then List.replicate nIdx pt else projList nIdx t

/-- A fitting spine over `Prop`-regime domains is the points. -/
theorem spineFit_zero_replicate :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V} {is : List V}, FieldsBound 0 ρ Fs → SpineFit ρ Fs is →
      is = List.replicate Fs.length pt
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => h.elim
  | _ :: _, _, [], _, h => h.elim
  | F :: Fs, ρ, a :: is, hb, hsp => by
    obtain ⟨ha, hsp'⟩ := hsp
    have hpt : a = pt := by
      have := hb.1
      rw [univ_zero] at this
      exact eq_pt_of_mem_univZero this ha
    subst hpt
    rw [List.length_cons, List.replicate_succ]
    exact congrArg _ (spineFit_zero_replicate (hb.2 pt ha) hsp')

theorem isOfW_tupW {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (hI : IdxOk u ρp Ids)
    {is : List V} (hsp : SpineFit ρp Ids is) : isOfW u Ids.length (tupW u is) = is := by
  by_cases hu : u = 0
  · rw [isOfW, if_pos hu]
    subst hu
    exact (spineFit_zero_replicate hI.2 hsp).symm
  · rw [isOfW, tupW, if_neg hu, if_neg hu]
    exact projList_mkTower _ _ hsp.length_eq

section Body

variable {ℓ u nP : Nat} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss : List (List (List AnnotTerm))} {rds : List (Nat × Nat × AnnotTerm)}

/-- A tuple of the index set is the tuple of a fitting spine. -/
theorem mem_idxSet_elim {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {t : V}
    (ht : t ∈ˢ idxSet u ρp Ids) : ∃ is : List V, SpineFit ρp Ids is ∧ t = tupW u is := by
  by_cases hu : u = 0
  · subst hu
    obtain ⟨rfl, as, has⟩ := towerSet_zero_elim (teleOfFields ρp Ids) ht
    exact ⟨as, fitsS_teleOfFields.mp has, (tupW_zero as).symm⟩
  · obtain ⟨hsp, heq⟩ := towerSet_elim_teleOfFields hu ht
    exact ⟨_, hsp, by rw [tupW_pos hu]; exact heq⟩

end Body

open ConLeche.Term ConLeche.Verify

/-! ## Π-tower boundedness -/

/-- A Π-tower over bounded binder data with a bounded conclusion is
bounded. -/
theorem mkPisAV_below_of {C : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {k : Nat}, DomsBelow k ds →
      Term.bvarsBelow (k + ds.length) C.erase → Term.bvarsBelow k (mkPisAV ds C).erase
  | [], _, _, hC => hC
  | d :: ds, k, hd, hC => by
    refine ⟨hd.1, mkPisAV_below_of hd.2 ?_⟩
    rwa [show k + 1 + ds.length = k + (d :: ds).length from by simp; omega]

end ConLeche.Semantics
