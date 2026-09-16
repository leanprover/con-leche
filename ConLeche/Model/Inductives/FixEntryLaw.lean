module

import ConLeche.Model.Inductives.StructBodyFrames
public import ConLeche.Model.Inductives.FixRealChains
public section

/-!
# The projection entry's law on the fixpoint route's carrier (task #210 Part A)

The three clauses of `TowerEntryLaw` at a STRUCTURE-LIKE block on the
fixpoint route — one constructor, no index — whose carrier is the
TAGGED tower: the family's fibre at the (empty) index tuple is the sum
route's restricted tagged union over the one constructor,
`sumSet w (sumFibre w ρ [Fs ++ [idxEqAV []]])` (`fixFamI_app_eq_sum`),
whose elements are `inj 0 (mkTower (fs ++ [pt]))` with `fs` fitting the
fields.  So field `i` is `projS (i + 1)` of a member (the tag in front,
`ProjTable.off = 1`), the tuple below the tag is `dropS 1`, and the
laws are the direct structure's (`StructEntryLawP`) with one pair
component to cross:

* **(A) the typing law** (`fixEntryTypingCore`): a member projects at
  `i + 1` into the body's residual — the graph regime by the tower's
  projection membership below the tag, the squash regime by the point;
* **(B) the iota law** (`fixEntryIotaCore`/`fixEntryIotaCoreZero`): the
  projection of a graded constructor application is the selected field
  (`sumMkAV_fold`: the application folds to the tagged tuple);
* **(C) the η law** (`fixEntryEtaCore`): a member is the constructor at
  the parameters and its own projections below the tag.

`fixFibre_elim`/`fixFibre_zero_elim` are the one-constructor fibre's
eliminations, `wellDenoted_proj1_sum`/`wellDenoted_proj1_pt` grade the tag
projection.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BinderMeta ProjEntry)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The one-constructor fibre -/

/-- The elements of the one-constructor fibre in the graph regime:
tagged point-terminated tuples fitting the fields, the tuple a member
of the restricted tower. -/
theorem fixFibre_elim {w : Nat} (hw : w ≠ 0) {ρ' : Nat → V} {Fs : List AnnotTerm} {x : V}
    (hx : x ∈ˢ sumSet w (sumFibre w ρ' [Fs ++ [idxEqAV []]])) :
    ∃ fs : List V, x = inj 0 (mkTower (fs ++ [pt])) ∧ SpineFit ρ' Fs fs ∧
      mkTower (fs ++ [pt]) ∈ˢ towerSet w (teleOfFields ρ' (Fs ++ [idxEqAV []])) := by
  obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw hx
  cases j with
  | zero =>
    rw [sumFibre_of_getElem? rfl] at ha
    obtain ⟨hfit, heta⟩ := towerSet_elim_teleOfFields hw ha
    obtain ⟨fs, hfs, hsp, -⟩ := spineFit_append_idxEq.mp hfit
    refine ⟨fs, ?_, hsp, ?_⟩
    · rw [heta, hfs]
    · rw [← hfs, ← heta]; exact ha
  | succ j =>
    rw [sumFibre_of_ge (by simp)] at ha
    exact absurd ha (not_mem_empty _)

/-- The one-constructor fibre in the squash regime: the point, with a
fitting field spine. -/
theorem fixFibre_zero_elim {ρ' : Nat → V} {Fs : List AnnotTerm} {x : V}
    (hx : x ∈ˢ sumSet 0 (sumFibre 0 ρ' [Fs ++ [idxEqAV []]])) :
    x = pt ∧ ∃ fs : List V, SpineFit ρ' Fs fs := by
  obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx
  refine ⟨rfl, ?_⟩
  cases j with
  | zero =>
    rw [sumFibre_of_getElem? rfl] at ha
    obtain ⟨-, as, hfits⟩ := towerSet_zero_elim _ ha
    obtain ⟨fs, -, hsp, -⟩ := spineFit_append_idxEq.mp (fitsS_teleOfFields.mp hfits)
    exact ⟨fs, hsp⟩
  | succ j =>
    rw [sumFibre_of_ge (by simp)] at ha
    exact absurd ha (not_mem_empty _)

/-- The tuple below the tag. -/
theorem dropS_one_inj (j : Nat) (a : V) : dropS 1 (inj j a) = a := by
  show ssnd (spair (vnat j) a) = a
  exact ssnd_spair _ _

/-- A projection past the tag is the tuple's. -/
theorem projS_succ_inj (i j : Nat) (a : V) : projS (i + 1) (inj j a) = projS i a := by
  rw [projS_add_dropS, dropS_one_inj]

/-- The restricted chain of the one constructor at no index is the
unrestricted one. -/
theorem fieldsBound_append_idxEq {w : Nat} {ρ' : Nat → V} {Fs : List AnnotTerm} (hw : w ≠ 0)
    (hok : FieldsOkB w ρ' Fs) : FieldsBound w ρ' (Fs ++ [idxEqAV []]) :=
  (FieldsOkB_append_idxEq hok fun _ _ _ he => absurd he List.not_mem_nil).toBound hw

/-! ## The carrier at a tag, abstractly (task #278)

The three law cores below need only two facts about the family's
value at a parameter frame: what its members look like in the graph
regime, and that they are the point in the squash regime.  Both are
independent of WHERE the fibre sits in the tagged union, so they are
packaged over an arbitrary tag `J` and an arbitrary carrier `S`: the
fixpoint route instantiates them at the one-constructor fibre
(`fixFibre_fibreAt`, tag `0`), a mutual block's structure-like member
at its own constructor's GLOBAL position inside the block's restricted
tagged union. -/

/-- **The carrier's shape at a tag**: in the graph regime every member
is the tag-`J` injection of a point-terminated tuple over a spine
fitting the fields `Fs`; in the squash regime it is the point and the
fields admit a fitting spine. -/
structure FibreAt (w J : Nat) (Fs : List AnnotTerm) (ρ' : Nat → V) (S : V) : Prop where
  /-- the graph regime's members are tagged point-terminated tuples -/
  graph : w ≠ 0 → ∀ x : V, x ∈ˢ S →
    ∃ fs : List V, x = inj J (mkTower (fs ++ [pt])) ∧ SpineFit ρ' Fs fs
  /-- the squash regime's member is the point -/
  squash : w = 0 → ∀ x : V, x ∈ˢ S → x = pt ∧ ∃ fs : List V, SpineFit ρ' Fs fs

/-- The fixpoint route's one-constructor fibre has that shape at tag
`0`. -/
theorem fixFibre_fibreAt {w : Nat} {ρ' : Nat → V} {Fs : List AnnotTerm} :
    FibreAt w 0 Fs ρ' (sumSet w (sumFibre w ρ' [Fs ++ [idxEqAV []]])) where
  graph := fun hw _ hx => by
    obtain ⟨fs, heq, hsp, -⟩ := fixFibre_elim hw hx
    exact ⟨fs, heq, hsp⟩
  squash := fun hw _ hx => by subst hw; exact fixFibre_zero_elim hx

/-! ## The tag projection's grading -/

/-- `.snd` of a tagged member is graded: the union is a Σ over the
numerals whose fibre at the tag is a bounded tower and whose other
fibres may be taken empty. -/
theorem wellDenoted_proj1_inj {w J : Nat} (hw : w ≠ 0) {ρ' ρ : Nat → V} {Fs : List AnnotTerm}
    {e : AnnotTerm} {a : V} (hb : FieldsBound w ρ' (Fs ++ [idxEqAV []]))
    (hok : WellDenoted V ρ e) (heq : interp V ρ e = inj J a)
    (ha : a ∈ˢ towerSet w (teleOfFields ρ' (Fs ++ [idxEqAV []]))) :
    WellDenoted V ρ (.snd e) := by
  rw [WellDenoted_snd]
  refine ⟨hok, w, w, omega,
    natFibre (fun j => if j = J then towerSet w (teleOfFields ρ' (Fs ++ [idxEqAV []]))
      else (empty : V)), ?_, ?_, ?_⟩
  · rw [nat_max_self, heq]
    exact inj_mem hw (by rw [if_pos rfl]; exact ha)
  · obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    exact omega_mem_univ_succ w'
  · intro k hk
    obtain ⟨j, rfl, hfib⟩ := natFibre_of_mem _ hk
    rw [hfib]
    by_cases hj : j = J
    · rw [if_pos hj]
      exact towerSet_mem_univ _ (boundS_teleOfFields.mpr hb)
    · rw [if_neg hj]
      exact empty_mem_univ w

/-- `.snd` of a member of the tagged union is graded: the union is a
Σ over the numerals whose fibres are bounded towers. -/
theorem wellDenoted_proj1_sum {w : Nat} (hw : w ≠ 0) {ρ' ρ : Nat → V} {Fs : List AnnotTerm}
    {e : AnnotTerm} (hb : FieldsBound w ρ' (Fs ++ [idxEqAV []]))
    (hok : WellDenoted V ρ e)
    (hval : interp V ρ e ∈ˢ sumSet w (sumFibre w ρ' [Fs ++ [idxEqAV []]])) :
    WellDenoted V ρ (.snd e) := by
  obtain ⟨fs, heq, -, hmem⟩ := fixFibre_elim hw hval
  exact wellDenoted_proj1_inj hw hb hok heq hmem

/-- `.snd` of the point is graded (the squash regime). -/
theorem wellDenoted_proj1_pt {ρ : Nat → V} {e : AnnotTerm} (hok : WellDenoted V ρ e)
    (hpt : interp V ρ e = (pt : V)) : WellDenoted V ρ (.snd e) := by
  rw [WellDenoted_snd]
  refine ⟨hok, 0, 0, unitSet, fun _ => unitSet, ?_, unitSet_mem_univ 0,
    fun _ _ => unitSet_mem_univ 0⟩
  rw [hpt, nat_max_self]
  exact pt_mem_sigma pt_mem_unitSet pt_mem_unitSet

/-- The projection reading past the tag, graded at a member of a
tag-`J` carrier (both regimes). -/
theorem wellDenoted_projAV_succ_of {w J i : Nat} {ρ' ρ : Nat → V} {Fs : List AnnotTerm}
    {S : V} {e : AnnotTerm} (hokB : w ≠ 0 → FieldsOkB w ρ' Fs)
    (hfib : FibreAt w J Fs ρ' S)
    (hok : WellDenoted V ρ e) (hval : interp V ρ e ∈ˢ S)
    (hi : i < Fs.length) : WellDenoted V ρ (projAV (i + 1) e) := by
  show WellDenoted V ρ (projAV i (.snd e))
  by_cases hw : w = 0
  · subst hw
    obtain ⟨hpt, -⟩ := hfib.squash rfl _ hval
    refine wellDenoted_projAV_pt (wellDenoted_proj1_pt hok hpt) ?_
    rw [interp_snd, hpt, ssnd_pt]
  · obtain ⟨fs, heq, hsp⟩ := hfib.graph hw _ hval
    have hb := fieldsBound_append_idxEq hw (hokB hw)
    have hmem : mkTower (fs ++ [pt]) ∈ˢ towerSet w (teleOfFields ρ' (Fs ++ [idxEqAV []])) :=
      mkTower_mem_teleOfFields hw (hsp.append ⟨pt_mem_idxEqAV_nil _, trivial⟩)
    refine wellDenoted_projAV_tower hb hmem (wellDenoted_proj1_inj hw hb hok heq hmem) ?_
      (by rw [List.length_append, List.length_singleton]; omega)
    rw [interp_snd, heq]
    exact ssnd_spair _ _

/-- The projection reading past the tag, graded at a member of the
one-constructor fibre (both regimes). -/
theorem wellDenoted_projAV_succ_fibre {w i : Nat} {ρ' ρ : Nat → V} {Fs : List AnnotTerm}
    {e : AnnotTerm} (hokB : w ≠ 0 → FieldsOkB w ρ' Fs)
    (hok : WellDenoted V ρ e)
    (hval : interp V ρ e ∈ˢ sumSet w (sumFibre w ρ' [Fs ++ [idxEqAV []]]))
    (hi : i < Fs.length) : WellDenoted V ρ (projAV (i + 1) e) :=
  wellDenoted_projAV_succ_of hokB fixFibre_fibreAt hok hval hi
/-! ## (A) the typing law -/

/-- **The typing law's core at an arbitrary tag** (task #278): the
family's value at fitting parameters is a carrier of the `FibreAt`
shape, so a member projects at `i + 1` into the body's residual — the
graph regime by the fitting field spine below the tag, the squash
regime by the point. -/
theorem fixEntryTypingCoreT {w J nP nF i : Nat} {pps ds eds : List (Nat × Nat × AnnotTerm)}
    {L bodyL R : AnnotTerm} {S : (Nat → V) → V} {sorts : List Level} {ψ : Name → Nat}
    (hLlam : L = mkLamsAV (pps.map fun d => (w + 1, d.2.2)) bodyL)
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP) (hlenEds : eds.length = nP + 1)
    (hiff : ∀ ρ : Nat → V, Sat V (pps.map (·.2.2)).reverse ρ ↔
      Sat V ((ds.take nP).map (·.2.2)).reverse ρ)
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2)))
    (hsorts : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    {used : Nat → Bool}
    (hguard : w = 0 → (sorts.getD i .zero).eval ψ = 0 ∧
      ∀ j, j < i → used j = true → (sorts.getD j .zero).eval ψ = 0)
    (hfree : ∀ j, j < i → used j = false →
      ∃ X : AnnotTerm, ((ds.drop nP).map (·.2.2)).getD i default = X.liftN 1 (i - 1 - j))
    (hi : i < nF)
    -- the family at the parameters is the carrier
    (hfold : ∀ (ρ : Nat → V) (ts : List V), SpineFit ρ (pps.map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ L) = S (consList ts ρ))
    (hfib : ∀ ρ' : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ' →
      FibreAt w J ((ds.drop nP).map (·.2.2)) ρ' (S ρ'))
    (hres : ∀ ρ : Nat → V, ρ 0 ∈ˢ S (fun j => ρ (j + 1)) →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
      interp V ρ R
        = interp V (consList (projList i (dropS 1 (ρ 0))) (fun j => ρ (j + 1)))
            (((ds.drop nP).map (·.2.2)).getD i default))
    (hokR : ∀ ρ : Nat → V, ρ 0 ∈ˢ S (fun j => ρ (j + 1)) →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
      WellDenotedV V ρ R) :
    ∀ (ρ : Nat → V) (vs : List AnnotTerm) (x rest : AnnotTerm),
      vs.length = nP →
      WellDenotedV V ρ (AnnotTerm.mkAppN L vs) →
      WellDenotedV V ρ x →
      interp V ρ x ∈ˢ interp V ρ (AnnotTerm.mkAppN L vs) →
      ConLeche.Model.AnnotTerm.peelPis (mkPisAV eds R) (vs ++ [x]) = some rest →
      WellDenotedV V ρ (projAV (i + 1) x) ∧ WellDenotedV V ρ rest ∧
        interp V ρ (projAV (i + 1) x) ∈ˢ interp V ρ rest := by
  intro ρ vs x rest hlenVs hokApp hokx hmem hpeel
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  -- the parameter fit
  have hsp : SpineFit ρ (pps.map (·.2.2)) (vs.map (interp V ρ)) := by
    have h := spineFit_of_wellDenotedV_mkAppN_lam (lds := pps.map fun d => (w + 1, d.2.2))
      (b := bodyL) (σ := ρ)
      (fun d hd => by obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd; exact Nat.succ_ne_zero w)
      hokApp (by rw [hLlam]) (by simp [hlenVs, hlenPps])
    simpa [List.map_map, Function.comp_def] using h
  have hlenAs : (vs.map (interp V ρ)).length = nP := by simp [hlenVs]
  -- the member of the carrier
  have hx : interp V ρ x ∈ˢ S (consList (vs.map (interp V ρ)) ρ) := by
    rw [interp_mkAppN_foldl, hfold ρ _ hsp] at hmem
    exact hmem
  -- the constructor's parameter frame
  have hspC : SpineFit ρ ((ds.take nP).map (·.2.2)) (vs.map (interp V ρ)) :=
    (spineFit_iff_of_sat_iff (by simp [hlenPps, hlenDs]) hiff ρ _ (by simp [hlenVs, hlenPps])).mp hsp
  have hsatC : Sat V ((ds.take nP).map (·.2.2)).reverse (consList (vs.map (interp V ρ)) ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hspC
    rwa [List.append_nil] at this
  -- the frame at the subject's chain
  have hchain : chain V ρ (vs ++ [x]) = cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ) := by
    unfold chain
    rw [consN_eq_consList, List.map_append, consList_append]
    rfl
  have hframeX : (cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ)) 0
      ∈ˢ S (fun j => (cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ)) (j + 1)) := hx
  have hframeS : Sat V ((ds.take nP).map (·.2.2)).reverse
      (fun j => (cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ)) (j + 1)) := hsatC
  -- the residual
  have hrest : rest = ConLeche.Model.AnnotTerm.instSeq (vs ++ [x]) nP R := by
    have h := peelPis_of_piTeleAV (nP + 1) (by rw [← hlenEds]; exact piTeleAV_mkPisAV eds R)
      (ws := vs ++ [x]) (by simp [hlenVs])
    rw [hpeel] at h
    have := Option.some.inj h
    rwa [Nat.add_sub_cancel] at this
  have hlen' : ConLeche.Model.AnnotTerm.instSeq (vs ++ [x]) nP R
      = ConLeche.Model.AnnotTerm.instSeq (vs ++ [x]) ((vs ++ [x]).length - 1) R := by
    simp [hlenVs]
  have hinterpRest : interp V ρ rest
      = interp V (consList (projList i (dropS 1 (interp V ρ x))) (consList (vs.map (interp V ρ)) ρ))
          (((ds.drop nP).map (·.2.2)).getD i default) := by
    rw [hrest, hlen', interp_instSeq, hchain, hres _ hframeX hframeS]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · -- the projection's grading
    exact ⟨wellDenoted_projAV_succ_of (fun hw => hokB _ hsatC) (hfib _ hsatC) hokx.1 hx
      (by rw [hlenFs]; exact hi), projAV_validV hokx.2⟩
  · -- the residual's grading
    rw [hrest, hlen']
    refine wellDenotedV_instSeq _ ?_ ?_
    · intro w' hw'
      rcases List.mem_append.mp hw' with h | h
      · exact WellDenotedV_mkAppN_args vs hokApp w' h
      · rw [List.mem_singleton] at h; subst h; exact hokx
    · rw [hchain]; exact hokR _ hframeX hframeS
  · -- the membership
    rw [hinterpRest, projAV_interp]
    by_cases hw : w = 0
    · -- squash: the point in the proof field at the point prefix,
      -- which agrees with a fitting prefix at every used slot
      subst hw
      obtain ⟨hpt, as', hspAs⟩ := (hfib _ hsatC).squash rfl _ hx
      obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)
      have hz := hsorts _ hsatC i hi _ hpre
      rw [(hguard rfl).1] at hz
      have hval := mem_univ_zero hz hnext
      rw [hval] at hnext
      rw [hpt, projS_pt, dropS_pt, projList_pt]
      have hlenTake : (as'.take i).length = i := spineFit_take_length hspAs (by rw [hlenFs]; omega)
      rw [interp_congr_lifts i
        (free_of_diff hlenDs hi (hsorts _ hsatC) (hguard rfl).2 hfree hspAs)
        (consList_prefix_agree hlenTake _).2]
      exact hnext
    · -- graph: the fitting field spine below the tag
      obtain ⟨fs, heq, hspF⟩ := (hfib _ hsatC).graph hw _ hx
      have hlenF : fs.length = nF := by rw [hspF.length_eq, hlenFs]
      obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hspF (by rw [hlenFs]; exact hi)
      rw [heq, projS_succ_inj, dropS_one_inj, projS_mkTower_getD (by rw [hlenF]; exact hi),
        projList_mkTower_take (by rw [hlenF]; omega)]
      exact hnext

/-- The typing law's core on the fixpoint route (task #210 Part A):
the one-constructor fibre at tag `0`. -/
theorem fixEntryTypingCore {u w nP nF i : Nat} {pps ds eds : List (Nat × Nat × AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {eiss : List (List (List AnnotTerm))} {Fss₀ Ess : List (List AnnotTerm)}
    {R : AnnotTerm} {sorts : List Level} {ψ : Name → Nat}
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP) (hlenEds : eds.length = nP + 1)
    (hiff : ∀ ρ : Nat → V, Sat V (pps.map (·.2.2)).reverse ρ ↔
      Sat V ((ds.take nP).map (·.2.2)).reverse ρ)
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2)))
    (hsorts : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    {used : Nat → Bool}
    (hguard : w = 0 → (sorts.getD i .zero).eval ψ = 0 ∧
      ∀ j, j < i → used j = true → (sorts.getD j .zero).eval ψ = 0)
    (hfree : ∀ j, j < i → used j = false →
      ∃ X : AnnotTerm, ((ds.drop nP).map (·.2.2)).getD i default = X.liftN 1 (i - 1 - j))
    (hi : i < nF)
    -- the family at the parameters is the one-constructor fibre
    (hfold : ∀ (ρ : Nat → V) (ts : List V), SpineFit ρ (pps.map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ (nativeTyAVI u w pps [] rss tlss eiss Fss₀ Ess))
        = sumSet w (sumFibre w (consList ts ρ)
            [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]))
    (hres : ∀ ρ : Nat → V,
      ρ 0 ∈ˢ sumSet w (sumFibre w (fun j => ρ (j + 1)) [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]) →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
      interp V ρ R
        = interp V (consList (projList i (dropS 1 (ρ 0))) (fun j => ρ (j + 1)))
            (((ds.drop nP).map (·.2.2)).getD i default))
    (hokR : ∀ ρ : Nat → V,
      ρ 0 ∈ˢ sumSet w (sumFibre w (fun j => ρ (j + 1)) [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]) →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
      WellDenotedV V ρ R) :
    ∀ (ρ : Nat → V) (vs : List AnnotTerm) (x rest : AnnotTerm),
      vs.length = nP →
      WellDenotedV V ρ (AnnotTerm.mkAppN (nativeTyAVI u w pps [] rss tlss eiss Fss₀ Ess) vs) →
      WellDenotedV V ρ x →
      interp V ρ x ∈ˢ interp V ρ
        (AnnotTerm.mkAppN (nativeTyAVI u w pps [] rss tlss eiss Fss₀ Ess) vs) →
      ConLeche.Model.AnnotTerm.peelPis (mkPisAV eds R) (vs ++ [x]) = some rest →
      WellDenotedV V ρ (projAV (i + 1) x) ∧ WellDenotedV V ρ rest ∧
        interp V ρ (projAV (i + 1) x) ∈ˢ interp V ρ rest :=
  fixEntryTypingCoreT (J := 0)
    (S := fun ρ' => sumSet w (sumFibre w ρ' [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]))
    rfl hlenDs hlenPps hlenEds hiff hokB hsorts hguard hfree hi hfold
    (fun _ _ => fixFibre_fibreAt) hres hokR

/-! ## (B) the iota law -/

/-- **The iota law's core at an arbitrary tag** (task #278): the
projection of a graded constructor application is the selected field
(`sumMkAV_fold`: the application folds to the tagged tuple). -/
theorem fixEntryIotaCoreT {w J nP nF i : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {Fss : List (List AnnotTerm)} {ρ : Nat → V}
    (hw : w ≠ 0) (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hFss : Fss[J]? = some ((ds.drop nP).map (·.2.2)))
    (hokU : ∀ ρ' : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ' →
      SumFieldsOkB w ρ' (uChains Fss))
    (ys : List AnnotTerm) (hlen : ys.length = nP + nF)
    (hok : WellDenotedV V ρ (AnnotTerm.mkAppN
      (sumMkAV w J ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys)) :
    interp V ρ (projAV (i + 1) (AnnotTerm.mkAppN
        (sumMkAV w J ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys))
      = interp V ρ (ys.getD (nP + i) default) := by
  have hsp : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp V ρ)) := by
    have h := spineFit_of_wellDenotedV_mkAppN_lam (lds := ds.map fun d => (w, d.2.2))
      (b := sumInjAtAV w (uChains Fss) ((ds.drop nP).map (·.2.2)).length
        (numeralAV J) (mkTowerGoU w ((ds.drop nP).map (·.2.2)) (idxEqAV [])))
      (σ := ρ)
      (fun d hd => by obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd; exact hw)
      hok rfl (by simp [hlen, hlenDs])
    simpa [List.map_map, Function.comp_def] using h
  rw [show ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) from by
    rw [← List.map_append, List.take_append_drop]] at hsp
  obtain ⟨as, bs, heq, hsp₁, hsp₂⟩ := spineFit_append_inv hsp
  have hlenAs : as.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlenBs : bs.length = nF := by rw [hsp₂.length_eq]; simp [hlenDs]
  have hsat : Sat V ((ds.take nP).map (·.2.2)).reverse (consList as ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  have hfold := sumMkAV_fold (pds := ds.take nP) (fds := ds.drop nP) (j := J) hw hsp₁ hsp₂
    (hokU _ hsat) (by rw [uChains_getElem?, hFss]; rfl)
  rw [List.take_append_drop] at hfold
  rw [projAV_interp, interp_mkAppN_foldl, heq, hfold, projS_succ_inj,
    projS_mkTower_getD (by rw [hlenBs]; exact hi)]
  -- the selected argument
  have hlt : nP + i < ys.length := by omega
  rw [List.getD_eq_getElem?_getD (l := ys), List.getElem?_eq_getElem hlt, Option.getD_some]
  have h1 : (ys.map (interp V ρ))[nP + i]? = some (interp V ρ ys[nP + i]) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
  rw [heq, List.getElem?_append_right (by omega), hlenAs, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)] at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenBs]; exact hi), Option.getD_some]
  exact Option.some.inj h1

/-- The iota law's core on the fixpoint route (task #210 Part A). -/
theorem fixEntryIotaCore {w nP nF i : Nat} {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    (hw : w ≠ 0) (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2)))
    (ys : List AnnotTerm) (hlen : ys.length = nP + nF)
    (hok : WellDenotedV V ρ (AnnotTerm.mkAppN
      (sumMkAV w 0 ds ((ds.drop nP).map (·.2.2)) (uChains [(ds.drop nP).map (·.2.2)])) ys)) :
    interp V ρ (projAV (i + 1) (AnnotTerm.mkAppN
        (sumMkAV w 0 ds ((ds.drop nP).map (·.2.2)) (uChains [(ds.drop nP).map (·.2.2)])) ys))
      = interp V ρ (ys.getD (nP + i) default) :=
  fixEntryIotaCoreT hw hlenDs hi rfl
    (fun ρ' hρ' => SumFieldsOkB_uChains (by
      intro Fs hFs
      rw [List.mem_singleton] at hFs
      subst hFs
      exact hokB ρ' hρ'))
    ys hlen hok

/-- **The iota law at a squash instantiation, at an arbitrary tag**:
the constructor application is the point, so is its projection, and
the selected field is a proposition's member. -/
theorem fixEntryIotaCoreZeroT {J nP nF i : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {Fss : List (List AnnotTerm)} {ρ : Nat → V} {sorts : List Level} {ψ : Name → Nat}
    (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hsorts : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    (hz : (sorts.getD i .zero).eval ψ = 0)
    (ys : List AnnotTerm) (hlen : ys.length = nP + nF)
    (hsp : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp V ρ))) :
    interp V ρ (projAV (i + 1) (AnnotTerm.mkAppN
        (sumMkAV 0 J ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys))
      = interp V ρ (ys.getD (nP + i) default) := by
  rw [projAV_interp, interp_mkAppN_foldl, sumMkAV_zero, foldl_app_pt, projS_pt]
  rw [show ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) from by
    rw [← List.map_append, List.take_append_drop]] at hsp
  obtain ⟨as, bs, heq, hsp₁, hsp₂⟩ := spineFit_append_inv hsp
  have hlenAs : as.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlenBs : bs.length = nF := by rw [hsp₂.length_eq]; simp [hlenDs]
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hsat : Sat V ((ds.take nP).map (·.2.2)).reverse (consList as ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hsp₂ (by rw [hlenFs]; exact hi)
  have hz' := hsorts _ hsat i hi _ hpre
  rw [hz] at hz'
  have hval : bs.getD i pt = pt := mem_univ_zero hz' hnext
  have hlt : nP + i < ys.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  have h1 : (ys.map (interp V ρ))[nP + i]? = some (interp V ρ ys[nP + i]) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
  rw [heq, List.getElem?_append_right (by omega), hlenAs, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)] at h1
  have h2 : bs[i] = bs.getD i pt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)]
    rfl
  rw [← Option.some.inj h1, h2, hval]

/-- The iota law at a squash instantiation: the constructor application
is the point, so is its projection, and the selected field is a
proposition's member. -/
theorem fixEntryIotaCoreZero {nP nF i : Nat} {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    {sorts : List Level} {ψ : Name → Nat}
    (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hsorts : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    (hz : (sorts.getD i .zero).eval ψ = 0)
    (ys : List AnnotTerm) (hlen : ys.length = nP + nF)
    (hsp : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp V ρ))) :
    interp V ρ (projAV (i + 1) (AnnotTerm.mkAppN
        (sumMkAV 0 0 ds ((ds.drop nP).map (·.2.2)) (uChains [(ds.drop nP).map (·.2.2)])) ys))
      = interp V ρ (ys.getD (nP + i) default) :=
  fixEntryIotaCoreZeroT hlenDs hi hsorts hz ys hlen hsp

/-! ## (C) the η law -/

/-- **The η law's core at an arbitrary tag** (task #278): a member of
the carrier is the constructor at the parameters and its own
projections below the tag. -/
theorem fixEntryEtaCoreT {w J nP nF : Nat} {pps ds : List (Nat × Nat × AnnotTerm)}
    {Fss : List (List AnnotTerm)} {L : AnnotTerm} {S : (Nat → V) → V} {ρ : Nat → V}
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP)
    (hiff : ∀ ρ : Nat → V, Sat V (pps.map (·.2.2)).reverse ρ ↔
      Sat V ((ds.take nP).map (·.2.2)).reverse ρ)
    (hFss : Fss[J]? = some ((ds.drop nP).map (·.2.2)))
    (hokU : ∀ ρ' : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ' →
      SumFieldsOkB w ρ' (uChains Fss))
    (hfold : ∀ (ρ : Nat → V) (ts : List V), SpineFit ρ (pps.map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ L) = S (consList ts ρ))
    (hfib : ∀ ρ' : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ' →
      FibreAt w J ((ds.drop nP).map (·.2.2)) ρ' (S ρ'))
    (ts : List V) (x : V) (hlen : ts.length = nP)
    (hsp : SpineFit ρ (pps.map (·.2.2)) ts)
    (hx : x ∈ˢ ts.foldl SetTheory.app (interp V ρ L)) :
    x = (ts ++ (List.range nF).map fun j => projS (j + 1) x).foldl SetTheory.app
      (interp V ρ (sumMkAV w J ds ((ds.drop nP).map (·.2.2)) (uChains Fss))) := by
  rw [hfold ρ ts hsp] at hx
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hsp₁ : SpineFit ρ ((ds.take nP).map (·.2.2)) ts :=
    (spineFit_iff_of_sat_iff (by simp [hlenPps, hlenDs]) hiff ρ ts (by simp [hlen, hlenPps])).mp hsp
  have hsat : Sat V ((ds.take nP).map (·.2.2)).reverse (consList ts ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  by_cases hw : w = 0
  · subst hw
    obtain ⟨hpt, -⟩ := (hfib _ hsat).squash rfl _ hx
    rw [hpt, sumMkAV_zero, foldl_app_pt]
  · obtain ⟨fs, heq, hspF⟩ := (hfib _ hsat).graph hw _ hx
    have hlenF : fs.length = nF := by rw [hspF.length_eq, hlenFs]
    have hfold' := sumMkAV_fold (pds := ds.take nP) (fds := ds.drop nP) (j := J) hw hsp₁ hspF
      (hokU _ hsat) (by rw [uChains_getElem?, hFss]; rfl)
    rw [List.take_append_drop] at hfold'
    -- the projections past the tag are the tuple's fields
    have hprojs : ((List.range nF).map fun j => projS (j + 1) x) = fs := by
      rw [heq]
      have h1 : ((List.range nF).map fun j => projS (j + 1) (inj J (mkTower (fs ++ [pt]))))
          = (List.range nF).map fun j => projS j (mkTower (fs ++ [pt])) :=
        List.map_congr_left fun j _ => projS_succ_inj j J _
      rw [h1, ← projList_eq_map_range, ← hlenF, projList_mkTower_take (Nat.le_refl _),
        List.take_length]
    rw [hprojs, hfold', heq]

/-- The η law's core on the fixpoint route (task #210 Part A). -/
theorem fixEntryEtaCore {u w nP nF : Nat} {pps ds : List (Nat × Nat × AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {eiss : List (List (List AnnotTerm))} {Fss₀ Ess : List (List AnnotTerm)} {ρ : Nat → V}
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP)
    (hiff : ∀ ρ : Nat → V, Sat V (pps.map (·.2.2)).reverse ρ ↔
      Sat V ((ds.take nP).map (·.2.2)).reverse ρ)
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2)))
    (hfold : ∀ (ρ : Nat → V) (ts : List V), SpineFit ρ (pps.map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ (nativeTyAVI u w pps [] rss tlss eiss Fss₀ Ess))
        = sumSet w (sumFibre w (consList ts ρ) [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]))
    (ts : List V) (x : V) (hlen : ts.length = nP)
    (hsp : SpineFit ρ (pps.map (·.2.2)) ts)
    (hx : x ∈ˢ ts.foldl SetTheory.app
      (interp V ρ (nativeTyAVI u w pps [] rss tlss eiss Fss₀ Ess))) :
    x = (ts ++ (List.range nF).map fun j => projS (j + 1) x).foldl SetTheory.app
      (interp V ρ (sumMkAV w 0 ds ((ds.drop nP).map (·.2.2))
        (uChains [(ds.drop nP).map (·.2.2)]))) :=
  fixEntryEtaCoreT (J := 0)
    (S := fun ρ' => sumSet w (sumFibre w ρ' [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]))
    hlenDs hlenPps hiff rfl
    (fun ρ' hρ' => SumFieldsOkB_uChains (by
      intro Fs hFs
      rw [List.mem_singleton] at hFs
      subst hFs
      exact hokB ρ' hρ'))
    hfold (fun _ _ => fixFibre_fibreAt) ts x hlen hsp hx

end ConLeche.Model
