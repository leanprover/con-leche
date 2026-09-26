module

public import ConLeche.Semantics.Tower.BlockLeafI
import ConLeche.Semantics.Tower.BlockFamI
public import ConLeche.Semantics.SubstAV
import ConLeche.Semantics.Tower.BlockRecI
@[expose] public section

/-!
# The block operator's HOLE chains (lane HOLE2, checkpoint (d))

Charter item 2: a block's operator is the interpretation of its
constructor types with HOLES at the members.  A constructor's fields
with holes (`LfpDatum.fields`, `Model/Annot/BlockLfp.lean`) are read at
the parameters, then one variable per member (the holes), then the
earlier fields.  The block's operator term (`blockPhiG`/`blockTyG`,
`BlockLeafI.lean`) is generic in its chains; this module builds the
chains from the fields with holes, with NO field classification: every
field, whatever it mentions, is the same substitution.

**The hole terms.**  Under the operator's binders (the index tuple `t`
innermost, then the family tuple `Y`, then the parameter frame), member
`m`'s hole is replaced by `holeTmAV`: the λ-tower over the member's own
parameter telescope (read below the parameter frame) and then its index
telescope READ AT THE ACTUAL PARAMETERS, of `Y`'s component `m` at the
tuple of the index variables.  It is graded at every family tuple of the
tuple space (`holeTmAV_wellDenoted`).  It is not the model's hole value
(`LfpDatum.holeVal`, whose index domains follow its own λ-bound
parameters), but the two agree APPLIED TO THE ACTUAL PARAMETERS, which is
the only way a hole occurs (`HoleApp`, lane CONTSEM's M3); the model
tier relates them by `interp_congr_holeApp`.

**The chains.**  Field `i` (below `i` earlier fields) is substituted in
parallel (`AnnotTerm.substAV`, lane CONTSEM) at the cut `i`: hole
variables by the hole terms, the parameter frame's variables moved past
`t` and `Y` (`holeTau`).  The result index readings likewise, below all
fields, as the chain's index equations (`holeEqsAV`).  At a family tuple
`Y` the chain's entries read as the fields at the frame whose holes hold
the hole terms' values (`spineFit_holeEntsAV`, `eqAll_holeEqsAV`), and
the operator's fibre is the injections of the spines fitting them
(`blockStepG_termChs_mem_iff`, generic in terminated chains).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## Grading crosses a parallel substitution -/

/-- **A substituted term is graded** exactly when the subject is graded
at the substituted valuation, provided the substituted terms are graded
where they are read. -/
theorem WellDenoted_substAV (τ : Nat → AnnotTerm) :
    ∀ (e : AnnotTerm) (k : Nat) (ρ : Nat → V), (∀ j, WellDenoted V (shiftE k 0 ρ) (τ j)) →
      (WellDenoted V ρ (AnnotTerm.substAV τ e k) ↔ WellDenoted V (substE V τ k ρ) e) := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ hτ
    by_cases hi : i < k
    · rw [AnnotTerm.substAV_bvar_lt τ hi]; simp
    · rw [AnnotTerm.substAV_bvar_ge τ (by omega), WellDenoted_liftN]
      simp only [WellDenoted_bvar, iff_true]
      exact hτ _
  | sort u => intro k ρ _; simp [AnnotTerm.substAV]
  | const c us => intro k ρ _; simp [AnnotTerm.substAV]
  | prf => intro k ρ _; simp [AnnotTerm.substAV]
  | app f a ihf iha =>
    intro k ρ hτ
    rw [AnnotTerm.substAV_app, WellDenoted_app, WellDenoted_app, ihf k ρ hτ, iha k ρ hτ,
      interp_substAV, interp_substAV]
  | lam u A b ihA ihb =>
    intro k ρ hτ
    have hτ' : ∀ x, ∀ j, WellDenoted V (shiftE (k + 1) 0 (cons x ρ)) (τ j) := by
      intro x j; rw [shiftE_succ_cons]; exact hτ j
    rw [AnnotTerm.substAV_lam, WellDenoted_lam, WellDenoted_lam, ihA k ρ hτ, interp_substAV]
    simp only [ihb (k + 1) _ (hτ' _), interp_substAV, cons_substE]
  | pi u v A B ihA ihB =>
    intro k ρ hτ
    have hτ' : ∀ x, ∀ j, WellDenoted V (shiftE (k + 1) 0 (cons x ρ)) (τ j) := by
      intro x j; rw [shiftE_succ_cons]; exact hτ j
    rw [AnnotTerm.substAV_pi, WellDenoted_pi, WellDenoted_pi, ihA k ρ hτ, interp_substAV]
    simp only [ihB (k + 1) _ (hτ' _), cons_substE]
  | eqE a b iha ihb =>
    intro k ρ hτ
    show WellDenoted V ρ (.eqE _ _) ↔ WellDenoted V _ (.eqE _ _)
    rw [WellDenoted_eqE, WellDenoted_eqE, iha k ρ hτ, ihb k ρ hτ]
  | fst e ih =>
    intro k ρ hτ
    rw [AnnotTerm.substAV_fst, WellDenoted_fst, WellDenoted_fst, ih k ρ hτ, interp_substAV]
  | snd e ih =>
    intro k ρ hτ
    rw [AnnotTerm.substAV_snd, WellDenoted_snd, WellDenoted_snd, ih k ρ hτ, interp_substAV]

/-! ## The hole terms -/

/-- **Member `m`'s hole term** under the operator's binders `t`, `Y`
(then the parameter frame): the λ-tower over the member's own parameter
telescope `Ps` (read below the parameter frame) and its index telescope
`Is` read at the ACTUAL parameters, of `Y`'s component `m` at the tuple
of the index variables. -/
def holeTmAV (u m : Nat) (Ps Is : List AnnotTerm) : AnnotTerm :=
  mkLamsAV ((liftFields (Ps.length + 2) 0 Ps ++ liftFields (Ps.length + 2) 0 Is).map (1, ·))
    (.app (projAV m (.bvar (Ps.length + Is.length + 1)))
      (mkTowerGo u (liftFields (Ps.length + 2) 0 Is)))

/-- **The hole substitution**: variable `j < k` (member `k - 1 - j`'s
hole: the last member is innermost) by that member's hole term, a
parameter-frame variable `k + j` moved past `t` and `Y`. -/
def holeTau (k : Nat) (H : Nat → AnnotTerm) : Nat → AnnotTerm :=
  fun j => if j < k then H (k - 1 - j) else .bvar (j - k + 2)

/-- A constructor's fields with holes as chain entries: field `i`
substituted at the cut `i`. -/
def holeEntsAV (k : Nat) (H : Nat → AnnotTerm) : Nat → List AnnotTerm → List AnnotTerm
  | _, [] => []
  | i, F :: Fs => AnnotTerm.substAV (holeTau k H) F i :: holeEntsAV k H (i + 1) Fs

/-- A constructor's result index readings with holes as the chain's
index equations (below its `nF` fields). -/
def holeEqsAV (k : Nat) (H : Nat → AnnotTerm) (nIdx nF : Nat) (Es : List AnnotTerm) :
    List (AnnotTerm × AnnotTerm) :=
  (List.range nIdx).map fun l =>
    (AnnotTerm.substAV (holeTau k H) (Es.getD l default) nF, projAV l (.bvar nF))

/-- **Terminated chains**: per member, per constructor, the entries and
then the index equations. -/
def termChs (Ents : Nat → List (List AnnotTerm))
    (Eqs : Nat → List (List (AnnotTerm × AnnotTerm))) : Nat → List (List AnnotTerm) :=
  fun m => (List.range (Ents m).length).map fun j =>
    (Ents m).getD j [] ++ [idxEqAV ((Eqs m).getD j [])]

/-- **The block's hole chains**: member `m`'s constructors' fields with
holes `Fsss m` and result index readings `Esss m`, member `m` having
`nIdxs m` indices, the holes the terms `H`. -/
def holeChs (k : Nat) (H : Nat → AnnotTerm) (nIdxs : Nat → Nat)
    (Fsss Esss : Nat → List (List AnnotTerm)) : Nat → List (List AnnotTerm) :=
  termChs (fun m => (Fsss m).map (holeEntsAV k H 0))
    (fun m => (List.range (Fsss m).length).map fun j =>
      holeEqsAV k H (nIdxs m) ((Fsss m).getD j []).length ((Esss m).getD j []))

omit [SetTheory V] in
theorem holeEntsAV_length (k : Nat) (H : Nat → AnnotTerm) :
    ∀ (i : Nat) (Fs : List AnnotTerm), (holeEntsAV k H i Fs).length = Fs.length
  | _, [] => rfl
  | i, _ :: Fs => by simp [holeEntsAV, holeEntsAV_length k H (i + 1) Fs]


/-! ## Reading the hole chains -/

/-- **The substituted valuation IS the hole frame**: at the operator's
frame, position `j < k` holds member `k - 1 - j`'s hole term's value,
the rest is the parameter frame. -/
theorem substE_holeTau {k : Nat} {H : Nat → AnnotTerm} {ρp : Nat → V} {t Y : V}
    {hv : Nat → V} (hH : ∀ m, m < k → interp V (cons t (cons Y ρp)) (H m) = hv m) :
    substE V (holeTau k H) 0 (cons t (cons Y ρp)) = consList ((List.range k).map hv) ρp := by
  funext j
  have hlen : ((List.range k).map hv).length = k := by simp
  unfold substE
  rw [if_neg (Nat.not_lt_zero _), shiftE_zero_zero, Nat.sub_zero]
  unfold holeTau
  by_cases hj : j < k
  · rw [if_pos hj, hH _ (by omega), consList_getD_of_lt _ _ _ (by rw [hlen]; exact hj), hlen,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · rw [if_neg hj, interp_bvar]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + k := ⟨j - k, by omega⟩
    rw [show i + k - k + 2 = i + 2 by omega]
    have := consList_apply_add ((List.range k).map hv) ρp i
    rw [hlen] at this
    rw [this]
    rfl

/-- **The entries fit where the fields with holes fit** at the frame the
substitution produces, below any common prefix. -/
theorem spineFit_holeEntsAV (k : Nat) (H : Nat → AnnotTerm) :
    ∀ (Fs : List AnnotTerm) (as : List V) (σ : Nat → V) (fs : List V),
      SpineFit (consList as σ) (holeEntsAV k H as.length Fs) fs ↔
        SpineFit (consList as (substE V (holeTau k H) 0 σ)) Fs fs
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | F :: Fs, as, σ, f :: fs => by
    show (f ∈ˢ interp V (consList as σ) (AnnotTerm.substAV (holeTau k H) F as.length) ∧ _) ↔
      (f ∈ˢ interp V _ F ∧ _)
    have hs : substE V (holeTau k H) as.length (consList as σ)
        = consList as (substE V (holeTau k H) 0 σ) := by
      have := substE_consList V (holeTau k H) as 0 σ
      rwa [Nat.add_zero] at this
    rw [interp_substAV, hs]
    refine and_congr Iff.rfl ?_
    have := spineFit_holeEntsAV k H Fs (as ++ [f]) σ fs
    rw [List.length_append, List.length_singleton] at this
    rw [consList_append, consList_append] at this
    exact this

/-- **The index equations hold** exactly when the result index readings
with holes, at the hole frame and the fields, are the index tuple's
components. -/
theorem eqAll_holeEqsAV {k : Nat} {H : Nat → AnnotTerm} {ρp : Nat → V} {t Y : V}
    {n nF : Nat} {Es : List AnnotTerm} {fs : List V} (hlen : fs.length = nF) :
    EqAll (consList fs (cons t (cons Y ρp))) (holeEqsAV k H n nF Es) ↔
      ∀ l, l < n → interp V (consList fs (substE V (holeTau k H) 0 (cons t (cons Y ρp))))
        (Es.getD l default) = projS l t := by
  have hs : substE V (holeTau k H) nF (consList fs (cons t (cons Y ρp)))
      = consList fs (substE V (holeTau k H) 0 (cons t (cons Y ρp))) := by
    subst hlen
    have := substE_consList V (holeTau k H) fs 0 (cons t (cons Y ρp))
    rwa [Nat.add_zero] at this
  have hproj : ∀ l, interp V (consList fs (cons t (cons Y ρp))) (projAV l (.bvar nF))
      = projS l t := by
    intro l
    subst hlen
    rw [projAV_interp, interp_bvar, Xframe_t]
  unfold EqAll holeEqsAV
  constructor
  · intro h l hl
    have := h _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)
    rw [interp_substAV, hs, hproj] at this
    exact this
  · intro h e he
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
    show interp V _ (AnnotTerm.substAV _ _ _) = interp V _ (projAV _ _)
    rw [interp_substAV, hs, hproj]
    exact h l (List.mem_range.mp hl)

/-! ## The operator's fibre at terminated chains -/

/-- **The tagged union of terminated chains, at any frame**: an element
is the injection of a spine fitting one of the entries whose index
equations hold — the tag the chain's position, the point at a
`Prop`-valued sort.  No premise: the chains' grading is not needed to
read the union. -/
theorem sumSet_termChs_mem_iff {w : Nat} {σ : Nat → V}
    {Ents : List (List AnnotTerm)} {Eqs : List (List (AnnotTerm × AnnotTerm))} {x : V} :
    x ∈ˢ sumSet w (sumFibre w σ ((List.range Ents.length).map fun j =>
        Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])])) ↔
      ∃ j fs, j < Ents.length ∧ SpineFit σ (Ents.getD j []) fs ∧
        EqAll (consList fs σ) (Eqs.getD j []) ∧
        x = (if w = 0 then (pt : V) else inj j (mkTower (fs ++ [pt]))) := by
  have hget : ∀ j, ((List.range Ents.length).map fun j =>
      Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])])[j]? = if j < Ents.length then
        some (Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])]) else none := by
    intro j
    rw [List.getElem?_map]
    split
    · next h => rw [List.getElem?_range h]; rfl
    · next h => rw [List.getElem?_eq_none (by simpa using h)]; rfl
  constructor
  · intro hx
    by_cases hw : w = 0
    · subst hw
      obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx
      unfold sumFibre at ha
      rw [hget] at ha
      by_cases hj : j < Ents.length
      · rw [if_pos hj] at ha
        obtain ⟨-, as, hfit⟩ := towerSet_zero_elim _ ha
        obtain ⟨fs, -, hsp, hall⟩ := spineFit_append_idxEq.mp (fitsS_teleOfFields.mp hfit)
        exact ⟨j, fs, hj, hsp, hall, by rw [if_pos rfl]⟩
      · rw [if_neg hj] at ha
        exact absurd ha (not_mem_empty _)
    · obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw hx
      unfold sumFibre at ha
      rw [hget] at ha
      by_cases hj : j < Ents.length
      · rw [if_pos hj] at ha
        obtain ⟨hfit, heta⟩ := towerSet_elim_teleOfFields hw ha
        obtain ⟨fs, hfs, hsp, hall⟩ := spineFit_append_idxEq.mp hfit
        refine ⟨j, fs, hj, hsp, hall, ?_⟩
        rw [if_neg hw, heta, hfs]
      · rw [if_neg hj] at ha
        exact absurd ha (not_mem_empty _)
  · rintro ⟨j, fs, hj, hsp, hall, rfl⟩
    have hspE : SpineFit σ (Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])])
        (fs ++ [pt]) := spineFit_append_idxEq.mpr ⟨fs, rfl, hsp, hall⟩
    have hfib : sumFibre w σ ((List.range Ents.length).map fun j =>
          Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])]) j
        = towerSet w (teleOfFields σ (Ents.getD j [] ++ [idxEqAV (Eqs.getD j [])])) :=
      sumFibre_of_getElem? (by rw [hget, if_pos hj])
    by_cases hw : w = 0
    · subst hw
      rw [if_pos rfl]
      refine pt_mem_sumSet_zero (i := j) (a := pt) ?_
      rw [hfib]
      exact pt_mem_tower_teleOfFields hspE
    · rw [if_neg hw]
      refine inj_mem hw ?_
      rw [hfib]
      exact mkTower_mem_teleOfFields hw hspE

/-- **The fibre of the operator at terminated chains**: an element is
the injection of a spine fitting one of the member's constructors'
entries whose index equations hold — the tag member-local, the point at
a `Prop`-valued block (`sumSet_termChs_mem_iff` at the operator's
frame). -/
theorem blockStepG_termChs_mem_iff {w : Nat} {ρp : Nat → V}
    {Ents : Nat → List (List AnnotTerm)} {Eqs : Nat → List (List (AnnotTerm × AnnotTerm))}
    {m : Nat} {Y t x : V} :
    x ∈ˢ blockStepG w ρp (termChs Ents Eqs) m Y t ↔
      ∃ j fs, j < (Ents m).length ∧ SpineFit (cons t (cons Y ρp)) ((Ents m).getD j []) fs ∧
        EqAll (consList fs (cons t (cons Y ρp))) ((Eqs m).getD j []) ∧
        x = (if w = 0 then (pt : V) else inj j (mkTower (fs ++ [pt]))) := by
  unfold blockStepG termChs
  exact sumSet_termChs_mem_iff

/-- **The fibre of the operator at the hole chains**: the injections of
the spines fitting a constructor's fields with holes at the hole frame,
whose result index readings there are the index tuple's components. -/
theorem blockStepG_holeChs_mem_iff {w k : Nat} {ρp : Nat → V} {H : Nat → AnnotTerm}
    {nIdxs : Nat → Nat} {Fsss Esss : Nat → List (List AnnotTerm)}
    {m : Nat} {Y t x : V} :
    x ∈ˢ blockStepG w ρp (holeChs k H nIdxs Fsss Esss) m Y t ↔
      ∃ j fs, j < (Fsss m).length ∧
        SpineFit (substE V (holeTau k H) 0 (cons t (cons Y ρp))) ((Fsss m).getD j []) fs ∧
        (∀ l, l < nIdxs m → interp V (consList fs (substE V (holeTau k H) 0 (cons t (cons Y ρp))))
          (((Esss m).getD j []).getD l default) = projS l t) ∧
        x = (if w = 0 then (pt : V) else inj j (mkTower (fs ++ [pt]))) := by
  unfold holeChs
  rw [blockStepG_termChs_mem_iff]
  simp only [List.length_map]
  refine exists_congr fun j => exists_congr fun fs => ?_
  constructor
  · rintro ⟨hj, hsp, hall, rfl⟩
    have hent : ((Fsss m).map (holeEntsAV k H 0)).getD j [] = holeEntsAV k H 0 ((Fsss m).getD j []) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj]; rfl
    rw [hent] at hsp
    have hsp' := (spineFit_holeEntsAV k H ((Fsss m).getD j []) [] _ fs).mp hsp
    have hlen : fs.length = ((Fsss m).getD j []).length := by
      have := hsp'.length_eq; exact this
    have heq : ((List.range (Fsss m).length).map fun j =>
        holeEqsAV k H (nIdxs m) ((Fsss m).getD j []).length ((Esss m).getD j [])).getD j []
        = holeEqsAV k H (nIdxs m) ((Fsss m).getD j []).length ((Esss m).getD j []) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl
    rw [heq] at hall
    exact ⟨hj, hsp', (eqAll_holeEqsAV hlen).mp hall, rfl⟩
  · rintro ⟨hj, hsp, hall, rfl⟩
    have hent : ((Fsss m).map (holeEntsAV k H 0)).getD j [] = holeEntsAV k H 0 ((Fsss m).getD j []) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj]; rfl
    have hlen : fs.length = ((Fsss m).getD j []).length := hsp.length_eq
    have heq : ((List.range (Fsss m).length).map fun j =>
        holeEqsAV k H (nIdxs m) ((Fsss m).getD j []).length ((Esss m).getD j [])).getD j []
        = holeEqsAV k H (nIdxs m) ((Fsss m).getD j []).length ((Esss m).getD j []) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl
    refine ⟨hj, ?_, ?_, rfl⟩
    · rw [hent]; exact (spineFit_holeEntsAV k H ((Fsss m).getD j []) [] _ fs).mpr hsp
    · rw [heq]; exact (eqAll_holeEqsAV hlen).mpr hall

/-! ## Grading -/

/-- The hole substitution's terms are graded at the operator's frame when
the hole terms are. -/
theorem holeTau_wellDenoted {k : Nat} {H : Nat → AnnotTerm} {σ : Nat → V}
    (hH : ∀ m, m < k → WellDenoted V σ (H m)) (as : List V) (j : Nat) :
    WellDenoted V (shiftE as.length 0 (consList as σ)) (holeTau k H j) := by
  rw [shiftE_consList]
  unfold holeTau
  split
  · exact hH _ (by omega)
  · simp

/-- **The entries are graded** exactly when the fields with holes are,
at the frame the substitution produces. -/
theorem FieldsOkB_holeEntsAV {w k : Nat} {H : Nat → AnnotTerm} {σ : Nat → V}
    (hH : ∀ m, m < k → WellDenoted V σ (H m)) :
    ∀ (Fs : List AnnotTerm) (as : List V),
      FieldsOkB w (consList as σ) (holeEntsAV k H as.length Fs) ↔
        FieldsOkB w (consList as (substE V (holeTau k H) 0 σ)) Fs
  | [], _ => Iff.rfl
  | F :: Fs, as => by
    have hs : substE V (holeTau k H) as.length (consList as σ)
        = consList as (substE V (holeTau k H) 0 σ) := by
      have := substE_consList V (holeTau k H) as 0 σ
      rwa [Nat.add_zero] at this
    show (WellDenoted V _ (AnnotTerm.substAV _ F _) ∧ _ ∧ _) ↔ (WellDenoted V _ F ∧ _ ∧ _)
    rw [WellDenoted_substAV (holeTau k H) F as.length _ (holeTau_wellDenoted hH as),
      interp_substAV, hs]
    refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun a => imp_congr Iff.rfl ?_))
    have := FieldsOkB_holeEntsAV (w := w) hH Fs (as ++ [a])
    rw [List.length_append, List.length_singleton, consList_append, consList_append] at this
    exact this

/-- **The index equations are graded** at the operator's frame, at a
fitting field spine. -/
theorem holeEqsAV_ok {u k : Nat} {H : Nat → AnnotTerm} {ρp : Nat → V} {Ids : List AnnotTerm}
    (hI : IdxOk u ρp Ids) {Y t : V} (ht : t ∈ˢ idxSet u ρp Ids)
    (hH : ∀ m, m < k → WellDenoted V (cons t (cons Y ρp)) (H m)) {bs : List V} {nF : Nat}
    (hlen : bs.length = nF) {Es : List AnnotTerm}
    (hEok : ∀ E ∈ Es, WellDenoted V (consList bs (substE V (holeTau k H) 0 (cons t (cons Y ρp)))) E)
    (hEs : Es.length = Ids.length) :
    EqsOk (consList bs (cons t (cons Y ρp))) (holeEqsAV k H Ids.length nF Es) := by
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  have hl' : l < Ids.length := List.mem_range.mp hl
  subst hlen
  have hs : substE V (holeTau k H) bs.length (consList bs (cons t (cons Y ρp)))
      = consList bs (substE V (holeTau k H) 0 (cons t (cons Y ρp))) := by
    have := substE_consList V (holeTau k H) bs 0 (cons t (cons Y ρp))
    rwa [Nat.add_zero] at this
  refine ⟨?_, ?_⟩
  · show WellDenoted V _ (AnnotTerm.substAV _ _ _)
    rw [WellDenoted_substAV (holeTau k H) _ bs.length _ (holeTau_wellDenoted hH bs), hs]
    exact hEok _ (getD_mem_of_lt (by omega))
  · show WellDenoted V _ (projAV l (.bvar bs.length))
    refine projAV_wellDenoted_tower (w := u) (Fs := Ids) (ρ := ρp) (by simp) ?_ hI.2 hl'
    rw [interp_bvar, Xframe_t]
    exact ht

/-- A λ-tower of graph-regime binders over a graded telescope with a
body graded at every fitting spine is graded. -/
theorem mkLamsAV_one_wellDenoted {b : AnnotTerm} :
    ∀ {Ts : List AnnotTerm} {ρ : Nat → V}, FieldsOkB 0 ρ Ts →
      (∀ vs, SpineFit ρ Ts vs → WellDenoted V (consList vs ρ) b) →
      WellDenoted V ρ (mkLamsAV (Ts.map (1, ·)) b)
  | [], _, _, hb => hb [] trivial
  | T :: Ts, ρ, hT, hb => by
    show WellDenoted V ρ (.lam 1 T (mkLamsAV (Ts.map (1, ·)) b))
    rw [WellDenoted_lam]
    refine ⟨hT.1, fun x hx => mkLamsAV_one_wellDenoted (hT.2.2 x hx)
      (fun vs hvs => hb (x :: vs) ⟨hx, hvs⟩),
      fun x => ConLeche.SetTheory.sing (interp V (cons x ρ) (mkLamsAV (Ts.map (1, ·)) b)),
      fun x _ => ConLeche.SetTheory.mem_sing.mpr rfl, fun h => absurd h (by decide)⟩

theorem FieldsOkB_zero_of {w : Nat} :
    ∀ {Ts : List AnnotTerm} {ρ : Nat → V}, FieldsOkB w ρ Ts → FieldsOkB 0 ρ Ts
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1, fun h0 => absurd rfl h0, fun a ha => FieldsOkB_zero_of (h.2.2 a ha)⟩

theorem FieldsOkB_append_iff {w : Nat} :
    ∀ {A B : List AnnotTerm} {ρ : Nat → V},
      FieldsOkB w ρ A → (∀ vs, SpineFit ρ A vs → FieldsOkB w (consList vs ρ) B) →
      FieldsOkB w ρ (A ++ B)
  | [], _, _, _, hB => hB [] trivial
  | _ :: _, _, _, hA, hB => ⟨hA.1, hA.2.1, fun a ha =>
      FieldsOkB_append_iff (hA.2.2 a ha) fun vs hvs => hB (a :: vs) ⟨ha, hvs⟩⟩

theorem fieldsBound_liftFields {w n : Nat} :
    ∀ {Fs : List AnnotTerm} {k : Nat} {σ : Nat → V},
      FieldsBound w σ (liftFields n k Fs) ↔ FieldsBound w (shiftE n k σ) Fs
  | [], _, _ => Iff.rfl
  | F :: Fs, k, σ => by
    simp only [liftFields_cons, FieldsBound, interp_liftN]
    refine and_congr Iff.rfl (forall_congr' fun a => imp_congr Iff.rfl ?_)
    rw [cons_shiftE]
    exact fieldsBound_liftFields

section Hole

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}

/-- **The hole term is graded** at the operator's frame at every family
tuple of the tuple space: its parameter binders by the member's own
parameter telescope's grading (below the parameter frame), its index
binders by the member's index telescope's (at the actual parameters),
the application by the tuple space. -/
theorem holeTmAV_wellDenoted (hIall : BlockIdxOk (V := V) k uf ρp Idss) {m : Nat} (hm : m < k)
    {Ps : List AnnotTerm} (hP : FieldsOkB 0 (shiftE Ps.length 0 ρp) Ps)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) (t : V) :
    WellDenoted V (cons t (cons Y ρp)) (holeTmAV (uf m) m Ps (Idss m)) := by
  have hsh : shiftE (Ps.length + 2) 0 (cons t (cons Y ρp)) = shiftE Ps.length 0 ρp := by
    rw [show Ps.length + 2 = Ps.length + 1 + 1 by omega, shiftE_succ_cons, shiftE_succ_cons]
  have hshI : ∀ ps : List V, ps.length = Ps.length →
      shiftE (Ps.length + 2) 0 (consList ps (cons t (cons Y ρp))) = ρp := by
    intro ps hps
    have := shiftE_consList_add ps 2 (cons t (cons Y ρp))
    rw [hps] at this
    rw [this, show (2 : Nat) = 1 + 1 by rfl, shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
  unfold holeTmAV
  refine mkLamsAV_one_wellDenoted ?_ ?_
  · refine FieldsOkB_append_iff ?_ fun ps hps => ?_
    · rw [FieldsOkB_liftFields, hsh]; exact hP
    · have hlen : ps.length = Ps.length := by
        have := hps.length_eq; rwa [liftFields_length] at this
      rw [FieldsOkB_liftFields, hshI ps hlen]
      exact FieldsOkB_zero_of (hIall m hm).1
  · intro vs hvs
    obtain ⟨ps, is, rfl, hps, his⟩ := spineFit_append_split hvs
    have hlen : ps.length = Ps.length := by
      have := hps.length_eq; rwa [liftFields_length] at this
    have hlenI : is.length = (Idss m).length := by
      have := his.length_eq; rwa [liftFields_length] at this
    have hisR : SpineFit ρp (Idss m) is := by
      rw [spineFit_liftFields, hshI ps hlen] at his; exact his
    have hbd : uf m ≠ 0 → FieldsBound (uf m) (consList ps (cons t (cons Y ρp)))
        (liftFields (Ps.length + 2) 0 (Idss m)) := fun _ => by
      rw [fieldsBound_liftFields, hshI ps hlen]; exact (hIall m hm).2
    have hok : FieldsOkB (uf m) (consList ps (cons t (cons Y ρp)))
        (liftFields (Ps.length + 2) 0 (Idss m)) := by
      rw [FieldsOkB_liftFields, hshI ps hlen]; exact (hIall m hm).1
    have hY' : consList (ps ++ is) (cons t (cons Y ρp)) (Ps.length + (Idss m).length + 1) = Y := by
      have := Xframe_X ρp (ps ++ is) t Y
      rwa [List.length_append, hlen, hlenI] at this
    have htv := mkTowerGo_interp hbd his
    rw [← consList_append] at htv
    have hXm : projS m Y ∈ˢ piR (w + 1) (idxSet (uf m) ρp (Idss m)) fun _ => (univ w : V) :=
      projS_mem_famsSpaceB hm hY
    rw [WellDenoted_app]
    refine ⟨?_, ?_, w + 1, idxSet (uf m) ρp (Idss m), fun _ => (univ w : V), ?_, ?_,
      fun h => absurd h (Nat.succ_ne_zero w)⟩
    · have hFu : ∀ c, c < 0 + k → lfpFamSpace V w (idxSet (uf c) ρp (Idss c))
          ∈ˢ (univ (blockR k w uf) : V) := fun c hc =>
        famSpace_mem_blockR (by omega) (idxTyAV_facts (hIall c (by omega))).2.1
      exact projAV_wellDenoted_ndTower V (blockR_ne_zero k w uf) m k 0 _ _ hm hFu trivial
        (by rw [interp_bvar, hY']; exact hY)
    · have := mkTowerGo_wellDenoted hok his
      rwa [← consList_append] at this
    · rw [projAV_interp, interp_bvar, hY']; exact hXm
    · rw [htv]
      exact tupW_mem (u := uf m) hisR

end Hole

end ConLeche.Semantics
