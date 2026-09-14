module

public import ConLeche.Model.Inductives.NestedCtorStage
import ConLeche.Semantics.Tower.FixRecCoreI
import ConLeche.Semantics.Kit
import ConLeche.Model.Inductives.FixRuleKit
public section

/-!
# The restored constructor's leaf, typed (task #279 M-D′ D3, DESIGN §M.50)

A REAL member's constructor `T.c` is restored from its auxiliary
stored type by `restoreNested R`: the parameters and the ordinary
fields are the auxiliary ones, a copy-recursive field `Π a⃗, auxJ p⃗ e⃗`
is put back to `Π a⃗, J D⃗ e⃗` (the container at the pin's components),
the residual `T p⃗ e⃗` is unchanged.  So the restored type reads as the
Π-tower over `dsRestored` — the auxiliary domains `d.dsF Ja ψ` with
`restoreAV` at every copy-recursive position — ending in the auxiliary
body `ctorBodyAVI mpAux T nP nF ψ (Es ψ)`.

Its leaf is `restoredCtorAV`: the λ-tower over `dsRestored` (the
telescope's own bits) of the AUXILIARY constructor's leaf at the
parameters and at ψ*'s spine `restoreVarsAV` — `psiVarsAV` with no
hypotheses and the transport `restoreVia` at every copy-recursive
position (ψ of the target pin over the field's telescope,
`viaEntryAV` at the leaf frame), the field itself elsewhere.

**Typing** (`restoredCtor_typed`): the leaf inhabits the restored
tower.  At a spine `p⃗ ++ f⃗` fitting `dsRestored`, ψ*'s values
`restoreVals` fit the AUXILIARY domains (`restoreVals_fit`: off the
copy positions the domains and the values coincide and the frames
agree — `ShadowRelP` at the datum's `NoBVar` facts, the recursive
positions being leaves of no later entry; at a copy position the value
is the λ-tower over the telescope of ψ at the index values applied to
the field, in the target copy's carrier by the ONE fact of ψ, `hΨ`),
so the auxiliary constructor's leaf at `p⃗ ++ ψ*f⃗` is graded and lands
in `⟦T⟧ p⃗ e⃗[p⃗, ψ*f⃗] = ⟦T⟧ p⃗ e⃗[p⃗, f⃗]` (the index readings mention no
recursive position) — `wellDenotedV_mkAppN_of_spineFit` at the
auxiliary model's `mem_type`, then `mkLamsAV_bits_mem`.

What stays NAMED here (each in the currency the run delivers, to be
discharged at D5's assembly): the transport fact `hΨ` (`psiFinal_mem`
at the pin: ψ at index values and a container value lands in the copy's
carrier), the transports' grading at the leaf frame `hviaWD` (as
`PsiSetup.hviaWD`), the restored tower's grading `hokR`
(`whnfContent_field`'s second conjunct at every field), the zero-bit
clause `hzero`, and the pins' readings bounded at the parameters.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind)

universe w

variable {V : Type w} [SetTheory V]

namespace IndRepData

variable (d : IndRepData V)

/-! ## The restored domains and ψ*'s spine -/

/-- A copy-recursive position of constructor `Ja`: recursive in the
recursor's view into a member at or past `k₀` — a copy. -/
@[expose] def copyPos (k₀ Ja i : Nat) : Prop :=
  i ∈ ConLeche.recIdxOf (d.ksR Ja) ∧ k₀ ≤ d.tgtsR Ja i

instance (k₀ Ja i : Nat) : Decidable (d.copyPos k₀ Ja i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **ψ*'s transports** at constructor `Ja`: at a copy-recursive field,
the target pin's term `Ψ` over the field's telescope at the field's
index readings; nothing elsewhere. -/
@[expose] def restoreVia (Ψ : Nat → AnnotTerm) (ψ : Name → Nat) (k₀ Ja : Nat) :
    Nat → Option ViaSpec := fun i =>
  if d.copyPos k₀ Ja i then
    some (Ψ (d.tgtsR Ja i - k₀), (d.eissR Ja ψ).getD i [], (d.tssR Ja ψ).getD i [])
  else none

/-- **ψ*'s spine** at the fields of constructor `Ja`, at the leaf frame:
`psiVarsAV` with no hypotheses and the transports `restoreVia`. -/
@[expose] def restoreVarsAV (Ψ : Nat → AnnotTerm) (ψ : Name → Nat) (k₀ Ja nF : Nat) :
    List AnnotTerm :=
  psiVarsAV [] (fun _ => false) (d.restoreVia Ψ ψ k₀ Ja) nF 0

/-- **ψ*'s values** at field values `fs` over the parameter frame `ρp`. -/
@[expose] noncomputable def restoreVals (b : Nat) (ρp : Nat → V) (Ψ : Nat → AnnotTerm)
    (ψ : Name → Nat) (k₀ Ja : Nat) (fs : List V) : List V :=
  psiVals b ρp [] (fun _ => false) (d.restoreVia Ψ ψ k₀ Ja) fs []

/-- **The restored domains** of constructor `Ja`: the auxiliary domains
with `restoreAV` at every field position (which is the auxiliary domain
itself off the copy-recursive positions), the bits the auxiliary
ones. -/
@[expose] def dsRestored (m : EnvModel V env) (ψ : Name → Nat) (k₀ Ja : Nat)
    (tgtCont : Nat → Name) (tgtLps : Nat → Name → Nat) (tgtDsA : Nat → List AnnotTerm) :
    List (Nat × Nat × AnnotTerm) :=
  (d.dsF Ja ψ).zipIdx.map fun q =>
    if q.2 < d.nP then q.1
    else (q.1.1, q.1.2.1, d.restoreAV m ψ k₀ Ja tgtCont tgtLps tgtDsA (q.2 - d.nP))

/-- **The restored constructor's leaf**: the λ-tower over the restored
domains of the auxiliary constructor's leaf `cname` at the parameters
and ψ*'s spine. -/
@[expose] def restoredCtorAV (m : EnvModel V env) (Ψ : Nat → AnnotTerm) (ψ : Name → Nat)
    (k₀ Ja nF : Nat) (cname : Name) (tgtCont : Nat → Name) (tgtLps : Nat → Name → Nat)
    (tgtDsA : Nat → List AnnotTerm) : AnnotTerm :=
  mkLamsAV ((d.dsRestored m ψ k₀ Ja tgtCont tgtLps tgtDsA).map fun e => (e.2.1, e.2.2))
    (AnnotTerm.mkAppN (m.acval cname ψ) (paramBvars d.nP nF ++ d.restoreVarsAV Ψ ψ k₀ Ja nF))

/-! ## Laws -/

omit [SetTheory V] in
theorem restoreVia_isSome_iff {Ψ : Nat → AnnotTerm} {ψ : Name → Nat} {k₀ Ja i : Nat} :
    (d.restoreVia Ψ ψ k₀ Ja i).isSome = true ↔ d.copyPos k₀ Ja i := by
  unfold restoreVia
  split <;> simp_all

omit [SetTheory V] in
theorem restoreVia_of_copy {Ψ : Nat → AnnotTerm} {ψ : Name → Nat} {k₀ Ja i : Nat}
    (h : d.copyPos k₀ Ja i) :
    d.restoreVia Ψ ψ k₀ Ja i
      = some (Ψ (d.tgtsR Ja i - k₀), (d.eissR Ja ψ).getD i [], (d.tssR Ja ψ).getD i []) := by
  unfold restoreVia; rw [if_pos h]

omit [SetTheory V] in
theorem restoreVia_of_not_copy {Ψ : Nat → AnnotTerm} {ψ : Name → Nat} {k₀ Ja i : Nat}
    (h : ¬ d.copyPos k₀ Ja i) : d.restoreVia Ψ ψ k₀ Ja i = none := by
  unfold restoreVia; rw [if_neg h]

omit [SetTheory V] in
/-- The replaced positions of ψ*'s spine are the copy-recursive ones. -/
theorem replaced_restoreVia {Ψ : Nat → AnnotTerm} {ψ : Name → Nat} {k₀ Ja i : Nat} :
    replaced (fun _ => false) (d.restoreVia Ψ ψ k₀ Ja) i ↔ d.copyPos k₀ Ja i := by
  unfold replaced
  rw [d.restoreVia_isSome_iff]
  simp

/-- `restoreAV` off a copy-recursive position is the auxiliary domain. -/
theorem restoreAV_of_not_copy (m : EnvModel V env) {ψ : Name → Nat} {k₀ Ja i : Nat}
    {tgtCont : Nat → Name} {tgtLps : Nat → Name → Nat} {tgtDsA : Nat → List AnnotTerm}
    (h : ¬ d.copyPos k₀ Ja i) :
    d.restoreAV m ψ k₀ Ja tgtCont tgtLps tgtDsA i = ((d.dsF Ja ψ).getD (d.nP + i) default).2.2 := by
  unfold restoreAV copyPos at *; rw [if_neg h]

theorem dsRestored_length (m : EnvModel V env) (ψ : Name → Nat) (k₀ Ja : Nat)
    (tgtCont : Nat → Name) (tgtLps : Nat → Name → Nat) (tgtDsA : Nat → List AnnotTerm) :
    (d.dsRestored m ψ k₀ Ja tgtCont tgtLps tgtDsA).length = (d.dsF Ja ψ).length := by
  simp [dsRestored]

/-- A restored entry below the parameter count is the auxiliary one. -/
theorem dsRestored_getElem?_lt (m : EnvModel V env) (ψ : Name → Nat) (k₀ Ja : Nat)
    (tgtCont : Nat → Name) (tgtLps : Nat → Name → Nat) (tgtDsA : Nat → List AnnotTerm)
    {l : Nat} (hl : l < d.nP) :
    (d.dsRestored m ψ k₀ Ja tgtCont tgtLps tgtDsA)[l]? = (d.dsF Ja ψ)[l]? := by
  unfold dsRestored
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases (d.dsF Ja ψ)[l]? with
  | none => rfl
  | some e => simp [hl]

/-- A restored entry at a field position: the auxiliary bits, the
restored domain. -/
theorem dsRestored_getElem?_field (m : EnvModel V env) (ψ : Name → Nat) (k₀ Ja : Nat)
    (tgtCont : Nat → Name) (tgtLps : Nat → Name → Nat) (tgtDsA : Nat → List AnnotTerm)
    (i : Nat) :
    (d.dsRestored m ψ k₀ Ja tgtCont tgtLps tgtDsA)[d.nP + i]?
      = ((d.dsF Ja ψ)[d.nP + i]?).map fun e =>
          (e.1, e.2.1, d.restoreAV m ψ k₀ Ja tgtCont tgtLps tgtDsA i) := by
  unfold dsRestored
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases (d.dsF Ja ψ)[d.nP + i]? with
  | none => rfl
  | some e =>
    simp only [Option.map_some, Option.some.injEq]
    rw [if_neg (by omega)]
    simp only [Nat.zero_add, Nat.add_sub_cancel_left]

/-- Every restored entry carries an auxiliary entry's bits. -/
theorem dsRestored_bits (m : EnvModel V env) (ψ : Name → Nat) (k₀ Ja : Nat)
    (tgtCont : Nat → Name) (tgtLps : Nat → Name → Nat) (tgtDsA : Nat → List AnnotTerm) :
    ∀ e ∈ d.dsRestored m ψ k₀ Ja tgtCont tgtLps tgtDsA,
      ∃ e' ∈ d.dsF Ja ψ, e.1 = e'.1 ∧ e.2.1 = e'.2.1 := by
  intro e he
  unfold dsRestored at he
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  refine ⟨q.1, List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq), ?_⟩
  split <;> simp

/-- The restored field domains, positionally. -/
theorem dsRestored_drop_getElem? (m : EnvModel V env) (ψ : Name → Nat) (k₀ Ja : Nat)
    (tgtCont : Nat → Name) (tgtLps : Nat → Name → Nat) (tgtDsA : Nat → List AnnotTerm)
    {nF : Nat} (hlen : (d.dsF Ja ψ).length = d.nP + nF) {i : Nat} (hi : i < nF) :
    (((d.dsRestored m ψ k₀ Ja tgtCont tgtLps tgtDsA).drop d.nP).map (·.2.2))[i]?
      = some (d.restoreAV m ψ k₀ Ja tgtCont tgtLps tgtDsA i) := by
  rw [List.getElem?_map, List.getElem?_drop, d.dsRestored_getElem?_field]
  obtain ⟨e, he⟩ : ∃ e, (d.dsF Ja ψ)[d.nP + i]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [he]; rfl

omit [SetTheory V] in
/-- The auxiliary field domains, positionally. -/
theorem dsF_drop_getElem? {ψ : Name → Nat} {Ja nF : Nat} (hlen : (d.dsF Ja ψ).length = d.nP + nF)
    {i : Nat} (hi : i < nF) :
    (((d.dsF Ja ψ).drop d.nP).map (·.2.2))[i]? = some ((d.dsF Ja ψ).getD (d.nP + i) default).2.2 := by
  rw [List.getElem?_map, List.getElem?_drop, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  rfl

/-! ## ψ*'s spine reads to its values -/

/-- **ψ*'s spine reads to ψ*'s values** at the leaf frame
(`interp_psiVarsAV` with no motives, minors or hypotheses). -/
theorem interp_restoreVarsAV {b : Nat} {ρp : Nat → V} {Ψ : Nat → AnnotTerm} {ψ : Name → Nat}
    {k₀ Ja : Nat} {fs : List V}
    (hbits : ∀ i, d.copyPos k₀ Ja i → ∀ dd ∈ (d.tssR Ja ψ).getD i [], dd.2.1 = b) :
    (d.restoreVarsAV Ψ ψ k₀ Ja fs.length).map (interp V (consList fs ρp))
      = d.restoreVals b ρp Ψ ψ k₀ Ja fs := by
  unfold restoreVarsAV restoreVals
  apply List.ext_getElem
  · simp [psiVarsAV, psiVals]
  · intro i h1 h2
    have hi : i < fs.length := by simpa [psiVarsAV] using h1
    simp only [psiVarsAV, psiVals, List.getElem_map, List.getElem_range]
    by_cases hc : d.copyPos k₀ Ja i
    · rw [d.restoreVia_of_copy hc]
      dsimp only
      simp only [List.length_nil]
      rw [interp_viaEntryAV_leaf rfl hi (hbits i hc) _ _]
      simp only [viaVal]
    · rw [d.restoreVia_of_not_copy hc]
      dsimp only
      simp only [Bool.false_eq_true, if_false, List.length_nil, Nat.add_zero, interp_bvar]
      rw [consList_apply_lt' fs _ (by omega), show fs.length - 1 - (fs.length - 1 - i) = i by omega]

/-- ψ*'s values agree with the fields off the copy-recursive positions. -/
theorem restoreVals_shadow (b : Nat) (ρp : Nat → V) (Ψ : Nat → AnnotTerm) (ψ : Name → Nat)
    (k₀ Ja : Nat) (fs : List V) :
    ShadowRelP (d.copyPos k₀ Ja) fs (d.restoreVals b ρp Ψ ψ k₀ Ja fs) := by
  have h := psiVals_shadowRelP b ρp [] (fun _ => false) (d.restoreVia Ψ ψ k₀ Ja) fs []
  refine ⟨h.1, fun l hl hnr => h.2 l hl ?_⟩
  rw [d.replaced_restoreVia]; exact hnr

theorem restoreVals_length (b : Nat) (ρp : Nat → V) (Ψ : Nat → AnnotTerm) (ψ : Name → Nat)
    (k₀ Ja : Nat) (fs : List V) : (d.restoreVals b ρp Ψ ψ k₀ Ja fs).length = fs.length :=
  psiVals_length _ _ _ _ _ _ _

/-- ψ*'s value at a non-copy position is the field. -/
theorem restoreVals_getD_of_not_copy {b : Nat} {ρp : Nat → V} {Ψ : Nat → AnnotTerm}
    {ψ : Name → Nat} {k₀ Ja : Nat} {fs : List V} {i : Nat} (hi : i < fs.length)
    (hc : ¬ d.copyPos k₀ Ja i) :
    (d.restoreVals b ρp Ψ ψ k₀ Ja fs).getD i pt = fs.getD i pt := by
  unfold restoreVals
  rw [psiVals_getD _ _ _ _ _ _ _ hi, d.restoreVia_of_not_copy hc]
  rfl

/-- ψ*'s value at a copy position is the transport's value. -/
theorem restoreVals_getD_of_copy {b : Nat} {ρp : Nat → V} {Ψ : Nat → AnnotTerm}
    {ψ : Name → Nat} {k₀ Ja : Nat} {fs : List V} {i : Nat} (hi : i < fs.length)
    (hc : d.copyPos k₀ Ja i) :
    (d.restoreVals b ρp Ψ ψ k₀ Ja fs).getD i pt
      = lamTower b (consList (fs.take i) ρp) ((d.tssR Ja ψ).getD i []) fun σ' =>
          (((d.eissR Ja ψ).getD i []).map (interp V σ') ++
            [(Semantics.frameIdx ((d.tssR Ja ψ).getD i []).length σ').foldl SetTheory.app
              (fs.getD i pt)]).foldl SetTheory.app (interp V ρp (Ψ (d.tgtsR Ja i - k₀))) := by
  unfold restoreVals
  rw [psiVals_getD _ _ _ _ _ _ _ hi, d.restoreVia_of_copy hc]
  rfl

/-! ## The fit: the fields at the restored domains, ψ*'s values at the auxiliary ones -/

set_option maxHeartbeats 1600000 in
/-- **ψ*'s values fit the auxiliary domains** when the fields fit the
restored ones (the leaf-frame twin of `psiVals_fit`): off a copy
position the two domains coincide and the frames agree (`ShadowRelP` at
the datum's `NoBVar` facts over the copy positions); at a copy position
the value is the λ-tower over the telescope of ψ at the index values
applied to the field, which lands in the target copy's carrier at the
parameters and those index values by the ONE fact of ψ (`hΨ`). -/
theorem restoreVals_fit (m : EnvModel V env) {ψ : Name → Nat} {k₀ Ja nF b : Nat}
    {Ψ : Nat → AnnotTerm} {tgtCont : Nat → Name} {tgtLps : Nat → Name → Nat}
    {tgtDsA : Nat → List AnnotTerm} {ρp : Nat → V}
    (hlen : (d.dsF Ja ψ).length = d.nP + nF)
    -- no auxiliary entry mentions a copy position below it
    (hnb : ∀ i, i < nF → NoBVar (exclP (replP d.nP (d.copyPos k₀ Ja) i) (d.nP + i))
      ((d.dsF Ja ψ).getD (d.nP + i) default).2.2)
    (hbits : ∀ i, d.copyPos k₀ Ja i → ∀ dd ∈ (d.tssR Ja ψ).getD i [], dd.2.1 = b)
    -- the auxiliary domain at a copy position: the target copy's leaf
    -- at the parameters and the index readings under the telescope
    (hentry : ∀ i, i < nF → d.copyPos k₀ Ja i →
      ((d.dsF Ja ψ).getD (d.nP + i) default).2.2
        = mkPisAV ((d.tssR Ja ψ).getD i [])
            (AnnotTerm.mkAppN (m.acval (d.memberName (d.tgtsR Ja i)) ψ)
              (paramBvarsAt d.nP (d.nP + i + ((d.tssR Ja ψ).getD i []).length) ++
                (d.eissR Ja ψ).getD i [])))
    (hleafC : ∀ i, Term.bvarsBelow 0 (m.acval (d.memberName (d.tgtsR Ja i)) ψ).erase)
    -- the ONE fact of ψ: at every telescope spine, ψ at the index
    -- values applied to the field lands in the target copy's carrier
    (hΨ : ∀ i, i < nF → d.copyPos k₀ Ja i → ∀ fs : List V, fs.length = nF →
      SpineFit ρp (((d.dsRestored m ψ k₀ Ja tgtCont tgtLps tgtDsA).drop d.nP).map (·.2.2)) fs →
      ∀ as, SpineFit (consList (fs.take i) ρp) (((d.tssR Ja ψ).getD i []).map (·.2.2)) as →
        (((d.eissR Ja ψ).getD i []).map (interp V (consList as (consList (fs.take i) ρp))) ++
          [as.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
            (interp V ρp (Ψ (d.tgtsR Ja i - k₀)))
          ∈ˢ (paramVals d.nP ρp ++
              ((d.eissR Ja ψ).getD i []).map (interp V (consList as (consList (fs.take i) ρp)))).foldl
              SetTheory.app (interp V ρp (m.acval (d.memberName (d.tgtsR Ja i)) ψ))) :
    ∀ fs : List V, fs.length = nF →
      SpineFit ρp (((d.dsRestored m ψ k₀ Ja tgtCont tgtLps tgtDsA).drop d.nP).map (·.2.2)) fs →
      SpineFit ρp (((d.dsF Ja ψ).drop d.nP).map (·.2.2)) (d.restoreVals b ρp Ψ ψ k₀ Ja fs) := by
  intro fs hfs hfit
  have hSR := d.restoreVals_shadow b ρp Ψ ψ k₀ Ja fs
  have hvLen : (d.restoreVals b ρp Ψ ψ k₀ Ja fs).length = nF := by
    rw [d.restoreVals_length, hfs]
  refine spineFit_of_getElem? (by rw [hvLen, List.length_map, List.length_drop, hlen]; omega) ?_
  intro n v F hv hF
  have hn : n < nF := by rw [← hvLen]; exact (List.getElem?_eq_some_iff.mp hv).1
  rw [d.dsF_drop_getElem? hlen hn] at hF
  obtain rfl := Option.some.inj hF
  have hvD : v = (d.restoreVals b ρp Ψ ψ k₀ Ja fs).getD n pt := by
    rw [List.getD_eq_getElem?_getD, hv]; rfl
  -- the frames agree off the copy positions below `n`
  have hfr := interp_congr_shadowRelP_at hSR ρp (by rw [hfs]; exact Nat.le_of_lt hn) (nP := d.nP)
    (hnb n hn)
  rw [← hfr, hvD]
  by_cases hc : d.copyPos k₀ Ja n
  · -- a copy position: the transport's value
    rw [d.restoreVals_getD_of_copy (by omega) hc, hentry n hn hc]
    rw [ConLeche.Semantics.interp_mkPisAV_piTele (v := b) (acc := [])
      (B := fun as => (paramVals d.nP ρp ++
        ((d.eissR Ja ψ).getD n []).map (interp V (consList as (consList (fs.take n) ρp)))).foldl
          SetTheory.app (interp V ρp (m.acval (d.memberName (d.tgtsR Ja n)) ψ)))
      (fun dd hdd => by rw [hbits n hc dd hdd]) ?_]
    · refine lamTower_mem_piTele fun as hfitT => ?_
      rw [List.nil_append]
      have hfitT' := fitsS_teleOfFields.mp hfitT
      have hlenT : as.length = ((d.tssR Ja ψ).getD n []).length := by
        rw [hfitT'.length_eq, List.length_map]
      rw [← hlenT, frameIdx_consList' as]
      exact hΨ n hn hc fs hfs hfit as hfitT'
    · intro as hsp
      rw [List.nil_append, interp_mkAppN_map, List.map_append, interp_closed (V := V) (hleafC n)]
      congr 2
      have hlenT : as.length = ((d.tssR Ja ψ).getD n []).length := by
        rw [hsp.length_eq, List.length_map]
      rw [← consList_append, show d.nP + n + ((d.tssR Ja ψ).getD n []).length
          = d.nP + (fs.take n ++ as).length from by
          rw [List.length_append, List.length_take, hlenT]; omega,
        interp_paramBvarsAt_consList]
  · -- off the copy positions: the field, at the same domain
    rw [d.restoreVals_getD_of_not_copy (by omega) hc]
    have := FixKI.spineFit_getD_mem' hfit (l := n)
      (by rw [List.length_map, List.length_drop, d.dsRestored_length, hlen]; omega)
    have hdom : (((d.dsRestored m ψ k₀ Ja tgtCont tgtLps tgtDsA).drop d.nP).map (·.2.2)).getD n default
        = ((d.dsF Ja ψ).getD (d.nP + n) default).2.2 := by
      rw [List.getD_eq_getElem?_getD, d.dsRestored_drop_getElem? m ψ k₀ Ja tgtCont tgtLps tgtDsA hlen hn,
        Option.getD_some, d.restoreAV_of_not_copy m hc]
    rw [hdom] at this
    exact this

/-! ## The leaf, typed -/

omit [SetTheory V] in
/-- A copy-recursive position is a recursive slot of the recursor's view. -/
theorem copyPos_recAt {k₀ Ja i : Nat} (h : d.copyPos k₀ Ja i) :
    recAt d.nP (d.ksR Ja) (d.nP + i) := by
  obtain ⟨-, hk⟩ := mem_recIdxOf.mp h.1
  refine ⟨Nat.le_add_right _ _, ?_⟩
  rw [Nat.add_sub_cancel_left]
  exact hk

omit [SetTheory V] in
/-- `NoBVar` over the recursive slots below a position is `NoBVar` over
the copy positions below it. -/
theorem noBVar_copyPos_of_recAt {k₀ Ja i D : Nat} {E : AnnotTerm}
    (h : NoBVar (exclP (fun q => recAt d.nP (d.ksR Ja) q ∧ q < d.nP + i) D) E) :
    NoBVar (exclP (replP d.nP (d.copyPos k₀ Ja) i) D) E := by
  refine NoBVar_mono (fun j hj => ?_) E h
  obtain ⟨q, ⟨hq₁, hq₂, hq₃⟩, hqD, hjq⟩ := hj
  refine ⟨q, ⟨?_, hq₃⟩, hqD, hjq⟩
  have := d.copyPos_recAt hq₂
  rw [Nat.add_sub_cancel' hq₁] at this
  exact this

/-- A parameter variable of the leaf's body mentions no copy position. -/
theorem noBVar_paramBvar {P : Nat → Prop} {nP nF k : Nat} (hk : k < nP) :
    NoBVar (exclP (replP nP P nF) (nP + nF)) (AnnotTerm.bvar (nP + nF - 1 - k)) := by
  rintro ⟨q, ⟨hq₁, -, hq₃⟩, -, hjq⟩
  omega

set_option maxHeartbeats 3200000 in
/-- **The restored constructor's leaf is typed** (see the module
docstring): closed below the parameters, and at every frame graded,
bit-valid and a member of the restored tower's reading. -/
theorem restoredCtor_typed {μ : CheckMode} {envAux : Env} (mpAux : EnvModelM V μ envAux)
    {T : Name} {lpsT : List Name} {cA : ConstantVal × Nat} {nIdx : Nat} {ψ : Name → Nat}
    {k₀ Ja b : Nat} {Ψ : Nat → AnnotTerm} {tgtCont : Nat → Name} {tgtLps : Nat → Name → Nat}
    {tgtDsA : Nat → List AnnotTerm}
    (hD : FixCtorDataI mpAux.base2 d.env₀ T lpsT cA.1 d.nP cA.2 nIdx d.resSort d.isProp d.large
      (d.idxF Ja) (d.dsF Ja) (d.esF Ja) (d.srcsF Ja) (d.ksF Ja) (d.fvsPF Ja) (d.xFvsF Ja)
      (d.xrestF Ja) (d.eissF Ja) (d.tssF Ja)
      (fun i => d.memberName (d.tgts Ja i)) (fun i => d.nIdxAt (d.tgts Ja i)))
    (hks : d.ksR Ja = d.ksF Ja) (htgts : d.tgtsR Ja = d.tgts Ja)
    (heiss : d.eissR Ja = d.eissF Ja) (htss : d.tssR Ja = d.tssF Ja)
    (hstored : envAux.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2))
    (hcf : cA.1.type.hasFvar = false) (hcb : cA.1.type.looseBVarsBounded 0 = true)
    (hbits : ∀ i, d.copyPos k₀ Ja i → ∀ dd ∈ (d.tssR Ja ψ).getD i [], dd.2.1 = b)
    -- the constructor's parameter telescope is the block's, as a frame
    (hpIff : ∀ ρ : Nat → V, Sat V (d.params ψ).reverse ρ ↔
      Sat V (((d.dsF Ja ψ).take d.nP).map (·.2.2)).reverse ρ)
    -- the ONE fact of ψ at every parameter frame
    (hΨ : ∀ (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ (i : Nat), i < cA.2 → d.copyPos k₀ Ja i → ∀ fs : List V, fs.length = cA.2 →
      SpineFit ρp (((d.dsRestored mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA).drop d.nP).map (·.2.2)) fs →
      ∀ as, SpineFit (consList (fs.take i) ρp) (((d.tssR Ja ψ).getD i []).map (·.2.2)) as →
        (((d.eissR Ja ψ).getD i []).map (interp V (consList as (consList (fs.take i) ρp))) ++
          [as.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
            (interp V ρp (Ψ (d.tgtsR Ja i - k₀)))
          ∈ˢ (paramVals d.nP ρp ++
              ((d.eissR Ja ψ).getD i []).map (interp V (consList as (consList (fs.take i) ρp)))).foldl
              SetTheory.app (interp V ρp (mpAux.base2.acval (d.memberName (d.tgtsR Ja i)) ψ)))
    -- the transports are graded at the leaf frame
    (hviaWD : ∀ (ρ : Nat → V) (ps fs : List V), ps.length = d.nP → fs.length = cA.2 →
      SpineFit ρ ((d.dsRestored mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA).map (·.2.2)) (ps ++ fs) →
      ∀ i, i < cA.2 → d.copyPos k₀ Ja i →
        WellDenotedV V (consList (ps ++ fs) ρ)
          (viaEntryAV (Ψ (d.tgtsR Ja i - k₀)) cA.2 0 i 0 ((d.tssR Ja ψ).getD i [])
            ((d.eissR Ja ψ).getD i [])))
    -- the restored tower is graded
    (hokR : ∀ ρ : Nat → V, WellDenotedV V ρ
      (mkPisAV (d.dsRestored mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA)
        (ctorBodyAVI mpAux.base2 T d.nP cA.2 ψ (d.esF Ja ψ))))
    -- at a zero sort the body is a truth value
    (hzero : d.resSort.eval ψ = 0 → ∀ (ρ : Nat → V) (as : List V),
      SpineFit ρ ((d.dsRestored mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA).map (·.2.2)) as →
      interp V (consList as ρ) (ctorBodyAVI mpAux.base2 T d.nP cA.2 ψ (d.esF Ja ψ))
        ∈ˢ (univZero : V))
    -- the restored domains are bounded at their own depth, ψ's terms at
    -- the parameters
    (hbelowR : DomsBelow 0 (d.dsRestored mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA))
    (hΨB : ∀ i, i < cA.2 → d.copyPos k₀ Ja i → Term.bvarsBelow d.nP (Ψ (d.tgtsR Ja i - k₀)).erase) :
    Term.bvarsBelow 0
      (d.restoredCtorAV mpAux.base2 Ψ ψ k₀ Ja cA.2 cA.1.name tgtCont tgtLps tgtDsA).erase ∧
    ∀ ρ : Nat → V,
      WellDenoted V ρ (d.restoredCtorAV mpAux.base2 Ψ ψ k₀ Ja cA.2 cA.1.name tgtCont tgtLps tgtDsA) ∧
      AnnotValid V ρ (d.restoredCtorAV mpAux.base2 Ψ ψ k₀ Ja cA.2 cA.1.name tgtCont tgtLps tgtDsA) ∧
      interp V ρ (d.restoredCtorAV mpAux.base2 Ψ ψ k₀ Ja cA.2 cA.1.name tgtCont tgtLps tgtDsA)
        ∈ˢ interp V ρ (mkPisAV (d.dsRestored mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA)
            (ctorBodyAVI mpAux.base2 T d.nP cA.2 ψ (d.esF Ja ψ))) := by
  -- names
  obtain ⟨dsR, hdsR⟩ : ∃ x, x = d.dsRestored mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA := ⟨_, rfl⟩
  obtain ⟨body, hbody⟩ : ∃ x, x = ctorBodyAVI mpAux.base2 T d.nP cA.2 ψ (d.esF Ja ψ) := ⟨_, rfl⟩
  obtain ⟨bodyL, hbodyL⟩ : ∃ x, x = AnnotTerm.mkAppN (mpAux.base2.acval cA.1.name ψ)
    (paramBvars d.nP cA.2 ++ d.restoreVarsAV Ψ ψ k₀ Ja cA.2) := ⟨_, rfl⟩
  rw [← hdsR] at hokR hzero hviaWD hΨ ⊢
  rw [← hbody] at hokR hzero ⊢
  rw [← hdsR] at hbelowR
  have hlenD : (d.dsF Ja ψ).length = d.nP + cA.2 := hD.len ψ
  have hlenR : dsR.length = d.nP + cA.2 := by rw [hdsR, d.dsRestored_length, hlenD]
  have hmemC : ConstantInfo.ctorInfo cA.1 d.nP cA.2 ∈ envAux.consts := Env.find?_mem hstored
  have hreadAux : denoteMeta mpAux.base2.acval envAux ψ 0
      (ConstantInfo.ctorInfo cA.1 d.nP cA.2).toConstantVal.type
        = some (mkPisAV (d.dsF Ja ψ) body) := by rw [hbody]; exact hD.read ψ
  -- the datum's `NoBVar` facts over the copy positions
  obtain ⟨hnb₁, hnb₂, hnb₃, hnb₄⟩ := hD.noBVar_entries hcf hcb ψ
  rw [← hks] at hnb₁ hnb₂ hnb₃ hnb₄
  have hheadC : Term.bvarsBelow 0 (mpAux.base2.acval T ψ).erase := mpAux.base2.cval_closedL _ ψ
  -- the body of the restored tower mentions no copy position and is
  -- bounded at the fields
  have hnbBody : NoBVar (exclP (replP d.nP (d.copyPos k₀ Ja) cA.2) (d.nP + cA.2)) body := by
    rw [hbody]
    unfold ctorBodyAVI
    refine NoBVar_mkAppN (NoBVar_of_bvarsBelow hheadC fun _ _ => Nat.zero_le _) _ fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      exact noBVar_paramBvar (List.mem_range.mp hk)
    · exact d.noBVar_copyPos_of_recAt (hnb₄ a ha)
  have hbodyB : Term.bvarsBelow (d.nP + cA.2) body.erase := by
    rw [hbody, ctorBodyAVI, AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (Term.bvarsBelow.mono (Nat.zero_le _) hheadC) fun a ha => ?_
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    rcases List.mem_append.mp ha' with h | h
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
      show d.nP + cA.2 - 1 - k < d.nP + cA.2
      have := List.mem_range.mp hk
      omega
    · exact hD.belowE ψ a' h
  -- the auxiliary domain at a copy position is the target's entry
  have hentry : ∀ i, i < cA.2 → d.copyPos k₀ Ja i →
      ((d.dsF Ja ψ).getD (d.nP + i) default).2.2
        = mkPisAV ((d.tssR Ja ψ).getD i [])
            (AnnotTerm.mkAppN (mpAux.base2.acval (d.memberName (d.tgtsR Ja i)) ψ)
              (paramBvarsAt d.nP (d.nP + i + ((d.tssR Ja ψ).getD i []).length) ++
                (d.eissR Ja ψ).getD i [])) := by
    intro i hi hc
    obtain ⟨-, hk⟩ := mem_recIdxOf.mp hc.1
    rw [hks] at hk
    rw [htgts, heiss, htss]
    rcases hk with hrec | hrefl
    · rw [hD.recEntry ψ i hrec hi, hD.tssNone ψ i (by rw [hrec]; exact fun h => nomatch h)]
      simp [mkPisAV]
    · exact hD.reflEntry ψ i hrefl hi
  -- the spine's values at a fitting spine, and the head applied to
  -- them: graded and in the auxiliary body
  have hspine : ∀ (ρ : Nat → V) (as : List V), SpineFit ρ (dsR.map (·.2.2)) as →
      WellDenotedV V (consList as ρ) bodyL ∧
      interp V (consList as ρ) bodyL ∈ˢ interp V (consList as ρ) body := by
    intro ρ as hfit
    -- the spine splits at the parameters
    have hfit' : SpineFit ρ ((dsR.take d.nP).map (·.2.2) ++ (dsR.drop d.nP).map (·.2.2)) as := by
      rw [← List.map_append, List.take_append_drop]; exact hfit
    obtain ⟨ps, fs, rfl, hps, hfs⟩ := spineFit_append_inv hfit'
    have hpsLen : ps.length = d.nP := by
      rw [hps.length_eq, List.length_map, List.length_take, hlenR]; omega
    have hfsLen : fs.length = cA.2 := by
      rw [hfs.length_eq, List.length_map, List.length_drop, hlenR]; omega
    -- the parameter domains are the auxiliary ones
    have htake : (dsR.take d.nP).map (·.2.2) = ((d.dsF Ja ψ).take d.nP).map (·.2.2) := by
      apply List.ext_getElem?
      intro l
      rw [List.getElem?_map, List.getElem?_map, List.getElem?_take, List.getElem?_take]
      split
      · next hl => rw [hdsR, d.dsRestored_getElem?_lt mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA hl]
      · rfl
    rw [htake] at hps
    -- ψ*'s values fit the auxiliary field domains at the parameter frame
    have hvals := d.restoreVals_fit mpAux.base2 (b := b) (Ψ := Ψ) (tgtCont := tgtCont)
      (tgtLps := tgtLps) (tgtDsA := tgtDsA) (ρp := consList ps ρ) hlenD
      (fun i hi => d.noBVar_copyPos_of_recAt (hnb₁ i hi)) hbits hentry
      (fun i => mpAux.base2.cval_closedL _ ψ)
      (fun i hi hc fs' hfs' hfit'' as' hsp => hΨ (consList ps ρ)
        ((hpIff _).mpr (by
          have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hps
          rwa [List.append_nil] at h))
        i hi hc fs' hfs' (by rw [hdsR]; exact hfit'') as' hsp)
      fs hfsLen (by rw [hdsR] at hfs; exact hfs)
    obtain ⟨vals, hvalsD⟩ : ∃ x, x = d.restoreVals b (consList ps ρ) Ψ ψ k₀ Ja fs := ⟨_, rfl⟩
    rw [← hvalsD] at hvals
    have hvLen : vals.length = cA.2 := by rw [hvalsD, d.restoreVals_length, hfsLen]
    -- the whole spine fits the auxiliary domains at the leaf frame
    have hσ : consList (ps ++ fs) ρ = consList fs (consList ps ρ) := consList_append _ _ _
    have hfitAux : SpineFit (consList (ps ++ fs) ρ) ((d.dsF Ja ψ).map (·.2.2)) (ps ++ vals) := by
      rw [← List.take_append_drop d.nP (d.dsF Ja ψ), List.map_append]
      refine SpineFit.append ?_ ?_
      · exact spineFit_congr_below (domsBelow_take (hD.below ψ))
          (fun i hi => absurd hi (Nat.not_lt_zero _)) hps
      · refine spineFit_congr_below (DomsBelow.drop d.nP (hD.below ψ)) (fun i hi => ?_) hvals
        rw [Nat.zero_add] at hi
        rw [consList_apply_lt' ps _ (by omega), consList_apply_lt' ps _ (by omega)]
    -- the spine reads to the values
    have hread : (paramBvars d.nP cA.2 ++ d.restoreVarsAV Ψ ψ k₀ Ja cA.2).map
        (interp V (consList (ps ++ fs) ρ)) = ps ++ vals := by
      rw [List.map_append, hσ, paramBvars_eq_paramBvarsAt, ← hfsLen, interp_paramBvarsAt_consList,
        paramVals_push hpsLen, d.interp_restoreVarsAV hbits, ← hvalsD]
    have hshadow := d.restoreVals_shadow b (consList ps ρ) Ψ ψ k₀ Ja fs
    rw [← hvalsD] at hshadow
    -- the head applied to the spine
    have hmain := wellDenotedV_mkAppN_of_spineFit (σ := consList (ps ++ fs) ρ) (ds := d.dsF Ja ψ)
      (C := body) (f := mpAux.base2.acval cA.1.name ψ)
      (as := paramBvars d.nP cA.2 ++ d.restoreVarsAV Ψ ψ k₀ Ja cA.2)
      (mpAux.type_wellDenotedV _ hmemC ψ _ hreadAux _)
      ⟨mpAux.base2.acval_wellDenoted _ ψ _, mpAux.acval_validV _ ψ _⟩
      (fun a ha => by
        rcases List.mem_append.mp ha with h | h
        · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
          exact wellDenotedV_bvar _ _
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
          have hiF := List.mem_range.mp hi
          by_cases hc : d.copyPos k₀ Ja i
          · rw [d.restoreVia_of_copy hc]
            dsimp only
            simp only [List.length_nil]
            exact hviaWD ρ ps fs hpsLen hfsLen hfit i hiF hc
          · rw [d.restoreVia_of_not_copy hc]
            dsimp only
            simp only [Bool.false_eq_true, if_false]
            exact wellDenotedV_bvar _ _)
      (mpAux.mem_type _ hmemC ψ _ hreadAux _)
      (by rw [hread]; exact hfitAux)
    rw [hbodyL]
    refine ⟨hmain.1, ?_⟩
    -- the auxiliary body at ψ*'s values is the body at the fields
    have hmem := hmain.2
    rw [hread] at hmem
    have hlenPV : (ps ++ vals).length = d.nP + cA.2 := by
      rw [List.length_append, hpsLen, hvLen]
    rw [interp_closed_bottom hbodyB hlenPV _ ρ, consList_append, consList_append] at hmem
    have hsh := interp_congr_shadowRelP hshadow (consList ps ρ) [] (E := body)
      (by rw [hfsLen, List.length_nil, Nat.add_zero]; exact hnbBody)
    simp only [consList_nil] at hsh
    rw [← hsh] at hmem
    rw [hσ]
    exact hmem
  -- the bits of the restored tower are the auxiliary ones
  have hz : ∀ e ∈ dsR, (d.resSort.eval ψ = 0 ↔ e.2.1 = 0) := by
    intro e he
    obtain ⟨e', he', -, hbit⟩ := d.dsRestored_bits mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA e (by rw [hdsR] at he; exact he)
    rw [hbit]
    exact hD.bits ψ e' he'
  refine ⟨?_, fun ρ => ?_⟩
  · -- closed
    unfold restoredCtorAV
    rw [← hdsR, ← hbodyL]
    refine mkLamsAV_below (DomsBelow.map21 hbelowR) ?_
    rw [List.length_map, hlenR, Nat.zero_add, hbodyL, AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (Term.bvarsBelow.mono (Nat.zero_le _) (mpAux.base2.cval_closedL _ ψ))
      fun a ha => ?_
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    rcases List.mem_append.mp ha' with h | h
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
      show d.nP + cA.2 - 1 - k < d.nP + cA.2
      have := List.mem_range.mp hk
      omega
    · have := psiVarsAV_below (nP := d.nP) (mm := 0) (o := 0) (nF := cA.2)
        (recIdx := []) (useIh := fun _ => false) (via := d.restoreVia Ψ ψ k₀ Ja)
        (fun i hi Ψ' Eis tl hv => by
          by_cases hc : d.copyPos k₀ Ja i
          · rw [d.restoreVia_of_copy hc] at hv
            have h := Option.some.inj hv
            obtain ⟨h1, h2⟩ := Prod.mk.inj h
            obtain ⟨h3, h4⟩ := Prod.mk.inj h2
            subst h1 h3 h4
            refine ⟨by rw [Nat.add_zero]; exact hΨB i hi hc, ?_, ?_⟩
            · rw [Nat.add_zero, htss]; exact hD.tssBelow ψ i
            · intro E hE
              rw [Nat.add_zero, htss, heiss] at *
              exact hD.eissBelow ψ i E hE
          · rw [d.restoreVia_of_not_copy hc] at hv
            exact nomatch hv)
        a' h
      simpa using this
  · have hUT : UnderTowerOk (d.resSort.eval ψ) ρ bodyL body dsR :=
      underTowerOk_of_wellDenoted (hokR ρ).1 fun as hfit =>
        ⟨(hspine ρ as hfit).1.1, (hspine ρ as hfit).2, fun h0 => hzero h0 ρ as hfit⟩
    have hUV : UnderTowerValid ρ bodyL dsR :=
      underTowerValid_of (fun k dd hk as hsp => annotValid_mkPisAV_dom (hokR ρ).2 as k dd hk hsp)
        fun as hfit => (hspine ρ as hfit).1.2
    unfold restoredCtorAV
    rw [← hdsR, ← hbodyL]
    exact ⟨mkLamsAV_bits_wellDenoted hz hUT, mkLamsAV_bits_validV hUV, mkLamsAV_bits_mem hz hUT⟩

end IndRepData

end ConLeche.Model
