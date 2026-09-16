module

public import ConLeche.Model.Inductives.BlockTableMember
import ConLeche.Model.Inductives.StructBodyFrames
import ConLeche.Model.Inductives.BlockRecFrames
import ConLeche.Model.Inductives.FixStageTable
import ConLeche.Model.Inductives.FixLeafOk
import ConLeche.Verify.Inductives.StructPartsInv
public section

/-!
# The P step at a mutual block's projection table (task #315, M4 s5)

`stageBlockTable`: the P step at ONE structure-like member's table
cons, read off the FLAT bundle `TableMember` (`BlockTableMember.lean`)
— the member's carrier is an abstract `S` with a `FibreAt` shape at
the constructor's GLOBAL block position `J`, and the constructor's
value at a fitting parameter-and-field spine is the tagged tower
injection `injW w J (mkTower (fs ++ [pt]))`.

The three entry laws are block model-level twins of the fixpoint route's
tag-generic cores (`FixEntryLaw.lean`): where those read the leaves
SYNTACTICALLY (`mkLamsAV …` for the former, `sumMkAV …` for the
constructor), the twins here read them SEMANTICALLY — the former by
its Π-membership (`blockEntryTypingCore`, whose parameter fit comes
from `spineFit_of_wellDenoted_mkAppN_pis` instead of the λ-shape) and
the constructor by the bundle's `ctor`/`Cmem` clauses
(`blockEntryIotaCore`, `blockEntryIotaCoreZero`, `blockEntryEtaCore`).
Everything else — the guards, the unused earlier fields' freedom, the
bodies' frames, the `NoProjEnv` crossings — is the fixpoint route's
table stage (`stageFixTable`) verbatim.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal IndCaps BinderMeta
  ProjEntry ProjTable MutualBlock MutualFormerA MutualCtor projTableName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## (A) the typing law, off a Π-membership -/

/-- **The typing law's core at an abstract carrier**
(`fixEntryTypingCoreT`'s twin): the family's value is read only
through its Π-membership `hLmem` and the fold `hfold`, never through a
λ-shape — the parameter fit comes from the application's grading
against the Π-tower (`spineFit_of_wellDenoted_mkAppN_pis`). -/
theorem blockEntryTypingCore {w J nP nF i : Nat} {pps ds eds : List (Nat × Nat × AnnotTerm)}
    {L R : AnnotTerm} {S : (Nat → V) → V} {sorts : List Level} {ψ : Name → Nat}
    (hLmem : ∀ ρ : Nat → V, interp V ρ L ∈ˢ interp V ρ (mkPisAV pps (.sort w)))
    (hbits : ∀ d ∈ pps, d.2.1 ≠ 0)
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
  -- the parameter fit, off the Π-membership
  have hsp : SpineFit ρ (pps.map (·.2.2)) (vs.map (interp V ρ)) := by
    have h := spineFit_of_wellDenoted_mkAppN_pis (C := (.sort w : AnnotTerm)) (ds := pps)
      (σ := ρ) (f := L) (fv := interp V ρ L) hbits
      (Nat.le_of_eq (hlenVs.trans hlenPps.symm)) hokApp.1 rfl (hLmem ρ)
    rwa [hlenVs, List.take_of_length_le (Nat.le_of_eq hlenPps)] at h
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
  · exact ⟨wellDenoted_projAV_succ_of (fun _ => hokB _ hsatC) (hfib _ hsatC) hokx.1 hx
      (by rw [hlenFs]; exact hi), projAV_validV hokx.2⟩
  · rw [hrest, hlen']
    refine wellDenotedV_instSeq _ ?_ ?_
    · intro w' hw'
      rcases List.mem_append.mp hw' with h | h
      · exact WellDenotedV_mkAppN_args vs hokApp w' h
      · rw [List.mem_singleton] at h; subst h; exact hokx
    · rw [hchain]; exact hokR _ hframeX hframeS
  · rw [hinterpRest, projAV_interp]
    by_cases hw : w = 0
    · subst hw
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
    · obtain ⟨fs, heq, hspF⟩ := (hfib _ hsatC).graph hw _ hx
      have hlenF : fs.length = nF := by rw [hspF.length_eq, hlenFs]
      obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hspF (by rw [hlenFs]; exact hi)
      rw [heq, projS_succ_inj, dropS_one_inj, projS_mkTower_getD (by rw [hlenF]; exact hi),
        projList_mkTower_take (by rw [hlenF]; omega)]
      exact hnext

/-! ## The constructor's value at the squash regime -/

/-- **A `Prop`-regime constructor is the point**: every binder of its
type is a `Prop`-regime one there (`CDbits`), so the whole Π-tower is
a truth value and its member is `pt`.  (The tower is nonempty because
the table has a field.) -/
theorem TableMember.ctor_pt {m : EnvModel V env} {lps : List Name} {nP : Nat} {T : Name}
    {cvTa cvCa : ConstantVal} {nF J : Nat} {resSort : Level} {isProp : Bool}
    {sorts : List Level} {pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {S : (Name → Nat) → (Nat → V) → V}
    (h : TableMember m lps nP T cvTa cvCa nF J resSort isProp sorts pps ds Es S)
    (hnF : 0 < nF) {ψ : Name → Nat} (hw : resSort.eval ψ = 0) (ρ : Nat → V) :
    interp V ρ (m.acval cvCa.name ψ) = pt := by
  refine eq_pt_of_mem_univZero ?_ (h.Cmem ψ ρ)
  refine interp_mkPisAV_mem_univZero (fun d hd => (h.CDbits ψ d hd).mp hw) (fun he => ?_)
  exfalso
  have hlen := h.CDlen ψ
  rw [he, List.length_nil] at hlen
  omega

/-! ## (B) the iota law, off the constructor's value -/

/-- **The iota law's core at an abstract constructor value**
(`fixEntryIotaCoreT`'s twin, graph regime): the constructor's value at
a fitting parameter-and-field spine is the tagged tower (`hctor`), so
the projection past the tag selects the field. -/
theorem blockEntryIotaCore {w J nP nF i : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {C : AnnotTerm} {ρ : Nat → V}
    (hw : w ≠ 0) (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hctor : ∀ (σ : Nat → V) (as fs : List V),
      SpineFit σ ((ds.take nP).map (·.2.2)) as →
      SpineFit (consList as σ) ((ds.drop nP).map (·.2.2)) fs →
      (as ++ fs).foldl SetTheory.app (interp V σ C) = injW w J (mkTower (fs ++ [pt])))
    (ys : List AnnotTerm) (hlen : ys.length = nP + nF)
    (hsp : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp V ρ))) :
    interp V ρ (projAV (i + 1) (AnnotTerm.mkAppN C ys))
      = interp V ρ (ys.getD (nP + i) default) := by
  rw [show ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) from by
    rw [← List.map_append, List.take_append_drop]] at hsp
  obtain ⟨as, bs, heq, hsp₁, hsp₂⟩ := spineFit_append_inv hsp
  have hlenAs : as.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlenBs : bs.length = nF := by rw [hsp₂.length_eq]; simp [hlenDs]
  have hfold := hctor ρ as bs hsp₁ hsp₂
  rw [injW_pos hw] at hfold
  rw [projAV_interp, interp_mkAppN_foldl, heq, hfold, projS_succ_inj,
    projS_mkTower_getD (by rw [hlenBs]; exact hi)]
  -- the selected argument
  have hlt : nP + i < ys.length := by omega
  rw [List.getD_eq_getElem?_getD (l := ys), List.getElem?_eq_getElem hlt, Option.getD_some]
  have h1 : (ys.map (interp V ρ))[nP + i]? = some (interp V ρ ys[nP + i]) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
  rw [heq, List.getElem?_append_right (by omega), hlenAs, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)] at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenBs]; exact hi),
    Option.getD_some]
  exact Option.some.inj h1

/-- **The iota law's core at an abstract constructor value**
(`fixEntryIotaCoreZeroT`'s twin, squash regime): the constructor's
value is the point (`hC0`), so is its projection, and the certified
spine's fit pins the selected field to a proposition's member. -/
theorem blockEntryIotaCoreZero {nP nF i : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {C : AnnotTerm} {ρ : Nat → V} {sorts : List Level} {ψ : Name → Nat}
    (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hsorts : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    (hz : (sorts.getD i .zero).eval ψ = 0) (hC0 : interp V ρ C = pt)
    (ys : List AnnotTerm) (hlen : ys.length = nP + nF)
    (hsp : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp V ρ))) :
    interp V ρ (projAV (i + 1) (AnnotTerm.mkAppN C ys))
      = interp V ρ (ys.getD (nP + i) default) := by
  rw [projAV_interp, interp_mkAppN_foldl, hC0, foldl_app_pt, projS_pt]
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

/-! ## (C) the η law -/

/-- **The η law's core at an abstract carrier and constructor value**
(`fixEntryEtaCoreT`'s twin): a member of the carrier is the tagged
tower of a fitting field spine, which the constructor reproduces at
the parameters and the member's own projections. -/
theorem blockEntryEtaCore {w J nP nF : Nat} {pps ds : List (Nat × Nat × AnnotTerm)}
    {L C : AnnotTerm} {S : (Nat → V) → V} {ρ : Nat → V}
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP)
    (hiff : ∀ ρ : Nat → V, Sat V (pps.map (·.2.2)).reverse ρ ↔
      Sat V ((ds.take nP).map (·.2.2)).reverse ρ)
    (hctor : ∀ (σ : Nat → V) (as fs : List V),
      SpineFit σ ((ds.take nP).map (·.2.2)) as →
      SpineFit (consList as σ) ((ds.drop nP).map (·.2.2)) fs →
      (as ++ fs).foldl SetTheory.app (interp V σ C) = injW w J (mkTower (fs ++ [pt])))
    (hC0 : w = 0 → interp V ρ C = pt)
    (hfold : ∀ (ρ : Nat → V) (ts : List V), SpineFit ρ (pps.map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ L) = S (consList ts ρ))
    (hfib : ∀ ρ' : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ' →
      FibreAt w J ((ds.drop nP).map (·.2.2)) ρ' (S ρ'))
    (ts : List V) (x : V) (hlen : ts.length = nP)
    (hsp : SpineFit ρ (pps.map (·.2.2)) ts)
    (hx : x ∈ˢ ts.foldl SetTheory.app (interp V ρ L)) :
    x = (ts ++ (List.range nF).map fun j => projS (j + 1) x).foldl SetTheory.app
      (interp V ρ C) := by
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
    rw [hpt, hC0 rfl, foldl_app_pt]
  · obtain ⟨fs, heq, hspF⟩ := (hfib _ hsat).graph hw _ hx
    have hlenF : fs.length = nF := by rw [hspF.length_eq, hlenFs]
    have hfold' := hctor ρ ts fs hsp₁ hspF
    rw [injW_pos hw] at hfold'
    have hprojs : ((List.range nF).map fun j => projS (j + 1) x) = fs := by
      rw [heq]
      have h1 : ((List.range nF).map fun j => projS (j + 1) (inj J (mkTower (fs ++ [pt]))))
          = (List.range nF).map fun j => projS j (mkTower (fs ++ [pt])) :=
        List.map_congr_left fun j _ => projS_succ_inj j J _
      rw [h1, ← projList_eq_map_range, ← hlenF, projList_mkTower_take (Nat.le_refl _),
        List.take_length]
    rw [hprojs, hfold', heq]

/-! ## The guards and the unused earlier fields

Both are the fixpoint route's (`stageFixTable`), lifted out of the
proof so that the stage itself fits the default elaboration budget. -/

/-- **The official guard's content**: the join over the used earlier
slots is a proposition exactly when the field's own sort and every
used earlier one are. -/
theorem structProjGuard_eval_zero_iff {cty : Expr} {nP nF k : Nat} {sorts : List Level}
    (hk : k < nF) (ψ : Name → Nat) :
    ((ConLeche.structProjGuards cty nP nF sorts).getD k .zero).eval ψ = 0 ↔
      ((sorts.getD k .zero).eval ψ = 0 ∧
        ∀ j, j < k → ConLeche.structUsedLater cty nP j = true →
          (sorts.getD j .zero).eval ψ = 0) := by
  rw [ConLeche.structProjGuards_getD _ _ _ _ hk,
    eval_foldl_max_if_zero_iff ψ (ConLeche.structUsedLater cty nP)
      (fun j => sorts.getD j .zero)]
  exact ⟨fun h => ⟨h.1, fun j hj hu => h.2 j (List.mem_range.mpr hj) hu⟩,
    fun h => ⟨h.1, fun j hj hu => h.2 j (List.mem_range.mp hj) hu⟩⟩

/-! ## The unused earlier fields are free in the projected field's type -/

/-- **A field's reading is a lift past every unused earlier field**:
an earlier binder whose variable does not occur later
(`structUsedLater`) is free in the field's opened type, so its
reading is a lift at that slot (`openPisAtFvars_leaf_free`). -/
theorem structField_free_of_unused {m : EnvModel V env} {cty : Expr} {nP nF : Nat}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {bodyA : (Name → Nat) → AnnotTerm}
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hCf : cty.hasFvar = false)
    (hread : ∀ ψ, denoteMeta m.acval env ψ 0 cty = some (mkPisAV (ds ψ) (bodyA ψ)))
    (hlen : ∀ ψ, (ds ψ).length = nP + nF) :
    ∀ (ψ : Name → Nat) (k : Nat), k < nF → ∀ (j : Nat), j < k →
      ConLeche.structUsedLater cty nP j = false →
      ∃ X : AnnotTerm, (((ds ψ).drop nP).map (·.2.2)).getD k default = X.liftN 1 (k - 1 - j) := by
  obtain ⟨fvsA, oA, hopAll⟩ := openPisAtFvars_of_stripPis_isSome (nP + nF) 0 hstripC
  have hlenA : fvsA.length = nP + nF := openPisAtFvars_length _ hopAll
  intro ψ k hk j hj hun
  have hsome : (cty.stripPis (nP + j + 1)).isSome = true :=
    ConLeche.stripPis_isSome_of_le (by omega) hstripC
  obtain ⟨⟨bs, rest⟩, hst⟩ := Option.isSome_iff_exists.mp hsome
  have hrest : rest.hasLooseBVar 0 = false := by
    unfold ConLeche.structUsedLater at hun
    rw [hst] at hun
    have hun' : rest.hasLooseBVarB 0 = false := hun
    rw [ConLeche.Expr.hasLooseBVarB_eq] at hun'
    exact hun'
  obtain ⟨hleavesK, -⟩ := openPisAtFvars_leaf_free (nP + nF) (nP + j) hopAll (by omega)
    hst hrest (by
      intro l hl
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf] at hl
      exact absurd hl List.not_mem_nil)
  obtain ⟨pps', b, hstA, -, -, hbind⟩ := denoteMeta_openPis (nP + nF) hopAll (hread ψ)
  have hppsEq : pps' = ds ψ := by
    have h2 := stripPisAV_mkPisAV (ds ψ) (bodyA ψ)
    rw [hlen ψ] at h2
    exact (Prod.mk.inj (Option.some.inj (hstA.symm.trans h2))).1
  obtain ⟨x, hx⟩ : ∃ x, fvsA[nP + k]? = some x :=
    ⟨fvsA[nP + k]'(by rw [hlenA]; omega), List.getElem?_eq_getElem (by rw [hlenA]; omega)⟩
  obtain ⟨q, hq, -, hqread⟩ := hbind (nP + k) x hx
  rw [hppsEq] at hq
  have hW : Expr.WScoped (0 + (nP + k)) (Expr.fvarTypeD x) :=
    openPisAtFvars_typeWScoped (nP + nF) hopAll (Expr.WScoped.of_not_hasFvar hCf) _ x hx
  have hleaf : ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, l.1 ≠ nP + j := by
    intro l hl
    have hsub : l ∈ x.fvarLeaves := by
      cases x with
      | fvar idx ty =>
        simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
        exact List.mem_cons_of_mem _ hl
      | _ => exact hl
    have := hleavesK (nP + k) (by omega) x hx l hsub
    simpa using this
  obtain ⟨X, hX⟩ := denoteMeta_liftN_of_leaf_free m (0 + (nP + k)) (Expr.fvarTypeD x) hW
    (q := nP + j) (by omega) (by intro l hl; exact hleaf l hl) hqread
  refine ⟨X, ?_⟩
  have hFk : (((ds ψ).drop nP).map (·.2.2)).getD k default = q.2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop, hq]
    rfl
  rw [hFk, hX, show 0 + (nP + k) - 1 - (nP + j) = k - 1 - j from by omega]

/-! ## The P step at a structure-like member's table -/

/-- **The P step at a mutual block's projection table**: `stageTable` against the member's carrier. -/
theorem stageBlockTable {env envOut : Env} (mp : EnvModelM V μ env) {lps : List Name} {nP : Nat} {T : Name}
    {cvTa cvCa : ConstantVal} {nF J : Nat} {resSort : Level} {isProp : Bool} {sorts : List Level}
    {pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {S : (Name → Nat) → (Nat → V) → V}
    (h : TableMember mp.base2 lps nP T cvTa cvCa nF J resSort isProp sorts pps ds Es S)
    (hTbl : ConLeche.checkStructProjTable (m := ConLeche.CheckM) T cvCa.name lps nP nF resSort
      (ConLeche.structProjGuards cvCa.type nP nF sorts) 1 cvCa env = .ok envOut) :
    ∃ mp' : EnvModelM V μ envOut,
      mp'.base2.acval = acvalWith mp.base2.acval (projTableName T) (fun _ => .sort 0) := by
  have hwf' : ConLeche.EnvWF envOut := ConLeche.direct_table_wf mp.base2.wf hTbl
  obtain ⟨bodies, hbodies, -, -, hfresh, rfl⟩ := ConLeche.checkStructProjTable_inv hTbl
  let tbl : ProjTable := ⟨T, lps, nP, cvCa.name, nF, resSort,
    bodies, ConLeche.structProjGuards cvCa.type nP nF sorts, 1⟩
  -- the field-chain facts, in the frames' spelling
  have hokB : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) :=
    fun ψ ρ hρ => (h.fields ψ ρ hρ).1
  -- the guards' content: the official join over the used earlier slots
  have hO5 : ∀ k, k < nF → (Level.isEquiv resSort .zero == some true) = false →
      ∀ ψ : Name → Nat, resSort.eval ψ = 0 →
      ((ConLeche.structProjGuards cvCa.type nP nF sorts).getD k .zero).eval ψ = 0 := by
    intro k hk hne ψ h0
    refine (structProjGuard_eval_zero_iff hk ψ).mpr ⟨?_, fun j hj _ => ?_⟩
    · have := Level.leq_sound (h.leq k hk (by rw [h.prop]; exact hne)) ψ
      omega
    · have := Level.leq_sound (h.leq j (by omega) (by rw [h.prop]; exact hne)) ψ
      omega
  -- the constructor type's scoping
  obtain ⟨hCf, -, -, hCb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem h.fC)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  -- the unused earlier fields are free in the projected field's type
  have hfree := structField_free_of_unused (m := mp.base2) (nF := nF) (ds := ds)
    (bodyA := fun ψ => ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) h.stripC hCf h.CDread h.CDlen
  -- names
  have hneT : T ≠ projTableName T := by
    intro he
    have := projTableName_isProjFnShape T
    rw [← he, h.Tshape] at this
    exact nomatch this
  have hneC : cvCa.name ≠ projTableName T := by
    intro he
    have := projTableName_isProjFnShape T
    rw [← he, h.Cshape] at this
    exact nomatch this
  have hnres : ConLeche.reservedBasisNames.contains (projTableName T) = false :=
    ConLeche.reservedBasisNames_not_num _ _
  -- the crossings
  have hcrossT : ConsCrossAt (.projInfo tbl) cvTa.type := by
    intro t2 he' j
    cases he'
    exact (h.nproj j).type _ (ConLeche.Semantics.Env.find?_mem h.fT)
  have hcrossC : ConsCrossAt (.projInfo tbl) cvCa.type := by
    intro t2 he' j
    cases he'
    exact (h.nproj j).type _ (ConLeche.Semantics.Env.find?_mem h.fC)
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem h.fT)).2.2.1
  have hcbC : ConstsBound env cvCa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem h.fC)).2.2.1
  -- the lookups at the extension
  have hfT₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? T
      = some (.indInfo cvTa {}) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun he => hneT he.symm)]
    exact h.fT
  have hfC₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? cvCa.name
      = some (.ctorInfo cvCa nP nF) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun he => hneC he.symm)]
    exact h.fC
  have hfTbl₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? (projTableName T)
      = some (.projInfo tbl) := ConLeche.Env.find?_cons_self _ _
  have hprev₂ : ∀ j, j < nF →
      ∃ entry, (⟨.projInfo tbl :: env.consts⟩ : Env).findProj? T j = some entry :=
    fun j hj => ⟨tbl.entry j, ConLeche.Env.findProj?_of_table hfTbl₂ hj⟩
  -- the head data at every field
  have hhead : ∀ i, i < nF → ConLeche.TowerHead ⟨.projInfo tbl :: env.consts⟩ (tbl.entry i) :=
    fun i hi => ⟨h.resT, h.resR, h.resC, hi, ⟨cvTa, {}, hfT₂, h.lpsT⟩,
      ⟨cvCa, hfC₂, h.lpsC, h.stripC⟩⟩
  suffices hlaw : ∀ m₂ : EnvModel V ⟨.projInfo tbl :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0) →
      ∀ (φ : Name → Nat) (i : Nat), i < tbl.numFields →
        TowerEntryLaw m₂ φ tbl.structName i (tbl.entry i) by
    obtain ⟨mp', hac'⟩ :=
      declStep_preserves_of_tower_cons mp (tbl := tbl) hfresh hnres hwf' h.nproj hhead hlaw
    exact ⟨mp', hac'⟩
  -- the fields' laws
  intro m₂ hac φ i hi
  replace hi : i < nF := hi
  have hacT : ∀ ψ, m₂.acval T ψ = mp.base2.acval T ψ := by
    intro ψ
    rw [hac]
    show acvalWith mp.base2.acval (projTableName T) _ T ψ = _
    rw [acvalWith_ne hneT]
  have hacC : ∀ ψ, m₂.acval cvCa.name ψ = mp.base2.acval cvCa.name ψ := by
    intro ψ
    rw [hac]
    show acvalWith mp.base2.acval (projTableName T) _ cvCa.name ψ = _
    rw [acvalWith_ne hneC]
  have hFD₂ : FormerData m₂ cvTa nP resSort pps :=
    h.FD.cross (c₀ := .projInfo tbl) hfresh hcrossT hcbT m₂ hac
  -- the constructor type's reading at the extension
  have hCDread₂ : ∀ ψ, denoteMeta m₂.acval ⟨.projInfo tbl :: env.consts⟩ ψ 0 cvCa.type
      = some (mkPisAV (ds ψ) (ctorBodyAVI m₂ T nP nF ψ (Es ψ))) := by
    intro ψ
    have hbody : ctorBodyAVI m₂ T nP nF ψ (Es ψ)
        = ctorBodyAVI mp.base2 T nP nF ψ (Es ψ) := by
      unfold ctorBodyAVI; rw [hacT]
    rw [hbody, hac]
    exact denoteMeta_cons_mono hfresh hcrossC ψ 0 hcbC (h.CDread ψ)
  -- the body, opened at the variables
  obtain ⟨cds, bodyB, mbB, hcf⟩ :=
    ConLeche.structProjBody_open hbodies h.stripC hCb hi
  refine ⟨rfl, rfl, hi, ⟨cvTa, {}, hfT₂, h.lpsT, fun hh => nomatch hh⟩,
    hO5 i hi, cvCa, hfC₂, h.lpsC, ?_, ?_⟩
  · -- the per-instantiation laws
    intro us _
    obtain ⟨fdomA, hfdA, hokFd, hresFd⟩ := bodyFrames m₂ (off := 1) hcf hCf hCb
      (fun j hj => by
        obtain ⟨entry, hfe⟩ := hprev₂ j (by omega)
        refine ⟨entry, hfe, ?_⟩
        obtain ⟨tbl', hf', -, rfl⟩ := ConLeche.Env.findProj?_some hfe
        obtain rfl : tbl = tbl' := ConstantInfo.projInfo.inj (Option.some.inj (hfTbl₂.symm.trans hf'))
        rfl) hi
      (h.CDlen (Level.substFn φ lps us))
      (h.CDbelow (Level.substFn φ lps us))
      (hCDread₂ (Level.substFn φ lps us))
      (fun ρ hρ => h.fields _ ρ hρ) (h.sortsF _)
      (used := ConLeche.structUsedLater cvCa.type nP) (hfree _ i hi)
      (fun ρ => ρ 0 ∈ˢ S (Level.substFn φ lps us) (fun j => ρ (j + 1)))
      (fun ρ hx hsat hw => (h.fib _ _ hsat).squash hw _ hx)
      (fun ρ hx hsat hw => by
        obtain ⟨fs, heq, hsp⟩ := (h.fib _ _ hsat).graph hw _ hx
        have hlenF : fs.length = nF := by
          rw [hsp.length_eq, List.length_map, List.length_drop, h.CDlen, Nat.add_sub_cancel_left]
        rw [heq, dropS_one_inj, ← hlenF, projList_mkTower_take (Nat.le_refl _), List.take_length]
        exact hsp)
      (fun ρ hx hsat j hj => by
        refine wellDenoted_projAV_succ_of (fun _ => hokB _ _ hsat) (h.fib _ _ hsat) trivial ?_ ?_
        · rw [interp_bvar]; exact hx
        · rw [List.length_map, List.length_drop, h.CDlen, Nat.add_sub_cancel_left]; exact hj)
    have hread : denoteMeta m₂.acval ⟨.projInfo tbl :: env.consts⟩ φ 0
        (ConLeche.projTele ((tbl.entry i).numParams + 1)
          ((tbl.entry i).body.instantiateLevelParams (tbl.entry i).levelParams us))
        = some (mkPisAV (List.replicate (nP + 1) (0, 1, .sort 0)) fdomA) := by
      show denoteMeta m₂.acval _ φ 0 (ConLeche.projTele (nP + 1)
        ((bodies.getD i default).instantiateLevelParams lps us)) = _
      rw [← ConLeche.projTele_instantiateLevelParams,
        denotePInstLevels m₂ φ lps us 0]
      exact denoteMeta_projTele_zero hfdA
    refine ⟨⟨_, hread, ?_⟩, ?_⟩
    · -- (A)
      intro hguardAt ρ vs x rest hlenVs hokApp hokx hmem hpeel
      have hguard' : resSort.eval (Level.substFn φ lps us) = 0 →
          (sorts.getD i .zero).eval (Level.substFn φ lps us) = 0 ∧
          ∀ j, j < i → ConLeche.structUsedLater cvCa.type nP j = true →
            (sorts.getD j .zero).eval (Level.substFn φ lps us) = 0 :=
        fun h0 => (structProjGuard_eval_zero_iff hi _).mp (hguardAt h0)
      have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
          = mp.base2.acval T (Level.substFn φ lps us) := by
        show m₂.acval T (Level.substFn φ lps us) = _
        rw [hacT]
      rw [hacT'] at hokApp hmem
      exact blockEntryTypingCore (J := J) (fun ρ' => h.Tmem _ ρ') (h.FD.bits _)
        (h.CDlen _) (h.FD.len _) (by simp) (h.iff _) (hokB _)
        (h.sortsF _) (used := ConLeche.structUsedLater cvCa.type nP) hguard' (hfree _ i hi) hi
        (h.fold _) (fun ρ' hρ' => h.fib _ ρ' hρ') hresFd (hokFd (fun h0 => (hguard' h0).2))
        ρ vs x rest hlenVs hokApp hokx hmem hpeel
    · -- (B)
      refine ⟨mkPisAV (ds (Level.substFn φ lps us))
        (ctorBodyAVI m₂ T nP nF (Level.substFn φ lps us)
          (Es (Level.substFn φ lps us))), ?_, ?_⟩
      · rw [denotePInstLevels m₂ φ cvCa.levelParams us 0 cvCa.type, h.lpsC]
        exact hCDread₂ _
      · intro hguardAt ρ ys rest hlen _hok hfit
        have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
            = mp.base2.acval cvCa.name (Level.substFn φ lps us) := by
          show m₂.acval cvCa.name (Level.substFn φ lps us) = _
          rw [hacC]
        rw [hacC']
        show interp V ρ (projAV (i + 1) _) = _
        have hsp : SpineFit ρ ((ds (Level.substFn φ lps us)).map (·.2.2))
            (ys.map (interp V ρ)) :=
          spineFit_of_teleFit (by simp only [List.length_map, hlen, h.CDlen]; rfl) hfit
        by_cases hw : resSort.eval (Level.substFn φ lps us) = 0
        · exact blockEntryIotaCoreZero (h.CDlen _) hi (h.sortsF _)
            ((structProjGuard_eval_zero_iff hi _).mp (hguardAt hw)).1
            (h.ctor_pt (Nat.zero_lt_of_lt hi) hw ρ) ys hlen hsp
        · exact blockEntryIotaCore hw (h.CDlen _) hi (h.ctor _) ys hlen hsp
  · -- (C)
    intro cvT capsT hf us _
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT₂.symm.trans hf))
    refine ⟨mkPisAV (pps (Level.substFn φ lps us))
      (.sort (resSort.eval (Level.substFn φ lps us))), ?_, h.FD.okTy _, ?_⟩
    · rw [denotePInstLevels m₂ φ cvTa.levelParams us 0 cvTa.type, h.lpsT]
      exact hFD₂.read _
    · intro ρ ts rest x hlents hfit hmem
      have hsp := spineFit_of_teleFit (by rw [h.FD.len]; exact hlents) hfit
      have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
          = mp.base2.acval T (Level.substFn φ lps us) := by
        show m₂.acval T (Level.substFn φ lps us) = _
        rw [hacT]
      have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
          = mp.base2.acval cvCa.name (Level.substFn φ lps us) := by
        show m₂.acval cvCa.name (Level.substFn φ lps us) = _
        rw [hacC]
      rw [hacT'] at hmem
      rw [hacC']
      show x = (ts ++ (List.range nF).map fun j => projS (j + 1) x).foldl SetTheory.app _
      exact blockEntryEtaCore (h.CDlen _) (h.FD.len _) (h.iff _) (h.ctor _)
        (fun h0 => h.ctor_pt (Nat.zero_lt_of_lt hi) h0 ρ)
        (h.fold _) (fun ρ' hρ' => h.fib _ ρ' hρ') ts x hlents hsp hmem

/-- The step, as the members' fold takes it. -/
theorem blockTableStep : BlockTableStep V μ := fun mp => stageBlockTable mp

end ConLeche.Model
