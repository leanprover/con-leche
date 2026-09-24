module

public import ConLeche.Model.Inductives.FixStageTable
import ConLeche.Semantics.Tower.BlockFamI
import ConLeche.Model.Annot.BitLevels
public section

/-!
# The fieldless one-constructor block's laws (task #210 Part B)

On the fixpoint route's constant-functor arm a fieldless, index-free,
one-constructor block (`Unit`-shaped; `True`-shaped at `Prop`) claims
unit-likeness (`blockCapsAt`: not η — official's `try_eta_struct` at
zero fields is decided by `is_def_eq_unit_like` already), and the P
tier owes `UnitLaw` at every carrier from the former's cons on.  The
law reads off the former's fold alone: at the dummy former the family
is EMPTY (`fixEmptyUnitLaw`), at the fixpoint leaf the fibre is the
one tagged empty tuple (`fixFibreUnitLaw`).  The fold itself is Part
A's single-constructor identity, factored out (`fixFoldSingle`), and
at zero fields the real chains are the X-source chains by definition
(`chainsRealI_zero`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- **Unit-likeness at the dummy former's leaf**: the family with no
constructor chain is empty, so the law is vacuous. -/
theorem fixEmptyUnitLaw {m : EnvModel V env} {φ' : Name → Nat} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    {w : (Name → Nat) → Nat} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hleaf : ∀ ψ, m.acval T ψ = sumTyAV (w ψ) (pps ψ) [])
    (hread : ∀ ψ, denoteMeta m.acval env ψ 0 cvT.type
      = some (mkPisAV (pps ψ) (.sort (w ψ))))
    (hokTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (mkPisAV (pps ψ) (.sort (w ψ))))
    (hpar : ∀ ψ, caps.unitParams = (pps ψ).length) :
    UnitLaw m φ' T cvT caps := by
  intro us _
  refine ⟨mkPisAV (pps (Level.substFn φ' cvT.levelParams us))
    (.sort (w (Level.substFn φ' cvT.levelParams us))), ?_, hokTy _, ?_⟩
  · rw [denotePInstLevels m φ' cvT.levelParams us 0 cvT.type]
    exact hread _
  · intro ρ ts rest x y hlen hfit hx _
    have hsp := spineFit_of_teleFit (by rw [hlen, hpar]) hfit
    rw [hleaf, sumTyAV_fold hsp (fun _ h => absurd h List.not_mem_nil)] at hx
    exfalso
    by_cases hw : w (Level.substFn φ' cvT.levelParams us) = 0
    · rw [hw] at hx
      obtain ⟨-, i, a, ha⟩ := sumSet_zero_elim hx
      rw [sumFibre_of_ge (Nat.zero_le _)] at ha
      exact not_mem_empty _ ha
    · obtain ⟨i, a, ha, -⟩ := sumSet_elim hw hx
      rw [sumFibre_of_ge (Nat.zero_le _)] at ha
      exact not_mem_empty _ ha

/-- **Unit-likeness at a fieldless one-constructor block's leaf**: the
fibre is the one tagged empty tuple (the point at a squash instance).

The leaf `L` is ABSTRACT — what the law reads of it is its FOLD, and
nothing else — so the same theorem serves the one-family fixpoint leaf
(`fixFibreUnitLaw`, below) and a block member's (`blockTyAV` through
`blockFoldSingle`). -/
theorem fibreUnitLaw {m : EnvModel V env} {φ' : Name → Nat} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    {w : (Name → Nat) → Nat} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {L : (Name → Nat) → AnnotTerm}
    (hleaf : ∀ ψ, m.acval T ψ = L ψ)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((pps ψ).map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ (L ψ))
        = sumSet (w ψ) (sumFibre (w ψ) (consList ts ρ) [[] ++ [idxEqAV []]]))
    (hread : ∀ ψ, denoteMeta m.acval env ψ 0 cvT.type
      = some (mkPisAV (pps ψ) (.sort (w ψ))))
    (hokTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (mkPisAV (pps ψ) (.sort (w ψ))))
    (hpar : ∀ ψ, caps.unitParams = (pps ψ).length) :
    UnitLaw m φ' T cvT caps := by
  intro us _
  refine ⟨mkPisAV (pps (Level.substFn φ' cvT.levelParams us))
    (.sort (w (Level.substFn φ' cvT.levelParams us))), ?_, hokTy _, ?_⟩
  · rw [denotePInstLevels m φ' cvT.levelParams us 0 cvT.type]
    exact hread _
  · intro ρ ts rest x y hlen hfit hx hy
    have hsp := spineFit_of_teleFit (by rw [hlen, hpar]) hfit
    rw [hleaf, hfold _ ρ ts hsp] at hx hy
    by_cases hw : w (Level.substFn φ' cvT.levelParams us) = 0
    · rw [hw] at hx hy
      obtain ⟨rfl, -⟩ := fixFibre_zero_elim hx
      obtain ⟨rfl, -⟩ := fixFibre_zero_elim hy
      rfl
    · obtain ⟨fs, rfl, hspx, -⟩ := fixFibre_elim (Fs := []) hw hx
      obtain ⟨gs, rfl, hspy, -⟩ := fixFibre_elim (Fs := []) hw hy
      cases fs with
      | cons _ _ => exact hspx.elim
      | nil =>
        cases gs with
        | cons _ _ => exact hspy.elim
        | nil => rfl

/-- **The fieldless η law at the fixpoint leaf**: a member is the one
tagged empty tuple, and the constructor along the parameters is that
tuple (the point at a squash instance) — the fabricated η spine at no
field is the constructor at the parameters. -/
theorem fibreEtaLaw0 {m : EnvModel V env} {φ' : Name → Nat} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    {w : (Name → Nat) → Nat} {pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {L : (Name → Nat) → AnnotTerm}
    (hfields : caps.etaFields = 0)
    (hleaf : ∀ ψ, m.acval T ψ = L ψ)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((pps ψ).map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ (L ψ))
        = sumSet (w ψ) (sumFibre (w ψ) (consList ts ρ) [[] ++ [idxEqAV []]]))
    (hleafC : ∀ ψ, m.acval caps.etaCtor ψ = sumMkAV (w ψ) 0 (ds ψ) [] (uChains [[]]))
    (hread : ∀ ψ, denoteMeta m.acval env ψ 0 cvT.type
      = some (mkPisAV (pps ψ) (.sort (w ψ))))
    (hokTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (mkPisAV (pps ψ) (.sort (w ψ))))
    (hfit : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as : List V),
      SpineFit ρ ((pps ψ).map (·.2.2)) as → SpineFit ρ ((ds ψ).map (·.2.2)) as)
    (hpar : ∀ ψ, caps.etaParams = (pps ψ).length) :
    EtaLaw m φ' T cvT caps := by
  intro us _
  refine ⟨mkPisAV (pps (Level.substFn φ' cvT.levelParams us))
    (.sort (w (Level.substFn φ' cvT.levelParams us))), ?_, hokTy _, ?_⟩
  · rw [denotePInstLevels m φ' cvT.levelParams us 0 cvT.type]
    exact hread _
  · intro ρ ts rest x hlen hfitT hx
    have hsp := spineFit_of_teleFit (by rw [hlen, hpar]) hfitT
    rw [hleaf, hfold _ ρ ts hsp] at hx
    rw [hfields]
    simp only [etaFabArgsV, projSpines, List.range_zero, List.map_nil, List.append_nil]
    rw [hleafC]
    by_cases hw : w (Level.substFn φ' cvT.levelParams us) = 0
    · rw [hw] at hx
      obtain ⟨rfl, -⟩ := fixFibre_zero_elim hx
      rw [hw, sumMkAV_zero, foldl_app_pt]
    · obtain ⟨fs, rfl, hspx, -⟩ := fixFibre_elim (Fs := []) hw hx
      cases fs with
      | cons _ _ => exact hspx.elim
      | nil =>
        have hfd := sumMkAV_fold hw (j := 0) (pds := ds _) (fds := []) (Fss := uChains [[]])
          (ρ := ρ) (as := ts) (bs := []) (by simpa using hfit _ ρ ts hsp) trivial
          (SumFieldsOkB_uChains fun _ h => by
            simp only [List.mem_singleton] at h
            subst h; trivial) rfl
        simp only [List.append_nil, List.map_nil] at hfd
        rw [hfd]

/-! ## The block member's single-constructor fold -/

/-- **The single-constructor fold at no index, at a block member**
(`fixFoldSingle` at `k` members): member `m`'s leaf at a fitting
parameter spine is the one-constructor fibre of the member-local tagged
union.  This is what a structure-like member's capability laws read of
its leaf, and with `fibreUnitLaw`/`fibreEtaLaw0` — whose leaf is
abstract — it is ALL they read of it. -/
theorem blockFoldSingle {k w m : Nat} (hm : m < k)
    {pps : List (Nat × Nat × AnnotTerm)} {Fs : List AnnotTerm}
    {uf : Nat → Nat} {Idss : Nat → List AnnotTerm} {rsss : Nat → List (List Bool)}
    {tgtsss : Nat → List (List Nat)}
    {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}
    {ρ : Nat → V} {ts : List V}
    (hIdsm : Idss m = []) (hEss : Esss m = [[]])
    (hsp : SpineFit ρ (pps.map (·.2.2)) ts)
    (hok : BlockChainsOk k w (consList ts ρ) uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
    (hreal : ChainsRealBI
      (blockFam k w (consList ts ρ) uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
      k w (consList ts ρ) uf Idss m (rsss m) (tgtsss m) (tlsss m) (Eisss m) (Fsss m) [Fs]
      (Esss m)) :
    ts.foldl SetTheory.app
        (interp V ρ (blockTyAV k w uf Idss rsss tgtsss tlsss Eisss Fsss Esss pps m))
      = sumSet w (sumFibre w (consList ts ρ) [Fs ++ [idxEqAV []]]) := by
  have hsh : shiftE (Idss m).length 0 (consList ts ρ) = consList ts ρ := by
    rw [hIdsm]; exact shiftE_zero_zero _
  have hfr : ConLeche.Semantics.frameIdx (Idss m).length (consList ts ρ) = [] := by
    rw [hIdsm]; rfl
  have hbase : BlockBaseI k w (consList ts ρ) uf Idss rsss tgtsss tlsss Eisss Fsss Esss m := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hsh]; exact hok.hI
    · rw [hsh]; exact hok.hok
    · rw [hsh, hfr, hIdsm]; trivial
  rw [blockTyG_fold hm hsp hbase, hsh, hfr,
    blockFam_app_eq_sum hok hm hreal (is := []) (by rw [hIdsm]; trivial), consList_nil, hEss,
    hIdsm]
  show sumSet _ (sumFibre _ _ (rChains 0 0 [Fs] [[]])) = _
  rw [rChains_single_nil]

end ConLeche.Model
