module

public import ConLeche.Model.Annot.LfpHoleWitness
public import ConLeche.Model.Inductives.BlockLfpHoles
import ConLeche.Model.Inductives.SumData
import ConLeche.Model.Inductives.FixWitness
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Semantics.Tower.FixFamI

public section

/-!
# The fields with holes are FLAT at the install (lane HOLE2, stage D)

The producer of `LfpDatum.FlatAt` (`Model/Annot/LfpHoleWitness.lean`) at
a uniform block's datum: the constructors' fields with holes
(`BlockData.absF`) present themselves by the flat shape of the stored
field shape facts (`StoredFieldShapes.flat`: a field reading a member is
a Π-tower of hole-free domains over the member's hole applied to the
parameters and hole-free index readings, every other field hole-free,
U4), and

* **a recursive call's indices fit** its member's index telescope,
  read off the GRADING of the hole application at the hole frame of
  every tuple (`spineFit_of_wellDenoted_holeFam`: an application graded
  against a λ-tower of graphs fits its domains) — no slot fit;
* **the fields are sets of the level** by the same grading.

So `closed_of_flat` gives the hole operator its closed tuple at every
`Type`-valued parameter frame (`blockHoleClosed_of`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory.Tower (projS mkTower)
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal RecFieldKind)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A graded application against a λ-tower of graphs fits its domains -/

/-- **A spine graded against a λ-tower of graphs (`holeFam`) fits its
domains** — `spineFit_of_wellDenoted_lams` for the hole values. -/
theorem spineFit_of_wellDenoted_holeFam :
    ∀ {args Ts : List AnnotTerm} {σ ρ : Nat → V} {f : AnnotTerm} {g : List V → V},
      args.length ≤ Ts.length →
      WellDenoted V ρ (AnnotTerm.mkAppN f args) →
      interp V ρ f = holeFam σ Ts g →
      SpineFit σ (Ts.take args.length) (args.map (interp V ρ))
  | [], _, _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, hlen, _, _ => by simp at hlen
  | a :: args, T :: Ts, σ, ρ, f, g, hlen, hok, hf => by
    rw [AnnotTerm.mkAppN_cons] at hok
    have hokfa : WellDenoted V ρ (.app f a) := (WellDenoted.mkAppN_inv hok).1
    rw [WellDenoted_app] at hokfa
    obtain ⟨-, -, v, A, B, hfm, ham, -⟩ := hokfa
    have hf' : interp V ρ f
        = lamR 1 (interp V σ T) fun x => holeFam (cons x σ) Ts fun as => g (x :: as) := hf
    rw [hf'] at hfm
    have hA : A = interp V σ T := lamR_mem_piR_dom (by decide) hfm
    rw [hA] at ham
    have happ : interp V ρ (.app f a)
        = holeFam (cons (interp V ρ a) σ) Ts fun as => g (interp V ρ a :: as) := by
      rw [interp_app, hf', app_lamR_pos (by decide) ham]
    have ih := spineFit_of_wellDenoted_holeFam (args := args) (Ts := Ts)
      (σ := cons (interp V ρ a) σ) (ρ := ρ) (f := .app f a) (by simpa using hlen) hok happ
    simp only [List.length_cons, List.take_succ_cons, List.map_cons, SpineFit]
    exact ⟨ham, ih⟩

/-! ## Small readings -/

omit [SetTheory V] in
theorem holeParamVals_consList_add (k nP : Nat) :
    ∀ (L : List V) (lo : Nat) (σ : Nat → V),
      holeParamVals k nP (lo + L.length) (consList L σ) = holeParamVals k nP lo σ
  | [], lo, σ => by simp
  | a :: L, lo, σ => by
    rw [consList_cons, List.length_cons, show lo + (L.length + 1) = (lo + 1) + L.length by omega,
      holeParamVals_consList_add k nP L (lo + 1) (cons a σ), holeParamVals_cons]

/-- The per-position bound of `FieldsOkB`. -/
theorem FieldsOkB.bound_at {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsOkB w ρ Fs →
      ∀ i, i < Fs.length → ∀ as : List V, SpineFit ρ (Fs.take i) as →
        interp V (consList as ρ) (Fs.getD i default) ∈ˢ (univ w : V)
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | F :: Fs, ρ, h, 0, _, [], _ => h.2.1 hw
  | _ :: _, _, _, 0, _, _ :: _, hsp => hsp.elim
  | _ :: _, _, _, _ + 1, _, [], hsp => hsp.elim
  | F :: Fs, ρ, h, i + 1, hi, a :: as, hsp => by
    simp only [consList_cons, List.getD_cons_succ]
    exact FieldsOkB.bound_at hw (h.2.2 a hsp.1) i (by simpa using hi) as hsp.2

/-! ## The producer -/

section Producer

variable {env : Env} {mo : EnvModel V env} {d : BlockData V} {lps : List Name}

/-- **A uniform block's constructor presents its fields with holes flat**
(see the module docstring) at a `Type`-valued parameter frame: the flat
shape of the stored field shape facts (`StoredFieldShapes.flat`), and
the grading of the fields with holes at the hole frame of every tuple
(`hG`, U2) for the calls' index fit and the fields' level. -/
theorem blockFlatAt_of (hH : BlockHoleFacts mo d lps) {ψ : Name → Nat} {ρp : Nat → V}
    (hw : d.w ψ ≠ 0)
    (hlenIds : ∀ m, m < d.k → (d.IdsM m ψ).length = d.nIdxAt m)
    {c : Nat} (hc : c < d.N) {j : Nat} (hj : j < (d.ctorsM c).length)
    (hG : ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j)) :
    ∃ fas rec, d.toLfp.FlatAt ψ ρp c j fas rec := by
  obtain ⟨rec, hrec⟩ := (hH.shapes ψ c hc j hj).flat
  have hlenP : (d.params ψ).length = d.nP := hH.lenP ψ
  refine ⟨d.absF ψ c j, rec, rfl, fun _ _ _ _ _ _ => rfl, fun l tl m es h => ?_, hrec.2.1,
    hrec.2.2, ?_, ?_⟩
  · -- the recursive shape
    obtain ⟨hl, hm, hF, htl, hes, -⟩ := hrec.1 l tl m es h
    refine ⟨hl, hm, ?_, fun q dd hq => ⟨fun h0 => hw ((htl q dd hq).1.mp h0), (htl q dd hq).2⟩,
      hes⟩
    show (d.absF ψ c j).getD l default = mkPisAV tl (AnnotTerm.mkAppN
      (.bvar (l + tl.length + (d.k - 1 - m))) (holeParams d.k (d.params ψ).length (l + tl.length) ++ es))
    rw [hF, hlenP]
  · -- a recursive call's indices fit its member's index telescope: the
    -- hole application is graded at the hole frame of every tuple
    intro X hX l tl m es h as has bs hbs
    obtain ⟨hl, hmk, hF, -, -, hEsLen⟩ := hrec.1 l tl m es h
    have hwd := FieldsOkB.wellDenoted_at (hG X hX) l hl as has
    rw [hF] at hwd
    have hbody := (WellDenoted_mkPisAV_inv hwd).2 bs hbs
    have hasLen : as.length = l := by
      rw [has.length_eq, List.length_take]
      show min l (d.absF ψ c j).length = l
      omega
    have hbsLen : bs.length = tl.length := by rw [hbs.length_eq, List.length_map]
    rw [← consList_append] at hbody
    have hfr : d.toLfp.frame ψ ρp X = consList (d.holeList ψ ρp X) ρp := rfl
    rw [hfr] at hbody ⊢
    have hL : l + tl.length = (as ++ bs).length := by rw [List.length_append, hasLen, hbsLen]
    have hH' : interp V (consList (as ++ bs) (consList (d.holeList ψ ρp X) ρp))
        (.bvar (l + tl.length + (d.k - 1 - m))) = d.toLfp.holeVal ψ ρp X m := by
      rw [hL]
      exact BlockData.interp_hole_bvar hmk (as ++ bs)
    have hparsLen : (d.toLfp.pars m ψ).length = d.nP := hH.parsLen ψ _ hmk
    have hidsLen : (d.toLfp.ids m ψ).length = d.nIdxAt m := hlenIds _ hmk
    have hlenArgs : (holeParams d.k d.nP (l + tl.length) ++ es).length
        = (d.toLfp.pars m ψ ++ d.toLfp.ids m ψ).length := by
      simp only [List.length_append, holeParams, List.length_map, List.length_range]
      rw [hEsLen, hparsLen, hidsLen]
    have hfit := spineFit_of_wellDenoted_holeFam (Nat.le_of_eq hlenArgs) hbody hH'
    rw [hlenArgs, List.take_of_length_le (Nat.le_refl _), List.map_append] at hfit
    obtain ⟨v₁, v₂, heq, h₁, h₂⟩ := spineFit_append_inv hfit
    have hl₁ : v₁.length = ((holeParams d.k d.nP (l + tl.length)).map
          (interp V (consList (as ++ bs) (consList (d.holeList ψ ρp X) ρp)))).length := by
      rw [h₁.length_eq, hparsLen]; simp [holeParams]
    obtain ⟨hv₁, rfl⟩ := List.append_inj heq.symm hl₁
    rw [map_interp_holeParams, show l + tl.length = 0 + (as ++ bs).length by omega,
      holeParamVals_consList_add, holeParamVals_consList _ _ _ BlockData.holeList_length] at hv₁
    rw [hv₁, hparsLen, consList_frameIdx] at h₂
    exact h₂
  · -- the fields are sets of the level
    intro X hX l hl as has
    exact FieldsOkB.bound_at hw (hG X hX) l hl as has

/-- **The hole operator has a closed tuple** at a `Type`-valued parameter
frame (stage D: (W) from the flat presentation, `closed_of_flat`). -/
theorem blockHoleClosed_of (hH : BlockHoleFacts mo d lps) {ψ : Name → Nat} {ρp : Nat → V}
    (hs : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0)
    (hIdx : ∀ c, c < d.N → IdxOk (d.uM c ψ) ρp (d.IdsM c ψ))
    (hlenIds : ∀ m, m < d.k → (d.IdsM m ψ).length = d.nIdxAt m)
    (hG : ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j)) :
    ∃ L, IsClosedTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) (d.toLfp.holeOp ψ ρp) L := by
  have hkN : d.toLfp.k ≤ d.toLfp.N := Nat.le_add_right _ _
  have hok : d.toLfp.HoleTmOk ψ ρp := fun m hm =>
    ⟨⟨(hH.parsLen ψ m hm).trans (hH.lenP ψ).symm, hH.parsSat ψ m hm ρp hs⟩,
      fun _ => (hIdx m (Nat.lt_of_lt_of_le hm hkN)).2⟩
  refine LfpDatum.closed_of_flat hw hkN hok _ (fun X _ c hc t ht x hx => ?_)
    (fun c hc j hj => blockFlatAt_of hH hw hlenIds hc hj (hG c hc j hj))
  have happ : ∀ j, j < d.toLfp.nctors c → d.toLfp.HolesApplied ψ c j :=
    fun j hj => blockHolesApplied hH ψ hc hj
  have hres : ∀ j, j < d.toLfp.nctors c →
      (d.toLfp.resIdx ψ c j).length = (d.toLfp.ids c ψ).length := by
    intro j hj
    show (d.absE ψ c j).length = (d.IdsM c ψ).length
    simp only [BlockData.absE, List.length_map]
    exact hH.lenE ψ c hc j hj
  obtain ⟨j, fs, hf, rfl⟩ := (LfpDatum.holeOp_fibre hok hkN X happ hres ht x).mp hx
  exact ⟨j, fs, hf, if_neg hw⟩

end Producer

end ConLeche.Model
