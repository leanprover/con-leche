module

public import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Model.Annot.BlockLfpTup
public import ConLeche.Semantics.SubstAV
import ConLeche.Semantics.Inductives.FieldsEqOn
import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.InferLemmas

public section

/-!
# The per-constructor transfer of a container frame (lane CONTSEM, step 2)

A container frame (`nestCtors`) walks each constructor of its reached
group, instantiated at the key and with the group abstracted to the
frame's holes.  By the container substitution law (`frameCrest_read`)
the walked term reads as the recorded Π-tower (M2) with its parameter and
member positions substituted all at once (`substAV τ`), and a spine fits
the walked telescope at a walk valuation `σ` exactly when it fits the
recorded fields at `substE τ 0 σ` (`spineFit_substTele`).  So the walk's
positivity (`nestFields_sem`: every walked field monotone along the
frame relation, the result's indices hole-free) moves a HOLE FIT of the
recorded constructor from the smaller to the larger side — at any two
frames that agree with the substituted valuations at the holes (M3,
`hfits_iff_of_holeAgree`).  `ctor_transfer` is that step; the frame
lemma (`Model/Inductives/ContSem.lean`) supplies the substituted
valuations and the agreement.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx)
open ConLeche.SetTheory.Tower (projS)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- The substituted valuation below a spine of the substitution's depth. -/
theorem substE_consList (τ : Nat → AnnotTerm) :
    ∀ (fs : List V) (k : Nat) (σ : Nat → V),
      substE V τ (k + fs.length) (consList fs σ) = consList fs (substE V τ k σ)
  | [], k, σ => rfl
  | a :: as, k, σ => by
    rw [consList_cons, consList_cons, List.length_cons,
      show k + (as.length + 1) = (k + 1) + as.length by omega, substE_consList τ as (k + 1),
      cons_substE]

/-- **The per-constructor transfer** (see the module docstring): a walked
constructor whose walk is positive along `R'`, whose instantiated result
is its hole applied (`nestResHead`) with hole-free indices, moves a hole
fit of the recorded constructor from any frame agreeing at the holes
with the substituted smaller walk valuation to any frame agreeing with
the substituted larger one. -/
theorem ctor_transfer {D : LfpDatum V} {ψ : Name → Nat} {c j nF nPc : Nat}
    {ctx : NestCtx} {hi' : Nat} {cur : Expr}
    {ab : List (Nat × Nat × AnnotTerm)} {Δ : List AnnotTerm}
    (hEq : FieldsEqOn V Δ (ab.map (·.2.2)) (D.fields ψ c j))
    (hlen : ab.length = nF) (hnP : (D.params ψ).length = nPc)
    {τ : Nat → AnnotTerm} {p : Nat} (hhead : (τ (D.k - 1 - c)).liftN nF 0 = .bvar p)
    {R' : FrameRel V}
    (hwalk : PiPosThen (ResultAt m φ ctx.nP hi' (hi' + nF) cur) nF R'
      (mkPisAV (AnnotTerm.substTele τ 0 ab)
        (AnnotTerm.substAV τ (AnnotTerm.mkAppN (.bvar (nF + (D.k - 1 - c)))
          ((List.range nPc).map (fun i => AnnotTerm.bvar (nPc + D.k + nF - 1 - i))
            ++ D.resIdx ψ c j)) ab.length)))
    (hres : ConLeche.nestResHead cur = true)
    (hidx : (cur.getAppArgs.drop nPc).all (fun x => !x.nestOcc ctx.names ctx.nP hi') = true)
    (hha : D.HolesApplied ψ c j)
    {σS σL ρpS ρpL XS XL : Nat → V} {vsS vsL : List V} (hR : R' σS σL)
    (hvS : substE V τ 0 σS = consList vsS ρpS) (hvL : substE V τ 0 σL = consList vsL ρpL)
    (hagS : HoleAgree D.k nPc 0 (D.frame ψ ρpS XS) (consList vsS ρpS))
    (hagL : HoleAgree D.k nPc 0 (D.frame ψ ρpL XL) (consList vsL ρpL))
    (hsatS : Sat V Δ (consList vsS ρpS)) (hsatL : Sat V Δ (consList vsL ρpL)) :
    ∀ t fs, D.HFits ψ ρpS XS t c j fs → D.HFits ψ ρpL XL t c j fs := by
  intro t fs hf
  rw [← hnP] at hagS hagL
  obtain ⟨hjS, hspS, hresS⟩ := (LfpDatum.hfits_iff_of_holeAgree hha hagS).mp hf
  have hlenS : (AnnotTerm.substTele τ 0 ab).length = nF := by
    rw [substTele_length, hlen]
  rw [← hlenS] at hwalk
  obtain ⟨htele, hresAt⟩ := piPosThen_mkPisAV _ R' _ hwalk
  -- the fields: through the substitution, the walk, and back
  have h1 : SpineFit σS ((AnnotTerm.substTele τ 0 ab).map (·.2.2)) fs :=
    (spineFit_substTele V τ ab 0 σS fs).mpr
      (by rw [hvS]; exact (hEq.spineFit_iff hsatS fs).mpr hspS)
  have h2 := spineFit_mono _ htele hR h1
  have hspL : SpineFit (consList vsL ρpL) (D.fields ψ c j) fs := by
    refine (hEq.spineFit_iff hsatL fs).mp ?_
    rw [← hvL]; exact (spineFit_substTele V τ ab 0 σL fs).mp h2
  refine (LfpDatum.hfits_iff_of_holeAgree hha hagL).mpr ⟨hjS, hspL, fun l hl => ?_⟩
  obtain ⟨e, he, heq⟩ := hresS l hl
  refine ⟨e, he, ?_⟩
  rw [← heq]
  -- the result: the hole applied, its indices hole-free
  obtain ⟨hag, hrd, hws⟩ := hresAt
  rw [hlenS] at hag hrd hws
  have hfl : fs.length = nF := by rw [h1.length_eq, List.length_map, hlenS]
  rw [hlen, AnnotTerm.substAV_mkAppN, AnnotTerm.substAV_bvar_ge τ (by omega),
    show nF + (D.k - 1 - c) - nF = D.k - 1 - c by omega, hhead] at hrd
  have hspine := Expr.mkAppN_getApp cur
  obtain ⟨i, ty, hfn⟩ : ∃ i ty, cur.getAppFn = .fvar i ty := by
    unfold ConLeche.nestResHead at hres
    split at hres
    · rename_i i ty heq; exact ⟨i, ty, heq⟩
    · exact nomatch hres
  rw [← hspine, hfn] at hrd hws
  obtain ⟨fa, vs, hfa, hsp, hvs⟩ := denoteMeta_mkAppN_inv hrd
  rw [denoteMeta_fvar] at hfa
  cases hfa
  obtain ⟨-, hvs⟩ := mkAppN_bvar_inj hvs
  rw [List.map_append] at hvs
  have hwsargs := (wScoped_mkAppN _ hws).2
  have hlv := DenoteMetaSpine.length_eq hsp
  rw [← List.take_append_drop nPc cur.getAppArgs] at hsp
  obtain ⟨vs₁, vs₂, hv12, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
  have hl₁ : vs₁.length = nPc := by
    rw [← DenoteMetaSpine.length_eq hsp₁, List.length_take]
    have : cur.getAppArgs.length = nPc + (D.resIdx ψ c j).length := by
      rw [hlv, ← hvs]; simp
    omega
  rw [hv12] at hvs
  have hvs₂ : vs₂ = (D.resIdx ψ c j).map (AnnotTerm.substAV τ · nF) := by
    have := congrArg (List.drop nPc) hvs
    rw [List.drop_left' hl₁, List.drop_left' (by simp)] at this
    rw [this]
  have hconst := constOn_spine (m := m) (φ := φ) (names := ctx.names) hag (by omega) hsp₂
    (fun a ha => ⟨hwsargs a (List.mem_of_mem_drop ha), by
      simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hidx
      exact hidx a ha⟩)
  have hce := hconst (AnnotTerm.substAV τ e nF)
    (by rw [hvs₂]; exact List.mem_map_of_mem (List.mem_of_getElem? he))
    _ _ (FrameRel.underTele_consList _ fs hR h1)
  rw [interp_substAV, interp_substAV, ← hfl, ← Nat.zero_add fs.length, substE_consList,
    substE_consList, hvS, hvL] at hce
  exact hce.symm

end ConLeche.Model
