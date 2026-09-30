module

public import ConLeche.Model.Inductives.NestPosMono
public import ConLeche.Semantics.SubstAV
import ConLeche.Semantics.Inductives.FieldsEqOn
import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.InferLemmas

public section

/-!
# The per-constructor transfer of a container frame

A container frame (`nestCtors`) walks each constructor of its reached
group, instantiated at the key and with the group abstracted to the
frame's holes.  By the container substitution law (`frameCrest_read`)
the walked term reads as the recorded Π-tower (M2) with its parameter and
member positions substituted all at once (`substAV τ`), and a spine fits
the walked telescope at a walk valuation `σ` exactly when it fits the
recorded fields at `substE τ 0 σ` (`spineFit_substTele`).  So the walk's
positivity (`PiPosThen`: every walked field monotone along the
frame relation, the result's indices hole-free) moves a HOLE FIT of the
recorded constructor from the smaller to the larger side — the
substituted valuations ARE hole frames of the recorded block (the frame's
group is the container's whole block).  `ctor_transfer` is that step;
the frame lemma (`frameIter`, `ContWalk.lean`) supplies the substituted
valuations.
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

/-- **A hole-applied result's indices are constant along the walk's
relation**: the result reads to the hole applied to the substituted index
expressions, which are hole-free, so each substituted index reads alike on
related frames. -/
theorem resIdx_constOn {D : LfpDatum V} {ψ : Name → Nat} {c j nF : Nat}
    {ctx : NestCtx} {hi' : Nat} {cur : Expr}
    {τ : Nat → AnnotTerm} {p : Nat} (hhead : (τ (D.k - 1 - c)).liftN nF 0 = .bvar p)
    {Rx : FrameRel V}
    (hresAt : ResultAt m φ ctx.nP hi' (hi' + nF) cur Rx
      (AnnotTerm.substAV τ (AnnotTerm.mkAppN (.bvar (nF + (D.k - 1 - c))) (D.resIdx ψ c j)) nF))
    (hres : ConLeche.nestResHead cur = true)
    (hidx : cur.getAppArgs.all (fun x => !x.nestOcc ctx.names ctx.nP hi') = true) :
    ∀ e ∈ D.resIdx ψ c j, ConstOn Rx (AnnotTerm.substAV τ e nF) := by
  intro e he
  obtain ⟨hag, hrd, hws⟩ := hresAt
  rw [AnnotTerm.substAV_mkAppN, AnnotTerm.substAV_bvar_ge τ (by omega),
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
  have hwsargs := (wScoped_mkAppN _ hws).2
  have hconst := constOn_spine (m := m) (φ := φ) (names := ctx.names) hag (by omega) hsp
    (fun a ha => ⟨hwsargs a ha, by
      simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hidx
      exact hidx a ha⟩)
  exact hconst _ (by rw [← hvs]; exact List.mem_map_of_mem he)

/-- **The per-constructor transfer** (see the module docstring): a walked
constructor whose walk is positive along `R'`, whose instantiated result
is its hole applied (`nestResHead`) with hole-free indices, moves a hole
fit of the recorded constructor from the hole frame the substituted
smaller walk valuation IS to the one the substituted larger one is. -/
theorem ctor_transfer {D : LfpDatum V} {ψ : Name → Nat} {c j nF : Nat}
    {ctx : NestCtx} {hi' : Nat} {cur : Expr}
    {ab : List (Nat × Nat × AnnotTerm)} {Δ : List AnnotTerm}
    (hEq : FieldsEqOn V Δ (ab.map (·.2.2)) (D.fields ψ c j))
    (hlen : ab.length = nF)
    {τ : Nat → AnnotTerm} {p : Nat} (hhead : (τ (D.k - 1 - c)).liftN nF 0 = .bvar p)
    {R' : FrameRel V}
    (hwalk : PiPosThen (ResultAt m φ ctx.nP hi' (hi' + nF) cur) nF R'
      (mkPisAV (AnnotTerm.substTele τ 0 ab)
        (AnnotTerm.substAV τ (AnnotTerm.mkAppN (.bvar (nF + (D.k - 1 - c))) (D.resIdx ψ c j))
          ab.length)))
    (hres : ConLeche.nestResHead cur = true)
    (hidx : cur.getAppArgs.all (fun x => !x.nestOcc ctx.names ctx.nP hi') = true)
    {σS σL ρpS ρpL XS XL : Nat → V} (hR : R' σS σL)
    (hvS : substE V τ 0 σS = D.frame ψ ρpS XS) (hvL : substE V τ 0 σL = D.frame ψ ρpL XL)
    (hsatS : Sat V Δ (D.frame ψ ρpS XS)) (hsatL : Sat V Δ (D.frame ψ ρpL XL)) :
    ∀ t fs, D.HFits ψ ρpS XS t c j fs → D.HFits ψ ρpL XL t c j fs := by
  intro t fs hf
  obtain ⟨hjS, hspS, hresS⟩ := hf
  have hlenS : (AnnotTerm.substTele τ 0 ab).length = nF := by
    rw [substTele_length, hlen]
  rw [← hlenS] at hwalk
  obtain ⟨htele, hresAt⟩ := piPosThen_mkPisAV _ R' _ hwalk
  -- the fields: through the substitution, the walk, and back
  have h1 : SpineFit σS ((AnnotTerm.substTele τ 0 ab).map (·.2.2)) fs :=
    (spineFit_substTele V τ ab 0 σS fs).mpr
      (by rw [hvS]; exact (hEq.spineFit_iff hsatS fs).mpr hspS)
  have h2 := spineFit_mono _ htele hR h1
  have hspL : SpineFit (D.frame ψ ρpL XL) (D.fields ψ c j) fs := by
    refine (hEq.spineFit_iff hsatL fs).mp ?_
    rw [← hvL]; exact (spineFit_substTele V τ ab 0 σL fs).mp h2
  refine ⟨hjS, hspL, fun l hl => ?_⟩
  obtain ⟨e, he, heq⟩ := hresS l hl
  refine ⟨e, he, ?_⟩
  rw [← heq]
  -- the result: the hole applied, its indices hole-free
  have hfl : fs.length = nF := by rw [h1.length_eq, List.length_map, hlenS]
  rw [hlenS, hlen] at hresAt
  have hce := resIdx_constOn hhead hresAt hres hidx e (List.mem_of_getElem? he)
    _ _ (FrameRel.underTele_consList _ fs hR h1)
  rw [interp_substAV, interp_substAV, ← hfl, ← Nat.zero_add fs.length, substE_consList,
    substE_consList, hvS, hvL] at hce
  exact hce.symm

end ConLeche.Model
