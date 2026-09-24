module

public import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Annot.BlockLfpTup
import ConLeche.Model.Inductives.ContCtor

public section

/-!
# An INSTANTIATED container constructor, read (lane NESTIND, O12)

A recursor whose major is an outside container `C us ds` (an auxiliary
recursor of a nested block) has one minor premise per constructor of
`C`'s component, its fields the constructor's type INSTANTIATED at the
major's levels `us` and parameters `ds` — every member of `C`'s block
stays a constant (`.const (D.member mm) us`), read by its leaf.

This is CONTSEM's frame reading (`crest_read`) at the EMPTY group (no
member abstracted, `GrpWf`, `grpSub us hi [] = none`), followed by the
hole-agreement step of `ctor_transfer`: the member constants, applied to
the parameters, ARE the hole values of the carrier (`holeAgree_instance`
at the empty group), so a spine fits the instantiated constructor's
fields exactly when it hole-fits the recorded constructor at the key
frame and the carrier (`instCtor_hfits`).  This is what the recursor's
rule data read at an outside class: the decoding fit of a container
constructor is the clause's own `HFits` at the parameters' readings.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal NestCtx)
open ConLeche.SetTheory.Tower (projS)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- A context whose lookups are the environment's (the empty group reads
nothing else of it). -/
@[expose] def instCtx (env : Env) : NestCtx :=
  { names := [], lps := [], nP := 0, nIdxs := [], params := [], sort := .zero,
    find? := env.find?, consts := [] }

omit [SetTheory V] in
/-- The empty group is well formed. -/
theorem grpWf_nil {D : LfpDatum V} {hi : Nat} {us : List Level} {ds : List Expr} (ctx : NestCtx) :
    GrpWf ctx D hi us ds [] :=
  ⟨List.nodup_nil, fun _ hp => absurd hp List.not_mem_nil⟩

/-- The empty group substitutes nothing. -/
theorem grpSub_nil (us : List Level) (hi : Nat) (e : Expr) : e.replaceConsts (grpSub us hi []) = e :=
  replaceConsts_none (fun _ _ => grpSub_none (by simp)) e

/-- **The instantiated constructor's substitution**: the parameters at
their readings, every member its constant's reading (the depth-`hi`
readings of `grpS` at the empty group). -/
@[expose] noncomputable def instTau {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (φ : Name → Nat) (D : LfpDatum V) (us : List Level) (hi : Nat) (ds : List Expr) :
    Nat → AnnotTerm :=
  substTau (ds.length + D.k) hi (grpX mp.base2 φ D us hi [] ds hi)

section Inst

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List AnnotTerm}
  (hdsa : DenoteMetaSpine mp.base2.acval env φ hi ds dsa)
  (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)

include hD hnN hkN hlps hnd hul hds hdsa hlenP

/-- **An instantiated container constructor, read** (group-free
`crest_read`): constructor `(c, j)` of `D`'s component `c`, at the
levels `us` and the parameters `ds` (depth `hi`), is a Π-tower that
reads at depth `hi` as the recorded one substituted by `instTau`; its
recorded fields agree with the record's under the parameters and the
members' former types. -/
theorem instCtor_read {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal}
    {nF : Nat} (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv ds.length nF)) :
    cv.levelParams = lps ∧ ∃ crest ab,
      ConLeche.instPisWith ds (cv.type.instantiateLevelParams cv.levelParams us) = some crest ∧
      (∃ Tys : List AnnotTerm, Tys.length = D.k ∧
        (∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
          denoteMeta mp.base2.acval env (Level.substFn φ lps us) 0 cvm.type
            = some (Tys.getD mm default)) ∧
        FieldsEqOn V (D.params (Level.substFn φ lps us) ++ Tys).reverse (ab.map (·.2.2))
          (D.fields (Level.substFn φ lps us) c j)) ∧ ab.length = nF ∧
      denoteMeta mp.base2.acval env φ hi crest
        = some (mkPisAV (AnnotTerm.substTele (instTau mp φ D us hi ds) 0 ab)
            (AnnotTerm.substAV (instTau mp φ D us hi ds)
              (AnnotTerm.mkAppN (.bvar (nF + (D.k - 1 - c)))
                ((List.range ds.length).map (fun i => AnnotTerm.bvar (ds.length + D.k + nF - 1 - i))
                  ++ D.resIdx (Level.substFn φ lps us) c j)) ab.length)) := by
  have h := crest_read mp hD hnN hkN (ctx := instCtx env) (fun _ => rfl) hlps hnd hul hds hdsa
    hlenP (grpWf_nil (instCtx env)) hc hj hfc
  unfold instTau
  simpa only [grpSub_nil, List.length_nil, Nat.add_zero] using h

/-- The empty group's substituted valuation: the members' constants'
readings in the member slots, the parameters' readings below. -/
theorem instTau_substE (ρ : Nat → V) :
    substE V (instTau mp φ D us hi ds) 0 ρ
      = consList ((List.range D.k).map fun mm =>
          interp V ρ (mp.base2.acval (D.member mm) (Level.substFn φ lps us)))
        (keyFrame dsa hi ρ) := by
  have h := substE_grp mp hD hnN hkN (ctx := instCtx env) (fun _ => rfl) hlps hnd hul hds hdsa
    hlenP (grpWf_nil (instCtx env)) (keyFrame dsa hi ρ) (fun _ => ρ 0) ρ
  have hG : ∀ mm, InGrp D ([] : List (Name × Expr)) mm ↔ False := fun mm => by
    simp [InGrp]
  simp only [hG, decide_false, Bool.false_eq_true, if_false, grpVals, List.map_nil,
    List.length_nil, Nat.add_zero] at h
  unfold instTau
  exact h

/-- **The hole fit of an instantiated container constructor** (O12): a
spine hole-fits the recorded constructor `(c, j)` at the parameters'
readings (the key frame) and the carrier exactly when it fits the
instantiated constructor's fields as read (`instCtor_read`'s tower) and
its result's index readings are the index tuple's components. -/
theorem instCtor_hfits {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {nF : Nat}
    {ab : List (Nat × Nat × AnnotTerm)} {Tys : List AnnotTerm} (hlT : Tys.length = D.k)
    (hTys : ∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) 0 cvm.type
        = some (Tys.getD mm default))
    (hEq : FieldsEqOn V (D.params (Level.substFn φ lps us) ++ Tys).reverse (ab.map (·.2.2))
      (D.fields (Level.substFn φ lps us) c j)) (hlen : ab.length = nF)
    {ρ : Nat → V} (hs : Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ))
    (t : V) (fs : List V) :
    D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ)
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) t c j fs ↔
      (j < D.nctors c ∧
        SpineFit ρ ((AnnotTerm.substTele (instTau mp φ D us hi ds) 0 ab).map (·.2.2)) fs ∧
        ∀ l, l < (D.ids c (Level.substFn φ lps us)).length → ∃ e,
          (D.resIdx (Level.substFn φ lps us) c j)[l]? = some e ∧
          interp V (consList fs ρ) (AnnotTerm.substAV (instTau mp φ D us hi ds) e nF)
            = projS l t) := by
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  have hS := instTau_substE mp hD hnN hkN hlps hnd hul hds hdsa hlenP ρ
  generalize hψ : Level.substFn φ lps us = ψ at hs hlenP hTys hEq hS ⊢
  let vs : List V := (List.range D.k).map fun mm => interp V ρ (mp.base2.acval (D.member mm) ψ)
  have hag := holeAgree_instance mp hD hs ρ (fun _ => false) (D.carrier ψ (keyFrame dsa hi ρ))
    (vs := vs) (by simp [vs]) (fun m hm => by simp [vs])
  have hcar : (fun c => if (fun _ => false) c = true then D.carrier ψ (keyFrame dsa hi ρ) c
      else D.carrier ψ (keyFrame dsa hi ρ) c) = D.carrier ψ (keyFrame dsa hi ρ) := by
    funext c; simp
  rw [hcar] at hag
  have hsat := frameVals_sat mp hD hs hlT hTys (fun _ => false)
    (D.carrier ψ (keyFrame dsa hi ρ)) (fun c hc => lfpTuple_mem _ _ _ _ c hc) ρ
  have hsat' : Sat V (D.params ψ ++ Tys).reverse (consList vs (keyFrame dsa hi ρ)) := by
    simpa [vs] using hsat
  rw [LfpDatum.hfits_iff_of_holeAgree (h.holeApp ψ c (Nat.lt_of_lt_of_le hc h.kN) j hj) hag]
  have hfit : ∀ fs : List V,
      SpineFit ρ ((AnnotTerm.substTele (instTau mp φ D us hi ds) 0 ab).map (·.2.2)) fs ↔
        SpineFit (consList vs (keyFrame dsa hi ρ)) (D.fields ψ c j) fs := by
    intro fs
    rw [spineFit_substTele, hS]
    exact hEq.spineFit_iff hsat' fs
  have hidx : SpineFit ρ ((AnnotTerm.substTele (instTau mp φ D us hi ds) 0 ab).map (·.2.2)) fs →
      ∀ e, interp V (consList fs ρ) (AnnotTerm.substAV (instTau mp φ D us hi ds) e nF)
        = interp V (consList fs (consList vs (keyFrame dsa hi ρ))) e := by
    intro hsp e
    have hfl : fs.length = nF := by
      rw [hsp.length_eq, List.length_map, substTele_length, hlen]
    rw [interp_substAV, ← hfl, ← Nat.zero_add fs.length, substE_consList, hS]
  constructor
  · rintro ⟨hj, hsp, hr⟩
    have hsp' := (hfit fs).mpr hsp
    refine ⟨hj, hsp', fun l hl => ?_⟩
    obtain ⟨e, he, heq⟩ := hr l hl
    exact ⟨e, he, by rw [hidx hsp' e, heq]⟩
  · rintro ⟨hj, hsp, hr⟩
    refine ⟨hj, (hfit fs).mp hsp, fun l hl => ?_⟩
    obtain ⟨e, he, heq⟩ := hr l hl
    exact ⟨e, he, by rw [← hidx hsp e, heq]⟩

end Inst

end ConLeche.Model
