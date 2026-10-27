module

public import ConLeche.Model.Inductives.ContInst
public import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# A recursor rule's data at an OUTSIDE major

The target check opens a rule of a recursor whose major is an outside
container `C us ds` (`TargetRuleRun`): the constructor at the major's
instantiation (`instPisWith M.ds (targetCtorAt M c)`, levels
instantiated), then its `nF` fields at the rule's prefix depth
(`openPisAtFvars nF crest rP`).  `instCtor_open` reads that opening
through the container's clause (`instCtor_read`): the fields' domains
are the recorded fields substituted by `instTau`, the conclusion the
recorded result — the member's former at the parameters and the
recorded result indices, substituted.  With `instCtor_fit`/`instCtor_decode` this is
what the rule data (`fdoms`, `es`, `mk`) read at an outside class.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantVal)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

section Inst

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List Term}
  (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa)
  (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)

include hD hnN hkN hlps hnd hul hds hdsa hlenP

omit hnN hkN in
/-- **The opened instantiated constructor, read**: constructor
`(c, j)` of `D` at the levels `us` and the parameters `ds`, opened at
depth `hi` over its `nF` fields: the fields' domains read as the
recorded fields substituted by `instTau` (each opener at its own
depth), and the conclusion reads as the recorded result substituted. -/
theorem instCtor_open {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal}
    {nF : Nat} (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv ds.length nF))
    {crest : Expr}
    (hcr : ConLeche.instPisWith ds (cv.type.instantiateLevelParams cv.levelParams us)
      = some crest)
    {fvsF : List Expr} {cbody : Expr}
    (hfld : ConLeche.openPisAtFvars nF crest hi = some (fvsF, cbody)) :
    cv.levelParams = lps ∧ ∃ ab : List Term,
      (∃ Tys : List Term, Tys.length = D.k ∧
        (∀ mm, mm < D.k → ∃ cvm caps ty, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
          ConLeche.instPisWith (canonParams ds.length) cvm.type = some ty ∧
          denote mp.base2.acval env (Level.substFn φ lps us) (ds.length + mm) ty
            = some (Tys.getD mm default)) ∧
        FieldsEqOn V (D.params (Level.substFn φ lps us) ++ Tys).reverse ab
          (D.fields (Level.substFn φ lps us) c j)) ∧ ab.length = nF ∧
      readOpenedDoms mp.base2.acval env φ hi fvsF
        = Term.substTele (instTau mp φ D us hi ds) 0 ab ∧
      (∀ (l : Nat) (x : Expr), fvsF[l]? = some x →
        denote mp.base2.acval env φ (hi + l) x.fvarTypeD
          = some ((Term.substTele (instTau mp φ D us hi ds) 0 ab).getD l
              default)) ∧
      denote mp.base2.acval env φ (hi + nF) cbody
        = some (Term.substAV (instTau mp φ D us hi ds)
            (Term.mkAppN (.bvar (nF + (D.k - 1 - c)))
              (D.resIdx (Level.substFn φ lps us) c j)) nF) ∧
      denote mp.base2.acval env φ hi crest
        = some (mkPisAV (Term.substTele (instTau mp φ D us hi ds) 0 ab)
            (Term.substAV (instTau mp φ D us hi ds)
              (Term.mkAppN (.bvar (nF + (D.k - 1 - c)))
                (D.resIdx (Level.substFn φ lps us) c j)) nF)) := by
  obtain ⟨hlp, crest', ab, hcr', hTy, hlab, hrd⟩ :=
    instCtor_read mp hD hlps hnd hul hds hdsa hlenP hc hj hfc
  rw [hcr] at hcr'
  obtain rfl := Option.some.inj hcr'
  refine ⟨hlp, ab, hTy, hlab, ?_⟩
  have hrd' := hrd
  rw [hlab] at hrd'
  obtain ⟨pps, b, hst, hb, hlen, hbind⟩ := denote_openPis nF hfld hrd
  have hstEq := stripPisAV_mkPisAV (Term.substTele (instTau mp φ D us hi ds) 0 ab)
    (Term.substAV (instTau mp φ D us hi ds)
      (Term.mkAppN (.bvar (nF + (D.k - 1 - c)))
        (D.resIdx (Level.substFn φ lps us) c j)) ab.length)
  rw [substTele_length, hlab] at hstEq
  rw [hlab] at hst
  rw [hstEq] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst.symm)
  refine ⟨?_, fun l x hx => ?_, hb, hrd'⟩
  · exact readOpenedDoms_eq fvsF _ hi
      (by rw [openPisAtFvars_length _ hfld, substTele_length, hlab])
      (fun i x hx => by
        obtain ⟨q, hq, hd⟩ := hbind i x hx
        exact ⟨q, hq, hd⟩)
  · obtain ⟨q, hq, hd⟩ := hbind l x hx
    rw [List.getD_eq_getElem?_getD, hq]
    exact hd

end Inst

end ConLeche.Model
