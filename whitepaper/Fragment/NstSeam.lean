module

public import Fragment.Install
public import Fragment.NstInstall

@[expose] public section

/-!
# SCAFFOLDING — the plain block's new family is the frozen lane's

The nested lane reads a container's installation through the frozen
`BlockLaw` (`NstBlockModel.lean`): the former's set is the graph of
the OLD family (`Nst.IndSpec.famSet`), the constructors' sets its
graphs, the domains bounded in the old sense.  A plain block is now
installed by the NEW model (`Install.lean`: the family the least fixed
point of the block's operator inside the set theory).  This file
shows the two families equal at fitting parameters, under the
hypotheses the installer has — so the new model satisfies the old law
and the nested lane keeps reading it.  Delete with the scaffolding
when the nested lane is ported.

**The proof.**  The old family is `sep` of a closed-under-the-law
bounding set by the predicate-level least fixed point of the same
constructor clauses (`Nst.IndSpec.Fam`); the fits of the two
constructions coincide once the old bound-and-predicate is read as
the family of fibres it defines (`FitsFields_old_iff`).  The old
family is then closed under the new operator (the old constructor
law, `Nst.IndSpec.ctorVal_mem_Fam`), so the new least fixed point
lies below it; and the old predicate's induction (`Nst.IndSpec.Mem_ind`)
puts every old member into the new family, since the new family is
closed under the constructors (`ctorVal_mem_Fam`).
-/

namespace Fragment.IndSpec.Nst
open SetLib UnivLib IndLib

universe u

variable {V : Type u} [IndLib V]

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat)

/-- The old reading of a non-container field is the new reading at the
family of fibres its bound and predicate define. -/
theorem fieldSet_old_eq (B : List V → List V → V) (P : FamP V) (ps fs : List V) :
    ∀ f : Field, f.isCont = false →
      S.fieldSet M ls B P ps fs f
        = Fragment.IndSpec.fieldSet S M ls (fun is => fibreR (S.z ls) (B ps is) (P ps is)) ps fs f
  | .ordinary _, _ => rfl
  | .reflexive _ _, _ => rfl
  | .container, h => by simp [Field.isCont] at h

/-- The fits of the two constructions coincide, away from container
fields. -/
theorem FitsFields_old_iff (B : List V → List V → V) (P : FamP V) (ps : List V) :
    ∀ {fields : List Field} {fs : List V}, (∀ f ∈ fields, f.isCont = false) →
      (S.FitsFields M ls B P ps fields fs ↔
        Fragment.IndSpec.FitsFields S M ls (fun is => fibreR (S.z ls) (B ps is) (P ps is)) ps fields fs)
  | [], [], _ => Iff.rfl
  | [], _ :: _, _ => Iff.rfl
  | _ :: _, [], _ => Iff.rfl
  | f :: fields, v :: fs, h => by
    show (_ ∧ _) ↔ (_ ∧ _)
    rw [FitsFields_old_iff B P ps (fun f' hf' => h f' (List.mem_cons_of_mem f hf')),
      S.fieldSet_old_eq M ls B P ps fs f (h f List.mem_cons_self)]

/-- **The new family is the old one** at parameters where the
installer's hypotheses hold. -/
theorem Fam_eq_old (hnr : S.NoRecDep) (hnc : S.NoCont) {ps : List V}
    (hb : Fragment.IndSpec.DomsBounded S M ls ps) (hbo : S.DomsBounded M ls ps) (is : List V) :
    Fragment.IndSpec.Fam S M ls ps is = S.Fam M ls ps is := by
  have hcb := S.contInBound_of_noCont hnc M ls ps
  refine Sub.antisymm ?_ ?_
  · -- the old family is closed under the new operator
    refine lfpFamSet_least (X := S.Fam M ls ps) ⟨fun is => S.Fam_mem_univ M ls ps is, fun is x hx => ?_⟩ is
    obtain ⟨j, c, fs, hc, hfit, his, rfl⟩ := (Fragment.IndSpec.mem_famOp S M ls).mp hx
    have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
    have hfit' : S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs :=
      (S.FitsFields_old_iff M ls _ _ ps (fun f hf => hnc c hcm f hf)).mpr hfit
    rw [his]
    exact S.ctorVal_mem_Fam M ls hc hfit' hnr hbo hcb
  · -- every old member is a new one: induction over the old predicate
    intro t ht
    have key : ∀ ps' is x, S.Mem M ls ps' is x → ps' = ps →
        S.memb ls x ∈ˢ Fragment.IndSpec.Fam S M ls ps is := by
      intro ps' is x hm
      refine S.Mem_ind M ls
        (P := fun ps' is x => ps' = ps → S.memb ls x ∈ˢ Fragment.IndSpec.Fam S M ls ps is) ?_ hm
      intro ps' is x hs hps
      subst hps
      obtain ⟨j, c, fs, hc, hfit, his, rfl⟩ := hs
      have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
      have hfitW := (S.FitsFields_old_iff M ls _ _ ps' (fun f hf => hnc c hcm f hf)).mp hfit
      have hfitN := Fragment.IndSpec.FitsFields_mono S M ls
        (Fragment.IndSpec.Fam_inUniv S M ls ps') ?_ ps' hfitW
      · have hmemb : S.memb ls (tag (S.tagOf j) (tuple fs.reverse)) = S.ctorVal ls j fs := rfl
        rw [hmemb, his]
        exact Fragment.IndSpec.ctorVal_mem_Fam S M ls hnr hb hc hfitN
      · intro is y hy
        cases hz : S.z ls
        · rw [hz] at hy
          obtain ⟨-, -, hP⟩ := mem_fibreR_false.mp hy
          have := hP rfl
          unfold memb at this
          rwa [hz] at this
        · rw [hz] at hy
          obtain ⟨rfl, y', -, hP⟩ := mem_fibreR_true.mp hy
          have := hP rfl
          unfold memb at this
          rwa [hz] at this
    cases hz : S.z ls
    · obtain ⟨-, hm⟩ := (S.mem_Fam_false M ls hz).mp ht
      have := key ps is t hm rfl
      unfold memb at this
      rwa [hz] at this
    · obtain ⟨rfl, x, hm⟩ := (S.mem_Fam_true M ls hz).mp ht
      have := key ps is x hm rfl
      unfold memb at this
      rwa [hz] at this

/-- The former's set, new and old, at every level list. -/
theorem famSet_eq_old (hnr : S.NoRecDep) (hnc : S.NoCont)
    (hb : ∀ ps, FitsVals M (S.ψ ls) base S.params ps → Fragment.IndSpec.DomsBounded S M ls ps)
    (hbo : ∀ ps, FitsVals M (S.ψ ls) base S.params ps → S.DomsBounded M ls ps) :
    Fragment.IndSpec.famSet S M ls = S.famSet M ls := by
  unfold Fragment.IndSpec.famSet Fragment.IndSpec.famSetF famSet
  refine lamCtx_congr M _ fun vs hvs => ?_
  have hl := FitsVals_length M _ hvs
  simp only [List.length_append] at hl
  obtain ⟨hps, -⟩ := (FitsVals_append M _ (by simp [hl, nI])).mp
    (show FitsVals M (S.ψ ls) base (S.indices ++ S.params) (vs.take S.nI ++ vs.drop S.nI) by
      rw [List.take_append_drop]; exact hvs)
  have e1 : S.nI = S.indices.length := rfl
  have e2 : S.nP = S.params.length := rfl
  rw [readEnv_shiftE_consList (by omega), readEnv_consList_take (by omega),
    List.take_of_length_le (by rw [List.length_drop]; omega)]
  exact S.Fam_eq_old M ls hnr hnc (hb _ hps) (hbo _ hps) _

/-- The model with the former, new and old. -/
theorem M₁_eq_old (hnr : S.NoRecDep) (hnc : S.NoCont)
    (hb : ∀ ls ps, FitsVals M (S.ψ ls) base S.params ps → Fragment.IndSpec.DomsBounded S M ls ps)
    (hbo : ∀ ls ps, FitsVals M (S.ψ ls) base S.params ps → S.DomsBounded M ls ps) :
    Fragment.IndSpec.M₁ S M = S.M₁ M := by
  funext n ls'
  simp only [Fragment.IndSpec.M₁, Fragment.IndSpec.M₁F, M₁]
  split
  · exact S.famSet_eq_old M ls' hnr hnc (hb ls') (hbo ls')
  · rfl

/-- A constructor's set, new and old. -/
theorem ctorSet_eq_old (hnr : S.NoRecDep) (hnc : S.NoCont)
    (hb : ∀ ls ps, FitsVals M (S.ψ ls) base S.params ps → Fragment.IndSpec.DomsBounded S M ls ps)
    (hbo : ∀ ls ps, FitsVals M (S.ψ ls) base S.params ps → S.DomsBounded M ls ps)
    (j : Nat) (c : CtorSpec) : Fragment.IndSpec.ctorSet S M ls j c = S.ctorSet M ls j c := by
  unfold Fragment.IndSpec.ctorSet ctorSet
  rw [S.M₁_eq_old M hnr hnc hb hbo]

end IndSpec

end Fragment.IndSpec.Nst
