module

public import ConLeche.Semantics.IsModelBasis
public import ConLeche.Cached.Decls
import ConLeche.Semantics.DeclWF
import ConLeche.Verify.IsModelRecords

@[expose] public section

/-!
# A constant of type `False`: the stream declares `False`, and no model holds it (task #624)

The no-`False` corollaries (`ConLeche/MainTheorem.lean`) follow from a main theorem — a model of
the input — and two facts about the input, here:

* **an accepted stream with a constant of type `False` declares the prelude's `False`**
  (`checkDecls_declaresFalse_of_constant`, model-free): the constant is stored, the environment
  is well formed, so its type's `False` is stored, and the fold stores at that name only the
  pinned block (`Cached.checkDecls_declaresFalse`);
* **no model of constants declaring the prelude's `False` holds a constant of type `False`**
  (`IsModel.no_False_constant`): `⟦False⟧` is empty there (`IsModel.false_empty`).
-/

namespace ConLeche

open SetTheory

universe w

/-- **No model of constants declaring the prelude's `False` holds a constant of type `False`.** -/
theorem IsModel.no_False_constant {V : Type w} [SetTheory V] {C : ConstantInfo → Prop}
    (h : ∃ model, IsModel V model C) (hF : DeclaresFalse C) {c : ConstantInfo} (hc : C c)
    (hty : c.type = .const falseName []) : False := by
  obtain ⟨_, hM⟩ := h
  exact hM.no_false_record hF ⟨c, hc, by rw [← hty]⟩

/-- **A record checked with a solution keeps its statement**: every constant of a record is one
of its `sideRecord`'s, up to the kind. -/
theorem sideRecord_constants {d : Declaration} {c : ConstantInfo} (hc : c ∈ d.constants) :
    ∃ c' ∈ (Cached.sideRecord d).constants, c'.toConstantVal = c.toConstantVal := by
  -- a hole's record is the axiom of its statement
  have hax : ∀ cv : ConstantVal, Cached.builtinAxiomName cv.name = false →
      c.toConstantVal = cv →
      ∃ c' ∈ (Declaration.axiomDecl cv).constants, c'.toConstantVal = c.toConstantVal := by
    intro cv hb hcv
    have h1 : cv.name ≠ quotSoundName := fun h => by
      simp [Cached.builtinAxiomName, h] at hb
    have h2 : cv.name ≠ sorryAxName := fun h => by
      simp [Cached.builtinAxiomName, h] at hb
    exact ⟨.axiomInfo cv, by simp [Declaration.constants, h1, h2], hcv.symm⟩
  -- the three kinds `sideRecord` may turn into an axiom
  have hgen : ∀ cv v, c.toConstantVal = cv →
      Cached.sideRecord d = (if (!Cached.builtinAxiomName cv.name &&
        Expr.mentionsAnyConstC [sorryAxName] v) = true then .axiomDecl cv else d) →
      ∃ c' ∈ (Cached.sideRecord d).constants, c'.toConstantVal = c.toConstantVal := by
    intro cv v hcv hs
    rw [hs]
    split
    · rename_i hb
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
      exact hax cv hb.1 hcv
    · exact ⟨c, hc, rfl⟩
  cases d with
  | defnDecl cv v hint =>
    refine hgen cv v ?_ rfl
    simp only [Declaration.constants] at hc
    split at hc <;> simp_all [ConstantInfo.toConstantVal]
  | thmDecl cv v =>
    refine hgen cv v ?_ rfl
    simp only [Declaration.constants, List.mem_singleton] at hc
    subst hc; rfl
  | opaqueDecl cv v =>
    refine hgen cv v ?_ rfl
    simp only [Declaration.constants, List.mem_singleton] at hc
    subst hc; rfl
  | axiomDecl => exact ⟨c, hc, rfl⟩
  | quotDecl => exact ⟨c, hc, rfl⟩
  | indDecl => exact ⟨c, hc, rfl⟩

/-- **An accepted stream holding a constant of type `False` declares the prelude's `False`**,
model-free: the constant is stored, its type's `False` with it (`EnvWF`), and the fold stores at
`False`'s name only the pinned block.  With or without a solution. -/
theorem checkDecls_declaresFalse_of_constant {pins : List NatOpPinSet} {maxNatSize : Nat}
    {ds : Array Declaration} {justify : Option Env}
    (h : (Cached.checkDeclsWith .verified pins maxNatSize ds justify).isOk) {c : ConstantInfo}
    (hc : c ∈ constantsOf ds.toList) (hty : c.type = .const falseName []) :
    DeclaresFalse (· ∈ constantsOf ds.toList) := by
  obtain ⟨env, h⟩ : ∃ env, Cached.checkDeclsWith .verified pins maxNatSize ds justify = .ok env := by
    cases h' : Cached.checkDeclsWith .verified pins maxNatSize ds justify with
    | error => rw [h'] at h; cases h
    | ok env => exact ⟨env, rfl⟩
  -- the constant, as the fold checks it
  obtain ⟨c', hc', hcv⟩ : ∃ c' ∈ constantsOf (Cached.sideRecords justify ds).toList,
      c'.toConstantVal = c.toConstantVal := by
    cases justify with
    | none => exact ⟨c, hc, rfl⟩
    | some _ =>
      obtain ⟨d, hd, hcd⟩ := mem_constantsOf.1 hc
      obtain ⟨c', hc', hcv⟩ := sideRecord_constants hcd
      refine ⟨c', mem_constantsOf.2 ⟨_, ?_, hc'⟩, hcv⟩
      simp only [Cached.sideRecords, Array.toList_map]
      exact List.mem_map_of_mem hd
  obtain ⟨ci, hf, ⟨hst, -⟩, -⟩ := Cached.checkDecls_recordsStored h c' hc'
  refine Cached.checkDecls_declaresFalse h ?_
  obtain ⟨-, -, hres, -⟩ := (Semantics.checkDecls_envWF h).consts ci (Env.find?_mem hf)
  rw [hst, hcv] at hres
  change Expr.constsResolve env c.type = true at hres
  rw [hty] at hres
  exact hres

end ConLeche
