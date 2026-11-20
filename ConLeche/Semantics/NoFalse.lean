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

/-- **An accepted stream holding a constant of type `False` declares the prelude's `False`**,
model-free: the constant is stored, its type's `False` with it (`EnvWF`), and the fold stores at
`False`'s name only the pinned block. -/
theorem checkDecls_declaresFalse_of_constant {pins : List NatOpPinSet} {maxNatSize : Nat}
    {ds : Array Declaration}
    (h : (Cached.checkDecls .verified pins maxNatSize ds).isOk) {c : ConstantInfo}
    (hc : c ∈ constantsOf ds.toList) (hty : c.type = .const falseName []) :
    DeclaresFalse (· ∈ constantsOf ds.toList) := by
  obtain ⟨env, h⟩ : ∃ env, Cached.checkDecls .verified pins maxNatSize ds = .ok env := by
    cases h' : Cached.checkDecls .verified pins maxNatSize ds with
    | error => rw [h'] at h; cases h
    | ok env => exact ⟨env, rfl⟩
  obtain ⟨ci, hf, ⟨hst, -⟩, -⟩ := Cached.checkDecls_recordsStored h c hc
  refine Cached.checkDecls_declaresFalse h ?_
  obtain ⟨-, -, hres, -⟩ := (Semantics.checkDecls_envWF h).consts ci (Env.find?_mem hf)
  rw [hst] at hres
  change Expr.constsResolve env c.type = true at hres
  rw [hty] at hres
  exact hres

end ConLeche
