module

public import ConLeche.OleanInput
public import ConLeche.Verify.Driver.Graph
public import ConLeche.Driver.Cli
import ConLeche.Model.Modular.SeesMain
import ConLeche.Semantics.IsModelBasis

public section

/-!
# The modular corollaries, from the modular theorem (task #621)

No module of an accepted closure holds a theorem of type `False` where `False` is the prelude's:
the module declares the prelude's `False` itself, or sees `False` as a module that does
(`Sees`).  The proof reads only the family `main_modular` gives: the declaring module's model
makes `⟦False⟧` empty (`IsModel.false_empty`), the theorem's module gives `False` that model's
value, and its own model puts the theorem in `⟦False⟧`.
-/

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Frontend ConLeche.Frontend.Olean

universe w

/-- **A family of models as the modular theorem gives it has no theorem of type `False`** at a
module of the closure that declares the prelude's `False`, or sees `False` as a module that
does. -/
theorem family_no_False {V : Type w} [SetTheory V] {sp : Roots} {fs : FS} {roots : Array Name}
    {model : Name → (Name → List Nat → V)}
    (hM : ∀ m, InClosure sp fs roots m → IsModel V (model m) (moduleConstants sp fs m))
    (hS : ∀ m n m', InClosure sp fs roots m → Sees sp fs m n m' → model m n = model m' n)
    {m m' : Name} (hm : InClosure sp fs roots m) (hF : m' = m ∨ Sees sp fs m falseName m')
    (hD : DeclaresFalse (moduleConstants sp fs m'))
    {d : ModDecoded} {c : CEntryF Name Expr} {v : Expr} {all : List Name}
    (hv : ViewOf sp fs m d) (hmem : c ∈ d.constants) (hk : c.kind = .thm v all)
    (hty : c.type = .const falseName []) : False := by
  have hm' : InClosure sp fs roots m' := by
    rcases hF with rfl | hs
    · exact hm
    · exact sees_inClosure hm hs
  have hval : model m falseName = model m' falseName := by
    rcases hF with rfl | hs
    · rfl
    · exact hS m falseName m' hm hs
  have hc : HasConstant (moduleConstants sp fs m) c.name c.levelParams (.const falseName []) :=
    ⟨_, moduleConstants_thm hv hmem hk, by simp [CEntryF.cv, ConstantInfo.toConstantVal, hty]⟩
  have hmem' := (hM m hm).mem_of_hasRecord hc (c.levelParams.map fun _ => 0) (by simp)
  have he : Expr.eval (model m) (Level.assign c.levelParams (c.levelParams.map fun _ => 0)) ρ₀
      (.const falseName []) = model m falseName [] := rfl
  rw [he, hval, (hM m' hm').false_empty hD] at hmem'
  exact SetTheory.not_mem_empty _ hmem'

/-- **The modular corollary, run by run**, from `modular_sees_graph`. -/
theorem no_False_graph (V : Type w) [SetTheory V] {dirs root : String} {r m m' : Name}
    {fs : FS} {d : ModDecoded} {c : CEntryF Name Expr} {v : Expr} {all : List Name}
    (hr : parseModName root = some r)
    (hcl : InClosure (searchPathOf dirs) fs #[r] m)
    (hF : m' = m ∨ Sees (searchPathOf dirs) fs m falseName m')
    (hD : DeclaresFalse (moduleConstants (searchPathOf dirs) fs m'))
    (hv : ViewOf (searchPathOf dirs) fs m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all) (hty : c.type = .const falseName [])
    (hwork : ∀ m', Graph.HdrClosure (searchPathOf dirs) fs [r] m' → ∃ root',
      parseModName root' = some m' ∧ ModelIO.CanGive
        (runArgs ["--olean", "--module", "--search-path=" ++ dirs, "--", root']) fs 0) :
    ¬ ModelIO.CanGive (runArgs ["--check-graph", "--search-path=" ++ dirs, "--", root])
      fs 0 := fun h => by
  obtain ⟨_, hM, hS⟩ := modular_sees_graph V hr h hwork
  exact family_no_False hM hS hcl hF hD hv hmem hk hty

/-- **The modular corollary, in one process**, from `modular_sees_one`. -/
theorem no_False_one (V : Type w) [SetTheory V] {dirs root : String} {r m m' : Name}
    {fs : FS} {d : ModDecoded} {c : CEntryF Name Expr} {v : Expr} {all : List Name}
    (hr : parseModName root = some r)
    (hcl : InClosure (searchPathOf dirs) fs #[r] m)
    (hF : m' = m ∨ Sees (searchPathOf dirs) fs m falseName m')
    (hD : DeclaresFalse (moduleConstants (searchPathOf dirs) fs m'))
    (hv : ViewOf (searchPathOf dirs) fs m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all) (hty : c.type = .const falseName []) :
    ¬ ModelIO.CanGive
      (runArgs ["--olean", "--modular", "--search-path=" ++ dirs, "--", root]) fs 0 := fun h => by
  obtain ⟨_, hM, hS⟩ := modular_sees_one V hr h
  exact family_no_False hM hS hcl hF hD hv hmem hk hty

end ConLeche.Driver.Compose
