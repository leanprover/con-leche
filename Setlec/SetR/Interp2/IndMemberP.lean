import Setlec.SetR.Interp2.IndConsP
import Setlec.SetR.Annot.BitRename
import Setlec.SetR.Install.IndMembersS

/-!
# The block member's key, P tier (task #161, IND TIER)

`memberKeyS` (`Install/IndMembersS.lean`) is v1's; this is its
transpose, and it is the same short argument for the same reason:

> the member's leaf is *given* — it takes its model artifact's — so
> the invariant's own `mem_typeP`/`type_okP` at the stored `_model`
> constant supply the membership and the grading outright.  All that
> is left is that the member's type and the model's type **read the
> same**.

The two blindnesses that close that gap are `Annot/BitRename.lean`'s
(`denoteP_renameConsts_resolve` and `denoteP_erasedEq`), transposed
there for this consumer.

**What is V-free is reused, not re-proved** (ENDGAME D's §3 lesson).
The block renaming's `hup` clause — every stored constant's model is
stored with the same level parameters — is `BlockInstalledTT`'s, a
predicate about the environment and the *v1* valuation, already
carried by the v1 fold that rides beside this one.  Only its last
conjunct is about a valuation leaf, and `acval_erase` fixes leaves
only up to numerals (H's §1 finding, in the same shape once more), so
exactly that conjunct gets a P twin: `BlockAcvalInstalled`.  It is one
line, it is what the member cons establishes by construction (the
leaf it stores *is* `acval (n ++ "_model")`), and it is the only new
predicate the member fold needs.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-- **The annotated half of `BlockInstalledTT`**: an installed block
member's *leaf* is its model's.  The other three conjuncts of
`BlockInstalledTT` are V-free environment facts and are consumed from
the v1 predicate directly. -/
def BlockAcvalInstalled (blockNames : List Name) (env : Env)
    (acval : Name → (Name → Nat) → AVExpr) : Prop :=
  ∀ n, blockNames.contains n = true → ∀ ci : ConstantInfo,
    env.find? n = some ci →
    ∀ ψ : Name → Nat, acval (n.str "_model") ψ = acval n ψ

/-- The P invariant's three type facts at a *stored* constant, keyed
by `find?` rather than by membership (`EnvS.cval_memType`'s
transpose). -/
theorem EnvS2PM.acval_memTypeP (mp : EnvS2PM V μ env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (ψ : Name → Nat) :
    ∃ ta, denoteP mp.base2.acval env ψ 0 ci.toConstantVal.type
        = some ta ∧
      (∀ ρ : Nat → V, AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp2 V ρ (mp.base2.acval n ψ) ∈ˢ interp2 V ρ ta := by
  obtain ⟨ta, hta⟩ := mp.type_reads ci (Env.find?_mem hf) ψ
  refine ⟨ta, hta, mp.type_okP ci (Env.find?_mem hf) ψ ta hta, ?_⟩
  intro ρ
  have := mp.mem_typeP ci (Env.find?_mem hf) ψ ta hta ρ
  rwa [Env.find?_name hf] at this

/-- **The block member's key, P tier.**  The model artifact's leaf
inhabits the checked member's type's reading, graded, at every
assignment. -/
theorem memberKeyP (mp : EnvS2PM V μ env) {blockNames : List Name}
    {cv cvA : ConstantVal}
    (hmv : MemberValR μ F env mp.base2.base.cval blockNames cv cvA)
    (hIB : BlockInstalledTT blockNames env mp.base2.base.cval)
    (hIA : BlockAcvalInstalled blockNames env mp.base2.acval)
    (ψ : Name → Nat) :
    ∃ ta, denoteP mp.base2.acval env ψ 0 cvA.type = some ta ∧
      (∀ ρ : Nat → V, AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp2 V ρ (mp.base2.acval (cvA.name.str "_model") ψ)
          ∈ˢ interp2 V ρ ta := by
  obtain ⟨type', hcv, rfl, -, cvm, mval, hint, hfm, hlpm, hren⟩ := hmv
  obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := hcv
  -- the renaming's two `RenameOkT` clauses, at a member environment
  have hup : ∀ n ci, env.find? n = some ci →
      ∃ ci', env.find? ((fun n =>
          if blockNames.contains n then n.str "_model" else n) n)
        = some ci' ∧
        ci'.toConstantVal.levelParams
          = ci.toConstantVal.levelParams := by
    intro n ci hfn
    dsimp only
    by_cases hb : blockNames.contains n = true
    · obtain ⟨cvm', mval', hint', hfm', hlp', -, -⟩ := hIB n hb ci hfn
      exact ⟨.defnInfo cvm' mval' hint', by rw [if_pos hb]; exact hfm',
        hlp'⟩
    · exact ⟨ci, by rw [if_neg hb]; exact hfn, rfl⟩
  have hval : ∀ (n : Name) (ci : ConstantInfo),
      env.find? n = some ci → ∀ ψ' : Name → Nat,
      mp.base2.acval ((fun n =>
        if blockNames.contains n then n.str "_model" else n) n) ψ'
        = mp.base2.acval n ψ' := by
    intro n ci hfn ψ'
    dsimp only
    by_cases hb : blockNames.contains n = true
    · rw [if_pos hb]; exact hIA n hb ci hfn ψ'
    · rw [if_neg hb]
  -- the model constant's own facts, and the two types read the same
  obtain ⟨ta, hta, hokta, hmem⟩ :=
    mp.acval_memTypeP (n := cv.name.str "_model") hfm ψ
  refine ⟨ta, ?_, hokta, hmem⟩
  show denoteP mp.base2.acval env ψ 0 type' = some ta
  rw [← hta]
  show denoteP mp.base2.acval env ψ 0 type'
    = denoteP mp.base2.acval env ψ 0 cvm.type
  rw [← denoteP_erasedEq (Expr.ErasedEq.of_eqUpToNames hren) 0]
  exact (denoteP_renameConsts_resolve hup hval type' 0 htr).symm

end Setlec.SetR.Interp2
