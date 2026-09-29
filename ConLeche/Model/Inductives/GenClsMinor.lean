module

public import ConLeche.Model.Inductives.GenClsSem
public import ConLeche.Model.Inductives.GenRecRules
public import ConLeche.Verify.Inductives.GenDepth
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.ClassGenMinor
import ConLeche.Model.Inductives.GenRuleSyn
import ConLeche.Model.Inductives.GenRuleFree
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Verify.Subst
import ConLeche.Verify.Inductives.NestCallSyn

public section

/-!
# The minor premise at the rule frame (lane GENREC-CLS)

`GenPreSem.minor`: the minor premise's typing at the rule frame.  The
minor premise of recursor `c`'s `j`-th constructor sits in the shared
prefix at its slot `mp = nP + s`, its type the generator's
`ClassGen.minorTy` built at `mp`.  That term does not depend on the depth
it is built at (`ClassGen.minorTy_depth`), so it IS the one built at the
rule prefix `rP`, whose pieces are the rule frame's: the constructor's
declared fields opened at `rP` (`tgtFieldFvs`), one inductive hypothesis
type per recursive field (the same term at every depth,
`ClassGen.ihTy_depth`, so the one the generated rule's `ih` is built
over), and the conclusion `motive_c e⃗ (C ds f⃗)` over the declared
result (`tgtCbody`).  Read at `rP` (a lift of its reading at `mp`) it is
the Π-tower of the rule frame's field domains, the `ih` domains
`genIhDomAV`, and the motive at `tgtEsAV`/`tgtMkAV`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassGenScoped RecShape NestState BinderMeta
  closeTelescope)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## A closed telescope, read -/

/-- **A closed telescope, read at its own depth**: a Π-tower whose binder
data are the pieces' readings (each at its own depth, the bit its binder
datum's) over the body's reading. -/
theorem denoteMeta_closeTelescope_read {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} :
    ∀ (nds : List (Expr × BinderMeta)) (d : Nat) (body Y : Expr) {A : AnnotTerm},
      (∀ p ∈ nds, p.1.looseBVarsBounded 0 = true) → body.looseBVarsBounded 0 = true →
      Expr.ErasedEq Y (closeTelescope nds d body) →
      denoteMeta acval env φ d Y = some A →
      ∃ (bs : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm), A = mkPisAV bs b ∧
        bs.length = nds.length ∧
        (∀ (k : Nat) (nd : Expr × BinderMeta), nds[k]? = some nd → ∃ a,
          bs[k]? = some (0, pwBit φ nd.2.pw, a) ∧ denoteMeta acval env φ (d + k) nd.1 = some a) ∧
        denoteMeta acval env φ (d + nds.length) body = some b
  | [], d, body, Y, A, _, _, hY, hA => by
    refine ⟨[], A, rfl, rfl, fun k nd h => by simp at h, ?_⟩
    rw [← hA, List.length_nil, Nat.add_zero, denoteMeta_erasedEq hY]
    rfl
  | (dom, bm) :: nds, d, body, Y, A, hcl, hb, hY, hA => by
    cases Y with
    | forallE a b bm' =>
      simp only [closeTelescope] at hY
      obtain ⟨hbm, ha, hbE⟩ := hY
      have hcl' : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true :=
        fun p hp => hcl p (List.mem_cons_of_mem _ hp)
      have hC := closeTelescope_bounded nds (d + 1) body hcl' hb
      have hE : Expr.ErasedEq (b.instantiate1 (.fvar d a)) (closeTelescope nds (d + 1) body) :=
        Expr.ErasedEq.trans (Expr.ErasedEq.instantiate1 hbE (v' := .fvar d dom) rfl)
          (erasedEq_abstract1_instantiate1 _ 0 hC)
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hA
      obtain ⟨bs, b0, rfl, hbl, hbs, hb0⟩ :=
        denoteMeta_closeTelescope_read nds (d + 1) body _ hcl' hb hE hba
      refine ⟨(0, pwBit φ bm'.pw, ta) :: bs, b0, rfl, by simp [hbl], fun k nd hk => ?_, ?_⟩
      · cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          refine ⟨ta, by rw [hbm]; rfl, ?_⟩
          rw [Nat.add_zero, ← denoteMeta_erasedEq ha]; exact hta
        | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          obtain ⟨a', ha', hr⟩ := hbs k nd hk
          exact ⟨a', by simpa using ha', by rw [show d + (k + 1) = d + 1 + k by omega]; exact hr⟩
      · rw [List.length_cons, show d + (nds.length + 1) = d + 1 + nds.length by omega]
        exact hb0
    | _ => simp [closeTelescope, Expr.ErasedEq] at hY

end ConLeche.Model
