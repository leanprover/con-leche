module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecOpenerRead
import ConLeche.Model.Inductives.BlockCallCerts
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Model.Rules.Recompose
import ConLeche.Model.Tiers
import ConLeche.Model.Inductives.BlockRecIdxConv

public section

/-!
# The rule stage's peel obligation at the run

`BlockRuleBodyOwed` (`BlockRuleFit.lean` §10) is what the residue
producer asks of the rule stage: at the contract's telescope and the
peel's outputs, `BlockRuleBodyInputs` at the rule's `ihs`/`Rb0`.  A
producer needs those two function variables PINNED, not returned
existentially by the peel.

§A.9b (`BlockRecData.lean`) pins the peel's outputs to definitions;
this file pins the two function variables the same way
(`blockRuleIhsRunAV`, `blockRuleRbAV`) and produces the obligation's
rows from the run.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. `FieldReadAt` determines its readings -/


/-! ## 1b. Opener lists -/

section Openers

omit [SetTheory V] in
/-- The empty opening list. -/
theorem fvarList_nil : FvarList 0 [] :=
  ⟨rfl, fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ hx => nomatch hx⟩

omit [SetTheory V] in
/-- **An opening EXTENDS an opener list**: opening `n` binders of a
subject scoped at `E`, at depth `E`, prepends the new openers (reversed)
to an `E`-long list. -/
theorem fvarList_of_open {E n : Nat} {L : List Expr} {e : Expr} {fvs : List Expr} {o : Expr}
    (hL : FvarList E L) (hop : ConLeche.openPisAtFvars n e E = some (fvs, o))
    (hw : Expr.WScoped E e) :
    FvarList (E + n) (fvs.reverse ++ L) := by
  have hlen : fvs.length = n := openPisAtFvars_length n hop
  have h := FvarList.openerExtend (r := n) hL
    (fun j x hx => ConLeche.openPisAtFvars_index n e E hop j x hx)
    (fun j x hx => openPisAtFvars_typeWScoped n hop hw j x hx) (by omega)
  rwa [List.take_of_length_le (by omega)] at h

end Openers

/-! ## 1c. Two generic facts: a field's parts past the telescope, and the
opened residue -/


/-! ## 1d. The constant-scoping kit

`ConstsBound` through the five term operations the rule stage's
frame is built from: lifting, the lifting instantiation, spines, the
two Π-instantiations and the `ih` tower — and through the abstraction
itself, from the recursors' environment down to the constructors'. -/

section ConstsKit

variable {env : Env}

omit [SetTheory V] in
theorem constsBound_instPisAt :
    ∀ (sp : List Expr) {e : Expr} {ds : List Expr} {r : Expr},
      Expr.instPisAt sp e = some (ds, r) →
      ConstsBound env e → (∀ a ∈ sp, ConstsBound env a) → ConstsBound env r
  | [], e, ds, r, h, he, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ he
  | a :: sp, e, ds, r, h, he, hsp => by
    match e, h with
    | .forallE _ body _, h =>
      simp only [Expr.instPisAt, Option.map_eq_some_iff] at h
      obtain ⟨⟨ds', r'⟩, h', heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      rw [constsBound_forallE] at he
      exact constsBound_instPisAt sp h'
        (ConstsBound.instantiate1 (hsp a List.mem_cons_self) body 0 he.2)
        (fun x hx => hsp x (List.mem_cons_of_mem _ hx))

omit [SetTheory V] in
/-- The recursors' bare environment finds only the recursors' names and
what the constructors' environment finds. -/
theorem find?_consBlockRecsBare_isSome {p : ConLeche.BlockShape} :
    ∀ (m : Nat) (cvRas : List (ConstantVal × Nat)) (env₀ : Env) (n : Name),
      ((ConLeche.consBlockRecsBare p m cvRas env₀).find? n).isSome = true →
      n ∈ cvRas.map (·.1.name) ∨ (env₀.find? n).isSome = true
  | _, [], _, _, h => Or.inr h
  | m, (cvRa, nIdx) :: rest, env₀, n, h => by
    rw [ConLeche.consBlockRecsBare] at h
    rcases find?_consBlockRecsBare_isSome (m + 1) rest _ n h with h' | h'
    · exact Or.inl (List.mem_cons_of_mem _ h')
    · rw [ConLeche.Env.find?_cons] at h'
      split at h'
      · rename_i heq
        exact Or.inl (by simp only [List.map_cons, List.mem_cons]; exact Or.inl heq.symm)
      · exact Or.inr h'

end ConstsKit

/-! ## 2. `ihs`, as a function of the run -/


/-! ## 3. `BlockRuleBodyInputs` at the run -/

section BodyRun

open ConLeche (BlockParts BlockFieldKind)

variable {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **Bit validity from a grading** — the `AnnotValid` twin of
`fieldsOkB_zero_of_spineGrading`: a binder list each of whose entries is
valid under every spine fitting the entries before it is hereditarily
valid. -/
theorem fieldsValid_of_grading :
    ∀ (L : List AnnotTerm) {σ : Nat → V},
      (∀ l, l < L.length → ∀ ys : List V,
        SpineFit σ (L.take l) ys → AnnotValid V (consList ys σ) (L.getD l default)) →
      FieldsValid σ L
  | [], _, _ => trivial
  | F :: Fs, σ, hok => by
    refine ⟨?_, fun a ha => ?_⟩
    · simpa using hok 0 (by simp) [] trivial
    · refine fieldsValid_of_grading Fs (fun l hl ys hys => ?_)
      have hstep : SpineFit σ ((F :: Fs).take (l + 1)) (a :: ys) := ⟨ha, hys⟩
      have hq := hok (l + 1) (by simp only [List.length_cons]; omega) (a :: ys) hstep
      simpa using hq

end BodyRun

end ConLeche.Model
