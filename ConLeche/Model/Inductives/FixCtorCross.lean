module

import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Inductives.FixRuleData
public section

/-!
# The recursive constructor data across a cons (task #188)

`BlockCtorDataI` (`BlockData.lean`) crosses a cons whose head is not
the member's former: the sum data cross as before (`CtorDataI.cross`),
and the opened variables' types are bounded at the constructor's
environment (`openPisAtFvars_constsBound`), so their readings cross
too.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- **The block constructor data cross a cons** whose head is not the
member's former. -/
theorem BlockCtorDataI.cross {m : EnvModel V env} {T : Name} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr}
    (h : BlockCtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs
      fvsP xFvs xrest)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hat : ∀ e : Expr, ConsCrossAt c₀ e) (hcb : ConstsBound env cvC.type)
    (hcbI : ∀ e ∈ idxArgs, ConstsBound env e)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    BlockCtorDataI m₂ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs
      fvsP xFvs xrest := by
  have hbase := h.toCtorDataI.cross hfresh hT hat hcb hcbI m₂ hac
  -- the opened variables' types are bounded
  obtain ⟨crest, hopP, hopX⟩ := h.opens
  have hopAll : openPisAtFvars (nP + nF) cvC.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hfvs, -⟩ := openPisAtFvars_constsBound (nP + nF) hcb hopAll
  have hxcb : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x → ConstsBound env x.fvarTypeD := by
    intro i x hx
    have hb := hfvs x (List.mem_append_right _ (List.mem_of_getElem? hx))
    obtain ⟨ty, rfl⟩ := h.xIdx i x hx
    rw [constsBound_fvar] at hb
    exact hb
  exact {
    toCtorDataI := hbase
    opens := h.opens
    xLen := h.xLen
    pLen := h.pLen
    xIdx := h.xIdx
    pIdx := h.pIdx
    idxEq := h.idxEq
    domRead := fun ψ i x hx => by
      rw [hac]
      exact denoteMeta_cons_mono hfresh (hat _) ψ (nP + i) (hxcb i x hx) (h.domRead ψ i x hx)
    resShape := h.resShape }

end ConLeche.Model
