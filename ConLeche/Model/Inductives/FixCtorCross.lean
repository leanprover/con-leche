module

import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Inductives.FixRuleData
public section

/-!
# The recursive constructor data across a cons (task #188)

`FixCtorDataI` (`FixDataP.lean`) crosses a cons whose head is not
the block's former: the sum data cross as before
(`CtorDataI.cross`), the opened variables' types are bounded at the
constructor's environment (`openPisAtFvars_constsBound`), so their
readings and their index-argument spines cross too, and the
recursive entries mention the former only.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- **The recursive constructor data cross a cons** whose head is not
the block's former. -/
theorem BlockCtorDataI.cross {m : EnvModel V env} {env₀ : Env} {T : Name}
    {Tof : Nat → Name} {nIdxOf : Nat → Nat} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : BlockCtorDataI m env₀ T Tof nIdxOf lps cvC nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name) (hTof : ∀ i, Tof i ≠ c₀.name)
    (hat : ∀ e : Expr, ConsCrossAt c₀ e) (hcb : ConstsBound env cvC.type)
    (hcbI : ∀ e ∈ idxArgs, ConstsBound env e)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    BlockCtorDataI m₂ env₀ T Tof nIdxOf lps cvC nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss := by
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
    opened := h.opened
    opens := h.opens
    ksLen := h.ksLen
    xLen := h.xLen
    pLen := h.pLen
    xIdx := h.xIdx
    pIdx := h.pIdx
    idxEq := h.idxEq
    domRead := fun ψ i x hx => by
      rw [hac]
      exact denoteMeta_cons_mono hfresh (hat _) ψ (nP + i) (hxcb i x hx) (h.domRead ψ i x hx)
    eissLen := h.eissLen
    eisRead := fun ψ i x hx hk => by
      rw [hac]
      exact DenoteMetaSpine.cons_mono hfresh hat
        (fun a ha => constsBound_getAppArgs _ (hxcb i x hx) a (List.mem_of_mem_drop ha))
        (h.eisRead ψ i x hx hk)
    eisLen := h.eisLen
    recEntry := fun ψ i hk hi => by
      rw [hac, acvalWith_ne (hTof i)]
      exact h.recEntry ψ i hk hi
    eissParams := h.eissParams
    eissBelow := h.eissBelow
    ordNone := h.ordNone
    tssLen := h.tssLen
    tssNone := h.tssNone
    tssBits := h.tssBits
    tssPiBits := h.tssPiBits
    tssBelow := h.tssBelow
    tssParams := h.tssParams
    reflOpen := fun ψ i x hx hk => by
      obtain ⟨afvs, body, hop, hlenTl, hdoms, hsp⟩ := h.reflOpen ψ i x hx hk
      obtain ⟨hafvs, hbody⟩ := openPisAtFvars_constsBound _ (hxcb i x hx) hop
      refine ⟨afvs, body, hop, hlenTl, fun k a hka => ?_, ?_⟩
      · rw [hac]
        refine denoteMeta_cons_mono hfresh (hat _) ψ (nP + i + k) ?_ (hdoms k a hka)
        have hb := hafvs a (List.mem_of_getElem? hka)
        obtain ⟨ty, hy⟩ := (opening_vars_at hop).2.1 k a hka
        rw [hy, constsBound_fvar] at hb
        rw [hy]
        exact hb
      · rw [hac]
        exact DenoteMetaSpine.cons_mono hfresh hat
          (fun a ha => constsBound_getAppArgs _ hbody a (List.mem_of_mem_drop ha)) hsp
    eisLenRefl := h.eisLenRefl
    reflEntry := fun ψ i hk hi => by
      rw [hac, acvalWith_ne (hTof i)]
      exact h.reflEntry ψ i hk hi }

end ConLeche.Model
