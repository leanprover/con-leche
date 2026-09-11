module

import ConLeche.Model.IndRepCons
public import ConLeche.Model.Swap
public section

/-!
# The representation clause across the rule-list swap (task #280)

The modeled route stores its recursors rule-less first and swaps the
checked rule lists in afterwards (`EnvModelM.swapP`).  A representation
reads the environment only through `denoteMeta` and non-recursor
lookups, so it crosses the swap (`IndRep.swap`); a modeled leaf fact
likewise (`ModeledLeaf.swap`).  The clause crosses when every recursor
the swap changed is accounted for by the caller (`IndReps.swap`): the
modeled route's own recursors are its block's members, whose modeled
leaf fact it holds.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V]

theorem DenoteMetaSpine.swap {acval : Name → (Name → Nat) → AnnotTerm} {env₀ env₃ : Env}
    (hcg : ConLeche.SwapCongr env₀ env₃) {ψ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env₀ ψ d as vs → DenoteMetaSpine acval env₃ ψ d as vs
  | _, _, .nil => .nil
  | _, _, .cons ha htl => .cons (by rw [← denoteMeta_swap hcg]; exact ha) (DenoteMetaSpine.swap hcg htl)

theorem FormerData.swap {env₀ env₃ : Env} (hcg : ConLeche.SwapCongr env₀ env₃)
    {m₀ : EnvModel V env₀} {m₃ : EnvModel V env₃} (hac : m₃.acval = m₀.acval)
    {cvT : ConstantVal} {nP : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : FormerData m₀ cvT nP resSort pps) : FormerData m₃ cvT nP resSort pps where
  read ψ := by rw [hac, ← denoteMeta_swap hcg]; exact h.read ψ
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params

theorem CtorDataI.swap {env₀ env₃ : Env} (hcg : ConLeche.SwapCongr env₀ env₃)
    {m₀ : EnvModel V env₀} {m₃ : EnvModel V env₃} (hac : m₃.acval = m₀.acval)
    {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    (h : CtorDataI m₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs) :
    CtorDataI m₃ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs := by
  have hbody : ∀ ψ, ctorBodyAVI m₃ T nP nF ψ (Es ψ) = ctorBodyAVI m₀ T nP nF ψ (Es ψ) := by
    intro ψ; unfold ctorBodyAVI; rw [hac]
  refine ⟨h.resid, fun ψ => ?_, h.len, h.lenE, h.idxLen, fun ψ => ?_, h.bits,
    fun ψ ρ => ?_, h.below, h.belowE, h.params, h.srcLen, h.srcBnd, h.srcIdx, h.srcProp⟩
  · rw [hac, hbody, ← denoteMeta_swap hcg]; exact h.read ψ
  · rw [hac]; exact DenoteMetaSpine.swap hcg (h.idxRead ψ)
  · rw [hbody]; exact h.okTy ψ ρ

theorem FixCtorDataI.swap {env₀ env₃ : Env} (hcg : ConLeche.SwapCongr env₀ env₃)
    {m₀ : EnvModel V env₀} {m₃ : EnvModel V env₃} (hac : m₃.acval = m₀.acval)
    {envP : Env} {T : Name} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : FixCtorDataI m₀ envP T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss) :
    FixCtorDataI m₃ envP T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss :=
  { toCtorDataI := h.toCtorDataI.swap hcg hac
    opened := h.opened
    opens := h.opens
    ksLen := h.ksLen
    xLen := h.xLen
    pLen := h.pLen
    xIdx := h.xIdx
    pIdx := h.pIdx
    idxEq := h.idxEq
    domRead := fun ψ i x hx => by
      rw [hac, ← denoteMeta_swap hcg]; exact h.domRead ψ i x hx
    eissLen := h.eissLen
    eisRead := fun ψ i x hx hk => by
      rw [hac]; exact DenoteMetaSpine.swap hcg (h.eisRead ψ i x hx hk)
    eisLen := h.eisLen
    recEntry := fun ψ i hk hi => by rw [hac]; exact h.recEntry ψ i hk hi
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
      refine ⟨afvs, body, hop, hlenTl, fun k a hka => ?_, ?_⟩
      · rw [hac, ← denoteMeta_swap hcg]; exact hdoms k a hka
      · rw [hac]; exact DenoteMetaSpine.swap hcg hsp
    eisLenRefl := h.eisLenRefl
    reflEntry := fun ψ i hk hi => by rw [hac]; exact h.reflEntry ψ i hk hi }

/-- **A representation crosses the rule-list swap.** -/
theorem IndRep.swap {env₀ env₃ : Env} (hcg : ConLeche.SwapCongr env₀ env₃)
    {m₀ : EnvModel V env₀} {m₃ : EnvModel V env₃} (hac : m₃.acval = m₀.acval)
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {d : IndRepData V}
    (h : IndRep m₀ T cvT cvR mI rP rules d) : IndRep m₃ T cvT cvR mI rP rules d :=
  { strip := h.strip
    isProp := h.isProp
    mI := h.mI
    rP := h.rP
    rules := h.rules
    former := h.former.swap hcg hac
    ctors := fun j cA hj => by
      obtain ⟨hfC, hlps, hD⟩ := h.ctors j cA hj
      exact ⟨hcg.findUp _ _ hfC (fun _ _ _ _ h => nomatch h), hlps, hD.swap hcg hac⟩
    idxRes := fun j cA hj e he =>
      Expr.constsResolve_of_find (fun n hn => by rw [← hcg.isSomeEq]; exact hn) (h.idxRes j cA hj e he)
    uParams := h.uParams
    paramsIff := h.paramsIff
    chains := h.chains
    functor := h.functor
    fibre := h.fibre
    leaf := fun ψ ρ as is h1 h2 => by rw [hac]; exact h.leaf ψ ρ as is h1 h2
    ctor := fun j cA hj ψ ρ as fs h1 h2 => by rw [hac]; exact h.ctor j cA hj ψ ρ as fs h1 h2
    mkZero := h.mkZero
    mkInj := h.mkInj }

theorem ModeledLeaf.swap {env₀ env₃ : Env} (hcg : ConLeche.SwapCongr env₀ env₃)
    {m₀ : EnvModel V env₀} {m₃ : EnvModel V env₃} (hac : m₃.acval = m₀.acval)
    {n : Name} (h : ModeledLeaf m₀ n) : ModeledLeaf m₃ n :=
  ⟨by rw [← hcg.isSomeEq]; exact h.1, fun ψ => by rw [hac]; exact h.2 ψ⟩

/-- **The clause across the swap**: every recursor the swap left alone
keeps its prefix entry; every recursor it changed is the caller's. -/
theorem IndReps.swap {env₀ env₃ : Env} (hcg : ConLeche.SwapCongr env₀ env₃)
    {m₀ : EnvModel V env₀} {m₃ : EnvModel V env₃} (hac : m₃.acval = m₀.acval)
    (h : IndReps m₀)
    (hmod : ∀ (n : Name) (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₃.find? n = some (.recInfo cvR mI rP rules) →
      env₀.find? n = some (.recInfo cvR mI rP rules) ∨ ModeledLeaf m₃ n) :
    IndReps m₃ := by
  intro n cvR mI rP rules hf₃ T hn
  rcases hmod n cvR mI rP rules hf₃ with hf₀ | hmodn
  · rcases h n cvR mI rP rules hf₀ T hn with ⟨cvT, caps, d, hfT, hd⟩ | hml
    · exact Or.inl ⟨cvT, caps, d, hcg.findUp _ _ hfT (fun _ _ _ _ h => nomatch h),
        hd.swap hcg hac⟩
    · exact Or.inr (hml.swap hcg hac)
  · exact Or.inr hmodn

end ConLeche.Model
