module

import ConLeche.Model.IndRepCons
public import ConLeche.Model.Swap
public section

/-!
# The representation clause across the rule-list swap (task #280)

The mutual route stores its recursors rule-less first and swaps the
checked rule lists in afterwards (`EnvModelM.swapP`).  A representation
of the block BEING STORED reads the environment only through
`denoteMeta` and non-recursor lookups, so it crosses the swap
(`IndRep.swap`) once the caller supplies every member's recursor at the
target (`RecReadAt`, the install's own readings); a modeled leaf fact
likewise (`ModeledLeaf.swap`).  A PREFIX block's representation does
not cross the swap: since task #279 M-B′ the clause names every sibling
recursor's entry, and at the provisioned environment a sibling cannot
be told apart from a provisioned recursor of the new block — prefix
clauses cross the store as an extension of the constructors'
environment instead (`IndReps.ext`, `Model/IndRepExt.lean`).
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
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {lvls : (Name → Nat) → List Nat}
    (h : FormerData m₀ cvT nP resSort pps lvls) : FormerData m₃ cvT nP resSort pps lvls where
  read ψ := by rw [hac, ← denoteMeta_swap hcg]; exact h.read ψ
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params
  lvlsLen := h.lvlsLen
  lvl := h.lvl
  lvlsParams := h.lvlsParams

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
    {tgtOf : Nat → Name} {nIdxOf : Nat → Nat}
    (h : FixCtorDataI m₀ envP T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss tgtOf nIdxOf) :
    FixCtorDataI m₃ envP T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss tgtOf nIdxOf :=
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
    {mm : Nat}
    (h : IndRep m₀ T cvT cvR mI rP rules d mm)
    -- every member's recursor at the target (task #279 M-A′/M-B′): the
    -- install's own readings — the swap is only ever applied to a
    -- recursor of the block being stored, whose siblings the swap
    -- changed too (a prefix block's clause crosses the store as an
    -- EXTENSION of the constructors' environment instead, `IndRep.ext`)
    (hrr : d.nP ≠ 0 → rules ≠ [] → env₃.find? cvR.name = some (.recInfo cvR mI rP rules) →
      ∀ t, t < d.k → RecReadAt m₃ d cvT.levelParams t) :
    IndRep m₃ T cvT cvR mI rP rules d mm :=
  { member := h.member
    strip := h.strip
    isProp := h.isProp
    rulesRead := hrr
    mI := h.mI
    rP := h.rP
    rules := h.rules
    kRealLe := h.kRealLe
    memReal := h.memReal
    recName := h.recName
    recNamesReal := h.recNamesReal
    tgtsRLt := h.tgtsRLt
    membersFound := fun t ht => by
      obtain ⟨cv, caps, hf⟩ := h.membersFound t ht
      exact ⟨cv, caps, hcg.findUp _ _ hf (fun _ _ _ _ h => nomatch h)⟩
    membersLps := fun t ht cv caps hf => by
      obtain ⟨cv', caps', hf'⟩ := h.membersFound t ht
      rw [hcg.findUp _ _ hf' (fun _ _ _ _ h => nomatch h)] at hf
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
      exact h.membersLps t ht _ _ hf'
    memberNodup := h.memberNodup
    memsReal := h.memsReal
    ctorsCFound := fun cC hcC => by rw [← hcg.isSomeEq]; exact h.ctorsCFound cC hcC
    pinsReal := h.pinsReal
    recRead := fun hnP ψ => by
      rw [hac, ← denoteMeta_swap hcg, h.recRead hnP ψ]
      congr 2
      exact d.recDataAV_congr (fun _ _ => by rw [hac]) (fun _ _ => by rw [hac])
    former := h.former.swap hcg hac
    formersRead := fun t ht cv caps hf => by
      obtain ⟨cv0, caps0, hf0⟩ := h.membersFound t (Nat.lt_of_lt_of_le ht h.kRealLe)
      rw [hcg.findUp _ _ hf0 (fun _ _ _ _ hh => nomatch hh)] at hf
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
      exact (h.formersRead t ht cv0 caps0 hf0).swap hcg hac
    ctors := fun j cA hj => by
      obtain ⟨hfC, hlps, hD⟩ := h.ctors j cA hj
      exact ⟨hcg.findUp _ _ hfC (fun _ _ _ _ h => nomatch h), hlps, hD.swap hcg hac⟩
    memsFound := fun j hj => by
      obtain ⟨⟨cv, cps, hfm⟩, htg⟩ := h.memsFound j hj
      refine ⟨⟨cv, cps, hcg.findUp _ _ hfm (fun _ _ _ _ h => nomatch h)⟩, fun i => ?_⟩
      obtain ⟨cv', cps', hf'⟩ := htg i
      exact ⟨cv', cps', hcg.findUp _ _ hf' (fun _ _ _ _ h => nomatch h)⟩
    idxRes := fun j cA hj e he =>
      Expr.constsResolve_of_find (fun n hn => by rw [← hcg.isSomeEq]; exact hn) (h.idxRes j cA hj e he)
    uParams := h.uParams
    paramsIff := h.paramsIff
    chains := h.chains
    functor := h.functor
    fibre := h.fibre
    leaf := fun ψ ρ as is h1 h2 => by rw [hac]; exact h.leaf ψ ρ as is h1 h2
    tupMem := h.tupMem
    ctor := fun j cA hj ψ ρ as fs h1 h2 => by rw [hac]; exact h.ctor j cA hj ψ ρ as fs h1 h2
    mkZero := h.mkZero
    mkInj := h.mkInj }

theorem ModeledLeaf.swap {env₀ env₃ : Env} (hcg : ConLeche.SwapCongr env₀ env₃)
    {m₀ : EnvModel V env₀} {m₃ : EnvModel V env₃} (hac : m₃.acval = m₀.acval)
    {n : Name} (h : ModeledLeaf m₀ n) : ModeledLeaf m₃ n :=
  ⟨by rw [← hcg.isSomeEq]; exact h.1, fun ψ => by rw [hac]; exact h.2 ψ⟩

end ConLeche.Model
