module

public import ConLeche.Model.IndRep
public import ConLeche.Model.Annot.ConsMono
import ConLeche.Model.Inductives.StructBits
import ConLeche.Semantics.EnvFacts
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Inductives.FixRec
import ConLeche.Verify.ProjSlots
public section

/-!
# The representation clause across a fresh cons (task #280)

`IndReps` (`ConLeche/Model/IndRep.lean`) is a field of `EnvModelM`, so
every cons step owes it at the extension.  This module supplies the
transport: a representation of a stored block crosses any fresh cons
(`IndRep.cross` — the readings by `denoteMeta_cons_mono`, the leaves by
`acvalWith_ne`, the semantic laws untouched since they mention no
carrier), a modeled block's leaf fact crosses likewise
(`ModeledLeaf.cross`), and the clause at the extension follows from the
clause at the prefix plus the **head's obligation** (`IndRepsHead`):
a fresh inductive has no recursor stored yet, and a fresh recursor of a
stored inductive claims the block's representation itself.  Every
value-kind cons discharges the obligation by kind (`IndRepsHead.ofNtc`),
so the harvests pay nothing; the inductive installs supply the claim.

A table head (`projInfo`) is the one head whose slots a reading could
mention; the crossing there needs the opened pieces of the
constructors' types to carry no such slot, which follows from the
stored type carrying none (`ConsCrossEnv`) by `NoProjAt.openPisAtFvars`.
The `FixCtorDataI.cross` of the fixpoint route takes that fact for
EVERY expression, which only a non-table head has; `crossAt` below
takes it for the constructor's type alone.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Projection-freeness through openings -/

omit [SetTheory V] in
/-- An opening's variables and residual carry no projection node of a
structure when the opened term carries none. -/
theorem Expr.NoProjAt.openPisAtFvars {T : Name} {i : Nat} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      ConLeche.openPisAtFvars n e d = some (fvs, o) → Expr.NoProjAt T i e →
      (∀ x ∈ fvs, Expr.NoProjAt T i x) ∧ Expr.NoProjAt T i o
  | 0, e, d, fvs, o, hop, he => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun x hx => nomatch hx), he⟩
  | n + 1, e, d, fvs, o, hop, he => by
    match e, he, hop with
    | .forallE dom bd mb, he, hop =>
      simp only [ConLeche.openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        rw [Expr.noProjAt_forallE] at he
        have hfv : Expr.NoProjAt T i (Expr.fvar d dom) := Expr.noProjAt_fvar.mpr he.1
        obtain ⟨hfvs, ho⟩ :=
          Expr.NoProjAt.openPisAtFvars n h₁ (Expr.NoProjAt.instantiate1 hfv bd 0 he.2)
        refine ⟨fun x hx => ?_, ho⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hfv
        · exact hfvs x hx
      · exact nomatch hop

omit [SetTheory V] in
theorem ConsCrossAt.openPisAtFvars {c₀ : ConstantInfo} {n : Nat} {e : Expr} {d : Nat}
    {fvs : List Expr} {o : Expr} (hop : ConLeche.openPisAtFvars n e d = some (fvs, o))
    (h : ConsCrossAt c₀ e) :
    (∀ x ∈ fvs, ConsCrossAt c₀ x) ∧ ConsCrossAt c₀ o :=
  ⟨fun x hx tbl heq i => (Expr.NoProjAt.openPisAtFvars n hop (h tbl heq i)).1 x hx,
   fun tbl heq i => (Expr.NoProjAt.openPisAtFvars n hop (h tbl heq i)).2⟩

omit [SetTheory V] in
theorem ConsCrossAt.getAppArgs {c₀ : ConstantInfo} {e : Expr} (h : ConsCrossAt c₀ e) :
    ∀ a ∈ e.getAppArgs, ConsCrossAt c₀ a :=
  fun a ha tbl heq i => Expr.NoProjAt.getAppArgs (h tbl heq i) a ha

omit [SetTheory V] in
theorem ConsCrossAt.fvarTypeD {c₀ : ConstantInfo} {j : Nat} {ty : Expr}
    (h : ConsCrossAt c₀ (.fvar j ty)) : ConsCrossAt c₀ (Expr.fvar j ty).fvarTypeD :=
  fun tbl heq i => Expr.noProjAt_fvar.mp (h tbl heq i)

/-! ## The constructor data across any fresh cons -/

/-- `CtorDataI.cross` with the crossing fact at the constructor's type
alone (a table head): the residual's index arguments are opened
subterms of the type. -/
theorem CtorDataI.crossAt {m : EnvModel V env} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    (h : CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hat : ConsCrossAt c₀ cvC.type) (hcb : ConstsBound env cvC.type)
    (hatI : ∀ e ∈ idxArgs, ConsCrossAt c₀ e)
    (hcbI : ∀ e ∈ idxArgs, ConstsBound env e)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    CtorDataI m₂ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs := by
  have hbody : ∀ ψ, ctorBodyAVI m₂ T nP nF ψ (Es ψ) = ctorBodyAVI m T nP nF ψ (Es ψ) := by
    intro ψ
    unfold ctorBodyAVI
    rw [hac, acvalWith_ne hT]
  have hspine : ∀ {ψ : Name → Nat} {d : Nat} {as : List Expr} {vs : List AnnotTerm},
      (∀ a ∈ as, ConsCrossAt c₀ a) → (∀ a ∈ as, ConstsBound env a) →
      DenoteMetaSpine m.acval env ψ d as vs →
      DenoteMetaSpine (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d as vs := by
    intro ψ d as vs hat' hcb' hs
    induction hs with
    | nil => exact .nil
    | @cons a as' v vs' ha htl ih =>
      exact .cons (denoteMeta_cons_mono hfresh (hat' a List.mem_cons_self) ψ d
          (hcb' a List.mem_cons_self) ha)
        (ih (fun a' ha' => hat' a' (List.mem_cons_of_mem _ ha'))
          (fun a' ha' => hcb' a' (List.mem_cons_of_mem _ ha')))
  refine ⟨h.resid, fun ψ => ?_, h.len, h.lenE, h.idxLen, fun ψ => ?_, h.bits,
    fun ψ ρ => ?_, h.below, h.belowE, h.params, h.srcLen, h.srcBnd, h.srcIdx, h.srcProp⟩
  · rw [hac, hbody]
    exact denoteMeta_cons_mono hfresh hat ψ 0 hcb (h.read ψ)
  · rw [hac]
    exact hspine hatI hcbI (h.idxRead ψ)
  · rw [hbody]; exact h.okTy ψ ρ

/-- **The recursive constructor data cross any fresh cons** whose head
is not the block's former — `FixCtorDataI.cross` with the crossing
fact at the constructor's type alone: every piece the data reads (the
opened field domains, the residual's index arguments, a reflexive
field's opened telescope and body) is an opened subterm of the type. -/
theorem FixCtorDataI.crossAt {m : EnvModel V env} {env₀ : Env} {T : Name} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {tgtOf : Nat → Name} {nIdxOf : Nat → Nat}
    (h : FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss tgtOf nIdxOf)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hTgt : ∀ i, tgtOf i ≠ c₀.name)
    (hat : ConsCrossAt c₀ cvC.type) (hcb : ConstsBound env cvC.type)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    FixCtorDataI m₂ env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss tgtOf nIdxOf := by
  -- the opened variables' types are bounded and slot-free
  obtain ⟨crest, hopP, hopX⟩ := h.opens
  have hopAll : ConLeche.openPisAtFvars (nP + nF) cvC.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hfvs, hrest⟩ := openPisAtFvars_constsBound (nP + nF) hcb hopAll
  obtain ⟨hfvsAt, hrestAt⟩ := ConsCrossAt.openPisAtFvars hopAll hat
  have hxcb : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x → ConstsBound env x.fvarTypeD := by
    intro i x hx
    have hb := hfvs x (List.mem_append_right _ (List.mem_of_getElem? hx))
    obtain ⟨ty, rfl⟩ := h.xIdx i x hx
    rw [constsBound_fvar] at hb
    exact hb
  have hxat : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x → ConsCrossAt c₀ x.fvarTypeD := by
    intro i x hx
    have hb := hfvsAt x (List.mem_append_right _ (List.mem_of_getElem? hx))
    obtain ⟨ty, rfl⟩ := h.xIdx i x hx
    exact ConsCrossAt.fvarTypeD hb
  have hcbI : ∀ e ∈ idxArgs, ConstsBound env e := by
    intro e he
    rw [h.idxEq] at he
    exact constsBound_getAppArgs _ hrest e (List.mem_of_mem_drop he)
  have hatI : ∀ e ∈ idxArgs, ConsCrossAt c₀ e := by
    intro e he
    rw [h.idxEq] at he
    exact ConsCrossAt.getAppArgs hrestAt e (List.mem_of_mem_drop he)
  have hspine : ∀ {ψ : Name → Nat} {d : Nat} {as : List Expr} {vs : List AnnotTerm},
      (∀ a ∈ as, ConsCrossAt c₀ a) → (∀ a ∈ as, ConstsBound env a) →
      DenoteMetaSpine m.acval env ψ d as vs →
      DenoteMetaSpine (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d as vs := by
    intro ψ d as vs hat' hcb' hs
    induction hs with
    | nil => exact .nil
    | @cons a as' v vs' ha htl ih =>
      exact .cons (denoteMeta_cons_mono hfresh (hat' a List.mem_cons_self) ψ d
          (hcb' a List.mem_cons_self) ha)
        (ih (fun a' ha' => hat' a' (List.mem_cons_of_mem _ ha'))
          (fun a' ha' => hcb' a' (List.mem_cons_of_mem _ ha')))
  have hbase := h.toCtorDataI.crossAt hfresh hT hat hcb hatI hcbI m₂ hac
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
      exact denoteMeta_cons_mono hfresh (hxat i x hx) ψ (nP + i) (hxcb i x hx) (h.domRead ψ i x hx)
    eissLen := h.eissLen
    eisRead := fun ψ i x hx hk => by
      rw [hac]
      exact hspine
        (fun a ha => ConsCrossAt.getAppArgs (hxat i x hx) a (List.mem_of_mem_drop ha))
        (fun a ha => constsBound_getAppArgs _ (hxcb i x hx) a (List.mem_of_mem_drop ha))
        (h.eisRead ψ i x hx hk)
    eisLen := h.eisLen
    recEntry := fun ψ i hk hi => by
      rw [hac, acvalWith_ne (hTgt i)]
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
      obtain ⟨hafvsAt, hbodyAt⟩ := ConsCrossAt.openPisAtFvars hop (hxat i x hx)
      refine ⟨afvs, body, hop, hlenTl, fun k a hka => ?_, ?_⟩
      · rw [hac]
        have hb := hafvs a (List.mem_of_getElem? hka)
        have hbAt := hafvsAt a (List.mem_of_getElem? hka)
        obtain ⟨ty, hy⟩ := ConLeche.openPisAtFvars_index _ _ _ hop k a hka
        rw [hy, constsBound_fvar] at hb
        rw [hy] at hbAt
        rw [hy]
        exact denoteMeta_cons_mono hfresh (ConsCrossAt.fvarTypeD hbAt) ψ (nP + i + k) hb
          (by rw [← hy]; exact hdoms k a hka)
      · rw [hac]
        exact hspine
          (fun a ha => ConsCrossAt.getAppArgs hbodyAt a (List.mem_of_mem_drop ha))
          (fun a ha => constsBound_getAppArgs _ hbody a (List.mem_of_mem_drop ha)) hsp
    eisLenRefl := h.eisLenRefl
    reflEntry := fun ψ i hk hi => by
      rw [hac, acvalWith_ne (hTgt i)]
      exact h.reflEntry ψ i hk hi }

/-! ## The representation across a fresh cons -/

/-- The former's data cross a fresh cons (`FormerData.cross` of
`StructData`, restated here below it). -/
theorem FormerData.crossAt {m : EnvModel V env} {cvT : ConstantVal}
    {nP : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {lvls : (Name → Nat) → List Nat}
    (h : FormerData m cvT nP resSort pps lvls)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hat : ConsCrossAt c₀ cvT.type)
    (hcb : ConstsBound env cvT.type)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    FormerData m₂ cvT nP resSort pps lvls where
  read ψ := by
    rw [hac]
    exact denoteMeta_cons_mono hfresh hat ψ 0 hcb (h.read ψ)
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params
  lvlsLen := h.lvlsLen
  lvl := h.lvl
  lvlsParams := h.lvlsParams

/-- A stored name is not the fresh one. -/
theorem ne_of_stored {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none)
    {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci) : n ≠ c₀.name := by
  intro h; rw [h, hfresh] at hf; exact nomatch hf

/-- The names a representation's recursor spellings mention — the
members', the constructors' (real and copy) and, at the rules, the
recursors' — are all stored, so a fresh head is none of them and the
spellings do not move (`IndRepData.recDataAV_congr`,
`IndRepData.ruleAV_congr`). -/
theorem IndRep.names_ne {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {d : IndRepData V} {mm : Nat} (h : IndRep m T cvT cvR mI rP rules d mm)
    {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none) :
    (∀ t, t < d.k → d.memberName t ≠ c₀.name) ∧
    (∀ ψ, ∀ cd ∈ d.cdsR ψ, cd.1 ≠ c₀.name) := by
  refine ⟨fun t ht => ?_, fun ψ cd hcd => ?_⟩
  · obtain ⟨cv, caps, hf⟩ := h.membersFound t ht
    exact ne_of_stored hfresh hf
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hcd
    unfold IndRepData.cdsR at hi
    rw [fixCtorDataList_getElem?] at hi
    obtain ⟨cA, hcA, hcd'⟩ := Option.map_eq_some_iff.mp hi
    have hname : cd.1 = cA.1.name := by rw [← hcd']
    rw [hname]
    unfold IndRepData.ctorsAll at hcA
    rw [List.getElem?_append] at hcA
    split at hcA
    · obtain ⟨hfC, -, -⟩ := h.ctors i cA hcA
      exact ne_of_stored hfresh hfC
    · have hmem : cA ∈ d.ctorsC := List.mem_of_getElem? hcA
      have hs := h.ctorsCFound cA hmem
      cases hf : env.find? cA.1.name with
      | none => rw [hf] at hs; exact nomatch hs
      | some ci => exact ne_of_stored hfresh hf

/-- The recursor tower's spelling at a fresh cons is the prefix's. -/
theorem IndRep.recDataAV_cons {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : IndRepData V} {mm : Nat}
    (h : IndRep m T cvT cvR mI rP rules d mm)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) (ψ : Name → Nat) (mm' : Nat) :
    d.recDataAV m₂ ψ mm' = d.recDataAV m ψ mm' := by
  obtain ⟨hL, hC⟩ := h.names_ne hfresh
  refine d.recDataAV_congr (fun t ht => ?_) (fun cd hcd => ?_)
  · rw [hac, acvalWith_ne (hL t ht)]
  · rw [hac, acvalWith_ne (hC ψ cd hcd)]

/-- **The rules' readings at a fresh cons**, for a STORED recursor: the
prefix's readings cross (`denoteMeta_cons_mono` at every member's
recursor type and rule right-hand side, `ConsCrossEnv.typeOf`/
`ConsCrossEnv.ruleRhs`), the entries are the prefix's
(`Env.find?_cons_of_fresh` — the head is none of the block's recursors,
which are stored), and the spellings do not move. -/
theorem IndRep.rulesRead_cons {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : IndRepData V} {mm : Nat}
    (h : IndRep m T cvT cvR mI rP rules d mm)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hcross : ConsCrossEnv env c₀)
    (hfR : env.find? cvR.name = some (.recInfo cvR mI rP rules))
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    rules ≠ [] →
    Env.find? ⟨c₀ :: env.consts⟩ cvR.name = some (.recInfo cvR mI rP rules) →
    ∀ t, t < d.k → RecReadAt m₂ d cvT.levelParams t := by
  intro hne _ t ht
  have hbound := envWF_constsBound m.wf
  have hrecNe : ∀ t, t < d.k → d.recNames t ≠ c₀.name := by
    intro t ht
    obtain ⟨cvR', mI', rP', rules', hf', -⟩ := h.rulesRead hne hfR t ht
    exact ne_of_stored hfresh hf'
  obtain ⟨cvR', mI', rP', rules', hf', hlps, hmI', hrP', hread, hmap, hrules, hwalk⟩ :=
    h.rulesRead hne hfR t ht
  have hmemR' := ConLeche.Semantics.Env.find?_mem hf'
  refine ⟨cvR', mI', rP', rules', ConLeche.Env.find?_cons_of_fresh hfresh hf', hlps, hmI', hrP',
    fun ψ => ?_, hmap, fun j cA hj hmm => ?_, hwalk⟩
  · rw [hac, h.recDataAV_cons hfresh m₂ hac]
    exact denoteMeta_cons_mono hfresh (hcross.typeOf hf') ψ 0 (hbound _ hmemR').1 (hread ψ)
  · obtain ⟨rl, hrl, hctor, hfire, hread'⟩ := hrules j cA hj hmm
    refine ⟨rl, hrl, hctor, hfire, fun ψ => ?_⟩
    obtain ⟨-, -, -, -, -, hwfR, -⟩ := m.wf _ hmemR'
    obtain ⟨-, -, hres, -⟩ := hwfR cvR' mI' rP' rules' rfl rl hrl
    rw [hac, denoteMeta_cons_mono hfresh (hcross.ruleRhs hmemR' hrl) ψ 0
      (constsBound_of_constsResolve _ hres) (hread' ψ)]
    congr 1
    obtain ⟨hL, hC⟩ := h.names_ne hfresh
    refine d.ruleAV_congr (fun t ht => ?_) (fun cd hcd => ?_) (fun t ht => ?_) (h.tgtsRLt j)
    · rw [hac, acvalWith_ne (hL t ht)]
    · rw [hac, acvalWith_ne (hC ψ cd hcd)]
    · rw [hac, acvalWith_ne (hrecNe t ht)]

/-- **A representation crosses any fresh cons**: the block's former and
constructors are stored, so the head is none of them; the stored types
are unchanged and their readings cross (`crossAt`), the leaves are the
prefix's (`acvalWith_ne`), and the semantic laws mention no carrier. -/
theorem IndRep.cross {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {d : IndRepData V} {mm : Nat} (h : IndRep m T cvT cvR mI rP rules d mm)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hcross : ConsCrossEnv env c₀)
    {caps : IndCaps} (hfT : env.find? T = some (.indInfo cvT caps))
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A)
    -- the recursor's type crosses (task #279 M-A′: `recRead`)
    (hatR : ConsCrossAt c₀ cvR.type) (hcbR : ConstsBound env cvR.type)
    -- the rules' readings at the extension (`rulesRead`): the caller's —
    -- `IndRep.rulesRead_cons` for a recursor stored in the prefix, the
    -- install's own readings when the head IS the recursor
    (hrr : rules ≠ [] →
      Env.find? ⟨c₀ :: env.consts⟩ cvR.name = some (.recInfo cvR mI rP rules) →
      ∀ t, t < d.k → RecReadAt m₂ d cvT.levelParams t) :
    IndRep m₂ T cvT cvR mI rP rules d mm := by
  have hbound := envWF_constsBound m.wf
  have hTne : T ≠ c₀.name := ne_of_stored hfresh hfT
  have hcbT : ConstsBound env cvT.type :=
    (hbound _ (ConLeche.Semantics.Env.find?_mem hfT)).1
  have hleafT : m₂.acval T = m.acval T := by rw [hac, acvalWith_ne hTne]
  exact {
    member := h.member
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
      exact ⟨cv, caps, ConLeche.Env.find?_cons_of_fresh hfresh hf⟩
    membersLps := membersLps_of_find (fun _ _ hf => ConLeche.Env.find?_cons_of_fresh hfresh hf)
      h.membersFound h.membersLps
    memberNodup := h.memberNodup
    memsReal := h.memsReal
    ctorsCFound := fun cC hcC => by
      have hs := h.ctorsCFound cC hcC
      cases hf : env.find? cC.1.name with
      | none => rw [hf] at hs; exact nomatch hs
      | some ci => rw [ConLeche.Env.find?_cons_of_fresh hfresh hf]; rfl
    pinsReal := h.pinsReal
    recRead := fun ψ => by
      rw [hac, denoteMeta_cons_mono hfresh hatR ψ 0 hcbR (h.recRead ψ),
        h.recDataAV_cons hfresh m₂ hac]
    former := h.former.crossAt hfresh (hcross.typeOf hfT) hcbT m₂ hac
    formersRead := fun t ht cv caps hf => by
      obtain ⟨cv0, caps0, hf0⟩ := h.membersFound t (Nat.lt_of_lt_of_le ht h.kRealLe)
      have hne : d.memberName t ≠ c₀.name := ne_of_stored hfresh hf0
      rw [ConLeche.Env.find?_cons, if_neg (fun hh => hne hh.symm)] at hf
      exact (h.formersRead t ht cv caps hf).crossAt hfresh (hcross.typeOf hf)
        (hbound _ (ConLeche.Semantics.Env.find?_mem hf)).1 m₂ hac
    leafShape := fun t ht ψ => by
      obtain ⟨cv0, caps0, hf0⟩ := h.membersFound t (Nat.lt_of_lt_of_le ht h.kRealLe)
      rw [hac, acvalWith_ne (ne_of_stored hfresh hf0)]
      exact h.leafShape t ht ψ
    ctors := fun j cA hj => by
      obtain ⟨hfC, hlps, hD⟩ := h.ctors j cA hj
      obtain ⟨⟨cv, cps, hfm⟩, htg⟩ := h.memsFound j (List.getElem?_eq_some_iff.mp hj).1
      refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfC, hlps, ?_⟩
      refine hD.crossAt hfresh (ne_of_stored hfresh hfm) (fun i => ?_) (hcross.typeOf hfC)
        (hbound _ (ConLeche.Semantics.Env.find?_mem hfC)).1 m₂ hac
      obtain ⟨cv', cps', hf'⟩ := htg i
      exact ne_of_stored hfresh hf'
    memsFound := fun j hj => by
      obtain ⟨⟨cv, cps, hfm⟩, htg⟩ := h.memsFound j hj
      refine ⟨⟨cv, cps, ConLeche.Env.find?_cons_of_fresh hfresh hfm⟩, fun i => ?_⟩
      obtain ⟨cv', cps', hf'⟩ := htg i
      exact ⟨cv', cps', ConLeche.Env.find?_cons_of_fresh hfresh hf'⟩
    idxRes := fun j cA hj e he => Expr.constsResolve_mono (h.idxRes j cA hj e he)
    uParams := h.uParams
    paramsIff := h.paramsIff
    paramsIffM := h.paramsIffM
    chains := h.chains
    functor := h.functor
    fibre := h.fibre
    leaf := fun ψ ρ as is h1 h2 => by rw [hleafT]; exact h.leaf ψ ρ as is h1 h2
    tupMem := h.tupMem
    ctor := fun j cA hj ψ ρ as fs h1 h2 => by
      obtain ⟨hfC, -, -⟩ := h.ctors j cA hj
      rw [hac, acvalWith_ne (ne_of_stored hfresh hfC)]
      exact h.ctor j cA hj ψ ρ as fs h1 h2
    mkZero := h.mkZero
    mkInj := h.mkInj }

/-- A modeled recursor's leaf fact crosses any fresh cons: the recursor
and its model are stored, so the head is neither. -/
theorem ModeledLeaf.cross {m : EnvModel V env} {n : Name} (h : ModeledLeaf m n)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) {ci : ConstantInfo} (hfn : env.find? n = some ci)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    ModeledLeaf m₂ n := by
  obtain ⟨hsome, hleaf⟩ := h
  cases hfm : env.find? (n.str "_model") with
  | none => rw [hfm] at hsome; exact nomatch hsome
  | some cm =>
  refine ⟨by rw [ConLeche.Env.find?_cons_of_fresh hfresh hfm]; rfl, fun ψ => ?_⟩
  rw [hac, acvalWith_ne (ne_of_stored hfresh hfm), acvalWith_ne (ne_of_stored hfresh hfn)]
  exact hleaf ψ

/-- **The clause at a fresh cons**: the prefix's representations cross,
and a fresh recursor supplies its own (`IndRepsHead`). -/
theorem IndReps.cons {m : EnvModel V env} (h : IndReps m)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hcross : ConsCrossEnv env c₀)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A)
    (hhead : IndRepsHead env c₀ m₂) :
    IndReps m₂ := by
  intro n cvR mI rP rules hfR T hn
  rw [ConLeche.Env.find?_cons] at hfR
  by_cases hR : c₀.name = n
  · rw [if_pos hR] at hfR
    have hc₀ : c₀ = .recInfo cvR mI rP rules := Option.some.inj hfR
    have hname : cvR.name = n := by rw [← hR, hc₀]; rfl
    rw [← hname] at hn ⊢
    exact hhead cvR mI rP rules hc₀ T hn
  · rw [if_neg hR] at hfR
    rcases h n cvR mI rP rules hfR T hn with ⟨cvT, caps, d, mm, hfT, hd⟩ | hmod
    · have hfR' : env.find? cvR.name = some (.recInfo cvR mI rP rules) := by
        rw [show cvR.name = n from ConLeche.Semantics.Env.find?_name hfR]; exact hfR
      exact Or.inl ⟨cvT, caps, d, mm, ConLeche.Env.find?_cons_of_fresh hfresh hfT,
        hd.cross hfresh hcross hfT m₂ hac (hcross.typeOf hfR')
          ((envWF_constsBound m.wf _ (ConLeche.Semantics.Env.find?_mem hfR')).1)
          (hd.rulesRead_cons hfresh hcross hfR' m₂ hac)⟩
    · exact Or.inr (hmod.cross hfresh hfR m₂ hac)

end ConLeche.Model
