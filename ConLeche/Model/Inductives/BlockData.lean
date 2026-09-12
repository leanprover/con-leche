module

import ConLeche.Model.Annot.EnvModel
public import ConLeche.Model.Steps.Stuck
public import ConLeche.Semantics.Tower.TowerWire
import ConLeche.Semantics.Sat
public import ConLeche.Semantics.ConstsBound
import ConLeche.Kernel.Inductives.NativeInstall
public import ConLeche.Verify.Inductives.FixWF
public section

/-!
# The block data of an inductive install (task #280)

The reading structures the inductive installs establish and the
representation clause of the environment invariant (`IndReps`,
`ConLeche/Model/IndRep.lean`) states over: the former's peeled type
reading (`FormerData`), a constructor's reading at an indexed family
(`CtorDataI`) and its recursive refinement (`FixOpened`,
`FixCtorDataI`, `FixCtorFactsAt`), and the per-block lists the
fixpoint leaf is spelled from (`CtorDatumR`, `fixCtorDataList`,
`fssOfR`/`essOfR`/`eissOfR`/`tlssOfR`/`rssOfK`).  They used to live
next to their establishing theorems (`StructData`, `SumData`,
`FixData`, `FixCtorReads`, `FixStageRec`, `FixChains`); the clause
needs them BELOW `EnvModelM`, so the definitions moved here verbatim
and those modules re-export this one.  No statement changed.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- The parameter-variable spine of the constructor's opened body, in
the reading's spelling. -/
@[expose] def paramBvars (nP nF : Nat) : List AnnotTerm :=
  (List.range nP).map fun k => AnnotTerm.bvar (nP + nF - 1 - k)

/-- The parameter variables as seen from depth `D` (`D ≥ nP`). -/
@[expose] def paramBvarsAt (nP D : Nat) : List AnnotTerm :=
  (List.range nP).map fun k => .bvar (D - 1 - k)

theorem paramBvars_eq_paramBvarsAt (nP nF : Nat) :
    paramBvars nP nF = paramBvarsAt nP (nP + nF) := rfl

/-- **The type former's reading, peeled**: at every assignment the
stored type reads as the Π-tower over the parameter data ending in
the result sort, with nonzero codomain bits, graded, bounded, each
parameter domain in its own universe (`lvls`), and depending only on
the block's level parameters. -/
structure FormerData {env : Env} (m : EnvModel V env) (cvT : ConstantVal)
    (nP : Nat) (resSort : Level)
    (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (lvls : (Name → Nat) → List Nat) : Prop where
  read : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvT.type
    = some (mkPisAV (pps ψ) (.sort (resSort.eval ψ)))
  len : ∀ ψ : Name → Nat, (pps ψ).length = nP
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ pps ψ → d.2.1 ≠ 0
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    WellDenotedV V ρ (mkPisAV (pps ψ) (.sort (resSort.eval ψ)))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (pps ψ)
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvT.levelParams, ψ₁ p = ψ₂ p) →
    pps ψ₁ = pps ψ₂ ∧ resSort.eval ψ₁ = resSort.eval ψ₂
  /-- one universe per parameter binder -/
  lvlsLen : ∀ ψ : Name → Nat, (lvls ψ).length = nP
  /-- each parameter domain's reading lies in its binder's universe,
  at a frame satisfying the earlier domains (innermost first) -/
  lvl : ∀ (ψ : Name → Nat) (i : Nat), i < nP → ∀ ρ : Nat → V,
    Sat V ((((pps ψ).take i).map (·.2.2)).reverse) ρ →
    interp V ρ (((pps ψ).getD i default).2.2) ∈ˢ (univ ((lvls ψ).getD i 0) : V)
  lvlsParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvT.levelParams, ψ₁ p = ψ₂ p) →
    lvls ψ₁ = lvls ψ₂


/-- The fields not sourced by an index are propositions: each such
field's domain is a truth value, hereditarily. -/
@[expose] def FieldsBoundSrc (ρ : Nat → V) : List AnnotTerm → List (Option Nat) → Prop
  | [], _ => True
  | _ :: _, [] => True
  | F :: Fs, s :: ss => (s = none → interp V ρ F ∈ˢ (univ 0 : V)) ∧
      ∀ a, a ∈ˢ interp V ρ F → FieldsBoundSrc (cons a ρ) Fs ss

/-- The family at the parameter variables and the index readings,
read at the constructor's full frame. -/
@[expose] def ctorBodyAVI {env : Env} (m : EnvModel V env) (T : Name) (nP nF : Nat)
    (ψ : Name → Nat) (Es : List AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)

/-- **A constructor's data at an indexed family**: its stored type
reads to the Π-tower over `ds ψ` ending in the family at the
parameters and the index readings `Es ψ`; the index readings read the
residual's index expressions `idxArgs` at the constructor's frame; the
sources `srcs` name, per field, the index it literally is, and at a
large-eliminating `Prop` family the other fields are
propositional. -/
structure CtorDataI {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name)
    (cvC : ConstantVal) (nP nF nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (idxArgs : List Expr)
    (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (Es : (Name → Nat) → List AnnotTerm)
    (srcs : List (Option Nat)) : Prop where
  resid : ∃ (cbs : List (Expr × BinderMeta)) (es : List Expr),
    cvC.type.stripPis (nP + nF)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (ConLeche.structPsAt nF nP ++ es)) ∧
    es.length = nIdx
  read : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvC.type
    = some (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ)))
  len : ∀ ψ : Name → Nat, (ds ψ).length = nP + nF
  lenE : ∀ ψ : Name → Nat, (Es ψ).length = nIdx
  idxLen : idxArgs.length = nIdx
  idxRead : ∀ ψ : Name → Nat, DenoteMetaSpine m.acval env ψ (nP + nF) idxArgs (Es ψ)
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ ds ψ →
    (resSort.eval ψ = 0 ↔ d.2.1 = 0)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    WellDenotedV V ρ (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ)))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (ds ψ)
  belowE : ∀ ψ : Name → Nat, ∀ E ∈ Es ψ, Term.bvarsBelow (nP + nF) E.erase
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) →
    ds ψ₁ = ds ψ₂ ∧ Es ψ₁ = Es ψ₂
  srcLen : srcs.length = nF
  srcBnd : ∀ s ∈ srcs, ∀ l, s = some l → l < nIdx
  srcIdx : ∀ j l, srcs[j]? = some (some l) → ∀ ψ : Name → Nat,
    (Es ψ)[l]? = some (AnnotTerm.bvar (nF - 1 - j))
  srcProp : large = true → ∀ ψ : Name → Nat, resSort.eval ψ = 0 → ∀ ρ : Nat → V,
    Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
    FieldsBoundSrc ρ (((ds ψ).drop nP).map (·.2.2)) srcs

/-- The recursive positions as the functor's Bool list. -/
@[expose] def rsOf (ks : List RecFieldKind) : List Bool := ks.map fun k => decide (k = .recursive ∨ k = .reflexive)

/-- `nativeOpenedOk`, read positionally.

A recursive or reflexive field's domain is the leaf of the member it
TARGETS (`tgtOf`, whose index count is `nIdxOf`); at a single-family
block every field targets the block's own former, which is the
parameters' default (task #278 M2.6: the member view). -/
structure FixOpened (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx nF : Nat)
    (ks : List RecFieldKind) (fvsP xFvs : List Expr) (xrest : Expr)
    (tgtOf : Nat → Name := fun _ => T) (nIdxOf : Nat → Nat := fun _ => nIdx) : Prop where
  residRes : ∀ e ∈ xrest.getAppArgs.drop nP, e.constsResolve env₀ = true
  ord : ∀ i x, xFvs[i]? = some x → ks.getD i .ordinary = .ordinary →
    x.fvarTypeD.constsResolve env₀ = true
  recF : ∀ i x, xFvs[i]? = some x → ks.getD i .ordinary = .recursive →
    x.fvarTypeD.getAppFn = Expr.const (tgtOf i) (lps.map .param) ∧
    x.fvarTypeD.getAppArgs.take nP = fvsP ∧
    x.fvarTypeD.getAppArgs.length = nP + nIdxOf i ∧
    (∀ e ∈ x.fvarTypeD.getAppArgs.drop nP, e.constsResolve env₀ = true) ∧
    (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
    xrest.mentionsFvar (nP + i) = false
  /-- a REFLEXIVE field (task #202): its own telescope opened at
  variables at the field's depth, the domains resolving before the
  block, the body the family at the parameter variables and index
  expressions resolving before the block; the variable a leaf of no
  later domain nor of the residual -/
  reflF : ∀ i x, xFvs[i]? = some x → ks.getD i .ordinary = .reflexive →
    ∃ afvs body,
      openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) = some (afvs, body) ∧
      afvs.length ≠ 0 ∧
      (∀ a ∈ afvs, a.fvarTypeD.constsResolve env₀ = true) ∧
      body.getAppFn = Expr.const (tgtOf i) (lps.map .param) ∧
      body.getAppArgs.take nP = fvsP ∧
      body.getAppArgs.length = nP + nIdxOf i ∧
      (∀ e ∈ body.getAppArgs.drop nP, e.constsResolve env₀ = true) ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
      xrest.mentionsFvar (nP + i) = false
  kinds : ∀ i, i < nF → ks.getD i .ordinary = .ordinary ∨ ks.getD i .ordinary = .recursive ∨
    ks.getD i .ordinary = .reflexive

/-- **A recursive constructor's data** at a carrier storing the former
(see the module docstring). -/
structure FixCtorDataI {env : Env} (m : EnvModel V env) (env₀ : Env) (T : Name)
    (lps : List Name) (cvC : ConstantVal) (nP nF nIdx : Nat) (resSort : Level)
    (isProp large : Bool) (idxArgs : List Expr)
    (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (Es : (Name → Nat) → List AnnotTerm)
    (srcs : List (Option Nat)) (ks : List RecFieldKind) (fvsP xFvs : List Expr) (xrest : Expr)
    (Eiss : (Name → Nat) → List (List AnnotTerm))
    (tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (tgtOf : Nat → Name := fun _ => T) (nIdxOf : Nat → Nat := fun _ => nIdx) : Prop
    extends CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs where
  opened : FixOpened env₀ T lps nP nIdx nF ks fvsP xFvs xrest tgtOf nIdxOf
  opens : ∃ crest, openPisAtFvars nP cvC.type 0 = some (fvsP, crest) ∧
    openPisAtFvars nF crest nP = some (xFvs, xrest)
  ksLen : ks.length = nF
  xLen : xFvs.length = nF
  pLen : fvsP.length = nP
  xIdx : ∀ k x, xFvs[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty
  pIdx : ∀ k x, fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty
  idxEq : idxArgs = xrest.getAppArgs.drop nP
  domRead : ∀ ψ i x, xFvs[i]? = some x →
    denoteMeta m.acval env ψ (nP + i) x.fvarTypeD = some ((ds ψ).getD (nP + i) default).2.2
  eissLen : ∀ ψ, (Eiss ψ).length = nF
  eisRead : ∀ ψ i x, xFvs[i]? = some x → ks.getD i .ordinary = .recursive →
    DenoteMetaSpine m.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop nP) ((Eiss ψ).getD i [])
  eisLen : ∀ ψ i, ks.getD i .ordinary = .recursive → i < nF →
    ((Eiss ψ).getD i []).length = nIdxOf i
  /-- a recursive field's entry: the TARGET member's leaf at the
  parameter variables and the field's index readings -/
  recEntry : ∀ ψ i, ks.getD i .ordinary = .recursive → i < nF →
    ((ds ψ).getD (nP + i) default).2.2
      = AnnotTerm.mkAppN (m.acval (tgtOf i) ψ) (paramBvarsAt nP (nP + i) ++ (Eiss ψ).getD i [])
  eissParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) → Eiss ψ₁ = Eiss ψ₂
  /-- an index expression is read under the field's telescope (empty at
  a finitary field) -/
  eissBelow : ∀ ψ i, ∀ E ∈ (Eiss ψ).getD i [],
    Term.bvarsBelow (nP + i + ((tss ψ).getD i []).length) E.erase
  ordNone : ∀ ψ i, ks.getD i .ordinary ≠ .recursive → ks.getD i .ordinary ≠ .reflexive →
    (Eiss ψ).getD i [] = []
  /-- the reflexive fields' telescopes (task #202): one list per field,
  empty at a non-reflexive one -/
  tssLen : ∀ ψ, (tss ψ).length = nF
  tssNone : ∀ ψ i, ks.getD i .ordinary ≠ .reflexive → (tss ψ).getD i [] = []
  /-- the telescope's codomain bits are at the family's regime -/
  tssBits : ∀ ψ i, ∀ d ∈ (tss ψ).getD i [], (d.2.1 = 0 ↔ resSort.eval ψ = 0)
  /-- the telescope entries are readings' Π-entries: domain bit `0`,
  codomain bit at most `1` -/
  tssPiBits : ∀ ψ i, ∀ d ∈ (tss ψ).getD i [], d.1 = 0 ∧ d.2.1 ≤ 1
  tssBelow : ∀ ψ i, DomsBelow (nP + i) ((tss ψ).getD i [])
  tssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) → tss ψ₁ = tss ψ₂
  /-- a reflexive field's telescope, opened at the field's depth: its
  domains read to the telescope's entries, its body's index
  expressions read to the field's readings under the telescope -/
  reflOpen : ∀ ψ i x, xFvs[i]? = some x → ks.getD i .ordinary = .reflexive →
    ∃ afvs body,
      openPisAtFvars ((tss ψ).getD i []).length x.fvarTypeD (nP + i) = some (afvs, body) ∧
      ((tss ψ).getD i []).length = (x.fvarTypeD.piBinders).1.length ∧
      (∀ k a, afvs[k]? = some a →
        denoteMeta m.acval env ψ (nP + i + k) a.fvarTypeD
          = some (((tss ψ).getD i []).getD k default).2.2) ∧
      DenoteMetaSpine m.acval env ψ (nP + i + ((tss ψ).getD i []).length)
        (body.getAppArgs.drop nP) ((Eiss ψ).getD i [])
  eisLenRefl : ∀ ψ i, ks.getD i .ordinary = .reflexive → i < nF →
    ((Eiss ψ).getD i []).length = nIdxOf i
  /-- a reflexive field's entry: the Π-tower over its telescope of the
  TARGET member's leaf at the parameter variables (under the
  telescope) and the readings -/
  reflEntry : ∀ ψ i, ks.getD i .ordinary = .reflexive → i < nF →
    ((ds ψ).getD (nP + i) default).2.2
      = mkPisAV ((tss ψ).getD i [])
          (AnnotTerm.mkAppN (m.acval (tgtOf i) ψ)
            (paramBvarsAt nP (nP + i + ((tss ψ).getD i []).length) ++ (Eiss ψ).getD i []))

/-- A recursive constructor datum: name, field count, field data,
index readings, recursive positions, per-field index-expression
readings, per-field telescopes (empty at a finitary field; task
#202). -/
abbrev CtorDatumR :=
  Name × Nat × List (Nat × Nat × AnnotTerm) × List AnnotTerm × List Nat × List (List AnnotTerm) ×
    List (List (Nat × Nat × AnnotTerm))

/-- The recursive constructor data of a list of constructors, from
constructor `j` on. -/
@[expose] def fixCtorDataList (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    List (ConstantVal × Nat) → Nat → List CtorDatumR
  | [], _ => []
  | c :: cs, j =>
    (c.1.name, c.2, dsF j ψ, esF j ψ, ConLeche.recIdxOf (ksF j), eissF j ψ, tssF j ψ) ::
      fixCtorDataList dsF esF ksF eissF tssF ψ cs (j + 1)

omit [SetTheory V] in
theorem fixCtorDataList_getElem? (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j i : Nat),
      (fixCtorDataList dsF esF ksF eissF tssF ψ cs j)[i]?
        = (cs[i]?).map fun c =>
            (c.1.name, c.2, dsF (j + i) ψ, esF (j + i) ψ, ConLeche.recIdxOf (ksF (j + i)),
              eissF (j + i) ψ, tssF (j + i) ψ)
  | [], _, _ => rfl
  | c :: cs, j, 0 => by simp [fixCtorDataList]
  | c :: cs, j, i + 1 => by
    simp only [fixCtorDataList, List.getElem?_cons_succ]
    rw [fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ cs (j + 1) i]
    congr 2
    funext c
    rw [show j + 1 + i = j + (i + 1) from by omega]

/-- The per-constructor facts of a recursive block at a position. -/
@[expose] def FixCtorFactsAt {env : Env} (m : EnvModel V env) (env₀ : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List RecFieldKind) (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (j : Nat) (cA : ConstantVal × Nat)
    (tgtOf : Nat → Name := fun _ => T) (nIdxOf : Nat → Nat := fun _ => nIdx) : Prop :=
  env.find? cA.1.name = some (.ctorInfo cA.1 nP cA.2) ∧
  cA.1.levelParams = lps ∧
  FixCtorDataI m env₀ T lps cA.1 nP cA.2 nIdx resSort isProp large (idxF j) (dsF j) (esF j)
    (srcsF j) (ksF j) (fvsPF j) (xFvsF j) (xrestF j) (eissF j) (tssF j) tgtOf nIdxOf

/-- The constructors' field lists. -/
@[expose] def fssOfR (nP : Nat) (cds : List CtorDatumR) : List (List AnnotTerm) :=
  cds.map fun cd => (cd.2.2.1.drop nP).map (·.2.2)

/-- The constructors' index readings. -/
@[expose] def essOfR (cds : List CtorDatumR) : List (List AnnotTerm) := cds.map fun cd => cd.2.2.2.1

/-- The constructors' per-field index expressions. -/
@[expose] def eissOfR (cds : List CtorDatumR) : List (List (List AnnotTerm)) := cds.map fun cd => cd.2.2.2.2.2.1

/-- The per-constructor telescopes (task #202). -/
@[expose] def tlssOfR (cds : List CtorDatumR) : List (List (List (Nat × Nat × AnnotTerm))) :=
  cds.map fun cd => cd.2.2.2.2.2.2

/-- The recursive flags of the first `n` constructors. -/
@[expose] def rssOfK (ksF : Nat → List RecFieldKind) (n : Nat) : List (List Bool) :=
  (List.range n).map fun j => rsOf (ksF j)

/-! ## Boundness through openings -/

omit [SetTheory V] in
/-- A bounded application's arguments are bounded. -/
theorem constsBound_getAppArgs {env₀ : Env} :
    ∀ (e : Expr), ConstsBound env₀ e → ∀ a ∈ e.getAppArgs, ConstsBound env₀ a
  | .app f a, he, x, hx => by
    rw [constsBound_app] at he
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact constsBound_getAppArgs f he.1 x hx
    · exact he.2
  | .bvar _, _, _, hx => nomatch hx
  | .fvar _ _, _, _, hx => nomatch hx
  | .sort _, _, _, hx => nomatch hx
  | .const _ _, _, _, hx => nomatch hx
  | .lam _ _ _, _, _, hx => nomatch hx
  | .forallE _ _ _, _, _, hx => nomatch hx
  | .letE _ _ _, _, _, hx => nomatch hx
  | .lit _, _, _, hx => nomatch hx
  | .proj _ _ _, _, _, hx => nomatch hx

omit [SetTheory V] in
/-- An opening's variables (their types) and residual are bounded when
the opened term is. -/
theorem openPisAtFvars_constsBound {env₀ : Env} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      ConstsBound env₀ e → openPisAtFvars n e d = some (fvs, o) →
      (∀ x ∈ fvs, ConstsBound env₀ x) ∧ ConstsBound env₀ o
  | 0, e, d, fvs, o, he, hop => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun x hx => nomatch hx), he⟩
  | n + 1, e, d, fvs, o, he, hop => by
    match e, he, hop with
    | .forallE dom bd mb, he, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        rw [constsBound_forallE] at he
        have hfv : ConstsBound env₀ (Expr.fvar d dom) := by
          rw [constsBound_fvar]; exact he.1
        obtain ⟨hfvs, ho⟩ := openPisAtFvars_constsBound n
          (ConstsBound.instantiate1 hfv bd 0 he.2) h₁
        refine ⟨fun x hx => ?_, ho⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hfv
        · exact hfvs x hx
      · exact nomatch hop

end ConLeche.Model
