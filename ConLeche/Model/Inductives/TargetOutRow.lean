module

public import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.ContInst
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.ContInstRule
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.NatEqs
import ConLeche.Verify.BridgeWfImp
import ConLeche.Model.Annot.BitInst

public section

/-!
# The rule rows at an OUTSIDE class

At a recursor whose major is an outside container `C.{us} ds` the rule
data are the target check's at the major (`tgtFdomsAV`, `tgtMkAV`,
`TargetIhData.lean`), and the class is the recorded block `D` holding
`C` (`TgtOutCls`).  `instCtor_open` and `instCtor_decode` read the
rule's opened constructor through `D`'s clause; this file pins that
reading to the target check's rule run (`targetRuleAtG`):

* `tgtOutEs` — the class's index expressions: the recorded result
  indices substituted by `instTau` (no spine-arity fact identifies the
  kernel's `getAppArgs.drop nPc` with them, so an outside class DEFINES
  its `es` as the values the decoding reads);
* `tgtOutDec_core` — **the decoding row**: a spine fitting the rule's
  field domains at a prefix whose key frame satisfies the container's
  parameter telescope hole-fits the recorded constructor at the carrier,
  at the index tuple the class's index expressions read to
  (`LfpClause.resIdxFit`), and the fired spine (`tgtMkAV`) reads to the
  clause's injection.

The satisfaction of the container's parameter telescope at the key frame
is the row's premise `hsat`, discharged by `tgtOutSat` (the kernel types
the instantiation at the rule prefix, `TargetTyEntry.pinTys_of`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **A read spine read deeper**: its readings lifted past the extra
binders (`denoteMeta_lift`, argument by argument). -/
theorem denoteMetaSpine_liftD {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      (∀ x ∈ as, Expr.WScoped d x) → ∀ k : Nat,
      DenoteMetaSpine acval env φ (d + k) as (vs.map (AnnotTerm.liftN k · 0))
  | _, _, .nil, _, _ => .nil
  | a :: _, _, .cons ha hs, hw, k => by
    refine .cons ?_ (denoteMetaSpine_liftD hacl hs (fun x hx => hw x (List.mem_cons_of_mem _ hx)) k)
    rw [denoteMeta_lift hacl (hw a List.mem_cons_self) _ (Nat.le_add_right _ _), ha,
      Nat.add_sub_cancel_left]
    rfl

/-- The member-format family's constructors at `j` are the major's. -/
theorem tgtRs_ctors {out : List (ConstantVal × TargetMajor × List Expr)} {j : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) : r.2.2.2 = (tgtMajor out j).ctors := by
  simp only [tgtRs, List.getElem?_map] at hr
  cases ho : out[j]? with
  | none => rw [ho] at hr; exact nomatch hr
  | some t =>
    rw [ho] at hr
    obtain rfl := Option.some.inj hr
    simp only [tgtMajor, List.getD_eq_getElem?_getD, ho, Option.getD_some]

/-- **An outside class's index expressions** at the `(j, i)`-th rule:
the recorded result indices of `D`'s member `mm`'s constructor `i`,
substituted by the instantiation's `instTau` (below the rule's `nF`
field binders). -/
@[expose] noncomputable def tgtOutEs {env : Env} (mp : EnvModelM V μ env) (D : LfpDatum V)
    (mm : Nat) (lps : List Name) (M : TargetMajor) (rP : Nat) (ψ : Name → Nat) (i : Nat) :
    List AnnotTerm :=
  (D.resIdx (Level.substFn ψ lps M.lvls) mm i).map fun e =>
    AnnotTerm.substAV (instTau mp ψ D M.lvls rP M.ds) e (M.ctors.getD i default).2

end ConLeche.Model
