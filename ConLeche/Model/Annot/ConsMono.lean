module

import ConLeche.Model.Annot.BitExtend
public import ConLeche.Model.Annot.BitConsCross
import ConLeche.Semantics.ConstsBound

public section

/-!
# Readings across a fresh cons (task #161 P4; split out at task #280)

The transfer lemmas of the P declaration step (`ConLeche/Model/Install.lean`):
a fresh cons preserves every stored lookup, the readings of prefix-bound
subjects survive the extension and ignore the fresh leaf
(`denoteMeta_cons_fresh`, `denoteMeta_cons_mono`), and the pinned-basis
valuation crosses.  They sit below the step so that the representation
clause's own transport (`ConLeche/Model/IndRepCons.lean`) can use them
and the step can use that transport.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-- A fresh cons preserves every stored lookup. -/
theorem findPreserved_cons {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) :
    FindPreserved env ⟨c₀ :: env.consts⟩ := by
  intro n ci hf
  have hne : (c₀.name == n) = false := by
    by_cases h : c₀.name = n
    · subst h
      rw [hfresh] at hf
      exact nomatch hf
    · simpa using h
  show List.find? _ (c₀ :: env.consts) = some ci
  rw [List.find?_cons_of_neg (by simpa using hne)]
  exact hf

/-- **The fresh-cons transfer**: readings of prefix-bound subjects
survive the extension and ignore the fresh leaf — the composition of
`denoteMeta_envExtend` (a theorem) and `denoteMeta_acvalWith_fresh`.  The
harvest layer reads it directly; `declStep_preserves_of_cons` uses it for
every old-constant field. -/
theorem denoteMeta_cons_fresh {acval : Name → (Name → Nat) → AnnotTerm}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hntc : ∀ entry, c₀ ≠ .projInfo entry)
    (hlga : LitGuardsAgree env ⟨c₀ :: env.consts⟩)
    (ψ : Name → Nat) (d : Nat) (e : Expr) (hcb : ConstsBound env e) :
    denoteMeta (acvalWith acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d e
      = denoteMeta acval env ψ d e := by
  rw [← denoteMeta_envExtend (findPreserved_cons hfresh) hlga
      (ConLeche.Verify.findProj?_cons_of_base_none hntc)
      d e hcb,
    denoteMeta_acvalWith_fresh hfresh d e]

/-- **The fresh-cons forward transfer** (the monotone form; the
equality form is refutable at support-completing installs — see
`denoteMeta_envExtend_mono`): a successful prefix reading survives the
extension and ignores the fresh leaf.  The only direction the step
and the harvests use for their subjects, whose acceptance guaranteed
prefix-supported literals. -/
theorem denoteMeta_cons_fresh_mono {acval : Name → (Name → Nat) → AnnotTerm}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hntc : ∀ entry, c₀ ≠ .projInfo entry)
    (ψ : Name → Nat) (d : Nat) (e : Expr) (hcb : ConstsBound env e)
    {ea : AnnotTerm} (h : denoteMeta acval env ψ d e = some ea) :
    denoteMeta (acvalWith acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d e
      = some ea :=
  denoteMeta_envExtend_mono (findPreserved_cons hfresh)
    (litGuardsMono_cons hfresh)
    (ConLeche.Verify.findProj?_cons_of_base_none hntc) d e hcb
    (by rw [denoteMeta_acvalWith_fresh hfresh]; exact h)

/-- **The P cons crossing at any head** (task #175 W4c, module 4): a
prefix reading of a subject the head's slot does not mention
(`ConsCrossAt`) survives the cons — the fresh crossing at a non-table
head, the table-slot refinement (`denoteMeta_envExtend_mono_at`) at a
table one. -/
theorem denoteMeta_cons_mono {acval : Name → (Name → Nat) → AnnotTerm}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    {e : Expr} (hat : ConsCrossAt c₀ e)
    (ψ : Name → Nat) (d : Nat) (hcb : ConstsBound env e)
    {ea : AnnotTerm} (h : denoteMeta acval env ψ d e = some ea) :
    denoteMeta (acvalWith acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d e
      = some ea := by
  by_cases htw : ∃ tbl : ConLeche.ProjTable, c₀ = .projInfo tbl
  · obtain ⟨tbl, rfl⟩ := htw
    refine denoteMeta_envExtend_mono_at (findPreserved_cons hfresh)
      (litGuardsMono_cons hfresh)
      (fun sn j e' h0 h1 => findProj?_cons_tower sn j e' h0 h1)
      d e hcb (hat tbl rfl) ?_
    rw [denoteMeta_acvalWith_fresh hfresh]
    exact h
  · refine denoteMeta_cons_fresh_mono hfresh ?_ ψ d e hcb h
    intro e' heq
    exact htw ⟨e', heq⟩

/-- The pinned-basis valuation survives any fresh cons that moves no
other name (`BasisPinnedTT.cons` without the install record — its
proof consults only freshness and agreement). -/
theorem basisPinnedTT_consFresh {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : BasisPinnedTT env cval)
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → cval n = cval' n)
    (hhead : ConLeche.reservedBasisNames.contains c₀.name = true →
      (ConstantInfo.isBasis c₀ = true → c₀ = pinnedInfo c₀.name) ∧
      ∀ (ψ : Name → Nat) (t : Term),
        pinnedStructT c₀.name ψ = some t → cval' c₀.name ψ = t) :
    BasisPinnedTT ⟨c₀ :: env.consts⟩ cval' := by
  intro n ci hf hres
  by_cases hn : c₀.name = n
  · subst hn
    rw [ConLeche.Env.find?_cons, if_pos rfl] at hf
    obtain rfl : ci = c₀ := (Option.some.inj hf).symm
    exact ⟨(hhead hres).1, fun t ψ hp => (hhead hres).2 ψ t hp⟩
  · rw [ConLeche.Env.find?_cons, if_neg hn] at hf
    refine ⟨(h n ci hf hres).1, fun t ψ hp => ?_⟩
    rw [← hag n (fun hh => hn hh.symm)]
    exact (h n ci hf hres).2 t ψ hp


end ConLeche.Model
