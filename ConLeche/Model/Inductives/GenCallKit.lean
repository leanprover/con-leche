module

public import ConLeche.Model.Inductives.GenRecAssembly
public import ConLeche.Model.Inductives.TargetNodeRead
public import ConLeche.Verify.Inductives.GenK53Rename

public section

/-!
# The generated calls' kit (lane GENREC-B2)

* `openPis_stripPis_locOpen` — an `ih`'s telescope opened at variables
  (`ClassGen.ihParts`) is its `stripPis` split, the leaf opened at the
  canonical openers (`locOpen`) up to annotations, and its domains' reading
  (`readOpenedDoms`) is the telescope's (`teleDoms`) whenever that reads;
* `genFap_read` — the applied field of a call, read at the call's
  valuation, is the field value applied to the telescope's values;
* `genRecIdx_spec` — the recursor a generated rule calls at class `t`
  (`genRecIdx`) is a recursor at class `t`, below the family's length.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V]

/-- **An `ih`'s telescope, opened**: see the module docstring. -/
theorem openPis_stripPis_locOpen {n D : Nat} {w : Expr} {xsO : List Expr} {leafO : Expr}
    (h : openPisAtFvars n w D = some (xsO, leafO)) :
    ∃ (tele : List (Expr × ConLeche.BinderMeta)) (leaf : Expr),
      w.stripPis n = some (tele, leaf) ∧ xsO.length = n ∧
      (∀ l, l < n → ∃ ty, xsO[l]? = some (.fvar (D + l) ty)) ∧
      Expr.ErasedEq leafO (leaf.instantiateList (locOpen D n) 0) ∧
      ∀ (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (ψ : Name → Nat)
        (doms : List AnnotTerm),
        teleDoms acval env ψ D [] (tele.map (·.1)) = some doms →
        readOpenedDoms acval env ψ D xsO = doms := by
  sorry

/-- **A call's applied field, read**: the field `fvar (rP + i)` applied
to the telescope's openers `fvar (rP + nF + l)`, read at the call's
valuation, is the field's value applied to the telescope's values. -/
theorem genFap_read {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {ψ : Name → Nat}
    {rP nF m i : Nat} {f : Expr} {xsO : List Expr} (hi : i < nF)
    (hf : ∃ ty, f = .fvar (rP + i) ty)
    (hxsO : ∀ l, l < m → ∃ ty, xsO[l]? = some (.fvar (rP + nF + l) ty)) (hm : xsO.length = m)
    {xs fs bs : List V} (hxl : xs.length = rP) (hfl : fs.length = nF) (hbl : bs.length = m)
    (ρ : Nat → V) :
    interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta acval env ψ (rP + nF + m) (Expr.mkAppN f xsO)).getD default)
      = bs.foldl app (fs.getD i pt) := by
  sorry

/-- **The generated rules' callee at class `t`** (`genRecIdx`, the
kernel's `classRecOf` as a position): a recursor at class `t`, below the
generated family's length. -/
theorem genRecIdx_spec {rd : ClassRead} {cvGs : List ConstantVal} {t : Nat} {n : Name}
    (h : ConLeche.classRecOf rd.recCls cvGs t = some n) (hle : cvGs.length ≤ rd.recCls.length) :
    rd.recCls[genRecIdx rd t]? = some t ∧ genRecIdx rd t < cvGs.length := by
  sorry

end ConLeche.Model
