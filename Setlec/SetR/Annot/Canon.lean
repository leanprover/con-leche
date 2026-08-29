import Setlec.SetR.Annot.Pass

/-!
# Canonical annotations (task #151 tier C — the R1 resolution of WALL 3)

`denote2` is `denote` fused with the checker's *own* sort computation:
each binder numeral is the sort `inferTypeCore` + `whnf` produce — the
#100-stage-6 annotate pass resurrected **at the metatheory level**.
It is a definition in the proof development, never run by the binary:
zero runtime cost, and being a *function* it is coherent by
construction — two annotation threads meeting at one term in one
context carry the same numerals, which is what WALL 3 demanded and no
relational invariant could supply.

The stored-constant leaves come from the **canonical annotated
valuation** `acval` (an `EnvS2`-side object fixed at install), so
`denote2` is parametric in it exactly as `denote` is in `cval`; the
erasure law (`denote2_erase`) links the two levels pointwise under the
valuation-side link.

Sort computations live in `sortOfE` (the type's sort: infer, then
whnf to a sort, then evaluate the ground level) and the λ clause's
`lamSortE` (the *body type's* sort — the #152 chain fact, per node
here because the metatheory pays no interning cost).

The load-bearing piece — **the stability metatheorem** (canonicity
survives the checker's own substitutions and reductions, the
sort-level fragment of subject reduction over ground numerals) — is
deliberately NOT in this seal; it is the next one, alone, with its
own STOP condition (a genuine instability counterexample would be a
design finding, not a proof gap).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf
  natLitSupported strLitSupported)

/-- The sort of `e`'s **type**, as the checker computes it: infer,
whnf to a sort, evaluate the ground level. -/
def sortOfE (mode : CheckMode) (env : Env) (φ : Name → Nat)
    (fuel d : Nat) (e : Expr) : Option Nat :=
  match (inferTypeCore mode env fuel d e).toOption with
  | none => none
  | some t =>
    match (whnf mode env fuel d t).toOption with
    | some (.sort ℓ) => some (ℓ.eval φ)
    | _ => none

/-- The λ-body's codomain sort: the sort of the body's *type* — the
#152 chain fact, computed per node. -/
def lamSortE (mode : CheckMode) (env : Env) (φ : Name → Nat)
    (fuel d : Nat) (body : Expr) : Option Nat :=
  match (inferTypeCore mode env fuel d body).toOption with
  | none => none
  | some bt => sortOfE mode env φ fuel d bt

/-- The annotated `Nat`-literal spine (the `natLitT` mirror over the
annotated valuation). -/
def natLitT2 (za sa : AVExpr) : Nat → AVExpr
  | 0 => za
  | n + 1 => .app sa (natLitT2 za sa n)

/-- The annotated character-list spine (the `charListT` mirror). -/
def charListT2 (nilA consA ofNatA za sa : AVExpr) :
    List Char → AVExpr
  | [] => nilA
  | c :: cs =>
    .app (.app consA (.app ofNatA (natLitT2 za sa c.toNat)))
      (charListT2 nilA consA ofNatA za sa cs)

/-- The canonical annotation pass: `denote` with every binder numeral
computed by the checker's own functions and every constant leaf drawn
from the canonical annotated valuation.  Clause for clause the
`denote` recursion (`Setlec/Verify/Denote.lean`), so the two erase
pointwise (`denote2_erase`). -/
def denote2 (mode : CheckMode) (acval : Name → (Name → Nat) → AVExpr)
    (env : Env) (φ : Name → Nat) (fuel : Nat) :
    (d : Nat) → Expr → Option AVExpr
  | _, .sort u => some (.sort (u.eval φ))
  | d, .fvar idx _ _ => some (.bvar (d - 1 - idx))
  | _, .const n us =>
    match env.find? n with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        some (acval n (Level.substFn φ ci.toConstantVal.levelParams us))
      else none
    | none => none
  | d, .forallE n ty body _m =>
    match denote2 mode acval env φ fuel d ty with
    | none => none
    | some ta =>
      match denote2 mode acval env φ fuel (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | none => none
      | some ba =>
        match sortOfE mode env φ fuel d ty,
            sortOfE mode env φ fuel (d + 1)
              (body.instantiate1 (.fvar d n ty)) with
        | some u, some v => some (.pi u v ta ba)
        | _, _ => none
  | d, .lam n ty body _m =>
    match denote2 mode acval env φ fuel d ty with
    | none => none
    | some ta =>
      match denote2 mode acval env φ fuel (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | none => none
      | some ba =>
        match lamSortE mode env φ fuel (d + 1)
            (body.instantiate1 (.fvar d n ty)) with
        | none => none
        | some v => some (.lam v ta ba)
  | d, .app f a =>
    match denote2 mode acval env φ fuel d f,
        denote2 mode acval env φ fuel d a with
    | some fa, some aa => some (.app fa aa)
    | _, _ => none
  | d, .letE n ty val body =>
    match denote2 mode acval env φ fuel d ty,
        denote2 mode acval env φ fuel d val with
    | some ta, some va =>
      match denote2 mode acval env φ fuel (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | none => none
      | some ba => some (.letE ta va ba)
    | _, _ => none
  | d, .proj _ i e =>
    match denote2 mode acval env φ fuel d e with
    | none => none
    | some ea => if i < 2 then some (.proj i ea) else none
  | _, .lit (.natVal n) =>
    if natLitSupported env then
      some (natLitT2 (acval natZeroName (Level.substFn φ [] []))
        (acval natSuccName (Level.substFn φ [] [])) n)
    else none
  | _, .lit (.strVal s) =>
    if strLitSupported env then
      some (.app (acval stringOfListName (Level.substFn φ [] []))
        (charListT2
          (.app (acval listNilName
              (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (.app (acval listConsName
              (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (acval charOfNatName (Level.substFn φ [] []))
          (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] []))
          s.toList))
    else none
  | _, _ => none
termination_by _ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-! ## The erasure law

`denote2` erases to `denote`, pointwise under the valuation link: the
canonical annotation is an annotation *of the denotation*, exactly. -/

/-- The literal spines erase pointwise. -/
theorem natLitT2_erase {za sa : AVExpr} {zv sv : VExpr}
    (hz : za.erase = zv) (hs : sa.erase = sv) :
    ∀ n : Nat, (natLitT2 za sa n).erase = natLitT zv sv n := by
  intro n
  induction n with
  | zero => exact hz
  | succ m ih => simp [natLitT2, natLitT, hs, ih]

end Setlec.SetR.Interp2
