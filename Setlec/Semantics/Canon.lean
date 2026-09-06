import Setlec.Semantics.Syntax
import Setlec.Semantics.Tower.TowerLeaf
import Setlec.Verify.Denote
import Setlec.Verify.Knot

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

/-- The uniform projection spellings erase onto each other:
`projAV`'s image is `projNV` (task #175 wiring W3). -/
theorem erase_projAV : ∀ (i : Nat) (ea : AVExpr),
    (projAV i ea).erase = Setlec.TTVerify.projNV i ea.erase
  | 0, _ => rfl
  | i + 1, ea => erase_projAV i (.proj 1 ea)

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
  | d, .forallE n ty body _m => do
    let ta ← denote2 mode acval env φ fuel d ty
    let ba ← denote2 mode acval env φ fuel (d + 1)
      (body.instantiate1 (.fvar d n ty))
    let u ← sortOfE mode env φ fuel d ty
    let v ← sortOfE mode env φ fuel (d + 1)
      (body.instantiate1 (.fvar d n ty))
    some (.pi u v ta ba)
  | d, .lam n ty body _m => do
    let ta ← denote2 mode acval env φ fuel d ty
    let ba ← denote2 mode acval env φ fuel (d + 1)
      (body.instantiate1 (.fvar d n ty))
    let v ← lamSortE mode env φ fuel (d + 1)
      (body.instantiate1 (.fvar d n ty))
    some (.lam v ta ba)
  | d, .app f a => do
    let fa ← denote2 mode acval env φ fuel d f
    let aa ← denote2 mode acval env φ fuel d a
    some (.app fa aa)
  | d, .letE n ty val body => do
    let ta ← denote2 mode acval env φ fuel d ty
    let va ← denote2 mode acval env φ fuel d val
    let ba ← denote2 mode acval env φ fuel (d + 1)
      (body.instantiate1 (.fvar d n ty))
    some (.letE ta va ba)
  | d, .proj sn i e => do
    let ea ← denote2 mode acval env φ fuel d e
    -- the entry-kind branch (task #175 wiring W3), clause-parallel
    -- with `denote` and `denoteP`
    match env.findProj? sn i with
    | some entry =>
      if entry.tower then some (projAV i ea)
      else if i < 2 then some (.proj i ea) else none
    | none => if i < 2 then some (.proj i ea) else none
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

theorem charListT2_erase {nilA consA ofNatA za sa : AVExpr}
    {nilV consV ofNatV zv sv : VExpr}
    (h1 : nilA.erase = nilV) (h2 : consA.erase = consV)
    (h3 : ofNatA.erase = ofNatV) (hz : za.erase = zv)
    (hs : sa.erase = sv) :
    ∀ cs : List Char,
      (charListT2 nilA consA ofNatA za sa cs).erase
        = charListT nilV consV ofNatV zv sv cs := by
  intro cs
  induction cs with
  | nil => exact h1
  | cons c cs ih =>
    simp [charListT2, charListT, h2, h3, ih, natLitT2_erase hz hs]

/-- **The erasure law**: the canonical annotation is an annotation of
the denotation, exactly (no ζ slack — `denote2`'s `letE` clause is
structural). -/
theorem denote2_erase {mode : CheckMode}
    {acval : Name → (Name → Nat) → AVExpr} {cval : TConstVal}
    {env : Env} {φ : Name → Nat} {fuel : Nat}
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ) :
    ∀ (d : Nat) (e : Expr) {ea : AVExpr},
      denote2 mode acval env φ fuel d e = some ea →
      denote cval env φ d e = some ea.erase := by
  intro d e
  induction d, e using denote2.induct (env := env) with
  | case1 d u =>
    intro ea h
    rw [denote2] at h
    obtain rfl := Option.some.inj h
    rw [denote_sort]
    rfl
  | case2 d idx nm ty =>
    intro ea h
    rw [denote2] at h
    obtain rfl := Option.some.inj h
    rw [denote_fvar]
    rfl
  | case3 d n us ci hf hlen =>
    intro ea h
    rw [denote2, hf] at h
    dsimp only at h
    rw [if_pos hlen] at h
    obtain rfl := Option.some.inj h
    rw [denote_const, hf]
    dsimp only
    rw [if_pos hlen, hlink]
  | case4 d n us ci hf hlen =>
    intro ea h
    rw [denote2, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ea h
    rw [denote2, hf] at h
    exact nomatch h
  | case6 d n ty body m ihty ihbody =>
    intro ea h
    rw [denote2] at h
    rcases hta : denote2 mode acval env φ fuel d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denote2 mode acval env φ fuel (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    rcases hu : sortOfE mode env φ fuel d ty with _ | u
    · rw [hu] at h; exact nomatch h
    rw [hu] at h
    rcases hv : sortOfE mode env φ fuel (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | v
    · rw [hv] at h; exact nomatch h
    rw [hv] at h
    obtain rfl := Option.some.inj h
    rw [denote_forallE, ihty hta, ihbody hba]
    rfl
  | case7 d n ty body m ihty ihbody =>
    intro ea h
    rw [denote2] at h
    rcases hta : denote2 mode acval env φ fuel d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denote2 mode acval env φ fuel (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    rcases hv : lamSortE mode env φ fuel (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | v
    · rw [hv] at h; exact nomatch h
    rw [hv] at h
    obtain rfl := Option.some.inj h
    rw [denote_lam, ihty hta, ihbody hba]
    rfl
  | case8 d f a ihf iha =>
    intro ea h
    rw [denote2] at h
    rcases hfa : denote2 mode acval env φ fuel d f with _ | fa
    · rw [hfa] at h; exact nomatch h
    rw [hfa] at h
    rcases haa : denote2 mode acval env φ fuel d a with _ | aa
    · rw [haa] at h; exact nomatch h
    rw [haa] at h
    obtain rfl := Option.some.inj h
    rw [denote_app, ihf hfa, iha haa]
    rfl
  | case9 d n ty val body ihty ihval ihbody =>
    intro ea h
    rw [denote2] at h
    rcases hta : denote2 mode acval env φ fuel d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hva : denote2 mode acval env φ fuel d val with _ | va
    · rw [hva] at h; exact nomatch h
    rw [hva] at h
    rcases hba : denote2 mode acval env φ fuel (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    obtain rfl := Option.some.inj h
    rw [denote_letE, ihty hta, ihval hva, ihbody hba]
    rfl
  | case10 d sn i e ihe =>
    intro ea h
    rw [denote2] at h
    rcases hea : denote2 mode acval env φ fuel d e with _ | ea'
    · rw [hea] at h; exact nomatch h
    rw [hea] at h
    replace h : (match env.findProj? sn i with
        | some entry => if entry.tower = true then some (projAV i ea')
            else if i < 2 then some (AVExpr.proj i ea') else none
        | none => if i < 2 then some (AVExpr.proj i ea') else none)
          = some ea := h
    rw [denote_proj, ihe hea]
    dsimp only
    cases hfp : env.findProj? sn i with
    | some entry =>
      rw [hfp] at h
      dsimp only at h ⊢
      by_cases htw : entry.tower = true
      · rw [if_pos htw] at h
        obtain rfl := Option.some.inj h
        rw [if_pos htw, erase_projAV]
      · rw [if_neg htw] at h ⊢
        by_cases hi : i < 2
        · rw [if_pos hi] at h
          obtain rfl := Option.some.inj h
          rw [if_pos hi]
          rfl
        · rw [if_neg hi] at h
          exact nomatch h
    | none =>
      rw [hfp] at h
      dsimp only at h ⊢
      by_cases hi : i < 2
      · rw [if_pos hi] at h
        obtain rfl := Option.some.inj h
        rw [if_pos hi]
        rfl
      · rw [if_neg hi] at h
        exact nomatch h
  | case11 d n hsup =>
    intro ea h
    rw [denote2, if_pos hsup] at h
    obtain rfl := Option.some.inj h
    rw [denote_natLit, if_pos hsup,
      natLitT2_erase (hlink _ _) (hlink _ _)]
  | case12 d n hsup =>
    intro ea h
    rw [denote2, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ea h
    rw [denote2, if_pos hsup] at h
    obtain rfl := Option.some.inj h
    rw [denote_strLit, if_pos hsup]
    refine congrArg some ?_ |>.symm
    show VExpr.app _ _ = _
    rw [Setlec.TTVerify.strLitT]
    congr 1
    · exact hlink _ _
    · refine charListT2_erase ?_ ?_ (hlink _ _) (hlink _ _)
        (hlink _ _) s.toList
      · show VExpr.app ((acval _ _).erase) ((acval _ _).erase) = _
        rw [hlink, hlink]
      · show VExpr.app ((acval _ _).erase) ((acval _ _).erase) = _
        rw [hlink, hlink]
  | case14 d s hsup =>
    intro ea h
    rw [denote2, if_neg hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea h
    cases x with
    | bvar i =>
      rw [denote2.eq_def] at h
      exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i nm ty => exact absurd rfl (hfv i nm ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE n ty b m => exact absurd rfl (hpi n ty b m)
    | lam n ty b m => exact absurd rfl (hlam n ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE n ty v b => exact absurd rfl (hlet n ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

end Setlec.SetR.Interp2
