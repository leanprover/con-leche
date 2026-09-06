import Setlec.Semantics.Canon
import Setlec.Semantics.Tower.TowerLeaf
import Setlec.Verify.PropWhen

/-!
# `denoteP` — the validated-annotation reading (task #161, P3)

`denoteP` is the pw-driven sibling of `denote2` (`Annot/Canon.lean`):
clause for clause the same recursion, with every binder numeral read
off the term's **own validated annotation** — `pwBit φ m.pw`, the
datum's zero bit at the ground valuation — instead of `denote2`'s
`sortOfE`/`lamSortE` checker runs.

The consequences are the P3 pivot in miniature:

* **No fuel, no mode.**  `denoteP` runs no checker function, so the
  parameters that existed only to feed `sortOfE` are gone, and every
  lemma about it is fuel-slack-free.
* **The level crossing is algebra.**  Where `Denote2InstLevels` is a
  residue riding two *open* checker metatheorems
  (`SortOfEInstLevels`/`LamSortEInstLevels`, "inference and head
  normalisation commute with level instantiation" — false as stated,
  repaired only under `EnvWF`, still unproven), `denoteP`'s crossing
  is `PropWhen.holds_substPW` at each binder: **proved outright**
  (`Step2/BitLevels.lean`, `denotePInstLevels`).
* **The bit is canonical.**  `pwBit` lands in `{0, 1}`, so two data
  that agree on zero-ness produce *equal* numerals — the
  `piR_zero_agree`/`lamR_zero_agree` step is `rfl`-shaped where the
  canonical lane needed sort-agreement residues (`BinderSortAgree2`,
  residue 9): the checker's own P2 validation sites
  (`(defeq-forall)`/`(defeq-lam)`/`(eta)`) compare the data with
  `equiv` exactly where the run lemmas open two annotations at one
  index.

**The `pi` `u`-slot.**  `AVExpr.pi` carries a domain-sort numeral `u`
that `interp2` and `AnnotOk2` never read (`interp2_pi` matches `.pi _
v A B`; `DefEq`'s congruence rows hold at `u ≠ u'`).  Amendment 1
deliberately dropped the domain datum from the input language, so
`denoteP` fills the slot with `0`.  If any consumer downstream turns
out to *read* `u`, that is a named finding against the prop-only
amendment, not a plumbing gap.

API discipline (task #161 ruling): `PropWhen` is consumed only through
`holds` and the named battery laws — `pwBit` is `holds` composed with
a two-point test, and every lemma below factors through
`holds_eq_of_equiv` / `holds_of_equiv_zeronessOf` / `holds_substPW`.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify
open Setlec.Semantics (AVExpr)
open Setlec (CheckMode Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

/-! ## The regime bit -/

/-- The regime numeral a validated datum contributes at a ground
valuation: `0` (the squash regime) exactly when the datum holds —
"the codomain is a proposition here" — and `1` otherwise.  The value
`1` is arbitrary; `interp2` reads binder numerals only through the
`v = 0` test (`piR_zero_agree`/`lamR_zero_agree`). -/
def pwBit (φ : Name → Nat) (pw : PropWhen) : Nat :=
  if pw.holds φ then 0 else 1

@[simp] theorem pwBit_eq_zero_iff {φ : Name → Nat} {pw : PropWhen} :
    pwBit φ pw = 0 ↔ pw.holds φ = true := by
  unfold pwBit; split <;> simp_all

theorem pwBit_ne_zero_iff {φ : Name → Nat} {pw : PropWhen} :
    pwBit φ pw ≠ 0 ↔ pw.holds φ = false := by
  rw [Ne, pwBit_eq_zero_iff]
  simp

/-! ### The io gate's exactness (task #161 bucket 2)

The kernel's licensed check-skips test `PropWhen.isNever` — the one
thing about a datum a kernel can decide without a valuation.  The
sealed claims split on `pwBit φ pw = 0` at the *ambient* valuation.
The two lemmas below are the receipt that the gate's condition is the
**∀-`φ` uniform version of the claims' positive branch, exactly** —
sound (a gated site is positive at every valuation, so the claim's
cert-free arm applies) and complete (no other datum is positive at
every valuation, so the gate cannot be widened without leaving the
licensed branch).

Landed at stage 1 on `agent/bucket2-s1` (commit `0c865695`) and
re-landed here verbatim: the exactness is a fact about the datum, not
about which site reads it, so it serves the io lane's application
clause (`inferBodyIO`) and any future β-cert gate alike. -/

/-- **Soundness of the gate's condition**: a `never` datum is positive
at every valuation. -/
theorem pwBit_ne_zero_of_isNever {pw : PropWhen}
    (h : Setlec.PropWhen.isNever pw = true) (φ : Name → Nat) :
    pwBit φ pw ≠ 0 := by
  cases pw with
  | never => rw [pwBit_ne_zero_iff]; rfl
  | ifAllZero ps => exact nomatch h

/-- **Exactness of the gate's condition**: `never` is *the* datum that
is positive at every valuation — an `ifAllZero` datum lands in the
squash regime at the all-zero valuation, where the certificate is
consumed and the skip would be unlicensed. -/
theorem isNever_iff_forall_pwBit_ne_zero {pw : PropWhen} :
    Setlec.PropWhen.isNever pw = true ↔ ∀ φ : Name → Nat, pwBit φ pw ≠ 0 := by
  constructor
  · exact pwBit_ne_zero_of_isNever
  · intro h
    cases pw with
    | never => rfl
    | ifAllZero ps =>
      exact absurd (pwBit_eq_zero_iff.mpr
        (by simp [Setlec.PropWhen.holds])) (h (fun _ => 0))

/-- Checker-compared data (`PropWhen.equiv`, the P2 validation and
defeq sites) contribute **equal** numerals — not merely zero-agreeing
ones. -/
theorem pwBit_eq_of_equiv {p q : PropWhen}
    (h : PropWhen.equiv p q = true) (φ : Name → Nat) :
    pwBit φ p = pwBit φ q := by
  unfold pwBit
  rw [Setlec.PropWhen.holds_eq_of_equiv h φ]

/-- **The establishment reading**: a datum the checker validated
against a computed codomain sort (`(zeronessOf v).equiv m.pw`, the run
inversions' conjunct) contributes the sort's true zero bit. -/
theorem pwBit_of_equiv_zeronessOf {v : Level} {pw : PropWhen}
    (h : PropWhen.equiv (Level.zeronessOf v) pw = true) (φ : Name → Nat) :
    (pwBit φ pw = 0 ↔ Level.eval φ v = 0) := by
  rw [pwBit_eq_zero_iff, Setlec.PropWhen.holds_of_equiv_zeronessOf h φ]
  simp

/-- **The crossing reading**: the instantiated datum's bit at `φ` is
the datum's bit at the composed valuation — `denotePInstLevels`'
binder step. -/
theorem pwBit_substPW (φ : Name → Nat) (ks : List Name)
    (vs : List Level) (pw : PropWhen) :
    pwBit φ (Level.substPW ks vs pw) = pwBit (Level.substFn φ ks vs) pw := by
  unfold pwBit
  rw [Setlec.Level.holds_substPW]

/-! ## The reading -/

/-- The validated-annotation reading: `denote2`'s recursion with every
binder numeral read off the term's own meta (`pwBit φ m.pw`) — no
checker runs, no fuel, no mode.  See the module docstring for the
`pi` `u`-slot convention. -/
def denoteP (acval : Name → (Name → Nat) → AVExpr)
    (env : Env) (φ : Name → Nat) :
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
  | d, .forallE n ty body m => do
    let ta ← denoteP acval env φ d ty
    let ba ← denoteP acval env φ (d + 1)
      (body.instantiate1 (.fvar d n ty))
    some (.pi 0 (pwBit φ m.pw) ta ba)
  | d, .lam n ty body m => do
    let ta ← denoteP acval env φ d ty
    let ba ← denoteP acval env φ (d + 1)
      (body.instantiate1 (.fvar d n ty))
    some (.lam (pwBit φ m.pw) ta ba)
  | d, .app f a => do
    let fa ← denoteP acval env φ d f
    let aa ← denoteP acval env φ d a
    some (.app fa aa)
  | d, .letE n ty val body => do
    let ta ← denoteP acval env φ d ty
    let va ← denoteP acval env φ d val
    let ba ← denoteP acval env φ (d + 1)
      (body.instantiate1 (.fvar d n ty))
    some (.letE ta va ba)
  | d, .proj sn i e => do
    let ea ← denoteP acval env φ d e
    -- the entry-kind branch (task #175 wiring W3): a tower-backed
    -- entry reads field `i` by the uniform iterated spelling
    -- (`projAV`, whose `AnnotOk2`/substitution batteries are the
    -- introduction machinery's); the pair/absent side is the pre-W3
    -- clause
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

`denoteP` erases to `denote` exactly as `denote2` does
(`denote2_erase`): the annotations differ between the two readings,
the denotation does not. -/

/-- The validated-annotation reading is an annotation of the
denotation, exactly. -/
theorem denoteP_erase {acval : Name → (Name → Nat) → AVExpr}
    {cval : TConstVal} {env : Env} {φ : Name → Nat}
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ) :
    ∀ (d : Nat) (e : Expr) {ea : AVExpr},
      denoteP acval env φ d e = some ea →
      denote cval env φ d e = some ea.erase := by
  intro d e
  induction d, e using denoteP.induct (env := env) with
  | case1 d u =>
    intro ea h
    rw [denoteP] at h
    obtain rfl := Option.some.inj h
    rw [denote_sort]
    rfl
  | case2 d idx nm ty =>
    intro ea h
    rw [denoteP] at h
    obtain rfl := Option.some.inj h
    rw [denote_fvar]
    rfl
  | case3 d n us ci hf hlen =>
    intro ea h
    rw [denoteP, hf] at h
    dsimp only at h
    rw [if_pos hlen] at h
    obtain rfl := Option.some.inj h
    rw [denote_const, hf]
    dsimp only
    rw [if_pos hlen, hlink]
  | case4 d n us ci hf hlen =>
    intro ea h
    rw [denoteP, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ea h
    rw [denoteP, hf] at h
    exact nomatch h
  | case6 d n ty body mb ihty ihbody =>
    intro ea h
    rw [denoteP] at h
    rcases hta : denoteP acval env φ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denoteP acval env φ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    obtain rfl := Option.some.inj h
    rw [denote_forallE, ihty hta, ihbody hba]
    rfl
  | case7 d n ty body mb ihty ihbody =>
    intro ea h
    rw [denoteP] at h
    rcases hta : denoteP acval env φ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denoteP acval env φ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    obtain rfl := Option.some.inj h
    rw [denote_lam, ihty hta, ihbody hba]
    rfl
  | case8 d fe a ihf iha =>
    intro ea h
    rw [denoteP] at h
    rcases hfa : denoteP acval env φ d fe with _ | fa
    · rw [hfa] at h; exact nomatch h
    rw [hfa] at h
    rcases haa : denoteP acval env φ d a with _ | aa
    · rw [haa] at h; exact nomatch h
    rw [haa] at h
    obtain rfl := Option.some.inj h
    rw [denote_app, ihf hfa, iha haa]
    rfl
  | case9 d n ty val body ihty ihval ihbody =>
    intro ea h
    rw [denoteP] at h
    rcases hta : denoteP acval env φ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hva : denoteP acval env φ d val with _ | va
    · rw [hva] at h; exact nomatch h
    rw [hva] at h
    rcases hba : denoteP acval env φ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    obtain rfl := Option.some.inj h
    rw [denote_letE, ihty hta, ihval hva, ihbody hba]
    rfl
  | case10 d sn i e ihe =>
    intro ea h
    rw [denoteP] at h
    rcases hea : denoteP acval env φ d e with _ | ea'
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
  | case11 d k hsup =>
    intro ea h
    rw [denoteP, if_pos hsup] at h
    obtain rfl := Option.some.inj h
    rw [denote_natLit, if_pos hsup,
      natLitT2_erase (hlink _ _) (hlink _ _)]
  | case12 d k hsup =>
    intro ea h
    rw [denoteP, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ea h
    rw [denoteP, if_pos hsup] at h
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
    rw [denoteP, if_neg hsup] at h
    exact nomatch h
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea h
    cases x with
    | bvar i => rw [denoteP.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hxs u)
    | fvar i nm ty => exact absurd rfl (hfv i nm ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE n ty b mb => exact absurd rfl (hpi n ty b mb)
    | lam n ty b mb => exact absurd rfl (hlam n ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE n ty v b => exact absurd rfl (hlet n ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

end Setlec.SetP
