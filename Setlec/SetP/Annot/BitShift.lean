import Setlec.SetP.Annot.BitLemmas
import Setlec.Verify.Shift

/-!
# `denoteP`'s depth shift (task #161, P3.2)

`denote2_shiftFrom`/`denote2_weaken_top` (`Interp2/Step2/Dispatch.lean`)
mirrored for the validated-annotation reading.

**The dropped premise.**  `denote2_shiftFrom` takes `Setlec.EnvWF env`
and uses it in exactly two places — `sortOfE_shiftFrom` in the `∀`
clause, `lamSortE_shiftFrom` in the `λ` clause, the two rewrites that
move a *checker run* across the shift.  `denoteP` runs no checker: its
binder numeral is `pwBit φ mb.pw`, a function of the term's own meta,
and `Expr.shiftFrom` carries metas through unchanged — so the numeral
is literally the same expression on both sides and the clause closes
by the recursion alone.  `EnvWF` therefore has no occurrence left and
is dropped.

`hacl` is kept: it is the *leaf* obligation (stored annotations are
lift-invariant), which the constant and literal clauses need and which
has nothing to do with sorts.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level PropWhen)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AVExpr}

/-- The `Nat`-literal spine is lift-invariant when its two heads are.
A private local copy of `Dispatch.lean`'s helper of the same name,
which is `private` there and so not in scope here. -/
private theorem natLitT2_liftN {za sa : AVExpr} {k : Nat}
    (hz : za.liftN 1 k = za) (hs : sa.liftN 1 k = sa) :
    ∀ n : Nat, (natLitT2 za sa n).liftN 1 k = natLitT2 za sa n := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
    show (AVExpr.app sa (natLitT2 za sa n)).liftN 1 k = _
    rw [AVExpr.liftN_app, hs, ih]
    rfl

/-- Ditto the character-list spine (private local copy, as above). -/
private theorem charListT2_liftN {nilA consA ofNatA za sa : AVExpr}
    {k : Nat} (hn : nilA.liftN 1 k = nilA)
    (hc : consA.liftN 1 k = consA) (ho : ofNatA.liftN 1 k = ofNatA)
    (hz : za.liftN 1 k = za) (hs : sa.liftN 1 k = sa) :
    ∀ cs : List Char,
      (charListT2 nilA consA ofNatA za sa cs).liftN 1 k
        = charListT2 nilA consA ofNatA za sa cs := by
  intro cs
  induction cs with
  | nil => exact hn
  | cons c cs ih =>
    show (AVExpr.app (.app consA (.app ofNatA _)) _).liftN 1 k = _
    rw [AVExpr.liftN_app, AVExpr.liftN_app, AVExpr.liftN_app, hc, ho,
      natLitT2_liftN hz hs, ih]
    rfl

/-- **`denoteP`'s depth shift.**  `denote2_shiftFrom` with the two
sort-run rewrites deleted — see the module docstring for why `EnvWF`
goes with them.

Generalized over the cut `p` for the same reason both ancestors are:
the binder clause compares `denoteP (d+2) (body.instantiate1 (.fvar
(d+1) …))` with `denoteP (d+1) (body.instantiate1 (.fvar d …))`, two
genuinely different expressions related by `Expr.shiftFrom d`. -/
theorem denoteP_shiftFrom
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) {p : Nat} :
    ∀ (e : Expr) (d : Nat), p ≤ d → Expr.WScoped d e →
      denoteP acval env φ (d + 1) (e.shiftFrom p) =
        (denoteP acval env φ d e).map (AVExpr.liftN 1 · (d - p))
  | .bvar i, d, _, _ => by
    have h1 : denoteP acval env φ (d + 1) (.bvar i) = none := by
      rw [denoteP.eq_def]
    have h2 : denoteP acval env φ d (.bvar i) = none := by
      rw [denoteP.eq_def]
    simp [Setlec.Expr.shiftFrom, h1, h2]
  | .sort u, d, _, _ => by
    simp only [Setlec.Expr.shiftFrom, denoteP, Option.map_some]
    rfl
  | .const n us, d, _, _ => by
    simp only [Setlec.Expr.shiftFrom, denoteP]
    cases env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      split
      · simp only [Option.map_some, hacl]
      · rfl
  | .fvar idx n ty, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    have hlt : idx < d := hw.1
    simp only [Setlec.Expr.shiftFrom]
    split
    · next hge =>
      rw [denoteP, denoteP, Option.map_some, AVExpr.liftN_bvar,
        if_pos (show d - 1 - idx < d - p by omega),
        show d + 1 - 1 - (idx + 1) = d - 1 - idx from by omega]
    · next hge =>
      rw [denoteP, denoteP, Option.map_some, AVExpr.liftN_bvar,
        if_neg (show ¬ d - 1 - idx < d - p by omega),
        show d + 1 - 1 - idx = d - 1 - idx + 1 from by omega]
  | .app fe a, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    simp only [Setlec.Expr.shiftFrom, denoteP]
    rw [denoteP_shiftFrom hacl fe d hpd hw.1,
      denoteP_shiftFrom hacl a d hpd hw.2]
    cases denoteP acval env φ d fe <;>
      cases denoteP acval env φ d a <;> rfl
  | .forallE n ty body mb, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    have hwb : Expr.WScoped (d + 1)
        (body.instantiate1 (.fvar d n ty)) :=
      Setlec.Expr.WScoped.instantiate1 hw.1 0 hw.2
    simp only [Setlec.Expr.shiftFrom, denoteP]
    rw [← Setlec.Expr.shiftFrom_instantiate1 hpd body 0,
      denoteP_shiftFrom hacl ty d hpd hw.1,
      denoteP_shiftFrom hacl (body.instantiate1 (.fvar d n ty))
        (d + 1) (by omega) hwb,
      show d + 1 - p = d - p + 1 from by omega]
    cases denoteP acval env φ d ty with
    | none => rfl
    | some ta =>
      cases denoteP acval env φ (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some ba => rfl
  | .lam n ty body mb, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    have hwb : Expr.WScoped (d + 1)
        (body.instantiate1 (.fvar d n ty)) :=
      Setlec.Expr.WScoped.instantiate1 hw.1 0 hw.2
    simp only [Setlec.Expr.shiftFrom, denoteP]
    rw [← Setlec.Expr.shiftFrom_instantiate1 hpd body 0,
      denoteP_shiftFrom hacl ty d hpd hw.1,
      denoteP_shiftFrom hacl (body.instantiate1 (.fvar d n ty))
        (d + 1) (by omega) hwb,
      show d + 1 - p = d - p + 1 from by omega]
    cases denoteP acval env φ d ty with
    | none => rfl
    | some ta =>
      cases denoteP acval env φ (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some ba => rfl
  | .letE n ty val body, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    have hwb : Expr.WScoped (d + 1)
        (body.instantiate1 (.fvar d n ty)) :=
      Setlec.Expr.WScoped.instantiate1 hw.1 0 hw.2.2
    simp only [Setlec.Expr.shiftFrom, denoteP]
    rw [← Setlec.Expr.shiftFrom_instantiate1 hpd body 0,
      denoteP_shiftFrom hacl ty d hpd hw.1,
      denoteP_shiftFrom hacl val d hpd hw.2.1,
      denoteP_shiftFrom hacl (body.instantiate1 (.fvar d n ty))
        (d + 1) (by omega) hwb,
      show d + 1 - p = d - p + 1 from by omega]
    cases denoteP acval env φ d ty with
    | none => rfl
    | some ta =>
      cases denoteP acval env φ d val with
      | none => rfl
      | some va =>
        cases denoteP acval env φ (d + 1)
            (body.instantiate1 (.fvar d n ty)) with
        | none => rfl
        | some ba => rfl
  | .proj sn i e, d, hpd, hw => by
    rw [Setlec.Expr.WScoped] at hw
    simp only [Setlec.Expr.shiftFrom, denoteP]
    rw [denoteP_shiftFrom hacl e d hpd hw]
    cases denoteP acval env φ d e with
    | none => rfl
    | some ea =>
      simp only [Option.map_some]
      cases env.findProj? sn i with
      | none =>
        dsimp only
        split
        · rfl
        · rfl
      | some entry =>
        dsimp only
        split
        · show some (projAV i (AVExpr.liftN 1 ea (d - p)))
            = Option.map (fun x => AVExpr.liftN 1 x (d - p))
              (some (projAV i ea))
          simp only [Option.map_some, projAV_liftN]
        · split
          · rfl
          · rfl
  | .lit (.natVal k), d, _, _ => by
    simp only [Setlec.Expr.shiftFrom, denoteP]
    split
    · simp only [Option.map_some]
      rw [natLitT2_liftN (hacl _ _ _) (hacl _ _ _)]
    · rfl
  | .lit (.strVal s), d, _, _ => by
    simp only [Setlec.Expr.shiftFrom, denoteP]
    split
    · simp only [Option.map_some]
      refine congrArg some ?_
      symm
      rw [AVExpr.liftN_app, hacl,
        charListT2_liftN (by rw [AVExpr.liftN_app, hacl, hacl])
          (by rw [AVExpr.liftN_app, hacl, hacl]) (hacl _ _ _)
          (hacl _ _ _) (hacl _ _ _)]
    · rfl
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Setlec.Expr.sizeB]; omega)
  | (rw [Setlec.Expr.sizeB_instantiate1 _ rfl]
     simp [Setlec.Expr.sizeB]; omega)
  | (simp [Setlec.Expr.sizeB])

/-- **One level of weakening.**  `denote2_weaken_top`'s mirror: a
`d`-scoped term denoted at `d + 1` is its depth-`d` annotation,
lifted.  `EnvWF` goes with the shift it is derived from. -/
theorem denoteP_weaken_top
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) {d : Nat} {e : Expr}
    (hw : Expr.WScoped d e) :
    denoteP acval env φ (d + 1) e
      = (denoteP acval env φ d e).map (AVExpr.liftN 1 · 0) := by
  have h := denoteP_shiftFrom (env := env) (φ := φ) hacl (p := d) e d
    (Nat.le_refl d) hw
  rw [Setlec.Expr.shiftFrom_eq_self hw.fvarsBelow, Nat.sub_self] at h
  exact h

end Setlec.SetR.Interp2
