import Setlec.SetR.Interp2.IndZipperP
import Setlec.SetR.Interp2.Step2.StuckP

/-!
# The point stage's kit (task #161, IND TIER part 5)

The four small facts `pointS` reads that part 3's frame kit and part
4's stage kit left out, because they belong to the *spine* rather than
to the frame or to the fit: a read spine's pointwise lookup, `instSeq`
over an application, injectivity of `mkAppN` at equal arities, and the
determinacy of a `TeleFitPA` residual.

All four are `VExpr`-level facts one currency over and are transposed
verbatim — they mention no `interp2`, no bit, and no environment
except through `TeleFitPA`.  `AVExpr.mkAppN_inj` is the one that
carries the point stage's weight: the crossed constructor residual and
the fired index pin are both applications of the *same* arity, and the
stage reads their arguments off pointwise.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AVExpr}

/-- Pointwise reading of a read spine (`denoteSpine_getElem?'`). -/
theorem denoteSpineP_getElem?' {d : Nat} :
    ∀ {as : List Expr} {vs : List AVExpr},
      DenoteSpineP acval env φ d as vs →
      ∀ (i : Nat) (x : Expr), as[i]? = some x →
        ∃ v, vs[i]? = some v ∧ denoteP acval env φ d x = some v := by
  intro as vs h
  induction h with
  | nil => intro i x hx; exact nomatch hx
  | @cons a v as' vs' ha _ ih =>
    intro i x hx
    cases i with
    | zero =>
      obtain rfl : a = x := Option.some.inj hx
      exact ⟨v, rfl, ha⟩
    | succ j =>
      obtain ⟨v', hv', hd⟩ := ih j x (by simpa using hx)
      exact ⟨v', by simpa using hv', hd⟩

/-- Spine instantiation distributes over one application node. -/
theorem instSeqP_app : ∀ (as : List AVExpr) (t : Nat) (f a : AVExpr),
    AVExpr.instSeq as t (.app f a)
      = .app (AVExpr.instSeq as t f) (AVExpr.instSeq as t a) := by
  intro as
  induction as with
  | nil => intro t f a; rfl
  | cons b bs ih =>
    intro t f a
    rw [AVExpr.instSeq_cons, AVExpr.instSeq_cons, AVExpr.instSeq_cons,
      Setlec.SetR.AVExpr.inst_app, ih]

/-- Spine instantiation distributes over an application
(`instSeq_mkAppN`). -/
theorem instSeqP_mkAppN : ∀ (as : List AVExpr) (t : Nat) (f : AVExpr)
    (args : List AVExpr),
    AVExpr.instSeq as t (AVExpr.mkAppN f args) =
      AVExpr.mkAppN (AVExpr.instSeq as t f)
        (args.map (AVExpr.instSeq as t ·)) := by
  intro as t f args
  induction args generalizing f with
  | nil => rfl
  | cons a args ih =>
    rw [Setlec.SetR.AVExpr.mkAppN_cons, ih, instSeqP_app]
    rfl

/-- Applications of equal arity are equal only at equal heads and
equal argument lists (`VExpr.mkAppN_inj`). -/
theorem AVExpr.mkAppN_inj :
    ∀ {as bs : List AVExpr} {f g : AVExpr},
      AVExpr.mkAppN f as = AVExpr.mkAppN g bs → as.length = bs.length →
      f = g ∧ as = bs := by
  intro as
  induction as with
  | nil =>
    intro bs f g h hlen
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact ⟨h, rfl⟩
  | cons a as ih =>
    intro bs f g h hlen
    cases bs with
    | nil => exact nomatch hlen
    | cons b bs =>
      rw [Setlec.SetR.AVExpr.mkAppN_cons,
        Setlec.SetR.AVExpr.mkAppN_cons] at h
      obtain ⟨h1, rfl⟩ := ih h (by simpa using hlen)
      injection h1 with h2 h3
      exact ⟨h2, by rw [h3]⟩

/-- A `TeleFitPA` residual is determined: the tower body,
spine-instantiated (`teleFitV_rest_eq`). -/
theorem teleFitPA_rest_eq :
    ∀ (k : Nat) {T : AVExpr} {Γ : List AVExpr} {R : AVExpr},
      PiTeleP k T Γ R → ∀ {ws : List AVExpr} {ρ : Nat → V}
        {rest : AVExpr},
      ws.length = k → TeleFitPA V ρ T ws rest →
      rest = AVExpr.instSeq ws (k - 1) R := by
  intro k
  induction k with
  | zero =>
    intro T Γ R h ws ρ rest hlen hfit
    cases h
    obtain rfl := List.length_eq_zero_iff.mp hlen
    cases hfit
    rfl
  | succ k ihk =>
    intro T Γ R h ws ρ rest hlen hfit
    obtain ⟨u, v, A, B, Γ', rfl, rfl, htail⟩ := h.succ_inv
    match ws, hlen with
    | w :: ws', hlen =>
    have hlen' : ws'.length = k := by simpa using hlen
    cases hfit with
    | cons hmem htailFit =>
      have hr := ihk (htail.inst w 0) hlen' htailFit
      rw [hr, AVExpr.instSeq_cons,
        show k + 1 - 1 - 1 = k - 1 from by omega, Nat.add_sub_cancel,
        Nat.zero_add]

end Setlec.SetR.Interp2
