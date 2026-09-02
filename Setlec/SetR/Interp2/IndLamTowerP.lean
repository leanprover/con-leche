import Setlec.SetR.Interp2.IndReductP

/-!
# The λ-tower descent, at the reading (task #161, IND TIER part 5)

`lamTowerStepS`'s transpose, and the piece that turns the rule's own
right-hand-side grading into the *applied* form's: applying a read
λ-tower along readings that inhabit its layer domains walks the tower
by β — each partial application **is** the next layer's `.lam` at the
chain — and assembles the application's hereditary grading, each `.app`
package by `lamR_mem`.

**One shape delta from v1, and it is forced by the bits.**  v1's value
half is unconditional, because `app_lamC` needs only domain
membership.  `app_lamR` needs the *fibres* as well (at `v = 0` a
product is a truth value, so β has to know the codomain is one), and
the fibres come from `AnnotOk2`'s `.lam` clause — so at P the value
half is under the tower's grading too.  That costs nothing where it is
used: the transport has the grading in hand by construction, and the
reduct stage consumes both halves together.

**Part-9 generalization (kit repair).**  The `hokws` premise
(`∀ w ∈ ws, AnnotOkP V ρ w`) was a *premise* of the whole conclusion,
but only the fourth component uses it: the value equality and the
residual's grading run on the tower's own grading alone.  The
projection bottom needs the value half **unconditionally** (its first
conclusion carries no annotation hypotheses), so `hokws` now guards
only the fourth conjunct — v1's own shape (`lamTowerStepS`).  Strictly
more general; the one call site (`annotTransportP`) applies it.

The other delta is cosmetic: the tower is a `LamTeleP` relation rather
than a `lamCtx` constructor (see `IndTowerReadP.lean`), so the residual
is produced existentially instead of by `List.take` on a constructor
argument.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]

/-- An application spine grows at the right. -/
theorem AVExpr.mkAppN_snoc :
    ∀ (as : List AVExpr) (f a : AVExpr),
      AVExpr.mkAppN f (as ++ [a]) = .app (AVExpr.mkAppN f as) a := by
  intro as
  induction as with
  | nil => intro f a; rfl
  | cons x xs ih => intro f a; exact ih (.app f x) a

/-- The chain grows at the *inside* when the spine grows at the right
(`chainE_snoc`): the last argument is the innermost binding. -/
theorem chainP_snoc (ρ : Nat → V) (ws : List AVExpr) (w : AVExpr) :
    chainP V ρ (ws ++ [w]) = cons (interp2 V ρ w) (chainP V ρ ws) := by
  have hlen : (ws ++ [w]).length = ws.length + 1 := by simp
  funext i
  cases i with
  | zero =>
    rw [chainP_lt (by rw [hlen]; omega), hlen,
      show ws.length + 1 - 1 - 0 = ws.length from by omega, List.getD,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  | succ j =>
    rw [cons_succ]
    by_cases hj : j < ws.length
    · rw [chainP_lt (by rw [hlen]; omega), chainP_lt hj, hlen,
        show ws.length + 1 - 1 - (j + 1) = ws.length - 1 - j from by
          omega,
        List.getD, List.getD, List.getElem?_append_left (by omega)]
    · rw [chainP_ge (by rw [hlen]; omega), chainP_ge (by omega), hlen]
      congr 1
      omega

set_option maxHeartbeats 3200000 in
/-- **The λ-tower descent, at the reading** (`lamTowerStepS`). -/
theorem lamTowerStepP :
    ∀ (n : Nat) {K : Nat}, n ≤ K →
      ∀ {L C : AVExpr} {Γl : List AVExpr},
        LamTeleP K L Γl C →
        ∀ {ws : List AVExpr} {ρ : Nat → V}, ws.length = K →
        (∀ k, k < K → interp2 V ρ (ws.getD k default)
          ∈ˢ interp2 V (chainP V ρ (ws.take k))
              (Γl.getD (K - 1 - k) default)) →
        AnnotOkP V ρ L →
        ∃ L' : AVExpr,
          LamTeleP (K - n) L' (Γl.take (K - n)) C ∧
          interp2 V ρ (AVExpr.mkAppN L (ws.take n))
            = interp2 V (chainP V ρ (ws.take n)) L' ∧
          AnnotOkP V (chainP V ρ (ws.take n)) L' ∧
          ((∀ w ∈ ws, AnnotOkP V ρ w) →
            AnnotOkP V ρ (AVExpr.mkAppN L (ws.take n))) := by
  intro n
  induction n with
  | zero =>
    intro K hn L C Γl htele ws ρ hw hmem hokL
    have hΓlen : Γl.length = K := htele.length
    refine ⟨L, ?_, ?_, ?_, ?_⟩
    · rw [Nat.sub_zero, List.take_of_length_le (by omega)]
      exact htele
    · rw [List.take_zero, chainP_nil]
      rfl
    · rw [List.take_zero, chainP_nil]
      exact hokL
    · intro _
      rw [List.take_zero]
      exact hokL
  | succ n ih =>
    intro K hn L C Γl htele ws ρ hw hmem hokL
    have hΓlen : Γl.length = K := htele.length
    have hnK : n < K := by omega
    obtain ⟨L', htele', hval', hokL', hokApp'⟩ :=
      ih (by omega) htele hw hmem hokL
    -- the residual tower exposes its head λ
    have hKn : K - n = (K - (n + 1)) + 1 := by omega
    rw [hKn] at htele'
    obtain ⟨v, A, B, Γ'', hL'eq, hΓ''eq, htele''⟩ := htele'.succ_inv
    have hΓ''len : Γ''.length = K - (n + 1) := htele''.length
    have htklen : (Γl.take ((K - (n + 1)) + 1)).length
        = (K - (n + 1)) + 1 := by
      rw [List.length_take, hΓlen]
      omega
    -- the head domain is the tower's `K - 1 - n` slot
    have hAeq : A = Γl.getD (K - 1 - n) default := by
      have h1 : (Γ'' ++ [A]).getD Γ''.length default = A := by
        rw [List.getD, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self]
        rfl
      have h2 : (Γl.take ((K - (n + 1)) + 1)).getD (K - (n + 1)) default
          = Γl.getD (K - (n + 1)) default := by
        rw [List.getD, List.getD, List.getElem?_take_of_lt (by omega)]
      rw [show K - 1 - n = K - (n + 1) from by omega, ← h2, hΓ''eq,
        ← hΓ''len, h1]
    have hΓ''take : Γ'' = Γl.take (K - (n + 1)) := by
      have h1 : (Γ'' ++ [A]).take Γ''.length = Γ'' := by
        rw [List.take_left]
      rw [← h1, hΓ''len, ← hΓ''eq, List.take_take,
        show min (K - (n + 1)) ((K - (n + 1)) + 1) = K - (n + 1) from by
          omega]
    -- the spine and the chain grow at the right
    have hwn : ws[n]? = some (ws.getD n default) := by
      rcases hx : ws[n]? with _ | x
      · rw [List.getElem?_eq_none_iff, hw] at hx
        omega
      · rw [List.getD, hx]
        rfl
    have htk : ws.take (n + 1) = ws.take n ++ [ws.getD n default] := by
      rw [List.take_add_one, hwn]
      rfl
    have hmemn := hmem n hnK
    rw [← hAeq] at hmemn
    -- the head λ's fibres, from its grading
    subst hL'eq
    have hfib : ∃ Bf : V → V,
        (∀ x, x ∈ˢ interp2 V (chainP V ρ (ws.take n)) A →
          interp2 V (cons x (chainP V ρ (ws.take n))) B ∈ˢ Bf x) ∧
        (v = 0 → ∀ x, x ∈ˢ interp2 V (chainP V ρ (ws.take n)) A →
          Bf x ∈ˢ (univZero : V)) :=
      ((AnnotOk2_lam V (chainP V ρ (ws.take n)) v A B) ▸ hokL'.1).2.2
    obtain ⟨Bf, hBf, hBf0⟩ := hfib
    have hokB : ∀ x, x ∈ˢ interp2 V (chainP V ρ (ws.take n)) A →
        AnnotOkP V (cons x (chainP V ρ (ws.take n))) B := by
      intro x hx
      exact ⟨((AnnotOk2_lam V (chainP V ρ (ws.take n)) v A B)
          ▸ hokL'.1).2.1 x hx,
        ((AnnotValidV_lam V (chainP V ρ (ws.take n)) v A B)
          ▸ hokL'.2).2 x hx⟩
    -- the value: β at the head layer
    have hvalStep : interp2 V ρ (AVExpr.mkAppN L (ws.take (n + 1)))
        = interp2 V (chainP V ρ (ws.take (n + 1))) B := by
      rw [htk, AVExpr.mkAppN_snoc, interp2_app, hval', interp2_lam,
        app_lamR hmemn hBf hBf0, chainP_snoc]
    refine ⟨B, ?_, hvalStep, ?_, ?_⟩
    · rw [← hΓ''take]
      exact htele''
    · rw [htk, chainP_snoc]
      exact hokB _ hmemn
    · intro hokws
      rw [htk, AVExpr.mkAppN_snoc]
      refine ⟨?_, ?_⟩
      · rw [AnnotOk2_app]
        refine ⟨(hokApp' hokws).1, (hokws _ (List.mem_of_getElem? hwn)).1,
          v, interp2 V (chainP V ρ (ws.take n)) A, Bf, ?_, hmemn, hBf0⟩
        rw [hval', interp2_lam]
        exact lamR_mem hBf
      · rw [AnnotValidV_app]
        exact ⟨(hokApp' hokws).2, (hokws _ (List.mem_of_getElem? hwn)).2⟩

end Setlec.SetR.Interp2
