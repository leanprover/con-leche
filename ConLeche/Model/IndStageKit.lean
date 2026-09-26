module

public import ConLeche.Model.IndSubst

public section

/-!
# The stages' semantic prelude (task #161, IND TIER part 4, step 1)

`teleFitPA_to_chain`: a fit's memberships, read back in chain form
against the tower's context (`teleFitPA_of_tower`'s converse).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Fits -/

/-- **A fit's memberships in chain form**: `teleFitPA_of_tower`'s
converse — argument `n`'s reading inhabits the
tower's `n`-th open domain, read at the chain of the arguments outside
it. -/
theorem teleFitPA_to_chain :
    ∀ (k : Nat) {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R → ∀ {ws : List AnnotTerm} {ρ : Nat → V}
        {rest : AnnotTerm},
      ws.length = k → TeleFitPA V ρ T ws rest →
      ∀ n, n < k →
        interp V ρ (ws.getD n default)
          ∈ˢ interp V (chain V ρ (ws.take n))
            (Γ.getD (k - 1 - n) default) := by
  intro k
  induction k with
  | zero => intro T Γ R h ws ρ rest hlen hfit n hn; exact nomatch hn
  | succ k ihk =>
    intro T Γ R h ws ρ rest hlen hfit n hn
    obtain ⟨u, v, A, B, Γ', rfl, rfl, htail⟩ := h.succ_inv
    match ws, hlen with
    | w :: ws', hlen =>
    have hlen' : ws'.length = k := by simpa using hlen
    have hΓ'len : Γ'.length = k := htail.length
    cases hfit with
    | cons hmem htailFit =>
    match n, hn with
    | 0, _ =>
      rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
          rw [List.getD, List.getElem?_append_right (by omega), hΓ'len]
          simp]
      simpa using hmem
    | n + 1, hn =>
      have hinst := htail.inst w 0
      have h1 := ihk hinst hlen' htailFit n (by omega)
      rw [ctxInstAtAV_getD w 0 Γ' (k - 1 - n) (by omega),
        show 0 + Γ'.length - 1 - (k - 1 - n) = n from by omega,
        interp_inst] at h1
      have htklen : (ws'.take n).length = n := by
        rw [List.length_take]
        omega
      rw [show shiftE n 0 (chain V ρ (ws'.take n)) = ρ from by
          funext j
          show chain V ρ (ws'.take n) (j + n) = ρ j
          rw [chain_ge (by omega), htklen]
          congr 1
          omega,
        show instE n (interp V ρ w) (chain V ρ (ws'.take n))
            = chain V ρ (w :: ws'.take n) from by
          rw [chain_cons_eq_instE, htklen]] at h1
      rw [List.getD_cons_succ,
        show (w :: ws').take (n + 1) = w :: ws'.take n from rfl,
        show (Γ' ++ [A]).getD (k + 1 - 1 - (n + 1)) default
            = Γ'.getD (k - 1 - n) default from by
          rw [List.getD, List.getD,
            List.getElem?_append_left (by omega)]
          congr 2
          omega]
      exact h1

end ConLeche.Model
