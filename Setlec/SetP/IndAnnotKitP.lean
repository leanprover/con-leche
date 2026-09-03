import Setlec.SetP.IndLamTowerP

/-!
# The transport's two kit pieces (task #161, IND TIER part 5)

`annotMemS`'s two inputs that the frame kit did not have: the λ-tower's
slot grading, and the *walked* form of `CtxOkP`.

**The second is a finding, and it is a saving.**  v1 needs a separate
`ctxOkR_of_walked_openers` because `CtxOkR`'s per-leaf obligation is an
`Infer.bvar` derivation onto `DefEq.refl` — a *syntactic* identity of
the leaf's annotation with the context entry — so a walk that only
makes them `DefEq` needs its own constructor with slack.  `CtxOkP`'s
obligation is already an `interp2` **equation** (`Claims2P.lean:79-81`),
i.e. the slack is built into the P currency: `ctxOkP_of_walked_openers`
is `ctxOkP_of_openers` with the equation supplied instead of proved by
`interp2_liftN`, and nothing else changes.

That is why the transport's lam walk can fire at the **statement**
frame's own context, exactly as v1's does, even though its subjects'
leaves are the *public* frame's openers: the per-position
identification is precisely the equation `CtxOkP` asks for.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]

/-- **A λ-tower's domains are graded along a satisfying environment**
— `annotOkP_tower_slot`'s λ twin, clause for clause (`AnnotOk2`'s
`.lam` case carries the same two projections `.pi`'s does, plus the
fibre existential this proof does not read). -/
theorem annotOkP_lamTower_slot :
    ∀ (k : Nat) {T : AVExpr} {Γ : List AVExpr} {R : AVExpr},
      LamTeleP k T Γ R → ∀ {ρ' : Nat → V},
      AnnotOkP V (fun j => ρ' (j + k)) T →
      ∀ p, p < k →
        (∀ q, p < q → q < k →
          ρ' q ∈ˢ interp2 V (fun j => ρ' (j + q + 1)) (Γ.getD q default)) →
        AnnotOkP V (fun j => ρ' (j + p + 1)) (Γ.getD p default) := by
  intro k
  induction k with
  | zero => intro T Γ R _ ρ' _ p hp; exact absurd hp (by omega)
  | succ k ih =>
    intro T Γ R h ρ' hokT p hp hmem
    obtain ⟨v, A, B, Γ', rfl, rfl, htail⟩ := h.succ_inv
    have hΓ'len : Γ'.length = k := htail.length
    have hgetA : (Γ' ++ [A]).getD k default = A := by
      rw [List.getD, List.getElem?_append_right (by omega), hΓ'len]
      simp
    have hokT' : AnnotOkP V (fun j => ρ' (j + k + 1))
        (AVExpr.lam v A B) := hokT
    have hsplitA : AnnotOkP V (fun j => ρ' (j + k + 1)) A :=
      ⟨((AnnotOk2_lam V (fun j => ρ' (j + k + 1)) v A B) ▸ hokT'.1).1,
        ((AnnotValidV_lam V (fun j => ρ' (j + k + 1)) v A B)
          ▸ hokT'.2).1⟩
    rcases Nat.lt_or_ge p k with hpk | hpk
    · have hmemk : ρ' k ∈ˢ interp2 V (fun j => ρ' (j + k + 1)) A := by
        have := hmem k (by omega) (by omega)
        rwa [hgetA] at this
      have henv : cons (ρ' k) (fun j => ρ' (j + k + 1))
          = (fun j => ρ' (j + k)) := by
        funext j
        cases j with
        | zero =>
          show cons (ρ' k) (fun j => ρ' (j + k + 1)) 0 = ρ' (0 + k)
          rw [cons_zero]
          congr 1
          omega
        | succ j =>
          show cons (ρ' k) (fun j => ρ' (j + k + 1)) (j + 1)
            = ρ' (j + 1 + k)
          rw [cons_succ]
          show ρ' (j + k + 1) = ρ' (j + 1 + k)
          congr 1
          omega
      have hokB : AnnotOkP V (fun j => ρ' (j + k)) B := by
        refine ⟨?_, ?_⟩
        · have h := ((AnnotOk2_lam V (fun j => ρ' (j + k + 1)) v A B)
            ▸ hokT'.1).2.1 (ρ' k) hmemk
          rwa [henv] at h
        · have h := ((AnnotValidV_lam V (fun j => ρ' (j + k + 1)) v A B)
            ▸ hokT'.2).2 (ρ' k) hmemk
          rwa [henv] at h
      have hgetΓ' : ∀ q, q < k →
          (Γ' ++ [A]).getD q default = Γ'.getD q default := by
        intro q hq
        rw [List.getD, List.getD, List.getElem?_append_left (by omega)]
      rw [hgetΓ' p hpk]
      exact ih htail hokB p hpk (fun q hq1 hq2 => by
        have := hmem q hq1 (by omega)
        rwa [hgetΓ' q hq2] at this)
    · obtain rfl : p = k := by omega
      rw [hgetA]
      exact hsplitA

/-- **`CtxOkP` at *walked* openers** — `ctxOkP_of_openers` with the
context equation supplied rather than derived.  See the module
docstring: `CtxOkP`'s per-leaf obligation is semantic, so a frame whose
openers are only *defeq* to the context's entries correlates just as
well as one whose openers are them. -/
theorem ctxOkP_of_walked_openers {env : Env} {m : EnvS2Core V env}
    {φ : Name → Nat}
    {k : Nat} {fvs : List Expr} {Aa : Nat → AVExpr} {Δa : List AVExpr}
    (hΔlen : Δa.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hwalk : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ tya, denoteP m.acval env φ k (Expr.fvarTypeD x) = some tya ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ tya
            = interp2 V (fun j => ρ (j + (k - 1 - i) + 1)) (Aa i)) ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ tya))
    {e : Expr} {n : Nat}
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs)
    (hltE : ∀ l ∈ e.fvarLeaves, l.1 < n)
    (hent : ∀ i, i < n → Δa[k - 1 - i]? = some (Aa i)) :
    CtxOkP m φ k Δa e := by
  refine ⟨hΔlen, ?_⟩
  intro l hl
  have hmem := hleaf l hl
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hmem
  obtain ⟨nm, ty, hx⟩ := hshape pos _ hpos
  obtain ⟨h1, h2, h3⟩ : l.1 = pos ∧ l.2.1 = nm ∧ l.2.2 = ty := by
    injection hx with a b c
    exact ⟨a, b, c⟩
  subst h1 h2 h3
  have hlt : l.1 < n := hltE l hl
  have hw := hws _ (List.mem_of_getElem? hpos)
  have hwty : l.1 < k ∧ Expr.WScoped l.1 l.2.2 := by
    simpa [Expr.WScoped] using hw
  obtain ⟨tya, htya, heq, hok⟩ := hwalk l.1 _ hpos
  rw [show Expr.fvarTypeD (Expr.fvar l.1 l.2.1 l.2.2) = l.2.2 from rfl]
    at htya
  exact ⟨hwty.1, hwty.2.fvarsBelow, tya, Aa l.1, htya,
    hent l.1 hlt, heq, hok⟩

end Setlec.SetR.Interp2
