module

public import ConLeche.Model.Inductives.FixNoBVar
import ConLeche.Semantics.Frame
public section
/-!
# The reflexive telescopes' bounds (task #202 Stage B)

A reflexive field's type is a Π-tower over its telescope of the family
at the calls' tuples; at a `Type`-valued block (`w ≠ 0`) the family's
slot at such a field is the nested product `piTele w` over the
telescope, which lives in `univ w` only when every telescope domain
does.  The install checks each field's sort against the block's
(`checkStructFieldSortsI`: `imax` of the domains' sorts and the
family's, at most `resSort`); at `w ≠ 0` the `imax` is a `max`, so
every domain's sort is at most `resSort` (`piDoms_of_infer`, the
Π-inference walked along the opening), and the sort claim of the
tuple tier (`sortRow`) reads each domain, at the frame under the
earlier ones, into `univ w` (`teleBound_walk`, the context discipline
opened binder by binder).  `fixTeleBound_of` states this at the
constructor data: at a shadow-fitting field spine and a fitting
telescope prefix, the next domain's reading is bounded at the family's
regime.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The domains' sorts along a Π-inference -/

/-! ## The bound, walked along the telescope -/

/-- **The telescope's domains are bounded**, binder by binder: at a
frame satisfying the earlier domains, the next domain's reading is
graded and lies in `univ w` — the sort claim at the context opened by
the earlier binders. -/
theorem teleBound_walk (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env) (ψ : Name → Nat)
    {w : Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {fvs : List Expr} {o : Expr} {Δ : List AnnotTerm}
      {tl : List (Nat × Nat × AnnotTerm)},
      ConLeche.openPisAtFvars n e d = some (fvs, o) → tl.length = n →
      CtxOk mp.base2 ψ d Δ e → Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      (∀ k a, fvs[k]? = some a →
        denoteMeta mp.base2.acval env ψ (d + k) a.fvarTypeD = some (tl.getD k default).2.2) →
      (∀ k a, fvs[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
        ConLeche.inferTypeCore μ env F (d + k) a.fvarTypeD = .ok t ∧
        ConLeche.ensureSortCore μ env F (d + k) t = .ok u ∧ Level.eval ψ u ≤ w) →
      ∀ k, k < n → ∀ ρ : Nat → V, Sat V (((tl.take k).map (·.2.2)).reverse ++ Δ) ρ →
        WellDenotedV V ρ (tl.getD k default).2.2 ∧ interp V ρ (tl.getD k default).2.2 ∈ˢ (univ w : V)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k, hk, _, _ => absurd hk (Nat.not_lt_zero k)
  | n + 1, d, e, fvs, o, Δ, tl, hop, hlen, hC, hws, hb, hL, hread, hinf, k, hk, ρ, hρ => by
    match e, hop, hws, hb with
    | .forallE ty body mb, hop, hws, hb =>
      simp only [ConLeche.openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        cases tl with
        | nil => exact absurd hlen (by simp)
        | cons t0 tl' =>
        have hlen' : tl'.length = n := by simpa using hlen
        have hws2 : Expr.WScoped d ty ∧ Expr.WScoped d body := by
          simp only [Expr.WScoped] at hws; exact hws
        -- the first domain's frame conditions
        have hbty : ty.looseBVarsBounded 0 = true := by
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb; exact hb.1
        have hbb : body.looseBVarsBounded 1 = true := by
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb; exact hb.2
        have hLty : Expr.LeavesBounded ty := fun l hl =>
          hL l (by rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl)
        have hLbody : Expr.LeavesBounded body := fun l hl =>
          hL l (by rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl)
        -- the first domain's row
        have hread0 : denoteMeta mp.base2.acval env ψ d ty = some t0.2.2 := by
          have := hread 0 _ rfl
          simpa [Expr.fvarTypeD] using this
        obtain ⟨F, t, u, hi, hens, hle⟩ := hinf 0 _ rfl
        simp only [Nat.add_zero, Expr.fvarTypeD] at hi hens
        have hCty := hC.forallE_ty
        have hrow := (claimsAt_of hμ mp ψ F).sortRow hi hens hws2.1 hbty hLty hCty hread0
        cases k with
        | zero =>
          simp only [List.take_zero, List.map_nil, List.reverse_nil, List.nil_append] at hρ
          exact ⟨(hrow ρ hρ).1, univ_mono hle _ (hrow ρ hρ).2⟩
        | succ k =>
          -- open the binder, walk on
          have hC' : CtxOk mp.base2 ψ (d + 1) (t0.2.2 :: Δ) (body.instantiate1 (.fvar d ty)) :=
            CtxOk.open hC.forallE_body hCty hread0 fun ρ hρ => (hrow ρ hρ).1
          obtain ⟨hws', hb', hL'⟩ := frame_open2 hws2.1 hbty hws2.2 hbb hLty hLbody
          have hread' : ∀ k a, fvs'[k]? = some a →
              denoteMeta mp.base2.acval env ψ (d + 1 + k) a.fvarTypeD = some (tl'.getD k default).2.2 := by
            intro k a hk
            have := hread (k + 1) a (by simpa using hk)
            rwa [show d + (k + 1) = d + 1 + k from by omega] at this
          have hinf' : ∀ k a, fvs'[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
              ConLeche.inferTypeCore μ env F (d + 1 + k) a.fvarTypeD = .ok t ∧
              ConLeche.ensureSortCore μ env F (d + 1 + k) t = .ok u ∧ Level.eval ψ u ≤ w := by
            intro k a hk
            obtain ⟨F, t, u, h1, h2, h3⟩ := hinf (k + 1) a (by simpa using hk)
            rw [show d + (k + 1) = d + 1 + k from by omega] at h1 h2
            exact ⟨F, t, u, h1, h2, h3⟩
          have hρ' : Sat V (((tl'.take k).map (·.2.2)).reverse ++ (t0.2.2 :: Δ)) ρ := by
            simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hρ
          have := teleBound_walk hμ mp ψ n hop' hlen' hC' hws' hb' hL' hread' hinf' k (by omega) ρ hρ'
          simpa using this
      · exact nomatch hop
    | .bvar _, hop, _, _ | .fvar _ _, hop, _, _ | .sort _, hop, _, _
    | .const _ _, hop, _, _ | .app _ _, hop, _, _ | .lam _ _ _, hop, _, _
    | .letE _ _ _, hop, _, _ | .lit _, hop, _, _ | .proj _ _ _, hop, _, _ =>
      simp [ConLeche.openPisAtFvars] at hop

/-! ## The bound at the constructor data -/

end ConLeche.Model
