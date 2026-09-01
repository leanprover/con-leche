import Setlec.SetR.Install.Axiom

/-!
# The compiler-trust identity pin, discharged (task #148, T5)

`ReducePinS`: the identity certificate of a pinned reduce operation
(`checkReducePin`'s relation pack, `ReducePinR`) yields the value-level
identity `EnvS.reduce_ops` wants.  The content is one `DefEq.sound`
application: the certificate's open equation
`⊢ [E] (app V (bvar 0)) ≡ (bvar 0)` reads off, at any member `x` of the
element type's interpretation, as `app ⟦V⟧ x = x` — the one-entry `Sat`
is the membership itself, and the closed value's interpretation is
environment-independent.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- A one-entry context is satisfied by a member of the entry's
interpretation (no closedness needed: the entry's environment tail is
the ambient one on the nose). -/
theorem sat_one {A : VExpr} {ρ : Nat → V} {x : V}
    (hx : x ∈ˢ interp V ρ A) : Sat V [A] (cons V x ρ) := by
  intro i A' hi
  match i with
  | 0 =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    rw [show (fun j => cons V x ρ (j + 0 + 1)) = ρ from
      funext fun j => rfl]
    exact hx
  | n + 1 =>
    simp at hi

/-- **`ReducePinS`, discharged.** -/
theorem reducePinS : ReducePinS V := by
  intro μ F env m cv type' value value' hmem hfresh hcv hvfr hpin hpinCv
  -- the `-` is task #161 P4 H1's added identity-certificate *run*;
  -- this v1 install spends only the `DefEq` it was absorbed into.
  obtain ⟨hstored, helem, hguard, valA, pinA, hannA, hannP, -,
    hcert⟩ := hpin
  obtain ⟨hvlb, hvhf, hannv, hvp, hvr, hfrontV⟩ := hvfr
  -- the two annotate runs of the same value agree
  obtain rfl : value' = valA := by
    rw [hannv] at hannA
    exact Except.ok.inj hannA
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  -- the element inductive is stored, level-monomorphically
  obtain ⟨ciE, hfE, hlpE⟩ : ∃ ci, env.find? (reduceElemName cv.name)
      = some ci ∧ ci.toConstantVal.levelParams = [] := by
    unfold reduceElemOk at helem
    split at helem
    · next hc =>
      rw [show reduceElemName cv.name = natName from by
        rw [reduceElemName, if_pos hc]]
      rcases hfn : env.find? natName with _ | ci
      · rw [hfn] at helem; simp at helem
      · rw [hfn] at helem
        simp only [decide_eq_true_eq] at helem
        obtain rfl := Option.some.inj helem
        exact ⟨_, rfl, rfl⟩
    · next hc =>
      rw [show reduceElemName cv.name = boolName from by
        rw [reduceElemName, if_neg hc]]
      rcases hfb : env.find? boolName with _ | ci
      · rw [hfb] at helem; simp at helem
      · rw [hfb] at helem
        refine ⟨ci, rfl, ?_⟩
        cases ci with
        | indInfo cvB caps =>
          simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            decide_eq_true_eq] at helem
          exact helem.1.2
        | _ => exact nomatch helem
  have helemSome : (env.find? (reduceElemName cv.name)).isSome = true := by
    rw [hfE]; rfl
  -- the element name is not the operation's
  have hne : reduceElemName cv.name ≠ cv.name := by
    simp only [reduceOpNames, List.mem_cons, List.not_mem_nil, or_false]
      at hmem
    rcases hmem with h | h <;> rw [h] <;> decide
  refine ⟨by rw [Env.find?_cons_of_isSome hfresh helemSome]
             exact helemSome, ?_⟩
  intro ψ ρ x hx
  obtain ⟨E, Vc, hE, hVc, hDeq⟩ := hcert ψ
  -- the element type denotes to the stored valuation
  have hEval : E = m.cval (reduceElemName cv.name) ψ := by
    have : denoteClosed m.cval env ψ (reduceElemTy cv.name)
        = some (m.cval (reduceElemName cv.name) ψ) := by
      show denote m.cval env ψ 0 (reduceElemTy cv.name) = _
      rw [show reduceElemTy cv.name
          = .const (reduceElemName cv.name) [] from by
        unfold reduceElemTy reduceElemName
        split <;> simp_all]
      exact denote_const_nolevelsS hfE hlpE ψ 0
    rw [this] at hE
    exact (Option.some.inj hE).symm
  -- membership at the certificate's entry
  rw [show cvalAt m.cval env cv.name value' (reduceElemName cv.name)
      = m.cval (reduceElemName cv.name) from cvalAt_ne hne] at hx
  rw [← hEval] at hx
  -- the certificate's equation at `cons x ρ`
  have heq := DefEq.sound (m.toHyp ψ) hDeq (cons V x ρ) (sat_one hx)
  simp only [interp_app, interp_bvar, cons_zero] at heq
  -- the closed value's interpretation is environment-independent
  have hVcl : VExpr.Closed Vc :=
    denote_closed m.cval_closed hvf' hbv' hVc
  rw [interp_closed V hVcl (cons V x ρ) ρ] at heq
  -- and it is the valuation the install chose
  rw [show cvalAt m.cval env cv.name value' cv.name ψ = Vc from
    cvalAt_self hVc]
  exact heq

end Setlec.SetR
