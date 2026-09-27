module

public import ConLeche.Verify.EnvExt.Base
public import ConLeche.Kernel.Inductives.RecCheck
public import ConLeche.Verify.EnvExt.Ok
import ConLeche.Verify.EnvExt.Knot
import ConLeche.Verify.EnvExt.ScOps

public section

/-!
# Env extension, part 10: the rec check's field telescopes

The rec check reads a field's telescope through whnf
(`targetWhnfPis`, `targetFieldNorms`): a chain of `whnf` runs on the
reducts' codomains.  At the pure operations (`fueledOps`) it is in the
currency whenever its input is scoped — the form a stage-1 helper that
re-reads an older home's constructor fields at a later environment
consumes (DESIGN.md, ENVEXT: the member tie).
-/

namespace ConLeche.EnvExt

open ConLeche

variable {N : Name → Prop} {E₁ E₂ : Env} (mode : CheckMode) (F : Nat)

theorem targetWhnfPis_ok (H : Agree N E₁ E₂) :
    ∀ (d fuel : Nat) {e : Expr}, Sc N e →
      Ok (Sc N) (targetWhnfPis (fueledOps mode F) E₂ d fuel e)
        (targetWhnfPis (fueledOps mode F) E₁ d fuel e)
  | _, 0, _, _ => Ok.throw _
  | d, fuel + 1, e, he => by
    simp only [targetWhnfPis]
    refine Ok.bind ((pureFns_ok mode H F).whnf d e he) (fun w hw => ?_)
    split
    · rename_i dom body bm
      have hpi := sc_forallE.mp hw
      refine Ok.bind (targetWhnfPis_ok H (d + 1) fuel
        (sc_instantiate1' hpi.2 (sc_fvar.mpr hpi.1))) (fun b' hb' => ?_)
      exact Ok.pure (sc_forallE.mpr ⟨hpi.1, sc_abstract1 _ _ _ hb'⟩)
    · exact Ok.pure he

theorem targetFieldNorms_ok (H : Agree N E₁ E₂) (d : Nat) (absM : Expr → Expr) :
    ∀ (fs : List Expr), (∀ f ∈ fs, Sc N (absM f.fvarTypeD)) →
      Ok (fun ts => ∀ t ∈ ts, Sc N t) (targetFieldNorms (fueledOps mode F) E₂ d absM fs)
        (targetFieldNorms (fueledOps mode F) E₁ d absM fs)
  | [], _ => Ok.pure (by simp)
  | f :: fs, hfs => by
    simp only [targetFieldNorms]
    refine Ok.bind (targetWhnfPis_ok mode F H d _ (hfs f (by simp))) (fun t ht => ?_)
    refine Ok.bind (targetFieldNorms_ok H d absM fs (fun g hg => hfs g (by simp [hg])))
      (fun ts hts => ?_)
    exact Ok.pure (by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hts x hx)

/-- **The field telescopes at a base**: a rec check reading the fields'
telescopes of terms that resolve in a base `B` at a later environment
reproduces the earlier environment's answer when it succeeds — the
home's install environment and every later one. -/
theorem targetFieldNorms_base_agree {B : Env} (hwf : EnvWF B) (hctors : RecCtorsStored B)
    (hnat : NatOpGuards B)
    (hx₁ : Extends B E₁) (hn₁ : NoNewInScope B E₁)
    (hx₂ : Extends B E₂) (hn₂ : NoNewInScope B E₂) (h₁₂ : Extends E₁ E₂) (d : Nat)
    (absM : Expr → Expr)
    {fs : List Expr} (hfs : ∀ f ∈ fs, (absM f.fvarTypeD).constsResolve B = true) {ts : List Expr}
    (h : targetFieldNorms (fueledOps mode F) E₂ d absM fs = .ok ts) :
    targetFieldNorms (fueledOps mode F) E₁ d absM fs = .ok ts :=
  (targetFieldNorms_ok mode F (Agree.ofBase hwf hctors hnat hx₁ hn₁ hx₂ hn₂ h₁₂) d absM fs
    (fun f hf => sc_of_constsResolve (hfs f hf)) ts h).1

end ConLeche.EnvExt
