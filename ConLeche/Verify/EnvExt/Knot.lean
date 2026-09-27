module

public import ConLeche.Verify.EnvExt.Ok
public import ConLeche.Kernel.TypeChecker
import ConLeche.Verify.Knot
import ConLeche.Verify.EnvExt.Bodies
import ConLeche.Verify.EnvExt.Certs

public section

/-!
# Env extension, part 8: the knot — the theorem

One induction on the fuel ties the bodies' lemmas: at every fuel the
pure core records of two environments that `Agree` on a scope `N` are in
the currency.  The corollaries are the fueled entry points: at an
`N`-scoped input a success of the run at `E₂` is the same success of the
run at `E₁`, and it is `N`-scoped.

For the member tie `E₁` is the home block's install environment and
`E₂` any later one, with `N` the scope of the home's base
(`Base.lean`): a later run that succeeds reproduces the install's.
-/

namespace ConLeche.EnvExt

open ConLeche

variable {N : Name → Prop} {E₁ E₂ : Env} (mode : CheckMode)

/-- **The knot induction.** -/
theorem pureFns_ok (H : Agree N E₁ E₂) :
    ∀ f : Nat, RecOK N (pureFns mode E₁ f) (pureFns mode E₂ f)
  | 0 =>
    ⟨fun _ _ _ => Ok.throw _, fun _ _ _ => Ok.throw _, fun _ _ _ => Ok.throw _,
      fun _ _ _ _ _ => Ok.throw _, fun _ _ _ => Ok.throw _, fun _ _ _ => Ok.throw _⟩
  | f + 1 => by
    have ih := pureFns_ok H f
    refine ⟨fun d e he => ?_, fun d e he => ?_, fun d e he => ?_, fun d a b ha hb => ?_,
      fun d e he => ?_, fun d e he => ?_⟩
    · exact whnfCoreBody_ok H ih mode d he
    · exact whnfBody_ok H ih d he
    · exact inferBody_ok H ih mode d he
    · exact defeqBody_ok H ih mode d ha hb
    · exact annotateBody_ok H ih d he
    · rw [pureFns_inferIO, pureFns_inferIO]
      exact Ok.ite (fun _ => inferBodyIO_ok H ih.ioView mode d he)
        (fun _ => inferBody_ok H ih mode d he)

/-! ## The fueled entry points -/

section Entry

variable {mode} (H : Agree N E₁ E₂) {F d : Nat}
include H

theorem whnfCore_agree {e r : Expr} (he : Sc N e) (h : whnfCore mode E₂ F d e = .ok r) :
    whnfCore mode E₁ F d e = .ok r ∧ Sc N r :=
  (pureFns_ok mode H F).whnfCore d e he r h

theorem whnf_agree {e r : Expr} (he : Sc N e) (h : whnf mode E₂ F d e = .ok r) :
    whnf mode E₁ F d e = .ok r ∧ Sc N r :=
  (pureFns_ok mode H F).whnf d e he r h

theorem inferTypeCore_agree {e r : Expr} (he : Sc N e)
    (h : inferTypeCore mode E₂ F d e = .ok r) : inferTypeCore mode E₁ F d e = .ok r ∧ Sc N r :=
  (pureFns_ok mode H F).infer d e he r h

theorem inferTypeIO_agree {e r : Expr} (he : Sc N e) (h : inferTypeIO mode E₂ F d e = .ok r) :
    inferTypeIO mode E₁ F d e = .ok r ∧ Sc N r :=
  (pureFns_ok mode H F).inferIO d e he r h

theorem isDefEqCore_agree {a b : Expr} {v : Bool} (ha : Sc N a) (hb : Sc N b)
    (h : isDefEqCore mode E₂ F d a b = .ok v) : isDefEqCore mode E₁ F d a b = .ok v :=
  ((pureFns_ok mode H F).defeq d a b ha hb v h).1

theorem annotateCore_agree {e r : Expr} (he : Sc N e) (h : annotateCore mode E₂ F d e = .ok r) :
    annotateCore mode E₁ F d e = .ok r ∧ Sc N r :=
  (pureFns_ok mode H F).annotate d e he r h

theorem ensureSortCore_agree {e : Expr} {u : Level} (he : Sc N e)
    (h : ensureSortCore mode E₂ F d e = .ok u) : ensureSortCore mode E₁ F d e = .ok u :=
  (ensureSort_ok (pureFns_ok mode H F) d he u h).1

end Entry

end ConLeche.EnvExt
