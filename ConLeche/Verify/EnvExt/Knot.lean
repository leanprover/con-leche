module

public import ConLeche.Verify.EnvExt.Bodies
public import ConLeche.Kernel.TypeChecker
import ConLeche.Verify.Knot

public section

/-!
# Env extension, part 8: the knot — the theorem

One induction on the fuel ties the bodies' lemmas: at every fuel the
pure core records of two environments that `Agree` on a scope `N` are in
the currency.  The corollaries are the fueled entry points: at an
`N`-scoped input the run at `E₂` IS the run at `E₁` — errors included —
and a success is `N`-scoped.

**The extension lemma** (`whnf_extend`, …) is the special case: the
environment a run was made in and any later one, with `N` the scope the
consumer chooses (for the member tie: the home block's install
environment's names, the fixed names and their derived names).
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

theorem whnfCore_agree {e : Expr} (he : Sc N e) :
    whnfCore mode E₂ F d e = whnfCore mode E₁ F d e :=
  ((pureFns_ok mode H F).whnfCore d e he).1

theorem whnfCore_sc {e r : Expr} (he : Sc N e) (h : whnfCore mode E₁ F d e = .ok r) :
    Sc N r :=
  ((pureFns_ok mode H F).whnfCore d e he).2 r h

theorem whnf_agree {e : Expr} (he : Sc N e) : whnf mode E₂ F d e = whnf mode E₁ F d e :=
  ((pureFns_ok mode H F).whnf d e he).1

theorem whnf_sc {e r : Expr} (he : Sc N e) (h : whnf mode E₁ F d e = .ok r) : Sc N r :=
  ((pureFns_ok mode H F).whnf d e he).2 r h

theorem inferTypeCore_agree {e : Expr} (he : Sc N e) :
    inferTypeCore mode E₂ F d e = inferTypeCore mode E₁ F d e :=
  ((pureFns_ok mode H F).infer d e he).1

theorem inferTypeCore_sc {e r : Expr} (he : Sc N e)
    (h : inferTypeCore mode E₁ F d e = .ok r) : Sc N r :=
  ((pureFns_ok mode H F).infer d e he).2 r h

theorem inferTypeIO_agree {e : Expr} (he : Sc N e) :
    inferTypeIO mode E₂ F d e = inferTypeIO mode E₁ F d e :=
  ((pureFns_ok mode H F).inferIO d e he).1

theorem isDefEqCore_agree {a b : Expr} (ha : Sc N a) (hb : Sc N b) :
    isDefEqCore mode E₂ F d a b = isDefEqCore mode E₁ F d a b :=
  ((pureFns_ok mode H F).defeq d a b ha hb).1

theorem annotateCore_agree {e : Expr} (he : Sc N e) :
    annotateCore mode E₂ F d e = annotateCore mode E₁ F d e :=
  ((pureFns_ok mode H F).annotate d e he).1

theorem ensureSortCore_agree {e : Expr} (he : Sc N e) :
    ensureSortCore mode E₂ F d e = ensureSortCore mode E₁ F d e :=
  (ensureSort_ok (pureFns_ok mode H F) d he).1

/-- **The extension lemma**, success form: a successful `whnf` run at
`E₁` is the same successful run at any `E₂` agreeing on the scope. -/
theorem whnf_extend {e r : Expr} (he : Sc N e) (h : whnf mode E₁ F d e = .ok r) :
    whnf mode E₂ F d e = .ok r := by
  rw [whnf_agree H he, h]

end Entry

end ConLeche.EnvExt
