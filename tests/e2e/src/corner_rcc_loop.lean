--#export Skey T T.rec T.rec_1
/- RCC (lane PRIMREC/RCC): the good twin of `corner_rcc_loop_bad`, which
   `scripts/mk_rcc_fixtures.py` forges from this stream.

   `Skey π` is a type-level term `S` whose KERNEL whnf is literally `Q S`:
   a Girard/Abel–Coquand proof loop `ω` (propext + K-like `Eq.rec` +
   impredicative `Prop`) feeds `Acc.rec` into `Prop` at a SAME-index
   recursive call.  It needs `π : Acc R trivial` with `R _ _ := True`, a
   hypothesis the model has no valuation for (`acc_cycle`); no such loop
   is known at an inhabited valuation.  `Skey` is computed by the
   kernel's own whnf and installed verbatim (`addDecl`: no nested-proof
   abstraction, which would hide the loop behind an opaque theorem).

   `T π` is a plain nested block over `Q` at `T π`.  Official 0, today 0. -/
import Lean
set_option genSizeOf false
set_option genInjectivity false
inductive Q (α : Prop) : Prop where
  | mk : α → Q α
abbrev R : True → True → Prop := fun _ _ => True
abbrev P : Prop := @Acc True R trivial
abbrev A : Prop := ∀ X : Prop, X → P
def δ (π : P) : A := fun X z =>
  Acc.intro trivial (fun _ _ =>
    (cast (propext ⟨fun _ => (fun _ _ => π : A), fun _ => z⟩ : X = A) z) X z)
def ω (π : P) : P :=
  (cast (propext ⟨fun _ => (fun _ _ => π : A), fun _ => δ π⟩ : A = A) (δ π)) A (δ π)
def F : (x : True) → (∀ y, R y x → Acc R y) → (∀ y, R y x → Prop) → Prop :=
  fun _ _ ih => Q (ih trivial trivial)
def s0 (π : P) : Prop := @Acc.rec True R (fun _ _ => Prop) F trivial (ω π)
open Lean Meta Elab Command in
run_meta do
  let env ← getEnv
  withLocalDeclD `π (mkConst ``P) fun π => do
    let lctx ← getLCtx
    let wh (e : Expr) : MetaM Expr := match Kernel.whnf env lctx e with
      | .ok r => pure r
      | .error _ => throwError "kernel whnf failed"
    let r0 ← wh (mkApp (mkConst ``s0) π)
    let s1 := r0.appArg!
    let r1 ← wh s1
    unless r1.isAppOfArity ``Q 1 && r1.appArg! == s1 do throwError "no literal loop"
    let val ← mkLambdaFVars #[π] s1
    let ty ← mkArrow (mkConst ``P) (mkSort levelZero)
    let dv : DefinitionVal :=
      { name := `Skey, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe }
    addDecl (Declaration.defnDecl dv)
inductive T (π : P) : Prop where
  | mk : Q (T π) → T π
