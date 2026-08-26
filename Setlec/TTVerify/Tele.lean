import Setlec.TTVerify.Inst

/-!
# Telescope typing

`TeleTyped` — the transpose of `TeleFitI` (`Setlec/Model/Interp.lean`)
with **membership replaced by typing**: walking a `∀`-telescope one
argument at a time, each argument denoting and being *derivably of* the
corresponding (progressively instantiated) domain.

This is the hypothesis of the fired modeled-iota contract
(`Setlec/TTVerify/DESIGN.md` §8), and it is what the checker's
`iotaCerts` discharges at the fire site — **checked, before this
predicate was built on**: `iotaCerts` walks the same telescope in the
same order, instantiating `body.instantiate1 arg` as it goes, and per
argument yields `infer` + `defeq`, which is `HasType Δ ⟦arg⟧ ⟦ty⟧` at
that domain.  Exact, not a superset.  The set model's `certs_fit`
(`Setlec/Model/Core/Certs.lean`) already performs this induction for
`TeleFitI`, and `TeleTyped` demands strictly less than `TeleFitI` does.

It is also the shape the headline fact of §6 predicts is needed: one
typing premise per argument, established where the rule fires.

Two things to notice against the original.

**`AnnotOk` drops, again.**  `TeleFitI.cons` carries `AnnotOk … arg`
among its premises; there is nothing to carry here, so the constructor
is one premise shorter.  That is the same saving as everywhere else in
this bridge (§2).

**Nothing else changes.**  The scoping premises (`fvarsBelow`,
`WScoped`, `looseBVarsBounded`) transpose verbatim, because they are
facts about `Expr` that both sides need for the same reason: the
instantiation walk has to stay inside the frame.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- Arguments fitting a `∀`-telescope, with typing where `TeleFitI` has
membership: each argument denotes to a term derivably of the current
domain, and the telescope is instantiated one argument at a time.  The
last index is the fully instantiated residual. -/
inductive TeleTyped (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (Δ : List VExpr) :
    Expr → List Expr → List VExpr → Expr → Prop
  | nil {e : Expr} : TeleTyped cval env φ d Δ e [] [] e
  | cons {n : Name} {ty body : Expr} {m : BinderMeta} {arg : Expr}
      {args : List Expr} {x : VExpr} {xs : List VExpr} {A : VExpr}
      {rest : Expr} :
      denote cval env φ d ty = some A →
      denote cval env φ d arg = some x →
      HasType Δ x A →
      Expr.fvarsBelow d body →
      Expr.WScoped d arg →
      arg.looseBVarsBounded 0 = true →
      TeleTyped cval env φ d Δ (body.instantiate1 arg) args xs rest →
      TeleTyped cval env φ d Δ (.forallE n ty body m) (arg :: args)
        (x :: xs) rest

/-! ## The consumer

Per the house rule (`Setlec/TT/DESIGN.md` §3.1): a definition is a
conjecture until something that uses it elaborates.  This is the use —
and it is the one the iota contract needs, so it is not a toy.

**It is also where the headline fact shows up as an obligation rather
than as prose.**  `HasType.app` fires once per argument and wants
`⊢ x : A` at *that* domain each time; `TeleTyped` supplies exactly one
such premise per argument, and there is nowhere else for them to come
from.  The `iotaCerts` prediction of §6 is the claim that the checker
already computes precisely this list. -/

/-- Instantiating a `∀`-telescope typing along a fitting argument
spine.  The one interesting step is that the *codomain* denotation
after instantiation is the previous one's `inst` — which is
`denote_beta`, so the walk stays in step with `HasType.app`'s own
`B.inst a`. -/
theorem TeleTyped.appN {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {T : Expr} {args : List Expr} {xs : List VExpr} {rest : Expr}
    (h : TeleTyped cval env φ d Δ T args xs rest) :
    ∀ {f TV RV : VExpr},
      denote cval env φ d T = some TV →
      denote cval env φ d rest = some RV →
      HasType Δ f TV → HasType Δ (VExpr.mkAppN f xs) RV := by
  induction h with
  | nil =>
    intro f TV RV hT hR hf
    obtain rfl : TV = RV := by rw [hT] at hR; exact Option.some.inj hR
    exact hf
  | @cons n ty body m arg args x xs A rest hty harg hx hfb hwa hba _ ih =>
    intro f TV RV hT hR hf
    simp only [denote_forallE, hty] at hT
    split at hT
    · exact nomatch hT
    · next B hB =>
      obtain rfl : TV = .pi A B := (Option.some.inj hT).symm
      refine ih ?_ hR (HasType.app hf hx)
      rw [denote_beta (n := n) (ty := ty) hcl hfb hwa hba harg 0, hB]
      rfl

end Setlec.TTVerify
