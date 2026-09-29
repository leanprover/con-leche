--#export EvalExpr.rec
/- The cslib shape (`Cslib.Mech.FunCallEval.EvalExpr`, nested through
`List.Forall₂`): universe-polymorphic, the container's indices are
lists over the block's parameters.  Official ACCEPTS. -/
inductive F2 {α β : Type u} (R : α → β → Prop) : List α → List β → Prop
  | nil : F2 R [] []
  | cons {a b l₁ l₂} : R a b → F2 R l₁ l₂ → F2 R (a :: l₁) (b :: l₂)

inductive Ex (Var Val FunId : Type u) where
  | var (x : Var)
  | val (v : Val)
  | call (f : FunId) (args : List (Ex Var Val FunId))

inductive EvalExpr {FunId Val Var : Type u} (eval : FunId → List Val → Val → Prop) :
    (σ : Var → Val) → (e : Ex Var Val FunId) → (v : Val) → Prop where
  | val : EvalExpr eval σ (.val v) v
  | var : EvalExpr eval σ (.var x) (σ x)
  | call (hArgs : F2 (EvalExpr eval σ) args vals) (hFun : eval f vals v) :
    EvalExpr eval σ (.call f args) v
