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

/-! ## The VExpr-side telescope

`TeleTyped` mentions the environment, so a statement that takes it as a
*hypothesis* does not survive an install: the arguments it quantifies
over are arbitrary expressions, which may mention the newly stored
constant, and `denote` only moves from smaller environments to larger
ones.  See `Setlec/TTVerify/DESIGN.md` §8.1.

`VTeleTyped` is the same walk with the `Expr` layer stripped: the
transpose of `TeleFit` (`Setlec/Model/Interp.lean`) rather than of
`TeleFitI`, exactly as the set model keeps both.  It mentions no
environment and no valuation, so a law stated with it as a premise
transports across installs for free. -/

/-- Terms fitting a `∀`-telescope: each in the current domain, the
codomain instantiated as the walk proceeds.  Transpose of `TeleFit`. -/
inductive VTeleTyped (Δ : List VExpr) : VExpr → List VExpr → VExpr → Prop
  | nil {T : VExpr} : VTeleTyped Δ T [] T
  | cons {A B x : VExpr} {xs : List VExpr} {rest : VExpr} :
      HasType Δ x A →
      VTeleTyped Δ (B.inst x) xs rest →
      VTeleTyped Δ (.pi A B) (x :: xs) rest

/-- Fittings compose: walking `xs` and then `ys` from the residual is
walking `xs ++ ys`.  What a capability fold needs, where the pins reach
the parameter prefix and the law's subjects are peeled by hand. -/
theorem VTeleTyped.append {Δ : List VExpr} :
    ∀ {T : VExpr} {xs : List VExpr} {mid : VExpr} {ys : List VExpr}
      {rest : VExpr}, VTeleTyped Δ T xs mid → VTeleTyped Δ mid ys rest →
      VTeleTyped Δ T (xs ++ ys) rest := by
  intro T xs mid ys rest h
  induction h with
  | nil => intro h2; exact h2
  | cons hx _ ih => intro h2; exact .cons hx (ih h2)

/-- Applying along a fitting spine.  The object-level induction lives
here, once; the `Expr`-side `TeleTyped.appN` is a corollary. -/
theorem VTeleTyped.appN {Δ : List VExpr} {T : VExpr} {xs : List VExpr}
    {rest : VExpr} (h : VTeleTyped Δ T xs rest) :
    ∀ {f : VExpr}, HasType Δ f T → HasType Δ (VExpr.mkAppN f xs) rest := by
  induction h with
  | nil => intro f hf; exact hf
  | cons hx _ ih => intro f hf; exact ih (HasType.app hf hx)

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
theorem TeleTyped.toV {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {T : Expr} {args : List Expr} {xs : List VExpr} {rest : Expr}
    (h : TeleTyped cval env φ d Δ T args xs rest) :
    ∀ {TV : VExpr}, denote cval env φ d T = some TV →
      ∃ RV, VTeleTyped Δ TV xs RV ∧ denote cval env φ d rest = some RV := by
  induction h with
  | nil => intro TV hT; exact ⟨TV, .nil, hT⟩
  | @cons n ty body m arg args x xs A rest hty harg hx hfb hwa hba _ ih =>
    intro TV hT
    simp only [denote_forallE, hty] at hT
    split at hT
    · exact nomatch hT
    · next B hB =>
      obtain rfl : TV = .pi A B := (Option.some.inj hT).symm
      obtain ⟨RV, hfit, hrest⟩ := ih (TV := B.inst x)
        (by rw [denote_beta (n := n) (ty := ty) hcl hfb hwa hba harg 0, hB]; rfl)
      exact ⟨RV, .cons hx hfit, hrest⟩

theorem TeleTyped.appN {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {T : Expr} {args : List Expr} {xs : List VExpr} {rest : Expr}
    (h : TeleTyped cval env φ d Δ T args xs rest)
    {f TV RV : VExpr}
    (hT : denote cval env φ d T = some TV)
    (hR : denote cval env φ d rest = some RV)
    (hf : HasType Δ f TV) : HasType Δ (VExpr.mkAppN f xs) RV := by
  obtain ⟨RV', hfit, hrest⟩ := h.toV hcl hT
  obtain rfl : RV' = RV := by rw [hrest] at hR; exact Option.some.inj hR
  exact hfit.appN hf

/-! ## Spines

`Expr.mkAppN` and `VExpr.mkAppN` have the same shape, so a denoted
spine transports through an application chain.  Needed wherever a
clause matches on `getAppFn`/`getAppArgs` and the bridge has to
reassemble the denotation — `majorToCtor`'s rescues, and the iota
clause's redex. -/

/-- Each expression of a spine denotes to the corresponding term. -/
inductive DenoteSpine (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) : List Expr → List VExpr → Prop
  | nil : DenoteSpine cval env φ d [] []
  | cons {a : Expr} {v : VExpr} {as : List Expr} {vs : List VExpr} :
      denote cval env φ d a = some v →
      DenoteSpine cval env φ d as vs →
      DenoteSpine cval env φ d (a :: as) (v :: vs)

/-- Denotation commutes with application spines. -/
theorem denote_mkAppN {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as : List Expr} {vs : List VExpr}
    (h : DenoteSpine cval env φ d as vs) :
    ∀ {f : Expr} {vf : VExpr}, denote cval env φ d f = some vf →
      denote cval env φ d (Expr.mkAppN f as) = some (VExpr.mkAppN vf vs) := by
  induction h with
  | nil => intro f vf hf; exact hf
  | cons ha _ ih =>
    intro f vf hf
    refine ih ?_
    rw [denote_app, hf, ha]

/-- Denoted spines append. -/
theorem DenoteSpine.append {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as bs : List Expr} {xs ys : List VExpr}
    (h1 : DenoteSpine cval env φ d as xs)
    (h2 : DenoteSpine cval env φ d bs ys) :
    DenoteSpine cval env φ d (as ++ bs) (xs ++ ys) := by
  induction h1 with
  | nil => exact h2
  | cons ha _ ih => exact .cons ha ih

/-- A denoted spine's prefix. -/
theorem DenoteSpine.take {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as : List Expr} {xs : List VExpr}
    (h : DenoteSpine cval env φ d as xs) :
    ∀ k, DenoteSpine cval env φ d (as.take k) (xs.take k) := by
  induction h with
  | nil => intro k; simp [List.take_nil]; exact .nil
  | @cons a v as vs ha _ ih =>
    intro k
    cases k with
    | zero => exact .nil
    | succ k => exact .cons ha (ih k)

/-- A denoted spine's suffix. -/
theorem DenoteSpine.drop {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as : List Expr} {xs : List VExpr}
    (h : DenoteSpine cval env φ d as xs) :
    ∀ k, DenoteSpine cval env φ d (as.drop k) (xs.drop k) := by
  induction h with
  | nil => intro k; simp [List.drop_nil]; exact .nil
  | @cons a v as vs ha h ih =>
    intro k
    cases k with
    | zero => exact .cons ha h
    | succ k => exact ih k

/-- A denoted spine has the same length as its source. -/
theorem DenoteSpine.length {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as : List Expr} {xs : List VExpr}
    (h : DenoteSpine cval env φ d as xs) : xs.length = as.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- A mapped spine denotes pointwise — the shape the eta fabrication
has, where the fields are a `List.range` map. -/
theorem DenoteSpine.map {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {α : Type} {as : List α} {f : α → Expr} {g : α → VExpr}
    (h : ∀ a ∈ as, denote cval env φ d (f a) = some (g a)) :
    DenoteSpine cval env φ d (as.map f) (as.map g) := by
  induction as with
  | nil => exact .nil
  | cons a as ih =>
    exact .cons (h a (List.mem_cons_self ..))
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- A denoted spine's entries, indexed.  (Relocated from
`Setlec/TTVerify/DefEqStep.lean`: `Iota.lean` needs it too, and
`Tele.lean` is where `DenoteSpine` is declared.) -/
theorem DenoteSpine.get {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as : List Expr} {vs : List VExpr}
    (h : DenoteSpine cval env φ d as vs) :
    ∀ i : Fin as.length,
      denote cval env φ d as[i] = some (vs.getD i default) := by
  induction h with
  | nil => intro i; exact nomatch i.2
  | @cons a v as vs ha _ ih =>
    intro i
    match i with
    | ⟨0, _⟩ => simpa using ha
    | ⟨j + 1, hj⟩ =>
      have := ih ⟨j, by simpa using hj⟩
      simpa using this

/-- Splitting a denoted spine at a final argument — the shape the
recursor's telescope walk has at a fire site, where the major premise
is the last entry. -/
theorem DenoteSpine.snoc_inv {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} : ∀ {as : List Expr} {a : Expr} {zs : List VExpr},
    DenoteSpine cval env φ d (as ++ [a]) zs →
    ∃ xs y, zs = xs ++ [y] ∧ DenoteSpine cval env φ d as xs ∧
      denote cval env φ d a = some y := by
  intro as
  induction as with
  | nil =>
    intro a zs h
    cases h with
    | cons ha hn => cases hn; exact ⟨[], _, rfl, .nil, ha⟩
  | cons b bs ih =>
    intro a zs h
    cases h with
    | cons hb hn =>
      obtain ⟨xs, y, rfl, hxs, hy⟩ := ih hn
      exact ⟨_ :: xs, y, rfl, .cons hb hxs, hy⟩

/-- Denotation of an application spine, inverted: the head and every
argument denote, and the value is their `VExpr` application.  The
converse of `denote_mkAppN`, and what the delta step needs to read a
redex apart. -/
theorem denote_mkAppN_inv {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} : ∀ {as : List Expr} {f : Expr} {v : VExpr},
    denote cval env φ d (Expr.mkAppN f as) = some v →
    ∃ vf vs, denote cval env φ d f = some vf ∧
      DenoteSpine cval env φ d as vs ∧ v = VExpr.mkAppN vf vs := by
  intro as
  induction as with
  | nil => intro f v h; exact ⟨v, [], h, .nil, rfl⟩
  | cons a as ih =>
    intro f v h
    obtain ⟨vfa, vs, hfa, hsp, rfl⟩ := ih h
    rw [denote_app] at hfa
    split at hfa
    · next vf va hf ha =>
      exact ⟨vf, va :: vs, hf, .cons ha hsp, by
        rw [← Option.some.inj hfa]; rfl⟩
    · exact nomatch hfa

/-- **A typed walk's residual is the telescope's.**  `TeleTyped`
instantiates one argument at a time and so does `piResidual`, so the
two agree on the nose.  Needed where a checker guard is stated about
`piResidual` (`iotaRec`'s canonical-index comparison) and the bridge
holds the walk. -/
theorem TeleTyped.rest_eq {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} :
    ∀ {T : Expr} {args : List Expr} {xs : List VExpr} {rest : Expr},
      TeleTyped cval env φ d Δ T args xs rest →
      piResidual T args = some rest := by
  intro T args xs rest h
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => exact ih

/-- A typed telescope walk exposes its spine's denotations — the form
`denote_mkAppN` consumes, so a `TeleTyped` hypothesis doubles as the
reassembly fact. -/
theorem TeleTyped.spine {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {T : Expr} {args : List Expr}
    {xs : List VExpr} {rest : Expr}
    (h : TeleTyped cval env φ d Δ T args xs rest) :
    DenoteSpine cval env φ d args xs := by
  induction h with
  | nil => exact .nil
  | cons _ harg _ _ _ _ _ ih => exact .cons harg ih

end Setlec.TTVerify
