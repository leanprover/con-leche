import Setlec.SetBase.Bridge.Main
import Setlec.SetR.Bridge.Decl
import Setlec.SetR.Install.Value
import Setlec.Verify.DivModInv
import Setlec.SetBase.DivModEval

/-!
# The div/mod pin's certificates, extracted (task #148, T5)

The **extract layer** of `DivModPinS`: everything between the
checker's certificate verdict and the value equations the clauses are
assembled from.

`ReducePinS` is short because `ReducePinR` hands it a `DefEq`
*relation*, so its whole discharge is one `DefEq.sound`.  The div/mod
pack (T6's granted retirement of `DivModCertR`) hands over the
checker's own verdict instead, so this layer does the bridging itself
— and it can, because `checkBridge` runs at `m.toEnvR` and
`CtxOkR.pinnedCtx` is exactly the depth-4 frame the certificates are
checked in.  **No relation had to be reopened**: the reopen condition
recorded at `DivModPinR` asked whether the content wants first-class
relational form, and the answer is no — it wants an `EnvR`, which the
install's own `EnvS` already provides.

What is here:

* `certValueS` — one certificate run to *the statement's
  interpretation is inhabited*, via `InferClaimsR`/`DefEqClaimsR` at
  depth 4 and `Infer.sound`/`DefEq.sound`;
* the substitution facts the frame reads (`substConst0` rewrites
  `const` nodes and never enters an `fvar` annotation, so with a closed
  replacement the leaf list does not move);
* `dmVal` and its two denotation lemmas — the frame's valuation, at a
  dependency and at the pinned operation itself;
* `sat_four` — the four-entry frame, satisfied slot by slot;
* the pinned-type inversions and `dmBinMem`/`dmUnMem` — every operation
  the certificates mention is a function on the frame's `Nat`, which is
  what the `Eq`-spine's side conditions want;
* `eqSpine_eq` — the pinned `Eq`-spine's interpretation is the
  equation's truth set, so *inhabited* means *equal*;
* `dmCertEq1`/`dmCertEq2` — **one certificate, discharged**: the two
  packaged forms (one and two hypotheses) a clause instantiates.

Everything a certificate needs from its *statement* is decidable of
the literal statement (`dmLeavesOk`, `wscopedB`, `looseBVarsBounded`),
and the substitution of the pinned operation into it preserves all
three — so a clause's syntactic obligations are `by decide`.

* `dmFragOk`/`dmEvalV`/`dmDenEval` — the statements' expression
  grammar, its value, and the one-step "denote *and* evaluate": a
  statement side's denotation interprets to exactly the `app`-chain
  `DivModClausesV` is written in, so a clause never has to name a
  `VExpr`;
* `dmFrameS` — the whole obligation's preamble, assembled from the
  guards: the pinned operation's denotation and type, its
  dependencies' function-space memberships, the frame's `Nat` and
  `Bool` with their universes, and the pinned `Eq`.

What remains of `DivModPinS` is the nine operations' clause blocks.
Each denotes its two statement sides with `dmDenEval`, reads the
equation off the certificate with `dmCertEq1`/`dmCertEq2`, and matches
it against `DivModClausesV` — where the match is definitional, because
`dmEvalV` computes the same `app`-chain.
-/

-- The nine operations' clause blocks need slightly different lemma
-- sets at each of their thirty-four membership steps, and the
-- difference is not stable under editing: the same escape
-- `Setlec/TTVerify/DivModPin.lean` takes, for the same reason.
set_option linter.unusedSimpArgs false

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify SetTheory
universe w
variable {V : Type w} [SetTheory V]

/-- **One certificate, extracted**: a successful run identifies the
applied proof's inferred type with the pinned statement, so the
statement's interpretation is inhabited at any satisfying valuation. -/
theorem certValueS {μ : CheckMode} {F : Nat} {env : Env}
    (m : EnvS V env) (φ : Name → Nat) {c : Name} {annVal : Expr}
    {st : List Expr × Expr} {proof : Expr}
    (hfacts : CertRunFacts μ env F c annVal st proof)
    {Δ : List VExpr}
    (hW : Expr.WScoped 4 (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))))
    (hB : (divModCertApplied (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))).looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))))
    (hCA : CtxOkR μ m.cval env φ 4 Δ (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))))
    (hWE : Expr.WScoped 4 (Expr.substConst0 c annVal st.2))
    (hBE : (Expr.substConst0 c annVal st.2).looseBVarsBounded 0 = true)
    (hLE : Expr.LeavesBounded (Expr.substConst0 c annVal st.2))
    (hCE : CtxOkR μ m.cval env φ 4 Δ (Expr.substConst0 c annVal st.2))
    {vE : VExpr}
    (hvE : denote m.cval env φ 4 (Expr.substConst0 c annVal st.2)
      = some vE)
    (ρ : Nat → V) (hsat : Sat V Δ ρ) :
    ∃ w : V, w ∈ˢ interp V ρ vE := by
  obtain ⟨hguard, appliedA, tp, hann, hinf, hde⟩ := hfacts
  obtain ⟨-, -, ihd, ihi⟩ := checkBridge (mode := μ) m.toEnvR φ F
  -- the annotated applied proof keeps the frame
  have hWA : Expr.WScoped 4 appliedA := annotateCore_WScoped F _ hann hW
  have hBA : appliedA.looseBVarsBounded 0 = true :=
    annotateCore_looseBVars F _ hann hB
  have hsub := annotateCore_leaves_sub F _ hann hW hB
  have hLA : Expr.LeavesBounded appliedA := fun l hl => hL l (hsub l hl)
  have hCA' : CtxOkR μ m.cval env φ 4 Δ appliedA :=
    CtxOkR.of_subset hsub hCA
  obtain ⟨v, tv, hv, htv, T', hInf, hDeq⟩ :=
    ihi hinf hWA hBA hLA hCA'
  have hWtp : Expr.WScoped 4 tp :=
    inferTypeCore_WScoped m.wf F hinf hWA
  have hBtp : tp.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf F hinf hWA hBA hLA
  have hLtp : Expr.LeavesBounded tp :=
    fun l hl => hLA l (inferTypeCore_fvarLeaves m.wf F hinf hWA l hl)
  have hCtp : CtxOkR μ m.cval env φ 4 Δ tp :=
    CtxOkR.of_subset (inferTypeCore_fvarLeaves m.wf F hinf hWA) hCA'
  have hDeq2 : DefEq μ env m.cval φ Δ tv vE :=
    ihd hde hWtp hBtp hLtp hWE hBE hLE hCtp hCE htv hvE
  have hI := (Infer.sound (m.toHyp φ) hInf ρ hsat).2
  have hD1 := DefEq.sound (m.toHyp φ) hDeq ρ hsat
  have hD2 := DefEq.sound (m.toHyp φ) hDeq2 ρ hsat
  exact ⟨interp V ρ v, by rw [← hD2, ← hD1]; exact hI⟩

/-! ## The substitution moves nothing the frame reads

`Expr.substConst0` rewrites `const` nodes and recurses only through
applications — in particular it never enters an `fvar` annotation.  So
with a closed replacement it leaves the leaf list, and everything the
depth-4 frame reads off it, exactly where it was. -/


/-! ## The frame's valuation, and what the statements denote to -/

/-- The certificate frame's valuation: the pinned operation at its own
name (through the annotated stored value), every dependency at its
storage.  `DivModClausesV`'s `val` is this, interpreted. -/
def dmVal (cval : TConstVal) (env : Env) (c : Name) (value' : Expr)
    (φ : Name → Nat) (n : Name) : VExpr :=
  cvalAt cval env c value' n (Level.substFn φ [] [])

/-- A stored dependency denotes to the frame's valuation at its
name. -/
theorem denote_dmDep {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} (φ : Name → Nat) {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (hne : n ≠ c) (d : Nat) :
    denote cval env φ d (Expr.substConst0 c value' (.const n []))
      = some (dmVal cval env c value' φ n) := by
  rw [show Expr.substConst0 c value' (.const n []) = .const n [] from by
    simp only [Expr.substConst0]
    rw [if_neg (fun hh => hne hh.1)]]
  rw [denote_const_nolevelsS hf hlp φ d, dmVal, cvalAt_ne hne]
  rfl

/-- The pinned operation itself denotes to the frame's valuation at
its own name: the substitution puts the annotated stored value there,
and that is what `cvalAt` names. -/
theorem denote_dmSelf {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    (hvf : value'.hasFvar = false)
    (hvb : value'.looseBVarsBounded 0 = true)
    {Vc : VExpr} (hV : denoteClosed cval env φ value' = some Vc)
    (d : Nat) :
    denote cval env φ d (Expr.substConst0 c value' (.const c []))
      = some (dmVal cval env c value' φ c) := by
  rw [show Expr.substConst0 c value' (.const c []) = value' from by
    simp [Expr.substConst0]]
  rw [denote_depth_closed hcl hvf hvb d]
  rw [dmVal, show Level.substFn φ ([] : List Name) ([] : List Level) = φ
    from funext fun _ => rfl, cvalAt_self hV]
  exact hV

/-! ## The four-entry frame is satisfied -/

/-- A four-entry closed context is satisfied slot by slot. -/
theorem sat_four {A0 A1 A2 A3 : VExpr} {ρ : Nat → V}
    (hc0 : VExpr.Closed A0) (hc1 : VExpr.Closed A1)
    (hc2 : VExpr.Closed A2) (hc3 : VExpr.Closed A3)
    (h0 : ρ 0 ∈ˢ interp V ρ A0) (h1 : ρ 1 ∈ˢ interp V ρ A1)
    (h2 : ρ 2 ∈ˢ interp V ρ A2) (h3 : ρ 3 ∈ˢ interp V ρ A3) :
    Sat V [A0, A1, A2, A3] ρ := by
  intro i A hi
  match i with
  | 0 =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    rwa [interp_closed V hc0 _ ρ]
  | 1 =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hi
    subst hi
    rwa [interp_closed V hc1 _ ρ]
  | 2 =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hi
    subst hi
    rwa [interp_closed V hc2 _ ρ]
  | 3 =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hi
    subst hi
    rwa [interp_closed V hc3 _ ρ]
  | n + 4 => simp at hi

/-! ## The pinned operations are functions on the frame's `Nat` -/


/-- A stored, pinned **binary** operation is a function on the frame's
`Nat`: its valuation applied to two members of `⟦Nat⟧` lands in the
codomain's. -/
theorem dmBinMem {env : Env} (m : EnvS V env) (φ : Name → Nat)
    {n : Name} {ci : ConstantInfo}
    {nm nm2 : Name} {mb mb2 : BinderMeta} {cn : Name}
    (hf : env.find? n = some ci)
    (hty : ci.toConstantVal.type = .forallE nm (.const natName [])
      (.forallE nm2 (.const natName []) (.const cn []) mb2) mb)
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    {ciC : ConstantInfo} (hfC : env.find? cn = some ciC)
    (hlpC : ciC.toConstantVal.levelParams = [])
    (ρ : Nat → V) {x y : V}
    (hx : x ∈ˢ interp V ρ (m.cval natName φ))
    (hy : y ∈ˢ interp V ρ (m.cval natName φ)) :
    SetTheory.app (SetTheory.app (interp V ρ (m.cval n φ)) x) y
      ∈ˢ interp V ρ (m.cval cn φ) := by
  obtain ⟨t, ht, hlaw⟩ := m.cval_memType hf φ
  rw [hty, denoteClosed] at ht
  simp only [denote_forallE, denote_const_nolevelsS hfN hlpN,
    denote_const_nolevelsS hfC hlpC, Expr.instantiate1] at ht
  obtain rfl := Option.some.inj ht
  have h1 := (hlaw ρ).1
  rw [interp_pi, show (fun a : V => interp V (cons V a ρ)
        (VExpr.pi (m.cval natName φ) (m.cval cn φ)))
      = (fun _ : V => piC (interp V ρ (m.cval natName φ))
          (fun _ => interp V ρ (m.cval cn φ))) from by
    funext a
    rw [interp_pi, interp_closed V (m.cval_closed natName φ) _ ρ]
    congr 1
    funext b
    exact interp_closed V (m.cval_closed cn φ) _ ρ] at h1
  exact app_mem_piC (app_mem_piC h1 hx) hy

/-- A stored, pinned **unary** operation (`Nat.log2`). -/
theorem dmUnMem {env : Env} (m : EnvS V env) (φ : Name → Nat)
    {n : Name} {ci : ConstantInfo}
    {nm : Name} {mb : BinderMeta} {cn : Name}
    (hf : env.find? n = some ci)
    (hty : ci.toConstantVal.type
      = .forallE nm (.const natName []) (.const cn []) mb)
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    {ciC : ConstantInfo} (hfC : env.find? cn = some ciC)
    (hlpC : ciC.toConstantVal.levelParams = [])
    (ρ : Nat → V) {x : V}
    (hx : x ∈ˢ interp V ρ (m.cval natName φ)) :
    SetTheory.app (interp V ρ (m.cval n φ)) x
      ∈ˢ interp V ρ (m.cval cn φ) := by
  obtain ⟨t, ht, hlaw⟩ := m.cval_memType hf φ
  rw [hty, denoteClosed] at ht
  simp only [denote_forallE, denote_const_nolevelsS hfN hlpN,
    denote_const_nolevelsS hfC hlpC, Expr.instantiate1] at ht
  obtain rfl := Option.some.inj ht
  have h1 := (hlaw ρ).1
  rw [interp_pi, show (fun a : V => interp V (cons V a ρ)
        (m.cval cn φ))
      = (fun _ : V => interp V ρ (m.cval cn φ)) from by
    funext a
    exact interp_closed V (m.cval_closed cn φ) _ ρ] at h1
  exact app_mem_piC h1 hx

/-! ## From an inhabited statement to an equation -/

/-- The `Eq.{1}` level assignment sends `u` to `1`. -/
theorem eqSubst_uN (φ : Name → Nat) :
    Level.substFn φ eqA.toConstantVal.levelParams [Level.zero.succ] uN
      = 1 := rfl

/-- The pinned `Eq`-spine's interpretation is the truth set of the
equation, so *inhabited* means *equal*. -/
theorem eqSpine_eq {env : Env} (m : EnvS V env) (φ : Name → Nat)
    (hEq : env.find? eqName = some eqA) (ρ : Nat → V)
    {A l r : VExpr}
    (hA : interp V ρ A ∈ˢ univ 1)
    (hl : interp V ρ l ∈ˢ interp V ρ A)
    (hr : interp V ρ r ∈ˢ interp V ρ A)
    {w : V} (hw : w ∈ˢ interp V ρ (VExpr.mkAppN (eqVS m φ) [A, l, r])) :
    interp V ρ l = interp V ρ r := by
  rw [eqVS] at hw
  rw [EqLawV.app₃ V m.eq_lawV hEq
    (Level.substFn φ eqA.toConstantVal.levelParams [Level.zero.succ])
    ρ A l r (by rw [eqSubst_uN]; exact hA) hl hr] at hw
  exact eq_of_mem_eqv hw

/-- The pinned `Eq`-spine, denoted: the head carries `Eq.{1}`, whose
level argument is not `[]`, so the operation substitution leaves it
alone. -/
theorem denote_eqSpine {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} (φ : Name → Nat)
    (hEq : env.find? eqName = some eqA) {A a b : Expr}
    {AV aV bV : VExpr} {d : Nat}
    (hA : denote cval env φ d (Expr.substConst0 c value' A) = some AV)
    (ha : denote cval env φ d (Expr.substConst0 c value' a) = some aV)
    (hb : denote cval env φ d (Expr.substConst0 c value' b) = some bV) :
    denote cval env φ d (Expr.substConst0 c value'
        (.app (.app (.app (.const eqName [.succ .zero]) A) a) b))
      = some (VExpr.mkAppN
          (cval eqName (Level.substFn φ eqA.toConstantVal.levelParams
            [Level.zero.succ])) [AV, aV, bV]) := by
  have hhead : denote cval env φ d
      (Expr.substConst0 c value' (.const eqName [.succ .zero]))
      = some (cval eqName (Level.substFn φ
          eqA.toConstantVal.levelParams [Level.zero.succ])) := by
    rw [show Expr.substConst0 c value' (.const eqName [.succ .zero])
        = .const eqName [.succ .zero] from by
      simp only [Expr.substConst0]
      rw [if_neg (by rintro ⟨-, hh⟩; exact nomatch hh)]]
    rw [denote_const, hEq]
    exact if_pos rfl
  have h1 : denote cval env φ d
      (.app (Expr.substConst0 c value' (.const eqName [.succ .zero]))
        (Expr.substConst0 c value' A))
      = some (.app (cval eqName (Level.substFn φ
          eqA.toConstantVal.levelParams [Level.zero.succ])) AV) := by
    rw [denote_app, hhead, hA]
  have h2 : denote cval env φ d
      (.app (.app (Expr.substConst0 c value' (.const eqName [.succ .zero]))
        (Expr.substConst0 c value' A)) (Expr.substConst0 c value' a))
      = some (.app (.app (cval eqName (Level.substFn φ
          eqA.toConstantVal.levelParams [Level.zero.succ])) AV) aV) := by
    rw [denote_app, h1, ha]
  show denote cval env φ d
      (.app (.app (.app (Expr.substConst0 c value'
        (.const eqName [.succ .zero]))
        (Expr.substConst0 c value' A)) (Expr.substConst0 c value' a))
        (Expr.substConst0 c value' b)) = _
  rw [denote_app, h2, hb]
  rfl

/-! ## The applied certificate's leaves

`divModCertApplied` opens the proof at `x`, `y` and one `fvar` per
hypothesis, carrying the hypothesis *type* as the annotation.  With an
`fvar`-free proof blob every leaf is one of those variables or comes
from a hypothesis type. -/



/-! ## Depth lifting: a telescope entry denotes one way, reads another

A hypothesis slot's entry is its type's denotation at the depth where
that type is *stated* (2 for the first hypothesis, 3 for the second);
what `CtxOkR` reads is the denotation at 4, which is the entry lifted
by exactly `Infer.bvar`'s own amount.  These are the two instances the
div/mod frame needs — the `V`-free twins of the TT lane's
`denote4_of_denote2`, whose presence there was the clue that the
entries are shallow. -/

/-- Depth 3 to depth 4. -/
theorem denote_lift1 {env : Env} {cval : TConstVal} {φ : Name → Nat}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ)) {e : Expr} {W : VExpr}
    (hfb : Expr.fvarsBelow 3 e)
    (h : denote cval env φ 3 e = some W) :
    denote cval env φ 4 e = some (W.liftN 1) := by
  rw [show (4 : Nat) = 3 + 1 from rfl, denote_weaken_top hcl hfb, h]
  rfl

/-- Depth 2 to depth 4. -/
theorem denote_lift2 {env : Env} {cval : TConstVal} {φ : Name → Nat}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ)) {e : Expr} {W : VExpr}
    (hfb : Expr.fvarsBelow 2 e)
    (h : denote cval env φ 2 e = some W) :
    denote cval env φ 4 e = some (W.liftN 2) := by
  have h3 : denote cval env φ 3 e = some (W.liftN 1) := by
    rw [denote_weaken_top hcl hfb, h]; rfl
  rw [show (4 : Nat) = 3 + 1 from rfl,
    denote_weaken_top hcl (Expr.fvarsBelow_mono (by omega) hfb), h3]
  simp only [Option.map_some]
  rw [VExpr.liftN_liftN_absorb W (Nat.le_refl 0) (Nat.zero_le _) 1]

/-! ### Why the slots are not built here

An earlier version of this layer supplied `certValueS` with
`CtxOkR.pinnedCtx`'s *closed-entry* form: `Δ.length = 4`, every entry
closed, and each leaf's annotation denoting to `Δ.getD (3 - l.1)`.
For the two `Nat` slots that is right.  For a **hypothesis** slot it is
jointly unsatisfiable: the slot's entry is the denotation of a
hypothesis type, which mentions `x` and `y` — it is `.bvar 3`/`.bvar 2`
at depth 4 — so it is not closed, and `pinnedCtx`'s `hcl` can never be
discharged.  The pair compiled and sat in the tree because no consumer
had exercised it (trap family, sixth shape: *jointly unsatisfiable
premises*).

`CtxOkR` itself is **slack** — it asks for `Infer Δ (.bvar (d-1-l.1)) T'`
and `DefEq T' T`, not for entry equality — so the frame is satisfiable
with `Δ`'s hypothesis entries at depth 2 and `Infer.bvar`'s own
`liftN 2` supplying the depth-4 denotation.  So `certValueS`,
`dmCertEq1` and `dmCertEq2` take `CtxOkR` **directly**: strictly more
general, and it puts the lift where the caller can see it. -/

/-! ## One certificate, packaged -/


/-- **A two-hypothesis certificate, discharged**: at a frame
satisfying its hypotheses, the pinned equation's two sides have equal
interpretation. -/
theorem dmCertEq2 {μ : CheckMode} {F : Nat} {env : Env}
    (m : EnvS V env) (φ : Name → Nat) {c : Name} {value' : Expr}
    (hEq : env.find? eqName = some eqA) (hneN : natName ≠ c)
    (hvf : value'.hasFvar = false)
    (hvb : value'.looseBVarsBounded 0 = true)
    {h1 h2 l r proof : Expr}
    (hfacts : CertRunFacts μ env F c value'
      ([h1, h2], .app (.app (.app (.const eqName [.succ .zero])
        (.const natName [])) l) r) proof)
    (hl1 : dmLeavesOk h1 = true) (hl2 : dmLeavesOk h2 = true)
    (hlL : dmLeavesOk l = true) (hlR : dmLeavesOk r = true)
    (hw1 : Expr.wscopedB 2 h1 = true) (hw2 : Expr.wscopedB 3 h2 = true)
    (hwL : Expr.wscopedB 4 l = true) (hwR : Expr.wscopedB 4 r = true)
    (hb1 : h1.looseBVarsBounded 0 = true)
    (hb2 : h2.looseBVarsBounded 0 = true)
    (hbL : l.looseBVarsBounded 0 = true)
    (hbR : r.looseBVarsBounded 0 = true)
    {natV lV rV : VExpr} {Δ : List VExpr}
    (hnat : denote m.cval env φ 4 (Expr.const natName []) = some natV)
    (hdl : denote m.cval env φ 4 (Expr.substConst0 c value' l)
      = some lV)
    (hdr : denote m.cval env φ 4 (Expr.substConst0 c value' r)
      = some rV)
    (hCA : CtxOkR μ m.cval env φ 4 Δ (divModCertApplied
      (Expr.substConstAll c value' proof)
      ([h1, h2].map (Expr.substConst0 c value'))))
    (hCE : CtxOkR μ m.cval env φ 4 Δ (Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero])
        (.const natName [])) l) r)))
    (ρ : Nat → V) (hsat : Sat V Δ ρ)
    (hNU : interp V ρ natV ∈ˢ univ 1)
    (hlm : interp V ρ lV ∈ˢ interp V ρ natV)
    (hrm : interp V ρ rV ∈ˢ interp V ρ natV) :
    interp V ρ lV = interp V ρ rV := by
  obtain ⟨hguard, appliedA, tp, hann, hinf, hde⟩ := id hfacts
  simp only [divModCertGuard, Bool.and_eq_true, Bool.not_eq_true'] at hguard
  obtain ⟨⟨⟨⟨⟨hpb, hpf⟩, -⟩, -⟩, -⟩, -⟩ := hguard
  -- the substituted hypothesis types
  have hw1' : Expr.WScoped 2 (Expr.substConst0 c value' h1) :=
    Expr.WScoped.of_wscopedB (wscopedB_substConst0 hvf h1 hw1)
  have hw2' : Expr.WScoped 3 (Expr.substConst0 c value' h2) :=
    Expr.WScoped.of_wscopedB (wscopedB_substConst0 hvf h2 hw2)
  have hb1' := looseBVarsBounded_substConst0 (n := c) hvb h1 hb1
  have hb2' := looseBVarsBounded_substConst0 (n := c) hvb h2 hb2
  obtain ⟨hWA, hBA⟩ := dmApplied2_frame hpf hpb hw1' hw2'
  -- the applied term is leaf-bounded
  have hLA : Expr.LeavesBounded (divModCertApplied
      (Expr.substConstAll c value' proof)
      [Expr.substConst0 c value' h1, Expr.substConst0 c value' h2]) := by
    intro lf hlf
    rcases divModCertApplied_mem2 hpf hlf with rfl | rfl | rfl | hm |
      rfl | hm
    · rfl
    · rfl
    · exact hb1'
    · exact dmLeavesOk_leavesBounded
        (dmLeavesOk_substConst0 hvf hl1) lf hm
    · exact hb2'
    · exact dmLeavesOk_leavesBounded
        (dmLeavesOk_substConst0 hvf hl2) lf hm
  -- the statement's frame
  have hnat' : denote m.cval env φ 4
      (Expr.substConst0 c value' (Expr.const natName [])) = some natV := by
    rwa [show Expr.substConst0 c value' (Expr.const natName [])
        = Expr.const natName [] from by
      simp only [Expr.substConst0]
      rw [if_neg (fun hh => hneN hh.1)]]
  have hvE := denote_eqSpine (cval := m.cval) (c := c) (value' := value')
    φ hEq hnat' hdl hdr
  have hlE : dmLeavesOk (Expr.app (.app (.app
      (.const eqName [.succ .zero]) (.const natName [])) l) r) = true := by
    simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append,
      List.all_append, Bool.and_eq_true]
    exact ⟨hlL, hlR⟩
  have hwE : Expr.WScoped 4 (Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero])
        (.const natName [])) l) r)) :=
    Expr.WScoped.of_wscopedB (wscopedB_substConst0 hvf _
      (by simp [Expr.wscopedB, hwL, hwR]))
  have hbE : (Expr.substConst0 c value' (.app (.app (.app
      (.const eqName [.succ .zero]) (.const natName [])) l) r)).looseBVarsBounded 0
      = true :=
    looseBVarsBounded_substConst0 hvb _
      (by simp [Expr.looseBVarsBounded, hbL, hbR])
  have hLE : Expr.LeavesBounded (Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero])
        (.const natName [])) l) r)) :=
    dmLeavesOk_leavesBounded (dmLeavesOk_substConst0 hvf hlE)
  -- the certificate
  have hw := certValueS m φ hfacts (Δ := Δ) hWA hBA hLA hCA
    hwE hbE hLE hCE hvE ρ hsat
  obtain ⟨w, hw'⟩ := hw
  exact eqSpine_eq m φ hEq ρ hNU hlm hrm hw'

/-- **A one-hypothesis certificate, discharged**: at a frame
satisfying its hypotheses, the pinned equation's two sides have equal
interpretation. -/
theorem dmCertEq1 {μ : CheckMode} {F : Nat} {env : Env}
    (m : EnvS V env) (φ : Name → Nat) {c : Name} {value' : Expr}
    (hEq : env.find? eqName = some eqA) (hneN : natName ≠ c)
    (hvf : value'.hasFvar = false)
    (hvb : value'.looseBVarsBounded 0 = true)
    {h1 l r proof : Expr}
    (hfacts : CertRunFacts μ env F c value'
      ([h1], .app (.app (.app (.const eqName [.succ .zero])
        (.const natName [])) l) r) proof)
    (hl1 : dmLeavesOk h1 = true)
    (hlL : dmLeavesOk l = true) (hlR : dmLeavesOk r = true)
    (hw1 : Expr.wscopedB 2 h1 = true)
    (hwL : Expr.wscopedB 4 l = true) (hwR : Expr.wscopedB 4 r = true)
    (hb1 : h1.looseBVarsBounded 0 = true)
    (hbL : l.looseBVarsBounded 0 = true)
    (hbR : r.looseBVarsBounded 0 = true)
    {natV lV rV : VExpr} {Δ : List VExpr}
    (hnat : denote m.cval env φ 4 (Expr.const natName []) = some natV)
    (hdl : denote m.cval env φ 4 (Expr.substConst0 c value' l)
      = some lV)
    (hdr : denote m.cval env φ 4 (Expr.substConst0 c value' r)
      = some rV)
    (hCA : CtxOkR μ m.cval env φ 4 Δ (divModCertApplied
      (Expr.substConstAll c value' proof)
      ([h1].map (Expr.substConst0 c value'))))
    (hCE : CtxOkR μ m.cval env φ 4 Δ (Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero])
        (.const natName [])) l) r)))
    (ρ : Nat → V) (hsat : Sat V Δ ρ)
    (hNU : interp V ρ natV ∈ˢ univ 1)
    (hlm : interp V ρ lV ∈ˢ interp V ρ natV)
    (hrm : interp V ρ rV ∈ˢ interp V ρ natV) :
    interp V ρ lV = interp V ρ rV := by
  obtain ⟨hguard, appliedA, tp, hann, hinf, hde⟩ := id hfacts
  simp only [divModCertGuard, Bool.and_eq_true, Bool.not_eq_true'] at hguard
  obtain ⟨⟨⟨⟨⟨hpb, hpf⟩, -⟩, -⟩, -⟩, -⟩ := hguard
  -- the substituted hypothesis types
  have hw1' : Expr.WScoped 2 (Expr.substConst0 c value' h1) :=
    Expr.WScoped.of_wscopedB (wscopedB_substConst0 hvf h1 hw1)
  have hb1' := looseBVarsBounded_substConst0 (n := c) hvb h1 hb1
  obtain ⟨hWA, hBA⟩ := dmApplied1_frame hpf hpb hw1'
  -- the applied term is leaf-bounded
  have hLA : Expr.LeavesBounded (divModCertApplied
      (Expr.substConstAll c value' proof)
      [Expr.substConst0 c value' h1]) := by
    intro lf hlf
    rcases divModCertApplied_mem1 hpf hlf with rfl | rfl | rfl | hm
    · rfl
    · rfl
    · exact hb1'
    · exact dmLeavesOk_leavesBounded
        (dmLeavesOk_substConst0 hvf hl1) lf hm
  -- the statement's frame
  have hnat' : denote m.cval env φ 4
      (Expr.substConst0 c value' (Expr.const natName [])) = some natV := by
    rwa [show Expr.substConst0 c value' (Expr.const natName [])
        = Expr.const natName [] from by
      simp only [Expr.substConst0]
      rw [if_neg (fun hh => hneN hh.1)]]
  have hvE := denote_eqSpine (cval := m.cval) (c := c) (value' := value')
    φ hEq hnat' hdl hdr
  have hlE : dmLeavesOk (Expr.app (.app (.app
      (.const eqName [.succ .zero]) (.const natName [])) l) r) = true := by
    simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append,
      List.all_append, Bool.and_eq_true]
    exact ⟨hlL, hlR⟩
  have hwE : Expr.WScoped 4 (Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero])
        (.const natName [])) l) r)) :=
    Expr.WScoped.of_wscopedB (wscopedB_substConst0 hvf _
      (by simp [Expr.wscopedB, hwL, hwR]))
  have hbE : (Expr.substConst0 c value' (.app (.app (.app
      (.const eqName [.succ .zero]) (.const natName [])) l) r)).looseBVarsBounded 0
      = true :=
    looseBVarsBounded_substConst0 hvb _
      (by simp [Expr.looseBVarsBounded, hbL, hbR])
  have hLE : Expr.LeavesBounded (Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero])
        (.const natName [])) l) r)) :=
    dmLeavesOk_leavesBounded (dmLeavesOk_substConst0 hvf hlE)
  -- the certificate
  have hw := certValueS m φ hfacts (Δ := Δ) hWA hBA hLA hCA
    hwE hbE hLE hCE hvE ρ hsat
  obtain ⟨w, hw'⟩ := hw
  exact eqSpine_eq m φ hEq ρ hNU hlm hrm hw'

/-! ## The statements' vocabulary, denoted -/

/-- A binary application in a statement. -/
theorem denote_dmApp2 {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} {φ : Name → Nat} {d : Nat} {f a b : Expr}
    {fV aV bV : VExpr}
    (hf : denote cval env φ d (Expr.substConst0 c value' f) = some fV)
    (ha : denote cval env φ d (Expr.substConst0 c value' a) = some aV)
    (hb : denote cval env φ d (Expr.substConst0 c value' b) = some bV) :
    denote cval env φ d (Expr.substConst0 c value' (.app (.app f a) b))
      = some (.app (.app fV aV) bV) := by
  have h1 : denote cval env φ d
      (.app (Expr.substConst0 c value' f) (Expr.substConst0 c value' a))
      = some (.app fV aV) := by rw [denote_app, hf, ha]
  show denote cval env φ d (.app (.app (Expr.substConst0 c value' f)
    (Expr.substConst0 c value' a)) (Expr.substConst0 c value' b)) = _
  rw [denote_app, h1, hb]

/-- A unary application in a statement. -/
theorem denote_dmApp1 {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} {φ : Name → Nat} {d : Nat} {f a : Expr}
    {fV aV : VExpr}
    (hf : denote cval env φ d (Expr.substConst0 c value' f) = some fV)
    (ha : denote cval env φ d (Expr.substConst0 c value' a) = some aV) :
    denote cval env φ d (Expr.substConst0 c value' (.app f a))
      = some (.app fV aV) := by
  show denote cval env φ d (.app (Expr.substConst0 c value' f)
    (Expr.substConst0 c value' a)) = _
  rw [denote_app, hf, ha]

/-- The frame variable `x` denotes to the third de Bruijn slot. -/
theorem denote_dmX {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} {φ : Name → Nat} {nm : Name} :
    denote cval env φ 4 (Expr.substConst0 c value'
      (.fvar 0 nm (.const natName []))) = some (.bvar 3) := by
  show denote cval env φ 4 (.fvar 0 nm (.const natName [])) = _
  rw [denote_fvar]

/-- The frame variable `y` denotes to the second. -/
theorem denote_dmY {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} {φ : Name → Nat} {nm : Name} :
    denote cval env φ 4 (Expr.substConst0 c value'
      (.fvar 1 nm (.const natName []))) = some (.bvar 2) := by
  show denote cval env φ 4 (.fvar 1 nm (.const natName [])) = _
  rw [denote_fvar]

/-! ## The pinned operation's own typing, through the value front door

`c` is not stored in `env` — it is what the declaration is installing —
so its function-space membership comes from the value front door's
`Infer`/`DefEq` pair rather than from `EnvS.mem_type`. -/

/-- The pinned operation, applied to two members of the frame's `Nat`,
lands in the codomain — read off the checked value's own inference. -/
theorem dmSelfMem {μ : CheckMode} {F : Nat} {env : Env}
    (m : EnvS V env) (φ : Name → Nat) {cv : ConstantVal}
    {type' value value' : Expr} {nm nm2 : Name} {mb mb2 : BinderMeta}
    {cn : Name}
    (hvfr : ValueFrontR μ F env m.cval cv value type' value')
    (hty : type' = .forallE nm (.const natName [])
      (.forallE nm2 (.const natName []) (.const cn []) mb2) mb)
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    {ciC : ConstantInfo} (hfC : env.find? cn = some ciC)
    (hlpC : ciC.toConstantVal.levelParams = [])
    {Vv : VExpr}
    (hVv : denoteClosed m.cval env φ value' = some Vv)
    (ρ : Nat → V) {x y : V}
    (hx : x ∈ˢ interp V ρ (m.cval natName φ))
    (hy : y ∈ˢ interp V ρ (m.cval natName φ)) :
    SetTheory.app (SetTheory.app (interp V ρ Vv) x) y
      ∈ˢ interp V ρ (m.cval cn φ) := by
  obtain ⟨-, -, -, -, -, -, hfront⟩ := hvfr
  obtain ⟨Tv, Vv', tv, hTv, hVv', hInf, hDeq⟩ := hfront φ
  obtain rfl : Vv' = Vv := by rw [hVv'] at hVv; exact Option.some.inj hVv
  rw [hty, denoteClosed] at hTv
  simp only [denote_forallE, denote_const_nolevelsS hfN hlpN,
    denote_const_nolevelsS hfC hlpC, Expr.instantiate1] at hTv
  obtain rfl := Option.some.inj hTv
  have h1 := (Infer.sound (m.toHyp φ) hInf ρ (Sat_nil V ρ)).2
  rw [DefEq.sound (m.toHyp φ) hDeq ρ (Sat_nil V ρ)] at h1
  rw [interp_pi, show (fun a : V => interp V (cons V a ρ)
        (VExpr.pi (m.cval natName φ) (m.cval cn φ)))
      = (fun _ : V => piC (interp V ρ (m.cval natName φ))
          (fun _ => interp V ρ (m.cval cn φ))) from by
    funext a
    rw [interp_pi, interp_closed V (m.cval_closed natName φ) _ ρ]
    congr 1
    funext b
    exact interp_closed V (m.cval_closed cn φ) _ ρ] at h1
  exact app_mem_piC (app_mem_piC h1 hx) hy

/-- `Nat.succ`'s pinned shape, inverted. -/
theorem natSuccOk_ty {ci : ConstantInfo} (h : natSuccOk (some ci) = true) :
    ∃ nm mb, ci.toConstantVal.type
      = .forallE nm (.const natName []) (.const natName []) mb := by
  cases ci with
  | ctorInfo cvS nP nF =>
    simp only [natSuccOk, Bool.and_eq_true] at h
    obtain ⟨-, h2⟩ := h
    revert h2
    match hm : cvS.type with
    | .forallE nm (.const c1 []) (.const c2 []) mb =>
      intro h2
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact ⟨nm, mb, by rw [h2.1, h2.2]⟩
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _
    | .forallE _ (.bvar _) _ _ | .forallE _ (.fvar _ _ _) _ _
    | .forallE _ (.sort _) _ _ | .forallE _ (.app _ _) _ _
    | .forallE _ (.lam _ _ _ _) _ _ | .forallE _ (.letE _ _ _ _) _ _
    | .forallE _ (.lit _) _ _ | .forallE _ (.proj _ _ _) _ _
    | .forallE _ (.forallE _ _ _ _) _ _
    | .forallE _ (.const _ (_ :: _)) _ _
    | .forallE _ (.const _ []) (.bvar _) _
    | .forallE _ (.const _ []) (.fvar _ _ _) _
    | .forallE _ (.const _ []) (.sort _) _
    | .forallE _ (.const _ []) (.app _ _) _
    | .forallE _ (.const _ []) (.lam _ _ _ _) _
    | .forallE _ (.const _ []) (.letE _ _ _ _) _
    | .forallE _ (.const _ []) (.lit _) _
    | .forallE _ (.const _ []) (.proj _ _ _) _
    | .forallE _ (.const _ []) (.forallE _ _ _ _) _
    | .forallE _ (.const _ []) (.const _ (_ :: _)) _ =>
      intro h2; exact nomatch h2
  | _ => exact nomatch h

/-! ## The statements' fragment, denoted and evaluated in one step

Every side of every div/mod certificate statement is built from the
pinned operation, its stored dependencies, and the two frame
variables.  That grammar is `dmFragOk`; `dmEvalV` is its value, and
`dmDenEval` says the denotation interprets to it.  With those, a
clause is: denote the two sides, read the equation off the
certificate, and `simp [dmEvalV]` — the `app`-chains
`DivModClausesV` asks for are literally what `dmEvalV` computes. -/

/-- The certificate statements' expression grammar. -/
def dmFragOk (c : Name) (ns : List Name) : Expr → Bool
  | Expr.const n us => (n == c || ns.contains n) && us.isEmpty
  | Expr.app f a => dmFragOk c ns f && dmFragOk c ns a
  | Expr.fvar i _ ty =>
    (i == 0 || i == 1) && ty == Expr.const natName []
  | _ => false

/-- **The fragment, denoted and evaluated**, at any frame depth: the
statements are read at 4, the hypothesis *types* at 2 and 3. -/
theorem dmDenEval {env : Env} (m : EnvS V env) (φ : Name → Nat)
    {c : Name} {value' : Expr} {ns : List Name} {d : Nat}
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hvf : value'.hasFvar = false)
    (hvb : value'.looseBVarsBounded 0 = true)
    {Vc : VExpr} (hVc : denoteClosed m.cval env φ value' = some Vc)
    (hstore : ∀ n ∈ ns, n = c ∨ (n ≠ c ∧ ∃ ci,
      env.find? n = some ci ∧ ci.toConstantVal.levelParams = [])) :
    ∀ e : Expr, dmFragOk c ns e = true →
      ∃ eV, denote m.cval env φ d (Expr.substConst0 c value' e)
          = some eV ∧
        ∀ ρd : Nat → V, interp V ρd eV
          = dmEvalV V (fun n => interp V ρd
              (dmVal m.cval env c value' φ n))
              (ρd (d - 1 - 0)) (ρd (d - 1 - 1)) e
  | .const n us, h => by
    simp only [dmFragOk, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq, List.isEmpty_iff] at h
    obtain ⟨hn, rfl⟩ := h
    rcases hn with rfl | hn
    · exact ⟨_, denote_dmSelf φ hcl hvf hvb hVc d, fun ρd => rfl⟩
    · rcases hstore n (by simpa using hn) with rfl | ⟨hnc, ci, hfi, hlpi⟩
      · exact ⟨_, denote_dmSelf φ hcl hvf hvb hVc d, fun ρd => rfl⟩
      · exact ⟨_, denote_dmDep φ hfi hlpi hnc d, fun ρd => rfl⟩
  | .app f a, h => by
    simp only [dmFragOk, Bool.and_eq_true] at h
    obtain ⟨fV, hfd, hfe⟩ :=
      dmDenEval m φ (d := d) hcl hvf hvb hVc hstore f h.1
    obtain ⟨aV, had, hae⟩ :=
      dmDenEval m φ (d := d) hcl hvf hvb hVc hstore a h.2
    exact ⟨_, denote_dmApp1 hfd had, fun ρd => by
      rw [interp_app, hfe, hae, dmEvalV_app]⟩
  | .fvar i nm ty, h => by
    simp only [dmFragOk, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    rcases hi with rfl | rfl
    · refine ⟨.bvar (d - 1 - 0), ?_, fun ρd => by
        simp [dmEvalV_fvar]⟩
      show denote m.cval env φ d
        (.fvar 0 nm (.const natName [])) = _
      rw [denote_fvar]
    · refine ⟨.bvar (d - 1 - 1), ?_, fun ρd => by
        simp [dmEvalV_fvar]⟩
      show denote m.cval env φ d
        (.fvar 1 nm (.const natName [])) = _
      rw [denote_fvar]
  | .bvar _, h | .sort _, h | .lam _ _ _ _, h | .letE _ _ _ _, h
  | .forallE _ _ _ _, h | .lit _, h | .proj _ _ _, h => nomatch h

/-- **The div/mod frame, satisfied.**  The two `Nat` slots take `x`
and `y`; each hypothesis slot is read in its *own* shifted
environment, which is what makes a non-closed entry legitimate. -/
theorem sat_dm {A0 A1 natV : VExpr} {ρ : Nat → V} {a b yy xx : V}
    (hclN : VExpr.Closed natV)
    (h0 : a ∈ˢ interp V (cons V b (cons V yy (cons V xx ρ))) A0)
    (h1 : b ∈ˢ interp V (cons V yy (cons V xx ρ)) A1)
    (h2 : yy ∈ˢ interp V ρ natV)
    (h3 : xx ∈ˢ interp V ρ natV) :
    Sat V [A0, A1, natV, natV]
      (cons V a (cons V b (cons V yy (cons V xx ρ)))) := by
  intro i A hi
  match i with
  | 0 =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact h0
  | 1 =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hi
    subst hi
    exact h1
  | 2 =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hi
    subst hi
    rw [interp_closed V hclN _ ρ]
    exact h2
  | 3 =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hi
    subst hi
    rw [interp_closed V hclN _ ρ]
    exact h3
  | n + 4 => simp at hi

/-! ## The frame, built — in the lift-carrying form -/

/-- A statement's leaves sit in the two `Nat` slots, whose entry is
closed and so equal to its own lift. -/
theorem dmCtxOk_stmt {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} {μ : CheckMode} (φ : Name → Nat)
    {H1 H2 natV : VExpr}
    (hvf : value'.hasFvar = false) (hclN : VExpr.Closed natV)
    (hnat : denote cval env φ 4 (Expr.const natName []) = some natV)
    {e : Expr} (h : dmLeavesOk e = true) :
    CtxOkR μ cval env φ 4 [H2, H1, natV, natV]
      (Expr.substConst0 c value' e) := by
  refine CtxOkR.pinnedCtxLift rfl (fun l hl => ?_)
  rw [fvarLeaves_substConst0 (n := c) hvf e] at hl
  rcases dmLeavesOk_mem h hl with rfl | rfl
  · exact ⟨by omega, trivial, by
      rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩
  · exact ⟨by omega, trivial, by
      rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩

/-- The one-hypothesis applied certificate's frame: the hypothesis
entry is its type's denotation at depth **2**, which is where the type
is stated. -/
theorem dmCtxOk_applied1 {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} {μ : CheckMode} (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {H1 H2 natV : VExpr}
    (hvf : value'.hasFvar = false) (hclN : VExpr.Closed natV)
    (hnat : denote cval env φ 4 (Expr.const natName []) = some natV)
    {h1 p : Expr} (hp : p.hasFvar = false)
    (hl1 : dmLeavesOk h1 = true)
    (hfb1 : Expr.fvarsBelow 2 (Expr.substConst0 c value' h1))
    (hd1 : denote cval env φ 2 (Expr.substConst0 c value' h1)
      = some H1) :
    CtxOkR μ cval env φ 4 [H2, H1, natV, natV]
      (divModCertApplied p [Expr.substConst0 c value' h1]) := by
  refine CtxOkR.pinnedCtxLift rfl (fun l hl => ?_)
  rcases divModCertApplied_mem1 hp hl with rfl | rfl | rfl | hm
  · exact ⟨by omega, trivial, by
      rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩
  · exact ⟨by omega, trivial, by
      rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩
  · exact ⟨by omega, hfb1, denote_lift2 hcl hfb1 hd1⟩
  · rw [fvarLeaves_substConst0 (n := c) hvf h1] at hm
    rcases dmLeavesOk_mem hl1 hm with rfl | rfl
    · exact ⟨by omega, trivial, by
        rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩
    · exact ⟨by omega, trivial, by
        rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩

/-- The two-hypothesis applied certificate's frame: the second
hypothesis entry is stated at depth **3**. -/
theorem dmCtxOk_applied2 {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} {μ : CheckMode} (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {H1 H2 natV : VExpr}
    (hvf : value'.hasFvar = false) (hclN : VExpr.Closed natV)
    (hnat : denote cval env φ 4 (Expr.const natName []) = some natV)
    {h1 h2 p : Expr} (hp : p.hasFvar = false)
    (hl1 : dmLeavesOk h1 = true) (hl2 : dmLeavesOk h2 = true)
    (hfb1 : Expr.fvarsBelow 2 (Expr.substConst0 c value' h1))
    (hfb2 : Expr.fvarsBelow 3 (Expr.substConst0 c value' h2))
    (hd1 : denote cval env φ 2 (Expr.substConst0 c value' h1)
      = some H1)
    (hd2 : denote cval env φ 3 (Expr.substConst0 c value' h2)
      = some H2) :
    CtxOkR μ cval env φ 4 [H2, H1, natV, natV]
      (divModCertApplied p [Expr.substConst0 c value' h1,
        Expr.substConst0 c value' h2]) := by
  refine CtxOkR.pinnedCtxLift rfl (fun l hl => ?_)
  rcases divModCertApplied_mem2 hp hl with rfl | rfl | rfl | hm |
    rfl | hm
  · exact ⟨by omega, trivial, by
      rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩
  · exact ⟨by omega, trivial, by
      rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩
  · exact ⟨by omega, hfb1, denote_lift2 hcl hfb1 hd1⟩
  · rw [fvarLeaves_substConst0 (n := c) hvf h1] at hm
    rcases dmLeavesOk_mem hl1 hm with rfl | rfl
    · exact ⟨by omega, trivial, by
        rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩
    · exact ⟨by omega, trivial, by
        rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩
  · exact ⟨by omega, hfb2, denote_lift1 hcl hfb2 hd2⟩
  · rw [fvarLeaves_substConst0 (n := c) hvf h2] at hm
    rcases dmLeavesOk_mem hl2 hm with rfl | rfl
    · exact ⟨by omega, trivial, by
        rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩
    · exact ⟨by omega, trivial, by
        rw [hnat]; simp [VExpr.liftN_eq_self_of_closed hclN]⟩

/-! ## The install obligation's preamble -/

set_option maxHeartbeats 6400000 in
/-- **The div/mod frame, assembled from the guards.**  Everything the
nine operations' clauses are read against: the pinned operation's own
denotation and type, its dependencies' function-space memberships, the
frame's `Nat` and `Bool` with their universes, and the pinned `Eq`.

This is `DivModPinS`'s whole preamble; what remains of that obligation
is the nine clause blocks, each of which denotes two statement sides
(`dmDenEval`), reads the equation off a certificate (`dmCertEq1`/`2`)
and matches it against `DivModClausesV`'s `app`-chain. -/
theorem dmFrameS {μ : CheckMode} {F : Nat} {env : Env} (m : EnvS V env)
    {cv : ConstantVal} {type' value value' : Expr}
    {hint : ReducibilityHint}
    (hmem : cv.name ∈ natDivModNames)
    (hvfr : ValueFrontR μ F env m.cval cv value type' value')
    (hgenv : divModEnvGuard ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩
      value' hint :: env.consts⟩ cv.name = true)
    (φ : Name → Nat) :
    ∃ (ciN : ConstantInfo) (ciB : ConstantInfo) (Vc : VExpr),
      env.find? natName = some ciN ∧
      ciN.toConstantVal.levelParams = [] ∧
      env.find? boolName = some ciB ∧
      ciB.toConstantVal.levelParams = [] ∧
      env.find? eqName = some eqA ∧
      denoteClosed m.cval env φ value' = some Vc ∧
      dmVal m.cval env cv.name value' φ cv.name = Vc ∧
      cvalAt m.cval env cv.name value' natName
        (Level.substFn φ ([] : List Name) ([] : List Level))
        = m.cval natName φ ∧
      (∀ ρ' : Nat → V, interp V ρ' (m.cval natName φ) ∈ˢ univ 1) ∧
      (∀ ρ' : Nat → V, interp V ρ' (m.cval boolName φ) ∈ˢ univ 1) ∧
      (∀ (ρ' : Nat → V) (a b : V),
        a ∈ˢ interp V ρ' (m.cval natName φ) →
        b ∈ˢ interp V ρ' (m.cval natName φ) →
        SetTheory.app (SetTheory.app
          (interp V ρ' (m.cval natBleName φ)) a) b
          ∈ˢ interp V ρ' (m.cval boolName φ)) ∧
      (∀ n ∈ natOpDeps cv.name, n ≠ cv.name →
        (n = natPredName || n = natLog2Name) = false →
        (n = natBeqName || n = natBleName) = false →
        ∀ (ρ' : Nat → V) (a b : V),
          a ∈ˢ interp V ρ' (m.cval natName φ) →
          b ∈ˢ interp V ρ' (m.cval natName φ) →
          SetTheory.app (SetTheory.app (interp V ρ' (m.cval n φ)) a) b
            ∈ˢ interp V ρ' (m.cval natName φ)) ∧
      ((decide (cv.name = natLog2Name) = false →
          ∃ nm nm2 mb mb2, type' = .forallE nm (.const natName [])
            (.forallE nm2 (.const natName []) (.const natName []) mb2)
            mb) ∧
        (cv.name = natLog2Name →
          ∃ nm mb, type' = .forallE nm (.const natName [])
            (.const natName []) mb)) ∧
      (∀ n ∈ natOpDeps cv.name ++ [natSuccName, natZeroName,
          boolTrueName, boolFalseName],
        n = cv.name ∨ (n ≠ cv.name ∧ ∃ ci, env.find? n = some ci ∧
          ci.toConstantVal.levelParams = [])) ∧
      (∀ (bn : Name), bn = boolTrueName ∨ bn = boolFalseName →
        ∀ ρ' : Nat → V, interp V ρ' (m.cval bn φ)
          ∈ˢ interp V ρ' (m.cval boolName φ)) ∧
      (∀ ρ' : Nat → V, interp V ρ' (m.cval natZeroName φ)
        ∈ˢ interp V ρ' (m.cval natName φ)) ∧
      (∀ (ρ' : Nat → V) (a : V),
        a ∈ˢ interp V ρ' (m.cval natName φ) →
        SetTheory.app (interp V ρ' (m.cval natSuccName φ)) a
          ∈ˢ interp V ρ' (m.cval natName φ)) := by
  -- the guards, unpacked
  simp only [divModEnvGuard, Bool.and_eq_true] at hgenv
  obtain ⟨⟨⟨⟨hnog, hdeps⟩, hEq2⟩, hbT⟩, hbF⟩ := hgenv
  -- none of the names the frame reads is the operation being installed
  have hne : ∀ n ∈ ([natName, natZeroName, natSuccName, boolName,
      boolTrueName, boolFalseName, eqName] : List Name),
      n ≠ cv.name := by
    intro n hn
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
      or_false] at hmem hn
    rcases hmem with h|h|h|h|h|h|h|h|h <;>
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      (rw [h]; decide)
  -- lookups transfer from the extended environment to this one
  have hdown : ∀ (n : Name) (ci : ConstantInfo), n ≠ cv.name →
      (⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
        env.consts⟩ : Env).find? n = some ci →
      env.find? n = some ci := by
    intro n ci hnn hf
    rwa [Env.find?_cons, if_neg (fun hh => hnn hh.symm)] at hf
  -- the literal-support constants, at this environment
  simp only [natOpGuard, Bool.and_eq_true] at hnog
  obtain ⟨⟨hlit, -⟩, hnogFull⟩ := hnog
  simp only [natLitSupported, Bool.and_eq_true] at hlit
  obtain ⟨⟨hnat, hzero⟩, hsucc⟩ := hlit
  obtain ⟨cvN, capsN, hfN, hlpN, htyN⟩ :
      ∃ cvN capsN, env.find? natName = some (.indInfo cvN capsN) ∧
        cvN.levelParams = [] ∧ cvN.type = .sort (.succ .zero) := by
    revert hnat
    cases hf : (⟨ConstantInfo.defnInfo ⟨cv.name, cv.levelParams, type'⟩
        value' hint :: env.consts⟩ : Env).find? natName with
    | none => intro h; exact nomatch h
    | some ci =>
      cases ci with
      | indInfo cvN capsN =>
        intro h
        simp only [natIndOk, Bool.and_eq_true, List.isEmpty_iff,
          beq_iff_eq] at h
        exact ⟨cvN, capsN, hdown _ _ (hne _ (by simp)) hf, h.1, h.2⟩
      | _ => intro h; exact nomatch h
  obtain ⟨ciZ, hfZ, htyZ⟩ :
      ∃ ciZ, env.find? natZeroName = some ciZ ∧
        ciZ.toConstantVal.type = .const natName [] := by
    revert hzero
    cases hf : (⟨ConstantInfo.defnInfo ⟨cv.name, cv.levelParams, type'⟩
        value' hint :: env.consts⟩ : Env).find? natZeroName with
    | none => intro h; exact nomatch h
    | some ci =>
      cases ci with
      | ctorInfo cvZ nP nF =>
        intro h
        simp only [natZeroOk, Bool.and_eq_true, List.isEmpty_iff,
          beq_iff_eq] at h
        exact ⟨_, hdown _ _ (hne _ (by simp)) hf, h.2⟩
      | _ => intro h; exact nomatch h
  obtain ⟨ciS, hfS, htyS⟩ :
      ∃ ciS, env.find? natSuccName = some ciS ∧
        ∃ nmS mbS, ciS.toConstantVal.type
          = .forallE nmS (.const natName []) (.const natName []) mbS := by
    revert hsucc
    cases hf : (⟨ConstantInfo.defnInfo ⟨cv.name, cv.levelParams, type'⟩
        value' hint :: env.consts⟩ : Env).find? natSuccName with
    | none => intro h; exact nomatch h
    | some ci =>
      intro h
      exact ⟨ci, hdown _ _ (hne _ (by simp)) hf, natSuccOk_ty h⟩
  have hEqE : env.find? eqName = some eqA :=
    hdown _ _ (hne _ (by simp)) (by simpa using hEq2)
  -- the level assignment is the identity substitution
  have hsub : Level.substFn φ ([] : List Name) ([] : List Level) = φ :=
    funext fun _ => rfl
  -- the frame's `Nat`, and its universe
  have hvalNat : cvalAt m.cval env cv.name value' natName
      (Level.substFn φ ([] : List Name) ([] : List Level))
      = m.cval natName φ := by
    rw [show cvalAt m.cval env cv.name value' natName = m.cval natName
      from cvalAt_ne (hne _ (by simp)), hsub]
  have hNU : ∀ ρ' : Nat → V,
      interp V ρ' (m.cval natName φ) ∈ˢ univ 1 := by
    intro ρ'
    obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfN φ
    rw [show (ConstantInfo.indInfo cvN capsN).toConstantVal = cvN
        from rfl, htyN,
      show denoteClosed m.cval env φ (Expr.sort (.succ .zero))
        = denote m.cval env φ 0 (Expr.sort (.succ .zero)) from rfl,
      denote_sort] at ht
    obtain rfl := Option.some.inj ht
    exact (hlaw ρ').1
  -- every binary dependency is a function on it
  have hdepAll := List.all_eq_true.mp hdeps
  have hdepBin : ∀ n ∈ natOpDeps cv.name, n ≠ cv.name →
      (n = natPredName || n = natLog2Name) = false →
      (n = natBeqName || n = natBleName) = false →
      ∀ (ρ' : Nat → V) (a b : V),
        a ∈ˢ interp V ρ' (m.cval natName φ) →
        b ∈ˢ interp V ρ' (m.cval natName φ) →
        SetTheory.app (SetTheory.app (interp V ρ' (m.cval n φ)) a) b
          ∈ˢ interp V ρ' (m.cval natName φ) := by
    intro n hn hnc hnu hnb ρ' a b ha hb
    obtain ⟨cvn, vn, hintn, hfn2, hpin2⟩ :=
      natOpStoredOk_tyPinned (hdepAll n hn)
    obtain ⟨nm, nm2, mb, mb2, cod, htyn, hcod⟩ :=
      natOpTyPinned_binaryE hnu hpin2
    have hfn : env.find? n = some (.defnInfo cvn vn hintn) :=
      hdown _ _ hnc hfn2
    have hcodN : cod = Expr.const natName [] := by
      unfold natOpCod at hcod
      rw [if_neg (show ¬((decide (n = natBeqName)
        || decide (n = natBleName)) = true) from by simp [hnb])] at hcod
      simpa using hcod
    subst hcodN
    exact dmBinMem m φ hfn htyn hfN hlpN hfN hlpN ρ' ha hb
  -- the value front door: the checked value's own denotation
  obtain ⟨hvlb, hvhf, hannv, -, -, -, hfront⟩ := id hvfr
  obtain ⟨Tv, Vc, tv, hTv, hVc, hInfV, hDeqV⟩ := hfront φ
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  have hdenSelf : ∀ d : Nat, denote m.cval env φ d
      (Expr.substConst0 cv.name value' (.const cv.name []))
      = some (dmVal m.cval env cv.name value' φ cv.name) :=
    fun d => denote_dmSelf φ m.cval_closed hvf' hbv' hVc d
  have hvalSelf : dmVal m.cval env cv.name value' φ cv.name = Vc := by
    rw [dmVal, hsub, cvalAt_self hVc]
  -- the operation's own pinned type
  have hselfDep : cv.name ∈ natOpDeps cv.name := by
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h|h|h|h|h|h|h|h|h <;> (rw [h]; decide)
  obtain ⟨cvS2, vS2, hS2, hfS2, hpinS2⟩ :=
    natOpStoredOk_tyPinned (hdepAll _ hselfDep)
  have htyS2 : cvS2.type = type' := by
    rw [Env.find?_cons] at hfS2
    rw [if_pos (show (ConstantInfo.defnInfo
      ⟨cv.name, cv.levelParams, type'⟩ value' hint).name = cv.name
      from rfl)] at hfS2
    obtain ⟨h1, -, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hfS2)
    rw [← h1]
  -- `Nat.ble` is a dependency of every pin-certified operation, and it
  -- is where `Bool` enters
  have hbleDep : natBleName ∈ natOpDeps cv.name := by
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h|h|h|h|h|h|h|h|h <;> (rw [h]; decide)
  have hbleNe : natBleName ≠ cv.name := by
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h|h|h|h|h|h|h|h|h <;> (rw [h]; decide)
  obtain ⟨ciB, hfB, hlpB, htyB, hbleMem⟩ :
      ∃ ciB, env.find? boolName = some ciB ∧
        ciB.toConstantVal.levelParams = [] ∧
        ciB.toConstantVal.type = .sort (.succ .zero) ∧
        ∀ (ρ' : Nat → V) (a b : V),
          a ∈ˢ interp V ρ' (m.cval natName φ) →
          b ∈ˢ interp V ρ' (m.cval natName φ) →
          SetTheory.app (SetTheory.app
            (interp V ρ' (m.cval natBleName φ)) a) b
            ∈ˢ interp V ρ' (m.cval boolName φ) := by
    obtain ⟨cvb, vb, hintb, hfb2, hpinb⟩ :=
      natOpStoredOk_tyPinned (hdepAll _ hbleDep)
    obtain ⟨nm, nm2, mb, mb2, cod, htyb, hcodb⟩ :=
      natOpTyPinned_binaryE (by decide) hpinb
    obtain ⟨rfl, ciB, hfB2, hlpB, htyB⟩ := natOpCod_ble hcodb
    exact ⟨ciB, hdown _ _ (hne _ (by simp)) hfB2, hlpB, htyB,
      fun ρ' a b ha hb => dmBinMem m φ (hdown _ _ hbleNe hfb2) htyb
        hfN hlpN (hdown _ _ (hne _ (by simp)) hfB2) hlpB ρ' ha hb⟩
  have hBU : ∀ ρ' : Nat → V,
      interp V ρ' (m.cval boolName φ) ∈ˢ univ 1 := by
    intro ρ'
    obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfB φ
    rw [htyB, show denoteClosed m.cval env φ (Expr.sort (.succ .zero))
        = denote m.cval env φ 0 (Expr.sort (.succ .zero)) from rfl,
      denote_sort] at ht
    obtain rfl := Option.some.inj ht
    exact (hlaw ρ').1
  -- the operation's own pinned type, in the shape `dmSelfMem` reads
  -- no pin-certified operation is a comparison, so its codomain is
  -- `Nat`
  have hnotcmp : ∀ cod : Expr, natOpCod
      (⟨ConstantInfo.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value'
        hint :: env.consts⟩ : Env) cv.name cod = true →
      cod = Expr.const natName [] := by
    intro cod hcod
    unfold natOpCod at hcod
    rw [if_neg (show ¬((decide (cv.name = natBeqName)
        || decide (cv.name = natBleName)) = true) from by
      simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with h|h|h|h|h|h|h|h|h <;> (rw [h]; decide))] at hcod
    simpa using hcod
  have hnotpred : (decide (cv.name = natPredName)) = false := by
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h|h|h|h|h|h|h|h|h <;> (rw [h]; decide)
  have htyOwn :
      ((decide (cv.name = natLog2Name) = false →
          ∃ nm nm2 mb mb2, type' = Expr.forallE nm (.const natName [])
            (.forallE nm2 (.const natName []) (.const natName []) mb2)
            mb) ∧
        (cv.name = natLog2Name →
          ∃ nm mb, type' = Expr.forallE nm (.const natName [])
            (.const natName []) mb)) := by
    refine ⟨fun hnl => ?_, fun hl => ?_⟩
    · obtain ⟨nmT, nmT2, mbT, mbT2, codT, htyT, hcodT⟩ :=
        natOpTyPinned_binaryE (by
          simp only [Bool.or_eq_false_iff]
          exact ⟨hnotpred, hnl⟩) (htyS2 ▸ hpinS2)
      exact ⟨nmT, nmT2, mbT, mbT2, by rw [htyT, hnotcmp codT hcodT]⟩
    · obtain ⟨nmT, mbT, codT, htyT, hcodT⟩ :=
        natOpTyPinned_unaryE (by simp [hl]) (htyS2 ▸ hpinS2)
      exact ⟨nmT, mbT, by rw [htyT, hnotcmp codT hcodT]⟩
  -- the literal-support and `Bool` constructors, stored
  obtain ⟨ciZ, hfZ, hlpZ⟩ : ∃ ci, env.find? natZeroName = some ci ∧
      ci.toConstantVal.levelParams = [] := by
    simp only [natZeroOk] at hzero
    split at hzero
    · next cvZ nP nF hf =>
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hzero
      exact ⟨_, hdown _ _ (hne _ (by simp)) hf, hzero.1⟩
    · exact nomatch hzero
  obtain ⟨ciS', hfS', hlpS'⟩ : ∃ ci, env.find? natSuccName = some ci ∧
      ci.toConstantVal.levelParams = [] := by
    simp only [natSuccOk] at hsucc
    split at hsucc
    · next cvS nP nF hf =>
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hsucc
      exact ⟨_, hdown _ _ (hne _ (by simp)) hf, hsucc.1⟩
    · exact nomatch hsucc
  have hcont : natDivModNames.contains cv.name = true := by
    simpa using hmem
  have hbc := hnogFull
  rw [if_pos (show (decide (cv.name = natBeqName)
      || decide (cv.name = natBleName)
      || natDivModNames.contains cv.name) = true from by
    simp only [Bool.or_eq_true, decide_eq_true_eq,
      List.contains_iff_mem] at *
    exact Or.inr hmem)] at hbc
  simp only [Bool.and_eq_true] at hbc
  obtain ⟨hbcT, hbcF⟩ := hbc
  obtain ⟨ciT2, hfT2, hlpT2⟩ : ∃ ci, env.find? boolTrueName = some ci ∧
      ci.toConstantVal.levelParams = [] := by
    split at hbcT
    · next ci hf =>
      simp only [List.isEmpty_iff] at hbcT
      exact ⟨ci, hdown _ _ (hne _ (by simp)) hf, hbcT⟩
    · exact nomatch hbcT
  obtain ⟨ciF2, hfF2, hlpF2⟩ : ∃ ci,
      env.find? boolFalseName = some ci ∧
      ci.toConstantVal.levelParams = [] := by
    split at hbcF
    · next ci hf =>
      simp only [List.isEmpty_iff] at hbcF
      exact ⟨ci, hdown _ _ (hne _ (by simp)) hf, hbcF⟩
    · exact nomatch hbcF
  have hstore : ∀ n ∈ natOpDeps cv.name ++ [natSuccName, natZeroName,
      boolTrueName, boolFalseName],
      n = cv.name ∨ (n ≠ cv.name ∧ ∃ ci, env.find? n = some ci ∧
        ci.toConstantVal.levelParams = []) := by
    intro n hn
    rcases List.mem_append.mp hn with hn' | hn'
    · by_cases hnc : n = cv.name
      · exact Or.inl hnc
      · refine Or.inr ⟨hnc, ?_⟩
        have hs := hdepAll n hn'
        simp only [natOpStoredOk] at hs
        split at hs
        · next cvn vn hintn hf =>
          simp only [Bool.and_eq_true, List.isEmpty_iff] at hs
          exact ⟨_, hdown _ _ hnc hf, hs.1⟩
        · exact nomatch hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn'
      rcases hn' with rfl | rfl | rfl | rfl
      · exact Or.inr ⟨hne _ (by simp), _, hfS', hlpS'⟩
      · exact Or.inr ⟨hne _ (by simp), _, hfZ, hlpZ⟩
      · exact Or.inr ⟨hne _ (by simp), _, hfT2, hlpT2⟩
      · exact Or.inr ⟨hne _ (by simp), _, hfF2, hlpF2⟩
  -- the two `Bool` constructors inhabit `Bool`
  have hctorMem : ∀ (bn : Name),
      bn = boolTrueName ∨ bn = boolFalseName →
      ∀ ρ' : Nat → V, interp V ρ' (m.cval bn φ)
        ∈ˢ interp V ρ' (m.cval boolName φ) := by
    intro bn hbn ρ'
    obtain ⟨ci, hf, hty⟩ : ∃ ci, env.find? bn = some ci ∧
        ci.toConstantVal.type = Expr.const boolName [] := by
      rcases hbn with rfl | rfl
      · revert hbT
        split
        · next ci hf =>
          intro h; simp only [beq_iff_eq] at h
          exact ⟨ci, hdown _ _ (hne _ (by simp)) hf, h⟩
        · intro h; exact nomatch h
      · revert hbF
        split
        · next ci hf =>
          intro h; simp only [beq_iff_eq] at h
          exact ⟨ci, hdown _ _ (hne _ (by simp)) hf, h⟩
        · intro h; exact nomatch h
    obtain ⟨t, ht, hlaw⟩ := m.cval_memType hf φ
    rw [hty, show denoteClosed m.cval env φ (Expr.const boolName [])
        = denote m.cval env φ 0 (Expr.const boolName []) from rfl,
      denote_const_nolevelsS hfB hlpB φ 0] at ht
    obtain rfl := Option.some.inj ht
    exact (hlaw ρ').1
  -- the literals inhabit `Nat`
  have hzeroMem : ∀ ρ' : Nat → V,
      interp V ρ' (m.cval natZeroName φ)
        ∈ˢ interp V ρ' (m.cval natName φ) := by
    intro ρ'
    obtain ⟨cvZ, hfZ2, htyZ⟩ : ∃ cvZ, env.find? natZeroName = some cvZ ∧
        cvZ.toConstantVal.type = Expr.const natName [] := by
      cases hf : (⟨ConstantInfo.defnInfo
          ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
          env.consts⟩ : Env).find? natZeroName with
      | none => rw [hf] at hzero; exact nomatch hzero
      | some ci =>
        have hz := hf ▸ hzero
        cases ci with
        | ctorInfo cvZ nP nF =>
          simp only [natZeroOk, Bool.and_eq_true, beq_iff_eq] at hz
          exact ⟨_, hdown _ _ (hne _ (by simp)) hf, hz.2⟩
        | _ => exact nomatch hz
    obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfZ2 φ
    rw [htyZ, show denoteClosed m.cval env φ (Expr.const natName [])
        = denote m.cval env φ 0 (Expr.const natName []) from rfl,
      denote_const_nolevelsS hfN hlpN φ 0] at ht
    obtain rfl := Option.some.inj ht
    exact (hlaw ρ').1
  have hsuccMem : ∀ (ρ' : Nat → V) (a : V),
      a ∈ˢ interp V ρ' (m.cval natName φ) →
      SetTheory.app (interp V ρ' (m.cval natSuccName φ)) a
        ∈ˢ interp V ρ' (m.cval natName φ) := by
    intro ρ' a ha
    obtain ⟨ciS2, hfS2', htyS2'⟩ : ∃ ci,
        env.find? natSuccName = some ci ∧ ∃ nm mb,
        ci.toConstantVal.type = Expr.forallE nm (.const natName [])
          (.const natName []) mb := by
      cases hf : (⟨ConstantInfo.defnInfo
          ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
          env.consts⟩ : Env).find? natSuccName with
      | none => rw [hf] at hsucc; exact nomatch hsucc
      | some ci =>
        exact ⟨ci, hdown _ _ (hne _ (by simp)) hf,
          natSuccOk_ty (hf ▸ hsucc)⟩
    obtain ⟨nmS, mbS, htyS3⟩ := htyS2'
    exact dmUnMem m φ hfS2' htyS3 hfN hlpN hfN hlpN ρ' ha
  exact ⟨_, ciB, Vc, hfN, hlpN, hfB, hlpB, hEqE, hVc, hvalSelf,
    hvalNat, hNU, hBU, hbleMem, hdepBin, htyOwn, hstore, hctorMem,
    hzeroMem, hsuccMem⟩

/-! ## One guarded clause, as a theorem

The nine operations' clause blocks are instantiations of this: denote
the four fragments, read the equation off the certificate, and hand
back the `app`-chain `DivModClausesV` is written in.  Everything
syntactic about a statement is `by decide` at the call site. -/

set_option maxHeartbeats 12800000 in
/-- **A guarded div/mod clause, discharged.** -/
theorem dmClause1S {μ : CheckMode} {F : Nat} {env : Env}
    (m : EnvS V env) {cv : ConstantVal} {type' value value' : Expr}
    {hint : ReducibilityHint} {c : Name}
    (hmem : cv.name ∈ natDivModNames)
    (hvfr : ValueFrontR μ F env m.cval cv value type' value')
    (hgenv : divModEnvGuard ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩
      value' hint :: env.consts⟩ cv.name = true)
    (hc : cv.name = c)
    (φ : Name → Nat) (ρ : Nat → V) (xx yy : V)
    (hxx : xx ∈ˢ interp V ρ (cvalAt m.cval env cv.name value' natName
      (Level.substFn φ ([] : List Name) ([] : List Level))))
    (hyy : yy ∈ˢ interp V ρ (cvalAt m.cval env cv.name value' natName
      (Level.substFn φ ([] : List Name) ([] : List Level)))) :
    ∀ gl gr lhs rhs proof : Expr,
      CertRunFacts μ env F c value'
        ([Expr.app (.app (.app (.const eqName [.succ .zero])
            (.const boolName [])) gl) gr],
         Expr.app (.app (.app (.const eqName [.succ .zero])
            (.const natName [])) lhs) rhs) proof →
      dmFragOk c (natOpDeps c ++ [natSuccName, natZeroName,
        boolTrueName, boolFalseName]) gl = true →
      dmFragOk c (natOpDeps c ++ [natSuccName, natZeroName,
        boolTrueName, boolFalseName]) gr = true →
      dmFragOk c (natOpDeps c ++ [natSuccName, natZeroName,
        boolTrueName, boolFalseName]) lhs = true →
      dmFragOk c (natOpDeps c ++ [natSuccName, natZeroName,
        boolTrueName, boolFalseName]) rhs = true →
      Expr.wscopedB 2 (Expr.app (.app (.app
        (.const eqName [.succ .zero]) (.const boolName [])) gl) gr)
        = true →
      Expr.wscopedB 4 lhs = true → Expr.wscopedB 4 rhs = true →
      (Expr.app (.app (.app (.const eqName [.succ .zero])
        (.const boolName [])) gl) gr).looseBVarsBounded 0 = true →
      lhs.looseBVarsBounded 0 = true →
      rhs.looseBVarsBounded 0 = true →
      dmLeavesOk (Expr.app (.app (.app (.const eqName [.succ .zero])
        (.const boolName [])) gl) gr) = true →
      dmLeavesOk lhs = true → dmLeavesOk rhs = true →
      (dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy lhs
          ∈ˢ interp V ρ (m.cval natName φ)) →
      (dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy rhs
          ∈ˢ interp V ρ (m.cval natName φ)) →
      (dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy gl
          ∈ˢ interp V ρ (m.cval boolName φ)) →
      (dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy gr
          ∈ˢ interp V ρ (m.cval boolName φ)) →
      dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy gl
        = dmEvalV V (fun n => interp V ρ
          (dmVal m.cval env c value' φ n)) xx yy gr →
      dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy lhs
        = dmEvalV V (fun n => interp V ρ
          (dmVal m.cval env c value' φ n)) xx yy rhs := by
  obtain ⟨ciN, ciB, Vc, hfN, hlpN, hfB, hlpB, hEqE, hVc, hvalSelf,
    hvalNat, hNU, hBU, hbleMem, hdepBin, htyOwn, hstore, hctorMem,
    hzeroMem, hsuccMem⟩ := dmFrameS m hmem hvfr hgenv φ
  obtain ⟨hvlb, hvhf, hannv, -, -, -, -⟩ := id hvfr
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  have hclN : VExpr.Closed (m.cval natName φ) := m.cval_closed _ _
  have hnatDen : ∀ d : Nat, denote m.cval env φ d
      (Expr.const natName []) = some (m.cval natName φ) :=
    fun d => denote_const_nolevelsS hfN hlpN φ d
  have hneAll : ∀ n ∈ ([natName, boolName] : List Name),
      n ≠ cv.name := by
    intro n hn
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
      or_false] at hmem hn
    rcases hmem with h|h|h|h|h|h|h|h|h <;>
      rcases hn with rfl|rfl <;> (rw [h]; decide)
  have hvalDep : ∀ n : Name, n ≠ cv.name →
      dmVal m.cval env cv.name value' φ n = m.cval n φ := by
    intro n hn
    rw [dmVal, show cvalAt m.cval env cv.name value' n = m.cval n
      from cvalAt_ne hn,
      show Level.substFn φ ([] : List Name) ([] : List Level) = φ
      from funext fun _ => rfl]
  have hboolDen : ∀ d : Nat, denote m.cval env φ d
      (Expr.substConst0 cv.name value' (Expr.const boolName []))
      = some (m.cval boolName φ) := by
    intro d
    rw [denote_dmDep φ hfB hlpB (hneAll _ (by simp)) d,
      hvalDep _ (hneAll _ (by simp))]
  rw [hvalNat] at hxx hyy
  -- the frame's valuations are closed, hence environment-independent
  have hdmCl : ∀ n : Name,
      VExpr.Closed (dmVal m.cval env cv.name value' φ n) := by
    intro n
    by_cases hn : n = cv.name
    · subst hn
      rw [hvalSelf]
      exact denote_closed m.cval_closed hvf' hbv' hVc
    · rw [hvalDep n hn]
      exact m.cval_closed _ _
  have hdmInv : ∀ (n : Name) (ρ' : Nat → V),
      interp V ρ' (dmVal m.cval env cv.name value' φ n)
        = interp V ρ (dmVal m.cval env cv.name value' φ n) :=
    fun n ρ' => interp_closed V (hdmCl n) ρ' ρ
  -- the operation itself is a function on the frame's `Nat`
  have hselfMem : (∃ nm nm2 mb mb2, type' = Expr.forallE nm
        (.const natName [])
        (.forallE nm2 (.const natName []) (.const natName []) mb2) mb) →
      ∀ (ρ' : Nat → V) (a b : V),
        a ∈ˢ interp V ρ' (m.cval natName φ) →
        b ∈ˢ interp V ρ' (m.cval natName φ) →
        SetTheory.app (SetTheory.app (interp V ρ' Vc) a) b
          ∈ˢ interp V ρ' (m.cval natName φ) := by
    rintro ⟨nm, nm2, mb, mb2, hty⟩ ρ' a b ha hb
    exact dmSelfMem m φ hvfr hty hfN hlpN hfN hlpN hVc ρ' ha hb
  rw [hc] at hmem hvalSelf hstore hdepBin hvalDep hdmCl hdmInv hneAll hboolDen htyOwn
  intro gl gr lhs rhs proof hfacts hfgl hfgr hflhs hfrhs hwH hwL hwR
    hbH hbL hbR hlH hlL hlR hmL hmR hmgl hmgr hguard
  have hpf : (Expr.substConstAll c value' proof).hasFvar = false := by
    have hg := hfacts.1
    simp only [divModCertGuard, Bool.and_eq_true,
      Bool.not_eq_true'] at hg
    exact hg.1.1.1.1.2
  obtain ⟨glV, hgld, hgle⟩ := dmDenEval m φ (d := 4) m.cval_closed
    hvf' hbv' hVc hstore gl hfgl
  obtain ⟨grV, hgrd, hgre⟩ := dmDenEval m φ (d := 4) m.cval_closed
    hvf' hbv' hVc hstore gr hfgr
  obtain ⟨lV, hld, hle⟩ := dmDenEval m φ (d := 4) m.cval_closed
    hvf' hbv' hVc hstore lhs hflhs
  obtain ⟨rV, hrd, hre⟩ := dmDenEval m φ (d := 4) m.cval_closed
    hvf' hbv' hVc hstore rhs hfrhs
  obtain ⟨gl2, hgl2, hgle2⟩ := dmDenEval m φ (d := 2) m.cval_closed
    hvf' hbv' hVc hstore gl hfgl
  obtain ⟨gr2, hgr2, hgre2⟩ := dmDenEval m φ (d := 2) m.cval_closed
    hvf' hbv' hVc hstore gr hfgr
  have hH1 := denote_eqSpine (cval := m.cval) (c := c)
    (value' := value') φ hEqE (hboolDen 2) hgl2 hgr2
  have hfb1 : Expr.fvarsBelow 2 (Expr.substConst0 c value'
      (Expr.app (.app (.app (.const eqName [.succ .zero])
        (.const boolName [])) gl) gr)) :=
    Expr.WScoped.fvarsBelow
      (Expr.WScoped.of_wscopedB (wscopedB_substConst0 hvf' _ hwH))
  have hlE : dmLeavesOk (Expr.app (.app (.app
      (.const eqName [.succ .zero]) (.const natName [])) lhs) rhs)
      = true := by
    simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append,
      List.all_append, Bool.and_eq_true]
    exact ⟨hlL, hlR⟩
  have hCA := dmCtxOk_applied1 (μ := μ) (H2 := m.cval natName φ) φ
    m.cval_closed hvf' hclN (hnatDen 4) hpf hlH hfb1 hH1
  have hCE := dmCtxOk_stmt (μ := μ) (c := c) (value' := value')
    (H1 := VExpr.mkAppN (m.cval eqName (Level.substFn φ
      eqA.toConstantVal.levelParams [Level.zero.succ]))
      [m.cval boolName φ, gl2, gr2])
    (H2 := m.cval natName φ) φ hvf' hclN (hnatDen 4) hlE
  -- the frame's valuation, at the four-entry environment
  have hvalFun : ∀ ρ' : Nat → V, (fun n => interp V ρ'
      (dmVal m.cval env c value' φ n))
      = (fun n => interp V ρ (dmVal m.cval env c value' φ n)) :=
    fun ρ' => funext fun n => hdmInv n ρ'
  -- the hypothesis slot is inhabited by the guard
  have hsat := sat_dm (A0 := m.cval natName φ) (A1 := _)
    (natV := m.cval natName φ) (ρ := ρ) (a := xx) (b := pt)
    (yy := yy) (xx := xx) hclN
    (by rw [interp_closed V hclN _ ρ]; exact hxx)
    (by
      rw [EqLawV.app₃ V m.eq_lawV hEqE
        (Level.substFn φ eqA.toConstantVal.levelParams
          [Level.zero.succ]) (cons V yy (cons V xx ρ))
        (m.cval boolName φ) gl2 gr2
        (by rw [eqSubst_uN]; exact hBU _)
        (by
          rw [hgle2, hvalFun,
            interp_closed V (m.cval_closed boolName φ) _ ρ]
          exact hmgl)
        (by
          rw [hgre2, hvalFun,
            interp_closed V (m.cval_closed boolName φ) _ ρ]
          exact hmgr)]
      rw [hgle2, hgre2, hvalFun]
      show pt ∈ˢ eqv (dmEvalV V (fun n => interp V ρ
          (dmVal m.cval env c value' φ n)) xx yy gl)
        (dmEvalV V (fun n => interp V ρ
          (dmVal m.cval env c value' φ n)) xx yy gr)
      rw [hguard]
      exact pt_mem_eqv_self _)
    (by rw [interp_closed V hclN _ ρ]; exact hyy)
    (by rw [interp_closed V hclN _ ρ]; exact hxx)
  have heq := dmCertEq1 m φ hEqE (hneAll _ (by simp)) hvf' hbv'
    hfacts hlH hlL hlR hwH hwL hwR hbH hbL hbR (hnatDen 4) hld hrd
    hCA hCE
    _ hsat (hNU _)
    (by rw [hle, hvalFun, interp_closed V hclN _ ρ]; exact hmL)
    (by rw [hre, hvalFun, interp_closed V hclN _ ρ]; exact hmR)
  rw [hle, hre, hvalFun] at heq
  exact heq

set_option maxHeartbeats 12800000 in
/-- **A two-hypothesis guarded div/mod clause, discharged** —
`Nat.div`/`Nat.mod`'s recursive certificate. -/
theorem dmClause2S {μ : CheckMode} {F : Nat} {env : Env}
    (m : EnvS V env) {cv : ConstantVal} {type' value value' : Expr}
    {hint : ReducibilityHint} {c : Name}
    (hmem : cv.name ∈ natDivModNames)
    (hvfr : ValueFrontR μ F env m.cval cv value type' value')
    (hgenv : divModEnvGuard ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩
      value' hint :: env.consts⟩ cv.name = true)
    (hc : cv.name = c)
    (φ : Name → Nat) (ρ : Nat → V) (xx yy : V)
    (hxx : xx ∈ˢ interp V ρ (cvalAt m.cval env cv.name value' natName
      (Level.substFn φ ([] : List Name) ([] : List Level))))
    (hyy : yy ∈ˢ interp V ρ (cvalAt m.cval env cv.name value' natName
      (Level.substFn φ ([] : List Name) ([] : List Level)))) :
    ∀ gl gr gl2e gr2e lhs rhs proof : Expr,
      CertRunFacts μ env F c value'
        ([Expr.app (.app (.app (.const eqName [.succ .zero])
            (.const boolName [])) gl) gr,
          Expr.app (.app (.app (.const eqName [.succ .zero])
            (.const boolName [])) gl2e) gr2e],
         Expr.app (.app (.app (.const eqName [.succ .zero])
            (.const natName [])) lhs) rhs) proof →
      dmFragOk c (natOpDeps c ++ [natSuccName, natZeroName,
        boolTrueName, boolFalseName]) gl = true →
      dmFragOk c (natOpDeps c ++ [natSuccName, natZeroName,
        boolTrueName, boolFalseName]) gr = true →
      dmFragOk c (natOpDeps c ++ [natSuccName, natZeroName,
        boolTrueName, boolFalseName]) lhs = true →
      dmFragOk c (natOpDeps c ++ [natSuccName, natZeroName,
        boolTrueName, boolFalseName]) rhs = true →
      Expr.wscopedB 2 (Expr.app (.app (.app
        (.const eqName [.succ .zero]) (.const boolName [])) gl) gr)
        = true →
      Expr.wscopedB 3 (Expr.app (.app (.app
        (.const eqName [.succ .zero]) (.const boolName [])) gl2e) gr2e)
        = true →
      dmFragOk c (natOpDeps c ++ [natSuccName, natZeroName,
        boolTrueName, boolFalseName]) gl2e = true →
      dmFragOk c (natOpDeps c ++ [natSuccName, natZeroName,
        boolTrueName, boolFalseName]) gr2e = true →
      (Expr.app (.app (.app (.const eqName [.succ .zero])
        (.const boolName [])) gl2e) gr2e).looseBVarsBounded 0 = true →
      dmLeavesOk (Expr.app (.app (.app (.const eqName [.succ .zero])
        (.const boolName [])) gl2e) gr2e) = true →
      (dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy gl2e
          ∈ˢ interp V ρ (m.cval boolName φ)) →
      (dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy gr2e
          ∈ˢ interp V ρ (m.cval boolName φ)) →
      dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy gl2e
        = dmEvalV V (fun n => interp V ρ
          (dmVal m.cval env c value' φ n)) xx yy gr2e →
      Expr.wscopedB 4 lhs = true → Expr.wscopedB 4 rhs = true →
      (Expr.app (.app (.app (.const eqName [.succ .zero])
        (.const boolName [])) gl) gr).looseBVarsBounded 0 = true →
      lhs.looseBVarsBounded 0 = true →
      rhs.looseBVarsBounded 0 = true →
      dmLeavesOk (Expr.app (.app (.app (.const eqName [.succ .zero])
        (.const boolName [])) gl) gr) = true →
      dmLeavesOk lhs = true → dmLeavesOk rhs = true →
      (dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy lhs
          ∈ˢ interp V ρ (m.cval natName φ)) →
      (dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy rhs
          ∈ˢ interp V ρ (m.cval natName φ)) →
      (dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy gl
          ∈ˢ interp V ρ (m.cval boolName φ)) →
      (dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy gr
          ∈ˢ interp V ρ (m.cval boolName φ)) →
      dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy gl
        = dmEvalV V (fun n => interp V ρ
          (dmVal m.cval env c value' φ n)) xx yy gr →
      dmEvalV V (fun n => interp V ρ
        (dmVal m.cval env c value' φ n)) xx yy lhs
        = dmEvalV V (fun n => interp V ρ
          (dmVal m.cval env c value' φ n)) xx yy rhs := by
  obtain ⟨ciN, ciB, Vc, hfN, hlpN, hfB, hlpB, hEqE, hVc, hvalSelf,
    hvalNat, hNU, hBU, hbleMem, hdepBin, htyOwn, hstore, hctorMem,
    hzeroMem, hsuccMem⟩ := dmFrameS m hmem hvfr hgenv φ
  obtain ⟨hvlb, hvhf, hannv, -, -, -, -⟩ := id hvfr
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  have hclN : VExpr.Closed (m.cval natName φ) := m.cval_closed _ _
  have hnatDen : ∀ d : Nat, denote m.cval env φ d
      (Expr.const natName []) = some (m.cval natName φ) :=
    fun d => denote_const_nolevelsS hfN hlpN φ d
  have hneAll : ∀ n ∈ ([natName, boolName] : List Name),
      n ≠ cv.name := by
    intro n hn
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
      or_false] at hmem hn
    rcases hmem with h|h|h|h|h|h|h|h|h <;>
      rcases hn with rfl|rfl <;> (rw [h]; decide)
  have hvalDep : ∀ n : Name, n ≠ cv.name →
      dmVal m.cval env cv.name value' φ n = m.cval n φ := by
    intro n hn
    rw [dmVal, show cvalAt m.cval env cv.name value' n = m.cval n
      from cvalAt_ne hn,
      show Level.substFn φ ([] : List Name) ([] : List Level) = φ
      from funext fun _ => rfl]
  have hboolDen : ∀ d : Nat, denote m.cval env φ d
      (Expr.substConst0 cv.name value' (Expr.const boolName []))
      = some (m.cval boolName φ) := by
    intro d
    rw [denote_dmDep φ hfB hlpB (hneAll _ (by simp)) d,
      hvalDep _ (hneAll _ (by simp))]
  rw [hvalNat] at hxx hyy
  -- the frame's valuations are closed, hence environment-independent
  have hdmCl : ∀ n : Name,
      VExpr.Closed (dmVal m.cval env cv.name value' φ n) := by
    intro n
    by_cases hn : n = cv.name
    · subst hn
      rw [hvalSelf]
      exact denote_closed m.cval_closed hvf' hbv' hVc
    · rw [hvalDep n hn]
      exact m.cval_closed _ _
  have hdmInv : ∀ (n : Name) (ρ' : Nat → V),
      interp V ρ' (dmVal m.cval env cv.name value' φ n)
        = interp V ρ (dmVal m.cval env cv.name value' φ n) :=
    fun n ρ' => interp_closed V (hdmCl n) ρ' ρ
  -- the operation itself is a function on the frame's `Nat`
  have hselfMem : (∃ nm nm2 mb mb2, type' = Expr.forallE nm
        (.const natName [])
        (.forallE nm2 (.const natName []) (.const natName []) mb2) mb) →
      ∀ (ρ' : Nat → V) (a b : V),
        a ∈ˢ interp V ρ' (m.cval natName φ) →
        b ∈ˢ interp V ρ' (m.cval natName φ) →
        SetTheory.app (SetTheory.app (interp V ρ' Vc) a) b
          ∈ˢ interp V ρ' (m.cval natName φ) := by
    rintro ⟨nm, nm2, mb, mb2, hty⟩ ρ' a b ha hb
    exact dmSelfMem m φ hvfr hty hfN hlpN hfN hlpN hVc ρ' ha hb
  rw [hc] at hmem hvalSelf hstore hdepBin hvalDep hdmCl hdmInv hneAll hboolDen htyOwn
  intro gl gr gl2e gr2e lhs rhs proof hfacts hfgl hfgr hflhs hfrhs hwH
    hwH2 hfgl2 hfgr2 hbH2 hlH2 hmgl2 hmgr2 hguard2 hwL hwR
    hbH hbL hbR hlH hlL hlR hmL hmR hmgl hmgr hguard
  have hpf : (Expr.substConstAll c value' proof).hasFvar = false := by
    have hg := hfacts.1
    simp only [divModCertGuard, Bool.and_eq_true,
      Bool.not_eq_true'] at hg
    exact hg.1.1.1.1.2
  obtain ⟨glV, hgld, hgle⟩ := dmDenEval m φ (d := 4) m.cval_closed
    hvf' hbv' hVc hstore gl hfgl
  obtain ⟨grV, hgrd, hgre⟩ := dmDenEval m φ (d := 4) m.cval_closed
    hvf' hbv' hVc hstore gr hfgr
  obtain ⟨lV, hld, hle⟩ := dmDenEval m φ (d := 4) m.cval_closed
    hvf' hbv' hVc hstore lhs hflhs
  obtain ⟨rV, hrd, hre⟩ := dmDenEval m φ (d := 4) m.cval_closed
    hvf' hbv' hVc hstore rhs hfrhs
  obtain ⟨gl2, hgl2, hgle2⟩ := dmDenEval m φ (d := 2) m.cval_closed
    hvf' hbv' hVc hstore gl hfgl
  obtain ⟨gr2, hgr2, hgre2⟩ := dmDenEval m φ (d := 2) m.cval_closed
    hvf' hbv' hVc hstore gr hfgr
  obtain ⟨gl3, hgl3, hgle3⟩ := dmDenEval m φ (d := 3) m.cval_closed
    hvf' hbv' hVc hstore gl2e hfgl2
  obtain ⟨gr3, hgr3, hgre3⟩ := dmDenEval m φ (d := 3) m.cval_closed
    hvf' hbv' hVc hstore gr2e hfgr2
  have hH2 := denote_eqSpine (cval := m.cval) (c := c)
    (value' := value') φ hEqE (hboolDen 3) hgl3 hgr3
  have hfb2 : Expr.fvarsBelow 3 (Expr.substConst0 c value'
      (Expr.app (.app (.app (.const eqName [.succ .zero])
        (.const boolName [])) gl2e) gr2e)) :=
    Expr.WScoped.fvarsBelow
      (Expr.WScoped.of_wscopedB (wscopedB_substConst0 hvf' _ hwH2))
  have hH1 := denote_eqSpine (cval := m.cval) (c := c)
    (value' := value') φ hEqE (hboolDen 2) hgl2 hgr2
  have hfb1 : Expr.fvarsBelow 2 (Expr.substConst0 c value'
      (Expr.app (.app (.app (.const eqName [.succ .zero])
        (.const boolName [])) gl) gr)) :=
    Expr.WScoped.fvarsBelow
      (Expr.WScoped.of_wscopedB (wscopedB_substConst0 hvf' _ hwH))
  have hlE : dmLeavesOk (Expr.app (.app (.app
      (.const eqName [.succ .zero]) (.const natName [])) lhs) rhs)
      = true := by
    simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append,
      List.all_append, Bool.and_eq_true]
    exact ⟨hlL, hlR⟩
  have hCA := dmCtxOk_applied2 (μ := μ) φ
    m.cval_closed hvf' hclN (hnatDen 4) hpf hlH hlH2 hfb1 hfb2 hH1
    hH2
  have hCE := dmCtxOk_stmt (μ := μ) (c := c) (value' := value')
    (H1 := VExpr.mkAppN (m.cval eqName (Level.substFn φ
      eqA.toConstantVal.levelParams [Level.zero.succ]))
      [m.cval boolName φ, gl2, gr2])
    (H2 := VExpr.mkAppN (m.cval eqName (Level.substFn φ
      eqA.toConstantVal.levelParams [Level.zero.succ]))
      [m.cval boolName φ, gl3, gr3])
    φ hvf' hclN (hnatDen 4) hlE
  -- the frame's valuation, at the four-entry environment
  have hvalFun : ∀ ρ' : Nat → V, (fun n => interp V ρ'
      (dmVal m.cval env c value' φ n))
      = (fun n => interp V ρ (dmVal m.cval env c value' φ n)) :=
    fun ρ' => funext fun n => hdmInv n ρ'
  -- the hypothesis slot is inhabited by the guard
  have hsat := sat_dm (A0 := _) (A1 := _)
    (natV := m.cval natName φ) (ρ := ρ) (a := pt) (b := pt)
    (yy := yy) (xx := xx) hclN
    (by
      rw [EqLawV.app₃ V m.eq_lawV hEqE
        (Level.substFn φ eqA.toConstantVal.levelParams
          [Level.zero.succ]) (cons V pt (cons V yy (cons V xx ρ)))
        (m.cval boolName φ) gl3 gr3
        (by rw [eqSubst_uN]; exact hBU _)
        (by
          rw [hgle3, hvalFun,
            interp_closed V (m.cval_closed boolName φ) _ ρ]
          exact hmgl2)
        (by
          rw [hgre3, hvalFun,
            interp_closed V (m.cval_closed boolName φ) _ ρ]
          exact hmgr2)]
      rw [hgle3, hgre3, hvalFun]
      show pt ∈ˢ eqv (dmEvalV V (fun n => interp V ρ
          (dmVal m.cval env c value' φ n)) xx yy gl2e)
        (dmEvalV V (fun n => interp V ρ
          (dmVal m.cval env c value' φ n)) xx yy gr2e)
      rw [hguard2]
      exact pt_mem_eqv_self _)
    (by
      rw [EqLawV.app₃ V m.eq_lawV hEqE
        (Level.substFn φ eqA.toConstantVal.levelParams
          [Level.zero.succ]) (cons V yy (cons V xx ρ))
        (m.cval boolName φ) gl2 gr2
        (by rw [eqSubst_uN]; exact hBU _)
        (by
          rw [hgle2, hvalFun,
            interp_closed V (m.cval_closed boolName φ) _ ρ]
          exact hmgl)
        (by
          rw [hgre2, hvalFun,
            interp_closed V (m.cval_closed boolName φ) _ ρ]
          exact hmgr)]
      rw [hgle2, hgre2, hvalFun]
      show pt ∈ˢ eqv (dmEvalV V (fun n => interp V ρ
          (dmVal m.cval env c value' φ n)) xx yy gl)
        (dmEvalV V (fun n => interp V ρ
          (dmVal m.cval env c value' φ n)) xx yy gr)
      rw [hguard]
      exact pt_mem_eqv_self _)
    (by rw [interp_closed V hclN _ ρ]; exact hyy)
    (by rw [interp_closed V hclN _ ρ]; exact hxx)
  have heq := dmCertEq2 m φ hEqE (hneAll _ (by simp)) hvf' hbv'
    hfacts hlH hlH2 hlL hlR hwH hwH2 hwL hwR hbH hbH2 hbL hbR
    (hnatDen 4) hld hrd hCA hCE
    _ hsat (hNU _)
    (by rw [hle, hvalFun, interp_closed V hclN _ ρ]; exact hmL)
    (by rw [hre, hvalFun, interp_closed V hclN _ ρ]; exact hmR)
  rw [hle, hre, hvalFun] at heq
  exact heq

/-! ## The install obligation -/

set_option maxHeartbeats 12800000 in
/-- **`DivModPinS`, discharged.** -/
theorem divModPinS : DivModPinS V := by
  intro μ F env m cv type' value value' hint hmem hfresh hcv hvfr hpin
  obtain ⟨hgenv, hgpin, hgcerts, pinA, hannP, hcerts⟩ := hpin
  refine ⟨?_, ?_⟩
  · simp only [divModEnvGuard, Bool.and_eq_true] at hgenv
    exact hgenv.1.1.1.1
  intro φ ρ xx yy hxx hyy
  obtain ⟨ciN, ciB, Vc, hfN, hlpN, hfB, hlpB, hEqE, hVc, hvalSelf,
    hvalNat, hNU, hBU, hbleMem, hdepBin, htyOwn, hstore, hctorMem,
    hzeroMem, hsuccMem⟩ := dmFrameS m hmem hvfr hgenv φ
  obtain ⟨hvlb, hvhf, hannv, -, -, -, -⟩ := id hvfr
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  have hxx' : xx ∈ˢ interp V ρ (m.cval natName φ) := by
    rwa [hvalNat] at hxx
  have hyy' : yy ∈ˢ interp V ρ (m.cval natName φ) := by
    rwa [hvalNat] at hyy
  have hselfMem : (∃ nm nm2 mb mb2, type' = Expr.forallE nm
        (.const natName [])
        (.forallE nm2 (.const natName []) (.const natName []) mb2) mb) →
      ∀ (ρ' : Nat → V) (a b : V),
        a ∈ˢ interp V ρ' (m.cval natName φ) →
        b ∈ˢ interp V ρ' (m.cval natName φ) →
        SetTheory.app (SetTheory.app (interp V ρ' Vc) a) b
          ∈ˢ interp V ρ' (m.cval natName φ) := by
    rintro ⟨nm, nm2, mb, mb2, hty⟩ ρ' a b ha hb
    exact dmSelfMem m φ hvfr hty hfN hlpN hfN hlpN hVc ρ' ha hb
  have hunMem : (∃ nm mb, type' = Expr.forallE nm (.const natName [])
        (.const natName []) mb) →
      ∀ (ρ' : Nat → V) (a : V),
        a ∈ˢ interp V ρ' (m.cval natName φ) →
        SetTheory.app (interp V ρ' Vc) a
          ∈ˢ interp V ρ' (m.cval natName φ) := by
    rintro ⟨nm, mb, hty⟩ ρ' a ha
    obtain ⟨-, -, -, -, -, -, hfront⟩ := hvfr
    obtain ⟨Tv, Vv', tv, hTv, hVv', hInf, hDeq⟩ := hfront φ
    obtain rfl : Vv' = Vc := by
      rw [hVv'] at hVc; exact Option.some.inj hVc
    rw [hty, denoteClosed] at hTv
    simp only [denote_forallE, denote_const_nolevelsS hfN hlpN,
      Expr.instantiate1] at hTv
    obtain rfl := Option.some.inj hTv
    have h1 := (Infer.sound (m.toHyp φ) hInf ρ' (Sat_nil V ρ')).2
    rw [DefEq.sound (m.toHyp φ) hDeq ρ' (Sat_nil V ρ')] at h1
    rw [interp_pi, show (fun a : V => interp V (cons V a ρ')
          (m.cval natName φ))
        = (fun _ : V => interp V ρ' (m.cval natName φ)) from by
      funext a
      exact interp_closed V (m.cval_closed natName φ) _ ρ'] at h1
    exact app_mem_piC h1 ha
  have hc : cv.name = cv.name := rfl
  obtain ⟨c, hcname⟩ : ∃ c, cv.name = c := ⟨_, rfl⟩
  rw [hcname] at hmem hcerts hvalSelf htyOwn hdepBin hstore ⊢
  have hVs : interp V ρ (dmVal m.cval env c value' φ c)
      = interp V ρ Vc := by rw [hvalSelf]
  have hVd : ∀ n : Name, n ≠ c →
      interp V ρ (dmVal m.cval env c value' φ n)
        = interp V ρ (m.cval n φ) := by
    intro n hn
    rw [dmVal, show cvalAt m.cval env c value' n = m.cval n
      from cvalAt_ne hn,
      show Level.substFn φ ([] : List Name) ([] : List Level) = φ
      from funext fun _ => rfl]
  have hmem0 := hmem
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  have hruns := checkDivModCerts_inv hcerts
  rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · -- `Nat.div`
    simp only [divModCertStmts, divModCertProofs, natDivCertProofs,
      reduceIte,
      if_pos (show natDivName = natDivName from rfl)] at hruns
    cases hruns with
    | cons f1 r1 =>
      cases r1 with
      | cons f2 r2 =>
        cases r2 with
        | cons f3 r3 =>
          have hop := hselfMem (htyOwn.1 (by decide)) ρ
          have hone := hsuccMem ρ _ (hzeroMem ρ)
          have hVble := hVd natBleName (by decide)
          have hVsucc := hVd natSuccName (by decide)
          have hVzero := hVd natZeroName (by decide)
          have hVT := hVd boolTrueName (by decide)
          have hVF := hVd boolFalseName (by decide)
          have hsub := hdepBin natSubName (by decide) (by decide) (by decide) (by decide) ρ
          have hVsub := hVd natSubName (by decide)
          simp only [DivModClausesV, if_true, reduceIte,
            if_pos (show natDivName = natDivName from rfl)]
          refine ⟨fun hg hg2 => ?_, fun hg => ?_, fun hg => ?_⟩
          · have h := dmClause2S m (by rw [hcname]; exact hmem0) hvfr hgenv
              hcname φ ρ xx yy hxx hyy _ _ _ _ _ _ _ f1
              (by decide) (by decide) (by decide) (by decide)
              (by simp [Expr.wscopedB])
              (by simp [Expr.wscopedB])
              (by decide) (by decide)
              (by decide)
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVsucc, hVzero]
                  exact hbleMem ρ _ yy hone hyy')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVT]
                  exact hctorMem boolTrueName (Or.inl rfl) ρ)
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVsucc, hVzero, hVT]
                  exact hg2)
              (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
              (by decide) (by decide) (by decide)
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVs]
                  exact hop xx yy hxx' hyy')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVs, hVsub, hVsucc]
                  exact hsuccMem ρ _ (hop _ yy (hsub xx yy hxx' hyy') hyy'))
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble]
                  exact hbleMem ρ yy xx hyy' hxx')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVT]
                  exact hctorMem boolTrueName (Or.inl rfl) ρ)
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVT]
                  exact hg)
            simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
              using h
          · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
              hcname φ ρ xx yy hxx hyy _ _ _ _ _ f2
              (by decide) (by decide) (by decide) (by decide)
              (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
              (by simp [Expr.wscopedB])
              (by decide) (by decide) (by decide)
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVs]
                  exact hop xx yy hxx' hyy')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVzero]
                  exact hzeroMem ρ)
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble]
                  exact hbleMem ρ yy xx hyy' hxx')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVF]
                  exact hctorMem boolFalseName (Or.inr rfl) ρ)
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVF]
                  exact hg)
            simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
              using h
          · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
              hcname φ ρ xx yy hxx hyy _ _ _ _ _ f3
              (by decide) (by decide) (by decide) (by decide)
              (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
              (by simp [Expr.wscopedB])
              (by decide) (by decide) (by decide)
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVs]
                  exact hop xx yy hxx' hyy')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVzero]
                  exact hzeroMem ρ)
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVsucc, hVzero]
                  exact hbleMem ρ _ yy hone hyy')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVF]
                  exact hctorMem boolFalseName (Or.inr rfl) ρ)
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVsucc, hVzero, hVF]
                  exact hg)
            simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
              using h
  · -- `Nat.mod`
    simp only [divModCertStmts, divModCertProofs, natModCertProofs,
      reduceIte,
      if_neg (show ¬(natModName = natDivName) from by decide)]
      at hruns
    cases hruns with
    | cons f1 r1 =>
      cases r1 with
      | cons f2 r2 =>
        cases r2 with
        | cons f3 r3 =>
          have hop := hselfMem (htyOwn.1 (by decide)) ρ
          have hone := hsuccMem ρ _ (hzeroMem ρ)
          have hVble := hVd natBleName (by decide)
          have hVsucc := hVd natSuccName (by decide)
          have hVzero := hVd natZeroName (by decide)
          have hVT := hVd boolTrueName (by decide)
          have hVF := hVd boolFalseName (by decide)
          have hsub := hdepBin natSubName (by decide) (by decide) (by decide) (by decide) ρ
          have hVsub := hVd natSubName (by decide)
          simp only [DivModClausesV, if_true, reduceIte,
            if_neg (show ¬(natModName = natDivName) from by decide)]
          refine ⟨fun hg hg2 => ?_, fun hg => ?_, fun hg => ?_⟩
          · have h := dmClause2S m (by rw [hcname]; exact hmem0) hvfr hgenv
              hcname φ ρ xx yy hxx hyy _ _ _ _ _ _ _ f1
              (by decide) (by decide) (by decide) (by decide)
              (by simp [Expr.wscopedB])
              (by simp [Expr.wscopedB])
              (by decide) (by decide)
              (by decide)
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVsucc, hVzero]
                  exact hbleMem ρ _ yy hone hyy')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVT]
                  exact hctorMem boolTrueName (Or.inl rfl) ρ)
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVsucc, hVzero, hVT]
                  exact hg2)
              (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
              (by decide) (by decide) (by decide)
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVs]
                  exact hop xx yy hxx' hyy')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVs, hVsub]
                  exact hop _ yy (hsub xx yy hxx' hyy') hyy')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble]
                  exact hbleMem ρ yy xx hyy' hxx')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVT]
                  exact hctorMem boolTrueName (Or.inl rfl) ρ)
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVT]
                  exact hg)
            simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
              using h
          · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
              hcname φ ρ xx yy hxx hyy _ _ _ _ _ f2
              (by decide) (by decide) (by decide) (by decide)
              (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
              (by simp [Expr.wscopedB])
              (by decide) (by decide) (by decide)
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVs]
                  exact hop xx yy hxx' hyy')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte]
                  exact hxx')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble]
                  exact hbleMem ρ yy xx hyy' hxx')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVF]
                  exact hctorMem boolFalseName (Or.inr rfl) ρ)
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVF]
                  exact hg)
            simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
              using h
          · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
              hcname φ ρ xx yy hxx hyy _ _ _ _ _ f3
              (by decide) (by decide) (by decide) (by decide)
              (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
              (by simp [Expr.wscopedB])
              (by decide) (by decide) (by decide)
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp [dmLeavesOk, Expr.fvarLeaves])
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVs]
                  exact hop xx yy hxx' hyy')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte]
                  exact hxx')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVsucc, hVzero]
                  exact hbleMem ρ _ yy hone hyy')
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVF]
                  exact hctorMem boolFalseName (Or.inr rfl) ρ)
              (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                    reduceIte, hVble, hVsucc, hVzero, hVF]
                  exact hg)
            simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
              using h
  · -- `Nat.gcd`
    simp only [divModCertStmts, divModCertProofs, natGcdCertProofs,
      reduceIte] at hruns
    cases hruns with
    | cons f1 r1 =>
      cases r1 with
      | cons f2 r2 =>
        have hop := hselfMem (htyOwn.1 (by decide)) ρ
        have hone := hsuccMem ρ _ (hzeroMem ρ)
        have htwo := hsuccMem ρ _ hone
        have hVble := hVd natBleName (by decide)
        have hVsucc := hVd natSuccName (by decide)
        have hVzero := hVd natZeroName (by decide)
        have hVT := hVd boolTrueName (by decide)
        have hVF := hVd boolFalseName (by decide)
        have hmod := hdepBin natModName (by decide) (by decide) (by decide) (by decide) ρ
        have hVmod := hVd natModName (by decide)
        simp only [DivModClausesV, if_true, reduceIte]
        refine ⟨fun hg => ?_, fun hg => ?_⟩
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f1
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs, hVmod]
                exact hop _ xx (hmod yy xx hyy' hxx') hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ xx hone hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVT]
                exact hctorMem boolTrueName (Or.inl rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVT]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f2
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte]
                exact hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ xx hone hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVF]
                exact hctorMem boolFalseName (Or.inr rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVF]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
  · -- `Nat.land`
    simp only [divModCertStmts, divModCertProofs, natLandCertProofs,
      reduceIte] at hruns
    cases hruns with
    | cons f1 r1 =>
      cases r1 with
      | cons f2 r2 =>
        have hop := hselfMem (htyOwn.1 (by decide)) ρ
        have hone := hsuccMem ρ _ (hzeroMem ρ)
        have htwo := hsuccMem ρ _ hone
        have hVble := hVd natBleName (by decide)
        have hVsucc := hVd natSuccName (by decide)
        have hVzero := hVd natZeroName (by decide)
        have hVT := hVd boolTrueName (by decide)
        have hVF := hVd boolFalseName (by decide)
        have hadd := hdepBin natAddName (by decide) (by decide) (by decide) (by decide) ρ
        have hmul := hdepBin natMulName (by decide) (by decide) (by decide) (by decide) ρ
        have hdiv := hdepBin natDivName (by decide) (by decide) (by decide) (by decide) ρ
        have hmod := hdepBin natModName (by decide) (by decide) (by decide) (by decide) ρ
        have hVadd := hVd natAddName (by decide)
        have hVmul := hVd natMulName (by decide)
        have hVdiv := hVd natDivName (by decide)
        have hVmod := hVd natModName (by decide)
        simp only [DivModClausesV, if_true, reduceIte]
        refine ⟨fun hg => ?_, fun hg => ?_⟩
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f1
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs, hVadd, hVmul, hVdiv, hVmod, hVsucc, hVzero]
                exact hadd _ _ (hmul _ _ htwo (hop _ _ (hdiv xx _ hxx' htwo) (hdiv yy _ hyy' htwo))) (hmul _ _ (hmod xx _ hxx' htwo) (hmod yy _ hyy' htwo)))
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ xx hone hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVT]
                exact hctorMem boolTrueName (Or.inl rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVT]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f2
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVzero]
                exact hzeroMem ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ xx hone hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVF]
                exact hctorMem boolFalseName (Or.inr rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVF]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
  · -- `Nat.lor`
    simp only [divModCertStmts, divModCertProofs, natLorCertProofs,
      reduceIte] at hruns
    cases hruns with
    | cons f1 r1 =>
      cases r1 with
      | cons f2 r2 =>
        have hop := hselfMem (htyOwn.1 (by decide)) ρ
        have hone := hsuccMem ρ _ (hzeroMem ρ)
        have htwo := hsuccMem ρ _ hone
        have hVble := hVd natBleName (by decide)
        have hVsucc := hVd natSuccName (by decide)
        have hVzero := hVd natZeroName (by decide)
        have hVT := hVd boolTrueName (by decide)
        have hVF := hVd boolFalseName (by decide)
        have hadd := hdepBin natAddName (by decide) (by decide) (by decide) (by decide) ρ
        have hmul := hdepBin natMulName (by decide) (by decide) (by decide) (by decide) ρ
        have hdiv := hdepBin natDivName (by decide) (by decide) (by decide) (by decide) ρ
        have hmod := hdepBin natModName (by decide) (by decide) (by decide) (by decide) ρ
        have hsub := hdepBin natSubName (by decide) (by decide) (by decide) (by decide) ρ
        have hVadd := hVd natAddName (by decide)
        have hVmul := hVd natMulName (by decide)
        have hVdiv := hVd natDivName (by decide)
        have hVmod := hVd natModName (by decide)
        have hVsub := hVd natSubName (by decide)
        simp only [DivModClausesV, if_true, reduceIte]
        refine ⟨fun hg => ?_, fun hg => ?_⟩
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f1
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs, hVadd, hVmul, hVdiv, hVmod, hVsucc, hVzero, hVsub]
                exact hadd _ _ (hmul _ _ htwo (hop _ _ (hdiv xx _ hxx' htwo) (hdiv yy _ hyy' htwo))) (hsub _ _ (hadd _ _ (hmod xx _ hxx' htwo) (hmod yy _ hyy' htwo)) (hmul _ _ (hmod xx _ hxx' htwo) (hmod yy _ hyy' htwo))))
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ xx hone hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVT]
                exact hctorMem boolTrueName (Or.inl rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVT]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f2
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte]
                exact hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ xx hone hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVF]
                exact hctorMem boolFalseName (Or.inr rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVF]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
  · -- `Nat.xor`
    simp only [divModCertStmts, divModCertProofs, natXorCertProofs,
      reduceIte] at hruns
    cases hruns with
    | cons f1 r1 =>
      cases r1 with
      | cons f2 r2 =>
        have hop := hselfMem (htyOwn.1 (by decide)) ρ
        have hone := hsuccMem ρ _ (hzeroMem ρ)
        have htwo := hsuccMem ρ _ hone
        have hVble := hVd natBleName (by decide)
        have hVsucc := hVd natSuccName (by decide)
        have hVzero := hVd natZeroName (by decide)
        have hVT := hVd boolTrueName (by decide)
        have hVF := hVd boolFalseName (by decide)
        have hadd := hdepBin natAddName (by decide) (by decide) (by decide) (by decide) ρ
        have hmul := hdepBin natMulName (by decide) (by decide) (by decide) (by decide) ρ
        have hdiv := hdepBin natDivName (by decide) (by decide) (by decide) (by decide) ρ
        have hmod := hdepBin natModName (by decide) (by decide) (by decide) (by decide) ρ
        have hVadd := hVd natAddName (by decide)
        have hVmul := hVd natMulName (by decide)
        have hVdiv := hVd natDivName (by decide)
        have hVmod := hVd natModName (by decide)
        simp only [DivModClausesV, if_true, reduceIte]
        refine ⟨fun hg => ?_, fun hg => ?_⟩
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f1
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs, hVadd, hVmul, hVdiv, hVmod, hVsucc, hVzero]
                exact hadd _ _ (hmul _ _ htwo (hop _ _ (hdiv xx _ hxx' htwo) (hdiv yy _ hyy' htwo))) (hmod _ _ (hadd _ _ (hmod xx _ hxx' htwo) (hmod yy _ hyy' htwo)) htwo))
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ xx hone hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVT]
                exact hctorMem boolTrueName (Or.inl rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVT]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f2
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte]
                exact hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ xx hone hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVF]
                exact hctorMem boolFalseName (Or.inr rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVF]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
  · -- `Nat.shiftLeft`
    simp only [divModCertStmts, divModCertProofs, natShiftLeftCertProofs,
      reduceIte] at hruns
    cases hruns with
    | cons f1 r1 =>
      cases r1 with
      | cons f2 r2 =>
        have hop := hselfMem (htyOwn.1 (by decide)) ρ
        have hone := hsuccMem ρ _ (hzeroMem ρ)
        have htwo := hsuccMem ρ _ hone
        have hVble := hVd natBleName (by decide)
        have hVsucc := hVd natSuccName (by decide)
        have hVzero := hVd natZeroName (by decide)
        have hVT := hVd boolTrueName (by decide)
        have hVF := hVd boolFalseName (by decide)
        have hmul := hdepBin natMulName (by decide) (by decide) (by decide) (by decide) ρ
        have hsub := hdepBin natSubName (by decide) (by decide) (by decide) (by decide) ρ
        have hVmul := hVd natMulName (by decide)
        have hVsub := hVd natSubName (by decide)
        simp only [DivModClausesV, if_true, reduceIte]
        refine ⟨fun hg => ?_, fun hg => ?_⟩
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f1
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs, hVmul, hVsub, hVsucc, hVzero]
                exact hop _ _ (hmul _ xx htwo hxx') (hsub yy _ hyy' hone))
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ yy hone hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVT]
                exact hctorMem boolTrueName (Or.inl rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVT]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f2
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte]
                exact hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ yy hone hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVF]
                exact hctorMem boolFalseName (Or.inr rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVF]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
  · -- `Nat.shiftRight`
    simp only [divModCertStmts, divModCertProofs, natShiftRightCertProofs,
      reduceIte] at hruns
    cases hruns with
    | cons f1 r1 =>
      cases r1 with
      | cons f2 r2 =>
        have hop := hselfMem (htyOwn.1 (by decide)) ρ
        have hone := hsuccMem ρ _ (hzeroMem ρ)
        have htwo := hsuccMem ρ _ hone
        have hVble := hVd natBleName (by decide)
        have hVsucc := hVd natSuccName (by decide)
        have hVzero := hVd natZeroName (by decide)
        have hVT := hVd boolTrueName (by decide)
        have hVF := hVd boolFalseName (by decide)
        have hdiv := hdepBin natDivName (by decide) (by decide) (by decide) (by decide) ρ
        have hsub := hdepBin natSubName (by decide) (by decide) (by decide) (by decide) ρ
        have hVdiv := hVd natDivName (by decide)
        have hVsub := hVd natSubName (by decide)
        simp only [DivModClausesV, if_true, reduceIte]
        refine ⟨fun hg => ?_, fun hg => ?_⟩
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f1
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs, hVdiv, hVsub, hVsucc, hVzero]
                exact hdiv _ _ (hop xx _ hxx' (hsub yy _ hyy' hone)) htwo)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ yy hone hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVT]
                exact hctorMem boolTrueName (Or.inl rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVT]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f2
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hop xx yy hxx' hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte]
                exact hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ yy hone hyy')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVF]
                exact hctorMem boolFalseName (Or.inr rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVF]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
  · -- `Nat.log2`
    simp only [divModCertStmts, divModCertProofs, natLog2CertProofs,
      reduceIte] at hruns
    cases hruns with
    | cons f1 r1 =>
      cases r1 with
      | cons f2 r2 =>
        have hun := hunMem (htyOwn.2 rfl) ρ
        have hone := hsuccMem ρ _ (hzeroMem ρ)
        have htwo := hsuccMem ρ _ hone
        have hVble := hVd natBleName (by decide)
        have hVsucc := hVd natSuccName (by decide)
        have hVzero := hVd natZeroName (by decide)
        have hVT := hVd boolTrueName (by decide)
        have hVF := hVd boolFalseName (by decide)
        have hdiv := hdepBin natDivName (by decide) (by decide) (by decide) (by decide) ρ
        have hVdiv := hVd natDivName (by decide)
        simp only [DivModClausesV, if_true, reduceIte]
        refine ⟨fun hg => ?_, fun hg => ?_⟩
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f1
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hun xx hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs, hVdiv, hVsucc, hVzero]
                exact hsuccMem ρ _ (hun _ (hdiv xx _ hxx' htwo)))
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ xx htwo hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVT]
                exact hctorMem boolTrueName (Or.inl rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVT]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
        · have h := dmClause1S m (by rw [hcname]; exact hmem0) hvfr hgenv
            hcname φ ρ xx yy hxx hyy _ _ _ _ _ f2
            (by decide) (by decide) (by decide) (by decide)
            (by simp [Expr.wscopedB]) (by simp [Expr.wscopedB])
            (by simp [Expr.wscopedB])
            (by decide) (by decide) (by decide)
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp [dmLeavesOk, Expr.fvarLeaves])
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVs]
                exact hun xx hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVzero]
                exact hzeroMem ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero]
                exact hbleMem ρ _ xx htwo hxx')
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVF]
                exact hctorMem boolFalseName (Or.inr rfl) ρ)
            (by simp only [dmEvalV_app, dmEvalV_const, dmEvalV_fvar,
                  reduceIte, hVble, hVsucc, hVzero, hVF]
                exact hg)
          simpa [dmEvalV_app, dmEvalV_const, dmEvalV_fvar, dmVal]
            using h
end Setlec.SetR

