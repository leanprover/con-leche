import Setlec.SetR.Bridge.Main
import Setlec.SetR.Bridge.Decl
import Setlec.SetR.Install.Value
import Setlec.Verify.DivModInv

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

/-- A closed replacement moves no leaf. -/
theorem fvarLeaves_substConst0 {n : Name} {r : Expr}
    (hr : r.hasFvar = false) :
    ∀ e : Expr, (Expr.substConst0 n r e).fvarLeaves = e.fvarLeaves
  | .const c us => by
    simp only [Expr.substConst0]
    split
    · exact (Expr.fvarLeaves_eq_nil_of_not_hasFvar hr).trans
        (Expr.fvarLeaves_eq_nil_of_not_hasFvar
          (e := .const c us) (by simp [Expr.hasFvar])).symm
    · rfl
  | .app f a => by
    simp only [Expr.substConst0, Expr.fvarLeaves,
      fvarLeaves_substConst0 hr f, fvarLeaves_substConst0 hr a]
  | .bvar _ | .fvar _ _ _ | .sort _ | .lit _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .proj _ _ _ => rfl

/-- A `looseBVars`-closed replacement keeps the bound. -/
theorem looseBVarsBounded_substConst0 {n : Name} {r : Expr}
    (hr : r.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) {k : Nat}, e.looseBVarsBounded k = true →
      (Expr.substConst0 n r e).looseBVarsBounded k = true
  | .const c us, k, he => by
    simp only [Expr.substConst0]
    split
    · exact Expr.looseBVarsBounded_mono (Nat.zero_le k) hr
    · exact he
  | .app f a, k, he => by
    simp only [Expr.substConst0, Expr.looseBVarsBounded,
      Bool.and_eq_true] at he ⊢
    exact ⟨looseBVarsBounded_substConst0 hr f he.1,
      looseBVarsBounded_substConst0 hr a he.2⟩
  | .bvar _, _, he | .fvar _ _ _, _, he | .sort _, _, he
  | .lit _, _, he | .lam _ _ _ _, _, he | .forallE _ _ _ _, _, he
  | .letE _ _ _ _, _, he | .proj _ _ _, _, he => he

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

/-- The binary pinned type, inverted. -/
theorem natOpTyPinned_binaryE {env : Env} {n : Name} {ty : Expr}
    (hn : (n = natPredName || n = natLog2Name) = false)
    (h : natOpTyPinned env n ty = true) :
    ∃ nm nm2 mb mb2 cod, ty = .forallE nm (.const natName [])
      (.forallE nm2 (.const natName []) cod mb2) mb ∧
      natOpCod env n cod = true := by
  unfold natOpTyPinned at h
  rw [hn] at h
  revert h
  match ty with
  | .forallE nm dom (.forallE nm2 dom2 cod mb2) mb =>
    intro h
    rw [if_neg (show ¬(false = true) from by decide)] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨nm, nm2, mb, mb2, cod, by rw [h.1.1, h.1.2], h.2⟩
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _
  | .forallE _ _ (.bvar _) _ | .forallE _ _ (.fvar _ _ _) _
  | .forallE _ _ (.sort _) _ | .forallE _ _ (.const _ _) _
  | .forallE _ _ (.app _ _) _ | .forallE _ _ (.lam _ _ _ _) _
  | .forallE _ _ (.letE _ _ _ _) _ | .forallE _ _ (.lit _) _
  | .forallE _ _ (.proj _ _ _) _ => intro h; exact nomatch h

/-- The unary pinned type, inverted. -/
theorem natOpTyPinned_unaryE {env : Env} {n : Name} {ty : Expr}
    (hn : (n = natPredName || n = natLog2Name) = true)
    (h : natOpTyPinned env n ty = true) :
    ∃ nm mb cod, ty = .forallE nm (.const natName []) cod mb ∧
      natOpCod env n cod = true := by
  unfold natOpTyPinned at h
  rw [hn] at h
  revert h
  match ty with
  | .forallE nm dom cod mb =>
    intro h
    rw [if_pos rfl] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨nm, mb, cod, by rw [h.1], h.2⟩
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h

/-- The codomain is a stored, level-monomorphic constant. -/
theorem natOpCod_stored {env : Env} {n : Name} {cod : Expr}
    (h : natOpCod env n cod = true) :
    (∃ ci, cod = .const boolName [] ∧
      env.find? boolName = some ci ∧
      ci.toConstantVal.levelParams = []) ∨ cod = .const natName [] := by
  unfold natOpCod at h
  split at h
  · refine Or.inl ?_
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    revert h2
    cases hb : env.find? boolName with
    | none => intro h2; exact nomatch h2
    | some ci =>
      intro h2
      simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h2
      exact ⟨ci, rfl, rfl, h2.1⟩
  · exact Or.inr (by simpa using h)

/-- `Nat.ble`'s codomain is the stored `Bool`. -/
theorem natOpCod_ble {env : Env} {cod : Expr}
    (h : natOpCod env natBleName cod = true) :
    cod = Expr.const boolName [] ∧ ∃ ci,
      env.find? boolName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type = .sort (.succ .zero) := by
  unfold natOpCod at h
  rw [if_pos (show (decide (natBleName = natBeqName) ||
    decide (natBleName = natBleName)) = true from by decide)] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, h2⟩ := h
  revert h2
  cases hb : env.find? boolName with
  | none => intro h2; exact nomatch h2
  | some ci =>
    intro h2
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h2
    exact ⟨rfl, ci, rfl, h2.1, h2.2⟩

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

/-- Where a leaf of the two-hypothesis applied form can come from. -/
theorem divModCertApplied_mem2 {p h1 h2 : Expr}
    (hp : p.hasFvar = false) {l : Nat × Name × Expr}
    (hl : l ∈ (divModCertApplied p [h1, h2]).fvarLeaves) :
    l = (0, Name.anonymous.str "x", Expr.const natName []) ∨
    l = (1, Name.anonymous.str "y", Expr.const natName []) ∨
    l = (2, Name.anonymous.str "h1", h1) ∨ l ∈ h1.fvarLeaves ∨
    l = (3, Name.anonymous.str "h2", h2) ∨ l ∈ h2.fvarLeaves := by
  simp only [divModCertApplied, Expr.fvarLeaves,
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hp, List.nil_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with ((h | h) | h | h) | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- Where a leaf of the one-hypothesis applied form can come from. -/
theorem divModCertApplied_mem1 {p h1 : Expr}
    (hp : p.hasFvar = false) {l : Nat × Name × Expr}
    (hl : l ∈ (divModCertApplied p [h1]).fvarLeaves) :
    l = (0, Name.anonymous.str "x", Expr.const natName []) ∨
    l = (1, Name.anonymous.str "y", Expr.const natName []) ∨
    l = (2, Name.anonymous.str "h1", h1) ∨ l ∈ h1.fvarLeaves := by
  simp only [divModCertApplied, Expr.fvarLeaves,
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hp, List.nil_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with (h | h) | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-! ## The statements' syntactic frame, decided

Every div/mod certificate statement mentions exactly the two frame
variables `x` and `y`, both at `Nat`.  That is a decidable property of
the (literal) statement, and it is all the depth-4 frame needs from
it. -/

/-- Is every leaf of `e` the frame's `x` or `y`, at `Nat`? -/
def dmLeavesOk (e : Expr) : Bool :=
  e.fvarLeaves.all (fun l =>
    (l.1 == 0 && l.2.1 == Name.anonymous.str "x" &&
      l.2.2 == Expr.const natName []) ||
    (l.1 == 1 && l.2.1 == Name.anonymous.str "y" &&
      l.2.2 == Expr.const natName []))

/-- A leaf of a `dmLeavesOk` term, identified. -/
theorem dmLeavesOk_mem {e : Expr} (h : dmLeavesOk e = true)
    {l : Nat × Name × Expr} (hl : l ∈ e.fvarLeaves) :
    l = (0, Name.anonymous.str "x", Expr.const natName []) ∨
    l = (1, Name.anonymous.str "y", Expr.const natName []) := by
  have hm := List.all_eq_true.mp h l hl
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
  rcases hm with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl (by
      rcases l with ⟨i, n, t⟩
      simp only at h1 h2 h3
      rw [h1, h2, h3])
  · exact Or.inr (by
      rcases l with ⟨i, n, t⟩
      simp only at h1 h2 h3
      rw [h1, h2, h3])

/-- `dmLeavesOk` survives the operation substitution. -/
theorem dmLeavesOk_substConst0 {c : Name} {value' e : Expr}
    (hvf : value'.hasFvar = false) (h : dmLeavesOk e = true) :
    dmLeavesOk (Expr.substConst0 c value' e) = true := by
  unfold dmLeavesOk at h ⊢
  rw [fvarLeaves_substConst0 hvf e]
  exact h

/-- A `dmLeavesOk` term is leaf-bounded: `Nat` has no loose bound
variables. -/
theorem dmLeavesOk_leavesBounded {e : Expr} (h : dmLeavesOk e = true) :
    Expr.LeavesBounded e := by
  intro l hl
  rcases dmLeavesOk_mem h hl with rfl | rfl <;> rfl

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

/-- A frame variable is well-scoped at depth 4. -/
theorem dmFvar_wscoped {i : Nat} {n : Name} {ty : Expr} (hi : i < 4)
    (hty : Expr.WScoped i ty) :
    Expr.WScoped 4 (Expr.fvar i n ty) := by
  simp only [Expr.WScoped]
  exact ⟨hi, hty⟩

/-- Scope composes over applications. -/
theorem dmApp_wscoped {d : Nat} {f a : Expr} (hf : Expr.WScoped d f)
    (ha : Expr.WScoped d a) : Expr.WScoped d (.app f a) := by
  simp only [Expr.WScoped]
  exact ⟨hf, ha⟩

/-- The two-hypothesis applied form's scope and bound-variable
facts. -/
theorem dmApplied2_frame {p a b : Expr}
    (hpf : p.hasFvar = false) (hpb : p.looseBVarsBounded 0 = true)
    (hwa : Expr.WScoped 2 a) (hwb : Expr.WScoped 3 b) :
    Expr.WScoped 4 (divModCertApplied p [a, b]) ∧
      (divModCertApplied p [a, b]).looseBVarsBounded 0 = true := by
  refine ⟨?_, ?_⟩
  · show Expr.WScoped 4 (.app (.app (.app (.app p _) _) _) _)
    exact dmApp_wscoped (dmApp_wscoped (dmApp_wscoped
      (Expr.WScoped.of_not_hasFvar hpf)
      (dmFvar_wscoped (by omega) (Expr.WScoped.of_not_hasFvar rfl)))
      (dmFvar_wscoped (by omega) (Expr.WScoped.of_not_hasFvar rfl)))
      (dmFvar_wscoped (by omega) hwa) |> fun h =>
        dmApp_wscoped h (dmFvar_wscoped (by omega) hwb)
  · show ((((p.app _).app _).app _).app _).looseBVarsBounded 0 = true
    simp [Expr.looseBVarsBounded, hpb]

/-- The one-hypothesis applied form's scope and bound-variable
facts. -/
theorem dmApplied1_frame {p a : Expr}
    (hpf : p.hasFvar = false) (hpb : p.looseBVarsBounded 0 = true)
    (hwa : Expr.WScoped 2 a) :
    Expr.WScoped 4 (divModCertApplied p [a]) ∧
      (divModCertApplied p [a]).looseBVarsBounded 0 = true := by
  refine ⟨?_, ?_⟩
  · show Expr.WScoped 4 (.app (.app (.app p _) _) _)
    exact dmApp_wscoped (dmApp_wscoped (dmApp_wscoped
      (Expr.WScoped.of_not_hasFvar hpf)
      (dmFvar_wscoped (by omega) (Expr.WScoped.of_not_hasFvar rfl)))
      (dmFvar_wscoped (by omega) (Expr.WScoped.of_not_hasFvar rfl)))
      (dmFvar_wscoped (by omega) hwa)
  · show (((p.app _).app _).app _).looseBVarsBounded 0 = true
    simp [Expr.looseBVarsBounded, hpb]

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
  obtain ⟨-, -, -, -, -, hfront⟩ := hvfr
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

/-- The grammar's value at a valuation of the heads. -/
noncomputable def dmEvalV (W : Type w) [SetTheory W]
    (val : Name → W) (x y : W) : Expr → W
  | Expr.const n _ => val n
  | Expr.app f a =>
    SetTheory.app (dmEvalV W val x y f) (dmEvalV W val x y a)
  | Expr.fvar i _ _ => if i = 0 then x else y
  | _ => pt

@[simp] theorem dmEvalV_const (val : Name → V) (x y : V) (n : Name)
    (us : List Level) : dmEvalV V val x y (Expr.const n us) = val n := rfl

@[simp] theorem dmEvalV_app (val : Name → V) (x y : V) (f a : Expr) :
    dmEvalV V val x y (Expr.app f a)
      = SetTheory.app (dmEvalV V val x y f) (dmEvalV V val x y a) := rfl

@[simp] theorem dmEvalV_fvar (val : Name → V) (x y : V) (i : Nat)
    (n : Name) (ty : Expr) :
    dmEvalV V val x y (Expr.fvar i n ty) = if i = 0 then x else y := rfl

/-- **The fragment, denoted and evaluated.** -/
theorem dmDenEval {env : Env} (m : EnvS V env) (φ : Name → Nat)
    {c : Name} {value' : Expr} {ns : List Name}
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hvf : value'.hasFvar = false)
    (hvb : value'.looseBVarsBounded 0 = true)
    {Vc : VExpr} (hVc : denoteClosed m.cval env φ value' = some Vc)
    (hstore : ∀ n ∈ ns, n = c ∨ (n ≠ c ∧ ∃ ci,
      env.find? n = some ci ∧ ci.toConstantVal.levelParams = [])) :
    ∀ e : Expr, dmFragOk c ns e = true →
      ∃ eV, denote m.cval env φ 4 (Expr.substConst0 c value' e)
          = some eV ∧
        ∀ ρ4 : Nat → V, interp V ρ4 eV
          = dmEvalV V (fun n => interp V ρ4
              (dmVal m.cval env c value' φ n)) (ρ4 3) (ρ4 2) e
  | .const n us, h => by
    simp only [dmFragOk, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq, List.isEmpty_iff] at h
    obtain ⟨hn, rfl⟩ := h
    rcases hn with rfl | hn
    · exact ⟨_, denote_dmSelf φ hcl hvf hvb hVc 4, fun ρ4 => rfl⟩
    · rcases hstore n (by simpa using hn) with rfl | ⟨hnc, ci, hfi, hlpi⟩
      · exact ⟨_, denote_dmSelf φ hcl hvf hvb hVc 4, fun ρ4 => rfl⟩
      · exact ⟨_, denote_dmDep φ hfi hlpi hnc 4, fun ρ4 => rfl⟩
  | .app f a, h => by
    simp only [dmFragOk, Bool.and_eq_true] at h
    obtain ⟨fV, hfd, hfe⟩ := dmDenEval m φ hcl hvf hvb hVc hstore f h.1
    obtain ⟨aV, had, hae⟩ := dmDenEval m φ hcl hvf hvb hVc hstore a h.2
    exact ⟨_, denote_dmApp1 hfd had, fun ρ4 => by
      rw [interp_app, hfe, hae, dmEvalV_app]⟩
  | .fvar i nm ty, h => by
    simp only [dmFragOk, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    rcases hi with rfl | rfl
    · exact ⟨.bvar 3, denote_dmX, fun ρ4 => by simp [dmEvalV_fvar]⟩
    · exact ⟨.bvar 2, denote_dmY, fun ρ4 => by simp [dmEvalV_fvar]⟩
  | .bvar _, h | .sort _, h | .lam _ _ _ _, h | .letE _ _ _ _, h
  | .forallE _ _ _ _, h | .lit _, h | .proj _ _ _, h => nomatch h

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
        ∀ (ρ' : Nat → V) (a b : V),
          a ∈ˢ interp V ρ' (m.cval natName φ) →
          b ∈ˢ interp V ρ' (m.cval natName φ) →
          ∃ cn, (cn = boolName ∨ cn = natName) ∧
          SetTheory.app (SetTheory.app (interp V ρ' (m.cval n φ)) a) b
            ∈ˢ interp V ρ' (m.cval cn φ)) ∧
      ((∃ nm nm2 mb mb2 cn, type' = .forallE nm (.const natName [])
          (.forallE nm2 (.const natName []) (.const cn []) mb2) mb) ∨
        (∃ nm mb cn, type' = .forallE nm (.const natName [])
          (.const cn []) mb)) := by
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
  obtain ⟨⟨hlit, -⟩, -⟩ := hnog
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
      ∀ (ρ' : Nat → V) (a b : V),
        a ∈ˢ interp V ρ' (m.cval natName φ) →
        b ∈ˢ interp V ρ' (m.cval natName φ) →
        ∃ cn, (cn = boolName ∨ cn = natName) ∧
        SetTheory.app (SetTheory.app (interp V ρ' (m.cval n φ)) a) b
          ∈ˢ interp V ρ' (m.cval cn φ) := by
    intro n hn hnc hnu ρ' a b ha hb
    obtain ⟨cvn, vn, hintn, hfn2, hpin2⟩ :=
      natOpStoredOk_tyPinned (hdepAll n hn)
    obtain ⟨nm, nm2, mb, mb2, cod, htyn, hcod⟩ :=
      natOpTyPinned_binaryE hnu hpin2
    have hfn : env.find? n = some (.defnInfo cvn vn hintn) :=
      hdown _ _ hnc hfn2
    rcases natOpCod_stored hcod with ⟨ciB, rfl, hfB2, hlpB⟩ | rfl
    · exact ⟨boolName, Or.inl rfl,
        dmBinMem m φ hfn htyn hfN hlpN
          (hdown _ _ (hne _ (by simp)) hfB2) hlpB ρ' ha hb⟩
    · exact ⟨natName, Or.inr rfl,
        dmBinMem m φ hfn htyn hfN hlpN hfN hlpN ρ' ha hb⟩
  -- the value front door: the checked value's own denotation
  obtain ⟨hvlb, hvhf, hannv, -, -, hfront⟩ := id hvfr
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
  have htyOwn :
      ((∃ nm nm2 mb mb2 cn, type' = Expr.forallE nm (.const natName [])
          (.forallE nm2 (.const natName []) (.const cn []) mb2) mb) ∨
        (∃ nm mb cn, type' = Expr.forallE nm (.const natName [])
          (.const cn []) mb)) := by
    by_cases hun : (cv.name = natPredName || cv.name = natLog2Name)
        = true
    · obtain ⟨nmT, mbT, codT, htyT, hcodT⟩ :=
        natOpTyPinned_unaryE hun (htyS2 ▸ hpinS2)
      refine Or.inr ⟨nmT, mbT, ?_⟩
      rcases natOpCod_stored hcodT with ⟨-, rfl, -⟩ | rfl
      · exact ⟨boolName, htyT⟩
      · exact ⟨natName, htyT⟩
    · obtain ⟨nmT, nmT2, mbT, mbT2, codT, htyT, hcodT⟩ :=
        natOpTyPinned_binaryE (by simpa using hun) (htyS2 ▸ hpinS2)
      refine Or.inl ⟨nmT, nmT2, mbT, mbT2, ?_⟩
      rcases natOpCod_stored hcodT with ⟨-, rfl, -⟩ | rfl
      · exact ⟨boolName, htyT⟩
      · exact ⟨natName, htyT⟩
  exact ⟨_, ciB, Vc, hfN, hlpN, hfB, hlpB, hEqE, hVc, hvalSelf,
    hvalNat, hNU, hBU, hbleMem, hdepBin, htyOwn⟩

end Setlec.SetR
