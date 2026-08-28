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
    {Δ : List VExpr} (hlen : Δ.length = 4)
    (hclΔ : ∀ A ∈ Δ, VExpr.Closed A)
    (hW : Expr.WScoped 4 (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))))
    (hB : (divModCertApplied (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))).looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))))
    (hslot : ∀ l ∈ (divModCertApplied
        (Expr.substConstAll c annVal proof)
        (st.1.map (Expr.substConst0 c annVal))).fvarLeaves,
      l.1 < 4 ∧ Expr.fvarsBelow l.1 l.2.2 ∧
      denote m.cval env φ 4 l.2.2 = some (Δ.getD (3 - l.1) default))
    (hWE : Expr.WScoped 4 (Expr.substConst0 c annVal st.2))
    (hBE : (Expr.substConst0 c annVal st.2).looseBVarsBounded 0 = true)
    (hLE : Expr.LeavesBounded (Expr.substConst0 c annVal st.2))
    (hslotE : ∀ l ∈ (Expr.substConst0 c annVal st.2).fvarLeaves,
      l.1 < 4 ∧ Expr.fvarsBelow l.1 l.2.2 ∧
      denote m.cval env φ 4 l.2.2 = some (Δ.getD (3 - l.1) default))
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
  have hCA : CtxOkR μ m.cval env φ 4 Δ appliedA :=
    CtxOkR.pinnedCtx hlen hclΔ (fun l hl => hslot l (hsub l hl))
  have hCE : CtxOkR μ m.cval env φ 4 Δ
      (Expr.substConst0 c annVal st.2) :=
    CtxOkR.pinnedCtx hlen hclΔ hslotE
  obtain ⟨v, tv, hv, htv, T', hInf, hDeq⟩ :=
    ihi hinf hWA hBA hLA hCA
  have hWtp : Expr.WScoped 4 tp :=
    inferTypeCore_WScoped m.wf F hinf hWA
  have hBtp : tp.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf F hinf hWA hBA hLA
  have hLtp : Expr.LeavesBounded tp :=
    fun l hl => hLA l (inferTypeCore_fvarLeaves m.wf F hinf hWA l hl)
  have hCtp : CtxOkR μ m.cval env φ 4 Δ tp :=
    CtxOkR.of_subset (inferTypeCore_fvarLeaves m.wf F hinf hWA) hCA
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

/-- A stored, pinned **binary** operation is a function on the frame's
`Nat`: its valuation applied to two members of `⟦Nat⟧` lands in the
codomain's. -/
theorem dmBinMem {env : Env} (m : EnvS V env) (φ : Name → Nat)
    {n : Name} {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    {nm nm2 : Name} {mb mb2 : BinderMeta} {cn : Name}
    (hf : env.find? n = some (.defnInfo cv v hint))
    (hty : cv.type = .forallE nm (.const natName [])
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
  rw [show (ConstantInfo.defnInfo cv v hint).toConstantVal = cv from rfl,
    hty, denoteClosed] at ht
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
    {n : Name} {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    {nm : Name} {mb : BinderMeta} {cn : Name}
    (hf : env.find? n = some (.defnInfo cv v hint))
    (hty : cv.type = .forallE nm (.const natName []) (.const cn []) mb)
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    {ciC : ConstantInfo} (hfC : env.find? cn = some ciC)
    (hlpC : ciC.toConstantVal.levelParams = [])
    (ρ : Nat → V) {x : V}
    (hx : x ∈ˢ interp V ρ (m.cval natName φ)) :
    SetTheory.app (interp V ρ (m.cval n φ)) x
      ∈ˢ interp V ρ (m.cval cn φ) := by
  obtain ⟨t, ht, hlaw⟩ := m.cval_memType hf φ
  rw [show (ConstantInfo.defnInfo cv v hint).toConstantVal = cv from rfl,
    hty, denoteClosed] at ht
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

/-- The frame's four entries: the two hypothesis slots on top, the two
`Nat` variables below. -/
def dmCtx (H1 H2 natV : VExpr) : List VExpr := [H2, H1, natV, natV]

@[simp] theorem dmCtx_len {H1 H2 natV : VExpr} :
    (dmCtx H1 H2 natV).length = 4 := rfl

/-- A statement's leaves sit in the two `Nat` slots. -/
theorem dmSlots_stmt {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} (φ : Name → Nat) {H1 H2 natV : VExpr}
    (hvf : value'.hasFvar = false)
    (hnat : denote cval env φ 4 (Expr.const natName []) = some natV)
    {e : Expr} (h : dmLeavesOk e = true) :
    ∀ l ∈ (Expr.substConst0 c value' e).fvarLeaves, l.1 < 4 ∧
      Expr.fvarsBelow l.1 l.2.2 ∧
      denote cval env φ 4 l.2.2
        = some ((dmCtx H1 H2 natV).getD (3 - l.1) default) := by
  intro l hl
  rw [fvarLeaves_substConst0 (n := c) hvf e] at hl
  rcases dmLeavesOk_mem h hl with rfl | rfl
  · exact ⟨by omega, trivial, hnat⟩
  · exact ⟨by omega, trivial, hnat⟩

/-- The two-hypothesis applied certificate's leaves sit in their four
slots. -/
theorem dmSlots_applied2 {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} (φ : Name → Nat) {H1 H2 natV : VExpr}
    (hvf : value'.hasFvar = false)
    (hnat : denote cval env φ 4 (Expr.const natName []) = some natV)
    {h1 h2 p : Expr} (hp : p.hasFvar = false)
    (hl1 : dmLeavesOk h1 = true) (hl2 : dmLeavesOk h2 = true)
    (hfb1 : Expr.fvarsBelow 2 (Expr.substConst0 c value' h1))
    (hfb2 : Expr.fvarsBelow 3 (Expr.substConst0 c value' h2))
    (hd1 : denote cval env φ 4 (Expr.substConst0 c value' h1) = some H1)
    (hd2 : denote cval env φ 4 (Expr.substConst0 c value' h2)
      = some H2) :
    ∀ l ∈ (divModCertApplied p [Expr.substConst0 c value' h1,
        Expr.substConst0 c value' h2]).fvarLeaves,
      l.1 < 4 ∧ Expr.fvarsBelow l.1 l.2.2 ∧
      denote cval env φ 4 l.2.2
        = some ((dmCtx H1 H2 natV).getD (3 - l.1) default) := by
  intro l hl
  rcases divModCertApplied_mem2 hp hl with rfl | rfl | rfl | hm | rfl | hm
  · exact ⟨by omega, trivial, hnat⟩
  · exact ⟨by omega, trivial, hnat⟩
  · exact ⟨by omega, hfb1, hd1⟩
  · exact dmSlots_stmt (c := c) (value' := value') (H1 := H1)
      (H2 := H2) φ hvf hnat hl1 l hm
  · exact ⟨by omega, hfb2, hd2⟩
  · exact dmSlots_stmt (c := c) (value' := value') (H1 := H1)
      (H2 := H2) φ hvf hnat hl2 l hm

/-- The one-hypothesis applied certificate's leaves. -/
theorem dmSlots_applied1 {env : Env} {cval : TConstVal} {c : Name}
    {value' : Expr} (φ : Name → Nat) {H1 H2 natV : VExpr}
    (hvf : value'.hasFvar = false)
    (hnat : denote cval env φ 4 (Expr.const natName []) = some natV)
    {h1 p : Expr} (hp : p.hasFvar = false)
    (hl1 : dmLeavesOk h1 = true)
    (hfb1 : Expr.fvarsBelow 2 (Expr.substConst0 c value' h1))
    (hd1 : denote cval env φ 4 (Expr.substConst0 c value' h1)
      = some H1) :
    ∀ l ∈ (divModCertApplied p
        [Expr.substConst0 c value' h1]).fvarLeaves,
      l.1 < 4 ∧ Expr.fvarsBelow l.1 l.2.2 ∧
      denote cval env φ 4 l.2.2
        = some ((dmCtx H1 H2 natV).getD (3 - l.1) default) := by
  intro l hl
  rcases divModCertApplied_mem1 hp hl with rfl | rfl | rfl | hm
  · exact ⟨by omega, trivial, hnat⟩
  · exact ⟨by omega, trivial, hnat⟩
  · exact ⟨by omega, hfb1, hd1⟩
  · exact dmSlots_stmt (c := c) (value' := value') (H1 := H1)
      (H2 := H2) φ hvf hnat hl1 l hm

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
    {natV H1 H2 lV rV : VExpr}
    (hnat : denote m.cval env φ 4 (Expr.const natName []) = some natV)
    (hd1 : denote m.cval env φ 4 (Expr.substConst0 c value' h1)
      = some H1)
    (hd2 : denote m.cval env φ 4 (Expr.substConst0 c value' h2)
      = some H2)
    (hdl : denote m.cval env φ 4 (Expr.substConst0 c value' l)
      = some lV)
    (hdr : denote m.cval env φ 4 (Expr.substConst0 c value' r)
      = some rV)
    (hclN : VExpr.Closed natV) (hcl1 : VExpr.Closed H1)
    (hcl2 : VExpr.Closed H2)
    (ρ : Nat → V)
    (hs0 : ρ 0 ∈ˢ interp V ρ H2) (hs1 : ρ 1 ∈ˢ interp V ρ H1)
    (hs2 : ρ 2 ∈ˢ interp V ρ natV) (hs3 : ρ 3 ∈ˢ interp V ρ natV)
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
  have hw := certValueS m φ hfacts (Δ := dmCtx H1 H2 natV) rfl
    (by intro A hA
        simp only [dmCtx, List.mem_cons, List.not_mem_nil,
          or_false] at hA
        rcases hA with rfl | rfl | rfl | rfl <;> assumption)
    hWA hBA hLA
    (dmSlots_applied2 φ hvf hnat hpf hl1 hl2 hw1'.fvarsBelow
      hw2'.fvarsBelow hd1 hd2)
    hwE hbE hLE
    (dmSlots_stmt (c := c) (value' := value') (H1 := H1) (H2 := H2)
      φ hvf hnat hlE)
    hvE ρ
    (sat_four hcl2 hcl1 hclN hclN hs0 hs1 hs2 hs3)
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
    {natV H1 H2 lV rV : VExpr}
    (hnat : denote m.cval env φ 4 (Expr.const natName []) = some natV)
    (hd1 : denote m.cval env φ 4 (Expr.substConst0 c value' h1)
      = some H1)
    (hdl : denote m.cval env φ 4 (Expr.substConst0 c value' l)
      = some lV)
    (hdr : denote m.cval env φ 4 (Expr.substConst0 c value' r)
      = some rV)
    (hclN : VExpr.Closed natV) (hcl1 : VExpr.Closed H1)
    (hcl2 : VExpr.Closed H2)
    (ρ : Nat → V)
    (hs0 : ρ 0 ∈ˢ interp V ρ H2) (hs1 : ρ 1 ∈ˢ interp V ρ H1)
    (hs2 : ρ 2 ∈ˢ interp V ρ natV) (hs3 : ρ 3 ∈ˢ interp V ρ natV)
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
  have hw := certValueS m φ hfacts (Δ := dmCtx H1 H2 natV) rfl
    (by intro A hA
        simp only [dmCtx, List.mem_cons, List.not_mem_nil,
          or_false] at hA
        rcases hA with rfl | rfl | rfl | rfl <;> assumption)
    hWA hBA hLA
    (dmSlots_applied1 (H2 := H2) φ hvf hnat hpf hl1 hw1'.fvarsBelow hd1)
    hwE hbE hLE
    (dmSlots_stmt (c := c) (value' := value') (H1 := H1) (H2 := H2)
      φ hvf hnat hlE)
    hvE ρ
    (sat_four hcl2 hcl1 hclN hclN hs0 hs1 hs2 hs3)
  obtain ⟨w, hw'⟩ := hw
  exact eqSpine_eq m φ hEq ρ hNU hlm hrm hw'

end Setlec.SetR
