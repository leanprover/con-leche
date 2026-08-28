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
  what the `Eq`-spine's side conditions want.
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

end Setlec.SetR
