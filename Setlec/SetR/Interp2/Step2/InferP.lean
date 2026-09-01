import Setlec.SetR.Interp2.CtxOkPKit
import Setlec.SetR.Annot.BitLemmas
import Setlec.Verify.InferLemmas
import Setlec.SetR.Interp2.Step2.InferQ

/-!
# The infer quarter, P currency — the worked ∀ clause (task #161, P3.5)

`infer_forallE_claimP` below is the P-tier mirror of
`infer_forallE_claim2D` (`Step2/InferQ.lean`), and it is the **species
example** for the whole infer quarter: every binder clause of the swap
runs the same four moves —

1. the run inversion delivers the P2 validation conjunct
   (`(zeronessOf v).equiv mb.pw`, at `μ.verified`) alongside the sort
   runs — no `sortOfE` cross-fuel gymnastics, the annotation's numeral
   is `pwBit φ mb.pw` *definitionally* (`denoteP_forallE_inv`);
2. `SortSemP` (the routed residue, `SortSem2` with `sortOfE` unfolded
   into its two checker runs and the currency upgraded) grades domain
   and opened codomain;
3. **establishment**: `AnnotValidV`'s `pi` component is
   `pwBit_zero_mem_univZero` at the conjunct + the codomain's sort
   membership — one line;
4. **the numeral bridge**: the row (`sound_pi`) speaks at the true
   sort numerals; `piR_zero_agree` carries it to the stored bit, with
   `pwBit_of_equiv_zeronessOf` supplying the zero-agreement — this is
   where residue 9's sort-agreement machinery used to live, and it is
   now a rewrite.

**Mode pinning.**  The claims (`Claims2P`) quantify `μ`, but the
*step proofs* hold at `μ.verified = true` only: the validation
conjuncts are conditional on the mode, and at `.noModel` a stored bit
is unvalidated.  The P-tier assembly (and the capstone) is a
verified-mode statement — which is the design: the annotated checker's
consistency proof covers the mode that validates.

The opened contexts are built in place by `CtxOkP.openS` (batch 2),
at the grading the clause's own residue supplies — the D-tier's
self-propagation argument, inherited.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level whnf inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- **The P-tier sort-semantics residue** (`SortSem2` transposed): a
subject whose inferred type whnfs to a sort is graded (`AnnotOkP`) and
interprets into that universe — at every checker fuel, in the fuel-free
reading.  Routed exactly as `SortSem2` is: the top-level induction is
where it becomes available. -/
def SortSemP {env : Env} (m : EnvS2UM V μ env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {e t : Expr} {u : Level} {Δa : List AVExpr}
    {ea : AVExpr},
    CtxOkP m φ d Δa e →
    inferTypeCore μ env F d e = .ok t →
    whnf μ env F d t = .ok (.sort u) →
    denoteP m.acval env φ d e = some ea →
    ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOkP V ρ ea ∧ interp2 V ρ ea ∈ˢ (univ (u.eval φ) : V)

/-- `denoteP` at a sort (the `denote2_sortQ` mirror). -/
theorem denoteP_sortQ {acval : Name → (Name → Nat) → AVExpr} {d : Nat}
    {u : Level} :
    denoteP acval env φ d (.sort u) = some (.sort (u.eval φ)) := by
  rw [denoteP]

/-- **The leaf-validity residue** (the P tier's one new routed
obligation): every stored leaf of the annotated valuation is
bit-valid.  The `AnnotOk2` half is already an `EnvS2U` field
(`acval_ok2`); this is its `AnnotValidV` companion, to be discharged
at the install tier — a stored type's annotations went through the
checker's own front door, which is establishment — and folded into the
environment structure there (with the owed `EnvWF` records, if the
seal's invariants state them naturally). -/
def AcvalValidP {env : Env} (m : EnvS2UM V μ env) : Prop :=
  ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotValidV V ρ (m.acval n ψ)

/-- **The `const` clause's residue, P currency** (`ConstType2C`
transposed: no fuel, `AnnotOkP` conclusion). -/
def ConstTypeP {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (n : Name) (ci : Setlec.ConstantInfo) (us : List Level),
    env.find? n = some ci →
    us.length = ci.toConstantVal.levelParams.length →
    ∃ ta,
      denoteP m.acval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta ∧
      (∀ ρ : Nat → V, AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp2 V ρ (m.acval n
            (Level.substFn φ ci.toConstantVal.levelParams us))
          ∈ˢ interp2 V ρ ta

/-- `.const`, P currency: the residue answers with the type's row; the
subject's grading is the two leaf facts (`acval_ok2` + the routed
`AcvalValidP`). -/
theorem infer_const_claimP (m : EnvS2UM V μ env)
    (hct : ConstTypeP m φ) (hval : AcvalValidP m)
    {d : Nat} {n : Name} {us : List Level} {t : Expr}
    {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.const n us) = .ok t)
    (hea : denoteP m.acval env φ d (.const n us) = some ea)
    (hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  cases hf : env.find? n with
  | none =>
    rw [hf] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    rw [hf] at h
    dsimp only at h
    split at h
    · next hlen =>
      simp only [Except.ok.injEq] at h
      subst h
      rw [denoteP, hf] at hea
      dsimp only at hea
      rw [if_pos hlen] at hea
      obtain rfl : ea = m.acval n
          (Level.substFn φ ci.toConstantVal.levelParams us) :=
        (Option.some.inj hea).symm
      obtain ⟨ta', hta', hok, hmem⟩ := hct d n ci us hf hlen
      rw [hta'] at hta
      obtain rfl : ta = ta' := (Option.some.inj hta).symm
      exact ⟨fun ρ _ => ⟨m.acval_ok2 n _ ρ, hval n _ ρ⟩,
        fun ρ _ => hok ρ, fun ρ _ => hmem ρ⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `.sort`, P currency: both readings are sort nodes, gradings are
vacuous, the row is `sound_sort`. -/
theorem infer_sort_claimP (m : EnvS2UM V μ env) {d : Nat} {u : Level}
    {t : Expr} {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.sort u) = .ok t)
    (hea : denoteP m.acval env φ d (.sort u) = some ea)
    (hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind, Except.ok.injEq] at h
  subst h
  rw [denoteP_sortQ] at hea hta
  obtain rfl : ea = .sort (u.eval φ) := (Option.some.inj hea).symm
  obtain rfl : ta = .sort (Level.eval φ (.succ u)) :=
    (Option.some.inj hta).symm
  refine ⟨fun _ _ => ⟨by simp, by simp⟩,
    fun _ _ => ⟨by simp, by simp⟩, ?_⟩
  intro ρ _
  exact (sound_sort V ρ (u.eval φ)).2

/-- `.bvar`, P currency: outside the fragment, the checker throws. -/
theorem infer_bvar_claimP (m : EnvS2UM V μ env) {d i : Nat} {t : Expr}
    {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.bvar i) = .ok t)
    (_hea : denoteP m.acval env φ d (.bvar i) = some ea)
    (_hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `.fvar`, P currency: the leaf package of `CtxOkP` carries the
fourth conjunct at `AnnotOkP`, so the clause takes no residue —
`infer_fvar_claim2D`'s improvement inherited by construction. -/
theorem infer_fvar_claimP (m : EnvS2UM V μ env)
    {d idx : Nat} {n : Name} {ty t : Expr} {Δa : List AVExpr}
    {ea ta : AVExpr}
    (hC : CtxOkP m φ d Δa (.fvar idx n ty))
    (h : inferTypeCore μ env (fuel + 1) d (.fvar idx n ty) = .ok t)
    (hea : denoteP m.acval env φ d (.fvar idx n ty) = some ea)
    (hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨-, -, tya, Aa, hden, hi, hlink, hokP⟩ := CtxOkP.fvar_leaf hC
  rw [denoteP] at hea
  obtain rfl : ea = .bvar (d - 1 - idx) := (Option.some.inj hea).symm
  rw [Setlec.inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, pure,
    Except.pure, Bind.bind, Except.bind] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    rw [hden] at hta
    obtain rfl : ta = tya := (Option.some.inj hta).symm
    refine ⟨fun _ _ => ⟨by simp, by simp⟩, hokP, ?_⟩
    intro ρ hρ
    rw [interp2_bvar, hlink ρ hρ]
    exact hρ (d - 1 - idx) Aa hi
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **`.forallE`, P currency** — see the module docstring; the four
moves annotated inline. -/
theorem infer_forallE_claimP (m : EnvS2UM V μ env)
    (hμ : μ.verified = true) (hss : SortSemP m μ φ)
    {d : Nat} {n : Name} {ty body t : Expr} {mb : Setlec.BinderMeta}
    {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.forallE n ty body mb)
      = .ok t)
    (hC : CtxOkP m φ d Δa (.forallE n ty body mb))
    (hea : denoteP m.acval env φ d (.forallE n ty body mb) = some ea)
    (hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  -- move 1: the run inversion, validation conjunct included
  obtain ⟨tty, u, bt, v, hty, hwu, hbt, hens, hpw, rfl⟩ :=
    Setlec.inferTypeCore_forall_inv h
  have hz := hpw hμ
  obtain ⟨tyA, baA, htyA, hbaA, rfl⟩ := denoteP_forallE_inv hea
  rw [denoteP_sortQ] at hta
  obtain rfl : ta = .sort (Level.eval φ (.imax u v)) :=
    (Option.some.inj hta).symm
  -- move 2: grade domain and opened codomain through the residue,
  -- with the opened context built in place (`CtxOkP.openS`; the
  -- grading it asks for is the residue's own first component)
  have hdomU := hss hC.forallE_ty hty hwu htyA
  have hCop : CtxOkP m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
    CtxOkP.openS (n := n) hC.forallE_ty hC.forallE_body htyA
      (fun ρ hρ => (hdomU ρ hρ).1)
  have hcodU := hss hCop hbt
    (Setlec.ensureSortCore_inv hens) hbaA
  refine ⟨?_, ?_, ?_⟩
  · -- AnnotOkP of the ∀ node itself
    intro ρ hρ
    have hdom := hdomU ρ hρ
    have hcod : ∀ x, x ∈ˢ interp2 V ρ tyA →
        AnnotOkP V (cons x ρ) baA ∧
          interp2 V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
      fun x hx => hcodU (cons x ρ) (Sat2_cons V hρ hx)
    refine ⟨?_, ?_⟩
    · -- AnnotOk2: numerals unread
      rw [AnnotOk2_pi]
      exact ⟨hdom.1.1, fun x hx => (hcod x hx).1.1⟩
    · -- AnnotValidV: hereditary parts + the bit component
      rw [AnnotValidV_pi]
      refine ⟨hdom.1.2, fun x hx => (hcod x hx).1.2, ?_⟩
      -- move 3: establishment, one line
      intro hb x hx
      exact pwBit_zero_mem_univZero hz hb (hcod x hx).2
  · -- the sort's own grading: leaves
    intro ρ hρ
    exact ⟨by simp, by simp⟩
  · -- the membership row, through the numeral bridge
    intro ρ hρ
    have hdom := hdomU ρ hρ
    have hcod : ∀ x, x ∈ˢ interp2 V ρ tyA →
        AnnotOk2 V (cons x ρ) baA ∧
          interp2 V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
      fun x hx =>
        ⟨(hcodU (cons x ρ) (Sat2_cons V hρ hx)).1.1,
          (hcodU (cons x ρ) (Sat2_cons V hρ hx)).2⟩
    -- the row at the true sort numerals
    have hrow := sound_pi V (u := u.eval φ) (v := v.eval φ)
      hdom.1.1 (fun x hx => (hcod x hx).1) hdom.2
      (fun x hx => (hcod x hx).2)
    -- move 4: the numeral bridge (residue 9's successor is a rewrite)
    have hzag : pwBit φ mb.pw = 0 ↔ v.eval φ = 0 :=
      pwBit_of_equiv_zeronessOf hz φ
    have hbridge :
        interp2 V ρ (.pi 0 (pwBit φ mb.pw) tyA baA)
          = interp2 V ρ (.pi (u.eval φ) (v.eval φ) tyA baA) := by
      rw [interp2_pi, interp2_pi]
      exact piR_zero_agree hzag fun x _ => rfl
    rw [hbridge]
    exact hrow.2

/-- **`.lam`, P currency — the chain-case species.**  The λ's fibre
regime fact (`AnnotOk2`'s λ-clause `v = 0` component, and the copied
∀-type's `AnnotValidV` `pi` component — one `have`, both uses, because
the meta is *copied*, `infer_lam_meta_copy`) is established by cases
on the body:

* **leaf** (body not a λ): the P2 leaf conjunct delivers the codomain
  sort run + the validation `equiv`; `SortSemP` grades the inferred
  body type, `pwBit_zero_mem_univZero` reads the bit — the ∀ clause's
  move 3 again.
* **chain** (body a λ): *no run at all.*  The chain conjunct says the
  outer datum is `equiv` the inner λ's; the meta copy says the
  inferred body type is a ∀ carrying the inner meta, so its `denoteP`
  is a `.pi` at the inner bit, and at outer bit `0` the inner bit is
  `0` (`pwBit_eq_of_equiv`) — a `piR 0` is a truth value by
  **impredicativity** (`piR_zero_mem_univZero`).  This is where the
  canonical lane's `LamCodSort2` residue (the per-node sort run the
  #152 chain guard lost) dissolves into the model's own law. -/
theorem infer_lam_claimP (m : EnvS2UM V μ env)
    (hμ : μ.verified = true) (hss : SortSemP m μ φ)
    (ihi : InferClaims2P μ m φ fuel)
    {d : Nat} {n : Name} {ty body t : Expr} {mb : Setlec.BinderMeta}
    {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.lam n ty body mb) = .ok t)
    (hws : Expr.WScoped d (.lam n ty body mb))
    (hb : (Expr.lam n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.lam n ty body mb))
    (hC : CtxOkP m φ d Δa (.lam n ty body mb))
    (hea : denoteP m.acval env φ d (.lam n ty body mb) = some ea)
    (hta : denoteP m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  obtain ⟨tty, u, bt, hty, hwu, hbt, hleafC, hchainC, rfl⟩ :=
    Setlec.inferTypeCore_lam_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading
  rw [denoteP] at hea
  rcases htyA : denoteP m.acval env φ d ty with _ | tyA
  · rw [htyA] at hea; exact nomatch hea
  rw [htyA] at hea
  rcases hba : denoteP m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d n ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .lam (pwBit φ mb.pw) tyA ba :=
    (Option.some.inj hea).symm
  -- the abstraction round trip, for the ∀-type's reading
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 (n := n) hws.1 hb.1 hws.2 hb.2 hLty hLbody
  have hleaf :
      Expr.LeafCond d n ty (body.instantiate1 (.fvar d n ty)) := by
    intro l hl hd
    rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact absurd hd (by
        have := Expr.fvarLeaves_lt_of_wscoped hws.2 l h2
        omega)
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact ⟨rfl, rfl⟩
      · exact absurd hd (by
          have := Expr.fvarLeaves_lt_of_wscoped hws.1 l h3
          omega)
  have hcons : Expr.fvarConsistent d n ty bt :=
    Expr.fvarConsistent_of_leafCond bt (fun l hl =>
      hleaf l (inferTypeCore_fvarLeaves m.base.wf fuel hbt hwopen l hl))
  have hbtb : bt.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.base.wf fuel hbt hwopen hbopen hLopen
  have hround : (bt.abstract1 d).instantiate1 (.fvar d n ty) = bt :=
    abstract1_instantiate1 bt 0 hcons hbtb
  rw [denoteP, htyA, hround] at hta
  rcases hbtA : denoteP m.acval env φ (d + 1) bt with _ | btA
  · rw [hbtA] at hta; exact nomatch hta
  rw [hbtA] at hta
  obtain rfl : ta = .pi 0 (pwBit φ mb.pw) tyA btA :=
    (Option.some.inj hta).symm
  -- the domain and the opened body, graded; the opened context in
  -- place (`CtxOkP.openS` at the residue's own grading)
  have hdomU := hss hC.lam_ty hty hwu htyA
  have hCop : CtxOkP m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
    CtxOkP.openS (n := n) hC.lam_ty hC.lam_body htyA
      (fun ρ hρ => (hdomU ρ hρ).1)
  obtain ⟨hrowE, hrowT, hrowM⟩ :=
    ihi hbt hwopen hbopen hLopen hCop hba hbtA
  -- the fibre regime fact, one `have`, both uses (the meta copy)
  have hCbt : CtxOkP m φ (d + 1) (tyA :: Δa) bt :=
    hCop.of_subset
      (inferTypeCore_fvarLeaves m.base.wf fuel hbt hwopen)
  have hzfib : pwBit φ mb.pw = 0 →
      ∀ (ρ' : Nat → V), Sat2 V (tyA :: Δa) ρ' →
        interp2 V ρ' btA ∈ˢ (univZero : V) := by
    intro hb0 ρ' hρ'
    by_cases hbl : body.isLam
    · -- chain: no run — impredicativity at the copied meta
      obtain ⟨nI, tyI, bI, mbI, rfl⟩ :
          ∃ nI tyI bI mbI, body = .lam nI tyI bI mbI := by
        cases body <;> simp [Expr.isLam] at hbl
        exact ⟨_, _, _, _, rfl⟩
      have hpwEq : Setlec.PropWhen.equiv mb.pw mbI.pw = true :=
        hchainC hμ mbI.pw rfl
      -- the opened body is a λ with the same meta; the inferred type
      -- copies it
      obtain ⟨btI, rfl⟩ : ∃ btI,
          bt = .forallE nI (tyI.instantiate1 (.fvar d n ty)) btI mbI := by
        cases fuel with
        | zero =>
          rw [Setlec.inferTypeCore_zero] at hbt
          simp [throw, throwThe, MonadExceptOf.throw] at hbt
        | succ f =>
          exact Setlec.infer_lam_meta_copy hbt
      obtain ⟨tyIA, btIA, -, -, rfl⟩ := denoteP_forallE_inv hbtA
      rw [interp2_pi]
      have hinner : pwBit φ mbI.pw = 0 := by
        rw [← pwBit_eq_of_equiv hpwEq φ]
        exact hb0
      rw [hinner]
      exact piR_zero_mem_univZero
    · -- leaf: the P2 leaf conjunct's run + the bit law
      obtain ⟨btt, vb, hbtt, hwbtt, hzeq⟩ :=
        hleafC hμ (by simpa using hbl)
      exact pwBit_zero_mem_univZero hzeq hb0
        (hss hCbt hbtt hwbtt hbtA ρ' hρ').2
  refine ⟨?_, ?_, ?_⟩
  · -- AnnotOkP of the λ
    intro ρ hρ
    have hdom := hdomU ρ hρ
    refine ⟨?_, ?_⟩
    · rw [AnnotOk2_lam]
      exact ⟨hdom.1.1,
        fun x hx => (hrowE (cons x ρ) (Sat2_cons V hρ hx)).1,
        fun x => interp2 V (cons x ρ) btA,
        fun x hx => hrowM (cons x ρ) (Sat2_cons V hρ hx),
        fun h0 x hx => hzfib h0 (cons x ρ) (Sat2_cons V hρ hx)⟩
    · rw [AnnotValidV_lam]
      exact ⟨hdom.1.2,
        fun x hx => (hrowE (cons x ρ) (Sat2_cons V hρ hx)).2⟩
  · -- AnnotOkP of the copied ∀-type
    intro ρ hρ
    have hdom := hdomU ρ hρ
    refine ⟨?_, ?_⟩
    · rw [AnnotOk2_pi]
      exact ⟨hdom.1.1,
        fun x hx => (hrowT (cons x ρ) (Sat2_cons V hρ hx)).1⟩
    · rw [AnnotValidV_pi]
      exact ⟨hdom.1.2,
        fun x hx => (hrowT (cons x ρ) (Sat2_cons V hρ hx)).2,
        fun h0 x hx => hzfib h0 (cons x ρ) (Sat2_cons V hρ hx)⟩
  · -- the membership row
    intro ρ hρ
    exact (sound_lam V (hdomU ρ hρ).1.1
      (fun x hx => (hrowE (cons x ρ) (Sat2_cons V hρ hx)).1)
      (fun x hx => hrowM (cons x ρ) (Sat2_cons V hρ hx))
      (fun h0 x hx => hzfib h0 (cons x ρ) (Sat2_cons V hρ hx))).2

end Setlec.SetR.Interp2
