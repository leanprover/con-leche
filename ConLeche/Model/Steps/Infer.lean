module

public import ConLeche.Model.ClaimsIO
public import ConLeche.Model.CtxOkKit
import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Model.Annot.BitInst
public import ConLeche.Model.Annot.ValidSpine
import ConLeche.Verify.InferLemmas
public import ConLeche.Semantics.Frame
import ConLeche.Semantics.Skeleton
public import ConLeche.Semantics.Hoist
public import ConLeche.Semantics.LitStep
import ConLeche.Semantics.LitParams
public section

/-!
# The infer quarter, P currency — the worked ∀ clause (task #161, P3.5)

`infer_forallE_claim` below is the P-tier mirror of
`infer_forallE_claim2D` (`Steps/InferQ.lean`), and it is the **species
example** for the whole infer quarter: every binder clause of the swap
runs the same four moves —

1. the run inversion delivers the P2 validation conjunct
   (`(zeronessOf v) == mb.pw`, at `μ.verifiedChecks`) alongside the sort
   runs — no `sortOfE` cross-fuel gymnastics, the annotation's numeral
   is `pwBit φ mb.pw` *definitionally* (`denoteMeta_forallE_inv`);
2. `SortSemP` (the routed residue, `SortSem2` with `sortOfE` unfolded
   into its two checker runs and the currency upgraded) grades domain
   and opened codomain;
3. **establishment**: `AnnotValid`'s `pi` component is
   `pwBit_zero_mem_univZero` at the conjunct + the codomain's sort
   membership — one line;
4. **the numeral bridge**: the row (`sound_pi`) speaks at the true
   sort numerals; `piR_zero_agree` carries it to the stored bit, with
   `pwBit_zeronessOf` supplying the zero-agreement — this is
   where residue 9's sort-agreement machinery used to live, and it is
   now a rewrite.

**Mode pinning.**  The claims (`Claims`) quantify `μ`, but the
*step proofs* hold at `μ.verifiedChecks = true` only: the validation
conjuncts are conditional on the mode, and at `.trusted` a stored bit
is unvalidated.  The P-tier assembly (and the capstone) is a
verified-mode statement — which is the design: the annotated checker's
consistency proof covers the mode that validates.

The opened contexts are built in place by `CtxOk.openS` (batch 2),
at the grading the clause's own residue supplies — the D-tier's
self-propagation argument, inherited.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level whnf inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- **The sort fact, at the induction's own fuel** (`SortSem2`'s
successor).  The canonical lane ROUTES `SortSem2` — "the top-level
induction is where it becomes available", and in-tree it never does:
the annotation fuel made its runs off-induction, and it stands among
`Capstone2E`'s fifteen.  In the P tier the annotation fuel is gone,
every use in the quarter is at the induction-bounded checker fuel,
and `sortSemAt_of_claims` *derives* the fact from the claims one
level down — another canonical-frontier residue dissolved.  The
subject's scoping package is carried so the claims can be applied. -/
@[expose] def SortSemAt {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {u : Level} {Δa : List AnnotTerm}
    {ea : AnnotTerm},
    CtxOk m φ d Δa e →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    inferTypeCore μ env fuel d e = .ok t →
    whnf μ env fuel d t = .ok (.sort u) →
    denoteMeta m.acval env φ d e = some ea →
    ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V)

/-- `SortSemAt` at the knot's io slot (task #172 B4): the premise
form — the subject's `WellDenotedV` is consumed, because at the gated mode
the slot's run establishes nothing.  Derived from the two lanes'
(`sortSemAtIOS_of`, `InferIOP.lean`). -/
@[expose] def SortSemAtIOS {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {u : Level} {Δa : List AnnotTerm}
    {ea : AnnotTerm},
    CtxOk m φ d Δa e →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ConLeche.inferTypeIO μ env fuel d e = .ok t →
    whnf μ env fuel d t = .ok (.sort u) →
    denoteMeta m.acval env φ d e = some ea →
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
    ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V)

/-- `denoteMeta` at a sort (the `denote2_sortQ` mirror). -/
theorem denoteMeta_sortQ {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {u : Level} :
    denoteMeta acval env φ d (.sort u) = some (.sort (u.eval φ)) := by
  rw [denoteMeta]

/-- **The leaf-validity residue** (the P tier's one new routed
obligation): every stored leaf of the annotated valuation is
bit-valid.  The `WellDenoted` half is already an `EnvModelU` field
(`acval_wellDenoted`); this is its `AnnotValid` companion, to be discharged
at the install tier — a stored type's annotations went through the
checker's own front door, which is establishment — and folded into the
environment structure there (with the owed `EnvWF` records, if the
seal's invariants state them naturally). -/
@[expose] def AcvalValid {env : Env} (m : EnvModel V env) : Prop :=
  ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotValid V ρ (m.acval n ψ)

/-- **The `const` clause's residue, P currency** (`ConstType2C`
transposed: no fuel, `WellDenotedV` conclusion). -/
@[expose] def ConstType {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (n : Name) (ci : ConLeche.ConstantInfo) (us : List Level),
    env.find? n = some ci → ci.isTowerEntry = false →
    us.length = ci.toConstantVal.levelParams.length →
    ∃ ta,
      denoteMeta m.acval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp V ρ (m.acval n
            (Level.substFn φ ci.toConstantVal.levelParams us))
          ∈ˢ interp V ρ ta

/-- `.const`, P currency: the residue answers with the type's row; the
subject's grading is the two leaf facts (`acval_wellDenoted` + the routed
`AcvalValid`). -/
theorem infer_const_claim (m : EnvModel V env)
    (hct : ConstType m φ) (hval : AcvalValid m)
    {d : Nat} {n : Name} {us : List Level} {t : Expr}
    {Δa : List AnnotTerm} {ea ta : AnnotTerm}
    (h : inferTypeCore μ env (fuel + 1) d (.const n us) = .ok t)
    (hea : denoteMeta m.acval env φ d (.const n us) = some ea)
    (hta : denoteMeta m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea ∈ˢ interp V ρ ta := by
  rw [ConLeche.inferTypeCore_succ] at h
  simp only [ConLeche.inferBody, pure,
    Except.pure, Bind.bind, Except.bind] at h
  cases hf : env.find? n with
  | none =>
    rw [hf] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    rw [hf] at h
    dsimp only at h
    split at h
    · next htw =>
      split at h
      · next hlen =>
        simp only [Except.ok.injEq] at h
        subst h
        rw [denoteMeta, hf] at hea
        dsimp only at hea
        rw [if_pos hlen] at hea
        obtain rfl : ea = m.acval n
            (Level.substFn φ ci.toConstantVal.levelParams us) :=
          (Option.some.inj hea).symm
        obtain ⟨ta', hta', hok, hmem⟩ := hct d n ci us hf (by simpa using htw) hlen
        rw [hta'] at hta
        obtain rfl : ta = ta' := (Option.some.inj hta).symm
        exact ⟨fun ρ _ => ⟨m.acval_wellDenoted n _ ρ, hval n _ ρ⟩,
          fun ρ _ => hok ρ, fun ρ _ => hmem ρ⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `.sort`, P currency: both readings are sort nodes, gradings are
vacuous, the row is `sound_sort`. -/
theorem infer_sort_claim (m : EnvModel V env) {d : Nat} {u : Level}
    {t : Expr} {Δa : List AnnotTerm} {ea ta : AnnotTerm}
    (h : inferTypeCore μ env (fuel + 1) d (.sort u) = .ok t)
    (hea : denoteMeta m.acval env φ d (.sort u) = some ea)
    (hta : denoteMeta m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea ∈ˢ interp V ρ ta := by
  rw [ConLeche.inferTypeCore_succ] at h
  simp only [ConLeche.inferBody, pure,
    Except.pure, Except.ok.injEq] at h
  subst h
  rw [denoteMeta_sortQ] at hea hta
  obtain rfl : ea = .sort (u.eval φ) := (Option.some.inj hea).symm
  obtain rfl : ta = .sort (Level.eval φ (.succ u)) :=
    (Option.some.inj hta).symm
  refine ⟨fun _ _ => ⟨by simp, by simp⟩,
    fun _ _ => ⟨by simp, by simp⟩, ?_⟩
  intro ρ _
  exact (sound_sort V ρ (u.eval φ)).2

/-- `.bvar`, P currency: outside the fragment, the checker throws. -/
theorem infer_bvar_claim (m : EnvModel V env) {d i : Nat} {t : Expr}
    {Δa : List AnnotTerm} {ea ta : AnnotTerm}
    (h : inferTypeCore μ env (fuel + 1) d (.bvar i) = .ok t)
    (_hea : denoteMeta m.acval env φ d (.bvar i) = some ea)
    (_hta : denoteMeta m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea ∈ˢ interp V ρ ta := by
  rw [ConLeche.inferTypeCore_succ] at h
  simp only [ConLeche.inferBody] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `.fvar`, P currency: the leaf package of `CtxOk` carries the
fourth conjunct at `WellDenotedV`, so the clause takes no residue —
`infer_fvar_claim2D`'s improvement inherited by construction. -/
theorem infer_fvar_claim (m : EnvModel V env)
    {d idx : Nat} {ty t : Expr} {Δa : List AnnotTerm}
    {ea ta : AnnotTerm}
    (hC : CtxOk m φ d Δa (.fvar idx ty))
    (h : inferTypeCore μ env (fuel + 1) d (.fvar idx ty) = .ok t)
    (hea : denoteMeta m.acval env φ d (.fvar idx ty) = some ea)
    (hta : denoteMeta m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨-, -, tya, Aa, hden, hi, hlink, hokP⟩ := CtxOk.fvar_leaf hC
  rw [denoteMeta] at hea
  obtain rfl : ea = .bvar (d - 1 - idx) := (Option.some.inj hea).symm
  rw [ConLeche.inferTypeCore_succ] at h
  simp only [ConLeche.inferBody, pure,
    Except.pure] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    rw [hden] at hta
    obtain rfl : ta = tya := (Option.some.inj hta).symm
    refine ⟨fun _ _ => ⟨by simp, by simp⟩, hokP, ?_⟩
    intro ρ hρ
    rw [interp_bvar, hlink ρ hρ]
    exact hρ (d - 1 - idx) Aa hi
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **`.forallE`, P currency** — see the module docstring; the four
moves annotated inline. -/
theorem infer_forallE_claim (m : EnvModel V env)
    (hμ : μ.verifiedChecks = true) (hss : SortSemAt m μ φ fuel)
    {d : Nat} {ty body t : Expr} {mb : ConLeche.BinderMeta}
    {Δa : List AnnotTerm} {ea ta : AnnotTerm}
    (h : inferTypeCore μ env (fuel + 1) d (.forallE ty body mb)
      = .ok t)
    (hws : Expr.WScoped d (.forallE ty body mb))
    (hb : (Expr.forallE ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.forallE ty body mb))
    (hC : CtxOk m φ d Δa (.forallE ty body mb))
    (hea : denoteMeta m.acval env φ d (.forallE ty body mb) = some ea)
    (hta : denoteMeta m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea ∈ˢ interp V ρ ta := by
  -- move 1: the run inversion, validation conjunct included
  obtain ⟨tty, u, bt, v, hty, hwu, hbt, hens, hpw, rfl⟩ :=
    ConLeche.inferTypeCore_forall_inv h
  have hz := hpw hμ
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
  obtain ⟨tyA, baA, htyA, hbaA, rfl⟩ := denoteMeta_forallE_inv hea
  rw [denoteMeta_sortQ] at hta
  obtain rfl : ta = .sort (Level.eval φ (.imax u v)) :=
    (Option.some.inj hta).symm
  -- move 2: grade domain and opened codomain through the derived
  -- sort fact, with the opened context built in place
  have hdomU := hss hC.forallE_ty hws.1 hb.1 hLty hty hwu htyA
  have hCop : CtxOk m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
    CtxOk.openS hC.forallE_ty hC.forallE_body htyA
      (fun ρ hρ => (hdomU ρ hρ).1)
  have hcodU := hss hCop hwopen hbopen hLopen hbt
    (ConLeche.ensureSortCore_inv hens) hbaA
  refine ⟨?_, ?_, ?_⟩
  · -- WellDenotedV of the ∀ node itself
    intro ρ hρ
    have hdom := hdomU ρ hρ
    have hcod : ∀ x, x ∈ˢ interp V ρ tyA →
        WellDenotedV V (cons x ρ) baA ∧
          interp V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
      fun x hx => hcodU (cons x ρ) (Sat_cons V hρ hx)
    refine ⟨?_, ?_⟩
    · -- WellDenoted: numerals unread
      rw [WellDenoted_pi]
      exact ⟨hdom.1.1, fun x hx => (hcod x hx).1.1⟩
    · -- AnnotValid: hereditary parts + the bit component
      rw [AnnotValid_pi]
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
    have hcod : ∀ x, x ∈ˢ interp V ρ tyA →
        WellDenoted V (cons x ρ) baA ∧
          interp V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
      fun x hx =>
        ⟨(hcodU (cons x ρ) (Sat_cons V hρ hx)).1.1,
          (hcodU (cons x ρ) (Sat_cons V hρ hx)).2⟩
    -- the row at the true sort numerals
    have hrow := sound_pi V (u := u.eval φ) (v := v.eval φ)
      hdom.1.1 (fun x hx => (hcod x hx).1) hdom.2
      (fun x hx => (hcod x hx).2)
    -- move 4: the numeral bridge (residue 9's successor is a rewrite)
    have hzag : pwBit φ mb.pw = 0 ↔ v.eval φ = 0 := by
      rw [← hz]; exact pwBit_zeronessOf φ v
    have hbridge :
        interp V ρ (.pi 0 (pwBit φ mb.pw) tyA baA)
          = interp V ρ (.pi (u.eval φ) (v.eval φ) tyA baA) := by
      rw [interp_pi, interp_pi]
      exact piR_zero_agree hzag fun x _ => rfl
    rw [hbridge]
    exact hrow.2

/-- **`.lam`, P currency — the chain-case species.**  The λ's fibre
regime fact (`WellDenoted`'s λ-clause `v = 0` component, and the copied
∀-type's `AnnotValid` `pi` component — one `have`, both uses, because
the meta is *copied*, `infer_lam_meta_copy`) is established by cases
on the body:

* **leaf** (body not a λ): the P2 leaf conjunct delivers the codomain
  sort run + the validation `zeronessOf v = mb.pw`; `SortSemP` grades the inferred
  body type, `pwBit_zero_mem_univZero` reads the bit — the ∀ clause's
  move 3 again.
* **chain** (body a λ): *no run at all.*  The chain conjunct says the
  outer datum *is* the inner λ's; the meta copy says the
  inferred body type is a ∀ carrying the inner meta, so its `denoteMeta`
  is a `.pi` at the inner bit, and at outer bit `0` the inner bit is
  `0` (a rewrite) — a `piR 0` is a truth value by
  **impredicativity** (`piR_zero_mem_univZero`).  This is where the
  canonical lane's `LamCodSort2` residue (the per-node sort run the
  #152 chain guard lost) dissolves into the model's own law. -/
theorem infer_lam_claim (m : EnvModel V env)
    (hμ : μ.verifiedChecks = true) (hss : SortSemAt m μ φ fuel)
    (hsss : SortSemAtIOS m μ φ fuel)
    (ihi : InferClaim μ m φ fuel)
    {d : Nat} {ty body t : Expr} {mb : ConLeche.BinderMeta}
    {Δa : List AnnotTerm} {ea ta : AnnotTerm}
    (h : inferTypeCore μ env (fuel + 1) d (.lam ty body mb) = .ok t)
    (hws : Expr.WScoped d (.lam ty body mb))
    (hb : (Expr.lam ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.lam ty body mb))
    (hC : CtxOk m φ d Δa (.lam ty body mb))
    (hea : denoteMeta m.acval env φ d (.lam ty body mb) = some ea)
    (hta : denoteMeta m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨tty, u, bt, hty, hwu, hbt, hleafC, hchainC, rfl⟩ :=
    ConLeche.inferTypeCore_lam_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading
  rw [denoteMeta] at hea
  rcases htyA : denoteMeta m.acval env φ d ty with _ | tyA
  · rw [htyA] at hea; exact nomatch hea
  rw [htyA] at hea
  rcases hba : denoteMeta m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .lam (pwBit φ mb.pw) tyA ba :=
    (Option.some.inj hea).symm
  -- the abstraction round trip, for the ∀-type's reading
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
  have hleaf :
      Expr.LeafCond d ty (body.instantiate1 (.fvar d ty)) := by
    intro l hl hd
    rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact absurd hd (by
        have := Expr.fvarLeaves_lt_of_wscoped hws.2 l h2
        omega)
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact rfl
      · exact absurd hd (by
          have := Expr.fvarLeaves_lt_of_wscoped hws.1 l h3
          omega)
  have hcons : Expr.fvarConsistent d ty bt :=
    Expr.fvarConsistent_of_leafCond bt (fun l hl =>
      hleaf l (inferTypeCore_fvarLeaves m.wf fuel hbt hwopen l hl))
  have hbtb : bt.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel hbt hwopen hbopen hLopen
  have hround : (bt.abstract1 d).instantiate1 (.fvar d ty) = bt :=
    abstract1_instantiate1 bt 0 hcons hbtb
  rw [denoteMeta, htyA, hround] at hta
  rcases hbtA : denoteMeta m.acval env φ (d + 1) bt with _ | btA
  · rw [hbtA] at hta; exact nomatch hta
  rw [hbtA] at hta
  obtain rfl : ta = .pi 0 (pwBit φ mb.pw) tyA btA :=
    (Option.some.inj hta).symm
  -- the domain and the opened body, graded; the opened context in
  -- place (`CtxOk.openS` at the residue's own grading)
  have hdomU := hss hC.lam_ty hws.1 hb.1 hLty hty hwu htyA
  have hCop : CtxOk m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
    CtxOk.openS hC.lam_ty hC.lam_body htyA
      (fun ρ hρ => (hdomU ρ hρ).1)
  obtain ⟨hrowE, hrowT, hrowM⟩ :=
    ihi hbt hwopen hbopen hLopen hCop hba hbtA
  -- the fibre regime fact, one `have`, both uses (the meta copy)
  have hCbt : CtxOk m φ (d + 1) (tyA :: Δa) bt :=
    hCop.of_subset
      (inferTypeCore_fvarLeaves m.wf fuel hbt hwopen)
  have hzfib : pwBit φ mb.pw = 0 →
      ∀ (ρ' : Nat → V), Sat V (tyA :: Δa) ρ' →
        interp V ρ' btA ∈ˢ (univZero : V) := by
    intro hb0 ρ' hρ'
    by_cases hbl : body.isLam
    · -- chain: no run — impredicativity at the copied meta
      obtain ⟨tyI, bI, mbI, rfl⟩ :
          ∃ tyI bI mbI, body = .lam tyI bI mbI := by
        cases body <;> simp [Expr.isLam] at hbl
        exact ⟨_, _, _, rfl⟩
      have hpwEq : mb.pw = mbI.pw :=
        hchainC hμ mbI.pw rfl
      -- the opened body is a λ with the same meta; the inferred type
      -- copies it
      obtain ⟨btI, rfl⟩ : ∃ btI,
          bt = .forallE (tyI.instantiate1 (.fvar d ty)) btI mbI := by
        cases fuel with
        | zero =>
          rw [ConLeche.inferTypeCore_zero] at hbt
          simp [throw, throwThe, MonadExceptOf.throw] at hbt
        | succ f =>
          exact ConLeche.infer_lam_meta_copy hbt
      obtain ⟨tyIA, btIA, -, -, rfl⟩ := denoteMeta_forallE_inv hbtA
      rw [interp_pi]
      have hinner : pwBit φ mbI.pw = 0 := by
        rw [← hpwEq]
        exact hb0
      rw [hinner]
      exact piR_zero_mem_univZero
    · -- leaf: the P2 leaf conjunct's run + the bit law
      obtain ⟨btt, vb, hbtt, hwbtt, hzeq⟩ :=
        hleafC hμ (by simpa using hbl)
      exact pwBit_zero_mem_univZero hzeq hb0
        (hsss hCbt (inferTypeCore_WScoped m.wf fuel hbt hwopen)
          hbtb
          (fun l hl => hLopen l
            (inferTypeCore_fvarLeaves m.wf fuel hbt hwopen l hl))
          hbtt hwbtt hbtA hrowT ρ' hρ').2
  refine ⟨?_, ?_, ?_⟩
  · -- WellDenotedV of the λ
    intro ρ hρ
    have hdom := hdomU ρ hρ
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_lam]
      exact ⟨hdom.1.1,
        fun x hx => (hrowE (cons x ρ) (Sat_cons V hρ hx)).1,
        fun x => interp V (cons x ρ) btA,
        fun x hx => hrowM (cons x ρ) (Sat_cons V hρ hx),
        fun h0 x hx => hzfib h0 (cons x ρ) (Sat_cons V hρ hx)⟩
    · rw [AnnotValid_lam]
      exact ⟨hdom.1.2,
        fun x hx => (hrowE (cons x ρ) (Sat_cons V hρ hx)).2⟩
  · -- WellDenotedV of the copied ∀-type
    intro ρ hρ
    have hdom := hdomU ρ hρ
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_pi]
      exact ⟨hdom.1.1,
        fun x hx => (hrowT (cons x ρ) (Sat_cons V hρ hx)).1⟩
    · rw [AnnotValid_pi]
      exact ⟨hdom.1.2,
        fun x hx => (hrowT (cons x ρ) (Sat_cons V hρ hx)).2,
        fun h0 x hx => hzfib h0 (cons x ρ) (Sat_cons V hρ hx)⟩
  · -- the membership row
    intro ρ hρ
    exact (sound_lam V (hdomU ρ hρ).1.1
      (fun x hx => (hrowE (cons x ρ) (Sat_cons V hρ hx)).1)
      (fun x hx => hrowM (cons x ρ) (Sat_cons V hρ hx))
      (fun h0 x hx => hzfib h0 (cons x ρ) (Sat_cons V hρ hx))).2

/-! ## The numeral clause (task #161, P3 batch 3, T1)

`NatHeads2` is **denote-free** — it speaks only of `interp` at the
valuation's own `Nat` leaves — so the P tier consumes it with the
identical body, transposed only in its carrier (`NatHeads`, below:
batch 8's carrier sweep moved the P surface to `EnvModel`, and the
mode-indexed `EnvModelUM` the canonical statement binds is not what the
P fold can supply).  What the currency swap costs is one extra
grading per spine: `natLit_factsAV` produces the `WellDenoted` half of
the numeral's truthfulness (and the membership row) exactly as in the
canonical lane, and `AnnotValid_natLitAV` (batch 2) produces the
`AnnotValid` half from the two head leaves' bit validity — which is
the routed `AcvalValid`, the same residue `infer_const_claim`
takes. -/

/-- **The `Nat`-literal clause's residue, over the core**
(`Steps/InferQ.lean`'s `NatHeads2`, body for body): the zero's
membership and the successor's, at the annotated valuation's own
`Nat` leaf. -/
@[expose] def NatHeads {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) : Prop :=
  ConLeche.natLitSupported env = true →
  ∀ ρ : Nat → V,
    interp V ρ (m.acval natZeroName (Level.substFn φ [] []))
      ∈ˢ interp V ρ (m.acval natName (Level.substFn φ [] [])) ∧
    interp V ρ (m.acval natSuccName (Level.substFn φ [] []))
      ∈ˢ piR 1 (interp V ρ (m.acval natName (Level.substFn φ [] [])))
        (fun _ => interp V ρ
          (m.acval natName (Level.substFn φ [] [])))

/-- **`.lit (.natVal k)`, P currency.**  Dual success: the returned
type is `.const natName []`, whose reading the support guard pins to
the `Nat` leaf itself (`natName_levelParams_nil`), so identifying `ta`
with that leaf is the `denoteMeta` `const` clause and nothing more. -/
theorem infer_natLit_claim (m : EnvModel V env) (hnh : NatHeads m φ)
    (hval : AcvalValid m)
    {d k : Nat} {t : Expr} {Δa : List AnnotTerm} {ea ta : AnnotTerm}
    (h : inferTypeCore μ env (fuel + 1) d (.lit (.natVal k)) = .ok t)
    (hea : denoteMeta m.acval env φ d (.lit (.natVal k)) = some ea)
    (hta : denoteMeta m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea ∈ˢ interp V ρ ta := by
  rw [ConLeche.inferTypeCore_succ] at h
  simp only [ConLeche.inferBody, pure,
    Except.pure] at h
  split at h
  · next hg =>
    simp only [Except.ok.injEq] at h
    subst h
    have hgt : ConLeche.natLitSupported env = true := by simpa using hg
    rw [denoteMeta, if_pos hgt] at hea
    obtain rfl : ea = natLitAV
        (m.acval natZeroName (Level.substFn φ [] []))
        (m.acval natSuccName (Level.substFn φ [] [])) k :=
      (Option.some.inj hea).symm
    cases hf : env.find? natName with
    | none =>
      simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgt
      obtain ⟨⟨h1, -⟩, -⟩ := hgt
      rw [hf] at h1
      exact nomatch h1
    | some ci =>
      have hlp : ci.toConstantVal.levelParams = [] :=
        natName_levelParams_nil hgt hf
      rw [denoteMeta, hf] at hta
      dsimp only at hta
      rw [if_pos (by simp [hlp]), hlp] at hta
      obtain rfl : ta = m.acval natName (Level.substFn φ [] []) :=
        (Option.some.inj hta).symm
      have hrow : ∀ ρ : Nat → V,
          WellDenoted V ρ (natLitAV
              (m.acval natZeroName (Level.substFn φ [] []))
              (m.acval natSuccName (Level.substFn φ [] [])) k) ∧
            interp V ρ (natLitAV
                (m.acval natZeroName (Level.substFn φ [] []))
                (m.acval natSuccName (Level.substFn φ [] [])) k)
              ∈ˢ interp V ρ
                (m.acval natName (Level.substFn φ [] [])) :=
        fun ρ => natLit_factsAV (m.acval_wellDenoted _ _ ρ) (m.acval_wellDenoted _ _ ρ)
          (hnh hgt ρ).1 (hnh hgt ρ).2 k
      exact ⟨fun ρ _ => ⟨(hrow ρ).1,
          AnnotValid_natLitAV (hval _ _ ρ) (hval _ _ ρ) k⟩,
        fun ρ _ => ⟨m.acval_wellDenoted _ _ ρ, hval _ _ ρ⟩,
        fun ρ _ => (hrow ρ).2⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The two clause-granular residues (T2)

`InferStrLitStep2C` and `InferProjStep2C` transposed: the annotation
fuel `F` and the `∃ F' ≥ F` slack vanish with `denoteAnnot`, the reading
is `denoteMeta`, both readings sit in **premises** (dual success), and
the three rows are stated at `WellDenotedV`.  Their discharges belong to
later tiers exactly as the canonical ones do — the `String` clause is
`strLit_facts`' volume plus seven head facts, the projection clause
is the structure-type walk. -/

/-- The `String`-literal clause, P currency. -/
@[expose] def InferStrLitStep {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {s : String} {t : Expr} {Δa : List AnnotTerm}
    {ea ta : AnnotTerm},
    inferTypeCore μ env (fuel + 1) d (.lit (.strVal s)) = .ok t →
    denoteMeta m.acval env φ d (.lit (.strVal s)) = some ea →
    denoteMeta m.acval env φ d t = some ta →
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea ∈ˢ interp V ρ ta

/-- The projection clause, P currency. -/
@[expose] def InferProjStep {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d i : Nat} {sn : Name} {pe t : Expr} {Δa : List AnnotTerm}
    {ea ta : AnnotTerm},
    inferTypeCore μ env (fuel + 1) d (.proj sn i pe) = .ok t →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    CtxOk m φ d Δa (.proj sn i pe) →
    denoteMeta m.acval env φ d (.proj sn i pe) = some ea →
    denoteMeta m.acval env φ d t = some ta →
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea ∈ˢ interp V ρ ta

/-! ## The threading clauses (T3, T4) and what dual success costs them

### `hainst` is **discharged, not routed**

`denoteMeta_substFvarAt`/`denoteMeta_beta` (batch 2) take two leaf premises.
`hacl` is the structure field `acval_closed`; `hainst` — the stronger
`inst`-invariance at every cut — is *derivable* from the same single
closedness fact the module docstring of `Annot/BitInst.lean` predicts:
`AnnotTerm.inst_eq_self` wants `Term.bvarsBelow k (acval n ψ).erase`,
the erasure link `acval_erase` turns that into
`Term.bvarsBelow k (base.cval n ψ)`, and `EnvS.cval_closed` is
`bvarsBelow 0` of exactly that, which `bvarsBelow.mono` weakens.  So
the P tier pays **no** new environment field for the β/ζ crossing.

### FINDING — dual success charges the threading clauses a *totality*
residue

`InferClaim` puts **both** readings in premises.  A threading
clause that recurses therefore has to *supply* the recursive call's
type-side reading, and for the sub-runs the clause makes that reading
is nowhere in its hypotheses:

* `.app` needs the head's inferred type `tf` (for `ihi` at `f` and
  then `ihw`), the whnf'd `∀`-type's own reading (for `ihw`'s
  conclusion and for the domain `Aa`, which does not occur in the
  returned type at all), and the argument's inferred type `tya` (for
  `ihd`).

Neither is a gap in the *mathematics* — `denoteMeta` fails only on an
unfindable/mis-arity constant, an unsupported literal guard, a
projection index `≥ 2` or a loose `bvar`, and the checker's own
outputs have none of those on a well-formed environment.  It is
exactly the "success premises may later be dischargeable outright"
upgrade path `Claims.lean`'s docstring names, and until that lands
it is a **routed residue**, in the same currency and at the same fuel
as the claims it feeds.  One producer, so one residue (task #241
removed the second: the `.letE` clause, whose value-side reading had
the same shape, is gone with the constructor). -/

/-! ## The leaf side condition the inference residue carries

`LeafReads` was born in `Steps/Reads.lean` (batch 6) as the walk's
own hypothesis; batch 8 moved it here, because `InferReads` — stated
below — now carries it as a premise. -/

/-- **Every `fvar` leaf annotation of the subject reads.**  A strict
weakening of `CtxOk`: its per-leaf package's third component is
literally this existential, so `of_ctxOk` is a projection.

This is the side condition batch 6's FINDING identified as missing
from `InferReads` — without it that residue is REFUTABLE, since
`inferBody`'s `.fvar` clause returns the leaf's stored annotation and
`denoteMeta`'s `fvar` clause never looks at it (witness: `.fvar 0
(.const c [])` at `d = 1` with `c ∉ env`).  Batch 8 repaired the
statement by adding this premise, so nothing is routed: every consumer
holds a `CtxOk` and discharges it by `of_ctxOk`, and the walk
(`Steps/Reads.lean`) propagates it through the binder clauses
(`weakenTop`/`openS` below). -/
@[expose] def LeafReads {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, ∃ tya, denoteMeta m.acval env φ d l.2 = some tya

namespace LeafReads

variable {m : EnvModel V env}

/-- **The consumers' discharge**: `CtxOk`'s leaf package contains the
reading, so any clause holding a context correspondence holds this. -/
theorem of_ctxOk {d : Nat} {Δa : List AnnotTerm} {e : Expr}
    (hC : CtxOk m φ d Δa e) : LeafReads m φ d e := by
  intro l hl
  obtain ⟨-, -, tya, -, hden, -⟩ := hC.2 l hl
  exact ⟨tya, hden⟩

/-- Transport along a leaf-closure inclusion — the shape every clause
uses to reach a subterm (`CtxOk.of_subset`'s mirror). -/
theorem of_subset {d : Nat} {e e' : Expr} (h : LeafReads m φ d e)
    (hs : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    LeafReads m φ d e' :=
  fun l hl => h l (hs l hl)

/-- **One more binder.**  `denoteMeta_weaken_top` is an equality, so a
leaf that reads at `d` reads at `d + 1` (at the lifted annotation);
`CtxOk.weakenTop`'s first conjunct with everything semantic
dropped. -/
theorem weakenTop {d : Nat} {e : Expr} (hw : Expr.WScoped d e)
    (h : LeafReads m φ d e) : LeafReads m φ (d + 1) e := by
  intro l hl
  obtain ⟨hlt, hwl⟩ := ConLeche.Expr.WScoped_leaves e hw l hl
  obtain ⟨tya, hden⟩ := h l hl
  refine ⟨tya.liftN 1 0, ?_⟩
  rw [denoteMeta_weaken_top m.acval_closed (hwl.mono (by omega)), hden]
  rfl

/-- **Opening a binder**, `CtxOk.openS`'s shape: the body's own leaves
weaken, and the *new* leaf `(d, n, ty)` reads because the binder's
domain does (`hty`, which every clause has from the subject's own
reading). -/
theorem openS {d : Nat} {ty body : Expr} {ta : AnnotTerm}
    (hwt : Expr.WScoped d ty) (hwb : Expr.WScoped d body)
    (ht : LeafReads m φ d ty) (hbd : LeafReads m φ d body)
    (hty : denoteMeta m.acval env φ d ty = some ta) :
    LeafReads m φ (d + 1) (body.instantiate1 (.fvar d ty)) := by
  intro l hl
  rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · exact weakenTop hwb hbd l hl'
  · rw [ConLeche.Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · refine ⟨ta.liftN 1 0, ?_⟩
      rw [denoteMeta_weaken_top m.acval_closed hwt, hty]
      rfl
    · exact weakenTop hwt ht l hl''

end LeafReads

/-- **The inferred type reads** (P-tier totality residue; see the
FINDING above).  Conditioned exactly as the claims are: the run, the
subject's scoping package, the subject's leaf side condition, and the
subject's own reading.

The `LeafReads` premise is batch 8's repair of batch 6's FINDING:
without it the residue is *refutable* (the `.fvar` clause returns the
leaf's stored annotation, which the subject's reading never mentions).
It costs its consumers nothing — every one of them holds a `CtxOk` at
the same depth, and `LeafReads.of_ctxOk` is a projection. -/
@[expose] def InferReads {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {ea : AnnotTerm},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    LeafReads m φ d e →
    denoteMeta m.acval env φ d e = some ea →
    ∃ ta, denoteMeta m.acval env φ d t = some ta

/-- `InferReads` at the knot's io slot (task #172 B4); derived from
the two lanes' (`inferReadsIOS_of`, `InferIOP.lean`). -/
@[expose] def InferReadsIOS {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {ea : AnnotTerm},
    ConLeche.inferTypeIO μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    LeafReads m φ d e →
    denoteMeta m.acval env φ d e = some ea →
    ∃ ta, denoteMeta m.acval env φ d t = some ta

/-- **The head normal form reads** (P-tier totality residue, the
reduction producer). -/
@[expose] def WhnfReads {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {ea : AnnotTerm},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    LeafReads m φ d e →
    denoteMeta m.acval env φ d e = some ea →
    ∃ ea', denoteMeta m.acval env φ d e' = some ea'

/-- **`SortSem2`'s discharge** (impossible in the canonical lane): the
sort fact at `fuel` from the claims at `fuel` plus the one totality
factor — infer the type (`hreads` says it reads), grade both readings
(`ihi`), then walk the type to its sort (`ihw`) and the membership
lands in the universe. -/
theorem sortSemAt_of_claims {env : Env} {m : EnvModel V env}
    {fuel : Nat}
    (ihw : WhnfClaim μ m φ fuel) (ihi : InferClaim μ m φ fuel)
    (hreads : InferReads m μ φ fuel) :
    SortSemAt m μ φ fuel := by
  intro d e t u Δa ea hC hws hb hLb hi hw hea
  obtain ⟨ta, hta⟩ :=
    hreads hi hws hb hLb (LeafReads.of_ctxOk hC) hea
  obtain ⟨hokE, hokT, hmem⟩ := ihi hi hws hb hLb hC hea hta
  have hwt : Expr.WScoped d t :=
    inferTypeCore_WScoped m.wf fuel hi hws
  have hbt : t.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel hi hws hb hLb
  have hLt : Expr.LeavesBounded t := fun l hl =>
    hLb l (inferTypeCore_fvarLeaves m.wf fuel hi hws l hl)
  have hCt : CtxOk m φ d Δa t :=
    hC.of_subset (inferTypeCore_fvarLeaves m.wf fuel hi hws)
  obtain ⟨-, heq⟩ := ihw hw hwt hbt hLt hCt hta denoteMeta_sortQ hokT
  intro ρ hρ
  refine ⟨hokE ρ hρ, ?_⟩
  have hm := hmem ρ hρ
  rw [heq ρ hρ, interp_sort] at hm
  exact hm

/-- **`.app`, P currency — the quarter's hardest clause.**  Three
things replace canonical machinery:

1. **the returned type's reading is *derived*, not produced.**  The
   canonical clause routes `BetaCross2C` to build `denoteAnnot` of
   `body'.instantiate1 a`; here `hta` *gives* that reading and
   `denoteMeta_beta` runs backwards, identifying `ta` with `Ba.inst aa`
   — one equation, no ledger, no fuel slack;
2. **the app slot's kind-`0` component is read off the ∀-type's own
   annotation.**  The canonical clause re-runs `SortSem2` at the
   codomain to learn `v' = 0 → fibres ∈ univZero`; in the validated
   reading the whnf'd function type is `.pi 0 (pwBit φ mb'.pw) Aa Ba`
   and that implication *is* `AnnotValid`'s `pi` component, which
   `ihw` hands over as part of its conclusion.  So the clause takes
   **no `SortSemP`**;
3. the grading transport across the substitution is `WellDenotedV_inst0`.

The three readings the recursive calls need on the type side
(`tf`, the whnf'd ∀, `tya`) are the routed totality residues — see the
FINDING above. -/
theorem infer_app_claim (m : EnvModel V env)
    (hir : InferReads m μ φ fuel) (hwr : WhnfReads m μ φ fuel)
    (ihw : WhnfClaim μ m φ fuel) (ihd : DefEqClaim μ m φ fuel)
    (ihi : InferClaim μ m φ fuel)
    {d : Nat} {f a t : Expr} {Δa : List AnnotTerm} {ea ta : AnnotTerm}
    (h : inferTypeCore μ env (fuel + 1) d (.app f a) = .ok t)
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOk m φ d Δa (.app f a))
    (hea : denoteMeta m.acval env φ d (.app f a) = some ea)
    (hta : denoteMeta m.acval env φ d t = some ta) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨tf, ty', body', mb', htf, hwf, rfl, tya, hia, hde⟩ :=
    ConLeche.inferTypeCore_app_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading
  rw [denoteMeta] at hea
  rcases hfa : denoteMeta m.acval env φ d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denoteMeta m.acval env φ d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  -- the head, and its inferred type's frame
  obtain ⟨tfa, htfa⟩ :=
    hir htf hws.1 hb.1 hLf (LeafReads.of_ctxOk hC.app_fn) hfa
  obtain ⟨hrowfE, hrowfT, hrowfM⟩ :=
    ihi htf hws.1 hb.1 hLf hC.app_fn hfa htfa
  have htfsub := inferTypeCore_fvarLeaves m.wf fuel htf hws.1
  have htfw : Expr.WScoped d tf :=
    inferTypeCore_WScoped m.wf fuel htf hws.1
  have htfb : tf.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel htf hws.1 hb.1 hLf
  have htfL : Expr.LeavesBounded tf := fun l hl => hLf l (htfsub l hl)
  have htfC : CtxOk m φ d Δa tf := hC.app_fn.of_subset htfsub
  -- the ∀-type: read (routed) and graded by the reduction claim
  obtain ⟨pa, hpa⟩ := hwr hwf htfw htfb htfL
    (LeafReads.of_ctxOk htfC) htfa
  obtain ⟨hokpa, hredf⟩ :=
    ihw hwf htfw htfb htfL htfC htfa hpa hrowfT
  have hwfe : Expr.WScoped d (Expr.forallE ty' body' mb') :=
    whnf_WScoped m.wf fuel hwf htfw
  have hbfe : (Expr.forallE ty' body' mb').looseBVarsBounded 0
      = true := whnf_looseBVars m.wf fuel hwf htfb
  have hLfe : Expr.LeavesBounded (.forallE ty' body' mb') :=
    fun l hl => htfL l (whnf_fvarLeaves m.wf fuel hwf l hl)
  simp only [Expr.WScoped] at hwfe
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
  have hLty' : Expr.LeavesBounded ty' := fun l hl =>
    hLfe l (by simp [Expr.fvarLeaves, hl])
  have hCpi : CtxOk m φ d Δa (.forallE ty' body' mb') :=
    (hC.app_fn.of_subset htfsub).of_subset
      (whnf_fvarLeaves m.wf fuel hwf)
  obtain ⟨Aa, Ba, hAa, hBa, rfl⟩ := denoteMeta_forallE_inv hpa
  -- the ∀'s reading, split: domain, fibres, and the kind-`0` component
  have hokAa : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Aa := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hokpa ρ hρ
    rw [WellDenoted_pi] at h1
    rw [AnnotValid_pi] at h2
    exact ⟨h1.1, h2.1⟩
  have hokBa : ∀ (ρ : Nat → V), Sat V Δa ρ →
      ∀ x, x ∈ˢ interp V ρ Aa → WellDenotedV V (cons x ρ) Ba := by
    intro ρ hρ x hx
    obtain ⟨h1, h2⟩ := hokpa ρ hρ
    rw [WellDenoted_pi] at h1
    rw [AnnotValid_pi] at h2
    exact ⟨h1.2 x hx, h2.2.1 x hx⟩
  have hcod0 : ∀ (ρ : Nat → V), Sat V Δa ρ → pwBit φ mb'.pw = 0 →
      ∀ x, x ∈ˢ interp V ρ Aa →
        interp V (cons x ρ) Ba ∈ˢ (univZero : V) := by
    intro ρ hρ h0 x hx
    obtain ⟨-, h2⟩ := hokpa ρ hρ
    rw [AnnotValid_pi] at h2
    exact h2.2.2 h0 x hx
  -- the argument, and the domain agreement
  obtain ⟨tyaA, htyaA⟩ :=
    hir hia hws.2 hb.2 hLa (LeafReads.of_ctxOk hC.app_arg) haa
  obtain ⟨hrowaE, hrowaT, hrowaM⟩ :=
    ihi hia hws.2 hb.2 hLa hC.app_arg haa htyaA
  have htasub := inferTypeCore_fvarLeaves m.wf fuel hia hws.2
  have htaw : Expr.WScoped d tya :=
    inferTypeCore_WScoped m.wf fuel hia hws.2
  have htab : tya.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel hia hws.2 hb.2 hLa
  have htaL : Expr.LeavesBounded tya := fun l hl => hLa l (htasub l hl)
  have htaC : CtxOk m φ d Δa tya := hC.app_arg.of_subset htasub
  have hdom : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ tyaA = interp V ρ Aa :=
    ihd hde htaw htab htaL hwfe.1 hbfe.1 hLty' htaC hCpi.forallE_ty
      htyaA hAa hrowaT hokAa
  have ha2 : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ aa ∈ˢ interp V ρ Aa := by
    intro ρ hρ
    rw [← hdom ρ hρ]
    exact hrowaM ρ hρ
  have hf2 : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ fa
        ∈ˢ interp V ρ (.pi 0 (pwBit φ mb'.pw) Aa Ba) := by
    intro ρ hρ
    rw [← hredf ρ hρ]
    exact hrowfM ρ hρ
  -- the returned type's reading, `denoteMeta_beta` backwards
  have hcross : denoteMeta m.acval env φ d (body'.instantiate1 a)
      = some (Ba.inst aa) := by
    rw [denoteMeta_beta (ty := ty') m.acval_closed
      (acval_inst_self m) hwfe.2.fvarsBelow hws.2 hb.2 haa 0, hBa]
    rfl
  rw [hcross] at hta
  obtain rfl : ta = Ba.inst aa := (Option.some.inj hta).symm
  refine ⟨?_, ?_, ?_⟩
  · intro ρ hρ
    refine ⟨(sound_app V (hrowfE ρ hρ).1 (hrowaE ρ hρ).1 (hf2 ρ hρ)
      (ha2 ρ hρ) (hcod0 ρ hρ)).1, ?_⟩
    rw [AnnotValid_app]
    exact ⟨(hrowfE ρ hρ).2, (hrowaE ρ hρ).2⟩
  · intro ρ hρ
    exact (WellDenotedV_inst0 (hrowaE ρ hρ)).mpr (hokBa ρ hρ _ (ha2 ρ hρ))
  · intro ρ hρ
    exact (sound_app V (hrowfE ρ hρ).1 (hrowaE ρ hρ).1 (hf2 ρ hρ)
      (ha2 ρ hρ) (hcod0 ρ hρ)).2

/-! ## The quarter, assembled (T5)

`InferInputs2D`'s six fields become eight, and the deltas are the
P tier's own:

| `InferInputs2D` | `InferInputs` |
|---|---|
| `const_ty` (`ConstType2C`) | `const_ty` (`ConstType`) |
| `nat_heads` (`NatHeads2`) → `NatHeads` | `nat_heads` — **verbatim**, denote-free |
| `str_lit`, `proj` | the T2 transposes |
| `sort_sem` (`SortSem2`) | **gone** — `sortSemAt_of_claims` derives it |
| `beta` (`BetaCross2C`) | **gone** — `denoteMeta_beta` is a theorem |
| — | `acval_valid` (`AcvalValid`), the leaf bit-validity residue |
| — | `infer_reads`, `whnf_reads` (the FINDING's totality residues) |

**The step is verified-only.**  The claims stay mode-generic — they
have to, since `checkSound` inducts over them at whatever mode the
install fixed — but the *step* holds at `μ.verifiedChecks = true`: the ∀ and
λ clauses read validation conjuncts that the run inversions produce
only at that mode.  See the module docstring. -/

/-- **The quarter's routed inputs**, P currency. -/
structure InferInputs (V : Type w) [SetTheory V] (μ : CheckMode) :
    Prop where
  /-- I3: the stored type's annotation, carrying its truthfulness -/
  const_ty : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat),
    ConstType m φ
  /-- the stored leaves are bit-valid (`WellDenoted`'s companion; the
  `acval_wellDenoted` field's `AnnotValid` half) -/
  acval_valid : ∀ {env : Env} (m : EnvModel V env), AcvalValid m
  /-- I4: the two numeral head facts, unchanged from the canonical
  lane -/
  nat_heads : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat),
    NatHeads m φ
  /-- I5: the `String`-literal clause -/
  str_lit : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), InferStrLitStep m μ φ fuel
  /-- I9: the projection clause -/
  proj : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), InferProjStep m μ φ fuel
  /-- the inferred type reads (dual-success totality residue) -/
  infer_reads : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), InferReads m μ φ fuel
  /-- the head normal form reads (dual-success totality residue) -/
  whnf_reads : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), WhnfReads m μ φ fuel

/-- **The inference quarter, P currency** — `InferStep2D`'s shape with
the mode pinned: the four claims at `fuel` give the inference claim at
`fuel + 1`, at a validating mode. -/
@[expose] def InferStep (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat),
    μ.verifiedChecks = true →
    WhnfCoreClaim μ m φ fuel → WhnfClaim μ m φ fuel →
    DefEqClaim μ m φ fuel → InferClaim μ m φ fuel →
    InferClaimIO μ m φ fuel →
    InferClaim μ m φ (fuel + 1)

/-- **`InferStep`, modulo the routed inputs** — the eleven shapes
dispatched to the eleven clause lemmas, exactly as `inferStep2D_of`
does.  Nine are theorems of this file; `.lit (.strVal _)` and `.proj`
route through the input structure. -/
theorem inferStep_of (h : InferInputs V μ)
    (hsssF : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat)
      (fuel : Nat), WhnfClaim μ m φ fuel → InferClaim μ m φ fuel →
      InferClaimIO μ m φ fuel → SortSemAtIOS m μ φ fuel)
    (hμ : μ.verifiedChecks = true) :
    InferStep μ V := by
  intro env m φ fuel _hv _ihwc ihw ihd ihi ihio
  have hss : SortSemAt m μ φ fuel :=
    sortSemAt_of_claims ihw ihi (h.infer_reads m φ fuel)
  have hsss : SortSemAtIOS m μ φ fuel := hsssF m φ fuel ihw ihi ihio
  intro d e t Δa hrun hws hb hLb ea ta hC hea hta
  match e, hrun, hws, hb, hLb, hC, hea with
  | .sort u, hrun, _, _, _, _, hea =>
    exact infer_sort_claim m hrun hea hta
  | .bvar i, hrun, _, _, _, _, hea =>
    exact infer_bvar_claim m hrun hea hta
  | .fvar idx ty, hrun, _, _, _, hC, hea =>
    exact infer_fvar_claim m hC hrun hea hta
  | .const nm us, hrun, _, _, _, _, hea =>
    exact infer_const_claim m (h.const_ty m φ) (h.acval_valid m) hrun
      hea hta
  | .lit (.natVal k), hrun, _, _, _, _, hea =>
    exact infer_natLit_claim m (h.nat_heads m φ) (h.acval_valid m)
      hrun hea hta
  | .lit (.strVal s), hrun, _, _, _, _, hea =>
    exact h.str_lit m φ fuel hrun hea hta
  | .forallE ty body mb, hrun, hws, hb, hLb, hC, hea =>
    exact infer_forallE_claim m hμ hss hrun hws hb hLb hC hea hta
  | .lam ty body mb, hrun, hws, hb, hLb, hC, hea =>
    exact infer_lam_claim m hμ hss hsss ihi hrun hws hb hLb
      hC hea hta
  | .app fe ae, hrun, hws, hb, hLb, hC, hea =>
    exact infer_app_claim m (h.infer_reads m φ fuel)
      (h.whnf_reads m φ fuel) ihw ihd ihi hrun hws hb hLb hC hea hta
  | .letE ty val bd, hrun, hws, hb, hLb, hC, hea =>
    exact (ConLeche.inferTypeCore_letE_inv hrun).elim
  | .proj sn i pe, hrun, hws, hb, hLb, hC, hea =>
    exact h.proj m φ fuel hrun hws hb hLb hC hea hta

end ConLeche.Model
