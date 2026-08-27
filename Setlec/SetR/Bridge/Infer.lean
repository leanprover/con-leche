import Setlec.SetR.Bridge.WhnfCore

/-!
# The inference quarter of `CheckStepR` (task #148, T3, batch a)

`InferClaimsR` at `fuel + 1`.  `inferBody` has eleven clauses and each
one is a single rule of `Setlec/SetR/Rel.lean`'s `Infer`:

| `inferBody` clause | rule |
|---|---|
| `.sort u` | I1 `Infer.sort` |
| `.fvar idx _ ty` (in scope) | I2 `Infer.bvar`, via `CtxOkR`'s leaf package |
| `.const n us` | I3 `Infer.const` |
| `.lit (.natVal _)` | I4 `Infer.litNat` |
| `.lit (.strVal _)` | I5 `Infer.litStr` |
| `.forallE` | I6 `Infer.pi` |
| `.lam` | I7 `Infer.lam` |
| `.app` | I8 `Infer.app` |
| `.proj` | I9 `Infer.proj` |
| `.letE` | I10 `Infer.letE` |
| `.bvar` | throws |

**This module holds the five leaf clauses**, which are the ones the
slack shape serves without composition (each produces its `Infer` on
the nose, with `DefEq.refl` for the slack — except `.fvar`, which *is*
the slack's only source).  The six structural clauses are named `Prop`s
pending the resolution of the finding recorded in `Setlec/SetR/DESIGN.md`
("The `Red`-at-an-inferred-type premises do not compose with the
slack") — see that section before discharging any of them, because
their rule shapes are what the finding is about.

The literal clauses are worth one line of comparison with the TT lane.
There, `infer_natLit_claim` has to *identify* `cval natZeroName ψ` with
the layer's `natZeroT` (`EnvTT.basis_pinned`, `natLitT_eq_numeral`)
before `hasType_numeral` applies.  Here the rule is stated over `cval`
itself (`natLitV cval φ n` **is** `denote`'s own literal clause), so the
clause is the guard plus the stored arity — no pinning, no numeral
meta-induction.  That is premise-exactness paying for itself at the
cheapest possible site.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env} {fuel : Nat}

/-! ## The leaf clauses -/

/-- I1: `Sort u` infers `Sort (u+1)`. -/
theorem infer_sort_claimR {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {u : Level} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.sort u) = .ok t) :
    ∃ v tv, denote cval env φ d (.sort u) = some v ∧
      denote cval env φ d t = some tv ∧
      ∃ T', Infer mode env cval φ Δ v T' ∧ DefEq mode env cval φ Δ T' tv := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind, Except.ok.injEq] at h
  subst h
  refine ⟨.sort (u.eval φ), .sort (u.eval φ + 1), ?_, ?_,
    .sort (u.eval φ + 1), Infer.sort, DefEq.refl⟩
  · rw [denote_sort]
  · rw [denote_sort]
    rfl

/-- I2: an in-scope free variable infers its annotation — **the slack's
only source**.  `CtxOkR`'s leaf package is already in the claim's own
shape (`∃ T', Infer … ∧ DefEq … T' ⟦ty⟧`), because the context entry is
the *binder's* denotation while the checker reads the *leaf's*
annotation, and a binder congruence makes the two differ by exactly one
`DefEq`. -/
theorem infer_fvar_claimR {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {idx : Nat} {n : Name} {ty t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.fvar idx n ty) = .ok t)
    (hC : CtxOkR mode cval env φ d Δ (.fvar idx n ty)) :
    ∃ v tv, denote cval env φ d (.fvar idx n ty) = some v ∧
      denote cval env φ d t = some tv ∧
      ∃ T', Infer mode env cval φ Δ v T' ∧ DefEq mode env cval φ Δ T' tv := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · next hlt =>
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨-, -, T, hty, T', hI, hD⟩ :=
      hC.2 (idx, n, ty) (by simp [Expr.fvarLeaves])
    exact ⟨.bvar (d - 1 - idx), T, by rw [denote_fvar], hty, T', hI, hD⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `bvar` is outside the fragment; the checker throws, and the bridge
refutes it from the denotation as well. -/
theorem infer_bvar_claimR {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {i : Nat} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.bvar i) = .ok t) :
    ∃ v tv, denote cval env φ d (.bvar i) = some v ∧
      denote cval env φ d t = some tv ∧
      ∃ T', Infer mode env cval φ Δ v T' ∧ DefEq mode env cval φ Δ T' tv := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- I3: `.const` infers its stored type.  The two moves that get the
`denoteClosed` side condition from depth `0` to depth `d` are the same
two the delta step uses — `denote_instLevels` and `denote_lift` at a
closed denotation — because they are the same fact about `cval` read in
two directions. -/
theorem infer_const_claimR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    {d : Nat} {Δ : List VExpr} {n : Name} {us : List Level} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.const n us) = .ok t) :
    ∃ v tv, denote m.cval env φ d (.const n us) = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  cases hf : env.find? n with
  | none => rw [hf] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    rw [hf] at h
    dsimp only at h
    split at h
    · next hlen =>
      simp only [Except.ok.injEq] at h
      subst h
      obtain rfl : ci.name = n := by
        rw [Env.find?] at hf
        have := List.find?_some hf
        simpa using this
      obtain ⟨tv0, htv0⟩ :=
        m.ty_denotes ci (find?_mem hf)
          (Level.substFn φ ci.toConstantVal.levelParams us)
      obtain ⟨hnf, -, -, hbd, -⟩ := m.wf ci (find?_mem hf)
      have hcls : VExpr.Closed tv0 := denote_closed hcl hnf hbd htv0
      -- the rule's own spelling: level instantiation composes the
      -- assignment (`denote_instLevels`), so the stored type denotes at
      -- `φ` after instantiation exactly as it does at the substituted
      -- assignment before it
      have htv0' : denoteClosed m.cval env φ
          (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams us) = some tv0 := by
        rw [denoteClosed, denote_instLevels m.val_params]
        exact htv0
      -- the stored type, instantiated and denoted at the ambient depth
      have hdt : denote m.cval env φ d
          (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams us) = some tv0 := by
        rw [denote_instLevels m.val_params,
          denote_lift hcl
            (Expr.WScoped.of_not_hasFvar hnf).fvarsBelow d (Nat.zero_le d)]
        rw [denoteClosed] at htv0
        rw [htv0]
        simp only [Option.map_some, Nat.sub_zero,
          VExpr.liftN_eq_self_of_closed hcls]
      refine ⟨m.cval ci.name
        (Level.substFn φ ci.toConstantVal.levelParams us), tv0, ?_, hdt,
        tv0, Infer.const hf hlen htv0' hcls, DefEq.refl⟩
      rw [denote_const, hf]
      exact if_pos hlen
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ### The literal clauses

Both need one arity fact off the support guard — the stored family
carries no level parameters — so that the type constant's denotation is
`cval … (Level.substFn φ [] [])`, which is the rule's own spelling. -/

/-- The `Nat` family's stored declaration carries no level parameters
(read off `natLitSupported`'s `natIndOk` conjunct). -/
theorem natName_levelParams_nil {env : Env}
    (hg : natLitSupported env = true) {ci : ConstantInfo}
    (hf : env.find? natName = some ci) :
    ci.toConstantVal.levelParams = [] := by
  simp only [natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨h1, -⟩, -⟩ := hg
  rw [hf] at h1
  cases ci with
  | indInfo cv caps =>
    simp only [natIndOk, Bool.and_eq_true] at h1
    simpa [ConstantInfo.toConstantVal, List.isEmpty_iff] using h1.1
  | _ => simp [natIndOk] at h1

/-- The `String` family's stored declaration carries no level parameters
(read off `strLitSupported`'s `stringTyOk` conjunct). -/
theorem stringName_levelParams_nil {env : Env}
    (hg : strLitSupported env = true) {ci : ConstantInfo}
    (hf : env.find? stringName = some ci) :
    ci.toConstantVal.levelParams = [] := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg
  rw [hf] at h2
  simp only [stringTyOk, Bool.and_eq_true] at h2
  simpa [List.isEmpty_iff] using h2.1

/-- I4: a `Nat` literal infers `Nat`. -/
theorem infer_natLit_claimR {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {k : Nat} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.lit (.natVal k)) = .ok t) :
    ∃ v tv, denote cval env φ d (.lit (.natVal k)) = some v ∧
      denote cval env φ d t = some tv ∧
      ∃ T', Infer mode env cval φ Δ v T' ∧ DefEq mode env cval φ Δ T' tv := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · next hg =>
    simp only [Except.ok.injEq] at h
    subst h
    have hgt : natLitSupported env = true := by simpa using hg
    cases hf : env.find? natName with
    | none =>
      simp only [natLitSupported, Bool.and_eq_true] at hgt
      obtain ⟨⟨h1, -⟩, -⟩ := hgt
      rw [hf] at h1
      exact nomatch h1
    | some ci =>
      have hlp := natName_levelParams_nil hgt hf
      refine ⟨natLitV cval φ k, cval natName (Level.substFn φ [] []), ?_, ?_,
        _, Infer.litNat hgt, DefEq.refl⟩
      · rw [denote_natLit, if_pos hgt]
        rfl
      · simp [denote_const, hf, hlp]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- I5: a `String` literal infers `String`. -/
theorem infer_strLit_claimR {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {s : String} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.lit (.strVal s)) = .ok t) :
    ∃ v tv, denote cval env φ d (.lit (.strVal s)) = some v ∧
      denote cval env φ d t = some tv ∧
      ∃ T', Infer mode env cval φ Δ v T' ∧ DefEq mode env cval φ Δ T' tv := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · next hg =>
    simp only [Except.ok.injEq] at h
    subst h
    have hgt : strLitSupported env = true := by simpa using hg
    cases hf : env.find? stringName with
    | none =>
      simp only [strLitSupported, Bool.and_eq_true] at hgt
      obtain ⟨⟨⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hgt
      rw [hf] at h2
      exact nomatch h2
    | some ci =>
      have hlp := stringName_levelParams_nil hgt hf
      refine ⟨strLitT cval env φ s, cval stringName (Level.substFn φ [] []),
        ?_, ?_, _, Infer.litStr hgt, DefEq.refl⟩
      · rw [denote_strLit, if_pos hgt]
      · simp [denote_const, hf, hlp]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The six structural clauses, as named obligations

Each is stated at *clause* granularity (`inferBody` restricted to one
`Expr` shape — a case restriction, not a stage split, which is the only
legitimate boundary).

**Read `Setlec/SetR/DESIGN.md`'s finding before discharging these.**
Five of the six (`.forallE`, `.lam`, `.app`, `.proj`, `.letE`) need
their rule's `Infer x tx → Red μ Δ tx Shape` premise pair, and the
bridge can only produce `Infer x T'`, `DefEq T' ⟦tx⟧`, `Red ⟦tx⟧ Shape`
— the slack sits between the two premises, where nothing composes it
away.  That is the finding; the obligations are named here so that the
gap is visible in the source rather than in prose. -/

/-- The `∀` clause of `InferClaimsR` (I6). -/
def InferPiStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {n : Name} {ty body t : Expr}
    {mb : BinderMeta},
    inferTypeCore mode env (fuel + 1) d (.forallE n ty body mb) = .ok t →
    Expr.WScoped d (.forallE n ty body mb) →
    (Expr.forallE n ty body mb).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.forallE n ty body mb) →
    CtxOkR mode m.cval env φ d Δ (.forallE n ty body mb) →
    ∃ v tv, denote m.cval env φ d (.forallE n ty body mb) = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv

/-- The `λ` clause of `InferClaimsR` (I7). -/
def InferLamStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {n : Name} {ty body t : Expr}
    {mb : BinderMeta},
    inferTypeCore mode env (fuel + 1) d (.lam n ty body mb) = .ok t →
    Expr.WScoped d (.lam n ty body mb) →
    (Expr.lam n ty body mb).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.lam n ty body mb) →
    CtxOkR mode m.cval env φ d Δ (.lam n ty body mb) →
    ∃ v tv, denote m.cval env φ d (.lam n ty body mb) = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv

/-- The application clause of `InferClaimsR` (I8). -/
def InferAppStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {f a t : Expr},
    inferTypeCore mode env (fuel + 1) d (.app f a) = .ok t →
    Expr.WScoped d (.app f a) →
    (Expr.app f a).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.app f a) →
    CtxOkR mode m.cval env φ d Δ (.app f a) →
    ∃ v tv, denote m.cval env φ d (.app f a) = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv

/-- The `let` clause of `InferClaimsR` (I10). -/
def InferLetStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {n : Name} {ty val b t : Expr},
    inferTypeCore mode env (fuel + 1) d (.letE n ty val b) = .ok t →
    Expr.WScoped d (.letE n ty val b) →
    (Expr.letE n ty val b).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.letE n ty val b) →
    CtxOkR mode m.cval env φ d Δ (.letE n ty val b) →
    ∃ v tv, denote m.cval env φ d (.letE n ty val b) = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv

/-- The projection clause of `InferClaimsR` (I9). -/
def InferProjStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {sn : Name} {i : Nat} {pe t : Expr},
    inferTypeCore mode env (fuel + 1) d (.proj sn i pe) = .ok t →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    CtxOkR mode m.cval env φ d Δ (.proj sn i pe) →
    ∃ v tv, denote m.cval env φ d (.proj sn i pe) = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv

/-- **`InferClaimsR` at `fuel + 1`**, modulo the five structural
clauses.  The dispatch is the point: eleven clauses, each one line,
because each one *is* a rule. -/
theorem infer_claimsR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hpi : InferPiStepR (mode := mode) m φ fuel)
    (hlam : InferLamStepR (mode := mode) m φ fuel)
    (happ : InferAppStepR (mode := mode) m φ fuel)
    (hlet : InferLetStepR (mode := mode) m φ fuel)
    (hproj : InferProjStepR (mode := mode) m φ fuel) :
    InferClaimsR mode m φ (fuel + 1) := by
  intro d e t Δ h hws hb hLb hC
  match e, h, hws, hb, hLb, hC with
  | .sort u, h, _, _, _, _ => exact infer_sort_claimR h
  | .fvar idx nm ty, h, _, _, _, hC => exact infer_fvar_claimR h hC
  | .const nm us, h, _, _, _, _ => exact infer_const_claimR m φ hcl h
  | .lit (.natVal k), h, _, _, _, _ => exact infer_natLit_claimR h
  | .lit (.strVal st), h, _, _, _, _ => exact infer_strLit_claimR h
  | .bvar i, h, _, _, _, _ => exact infer_bvar_claimR h
  | .forallE nm ty body mb, h, hws, hb, hLb, hC => exact hpi h hws hb hLb hC
  | .lam nm ty body mb, h, hws, hb, hLb, hC => exact hlam h hws hb hLb hC
  | .app f a, h, hws, hb, hLb, hC => exact happ h hws hb hLb hC
  | .letE nm ty val b, h, hws, hb, hLb, hC => exact hlet h hws hb hLb hC
  | .proj sn i pe, h, hws, hb, hLb, hC => exact hproj h hws hb hLb hC

end Setlec.SetR
