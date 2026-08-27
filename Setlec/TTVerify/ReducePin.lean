import Setlec.TTVerify.DeclDefn

/-!
# The compiler-trust identity (`checkReducePin`)

`ReducePinTT`, the obligation `DeclOpaqueTT` left behind.  The checker
certifies, once at install, that the pinned opaque's value is the
identity on its element type:

```
isDefEq env 1 (.app valA (fvar 0 "a" (elemTy c))) (fvar 0 "a" (elemTy c))
```

— an *open* equation at depth `1`, over one free variable of the
element type.  `ReduceOpsTT` wants the same equation **closed** at an
arbitrary context and an arbitrary derivably-typed argument.  So the
whole content is a transport of one `Deq` across two moves:

| move | lemma |
| --- | --- |
| one-entry context becomes `E :: Δ` | `HasType.weakenTail` |
| the opened variable becomes the argument | `HasType.instantiate` |

Neither move needs the lifting algebra's general form, and that is the
point worth recording: **the certificate was written at depth `1` with
the variable at index `0`, which is exactly the shape the substitution
lemma consumes.**  A certificate stated at depth `0` over a fresh
constant, or at depth `2` with the variable buried, would have cost a
context-surgery lemma; this one costs an append that is definitionally
a cons.
-/

namespace Setlec.TTVerify

open Setlec.TT

variable {F : Nat}

/-- A derivable equation weakens by appending to the context's tail. -/
theorem Deq.weakenTail {Γ : List VExpr} {a b : VExpr} (Δ : List VExpr)
    (h : Deq Γ a b) : Deq (Γ ++ Δ) a b := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, hT.weakenTail Δ⟩

/-- **The identity certificate, closed.**  An open equation between
`f x` and `x` at the single opened variable becomes the equation at
every derivably-typed argument. -/
theorem identity_of_cert {E v : VExpr} (hcl : VExpr.Closed v)
    (h : Deq [E] (.app (v.liftN 1) (.bvar 0)) (.bvar 0))
    {Δ : List VExpr} {X : VExpr} (hX : HasType Δ X E) :
    Deq Δ (.app v X) X := by
  obtain ⟨T, hT⟩ := Deq.weakenTail Δ h
  have := (show HasType (E :: Δ) .prf
      (.eqE T (.app (v.liftN 1) (.bvar 0)) (.bvar 0)) from hT).instantiate hX
  refine ⟨T.inst X, ?_⟩
  rw [VExpr.liftN_eq_self_of_closed hcl 1 0] at this
  simpa [VExpr.inst, VExpr.inst_eq_self_of_closed hcl,
    VExpr.liftN_zero] using this

/-! ## The walk

`checkReducePin` is four nested guards and two `isDefEq`s; only the
second `isDefEq` is consumed here.  The first (`valA ≡ pin`) is the
*elaborator-drift* gate — it exists so a toolchain change surfaces as a
decline rather than silently — and the bridge needs nothing from it,
which is the expected shape: a gate that protects the *checker's* other
guarantees leaves the derivation layer alone. -/

/-- The element type is a stored constant with no level parameters. -/
theorem reduceElem_shape {env : Env} {c : Name}
    (h : reduceElemOk env c = true) :
    ∃ ci, env.find? (reduceElemName c) = some ci ∧
      ci.toConstantVal.levelParams = [] := by
  by_cases hc : c = reduceNatName
  · rw [reduceElemOk, if_pos hc] at h
    refine ⟨natA, ?_, rfl⟩
    rw [reduceElemName, if_pos hc]
    simpa using h
  · rw [reduceElemOk, if_neg hc] at h
    rw [reduceElemName, if_neg hc]
    cases hf : env.find? boolName with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      cases ci with
      | indInfo cvB caps =>
        refine ⟨.indInfo cvB caps, rfl, ?_⟩
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          decide_eq_true_eq] at h
        exact h.1.2
      | _ => exact nomatch h

/-- Inversion of the compiler-trust pin: the identity certificate. -/
theorem checkReducePin_inv {env env2 : Env} {c : Name} {value : Expr}
    (h : checkReducePin (fueledOps mode F) env env2 c value = .ok ()) :
    reduceElemOk env c = true ∧
    ∃ valA, annotateCore mode env F 0 value = .ok valA ∧
      isDefEqCore mode env F 1 (.app valA (reduceCertVar c))
        (reduceCertVar c) = .ok true := by
  simp only [checkReducePin, fueledOps_annotate, fueledOps_isDefEq,
    Bind.bind, Except.bind] at h
  by_cases hg : (reduceStoredOk env2 c && reduceElemOk env c) = true
  case neg => rw [if_neg hg] at h; exact nomatch h
  rw [if_pos hg] at h
  by_cases hpg : reducePinGuard env c = true
  case neg => rw [if_neg hpg] at h; exact nomatch h
  rw [if_pos hpg] at h
  have helem : reduceElemOk env c = true := by
    obtain ⟨-, h2⟩ := by simpa only [Bool.and_eq_true] using hg
    exact h2
  refine ⟨helem, ?_⟩
  cases hva : annotateCore mode env F 0 value with
  | error e => rw [hva] at h; exact nomatch h
  | ok valA =>
  rw [hva] at h
  dsimp only at h
  cases hpa : annotateCore mode env F 0 (reduceDeclPin c) with
  | error e => rw [hpa] at h; exact nomatch h
  | ok pinA =>
  rw [hpa] at h
  dsimp only at h
  cases hp1 : isDefEqCore mode env F 0 valA pinA with
  | error e => rw [hp1] at h; exact nomatch h
  | ok b1 =>
  rw [hp1] at h
  cases b1 with
  | false => simp [throw, throwThe, MonadExceptOf.throw] at h
  | true =>
  simp only [if_true] at h
  cases hp2 : isDefEqCore mode env F 1 (.app valA (reduceCertVar c))
      (reduceCertVar c) with
  | error e => rw [hp2] at h; exact nomatch h
  | ok b2 =>
  rw [hp2] at h
  cases b2 with
  | false => simp [throw, throwThe, MonadExceptOf.throw] at h
  | true => exact ⟨valA, rfl, hp2⟩

/-- **`ReducePinTT`, discharged.** -/
theorem reducePinTT : ReducePinTT F := by
  intro env m cv value value' hmem hfresh hpin hannv hvf hvb hvex hmp
  obtain ⟨helem, valA, hva, hcert⟩ := checkReducePin_inv hpin
  obtain rfl : value' = valA := by
    rw [hva] at hannv; exact (Except.ok.inj hannv).symm
  obtain ⟨ciE, hfE, hlpE⟩ := reduceElem_shape helem
  have hne : reduceElemName cv.name ≠ cv.name := by
    intro hh; rw [hh, hfresh] at hfE; exact nomatch hfE
  refine ⟨by
    rw [Env.find?_cons_of_isSome hfresh (by rw [hfE]; rfl), hfE]; rfl, ?_⟩
  intro φ Δ X hX
  rw [cvalAt_ne hne] at hX
  obtain ⟨v, hv⟩ := hvex φ
  rw [cvalAt_self hv]
  obtain ⟨-, -, ihd, -⟩ := checkClaimsTT m φ F
  -- the element type denotes to the stored valuation, at every depth
  have hty : reduceElemTy cv.name = .const (reduceElemName cv.name) [] := by
    unfold reduceElemTy reduceElemName
    split <;> rfl
  have hE : ∀ d, denote m.cval env φ d (reduceElemTy cv.name)
      = some (m.cval (reduceElemName cv.name) φ) := by
    intro d
    rw [hty]
    exact denote_const_nolevels m φ hfE hlpE d
  have hEcl : VExpr.Closed (m.cval (reduceElemName cv.name) φ) :=
    m.cval_closed _ _
  have hvcl : VExpr.Closed v := denote_closed m.cval_closed hvf hvb hv
  -- the certificate's two sides, framed at depth 1 over one variable
  have hCx : CtxOk m.cval env φ 1 [m.cval (reduceElemName cv.name) φ]
      (reduceCertVar cv.name) := by
    refine ⟨rfl, fun l hl => ?_⟩
    rw [reduceCertVar, hty] at hl
    simp [Expr.fvarLeaves] at hl
    subst hl
    refine ⟨by omega, by simp [Expr.fvarsBelow], _, ?_,
      HasType.bvar (A := m.cval (reduceElemName cv.name) φ) (by simp)⟩
    dsimp only
    rw [← hty, hE 1, VExpr.liftN_eq_self_of_closed hEcl _ 0]
  have hwx : Expr.WScoped 1 (reduceCertVar cv.name) := by
    rw [reduceCertVar, hty]
    simp only [Expr.WScoped]
    exact ⟨by omega, by simp⟩
  have hbx : (reduceCertVar cv.name).looseBVarsBounded 0 = true := rfl
  have hLx : Expr.LeavesBounded (reduceCertVar cv.name) := by
    intro l hl
    rw [reduceCertVar, hty] at hl
    simp [Expr.fvarLeaves] at hl
    subst hl
    rfl
  have hwv : Expr.WScoped 1 value' := Expr.WScoped.of_not_hasFvar hvf
  have hLv : Expr.LeavesBounded value' :=
    Expr.LeavesBounded.of_not_hasFvar hvf
  have hCv : CtxOk m.cval env φ 1 [m.cval (reduceElemName cv.name) φ]
      value' := by
    refine ⟨rfl, fun l hl => ?_⟩
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf] at hl
    exact nomatch hl
  -- and the denotations the claim compares
  have hden1 : denote m.cval env φ 1
      (.app value' (reduceCertVar cv.name))
      = some (.app (v.liftN 1) (.bvar 0)) := by
    rw [denote_app, denote_weaken_top m.cval_closed
      (Expr.WScoped.of_not_hasFvar (d := 0) hvf).fvarsBelow]
    rw [show denote m.cval env φ 0 value' = some v from hv]
    rw [reduceCertVar, denote_fvar]
    rfl
  have hden2 : denote m.cval env φ 1 (reduceCertVar cv.name)
      = some (.bvar 0) := by rw [reduceCertVar, denote_fvar]
  refine identity_of_cert hvcl (ihd hcert ?_ ?_ ?_ hwx hbx hLx ?_ hCx
    hden1 hden2) hX
  · simp only [Expr.WScoped]
    exact ⟨hwv, hwx⟩
  · simp [Expr.looseBVarsBounded, hvb, hbx]
  · intro l hl
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_append.mp hl with h | h
    · exact hLv l h
    · exact hLx l h
  · refine ⟨rfl, fun l hl => ?_⟩
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_append.mp hl with h | h
    · exact hCv.2 l h
    · exact hCx.2 l h

/-- **`DeclOpaqueTT`, with no outstanding obligation.** -/
theorem declOpaqueTT_closed : DeclOpaqueTT F := declOpaqueTT reducePinTT

end Setlec.TTVerify