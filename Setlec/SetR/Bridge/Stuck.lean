import Setlec.SetR.Bridge.StrLitR

/-!
# `DefEqStuckStepR`, discharged (task #148, T3, batch d)

`defeqStep`'s last block (`Core.lean:1794-1897`): neither side reduced,
neither is a proof, neither head unfolds — so the verdict comes from a
leaf comparison, a congruence, an eta certificate, or `stuckIrrel`.
Seventeen cases, and `split at h` delivers them in the checker's own
order, which is the map:

| # | case | rule |
|---|---|---|
| 1 | `sort`/`sort` under `Level.isEquiv` | D1 (`Level.isEquiv_sound`) |
| 2 | `lit`/`lit` equal | D1 |
| 3–4 | `lit 0` against `Nat.zero`, both orders | D1 — `natLitV … 0` **is** the `Nat.zero` valuation |
| 5–6 | `lit (k+1)` against a `Nat.succ` application, both orders | D14 (+ D2) |
| 7–8 | a string literal against a `String.ofList` application, both orders | the recursive verdict at the expanded form |
| 9 | `fvar i`/`fvar i` | D1 |
| 10 | `const n us`/`const n us'` under `isEquivList` | D1 (`denote_const_congrR`) |
| 11 | `forallE`/`forallE` | D5, **through `CtxOkR.openCong`** |
| 12 | `lam`/`lam` | D6, likewise |
| 13 | `app`/`app` | D7 (`defEqL_of_defEqListR`) |
| 14 | `proj`/`proj` at equal index | `DefEq.projCong` (finding 2's rule) |
| 15–16 | one-sided λ, both orders | D13 through `etaCert_stepR` (+ D2) |
| 17 | distinct stuck heads | `StuckIrrelStepR` |

and every *fallthrough* of cases 3–16 is `StuckIrrelStepR` too, which is
what `hfall` names once at the top.

**This is where `CtxOkR.openCong` fires.**  Batch (a) built it and
proved it composes; cases 11 and 12 are its only consumers, and they are
the reason the whole slack design exists: the checker opens each body
with *its own* annotation, the context takes the left one, and the right
side's leaf package is the plain `Infer.bvar` plus the domain
certificate weakened by M1.  `binder_congrR` factors the two cases,
which differ only in the denotation clause and the congruence rule.

Three cases are worth a line each.  **7–8 need no reduction rule at
all**: the checker compares `strLitToConstructor st` against the other
side, and `denote_strLitCtorR` says that expression denotes to *the same
`VExpr`* as the literal — so the recursive verdict is already the
equation wanted, and R7 is not invoked here (it is invoked at the
`.proj` and iota major sites, where the *reduct* is what moves).
**3–4** are `DefEq.refl` because `natLitV cval φ 0` is literally the
`Nat.zero` valuation.  **5–6** are D14, whose statement is
`natLitV (k+1) ≡ .app succV x` — the checker's own shape-directed
comparison, named rather than derived through D7.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify
variable {mode : CheckMode} {env : Env}


/-- A `Nat` literal denotes only under the support guard, and to
`natLitV`. -/
theorem denote_natLit_invR {cval : TConstVal} {φ : Name → Nat} {d n : Nat}
    {v : VExpr} (h : denote cval env φ d (.lit (.natVal n)) = some v) :
    natLitSupported env = true ∧ v = natLitV cval φ n := by
  rw [denote_natLit] at h
  split at h
  · next hg => exact ⟨hg, (Option.some.inj h).symm⟩
  · exact nomatch h

/-- `Nat.zero`, denoted: `natLitV … 0` is the valuation itself. -/
theorem denote_natZeroConstR {cval : TConstVal} {φ : Name → Nat}
    (hg : natLitSupported env = true) {d : Nat} :
    denote cval env φ d (.const natZeroName []) = some (natLitV cval φ 0) := by
  simp only [natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, h2⟩, -⟩ := hg
  cases hf : env.find? natZeroName with
  | none => rw [hf] at h2; exact nomatch h2
  | some ci =>
    rw [hf] at h2
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [natZeroOk, Bool.and_eq_true] at h2
        simpa [ConstantInfo.toConstantVal, List.isEmpty_iff] using h2.1
      | _ => simp [natZeroOk] at h2
    simp [denote_const, hf, hlp, natLitV, natLitT]

/-- `Nat.succ`, denoted. -/
theorem denote_natSuccConstR {cval : TConstVal} {φ : Name → Nat}
    (hg : natLitSupported env = true) {d : Nat} :
    denote cval env φ d (.const natSuccName []) = some (succV cval φ) := by
  simp only [natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨-, h3⟩ := hg
  cases hf : env.find? natSuccName with
  | none => rw [hf] at h3; exact nomatch h3
  | some ci =>
    rw [hf] at h3
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [natSuccOk, Bool.and_eq_true] at h3
        simpa [ConstantInfo.toConstantVal, List.isEmpty_iff] using h3.1
      | _ => simp [natSuccOk] at h3
    simp [denote_const, hf, hlp, succV]

/-- A closed expression's context correspondence is free. -/
theorem CtxOkR.of_fvarLeaves_nil {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {e : Expr} (hlen : Δ.length = d)
    (h : e.fvarLeaves = []) : CtxOkR mode cval env φ d Δ e :=
  ⟨hlen, fun l hl => by rw [h] at hl; exact absurd hl (by simp)⟩

/-- The frame conditions of an application's argument. -/
theorem frame_appArgR {cval : TConstVal} {φ : Name → Nat} {d : Nat}
    {Δ : List VExpr} {f x : Expr}
    (hws : Expr.WScoped d (.app f x))
    (hb : (Expr.app f x).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f x))
    (hC : CtxOkR mode cval env φ d Δ (.app f x)) :
    Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ CtxOkR mode cval env φ d Δ x := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hws.2, hb.2, fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]),
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC⟩


/-- **The binder congruence's two premises**, shared by the `∀` and `λ`
cases: the domain certificate, and the opened-body certificate read in
the *left* domain's context.  This is where `CtxOkR.openCong` — the
slack design's whole point — fires. -/
theorem binder_congrR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {n₁ n₂ : Name} {ty₁ bd₁ ty₂ bd₂ : Expr}
    {A₁ B₁ A₂ B₂ : VExpr}
    (hdt : isDefEqCore mode env fuel d ty₁ ty₂ = .ok true)
    (hdb : isDefEqCore mode env fuel (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁))
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true)
    (hwt₁ : Expr.WScoped d ty₁) (hbt₁ : ty₁.looseBVarsBounded 0 = true)
    (hLt₁ : Expr.LeavesBounded ty₁) (hCt₁ : CtxOkR mode m.cval env φ d Δ ty₁)
    (hwb₁ : Expr.WScoped d bd₁) (hbb₁ : bd₁.looseBVarsBounded 1 = true)
    (hLb₁ : Expr.LeavesBounded bd₁) (hCb₁ : CtxOkR mode m.cval env φ d Δ bd₁)
    (hwt₂ : Expr.WScoped d ty₂) (hbt₂ : ty₂.looseBVarsBounded 0 = true)
    (hLt₂ : Expr.LeavesBounded ty₂) (hCt₂ : CtxOkR mode m.cval env φ d Δ ty₂)
    (hwb₂ : Expr.WScoped d bd₂) (hbb₂ : bd₂.looseBVarsBounded 1 = true)
    (hLb₂ : Expr.LeavesBounded bd₂) (hCb₂ : CtxOkR mode m.cval env φ d Δ bd₂)
    (hA₁ : denote m.cval env φ d ty₁ = some A₁)
    (hB₁ : denote m.cval env φ (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁)) = some B₁)
    (hA₂ : denote m.cval env φ d ty₂ = some A₂)
    (hB₂ : denote m.cval env φ (d + 1)
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = some B₂) :
    DefEq mode env m.cval φ Δ A₁ A₂ ∧
      DefEq mode env m.cval φ (A₁ :: Δ) B₁ B₂ := by
  have hDA : DefEq mode env m.cval φ Δ A₁ A₂ :=
    ihd hdt hwt₁ hbt₁ hLt₁ hwt₂ hbt₂ hLt₂ hCt₁ hCt₂ hA₁ hA₂
  obtain ⟨hwo₁, hbo₁, hLo₁, hCo₁⟩ :=
    frame_openR (n := n₁) (A := A₁) hcl hwt₁ hbt₁ hwb₁ hbb₁ hLt₁ hLb₁ hCt₁
      hCb₁ hA₁
  -- the second side is opened with *its own* annotation, in the *left*
  -- domain's context: `CtxOkR.openCong`, and nothing else
  have hCo₂ : CtxOkR mode m.cval env φ (d + 1) (A₁ :: Δ)
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) :=
    CtxOkR.openCong (n := n₂) hcl hCb₂ hCt₂ hA₂ hwt₂.fvarsBelow hDA
  refine ⟨hDA, ihd hdb hwo₁ hbo₁ hLo₁
    (Expr.WScoped.instantiate1 hwt₂ 0 hwb₂)
    (looseBVarsBounded_instantiate1 bd₂ 0 hbb₂) (fun l hl => ?_)
    hCo₁ hCo₂ hB₁ hB₂⟩
  rcases Expr.fvarLeaves_instantiate1 bd₂ 0 hl with h2 | h2
  · exact hLb₂ l h2
  · rw [Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hbt₂
    · exact hLt₂ l h3

/-- **`DefEqStuckStepR`, proved**, modulo `StuckIrrelStepR` (which is
itself proved modulo the two eta certificates). -/
theorem defeqStuck_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel)
    (hsi : StuckIrrelStepR (mode := mode) m φ fuel) :
    DefEqStuckStepR (mode := mode) m φ fuel := by
  intro d Δ k a b a' b' h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  simp only [defeqStep, Bind.bind, Except.bind, whnfCore_def,
    proofIrrel_fold, reduceNat_fold, defeqSpine_fold, stuckIrrel_fold,
    defeq_def, defEqList_fold, etaCert_fold] at h
  rw [if_neg (by simpa using hab), hwca] at h
  dsimp only at h
  rw [hwcb] at h
  dsimp only at h
  rw [if_neg (by simpa using hab'), hir] at h
  dsimp only at h
  rw [hna] at h
  dsimp only at h
  rw [hnb] at h
  dsimp only at h
  rw [hha, hhb] at h
  simp only [Bool.false_eq_true, if_false] at h
  have hfall : stuckIrrelP mode env fuel d a' b' = .ok true →
      DefEq mode env m.cval φ Δ va vb := fun hs =>
    hsi hs hwa hba hLa hwb hbb hLb hCa hCb hva hvb
  clear hab hwca hwcb hab' hir hna hnb hha hhb hsi
  split at h
  -- 1: sort/sort (D1)
  · rename_i u v
    rw [denote_sort] at hva hvb
    obtain rfl : va = .sort (u.eval φ) := (Option.some.inj hva).symm
    obtain rfl : vb = .sort (v.eval φ) := (Option.some.inj hvb).symm
    cases hle : Level.isEquiv u v with
    | none => rw [hle] at h; exact nomatch h
    | some r =>
      rw [hle] at h
      dsimp only [liftFueled] at h
      cases r with
      | false => exact nomatch h
      | true =>
        rw [Level.isEquiv_sound hle φ]
        exact DefEq.refl
  -- 2: lit/lit (D1)
  · rename_i l₁ l₂
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl : l₁ = l₂ := eq_of_beq h
    obtain rfl : va = vb := by rw [hva] at hvb; exact Option.some.inj hvb
    exact DefEq.refl
  -- 3: `lit 0` against `Nat.zero` (D1)
  · rename_i n c us
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denote_natLit_invR hva
      rw [denote_natZeroConstR hg] at hvb
      obtain rfl : vb = natLitV m.cval φ 0 := (Option.some.inj hvb).symm
      exact DefEq.refl
    · exact hfall h
  -- 4: `Nat.zero` against `lit 0` (D1)
  · rename_i c us n
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denote_natLit_invR hvb
      rw [denote_natZeroConstR hg] at hva
      obtain rfl : va = natLitV m.cval φ 0 := (Option.some.inj hva).symm
      exact DefEq.refl
    · exact hfall h
  -- 5: `lit (k+1)` against a `Nat.succ` application (D14)
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denote_natLit_invR hva
        rw [denote_app] at hvb
        split at hvb
        · next vf vx hf hx =>
          rw [denote_natSuccConstR hg] at hf
          obtain rfl : vf = succV m.cval φ := (Option.some.inj hf).symm
          obtain rfl : vb = .app (succV m.cval φ) vx := (Option.some.inj hvb).symm
          obtain ⟨hwx, hbx, hLx, hCx⟩ := frame_appArgR hwb hbb hLb hCb
          have hlit : CtxOkR mode m.cval env φ d Δ (.lit (.natVal 0)) :=
            CtxOkR.of_fvarLeaves_nil hCa.1 (by simp [Expr.fvarLeaves])
          exact DefEq.litSuccApp hg
            (ihd h (Expr.WScoped.of_not_hasFvar rfl) rfl
              (Expr.LeavesBounded.of_not_hasFvar rfl) hwx hbx hLx
              (CtxOkR.of_fvarLeaves_nil hCa.1 (by simp [Expr.fvarLeaves])) hCx
              (denote_natLitV hg d _) hx)
        · exact nomatch hvb
      · exact hfall h
    · exact hfall h
  -- 6: a `Nat.succ` application against `lit (k+1)` (D14 + D2)
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denote_natLit_invR hvb
        rw [denote_app] at hva
        split at hva
        · next vf vx hf hx =>
          rw [denote_natSuccConstR hg] at hf
          obtain rfl : vf = succV m.cval φ := (Option.some.inj hf).symm
          obtain rfl : va = .app (succV m.cval φ) vx := (Option.some.inj hva).symm
          obtain ⟨hwx, hbx, hLx, hCx⟩ := frame_appArgR hwa hba hLa hCa
          have hrec := ihd h hwx hbx hLx (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl) hCx
            (CtxOkR.of_fvarLeaves_nil hCb.1 (by simp [Expr.fvarLeaves])) hx (denote_natLitV hg d _)
          exact (DefEq.litSuccApp hg hrec.symm).symm
        · exact nomatch hva
      · exact hfall h
    · exact hfall h
  -- 7: a string literal against a `String.ofList` application
  · rename_i st cO usO x
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨-, -, hdc⟩ := denote_strLitCtorR m φ hcl hg d st
      rw [denote_strLit, if_pos hg] at hva
      obtain rfl : va = strLitT m.cval env φ st := (Option.some.inj hva).symm
      obtain ⟨hwc, hbc, hLc, hCc⟩ :=
        frame_strLitCtorR (mode := mode) (cval := m.cval) (φ := φ) st hCa.1
      exact ihd h hwc hbc hLc hwb hbb hLb hCc hCb hdc hvb
    · exact hfall h
  -- 8: a `String.ofList` application against a string literal
  · rename_i cO usO x st
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨-, -, hdc⟩ := denote_strLitCtorR m φ hcl hg d st
      rw [denote_strLit, if_pos hg] at hvb
      obtain rfl : vb = strLitT m.cval env φ st := (Option.some.inj hvb).symm
      obtain ⟨hwc, hbc, hLc, hCc⟩ :=
        frame_strLitCtorR (mode := mode) (cval := m.cval) (φ := φ) st hCb.1
      exact ihd h hwa hba hLa hwc hbc hLc hCa hCc hva hdc
    · exact hfall h
  -- 9: the same de Bruijn level (D1)
  · rename_i i n₁ t₁ j n₂ t₂
    split at h
    · next hij =>
      obtain rfl : i = j := eq_of_beq hij
      rw [denote_fvar] at hva hvb
      obtain rfl : va = .bvar (d - 1 - i) := (Option.some.inj hva).symm
      obtain rfl : vb = .bvar (d - 1 - i) := (Option.some.inj hvb).symm
      exact DefEq.refl
    · exact hfall h
  -- 10: the same constant at level-equivalent instantiations (D1)
  · rename_i n us n' us'
    split at h
    · next hnn =>
      subst hnn
      cases hle : Level.isEquivList us us' with
      | none => rw [hle] at h; exact nomatch h
      | some r =>
        rw [hle] at h
        dsimp only [liftFueled] at h
        cases r with
        | false => exact hfall h
        | true =>
          obtain rfl : va = vb := denote_const_congrR m φ hle hva hvb
          exact DefEq.refl
    · exact hfall h
  -- 11: ∀-congruence (D5)
  · rename_i n₁ ty₁ bd₁ mb₁ n₂ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore mode env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      rw [denote_forallE] at hva hvb
      split at hva
      · exact nomatch hva
      · next A₁ hA₁ =>
        split at hva
        · exact nomatch hva
        · next B₁ hB₁ =>
          split at hvb
          · exact nomatch hvb
          · next A₂ hA₂ =>
            split at hvb
            · exact nomatch hvb
            · next B₂ hB₂ =>
              obtain rfl : va = VExpr.pi A₁ B₁ := (Option.some.inj hva).symm
              obtain rfl : vb = VExpr.pi A₂ B₂ := (Option.some.inj hvb).symm
              have hbd : isDefEqCore mode env fuel (d + 1)
                  (bd₁.instantiate1 (.fvar d n₁ ty₁))
                  (bd₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true := by
                revert h
                cases hbd0 : isDefEqCore mode env fuel (d + 1)
                    (bd₁.instantiate1 (.fvar d n₁ ty₁))
                    (bd₂.instantiate1 (.fvar d n₂ ty₂)) with
                | error err => intro h; exact nomatch h
                | ok rb =>
                  intro h
                  dsimp only at h
                  cases rb with
                  | false => simp [pure, Except.pure] at h
                  | true => rfl
              obtain ⟨hDA, hDB⟩ := binder_congrR m φ hcl ihd hdt hbd
                hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
                (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
                hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
                (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
                hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
                (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
                hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
                (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
                hA₁ hB₁ hA₂ hB₂
              exact DefEq.piCong hDA hDB
  -- 12: λ-congruence (D6)
  · rename_i n₁ ty₁ bd₁ mb₁ n₂ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore mode env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      rw [denote_lam] at hva hvb
      split at hva
      · exact nomatch hva
      · next A₁ hA₁ =>
        split at hva
        · exact nomatch hva
        · next B₁ hB₁ =>
          split at hvb
          · exact nomatch hvb
          · next A₂ hA₂ =>
            split at hvb
            · exact nomatch hvb
            · next B₂ hB₂ =>
              obtain rfl : va = VExpr.lam A₁ B₁ := (Option.some.inj hva).symm
              obtain rfl : vb = VExpr.lam A₂ B₂ := (Option.some.inj hvb).symm
              have hbd : isDefEqCore mode env fuel (d + 1)
                  (bd₁.instantiate1 (.fvar d n₁ ty₁))
                  (bd₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true := by
                revert h
                cases hbd0 : isDefEqCore mode env fuel (d + 1)
                    (bd₁.instantiate1 (.fvar d n₁ ty₁))
                    (bd₂.instantiate1 (.fvar d n₂ ty₂)) with
                | error err => intro h; exact nomatch h
                | ok rb =>
                  intro h
                  dsimp only at h
                  cases rb with
                  | false => simp [pure, Except.pure] at h
                  | true => rfl
              obtain ⟨hDA, hDB⟩ := binder_congrR m φ hcl ihd hdt hbd
                hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
                (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
                hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
                (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
                hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
                (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
                hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
                (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
                hA₁ hB₁ hA₂ hB₂
              exact DefEq.lamCong hDA hDB
  -- 13: the stuck spine congruence (D7)
  · rename_i f₁ a₁ f₂ a₂
    split at h
    · next hlen =>
      cases hhd : isDefEqCore mode env fuel d (Expr.app f₁ a₁).getAppFn
          (Expr.app f₂ a₂).getAppFn with
      | error err => rw [hhd] at h; exact nomatch h
      | ok r =>
      rw [hhd] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        cases hls : defEqListP mode env fuel d (Expr.app f₁ a₁).getAppArgs
            (Expr.app f₂ a₂).getAppArgs with
        | error err => rw [hls] at h; exact nomatch h
        | ok r' =>
        rw [hls] at h
        dsimp only at h
        cases r' with
        | false => exact hfall h
        | true =>
          rw [show Expr.app f₁ a₁ = Expr.mkAppN (Expr.app f₁ a₁).getAppFn
            (Expr.app f₁ a₁).getAppArgs from (Expr.mkAppN_getApp _).symm] at hva
          rw [show Expr.app f₂ a₂ = Expr.mkAppN (Expr.app f₂ a₂).getAppFn
            (Expr.app f₂ a₂).getAppArgs from (Expr.mkAppN_getApp _).symm] at hvb
          obtain ⟨vf₁, vs₁, hvf₁, hsp₁, rfl⟩ := denote_mkAppN_inv hva
          obtain ⟨vf₂, vs₂, hvf₂, hsp₂, rfl⟩ := denote_mkAppN_inv hvb
          refine DefEq.appCong (by rw [hsp₁.length, hsp₂.length, hlen])
            (ihd hhd (Expr.WScoped.getAppFn hwa) (looseBVarsBounded_getAppFn hba)
              (fun l hl => hLa l (fvarLeaves_getAppFn l hl))
              (Expr.WScoped.getAppFn hwb) (looseBVarsBounded_getAppFn hbb)
              (fun l hl => hLb l (fvarLeaves_getAppFn l hl))
              (CtxOkR.of_subset (fun l hl => fvarLeaves_getAppFn l hl) hCa)
              (CtxOkR.of_subset (fun l hl => fvarLeaves_getAppFn l hl) hCb)
              hvf₁ hvf₂)
            (defEqL_of_defEqListR m φ ihd hls (frame_spineR hwa hba hLa hCa)
              (frame_spineR hwb hbb hLb hCb) hsp₁ hsp₂)
    · exact hfall h
  -- 14: the stuck projection congruence (finding 2's `projCong`)
  · rename_i s₁ i₁ e₁ s₂ i₂ e₂
    split at h
    · next hii =>
      obtain rfl : i₁ = i₂ := eq_of_beq hii
      cases hde : isDefEqCore mode env fuel d e₁ e₂ with
      | error err => rw [hde] at h; exact nomatch h
      | ok r =>
      rw [hde] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        rw [denote_proj] at hva hvb
        cases he₁ : denote m.cval env φ d e₁ with
        | none => rw [he₁] at hva; exact nomatch hva
        | some ve₁ =>
        cases he₂ : denote m.cval env φ d e₂ with
        | none => rw [he₂] at hvb; exact nomatch hvb
        | some ve₂ =>
        rw [he₁] at hva
        rw [he₂] at hvb
        dsimp only at hva hvb
        by_cases hlt : i₁ < 2
        · rw [if_pos hlt] at hva hvb
          obtain rfl : va = .proj i₁ ve₁ := (Option.some.inj hva).symm
          obtain rfl : vb = .proj i₁ ve₂ := (Option.some.inj hvb).symm
          simp only [Expr.WScoped] at hwa hwb
          simp only [Expr.looseBVarsBounded] at hba hbb
          exact DefEq.projCong (ihd hde hwa hba
            (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
            hwb hbb (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
            (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa)
            (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb)
            he₁ he₂)
        · rw [if_neg hlt] at hva; exact nomatch hva
    · exact hfall h
  -- 15: one-sided λ on the left (D13)
  · rename_i n₁ ty₁ bd₁ mb₁ hnl
    cases he : etaCertP mode env fuel d n₁ ty₁ bd₁ mb₁ b' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact etaCert_stepR m φ hcl ihw ihd ihi he hwa hba hLa hwb hbb hLb
        hCa hCb hva hvb
    | false => exact hfall h
  -- 16: one-sided λ on the right (D13 + D2)
  · rename_i n₂ ty₂ bd₂ mb₂ hnl
    cases he : etaCertP mode env fuel d n₂ ty₂ bd₂ mb₂ a' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact (etaCert_stepR m φ hcl ihw ihd ihi he hwb hbb hLb hwa hba hLa
        hCb hCa hvb hva).symm
    | false => exact hfall h
  -- 17: distinct stuck heads — only the stuck fallbacks can equate them
  · exact hfall h

end Setlec.SetR
