import Setlec.Verify.Denote.Shift
import Setlec.TT.Deq
import Setlec.Verify.Subst

/-!
# Denotation commutes with instantiation

The transpose of `interp_substFvarAt` / `interp_beta`
(`Setlec/Model/Subst.lean`), and the bottleneck every interesting
clause of `CheckStepTT` runs through: the checker's `infer` on
`.app f a` returns the *expression* `B.instantiate1 a`, while
`HasType.app` concludes at the *term* `(⟦B⟧).inst ⟦a⟧`, and those have
to agree.

## Where the transpose is nicer than the original

`interp_substFvarAt` contracts the free-variable *valuation* at `p`
(`delV`).  There is no valuation here, so the contraction becomes a de
Bruijn substitution — and the arithmetic lines up without any auxiliary
shifting, which is not obvious in advance:

* at depth `D + 1` the variable `fvar p` denotes `.bvar (D - p)`, so the
  substitution happens at cut `k = D - p`;
* an outer `fvar j` (`j < p`) denotes `.bvar (p-1-j)` at depth `p` and
  `.bvar (D-1-j)` at depth `D`, and `D-1-j = (p-1-j) + (D-p)` — the
  deeper denotation is the shallower one lifted by exactly `D - p`;
* `VExpr.inst e a k` already substitutes `liftN k a`.

So `k = D - p` makes `VExpr.inst`'s built-in lift *be* the depth shift,
and the substituted variable's case is discharged by `denote_lift`
(`Setlec/Verify/Denote/Shift.lean`) with nothing left over.

## Where it is nicer for a second reason

Every binder case below is structural, because `denote` is
(`Setlec/Verify/Denote.lean`, "Why `denote` is structural").  Had a
`let` denoted to its zeta reduct, this proof — like the shift lemma
before it — would need lifting to commute with instantiation, and then
with itself.  It needs neither.
-/

set_option linter.unusedVariables false

namespace Setlec.TTVerify

open Setlec.TT

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- **The substitution lemma.**  Substituting the expression `a` for
`fvar p` corresponds to instantiating the denotation at de Bruijn cut
`D - p`. -/
theorem denote_substFvarAt (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {p : Nat} {a : Expr} {x : VExpr}
    (hwa : Expr.WScoped p a) (hba : a.looseBVarsBounded 0 = true)
    (ha : denote cval env φ p a = some x) :
    ∀ (e : Expr) (D : Nat), p ≤ D → Expr.fvarsBelow (D + 1) e →
      denote cval env φ D (Expr.substFvarAt p a e) =
        (denote cval env φ (D + 1) e).map (VExpr.inst · x (D - p))
  | .bvar i, D, hpD, hfb => by simp [Expr.substFvarAt]
  | .sort u, D, hpD, hfb => by simp [Expr.substFvarAt]
  | .const n us, D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_const]
    split
    · next ci hf =>
      split
      · next hlen =>
        simp only [Option.map_some]
        rw [VExpr.inst_eq_self_of_closed (hcl _ _)]
      · rfl
    · rfl
  | .fvar idx n ty, D, hpD, hfb => by
    have hlt : idx < D + 1 := hfb
    by_cases h1 : idx = p
    · -- the substituted variable: `denote_lift` is exactly the fact
      subst h1
      rw [show Expr.substFvarAt idx a (Expr.fvar idx n ty) = a from by
            simp [Expr.substFvarAt],
        denote_lift (env := env) (φ := φ) hcl hwa.fvarsBelow D hpD, ha]
      simp only [denote_fvar, Option.map_some, VExpr.inst_bvar,
        show D + 1 - 1 - idx = D - idx from by omega]
      simp
    · by_cases h2 : idx > p
      · simp only [Expr.substFvarAt, if_neg h1, if_pos h2, denote_fvar,
          Option.map_some, VExpr.inst_bvar,
          if_pos (show D + 1 - 1 - idx < D - p from by omega)]
        congr 2
        omega
      · simp only [Expr.substFvarAt, if_neg h1, if_neg h2, denote_fvar,
          Option.map_some, VExpr.inst_bvar,
          if_neg (show ¬ D + 1 - 1 - idx < D - p from by omega),
          if_neg (show ¬ D + 1 - 1 - idx = D - p from by omega)]
        congr 2
        omega
  | .app f b, D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_app]
    rw [denote_substFvarAt hcl hwa hba ha f D hpD hfb.1,
      denote_substFvarAt hcl hwa hba ha b D hpD hfb.2]
    cases denote cval env φ (D + 1) f <;>
      cases denote cval env φ (D + 1) b <;> rfl
  | .forallE n ty body m, D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_forallE]
    rw [denote_substFvarAt hcl hwa hba ha ty D hpD hfb.1]
    cases hty : denote cval env φ (D + 1) ty with
    | none => rfl
    | some A =>
      simp only [Option.map_some]
      rw [← Expr.substFvarAt_instantiate1 hpD hba body 0,
        denote_substFvarAt hcl hwa hba ha
          (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1) (by omega)
          (Expr.fvarsBelow_instantiate1 0 hfb.2),
        show D + 1 - p = D - p + 1 from by omega]
      cases denote cval env φ (D + 2)
          (body.instantiate1 (.fvar (D + 1) n ty)) with
      | none => rfl
      | some B => simp only [Option.map_some, VExpr.inst_pi]
  | .lam n ty body m, D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_lam]
    rw [denote_substFvarAt hcl hwa hba ha ty D hpD hfb.1]
    cases hty : denote cval env φ (D + 1) ty with
    | none => rfl
    | some A =>
      simp only [Option.map_some]
      rw [← Expr.substFvarAt_instantiate1 hpD hba body 0,
        denote_substFvarAt hcl hwa hba ha
          (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1) (by omega)
          (Expr.fvarsBelow_instantiate1 0 hfb.2),
        show D + 1 - p = D - p + 1 from by omega]
      cases denote cval env φ (D + 2)
          (body.instantiate1 (.fvar (D + 1) n ty)) with
      | none => rfl
      | some B => simp only [Option.map_some, VExpr.inst_lam]
  | .letE n ty val body, D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_letE]
    rw [denote_substFvarAt hcl hwa hba ha ty D hpD hfb.1,
      denote_substFvarAt hcl hwa hba ha val D hpD hfb.2.1]
    cases hty : denote cval env φ (D + 1) ty with
    | none => simp
    | some A =>
      cases hval : denote cval env φ (D + 1) val with
      | none => simp
      | some xv =>
        simp only [Option.map_some]
        rw [← Expr.substFvarAt_instantiate1 hpD hba body 0,
          denote_substFvarAt hcl hwa hba ha
            (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1) (by omega)
            (Expr.fvarsBelow_instantiate1 0 hfb.2.2),
          show D + 1 - p = D - p + 1 from by omega]
        cases denote cval env φ (D + 2)
            (body.instantiate1 (.fvar (D + 1) n ty)) with
        | none => rfl
        | some B => simp only [Option.map_some, VExpr.inst_letE]
  | .proj s i e, D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_proj]
    rw [denote_substFvarAt hcl hwa hba ha e D hpD hfb]
    cases denote cval env φ (D + 1) e with
    | none => rfl
    | some ve =>
      simp only [Option.map_some]
      split
      · simp only [Option.map_some, VExpr.inst_proj]
      · rfl
  | .lit (.natVal k), D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_natLit]
    split
    · simp only [Option.map_some]
      rw [VExpr.inst_eq_self_of_closed
        (natLitT_closed (hcl _ _) (hcl _ _) k)]
    · rfl
  | .lit (.strVal s), D, hpD, hfb => by
    simp only [Expr.substFvarAt, denote_strLit]
    split
    · simp only [Option.map_some]
      rw [VExpr.inst_eq_self_of_closed (strLitT_closed hcl s)]
    · rfl
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- **Beta, denotation side** — the form the reduction clauses consume:
opening a binder body with the argument directly is opening it with a
fresh variable and then instantiating.  Transpose of `interp_beta`. -/
theorem denote_beta (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {d : Nat} {n : Name} {ty body a : Expr} {x : VExpr}
    (hfb : Expr.fvarsBelow d body) (hwa : Expr.WScoped d a)
    (hba : a.looseBVarsBounded 0 = true)
    (ha : denote cval env φ d a = some x) (k : Nat) :
    denote cval env φ d (body.instantiate1 a k) =
      (denote cval env φ (d + 1)
        (body.instantiate1 (.fvar d n ty) k)).map (VExpr.inst · x 0) := by
  have h := denote_substFvarAt (p := d) hcl hwa hba ha
    (body.instantiate1 (.fvar d n ty) k) d (Nat.le_refl d)
    (Expr.fvarsBelow_instantiate1 k hfb)
  rw [Expr.substFvarAt_instantiate1_self body k hfb, Nat.sub_self] at h
  exact h

/-! ## The beta step

The reduction the certificate-tax story is about
(`Setlec/TTVerify/DESIGN.md` §6), assembled: the checker's `whnfCore`
fires a redex `(fun (_ : ty) => body) a` to `body.instantiate1 a`, and
this is that step's whole content on the bridge side.

Note where each premise comes from, because it is the argument of §6 in
mechanized form:

* `ha` and `hlam` are definedness, from the inference claim;
* **`hx : HasType Δ x A` is the beta certificate.**  The checker infers
  the argument's type and compares it definitionally with the λ's
  annotation; the inference and defeq claims turn that into
  `⊢ x : ⟦ta⟧` and `Deq Δ ⟦ta⟧ A`, and `Deq.conv` closes it.  It is
  *not* obtainable from the ambient typing of the redex — inversion
  gives the argument at the ambient domain `A₀`, and bridging `A₀` to
  `A` needs Pi-domain-injectivity, which `propext` **refutes** — so the
  certificate is not merely the current supplier, it is the only one
  any sound rule set can have (§6).

So this lemma is where "the beta certificate is load-bearing for the
bridge" stops being a claim and becomes a hypothesis with exactly one
supplier. -/

/-- **The beta step.**  Firing a certified redex preserves the
denotation up to a derivable equation, and the reduct denotes. -/
theorem denote_beta_step (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {d : Nat} {Δ : List VExpr} {n : Name} {ty body a : Expr}
    {m : BinderMeta} {A B x : VExpr}
    (hfb : Expr.fvarsBelow d body) (hwa : Expr.WScoped d a)
    (hba : a.looseBVarsBounded 0 = true)
    (hlam : denote cval env φ d (.lam n ty body m) = some (.lam A B))
    (ha : denote cval env φ d a = some x)
    (hx : HasType Δ x A) :
    denote cval env φ d (body.instantiate1 a) = some (B.inst x) ∧
      Deq Δ (.app (.lam A B) x) (B.inst x) := by
  rw [denote_lam] at hlam
  split at hlam
  · exact nomatch hlam
  · next A' hA =>
    split at hlam
    · exact nomatch hlam
    · next B' hB =>
      obtain ⟨rfl, rfl⟩ : A' = A ∧ B' = B := by
        simpa [VExpr.lam.injEq] using hlam
      -- the `eqE` type slot is inert, so any annotation will do
      refine ⟨?_, ⟨.sort 0, HasType.beta (T := .sort 0) hx⟩⟩
      rw [denote_beta (n := n) (ty := ty) hcl hfb hwa hba ha 0, hB]
      rfl

/-! ## Name insensitivity

The standard-axiom pins compare stored types to pinned ones **up to
binder names** (`ConstantVal.matchesPin` uses `Expr.eraseNames`), so
every inhabitation key needs the denotation to ignore exactly what the
pin ignores.  It does — `denote` reads a binder's name only to build the
`fvar` it opens with, and an `fvar` denotes to its de Bruijn index.

Transpose of `interp_erasedEq` (`Setlec/Model/InterpLemmas.lean`), and
another §8.4 reading: **the pin's tolerance and the denotation's
blindness are the same set of syntax**, which is why a `matchesPin` hit
is usable at all. -/

/-- Erasure-equal expressions denote equally. -/
theorem denote_erasedEq {cval : TConstVal} {env : Env} {φ : Name → Nat} :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ →
      ∀ d : Nat, denote cval env φ d e₁ = denote cval env φ d e₂
  | .bvar i, e₂, he, d => by
    match e₂, he with
    | .bvar j, he => obtain rfl : i = j := he; rfl
  | .fvar i n ty, e₂, he, d => by
    match e₂, he with
    | .fvar j n' ty', he =>
      obtain rfl : i = j := he
      simp [denote_fvar]
  | .sort u, e₂, he, d => by
    match e₂, he with
    | .sort u', he => obtain rfl : u = u' := he; rfl
  | .const n us, e₂, he, d => by
    match e₂, he with
    | .const n' us', he =>
      obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := he
      rfl
  | .app f a, e₂, he, d => by
    match e₂, he with
    | .app g b, he =>
      obtain ⟨h1, h2⟩ : Expr.ErasedEq f g ∧ Expr.ErasedEq a b := he
      simp only [denote_app, denote_erasedEq h1 d, denote_erasedEq h2 d]
  | .forallE n ty body m, e₂, he, d => by
    match e₂, he with
    | .forallE n' ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ :
          m = m' ∧ Expr.ErasedEq ty ty' ∧ Expr.ErasedEq body body' := he
      simp only [denote_forallE, denote_erasedEq h1 d,
        denote_erasedEq (Expr.ErasedEq.instantiate1 h2
          (show Expr.ErasedEq (.fvar d n ty) (.fvar d n' ty') from rfl))
          (d + 1)]
  | .lam n ty body m, e₂, he, d => by
    match e₂, he with
    | .lam n' ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ :
          m = m' ∧ Expr.ErasedEq ty ty' ∧ Expr.ErasedEq body body' := he
      simp only [denote_lam, denote_erasedEq h1 d,
        denote_erasedEq (Expr.ErasedEq.instantiate1 h2
          (show Expr.ErasedEq (.fvar d n ty) (.fvar d n' ty') from rfl))
          (d + 1)]
  | .letE n ty vl body, e₂, he, d => by
    match e₂, he with
    | .letE n' ty' vl' body', he =>
      obtain ⟨h1, h2, h3⟩ : Expr.ErasedEq ty ty' ∧ Expr.ErasedEq vl vl' ∧
        Expr.ErasedEq body body' := he
      simp only [denote_letE, denote_erasedEq h1 d, denote_erasedEq h2 d,
        denote_erasedEq (Expr.ErasedEq.instantiate1 h3
          (show Expr.ErasedEq (.fvar d n ty) (.fvar d n' ty') from rfl))
          (d + 1)]
  | .lit l, e₂, he, d => by
    match e₂, he with
    | .lit l', he => obtain rfl : l = l' := he; rfl
  | .proj sn i pe, e₂, he, d => by
    match e₂, he with
    | .proj sn' i' pe', he =>
      obtain ⟨rfl, rfl, h⟩ :
          sn = sn' ∧ i = i' ∧ Expr.ErasedEq pe pe' := he
      simp only [denote_proj, denote_erasedEq h d]
termination_by e₁ => e₁.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Name erasure only changes what `ErasedEq` ignores.  A duplicate of
`Setlec/Model/StdAxioms.lean`'s lemma of the same name; `V`-free, and
one more member of the misfiled class named at `EtaFamilyStoredT`. -/
theorem erasedEq_of_eraseNames :
    ∀ {a b : Expr}, a.eraseNames = b.eraseNames → Expr.ErasedEq a b
  | .bvar _, b, h => by
    match b, h with
    | .bvar _, h =>
      simp only [Expr.eraseNames, Expr.bvar.injEq] at h
      exact h
  | .fvar _ _ tya, b, h => by
    match b, h with
    | .fvar _ _ tyb, h =>
      simp only [Expr.eraseNames, Expr.fvar.injEq] at h
      exact h.1
  | .sort _, b, h => by
    match b, h with
    | .sort _, h =>
      simp only [Expr.eraseNames, Expr.sort.injEq] at h
      exact h
  | .const _ _, b, h => by
    match b, h with
    | .const _ _, h =>
      simp only [Expr.eraseNames, Expr.const.injEq] at h
      exact h
  | .app fa aa, b, h => by
    match b, h with
    | .app fb ab, h =>
      simp only [Expr.eraseNames, Expr.app.injEq] at h
      exact ⟨erasedEq_of_eraseNames h.1, erasedEq_of_eraseNames h.2⟩
  | .lam _ tya ba ma, b, h => by
    match b, h with
    | .lam _ tyb bb mb, h =>
      simp only [Expr.eraseNames, Expr.lam.injEq] at h
      exact ⟨h.2.2.2, erasedEq_of_eraseNames h.2.1,
        erasedEq_of_eraseNames h.2.2.1⟩
  | .forallE _ tya ba ma, b, h => by
    match b, h with
    | .forallE _ tyb bb mb, h =>
      simp only [Expr.eraseNames, Expr.forallE.injEq] at h
      exact ⟨h.2.2.2, erasedEq_of_eraseNames h.2.1,
        erasedEq_of_eraseNames h.2.2.1⟩
  | .letE _ tya va ba, b, h => by
    match b, h with
    | .letE _ tyb vb bb, h =>
      simp only [Expr.eraseNames, Expr.letE.injEq] at h
      exact ⟨erasedEq_of_eraseNames h.2.1, erasedEq_of_eraseNames h.2.2.1,
        erasedEq_of_eraseNames h.2.2.2⟩
  | .lit _, b, h => by
    match b, h with
    | .lit _, h =>
      simp only [Expr.eraseNames, Expr.lit.injEq] at h
      exact h
  | .proj _ _ ea, b, h => by
    match b, h with
    | .proj _ _ eb, h =>
      simp only [Expr.eraseNames, Expr.proj.injEq] at h
      exact ⟨h.1, h.2.1, erasedEq_of_eraseNames h.2.2⟩

/-- A `matchesPin` hit lets a stored type be denoted on the pin. -/
theorem denote_matchesPin {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {cv pin : ConstantVal} (h : ConstantVal.matchesPin cv pin = true)
    (d : Nat) :
    denote cval env φ d cv.type = denote cval env φ d pin.type := by
  simp only [ConstantVal.matchesPin, Bool.and_eq_true, beq_iff_eq] at h
  exact denote_erasedEq (erasedEq_of_eraseNames h.2) d

end Setlec.TTVerify
