module

public import ConLeche.Model.Annot.Bit
public import ConLeche.Semantics.ConstsBound

public section

/-!
# The reading RESTRICTS to the environment a term resolves in (task #315 U-18, lane D)

`denoteMeta_env_mono` (`Model/Inductives/BlockRepCross.lean`) carries a
SUCCESSFUL reading forward across an extension.  Its twin here is the
EQUATION: for a term all of whose constants resolve at the smaller
environment, the two readings are the same `Option AnnotTerm` — failure
included.  That is what a caller needs when it has the reading at the
LATER environment and wants to talk about the earlier one, which no
one-directional lemma gives.

The resolve premise is what makes each clause an equation:

* `.const n us` — resolve says `n` is stored at `env₁`, so `hF` hands
  back the SAME `ConstantInfo` at `env₂` and both clauses take the same
  branch with the same level-parameter list;
* the two literal spines — resolve pins exactly the names the guards
  (`natLitSupported`/`strLitSupported`) inspect, so the guards agree as
  BOOLEANS (not merely monotonically: that is why the `LitGuardsMono`
  premise of the monotone twin is not needed here), and the string
  clause's `levelParamsAt` reads agree by `levelParamsAt_congr`;
* binders — `Expr.constsResolve_instantiate1` carries resolution through
  the opening, so the induction hypotheses apply.

**The projection clause is the one place resolution does not reach.**
`Expr.constsResolve` asks that the structure name `s` be stored;
`denoteMeta` reads `env.findProj? s i`, which looks up
`projTableName s` — a DIFFERENT name, about which resolve says nothing.
An extension may therefore install a projection table the smaller
environment lacks and change the clause.  So `hproj` (a table absent at
`env₁` is absent at `env₂`) stays as a premise, exactly as in
`denoteMeta_env_mono`; the `some` direction comes from `hF` alone.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level natLitSupported strLitSupported)

/-- **The reading at the smaller environment IS the reading at the
extension**, for a term that resolves at the smaller one.  An equation,
so it transports failures as well as successes; see the module
docstring for why `hproj` cannot be dropped. -/
theorem denoteMeta_env_restrict {env₁ env₂ : Env}
    {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    (hF : FindPreserved env₁ env₂)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₁.findProj? sn i = none → env₂.findProj? sn i = none) :
    ∀ (d : Nat) (e : Expr), Expr.constsResolve env₁ e = true →
      denoteMeta acval env₂ φ d e = denoteMeta acval env₁ φ d e := by
  have hfind : ∀ n : Name, (env₁.find? n).isSome = true → env₂.find? n = env₁.find? n := by
    intro n hn
    cases hf : env₁.find? n with
    | none => rw [hf] at hn; exact nomatch hn
    | some ci => rw [hF hf]
  have hnatG : (env₁.find? ConLeche.natName).isSome = true →
      (env₁.find? ConLeche.natZeroName).isSome = true →
      (env₁.find? ConLeche.natSuccName).isSome = true →
      natLitSupported env₂ = natLitSupported env₁ := by
    intro h1 h2 h3
    unfold natLitSupported
    rw [hfind _ h1, hfind _ h2, hfind _ h3]
  have hstrG : ∀ s : String, Expr.constsResolve env₁ (.lit (.strVal s)) = true →
      strLitSupported env₂ = strLitSupported env₁ := by
    intro s h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hZ⟩, hS⟩, hStr⟩, hO⟩, hL⟩, hNil⟩, hCons⟩, hC⟩, hCo⟩ := h
    unfold strLitSupported
    rw [hnatG hN hZ hS, hfind _ hStr, hfind _ hO, hfind _ hL, hfind _ hNil,
      hfind _ hCons, hfind _ hC, hfind _ hCo]
  have hprojEq : ∀ (sn : Name) (i : Nat), env₂.findProj? sn i = env₁.findProj? sn i := by
    intro sn i
    cases hf : env₁.findProj? sn i with
    | none => exact hproj sn i hf
    | some entry =>
      obtain ⟨tbl, hf0, hi, rfl⟩ := ConLeche.Env.findProj?_some hf
      exact ConLeche.Env.findProj?_of_table (hF hf0) hi
  intro d e
  induction d, e using denoteMeta.induct (env := env₁) with
  | case1 d u => intro _; rw [denoteMeta, denoteMeta]
  | case2 d idx ty => intro _; rw [denoteMeta, denoteMeta]
  | case3 d n us ci hf hlen =>
    intro _
    rw [denoteMeta, denoteMeta, hF hf, hf]
  | case4 d n us ci hf hlen =>
    intro _
    rw [denoteMeta, denoteMeta, hF hf, hf]
  | case5 d n us hf =>
    intro hcr
    simp [Expr.constsResolve, hf] at hcr
  | case6 d ty body m ihty ihbody =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta, ihty hcr.1,
      ihbody (Expr.constsResolve_instantiate1 hcr.1 0 hcr.2)]
  | case7 d ty body m ihty ihbody =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta, ihty hcr.1,
      ihbody (Expr.constsResolve_instantiate1 hcr.1 0 hcr.2)]
  | case8 d f a ihf iha =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta, ihf hcr.1, iha hcr.2]
  | case9 d ty val body =>
    intro _
    rw [denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta, ihe hcr.2, hprojEq]
  | case11 d n hsup =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta, hnatG hcr.1.1 hcr.1.2 hcr.2, if_pos hsup]
  | case12 d n hsup =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta, hnatG hcr.1.1 hcr.1.2 hcr.2, if_neg hsup]
  | case13 d s hsup =>
    intro hcr
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denoteMeta, denoteMeta, hstrG s hcr, if_pos hsup, if_pos hsup,
      ← levelParamsAt_congr hF hnil, ← levelParamsAt_congr hF hcons]
  | case14 d s hsup =>
    intro hcr
    rw [denoteMeta, denoteMeta, hstrG s hcr, if_neg hsup, if_neg hsup]
  | case15 d x hs hfv hc hpi hlam happ hlet hprj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hprj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

end ConLeche.Model
