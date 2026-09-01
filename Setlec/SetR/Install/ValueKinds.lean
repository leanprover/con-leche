import Setlec.SetR.Install.Value

/-!
# The three value kinds: `theorem`, `opaque`, `def` (task #148, T5)

The per-kind extension lemmas, consuming `DeclR`'s packs (T2's
statements) and concluding the `EnvS` extension through
`extendValueS`.  Transposes of `declThmTT`/`declOpaqueTT`/`declDefnTT`
minus their checker-inversion halves — the bridge owns those; here the
premises arrive relation-shaped.

The structural-`Nat` recurrence clause is discharged **inline** in the
`def` case: `NatEqsR` already carries the substituted equations'
denotations and `DefEq` derivations, so the discharge is
`denote_substConst0` (moving the denotation across the install) plus
`DefEq.sound` (reading the interp equality off, at a two-entry `Sat`
built from the closed stored `Nat`'s interpretation).  The div/mod and
compiler-trust clauses enter through their stated obligations
(`DivModPinS`, `ReducePinS`).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## Shared syntactic plumbing -/

/-- The annotate outputs' syntactic facts, packaged: no fvars, bounded,
from the annotate run and the input's own guards. -/
theorem annotate_syntax {μ : CheckMode} {F : Nat} {env : Env} {e e' : Expr}
    (hann : annotateCore μ env F 0 e = .ok e')
    (hef : e.hasFvar = false) (heb : e.looseBVarsBounded 0 = true) :
    e'.hasFvar = false ∧ e'.looseBVarsBounded 0 = true :=
  ⟨Expr.not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F e hann
        (Expr.WScoped.of_not_hasFvar hef)).fvarsBelow),
    annotateCore_looseBVars F e hann heb⟩

/-- Both sides of every structural-`Nat` recurrence are in the shallow
fragment (`substConst0` is faithful on them): the equations are
application spines over constants and two free variables, whatever the
operation. -/
theorem natOpEquations_shallow (d : Nat) (c : Name) :
    ∀ eq ∈ natOpEquations d c,
      shallowE eq.1 = true ∧ shallowE eq.2 = true := by
  intro eq hq
  simp only [natOpEquations] at hq
  repeat' split at hq
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  all_goals
    first
    | (rcases hq with rfl | rfl <;> simp [shallowE])
    | (rcases hq with rfl | rfl | rfl <;> simp [shallowE])
    | (rcases hq with rfl | rfl | rfl | rfl <;> simp [shallowE])

/-- A two-entry `Nat` context is satisfied by any two members of the
closed entry's interpretation. -/
theorem sat_two {A : VExpr} (hA : VExpr.Closed A) {ρ : Nat → V} {x y : V}
    (hx : x ∈ˢ interp V ρ A) (hy : y ∈ˢ interp V ρ A) :
    Sat V [A, A] (cons V y (cons V x ρ)) := by
  intro i A' hi
  match i with
  | 0 =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    rw [interp_closed V hA _ ρ]
    exact hy
  | 1 =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hi
    subst hi
    rw [interp_closed V hA _ ρ]
    exact hx
  | n + 2 =>
    simp at hi

/-! ## `theorem` -/

/-- A checked `theorem` extends the invariant, **with the extension's
valuation agreement exposed** — see `extendValueS`'s docstring for why
`Nonempty` alone is not usable one tier up. -/
theorem declThmS {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {cv : ConstantVal} {value : Expr} (m : EnvS V env)
    (h : DeclThmR μ F env m.cval cv value env₂) :
    ∃ m' : EnvS V env₂, ∀ n, n ≠ cv.name → m.cval n = m'.cval n := by
  -- the `-` is task #161 P4 H1's added prop-check run triple, which
  -- this v1 install does not spend (the semantic `hprop` is what the
  -- `EnvS` field wants); the P tier reads it off `DeclThmR` directly.
  obtain ⟨type', value', hcv, -, hprop, hvfr, rfl⟩ := h
  obtain ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr, hfrontT⟩ :=
    hcv
  obtain ⟨hvlb, hvhf, hannv, hvp, hvr, hfrontV⟩ := hvfr
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  have hfresh : env.find? cv.name = none := Option.isNone_iff_eq_none.mp hfind
  have hwfc : EnvWF ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value' ::
      env.consts⟩ := by
    refine EnvWF.cons m.wf ⟨htf', htp, Expr.constsResolve_mono htr, hbt',
      ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq
      injection heq with h1 h2
      subst h1; subst h2
      exact ⟨hvf', hvp, Expr.constsResolve_mono hvr, hbv'⟩
  refine Exists.imp (fun m' h => h.1)
    (extendValueS m (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩
      value') rfl rfl hfresh hwfc hvf' hbv' ?_ ?_
    (fun _ _ _ heq => nomatch heq)
    (fun _ value2 heq => by injection heq with _ h2; exact h2.symm)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ _ heq => nomatch heq) hres
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq))
  · intro ψ
    obtain ⟨Vv, Tv, hVv, hTv, hlaw⟩ :=
      valueKeyS m ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
        hfrontT⟩ ⟨hvlb, hvhf, hannv, hvp, hvr, hfrontV⟩ ψ
    exact ⟨Vv, Tv, hVv, hTv, hlaw⟩
  · intro φ₁ φ₂ hp
    exact denote_params_ext m.val_params hp 0 value' hvp

/-! ## `opaque` -/

/-- A checked `opaque` extends the invariant, given the compiler-trust
obligation; the extension's valuation agreement is exposed. -/
theorem declOpaqueS (hrp : ReducePinS V) {μ : CheckMode} {F : Nat}
    {env env₂ : Env} {cv : ConstantVal} {value : Expr} (m : EnvS V env)
    (h : DeclOpaqueR μ F env m.cval cv value env₂) :
    ∃ m' : EnvS V env₂,
      (∀ n, n ≠ cv.name → m.cval n = m'.cval n) ∧
      ∃ value', annotateCore μ env F 0 value = .ok value' ∧
        ∀ ψ : Name → Nat,
          denoteClosed m.cval env ψ value' = some (m'.cval cv.name ψ) := by
  obtain ⟨type', value', hcv, hvfr, rfl, hred⟩ := h
  obtain ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr, hfrontT⟩ :=
    hcv
  obtain ⟨hvlb, hvhf, hannv, hvp, hvr, hfrontV⟩ := hvfr
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  have hfresh : env.find? cv.name = none := Option.isNone_iff_eq_none.mp hfind
  have hwfc : EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts⟩ := by
    refine EnvWF.cons m.wf ⟨htf', htp, Expr.constsResolve_mono htr, hbt',
      ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq; exact nomatch heq
  refine Exists.imp (fun m' hh => ⟨hh.1, value', hannv, hh.2⟩)
    (extendValueS m (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (value := value') rfl rfl hfresh hwfc hvf' hbv' ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ _ heq => nomatch heq) hres
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ heq => nomatch heq) ?_)
  · intro ψ
    obtain ⟨Vv, Tv, hVv, hTv, hlaw⟩ :=
      valueKeyS m ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
        hfrontT⟩ ⟨hvlb, hvhf, hannv, hvp, hvr, hfrontV⟩ ψ
    exact ⟨Vv, Tv, hVv, hTv, hlaw⟩
  · intro φ₁ φ₂ hp
    exact denote_params_ext m.val_params hp 0 value' hvp
  · -- the compiler-trust identity, via the obligation
    intro cv2 heq hmem hpin
    have hname : (ConstantInfo.axiomInfo ⟨cv.name, cv.levelParams,
        type'⟩).name = cv.name := rfl
    obtain rfl : cv2 = ⟨cv.name, cv.levelParams, type'⟩ := by
      injection heq with h1
      exact h1.symm
    exact hrp m (hmem : cv.name ∈ reduceOpNames) hfresh
      ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr, hfrontT⟩
      ⟨hvlb, hvhf, hannv, hvp, hvr, hfrontV⟩
      (hred (List.contains_iff_mem.mpr hmem)) hpin

/-! ## `def` -/

/-- A checked `def` extends the invariant, given the div/mod
obligation; the structural-`Nat` recurrence clause is discharged
inline, and the extension's valuation agreement is exposed. -/
theorem declDefnS (hdm : DivModPinS V) {μ : CheckMode} {F : Nat}
    {env env₂ : Env} {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint} (m : EnvS V env)
    (h : DeclDefnR μ F env m.cval cv value hint env₂) :
    ∃ m' : EnvS V env₂, ∀ n, n ≠ cv.name → m.cval n = m'.cval n := by
  obtain ⟨type', value', hcv, hvfr, rfl, hnatc, hdmc⟩ := h
  obtain ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr, hfrontT⟩ :=
    hcv
  obtain ⟨hvlb, hvhf, hannv, hvp, hvr, hfrontV⟩ := hvfr
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  have hfresh : env.find? cv.name = none := Option.isNone_iff_eq_none.mp hfind
  have hwfc : EnvWF ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value'
      hint :: env.consts⟩ := by
    refine EnvWF.cons m.wf ⟨htf', htp, Expr.constsResolve_mono htr, hbt',
      ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq
      injection heq with h1 h2 h3
      subst h1; subst h2; subst h3
      exact ⟨hvf', hvp, Expr.constsResolve_mono hvr, hbv'⟩
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq; exact nomatch heq
  refine Exists.imp (fun m' h => h.1)
    (extendValueS m (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩
      value' hint) rfl rfl hfresh hwfc hvf' hbv' ?_ ?_
    (fun _ value2 _ heq => by injection heq with _ h2 _; exact h2.symm)
    (fun _ _ heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ _ heq => nomatch heq) hres
    ?_ ?_ (fun _ heq => nomatch heq))
  · intro ψ
    obtain ⟨Vv, Tv, hVv, hTv, hlaw⟩ :=
      valueKeyS m ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
        hfrontT⟩ ⟨hvlb, hvhf, hannv, hvp, hvr, hfrontV⟩ ψ
    exact ⟨Vv, Tv, hVv, hTv, hlaw⟩
  · intro φ₁ φ₂ hp
    exact denote_params_ext m.val_params hp 0 value' hvp
  · -- the structural-`Nat` recurrences, inline
    intro cv2 v2 hint2 heq hmem
    obtain ⟨hg2, hdeps, hne⟩ := hnatc (List.contains_iff_mem.mpr hmem)
    refine ⟨hg2, ?_⟩
    -- the operation is stored level-monomorphically (it is its own
    -- dependency, and the dependency check pins the levels)
    have hmem7 : cv.name ∈ natOpNames := hmem
    simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false]
      at hmem7
    have hself : cv.name ∈ natOpDeps cv.name := by
      rcases hmem7 with h | h | h | h | h | h | h <;> rw [h] <;> decide
    have hnatne : natName ≠ cv.name := by
      rcases hmem7 with h | h | h | h | h | h | h <;> rw [h] <;> decide
    have hlp : cv.levelParams = [] := by
      rw [List.all_eq_true] at hdeps
      have hd := hdeps cv.name (by simpa using hself)
      unfold natOpStoredOk at hd
      rw [show (⟨ConstantInfo.defnInfo ⟨cv.name, cv.levelParams, type'⟩
            value' hint :: env.consts⟩ : Env).find? cv.name
          = some (.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
          from by rw [Env.find?_cons]; exact if_pos rfl] at hd
      simp only [Bool.and_eq_true] at hd
      simpa [List.isEmpty_iff] using hd.1
    intro φ eq hq
    obtain ⟨L, R, hL, hR, hD⟩ := hne _ (List.mem_map.mpr ⟨eq, hq, rfl⟩) φ
    obtain ⟨Vv, -, hVv, -, -⟩ := valueKeyS m
      ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr, hfrontT⟩
      ⟨hvlb, hvhf, hannv, hvp, hvr, hfrontV⟩ φ
    have hsub := denote_substConst0 m.cval_closed
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (c := cv.name) φ rfl hfresh
      (show (ConstantInfo.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value'
        hint).toConstantVal.levelParams = [] from hlp) hVv hvf' hbv' 2
    obtain ⟨hs1, hs2⟩ := natOpEquations_shallow 0 cv.name eq hq
    refine ⟨L, R, by rw [hsub _ hs1]; exact hL,
      by rw [hsub _ hs2]; exact hR, ?_⟩
    intro ρ x y hx hy
    rw [show cvalAt m.cval env cv.name value' natName = m.cval natName
      from cvalAt_ne hnatne] at hx hy
    have hcl : VExpr.Closed (m.cval natName (Level.substFn φ [] [])) :=
      m.cval_closed _ _
    exact DefEq.sound (m.toHyp φ) hD (cons V y (cons V x ρ))
      (sat_two hcl hx hy)
  · -- the WF-recursive recurrences, via the obligation
    intro cv2 v2 hint2 heq hmem
    obtain ⟨h1, h2, h3⟩ : cv2 = ⟨cv.name, cv.levelParams, type'⟩ ∧
        v2 = value' ∧ hint2 = hint := by
      injection heq with a b c
      exact ⟨a.symm, b.symm, c.symm⟩
    exact hdm m (hmem : cv.name ∈ natDivModNames) hfresh
      ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr, hfrontT⟩
      ⟨hvlb, hvhf, hannv, hvp, hvr, hfrontV⟩
      (hdmc (List.contains_iff_mem.mpr hmem))

end Setlec.SetR
