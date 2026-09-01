import Setlec.SetR.Interp2.EnvS2UNe

/-!
# The second probe: an `EnvS2U` whose stored type **has a binder**

`probeEnvS2U` (`EnvS2UNe.lean`) closed seal 37's vacuity gap, and its
own file records the limit that made it cheap: *the stored type is
sort-shaped, so no binder numeral is computed and `sortOfE` never
runs.*  **A first inhabitant that exercises one field is not one that
exercises the structure.**

This file walks into that.  The stored constant is

    axiom piProbeName : ∀ _ : Sort 0, Sort 0

whose canonical annotation is `.pi 1 1 (.sort 0) (.sort 0)` — and
each of those two numerals is a `sortOfE` run: `inferTypeCore` on the
domain, `whnf` on its output, `Level.eval` on the resulting sort.
`denote2_two_forallE` (`Step2/Whnf.lean`) is the witness that they
succeed, and `sortOfE_two_sort` is where the run actually happens.

## What this buys over the first probe

`mem_type2`'s premise is no longer met at every fuel.  It is `none`
at `0` and at `1` — `denote2_one_forallE`, the very fact that made
`EnvS2.acval_defn`'s original shape false at STOP 2 — and first
succeeds at `2`.  So the field is exercised **through a checker run**,
not past one, which is the whole difference between this probe and
the last.

`memberBlock2_probe` put `Denote2Total`'s wall "exactly one binder
away".  This probe crosses that binder.  It does **not** discharge
`Denote2Total`: what it shows is that the wall is not *at* the first
binder — a `∀` over sorts annotates — and that an `EnvS2U` survives
at a stored type that needs the checker to run.

## What is still not exercised

The domain is a sort, so `sortOfE`'s `inferTypeCore` call lands in the
`.sort` clause and its `whnf` call returns its input.  A stored type
whose domain is a *stored constant* would exercise the `.const`
clause of both, and that needs a second constant in the environment.
Recorded here so the next probe up is named rather than assumed.

## Route note

`EnvS.cons` again (`EnvS2UNe.lean`'s finding), but the valuation now
**moves**: the leaf is the identity λ on `Sort 0`, not the empty type,
because the stored type is a `∀` and its inhabitant must be a
function.  `Installs.of_fresh` allows exactly this — the valuation may
change at the installed name and nowhere else.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta)

universe w

variable (V : Type w) [SetTheory V]

/-! ## The probe environment -/

/-- The probe axiom's name, `.num`-shaped for the same reason
`probeName` is: every reserved name in the tree is `.str`-shaped. -/
def piProbeName : Name := .num .anonymous 1

/-- The stored type: `∀ _ : Sort 0, Sort 0` — the smallest closed `∀`,
and the one `denote2_two_forallE` is stated at. -/
def piProbeTy : Expr :=
  .forallE (.num .anonymous 2) (.sort .zero) (.sort .zero)
    ⟨.default, .never⟩

/-- The probe's stored constant. -/
def piProbeCi : ConstantInfo :=
  .axiomInfo ⟨piProbeName, [], piProbeTy⟩

/-- The probe environment: one stored constant, with a binder in its
type. -/
def piProbeEnv : Env := ⟨[piProbeCi]⟩

/-- The collapse-lane leaf: the identity λ on `Sort 0`. -/
def piProbeCval : TConstVal := fun n _ =>
  if n = piProbeName then .lam (.sort 0) (.bvar 0) else emptyT 0

/-- The annotated leaf: the same λ with its codomain numeral, which
is `1` because the body's type is `Sort 1`. -/
def piProbeAcval : Name → (Name → Nat) → AVExpr := fun n _ =>
  if n = piProbeName then .lam 1 (.sort 0) (.bvar 0)
  else .const .empty [0]

theorem piProbeCval_head (ψ : Name → Nat) :
    piProbeCval piProbeCi.name ψ = VExpr.lam (.sort 0) (.bvar 0) :=
  if_pos rfl

theorem piProbeCval_ne {n : Name} (h : n ≠ piProbeCi.name)
    (ψ : Name → Nat) : piProbeCval n ψ = emptyT 0 :=
  if_neg h

theorem piProbeAcval_head (ψ : Name → Nat) :
    piProbeAcval piProbeCi.name ψ
      = AVExpr.lam 1 (.sort 0) (.bvar 0) :=
  if_pos rfl

theorem piProbeAcval_ne {n : Name} (h : n ≠ piProbeCi.name)
    (ψ : Name → Nat) : piProbeAcval n ψ = .const .empty [0] :=
  if_neg h

theorem piProbeEnv_find_ne {n : Name} (h : n ≠ piProbeName) :
    piProbeEnv.find? n = none := by
  rw [piProbeEnv,
    show (⟨[piProbeCi]⟩ : Env) = ⟨piProbeCi :: Env.empty.consts⟩
      from rfl,
    Env.find?_cons,
    if_neg (show ¬ piProbeCi.name = n from fun hh => h hh.symm)]
  rfl

/-! ## The two `sortOfE` runs, and where the premise first succeeds -/

/-- No sort computes at fuel `0` either — the companion of
`sortOfE_one`, needed because `mem_type2` quantifies every fuel. -/
theorem sortOfE_zero_fuel {μ : CheckMode} {env : Env}
    {φ : Name → Nat} (d : Nat) (e : Expr) :
    sortOfE μ env φ 0 d e = none := by
  rw [sortOfE, Setlec.inferTypeCore_zero]
  simp [throw, throwThe, MonadExceptOf.throw, Except.toOption]

/-- …hence no `∀` annotates at fuel `0`. -/
theorem denote2_zero_forallE {μ : CheckMode} {env : Env}
    {φ : Name → Nat} {acval : Name → (Name → Nat) → AVExpr}
    (d : Nat) (n : Name) (ty body : Expr) (mb : BinderMeta) :
    denote2 μ acval env φ 0 d (.forallE n ty body mb) = none := by
  rw [denote2]
  simp [sortOfE_zero_fuel]

/-- **The stored type's canonical annotation, at every fuel that
computes one.**  The two numerals are the two `sortOfE` runs. -/
theorem piProbe_denote2_ty {μ : CheckMode} {φ : Name → Nat}
    {fuel : Nat} (h : 2 ≤ fuel) :
    denote2 μ piProbeAcval piProbeEnv φ fuel 0 piProbeTy
      = some (.pi 1 1 (.sort 0) (.sort 0)) :=
  denote2_fuelMono h 0 piProbeTy (denote2_two_forallE 0 _ _)

/-- **…and it is the only one.**  Below fuel `2` the premise cannot be
met — `denote2_zero_forallE` and `denote2_one_forallE` — and at or
above it the annotation is fixed by `denote2_fuelMono`.  This is what
makes `mem_type2` a *used* hypothesis at a subject the checker has to
run on. -/
theorem piProbe_denote2_ty_eq {μ : CheckMode} {φ : Name → Nat}
    {fuel : Nat} {ta : AVExpr}
    (h : denote2 μ piProbeAcval piProbeEnv φ fuel 0 piProbeTy
      = some ta) :
    ta = .pi 1 1 (.sort 0) (.sort 0) := by
  match fuel with
  | 0 => rw [piProbeTy, denote2_zero_forallE] at h; exact nomatch h
  | 1 => rw [piProbeTy, denote2_one_forallE] at h; exact nomatch h
  | f + 2 =>
    have := piProbe_denote2_ty (μ := μ) (φ := φ)
      (fuel := f + 2) (by omega)
    rw [this] at h
    exact (Option.some.inj h).symm

/-! ## The leaf's two truthfulness facts -/

theorem piProbe_annotOkV (ρ : Nat → V) :
    AnnotOkV V ρ (.lam (.sort 0) (.bvar 0)) := by
  rw [AnnotOkV_lam]
  exact ⟨by simp, fun _ _ => by simp⟩

theorem piProbe_annotOk2 (ρ : Nat → V) :
    AnnotOk2 V ρ (.lam 1 (.sort 0) (.bvar 0)) := by
  rw [AnnotOk2_lam]
  refine ⟨by simp, fun _ _ => by simp, fun _ => univ 0, ?_, ?_⟩
  · intro x hx
    rw [interp2_sort] at hx
    exact hx
  · intro h; exact nomatch h

/-! ## `CvalAnnot` at the probe — the λ-shape conjunct's ingredients

`CvalAnnot` — carried as `EnvS2.cval_annot` until the cleanup seal
withdrew it, and never on `EnvS2U` for the reason recorded at
`EnvS2U.lean` — has two conjuncts, and at *this* probe neither is
vacuous.
The first needs an `Annotates` derivation for the stored λ, which
carries an `Infer` and a `HasSortC` premise.  The second needs the
converse direction: **every** type the relation infers for the stored
λ must be sorted — and since `Infer`'s type slot is pinned only up to
`DefEq` (`Annot/Validity.lean`, finding A5), that is an *inversion*,
not a computation.

The inversion is stated with a generalized subject, exactly as
`infer_shape_empty` is and for the same reason: `Infer.const`'s
subject is `cval n ψ`, an application, so `cases` at a fixed λ cannot
decide it.  What refutes I3 here is not the empty environment but the
stored name — `piProbe_find_eq` — and that is the difference the
non-empty probe pays for. -/

theorem piProbeCval_at (ψ : Name → Nat) :
    piProbeCval piProbeName ψ = VExpr.lam (.sort 0) (.bvar 0) :=
  piProbeCval_head ψ

theorem piProbeEnv_find_self :
    piProbeEnv.find? piProbeName = some piProbeCi := rfl

/-- The probe environment stores exactly one name, so I3's lookup
premise names it. -/
theorem piProbe_find_eq {n : Name} {ci : ConstantInfo}
    (h : piProbeEnv.find? n = some ci) :
    n = piProbeName ∧ ci = piProbeCi := by
  by_cases hn : n = piProbeName
  · subst hn
    rw [piProbeEnv_find_self] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩
  · rw [piProbeEnv_find_ne hn] at h
    exact nomatch h

/-- The stored type's closed denotation, in the spelling I3's third
premise uses.  `piProbeTy` mentions no level parameter, so the
instantiation is the identity at every `us`. -/
theorem piProbe_denoteClosed_ty (φ : Name → Nat) (us : List Level) :
    denoteClosed piProbeCval piProbeEnv φ
      (piProbeCi.toConstantVal.type.instantiateLevelParams
        piProbeCi.toConstantVal.levelParams us)
      = some (.pi (.sort 0) (.sort 0)) := by
  rw [show piProbeCi.toConstantVal.type.instantiateLevelParams
      piProbeCi.toConstantVal.levelParams us = piProbeTy from rfl,
    denoteClosed, piProbeTy, denote, Expr.instantiate1_sort]
  simp [Setlec.Level.eval]

/-- **I2's inversion at the probe.**  The only clause whose subject is
a `.bvar` is I2 — I3's subject is the stored λ, and the two literal
clauses are guarded off by the environment. -/
theorem piProbe_infer_bvar0 {μ : CheckMode} {φ : Name → Nat}
    {Δ : List VExpr} {A e B : VExpr}
    (h : Infer μ piProbeEnv piProbeCval φ (A :: Δ) e B)
    (he : e = .bvar 0) : B = A.liftN 1 := by
  cases h with
  | bvar hi =>
    injection he with hi0
    subst hi0
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    rfl
  | const hfind =>
    obtain ⟨rfl, rfl⟩ := piProbe_find_eq hfind
    rw [piProbeCval_at] at he
    exact nomatch he
  | litNat hsup => exact absurd hsup (by decide)
  | litStr hsup => exact absurd hsup (by decide)
  | sort | pi | lam | app | proj | letE => exact nomatch he

/-- **The λ-shape conjunct's content.**  Whatever type the relation
infers for the stored λ, it is `Sort 0 → Sort 0`: I7 pins the domain
and reads the codomain off I2, and I3 pins it to the stored type's
denotation.  The two agree, which is what makes the obligation
dischargeable at all. -/
theorem piProbe_infer_lam {μ : CheckMode} {φ : Name → Nat}
    {Δ : List VExpr} {e T : VExpr}
    (h : Infer μ piProbeEnv piProbeCval φ Δ e T)
    (he : e = .lam (.sort 0) (.bvar 0)) :
    T = .pi (.sort 0) (.sort 0) := by
  cases h with
  | lam _ _ hb =>
    injection he with hA hb'
    subst hA
    subst hb'
    rw [piProbe_infer_bvar0 hb rfl]
    rfl
  | const hfind _ hden =>
    obtain ⟨rfl, rfl⟩ := piProbe_find_eq hfind
    rw [piProbe_denoteClosed_ty] at hden
    exact (Option.some.inj hden).symm
  | litNat hsup => exact absurd hsup (by decide)
  | litStr hsup => exact absurd hsup (by decide)
  | sort | bvar | pi | app | proj | letE => exact nomatch he

/-- `Sort 0 → Sort 0` is sorted — the fact the λ-shape conjunct
delivers, by I6 over I1 twice. -/
theorem piProbe_hasSortC_ty {μ : CheckMode} {φ : Name → Nat}
    {Δ : List VExpr} :
    ∃ v, HasSortC μ piProbeEnv piProbeCval φ Δ
      (.pi (.sort 0) (.sort 0)) v :=
  ⟨imax 1 1, HasSortC.ofHasSort
    ⟨.sort (imax 1 1),
      Infer.pi Infer.sort DefEq.refl Infer.sort DefEq.refl,
      DefEq.refl⟩⟩

/-- The stored λ annotates, at every context — the first conjunct's
subject at the installed name.  The codomain numeral `1` is I7's
cached premise: the body's type is `Sort 0`, whose sort is `1`. -/
theorem piProbe_annotates_lam (μ : CheckMode) (φ : Name → Nat)
    (Δ : List VExpr) :
    Annotates μ piProbeEnv piProbeCval φ Δ
      (.lam (.sort 0) (.bvar 0)) (.lam 1 (.sort 0) (.bvar 0)) :=
  .lam (B := .sort 0) (Infer.bvar (A := .sort 0) rfl)
    (HasSortC.ofHasSort ⟨.sort 1, Infer.sort, DefEq.refl⟩)
    .sort .bvar

/-! ## The collapse-lane invariant at the probe -/

/-- The probe's `EnvS`.  The install assembler again, but with a
valuation that moves at the installed name. -/
def piProbeEnvS : EnvS V piProbeEnv := by
  refine EnvS.cons (V := V) (env := Env.empty) (EnvS.empty V)
    (c₀ := piProbeCi) (cval' := piProbeCval)
    (Installs.of_fresh rfl ?_)
    (hwf := ?_)
    (hclosed := fun ψ => by
      rw [piProbeCval_head]
      exact ⟨trivial, Nat.zero_lt_one⟩)
    (hparams := fun _ _ _ => rfl)
    (hannot := fun ψ ρ => ?_)
    (htype := ?_)
    (hdefn := fun _ _ _ heq => nomatch heq)
    (hthm := fun _ _ heq => nomatch heq)
    (hempty := fun heq => absurd heq (by decide))
    (hheadCtors := fun _ _ _ _ heq => nomatch heq)
    (hheadRec := fun _ _ _ _ heq => nomatch heq)
    (hheadEta := ?_)
    (hheadUnit := fun _ _ heq => nomatch heq)
    (hheadProj := fun _ heq => nomatch heq)
    (hheadProjPair := fun _ _ heq => nomatch heq)
    (hheadEq := fun heq => absurd heq (by decide))
    (hheadBasis := fun heq => nomatch heq)
    (hheadNat := fun _ _ _ heq => nomatch heq)
    (hheadDivMod := fun _ _ _ heq => nomatch heq)
    (hheadReduce := fun _ _ hmem => nomatch hmem)
  · -- the valuation moves only at the installed name
    intro n hne
    funext ψ
    rw [piProbeCval_ne hne]
    rfl
  · -- `EnvWF`: the stored type is a closed `∀` of sorts
    refine EnvWF.cons (fun c hc => nomatch hc)
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
    · decide
    · intro _ _ _ heq; exact nomatch heq
    · intro _ _ _ _ heq; exact nomatch heq
    · intro _ _ heq; exact nomatch heq
  · -- `hannot` at the installed name
    rw [piProbeCval_head]
    exact piProbe_annotOkV V ρ
  · -- `mem_type`: the λ inhabits the `piC`
    intro φ
    refine ⟨.pi (.sort 0) (.sort 0), ?_, fun ρ => ⟨?_, ?_⟩⟩
    · rw [show piProbeCi.toConstantVal.type = piProbeTy from rfl,
        denoteClosed, piProbeTy, denote, Expr.instantiate1_sort]
      simp [Setlec.Level.eval]
    · rw [piProbeCval_head, interp_lam, interp_pi, interp_sort]
      exact lamC_mem fun x hx => by rw [interp_bvar]; exact hx
    · rw [AnnotOkV_pi]
      exact ⟨by simp, fun _ _ => by simp⟩
  · -- `hheadEta`: the probe environment stores no inductive
    intro T cvT caps hf _ _ _ _
    by_cases hn : T = piProbeName
    · rw [hn] at hf
      exact nomatch hf
    · rw [show (⟨piProbeCi :: Env.empty.consts⟩ : Env) = piProbeEnv
        from rfl, piProbeEnv_find_ne hn] at hf
      exact nomatch hf

/-- The probe's collapse-lane valuation, read off the assembler. -/
theorem piProbeEnvS_cval : (piProbeEnvS V).cval = piProbeCval := rfl

/-- **`CvalAnnot` at the λ-leaf probe** — the one place in this
campaign where its **λ-shape conjunct is not vacuous**.  Kept as a
standalone fact after the cleanup seal withdrew `EnvS2.cval_annot`:
the content is the inversion below, not the field it once fed.
`EnvS2.empty` and `probeEnvS_cvalAnnot` both discharge
that conjunct by having no λ-shaped stored valuation; here the stored
leaf *is* a λ, so the obligation has to be met: every type the
relation infers for `fun (_ : Sort 0) => _` must be sorted.

It is met, and the two clauses that can infer a type for the stored
leaf agree on it — I7 reads the codomain off I2, I3 reads it off the
stored type's denotation, and both give `Sort 0 → Sort 0`.  That
agreement is not automatic: it is the probe's install contract
(`piProbeCval` inhabits `piProbeTy`) showing up on the relational
side.

Stated standalone for the reason `probeEnvS_cvalAnnot` is: the field
is not on `EnvS2U` yet, and the obstruction is `declStep2_of_axiom`
rather than either probe (`EnvS2U.lean`'s module docstring). -/
theorem piProbeEnvS_cvalAnnot (μ : CheckMode) (φ : Name → Nat) :
    CvalAnnot μ piProbeEnv (piProbeEnvS V).cval φ := by
  rw [piProbeEnvS_cval]
  refine ⟨fun n ψ Δ => ?_, ?_⟩
  · by_cases hn : n = piProbeName
    · subst hn
      rw [piProbeCval_at]
      exact ⟨_, piProbe_annotates_lam μ φ Δ⟩
    · rw [piProbeCval_ne hn]
      exact ⟨.const .empty [0], .const⟩
  · intro n ψ Δ T _ hlam hinf
    by_cases hn : n = piProbeName
    · subst hn
      rw [piProbeCval_at] at hinf
      rw [piProbe_infer_lam hinf rfl]
      exact piProbe_hasSortC_ty
    · rw [piProbeCval_ne hn] at hlam
      exact absurd hlam (by simp [emptyT, VExpr.isLam])

/-- **The conjunct really is non-vacuous here.**  The stored leaf is
λ-shaped, so the second clause's guard fires — the check that
distinguishes "met" from "dodged", and the difference from both
`EnvS2.empty` and the first probe. -/
theorem piProbeCval_isLam (ψ : Name → Nat) :
    (piProbeCval piProbeName ψ).isLam = true := by
  rw [piProbeCval_at]
  rfl

/-! ## The uniqueness-form invariant at the probe -/

/-- **A non-empty `EnvS2U` whose stored type has a binder.**  Every
field is as before *except* `mem_type2`, whose premise now costs the
checker two `sortOfE` runs before it can be met. -/
noncomputable def piProbeEnvS2U : EnvS2U V piProbeEnv where
  base := piProbeEnvS V
  acval := piProbeAcval
  acval_erase := by
    intro n ψ
    rw [piProbeAcval]
    by_cases hn : n = piProbeName
    · rw [if_pos hn, show (piProbeEnvS V).cval = piProbeCval from rfl,
        piProbeCval, if_pos hn]
      rfl
    · rw [if_neg hn, show (piProbeEnvS V).cval = piProbeCval from rfl,
        piProbeCval, if_neg hn]
      rfl
  acval_closed := by
    intro n ψ k
    rw [piProbeAcval]
    by_cases hn : n = piProbeName
    · rw [if_pos hn]
      simp [AVExpr.liftN]
    · rw [if_neg hn]
      rfl
  acval_params := fun _ _ _ _ _ _ => rfl
  acval_ok2 := by
    intro n ψ ρ
    rw [piProbeAcval]
    by_cases hn : n = piProbeName
    · rw [if_pos hn]; exact piProbe_annotOk2 V ρ
    · rw [if_neg hn]; simp
  acval_defn := by
    intro _ _ _ _ _ _ hc
    rcases List.mem_singleton.mp hc with h
    exact nomatch h
  acval_thm := by
    intro _ _ _ _ _ hc
    rcases List.mem_singleton.mp hc with h
    exact nomatch h
  mem_type2 := by
    intro μ φ fuel c hc ta hden ρ
    obtain rfl : c = piProbeCi := List.mem_singleton.mp hc
    obtain rfl : ta = .pi 1 1 (.sort 0) (.sort 0) :=
      piProbe_denote2_ty_eq hden
    rw [piProbeAcval_head, interp2_lam, interp2_pi, interp2_sort]
    exact lamR_mem fun x hx => by rw [interp2_bvar]; exact hx

/-! ## The checks

`sortOfE` really runs, and the field really needs it. -/

/-- **`sortOfE` runs, and this is where.**  The domain's sort numeral
is computed by the checker: `inferTypeCore` on `Sort 0` returns
`Sort 1`, `whnf` returns it unchanged, and `Level.eval` reads `1`.
The first probe never reached this function. -/
theorem piProbe_sortOfE_runs (μ : CheckMode) (φ : Name → Nat)
    (d : Nat) :
    sortOfE μ piProbeEnv φ 2 d (.sort .zero) = some 1 := by
  rw [sortOfE_two_sort]
  simp [Setlec.Level.eval]

/-- **The premise is not met at every fuel** — the difference from the
first probe, and the reason this one exercises the structure.  A
sort-shaped stored type annotates at fuel `0`; a `∀`-shaped one does
not annotate until fuel `2`. -/
theorem piProbe_denote2_ty_none (μ : CheckMode) (φ : Name → Nat) :
    denote2 μ piProbeAcval piProbeEnv φ 1 0 piProbeTy = none := by
  rw [piProbeTy, denote2_one_forallE]

/-- **The gap is closed one binder further out.**  `EnvS2U` is
inhabited at an environment whose stored type the checker must run on,
so `DeclStep2`'s subject is inhabited beyond the sort-shaped case. -/
theorem nonempty_envS2U_piProbe : Nonempty (EnvS2U V piProbeEnv) :=
  ⟨piProbeEnvS2U V⟩

/-- …and the stored type really has a binder. -/
theorem piProbeTy_is_forallE :
    ∃ n ty body mb, piProbeTy = .forallE n ty body mb :=
  ⟨_, _, _, _, rfl⟩

/-! ## The probe as an `EnvS2` — `EnvS2UInImage`'s second witness

The λ-leaf probe lifts too.  Until the cleanup seal this was the more
interesting of the two lifts, because `EnvS2`'s tenth field was met
here by `piProbeEnvS_cvalAnnot`, whose λ-shape conjunct is not
vacuous; with the field withdrawn the lift is field-for-field.  The
two `denote2` fields still agree only because the environment stores
no `defnInfo`/`thmInfo` — *that* is where the residue lives, and no
axiom-only probe can exercise it. -/

/-- The λ-leaf probe's `EnvS2`. -/
noncomputable def piProbeEnvS2 : EnvS2 V piProbeEnv where
  base := (piProbeEnvS2U V).base
  acval := (piProbeEnvS2U V).acval
  acval_erase := (piProbeEnvS2U V).acval_erase
  acval_closed := (piProbeEnvS2U V).acval_closed
  acval_params := (piProbeEnvS2U V).acval_params
  acval_ok2 := (piProbeEnvS2U V).acval_ok2
  acval_defn := by
    intro _ _ _ _ _ _ hc
    rcases List.mem_singleton.mp hc with h
    exact nomatch h
  acval_thm := by
    intro _ _ _ _ _ hc
    rcases List.mem_singleton.mp hc with h
    exact nomatch h
  mem_type2 := (piProbeEnvS2U V).mem_type2

theorem piProbeEnvS2_toU :
    EnvS2.toU V (piProbeEnvS2 V) = piProbeEnvS2U V := rfl

theorem piProbeEnvS2U_inImage : EnvS2UInImage V (piProbeEnvS2U V) :=
  ⟨piProbeEnvS2 V, piProbeEnvS2_toU V⟩

end Setlec.SetR.Interp2
