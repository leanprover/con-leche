import Setlec.SetR.Interp2.EnvS2UPi
import Setlec.SetR.Interp2.Denote2Extend

/-!
# The third probe: an `EnvS2U` that stores a **definition**

Both earlier probes (`EnvS2UNe.lean`, `EnvS2UPi.lean`) lift to an
`EnvS2` on the nose, and both files record why that is not the good
news it looks like: **neither environment stores a `defnInfo` or a
`thmInfo`**, so the two `denote2` fields — the only place `EnvS2` and
`EnvS2U` differ in content — agree *vacuously*.  No axiom-only probe
can exercise `EnvS2UInImage`'s residue.

This file stores a definition, so `acval_defn` has content, and then
asks the question the probe exists for: **does it still lift?**

Two probes, because the contrast is the finding:

* `defProbe` — `def _ : Sort 1 := Sort 0`.  The value is binder-free,
  so its canonical annotation costs no checker run and `acval_defn`'s
  premise is met at **every** fuel.
* `lamDef` — `def _ : (∀ _ : Sort 0, Sort 1) := fun _ : Sort 0 =>
  Sort 0`.  The value is a **λ**, so `denote2_one_lam` — the fact that
  refuted `EnvS2.acval_defn`'s original shape — makes the premise
  unmeetable below fuel `2`, and the annotation exists only through a
  `lamSortE` run.

**The verdict is that both lift**, and the general reason is isolated
from the probes as `envS2UInImage_iff`: `EnvS2UInImage`'s residue is
`CvalAnnot` plus annotation-**existence** at the stored bodies, and
nothing else — uniqueness supplies the identification for free.  So a
stored `defnInfo` does not part uniqueness from existence, and neither
does a λ-bodied one; only a body that annotates at **no** fuel would.
The closing section records why this file did not exhibit such a body.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint BinderMeta)

universe w

variable (V : Type w) [SetTheory V]

/-! ## The probe environment: `def defProbeName : Sort 1 := Sort 0` -/

/-- The probe definition's name, `.num`-shaped for the reason
`probeName` is: every reserved name in the tree is `.str`-shaped. -/
def defProbeName : Name := .num .anonymous 3

/-- The stored type, `Sort 1`. -/
def defProbeTy : Expr := .sort (.succ .zero)

/-- The stored **value**, `Sort 0` — binder-free, so its canonical
annotation costs no sort computation. -/
def defProbeVal : Expr := .sort .zero

/-- The probe's stored constant — a `defnInfo`, which is the whole
point. -/
def defProbeCi : ConstantInfo :=
  .defnInfo ⟨defProbeName, [], defProbeTy⟩ defProbeVal (.regular 0)

/-- The probe environment: one stored **definition**. -/
def defProbeEnv : Env := ⟨[defProbeCi]⟩

/-- The collapse-lane leaf: the value's own denotation, as
`EnvS.defn_eq` demands. -/
def defProbeCval : TConstVal := fun n _ =>
  if n = defProbeName then .sort 0 else emptyT 0

/-- The annotated leaf.  It is **not** a free choice: `acval_defn`
forces it to be the value's canonical annotation. -/
def defProbeAcval : Name → (Name → Nat) → AVExpr := fun n _ =>
  if n = defProbeName then .sort 0 else .const .empty [0]

theorem defProbeCi_name : defProbeCi.name = defProbeName := rfl

theorem defProbeCval_head (ψ : Name → Nat) :
    defProbeCval defProbeCi.name ψ = VExpr.sort 0 := if_pos rfl

theorem defProbeCval_at (ψ : Name → Nat) :
    defProbeCval defProbeName ψ = VExpr.sort 0 := if_pos rfl

theorem defProbeCval_ne {n : Name} (h : n ≠ defProbeName)
    (ψ : Name → Nat) : defProbeCval n ψ = emptyT 0 := if_neg h

theorem defProbeAcval_head (ψ : Name → Nat) :
    defProbeAcval defProbeCi.name ψ = AVExpr.sort 0 := if_pos rfl

theorem defProbeAcval_at (ψ : Name → Nat) :
    defProbeAcval defProbeName ψ = AVExpr.sort 0 := if_pos rfl

theorem defProbeAcval_ne {n : Name} (h : n ≠ defProbeName)
    (ψ : Name → Nat) : defProbeAcval n ψ = .const .empty [0] :=
  if_neg h

theorem defProbeEnv_find_ne {n : Name} (h : n ≠ defProbeName) :
    defProbeEnv.find? n = none := by
  rw [defProbeEnv,
    show (⟨[defProbeCi]⟩ : Env) = ⟨defProbeCi :: Env.empty.consts⟩
      from rfl,
    Env.find?_cons,
    if_neg (show ¬ defProbeCi.name = n from fun hh => h hh.symm)]
  rfl

/-- The stored constant, inverted: the environment holds exactly one
declaration and it is the probe's definition. -/
theorem defProbe_defn_inv {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint}
    (h : ConstantInfo.defnInfo cv value hint = defProbeCi) :
    cv = ⟨defProbeName, [], defProbeTy⟩ ∧ value = defProbeVal := by
  rw [defProbeCi] at h
  injection h with h1 h2 _
  exact ⟨h1, h2⟩

/-! ## The collapse-lane invariant at the probe -/

/-- The probe's `EnvS`.  The install assembler once more; the two
clauses an axiom install never reaches — `hdefn` and `EnvWF`'s value
conjunct — carry content here. -/
def defProbeEnvS : EnvS V defProbeEnv := by
  refine EnvS.cons (V := V) (env := Env.empty) (EnvS.empty V)
    (c₀ := defProbeCi) (cval' := defProbeCval)
    (Installs.of_fresh rfl ?_)
    (hwf := ?_)
    (hclosed := fun ψ => by rw [defProbeCval_head]; trivial)
    (hparams := fun _ _ _ => rfl)
    (hannot := fun ψ ρ => by rw [defProbeCval_head]; trivial)
    (htype := ?_)
    (hdefn := ?_)
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
    (hheadNat := fun _ _ _ _ hmem => absurd hmem (by decide))
    (hheadDivMod := fun _ _ _ _ hmem => absurd hmem (by decide))
    (hheadReduce := fun _ _ hmem => nomatch hmem)
  · -- the valuation moves only at the installed name
    intro n hne
    funext ψ
    rw [defProbeCval_ne hne]
    rfl
  · -- `EnvWF`: type and value are both closed sorts
    refine EnvWF.cons (fun c hc => nomatch hc)
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
    · decide
    · intro cv value hint heq
      obtain ⟨rfl, rfl⟩ := defProbe_defn_inv heq.symm
      exact ⟨by decide, by decide, by decide, by decide⟩
    · intro _ _ _ _ heq; exact nomatch heq
    · intro _ _ heq; exact nomatch heq
  · -- `mem_type`: `Sort 0` inhabits `Sort 1`
    intro φ
    refine ⟨.sort 1, ?_, fun ρ => ⟨?_, trivial⟩⟩
    · rw [show defProbeCi.toConstantVal.type = defProbeTy from rfl,
        denoteClosed, defProbeTy, denote]
      simp [Setlec.Level.eval]
    · rw [defProbeCval_head, interp_sort, interp_sort]
      exact univ_mem_univ 0
  · -- `hdefn`: the value's denotation **is** the leaf
    intro cv value hint heq φ
    obtain ⟨rfl, rfl⟩ := defProbe_defn_inv heq.symm
    rw [denoteClosed, defProbeVal, denote, defProbeCval_at]
    simp [Setlec.Level.eval]
  · -- `hheadEta`: the probe environment stores no inductive
    intro T cvT caps hf _ _ _ _
    by_cases hn : T = defProbeName
    · rw [hn] at hf
      exact nomatch hf
    · rw [show (⟨defProbeCi :: Env.empty.consts⟩ : Env) = defProbeEnv
        from rfl, defProbeEnv_find_ne hn] at hf
      exact nomatch hf

theorem defProbeEnvS_cval : (defProbeEnvS V).cval = defProbeCval := rfl

/-- **`EnvS2`'s tenth field at the definition probe.**  Both conjuncts
are met by absence of a λ: the stored leaf is a *sort*. -/
theorem defProbeEnvS_cvalAnnot (μ : CheckMode) (φ : Name → Nat) :
    CvalAnnot μ defProbeEnv (defProbeEnvS V).cval φ := by
  rw [defProbeEnvS_cval]
  refine ⟨fun n ψ Δ => ?_, ?_⟩
  · by_cases hn : n = defProbeName
    · subst hn; rw [defProbeCval_at]; exact ⟨_, .sort⟩
    · rw [defProbeCval_ne hn]; exact ⟨.const .empty [0], .const⟩
  · intro n ψ Δ T _ hlam _
    by_cases hn : n = defProbeName
    · subst hn
      rw [defProbeCval_at] at hlam
      exact absurd hlam (by simp [VExpr.isLam])
    · rw [defProbeCval_ne hn] at hlam
      exact absurd hlam (by simp [emptyT, VExpr.isLam])

/-! ## The uniqueness-form invariant at the probe -/

/-- **An `EnvS2U` at an environment that stores a definition.**
`acval_defn` is no longer discharged by an absent premise: the stored
`defnInfo` matches, `denote2` answers on its value, and the field's
equation has to hold. -/
noncomputable def defProbeEnvS2U : EnvS2U V defProbeEnv where
  base := defProbeEnvS V
  acval := defProbeAcval
  acval_erase := by
    intro n ψ
    by_cases hn : n = defProbeName
    · subst hn
      rw [defProbeAcval_at,
        show (defProbeEnvS V).cval = defProbeCval from rfl,
        defProbeCval_at]
      rfl
    · rw [defProbeAcval_ne hn,
        show (defProbeEnvS V).cval = defProbeCval from rfl,
        defProbeCval_ne hn]
      rfl
  acval_closed := by
    intro n ψ k
    by_cases hn : n = defProbeName
    · subst hn; rw [defProbeAcval_at]; rfl
    · rw [defProbeAcval_ne hn]; rfl
  acval_params := fun _ _ _ _ _ _ => rfl
  acval_ok2 := by
    intro n ψ ρ
    by_cases hn : n = defProbeName
    · subst hn; rw [defProbeAcval_at]; simp
    · rw [defProbeAcval_ne hn]; simp
  acval_defn := by
    intro μ φ F cv value hint hc ra hra
    obtain ⟨rfl, rfl⟩ := defProbe_defn_inv (List.mem_singleton.mp hc)
    rw [defProbeVal, denote2] at hra
    obtain rfl : ra = AVExpr.sort (Level.zero.eval φ) :=
      (Option.some.inj hra).symm
    rw [show (⟨defProbeName, [], defProbeTy⟩ : ConstantVal).name
        = defProbeName from rfl, defProbeAcval_at]
    simp [Setlec.Level.eval]
  acval_thm := by
    intro _ _ _ _ _ hc
    rcases List.mem_singleton.mp hc with h
    exact nomatch h
  mem_type2 := by
    intro μ φ fuel c hc ta hden ρ
    obtain rfl : c = defProbeCi := List.mem_singleton.mp hc
    rw [show defProbeCi.toConstantVal.type = defProbeTy from rfl,
      defProbeTy, denote2] at hden
    obtain rfl : ta = AVExpr.sort ((Level.succ .zero).eval φ) :=
      (Option.some.inj hden).symm
    rw [defProbeAcval_head,
      show (Level.succ Level.zero).eval φ = 1 from by
        simp [Setlec.Level.eval]]
    exact interp2_sort_mem V ρ 0

/-- **`acval_defn`'s premise is met, at every fuel.**  The check that
distinguishes "the field holds" from "the field is vacuous": the
stored value annotates without any checker run, so the uniqueness
equation is a real obligation here rather than an empty one. -/
theorem defProbe_denote2_value (μ : CheckMode) (φ : Name → Nat)
    (F : Nat) :
    denote2 μ defProbeAcval defProbeEnv φ F 0 defProbeVal
      = some (defProbeAcval defProbeName φ) := by
  rw [defProbeVal, denote2, defProbeAcval_at]
  simp [Setlec.Level.eval]

/-- …and the stored declaration really is a definition. -/
theorem defProbeEnv_stores_defn :
    ∃ (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
      ConstantInfo.defnInfo cv value hint ∈ defProbeEnv.consts :=
  ⟨_, _, _, List.mem_singleton.mpr rfl⟩

theorem nonempty_envS2U_defProbe :
    Nonempty (EnvS2U V defProbeEnv) := ⟨defProbeEnvS2U V⟩

/-! ## The verdict: it lifts -/

/-- The definition probe's `EnvS2`.  `acval_defn` is the existential
field, and the witness fuel is the given one: the value is
binder-free, so its annotation exists at every fuel. -/
noncomputable def defProbeEnvS2 : EnvS2 V defProbeEnv where
  base := (defProbeEnvS2U V).base
  cval_annot := defProbeEnvS_cvalAnnot V
  acval := (defProbeEnvS2U V).acval
  acval_erase := (defProbeEnvS2U V).acval_erase
  acval_closed := (defProbeEnvS2U V).acval_closed
  acval_params := (defProbeEnvS2U V).acval_params
  acval_ok2 := (defProbeEnvS2U V).acval_ok2
  acval_defn := by
    intro μ φ F cv value hint hc
    obtain ⟨rfl, rfl⟩ := defProbe_defn_inv (List.mem_singleton.mp hc)
    exact ⟨F, Nat.le_refl F, defProbe_denote2_value μ φ F⟩
  acval_thm := by
    intro _ _ _ _ _ hc
    rcases List.mem_singleton.mp hc with h
    exact nomatch h
  mem_type2 := (defProbeEnvS2U V).mem_type2

theorem defProbeEnvS2_toU :
    EnvS2.toU V (defProbeEnvS2 V) = defProbeEnvS2U V := rfl

/-- **The first stored-definition witness of `EnvS2UInImage`.**  The
residue is *not* empty here — `acval_defn`'s premise is met at every
fuel — and it is still satisfied. -/
theorem defProbeEnvS2U_inImage :
    EnvS2UInImage V (defProbeEnvS2U V) :=
  ⟨defProbeEnvS2 V, defProbeEnvS2_toU V⟩

/-! ## What the probe measures: the residue, stated in general

The definition probe lifts, and the reason is worth isolating from the
probe: **uniqueness supplies the identification for free**, so the
whole of `EnvS2UInImage`'s residue at the two `denote2` fields is
*existence of an annotation at some fuel* — `Denote2Total` restricted
to the stored bodies.  The identification `ra = acval cv.name φ`, the
part that looks like the hard half, is the `EnvS2U` field itself.

That is the precise sense in which uniqueness and existence part
company, and the two theorems below make it an **equivalence** rather
than a sufficient condition: nothing else is in the residue. -/

/-- **Every stored body's canonical annotation exists.**  The
`denote2` transpose of `EnvS.defn_eq`/`EnvS.thm_ok`: the collapse lane
already asserts that a stored body *denotes*; this asserts that it
*annotates*, at a fuel of the supplier's choosing.  Note that it does
**not** say which annotation — `EnvS2U.acval_defn` says that. -/
def Denote2Bodies {env : Env} (m : EnvS2U V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  (∀ (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
      ConstantInfo.defnInfo cv value hint ∈ env.consts →
      ∃ (F : Nat) (ra : AVExpr),
        denote2 μ m.acval env φ F 0 value = some ra) ∧
    ∀ (cv : ConstantVal) (value : Expr),
      ConstantInfo.thmInfo cv value ∈ env.consts →
      ∃ (F : Nat) (ra : AVExpr),
        denote2 μ m.acval env φ F 0 value = some ra

/-- **Existence at the stored bodies is enough.**  Given it, the two
existential `EnvS2` fields are the `EnvS2U` fields plus
`denote2_fuelMono`: uniqueness names the annotation, monotonicity
places it at any requested fuel. -/
theorem envS2UInImage_of_bodies {env : Env} (m : EnvS2U V env)
    (hann : ∀ (μ : CheckMode) (φ : Name → Nat),
      CvalAnnot μ env m.base.cval φ)
    (hbod : ∀ (μ : CheckMode) (φ : Name → Nat),
      Denote2Bodies V m μ φ) :
    EnvS2UInImage V m := by
  refine ⟨{
    base := m.base
    cval_annot := hann
    acval := m.acval
    acval_erase := m.acval_erase
    acval_closed := m.acval_closed
    acval_params := m.acval_params
    acval_ok2 := m.acval_ok2
    acval_defn := ?_
    acval_thm := ?_
    mem_type2 := m.mem_type2 }, rfl⟩
  · intro μ φ F cv value hint hc
    obtain ⟨F₀, ra, h⟩ := (hbod μ φ).1 cv value hint hc
    obtain rfl := m.acval_defn μ φ F₀ cv value hint hc h
    exact ⟨max F F₀, Nat.le_max_left _ _,
      denote2_fuelMono (Nat.le_max_right _ _) 0 value h⟩
  · intro μ φ F cv value hc
    obtain ⟨F₀, ra, h⟩ := (hbod μ φ).2 cv value hc
    obtain rfl := m.acval_thm μ φ F₀ cv value hc h
    exact ⟨max F F₀, Nat.le_max_left _ _,
      denote2_fuelMono (Nat.le_max_right _ _) 0 value h⟩

/-- …and it is **necessary**, so the residue is exactly this and the
tenth field. -/
theorem bodies_of_envS2UInImage {env : Env} {m : EnvS2U V env}
    (h : EnvS2UInImage V m) (μ : CheckMode) (φ : Name → Nat) :
    CvalAnnot μ env m.base.cval φ ∧ Denote2Bodies V m μ φ := by
  obtain ⟨m', rfl⟩ := h
  refine ⟨m'.cval_annot μ φ, ?_, ?_⟩
  · intro cv value hint hc
    obtain ⟨F, -, hd⟩ := m'.acval_defn μ φ 0 cv value hint hc
    exact ⟨F, _, hd⟩
  · intro cv value hc
    obtain ⟨F, -, hd⟩ := m'.acval_thm μ φ 0 cv value hc
    exact ⟨F, _, hd⟩

/-- **The bridge's residue, exactly.**  `EnvS2UInImage` is `CvalAnnot`
plus annotation-existence at the stored bodies — and nothing about
*which* annotation, which is what the uniqueness ruling bought. -/
theorem envS2UInImage_iff {env : Env} (m : EnvS2U V env) :
    EnvS2UInImage V m ↔
      ∀ (μ : CheckMode) (φ : Name → Nat),
        CvalAnnot μ env m.base.cval φ ∧ Denote2Bodies V m μ φ :=
  ⟨fun h μ φ => bodies_of_envS2UInImage V h μ φ,
    fun h => envS2UInImage_of_bodies V m (fun μ φ => (h μ φ).1)
      (fun μ φ => (h μ φ).2)⟩

/-! ## The fourth probe: a **λ-bodied** definition

`def lamDefName : (∀ _ : Sort 0, Sort 1) := fun _ : Sort 0 => Sort 0`

The contrast with the sort-valued probe is the point.  There the
stored value annotates at *every* fuel, so `acval_defn`'s premise
costs the checker nothing.  Here the value is a λ, and
`denote2_one_lam` — **the fact that refuted `EnvS2.acval_defn`'s
original "at every fuel" shape** — makes the premise unmeetable below
fuel `2`.  The annotation exists only through a `lamSortE` run:
`inferTypeCore` on the opened body, then `sortOfE` on its output. -/

/-- The λ-bodied definition's name. -/
def lamDefName : Name := .num .anonymous 4

/-- Its stored type, `∀ _ : Sort 0, Sort 1`. -/
def lamDefTy : Expr :=
  .forallE (.num .anonymous 5) (.sort .zero) (.sort (.succ .zero))
    ⟨.default⟩

/-- Its stored value, `fun _ : Sort 0 => Sort 0` — a λ, which is what
this probe is for. -/
def lamDefVal : Expr :=
  .lam (.num .anonymous 6) (.sort .zero) (.sort .zero) ⟨.default⟩

def lamDefCi : ConstantInfo :=
  .defnInfo ⟨lamDefName, [], lamDefTy⟩ lamDefVal (.regular 0)

def lamDefEnv : Env := ⟨[lamDefCi]⟩

/-- The collapse-lane leaf: the value's denotation. -/
def lamDefCval : TConstVal := fun n _ =>
  if n = lamDefName then .lam (.sort 0) (.sort 0) else emptyT 0

/-- The annotated leaf.  The numeral `2` is not a choice either: it is
`lamSortE`'s answer — the sort of the body's type's type. -/
def lamDefAcval : Name → (Name → Nat) → AVExpr := fun n _ =>
  if n = lamDefName then .lam 2 (.sort 0) (.sort 0)
  else .const .empty [0]

theorem lamDefCval_head (ψ : Name → Nat) :
    lamDefCval lamDefCi.name ψ = VExpr.lam (.sort 0) (.sort 0) :=
  if_pos rfl

theorem lamDefCval_at (ψ : Name → Nat) :
    lamDefCval lamDefName ψ = VExpr.lam (.sort 0) (.sort 0) :=
  if_pos rfl

theorem lamDefCval_ne {n : Name} (h : n ≠ lamDefName)
    (ψ : Name → Nat) : lamDefCval n ψ = emptyT 0 := if_neg h

theorem lamDefAcval_head (ψ : Name → Nat) :
    lamDefAcval lamDefCi.name ψ = AVExpr.lam 2 (.sort 0) (.sort 0) :=
  if_pos rfl

theorem lamDefAcval_at (ψ : Name → Nat) :
    lamDefAcval lamDefName ψ = AVExpr.lam 2 (.sort 0) (.sort 0) :=
  if_pos rfl

theorem lamDefAcval_ne {n : Name} (h : n ≠ lamDefName)
    (ψ : Name → Nat) : lamDefAcval n ψ = .const .empty [0] := if_neg h

theorem lamDefEnv_find_ne {n : Name} (h : n ≠ lamDefName) :
    lamDefEnv.find? n = none := by
  rw [lamDefEnv,
    show (⟨[lamDefCi]⟩ : Env) = ⟨lamDefCi :: Env.empty.consts⟩
      from rfl,
    Env.find?_cons,
    if_neg (show ¬ lamDefCi.name = n from fun hh => h hh.symm)]
  rfl

theorem lamDefEnv_find_self :
    lamDefEnv.find? lamDefName = some lamDefCi := rfl

theorem lamDef_find_eq {n : Name} {ci : ConstantInfo}
    (h : lamDefEnv.find? n = some ci) :
    n = lamDefName ∧ ci = lamDefCi := by
  by_cases hn : n = lamDefName
  · subst hn
    rw [lamDefEnv_find_self] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩
  · rw [lamDefEnv_find_ne hn] at h
    exact nomatch h

theorem lamDef_defn_inv {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint}
    (h : ConstantInfo.defnInfo cv value hint = lamDefCi) :
    cv = ⟨lamDefName, [], lamDefTy⟩ ∧ value = lamDefVal := by
  rw [lamDefCi] at h
  injection h with h1 h2 _
  exact ⟨h1, h2⟩

/-! ### The fuel wall, and where the λ first annotates -/

/-- No body type is inferred at fuel `0`, hence no λ-codomain sort. -/
theorem lamSortE_zero_fuel {μ : CheckMode} {env : Env}
    {φ : Name → Nat} (d : Nat) (e : Expr) :
    lamSortE μ env φ 0 d e = none := by
  rw [lamSortE, Setlec.inferTypeCore_zero]
  simp [throw, throwThe, MonadExceptOf.throw, Except.toOption]

/-- …so no λ annotates at fuel `0` either. -/
theorem denote2_zero_lam {μ : CheckMode} {env : Env}
    {φ : Name → Nat} {acval : Name → (Name → Nat) → AVExpr}
    (d : Nat) (n : Name) (ty body : Expr) (mb : BinderMeta) :
    denote2 μ acval env φ 0 d (.lam n ty body mb) = none := by
  rw [denote2]
  simp [lamSortE_zero_fuel]

/-- **The λ annotates at fuel `2`, and the numeral is a run's
answer.**  `lamSortE` infers the opened body's type (`Sort 1`) and
then takes *its* sort (`2`). -/
theorem denote2_two_lam_sort {μ : CheckMode} {env : Env}
    {φ : Name → Nat} {acval : Name → (Name → Nat) → AVExpr}
    (d : Nat) (n : Name) (mb : BinderMeta) :
    denote2 μ acval env φ 2 d (.lam n (.sort .zero) (.sort .zero) mb)
      = some (.lam 2 (.sort 0) (.sort 0)) := by
  rw [denote2, Expr.instantiate1_sort, denote2_two_sort,
    denote2_two_sort, lamSortE, infer_two_sort]
  simp only [Except.toOption]
  rw [sortOfE_two_sort]
  simp [Setlec.Level.eval]

theorem lamDef_denote2_value {μ : CheckMode} {φ : Name → Nat}
    {fuel : Nat} (h : 2 ≤ fuel) :
    denote2 μ lamDefAcval lamDefEnv φ fuel 0 lamDefVal
      = some (lamDefAcval lamDefName φ) := by
  rw [lamDefAcval_at, lamDefVal]
  exact denote2_fuelMono h 0 _ (denote2_two_lam_sort 0 _ _)

/-- **…and below fuel `2` the premise cannot be met.**  Fuel `0` by
`denote2_zero_lam`, fuel `1` by `denote2_one_lam` — the refuting fact
itself, admissible here and discharging the obligation rather than
contradicting it. -/
theorem lamDef_denote2_value_eq {μ : CheckMode} {φ : Name → Nat}
    {fuel : Nat} {ra : AVExpr}
    (h : denote2 μ lamDefAcval lamDefEnv φ fuel 0 lamDefVal
      = some ra) :
    ra = lamDefAcval lamDefName φ := by
  match fuel with
  | 0 => rw [lamDefVal, denote2_zero_lam] at h; exact nomatch h
  | 1 => rw [lamDefVal, denote2_one_lam] at h; exact nomatch h
  | f + 2 =>
    rw [lamDef_denote2_value (μ := μ) (φ := φ) (fuel := f + 2)
      (by omega)] at h
    exact (Option.some.inj h).symm

theorem lamDef_denote2_ty {μ : CheckMode} {φ : Name → Nat}
    {fuel : Nat} (h : 2 ≤ fuel) :
    denote2 μ lamDefAcval lamDefEnv φ fuel 0 lamDefTy
      = some (.pi 1 2 (.sort 0) (.sort 1)) := by
  refine denote2_fuelMono h 0 lamDefTy ?_
  rw [lamDefTy, denote2, Expr.instantiate1_sort, denote2_two_sort,
    denote2, sortOfE_two_sort, sortOfE_two_sort]
  simp [Setlec.Level.eval]

theorem lamDef_denote2_ty_eq {μ : CheckMode} {φ : Name → Nat}
    {fuel : Nat} {ta : AVExpr}
    (h : denote2 μ lamDefAcval lamDefEnv φ fuel 0 lamDefTy
      = some ta) :
    ta = .pi 1 2 (.sort 0) (.sort 1) := by
  match fuel with
  | 0 => rw [lamDefTy, denote2_zero_forallE] at h; exact nomatch h
  | 1 => rw [lamDefTy, denote2_one_forallE] at h; exact nomatch h
  | f + 2 =>
    rw [lamDef_denote2_ty (μ := μ) (φ := φ) (fuel := f + 2)
      (by omega)] at h
    exact (Option.some.inj h).symm

/-! ### The leaf's semantic facts -/

theorem lamDef_annotOkV (ρ : Nat → V) :
    AnnotOkV V ρ (.lam (.sort 0) (.sort 0)) := by
  rw [AnnotOkV_lam]
  exact ⟨by simp, fun _ _ => by simp⟩

theorem lamDef_annotOk2 (ρ : Nat → V) :
    AnnotOk2 V ρ (.lam 2 (.sort 0) (.sort 0)) := by
  rw [AnnotOk2_lam]
  refine ⟨by simp, fun _ _ => by simp, fun _ => univ 1, ?_, ?_⟩
  · intro x _
    rw [interp2_sort]
    exact univ_mem_univ 0
  · intro h; exact nomatch h

theorem lamDef_mem (ρ : Nat → V) :
    interp V ρ (.lam (.sort 0) (.sort 0)) ∈ˢ
      interp V ρ (.pi (.sort 0) (.sort 1)) := by
  rw [interp_lam, interp_pi]
  exact lamC_mem fun x hx => by rw [interp_sort]; exact univ_mem_univ 0

/-! ### The relational side: `CvalAnnot`'s λ-shape conjunct

The stored leaf is λ-shaped, so — exactly as at `piProbeEnvS` — the
second `CvalAnnot` clause has to be *met*, by inverting `Infer` at a
fixed λ subject.  The agreement seal 42 recorded repeats: I7 reads the
codomain off the body's own `Infer`, I3 reads it off the stored type's
denotation, and both answer `Sort 0 → Sort 1`. -/

theorem lamDef_denoteClosed_ty (φ : Name → Nat) (us : List Level) :
    denoteClosed lamDefCval lamDefEnv φ
      (lamDefCi.toConstantVal.type.instantiateLevelParams
        lamDefCi.toConstantVal.levelParams us)
      = some (.pi (.sort 0) (.sort 1)) := by
  rw [show lamDefCi.toConstantVal.type.instantiateLevelParams
      lamDefCi.toConstantVal.levelParams us = lamDefTy from rfl,
    denoteClosed, lamDefTy, denote, Expr.instantiate1_sort]
  simp [Setlec.Level.eval]

/-- **I1's inversion at the probe.**  The only clause whose subject is
a `.sort` is I1: I3's subject is the stored λ. -/
theorem lamDef_infer_sort0 {μ : CheckMode} {φ : Name → Nat}
    {Δ : List VExpr} {e B : VExpr}
    (h : Infer μ lamDefEnv lamDefCval φ Δ e B)
    (he : e = .sort 0) : B = .sort 1 := by
  cases h with
  | sort =>
    injection he with hu
    subst hu
    rfl
  | const hfind =>
    obtain ⟨rfl, rfl⟩ := lamDef_find_eq hfind
    rw [lamDefCval_at] at he
    exact nomatch he
  | litNat hsup => exact absurd hsup (by decide)
  | litStr hsup => exact absurd hsup (by decide)
  | bvar | pi | lam | app | proj | letE => exact nomatch he

/-- **The λ-shape conjunct's content**, and the two clauses agree. -/
theorem lamDef_infer_lam {μ : CheckMode} {φ : Name → Nat}
    {Δ : List VExpr} {e T : VExpr}
    (h : Infer μ lamDefEnv lamDefCval φ Δ e T)
    (he : e = .lam (.sort 0) (.sort 0)) :
    T = .pi (.sort 0) (.sort 1) := by
  cases h with
  | lam _ _ hb =>
    injection he with hA hb'
    subst hA
    subst hb'
    rw [lamDef_infer_sort0 hb rfl]
  | const hfind _ hden =>
    obtain ⟨rfl, rfl⟩ := lamDef_find_eq hfind
    rw [lamDef_denoteClosed_ty] at hden
    exact (Option.some.inj hden).symm
  | litNat hsup => exact absurd hsup (by decide)
  | litStr hsup => exact absurd hsup (by decide)
  | sort | bvar | pi | app | proj | letE => exact nomatch he

theorem lamDef_hasSortC_ty {μ : CheckMode} {φ : Name → Nat}
    {Δ : List VExpr} :
    ∃ v, HasSortC μ lamDefEnv lamDefCval φ Δ
      (.pi (.sort 0) (.sort 1)) v :=
  ⟨imax 1 2, HasSortC.ofHasSort
    ⟨.sort (imax 1 2),
      Infer.pi Infer.sort DefEq.refl Infer.sort DefEq.refl,
      DefEq.refl⟩⟩

theorem lamDef_annotates_lam (μ : CheckMode) (φ : Name → Nat)
    (Δ : List VExpr) :
    Annotates μ lamDefEnv lamDefCval φ Δ
      (.lam (.sort 0) (.sort 0)) (.lam 2 (.sort 0) (.sort 0)) :=
  .lam (B := .sort 1) Infer.sort
    (HasSortC.ofHasSort ⟨.sort 2, Infer.sort, DefEq.refl⟩)
    .sort .sort

/-! ### The collapse-lane invariant -/

def lamDefEnvS : EnvS V lamDefEnv := by
  refine EnvS.cons (V := V) (env := Env.empty) (EnvS.empty V)
    (c₀ := lamDefCi) (cval' := lamDefCval)
    (Installs.of_fresh rfl ?_)
    (hwf := ?_)
    (hclosed := fun ψ => by
      rw [lamDefCval_head]
      exact ⟨trivial, trivial⟩)
    (hparams := fun _ _ _ => rfl)
    (hannot := fun ψ ρ => by
      rw [lamDefCval_head]; exact lamDef_annotOkV V ρ)
    (htype := ?_)
    (hdefn := ?_)
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
    (hheadNat := fun _ _ _ _ hmem => absurd hmem (by decide))
    (hheadDivMod := fun _ _ _ _ hmem => absurd hmem (by decide))
    (hheadReduce := fun _ _ hmem => nomatch hmem)
  · intro n hne
    funext ψ
    rw [lamDefCval_ne hne]
    rfl
  · refine EnvWF.cons (fun c hc => nomatch hc)
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
    · decide
    · intro cv value hint heq
      obtain ⟨rfl, rfl⟩ := lamDef_defn_inv heq.symm
      exact ⟨by decide, by decide, by decide, by decide⟩
    · intro _ _ _ _ heq; exact nomatch heq
    · intro _ _ heq; exact nomatch heq
  · intro φ
    refine ⟨.pi (.sort 0) (.sort 1), ?_, fun ρ => ⟨?_, ?_⟩⟩
    · rw [show lamDefCi.toConstantVal.type = lamDefTy from rfl,
        denoteClosed, lamDefTy, denote, Expr.instantiate1_sort]
      simp [Setlec.Level.eval]
    · rw [lamDefCval_head]; exact lamDef_mem V ρ
    · rw [AnnotOkV_pi]
      exact ⟨by simp, fun _ _ => by simp⟩
  · intro cv value hint heq φ
    obtain ⟨rfl, rfl⟩ := lamDef_defn_inv heq.symm
    rw [denoteClosed, lamDefVal, denote, Expr.instantiate1_sort,
      lamDefCval_at]
    simp [Setlec.Level.eval]
  · intro T cvT caps hf _ _ _ _
    by_cases hn : T = lamDefName
    · rw [hn] at hf
      exact nomatch hf
    · rw [show (⟨lamDefCi :: Env.empty.consts⟩ : Env) = lamDefEnv
        from rfl, lamDefEnv_find_ne hn] at hf
      exact nomatch hf

theorem lamDefEnvS_cval : (lamDefEnvS V).cval = lamDefCval := rfl

/-- **The λ-shape conjunct, met rather than dodged** — as at
`piProbeEnvS_cvalAnnot`, but now at a **definition**'s leaf. -/
theorem lamDefEnvS_cvalAnnot (μ : CheckMode) (φ : Name → Nat) :
    CvalAnnot μ lamDefEnv (lamDefEnvS V).cval φ := by
  rw [lamDefEnvS_cval]
  refine ⟨fun n ψ Δ => ?_, ?_⟩
  · by_cases hn : n = lamDefName
    · subst hn
      rw [lamDefCval_at]
      exact ⟨_, lamDef_annotates_lam μ φ Δ⟩
    · rw [lamDefCval_ne hn]
      exact ⟨.const .empty [0], .const⟩
  · intro n ψ Δ T _ hlam hinf
    by_cases hn : n = lamDefName
    · subst hn
      rw [lamDefCval_at] at hinf
      rw [lamDef_infer_lam hinf rfl]
      exact lamDef_hasSortC_ty
    · rw [lamDefCval_ne hn] at hlam
      exact absurd hlam (by simp [emptyT, VExpr.isLam])

/-- The stored leaf really is λ-shaped. -/
theorem lamDefCval_isLam (ψ : Name → Nat) :
    (lamDefCval lamDefName ψ).isLam = true := by
  rw [lamDefCval_at]; rfl

/-! ### The uniqueness-form invariant, and the verdict -/

noncomputable def lamDefEnvS2U : EnvS2U V lamDefEnv where
  base := lamDefEnvS V
  acval := lamDefAcval
  acval_erase := by
    intro n ψ
    by_cases hn : n = lamDefName
    · subst hn
      rw [lamDefAcval_at,
        show (lamDefEnvS V).cval = lamDefCval from rfl,
        lamDefCval_at]
      rfl
    · rw [lamDefAcval_ne hn,
        show (lamDefEnvS V).cval = lamDefCval from rfl,
        lamDefCval_ne hn]
      rfl
  acval_closed := by
    intro n ψ k
    by_cases hn : n = lamDefName
    · subst hn; rw [lamDefAcval_at]; simp [AVExpr.liftN]
    · rw [lamDefAcval_ne hn]; rfl
  acval_params := fun _ _ _ _ _ _ => rfl
  acval_ok2 := by
    intro n ψ ρ
    by_cases hn : n = lamDefName
    · subst hn; rw [lamDefAcval_at]; exact lamDef_annotOk2 V ρ
    · rw [lamDefAcval_ne hn]; simp
  acval_defn := by
    intro μ φ F cv value hint hc ra hra
    obtain ⟨rfl, rfl⟩ := lamDef_defn_inv (List.mem_singleton.mp hc)
    exact lamDef_denote2_value_eq hra
  acval_thm := by
    intro _ _ _ _ _ hc
    rcases List.mem_singleton.mp hc with h
    exact nomatch h
  mem_type2 := by
    intro μ φ fuel c hc ta hden ρ
    obtain rfl : c = lamDefCi := List.mem_singleton.mp hc
    obtain rfl : ta = .pi 1 2 (.sort 0) (.sort 1) :=
      lamDef_denote2_ty_eq hden
    rw [lamDefAcval_head, interp2_lam, interp2_pi, interp2_sort]
    exact lamR_mem fun x hx => by
      rw [interp2_sort]; exact univ_mem_univ 0

/-- **The premise is not met at every fuel** — the difference from the
sort-valued probe.  `acval_defn` is exercised *through* a checker run
here, at the very shape that refuted the field's original form. -/
theorem lamDef_denote2_value_none (μ : CheckMode) (φ : Name → Nat) :
    denote2 μ lamDefAcval lamDefEnv φ 1 0 lamDefVal = none := by
  rw [lamDefVal, denote2_one_lam]

theorem nonempty_envS2U_lamDef : Nonempty (EnvS2U V lamDefEnv) :=
  ⟨lamDefEnvS2U V⟩

/-- The λ-bodied definition probe's `EnvS2` — **it lifts too**, and
the witness fuel is `max F 2` rather than `F`. -/
noncomputable def lamDefEnvS2 : EnvS2 V lamDefEnv where
  base := (lamDefEnvS2U V).base
  cval_annot := lamDefEnvS_cvalAnnot V
  acval := (lamDefEnvS2U V).acval
  acval_erase := (lamDefEnvS2U V).acval_erase
  acval_closed := (lamDefEnvS2U V).acval_closed
  acval_params := (lamDefEnvS2U V).acval_params
  acval_ok2 := (lamDefEnvS2U V).acval_ok2
  acval_defn := by
    intro μ φ F cv value hint hc
    obtain ⟨rfl, rfl⟩ := lamDef_defn_inv (List.mem_singleton.mp hc)
    exact ⟨max F 2, Nat.le_max_left _ _,
      lamDef_denote2_value (Nat.le_max_right _ _)⟩
  acval_thm := by
    intro _ _ _ _ _ hc
    rcases List.mem_singleton.mp hc with h
    exact nomatch h
  mem_type2 := (lamDefEnvS2U V).mem_type2

theorem lamDefEnvS2_toU :
    EnvS2.toU V (lamDefEnvS2 V) = lamDefEnvS2U V := rfl

/-- **The verdict at the λ-bodied definition: it lifts.**  So the
place where uniqueness and existence part company is *not* the λ — it
is a stored body whose annotation exists at **no** fuel. -/
theorem lamDefEnvS2U_inImage : EnvS2UInImage V (lamDefEnvS2U V) :=
  ⟨lamDefEnvS2 V, lamDefEnvS2_toU V⟩

/-! ## The residue, exercised at a definition-storing environment

`envS2UInImage_of_bodies` would be seal 20's *"vacuous `Prop` with a
good name"* if `Denote2Bodies` were never met at an environment that
stores anything.  It is met here, and by a body the checker has to run
on. -/

/-- The residue holds at the λ-bodied definition probe. -/
theorem denote2Bodies_lamDef (μ : CheckMode) (φ : Name → Nat) :
    Denote2Bodies V (lamDefEnvS2U V) μ φ := by
  refine ⟨?_, ?_⟩
  · intro cv value hint hc
    obtain ⟨rfl, rfl⟩ := lamDef_defn_inv (List.mem_singleton.mp hc)
    exact ⟨2, _, lamDef_denote2_value (Nat.le_refl 2)⟩
  · intro cv value hc
    rcases List.mem_singleton.mp hc with h
    exact nomatch h

/-- …and the general route reaches the same verdict as the hand-built
lift, which is the check that the general theorem is usable and not
merely true. -/
theorem lamDefEnvS2U_inImage_via_residue :
    EnvS2UInImage V (lamDefEnvS2U V) :=
  envS2UInImage_of_bodies V (lamDefEnvS2U V)
    (fun μ φ => lamDefEnvS_cvalAnnot V μ φ)
    (fun μ φ => denote2Bodies_lamDef V μ φ)

/-! ## The three sweeps

**1. Smallest fuel.**  `Denote2Bodies` asserts a `denote2` success as
a *conclusion*, which is the shape that refuted three statements in
this campaign — deliberately so: it **is** the residue, named at the
place the campaign has always put existence, and it is existential in
the fuel rather than universal.  `lamDef_denote2_value_none` is the
recorded witness that the fuel matters: the λ-bodied probe's body has
no annotation at fuel `1`.

**2. Vacuity.**  Every field of both probes' `EnvS2U`s that can be
exercised is: `acval_defn`'s premise is *met* at both (at every fuel
at `defProbe`, only from fuel `2` at `lamDef`), `mem_type2`'s premise
likewise, and `CvalAnnot`'s λ-shape conjunct is non-vacuous at
`lamDef` (`lamDefCval_isLam`).  `Denote2Bodies` is exhibited met at a
definition-storing environment (`denote2Bodies_lamDef`), so
`envS2UInImage_of_bodies` is not conditional on nothing.

**3. Tombstones.**  A file added, none edited.

## The verdict, and its honest limit

**Both probes lift.**  So the answer to "does a stored `defnInfo`
break `EnvS2UInImage`?" is **no, not by itself** — and
`envS2UInImage_iff` says exactly why: uniqueness supplies the
*identification* half of the existential field for free, leaving only
annotation-**existence** at the stored bodies.

Where the parting must therefore live, named rather than exhibited:
`denote2` differs from `denote` **only** at the two binder clauses,
by `sortOfE`/`lamSortE`.  `EnvS.defn_eq` already forces the body to
`denote`.  So a witness separating uniqueness from existence needs a
stored body whose binder sorts the checker cannot compute *at any
fuel* — and every well-typed body computes them.  This file did not
find one, and says so rather than claiming the residue is closed:
what it establishes is that the residue is `Denote2Total` at the
stored bodies and **nothing else**. -/

/-! ## Establishing `Denote2Bodies` at an install step

Seal 44 stopped the endgame lead with its gap: `EnvS`'s only
well-formedness field is `EnvWF`, which is **purely syntactic**, so no
`EnvS` field records that any checker run succeeded. `Denote2Bodies`
does not follow from the invariant.

**But it is establishable per declaration**, and that is the whole
point of the relocation. The residue moved from `Denote2Total`'s
run-less `∀` — an object **no later run has as its subject** — to
**stored bodies, every one of which the front door demonstrably ran
on.** The statement below is the supplier that turns that observation
into an obligation an install can meet.

`Denote2TotalR` (`EnvLaws2.lean`) is the same family: run-conditioned
existence, naming the run's *output*. This one names the body, which
is the run's *subject*, so it is the `.const`-side twin rather than a
re-run of seal 30's error. -/

/-- **The front door's fact, as a supplier**: a body the checker
successfully inferred a type for has an annotation at some fuel.

Run-conditioned, so it predicts nothing — the discipline seal 33
parked `Denote2Total` for failing. Depth `0`, because a stored body is
closed. -/
def Denote2BodyOfRun (μ : CheckMode) (env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat) : Prop :=
  ∀ (value t : Expr) (F : Nat),
    Setlec.inferTypeCore μ env F 0 value = .ok t →
    ∃ (F' : Nat) (ra : AVExpr),
      denote2 μ acval env φ F' 0 value = some ra

/-- **The new declaration's body, as the front door left it**:
prefix-bound, and a term the checker inferred a type for.

*Supplied by* `ValueFrontR` — its `constsResolve` conjunct gives the
first half through `constsBound_of_constsResolve`, and seal 49's
exposed run gives the second.  Both halves are **inhabited from real
runs**; nothing here is a residue.

Named because `Denote2BodiesStep` was missing it: the step's
conclusion is about the body `c₀` stores, and `Denote2BodyOfRun` is
keyed on a *run*, which no other premise of that statement produced. -/
def NewBodyFrontR (μ : CheckMode) (env : Env) (c₀ : ConstantInfo) :
    Prop :=
  (∀ (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
      c₀ = ConstantInfo.defnInfo cv value hint →
      ConstsBound env value ∧
        ∃ (t : Expr) (F : Nat),
          Setlec.inferTypeCore μ env F 0 value = .ok t) ∧
    ∀ (cv : ConstantVal) (value : Expr),
      c₀ = ConstantInfo.thmInfo cv value →
      ConstsBound env value ∧
        ∃ (t : Expr) (F : Nat),
          Setlec.inferTypeCore μ env F 0 value = .ok t

/-- **The fold's step.**  `Denote2Bodies` at the extension follows from
`Denote2Bodies` at the prefix, the extension's own transport, and the
front-door fact at the one new body.

**Amended at seal 47**, because as first stated it was *unprovable*:
its premise spoke at the **prefix** `env` and its conclusion at the
**extension**, and nothing in the statement bridged them. The
transport is now an explicit premise rather than a hope — and naming
it also names its cost, since `Denote2EnvExtend` is itself
undischarged and its literal clause outright **refuted**
(`denote2EnvExtend_lit_refuted`), needing a direction the Θ lane's (E)
did not originally give.

*Rule: a step lemma whose premise and conclusion live at different
environments must carry the transport, or it is a wish with a
signature.*

**Amended a second time, and this one was a missing premise rather
than a missing transport.**  As left at seal 47 the statement was
still not provable: its conclusion is about the body `c₀` *stores*,
while `Denote2BodyOfRun` is keyed on a **run**, and no premise
produced one at that body — nor said the body was prefix-bound, which
the transport needs.  `NewBodyFrontR` is now the third premise, and
with it the step is **proved** (`denote2BodiesStep_holds`) rather than
carried.

*Rule, one turn of the same screw: a step lemma must carry not only
the transport but the fact its supplier is keyed on.  Seal 47 named
the run in prose and took neither.* -/
def Denote2BodiesStep (μ : CheckMode) (env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat)
    (c₀ : ConstantInfo) : Prop :=
  Denote2BodyOfRun μ env acval φ →
    Denote2EnvExtend μ env ⟨c₀ :: env.consts⟩ acval φ →
    NewBodyFrontR μ env c₀ →
    (∀ (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
      c₀ = ConstantInfo.defnInfo cv value hint →
      ∃ (F : Nat) (ra : AVExpr),
        denote2 μ acval ⟨c₀ :: env.consts⟩ φ F 0 value = some ra) ∧
    ∀ (cv : ConstantVal) (value : Expr),
      c₀ = ConstantInfo.thmInfo cv value →
      ∃ (F : Nat) (ra : AVExpr),
        denote2 μ acval ⟨c₀ :: env.consts⟩ φ F 0 value = some ra

/-- **The step, established.**  Both halves are the same three moves:
the front door's run gives the body an annotation at the **prefix**
(`Denote2BodyOfRun`), and the transport carries it to the extension
(`Denote2EnvExtend`, at the body's own prefix-boundness).

*Inhabitation, precisely*: this theorem is unconditional, so
`Denote2BodiesStep` is **no longer a residue**.  What its two
premises cost is unchanged — `Denote2BodyOfRun` is seal 33's parked
existence at a run's subject, `Denote2EnvExtend` is frozen on Θ — but
the *step* is not a third thing to discharge. -/
theorem denote2BodiesStep_holds (μ : CheckMode) (env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat)
    (c₀ : ConstantInfo) : Denote2BodiesStep μ env acval φ c₀ := by
  intro hrun hext hfront
  constructor
  · intro cv value hint heq
    obtain ⟨hcb, t, F, hinf⟩ := hfront.1 cv value hint heq
    obtain ⟨F', ra, hra⟩ := hrun value t F hinf
    exact ⟨F', ra, by rw [← hext F' 0 value hcb]; exact hra⟩
  · intro cv value heq
    obtain ⟨hcb, t, F, hinf⟩ := hfront.2 cv value heq
    obtain ⟨F', ra, hra⟩ := hrun value t F hinf
    exact ⟨F', ra, by rw [← hext F' 0 value hcb]; exact hra⟩

/-! ## The supplier check, run — and the verdict is NOT VISIBLE

Seal 45 froze `Denote2BodiesStep` with a standing instruction: run the
pre-build supplier check first, and *if the front-door run's existence
is not visible where `DeclStep2` can see it, that is an exposure
request rather than a rebuild*.  The check was run against the actual
install path, and the answer is **not visible**.  Nothing below is
proved here, by that instruction.

### The fact is true, and it is held three times over

The claim behind the relocation holds exactly as seal 44 stated it.
`checkDefnVal` (`Setlec/Kernel/Checker.lean:361`) annotates the value
and then runs

```
let vtype ← ops.inferType env 0 value
```

on the **annotated** value — which is the term that gets stored — at
the **pre-install** environment.  `checkThmVal` and `checkOpaqueVal`
run the same line.  So every stored body really is a term the front
door inferred a type for, and `Denote2BodyOfRun`'s premise is met at
the install for the one new declaration.

The bridge holds it in a named binder: `valueFrontR_of`
(`Setlec/SetR/Bridge/Decl.lean:134`) takes

```
(hvt : inferTypeCore μ env F 0 value' = .ok vtype)
```

as an explicit hypothesis.  Its type-side twin `constantValR_of`
(`:97`) takes the whole `checkConstantVal` run and obtains `hst`
(`inferTypeCore` on the annotated type) and `hsort` (`ensureSort` on
its output) from `checkConstantVal_inv`.

### …and it is dropped at exactly one place

`ValueFrontR` (`Setlec/SetR/Decl.lean:152`) records **five syntactic
conjuncts and one relational front door**, and no run:
`annotateCore μ env F 0 value = .ok value'` is the only checker call
in it.  `ConstantValR` (`:132`) is the same shape.  `hvt`, `hst` and
`hsort` are consumed into the `Infer`/`DefEq` conjunct and never
re-emitted.

Downstream the fact is simply absent.  `extendValueS`
(`Setlec/SetR/Install/Value.lean:91`) consumes `ValueFrontR` through
`valueKeyS`; `EnvS.cons` (`Setlec/SetR/Install/Cons.lean:454`) states
every one of its obligations in `denote`/`interp` vocabulary.  A grep
for `inferTypeCore` across `Decl.lean` and all of `Install/` returns
**nothing**.

**And `annotateCore` is not a substitute.**  Since task #100 stage 6,
`annotateBody`'s `forallE` and `lam` clauses are purely structural
(`Setlec/Kernel/Core.lean:2097-2107`) — they compute no sort and run
no `infer`.  So the one run `ValueFrontR` *does* expose says nothing
about the binder sorts `denote2` needs, and restating
`Denote2BodyOfRun` over `annotateCore` would trade a true premise for
a useless one.

### The exposure request

**Held by:** `valueFrontR_of`'s binder `hvt`
(`Setlec/SetR/Bridge/Decl.lean:144`) and, on the type side,
`checkConstantVal_inv`'s `hst`/`hsort` at `constantValR_of`.

**Conjunct that would expose it**, added to `ValueFrontR`
(`Setlec/SetR/Decl.lean:152`):

```
(∃ vtype, inferTypeCore μ env F 0 value' = .ok vtype) ∧
```

supplied at `valueFrontR_of` by `⟨vtype, hvt⟩` — the binder is already
in scope, so the producer side is a pair, not a proof.  The type-side
twin, wanted by `memberBlock2_of_stored`'s `hrun` for the *same*
reason, is added to `ConstantValR` (`:132`):

```
(∃ stype u, inferTypeCore μ env F 0 type' = .ok stype ∧
  ensureSortCore μ env F 0 stype = .ok u) ∧
```

Both are pure strengthenings of a pack; the cost is that every
positional destructuring of the two relations moves
(`Install/Value.lean:55`, `:74`, four sites in `DivModPin.lean`, and
the per-kind assemblies in `Bridge/Decl.lean`).  Neither file is this
worker's to edit.

### Two things the exposure would still not close

Recorded against interest, because a request that undersells its own
remainder is the failure mode this campaign keeps catching.

1. **`Denote2BodiesStep` is unprovable as stated, exposure or not.**
   Its only premise is `Denote2BodyOfRun` *at the prefix* `env`,
   while its conclusion is a `denote2` success at the **extension**
   `⟨c₀ :: env.consts⟩`.  Nothing in the statement bridges the two,
   and `Denote2EnvExtend` — the object that would — is itself
   undischarged (`Denote2Extend.lean`, whose
   `denote2EnvExtend_lit_refuted` shows its literal clause is *false*
   without a guard agreement the Θ lane has not published; the same
   file's finding 1 shows the equation needs a direction (E) does not
   give at all).  The docstring above
   names both suppliers in prose; the statement takes neither as a
   premise.  Amending it is a statement change and is not made here.

   **Settled since.**  Seal 47 took the transport as a premise and
   that was still not enough — the run itself was missing, and so was
   the body's prefix-boundness.  With `NewBodyFrontR` added the step
   is proved outright (`denote2BodiesStep_holds`), and both of its
   halves are supplied by `ValueFrontR`.  *Two amendments to reach a
   provable statement, each found by trying to write the proof.*
2. **`memberBlock2_of_stored`'s `hrun` is stronger than the front
   door.**  It demands `inferTypeCore … type = .ok (.sort u)` — the
   inferred type *literally* a sort — whereas `checkConstantVal` only
   `ensureSort`s the output, i.e. whnfs it to a sort.  The exposed
   conjunct above would therefore still not apply on the nose; the
   key would need the claim at a non-sort inferred type, where its
   second dual-success premise stops being free.

*The pattern goes four for four: the front door had the fact, the
pack transposed it away, and the consumer three tiers down is the one
that noticed.* -/

end Setlec.SetR.Interp2
