import Setlec.SetR.Interp2.EnvS2U
import Setlec.SetR.Install.Cons

/-!
# A non-empty `EnvS2U` — closing seal 37's honest gap

Seal 37 recorded one: **`EnvS2U`'s only exhibited inhabitant is
`EnvS2U.empty`**, and that is the shape of every vacuity failure of
this campaign (`EnvS2.empty` masked a false field for four seals,
because `env.consts = []` made the two `denote2` fields vacuous).
A key whose subject is uninhabited says nothing, so `DeclStep2` —
`Nonempty (EnvS2U V env₂)` — could not be believed until an `EnvS2U`
existed at an environment that actually stores something.

This file exhibits one, by the cheapest of the routes surveyed: **a
single axiom**.

## Why the axiom route, and what it does and does not buy

`acval_defn`/`acval_thm` stay discharged-by-absent-premise, but now
**for the right reason**: the environment stores no `defnInfo` and no
`thmInfo`, rather than storing nothing at all.  The fields that carry
real content at a stored constant — `mem_type2` and `acval_ok2` —
are met at a genuine leaf, and `mem_type2` in particular is now a
*used* hypothesis: `denote2` runs on the stored type and its output
must contain the leaf.

The axiom's type is `.sort .zero`, which is what makes the probe
small: an axiom `X : Prop` needs no annotation run at all
(`denote2 … (.sort .zero) = some (.sort 0)` at every mode, fuel and
valuation), and the membership obligation is `empty ∈ˢ univ 0`.

## What is honestly still not exercised

`mem_type2` is met here at a **sort-typed** constant, so no binder
numeral is computed and `sortOfE` never runs.  This closes the
vacuity question the seal asked — the structure is inhabited at a
non-empty environment, and no field goes false there — and it does
**not** claim that the fields are satisfiable at an arbitrary
install; the basis block would be the next probe up.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable (V : Type w) [SetTheory V]

/-! ## The probe environment -/

/-- The probe axiom's name.  Chosen `.num`-shaped: every reserved,
pinned and accelerated name in the tree is `.str`-shaped, so each
disequality this file needs is one constructor comparison rather than
a string decision. -/
def probeName : Name := .num .anonymous 0

/-- The probe's stored constant: `axiom probeName : Prop`. -/
def probeCi : ConstantInfo :=
  .axiomInfo ⟨probeName, [], .sort .zero⟩

/-- The probe environment: **one** stored constant. -/
def probeEnv : Env := ⟨[probeCi]⟩

theorem probeCi_name : probeCi.name = probeName := rfl

theorem probeEnv_find_ne {n : Name} (h : n ≠ probeName) :
    probeEnv.find? n = none := by
  rw [probeEnv, show (⟨[probeCi]⟩ : Env) = ⟨probeCi :: Env.empty.consts⟩
    from rfl, Env.find?_cons,
    if_neg (show ¬ probeCi.name = n from fun hh => h hh.symm)]
  rfl

/-! ## The collapse-lane invariant at the probe -/

/-- The probe's `EnvS`, built by the ordinary install assembler from
`EnvS.empty`.  The valuation does not move: `EnvS.empty`'s leaf is the
empty type at every name, and so is the probe's, which is what makes
`Installs` cost one `rfl`. -/
def probeEnvS : EnvS V probeEnv := by
  refine EnvS.cons (V := V) (env := Env.empty) (EnvS.empty V)
    (c₀ := probeCi) (cval' := fun _ _ => emptyT 0)
    (Installs.of_fresh rfl (fun _ heq => nomatch heq) (fun _ _ => rfl))
    (hwf := ?_)
    (hclosed := fun _ => trivial)
    (hparams := fun _ _ _ => rfl)
    (hannot := fun _ _ => trivial)
    (htype := ?_)
    (hdefn := fun _ _ _ heq => nomatch heq)
    (hthm := fun _ _ heq => nomatch heq)
    (hempty := fun _ _ => ⟨0, rfl⟩)
    (hheadCtors := fun _ _ _ _ heq => nomatch heq)
    (hheadRec := fun _ _ _ _ heq => nomatch heq)
    (hheadEta := ?_)
    (hheadUnit := fun _ _ heq => nomatch heq)
    (hheadProj := fun _ heq => nomatch heq)
    (hheadProjPair := fun _ _ heq => nomatch heq)
    (hheadProjTower := fun _ heq => nomatch heq)
    (hheadEq := fun heq => nomatch heq)
    (hheadBasis := fun heq => nomatch heq)
    (hheadNat := fun _ _ _ heq => nomatch heq)
    (hheadDivMod := fun _ _ _ heq => nomatch heq)
    (hheadReduce := fun _ _ hmem => nomatch hmem)
  · -- `EnvWF`: the stored type is `Sort 0`, and the three value
    -- clauses are vacuous at an `axiomInfo`
    refine EnvWF.cons (fun c hc => nomatch hc)
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
    · decide
    · intro _ _ _ heq; exact nomatch heq
    · intro _ _ _ _ heq; exact nomatch heq
    · intro _ _ heq; exact nomatch heq
  · -- `mem_type`: `Sort 0` denotes to `.sort 0`, and the empty type
    -- inhabits `univ 0`
    intro φ
    refine ⟨.sort 0, ?_, fun _ => ⟨empty_mem_univ 0, trivial⟩⟩
    rw [show probeCi.toConstantVal.type = Expr.sort .zero from rfl,
      denoteClosed, denote_sort]
    rfl
  · -- `hheadEta`: the probe environment stores no inductive
    intro T cvT caps hf _ _ _ _
    by_cases hn : T = probeName
    · rw [hn] at hf
      exact nomatch hf
    · rw [show (⟨probeCi :: Env.empty.consts⟩ : Env) = probeEnv
        from rfl, probeEnv_find_ne hn] at hf
      exact nomatch hf

/-- The probe's collapse-lane valuation, read off the assembler: the
install did not move it, so it is `EnvS.empty`'s leaf at every name.
Named rather than inlined because `probeEnvS_cvalAnnot` rewrites with
it — a `simp` set that unfolds `probeEnvS` cannot get there, since
the assembler is applied to twenty arguments. -/
theorem probeEnvS_cval : (probeEnvS V).cval = fun _ _ => emptyT 0 :=
  rfl

/-- **`CvalAnnot` at the probe.**  Written when `EnvS2` still carried
a `cval_annot` field; the cleanup seal withdrew that field from both
structures, so this now stands as a **standalone fact about the
probe's valuation** rather than as a supplier.  It is kept because it
is content: what the probe's leaves are, not what a structure asks
for.

Both conjuncts are met by *absence of a λ*: the install did not move
the valuation, so every leaf is the empty type's constant, which
annotates by `Annotates.const` and is not λ-shaped.  That is the
**same** discharge `EnvS2.empty` uses, and it is honest here only
because the probe's one stored constant happens to keep the empty
valuation — `piProbeEnvS_cvalAnnot` is where the λ-shape conjunct has
to be met rather than dodged. -/
theorem probeEnvS_cvalAnnot (μ : CheckMode) (φ : Name → Nat) :
    CvalAnnot μ probeEnv (probeEnvS V).cval φ := by
  refine ⟨fun n ψ Δ => ⟨.const .empty [0], ?_⟩, ?_⟩
  · rw [probeEnvS_cval]
    exact .const
  · intro n ψ Δ T _ hlam _
    rw [probeEnvS_cval] at hlam
    exact absurd hlam (by simp [emptyT, VExpr.isLam])

/-! ## The uniqueness-form invariant at the probe -/

/-- **A non-empty `EnvS2U`.**  The annotated valuation is the same
constant leaf `EnvS2.empty` uses, so `acval_erase`, `acval_closed` and
`acval_params` are equations between identical terms; `acval_ok2` is
the constant clause.  The two `denote2` fields are discharged by
*absence of a stored `defnInfo`/`thmInfo`*, and `mem_type2` is the one
field with content: the stored type's canonical annotation is `.sort
0`, whose interpretation is `univ 0`. -/
noncomputable def probeEnvS2U : EnvS2U V probeEnv where
  base := probeEnvS V
  acval := fun _ _ => .const .empty [0]
  acval_erase := fun _ _ => rfl
  acval_closed := fun _ _ _ => rfl
  acval_params := fun _ _ _ _ _ _ => rfl
  acval_ok2 := fun _ _ _ => by simp
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
    obtain rfl : c = probeCi := List.mem_singleton.mp hc
    rw [show probeCi.toConstantVal.type = .sort .zero from rfl,
      denote2] at hden
    obtain rfl : ta = .sort 0 := (Option.some.inj hden).symm
    rw [interp2_sort, interp2_const]
    exact empty_mem_univ 0

/-- **`mem_type2`'s premise is met at the probe** — the check that
distinguishes "the field holds" from "the field is vacuous".  The
stored type annotates at *every* mode, fuel and valuation, so the
field is exercised at the stored constant rather than skipped. -/
theorem probe_denote2_type (μ : CheckMode) (φ : Name → Nat)
    (fuel : Nat) :
    denote2 μ (fun _ _ => .const .empty [0]) probeEnv φ fuel 0
        probeCi.toConstantVal.type = some (.sort 0) := by
  rw [show probeCi.toConstantVal.type = Expr.sort .zero from rfl,
    denote2]
  rfl

/-- **The gap seal 37 recorded is closed.**  `EnvS2U` is inhabited at
an environment that stores a constant, so `DeclStep2`'s subject is not
uninhabited. -/
theorem nonempty_envS2U_probe : Nonempty (EnvS2U V probeEnv) :=
  ⟨probeEnvS2U V⟩

/-! ## The probe as an `EnvS2` — `EnvS2UInImage`'s first witness

`EnvS2UInImage` is the residue the `EnvS2U`-form step's derivability
turned on before the live lane was re-pointed to `EnvS2U` (seal 46),
and a residue nobody can satisfy is seal 20's
"vacuous `Prop` with a good name".  It is satisfied here: the probe's
`EnvS2U` *is* an `EnvS2`, and every field is the same term — the two
`denote2` fields differ in form but agree on this environment,
because there is no stored `defnInfo`/`thmInfo` for either to speak
about.

Since the cleanup seal the two structures have the *same* field list,
so this lift is field-for-field and `probeEnvS_cvalAnnot` is no longer
consumed here. -/

/-- The probe environment's `EnvS2` — the same data. -/
noncomputable def probeEnvS2 : EnvS2 V probeEnv where
  base := (probeEnvS2U V).base
  acval := (probeEnvS2U V).acval
  acval_erase := (probeEnvS2U V).acval_erase
  acval_closed := (probeEnvS2U V).acval_closed
  acval_params := (probeEnvS2U V).acval_params
  acval_ok2 := (probeEnvS2U V).acval_ok2
  acval_defn := by
    intro _ _ _ _ _ _ hc
    rcases List.mem_singleton.mp hc with h
    exact nomatch h
  acval_thm := by
    intro _ _ _ _ _ hc
    rcases List.mem_singleton.mp hc with h
    exact nomatch h
  mem_type2 := (probeEnvS2U V).mem_type2

/-- …and it lifts to the probe's `EnvS2U` on the nose. -/
theorem probeEnvS2_toU :
    EnvS2.toU V (probeEnvS2 V) = probeEnvS2U V := rfl

theorem probeEnvS2U_inImage : EnvS2UInImage V (probeEnvS2U V) :=
  ⟨probeEnvS2 V, probeEnvS2_toU V⟩

/-- …and the environment really is non-empty, which is the whole point
of the probe. -/
theorem probeEnv_consts_ne_nil : probeEnv.consts ≠ [] := by
  intro h; exact nomatch h

end Setlec.SetR.Interp2
