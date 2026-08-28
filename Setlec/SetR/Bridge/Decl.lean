import Setlec.SetR.Bridge.Main
import Setlec.SetR.Install.Step

/-!
# The declaration-level bridge (task #148, T6)

`Setlec/SetR/Bridge/*` bridges the checker's *inference* steps into the
`[set]` relation family; this file bridges its **declarations**.  Each
of `checkDecl`'s six branches is inverted into the corresponding
`Decl*R` clause of `Setlec/SetR/Decl.lean`, and `checkDeclR_of`
assembles them.  Composed with `declStepS` (`Install/Step.lean`) that
gives the `EnvS`-extension step the consistency fold runs.

Nothing semantic happens here: every lemma is V-free inversion of the
checker's own control flow.  The valuation enters only where a clause
mentions `cval`, and there it is carried, never chosen.
-/

namespace Setlec.SetR

open Setlec.TT SetTheory

universe w

/-! ## `EnvS` is an `EnvR`

The bridge runs against `EnvR` — the weakest V-free invariant its
steps need — and the install layer produces `EnvS`.  The assembly
needs the projection, and building it is what exposed **finding 7**
(recorded in `DESIGN.md`): as landed, two of `EnvR`'s fields were
stated more strongly than `EnvS.rec_rules` can supply.

`EnvS.rec_rules` is `RecRulesV`, which speaks only of rules whose
`fire ≠ .inert` and only at level arguments of the declared length;
`EnvR.rec_rhs_denotes`/`rec_params_le` quantified over *all* rules and
*all* level lists.  The gap is not cosmetic: `Empty.rec` stores **no
rules at all**, so no install could ever supply an unguarded
`rP ≤ mI`, and adding an unguarded `EnvS` field would have been owed
by every install for a fact the bridge never uses.  Both fields are
consumed at exactly one place — the iota fire site in
`Bridge/Iota.lean` — where the fired rule, its non-inertness (`hfire`)
and the level-length check (`hlenU`) are all already in scope.  The
repair is therefore to narrow the fields to their consumption, which
is what `Bridge/Env.lean` now states. -/

/-- **The bridge invariant, from the install invariant.** -/
def EnvS.toEnvR {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env) : EnvR env where
  cval := m.cval
  cval_closed := m.cval_closed
  wf := m.wf
  val_params := m.val_params
  ty_denotes := fun c hc ψ => by
    obtain ⟨t, ht, -⟩ := m.mem_type c hc ψ
    exact ⟨t, ht⟩
  defn_eq := m.defn_eq
  rec_rhs_denotes := fun n cv mI rP rules hf r hr hfire us ψ hlen => by
    obtain ⟨-, hR⟩ := m.rec_rules ψ n cv mI rP rules hf r hr hfire
    obtain ⟨R, hR0, -⟩ := hR us hlen
    exact ⟨R, hR0⟩
  rec_params_le := fun n cv mI rP rules hf r hr hfire =>
    (m.rec_rules (fun _ => 0) n cv mI rP rules hf r hr hfire).1
  proj_ok := m.proj_ok
  thm_ok := m.thm_ok

/-! ## `basisDecl`

The simplest branch: a guard on the pinned `Eq` former, then a fold of
duplicate checks.  `BasisInstallR` records exactly the fold's output —
each constant fresh, then consed — so the inversion is one induction
over `installBasisDecl_inv`. -/

/-- **The pinned-block fold, inverted** into `BasisInstallR`. -/
theorem foldlM_installBasisDecl_invR :
    ∀ (l : List ConstantInfo) {env env₁ : Env},
      l.foldlM (installBasisDecl (m := CheckM)) env = .ok env₁ →
      BasisInstallR env l env₁
  | [], env, env₁, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | ci :: l, env, env₁, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hi : installBasisDecl (m := CheckM) env ci with
    | error e => intro h; exact nomatch h
    | ok env' =>
      intro h
      obtain ⟨hfresh, rfl⟩ := installBasisDecl_inv hi
      exact ⟨Option.isNone_iff_eq_none.mpr hfresh,
        foldlM_installBasisDecl_invR l h⟩

/-- **`basisDecl`, bridged.** -/
theorem declBasisR {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {kind : BasisKind}
    (h : checkDecl μ (fueledOps μ F) env (.basisDecl kind) = .ok env₂) :
    DeclBasisR env kind env₂ := by
  simp only [checkDecl, Bind.bind, Except.bind] at h
  by_cases hk : kind = .quotK
  · subst hk
    by_cases hEq : env.find? eqName = some eqA
    · simp only [hEq, if_true] at h
      exact ⟨fun _ => hEq, foldlM_installBasisDecl_invR _ h⟩
    · simp [hEq] at h
  · simp only [if_neg hk] at h
    exact ⟨fun hh => absurd hh hk, foldlM_installBasisDecl_invR _ h⟩

end Setlec.SetR
