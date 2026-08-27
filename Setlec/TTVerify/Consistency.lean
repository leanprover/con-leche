import Setlec.TTVerify.EnvTT

/-!
# The acceptance theorem and its consistency corollary

The shape mirrors `Setlec/Model/Consistency.lean` exactly:

| set model | here |
|---|---|
| `checkDecl_sound` | `CheckDeclTT` (stage 2) |
| `foldlM_sound` | `foldlM_TT` |
| `checkDecls_sound` | `checkDecls_TT` |
| `no_constant_of_Empty` | `no_constant_of_Empty_TT` |
| `no_proof_of_Empty` | `no_proof_of_Empty_TT` |

Everything below the per-declaration step is proved here.  The step
itself — "checking one declaration preserves the derivation model" — is
the clause-by-clause fuel induction, and is stage 2 of task #119; it is
named as the hypothesis `CheckDeclTT` so that the shape of the argument
is on the record and every consumer of it is visible.

## The direct-install hypothesis

The step is stated for the configuration in which the direct
simple-structure install path is off (`CertifiedConfigTT`, currently `Setlec.directStructsEnabled =
false`, `Setlec/Kernel/Direct.lean`).  A directly installed structure
has no `_model` artifact, and the denotation of a stored inductive goes
through exactly those artifacts, so the bridge has nothing to read for
one.  With the switch off such a block takes the ordinary modeled
clause instead — a fall-through, not a decline.

**The switch defaults on** (measured: turning it off costs five
verdicts, all losses; see `DESIGN.md`, "The master switch, and why it
defaults on"), so this hypothesis is a real restriction on the
configuration the bridge covers, and it is stated rather than hidden.
The set model covers both settings and continues to.
-/

namespace Setlec.TTVerify

open Setlec.TT

variable {F : Nat}

/-- **The per-declaration step**, stage 2 of task #119: checking one
declaration against a derivation-modelled environment yields a
derivation-modelled environment.  The transpose of `checkDecl_sound`,
and the only thing between `EnvTT.empty` and the acceptance theorem.

The closure of the stored eta families (`EtaFamiliesClosedT`) enters
as a hypothesis, threaded through the fold beside the invariant
exactly as the set model threads `EtaFamiliesClosed`: it holds at
every declaration boundary but not mid-block, so it cannot be an
`EnvTT` field, and only the modeled-inductive case reads it (to refute
a fresh constructor completing an *older* former's family).  Its own
preservation is the purely syntactic `FamiliesStepTT` below —
separated rather than bundled into the conclusion so that the five
value/basis cases stay untouched by the re-signing. -/
def CheckDeclTT (F : Nat) : Prop :=
  ∀ {mode : CheckMode} {env env₁ : Env} {d : Declaration},
    checkDecl mode (fueledOps mode F) env d = .ok env₁ →
    CertifiedConfigTT mode →
    EnvTT env → EtaFamiliesClosedT env → Nonempty (EnvTT env₁)

/-- **The closure of stored eta families survives a checked
declaration.**  Purely syntactic (no valuation, no derivations) — the
closure half of the model's `checkDecl_sound` conclusion, separated.
Stated under the certified configuration, like `CheckDeclTT`: the
direct-install path is the one dispatch it does not cover. -/
def FamiliesStepTT (F : Nat) : Prop :=
  ∀ {mode : CheckMode} {env env₁ : Env} {d : Declaration},
    checkDecl mode (fueledOps mode F) env d = .ok env₁ →
    CertifiedConfigTT mode →
    EtaFamiliesClosedT env → EtaFamiliesClosedT env₁

/-- The fold over the declaration stream.  Transpose of
`foldlM_sound`. -/
private theorem foldlM_TT {mode : CheckMode} (hstep : CheckDeclTT F)
    (hfam : FamiliesStepTT F) (hdir : CertifiedConfigTT mode) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      Nonempty (EnvTT env) → EtaFamiliesClosedT env →
      ds.foldlM (checkDecl mode (fueledOps mode F)) env = .ok env' →
      Nonempty (EnvTT env')
  | [], _, _, hm, _, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, hE1, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl mode (fueledOps mode F) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨m⟩ := hm
      exact foldlM_TT hstep hfam hdir ds env1 (hstep hd hdir m hE1)
        (hfam hd hdir hE1) h

/-- **The acceptance theorem**: every accepted environment has a
derivation model, i.e. every constant it stores has a `HasType`
derivation of its type's denotation.  Transpose of
`checkDecls_sound`. -/
theorem checkDecls_TT {mode : CheckMode}
    (hstep : CheckDeclTT F) (hfam : FamiliesStepTT F)
    (hdir : CertifiedConfigTT mode)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls mode (fueledOps mode F) ds = .ok env') :
    Nonempty (EnvTT env') :=
  foldlM_TT hstep hfam hdir ds Env.empty ⟨EnvTT.empty⟩
    EtaFamiliesClosedT.empty h

/-! ## The consistency corollary

`Empty` is a reserved name (input declarations cannot redefine it) and
the layer's `Empty` is level-polymorphic, so this stays
input-independent exactly as the set-model corollary does. -/

/-- A derivation-modelled environment stores no constant of type
`Empty`: its denotation would be a closed derivation of the layer's
empty type, which `Setlec.TT.no_proof_of_empty` refutes.  Transpose of
`no_constant_of_Empty`.

Parametric in a model of the `SetTheory` interface, like every
consistency statement in this project — and *only* here: the invariant
itself (`EnvTT`) mentions no set theory at all, because the layer's own
consistency theorem is what turns the pinned valuation of `Empty` into
uninhabitation. -/
theorem no_constant_of_Empty_TT (V : Type u) [SetTheory V] {env : Env}
    (m : EnvTT env) (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨t, hti, hd⟩ := m.has_type c hc (fun _ => 0)
  rw [hty] at hti
  rw [denoteClosed, denote_const] at hti
  split at hti
  · next ci hfind =>
    split at hti
    · next hlen =>
      obtain rfl := Option.some.inj hti
      obtain ⟨u, hu⟩ := m.empty_pinned
        (Level.substFn (fun _ => 0) ci.toConstantVal.levelParams [])
      rw [hu] at hd
      exact TT.no_proof_of_empty V hd
    · exact nomatch hti
  · exact nomatch hti

/-- **No proof of `Empty` is ever accepted** — through the declarative
type theory.  Transpose of `no_proof_of_Empty`; the set-model theorem of
the same name is untouched and both paths coexist. -/
theorem no_proof_of_Empty_TT (V : Type u) [SetTheory V] {mode : CheckMode}
    (hstep : CheckDeclTT F) (hfam : FamiliesStepTT F)
    (hdir : CertifiedConfigTT mode)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls mode (fueledOps mode F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_TT hstep hfam hdir h
  exact no_constant_of_Empty_TT V m c hc hty

end Setlec.TTVerify
