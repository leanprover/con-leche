import Setlec.SetBase.Bridge.Decl
import Setlec.SetR.Install.Step

/-!
# The collapsed lane's bridge projection (task #161, S8)

THE ZERO-OPENER left exactly one declaration of the old
`Setlec/SetR/Bridge/Decl.lean` behind: `EnvS.toEnvR`.  Everything else
in that file — the six per-kind branch bridges and their front doors —
is model-free and now lives in `Setlec/SetBase/Bridge/Decl.lean`,
statements byte-unchanged.

What is left is the collapsed lane's *own* projection: the install
layer produces an `EnvS V env`, the bridge runs against `EnvR env`,
and this is the map.  The graded lane has its own twin
(`EnvS2PM.toEnvR`, `SetP/Annot/EnvS2P.lean`); neither lane ever sees
the other's.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

/-! ## `EnvS` is an `EnvR`

**Task #161 S5 — this file is model-free apart from the projection
below.**  Ten of its signatures took `m : EnvS V env`; every one used
it only through `EnvS.toEnvR`, so all ten were re-signed to
`EnvR env` and **not one proof line changed**.  `declDefnR`,
`declThmR`, `declOpaqueR`, `declAxiomR`, `natEqsBridge_of`,
`natFrag_subst_denotes`, `natEqFrame_of_frag`, `natEqsR_of_certs`,
`reducePinR_of` and `divModPinR_of` therefore carry no `V` at all, and
`checkDeclR_ofEnvR` (`Bridge/Sound.lean`) assembles the five non-`ind`
kinds without a model.  The `ind` kind is `Bridge/DeclInd.lean`'s, and
its obstacle is finding 8 (the member fold's intermediate `EnvR`s),
not the records.

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
  -- task #161 item B3: the guard, read off `nat_ops`/`div_mod` (the
  -- guard does not mention the level valuation, so any `φ` serves)
  nat_op_guard := fun c hmem hst => by
    obtain ⟨cv, v, hh, hf⟩ := natOpStored_inv hst
    rcases hmem with hm | hm
    · exact (m.nat_ops (fun _ => 0) c hm cv v hh hf).1
    · exact (m.div_mod (fun _ => 0) c hm cv v hh hf).1

end Setlec.SetR
