import Setlec.Model.Consistency
import Setlec.Model.RawEnv

/-!
# The soundness interface, over `RawEnvModelE` (task #100, stage 3)

The consistency results are restated over the erasure-parameterized
model (`Setlec/Model/RawEnv.lean`) at the **identity erasure**.  This
is the transitional step of the raw-storage refactor: annotations are
still stored and still live, so the witness environment *is* the stored
environment and every statement below is `checkDecl_sound` &co. after
`RawEnvModelE.ofEnvModel`/`toEnvModel`.

The point is not the content — it is the *interface*.  Downstream
consumers phrased against `RawEnvModelE` keep working verbatim when the
erasure is swapped for `Env.eraseCod`; only the proofs below have to
be replaced then, and only they.  `Setlec/Model/Decorate.lean` supplies
what those replacements will consume: the annotated twin of a stored
raw tree, recovered exactly (`decorate_eq`) and truthfully
(`decorate_sound`).
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {F : Nat}

/-- `checkDecl_sound` over the raw-model interface (identity erasure). -/
theorem checkDecl_sound_raw {env env' : Env} {d : Declaration}
    (h : checkDecl (fueledOps F) env d = .ok env') (M : RawEnvModelId V env)
    (hE1 : EtaFamiliesClosed env) :
    Nonempty (RawEnvModelId V env') ∧ EtaFamiliesClosed env' := by
  obtain ⟨hm, hE⟩ := checkDecl_sound h M.toEnvModel hE1
  obtain ⟨m'⟩ := hm
  exact ⟨⟨RawEnvModelE.ofEnvModel m'⟩, hE⟩

/-- `checkDecls_sound` over the raw-model interface. -/
theorem checkDecls_sound_raw {ds : List Declaration} {env' : Env}
    (h : checkDecls (fueledOps F) ds = .ok env') :
    Nonempty (RawEnvModelId V env') := by
  obtain ⟨m⟩ := checkDecls_sound (V := V) h
  exact ⟨RawEnvModelE.ofEnvModel m⟩

/-- The consistency core over the raw-model interface: a modeled
environment stores no constant of type `Empty`.  Stated through the
witness, so the flip only has to re-establish the lookup transfer
(`RawEnvModelE.consts_eraseCod`), not the argument. -/
theorem no_constant_of_Empty_raw {env : Env} (M : RawEnvModelId V env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False :=
  no_constant_of_Empty M.toEnvModel c hc hty

end Setlec
