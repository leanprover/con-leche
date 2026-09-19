module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.CtxOkKit

public section

/-!
# The soundness of the reduction rules (task #305, lanes S-red / S-iota)

One lemma per constructor of `Red`: the motives of its derivation
premises (the induction hypotheses) and its side conditions give the
motive of its conclusion.  The master induction (`Sound.lean`) is the
only place that mentions derivations; these lemmas are pure semantics
and mine the corresponding rows of `Model/Steps/*` — the file and
theorem each docstring names.

Lane S-red owns this file; `iota` and the three rescues are in
`IotaSound.lean` (lane S-iota).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

theorem Red.refl_sound {d : Nat} {e : Expr} : RedSem m φ d e e := by
  intro hf Δa ea _ hea hg
  exact ⟨hf, fun _ hl => hl, ea, hea, hg, fun _ _ => rfl⟩

theorem Red.trans_sound {d : Nat} {e₁ e₂ e₃ : Expr}
    (h₁ : RedSem m φ d e₁ e₂) (h₂ : RedSem m φ d e₂ e₃) :
    RedSem m φ d e₁ e₃ := by
  intro hf Δa ea hC hea hg
  obtain ⟨hf₂, hsub₂, ea₂, hea₂, hg₂, heq₂⟩ := h₁ hf hC hea hg
  obtain ⟨hf₃, hsub₃, ea₃, hea₃, hg₃, heq₃⟩ :=
    h₂ hf₂ (hC.of_subset hsub₂) hea₂ hg₂
  exact ⟨hf₃, fun l hl => hsub₂ l (hsub₃ l hl), ea₃, hea₃, hg₃,
    fun ρ hρ => (heq₂ ρ hρ).trans (heq₃ ρ hρ)⟩

/-- `whnfCore_app_claim`'s head-reduction half (`Steps/Whnf.lean:509`)
+ `frame_appFn` (`Stuck.lean:206`). -/
theorem Red.appFn_sound (hin : RulesInputs V m φ) {d : Nat} {f f' a : Expr}
    (hf : RedSem m φ d f f') : RedSem m φ d (.app f a) (.app f' a) := by
  sorry

/-- The `.proj` clause's scrutinee reduction (`projStep_of_claims`'s
stuck branch, `Steps/ProjRows.lean:278`; `WellDenotedV_projAV_congr`). -/
theorem Red.projArg_sound (hin : RulesInputs V m φ) {d : Nat} {sn : Name}
    {i : Nat} {e e' : Expr} (he : RedSem m φ d e e') :
    RedSem m φ d (.proj sn i e) (.proj sn i e') := by
  sorry

/-- `WellDenotedV_beta_gate` (`Steps/Gate.lean:80`) + `denoteMeta_beta`. -/
theorem Red.betaGate_sound (hin : RulesInputs V m φ) {d : Nat}
    {ty body a : Expr} {mb : BinderMeta} (hnev : mb.pw.isNever = true) :
    RedSem m φ d (.app (.lam ty body mb) a) (body.instantiate1 a) := by
  sorry

/-- `WellDenotedV_beta_pos` / `WellDenotedV_beta_zero` with the
certificate's membership (`betaCert_of_claims`, `Steps/Whnf.lean:424`). -/
theorem Red.beta_sound (hin : RulesInputs V m φ) {d : Nat}
    {ty body a ta : Expr} {mb : BinderMeta}
    (hta : InferSemIO m φ d a ta) (hd : DefEqSem m φ d ta ty) :
    RedSem m φ d (.app (.lam ty body mb) a) (body.instantiate1 a) := by
  sorry

/-- The δ identity (`delta_of`, `Steps/Whnf.lean:329`: the same
annotation reads the unfolding) + `unfoldDefinition_WScoped`. -/
theorem Red.delta_sound (hin : RulesInputs V m φ) {d : Nat} {e e' : Expr}
    (h : ConLeche.unfoldDefinition env e = some e') : RedSem m φ d e e' := by
  sorry

/-- `denoteMeta_litToCtorIfNat` + `frame_litToCtorIfNat`
(`Steps/Major.lean:66`, `:92`). -/
theorem Red.natLit_sound {d n : Nat} (h : ConLeche.natLitSupported env = true) :
    RedSem m φ d (.lit (.natVal n)) (natLitToConstructor n) := by
  sorry

/-- `denotePStrLit_of_guard` (`Steps/Stuck.lean:540`). -/
theorem Red.strLit_sound {d : Nat} {s : String}
    (h : ConLeche.strLitSupported env = true) :
    RedSem m φ d (.lit (.strVal s)) (strLitToConstructor s) := by
  sorry

/-- The successor row at the reduced argument (`NatSuccRow`). -/
theorem Red.natSucc_sound (hin : RulesInputs V m φ) {d : Nat} {a w : Expr}
    {n : Nat} (hsup : ConLeche.natLitSupported env = true)
    (hw : RedSem m φ d a w) (hn : ConLeche.rawNatLit? w = some n) :
    RedSem m φ d (.app (.const natSuccName []) a) (.lit (.natVal (n + 1))) := by
  sorry

/-- The binary row at the reduced arguments (`NatOpRow`). -/
theorem Red.natOp_sound (hin : RulesInputs V m φ) {d : Nat} {c : Name}
    {a wa b wb r : Expr} {n₁ n₂ : Nat}
    (hc : c ∈ natBinOpNames) (hst : ConLeche.natOpStored env c = true)
    (hwa : RedSem m φ d a wa) (hn₁ : ConLeche.rawNatLit? wa = some n₁)
    (hwb : RedSem m φ d b wb) (hn₂ : ConLeche.rawNatLit? wb = some n₂)
    (hr : ConLeche.natOpResult c n₁ n₂ = some r) :
    RedSem m φ d (.app (.app (.const c []) a) b) r := by
  sorry

/-- The tower law's iota clause at a certified spine (`projStep_of_claims`'s
firing branch, `Steps/ProjRows.lean:278`; `teleFit_of_teleFitPA`). -/
theorem Red.proj_sound (hin : RulesInputs V m φ) {d : Nat} {sn : Name} {i : Nat}
    {e : Expr} {entry : ProjEntry} {us : List Level} {cvC : ConstantVal}
    {nP nF : Nat}
    (hent : env.findProj? sn i = some entry)
    (hhead : e.getAppFn = .const entry.ctor us)
    (hi : i < entry.numFields)
    (hlen : e.getAppArgs.length = entry.numParams + entry.numFields)
    (hus : us.length = entry.levelParams.length)
    (hfire : entry.fireOk us = true)
    (hctor : env.find? entry.ctor = some (.ctorInfo cvC nP nF))
    (hcerts : CertsSem m φ d true
      (cvC.type.instantiateLevelParams cvC.levelParams us) e.getAppArgs) :
    RedSem m φ d (.proj sn i e)
      (e.getAppArgs.getD (entry.numParams + i) (.bvar 0)) := by
  sorry

end ConLeche.Model.Rules
