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

Lane S-red owns `refl` … `natOp` and `proj`; lane S-iota owns `iota`
and the three rescues.
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

/-- The ι row (`iotaStep_of`, `Steps/IotaRows.lean:492`, with
`iotaReads_of`, `:332`, for the reduct's reading): the stored
recursor's fired contract (`RecRules`) at the two certified telescopes
and the parameter/index comparisons. -/
theorem Red.iota_sound (hin : RulesInputs V m φ) {d : Nat} {e : Expr} {c : Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {major : Expr} {cj : Name} {usj : List Level} {cvj : ConstantVal}
    {cnP cnF : Nat} {rl : RecRule} {residual : Expr}
    (hhead : e.getAppFn = .const c us)
    (hrec : env.find? c = some (.recInfo cv mI rP rules))
    (hlen : e.getAppArgs.length = mI + 1)
    (hus : us.length = cv.levelParams.length)
    (hmajor : RedSem m φ d (e.getAppArgs.getD mI (.bvar 0)) major)
    (hmhead : major.getAppFn = .const cj usj)
    (hctor : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hrule : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hmlen : major.getAppArgs.length = rl.ctorParams + rl.nfields)
    (hfire : rl.fire ≠ .inert)
    (hlv : Level.isEquivList usj
      (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
        e.getAppArgs rP).1 = some true)
    (hparams : rl.compareParams = true →
      DefEqListSem m φ d (major.getAppArgs.take rl.ctorParams)
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).2)
    (hcertR : CertsSem m φ d true (cv.type.instantiateLevelParams cv.levelParams us)
      (e.getAppArgs.take mI ++ [major]))
    (hcertC : CertsSem m φ d true
      (cvj.type.instantiateLevelParams cvj.levelParams usj) major.getAppArgs)
    (hres : mI ≠ rP →
      ConLeche.piResidual (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs = some residual)
    (hidx : mI ≠ rP →
      DefEqListSem m φ d (residual.getAppArgs.drop rl.ctorParams)
        ((e.getAppArgs.take mI).drop rP)) :
    RedSem m φ d e
      (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
        (e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams)) := by
  sorry

/-- The K rescue (`majorToCtorFueled_step`'s K arm, `Steps/Major.lean:383`,
with `majorToCtorFueled_reads`, `:178`): the fabrication reads and is
graded by the certified constructor telescope (`certs_telePA`), and
proof irrelevance equates it to the major. -/
theorem Red.rescueK_sound (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab tf : Expr} {recName : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat} {T : Name}
    {tus ust : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl]))
    (hk : rl.k = true)
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hres : (cvj.type.piResult).getAppFn = .const T tus)
    (hind : env.find? T = some (.indInfo cvT caps))
    (htm : InferSemIO m φ d major tm) (htmaj : RedSem m φ d tm tmaj)
    (hthead : tmaj.getAppFn = .const T ust)
    (hlv : cvj.levelParams.length = ust.length)
    (hnP : cnP ≤ tmaj.getAppArgs.length)
    (hfab : fab = Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsSem m φ d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs.take cnP))
    (htf : InferSemIO m φ d fab tf) (hdt : DefEqSem m φ d tmaj tf)
    (hpi : DefEqSem m φ d fab major) :
    RedSem m φ d major fab := by
  sorry

/-- The structure-η rescue (`majorToCtorFueled_step`'s η arm). -/
theorem Red.rescueEta_sound (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab : Expr} {recName : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat} {T : Name}
    {tus ust : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl]))
    (heta : rl.eta = true)
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hres : (cvj.type.piResult).getAppFn = .const T tus)
    (hind : env.find? T = some (.indInfo cvT caps))
    (htm : InferSemIO m φ d major tm) (htmaj : RedSem m φ d tm tmaj)
    (hthead : tmaj.getAppFn = .const T ust)
    (hlen : tmaj.getAppArgs.length = caps.etaParams)
    (hlv : ust.length = cvT.levelParams.length)
    (hnz : ConLeche.capsNeverZero cvT.levelParams ust caps = true)
    (hfab : fab = Expr.mkAppN (.const caps.etaCtor ust)
      (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsSem m φ d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
    (hpi : DefEqSem m φ d fab major) :
    RedSem m φ d major fab := by
  sorry

/-- The `And` rescue (`majorToCtorFueled_step`'s `And` arm). -/
theorem Red.rescueAnd_sound (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab tf : Expr} {recName : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat}
    {tus ust : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl]))
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hres : (cvj.type.piResult).getAppFn = .const andName tus)
    (hind : env.find? andName = some (.indInfo cvT caps))
    (htm : InferSemIO m φ d major tm) (htmaj : RedSem m φ d tm tmaj)
    (hthead : tmaj.getAppFn = .const andName ust)
    (hlen : tmaj.getAppArgs.length = cnP)
    (hlv : cvj.levelParams.length = ust.length)
    (hslots : ConLeche.andRescueSlots env rl.ctor cnP ust = true)
    (hfab : fab = Expr.mkAppN (.const rl.ctor ust)
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsSem m φ d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]))
    (htf : InferSemIO m φ d fab tf) (hdt : DefEqSem m φ d tmaj tf)
    (hpi : DefEqSem m φ d fab major) :
    RedSem m φ d major fab := by
  sorry

end ConLeche.Model.Rules
