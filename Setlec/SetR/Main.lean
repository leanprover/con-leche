import Setlec.SetR.Bridge.Sound
import Setlec.Verify.BridgeWFDecl
import Setlec.Verify.DeclStores

/-!
# The `SetR` route's consistency theorems (task #148, T6)

The replacements for `Setlec/Model/Consistency*.lean`'s top-level
claims, on the algorithmic-relation route.  Three of the fourteen land
here — the ones over `checkDecls` at `fueledOps`.  The other eleven are
the `_S`/`_C`/`_SP` driver variants, each of which needs its *own*
fold soundness (`foldlM_soundS`, `foldlM_soundC`, `foldSP` in the
Model lane); they are a distinct shape and are tracked separately.

Every theorem here carries its obligations as **named hypotheses**,
all stated attached to an `EnvS`.  That is deliberate: the campaign's
recorded vacuity signature is a valuation with no invariant attached,
and these are the last place new hypotheses enter.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify SetTheory Expr
universe u w
variable {V : Type w} [SetTheory V]

theorem no_constant_of_Empty_R {env : Env} (m : EnvS V env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨t, hTi, hrest⟩ := m.mem_type c hc (fun _ => 0)
  rw [hty, denoteClosed, denote_const] at hTi
  revert hTi
  cases hf : env.find? emptyName with
  | none => intro hTi; exact nomatch hTi
  | some ci =>
    dsimp only
    split
    · next hlen =>
      intro hTi
      obtain rfl := (Option.some.inj hTi).symm
      obtain ⟨u0, hu0⟩ := m.empty_pinned
        (Level.substFn (fun _ => 0) ci.toConstantVal.levelParams [])
      obtain ⟨hmem, -⟩ := hrest (fun _ => (SetTheory.empty : V))
      rw [hu0, interp_emptyT] at hmem
      exact not_mem_empty _ hmem
    · intro hTi; exact nomatch hTi

/-- **The acceptance theorem, on the `SetR` route.** -/
theorem checkDecls_sound_R
    {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env') :
    Nonempty (EnvS V env') :=
  (foldlM_R
    ds Env.empty ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩ h).1

/-- **No proof of `Empty` is ever accepted**, on the `SetR` route. -/
theorem no_proof_of_Empty_R (V : Type w) [SetTheory V]
    {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_sound_R (V := V) h
  exact no_constant_of_Empty_R m c hc hty

/-- **One checked declaration extends the invariant.** -/
theorem checkDecl_sound_R
    {F : Nat}
    {env env₂ : Env} {d : Declaration} (m : EnvS V env)
    (hE : EtaFamiliesClosed env)
    (h : checkDecl modeR (fueledOps modeR F) env d = .ok env₂) :
    EnvSOk V env₂ :=
  declStepS divModPinS reducePinS stdAxiomKeyS declBasisS
    (declIndS memberKeyS) m hE
    (checkDeclR_sound m hE h)

/-- A declared `Empty`-typed `def`/`theorem` cannot survive the fold:
the stored constant would carry the annotated type, which annotation
leaves as `Empty`. -/
theorem foldlM_no_Empty_R
    {F : Nat}
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hty : cv.type = .const emptyName []) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvSOk V env →
      ds.foldlM (checkDecl modeR (fueledOps modeR F)) env = .ok env' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False
  | [], _, _, _, _, hd => by rcases hd with hd | hd <;> cases hd
  | d :: ds, env, env', hm, h, hd => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDecl modeR (fueledOps modeR F) env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
    rw [hdd] at h
    obtain ⟨⟨m⟩, hE⟩ := hm
    by_cases hdis : d = Declaration.defnDecl cv value hint ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hdd hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type := by
        have h1 : annotateCore modeR env F 0 (.const emptyName []) =
            .ok type := hann
        cases F with
        | zero =>
          rw [annotateCore_zero] at h1
          simp [throw, throwThe, MonadExceptOf.throw] at h1
        | succ F' =>
          rw [annotateCore_succ] at h1
          simpa [annotateBody, pure, Except.pure] using h1
      obtain ⟨m1⟩ := (checkDecl_sound_R (d := d)
        m hE hdd).1
      exact no_constant_of_Empty_R m1 c hc (by rw [hcv])
    · refine foldlM_no_Empty_R (value := value) (hint := hint)
        hty ds env1
        (checkDecl_sound_R (d := d) m hE hdd)
        h ?_
      rcases hd with hd | hd
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inl rfl) hdis
        · exact Or.inl hmem
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inr rfl) hdis
        · exact Or.inr hmem

/-- **No accepted stream declares a proof of `Empty`.** -/
theorem no_proof_of_Empty_input_R (V : Type w) [SetTheory V]
    {F : Nat}
     {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False :=
  foldlM_no_Empty_R hty ds Env.empty
    ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩ h hd


end Setlec.SetR