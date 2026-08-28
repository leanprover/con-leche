import Setlec.SetR.Bridge.DeclInd
import Setlec.Verify.NatOpFrag

/-!
# The assembly (task #148, T6)

`checkDecl` → `DeclR` by dispatch, and the `checkDecls` fold that
carries the `EnvS` invariant along it.  This is the transpose of the
TT lane's `checkDeclTT` / `foldlM_TT` pair
(`Setlec/TTVerify/Consistency.lean`).

Three per-declaration bridge obligations stay **named hypotheses**
here rather than being discharged: the `Nat` equation certificates,
the div/mod pins and the reduce pins.  Each is stated *attached* — it
quantifies over an `EnvS V env` and speaks at that `m`'s own
valuation — which is what keeps it dischargeable (an unattached
valuation in a semantic hypothesis is the campaign's recorded vacuity
signature).
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify SetTheory
universe w
variable {V : Type w} [SetTheory V]

/-- **The direct-structure path is compile-time disabled**
(`directStructsEnabled = false`), so `checkDecl`'s `indDecl` clause
*is* `checkIndDecl`.  `DeclR` records the modeled path only, and this
is the single place that dependence is discharged — worth its own
name so the audit can find it. -/
theorem directParts?_none (env : Env) (block : List ConstantInfo) :
    directParts? env block = none := by
  unfold directParts?
  cases directPartsCore? block with
  | none => rfl
  | some p => simp [directStructsEnabled]

/-- The frame package one side of a certified `Nat` recurrence needs:
the three syntactic facts, the `Nat`-annotated-leaf shape that the
canonical context matches, and the denotation. -/
def NatEqFrameR (cval : TConstVal) (env : Env) (e : Expr) : Prop :=
  Expr.WScoped 2 e ∧ e.looseBVarsBounded 0 = true ∧
  Expr.LeavesBounded e ∧
  (∀ l ∈ e.fvarLeaves, l.1 < 2 ∧ l.2.2 = .const natName []) ∧
  ∀ φ : Name → Nat, ∃ v, denote cval env φ 2 e = some v

/-- **`certifyNatEqs`, bridged.**  The verdict is `isDefEqCore` at
depth `2` on each pair; `DefEqClaimsR` turns it into the relation
family's `DefEq` once both sides have a frame package and a context.
The context is `CtxOkR.constCtx` at the pinned `Nat` entries — which
is exactly what the leaf-shape conjunct of `NatEqFrameR` is for. -/
theorem natEqsBridge_of {env : Env} (m : EnvS V env) {μ : CheckMode}
    {F : Nat} {ciN : ConstantInfo}
    (hnatE : env.find? natName = some ciN)
    (hnatL : ciN.toConstantVal.levelParams = [])
    : ∀ (eqs : List (Expr × Expr)),
      (∀ eq ∈ eqs, NatEqFrameR m.cval env eq.1 ∧
        NatEqFrameR m.cval env eq.2) →
      certifyNatEqs (m := CheckM) (fueledOps μ F) env eqs = .ok true →
      NatEqsR μ env m.cval eqs := by
  have hden : ∀ φ : Name → Nat, ∀ d : Nat,
      denote m.cval env φ d (.const natName [])
        = some (natVR m.cval φ) := by
    intro φ d
    rw [denote_const, hnatE]
    dsimp only
    rw [if_pos (by rw [hnatL]; rfl), hnatL]
    rfl
  intro eqs
  induction eqs with
  | nil => intro _ _ eq heq; exact nomatch heq
  | cons e rest ih =>
    intro hfr h eq heq φ
    simp only [certifyNatEqs, fueledOps_isDefEq, Bind.bind,
      Except.bind] at h
    by_cases hde : isDefEqCore μ env F 2 e.1 e.2 = .ok true
    case neg =>
      exfalso
      cases hx : isDefEqCore μ env F 2 e.1 e.2 with
      | error err => rw [hx] at h; exact nomatch h
      | ok b =>
        cases b with
        | true => exact hde hx
        | false =>
          rw [hx] at h
          simp only [Bool.false_eq_true, if_false, pure, Except.pure,
            Except.ok.injEq] at h
    rcases List.mem_cons.mp heq with rfl | heq'
    · obtain ⟨⟨hw1, hb1, hL1, hl1, hd1⟩, ⟨hw2, hb2, hL2, hl2, hd2⟩⟩ :=
        hfr eq List.mem_cons_self
      obtain ⟨L, hL⟩ := hd1 φ
      obtain ⟨R, hR⟩ := hd2 φ
      refine ⟨L, R, hL, hR, ?_⟩
      obtain ⟨-, -, ihd, -⟩ := checkBridge m.toEnvR φ F
      have hC1 : CtxOkR μ m.cval env φ 2
          (List.replicate 2 (natVR m.cval φ)) eq.1 :=
        CtxOkR.constCtx (m.cval_closed _ _) (hden φ 2) trivial hl1
      have hC2 : CtxOkR μ m.cval env φ 2
          (List.replicate 2 (natVR m.cval φ)) eq.2 :=
        CtxOkR.constCtx (m.cval_closed _ _) (hden φ 2) trivial hl2
      have := ihd hde hw1 hb1 hL1 hw2 hb2 hL2 hC1 hC2 hL hR
      exact this
    · rw [hde] at h
      simp only [if_true] at h
      exact ih (fun q hq => hfr q (List.mem_cons_of_mem _ hq)) h eq
        heq' φ

/-- **The fragment gives the frame package**, in one induction over
`natFragOk`'s four constructors.  The operation `c` is the one being
defined, so it is *not* stored: its occurrences are the ones
`substConst0` replaces, and the substituted value's own facts stand in
for them. -/
theorem natEqFrame_of_frag {env : Env} (m : EnvS V env) {c : Name}
    {v : Expr} (hvf : v.hasFvar = false)
    (hvb : v.looseBVarsBounded 0 = true)
    (hvd : ∀ φ : Name → Nat, ∃ V0, denote m.cval env φ 0 v = some V0) :
    ∀ {e : Expr}, natFragOk env c e = true →
      NatEqFrameR m.cval env (Expr.substConst0 c v e)
  | .sort u, _ => by
    rw [show Expr.substConst0 c v (Expr.sort u) = Expr.sort u from rfl]
    refine ⟨by rw [Expr.WScoped]; trivial, rfl, ?_, ?_,
      fun φ => ⟨_, by rw [denote_sort]⟩⟩
    · intro l hl; simp [Expr.fvarLeaves] at hl
    · intro l hl; simp [Expr.fvarLeaves] at hl
  | .fvar i n ty, h => by
    simp only [natFragOk, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    have hilt : i < 2 := by rcases hi with rfl | rfl <;> omega
    rw [show Expr.substConst0 c v (Expr.fvar i n (.const natName []))
      = Expr.fvar i n (.const natName []) from rfl]
    refine ⟨?_, rfl, ?_, ?_, fun φ => ⟨_, by rw [denote_fvar]⟩⟩
    · rw [Expr.WScoped]
      exact ⟨hilt, by rw [Expr.WScoped]; trivial⟩
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · rfl
      · simp [Expr.fvarLeaves] at hl'
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · exact ⟨hilt, rfl⟩
      · simp [Expr.fvarLeaves] at hl'
  | .const n us, h => by
    rw [show Expr.substConst0 c v (Expr.const n us)
      = (if n = c ∧ us = [] then v else Expr.const n us) from rfl]
    by_cases hn : n = c ∧ us.isEmpty = true
    · rw [if_pos (show n = c ∧ us = [] from
        ⟨hn.1, List.isEmpty_iff.mp hn.2⟩)]
      refine ⟨Expr.WScoped.mono (Nat.zero_le 2)
          (Expr.WScoped.of_not_hasFvar hvf), hvb,
        Expr.LeavesBounded.of_not_hasFvar hvf, ?_, fun φ => ?_⟩
      · intro l hl
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf] at hl
        exact nomatch hl
      · obtain ⟨V0, hV0⟩ := hvd φ
        exact opener_denotes_at m.toEnvR
          (Expr.WScoped.of_not_hasFvar hvf).fvarsBelow
          (Nat.zero_le 2) hV0
    · rw [if_neg (fun hh => hn ⟨hh.1, by rw [hh.2]; rfl⟩)]
      simp only [natFragOk, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rcases h with h' | h'
      · exact absurd h' hn
      · refine ⟨by rw [Expr.WScoped]; trivial, rfl, ?_, ?_,
          fun φ => ?_⟩
        · intro l hl; simp [Expr.fvarLeaves] at hl
        · intro l hl; simp [Expr.fvarLeaves] at hl
        revert h'
        cases hf : env.find? n with
        | none => intro hx; exact nomatch hx
        | some ci =>
          intro hx
          refine ⟨m.cval n (Level.substFn φ
            ci.toConstantVal.levelParams us), ?_⟩
          rw [denote_const, hf]
          dsimp only
          rw [if_pos (by simpa using hx)]
  | .app f a, h => by
    simp only [natFragOk, Bool.and_eq_true] at h
    obtain ⟨hwf, hbf, hLf, hlf, hdf⟩ :=
      natEqFrame_of_frag m hvf hvb hvd h.1
    obtain ⟨hwa, hba, hLa, hla, hda⟩ :=
      natEqFrame_of_frag m hvf hvb hvd h.2
    rw [show Expr.substConst0 c v (Expr.app f a)
      = Expr.app (Expr.substConst0 c v f) (Expr.substConst0 c v a)
      from rfl]
    refine ⟨by rw [Expr.WScoped]; exact ⟨hwf, hwa⟩, ?_, ?_, ?_,
      fun φ => ?_⟩
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hbf, hba⟩
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h' | h'
      · exact hLf l h'
      · exact hLa l h'
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h' | h'
      · exact hlf l h'
      · exact hla l h'
    · obtain ⟨vf, hvf'⟩ := hdf φ
      obtain ⟨va, hva'⟩ := hda φ
      exact ⟨_, by rw [denote_app, hvf', hva']⟩
  | .bvar _, h | .lam _ _ _ _, h | .forallE _ _ _ _, h
  | .letE _ _ _ _, h | .proj _ _ _, h | .lit _, h => by
    simp [natFragOk] at h

def NatEqsBridgeR (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) :
    Prop :=
  ∀ {env : Env} (m : EnvS V env) {eqs : List (Expr × Expr)},
    certifyNatEqs (m := CheckM) (fueledOps μ F) env eqs = .ok true →
    NatEqsR μ env m.cval eqs

def DivModPinBridgeR (V : Type w) [SetTheory V] (μ : CheckMode)
    (F : Nat) : Prop :=
  ∀ {env env' : Env} (m : EnvS V env) {n : Name} {v : Expr},
    natDivModNames.contains n = true →
    checkDivModPin (m := CheckM) (fueledOps μ F) env env' n = .ok () →
    DivModPinR μ F env env' m.cval n v

def ReducePinBridgeR (V : Type w) [SetTheory V] (μ : CheckMode)
    (F : Nat) : Prop :=
  ∀ {env env' : Env} (m : EnvS V env) {n : Name} {value : Expr},
    reduceOpNames.contains n = true →
    checkReducePin (m := CheckM) (fueledOps μ F) env env' n value
      = .ok () →
    ReducePinR μ F env env' m.cval n value

theorem checkDeclR_sound (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    (hnat : NatEqsBridgeR V μ F) (hdmR : DivModPinBridgeR V μ F)
    (hrpR : ReducePinBridgeR V μ F)
    {env env₂ : Env} (m : EnvS V env) {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂) :
    DeclR μ F m.cval env d env₂ :=
  checkDeclR_of
    (fun hh => declDefnR m (hnat m) (fun hn hp => hdmR m hn hp) hh)
    (fun hh => declThmR m hh)
    (fun hh => declOpaqueR m (fun hn hp => hrpR m hn hp) hh)
    (fun hh => declAxiomR m hh)
    (fun hh => declBasisR hh)
    -- the direct-structure path is compile-time disabled
    -- (`directStructsEnabled = false`), so `checkDecl`'s `indDecl`
    -- clause *is* `checkIndDecl`.  The `DeclR` relation records the
    -- modeled path only, and this is where that is discharged.
    (fun hh => declIndRS hkey heta m (by
      simpa [checkDecl, directParts?_none] using hh)) h

theorem foldlM_R (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    (hnat : NatEqsBridgeR V μ F) (hdmR : DivModPinBridgeR V μ F)
    (hrpR : ReducePinBridgeR V μ F)
    (hdm : DivModPinS V) (hrp : ReducePinS V) (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V) (hbas : DeclBasisS V) (hind : DeclIndS V) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      Nonempty (EnvS V env) →
      ds.foldlM (checkDecl μ (fueledOps μ F)) env = .ok env' →
      Nonempty (EnvS V env')
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl μ (fueledOps μ F) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨m⟩ := hm
      exact foldlM_R hkey heta hnat hdmR hrpR hdm hrp hstd hofr hbas
        hind ds env1
        (declStepS hdm hrp hstd hofr hbas hind m
          (checkDeclR_sound hkey heta hnat hdmR hrpR m hd)) h

end Setlec.SetR
