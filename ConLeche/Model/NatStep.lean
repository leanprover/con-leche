module

public import ConLeche.Model.NatWf
import ConLeche.Model.Rules.Inputs

public section

/-!
# The literal tier's two semantic rows (task #161, #305)

`Rules.NatSuccRow` and `Rules.NatOpRow` (`Model/Rules/Inputs.lean`),
discharged: the `Nat`-literal reduction's branch analysis at the
`denote` currency, standing on `EnvModelM.nat_ops` and
`EnvModelM.div_mod` (the recurrence laws, from the run certificates)
and the sixteen numeral transports (`Model/NatSem.lean`,
`Model/NatWf.lean`).  `Model/Capstone.lean`'s `Rules.RulesInputs.ofSem`
reads the two theorems below into the bundle.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported natOpResult reduceNatFueled)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}

/-! ## The pieces the rows read -/

/-- Whatever `rawNatLit?` accepts reads to the numeral spine it
reports — its two shapes are the literal itself and the `Nat.zero`
constant, and `natLit … 0` *is* the `Nat.zero` leaf. -/
theorem denote_rawNatLit (m : EnvModel V env)
    (hs : natLitSupported env = true) {a0 : Expr} {n : Nat}
    (h : ConLeche.rawNatLit? a0 = some n) (d : Nat) :
    denote m.acval env φ d a0 = some (natLit m φ n) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  match a0, h with
  | .lit (.natVal k), h =>
    obtain rfl : k = n := Option.some.inj h
    exact denote_natLit_spine m hs d k
  | .const c [], h =>
    simp only [ConLeche.rawNatLit?] at h
    split at h
    · next hc =>
      subst hc
      obtain rfl : (0 : Nat) = n := Option.some.inj h
      rw [natLit_zero]
      exact denote_levelless_const hfZ
        (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
          = [] from hlpZ)
    · exact nomatch h

/-- A stored level-monomorphic head's reading, inverted. -/
theorem denote_head {m : EnvModel V env} {d : Nat} {c : Name}
    {ci : ConstantInfo} {fa : Term}
    (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = [])
    (h : denote m.acval env φ d (.const c []) = some fa) :
    fa = m.acval c φ :=
  (Option.some.inj ((denote_levelless_const hf hlp).symm.trans h)).symm

/-! ## The two semantic rows

The literal accelerations' semantic content, at the shapes
`reduceNat` fires on and with the arguments already at literal
readings: `Rules.NatSuccRow` and `Rules.NatOpRow`
(`Model/Rules/Inputs.lean`).  The run inversion that puts a
`reduceNat` run into these shapes — the `whnf`/`rawNatLit?` case
analysis and the whnf IH at the two arguments — is the bridge's
`reduceNat_bridge` (`Verify/Rules/RedBridge.lean`), whose `Red.natSucc`/
`Red.natOp` derivations `Red.natSucc_sound`/`Red.natOp_sound` read
through these rows; the old run rows went with `Model/Steps/*` at the
task #305 closing. -/

/-- **`NatSuccRow`, proved.**  At a literal reading of the argument
the `Nat.succ` application *is* the packed numeral: the head reads to
the `Nat.succ` leaf, the argument to the numeral spine, and
`natLit_succ` is the packing. -/
theorem natSuccRow_of (mp : EnvModelM V env) (φ : Name → Nat) :
    Rules.NatSuccRow mp.base2 φ := by
  intro d w n ea hnat hraw hea
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hnat
  obtain ⟨fa, wa, hfa, hwa, rfl⟩ := denote_app_inv hea
  obtain rfl : fa = mp.base2.acval ConLeche.natSuccName φ :=
    denote_head hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS) hfa
  obtain rfl : wa = natLit mp.base2 φ n :=
    Option.some.inj
      (hwa.symm.trans (denote_rawNatLit mp.base2 hnat hraw d))
  refine ⟨natLit mp.base2 φ (n + 1),
    denote_natLit_spine mp.base2 hnat d (n + 1), fun ρ hg => ⟨?_, ?_⟩⟩
  · rw [natLit_succ]
    exact hg
  · rw [natLit_succ]

set_option maxHeartbeats 1600000 in
/-- **`NatOpRow`, proved.**  The fourteen certified binary operations
at two literal readings: the head reads to the stored operation's
leaf, the arguments to the numeral spines, and the operation's own
recurrence law (`EnvModelM.nat_ops` / `EnvModelM.div_mod`, through the
`natOpV_*` transports) computes the interpretation of `natOpResult`. -/
theorem natOpRow_of (mp : EnvModelM V env) (φ : Name → Nat) :
    Rules.NatOpRow mp.base2 φ := by
  intro d c wa wb r n₁ n₂ ea hc hstored hrawa hrawb hres hea
  have h14 : c = ConLeche.natAddName ∨ c = ConLeche.natSubName ∨
      c = ConLeche.natMulName ∨ c = ConLeche.natPowName ∨
      c = ConLeche.natBeqName ∨ c = ConLeche.natBleName ∨
      c = ConLeche.natDivName ∨ c = ConLeche.natModName ∨
      c = ConLeche.natGcdName ∨ c = ConLeche.natLandName ∨
      c = ConLeche.natLorName ∨ c = ConLeche.natXorName ∨
      c = ConLeche.natShiftLeftName ∨ c = ConLeche.natShiftRightName := by
    simpa [_root_.ConLeche.Rules.natBinOpNames, ConLeche.natDivModNames]
      using hc
  have hmemN : c ∈ ConLeche.natOpNames ∨ c ∈ ConLeche.natDivModNames := by
    rcases h14 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact Or.inl (by decide)
      | exact Or.inr (by decide)
  have hguard := natOpGuardLaw_of mp _ hmemN hstored
  obtain ⟨hnat, hdeps, hbool⟩ := ConLeche.natOpGuard_inv hguard
  have hself : c ∈ ConLeche.natOpDeps c := by
    rcases h14 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
      rfl|rfl <;> decide
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps c hself
  obtain ⟨fab, ba, hfab, hba', rfl⟩ := denote_app_inv hea
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denote_app_inv hfab
  obtain rfl : fa = mp.base2.acval c φ :=
    denote_head hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc) hfa
  obtain rfl : aa = natLit mp.base2 φ n₁ :=
    Option.some.inj
      (haa.symm.trans (denote_rawNatLit mp.base2 hnat hrawa d))
  obtain rfl : ba = natLit mp.base2 φ n₂ :=
    Option.some.inj
      (hba'.symm.trans (denote_rawNatLit mp.base2 hnat hrawb d))
  -- the two reduct shapes `natOpResult` can take
  have close : ∀ K : Nat, r = .lit (.natVal K) →
      (∀ ρ : Nat → V, SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval c φ))
        (interp V ρ (natLit mp.base2 φ n₁)))
        (interp V ρ (natLit mp.base2 φ n₂))
        = interp V ρ (natLit mp.base2 φ K)) →
      ∃ ra, denote mp.base2.acval env φ d r = some ra ∧
        ∀ ρ : Nat → V, WellDenoted V ρ ((.app (.app (mp.base2.acval c φ)
              (natLit mp.base2 φ n₁)) (natLit mp.base2 φ n₂) : Term)) →
          WellDenoted V ρ ra ∧
          interp V ρ ((.app (.app (mp.base2.acval c φ)
              (natLit mp.base2 φ n₁)) (natLit mp.base2 φ n₂) : Term))
            = interp V ρ ra := by
    intro K hr hop
    subst hr
    refine ⟨natLit mp.base2 φ K,
      denote_natLit_spine mp.base2 hnat d K, fun ρ _ => ⟨?_, ?_⟩⟩
    · exact (natLit_facts mp.base2 (mp.nat_heads φ) hnat
        ρ K).1
    · rw [interp_app, interp_app]
      exact hop ρ
  have closeB : (c = ConLeche.natBeqName ∨ c = ConLeche.natBleName) →
      ∀ bn : Name,
      (bn = ConLeche.boolTrueName ∨ bn = ConLeche.boolFalseName) →
      r = .const bn [] →
      (∀ ρ : Nat → V, SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval c φ))
        (interp V ρ (natLit mp.base2 φ n₁)))
        (interp V ρ (natLit mp.base2 φ n₂))
        = interp V ρ (mp.base2.acval bn φ)) →
      ∃ ra, denote mp.base2.acval env φ d r = some ra ∧
        ∀ ρ : Nat → V, WellDenoted V ρ ((.app (.app (mp.base2.acval c φ)
              (natLit mp.base2 φ n₁)) (natLit mp.base2 φ n₂) : Term)) →
          WellDenoted V ρ ra ∧
          interp V ρ ((.app (.app (mp.base2.acval c φ)
              (natLit mp.base2 φ n₁)) (natLit mp.base2 φ n₂) : Term))
            = interp V ρ ra := by
    intro hcb bn hbn hr hop
    subst hr
    obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ := hbool
      (by rcases hcb with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl))
    have hread : denote mp.base2.acval env φ d (.const bn [])
        = some (mp.base2.acval bn φ) := by
      rcases hbn with rfl | rfl
      · exact denote_levelless_const hfT hlpT
      · exact denote_levelless_const hfF hlpF
    refine ⟨mp.base2.acval bn φ, hread, fun ρ _ => ⟨?_, ?_⟩⟩
    · exact mp.base2.acval_wellDenoted _ _ ρ
    · rw [interp_app, interp_app]
      exact hop ρ
  rcases h14 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_add mp.base2 (mp.nat_ops φ) (mp.nat_heads φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_sub mp.base2 (mp.nat_ops φ) (mp.nat_heads φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_mul mp.base2 (mp.nat_ops φ) (mp.nat_heads φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_pow mp.base2 (mp.nat_ops φ) (mp.nat_heads φ) hfc ρ n₁ n₂)
  · refine closeB (Or.inl rfl)
      (if n₁ = n₂ then ConLeche.boolTrueName else ConLeche.boolFalseName)
      (by by_cases hh : n₁ = n₂ <;> simp [hh])
      (by simpa +decide [natOpResult] using hres.symm) ?_
    exact fun ρ => natOpV_beq mp.base2 (mp.nat_ops φ) (mp.nat_heads φ) hfc ρ n₁ n₂
  · refine closeB (Or.inr rfl)
      (if n₁ ≤ n₂ then ConLeche.boolTrueName else ConLeche.boolFalseName)
      (by by_cases hh : n₁ ≤ n₂ <;> simp [hh])
      (by simpa +decide [natOpResult] using hres.symm) ?_
    exact fun ρ => natOpV_ble mp.base2 (mp.nat_ops φ) (mp.nat_heads φ) hfc ρ n₁ n₂
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_div (mp.nat_ops φ) (mp.nat_heads φ)
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_mod (mp.nat_ops φ) (mp.nat_heads φ)
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_gcd (mp.nat_ops φ) (mp.nat_heads φ)
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_land (mp.nat_ops φ) (mp.nat_heads φ)
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_lor (mp.nat_ops φ) (mp.nat_heads φ)
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_xor (mp.nat_ops φ) (mp.nat_heads φ)
        (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_shiftLeft (mp.nat_ops φ) (mp.nat_heads φ) (mp.div_mod φ) hfc ρ n₁ n₂)
  · exact close _ (by simpa +decide [natOpResult] using hres.symm)
      (fun ρ => natOpV_shiftRight (mp.nat_ops φ) (mp.nat_heads φ) (mp.div_mod φ) hfc ρ n₁ n₂)

/-- **`NatOpHead`, proved.**  A stored operation the rule fires on keeps
its pinned type `Nat → Nat → cod` in its `EnvModelM.nat_ops`/`div_mod`
entry; its leaf inhabits that type's reading (`mem_type`), a two-step
function space over the `Nat` leaf, its regimes read off the values. -/
theorem natOpHead_of (mp : EnvModelM V env) (φ : Name → Nat) :
    Rules.NatOpHead mp.base2 φ := by
  intro c hc hst
  have h14 : c = ConLeche.natAddName ∨ c = ConLeche.natSubName ∨
      c = ConLeche.natMulName ∨ c = ConLeche.natPowName ∨
      c = ConLeche.natBeqName ∨ c = ConLeche.natBleName ∨
      c = ConLeche.natDivName ∨ c = ConLeche.natModName ∨
      c = ConLeche.natGcdName ∨ c = ConLeche.natLandName ∨
      c = ConLeche.natLorName ∨ c = ConLeche.natXorName ∨
      c = ConLeche.natShiftLeftName ∨ c = ConLeche.natShiftRightName := by
    simpa [_root_.ConLeche.Rules.natBinOpNames, ConLeche.natDivModNames]
      using hc
  have hmemN : c ∈ ConLeche.natOpNames ∨ c ∈ ConLeche.natDivModNames := by
    rcases h14 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact Or.inl (by decide)
      | exact Or.inr (by decide)
  have hnp : ¬(c = ConLeche.natPredName) := by
    rcases h14 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨cv, v, hh, hf⟩ := ConLeche.natOpStored_inv hst
  obtain ⟨hguard, hpin⟩ : natOpGuard env c = true ∧
      ConLeche.natOpTyPinned env c cv.type = true := by
    rcases hmemN with hm | hm
    · exact ⟨(mp.nat_ops φ c hm cv v hh hf).1, (mp.nat_ops φ c hm cv v hh hf).2.1⟩
    · exact ⟨(mp.div_mod φ c hm cv v hh hf).1, (mp.div_mod φ c hm cv v hh hf).2.1⟩
  obtain ⟨hnat, hdeps, -⟩ := ConLeche.natOpGuard_inv hguard
  refine ⟨hnat, fun {d ca} hca ρ => ?_⟩
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, -, -, hlpN, -⟩ :=
    ConLeche.natLitSupported_inv hnat
  obtain ⟨cod, hty, hcodB, hcodN⟩ := natOpTyPinned_shape_bin hnp hpin
  -- the head reads to the operation's leaf
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps c (ConLeche.mem_natOpDeps_self hmemN)
  rw [hf] at hfc
  obtain ⟨rfl, -, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hfc)
  obtain rfl : ca = mp.base2.acval c φ :=
    denote_head hf
      (show (ConstantInfo.defnInfo cv v hh).toConstantVal.levelParams = [] from hlpc) hca
  -- the codomain is a stored level-free constant
  obtain ⟨codN, codCi, rfl, hcodF, hcodLp⟩ : ∃ codN codCi,
      cod = .const codN [] ∧ env.find? codN = some codCi ∧
        codCi.toConstantVal.levelParams = [] := by
    by_cases hb : c = ConLeche.natBeqName ∨ c = ConLeche.natBleName
    · obtain ⟨rfl, ciB, hfB, hlpB⟩ := hcodB hb
      exact ⟨_, ciB, rfl, hfB, hlpB⟩
    · rw [hcodN hb]
      exact ⟨_, _, rfl, hfN,
        show (ConstantInfo.indInfo cvN caps).toConstantVal.levelParams = [] from hlpN⟩
  -- the leaf inhabits the pinned type's reading
  have hta : denote mp.base2.acval env φ 0
      (ConstantInfo.defnInfo cv v hh).toConstantVal.type
      = some (.pi (mp.base2.acval ConLeche.natName φ)
          (.pi (mp.base2.acval ConLeche.natName φ)
            (mp.base2.acval codN φ))) := by
    show denote mp.base2.acval env φ 0 cv.type = _
    rw [hty]
    exact denote_pinnedBinTy mp.base2 φ hfN
      (show (ConstantInfo.indInfo cvN caps).toConstantVal.levelParams = [] from hlpN)
      hcodF hcodLp
  have hmem := mp.mem_type _ (ConLeche.Env.find?_mem hf) φ _ hta ρ
  rw [show (ConstantInfo.defnInfo cv v hh).name = c from
    ConLeche.Env.find?_name hf, interp_pi] at hmem
  rw [substFn_nil]
  have hfib : (fun x => interp V (cons x ρ)
        ((.pi (mp.base2.acval ConLeche.natName φ)
          (mp.base2.acval codN φ)) : Term))
      = fun _ => piV (interp V ρ (mp.base2.acval ConLeche.natName φ))
          (fun _ => interp V ρ (mp.base2.acval codN φ)) := by
    funext x
    rw [interp_pi]
    congr 1
    · exact acval_interp_closed mp.base2 _ φ _ ρ
    · funext y
      exact acval_interp_closed mp.base2 _ φ _ ρ
  rw [hfib] at hmem
  unfold piV at hmem
  exact ⟨_, _, _, hmem⟩

end ConLeche.Model
