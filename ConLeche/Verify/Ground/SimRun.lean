module

public import ConLeche.Verify.Ground.SimStep
public import ConLeche.Verify.Ground.SimBridge
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Ground.Fuel
import ConLeche.Verify.Ground.Sound
import ConLeche.Verify.Ground.Step1N
import ConLeche.Verify.Ground.SimStep0
import ConLeche.Verify.Ground.SimStep4
import ConLeche.Verify.Ground.SimStep3
import ConLeche.Verify.Ground.SimStep1
import ConLeche.Verify.Ground.SimStep1P
import ConLeche.Verify.Ground.SimStep1N
import ConLeche.Verify.Ground.SimStep1I

public section

/-!
# The step simulation, assembled (task #423 soundness, layer (d), item 2(c))

`sim_mode1` dispatches mode 1 on the frame on top; `sim_run` is the
induction over the first run's fuel, as `run_sound`: two runs with two
lookups agreeing on `N`, from related states, end alike (`OutRel`) once the
second has twice the first's fuel.
-/

namespace ConLeche.Verify.Ground

open ConLeche

section
variable {N : Name → Prop} {env : Env} {f₂ : Name → Option ConstantInfo}
  {p₂ : Name → Nat → Option ProjEntry} {t₀ : Expr} {n : Nat}

/-- **Mode 1**, by the frame on top. -/
theorem sim_mode1 (hwf : EnvWF env) (hag : LookAgree N env.find? env.findProj? f₂ p₂)
    (hsN : strLitStored env = true → StrNames N) (ih : SimAt N env f₂ p₂ t₀ n)
    {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 1) {m : Nat} (hmn : 2 * (n + 1) ≤ m) :
    OutRel N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
  rcases Nat.eq_zero_or_pos sA.fs.size with h0 | hn
  · exact sim_mode1a ih h hR hr hm (.inl h0) (by omega)
  by_cases h1 : sA.fs[sA.fs.size - 1]! &&& 15 = 1
  · exact sim_mode1a ih h hR hr hm (.inr (.inl h1)) (by omega)
  by_cases h2 : sA.fs[sA.fs.size - 1]! &&& 15 = 2
  · exact sim_mode1a ih h hR hr hm (.inr (.inr h2)) (by omega)
  by_cases h3 : sA.fs[sA.fs.size - 1]! &&& 15 = 3
  · exact sim_mode1i hwf hag hsN ih h hR hr hm hn h3 hmn
  by_cases h4 : sA.fs[sA.fs.size - 1]! &&& 15 = 4
  · exact sim_mode1p hag hsN ih h hR hr hm hn h4 (by omega)
  by_cases h7 : sA.fs[sA.fs.size - 1]! &&& 15 = 7
  · exact sim_mode1s ih h hR hr hm hn h7 (by omega)
  exact sim_mode1n hag ih h hR hr hm hn (FS.top_lit h.stack hn h1 h2 h3 h4 h7) (by omega)

/-- **The simulation**, by induction over the first run's fuel. -/
theorem sim_run (hwf : EnvWF env) (hag : LookAgree N env.find? env.findProj? f₂ p₂)
    (hsN : strLitStored env = true → StrNames N) (t₀ : Expr) : ∀ n, SimAt N env f₂ p₂ t₀ n
  | 0 => fun _ _ _ _ _ _ _ _ _ => by
    unfold MS.run; rw [g4Run.eq_1]; exact .inl ⟨_, rfl⟩
  | n + 1 => fun sA sB oc fl h hR hr m hmn => by
    have ih := sim_run hwf hag hsN t₀ n
    have hle := h.mode_le
    rcases hm : sA.mode with _ | _ | _ | _ | _ | md
    · exact sim_mode0 hag ih h hR hr hm hmn
    · exact sim_mode1 hwf hag hsN ih h hR hr hm hmn
    · exact sim_mode2 ih h hR hr hm hmn
    · exact sim_mode3 hwf hag ih h hR hr hm hmn
    · exact sim_mode4 hag ih h hR hr hm hmn
    · omega

end

end ConLeche.Verify.Ground
