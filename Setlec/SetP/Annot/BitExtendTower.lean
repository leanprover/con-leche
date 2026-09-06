import Setlec.SetP.Annot.BitExtend
import Setlec.Verify.ProjSlots

/-!
# `denoteP` across a tower-entry cons (task #175 wiring, W4c S6)

`denoteP_envExtend_mono` refutes a tower head outright: its `hproj`
premise says every entry the extension adds is non-tower, because a
`.proj T i` node with *no* entry reads by the pair fallback and would
move under a tower entry at `(T, i)`.  The direct install conses
exactly such entries, so its transport needs the refinement below:
the extension may add **one** tower slot `(T, i)`, and the subject
has no `.proj T i` node (`Expr.NoProjAt`, `Verify/ProjSlots.lean`,
whose two dischargers cover every stored expression).  Every other
clause is `denoteP_envExtend_mono`'s verbatim.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

/-- **The monotone crossing, tower-slot refined**: a successful prefix
reading of a subject with no `.proj T i` node is reproduced at an
extension whose only new tower slot is `(T, i)`. -/
theorem denoteP_envExtend_mono_at {env₀ env : Env}
    {acval : Name → (Name → Nat) → AVExpr} {φ : Name → Nat}
    {T : Name} {i : Nat}
    (hF : FindPreserved env₀ env) (hG : LitGuardsMono env₀ env)
    (hproj : ∀ (sn : Name) (j : Nat) (entry : Setlec.ProjEntry),
      env₀.findProj? sn j = none → env.findProj? sn j = some entry →
      entry.tower = true → sn = T ∧ j = i) :
    ∀ (d : Nat) (e : Expr), ConstsBound env₀ e → Expr.NoProjAt T i e →
      ∀ {ea : AVExpr}, denoteP acval env₀ φ d e = some ea →
        denoteP acval env φ d e = some ea := by
  have hmono : ∀ (sn : Name) (j : Nat) (entry : Setlec.ProjEntry),
      env₀.findProj? sn j = some entry →
      env.findProj? sn j = some entry := by
    intro sn j entry h
    unfold Setlec.Env.findProj? at h ⊢
    cases hf0 : env₀.find? (Setlec.projFnName sn j) with
    | none => rw [hf0] at h; exact nomatch h
    | some ci =>
      rw [hf0] at h
      rw [hF hf0]
      exact h
  intro d e
  induction d, e using denoteP.induct (env := env₀) with
  | case1 d u => intro _ _ ea h; rw [denoteP] at h ⊢; exact h
  | case2 d idx nm ty => intro _ _ ea h; rw [denoteP] at h ⊢; exact h
  | case3 d n us ci hf hlen =>
    intro _ _ ea h
    rw [denoteP, hf] at h
    rw [denoteP, hF hf]
    exact h
  | case4 d n us ci hf hlen =>
    intro _ _ ea h
    rw [denoteP, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro hc _ ea h
    rw [constsBound_const, hf] at hc
    exact nomatch hc
  | case6 d n ty body m ihty ihbody =>
    intro hc hnp ea h
    rw [constsBound_forallE] at hc
    rw [Expr.noProjAt_forallE] at hnp
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    have hnpb : Expr.NoProjAt T i (body.instantiate1 (.fvar d n ty)) :=
      Expr.NoProjAt.instantiate1 (Expr.noProjAt_fvar.mpr hnp.1) _ _ hnp.2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteP_forallE_inv h
    rw [denoteP, ihty hc.1 hnp.1 hta, ihbody hcb hnpb hba]
    rfl
  | case7 d n ty body m ihty ihbody =>
    intro hc hnp ea h
    rw [constsBound_lam] at hc
    rw [Expr.noProjAt_lam] at hnp
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    have hnpb : Expr.NoProjAt T i (body.instantiate1 (.fvar d n ty)) :=
      Expr.NoProjAt.instantiate1 (Expr.noProjAt_fvar.mpr hnp.1) _ _ hnp.2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteP_lam_inv h
    rw [denoteP, ihty hc.1 hnp.1 hta, ihbody hcb hnpb hba]
    rfl
  | case8 d f a ihf iha =>
    intro hc hnp ea h
    rw [constsBound_app] at hc
    rw [Expr.noProjAt_app] at hnp
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteP_app_inv h
    rw [denoteP, ihf hc.1 hnp.1 hfa, iha hc.2 hnp.2 haa]
    rfl
  | case9 d n ty val body ihty ihval ihbody =>
    intro hc hnp ea h
    rw [constsBound_letE] at hc
    rw [Expr.noProjAt_letE] at hnp
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2.2
    have hnpb : Expr.NoProjAt T i (body.instantiate1 (.fvar d n ty)) :=
      Expr.NoProjAt.instantiate1 (Expr.noProjAt_fvar.mpr hnp.1) _ _ hnp.2.2
    rw [denoteP] at h
    rcases hta : denoteP acval env₀ φ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hva : denoteP acval env₀ φ d val with _ | va
    · rw [hva] at h; exact nomatch h
    rw [hva] at h
    rcases hba : denoteP acval env₀ φ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    rw [denoteP, ihty hc.1 hnp.1 hta, ihval hc.2.1 hnp.2.1 hva,
      ihbody hcb hnpb hba]
    exact h
  | case10 d sn j e ihe =>
    intro hc hnp ea h
    rw [constsBound_proj] at hc
    rw [Expr.noProjAt_proj] at hnp
    obtain ⟨ea', hea', hcase⟩ := denoteP_proj_inv h
    rcases hcase with ⟨entry, hfp0, htw, rfl⟩ | ⟨hnt0, hj, rfl⟩
    · -- a tower entry at the prefix persists unchanged
      rw [denoteP, ihe hc hnp.2 hea', hmono sn j entry hfp0]
      show (if entry.tower = true then some (projAV j ea')
          else if j < 2 then some (AVExpr.proj j ea') else none)
        = some (projAV j ea')
      rw [if_pos htw]
    · -- the pair path: any extension-side entry is still tower-free —
      -- the one slot that may have turned tower is `(T, i)`, and the
      -- subject has no node there
      rw [denoteP, ihe hc hnp.2 hea']
      cases hfp : env.findProj? sn j with
      | none =>
        show (if j < 2 then some (AVExpr.proj j ea') else none)
          = some (AVExpr.proj j ea')
        rw [if_pos hj]
      | some entry =>
        have hntw : entry.tower = false := by
          cases hfp0 : env₀.findProj? sn j with
          | some entry0 =>
            have hsame := hmono sn j entry0 hfp0
            rw [hfp] at hsame
            obtain rfl := Option.some.inj hsame
            exact hnt0 _ hfp0
          | none =>
            cases htw : entry.tower with
            | false => rfl
            | true => exact absurd (hproj sn j entry hfp0 hfp htw) hnp.1
        show (if entry.tower = true then some (projAV j ea')
            else if j < 2 then some (AVExpr.proj j ea') else none)
          = some (AVExpr.proj j ea')
        rw [if_neg (by simp [hntw]), if_pos hj]
  | case11 d n hsup =>
    intro _ _ ea h
    rw [denoteP, if_pos hsup] at h
    rw [denoteP, if_pos (hG.1 hsup)]
    exact h
  | case12 d n hsup =>
    intro _ _ ea h
    rw [denoteP, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro _ _ ea h
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denoteP, if_pos hsup] at h
    rw [denoteP, if_pos (hG.2 hsup),
      ← levelParamsAt_congr hF hnil, ← levelParamsAt_congr hF hcons]
    exact h
  | case14 d s hsup =>
    intro _ _ ea h
    rw [denoteP, if_neg hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _ _ ea h
    cases x with
    | bvar i => rw [denoteP.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i nm ty => exact absurd rfl (hfv i nm ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE n ty b m => exact absurd rfl (hpi n ty b m)
    | lam n ty b m => exact absurd rfl (hlam n ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE n ty v b => exact absurd rfl (hlet n ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-- A tower-entry cons adds exactly its own slot: any lookup new at
the extension is the head's. -/
theorem findProj?_cons_tower {env : Env} {entry₀ : Setlec.ProjEntry} :
    ∀ (sn : Name) (j : Nat) (entry : Setlec.ProjEntry),
      env.findProj? sn j = none →
      Env.findProj? ⟨.projInfo entry₀ :: env.consts⟩ sn j = some entry →
      entry.tower = true → sn = entry₀.structName ∧ j = entry₀.idx := by
  intro sn j entry h0 h1 _
  unfold Setlec.Env.findProj? at h0 h1
  rw [Setlec.Env.find?_cons] at h1
  by_cases hn : (Setlec.ConstantInfo.projInfo entry₀).name = Setlec.projFnName sn j
  · have hn' : Setlec.projFnName entry₀.structName entry₀.idx
        = Setlec.projFnName sn j := hn
    obtain ⟨h1, h2⟩ := Setlec.projFnName_inj hn'
    exact ⟨h1.symm, h2.symm⟩
  · rw [if_neg hn, h0] at h1
    exact nomatch h1

end Setlec.SetP
