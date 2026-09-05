import Setlec.SetP.Annot.BitInstall
import Setlec.SetBase.ConstsBound

/-!
# `denoteP` across an environment extension (task #161, P3.2)

The mirror of `Denote2EnvExtend` (`Interp2/Keys2.lean`) and its
discharge `denote2_envExtend` (`Interp2/Denote2Extend.lean`) — and the
place where the P3 pivot pays out most visibly.

**`SortAgree` is deleted.**  `denote2_envExtend` takes three premises:
`FindPreserved` (the `.const` clause and the string spine's
`levelParamsAt`), `LitGuardsAgree` (the two literal guards), and
`SortAgree` — "`sortOfE` and `lamSortE` agree at `env₀` and `env`",
itself a composition of `EnvExtendStable`, `EnvExtendReflect` and
`InferOutputBound` (`sortAgree_of`), i.e. three *open* checker
metatheorems.  It is used at exactly three rewrites, all inside the
`∀` and `λ` clauses (`hS.1 hc.1`, `hS.1 hcb`, `hS.2 hcb`).

`denoteP`'s binder numeral is `pwBit φ mb.pw`: a function of the
term's own validated meta and the valuation `φ`, mentioning no
environment at all.  So those three rewrites have no mirror and no
residue — the binder clauses close on the two induction hypotheses
alone, exactly like `.app`.  The two kept premises are the ones the
*reading itself* needs: `denoteP` consults `env` only through
`find?` and the two support guards.

That is the whole Θ-residue for this key, gone by construction rather
than by discharge.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

/-- **`denoteP` is stable under environment extension**, stated.
`Denote2EnvExtend` with the fuel and mode indices deleted.

An **equation**, not an implication, for the reason the original is
one: an install must not be able to assume silently that an
annotation exists on one side and not the other. -/
def DenotePEnvExtend (env₀ env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (e : Expr), ConstsBound env₀ e →
    denoteP acval env₀ φ d e = denoteP acval env φ d e

/-- **`DenotePEnvExtend`, discharged** — from `FindPreserved` and
`LitGuardsAgree` alone.  See the module docstring for the dropped
`SortAgree`. -/
theorem denoteP_envExtend {env₀ env : Env}
    {acval : Name → (Name → Nat) → AVExpr} {φ : Name → Nat}
    (hF : FindPreserved env₀ env) (hG : LitGuardsAgree env₀ env)
    (hproj : ∀ (sn : Name) (i : Nat) (entry : Setlec.ProjEntry),
      env₀.findProj? sn i = none → env.findProj? sn i = some entry →
      entry.tower = false) :
    DenotePEnvExtend env₀ env acval φ := by
  -- a preserved lookup carries its entry across unchanged
  have hmono : ∀ (sn : Name) (i : Nat) (entry : Setlec.ProjEntry),
      env₀.findProj? sn i = some entry →
      env.findProj? sn i = some entry := by
    intro sn i entry h
    unfold Setlec.Env.findProj? at h ⊢
    cases hf0 : env₀.find? (Setlec.projFnName sn i) with
    | none => rw [hf0] at h; exact nomatch h
    | some ci =>
      rw [hf0] at h
      rw [hF hf0]
      exact h
  intro d e
  induction d, e using denoteP.induct (env := env₀) with
  | case1 d u => intro _; rw [denoteP, denoteP]
  | case2 d idx nm ty => intro _; rw [denoteP, denoteP]
  | case3 d n us ci hf hlen =>
    intro _
    rw [denoteP, hf, denoteP, hF hf]
  | case4 d n us ci hf hlen =>
    intro _
    rw [denoteP, hf, denoteP, hF hf]
  | case5 d n us hf =>
    intro hc
    rw [constsBound_const, hf] at hc
    exact nomatch hc
  | case6 d n ty body m ihty ihbody =>
    intro hc
    rw [constsBound_forallE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    rw [denoteP, denoteP, ihty hc.1, ihbody hcb]
  | case7 d n ty body m ihty ihbody =>
    intro hc
    rw [constsBound_lam] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    rw [denoteP, denoteP, ihty hc.1, ihbody hcb]
  | case8 d f a ihf iha =>
    intro hc
    rw [constsBound_app] at hc
    rw [denoteP, denoteP, ihf hc.1, iha hc.2]
  | case9 d n ty val body ihty ihval ihbody =>
    intro hc
    rw [constsBound_letE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2.2
    rw [denoteP, denoteP, ihty hc.1, ihval hc.2.1, ihbody hcb]
  | case10 d sn i e ihe =>
    intro hc
    rw [constsBound_proj] at hc
    rw [denoteP, denoteP, ihe hc]
    cases denoteP acval env φ d e with
    | none => rfl
    | some ea =>
      show (match env₀.findProj? sn i with
          | some entry => if entry.tower = true then some (projAV i ea)
              else if i < 2 then some (AVExpr.proj i ea) else none
          | none => if i < 2 then some (AVExpr.proj i ea) else none)
        = (match env.findProj? sn i with
          | some entry => if entry.tower = true then some (projAV i ea)
              else if i < 2 then some (AVExpr.proj i ea) else none
          | none => if i < 2 then some (AVExpr.proj i ea) else none)
      cases hfp0 : env₀.findProj? sn i with
      | some entry => rw [hmono sn i entry hfp0]
      | none =>
        cases hfp : env.findProj? sn i with
        | none => rfl
        | some entry =>
          dsimp only
          rw [if_neg (show ¬ entry.tower = true by
            simp [hproj sn i entry hfp0 hfp])]
  | case11 d n hsup =>
    intro _
    rw [denoteP, if_pos hsup, denoteP, if_pos (hG.1 ▸ hsup)]
  | case12 d n hsup =>
    intro _
    rw [denoteP, if_neg hsup, denoteP,
      if_neg (fun h => hsup (hG.1.trans h))]
  | case13 d s hsup =>
    intro _
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denoteP, if_pos hsup, denoteP, if_pos (hG.2 ▸ hsup),
      levelParamsAt_congr hF hnil, levelParamsAt_congr hF hcons]
  | case14 d s hsup =>
    intro _
    rw [denoteP, if_neg hsup, denoteP,
      if_neg (fun h => hsup (hG.2.trans h))]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denoteP.eq_def, denoteP.eq_def]
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

/-! ## The monotone crossing (task #161, the literal tier's opening)

`LitGuardsAgree` — the guard *equality* — is refutable at a
support-completing install (a pinned-type `def` named `String.ofList`
flips `strLitSupported` upward, and nothing forbids the name).  The
fold therefore rides the **monotone** crossing below: literal guards
only ever gain under a fresh cons (`natLitSupported_cons`/
`strLitSupported_cons`), and a *successful* prefix reading transfers
forward — which is the only direction the harvests use for their
subjects, whose acceptance guaranteed prefix-supported literals. -/

/-- The literal guards are monotone across the extension. -/
def LitGuardsMono (env₀ env : Env) : Prop :=
  (natLitSupported env₀ = true → natLitSupported env = true) ∧
  (strLitSupported env₀ = true → strLitSupported env = true)

/-- Free at every fresh cons, of any kind. -/
theorem litGuardsMono_cons {env : Env} {c₀ : Setlec.ConstantInfo}
    (hfresh : env.find? c₀.name = none) :
    LitGuardsMono env ⟨c₀ :: env.consts⟩ :=
  ⟨natLitSupported_cons hfresh, strLitSupported_cons hfresh⟩

/-- **The monotone crossing**: a successful prefix reading is
reproduced verbatim at the extension. -/
theorem denoteP_envExtend_mono {env₀ env : Env}
    {acval : Name → (Name → Nat) → AVExpr} {φ : Name → Nat}
    (hF : FindPreserved env₀ env) (hG : LitGuardsMono env₀ env)
    (hproj : ∀ (sn : Name) (i : Nat) (entry : Setlec.ProjEntry),
      env₀.findProj? sn i = none → env.findProj? sn i = some entry →
      entry.tower = false) :
    ∀ (d : Nat) (e : Expr), ConstsBound env₀ e →
      ∀ {ea : AVExpr}, denoteP acval env₀ φ d e = some ea →
        denoteP acval env φ d e = some ea := by
  have hmono : ∀ (sn : Name) (i : Nat) (entry : Setlec.ProjEntry),
      env₀.findProj? sn i = some entry →
      env.findProj? sn i = some entry := by
    intro sn i entry h
    unfold Setlec.Env.findProj? at h ⊢
    cases hf0 : env₀.find? (Setlec.projFnName sn i) with
    | none => rw [hf0] at h; exact nomatch h
    | some ci =>
      rw [hf0] at h
      rw [hF hf0]
      exact h
  intro d e
  induction d, e using denoteP.induct (env := env₀) with
  | case1 d u => intro _ ea h; rw [denoteP] at h ⊢; exact h
  | case2 d idx nm ty => intro _ ea h; rw [denoteP] at h ⊢; exact h
  | case3 d n us ci hf hlen =>
    intro _ ea h
    rw [denoteP, hf] at h
    rw [denoteP, hF hf]
    exact h
  | case4 d n us ci hf hlen =>
    intro _ ea h
    rw [denoteP, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro hc ea h
    rw [constsBound_const, hf] at hc
    exact nomatch hc
  | case6 d n ty body m ihty ihbody =>
    intro hc ea h
    rw [constsBound_forallE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteP_forallE_inv h
    rw [denoteP, ihty hc.1 hta, ihbody hcb hba]
    rfl
  | case7 d n ty body m ihty ihbody =>
    intro hc ea h
    rw [constsBound_lam] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteP_lam_inv h
    rw [denoteP, ihty hc.1 hta, ihbody hcb hba]
    rfl
  | case8 d f a ihf iha =>
    intro hc ea h
    rw [constsBound_app] at hc
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteP_app_inv h
    rw [denoteP, ihf hc.1 hfa, iha hc.2 haa]
    rfl
  | case9 d n ty val body ihty ihval ihbody =>
    intro hc ea h
    rw [constsBound_letE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2.2
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
    rw [denoteP, ihty hc.1 hta, ihval hc.2.1 hva, ihbody hcb hba]
    exact h
  | case10 d sn i e ihe =>
    intro hc ea h
    rw [constsBound_proj] at hc
    obtain ⟨ea', hea', hcase⟩ := denoteP_proj_inv h
    rcases hcase with ⟨entry, hfp0, htw, rfl⟩ | ⟨hnt0, hi, rfl⟩
    · -- a tower entry at the prefix persists unchanged
      rw [denoteP, ihe hc hea', hmono sn i entry hfp0]
      show (if entry.tower = true then some (projAV i ea')
          else if i < 2 then some (AVExpr.proj i ea') else none)
        = some (projAV i ea')
      rw [if_pos htw]
    · -- the pair path: any extension-side entry is still tower-free
      rw [denoteP, ihe hc hea']
      cases hfp : env.findProj? sn i with
      | none =>
        show (if i < 2 then some (AVExpr.proj i ea') else none)
          = some (AVExpr.proj i ea')
        rw [if_pos hi]
      | some entry =>
        have hntw : entry.tower = false := by
          cases hfp0 : env₀.findProj? sn i with
          | some entry0 =>
            have hsame := hmono sn i entry0 hfp0
            rw [hfp] at hsame
            obtain rfl := Option.some.inj hsame
            exact hnt0 _ hfp0
          | none => exact hproj sn i entry hfp0 hfp
        show (if entry.tower = true then some (projAV i ea')
            else if i < 2 then some (AVExpr.proj i ea') else none)
          = some (AVExpr.proj i ea')
        rw [if_neg (by simp [hntw]), if_pos hi]
  | case11 d n hsup =>
    intro _ ea h
    rw [denoteP, if_pos hsup] at h
    rw [denoteP, if_pos (hG.1 hsup)]
    exact h
  | case12 d n hsup =>
    intro _ ea h
    rw [denoteP, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro _ ea h
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denoteP, if_pos hsup] at h
    rw [denoteP, if_pos (hG.2 hsup),
      ← levelParamsAt_congr hF hnil, ← levelParamsAt_congr hF hcons]
    exact h
  | case14 d s hsup =>
    intro _ ea h
    rw [denoteP, if_neg hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _ ea h
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

end Setlec.SetR.Interp2
