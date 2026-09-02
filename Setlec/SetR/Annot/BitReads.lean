import Setlec.SetR.Annot.Bit

/-!
# The reading's totality bridge (task #161, IND TIER part 9)

`denoteP_erase` (`Annot/Bit.lean`) says the reading *erases* to the
denotation.  This file says the two are **defined on the same terms**:
`denoteP` and `denote` are clause for clause the same recursion, and
their four failure guards — a loose `.bvar`, an unfindable or
mis-arity `.const`, a `.proj` index `≥ 2`, an unsupported literal — are
all *syntactic or environmental*.  None of them mentions a valuation,
so neither reading can fail where the other succeeds.

**Why the ind tier wants this.**  The install statements
(`IotaRuleR`, `ProjFnR`, `SetR/Decl.lean`) carry the rule right-hand
side's front door as a v1 *derivation* row — `denoteClosed cval env ψ
rhsA = some Rv` together with an `Infer` derivation.  The P tier
consumes runs, not derivations, and the H1 widenings recorded the
runs beside them; but a run is a statement about the checker and says
nothing about whether the subject **reads**.  `RecRuleLawP` opens with
`∃ Ra, denoteP … = some Ra`, so that existence has to come from
somewhere, and the answer is: from the derivation row's own
denotation, through this bridge.  Nothing is routed and no row is
owed.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo)

/-- **A term that denotes reads.**  The two recursions share every
guard, and no guard mentions a valuation. -/
theorem denoteP_isSome_of_denote
    {acval : Name → (Name → Nat) → AVExpr} {cval : TConstVal}
    {env : Env} {φ : Name → Nat} :
    ∀ (d : Nat) (e : Expr) {v : VExpr},
      denote cval env φ d e = some v →
      ∃ ea, denoteP acval env φ d e = some ea := by
  intro d e
  induction d, e using denoteP.induct (env := env) with
  | case1 d u =>
    intro v _
    refine Option.isSome_iff_exists.mp ?_
    rw [denoteP]
    rfl
  | case2 d idx nm ty =>
    intro v _
    refine Option.isSome_iff_exists.mp ?_
    rw [denoteP]
    rfl
  | case3 d n us ci hf hlen =>
    intro v _
    refine Option.isSome_iff_exists.mp ?_
    rw [denoteP, hf]
    dsimp only
    rw [if_pos hlen]
    rfl
  | case4 d n us ci hf hlen =>
    intro v h
    rw [denote_const, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro v h
    rw [denote_const, hf] at h
    exact nomatch h
  | case6 d n ty body mb ihty ihbody =>
    intro v h
    rw [denote_forallE] at h
    rcases hA : denote cval env φ d ty with _ | A
    · rw [hA] at h; exact nomatch h
    rcases hB : denote cval env φ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | B
    · rw [hA, hB] at h; exact nomatch h
    obtain ⟨ta, hta⟩ := ihty hA
    obtain ⟨ba, hba⟩ := ihbody hB
    refine Option.isSome_iff_exists.mp ?_
    rw [denoteP, hta, hba]
    rfl
  | case7 d n ty body mb ihty ihbody =>
    intro v h
    rw [denote_lam] at h
    rcases hA : denote cval env φ d ty with _ | A
    · rw [hA] at h; exact nomatch h
    rcases hB : denote cval env φ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | B
    · rw [hA, hB] at h; exact nomatch h
    obtain ⟨ta, hta⟩ := ihty hA
    obtain ⟨ba, hba⟩ := ihbody hB
    refine Option.isSome_iff_exists.mp ?_
    rw [denoteP, hta, hba]
    rfl
  | case8 d fe a ihf iha =>
    intro v h
    rw [denote_app] at h
    rcases hF : denote cval env φ d fe with _ | vf
    · rw [hF] at h; exact nomatch h
    rcases hA : denote cval env φ d a with _ | va
    · rw [hF, hA] at h; exact nomatch h
    obtain ⟨fa, hfa⟩ := ihf hF
    obtain ⟨aa, haa⟩ := iha hA
    refine Option.isSome_iff_exists.mp ?_
    rw [denoteP, hfa, haa]
    rfl
  | case9 d n ty val body ihty ihval ihbody =>
    intro v h
    rw [denote_letE] at h
    rcases hA : denote cval env φ d ty with _ | A
    · rw [hA] at h; exact nomatch h
    rcases hV : denote cval env φ d val with _ | xv
    · rw [hA, hV] at h; exact nomatch h
    rcases hB : denote cval env φ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | B
    · rw [hA, hV, hB] at h; exact nomatch h
    obtain ⟨ta, hta⟩ := ihty hA
    obtain ⟨va, hva⟩ := ihval hV
    obtain ⟨ba, hba⟩ := ihbody hB
    refine Option.isSome_iff_exists.mp ?_
    rw [denoteP, hta, hva, hba]
    rfl
  | case10 d sn i e ihe =>
    intro v h
    rw [denote_proj] at h
    rcases hE : denote cval env φ d e with _ | ve
    · rw [hE] at h; exact nomatch h
    rw [hE] at h
    dsimp only at h
    by_cases hi : i < 2
    · obtain ⟨ea, hea⟩ := ihe hE
      refine ⟨AVExpr.proj i ea, ?_⟩
      rw [denoteP, hea]
      show (if i < 2 then some (AVExpr.proj i ea) else none) = _
      rw [if_pos hi]
    · rw [if_neg hi] at h
      exact nomatch h
  | case11 d k hsup =>
    intro v _
    refine Option.isSome_iff_exists.mp ?_
    rw [denoteP, if_pos hsup]
    rfl
  | case12 d k hsup =>
    intro v h
    rw [denote_natLit, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro v _
    refine Option.isSome_iff_exists.mp ?_
    rw [denoteP, if_pos hsup]
    rfl
  | case14 d s hsup =>
    intro v h
    rw [denote_strLit, if_neg hsup] at h
    exact nomatch h
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro v h
    cases x with
    | bvar i => rw [denote.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hxs u)
    | fvar i nm ty => exact absurd rfl (hfv i nm ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE n ty b mb => exact absurd rfl (hpi n ty b mb)
    | lam n ty b mb => exact absurd rfl (hlam n ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE n ty vv b => exact absurd rfl (hlet n ty vv b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

/-- **The closed form** — the shape the install statements' front-door
rows are stated in (`denoteClosed`, `Verify/Denote.lean`). -/
theorem denotePClosed_isSome_of_denoteClosed
    {acval : Name → (Name → Nat) → AVExpr} {cval : TConstVal}
    {env : Env} {φ : Name → Nat} {e : Expr} {v : VExpr}
    (h : denoteClosed cval env φ e = some v) :
    ∃ ea, denoteP acval env φ 0 e = some ea :=
  denoteP_isSome_of_denote 0 e h

end Setlec.SetR.Interp2
