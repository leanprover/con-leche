import Setlec.Semantics.Sem
import Setlec.SetP.Annot.EnvS2P

/-!
# `sem` agrees with the two-stage reading, and the model it exposes

`Setlec/Semantics/Sem.lean` defines the interpretation of a checker
term in one function, directly on `Expr`, so that a statement about the
model can be read without `AVExpr`, `denoteP` or `interp2`.  This module
is the bridge: wherever `denoteP` reads a term, `sem` at the
interpreted leaves agrees with `interp2` of the reading
(`sem_of_denoteP`, by `denoteP`'s own induction principle, clause for
clause), and from that the P carrier yields the model statement
`EnvS2PM.model_exists` — a set for every constant such that definitions
and theorems denote their bodies and every stored constant is a member
of its type.  `Setlec/Verify/Cached/MainC.lean` states it for the
shipped driver; `ChallengeModel.lean` is the comparator challenge.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify
open Setlec.Semantics (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal PropWhen)
open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- The set-valued leaf of an annotated valuation: the interpretation of
the (closed) leaf, under the empty variable environment. -/
noncomputable def cvalOf (acval : Name → (Name → Nat) → AVExpr)
    (n : Name) (ψ : Name → Nat) : V :=
  interp2 V (fun _ => SetTheory.empty) (acval n ψ)

/-- A closed leaf interprets to its `cvalOf` under every environment. -/
theorem interp2_cvalOf {acval : Name → (Name → Nat) → AVExpr}
    (hcl : ∀ n ψ, VExpr.Closed (acval n ψ).erase) (n : Name) (ψ : Name → Nat)
    (ρ : Nat → V) : interp2 V ρ (acval n ψ) = cvalOf acval n ψ :=
  interp2_closed (V := V) (hcl n ψ) ρ _

omit [SetTheory V] in
theorem push_eq_cons (x : V) (ρ : Nat → V) : push x ρ = cons x ρ := by
  funext i; cases i <;> rfl

theorem regime_eq_pwBit (φ : Name → Nat) (pw : PropWhen) :
    regime φ pw = pwBit φ pw := rfl

theorem interp2_natLitT2 (ρ : Nat → V) (za sa : AVExpr) :
    ∀ k, interp2 V ρ (natLitT2 za sa k) = natLitV (interp2 V ρ za) (interp2 V ρ sa) k
  | 0 => rfl
  | k + 1 => by rw [natLitT2, natLitV, interp2_app, interp2_natLitT2 ρ za sa k]

theorem interp2_charListT2 (ρ : Nat → V) (nilA consA ofNatA za sa : AVExpr) :
    ∀ cs, interp2 V ρ (charListT2 nilA consA ofNatA za sa cs) =
      charListV (interp2 V ρ nilA) (interp2 V ρ consA) (interp2 V ρ ofNatA)
        (interp2 V ρ za) (interp2 V ρ sa) cs
  | [] => rfl
  | c :: cs => by
    rw [charListT2, charListV, interp2_app, interp2_app, interp2_app,
      interp2_natLitT2, interp2_charListT2 ρ nilA consA ofNatA za sa cs]

theorem interp2_projAV (ρ : Nat → V) :
    ∀ (i : Nat) (e : AVExpr), interp2 V ρ (projAV i e) = projV i (interp2 V ρ e)
  | 0, e => by rw [projAV, projV, interp2_proj, if_pos rfl]
  | i + 1, e => by
    rw [projAV, projV, interp2_projAV ρ i, interp2_proj, if_neg (by decide)]

/-- **The bridge**: wherever `denoteP` reads, `sem` at the interpreted
leaves is `interp2` of the reading. -/
theorem sem_of_denoteP {acval : Name → (Name → Nat) → AVExpr}
    (hcl : ∀ n ψ, VExpr.Closed (acval n ψ).erase) {env : Env} {φ : Name → Nat} :
    ∀ (d : Nat) (e : Expr) {ta : AVExpr},
      denoteP acval env φ d e = some ta →
      ∀ ρ : Nat → V, sem (cvalOf (V := V) acval) env φ d ρ e = interp2 V ρ ta := by
  intro d e
  induction d, e using denoteP.induct (env := env) with
  | case1 d u =>
    intro ta h ρ
    rw [denoteP] at h
    cases h
    rw [sem, interp2_sort]
  | case2 d idx nm ty =>
    intro ta h ρ
    rw [denoteP] at h
    cases h
    rw [sem, interp2_bvar]
  | case3 d n us ci hf hlen =>
    intro ta h ρ
    rw [denoteP, hf] at h
    dsimp only at h
    rw [if_pos hlen] at h
    cases h
    rw [sem, hf]
    dsimp only
    rw [if_pos hlen, interp2_cvalOf hcl]
  | case4 d n us ci hf hlen =>
    intro ta h
    rw [denoteP, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ta h
    rw [denoteP, hf] at h
    exact nomatch h
  | case6 d n ty body mb ihty ihbody =>
    intro ta h ρ
    rcases hA : denoteP acval env φ d ty with _ | A
    · rw [denoteP, hA] at h; exact nomatch h
    rcases hB : denoteP acval env φ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | B
    · rw [denoteP, hA, hB] at h; exact nomatch h
    have hd : denoteP acval env φ d (.forallE n ty body mb)
        = some (.pi 0 (pwBit φ mb.pw) A B) := by
      rw [denoteP, hA, hB]; rfl
    rw [hd] at h
    cases h
    rw [sem, interp2_pi, ihty hA ρ, regime_eq_pwBit]
    congr 1
    funext x
    rw [push_eq_cons]
    exact ihbody hB _
  | case7 d n ty body mb ihty ihbody =>
    intro ta h ρ
    rcases hA : denoteP acval env φ d ty with _ | A
    · rw [denoteP, hA] at h; exact nomatch h
    rcases hB : denoteP acval env φ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | B
    · rw [denoteP, hA, hB] at h; exact nomatch h
    have hd : denoteP acval env φ d (.lam n ty body mb)
        = some (.lam (pwBit φ mb.pw) A B) := by
      rw [denoteP, hA, hB]; rfl
    rw [hd] at h
    cases h
    rw [sem, interp2_lam, ihty hA ρ, regime_eq_pwBit]
    congr 1
    funext x
    rw [push_eq_cons]
    exact ihbody hB _
  | case8 d fe a ihf iha =>
    intro ta h ρ
    rcases hF : denoteP acval env φ d fe with _ | fa
    · rw [denoteP, hF] at h; exact nomatch h
    rcases hA : denoteP acval env φ d a with _ | aa
    · rw [denoteP, hF, hA] at h; exact nomatch h
    have hd : denoteP acval env φ d (.app fe a) = some (.app fa aa) := by
      rw [denoteP, hF, hA]; rfl
    rw [hd] at h
    cases h
    rw [sem, interp2_app, ihf hF ρ, iha hA ρ]
  | case9 d n ty val body ihty ihval ihbody =>
    intro ta h ρ
    rcases hA : denoteP acval env φ d ty with _ | A
    · rw [denoteP, hA] at h; exact nomatch h
    rcases hV : denoteP acval env φ d val with _ | va
    · rw [denoteP, hA, hV] at h; exact nomatch h
    rcases hB : denoteP acval env φ (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | B
    · rw [denoteP, hA, hV, hB] at h; exact nomatch h
    have hd : denoteP acval env φ d (.letE n ty val body)
        = some (.letE A va B) := by
      rw [denoteP, hA, hV, hB]; rfl
    rw [hd] at h
    cases h
    rw [sem, interp2_letE, ihval hV ρ, push_eq_cons]
    exact ihbody hB _
  | case10 d sn i e ihe =>
    intro ta h ρ
    rcases hE : denoteP acval env φ d e with _ | ea
    · rw [denoteP, hE] at h; exact nomatch h
    cases hfp : env.findProj? sn i with
    | some entry =>
      have hd : denoteP acval env φ d (.proj sn i e) = some (projAV i ea) := by
        rw [denoteP, hE]
        show (match env.findProj? sn i with
          | some _ => some (projAV i ea)
          | none => if i < 2 then some (AVExpr.proj i ea) else none)
            = _
        rw [hfp]
      rw [hd] at h
      cases h
      rw [sem, hfp]
      dsimp only
      rw [interp2_projAV, ihe hE ρ]
    | none =>
      by_cases hi : i < 2
      · have hd : denoteP acval env φ d (.proj sn i e) = some (AVExpr.proj i ea) := by
          rw [denoteP, hE]
          show (match env.findProj? sn i with
            | some _ => some (projAV i ea)
            | none => if i < 2 then some (AVExpr.proj i ea) else none)
              = _
          rw [hfp]
          dsimp only
          rw [if_pos hi]
        rw [hd] at h
        cases h
        rw [sem, hfp]
        dsimp only
        rw [if_pos hi, interp2_proj, ihe hE ρ]
      · have hd : denoteP acval env φ d (.proj sn i e) = none := by
          rw [denoteP, hE]
          show (match env.findProj? sn i with
            | some _ => some (projAV i ea)
            | none => if i < 2 then some (AVExpr.proj i ea) else none)
              = _
          rw [hfp]
          dsimp only
          rw [if_neg hi]
        rw [hd] at h
        exact nomatch h
  | case11 d k hsup =>
    intro ta h ρ
    rw [denoteP, if_pos hsup] at h
    cases h
    rw [sem, interp2_natLitT2, interp2_cvalOf hcl, interp2_cvalOf hcl]
  | case12 d k hsup =>
    intro ta h
    rw [denoteP, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ta h ρ
    rw [denoteP, if_pos hsup] at h
    cases h
    rw [sem, interp2_app, interp2_charListT2, interp2_app, interp2_app]
    simp only [interp2_cvalOf hcl]
    rfl
  | case14 d s hsup =>
    intro ta h
    rw [denoteP, if_neg hsup] at h
    exact nomatch h
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ta h
    cases x with
    | bvar i => rw [denoteP.eq_def] at h; exact nomatch h
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

/-- **The model, read off the P carrier**: a set for every constant at
every level assignment such that every stored definition and theorem
denotes its body, and every stored constant is a member of its type's
denotation. -/
theorem EnvS2PM.model_exists {μ : CheckMode} {env : Env} (mp : EnvS2PM V μ env) :
    ∃ cval : Name → (Name → Nat) → V,
      (∀ (cv : ConstantVal) (value : Expr),
        ((∃ hint, ConstantInfo.defnInfo cv value hint ∈ env.consts) ∨
          ConstantInfo.thmInfo cv value ∈ env.consts) →
        ∀ (φ : Name → Nat) (ρ : Nat → V),
          sem cval env φ 0 ρ value = cval cv.name φ) ∧
      (∀ c ∈ env.consts, ∀ (φ : Name → Nat) (ρ : Nat → V),
        cval c.name φ ∈ˢ sem cval env φ 0 ρ c.toConstantVal.type) := by
  have hcl := mp.base2.cval_closedL
  refine ⟨cvalOf mp.base2.acval, ?_, ?_⟩
  · intro cv value hmem φ ρ
    rw [sem_of_denoteP hcl 0 value (mp.defn_reads φ cv value hmem) ρ,
      interp2_cvalOf hcl]
  · intro c hc φ ρ
    obtain ⟨ta, hta⟩ := mp.type_reads c hc φ
    rw [sem_of_denoteP hcl 0 _ hta ρ, ← interp2_cvalOf hcl c.name φ ρ]
    exact mp.mem_typeP c hc φ ta hta ρ

end Setlec.SetP
