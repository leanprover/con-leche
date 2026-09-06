import Setlec.Semantics.Sem
import Setlec.Verify.EnvGuards
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

/-! ### `sem`'s equations at the shapes the literal expansions use -/

theorem sem_app {cval : Name → (Name → Nat) → V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} {f a : Expr} :
    sem cval env φ d ρ (.app f a) =
      SetTheory.app (sem cval env φ d ρ f) (sem cval env φ d ρ a) := by
  rw [sem]

theorem sem_const_of_find {cval : Name → (Name → Nat) → V} {env : Env}
    {φ : Name → Nat} {d : Nat} {ρ : Nat → V} {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) {us : List Level}
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    sem cval env φ d ρ (.const n us) =
      cval n (Level.substFn φ ci.toConstantVal.levelParams us) := by
  rw [sem, hf]
  dsimp only
  rw [if_pos hlen]

theorem sem_natLit {cval : Name → (Name → Nat) → V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} {k : Nat} :
    sem cval env φ d ρ (.lit (.natVal k)) =
      sem cval env φ d ρ (Setlec.natLitToConstructor k) := by
  rw [sem]

theorem sem_strLit {cval : Name → (Name → Nat) → V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} {s : String} :
    sem cval env φ d ρ (.lit (.strVal s)) =
      sem cval env φ d ρ (Setlec.strLitToConstructor s) := by
  rw [sem]

/-- Under the `Nat`-literal guard, the constructor form of a literal
interprets to the annotated numeral `denoteP` reads. -/
theorem sem_natLitToConstructor {acval : Name → (Name → Nat) → AVExpr}
    (hcl : ∀ n ψ, VExpr.Closed (acval n ψ).erase) {env : Env} {φ : Name → Nat}
    (hsup : Setlec.natLitSupported env = true) (d : Nat) (ρ : Nat → V) :
    ∀ k, sem (cvalOf (V := V) acval) env φ d ρ (Setlec.natLitToConstructor k)
      = interp2 V ρ (natLitT2 (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] [])) k) := by
  obtain ⟨_, _, cv0, i0, j0, cv1, i1, j1, -, hz, hs, -, hz0, hs0, -, -, -⟩ :=
    natLitSupported_inv hsup
  have hz' : ([] : List Level).length
      = (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams.length := by
    simp [ConstantInfo.toConstantVal, hz0]
  have hs' : ([] : List Level).length
      = (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams.length := by
    simp [ConstantInfo.toConstantVal, hs0]
  intro k
  induction k with
  | zero =>
    rw [Setlec.natLitToConstructor, natLitT2, sem_const_of_find hz hz', interp2_cvalOf hcl]
    simp only [ConstantInfo.toConstantVal, hz0]
  | succ k ih =>
    rw [Setlec.natLitToConstructor, natLitT2, sem_app, sem_const_of_find hs hs',
      sem_natLit, ih, interp2_app, interp2_cvalOf hcl]
    simp only [ConstantInfo.toConstantVal, hs0]

/-- Under the `String`-literal guard, the character-list spine of a
literal's constructor form interprets to the annotated spine `denoteP`
reads. -/
theorem sem_charList {acval : Name → (Name → Nat) → AVExpr}
    (hcl : ∀ n ψ, VExpr.Closed (acval n ψ).erase) {env : Env} {φ : Name → Nat}
    (hsup : Setlec.strLitSupported env = true) (d : Nat) (ρ : Nat → V) :
    ∀ l : List Char,
      sem (cvalOf (V := V) acval) env φ d ρ
        (l.foldr
          (init := .app (.const listNilName [.zero]) (.const charName []))
          fun c e =>
            .app (.app (.app (.const listConsName [.zero]) (.const charName []))
              (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e)
      = interp2 V ρ (charListT2
          (.app (acval listNilName
              (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (.app (acval listConsName
              (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (acval charOfNatName (Level.substFn φ [] []))
          (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] []))
          l) := by
  obtain ⟨hnat, _, _, _, ciN, ciC, ciH, ciF, _, pN, pC, -, -, -, hN, hC, hH, hF,
    -, -, -, hN1, hC1, hH0, hF0, -⟩ := strLitSupported_inv hsup
  have hNlp : levelParamsAt env listNilName = ciN.toConstantVal.levelParams := by
    simp only [levelParamsAt, hN]
  have hClp : levelParamsAt env listConsName = ciC.toConstantVal.levelParams := by
    simp only [levelParamsAt, hC]
  intro l
  induction l with
  | nil =>
    rw [List.foldr_nil, charListT2, sem_app,
      sem_const_of_find hN (by rw [hN1]; rfl),
      sem_const_of_find hH (by rw [hH0]; rfl),
      interp2_app, interp2_cvalOf hcl, interp2_cvalOf hcl, hNlp, hH0]
  | cons c cs ih =>
    rw [List.foldr_cons, charListT2, sem_app, sem_app, sem_app, sem_app,
      sem_const_of_find hC (by rw [hC1]; rfl),
      sem_const_of_find hH (by rw [hH0]; rfl),
      sem_const_of_find hF (by rw [hF0]; rfl),
      sem_natLit, sem_natLitToConstructor hcl hnat d ρ, ih,
      interp2_app, interp2_app, interp2_app, interp2_app,
      interp2_cvalOf hcl, interp2_cvalOf hcl, interp2_cvalOf hcl, hClp, hH0, hF0]

/-- Under the `String`-literal guard, the constructor form of a literal
interprets to what `denoteP` reads for the literal. -/
theorem sem_strLitToConstructor {acval : Name → (Name → Nat) → AVExpr}
    (hcl : ∀ n ψ, VExpr.Closed (acval n ψ).erase) {env : Env} {φ : Name → Nat}
    (hsup : Setlec.strLitSupported env = true) (d : Nat) (ρ : Nat → V) (s : String) :
    sem (cvalOf (V := V) acval) env φ d ρ (Setlec.strLitToConstructor s)
      = interp2 V ρ (.app (acval stringOfListName (Level.substFn φ [] []))
          (charListT2
            (.app (acval listNilName
                (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
              (acval charName (Level.substFn φ [] [])))
            (.app (acval listConsName
                (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
              (acval charName (Level.substFn φ [] [])))
            (acval charOfNatName (Level.substFn φ [] []))
            (acval natZeroName (Level.substFn φ [] []))
            (acval natSuccName (Level.substFn φ [] []))
            s.toList)) := by
  obtain ⟨-, _, ciO, _, _, _, _, _, _, _, _, -, hO, -, -, -, -, -, -, hO0, -⟩ :=
    strLitSupported_inv hsup
  unfold Setlec.strLitToConstructor
  rw [sem_app, sem_const_of_find hO (by rw [hO0]; rfl), sem_charList hcl hsup d ρ,
    interp2_app, interp2_cvalOf hcl, hO0]

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
    rw [sem_natLit, sem_natLitToConstructor hcl hsup d ρ k]
  | case12 d k hsup =>
    intro ta h
    rw [denoteP, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ta h ρ
    rw [denoteP, if_pos hsup] at h
    cases h
    rw [sem_strLit, sem_strLitToConstructor hcl hsup d ρ s]
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
