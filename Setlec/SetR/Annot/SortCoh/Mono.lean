import Setlec.SetR.Annot.SortCoh.Claims

/-!
# Run-level sort coherence — the mono apparatus and the knot chain

Split from `SortCoh.lean` (pure motion; the umbrella
`Setlec.SetR.Annot.SortCoh` re-exports the whole family).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf whnfCore
  isDefEqCore unfoldDefinition)

/-! ## `KnotFuelMono` discharge, batch 1: the oracle order and the helper tier

The obligation discharges by oracle-extension induction over
`coreKnot`: define success-extension between oracles, show every
body and helper respects it, chain up the knot.  Batch 1: the order
and the helpers below the bodies.  (`annotate` is in the order — the
bodies reach it through `isPropType` — even though the public
obligation omits it.) -/

/-- Success-extension: every successful call of `r₁` is reproduced
verbatim by `r₂`, on all five fields. -/
def CoreSub (r₁ r₂ : Setlec.CoreFns Setlec.CheckM) : Prop :=
  (∀ {d : Nat} {e x : Expr},
    r₁.whnfCore d e = .ok x → r₂.whnfCore d e = .ok x) ∧
  (∀ {d : Nat} {e x : Expr},
    r₁.whnf d e = .ok x → r₂.whnf d e = .ok x) ∧
  (∀ {d : Nat} {e x : Expr},
    r₁.infer d e = .ok x → r₂.infer d e = .ok x) ∧
  (∀ {d : Nat} {a b : Expr} {v : Bool},
    r₁.defeq d a b = .ok v → r₂.defeq d a b = .ok v) ∧
  (∀ {d : Nat} {e x : Expr},
    r₁.annotate d e = .ok x → r₂.annotate d e = .ok x) ∧
  (∀ {d : Nat} {e x : Expr},
    r₁.inferIO d e = .ok x → r₂.inferIO d e = .ok x)

section MonoHelpers
variable {env : Env} {r₁ r₂ : Setlec.CoreFns Setlec.CheckM}

/-- `ensureSort` respects the order. -/
theorem ensureSort_mono (hs : CoreSub r₁ r₂) {d : Nat} {e : Expr}
    {u : Level} (h : Setlec.ensureSort r₁ env d e = .ok u) :
    Setlec.ensureSort r₂ env d e = .ok u := by
  unfold Setlec.ensureSort at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases hw : r₁.whnf d e with
  | error err => rw [hw] at h; exact nomatch h
  | ok w =>
    rw [hw] at h
    rw [hs.2.1 hw]
    exact h

/-- `defEqList` respects the order. -/
theorem defEqList_mono (hs : CoreSub r₁ r₂) {d : Nat} :
    ∀ {as bs : List Expr} {v : Bool},
      Setlec.defEqList r₁ env d as bs = .ok v →
      Setlec.defEqList r₂ env d as bs = .ok v := by
  intro as
  induction as with
  | nil => intro bs v h; cases bs <;> exact h
  | cons a as ih =>
    intro bs v h
    cases bs with
    | nil => exact h
    | cons b bs =>
      unfold Setlec.defEqList at h ⊢
      simp only [Bind.bind, Except.bind] at h ⊢
      cases hd : r₁.defeq d a b with
      | error err => rw [hd] at h; exact nomatch h
      | ok c =>
        rw [hd] at h
        rw [hs.2.2.2.1 hd]
        cases c with
        | true => simpa using ih (by simpa using h)
        | false => exact h

/-- `reduceNat` respects the order (its only oracle use is whnf on
the arguments). -/
theorem reduceNat_mono (hs : CoreSub r₁ r₂) {d : Nat} {e : Expr}
    {o : Option Expr}
    (h : Setlec.reduceNat r₁ env d e = .ok o) :
    Setlec.reduceNat r₂ env d e = .ok o := by
  unfold Setlec.reduceNat at h ⊢
  split at h
  · -- unary shape `.app (.const c []) a`
    next c a =>
    by_cases h1 : c = Setlec.natSuccName ∧ Setlec.natLitSupported env
    · rw [if_pos h1] at h ⊢
      simp only [Bind.bind, Except.bind] at h ⊢
      cases hw : r₁.whnf d a with
      | error err => rw [hw] at h; exact nomatch h
      | ok w => rw [hw] at h; rw [hs.2.1 hw]; exact h
    · rw [if_neg h1] at h ⊢
      by_cases h2 : c = Setlec.natPredName ∧
          Setlec.natOpStored env c = true
      · rw [if_pos h2] at h ⊢
        simp only [Bind.bind, Except.bind] at h ⊢
        cases hw : r₁.whnf d a with
        | error err => rw [hw] at h; exact nomatch h
        | ok w => rw [hw] at h; rw [hs.2.1 hw]; exact h
      · rw [if_neg h2] at h ⊢
        by_cases h3 : c = Setlec.natLog2Name ∧
            Setlec.natOpStored env c = true
        · rw [if_pos h3] at h ⊢
          simp only [Bind.bind, Except.bind] at h ⊢
          cases hw : r₁.whnf d a with
          | error err => rw [hw] at h; exact nomatch h
          | ok w => rw [hw] at h; rw [hs.2.1 hw]; exact h
        · rw [if_neg h3] at h ⊢
          by_cases h4 : c = Setlec.natLog2Name ∧
              Setlec.natLitSupported env
          · rw [if_pos h4] at h ⊢
            simp only [Bind.bind, Except.bind] at h ⊢
            cases hw : r₁.whnf d a with
            | error err => rw [hw] at h; exact nomatch h
            | ok w => rw [hw] at h; rw [hs.2.1 hw]; exact h
          · rw [if_neg h4] at h ⊢
            exact h
  · -- binary shape `.app (.app (.const c []) a) b`
    next c a b =>
    by_cases h1 : (c = Setlec.natAddName ∨ c = Setlec.natSubName ∨
        c = Setlec.natMulName ∨ c = Setlec.natPowName ∨
        c = Setlec.natBeqName ∨ c = Setlec.natBleName ∨
        c = Setlec.natDivName ∨ c = Setlec.natModName ∨
        c = Setlec.natGcdName ∨ c = Setlec.natLandName ∨
        c = Setlec.natLorName ∨ c = Setlec.natXorName ∨
        c = Setlec.natShiftLeftName ∨ c = Setlec.natShiftRightName) ∧
        Setlec.natOpStored env c = true
    · rw [if_pos h1] at h ⊢
      simp only [Bind.bind, Except.bind] at h ⊢
      cases hwa : r₁.whnf d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok wa =>
        rw [hwa] at h
        rw [hs.2.1 hwa]
        cases hwb : r₁.whnf d b with
        | error err => rw [hwb] at h; exact nomatch h
        | ok wb => rw [hwb] at h; rw [hs.2.1 hwb]; exact h
    · rw [if_neg h1] at h ⊢
      by_cases h2 : Setlec.natOpWfNames.contains c ∧
          Setlec.natLitSupported env
      · rw [if_pos h2] at h ⊢
        simp only [Bind.bind, Except.bind] at h ⊢
        cases hwa : r₁.whnf d a with
        | error err => rw [hwa] at h; exact nomatch h
        | ok wa =>
          rw [hwa] at h
          rw [hs.2.1 hwa]
          cases hwb : r₁.whnf d b with
          | error err => rw [hwb] at h; exact nomatch h
          | ok wb => rw [hwb] at h; rw [hs.2.1 hwb]; exact h
      · rw [if_neg h2] at h ⊢
        exact h
  · -- inert shapes
    exact h

/-- `whnfStep` respects the order (decompose, lift, reassemble). -/
theorem whnfStep_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {k₁ k₂ : Expr → Setlec.CheckM Expr}
    (hk : ∀ {e s : Expr}, k₁ e = .ok s → k₂ e = .ok s)
    {e s : Expr} (h : Setlec.whnfStep r₁ env d k₁ e = .ok s) :
    Setlec.whnfStep r₂ env d k₂ e = .ok s := by
  obtain ⟨e₁, hwc, hrest⟩ := whnfStep_decompose h
  rcases hrest with ⟨e₂, hrn, hkk⟩ | ⟨hrn, e₂, hud, hkk⟩ | ⟨hrn, hud, rfl⟩
  · exact whnfStep_assemble_nat (hs.1 hwc) (reduceNat_mono hs hrn)
      (hk hkk)
  · exact whnfStep_assemble_delta (hs.1 hwc) (reduceNat_mono hs hrn)
      hud (hk hkk)
  · exact whnfStep_assemble_stuck (hs.1 hwc) (reduceNat_mono hs hrn)
      hud

/-- `whnfLoop` respects the order at every budget. -/
theorem whnfLoop_mono (hs : CoreSub r₁ r₂) {d : Nat} :
    ∀ {l : Nat} {e s : Expr},
      Setlec.whnfLoop r₁ env d l e = .ok s →
      Setlec.whnfLoop r₂ env d l e = .ok s := by
  intro l
  induction l with
  | zero => intro e s h; exact nomatch h
  | succ l ih =>
    intro e s h
    rw [whnfLoop_succ] at h
    rw [whnfLoop_succ]
    exact whnfStep_mono hs (fun hk => ih hk) h

end MonoHelpers

/-! ## Batch 2a: the cert-helper tier -/

section MonoHelpers2
variable {env : Env} {r₁ r₂ : Setlec.CoreFns Setlec.CheckM}

/-- `iotaCerts` respects the order. -/
theorem iotaCerts_mono (hs : CoreSub r₁ r₂) {d : Nat} :
    ∀ {args : List Expr} {ty : Expr} {v : Bool},
      Setlec.iotaCerts r₁ env d ty args = .ok v →
      Setlec.iotaCerts r₂ env d ty args = .ok v := by
  intro args
  induction args with
  | nil => intro ty v h; exact h
  | cons a rest ih =>
    intro ty v h
    cases ty with
    | forallE n dom body bi =>
      unfold Setlec.iotaCerts at h ⊢
      simp only [Bind.bind, Except.bind] at h ⊢
      cases hi : r₁.inferIO d a with
      | error err => rw [hi] at h; exact nomatch h
      | ok ta =>
        rw [hi] at h
        rw [hs.2.2.2.2.2 hi]
        simp only [] at h ⊢
        cases hd : r₁.defeq d ta dom with
        | error err => rw [hd] at h; exact nomatch h
        | ok c =>
          rw [hd] at h
          rw [hs.2.2.2.1 hd]
          simp only [] at h ⊢
          cases c with
          | true => simpa using ih (by simpa using h)
          | false => exact h
    | sort u => exact h
    | fvar i n ty => exact h
    | app f a' => exact h
    | lam n ty b m => exact h
    | letE n ty v' b => exact h
    | proj s i e => exact h
    | lit l => exact h
    | const n us => exact h
    | bvar i => exact h

/-- `defeqSpine` respects the order. -/
theorem defeqSpine_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {a b : Expr} {v : Bool}
    (h : Setlec.defeqSpine r₁ env d a b = .ok v) :
    Setlec.defeqSpine r₂ env d a b = .ok v := by
  unfold Setlec.defeqSpine at h ⊢
  cases hga : a.getAppFn with
  | const n us =>
    rw [hga] at h
    cases hgb : b.getAppFn with
    | const n' us' =>
      rw [hgb] at h
      simp only [] at h ⊢
      by_cases hcond : n = n' ∧
          a.getAppArgs.length = b.getAppArgs.length
      · rw [if_pos hcond] at h ⊢
        cases hle : Level.isEquivList us us' with
        | some c =>
          rw [hle] at h
          cases c with
          | true => exact defEqList_mono hs (by simpa using h)
          | false => exact h
        | none => rw [hle] at h; exact h
      · rw [if_neg hcond] at h ⊢; exact h
    | sort u => rw [hgb] at h; exact h
    | fvar i nm ty => rw [hgb] at h; exact h
    | forallE nm ty bd bi => rw [hgb] at h; exact h
    | lam nm ty bd m => rw [hgb] at h; exact h
    | letE nm ty vl bd => rw [hgb] at h; exact h
    | app f x => rw [hgb] at h; exact h
    | proj s i e => rw [hgb] at h; exact h
    | lit l => rw [hgb] at h; exact h
    | bvar i => rw [hgb] at h; exact h
  | sort u => rw [hga] at h; exact h
  | fvar i nm ty => rw [hga] at h; exact h
  | forallE nm ty bd bi => rw [hga] at h; exact h
  | lam nm ty bd m => rw [hga] at h; exact h
  | letE nm ty vl bd => rw [hga] at h; exact h
  | app f x => rw [hga] at h; exact h
  | proj s i e => rw [hga] at h; exact h
  | lit l => rw [hga] at h; exact h
  | bvar i => rw [hga] at h; exact h

/-- `projLitToCtor` respects the order. -/
theorem projLitToCtor_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {e x : Expr}
    (h : Setlec.projLitToCtor r₁ env d e = .ok x) :
    Setlec.projLitToCtor r₂ env d e = .ok x := by
  cases e with
  | lit l =>
    cases l with
    | strVal s =>
      unfold Setlec.projLitToCtor at h ⊢
      simp only [] at h ⊢
      by_cases hsup : Setlec.strLitSupported env = true
      · rw [if_pos hsup] at h
        rw [if_pos hsup]
        exact hs.2.1 h
      · rw [if_neg hsup] at h
        rw [if_neg hsup]
        exact h
    | natVal n => exact h
  | sort u => exact h
  | fvar i n ty => exact h
  | app f a => exact h
  | lam n ty b m => exact h
  | letE n ty v' b => exact h
  | proj s i e' => exact h
  | const n us => exact h
  | forallE n ty b bi => exact h
  | bvar i => exact h

/-- `isPropType` respects the order (the `annotate` field's one
consumer). -/
theorem isPropType_mono (hs : CoreSub r₁ r₂) {d : Nat} {ty : Expr}
    {v : Bool} (h : Setlec.isPropType r₁ env d ty = .ok v) :
    Setlec.isPropType r₂ env d ty = .ok v := by
  unfold Setlec.isPropType at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases han : r₁.annotate d ty with
  | error err => rw [han] at h; exact nomatch h
  | ok ty' =>
    rw [han] at h
    rw [hs.2.2.2.2.1 han]
    simp only [] at h ⊢
    cases hi : r₁.infer d ty' with
    | error err => rw [hi] at h; exact nomatch h
    | ok t =>
      rw [hi] at h
      rw [hs.2.2.1 hi]
      simp only [] at h ⊢
      cases hes : Setlec.ensureSort r₁ env d t with
      | error err => rw [hes] at h; exact nomatch h
      | ok s =>
        rw [hes] at h
        rw [ensureSort_mono hs hes]
        simp only [] at h ⊢
        exact h

/-- `projCert` respects the order. -/
theorem projCert_mono (hs : CoreSub r₁ r₂) {d : Nat} {e₂ : Expr}
    {i : Nat} {nP : Nat} {v : Bool}
    (h : Setlec.projCert r₁ env d e₂ i nP = .ok v) :
    Setlec.projCert r₂ env d e₂ i nP = .ok v := by
  unfold Setlec.projCert at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : r₁.inferIO d (e₂.getAppArgs.getD (nP + i) (.bvar 0)) with
  | error err => rw [h1] at h; exact nomatch h
  | ok ta =>
  rw [h1] at h; rw [hs.2.2.2.2.2 h1]
  simp only [] at h ⊢
  cases h5 : r₁.inferIO d e₂ with
  | error err => rw [h5] at h; exact nomatch h
  | ok te =>
  rw [h5] at h; rw [hs.2.2.2.2.2 h5]
  simp only [] at h ⊢
  exact h

/-- `proofIrrel` respects the order. -/
theorem proofIrrel_mono (hs : CoreSub r₁ r₂) {d : Nat} {a b : Expr}
    {v : Bool} (h : Setlec.proofIrrel r₁ env d a b = .ok v) :
    Setlec.proofIrrel r₂ env d a b = .ok v := by
  unfold Setlec.proofIrrel at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : r₁.inferIO d a with
  | error err => rw [h1] at h; exact nomatch h
  | ok ta =>
  rw [h1] at h; rw [hs.2.2.2.2.2 h1]
  simp only [] at h ⊢
  cases h2 : r₁.whnf d ta with
  | error err => rw [h2] at h; exact nomatch h
  | ok wa =>
  rw [h2] at h; rw [hs.2.1 h2]
  simp only [] at h ⊢
  by_cases hu : Setlec.isUnitLikeTy env wa = true
  · rw [if_pos hu] at h ⊢
    cases h3 : r₁.inferIO d b with
    | error err => rw [h3] at h; exact nomatch h
    | ok tb =>
    rw [h3] at h; rw [hs.2.2.2.2.2 h3]
    simp only [] at h ⊢
    cases h4 : r₁.whnf d tb with
    | error err => rw [h4] at h; exact nomatch h
    | ok wb =>
    rw [h4] at h; rw [hs.2.1 h4]
    simp only [] at h ⊢
    exact h
  · rw [if_neg hu] at h ⊢
    cases h3 : r₁.inferIO d ta with
    | error err => rw [h3] at h; exact nomatch h
    | ok tta =>
    rw [h3] at h; rw [hs.2.2.2.2.2 h3]
    simp only [] at h ⊢
    cases h4 : r₁.whnf d tta with
    | error err => rw [h4] at h; exact nomatch h
    | ok w =>
    rw [h4] at h; rw [hs.2.1 h4]
    simp only [] at h ⊢
    cases w with
    | sort uT =>
      simp only [] at h ⊢
      cases h5 : Setlec.liftFueled "level comparison"
          (Level.isEquiv uT Level.zero) (m := Setlec.CheckM) with
      | error err => rw [h5] at h; exact nomatch h
      | ok okA =>
      rw [h5] at h
      simp only [] at h ⊢
      cases h6 : r₁.inferIO d b with
      | error err => rw [h6] at h; exact nomatch h
      | ok tb =>
      rw [h6] at h; rw [hs.2.2.2.2.2 h6]
      simp only [] at h ⊢
      cases h7 : r₁.inferIO d tb with
      | error err => rw [h7] at h; exact nomatch h
      | ok ttb =>
      rw [h7] at h; rw [hs.2.2.2.2.2 h7]
      simp only [] at h ⊢
      cases h8 : r₁.whnf d ttb with
      | error err => rw [h8] at h; exact nomatch h
      | ok w₂ =>
      rw [h8] at h; rw [hs.2.1 h8]
      simp only [] at h ⊢
      exact h
    | fvar i' n ty => exact h
    | app f a' => exact h
    | lam n ty b' m => exact h
    | letE n ty v' b' => exact h
    | proj s i' e => exact h
    | lit l => exact h
    | const n us => exact h
    | forallE n ty b' bi => exact h
    | bvar i' => exact h

/-- `etaCert` respects the order. -/
theorem etaCert_mono (hs : CoreSub r₁ r₂) {d : Nat} {n₁ : Name}
    {ty₁ body₁ : Expr} {m₁ : Setlec.BinderMeta} {b : Expr} {v : Bool}
    (h : Setlec.etaCert μ r₁ env d n₁ ty₁ body₁ m₁ b = .ok v) :
    Setlec.etaCert μ r₂ env d n₁ ty₁ body₁ m₁ b = .ok v := by
  unfold Setlec.etaCert at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : r₁.inferIO d b with
  | error err => rw [h1] at h; exact nomatch h
  | ok tb =>
  rw [h1] at h; rw [hs.2.2.2.2.2 h1]
  simp only [] at h ⊢
  cases h2 : r₁.whnf d tb with
  | error err => rw [h2] at h; exact nomatch h
  | ok w =>
  rw [h2] at h; rw [hs.2.1 h2]
  simp only [] at h ⊢
  cases w with
  | forallE n₂ ty₂ bd₂ m₂ =>
    simp only [] at h ⊢
    cases h3 : r₁.defeq d ty₂ ty₁ with
    | error err => rw [h3] at h; exact nomatch h
    | ok c =>
    rw [h3] at h; rw [hs.2.2.2.1 h3]
    simp only [] at h ⊢
    cases c with
    | true =>
      cases h4 : r₁.defeq (d + 1)
          (body₁.instantiate1 (.fvar d n₁ ty₁))
          (.app b (.fvar d n₁ ty₁)) with
      | error err => rw [h4] at h; exact nomatch h
      | ok c₂ =>
        rw [h4] at h
        rw [hs.2.2.2.1 h4]
        dsimp only at h ⊢
        exact h
    | false => exact h
  | sort u => exact h
  | fvar i' n ty => exact h
  | app f a' => exact h
  | lam n ty b' m => exact h
  | letE n ty v' b' => exact h
  | proj s i' e => exact h
  | lit l => exact h
  | const n us => exact h
  | bvar i' => exact h

/-- `structEtaProjCerts` respects the order. -/
theorem structEtaProjCerts_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {T : Name} {us' : List Level} {targs : List Expr} {b : Expr}
    {lpsT : List Name} :
    ∀ {idxs : List Nat} {v : Bool},
      Setlec.structEtaProjCerts r₁ env d T us' targs b lpsT idxs
        = .ok v →
      Setlec.structEtaProjCerts r₂ env d T us' targs b lpsT idxs
        = .ok v := by
  intro idxs
  induction idxs with
  | nil => intro v h; exact h
  | cons i rest ih =>
    intro v h
    unfold Setlec.structEtaProjCerts at h ⊢
    cases hf : env.find? (Setlec.projFnName T i) with
    | none => rw [hf] at h; exact h
    | some ci =>
      rw [hf] at h
      cases ci with
      | recInfo cvp mi rp rules =>
        simp only [] at h ⊢
        by_cases hg : cvp.levelParams = lpsT ∧
            (cvp.type.stripPis (targs.length + 1)).isSome = true
        · rw [if_pos hg] at h ⊢
          simp only [Bind.bind, Except.bind] at h ⊢
          cases hic : Setlec.iotaCerts r₁ env d
              (cvp.type.instantiateLevelParams cvp.levelParams us')
              (targs ++ [b]) with
          | error err => rw [hic] at h; exact nomatch h
          | ok c =>
          rw [hic] at h; rw [iotaCerts_mono hs hic]
          simp only [] at h ⊢
          cases c with
          | true => exact ih h
          | false => exact h
        · rw [if_neg hg] at h ⊢; exact h
      | axiomInfo cv => exact h
      | defnInfo cv vl hint => exact h
      | thmInfo cv vl => exact h
      | indInfo cv caps => exact h
      | ctorInfo cv na nb => exact h
      | projInfo entry => exact h

/-- `pairEtaCert` respects the order (the split-both-sides recipe:
`split at h` handles compound patterns natively; the goal's matches
split into equation branches that unify with `h`'s or contradict). -/
theorem pairEtaCert_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {a b : Expr} {v : Bool}
    (h : Setlec.pairEtaCert μ r₁ env d a b = .ok v) :
    Setlec.pairEtaCert μ r₂ env d a b = .ok v := by
  unfold Setlec.pairEtaCert at h ⊢
  split at h
  · next c us pα pβ s₁ s₂ =>
    split at h
    · next cvm heq =>
      simp only [Bind.bind, Except.bind] at h ⊢
      cases h1 : r₁.inferIO d b with
      | error err => rw [h1] at h; exact nomatch h
      | ok tb =>
      rw [h1] at h; rw [hs.2.2.2.2.2 h1]
      simp only [] at h ⊢
      cases h2 : r₁.whnf d tb with
      | error err => rw [h2] at h; exact nomatch h
      | ok w =>
      rw [h2] at h; rw [hs.2.1 h2]
      simp only [] at h ⊢
      split at h
      · next c' us' A B =>
        split at h
        · next heq2 =>
          split at h
          · next cvr mI rP rr heq3 =>
            split at h
            · next hg =>
              rw [if_pos hg]
              cases h3 : Setlec.liftFueled "level comparison"
                  (Level.isEquivList us us') (m := Setlec.CheckM) with
              | error err => rw [h3] at h; exact nomatch h
              | ok c₃ =>
              rw [h3] at h
              simp only [] at h ⊢
              split at h
              · next hc₃ =>
                rw [if_pos hc₃]
                cases h4 : r₁.defeq d pα A with
                | error err => rw [h4] at h; exact nomatch h
                | ok c₄ =>
                rw [h4] at h; rw [hs.2.2.2.1 h4]
                simp only [] at h ⊢
                split at h
                · next hc₄ =>
                  rw [if_pos hc₄]
                  cases h5 : r₁.defeq d pβ B with
                  | error err => rw [h5] at h; exact nomatch h
                  | ok c₅ =>
                  rw [h5] at h; rw [hs.2.2.2.1 h5]
                  simp only [] at h ⊢
                  split at h
                  · next hc₅ =>
                    rw [if_pos hc₅]
                    cases h6 : r₁.defeq d s₁ (.proj c' 0 b) with
                    | error err => rw [h6] at h; exact nomatch h
                    | ok c₆ =>
                    rw [h6] at h; rw [hs.2.2.2.1 h6]
                    simp only [] at h ⊢
                    split at h
                    · next hc₆ =>
                      rw [if_pos hc₆]
                      cases h7 : r₁.defeq d s₂ (.proj c' 1 b) with
                      | error err => rw [h7] at h; exact nomatch h
                      | ok c₇ =>
                      rw [h7] at h; rw [hs.2.2.2.1 h7]
                      simp only [] at h ⊢
                      split at h
                      · next hc₇ => rw [if_pos hc₇]; exact h
                      · next hc₇ => rw [if_neg hc₇]; exact h
                    · next hc₆ => rw [if_neg hc₆]; exact h
                  · next hc₅ => rw [if_neg hc₅]; exact h
                · next hc₄ => rw [if_neg hc₄]; exact h
              · next hc₃ => rw [if_neg hc₃]; exact h
            · next hg => rw [if_neg hg]; exact h
          · next =>
            exact h
        · next =>
          exact h
      · next => exact h
    · next =>
      exact h
  · next => exact h

/-- `structUnitCert` respects the order. -/
theorem structUnitCert_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {a b : Expr} {v : Bool}
    (h : Setlec.structUnitCert r₁ env d a b = .ok v) :
    Setlec.structUnitCert r₂ env d a b = .ok v := by
  unfold Setlec.structUnitCert at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : r₁.inferIO d a with
  | error err => rw [h1] at h; exact nomatch h
  | ok ta =>
  rw [h1] at h; rw [hs.2.2.2.2.2 h1]
  simp only [] at h ⊢
  cases h2 : r₁.whnf d ta with
  | error err => rw [h2] at h; exact nomatch h
  | ok wta =>
  rw [h2] at h; rw [hs.2.1 h2]
  simp only [] at h ⊢
  split at h
  · next T us' =>
    split at h
    · next cvT caps heq =>
      split at h
      · next hg =>
        rw [if_pos hg]
        cases h3 : r₁.inferIO d b with
        | error err => rw [h3] at h; exact nomatch h
        | ok tb =>
        rw [h3] at h; rw [hs.2.2.2.2.2 h3]
        simp only [] at h ⊢
        cases h4 : r₁.whnf d tb with
        | error err => rw [h4] at h; exact nomatch h
        | ok wtb =>
        rw [h4] at h; rw [hs.2.1 h4]
        simp only [] at h ⊢
        cases h5 : r₁.defeq d wta wtb with
        | error err => rw [h5] at h; exact nomatch h
        | ok c₅ =>
        rw [h5] at h; rw [hs.2.2.2.1 h5]
        simp only [] at h ⊢
        cases c₅ with
        | true => exact iotaCerts_mono hs h
        | false => exact h
      · next hg => rw [if_neg hg]; exact h
    · next => exact h
  · next => exact h

/-- `structEtaCertWith` respects the order. -/
theorem structEtaCertWith_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {a b wtb : Expr} {v : Bool}
    (h : Setlec.structEtaCertWith μ r₁ env d a b wtb = .ok v) :
    Setlec.structEtaCertWith μ r₂ env d a b wtb = .ok v := by
  unfold Setlec.structEtaCertWith at h ⊢
  split at h
  · next c us hga =>
    split at h
    · next cvc cnP cnF heq =>
      split at h
      · next hlen =>
        rw [if_pos hlen]
        split at h
        · next T us' hgb =>
          split at h
          · next cvT caps heq2 =>
            split at h
            · next hg =>
              rw [if_pos hg]
              simp only [Bind.bind, Except.bind] at h ⊢
              cases h3 : Setlec.liftFueled "level comparison"
                  (Level.isEquivList us us') (m := Setlec.CheckM) with
              | error err => rw [h3] at h; exact nomatch h
              | ok c₃ =>
              rw [h3] at h
              simp only [] at h ⊢
              split at h
              · next hc₃ =>
                rw [if_pos hc₃]
                cases h4 : Setlec.iotaCerts r₁ env d
                    (cvT.type.instantiateLevelParams cvT.levelParams
                      us') wtb.getAppArgs with
                | error err => rw [h4] at h; exact nomatch h
                | ok c₄ =>
                rw [h4] at h; rw [iotaCerts_mono hs h4]
                simp only [] at h ⊢
                split at h
                · next hc₄ =>
                  rw [if_pos hc₄]
                  cases h5 : Setlec.structEtaProjCerts r₁ env d T us'
                      wtb.getAppArgs b cvT.levelParams
                      (List.range cnF) with
                  | error err => rw [h5] at h; exact nomatch h
                  | ok c₅ =>
                  rw [h5] at h; rw [structEtaProjCerts_mono hs h5]
                  simp only [] at h ⊢
                  split at h
                  · next hc₅ =>
                    rw [if_pos hc₅]
                    cases h6 : Setlec.defEqList r₁ env d
                        (a.getAppArgs.take cnP) wtb.getAppArgs with
                    | error err => rw [h6] at h; exact nomatch h
                    | ok c₆ =>
                    rw [h6] at h; rw [defEqList_mono hs h6]
                    simp only [] at h ⊢
                    split at h
                    · next hc₆ =>
                      rw [if_pos hc₆]
                      by_cases htt : μ.ttChecks = true
                      · rw [if_pos htt] at h ⊢
                        cases h7 : Setlec.iotaCerts r₁ env d
                            (cvc.type.instantiateLevelParams
                              cvc.levelParams us)
                            (wtb.getAppArgs ++
                              (List.range cnF).map fun i =>
                                Expr.mkAppN
                                  (.const (Setlec.projFnName T i) us')
                                  (wtb.getAppArgs ++ [b])) with
                        | error err => rw [h7] at h; exact nomatch h
                        | ok c₇ =>
                        rw [h7] at h; rw [iotaCerts_mono hs h7]
                        simp only [] at h ⊢
                        cases c₇ with
                        | true => exact defEqList_mono hs h
                        | false => exact h
                      · rw [if_neg htt] at h ⊢
                        exact defEqList_mono hs
                          (by simpa [pure, Except.pure] using h)
                    · next hc₆ => rw [if_neg hc₆]; exact h
                  · next hc₅ => rw [if_neg hc₅]; exact h
                · next hc₄ => rw [if_neg hc₄]; exact h
              · next hc₃ => rw [if_neg hc₃]; exact h
            · next hg => rw [if_neg hg]; exact h
          · next => exact h
        · next => exact h
      · next hlen => rw [if_neg hlen]; exact h
    · next => exact h
  · next => exact h

/-- `structEtaCert` respects the order. -/
theorem structEtaCert_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {a b : Expr} {v : Bool}
    (h : Setlec.structEtaCert μ r₁ env d a b = .ok v) :
    Setlec.structEtaCert μ r₂ env d a b = .ok v := by
  unfold Setlec.structEtaCert at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : r₁.inferIO d b with
  | error err => rw [h1] at h; exact nomatch h
  | ok tb =>
  rw [h1] at h; rw [hs.2.2.2.2.2 h1]
  simp only [] at h ⊢
  cases h2 : r₁.whnf d tb with
  | error err => rw [h2] at h; exact nomatch h
  | ok wtb =>
  rw [h2] at h; rw [hs.2.1 h2]
  simp only [] at h ⊢
  exact structEtaCertWith_mono hs h

/-- `stuckIrrel` respects the order. -/
theorem stuckIrrel_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {a b : Expr} {v : Bool}
    (h : Setlec.stuckIrrel μ r₁ env d a b = .ok v) :
    Setlec.stuckIrrel μ r₂ env d a b = .ok v := by
  unfold Setlec.stuckIrrel at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : Setlec.pairEtaCert μ r₁ env d a b with
  | error err => rw [h1] at h; exact nomatch h
  | ok c₁ =>
  rw [h1] at h; rw [pairEtaCert_mono hs h1]
  simp only [] at h ⊢
  cases c₁ with
  | true => exact h
  | false =>
  cases h2 : Setlec.pairEtaCert μ r₁ env d b a with
  | error err => rw [h2] at h; exact nomatch h
  | ok c₂ =>
  rw [h2] at h; rw [pairEtaCert_mono hs h2]
  simp only [] at h ⊢
  cases c₂ with
  | true => exact h
  | false =>
  cases h3 : Setlec.structEtaCert μ r₁ env d a b with
  | error err => rw [h3] at h; exact nomatch h
  | ok c₃ =>
  rw [h3] at h; rw [structEtaCert_mono hs h3]
  simp only [] at h ⊢
  cases c₃ with
  | true => exact h
  | false =>
  cases h4 : Setlec.structEtaCert μ r₁ env d b a with
  | error err => rw [h4] at h; exact nomatch h
  | ok c₄ =>
  rw [h4] at h; rw [structEtaCert_mono hs h4]
  simp only [] at h ⊢
  cases c₄ with
  | true => exact h
  | false =>
  cases h5 : Setlec.structUnitCert r₁ env d a b with
  | error err => rw [h5] at h; exact nomatch h
  | ok c₅ =>
  rw [h5] at h; rw [structUnitCert_mono hs h5]
  simp only [] at h ⊢
  cases c₅ with
  | true => exact h
  | false => exact proofIrrel_mono hs h

/-- `litMajorToCtor` respects the order. -/
theorem litMajorToCtor_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {e x : Expr}
    (h : Setlec.litMajorToCtor r₁ env d e = .ok x) :
    Setlec.litMajorToCtor r₂ env d e = .ok x := by
  cases e with
  | lit l =>
    cases l with
    | strVal s =>
      unfold Setlec.litMajorToCtor at h ⊢
      simp only [] at h ⊢
      by_cases hsup : Setlec.strLitSupported env = true
      · rw [if_pos hsup] at h
        rw [if_pos hsup]
        exact hs.2.1 h
      · rw [if_neg hsup] at h
        rw [if_neg hsup]
        exact h
    | natVal n => exact h
  | sort u => exact h
  | fvar i n ty => exact h
  | app f a => exact h
  | lam n ty b m => exact h
  | letE n ty v' b => exact h
  | proj s i e' => exact h
  | const n us => exact h
  | forallE n ty b bi => exact h
  | bvar i => exact h

/-- `majorToCtor` respects the order. -/
theorem majorToCtor_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {recName : Name} {rules : List Setlec.RecRule}
    {major x : Expr}
    (h : Setlec.majorToCtor μ r₁ env d recName rules major = .ok x) :
    Setlec.majorToCtor μ r₂ env d recName rules major = .ok x := by
  unfold Setlec.majorToCtor at h ⊢
  by_cases hca : Setlec.isCtorApp env major = true
  · rw [if_pos hca] at h ⊢; exact h
  rw [if_neg hca] at h ⊢
  split at h
  · next rl =>
    split at h
    · next cvj cnP cnF heq =>
      split at h
      · next T tus heq2 =>
        split at h
        · next cvT caps heq3 =>
          by_cases hK : caps.ruleK = true ∧ cnF = 0
          · rw [if_pos hK] at h ⊢
            simp only [Bind.bind, Except.bind] at h ⊢
            cases h1 : r₁.inferIO d major with
            | error err => rw [h1] at h; exact nomatch h
            | ok tm =>
            rw [h1] at h; rw [hs.2.2.2.2.2 h1]
            simp only [] at h ⊢
            cases h2 : r₁.whnf d tm with
            | error err => rw [h2] at h; exact nomatch h
            | ok tmaj =>
            rw [h2] at h; rw [hs.2.1 h2]
            simp only [] at h ⊢
            split at h
            · next T' ust heq4 =>
              split at h
              · next hg1 =>
                rw [if_pos hg1]
                split at h
                · next hg2 =>
                  rw [if_pos hg2]
                  split at h
                  · next hg3 =>
                    rw [if_pos hg3]
                    cases h3 : Setlec.iotaCerts r₁ env d
                        (cvj.type.instantiateLevelParams
                          cvj.levelParams ust)
                        (tmaj.getAppArgs.take cnP) with
                    | error err => rw [h3] at h; exact nomatch h
                    | ok c₃ =>
                    rw [h3] at h; rw [iotaCerts_mono hs h3]
                    simp only [] at h ⊢
                    cases c₃ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    cases h4 : r₁.inferIO d (Expr.mkAppN
                        (.const rl.ctor ust)
                        (tmaj.getAppArgs.take cnP)) with
                    | error err => rw [h4] at h; exact nomatch h
                    | ok tf =>
                    rw [h4] at h; rw [hs.2.2.2.2.2 h4]
                    simp only [] at h ⊢
                    cases h5 : r₁.defeq d tmaj tf with
                    | error err => rw [h5] at h; exact nomatch h
                    | ok c₅ =>
                    rw [h5] at h; rw [hs.2.2.2.1 h5]
                    simp only [] at h ⊢
                    cases c₅ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    cases h6 : Setlec.proofIrrel r₁ env d
                        (Expr.mkAppN (.const rl.ctor ust)
                          (tmaj.getAppArgs.take cnP)) major with
                    | error err => rw [h6] at h; exact nomatch h
                    | ok c₆ =>
                    rw [h6] at h; rw [proofIrrel_mono hs h6]
                    simp only [] at h ⊢
                    exact h
                  · next hg3 => rw [if_neg hg3]; exact h
                · next hg2 => rw [if_neg hg2]; exact h
              · next hg1 => rw [if_neg hg1]; exact h
            · next => exact h
          · rw [if_neg hK] at h ⊢
            by_cases hE : caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
                Setlec.Name.isProjFnShape recName = false
            · rw [if_pos hE] at h ⊢
              simp only [Bind.bind, Except.bind] at h ⊢
              cases h1 : r₁.inferIO d major with
              | error err => rw [h1] at h; exact nomatch h
              | ok tm =>
              rw [h1] at h; rw [hs.2.2.2.2.2 h1]
              simp only [] at h ⊢
              cases h2 : r₁.whnf d tm with
              | error err => rw [h2] at h; exact nomatch h
              | ok tmaj =>
              rw [h2] at h; rw [hs.2.1 h2]
              simp only [] at h ⊢
              split at h
              · next T' ust heq4 =>
                split at h
                · next hg1 =>
                  rw [if_pos hg1]
                  split at h
                  · next hg2 =>
                    rw [if_pos hg2]
                    split at h
                    · next hg3 =>
                      rw [if_pos hg3]
                      cases h3 : Setlec.iotaCerts r₁ env d
                          (cvj.type.instantiateLevelParams
                            cvj.levelParams ust)
                          (Setlec.etaFabArgs T ust tmaj.getAppArgs
                            major caps.etaFields) with
                      | error err => rw [h3] at h; exact nomatch h
                      | ok c₃ =>
                      rw [h3] at h; rw [iotaCerts_mono hs h3]
                      simp only [] at h ⊢
                      cases c₃ with
                      | false => exact h
                      | true =>
                      simp only [if_true] at h ⊢
                      cases h4 : Setlec.structEtaCertWith μ r₁ env d
                          (Expr.mkAppN (.const caps.etaCtor ust)
                            (Setlec.etaFabArgs T ust tmaj.getAppArgs
                              major caps.etaFields)) major tmaj with
                      | error err => rw [h4] at h; exact nomatch h
                      | ok c₄ =>
                      rw [h4] at h; rw [structEtaCertWith_mono hs h4]
                      simp only [] at h ⊢
                      cases c₄ with
                      | true => exact h
                      | false =>
                      simp only [Bool.false_eq_true, if_false] at h ⊢
                      split at h
                      · next hg4 =>
                        rw [if_pos hg4]
                        cases h5 : Setlec.proofIrrel r₁ env d
                            (Expr.mkAppN (.const caps.etaCtor ust)
                              (Setlec.etaFabArgs T ust
                                tmaj.getAppArgs major
                                caps.etaFields)) major with
                        | error err => rw [h5] at h; exact nomatch h
                        | ok c₅ =>
                        rw [h5] at h; rw [proofIrrel_mono hs h5]
                        simp only [] at h ⊢
                        exact h
                      · next hg4 => rw [if_neg hg4]; exact h
                    · next hg3 => rw [if_neg hg3]; exact h
                  · next hg2 => rw [if_neg hg2]; exact h
                · next hg1 => rw [if_neg hg1]; exact h
              · next => exact h
            · rw [if_neg hE] at h ⊢
              exact h
        · next => exact h
      · next => exact h
    · next => exact h
  · next => exact h

/-- `iotaRec` respects the order — the last helper. -/
theorem iotaRec_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {e : Expr} {o : Option Expr}
    (h : Setlec.iotaRec μ r₁ env d e = .ok o) :
    Setlec.iotaRec μ r₂ env d e = .ok o := by
  unfold Setlec.iotaRec at h ⊢
  split at h
  · next c us hga =>
    split at h
    · next cv mI rP rules heq =>
      dsimp only [] at h ⊢
      split at h
      · next hlen =>
        rw [if_pos hlen]
        simp only [Bind.bind, Except.bind] at h ⊢
        cases h1 : r₁.whnf d (e.getAppArgs.getD mI (.bvar 0)) with
        | error err => rw [h1] at h; exact nomatch h
        | ok major₀ =>
        rw [h1] at h; rw [hs.2.1 h1]
        simp only [] at h ⊢
        cases h2 : Setlec.litMajorToCtor r₁ env d major₀ with
        | error err => rw [h2] at h; exact nomatch h
        | ok major₁ =>
        rw [h2] at h; rw [litMajorToCtor_mono hs h2]
        simp only [] at h ⊢
        cases h3 : Setlec.majorToCtor μ r₁ env d c rules major₁ with
        | error err => rw [h3] at h; exact nomatch h
        | ok major =>
        rw [h3] at h; rw [majorToCtor_mono hs h3]
        simp only [] at h ⊢
        split at h
        · next cj usj hgm =>
          split at h
          · next cvj na nb heq2 =>
            split at h
            · next rl heq3 =>
              split at h
              · next hlen2 =>
                rw [if_pos hlen2]
                split at h
                · next hinert => exact nomatch h
                · next hinert =>
                  rw [if_neg hinert]
                  split at h
                  · next hg2 =>
                    rw [if_pos hg2]
                    cases h4 : Setlec.liftFueled "level comparison"
                        (Level.isEquivList usj
                          (Setlec.recFireComparands rl cv.levelParams
                            us cvj.levelParams e.getAppArgs rP).1)
                        (m := Setlec.CheckM) with
                    | error err => rw [h4] at h; exact nomatch h
                    | ok c₄ =>
                    rw [h4] at h
                    simp only [] at h ⊢
                    cases c₄ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    cases h5 : Setlec.defEqList r₁ env d
                        (major.getAppArgs.take rl.ctorParams)
                        (Setlec.recFireComparands rl cv.levelParams
                          us cvj.levelParams e.getAppArgs rP).2 with
                    | error err => rw [h5] at h; exact nomatch h
                    | ok c₅ =>
                    rw [h5] at h; rw [defEqList_mono hs h5]
                    simp only [] at h ⊢
                    cases c₅ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    cases h6 : Setlec.iotaCerts r₁ env d
                        (cv.type.instantiateLevelParams cv.levelParams
                          us)
                        (e.getAppArgs.take mI ++ [major]) with
                    | error err => rw [h6] at h; exact nomatch h
                    | ok c₆ =>
                    rw [h6] at h; rw [iotaCerts_mono hs h6]
                    simp only [] at h ⊢
                    cases c₆ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    cases h7 : Setlec.iotaCerts r₁ env d
                        (cvj.type.instantiateLevelParams
                          cvj.levelParams usj)
                        major.getAppArgs with
                    | error err => rw [h7] at h; exact nomatch h
                    | ok c₇ =>
                    rw [h7] at h; rw [iotaCerts_mono hs h7]
                    simp only [] at h ⊢
                    cases c₇ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    split at h
                    · next cbody residual heq4 heq5 =>
                      split at h
                      · next hcb =>
                        cases h8 : Setlec.defEqList r₁ env d
                            (residual.getAppArgs.drop rl.ctorParams)
                            ((e.getAppArgs.take mI).drop rP) with
                        | error err => rw [h8] at h; exact nomatch h
                        | ok c₈ =>
                        rw [h8] at h; rw [defEqList_mono hs h8]
                        simp only [] at h ⊢
                        exact h
                      · next => exact h
                    · next => exact h
                  · next hg2 => rw [if_neg hg2]; exact h
              · next hlen2 => rw [if_neg hlen2]; exact h
            · next => exact h
          · next => exact h
        · next => exact h
      · next hlen => rw [if_neg hlen]; exact h
    · next => exact h
  · next => exact h

/-- `projFieldDom` respects the order. -/
theorem projFieldDom_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {sp : Bool} {sn : Name} {e' : Expr} :
    ∀ {k j : Nat} {tel x : Expr},
      Setlec.projFieldDom r₁ env d sp sn e' j k tel = .ok x →
      Setlec.projFieldDom r₂ env d sp sn e' j k tel = .ok x := by
  intro k
  induction k with
  | zero => intro j tel x h; cases tel <;> exact h
  | succ k ih =>
    intro j tel x h
    cases tel with
    | forallE nm dom rest bi =>
      unfold Setlec.projFieldDom at h ⊢
      by_cases hb : rest.looseBVarsBounded 0 = true
      · rw [if_pos hb] at h ⊢
        exact ih h
      · rw [if_neg hb] at h ⊢
        by_cases hsp : sp = true
        · rw [if_pos hsp] at h ⊢
          simp only [Bind.bind, Except.bind] at h ⊢
          cases h1 : Setlec.isPropType r₁ env d dom with
          | error err => rw [h1] at h; exact nomatch h
          | ok b =>
          rw [h1] at h; rw [isPropType_mono hs h1]
          simp only [] at h ⊢
          cases b with
          | true => exact ih (by simpa using h)
          | false => exact h
        · rw [if_neg hsp] at h ⊢
          exact ih (by simpa [Bind.bind, Except.bind] using h)
    | sort u => exact h
    | fvar i n ty => exact h
    | app f a => exact h
    | lam n ty b m => exact h
    | letE n ty v b => exact h
    | proj s i e => exact h
    | lit l => exact h
    | const n us => exact h
    | bvar i => exact h

/-- `annotateProjRec` respects the order. -/
theorem annotateProjRec_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {entry : Setlec.ProjEntry} {i : Nat} {te e' : Expr}
    {us : List Level} {x : Expr}
    (h : Setlec.annotateProjRec r₁ env d entry i te e' us = .ok x) :
    Setlec.annotateProjRec r₂ env d entry i te e' us = .ok x := by
  unfold Setlec.annotateProjRec at h ⊢
  dsimp only [] at h ⊢
  split at h
  · next cvC nc cnF heq =>
    split at h
    · next hlen =>
      rw [if_pos hlen]
      split at h
      · next tel heq2 =>
        cases h1 : Setlec.isPropType r₁ env d te with
        | error err => rw [h1] at h; exact nomatch h
        | ok sp =>
        rw [h1] at h; rw [isPropType_mono hs h1]
        simp only [Bind.bind, Except.bind] at h ⊢
        cases h2 : Setlec.projFieldDom r₁ env d sp entry.structName e'
            0 i tel with
        | error err => rw [h2] at h; exact nomatch h
        | ok fi =>
        rw [h2] at h; rw [projFieldDom_mono hs h2]
        simp only [] at h ⊢
        split at h
        · next minor heq3 =>
          cases h3 : r₁.annotate d fi with
          | error err => rw [h3] at h; exact nomatch h
          | ok fi' =>
          rw [h3] at h; rw [hs.2.2.2.2.1 h3]
          simp only [] at h ⊢
          cases h4 : r₁.infer d fi' with
          | error err => rw [h4] at h; exact nomatch h
          | ok tfi =>
          rw [h4] at h; rw [hs.2.2.1 h4]
          simp only [] at h ⊢
          cases h5 : Setlec.ensureSort r₁ env d tfi with
          | error err => rw [h5] at h; exact nomatch h
          | ok sfi =>
          rw [h5] at h; rw [ensureSort_mono hs h5]
          simp only [] at h ⊢
          by_cases hsp : sp = true
          · rw [if_pos hsp] at h ⊢
            cases h6 : Setlec.liftFueled "level comparison"
                (Level.isEquiv sfi Level.zero)
                (m := Setlec.CheckM) with
            | error err => rw [h6] at h; exact nomatch h
            | ok c₆ =>
            rw [h6] at h
            simp only [] at h ⊢
            cases c₆ with
            | false => exact h
            | true =>
            simp only [if_true] at h ⊢
            split at h
            · next hre =>
              rw [if_pos hre]
              split at h
              · next hg => rw [if_pos hg]; exact hs.2.2.2.2.1 h
              · next hg => rw [if_neg hg]; exact h
            · next hre =>
              rw [if_neg hre]
              split at h
              · next hg => rw [if_pos hg]; exact hs.2.2.2.2.1 h
              · next hg => rw [if_neg hg]; exact h
          · rw [if_neg hsp] at h ⊢
            split at h
            · next hre =>
              rw [if_pos hre]
              split at h
              · next hg =>
                rw [if_pos hg]
                exact hs.2.2.2.2.1 (by simpa using h)
              · next hg => rw [if_neg hg]; exact h
            · next hre =>
              rw [if_neg hre]
              split at h
              · next hg =>
                rw [if_pos hg]
                exact hs.2.2.2.2.1 (by simpa using h)
              · next hg => rw [if_neg hg]; exact h
        · next => exact h
      · next => exact h
    · next hlen => rw [if_neg hlen]; exact h
  · next => exact h

/-- `annotateProjElim` respects the order. -/
theorem annotateProjElim_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {sn : Name} {i : Nat} {te e' x : Expr}
    (h : Setlec.annotateProjElim r₁ env d sn i te e' = .ok x) :
    Setlec.annotateProjElim r₂ env d sn i te e' = .ok x := by
  unfold Setlec.annotateProjElim at h ⊢
  split at h
  · next T us hga =>
    by_cases hT : T = sn
    · rw [if_pos hT] at h ⊢
      split at h
      · next cvp mi rp rules heq =>
        split at h
        · next hlen =>
          rw [if_pos hlen]
          dsimp only [] at h ⊢
          split at h
          · next hg =>
            rw [if_pos hg]
            exact hs.2.2.2.2.1 h
          · next hg => rw [if_neg hg]; exact h
        · next hlen => rw [if_neg hlen]; exact h
      · next entry heq =>
        split at h
        · next hnat => exact nomatch h
        · next hnat =>
          rw [if_neg hnat]
          exact annotateProjRec_mono hs h
      · next => exact h
    · rw [if_neg hT] at h ⊢
      exact h
  · next => exact h

/-- Task #161 P5: the ∀/λ writes respect the order — a pure chain read,
or the `infer`/`ensureSort` calls the `letE` clause already makes. -/
theorem annotPwPi_sub (hs : CoreSub r₁ r₂) {d : Nat} {e : Expr}
    {pw : PropWhen} (h : Setlec.annotPwPi r₁ env d e = .ok pw) :
    Setlec.annotPwPi r₂ env d e = .ok pw := by
  revert h
  unfold Setlec.annotPwPi
  cases e.forallPw with
  | some p => exact id
  | none =>
    simp only [Bind.bind, Except.bind]
    cases h1 : r₁.infer d e with
    | error err => intro h; exact nomatch h
    | ok bt =>
      rw [hs.2.2.1 h1]
      simp only []
      cases h2 : Setlec.ensureSort r₁ env d bt with
      | error err => intro h; exact nomatch h
      | ok v => rw [ensureSort_mono hs h2]; exact id

/-- The λ twin of `annotPwPi_sub`. -/
theorem annotPwLam_sub (hs : CoreSub r₁ r₂) {d : Nat} {e : Expr}
    {pw : PropWhen} (h : Setlec.annotPwLam r₁ env d e = .ok pw) :
    Setlec.annotPwLam r₂ env d e = .ok pw := by
  revert h
  unfold Setlec.annotPwLam
  cases e.lamPw with
  | some p => exact id
  | none =>
    simp only [Bind.bind, Except.bind]
    cases h1 : r₁.infer d e with
    | error err => intro h; exact nomatch h
    | ok bt =>
      rw [hs.2.2.1 h1]
      simp only []
      cases h2 : r₁.infer d bt with
      | error err => intro h; exact nomatch h
      | ok btt =>
        rw [hs.2.2.1 h2]
        simp only []
        cases h3 : Setlec.ensureSort r₁ env d btt with
        | error err => intro h; exact nomatch h
        | ok v => rw [ensureSort_mono hs h3]; exact id

/-- `annotateBody` respects the order. -/
theorem annotateBody_mono (hs : CoreSub r₁ r₂) {μ : Setlec.CheckMode}
    {d : Nat} {e x : Expr}
    (h : Setlec.annotateBody μ r₁ env d e = .ok x) :
    Setlec.annotateBody μ r₂ env d e = .ok x := by
  unfold Setlec.annotateBody at h ⊢
  cases e with
  | bvar i => exact h
  | fvar idx n ty => exact h
  | sort u => exact h
  | const n us => exact h
  | lit l => cases l <;> exact h
  | app f a =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.annotate d f with
    | error err => rw [h1] at h; exact nomatch h
    | ok f' =>
    rw [h1] at h; rw [hs.2.2.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.annotate d a with
    | error err => rw [h2] at h; exact nomatch h
    | ok a' =>
    rw [h2] at h; rw [hs.2.2.2.2.1 h2]
    simp only [] at h ⊢
    exact h
  | forallE n ty body mb =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.annotate d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok ty' =>
    rw [h1] at h; rw [hs.2.2.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.annotate (d + 1)
        (body.instantiate1 (.fvar d n ty')) with
    | error err => rw [h2] at h; exact nomatch h
    | ok body' =>
    rw [h2] at h; rw [hs.2.2.2.2.1 h2]
    simp only [] at h ⊢
    -- task #161 P5: the write, one bind further in
    revert h
    split
    · cases h3 : Setlec.annotPwPi r₁ env (d + 1) body' with
      | error err => intro h; exact nomatch h
      | ok pw => rw [annotPwPi_sub hs h3]; exact id
    · exact id
  | lam n ty body mb =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.annotate d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok ty' =>
    rw [h1] at h; rw [hs.2.2.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.annotate (d + 1)
        (body.instantiate1 (.fvar d n ty')) with
    | error err => rw [h2] at h; exact nomatch h
    | ok body' =>
    rw [h2] at h; rw [hs.2.2.2.2.1 h2]
    simp only [] at h ⊢
    -- task #161 P5: the write, one bind further in
    revert h
    split
    · cases h3 : Setlec.annotPwLam r₁ env (d + 1) body' with
      | error err => intro h; exact nomatch h
      | ok pw => rw [annotPwLam_sub hs h3]; exact id
    · exact id
  | letE nm ty v b =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.annotate d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok ty' =>
    rw [h1] at h; rw [hs.2.2.2.2.1 h1]
    simp only [] at h ⊢
    cases h4 : r₁.annotate d v with
    | error err => rw [h4] at h; exact nomatch h
    | ok v' =>
    rw [h4] at h; rw [hs.2.2.2.2.1 h4]
    simp only [] at h ⊢
    exact hs.2.2.2.2.1 h
  | proj sn i pe =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.annotate d pe with
    | error err => rw [h1] at h; exact nomatch h
    | ok e' =>
    rw [h1] at h; rw [hs.2.2.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.infer d e' with
    | error err => rw [h2] at h; exact nomatch h
    | ok te₀ =>
    rw [h2] at h; rw [hs.2.2.1 h2]
    simp only [] at h ⊢
    cases h3 : r₁.whnf d te₀ with
    | error err => rw [h3] at h; exact nomatch h
    | ok te =>
    rw [h3] at h; rw [hs.2.1 h3]
    simp only [] at h ⊢
    split at h
    · next T tus hga =>
      split at h
      · next entry heq =>
        split at h
        · next hnat =>
          rw [if_pos hnat]
          split at h
          · next hlen =>
            rw [if_pos hlen]
            exact h
          · next hlen => rw [if_neg hlen]; exact nomatch h
        · next hnat =>
          rw [if_neg hnat]
          exact annotateProjElim_mono hs h
      · next heq => exact annotateProjElim_mono hs h
    · next => exact annotateProjElim_mono hs h

/-- `whnfCoreBody` respects the order. -/
theorem whnfCoreBody_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {e x : Expr}
    (h : Setlec.whnfCoreBody μ r₁ env d e = .ok x) :
    Setlec.whnfCoreBody μ r₂ env d e = .ok x := by
  unfold Setlec.whnfCoreBody at h ⊢
  cases e with
  | sort u => exact h
  | fvar idx n ty => exact h
  | forallE n ty body bi => exact h
  | lam n ty body mb => exact h
  | const n us => exact h
  | lit l => exact h
  | bvar i => exact h
  | app f a =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.whnfCore d f with
    | error err => rw [h1] at h; exact nomatch h
    | ok fw =>
    rw [h1] at h; rw [hs.1 h1]
    simp only [] at h ⊢
    split at h
    · next n₁ ty₁ body₁ mb₁ =>
      -- task #161: the β gate's fired arm is the reduct site; the
      -- other arm is the pre-gate proof, verbatim
      by_cases hgate : betaGateFires μ mb₁.pw = true
      · rw [if_pos hgate] at h ⊢
        exact hs.1 h
      rw [if_neg hgate] at h ⊢
      cases h2 : r₁.inferIO d a with
      | error err => rw [h2] at h; exact nomatch h
      | ok ta =>
      rw [h2] at h; rw [hs.2.2.2.2.2 h2]
      simp only [] at h ⊢
      cases h3 : r₁.defeq d ta ty₁ with
      | error err => rw [h3] at h; exact nomatch h
      | ok c₃ =>
      rw [h3] at h; rw [hs.2.2.2.1 h3]
      simp only [] at h ⊢
      cases c₃ with
      | true => exact hs.1 (by simpa using h)
      | false => exact h
    · next =>
      cases h2 : Setlec.iotaRec μ r₁ env d (.app fw a) with
      | error err => rw [h2] at h; exact nomatch h
      | ok o =>
      rw [h2] at h; rw [iotaRec_mono hs h2]
      simp only [] at h ⊢
      cases o with
      | some e₂ => exact hs.1 h
      | none => exact h
  | letE nm ty v b =>
    exact hs.1 h
  | proj sn i pe =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.whnf d pe with
    | error err => rw [h1] at h; exact nomatch h
    | ok w =>
    rw [h1] at h; rw [hs.2.1 h1]
    simp only [] at h ⊢
    cases h2 : Setlec.projLitToCtor r₁ env d w with
    | error err => rw [h2] at h; exact nomatch h
    | ok w₂ =>
    rw [h2] at h; rw [projLitToCtor_mono hs h2]
    simp only [] at h ⊢
    split at h
    · next entry heq =>
      split at h
      · next c us hga =>
        split at h
        · next hg =>
          rw [if_pos hg]
          cases h3 : Setlec.projCert r₁ env d w₂ i entry.numParams with
          | error err => rw [h3] at h; exact nomatch h
          | ok c₃ =>
          rw [h3] at h; rw [projCert_mono hs h3]
          simp only [] at h ⊢
          cases c₃ with
          | false => exact h
          | true =>
          simp only [if_true] at h ⊢
          exact hs.1 h
        · next hg => rw [if_neg hg]; exact h
      · next => exact h
    · next => exact h

/-- `inferBody` respects the order. -/
theorem inferBody_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {e x : Expr}
    (h : Setlec.inferBody μ r₁ env d e = .ok x) :
    Setlec.inferBody μ r₂ env d e = .ok x := by
  unfold Setlec.inferBody at h ⊢
  simp only [Setlec.viewM, Setlec.Expr.view, Bind.bind, Except.bind,
    pure, Except.pure] at h ⊢
  cases e with
  | sort u => exact h
  | fvar idx n ty => exact h
  | const n us => exact h
  | lit l => cases l <;> exact h
  | bvar i => exact h
  | forallE n ty body mb =>
    simp only [] at h ⊢
    cases h1 : r₁.infer d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok tty =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tty with
    | error err => rw [h2] at h; exact nomatch h
    | ok w =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    split at h
    · next u =>
      cases h3 : r₁.infer (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | error err => rw [h3] at h; exact nomatch h
      | ok tb =>
      rw [h3] at h; rw [hs.2.2.1 h3]
      simp only [] at h ⊢
      cases h4 : Setlec.ensureSort r₁ env (d + 1) tb with
      | error err => rw [h4] at h; exact nomatch h
      | ok v' =>
      rw [h4] at h; rw [ensureSort_mono hs h4]
      simp only [] at h ⊢
      exact h
    · next => exact h
  | lam n ty body mb =>
    simp only [] at h ⊢
    cases h1 : r₁.infer d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok tty =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tty with
    | error err => rw [h2] at h; exact nomatch h
    | ok w =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    split at h
    · next u =>
      cases h3 : r₁.infer (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | error err => rw [h3] at h; exact nomatch h
      | ok bt =>
      rw [h3] at h; rw [hs.2.2.1 h3]
      simp only [] at h ⊢
      by_cases hv : μ.verified = true
      case neg =>
        rw [if_neg hv] at h ⊢
        exact h
      rw [if_pos hv] at h ⊢
      revert h
      cases body.lamPw with
      | some pwI =>
        intro h
        exact h
      | none =>
        intro h
        dsimp only at h ⊢
        cases h4 : r₁.inferIO (d + 1) bt with
        | error err => rw [h4] at h; exact nomatch h
        | ok btt =>
        rw [h4] at h; rw [hs.2.2.2.2.2 h4]
        simp only [] at h ⊢
        cases h5 : Setlec.ensureSort r₁ env (d + 1) btt with
        | error err => rw [h5] at h; exact nomatch h
        | ok s5 =>
        rw [h5] at h; rw [ensureSort_mono hs h5]
        simp only [] at h ⊢
        exact h
    · next => exact h
  | app f a =>
    simp only [] at h ⊢
    cases h1 : r₁.infer d f with
    | error err => rw [h1] at h; exact nomatch h
    | ok tf =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tf with
    | error err => rw [h2] at h; exact nomatch h
    | ok w =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    split at h
    · next n₁ ty₁ body₁ mt =>
      cases h3 : r₁.infer d a with
      | error err => rw [h3] at h; exact nomatch h
      | ok ta =>
      rw [h3] at h; rw [hs.2.2.1 h3]
      simp only [] at h ⊢
      cases h4 : r₁.defeq d ta ty₁ with
      | error err => rw [h4] at h; exact nomatch h
      | ok c₄ =>
      rw [h4] at h; rw [hs.2.2.2.1 h4]
      simp only [] at h ⊢
      cases c₄ with
      | true => simpa using h
      | false => exact h
    · next => exact h
  | proj sn i pe =>
    simp only [] at h ⊢
    cases h1 : r₁.infer d pe with
    | error err => rw [h1] at h; exact nomatch h
    | ok tpe =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tpe with
    | error err => rw [h2] at h; exact nomatch h
    | ok te =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    split at h
    · next T us hga =>
      split at h
      · next entry heq =>
        split at h
        · next hg =>
          rw [if_pos hg]
          exact h
        · next hg => rw [if_neg hg]; exact h
      · next => exact h
    · next => exact h
  | letE nm ty v b =>
    simp only [] at h ⊢
    cases h1 : r₁.infer d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok tty =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : Setlec.ensureSort r₁ env d tty with
    | error err => rw [h2] at h; exact nomatch h
    | ok s2 =>
    rw [h2] at h; rw [ensureSort_mono hs h2]
    simp only [] at h ⊢
    cases h3 : r₁.infer d v with
    | error err => rw [h3] at h; exact nomatch h
    | ok tv =>
    rw [h3] at h; rw [hs.2.2.1 h3]
    simp only [] at h ⊢
    cases h4 : r₁.defeq d tv ty with
    | error err => rw [h4] at h; exact nomatch h
    | ok c₄ =>
    rw [h4] at h; rw [hs.2.2.2.1 h4]
    simp only [] at h ⊢
    cases c₄ with
    | true => exact hs.2.2.1 (by simpa using h)
    | false => exact h

/-- `defeqStep` respects the order — the last cascade. -/
theorem defeqStep_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {k₁ k₂ : Expr → Expr → Setlec.CheckM Bool}
    (hk : ∀ {a b : Expr} {v : Bool},
      k₁ a b = .ok v → k₂ a b = .ok v)
    {a b : Expr} {v : Bool}
    (h : Setlec.defeqStep μ r₁ env d k₁ a b = .ok v) :
    Setlec.defeqStep μ r₂ env d k₂ a b = .ok v := by
  unfold Setlec.defeqStep at h ⊢
  by_cases hab : (a == b) = true
  · rw [if_pos hab] at h ⊢; exact h
  rw [if_neg hab] at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases hwa : r₁.whnfCore d a with
  | error err => rw [hwa] at h; exact nomatch h
  | ok a' =>
  rw [hwa] at h; rw [hs.1 hwa]
  simp only [] at h ⊢
  cases hwb : r₁.whnfCore d b with
  | error err => rw [hwb] at h; exact nomatch h
  | ok b' =>
  rw [hwb] at h; rw [hs.1 hwb]
  simp only [] at h ⊢
  by_cases hab' : (a' == b') = true
  · rw [if_pos hab'] at h ⊢; exact h
  rw [if_neg hab'] at h ⊢
  cases hpi : Setlec.proofIrrel r₁ env d a' b' with
  | error err => rw [hpi] at h; exact nomatch h
  | ok cpi =>
  rw [hpi] at h; rw [proofIrrel_mono hs hpi]
  simp only [] at h ⊢
  cases cpi with
  | true => exact h
  | false =>
  simp only [Bool.false_eq_true, if_false] at h ⊢
  by_cases hg : (!a'.hasFvar && !b'.hasFvar) = true
  · rw [if_pos hg] at h ⊢
    cases hra : Setlec.reduceNat r₁ env d a' with
    | error err => rw [hra] at h; exact nomatch h
    | ok oa =>
    rw [hra] at h; rw [reduceNat_mono hs hra]
    simp only [] at h ⊢
    cases oa with
    | some a₂ => exact hk h
    | none =>
    rw [if_pos hg] at h ⊢
    cases hrb : Setlec.reduceNat r₁ env d b' with
    | error err => rw [hrb] at h; exact nomatch h
    | ok ob =>
    rw [hrb] at h; rw [reduceNat_mono hs hrb]
    simp only [] at h ⊢
    cases ob with
    | some b₂ => exact hk h
    | none =>
      cases hua : Setlec.unfoldableHead env a' <;>
        cases hub : Setlec.unfoldableHead env b' <;>
        rw [hua, hub] at h <;> simp only [] at h ⊢
      case true.false =>
        cases hud : Setlec.unfoldDefinition env a' with
        | some a₂ => rw [hud] at h; exact hk h
        | none => rw [hud] at h; exact h
      case false.true =>
        cases hud : Setlec.unfoldDefinition env b' with
        | some b₂ => rw [hud] at h; exact hk h
        | none => rw [hud] at h; exact h
      case true.true =>
        by_cases hlt1 : (Setlec.headHint env b').lt
            (Setlec.headHint env a') = true
        · rw [if_pos hlt1] at h ⊢
          cases hud : Setlec.unfoldDefinition env a' with
          | some a₂ => rw [hud] at h; exact hk h
          | none => rw [hud] at h; exact h
        rw [if_neg hlt1] at h ⊢
        by_cases hlt2 : (Setlec.headHint env a').lt
            (Setlec.headHint env b') = true
        · rw [if_pos hlt2] at h ⊢
          cases hud : Setlec.unfoldDefinition env b' with
          | some b₂ => rw [hud] at h; exact hk h
          | none => rw [hud] at h; exact h
        rw [if_neg hlt2] at h ⊢
        by_cases hsr : ((Setlec.headHint env a').sameRegular
            (Setlec.headHint env b') && Setlec.sameConstHeads a' b') = true
        · rw [if_pos hsr] at h ⊢
          cases hsp : Setlec.defeqSpine r₁ env d a' b' with
          | error err => rw [hsp] at h; exact nomatch h
          | ok csp =>
          rw [hsp] at h; rw [defeqSpine_mono hs hsp]
          simp only [] at h ⊢
          cases csp with
          | true => exact h
          | false =>
          simp only [Bool.false_eq_true, if_false] at h ⊢
          cases hud1 : Setlec.unfoldDefinition env a' with
          | none => rw [hud1] at h; cases hud2 : Setlec.unfoldDefinition env b' <;> rw [hud2] at h <;> exact h
          | some a₂ =>
          rw [hud1] at h
          cases hud2 : Setlec.unfoldDefinition env b' with
          | some b₂ => rw [hud2] at h; exact hk h
          | none => rw [hud2] at h; exact h
        · rw [if_neg hsr] at h ⊢
          cases hud1 : Setlec.unfoldDefinition env a' with
          | none => rw [hud1] at h; cases hud2 : Setlec.unfoldDefinition env b' <;> rw [hud2] at h <;> exact h
          | some a₂ =>
          rw [hud1] at h
          cases hud2 : Setlec.unfoldDefinition env b' with
          | some b₂ => rw [hud2] at h; exact hk h
          | none => rw [hud2] at h; exact h
      case false.false =>
        split at h
        · next u v' => exact h
        · next l₁ l₂ => exact h
        · next n c us =>
          by_cases hc : (c = Setlec.natZeroName ∧ us = [])
          · rw [if_pos hc] at h ⊢; exact h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next c us n =>
          by_cases hc : (c = Setlec.natZeroName ∧ us = [])
          · rw [if_pos hc] at h ⊢; exact h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next nn f x =>
          split at h
          · next m c =>
            by_cases hc : c = Setlec.natSuccName
            · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
            · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
          · next => exact stuckIrrel_mono hs h
        · next f x nn =>
          split at h
          · next m c =>
            by_cases hc : c = Setlec.natSuccName
            · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
            · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
          · next => exact stuckIrrel_mono hs h
        · next st cO usO x =>
          by_cases hc : (cO = Setlec.stringOfListName ∧ usO = [] ∧
              Setlec.strLitSupported env)
          · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next cO usO x st =>
          by_cases hc : (cO = Setlec.stringOfListName ∧ usO = [] ∧
              Setlec.strLitSupported env)
          · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next i n₁ ty₁ j n₂ ty₂ =>
          by_cases hij : (i == j) = true
          · rw [if_pos hij] at h ⊢; exact h
          · rw [if_neg hij] at h ⊢; exact stuckIrrel_mono hs h
        · next n us n' us' =>
          by_cases hn : n = n'
          · rw [if_pos hn] at h ⊢
            cases hle : Setlec.liftFueled "level comparison"
                (Level.isEquivList us us') (m := Setlec.CheckM) with
            | error err => rw [hle] at h; exact nomatch h
            | ok cle =>
            rw [hle] at h
            simp only [] at h ⊢
            cases cle with
            | true => exact h
            | false => exact stuckIrrel_mono hs h
          · rw [if_neg hn] at h ⊢; exact stuckIrrel_mono hs h
        · next n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ =>
          cases hd1 : r₁.defeq d ty₁ ty₂ with
          | error err => rw [hd1] at h; exact nomatch h
          | ok c₁ =>
          rw [hd1] at h; rw [hs.2.2.2.1 hd1]
          simp only [] at h ⊢
          cases c₁ with
          | false => exact h
          | true =>
            simp only [↓reduceIte] at h ⊢
            cases hd2 : r₁.defeq (d + 1)
                (body₁.instantiate1 (.fvar d n₁ ty₁))
                (body₂.instantiate1 (.fvar d n₂ ty₂)) with
            | error err => rw [hd2] at h; exact nomatch h
            | ok c₂ =>
            rw [hd2] at h
            rw [hs.2.2.2.1 hd2]
            dsimp only at h ⊢
            exact h
        · next n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ =>
          cases hd1 : r₁.defeq d ty₁ ty₂ with
          | error err => rw [hd1] at h; exact nomatch h
          | ok c₁ =>
          rw [hd1] at h; rw [hs.2.2.2.1 hd1]
          simp only [] at h ⊢
          cases c₁ with
          | false => exact h
          | true =>
            simp only [↓reduceIte] at h ⊢
            cases hd2 : r₁.defeq (d + 1)
                (body₁.instantiate1 (.fvar d n₁ ty₁))
                (body₂.instantiate1 (.fvar d n₂ ty₂)) with
            | error err => rw [hd2] at h; exact nomatch h
            | ok c₂ =>
            rw [hd2] at h
            rw [hs.2.2.2.1 hd2]
            dsimp only at h ⊢
            exact h
        · next f₁ a₁ f₂ a₂ =>
          by_cases hlen : (Expr.app f₁ a₁).getAppArgs.length =
              (Expr.app f₂ a₂).getAppArgs.length
          · rw [if_pos hlen] at h ⊢
            cases hdf : r₁.defeq d (Expr.app f₁ a₁).getAppFn
                (Expr.app f₂ a₂).getAppFn with
            | error err => rw [hdf] at h; exact nomatch h
            | ok cdf =>
            rw [hdf] at h; rw [hs.2.2.2.1 hdf]
            simp only [] at h ⊢
            cases cdf with
            | false =>
              simp only [Bool.false_eq_true, if_false] at h ⊢
              exact stuckIrrel_mono hs h
            | true =>
            simp only [if_true] at h ⊢
            cases hdl : Setlec.defEqList r₁ env d
                (Expr.app f₁ a₁).getAppArgs
                (Expr.app f₂ a₂).getAppArgs with
            | error err => rw [hdl] at h; exact nomatch h
            | ok cdl =>
            rw [hdl] at h; rw [defEqList_mono hs hdl]
            simp only [] at h ⊢
            cases cdl with
            | true => exact h
            | false => exact stuckIrrel_mono hs h
          · rw [if_neg hlen] at h ⊢; exact stuckIrrel_mono hs h
        · next s₁ i₁ e₁ s₂ i₂ e₂ =>
          by_cases hij : (i₁ == i₂) = true
          · rw [if_pos hij] at h ⊢
            cases hd1 : r₁.defeq d e₁ e₂ with
            | error err => rw [hd1] at h; exact nomatch h
            | ok c₁ =>
            rw [hd1] at h; rw [hs.2.2.2.1 hd1]
            simp only [] at h ⊢
            cases c₁ with
            | true => exact h
            | false => exact stuckIrrel_mono hs h
          · rw [if_neg hij] at h ⊢; exact stuckIrrel_mono hs h
        · next =>
          split at h
          · exact nomatch h
          · next ce he =>
            rw [etaCert_mono hs he]
            cases ce with
            | true => exact h
            | false => exact stuckIrrel_mono hs h
        · next =>
          split at h
          · exact nomatch h
          · next ce he =>
            rw [etaCert_mono hs he]
            cases ce with
            | true => exact h
            | false => exact stuckIrrel_mono hs h
        · next => exact stuckIrrel_mono hs h
  · rw [if_neg hg] at h ⊢
    rw [if_neg hg] at h ⊢
    simp only [pure, Except.pure] at h ⊢
    cases hua : Setlec.unfoldableHead env a' <;>
      cases hub : Setlec.unfoldableHead env b' <;>
      rw [hua, hub] at h <;> simp only [] at h ⊢
    case true.false =>
      cases hud : Setlec.unfoldDefinition env a' with
      | some a₂ => rw [hud] at h; exact hk h
      | none => rw [hud] at h; exact h
    case false.true =>
      cases hud : Setlec.unfoldDefinition env b' with
      | some b₂ => rw [hud] at h; exact hk h
      | none => rw [hud] at h; exact h
    case true.true =>
      by_cases hlt1 : (Setlec.headHint env b').lt
          (Setlec.headHint env a') = true
      · rw [if_pos hlt1] at h ⊢
        cases hud : Setlec.unfoldDefinition env a' with
        | some a₂ => rw [hud] at h; exact hk h
        | none => rw [hud] at h; exact h
      rw [if_neg hlt1] at h ⊢
      by_cases hlt2 : (Setlec.headHint env a').lt
          (Setlec.headHint env b') = true
      · rw [if_pos hlt2] at h ⊢
        cases hud : Setlec.unfoldDefinition env b' with
        | some b₂ => rw [hud] at h; exact hk h
        | none => rw [hud] at h; exact h
      rw [if_neg hlt2] at h ⊢
      by_cases hsr : ((Setlec.headHint env a').sameRegular
          (Setlec.headHint env b') && Setlec.sameConstHeads a' b') = true
      · rw [if_pos hsr] at h ⊢
        cases hsp : Setlec.defeqSpine r₁ env d a' b' with
        | error err => rw [hsp] at h; exact nomatch h
        | ok csp =>
        rw [hsp] at h; rw [defeqSpine_mono hs hsp]
        simp only [] at h ⊢
        cases csp with
        | true => exact h
        | false =>
        simp only [Bool.false_eq_true, if_false] at h ⊢
        cases hud1 : Setlec.unfoldDefinition env a' with
        | none => rw [hud1] at h; cases hud2 : Setlec.unfoldDefinition env b' <;> rw [hud2] at h <;> exact h
        | some a₂ =>
        rw [hud1] at h
        cases hud2 : Setlec.unfoldDefinition env b' with
        | some b₂ => rw [hud2] at h; exact hk h
        | none => rw [hud2] at h; exact h
      · rw [if_neg hsr] at h ⊢
        cases hud1 : Setlec.unfoldDefinition env a' with
        | none => rw [hud1] at h; cases hud2 : Setlec.unfoldDefinition env b' <;> rw [hud2] at h <;> exact h
        | some a₂ =>
        rw [hud1] at h
        cases hud2 : Setlec.unfoldDefinition env b' with
        | some b₂ => rw [hud2] at h; exact hk h
        | none => rw [hud2] at h; exact h
    case false.false =>
      split at h
      · next u v' => exact h
      · next l₁ l₂ => exact h
      · next n c us =>
        by_cases hc : (c = Setlec.natZeroName ∧ us = [])
        · rw [if_pos hc] at h ⊢; exact h
        · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
      · next c us n =>
        by_cases hc : (c = Setlec.natZeroName ∧ us = [])
        · rw [if_pos hc] at h ⊢; exact h
        · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
      · next nn f x =>
        split at h
        · next m c =>
          by_cases hc : c = Setlec.natSuccName
          · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next => exact stuckIrrel_mono hs h
      · next f x nn =>
        split at h
        · next m c =>
          by_cases hc : c = Setlec.natSuccName
          · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next => exact stuckIrrel_mono hs h
      · next st cO usO x =>
        by_cases hc : (cO = Setlec.stringOfListName ∧ usO = [] ∧
            Setlec.strLitSupported env)
        · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
        · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
      · next cO usO x st =>
        by_cases hc : (cO = Setlec.stringOfListName ∧ usO = [] ∧
            Setlec.strLitSupported env)
        · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
        · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
      · next i n₁ ty₁ j n₂ ty₂ =>
        by_cases hij : (i == j) = true
        · rw [if_pos hij] at h ⊢; exact h
        · rw [if_neg hij] at h ⊢; exact stuckIrrel_mono hs h
      · next n us n' us' =>
        by_cases hn : n = n'
        · rw [if_pos hn] at h ⊢
          cases hle : Setlec.liftFueled "level comparison"
              (Level.isEquivList us us') (m := Setlec.CheckM) with
          | error err => rw [hle] at h; exact nomatch h
          | ok cle =>
          rw [hle] at h
          simp only [] at h ⊢
          cases cle with
          | true => exact h
          | false => exact stuckIrrel_mono hs h
        · rw [if_neg hn] at h ⊢; exact stuckIrrel_mono hs h
      · next n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ =>
        cases hd1 : r₁.defeq d ty₁ ty₂ with
        | error err => rw [hd1] at h; exact nomatch h
        | ok c₁ =>
        rw [hd1] at h; rw [hs.2.2.2.1 hd1]
        simp only [] at h ⊢
        cases c₁ with
        | false => exact h
        | true =>
          simp only [↓reduceIte] at h ⊢
          cases hd2 : r₁.defeq (d + 1)
              (body₁.instantiate1 (.fvar d n₁ ty₁))
              (body₂.instantiate1 (.fvar d n₂ ty₂)) with
          | error err => rw [hd2] at h; exact nomatch h
          | ok c₂ =>
          rw [hd2] at h
          rw [hs.2.2.2.1 hd2]
          dsimp only at h ⊢
          exact h
      · next n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ =>
        cases hd1 : r₁.defeq d ty₁ ty₂ with
        | error err => rw [hd1] at h; exact nomatch h
        | ok c₁ =>
        rw [hd1] at h; rw [hs.2.2.2.1 hd1]
        simp only [] at h ⊢
        cases c₁ with
        | false => exact h
        | true =>
          simp only [↓reduceIte] at h ⊢
          cases hd2 : r₁.defeq (d + 1)
              (body₁.instantiate1 (.fvar d n₁ ty₁))
              (body₂.instantiate1 (.fvar d n₂ ty₂)) with
          | error err => rw [hd2] at h; exact nomatch h
          | ok c₂ =>
          rw [hd2] at h
          rw [hs.2.2.2.1 hd2]
          dsimp only at h ⊢
          exact h
      · next f₁ a₁ f₂ a₂ =>
        by_cases hlen : (Expr.app f₁ a₁).getAppArgs.length =
            (Expr.app f₂ a₂).getAppArgs.length
        · rw [if_pos hlen] at h ⊢
          cases hdf : r₁.defeq d (Expr.app f₁ a₁).getAppFn
              (Expr.app f₂ a₂).getAppFn with
          | error err => rw [hdf] at h; exact nomatch h
          | ok cdf =>
          rw [hdf] at h; rw [hs.2.2.2.1 hdf]
          simp only [] at h ⊢
          cases cdf with
          | false =>
            simp only [Bool.false_eq_true, if_false] at h ⊢
            exact stuckIrrel_mono hs h
          | true =>
          simp only [if_true] at h ⊢
          cases hdl : Setlec.defEqList r₁ env d
              (Expr.app f₁ a₁).getAppArgs
              (Expr.app f₂ a₂).getAppArgs with
          | error err => rw [hdl] at h; exact nomatch h
          | ok cdl =>
          rw [hdl] at h; rw [defEqList_mono hs hdl]
          simp only [] at h ⊢
          cases cdl with
          | true => exact h
          | false => exact stuckIrrel_mono hs h
        · rw [if_neg hlen] at h ⊢; exact stuckIrrel_mono hs h
      · next s₁ i₁ e₁ s₂ i₂ e₂ =>
        by_cases hij : (i₁ == i₂) = true
        · rw [if_pos hij] at h ⊢
          cases hd1 : r₁.defeq d e₁ e₂ with
          | error err => rw [hd1] at h; exact nomatch h
          | ok c₁ =>
          rw [hd1] at h; rw [hs.2.2.2.1 hd1]
          simp only [] at h ⊢
          cases c₁ with
          | true => exact h
          | false => exact stuckIrrel_mono hs h
        · rw [if_neg hij] at h ⊢; exact stuckIrrel_mono hs h
      · next =>
        split at h
        · exact nomatch h
        · next ce he =>
          rw [etaCert_mono hs he]
          cases ce with
          | true => exact h
          | false => exact stuckIrrel_mono hs h
      · next =>
        split at h
        · exact nomatch h
        · next ce he =>
          rw [etaCert_mono hs he]
          cases ce with
          | true => exact h
          | false => exact stuckIrrel_mono hs h
      · next => exact stuckIrrel_mono hs h

/-- `defeqLoop` respects the order at every budget. -/
theorem defeqLoop_mono {μ : CheckMode} (hs : CoreSub r₁ r₂) {d : Nat} :
    ∀ {l : Nat} {a b : Expr} {v : Bool},
      Setlec.defeqLoop μ r₁ env d l a b = .ok v →
      Setlec.defeqLoop μ r₂ env d l a b = .ok v := by
  intro l
  induction l with
  | zero => intro a b v h; exact nomatch h
  | succ l ih =>
    intro a b v h
    rw [defeqLoop_succ] at h
    rw [defeqLoop_succ]
    exact defeqStep_mono hs (fun hk => ih hk) h

end MonoHelpers2

/-! ## The knot chain and the public projection -/

/-- The io-grade view respects the order: the view only permutes
fields. -/
theorem CoreSub.ioView {r₁ r₂ : Setlec.CoreFns Setlec.CheckM}
    (h : CoreSub r₁ r₂) : CoreSub r₁.ioView r₂.ioView :=
  ⟨h.1, h.2.1, h.2.2.2.2.2, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `inferBodyIO` respects the order (the io body reads `whnf`,
`infer` and `defeq` only). -/
theorem inferBodyIO_mono' {μ : CheckMode} {env : Env}
    {r₁ r₂ : Setlec.CoreFns Setlec.CheckM} (hs : CoreSub r₁ r₂)
    {d : Nat} {e x : Expr}
    (h : Setlec.inferBodyIO μ r₁ env d e = .ok x) :
    Setlec.inferBodyIO μ r₂ env d e = .ok x := by
  unfold Setlec.inferBodyIO at h ⊢
  cases e with
  | sort u => exact h
  | bvar i => exact h
  | fvar idx n ty => exact h
  | const n us => exact h
  | lit l => cases l <;> exact h
  | forallE n ty body mb =>
    simp only [Setlec.viewM, Expr.view, pure, Except.pure, Bind.bind,
      Except.bind] at h ⊢
    try dsimp only at h ⊢
    cases h1 : r₁.infer d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok tty =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tty with
    | error err => rw [h2] at h; exact nomatch h
    | ok w =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    cases w <;> try exact h
    case sort u =>
    cases h3 : r₁.infer (d + 1) (body.instantiate1 (.fvar d n ty)) with
    | error err => rw [h3] at h; exact nomatch h
    | ok bt =>
    rw [h3] at h; rw [hs.2.2.1 h3]
    simp only [] at h ⊢
    unfold Setlec.ensureSort at h ⊢
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h4 : r₁.whnf (d + 1) bt with
    | error err => rw [h4] at h; exact nomatch h
    | ok w' =>
    rw [h4] at h; rw [hs.2.1 h4]
    exact h
  | lam n ty body mb =>
    simp only [Setlec.viewM, Expr.view, pure, Except.pure, Bind.bind,
      Except.bind] at h ⊢
    try dsimp only at h ⊢
    cases h1 : r₁.infer d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok tty =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tty with
    | error err => rw [h2] at h; exact nomatch h
    | ok w =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    cases w <;> try exact h
    case sort u =>
    cases h3 : r₁.infer (d + 1) (body.instantiate1 (.fvar d n ty)) with
    | error err => rw [h3] at h; exact nomatch h
    | ok bt =>
    rw [h3] at h; rw [hs.2.2.1 h3]
    simp only [] at h ⊢
    by_cases hv : μ.verified = true
    case neg =>
      rw [if_neg hv] at h ⊢
      exact h
    rw [if_pos hv] at h ⊢
    cases hbp : body.lamPw with
    | some pwI =>
      simp only [hbp] at h ⊢
      exact h
    | none =>
      simp only [hbp] at h ⊢
      cases h4 : r₁.infer (d + 1) bt with
        | error err => rw [h4] at h; exact nomatch h
        | ok btt =>
        rw [h4] at h; rw [hs.2.2.1 h4]
        simp only [] at h ⊢
        unfold Setlec.ensureSort at h ⊢
        simp only [Bind.bind, Except.bind] at h ⊢
        cases h5 : r₁.whnf (d + 1) btt with
        | error err => rw [h5] at h; exact nomatch h
        | ok w' =>
        rw [h5] at h; rw [hs.2.1 h5]
        exact h
  | app f a =>
    simp only [Setlec.viewM, Expr.view, pure, Except.pure, Bind.bind,
      Except.bind] at h ⊢
    try dsimp only at h ⊢
    cases h1 : r₁.infer d f with
    | error err => rw [h1] at h; exact nomatch h
    | ok tf =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tf with
    | error err => rw [h2] at h; exact nomatch h
    | ok w =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    cases w <;> try exact h
    case forallE n' ty' body' mt =>
    by_cases hg2 : (μ.verified && mt.pw.isNever) = true
    · simp only [hg2, ↓reduceIte] at h ⊢
      exact h
    · simp only [hg2, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases h3 : r₁.infer d a with
      | error err => rw [h3] at h; exact nomatch h
      | ok ta =>
      rw [h3] at h; rw [hs.2.2.1 h3]
      simp only [] at h ⊢
      cases h4 : r₁.defeq d ta ty' with
      | error err => rw [h4] at h; exact nomatch h
      | ok c =>
      rw [h4] at h; rw [hs.2.2.2.1 h4]
      exact h
  | letE n ty v b =>
    simp only [Setlec.viewM, Expr.view, pure, Except.pure, Bind.bind,
      Except.bind] at h ⊢
    try dsimp only at h ⊢
    cases h1 : r₁.infer d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok tty =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    unfold Setlec.ensureSort at h ⊢
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h2 : r₁.whnf d tty with
    | error err => rw [h2] at h; exact nomatch h
    | ok w =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    cases w with
    | bvar i => exact nomatch h
    | fvar idx nm t => exact nomatch h
    | const nm us => exact nomatch h
    | app f' a' => exact nomatch h
    | lam nm t b' m' => exact nomatch h
    | forallE nm t b' m' => exact nomatch h
    | letE nm t v' b' => exact nomatch h
    | lit l => exact nomatch h
    | proj s' i' e' => exact nomatch h
    | sort u =>
    simp only [] at h ⊢
    cases h3 : r₁.infer d v with
    | error err => rw [h3] at h; exact nomatch h
    | ok tv =>
    rw [h3] at h; rw [hs.2.2.1 h3]
    simp only [] at h ⊢
    cases h4 : r₁.defeq d tv ty with
    | error err => rw [h4] at h; exact nomatch h
    | ok c =>
    rw [h4] at h; rw [hs.2.2.2.1 h4]
    simp only [] at h ⊢
    cases c with
    | false => exact h
    | true =>
      simp only [] at h ⊢
      exact hs.2.2.1 h
  | proj sn i pe =>
    simp only [Setlec.viewM, Expr.view, pure, Except.pure, Bind.bind,
      Except.bind] at h ⊢
    try dsimp only at h ⊢
    cases h1 : r₁.infer d pe with
    | error err => rw [h1] at h; exact nomatch h
    | ok tpe =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tpe with
    | error err => rw [h2] at h; exact nomatch h
    | ok te =>
    rw [h2] at h; rw [hs.2.1 h2]
    exact h

/-- `CoreSub` is transitive. -/
theorem CoreSub.trans {r₁ r₂ r₃ : Setlec.CoreFns Setlec.CheckM}
    (h₁ : CoreSub r₁ r₂) (h₂ : CoreSub r₂ r₃) : CoreSub r₁ r₃ :=
  ⟨fun h => h₂.1 (h₁.1 h),
   fun h => h₂.2.1 (h₁.2.1 h),
   fun h => h₂.2.2.1 (h₁.2.2.1 h),
   fun h => h₂.2.2.2.1 (h₁.2.2.2.1 h),
   fun h => h₂.2.2.2.2.1 (h₁.2.2.2.2.1 h),
   fun h => h₂.2.2.2.2.2 (h₁.2.2.2.2.2 h)⟩

/-- One knot level: the oracle at fuel `f` extends into fuel `f+1`. -/
theorem coreSub_succ (μ : CheckMode) (env : Env) :
    ∀ f : Nat, CoreSub (Setlec.pureFns μ env f)
      (Setlec.pureFns μ env (f + 1)) := by
  intro f
  induction f with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d e x h; exact nomatch h
    · intro d e x h; exact nomatch h
    · intro d e x h; exact nomatch h
    · intro d a b v h; exact nomatch h
    · intro d e x h; exact nomatch h
    · intro d e x h; exact nomatch h
  | succ f ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d e x h
      exact whnfCoreBody_mono ih h
    · intro d e x h
      exact whnfLoop_mono ih h
    · intro d e x h
      exact inferBody_mono ih h
    · intro d a b v h
      exact defeqLoop_mono ih h
    · intro d e x h
      exact annotateBody_mono ih h
    · -- the io slot (task #172 B4): fuel monotonicity of the named
      -- slot family (`Verify/Mono.lean`), read at the knot level
      intro d e x h
      exact Setlec.inferTypeIO_mono (Nat.le_succ _)
        (show Setlec.inferTypeIO μ env (f + 1) d e = .ok x from h)

/-- The chain: fuel-gap induction. -/
theorem coreSub_le (μ : CheckMode) (env : Env) :
    ∀ {f f' : Nat}, f ≤ f' →
      CoreSub (Setlec.pureFns μ env f) (Setlec.pureFns μ env f') := by
  intro f f' hle
  induction f' with
  | zero =>
    obtain rfl : f = 0 := Nat.le_zero.mp hle
    exact ⟨fun h => h, fun h => h, fun h => h, fun h => h, fun h => h,
      fun h => h⟩
  | succ f' ih =>
    rcases Nat.lt_or_ge f (f' + 1) with hlt | hge
    · exact CoreSub.trans (ih (Nat.lt_succ_iff.mp hlt))
        (coreSub_succ μ env f')
    · obtain rfl : f = f' + 1 := Nat.le_antisymm hle hge
      exact ⟨fun h => h, fun h => h, fun h => h, fun h => h, fun h => h,
        fun h => h⟩

/-- **`KnotFuelMono` LANDS**: the carried obligation is a theorem.
Every lemma that hypothesized it — the dual shell
(`ensureSortAgreeR_of`), the run-threaded re-idem
(`whnfCore_reidem_const`), the loop algebra (`whnfLoop_r_mono`,
`whnfLoop_det`, `loop_stuck_out`, `loop_align`), the cross-fuel sort
determinism (`sortOfE_fuelDet` via `KnotFuelDet_of_mono`) — now
closes with this theorem in the slot. -/
theorem knotFuelMono (μ : CheckMode) (env : Env) : KnotFuelMono μ env := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f f' d e t hle h
    exact (coreSub_le μ env hle).2.2.1 h
  · intro f f' d e t hle h
    exact (coreSub_le μ env hle).2.1 h
  · intro f f' d e t hle h
    exact (coreSub_le μ env hle).1 h
  · intro f f' d a b v hle h
    exact (coreSub_le μ env hle).2.2.2.1 h
  · intro f f' d e o hle h
    exact reduceNat_mono (coreSub_le μ env hle) h

/-- The determinism corollary, now unconditional. -/
theorem knotFuelDet (μ : CheckMode) (env : Env) : KnotFuelDet μ env :=
  KnotFuelDet_of_mono (knotFuelMono μ env)

/-- **The payoff**: the dual shell conditioned on the five routings
alone — the wide obligation's slot is filled by the theorem.  (The
same instantiation closes `whnfCore_reidem_const`, `whnfLoop_r_mono`,
`whnfLoop_det`, `loop_stuck_out`, `loop_align`, `whnf_sort_out`,
`sortOfE_sort_out`, `sortOfE_fuelDet`, `unitBranch_absurd`,
`SortOfLE_det`, and `EnsureSortAgreeR_of_link` at their `hm`/`hdet`
slots.) -/
theorem ensureSortAgreeR_of_vacuities {μ : CheckMode} {env : Env}
    {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeSortVacuity μ env Q) (hR : RescueSortVacuity μ env Q)
    (hE : EtaSortVacuity μ env Q) (hN : NatStepNoSort μ env)
    (hS : SpineSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q :=
  ensureSortAgreeRQ_of (Q := Q) (knotFuelMono μ env) hIC hID hIN
    hLC hLD hLN hQC hQD hQN hQs hP hR hE hN hS

/-! ## The nat-chase discharge -/

/-- The env-side fact the chase needs (ledger; install-tier supplier):
the comparison ops' output constants are delta-inert. -/
def BoolCtorsInert (env : Env) : Prop :=
  Setlec.unfoldDefinition env (.const Setlec.boolTrueName []) = none ∧
  Setlec.unfoldDefinition env (.const Setlec.boolFalseName []) = none

/-- Literals re-core to themselves (value branch). -/
theorem whnfCore_lit_run {μ : CheckMode} {env : Env} {f d : Nat}
    {l : Setlec.Literal} (hf : 1 ≤ f) :
    whnfCore μ env f d (.lit l) = .ok (.lit l) := by
  cases f with
  | zero => exact nomatch hf
  | succ f => rw [Setlec.whnfCore_succ]; rfl

/-- Constants re-core to themselves (value branch). -/
theorem whnfCore_const_run {μ : CheckMode} {env : Env} {f d : Nat}
    {n : Name} {us : List Level} (hf : 1 ≤ f) :
    whnfCore μ env f d (.const n us) = .ok (.const n us) := by
  cases f with
  | zero => exact nomatch hf
  | succ f => rw [Setlec.whnfCore_succ]; rfl

/-- `natOpResult` outputs are literals or the two `Bool` constants. -/
theorem natOpResult_shape {c : Name} {a b : Nat} {e : Expr}
    (h : Setlec.natOpResult c a b = some e) :
    (∃ n, e = .lit (.natVal n)) ∨
      e = .const Setlec.boolTrueName [] ∨
      e = .const Setlec.boolFalseName [] := by
  rw [Setlec.natOpResult.eq_def] at h
  by_cases h1 : c = Setlec.natPredName
  · rw [if_pos h1] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h1] at h
  by_cases h2 : c = Setlec.natAddName
  · rw [if_pos h2] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h2] at h
  by_cases h3 : c = Setlec.natSubName
  · rw [if_pos h3] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h3] at h
  by_cases h4 : c = Setlec.natMulName
  · rw [if_pos h4] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h4] at h
  by_cases h5 : c = Setlec.natPowName
  · rw [if_pos h5] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h5] at h
  by_cases h6 : c = Setlec.natDivName
  · rw [if_pos h6] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h6] at h
  by_cases h7 : c = Setlec.natModName
  · rw [if_pos h7] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h7] at h
  by_cases h8 : c = Setlec.natGcdName
  · rw [if_pos h8] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h8] at h
  by_cases h9 : c = Setlec.natLandName
  · rw [if_pos h9] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h9] at h
  by_cases h10 : c = Setlec.natLorName
  · rw [if_pos h10] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h10] at h
  by_cases h11 : c = Setlec.natXorName
  · rw [if_pos h11] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h11] at h
  by_cases h12 : c = Setlec.natShiftLeftName
  · rw [if_pos h12] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h12] at h
  by_cases h13 : c = Setlec.natShiftRightName
  · rw [if_pos h13] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h13] at h
  by_cases h14 : c = Setlec.natLog2Name
  · rw [if_pos h14] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h14] at h
  by_cases hbeq : c = Setlec.natBeqName
  · rw [if_pos hbeq] at h
    by_cases hab : a = b
    · rw [if_pos hab] at h
      exact .inr (.inl (Option.some.inj h).symm)
    · rw [if_neg hab] at h
      exact .inr (.inr (Option.some.inj h).symm)
  rw [if_neg hbeq] at h
  by_cases hble : c = Setlec.natBleName
  · rw [if_pos hble] at h
    by_cases hab : a ≤ b
    · rw [if_pos hab] at h
      exact .inr (.inl (Option.some.inj h).symm)
    · rw [if_neg hab] at h
      exact .inr (.inr (Option.some.inj h).symm)
  rw [if_neg hble] at h
  exact nomatch h

/-- `reduceNat`'s rewrites are literals or the two `Bool`
constants. -/
theorem reduceNat_some_shape {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} {e x : Expr}
    (h : Setlec.reduceNat r env d e = .ok (some x)) :
    (∃ n, x = .lit (.natVal n)) ∨
      x = .const Setlec.boolTrueName [] ∨
      x = .const Setlec.boolFalseName [] := by
  unfold Setlec.reduceNat at h
  split at h
  · next c a =>
    by_cases h1 : c = Setlec.natSuccName ∧ Setlec.natLitSupported env
    · rw [if_pos h1] at h
      simp only [Bind.bind, Except.bind] at h
      cases hw : r.whnf d a with
      | error err => rw [hw] at h; exact nomatch h
      | ok w =>
        rw [hw] at h
        simp only [] at h
        split at h
        · next n heq =>
          obtain rfl := (Option.some.inj (Except.ok.inj h)).symm
          exact .inl ⟨_, rfl⟩
        · exact nomatch h
    · rw [if_neg h1] at h
      by_cases h2 : c = Setlec.natPredName ∧
          Setlec.natOpStored env c = true
      · rw [if_pos h2] at h
        simp only [Bind.bind, Except.bind] at h
        cases hw : r.whnf d a with
        | error err => rw [hw] at h; exact nomatch h
        | ok w =>
          rw [hw] at h
          simp only [] at h
          split at h
          · next n heq => exact natOpResult_shape (Except.ok.inj h)
          · exact nomatch h
      · rw [if_neg h2] at h
        by_cases h3 : c = Setlec.natLog2Name ∧
            Setlec.natOpStored env c = true
        · rw [if_pos h3] at h
          simp only [Bind.bind, Except.bind] at h
          cases hw : r.whnf d a with
          | error err => rw [hw] at h; exact nomatch h
          | ok w =>
            rw [hw] at h
            simp only [] at h
            split at h
            · next n heq => exact natOpResult_shape (Except.ok.inj h)
            · exact nomatch h
        · rw [if_neg h3] at h
          by_cases h4 : c = Setlec.natLog2Name ∧
              Setlec.natLitSupported env
          · rw [if_pos h4] at h
            simp only [Bind.bind, Except.bind] at h
            cases hw : r.whnf d a with
            | error err => rw [hw] at h; exact nomatch h
            | ok w =>
              rw [hw] at h
              simp only [] at h
              split at h
              · next n heq => exact nomatch h
              · exact nomatch h
          · rw [if_neg h4] at h
            exact nomatch h
  · next c a b =>
    by_cases h1 : (c = Setlec.natAddName ∨ c = Setlec.natSubName ∨
        c = Setlec.natMulName ∨ c = Setlec.natPowName ∨
        c = Setlec.natBeqName ∨ c = Setlec.natBleName ∨
        c = Setlec.natDivName ∨ c = Setlec.natModName ∨
        c = Setlec.natGcdName ∨ c = Setlec.natLandName ∨
        c = Setlec.natLorName ∨ c = Setlec.natXorName ∨
        c = Setlec.natShiftLeftName ∨ c = Setlec.natShiftRightName) ∧
        Setlec.natOpStored env c = true
    · rw [if_pos h1] at h
      simp only [Bind.bind, Except.bind] at h
      cases hwa : r.whnf d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok wa =>
        rw [hwa] at h
        simp only [] at h
        cases hwb : r.whnf d b with
        | error err => rw [hwb] at h; exact nomatch h
        | ok wb =>
          rw [hwb] at h
          simp only [] at h
          split at h
          · next n₁ n₂ heq₁ heq₂ =>
            exact natOpResult_shape (Except.ok.inj h)
          all_goals exact nomatch h
    · rw [if_neg h1] at h
      by_cases h2 : Setlec.natOpWfNames.contains c ∧
          Setlec.natLitSupported env
      · rw [if_pos h2] at h
        simp only [Bind.bind, Except.bind] at h
        cases hwa : r.whnf d a with
        | error err => rw [hwa] at h; exact nomatch h
        | ok wa =>
          rw [hwa] at h
          simp only [] at h
          cases hwb : r.whnf d b with
          | error err => rw [hwb] at h; exact nomatch h
          | ok wb =>
            rw [hwb] at h
            simp only [] at h
            split at h
            all_goals exact nomatch h
      · rw [if_neg h2] at h
        exact nomatch h
  · exact nomatch h

/-- **The `NatStepNoSort` discharge** (with the env fact
hypothesized): the nat step's target is a literal or `Bool` constant,
all of which are whnf-inert — colliding with the given
literal-sort convergence. -/
theorem natStepNoSort_of {μ : CheckMode} {env : Env}
    (hB : BoolCtorsInert env) : NatStepNoSort μ env := by
  intro g g' l f d e e' x ℓ hwc hrn hrun
  have hdet := knotFuelDet μ env
  have hm := knotFuelMono μ env
  cases l with
  | zero => exact nomatch hrun
  | succ l =>
  rw [whnfLoop_succ] at hrun
  obtain ⟨e₁, hwc', htri⟩ := whnfStep_decompose hrun
  obtain rfl : e' = e₁ :=
    (hdet.2.2.1 (hwc' : whnfCore μ env g' d e = .ok e₁) hwc).symm
  rcases htri with ⟨y, hry, hk⟩ | ⟨hry, y, huy, hk⟩ | ⟨hry, huy, hstop⟩
  · have h1 := hm.2.2.2.2 (Nat.le_max_left g' g) hry
    have h2 := hm.2.2.2.2 (Nat.le_max_right g' g) hrn
    rw [h1] at h2
    obtain rfl : y = x := Option.some.inj (Except.ok.inj h2)
    rcases reduceNat_some_shape hry with ⟨n, rfl⟩ | rfl | rfl
    · exact nomatch (loop_stuck_out hm hk
        (whnfCore_lit_run (Nat.le_refl 1))
        (fun _ => reduceNat_lit) unfoldDefinition_lit)
    · exact nomatch (loop_stuck_out hm hk
        (whnfCore_const_run (Nat.le_refl 1))
        (fun _ => reduceNat_const) hB.1)
    · exact nomatch (loop_stuck_out hm hk
        (whnfCore_const_run (Nat.le_refl 1))
        (fun _ => reduceNat_const) hB.2)
  · have h1 := hm.2.2.2.2 (Nat.le_max_left g' g) hry
    have h2 := hm.2.2.2.2 (Nat.le_max_right g' g) hrn
    rw [h1] at h2; exact nomatch h2
  · have h1 := hm.2.2.2.2 (Nat.le_max_left g' g) hry
    have h2 := hm.2.2.2.2 (Nat.le_max_right g' g) hrn
    rw [h1] at h2; exact nomatch h2

/-- The shell, nat routing discharged: conditioned on the three PSS
routings, the spine unknown, the env fact, and the `InvPreserve*F`
supply chain (obligations with named suppliers — their own discharge
seals). -/
theorem ensureSortAgreeR_of_pss {μ : CheckMode} {env : Env}
    {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeSortVacuity μ env Q) (hR : RescueSortVacuity μ env Q)
    (hE : EtaSortVacuity μ env Q) (hS : SpineSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q :=
  ensureSortAgreeR_of_vacuities (Q := Q) hIC hID hIN hLC hLD hLN
    hQC hQD hQN hQs hP hR hE (natStepNoSort_of hB) hS

end Setlec.SetR.Interp2
