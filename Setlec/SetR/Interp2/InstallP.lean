import Setlec.SetR.Interp2.Step2.TiersP
import Setlec.SetR.Interp2.Keys2Cond
import Setlec.SetR.Annot.BitExtend

/-!
# The P declaration step (task #161, P4 — the fold's species)

`declStepPM_of_cons`: extending `EnvS2PM` by one fresh constant, in
the shape the declaration fold consumes — `declStep2M_of_cons`
(`Step2Cons.lean`) transposed to the P invariant.  The systematic
deltas:

* the new leaf `A` is the value's **`denoteP` reading** (bit
  numerals), and the denote2-currency uniqueness premises
  (`hdefnA`/`hthmA`) become the **existence** premise `hvalReads` —
  the P carrier stores no denote2 field, which is the `EnvS2Core`
  finding made structural;
* the crossing premise is not routed: `denoteP_envExtend` is a
  theorem, so the old constants' facts transfer from
  `findPreserved_cons` + a literal-guard agreement — where the
  canonical step routes `Denote2EnvExtend` per mode;
* the new constant's own facts (`htyReads`/`htyOk`/`hmemNew` and the
  leaf laws) are the **front-door harvest**: at the fold they come
  from `checkSoundAtP` at the prefix environment applied to the
  declaration's checked runs.

`nat_heads` at the extension is taken as a premise
(`declStepPM_natHeads_fresh` discharges it whenever the new constant
is not a literal pin; the pin installs supply it bespoke).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-- A fresh cons preserves every stored lookup. -/
theorem findPreserved_cons {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) :
    FindPreserved env ⟨c₀ :: env.consts⟩ := by
  intro n ci hf
  have hne : (c₀.name == n) = false := by
    by_cases h : c₀.name = n
    · subst h
      rw [hfresh] at hf
      exact nomatch hf
    · simpa using h
  show List.find? _ (c₀ :: env.consts) = some ci
  rw [List.find?_cons_of_neg (by simpa using hne)]
  exact hf

/-- The bit-validity combinator for a fresh leaf (`acvalWith_ok2`'s
`AnnotValidV` twin). -/
theorem acvalWith_validV {acval : Name → (Name → Nat) → AVExpr}
    {n : Name} {A : (Name → Nat) → AVExpr}
    (h : ∀ (m : Name) (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValidV V ρ (acval m ψ))
    (hA : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValidV V ρ (A ψ)) :
    ∀ (m : Name) (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValidV V ρ (acvalWith acval n A m ψ) := by
  intro m ψ ρ
  by_cases hm : m = n
  · subst hm; rw [acvalWith_self]; exact hA ψ ρ
  · rw [acvalWith_ne hm]; exact h m ψ ρ

/-- **The P declaration step, cons shape** (see the module
docstring). -/
theorem declStepPM_of_cons (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hbase : EnvS V ⟨c₀ :: env.consts⟩)
    (hag : ∀ n, n ≠ c₀.name → mp.base2.base.cval n = hbase.cval n)
    (hlga : LitGuardsAgree env ⟨c₀ :: env.consts⟩)
    (hAerase : ∀ ψ, (A ψ).erase = hbase.cval c₀.name ψ)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValidV V ρ (A ψ))
    (htyReads : ∀ ψ : Name → Nat,
      ∃ ta : AVExpr,
        denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta)
    (htyOk : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, AnnotOkP V ρ ta)
    (hmemNew : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, interp2 V ρ (A ψ) ∈ˢ interp2 V ρ ta)
    (hvalReads : ∀ (ψ : Name → Nat) (cv : ConstantVal)
      (value : Expr),
      ((∃ hint : ReducibilityHint,
          ConstantInfo.defnInfo cv value hint = c₀) ∨
        ConstantInfo.thmInfo cv value = c₀) →
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 value = some (A ψ))
    (hnh : ∀ φ : Name → Nat,
      NatHeadsP (V := V)
        ⟨hbase, acvalWith mp.base2.acval c₀.name A,
         by intro n ψ
            by_cases hn : n = c₀.name
            · subst hn; rw [acvalWith_self]; exact hAerase ψ
            · rw [acvalWith_ne hn, mp.base2.acval_erase, hag n hn],
         acvalWith_closed mp.base2.acval_closed hAclosed,
         acvalWith_params mp.base2.acval_params hAparams,
         acvalWith_ok2 mp.base2.acval_ok2 hAok⟩ φ) :
    Nonempty (EnvS2PM V μ ⟨c₀ :: env.consts⟩) := by
  have hbound := envWF_constsBound mp.base2.base.wf
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hfresh
    rw [Setlec.Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  -- the P crossing: readings of prefix-bound subjects survive
  have hcompP : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      ConstsBound env e →
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ d e
        = denoteP mp.base2.acval env ψ d e := by
    intro ψ d e hcb
    rw [← denoteP_envExtend (findPreserved_cons hfresh) hlga d e hcb,
      denoteP_acvalWith_fresh hfresh d e]
  -- the P fields, at the `acvalWith` spelling (defeq to the core's)
  have htr : ∀ c ∈ (⟨c₀ :: env.consts⟩ : Env).consts, ∀ ψ : Name → Nat,
      ∃ ta : AVExpr,
        denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c.toConstantVal.type = some ta := by
    intro c hc ψ
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact htyReads ψ
    · obtain ⟨ta, hta⟩ := mp.type_reads c h ψ
      exact ⟨ta, by rw [hcompP ψ 0 _ (hbound _ h).1]; exact hta⟩
  have hto : ∀ c ∈ (⟨c₀ :: env.consts⟩ : Env).consts,
      ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, AnnotOkP V ρ ta := by
    intro c hc ψ ta hta ρ
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact htyOk ψ ta hta ρ
    · rw [hcompP ψ 0 _ (hbound _ h).1] at hta
      exact mp.type_okP c h ψ ta hta ρ
  have hmt : ∀ c ∈ (⟨c₀ :: env.consts⟩ : Env).consts,
      ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c.toConstantVal.type = some ta →
      ∀ ρ : Nat → V,
        interp2 V ρ (acvalWith mp.base2.acval c₀.name A c.name ψ)
          ∈ˢ interp2 V ρ ta := by
    intro c hc ψ ta hta ρ
    rcases List.mem_cons.mp hc with rfl | h
    · rw [show acvalWith mp.base2.acval c.name A c.name = A from
        acvalWith_self]
      exact hmemNew ψ ta hta ρ
    · rw [hcompP ψ 0 _ (hbound _ h).1] at hta
      rw [show acvalWith mp.base2.acval c₀.name A c.name
            = mp.base2.acval c.name from acvalWith_ne (hne _ h)]
      exact mp.mem_typeP c h ψ ta hta ρ
  have hdr : ∀ (ψ : Name → Nat) (cv : ConstantVal) (value : Expr),
      ((∃ hint : ReducibilityHint,
          ConstantInfo.defnInfo cv value hint
            ∈ (⟨c₀ :: env.consts⟩ : Env).consts) ∨
        ConstantInfo.thmInfo cv value
          ∈ (⟨c₀ :: env.consts⟩ : Env).consts) →
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 value
        = some (acvalWith mp.base2.acval c₀.name A cv.name ψ) := by
    intro ψ cv value hmem
    rcases hmem with ⟨hint, hdt⟩ | hdt
    · rcases List.mem_cons.mp hdt with h | h
      · have hnm : cv.name = c₀.name := congrArg ConstantInfo.name h
        have hleaf : acvalWith mp.base2.acval c₀.name A cv.name = A := by
          rw [hnm]; exact acvalWith_self
        rw [hleaf]
        exact hvalReads ψ cv value (.inl ⟨hint, h⟩)
      · rw [hcompP ψ 0 value ((hbound _ h).2.1 cv value hint rfl),
          show acvalWith mp.base2.acval c₀.name A cv.name
            = mp.base2.acval cv.name from
            acvalWith_ne (show cv.name ≠ c₀.name from hne _ h)]
        exact mp.defn_reads ψ cv value (.inl ⟨hint, h⟩)
    · rcases List.mem_cons.mp hdt with h | h
      · have hnm : cv.name = c₀.name := congrArg ConstantInfo.name h
        have hleaf : acvalWith mp.base2.acval c₀.name A cv.name = A := by
          rw [hnm]; exact acvalWith_self
        rw [hleaf]
        exact hvalReads ψ cv value (.inr h)
      · rw [hcompP ψ 0 value ((hbound _ h).2.2 cv value rfl),
          show acvalWith mp.base2.acval c₀.name A cv.name
            = mp.base2.acval cv.name from
            acvalWith_ne (show cv.name ≠ c₀.name from hne _ h)]
        exact mp.defn_reads ψ cv value (.inr h)
  exact ⟨{
    base2 := ⟨hbase, acvalWith mp.base2.acval c₀.name A,
      by intro n ψ
         by_cases hn : n = c₀.name
         · subst hn
           rw [show acvalWith mp.base2.acval c₀.name A c₀.name = A from
             acvalWith_self]
           exact hAerase ψ
         · rw [show acvalWith mp.base2.acval c₀.name A n
                 = mp.base2.acval n from acvalWith_ne hn,
             mp.base2.acval_erase, hag n hn],
      acvalWith_closed mp.base2.acval_closed hAclosed,
      acvalWith_params mp.base2.acval_params hAparams,
      acvalWith_ok2 mp.base2.acval_ok2 hAok⟩
    acval_validV := acvalWith_validV (n := c₀.name)
      mp.acval_validV hAvalid
    type_reads := htr
    type_okP := hto
    mem_typeP := hmt
    defn_reads := hdr
    nat_heads := hnh }⟩

end Setlec.SetR.Interp2
