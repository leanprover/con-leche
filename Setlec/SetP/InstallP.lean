import Setlec.SetP.Step2.TiersP
import Setlec.SetP.Annot.BitExtend
import Setlec.SetP.Annot.BitConsCross
import Setlec.Semantics.ConstsBound
import Setlec.Verify.Extend.Sibs

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

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.Semantics (AVExpr)
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

/-- **The fresh-cons transfer**: readings of prefix-bound subjects
survive the extension and ignore the fresh leaf — the composition of
`denoteP_envExtend` (a theorem) and `denoteP_acvalWith_fresh`.  The
harvest layer reads it directly; `declStepPM_of_cons` uses it for
every old-constant field. -/
theorem denoteP_cons_fresh {acval : Name → (Name → Nat) → AVExpr}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hntc : ∀ entry, c₀ = .projInfo entry → entry.tower = false)
    (hlga : LitGuardsAgree env ⟨c₀ :: env.consts⟩)
    (ψ : Name → Nat) (d : Nat) (e : Expr) (hcb : ConstsBound env e) :
    denoteP (acvalWith acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d e
      = denoteP acval env ψ d e := by
  rw [← denoteP_envExtend (findPreserved_cons hfresh) hlga
      (Setlec.TTVerify.findProj?_cons_of_base_none hfresh hntc)
      d e hcb,
    denoteP_acvalWith_fresh hfresh d e]

/-- **The fresh-cons forward transfer** (the monotone form; the
equality form is refutable at support-completing installs — see
`denoteP_envExtend_mono`): a successful prefix reading survives the
extension and ignores the fresh leaf.  The only direction the step
and the harvests use for their subjects, whose acceptance guaranteed
prefix-supported literals. -/
theorem denoteP_cons_fresh_mono {acval : Name → (Name → Nat) → AVExpr}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hntc : ∀ entry, c₀ = .projInfo entry → entry.tower = false)
    (ψ : Name → Nat) (d : Nat) (e : Expr) (hcb : ConstsBound env e)
    {ea : AVExpr} (h : denoteP acval env ψ d e = some ea) :
    denoteP (acvalWith acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d e
      = some ea :=
  denoteP_envExtend_mono (findPreserved_cons hfresh)
    (litGuardsMono_cons hfresh)
    (Setlec.TTVerify.findProj?_cons_of_base_none hfresh hntc) d e hcb
    (by rw [denoteP_acvalWith_fresh hfresh]; exact h)

/-- **The P cons crossing at any head** (task #175 W4c, module 4): a
prefix reading of a subject the head's slot does not mention
(`ConsCrossAt`) survives the cons — the fresh crossing at a non-tower
head, the tower-slot refinement (`denoteP_envExtend_mono_at`) at a
tower one. -/
theorem denoteP_cons_mono {acval : Name → (Name → Nat) → AVExpr}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    {e : Expr} (hat : ConsCrossAt c₀ e)
    (ψ : Name → Nat) (d : Nat) (hcb : ConstsBound env e)
    {ea : AVExpr} (h : denoteP acval env ψ d e = some ea) :
    denoteP (acvalWith acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d e
      = some ea := by
  by_cases htw : ∃ tbl : Setlec.ProjTable, c₀ = .projInfo tbl ∧
      tbl.tower = true
  · obtain ⟨tbl, rfl, htw⟩ := htw
    refine denoteP_envExtend_mono_at (findPreserved_cons hfresh)
      (litGuardsMono_cons hfresh)
      (fun sn j e' h0 h1 htw' => findProj?_cons_tower sn j e' h0 h1 htw')
      d e hcb (hat tbl rfl htw) ?_
    rw [denoteP_acvalWith_fresh hfresh]
    exact h
  · refine denoteP_cons_fresh_mono hfresh ?_ ψ d e hcb h
    intro e' heq
    exact Classical.byContradiction fun h' =>
      htw ⟨e', heq, by simpa using h'⟩

/-- The pinned-basis valuation survives any fresh cons that moves no
other name (`BasisPinnedTT.cons` without the install record — its
proof consults only freshness and agreement). -/
theorem basisPinnedTT_consFresh {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : BasisPinnedTT env cval)
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → cval n = cval' n)
    (hhead : Setlec.reservedBasisNames.contains c₀.name = true →
      (ConstantInfo.isBasis c₀ = true → c₀ = pinnedInfo c₀.name) ∧
      ∀ (ψ : Name → Nat) (t : VExpr),
        pinnedDirectT c₀.name ψ = some t → cval' c₀.name ψ = t) :
    BasisPinnedTT ⟨c₀ :: env.consts⟩ cval' := by
  intro n ci hf hres
  by_cases hn : c₀.name = n
  · subst hn
    rw [Setlec.Env.find?_cons, if_pos rfl] at hf
    obtain rfl : ci = c₀ := (Option.some.inj hf).symm
    exact ⟨(hhead hres).1, fun t ψ hp => (hhead hres).2 ψ t hp⟩
  · rw [Setlec.Env.find?_cons, if_neg hn] at hf
    refine ⟨(h n ci hf hres).1, fun t ψ hp => ?_⟩
    rw [← hag n (fun hh => hn hh.symm)]
    exact (h n ci hf hres).2 t ψ hp

/-! ## The core at a fresh cons, model-free (task #161 S7, Wall C)

`coreOfBase` reads `EnvS2Core`'s five syntactic fields off a contained
`EnvS`.  `coreCons` builds them from the *prefix core's own* fields
plus the head's obligations — `BasisPinnedTT.cons`, `ProjOkT.cons`,
`RecCtorsStored.cons` (`Verify/Denote/Install`, `Verify/Extend/Sibs`),
all model-free — which is what lets `EnvS2PM.base` go.
-/

/-- The valuation moves only at the fresh name, at the erased
spelling: the `Installs` context the three env-facts share. -/
theorem installsE {acval : Name → (Name → Nat) → AVExpr}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hntc : ∀ entry, c₀ = .projInfo entry → entry.tower = false) :
    Installs env (fun n ψ => (acval n ψ).erase)
      (fun n ψ => (acvalWith acval c₀.name A n ψ).erase) c₀ :=
  Installs.of_fresh hfresh hntc (fun n hn =>
    funext fun ψ => by rw [acvalWith_ne hn])

/-- **The head obligations of a fresh cons** (task #161 S7, Wall C
step (b)): what `declStepPM_of_cons` used to read off the contained
`EnvS`, stated at the new leaf.  Bundled because the wrapper stack
between the step and its 40 call sites re-states it thirty-five
times. -/
structure ConsHeadP (env : Env) (c₀ : ConstantInfo)
    (A : (Name → Nat) → AVExpr) : Prop where
  /-- the extended store is syntactically well-formed -/
  wf : EnvWF ⟨c₀ :: env.consts⟩
  /-- the new leaf's erasure is closed (`EnvS.cval_closed` at the head) -/
  vclosed : ∀ ψ : Name → Nat, VExpr.Closed ((A ψ).erase)
  /-- if the head sits at a reserved basis name, it is the pinned
  declaration and its leaf erases to the direct pin -/
  pin : Setlec.reservedBasisNames.contains c₀.name = true →
    (ConstantInfo.isBasis c₀ = true → c₀ = pinnedInfo c₀.name) ∧
    ∀ (ψ : Name → Nat) (t : VExpr),
      pinnedDirectT c₀.name ψ = some t → (A ψ).erase = t
  /-- a head tower table's slots are mentioned by no stored piece, so
  the store's readings survive the cons (task #175 W4c, module 4;
  vacuous at every other head — `ConsCrossEnv.ofNtc`) -/
  projTower : ConsCrossEnv env c₀
  /-- a head tower table carries its head data, at every field, at the
  extension (task #175 S1) -/
  projTowerHead : ∀ tbl, c₀ = .projInfo tbl → tbl.tower = true →
    ∀ i, i < tbl.numFields → Setlec.TowerHead ⟨c₀ :: env.consts⟩ (tbl.entry i)
  /-- a head recursor's rules' constructors are stored
  (`RecCtorsStored`'s head) -/
  ctorsHead : ∀ cvR mI rP rules, c₀ = .recInfo cvR mI rP rules →
    ∀ r ∈ rules, ∃ cvj cnP cnF,
      env.find? (Setlec.RecRule.ctor r)
        = some (.ctorInfo cvj cnP cnF)

/-- **The head obligations of a basis cons**: the head is the pinned
declaration, its leaf is the direct pin, it is not a projection-table
entry, and (for a recursor) its rules' constructors are stored. -/
theorem ConsHeadP.ofBasis {c₀ : ConstantInfo}
    {A : (Name → Nat) → AVExpr}
    (hwf : EnvWF ⟨c₀ :: env.consts⟩)
    (hvclosed : ∀ ψ : Name → Nat, VExpr.Closed ((A ψ).erase))
    (hpinned : ConstantInfo.isBasis c₀ = true → c₀ = pinnedInfo c₀.name)
    (hleaf : ∀ (ψ : Name → Nat) (t : VExpr),
      pinnedDirectT c₀.name ψ = some t → (A ψ).erase = t)
    (hnotproj : ∀ tbl, c₀ ≠ .projInfo tbl)
    (hctors : ∀ cvR mI rP rules, c₀ = .recInfo cvR mI rP rules →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (Setlec.RecRule.ctor r)
          = some (.ctorInfo cvj cnP cnF)) :
    ConsHeadP env c₀ A :=
  ⟨hwf, hvclosed, fun _ => ⟨hpinned, hleaf⟩,
    fun tbl heq => absurd heq (hnotproj tbl),
    fun tbl heq => absurd heq (hnotproj tbl), hctors⟩

/-- **The head obligations of an ordinary (non-reserved) cons**: the
pin clause is vacuous. -/
theorem ConsHeadP.ofFresh {c₀ : ConstantInfo}
    {A : (Name → Nat) → AVExpr}
    (hwf : EnvWF ⟨c₀ :: env.consts⟩)
    (hvclosed : ∀ ψ : Name → Nat, VExpr.Closed ((A ψ).erase))
    (hnres : Setlec.reservedBasisNames.contains c₀.name = false)
    (hprojTower : ∀ tbl, c₀ = .projInfo tbl → tbl.tower = false)
    (hctors : ∀ cvR mI rP rules, c₀ = .recInfo cvR mI rP rules →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (Setlec.RecRule.ctor r)
          = some (.ctorInfo cvj cnP cnF)) :
    ConsHeadP env c₀ A :=
  ⟨hwf, hvclosed,
    fun hres => absurd hres (by rw [hnres]; exact fun h => nomatch h),
    ConsCrossEnv.ofNtc hprojTower,
    fun tbl heq htw => absurd ((hprojTower tbl heq).symm.trans htw)
      (by decide),
    hctors⟩

/-- **The de-based core at a fresh cons** — `coreOfBase`'s successor
(task #161 S7).  Every field is the prefix's own, stepped by the
head's obligation; nothing of the collapsed model is consulted. -/
def coreCons (m : EnvS2Core V env) {c₀ : ConstantInfo}
    (A : (Name → Nat) → AVExpr)
    (hfresh : env.find? c₀.name = none)
    (hh : ConsHeadP env c₀ A)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ)) :
    EnvS2Core V ⟨c₀ :: env.consts⟩ where
  wf := hh.wf
  acval := acvalWith m.acval c₀.name A
  cval_closedL := by
    intro n ψ
    by_cases hn : n = c₀.name
    · rw [show acvalWith m.acval c₀.name A n = A from by
        rw [hn]; exact acvalWith_self]
      exact hh.vclosed ψ
    · rw [show acvalWith m.acval c₀.name A n = m.acval n from
        acvalWith_ne hn]
      exact m.cval_closedL n ψ
  basis_pinnedL :=
    basisPinnedTT_consFresh m.basis_pinnedL hfresh
      (fun n hn => funext fun ψ => by rw [acvalWith_ne hn])
      (fun hres => ⟨(hh.pin hres).1, fun ψ t hp => by
        show (acvalWith m.acval c₀.name A c₀.name ψ).erase = t
        rw [show acvalWith m.acval c₀.name A c₀.name = A from
          acvalWith_self]
        exact (hh.pin hres).2 ψ t hp⟩)
  proj_ok := ProjOkT.cons m.proj_ok hfresh hh.projTowerHead
  rec_ctors := Setlec.RecCtorsStored.cons m.rec_ctors hfresh hh.ctorsHead
  acval_closed := acvalWith_closed m.acval_closed hAclosed
  acval_params := acvalWith_params m.acval_params hAparams
  acval_ok2 := acvalWith_ok2 m.acval_ok2 hAok

/-- **The P declaration step, cons shape** (see the module
docstring). -/
theorem declStepPM_of_cons_guarded (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hh : ConsHeadP env c₀ A)
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
        (coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) φ)
    (hnat_ops : ∀ φ : Name → Nat,
      NatOpsP (V := V)
        ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _) φ)
    (hdiv_mod : ∀ φ : Name → Nat,
      DivModP (V := V) ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _) φ)
    (heq_law : EqLawP (V := V) ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _))
    (hcaps_ok : CapsOkP (V := V)
        ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _))
    (hrec_rules : ∀ φ : Name → Nat,
      RecRulesP (V := V) ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _) φ)
    (hreduce_ops : ReduceOpsP (V := V)
        ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _))
    (htower_ok : ∀ φ : Name → Nat,
      TowerOkP (V := V) ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _) φ) :
    ∃ mp' : EnvS2PM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  have hbound := envWF_constsBound mp.base2.wf
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hfresh
    rw [Setlec.Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  -- the P crossing, forward only: successful prefix readings of the
  -- stored pieces survive (the head's slot mentions none of them)
  have hcompM : ∀ (ψ : Name → Nat) (e : Expr), ConstsBound env e →
      ConsCrossAt c₀ e →
      ∀ {ea : AVExpr}, denoteP mp.base2.acval env ψ 0 e = some ea →
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb hat {ea} h => denoteP_cons_mono hfresh hat ψ 0 hcb h
  -- the P fields, at the `acvalWith` spelling (defeq to the core's)
  have htr : ∀ c ∈ (⟨c₀ :: env.consts⟩ : Env).consts, ∀ ψ : Name → Nat,
      ∃ ta : AVExpr,
        denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c.toConstantVal.type = some ta := by
    intro c hc ψ
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact htyReads ψ
    · obtain ⟨ta, hta⟩ := mp.type_reads c h ψ
      exact ⟨ta, hcompM ψ _ (hbound _ h).1 (hh.projTower.type h) hta⟩
  have hto : ∀ c ∈ (⟨c₀ :: env.consts⟩ : Env).consts,
      ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts⟩ ψ 0 c.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, AnnotOkP V ρ ta := by
    intro c hc ψ ta hta ρ
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact htyOk ψ ta hta ρ
    · obtain ⟨ta', hta'⟩ := mp.type_reads c h ψ
      obtain rfl : ta' = ta :=
        Option.some.inj
          ((hcompM ψ _ (hbound _ h).1 (hh.projTower.type h) hta').symm.trans
            hta)
      exact mp.type_okP c h ψ ta' hta' ρ
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
    · obtain ⟨ta', hta'⟩ := mp.type_reads c h ψ
      obtain rfl : ta' = ta :=
        Option.some.inj
          ((hcompM ψ _ (hbound _ h).1 (hh.projTower.type h) hta').symm.trans
            hta)
      rw [show acvalWith mp.base2.acval c₀.name A c.name
            = mp.base2.acval c.name from acvalWith_ne (hne _ h)]
      exact mp.mem_typeP c h ψ ta' hta' ρ
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
      · rw [show acvalWith mp.base2.acval c₀.name A cv.name
            = mp.base2.acval cv.name from
            acvalWith_ne (show cv.name ≠ c₀.name from hne _ h)]
        exact hcompM ψ value ((hbound _ h).2.1 cv value hint rfl)
          (hh.projTower.defn h)
          (mp.defn_reads ψ cv value (.inl ⟨hint, h⟩))
    · rcases List.mem_cons.mp hdt with h | h
      · have hnm : cv.name = c₀.name := congrArg ConstantInfo.name h
        have hleaf : acvalWith mp.base2.acval c₀.name A cv.name = A := by
          rw [hnm]; exact acvalWith_self
        rw [hleaf]
        exact hvalReads ψ cv value (.inr h)
      · rw [show acvalWith mp.base2.acval c₀.name A cv.name
            = mp.base2.acval cv.name from
            acvalWith_ne (show cv.name ≠ c₀.name from hne _ h)]
        exact hcompM ψ value ((hbound _ h).2.2 cv value rfl)
          (hh.projTower.thm h)
          (mp.defn_reads ψ cv value (.inr h))
  exact ⟨{
    base2 := coreCons mp.base2 A hfresh hh hAclosed hAparams hAok
    acval_validV := acvalWith_validV (n := c₀.name)
      mp.acval_validV hAvalid
    type_reads := htr
    type_okP := hto
    mem_typeP := hmt
    defn_reads := hdr
    nat_heads := hnh
    nat_ops := hnat_ops
    div_mod := hdiv_mod
    eq_lawP := heq_law
    caps_ok := hcaps_ok
    rec_rules := hrec_rules
    reduce_ops := hreduce_ops
    tower_ok := htower_ok }, rfl⟩


/-- **The P step at a cons, at an unconditional membership premise**
(every caller but the tower-entry kit: a table entry's leaf owes no
membership, `EnvS2PM.mem_typeP`'s guard). -/
theorem declStepPM_of_cons (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hh : ConsHeadP env c₀ A)
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
        (coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) φ)
    (hnat_ops : ∀ φ : Name → Nat,
      NatOpsP (V := V)
        ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _) φ)
    (hdiv_mod : ∀ φ : Name → Nat,
      DivModP (V := V) ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _) φ)
    (heq_law : EqLawP (V := V) ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _))
    (hcaps_ok : CapsOkP (V := V)
        ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _))
    (hrec_rules : ∀ φ : Name → Nat,
      RecRulesP (V := V) ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _) φ)
    (hreduce_ops : ReduceOpsP (V := V)
        ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _))
    (htower_ok : ∀ φ : Name → Nat,
      TowerOkP (V := V) ((coreCons mp.base2 A hfresh hh hAclosed hAparams hAok) : EnvS2Core V _) φ) :
    ∃ mp' : EnvS2PM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A :=
  declStepPM_of_cons_guarded mp hfresh hh hAclosed hAparams hAok hAvalid htyReads htyOk
    hmemNew hvalReads hnh hnat_ops hdiv_mod heq_law hcaps_ok hrec_rules hreduce_ops
    htower_ok

end Setlec.SetP
