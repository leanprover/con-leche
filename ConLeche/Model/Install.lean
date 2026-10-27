module

public import ConLeche.Model.Tiers
public import ConLeche.Verify.Denote.EnvExtend
import ConLeche.Verify.Denote.OpenVars
public import ConLeche.Verify.Denote.ConstsBound
public import ConLeche.Verify.Extend.Sibs
import ConLeche.Model.Env.CanonCrest

public section

/-!
# The P declaration step (task #161, P4 — the fold's species)

`declStep_preserves_of_cons`: extending `EnvModelM` by one fresh
constant, in the shape the declaration fold consumes:

* the new leaf `A` is the value's **`denote` reading**, with the **existence** premise `hvalReads`;
* the crossing is not routed: `denote_envExtend` is a theorem, so
  the old constants' facts transfer from `findPreserved_cons` + a
  literal-guard agreement;
* the new constant's own facts (`htyReads`/`htyOk`/`hmemNew` and the
  leaf laws) are the **front-door harvest**: at the fold they come
  from `checkSoundAt` at the prefix environment applied to the
  declaration's checked runs.

`nat_heads` at the extension is taken as a premise
(`natHeads_cons_fresh` discharges it whenever the new constant is not
a literal pin; the pin installs supply it bespoke).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-- A fresh cons preserves every stored lookup. -/
theorem findPreserved_cons {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) :
    FindPreserved env ⟨c₀ :: env.consts, env.tables⟩ := by
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

/-- **The fresh-cons forward transfer** (the monotone form; the
equality form is refutable at support-completing installs — see
`denote_envExtend_mono`): a successful prefix reading survives the
extension and ignores the fresh leaf.  The only direction the step
and the harvests use for their subjects, whose acceptance guaranteed
prefix-supported literals. -/
theorem denote_cons_mono {acval : Name → (Name → Nat) → Term}
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    (hfresh : env.find? c₀.name = none) {e : Expr}
    (ψ : Name → Nat) (d : Nat) (hcb : ConstsBound env e)
    {ea : Term} (h : denote acval env ψ d e = some ea) :
    denote (acvalWith acval c₀.name A) ⟨c₀ :: env.consts, env.tables⟩ ψ d e
      = some ea :=
  denote_envExtend_mono (findPreserved_cons hfresh)
    (litGuardsMono_cons hfresh)
    (findProj?_mono_of_tables (findPreserved_cons hfresh) rfl) d e hcb
    (by rw [denote_acvalWith_fresh hfresh]; exact h)

/-! ## Extensions that keep the prefix's readings (task #362)

Two installs extend the environment without moving anything the
prefix's stored data reads: a fresh constant (the leaf valuation gains
one name) and a projection table (the valuation is unchanged; the table
is of a stored structure without one).  At both, every stored name
looks up as before and keeps its leaf, and every successful prefix
reading of a prefix-bound subject survives (`denote_envExtend_mono`).
`ModelExt` is that much; the environment laws' transports
(`recRuleLaw_ext`, `towerEntryLaw_ext`, …) consume nothing else, so
both installs share them. -/

/-- **An extension keeping the prefix's readings**: stored names look up
and read as before, and successful readings of prefix-bound subjects
survive. -/
structure ModelExt {μ : CheckMode} {env : Env} (mp : EnvModelM V μ env) (env' : Env)
    (acval' : Name → (Name → Nat) → Term) : Prop where
  agree : ∀ n, (env.find? n).isSome = true → env'.find? n = env.find? n
  leaf : ∀ n, (env.find? n).isSome = true → acval' n = mp.base2.acval n
  denote : ∀ {ψ : Name → Nat} {d : Nat} {e : Expr} {ea : Term}, ConstsBound env e →
    denote mp.base2.acval env ψ d e = some ea → denote acval' env' ψ d e = some ea

namespace ModelExt

variable {mp : EnvModelM V μ env} {env' : Env} {acval' : Name → (Name → Nat) → Term}

theorem find (hx : ModelExt mp env' acval') {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) : env'.find? n = some ci := by
  rw [hx.agree n (by rw [hf]; rfl)]; exact hf

theorem back (hx : ModelExt mp env' acval') {n : Name} {ci : ConstantInfo}
    (hs : (env.find? n).isSome = true) (hf : env'.find? n = some ci) :
    env.find? n = some ci := by
  rw [← hx.agree n hs]; exact hf

theorem leafOf (hx : ModelExt mp env' acval') {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) : acval' n = mp.base2.acval n :=
  hx.leaf n (by rw [hf]; rfl)

/-- A fresh constant's install keeps the prefix's readings. -/
theorem cons (mp : EnvModelM V μ env) {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) (A : (Name → Nat) → Term) :
    ModelExt mp ⟨c₀ :: env.consts, env.tables⟩ (acvalWith mp.base2.acval c₀.name A) :=
  ⟨fun _ hn => ConLeche.Env.find?_cons_of_isSome hfresh hn,
    fun n hn => acvalWith_ne (fun h => by rw [h, hfresh] at hn; exact nomatch hn),
    fun hcb h => denote_cons_mono hfresh _ _ hcb h⟩

/-- A fresh constant's install, at any model whose valuation is the
installed one. -/
theorem consOf (mp : EnvModelM V μ env) {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    (hfresh : env.find? c₀.name = none)
    {m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩}
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A) :
    ModelExt mp ⟨c₀ :: env.consts, env.tables⟩ m₂.acval := by
  rw [hac]; exact ModelExt.cons mp hfresh A

end ModelExt

/-- **A table install keeps every successful reading** (task #362): the
new table is of a structure that had none, so every table a reading
consulted is still there. -/
theorem denote_pushTable_mono {acval : Name → (Name → Nat) → Term} {t : ConLeche.ProjTable}
    (hT : env.findTable? t.structName = none) {e : Expr} (ψ : Name → Nat) (d : Nat)
    (hcb : ConstsBound env e) {ea : Term} (h : denote acval env ψ d e = some ea) :
    denote acval ⟨env.consts, t :: env.tables⟩ ψ d e = some ea := by
  refine denote_envExtend_mono (env₀ := env) (env := ⟨env.consts, t :: env.tables⟩)
    (fun hf => hf) ⟨fun h => h, fun h => h⟩ ?_ d e hcb h
  intro sn i entry hfp
  obtain ⟨tbl, hft, hi, rfl⟩ := ConLeche.Env.findProj?_some hfp
  refine ConLeche.Env.findProj?_of_table ?_ hi
  rw [ConLeche.Env.findTable?_pushTable]
  split
  · next hh =>
    rw [← hh.1, hT] at hft
    exact nomatch hft
  · exact hft

/-- A table install keeps the prefix's readings, at the same valuation. -/
theorem ModelExt.pushTable (mp : EnvModelM V μ env) {t : ConLeche.ProjTable}
    (hT : env.findTable? t.structName = none) :
    ModelExt mp ⟨env.consts, t :: env.tables⟩ mp.base2.acval :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun hcb h => denote_pushTable_mono hT _ _ hcb h⟩

/-- The pinned-basis valuation survives any fresh cons that moves no
other name (`BasisPinnedTT.cons` without the install record — its
proof consults only freshness and agreement). -/
theorem basisPinnedTT_consFresh {cval cval' : (Name → (Name → Nat) → Term)}
    {c₀ : ConstantInfo} (h : BasisPinnedTT env cval)
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → cval n = cval' n)
    (hhead : ConLeche.reservedBasisNames.contains c₀.name = true →
      c₀ = pinnedInfo c₀.name ∧
      ∀ (ψ : Name → Nat) (t : Term),
        pinnedStructT c₀.name ψ = some t → cval' c₀.name ψ = t) :
    BasisPinnedTT ⟨c₀ :: env.consts, env.tables⟩ cval' := by
  intro n ci hf hres
  by_cases hn : c₀.name = n
  · subst hn
    rw [ConLeche.Env.find?_cons, ite_eq_left rfl] at hf
    obtain rfl : ci = c₀ := (Option.some.inj hf).symm
    exact ⟨(hhead hres).1, fun t ψ hp => (hhead hres).2 ψ t hp⟩
  · rw [ConLeche.Env.find?_cons, ite_eq_right hn] at hf
    refine ⟨(h n ci hf hres).1, fun t ψ hp => ?_⟩
    rw [← hag n (fun hh => hn hh.symm)]
    exact (h n ci hf hres).2 t ψ hp

/-! ## The core at a fresh cons, model-free (task #161 S7)

`coreCons` builds `EnvModel`'s syntactic fields from the *prefix
core's own* fields plus the head's obligations — `BasisPinnedTT.cons`,
`ProjOkT.cons`, `RecCtorsStored.cons`, all model-free.
-/

/-- **The head obligations of a fresh cons** (task #161 S7): what
`declStep_preserves_of_cons` needs of the new leaf.  Bundled because the wrapper stack
between the step and its 40 call sites re-states it thirty-five
times. -/
structure ConsHead (env : Env) (c₀ : ConstantInfo)
    (A : (Name → Nat) → Term) : Prop where
  /-- the extended store is syntactically well-formed -/
  wf : EnvWF ⟨c₀ :: env.consts, env.tables⟩
  /-- the new leaf's erasure is closed -/
  vclosed : ∀ ψ : Name → Nat, Term.Closed (A ψ)
  /-- if the head sits at a reserved basis name, it is the pinned
  declaration and its leaf erases to the direct pin -/
  pin : ConLeche.reservedBasisNames.contains c₀.name = true →
    c₀ = pinnedInfo c₀.name ∧
    ∀ (ψ : Name → Nat) (t : Term),
      pinnedStructT c₀.name ψ = some t → (A ψ) = t
  /-- a head recursor's rules' constructors are stored and its two
  rescue bits are the store's own verdict (`RecCtorsStored`'s head) -/
  ctorsHead : ∀ cvR mI rP rules, c₀ = .recInfo cvR mI rP rules →
    ∀ r ∈ rules,
      (∃ cvj cnP cnF,
        env.find? (ConLeche.RecRule.ctor r)
          = some (.ctorInfo cvj cnP cnF)) ∧
      (r.k = true → ConLeche.recRuleKOf env.find? r.ctor = true) ∧
      (r.eta = true →
        ConLeche.recRuleEtaOf env.find? r.ctor = true)

/-- **The head obligations of a basis cons**: the head is the pinned
declaration, its leaf is the direct pin, and (for a recursor) its rules'
constructors are stored. -/
theorem ConsHead.ofBasis {c₀ : ConstantInfo}
    {A : (Name → Nat) → Term}
    (hwf : EnvWF ⟨c₀ :: env.consts, env.tables⟩)
    (hvclosed : ∀ ψ : Name → Nat, Term.Closed (A ψ))
    (hpinned : c₀ = pinnedInfo c₀.name)
    (hleaf : ∀ (ψ : Name → Nat) (t : Term),
      pinnedStructT c₀.name ψ = some t → (A ψ) = t)
    (hctors : ∀ cvR mI rP rules, c₀ = .recInfo cvR mI rP rules →
      ∀ r ∈ rules,
        (∃ cvj cnP cnF,
          env.find? (ConLeche.RecRule.ctor r)
            = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → ConLeche.recRuleKOf env.find? r.ctor = true) ∧
        (r.eta = true →
          ConLeche.recRuleEtaOf env.find? r.ctor = true)) :
    ConsHead env c₀ A :=
  ⟨hwf, hvclosed, fun _ => ⟨hpinned, hleaf⟩, hctors⟩

/-- **The head obligations of an ordinary (non-reserved) cons**: the
pin clause is vacuous. -/
theorem ConsHead.ofFresh {c₀ : ConstantInfo}
    {A : (Name → Nat) → Term}
    (hwf : EnvWF ⟨c₀ :: env.consts, env.tables⟩)
    (hvclosed : ∀ ψ : Name → Nat, Term.Closed (A ψ))
    (hnres : ConLeche.reservedBasisNames.contains c₀.name = false)
    (hctors : ∀ cvR mI rP rules, c₀ = .recInfo cvR mI rP rules →
      ∀ r ∈ rules,
        (∃ cvj cnP cnF,
          env.find? (ConLeche.RecRule.ctor r)
            = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → ConLeche.recRuleKOf env.find? r.ctor = true) ∧
        (r.eta = true →
          ConLeche.recRuleEtaOf env.find? r.ctor = true)) :
    ConsHead env c₀ A :=
  ⟨hwf, hvclosed,
    fun hres => absurd hres (by rw [hnres]; exact fun h => nomatch h),
    hctors⟩

/-- `acval_wellDenoted` extends. -/
theorem acvalWith_wellDenoted
    {acval : Name → (Name → Nat) → Term} {n : Name}
    {A : (Name → Nat) → Term}
    (h : ∀ (m : Name) (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (acval m ψ))
    (hA : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ)) :
    ∀ (m : Name) (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (acvalWith acval n A m ψ) := by
  intro m ψ ρ
  by_cases hm : m = n
  · subst hm
    rw [acvalWith_self]
    exact hA ψ ρ
  · rw [acvalWith_ne hm]
    exact h m ψ ρ

/-- **The core at a fresh cons** (task #161 S7).  Every field is the prefix's own, stepped by the
head's obligation; nothing of the collapsed model is consulted. -/
@[expose] def coreCons (m : EnvModel V env) {c₀ : ConstantInfo}
    (A : (Name → Nat) → Term)
    (hfresh : env.find? c₀.name = none)
    (hh : ConsHead env c₀ A)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ)) :
    EnvModel V ⟨c₀ :: env.consts, env.tables⟩ where
  wf := hh.wf
  acval := acvalWith m.acval c₀.name A
  cval_closed := by
    intro n ψ
    by_cases hn : n = c₀.name
    · rw [show acvalWith m.acval c₀.name A n = A from by
        rw [hn]; exact acvalWith_self]
      exact hh.vclosed ψ
    · rw [show acvalWith m.acval c₀.name A n = m.acval n from
        acvalWith_ne hn]
      exact m.cval_closed n ψ
  basis_pinned :=
    basisPinnedTT_consFresh m.basis_pinned hfresh
      (fun n hn => funext fun ψ => by rw [acvalWith_ne hn])
      (fun hres => ⟨(hh.pin hres).1, fun ψ t hp => by
        show (acvalWith m.acval c₀.name A c₀.name ψ) = t
        rw [show acvalWith m.acval c₀.name A c₀.name = A from
          acvalWith_self]
        exact (hh.pin hres).2 ψ t hp⟩)
  proj_ok := ProjOkT.cons m.proj_ok m.wf hfresh
  rec_ctors := ConLeche.RecCtorsStored.cons m.rec_ctors hfresh hh.ctorsHead
  acval_params := acvalWith_params m.acval_params hAparams
  acval_wellDenoted := acvalWith_wellDenoted m.acval_wellDenoted hAok

/-- `indStrictHead_of` at a cons's own leaf. -/
theorem indStrictHead_cons {acval : Name → (Name → Nat) → Term} {env : Env}
    {cv : ConstantVal} {caps : IndCaps} {A : (Name → Nat) → Term}
    {ab : (Name → Nat) → List Term} {s : (Name → Nat) → Nat}
    (hread : ∀ ψ, denote (acvalWith acval cv.name A) env ψ 0 cv.type
      = some (mkPisAV (ab ψ) (.sort (s ψ))))
    (h : ∀ ψ, s ψ ≠ 0 → ∀ (ρ : Nat → V) (vs : List V), SpineFit ρ (ab ψ) vs →
      Strict (vs.foldl SetTheory.app (interp V ρ (A ψ)))) :
    IndStrictHead (V := V) (acvalWith acval cv.name A) env (.indInfo cv caps) :=
  indStrictHead_of hread fun ψ hn ρ vs hsp => by
    rw [show acvalWith acval cv.name A cv.name ψ = A ψ from congrFun acvalWith_self ψ]
    exact h ψ hn ρ vs hsp

/-- `indStrictHead_cons` at a former whose sort is `Prop` at every
assignment: nothing to prove. -/
theorem indStrictHead_cons_prop {acval : Name → (Name → Nat) → Term} {env : Env}
    {cv : ConstantVal} {caps : IndCaps} {A : (Name → Nat) → Term}
    {ab : (Name → Nat) → List Term}
    (hread : ∀ ψ, denote (acvalWith acval cv.name A) env ψ 0 cv.type
      = some (mkPisAV (ab ψ) (.sort 0))) :
    IndStrictHead (V := V) (acvalWith acval cv.name A) env (.indInfo cv caps) :=
  indStrictHead_cons (s := fun _ => 0) hread fun _ hn => absurd rfl hn

/-- **The P declaration step, cons shape** (see the module
docstring). -/
theorem declStep_preserves_of_cons (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    (hfresh : env.find? c₀.name = none)
    (hh : ConsHead env c₀ A)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ))
    (htyReads : ∀ ψ : Name → Nat,
      ∃ ta : Term,
        denote (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts, env.tables⟩ ψ 0 c₀.toConstantVal.type = some ta)
    (htyOk : ∀ (ψ : Name → Nat) (ta : Term),
      denote (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts, env.tables⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, WellDenotedTy V ρ ta)
    (hmemNew : ∀ (ψ : Name → Nat) (ta : Term),
      denote (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts, env.tables⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, interp V ρ (A ψ) ∈ˢ interp V ρ ta)
    (hvalReads : ∀ (ψ : Name → Nat) (cv : ConstantVal)
      (value : Expr),
      (∃ hint : ReducibilityHint,
        ConstantInfo.defnInfo cv value hint = c₀) →
      ∃ t, denote (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts, env.tables⟩ ψ 0 value = some t ∧ LeafReads V (A ψ) t)
    (hnh : ∀ φ : Name → Nat,
      NatHeads (V := V)
        (coreCons mp.base2 A hfresh hh hAparams hAok) φ)
    (hnat_ops : ∀ φ : Name → Nat,
      NatOps (V := V)
        ((coreCons mp.base2 A hfresh hh hAparams hAok) : EnvModel V _) φ)
    (hdiv_mod : ∀ φ : Name → Nat,
      DivMod (V := V) ((coreCons mp.base2 A hfresh hh hAparams hAok) : EnvModel V _) φ)
    (heq_law : EqLaw (V := V) ((coreCons mp.base2 A hfresh hh hAparams hAok) : EnvModel V _))
    (hcaps_ok : CapsOk (V := V)
        ((coreCons mp.base2 A hfresh hh hAparams hAok) : EnvModel V _))
    (hrec_rules : ∀ φ : Name → Nat,
      RecRules (V := V) ((coreCons mp.base2 A hfresh hh hAparams hAok) : EnvModel V _) φ)
    (hreduce_ops : ReduceOps (V := V)
        ((coreCons mp.base2 A hfresh hh hAparams hAok) : EnvModel V _))
    (htower_ok : ∀ φ : Name → Nat,
      TowerOk (V := V) ((coreCons mp.base2 A hfresh hh hAparams hAok) : EnvModel V _) φ)
    -- the head's fibres above a proposition, if it is a former (task
    -- #342 L7); vacuous at every other head kind
    (hind : IndStrictHead (V := V) (acvalWith mp.base2.acval c₀.name A)
      ⟨c₀ :: env.consts, env.tables⟩ c₀ := by
      intro _ _ h; first | exact nomatch h | exact ConstantInfo.noConfusion h) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts, env.tables⟩,
      mp'.base2.acval = acvalWith mp.base2.acval c₀.name A := by
  have hbound := envWF_constsBound mp.base2.wf
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hfresh
    rw [ConLeche.Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  -- the P crossing, forward only: successful prefix readings of the
  -- stored pieces survive
  have hcompM : ∀ (ψ : Name → Nat) (e : Expr), ConstsBound env e →
      ∀ {ea : Term}, denote mp.base2.acval env ψ 0 e = some ea →
      denote (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts, env.tables⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h => denote_cons_mono hfresh ψ 0 hcb h
  -- the P fields, at the `acvalWith` spelling (defeq to the core's)
  have htr : ∀ c ∈ (⟨c₀ :: env.consts, env.tables⟩ : Env).consts, ∀ ψ : Name → Nat,
      ∃ ta : Term,
        denote (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts, env.tables⟩ ψ 0 c.toConstantVal.type = some ta := by
    intro c hc ψ
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact htyReads ψ
    · obtain ⟨ta, hta⟩ := mp.type_reads c h ψ
      exact ⟨ta, hcompM ψ _ (hbound _ h).1 hta⟩
  have hto : ∀ c ∈ (⟨c₀ :: env.consts, env.tables⟩ : Env).consts,
      ∀ (ψ : Name → Nat) (ta : Term),
      denote (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts, env.tables⟩ ψ 0 c.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, WellDenotedTy V ρ ta := by
    intro c hc ψ ta hta ρ
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact htyOk ψ ta hta ρ
    · obtain ⟨ta', hta'⟩ := mp.type_reads c h ψ
      obtain rfl : ta' = ta :=
        Option.some.inj
          ((hcompM ψ _ (hbound _ h).1 hta').symm.trans
            hta)
      exact mp.type_wellDenotedTy c h ψ ta' hta' ρ
  have hmt : ∀ c ∈ (⟨c₀ :: env.consts, env.tables⟩ : Env).consts,
      ∀ (ψ : Name → Nat) (ta : Term),
      denote (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts, env.tables⟩ ψ 0 c.toConstantVal.type = some ta →
      ∀ ρ : Nat → V,
        interp V ρ (acvalWith mp.base2.acval c₀.name A c.name ψ)
          ∈ˢ interp V ρ ta := by
    intro c hc ψ ta hta ρ
    rcases List.mem_cons.mp hc with rfl | h
    · rw [show acvalWith mp.base2.acval c.name A c.name = A from
        acvalWith_self]
      exact hmemNew ψ ta hta ρ
    · obtain ⟨ta', hta'⟩ := mp.type_reads c h ψ
      obtain rfl : ta' = ta :=
        Option.some.inj
          ((hcompM ψ _ (hbound _ h).1 hta').symm.trans
            hta)
      rw [show acvalWith mp.base2.acval c₀.name A c.name
            = mp.base2.acval c.name from acvalWith_ne (hne _ h)]
      exact mp.mem_type c h ψ ta' hta' ρ
  have hdr : ∀ (ψ : Name → Nat) (cv : ConstantVal) (value : Expr),
      (∃ hint : ReducibilityHint,
        ConstantInfo.defnInfo cv value hint
          ∈ (⟨c₀ :: env.consts, env.tables⟩ : Env).consts) →
      ∃ t, denote (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env.consts, env.tables⟩ ψ 0 value = some t ∧
        LeafReads V (acvalWith mp.base2.acval c₀.name A cv.name ψ) t := by
    intro ψ cv value hmem
    obtain ⟨hint, hdt⟩ := hmem
    rcases List.mem_cons.mp hdt with h | h
    · have hnm : cv.name = c₀.name := congrArg ConstantInfo.name h
      have hleaf : acvalWith mp.base2.acval c₀.name A cv.name = A := by
        rw [hnm]; exact acvalWith_self
      rw [hleaf]
      exact hvalReads ψ cv value ⟨hint, h⟩
    · rw [show acvalWith mp.base2.acval c₀.name A cv.name
          = mp.base2.acval cv.name from
          acvalWith_ne (show cv.name ≠ c₀.name from hne _ h)]
      obtain ⟨t, ht, hlr⟩ := mp.defn_reads ψ cv value ⟨hint, h⟩
      exact ⟨t, hcompM ψ value ((hbound _ h).2 cv value hint rfl) ht, hlr⟩
  -- the stored formers' strict fibres: the head's is `hind`; a prefix
  -- former keeps its leaf and its type's reading
  have hind' : IndStrictOk (V := V) (coreCons mp.base2 A hfresh hh hAparams hAok) := by
    intro I cv caps hf ψ ab n hread hn ρ vs hsp
    by_cases hI : I = c₀.name
    · subst hI
      rw [ConLeche.Env.find?_cons_self] at hf
      exact hind cv caps (Option.some.inj hf) ψ ab n hread hn ρ vs hsp
    · have hfE : env.find? I = some (.indInfo cv caps) := by
        rw [ConLeche.Env.find?_cons, ite_eq_right (fun hh' => hI hh'.symm)] at hf
        exact hf
      have hm := ConLeche.Env.find?_mem hfE
      obtain ⟨ta, hta⟩ := mp.type_reads _ hm ψ
      have hcv : (ConstantInfo.indInfo cv caps).toConstantVal = cv := rfl
      rw [hcv] at hta
      have hta' := hcompM ψ _ ((hbound _ hm).1) hta
      rw [hcv] at hta'
      have hEq : ta = mkPisAV ab (.sort n) := Option.some.inj (hta'.symm.trans hread)
      subst hEq
      show Strict (vs.foldl SetTheory.app
        (interp V ρ (acvalWith mp.base2.acval c₀.name A I ψ)))
      rw [acvalWith_ne hI]
      exact mp.ind_strict I cv caps hfE ψ ab n hta hn ρ vs hsp
  exact ⟨{
    base2 := coreCons mp.base2 A hfresh hh hAparams hAok
    type_reads := htr
    type_wellDenotedTy := hto
    mem_type := hmt
    defn_reads := hdr
    nat_heads := hnh
    nat_ops := hnat_ops
    div_mod := hdiv_mod
    eq_law := heq_law
    caps_ok := hcaps_ok
    rec_rules := hrec_rules
    reduce_ops := hreduce_ops
    tower_ok := htower_ok
    ind_strict := hind'
    -- the recorded lfp clauses: a fresh cons re-reads no stored name
    lfpBlocks := mp.lfpBlocks
    lfp_ok := mp.lfp_ok_transport (fun _ _ hf _ => findPreserved_cons hfresh hf)
      (fun n _ hf _ => acvalWith_ne fun h => by
        rw [h, hfresh] at hf; exact nomatch hf)
      (fun _ _ _ hf ψ _ hta =>
        have hm := ConLeche.Env.find?_mem hf
        hcompM ψ _ (hbound _ hm).1 hta)
      (fun _ _ _ _ hf ψ _ hta =>
        have hm := ConLeche.Env.find?_mem hf
        hcompM ψ _ (hbound _ hm).1 hta)
      (fun _ _ hf _ _ hA ψ d _ hta =>
        have hm := ConLeche.Env.find?_mem hf
        denote_cons_mono hfresh ψ d (canonOf_constsBound (hbound _ hm).1 hA) hta) }, rfl⟩

end ConLeche.Model
