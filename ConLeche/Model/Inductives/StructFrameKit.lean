module

public import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Verify.BinderLoop
public import ConLeche.Model.Inductives.TowerCons
public import ConLeche.Model.IndTowerRead
public import ConLeche.Model.Capstone
import ConLeche.Semantics.Tower.TowerLeaf
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Mono
import ConLeche.Verify.Subst
import ConLeche.Kernel.Inductives.StructParts
import ConLeche.Model.Annot.BitInstall
import ConLeche.Verify.EnvWF
import ConLeche.Model.IndFrame
import ConLeche.Model.IndDomGrade
import ConLeche.Verify.Leaves
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Tiers
import ConLeche.Semantics.Tower.TowerRec
import ConLeche.Semantics.Tower.TowerWire
import ConLeche.Model.Annot.BitLevels
import ConLeche.Verify.Inductives.DirectInv

public section

/-!
# Block library: a constructor's frames and the former's stage data

The single-constructor readings the block stages are built from, one
section per topic: the annotated Π-bits are exact; `CapsOk` across the
member conses; the stored types' readings; the opened frames, their
rows and telescope walks; the two parameter frames identified; the
family laws; the former's stage data and its cons.
-/

/-!
## The direct structure's annotated Π-bits are exact

The tower leaves' folds need the annotated Π-types' codomain bits
*exactly*: the type former's parameter binders carry a nonzero bit
(their codomains end in `Sort w`, of sort `succ w`), the constructor's
and recursor's binders carry a bit that is zero exactly when the
result sort (resp. the elimination sort) evaluates to zero.  Validity
(`AnnotValid`) is one-directional — a zero bit at an empty-domain
codomain is valid — so the content is *syntactic*: in verified mode
`inferTypeCore`'s `.forallE` clause validates `zeronessOf v ==
mb.pw` against the opened body's inferred sort `v`
(`inferTypeCore_forall_inv`), and `checkConstantVal` runs that
inference on the annotated type.  This module walks the Π-prefix
(`piBits_of_infer`), pins the innermost sort per block constant, and
reads the bits off the `denoteMeta` reading (`stripPisAV_bits`) — the
three walks (`checkConstantVal`, `openPisAtFvars`, `denoteMeta`) open
the binders with the same `fvar`s, so one predicate over the opening
(`PiBitsOpen`) serves all three.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta inferTypeCore ensureSortCore whnf openPisAtFvars)

variable {mode : CheckMode}

/-! ## Leaf clauses of the inference, inverted -/

theorem whnf_sort_eq {env : Env} {F d : Nat} {u : Level} {e' : Expr}
    (h : whnf mode env F d (.sort u) = .ok e') : e' = .sort u := by
  have h1 := ConLeche.whnf_mono (Nat.le_add_right F 2) h
  rw [ConLeche.whnf_sort] at h1
  exact (Except.ok.inj h1).symm

theorem ensureSortCore_sort_eq {env : Env} {F d : Nat} {u v : Level}
    (h : ensureSortCore mode env F d (.sort u) = .ok v) : v = u :=
  Expr.sort.inj (whnf_sort_eq (ConLeche.ensureSortCore_inv h))

theorem inferTypeCore_sort_inv {env : Env} {F d : Nat} {u : Level} {t : Expr}
    (h : inferTypeCore mode env F d (.sort u) = .ok t) :
    t = .sort (.succ u) := by
  match F, h with
  | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
  | F + 1, h =>
    rw [ConLeche.inferTypeCore_succ] at h
    simp only [ConLeche.inferBody, pure, Except.pure] at h
    exact (Except.ok.inj h).symm

/-- A run on an application spine carries a run on its head. -/
theorem inferTypeCore_mkAppN_fn_inv {env : Env} {F d : Nat} :
    ∀ (as : List Expr) {f t : Expr},
      inferTypeCore mode env F d (Expr.mkAppN f as) = .ok t →
      ∃ tf, inferTypeCore mode env F d f = .ok tf
  | [], _, t, h => ⟨t, h⟩
  | a :: as, f, t, h => by
    obtain ⟨tfa, hfa⟩ := inferTypeCore_mkAppN_fn_inv as (f := .app f a) h
    obtain ⟨tf, _, _, _, hf, -⟩ := ConLeche.inferTypeCore_app_inv' hfa
    exact ⟨tf, hf⟩

/-- **A spine into a sort**: applying a head whose type is a
Π-telescope of the spine's length ending in `Sort s` types at
`Sort s` — the sort carries no bound variables, so the per-argument
instantiations leave it alone. -/
theorem inferTypeCore_mkAppN_sort {env : Env} {F d : Nat} :
    ∀ (as : List Expr) {f ty : Expr} {bs : List (Expr × BinderMeta)}
      {s : Level} {t : Expr},
      inferTypeCore mode env F d f = .ok ty →
      ty.stripPis as.length = some (bs, .sort s) →
      inferTypeCore mode env F d (Expr.mkAppN f as) = .ok t →
      t = .sort s
  | [], f, ty, bs, s, t, hf, hst, h => by
    obtain rfl : ty = t := Except.ok.inj (hf.symm.trans h)
    simp only [List.length_nil, Expr.stripPis, Option.some.injEq,
      Prod.mk.injEq] at hst
    exact hst.2
  | a :: as, f, ty, bs, s, t, hf, hst, h => by
    obtain ⟨dom, body, mb, rfl⟩ :
        ∃ dom body mb, ty = .forallE dom body mb := by
      cases ty <;> first
        | exact ⟨_, _, _, rfl⟩
        | simp [Expr.stripPis] at hst
    obtain ⟨tfa, hfa⟩ := inferTypeCore_mkAppN_fn_inv as (f := .app f a) h
    obtain ⟨tf, ty', body', m', hf', hw, rfl, -⟩ :=
      ConLeche.inferTypeCore_app_inv' hfa
    obtain rfl : tf = .forallE dom body mb :=
      Except.ok.inj (hf'.symm.trans hf)
    obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (ConLeche.whnf_forallE_eq hw)
    simp only [List.length_cons, Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    have hsome := Expr.stripPis_instantiate1_isSome (v := a) as.length
      (e := body') 0 (by rw [hst']; rfl)
    obtain ⟨⟨bs'', body''⟩, hst''⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hb, -⟩ := Expr.stripPis_instantiate1_eq (v := a) as.length 0
      hst' hst''
    rw [Expr.instantiate1_sort] at hb
    subst hb
    exact inferTypeCore_mkAppN_sort as hfa hst'' h

/-! ## The opening walk -/

/-- The first `n` binders of `e`, opened from depth `d` with the
inference's own `fvar`s, each codomain bit zero exactly when `z`. -/
def PiBitsOpen (φ : Name → Nat) (z : Prop) : Nat → Nat → Expr → Prop
  | 0, _, _ => True
  | n + 1, d, .forallE dom body mb =>
    (pwBit φ mb.pw = 0 ↔ z) ∧
      PiBitsOpen φ z n (d + 1) (body.instantiate1 (.fvar d dom))
  | _ + 1, _, _ => False

theorem eval_imax_eq_zero_iff (φ : Name → Nat) (l r : Level) :
    Level.eval φ (.imax l r) = 0 ↔ Level.eval φ r = 0 := by
  simp only [Level.eval]
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun h' => absurd (Nat.max_eq_zero_iff.mp h').2 h, fun h' => absurd h' h⟩

/-- **The Π-prefix walk**: in verified mode, the first `n` binders'
bits of an inferred type are exact against the innermost opened
body's inferred sort, and the whole type's sort is zero exactly when
that one is (`imax`'s zero-ness is its right argument's). -/
theorem piBits_of_infer {env : Env} (hver : mode.verifiedChecks = true) :
    ∀ (n : Nat) {F d : Nat} {e t : Expr} {v₀ : Level} {fvs : List Expr}
      {opened : Expr},
      openPisAtFvars n e d = some (fvs, opened) →
      inferTypeCore mode env F d e = .ok t →
      ensureSortCore mode env F d t = .ok v₀ →
      ∃ (F' : Nat) (tb : Expr) (vb : Level),
        inferTypeCore mode env F' (d + n) opened = .ok tb ∧
        ensureSortCore mode env F' (d + n) tb = .ok vb ∧
        (∀ φ, Level.eval φ v₀ = 0 ↔ Level.eval φ vb = 0) ∧
        ∀ φ, PiBitsOpen φ (Level.eval φ vb = 0) n d e
  | 0, F, d, e, t, v₀, fvs, opened, hop, h, hens => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    exact ⟨F, t, v₀, h, hens, fun _ => Iff.rfl, fun _ => trivial⟩
  | n + 1, F, d, e, t, v₀, fvs, opened, hop, h, hens => by
    match e, hop, h with
    | .forallE dom body mb, hop, h =>
      match F, h with
      | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
      | F + 1, h =>
        obtain ⟨tty, u, bt, v, -, -, hbt, hensb, hz, rfl⟩ :=
          ConLeche.inferTypeCore_forall_inv h
        simp only [openPisAtFvars] at hop
        split at hop
        · next fvs' e' hop' =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨-, rfl⟩ := hop
          obtain ⟨F', tb, vb, hrun, hensb', hv, hbits⟩ :=
            piBits_of_infer hver n hop' hbt hensb
          refine ⟨F', tb, vb, ?_, ?_, ?_, ?_⟩
          · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hrun
          · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hensb'
          · intro φ
            rw [ensureSortCore_sort_eq hens, eval_imax_eq_zero_iff]
            exact hv φ
          · intro φ
            refine ⟨?_, hbits φ⟩
            rw [← hz hver]
            exact (pwBit_zeronessOf φ _).trans (hv φ)
        · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _, hop, _ | .sort _, hop, _
    | .const _ _, hop, _ | .app _ _, hop, _ | .lam _ _ _, hop, _
    | .letE _ _ _, hop, _ | .lit _, hop, _ | .proj _ _ _, hop, _ =>
      simp [openPisAtFvars] at hop

/-! ## The bits, read -/

/-- The reading's Π-peel carries the syntactic bits: `denoteMeta` opens
with the same `fvar`s. -/
theorem stripPisAV_bits {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {z : Prop} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {ea : AnnotTerm}
      {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm},
      PiBitsOpen φ z n d e → denoteMeta acval env φ d e = some ea →
      stripPisAV n ea = some (pps, b) →
      ∀ p ∈ pps, (p.2.1 = 0 ↔ z)
  | 0, d, e, ea, pps, b, _, _, hst => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hst
    intro p hp
    exact absurd hp (by simp)
  | n + 1, d, e, ea, pps, b, hbits, hden, hst => by
    match e, hbits with
    | .forallE dom body mb, ⟨hhead, htail⟩ =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hden
      simp only [stripPisAV, Option.map_eq_some_iff] at hst
      obtain ⟨⟨pps', b'⟩, hst', heq⟩ := hst
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hhead
      · exact stripPisAV_bits n htail hba hst' p hp
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      exact h.elim

/-! ## `openPisAtFvars` bookkeeping -/

/-- Two consecutive openings are one. -/
theorem openPisAtFvars_add :
    ∀ (n : Nat) {m : Nat} {e : Expr} {d : Nat} {fvs fvs' : List Expr}
      {o o' : Expr},
      openPisAtFvars n e d = some (fvs, o) →
      openPisAtFvars m o (d + n) = some (fvs', o') →
      openPisAtFvars (n + m) e d = some (fvs ++ fvs', o')
  | 0, m, e, d, fvs, fvs', o, o', h, h' => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using h'
  | n + 1, m, e, d, fvs, fvs', o, o', h, h' => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h'' := openPisAtFvars_add n h₁
          (by rw [show d + 1 + n = d + (n + 1) from by omega]; exact h')
        rw [show n + 1 + m = n + m + 1 from by omega]
        simp only [openPisAtFvars]
        rw [h'']
        rfl
      · exact nomatch h
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

/-- Opening a telescope whose stripped body is a sort reaches that
sort (sorts carry no bound variables). -/
theorem openPisAtFvars_of_stripPis_sort :
    ∀ (n : Nat) {e : Expr} (d : Nat) {bs : List (Expr × BinderMeta)}
      {s : Level},
      e.stripPis n = some (bs, .sort s) →
      ∃ fvs, openPisAtFvars n e d = some (fvs, .sort s)
  | 0, e, d, bs, s, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by rw [h.2]; rfl⟩
  | n + 1, e, d, bs, s, h => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      have hsome := Expr.stripPis_instantiate1_isSome
        (v := .fvar d dom) n (e := body) 0 (by rw [hst']; rfl)
      obtain ⟨⟨bs'', body''⟩, hst''⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hb, -⟩ := Expr.stripPis_instantiate1_eq
        (v := .fvar d dom) n 0 hst' hst''
      rw [Expr.instantiate1_sort] at hb
      subst hb
      obtain ⟨fvs, hop⟩ := openPisAtFvars_of_stripPis_sort n (d + 1) hst''
      refine ⟨Expr.fvar d dom :: fvs, ?_⟩
      show (match openPisAtFvars n (body.instantiate1 (.fvar d dom)) (d + 1)
          with
        | some (fvs, e) => some (Expr.fvar d dom :: fvs, e)
        | none => none) = _
      rw [hop]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h


/-!
## `CapsOk` across the direct block's member conses

The block's three non-entry conses — the former, the constructor and
the recursor — are exactly the head kinds `capsOk_cons_fresh`
refutes, because a head of those kinds can *complete* a stored family
(`EtaFamilyStored`).  Here the only family a block cons can complete
is the block's own (`T`): every other stored family's capability
constructor is stored already (the fold's `EtaFamiliesClosed` at the
pre-block environment), and its projection-function slots are
projection-shaped names a block constant never carries.  So the
prefix families' laws cross as at any fresh cons, and the block's
own family's laws are the install's premise.
-/


open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  projFnName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

theorem projFnName_isProjFnShape (T : Name) (j : Nat) :
    (projFnName T j).isProjFnShape = true := rfl

/-- **The block's own capability laws at a carrier** (task #210 Part
A): what `capsOk_cons_native` asks of the family being installed at
each of its conses — the η law where the family claims η and is
stored complete, the unit law where it claims unit-likeness.  A stage
takes it as a hypothesis about the carrier it builds; the assembly
discharges it from the leaves (or vacuously: `capsLawsAt_of_none`,
`capsLawsAt_vacuous`). -/
@[expose] def CapsLawsAt {env : Env} (m : EnvModel V env) (T : Name) (cvT : ConstantVal)
    (caps : IndCaps) : Prop :=
  (caps.eta = true → ConLeche.EtaFamilyStored env T caps →
    ∀ φ' : Name → Nat, EtaLaw m φ' T cvT caps) ∧
  (caps.unitlike = true → ∀ φ' : Name → Nat, UnitLaw m φ' T cvT caps)

/-- A record claiming η at a family with a field and no unit-likeness
owes nothing while its projection-function family is free: the η
half's premise `EtaFamilyStored` stores a projection function at every
field, and the first slot is fresh. -/
theorem capsLawsAt_vacuous {env : Env} (m : EnvModel V env) {T : Name} {cvT : ConstantVal}
    {caps : IndCaps} (hU : caps.unitlike = false)
    (hE : caps.eta = true → 0 < caps.etaFields ∧ env.find? (projFnName T 0) = none) :
    CapsLawsAt m T cvT caps := by
  refine ⟨fun he hfam => ?_, fun hu => absurd (hU.symm.trans hu) Bool.false_ne_true⟩
  exfalso
  obtain ⟨hpos, hfresh⟩ := hE he
  obtain ⟨-, -, hslots⟩ := hfam
  obtain ⟨cv, mI, rP, rules, hf⟩ := hslots 0 hpos
  rw [hfresh] at hf
  exact nomatch hf

/-- A family whose capability constructor is stored in the prefix does
not have this cons's head as that constructor — `hother`'s shape at a
route where every other stored family is CLOSED. -/
theorem etaCtor_ne_of_closed {env : Env} {c₀ : ConstantInfo} {caps' : IndCaps}
    (hfresh : env.find? c₀.name = none)
    (h : ∃ cvC', env.find? caps'.etaCtor
      = some (.ctorInfo cvC' caps'.etaParams caps'.etaFields)) :
    caps'.etaCtor ≠ c₀.name := by
  obtain ⟨cvC', hfC'⟩ := h
  intro hh
  rw [hh, hfresh] at hfC'
  exact nomatch hfC'

/-- **`CapsOk` at a block-member cons.**  The head is fresh, not
projection-shaped, and either the block's former itself or not an
inductive at all; every other stored family's capability constructor
is NOT this head (`hother`, which may consume the family's storedness
AT THE EXTENSION — so that a block's still-pending members are refuted
from the head's KIND rather than from closure); the block's own
family's laws at the extension are supplied (`hTlaws`). -/
theorem capsOk_cons_native (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm} {T : Name}
    (hfresh : env.find? c₀.name = none)
    (hcross : ConsCrossEnv env c₀)
    (hpshape : c₀.name.isProjFnShape = false)
    (hkind : (∃ cvT caps, c₀ = .indInfo cvT caps ∧ c₀.name = T) ∨
      ∀ cv caps, c₀ ≠ .indInfo cv caps)
    (hother : ∀ (T' : Name) (cvT' : ConstantVal) (caps' : IndCaps),
      env.find? T' = some (.indInfo cvT' caps') → T' ≠ T →
      ConLeche.reservedBasisNames.contains T' = false →
      caps'.eta = true →
      ConLeche.EtaFamilyStored ⟨c₀ :: env.consts⟩ T' caps' →
      caps'.etaCtor ≠ c₀.name)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    (hTlaws : ∀ (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      ConLeche.reservedBasisNames.contains T = false →
      (caps.eta = true → ConLeche.EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
        ∀ φ' : Name → Nat, EtaLaw m₂ φ' T cvT caps) ∧
      (caps.unitlike = true → ∀ φ' : Name → Nat, UnitLaw m₂ φ' T cvT caps)) :
    CapsOk m₂ := by
  -- a stored family other than the block's is a prefix lookup
  have hdown : ∀ n : Name, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [ConLeche.Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  have hneT : ∀ (T' : Name) (cvT' : ConstantVal) (caps' : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T' = some (.indInfo cvT' caps') →
      T' ≠ T → T' ≠ c₀.name := by
    intro T' cvT' caps' hf hne hh
    rcases hkind with ⟨cvT₀, caps₀, rfl, hname⟩ | hnotind
    · exact hne (hh.trans hname)
    · rw [hh, ConLeche.Env.find?_cons_self] at hf
      exact hnotind cvT' caps' (Option.some.inj hf)
  constructor
  · -- the η half
    intro T' cvT' caps' hf hcape hres hfam φ' us hlen
    by_cases hTT : T' = T
    · subst hTT
      exact (hTlaws cvT' caps' hf hres).1 hcape hfam φ' us hlen
    have hnT' : T' ≠ c₀.name := hneT T' cvT' caps' hf hTT
    have hfE : env.find? T' = some (.indInfo cvT' caps') := by
      rwa [hdown _ hnT'] at hf
    -- the family's names are all prefix lookups
    have hnC : caps'.etaCtor ≠ c₀.name := hother T' cvT' caps' hfE hTT hres hcape hfam
    have hnP : ∀ j, j < caps'.etaFields → projFnName T' j ≠ c₀.name := by
      intro j _ hh
      have := projFnName_isProjFnShape T' j
      rw [hh, hpshape] at this
      exact nomatch this
    have hfam₀ : ConLeche.EtaFamilyStored env T' caps' := by
      obtain ⟨hCres, ⟨cvC'', hfC''⟩, hfP⟩ := hfam
      refine ⟨hCres, ⟨cvC'', by rwa [hdown _ hnC] at hfC''⟩, ?_⟩
      intro j hj
      obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
      exact ⟨cv2, mI2, rP2, rules2, by rwa [hdown _ (hnP j hj)] at hf2⟩
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      mp.caps_ok.1 T' cvT' caps' hfE hcape hres hfam₀ φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_mono hfresh
        ((hcross.typeOf hfE).instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x hlents hfit hmem
      rw [hac, acvalWith_ne hnT'] at hmem
      have hfab : etaFabArgsV
            (fun n => interp V ρ
              (m₂.acval n (Level.substFn φ' cvT'.levelParams us)))
            T' ts x caps'.etaFields
          = etaFabArgsV
            (fun n => interp V ρ
              (mp.base2.acval n (Level.substFn φ' cvT'.levelParams us)))
            T' ts x caps'.etaFields := by
        unfold etaFabArgsV projSpines
        refine congrArg _ (List.map_congr_left fun j hj => ?_)
        dsimp only
        rw [hac, acvalWith_ne (hnP j (List.mem_range.mp hj))]
      rw [hfab, hac, acvalWith_ne hnC]
      exact hlaw ρ ts rest x hlents hfit hmem
  · -- the unit-like half
    intro T' cvT' caps' hf hcapu hres φ' us hlen
    by_cases hTT : T' = T
    · subst hTT
      exact (hTlaws cvT' caps' hf hres).2 hcapu φ' us hlen
    have hnT' : T' ≠ c₀.name := hneT T' cvT' caps' hf hTT
    have hfE : env.find? T' = some (.indInfo cvT' caps') := by
      rwa [hdown _ hnT'] at hf
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      mp.caps_ok.2 T' cvT' caps' hfE hcapu hres φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_mono hfresh
        ((hcross.typeOf hfE).instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x y hlents hfit hmx hmy
      rw [hac, acvalWith_ne hnT'] at hmx hmy
      exact hlaw ρ ts rest x y hlents hfit hmx hmy


/-!
## The direct structure's readings

The P install of a direct structure reads its four stored types (the
former's, the constructor's, the recursor's, each entry's) at the
stage environments, and peels the Π-prefixes into the binder data the
tower leaves are built over.  Two syntactic facts carry the module:

* **The unmentioned leaf** (`denoteMeta_acvalWith_unmentioned`): a term
  whose constants all resolve in the pre-block environment reads the
  same under any leaf at the block's name.  The type former's
  parameter domains and the constructor's field domains are such
  terms (`checkConstantVal` at `env₀`, resp. the constructor stage's
  `constsResolve env₀` re-check), so their readings — the leaves'
  ingredients — are fixed before the leaves are, which is what lets
  the former's leaf mention them without circularity.

* **The reading peel** (`denoteMeta_openPis`): `denoteMeta` opens a Π-prefix
  with the very `fvar`s `openPisAtFvars` does, so a type's reading
  strips (`stripPisAV`) to the per-binder readings of the opened
  variables' annotations, each at its own depth.
-/


open ConLeche ConLeche.Semantics ConLeche.Verify ConLeche.SetModel

/-! ## The unmentioned leaf -/

/-- **The names a reading of `e` looks up satisfy `P`**: its constants,
and — at a literal the environment supports — the support constants
the literal's reading consults.  (`fvar` annotations are never read.) -/
@[expose] def Expr.ReadsAt (P : Name → Prop) (env : Env) : Expr → Prop
  | .const n _ => P n
  | .app f a => Expr.ReadsAt P env f ∧ Expr.ReadsAt P env a
  | .lam ty b _ => Expr.ReadsAt P env ty ∧ Expr.ReadsAt P env b
  | .forallE ty b _ => Expr.ReadsAt P env ty ∧ Expr.ReadsAt P env b
  | .proj _ _ e => Expr.ReadsAt P env e
  | .lit (.natVal _) => natLitSupported env = true → P natZeroName ∧ P natSuccName
  | .lit (.strVal _) => strLitSupported env = true →
      P stringOfListName ∧ P listNilName ∧ P listConsName ∧ P charName ∧ P charOfNatName ∧
        P natZeroName ∧ P natSuccName
  | _ => True

/-- Opening at a variable keeps the looked-up names. -/
theorem Expr.ReadsAt.instantiate1 {P : Name → Prop} {env : Env} {v : Expr}
    (hv : Expr.ReadsAt P env v) :
    ∀ (e : Expr) (k : Nat), Expr.ReadsAt P env e → Expr.ReadsAt P env (e.instantiate1 v k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> trivial
  | app f a ihf iha => intro k h; exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b m iht ihb => intro k h; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE t b m iht ihb => intro k h; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | proj s i e ihe => intro k h; exact ihe k h
  | letE => intro _ _; trivial
  | _ => intro _ h; exact h

/-- **A reading consults the leaves only at the names it looks up**: two
leaf assignments agreeing there read `e` alike (the two runs are `none`
together). -/
theorem denoteMeta_agree_of_readsAt
    {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}
    {P : Name → Prop} (hag : ∀ n, P n → acval₁ n = acval₂ n) :
    ∀ (d : Nat) (e : Expr), Expr.ReadsAt P env e →
      denoteMeta acval₁ env φ d e = denoteMeta acval₂ env φ d e := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u => intro _; rw [denoteMeta, denoteMeta]
  | case2 d idx ty => intro _; rw [denoteMeta, denoteMeta]
  | case3 d n us ci hf hlen =>
    intro hcr
    rw [denoteMeta, denoteMeta, hf]
    dsimp only
    rw [if_pos hlen, if_pos hlen, hag n hcr]
  | case4 d n us ci hf hlen =>
    intro _
    rw [denoteMeta, denoteMeta, hf]
    dsimp only
    rw [if_neg hlen, if_neg hlen]
  | case5 d n us hf => intro _; rw [denoteMeta, denoteMeta, hf]
  | case6 d ty body m ihty ihbody =>
    intro hcr
    rw [denoteMeta, denoteMeta, ihty hcr.1,
      ihbody (Expr.ReadsAt.instantiate1 (v := .fvar d ty) (by simp [Expr.ReadsAt]) _ 0 hcr.2)]
  | case7 d ty body m ihty ihbody =>
    intro hcr
    rw [denoteMeta, denoteMeta, ihty hcr.1,
      ihbody (Expr.ReadsAt.instantiate1 (v := .fvar d ty) (by simp [Expr.ReadsAt]) _ 0 hcr.2)]
  | case8 d f a ihf iha =>
    intro hcr
    rw [denoteMeta, denoteMeta, ihf hcr.1, iha hcr.2]
  | case9 d ty val body =>
    intro _
    rw [denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    intro hcr
    rw [denoteMeta, denoteMeta, ihe hcr]
  | case11 d n hsup =>
    intro hcr
    obtain ⟨hZ, hS⟩ := hcr hsup
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup, hag natZeroName hZ,
      hag natSuccName hS]
  | case12 d n hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    intro hcr
    obtain ⟨hO, hN, hC, hH, hF, hZ, hS⟩ := hcr hsup
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup,
      hag stringOfListName hO, hag listNilName hN, hag listConsName hC,
      hag charName hH, hag charOfNatName hF, hag natZeroName hZ, hag natSuccName hS]
  | case14 d s hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)


/-! ## The reading peel -/

/-- **The peel.**  A Π-prefix opened at `fvar`s reads to a
`stripPisAV`-strippable reading whose binder data are the opened
variables' annotation readings at their own depths (domain sort
numeral `0`, the codomain bit the binder's own), and whose residual is
the opened body's reading at the full depth. -/
theorem denoteMeta_openPis {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
      {ea : AnnotTerm},
      openPisAtFvars n e d = some (fvs, o) →
      denoteMeta acval env φ d e = some ea →
      ∃ (pps : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm),
        stripPisAV n ea = some (pps, b) ∧
        denoteMeta acval env φ (d + n) o = some b ∧
        pps.length = n ∧
        ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
          ∃ p, pps[i]? = some p ∧ p.1 = 0 ∧
            denoteMeta acval env φ (d + i) x.fvarTypeD = some p.2.2
  | 0, d, e, fvs, o, ea, hop, hden => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨[], ea, rfl, by simpa using hden, rfl,
      fun i x hx => by simp at hx⟩
  | n + 1, d, e, fvs, o, ea, hop, hden => by
    match e, hop with
    | .forallE dom body mb, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hden
        obtain ⟨pps, b, hst, hb, hlen, hbind⟩ := denoteMeta_openPis n hop' hba
        refine ⟨(0, pwBit φ mb.pw, ta) :: pps, b, ?_, ?_, ?_, ?_⟩
        · simp only [stripPisAV, hst, Option.map_some]
        · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hb
        · simp [hlen]
        · intro i x hx
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
            subst hx
            exact ⟨(0, pwBit φ mb.pw, ta), rfl, rfl,
              by rw [Nat.add_zero]; exact hta⟩
          | succ i =>
            simp only [List.getElem?_cons_succ] at hx
            obtain ⟨p, hp, hp1, hpd⟩ := hbind i x hx
            exact ⟨p, by simpa using hp, hp1,
              by rw [show d + (i + 1) = d + 1 + i from by omega]; exact hpd⟩
      · exact nomatch hop
    | .bvar _, hop | .fvar _ _, hop | .sort _, hop | .const _ _, hop
    | .app _ _, hop | .lam _ _ _, hop | .letE _ _ _, hop | .lit _, hop
    | .proj _ _ _, hop =>
      simp [openPisAtFvars] at hop


/-!
## The direct structure's opened frames

The direct install's stage checks run **at opened frames**: each
binder-domain comparison (`checkStructDomsAt`), each field's sort
inference (`checkStructFieldSorts`) and the recursor's pins run at the
depth of the binder they concern, over the variables `openPisAtFvars`
created for the earlier binders.  The claims interface
(`Model/Claims.lean`) answers such a run at a context `Δa` that
correlates with the run's subject (`CtxOk`) and is satisfied by the
valuations the conclusion is drawn at (`Sat`).  This module builds
those contexts from a type's reading:

* the **telescope grading** (`piTeleAV_graded`): the reading's own
  grading descends the `.pi` tower — each domain is graded at every
  valuation satisfying the earlier domains, in `Sat`-of-`drop` form;
* the **opened context** (`ctxOk_opened`): any well-scoped term over
  the opening's variables correlates with the reading's context at its
  depth;
* the **context transfer** (`CtxOk.transfer`, `Sat2_of_entries_eq`):
  two contexts whose entries interpret alike under the earlier entries
  are interchangeable — how the type former's and the constructor's
  parameter frames, opened at their own variables and pinned
  definitionally binder by binder, are identified.

The tower leaves' premises (`ParamsOkT`, `MkPre`, `RecPre`) walk the
same frames in `cons` form; `Sat_cons`/`Sat_cons_inv` are the
bridge, one binder at a time.
-/


open ConLeche ConLeche.Semantics ConLeche.Verify SetTheory ConLeche.SetModel


variable {V : Type w} [SetTheory V]

/-! ## `Sat` bookkeeping -/

omit [SetTheory V] in
theorem cons_eta (ρ : Nat → V) : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
  funext i
  cases i <;> rfl

theorem Sat_cons_inv {Δ : List AnnotTerm} {A : AnnotTerm} {ρ : Nat → V}
    (h : Sat V (A :: Δ) ρ) :
    ρ 0 ∈ˢ interp V (fun j => ρ (j + 1)) A ∧
      Sat V Δ (fun j => ρ (j + 1)) :=
  ⟨by have := h 0 A rfl; simpa using this, Sat_tail h⟩

/-- **Context transfer**: a correspondence survives replacing the
context by one with the same satisfying valuations whose entries
interpret alike under them. -/
theorem CtxOk.transfer {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {d : Nat} {Δ₁ Δ₂ : List AnnotTerm} {b : Expr}
    (h : CtxOk m φ d Δ₁ b) (hlen : Δ₂.length = d)
    (hsat : ∀ ρ : Nat → V, Sat V Δ₂ ρ → Sat V Δ₁ ρ)
    (hent : ∀ (p : Nat) (A₁ A₂ : AnnotTerm), Δ₁[p]? = some A₁ →
      Δ₂[p]? = some A₂ → ∀ ρ : Nat → V, Sat V Δ₂ ρ →
        interp V (fun j => ρ (j + p + 1)) A₁
          = interp V (fun j => ρ (j + p + 1)) A₂) :
    CtxOk m φ d Δ₂ b := by
  obtain ⟨hlen₁, hleaf⟩ := h
  refine ⟨hlen, ?_⟩
  intro l hl
  obtain ⟨hlt, hfb, tya, A₁, hty, hA₁, heq, hok⟩ := hleaf l hl
  have hpl : d - 1 - l.1 < Δ₂.length := by omega
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, Δ₂[d - 1 - l.1]? = some A₂ :=
    ⟨Δ₂[d - 1 - l.1]'hpl, List.getElem?_eq_getElem hpl⟩
  refine ⟨hlt, hfb, tya, A₂, hty, hA₂, ?_, fun ρ hρ => hok ρ (hsat ρ hρ)⟩
  intro ρ hρ
  rw [heq ρ (hsat ρ hρ), hent _ A₁ A₂ hA₁ hA₂ ρ hρ]

/-! ## The telescope grading -/

/-- **The reading's grading descends its `.pi` tower**: domain `i`
(outermost first) is graded at every valuation satisfying the earlier
domains, and the core at every valuation satisfying them all. -/
theorem piTeleAV_graded :
    ∀ {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R →
      ∀ {Δ₀ : List AnnotTerm},
        (∀ ρ : Nat → V, Sat V Δ₀ ρ → WellDenotedV V ρ T) →
        (∀ i, i < k → ∀ ρ : Nat → V, Sat V (Γ.drop (k - i) ++ Δ₀) ρ →
          WellDenotedV V ρ (Γ.getD (k - 1 - i) default)) ∧
        (∀ ρ : Nat → V, Sat V (Γ ++ Δ₀) ρ → WellDenotedV V ρ R) := by
  intro k T Γ R h
  induction h with
  | nil =>
    intro Δ₀ hT
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun ρ hρ => hT ρ hρ⟩
  | @cons k u v A B R Γ' h ih =>
    intro Δ₀ hT
    have hlen : Γ'.length = k := h.length
    have hB : ∀ ρ : Nat → V, Sat V (A :: Δ₀) ρ → WellDenotedV V ρ B := by
      intro ρ hρ
      obtain ⟨h0, htl⟩ := Sat_cons_inv hρ
      have := WellDenotedV_pi_body (hT _ htl) h0
      rwa [cons_eta] at this
    obtain ⟨ih1, ih2⟩ := ih hB
    refine ⟨?_, ?_⟩
    · intro i hi ρ hρ
      cases i with
      | zero =>
        rw [Nat.sub_zero, show k + 1 = (Γ' ++ [A]).length from by
          simp [hlen], List.drop_length, List.nil_append] at hρ
        rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
          simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
          rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
          rfl]
        exact WellDenotedV_pi_dom (hT ρ hρ)
      | succ i =>
        rw [show k + 1 - (i + 1) = k - i from by omega,
          List.drop_append_of_le_length (by omega), List.append_assoc,
          List.singleton_append] at hρ
        rw [show (Γ' ++ [A]).getD (k + 1 - 1 - (i + 1)) default
            = Γ'.getD (k - 1 - i) default from by
          simp only [List.getD]
          rw [show k + 1 - 1 - (i + 1) = k - 1 - i from by omega,
            List.getElem?_append_left (by omega)]]
        exact ih1 i (by omega) ρ hρ
    · intro ρ hρ
      rw [List.append_assoc, List.singleton_append] at hρ
      exact ih2 ρ hρ

/-! ## The opened context -/

/-- **`CtxOk` at an opening's frame**: a term well-scoped at depth
`i ≤ k` over the opening's variables correlates with the reading's
context at that depth (`Γ.drop (k - i)` — the earlier domains,
innermost first). -/
theorem ctxOk_opened {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {k : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars k e 0 = some (fvs, o)) (hcl : e.hasFvar = false)
    {Γ : List AnnotTerm} (hΓ : Γ.length = k)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (Γ.getD (k - 1 - i) default))
    (hokΓ : ∀ i, i < k → ∀ ρ : Nat → V, Sat V (Γ.drop (k - i)) ρ →
      WellDenotedV V ρ (Γ.getD (k - 1 - i) default))
    {i : Nat} (hik : i ≤ k) {x : Expr} (hwx : Expr.WScoped i x)
    (hleaf : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) :
    CtxOk m φ i (Γ.drop (k - i)) x := by
  have hidx := openPisAtFvars_index k e 0 hop
  have hlenF : fvs.length = k := openPisAtFvars_length k hop
  have hws := (openPisAtFvars_WScoped k e 0 hop
    (Expr.WScoped.of_not_hasFvar hcl)).1
  -- the positions of the variables a leaf can be
  have hpos : ∀ l ∈ x.fvarLeaves, fvs[l.1]? = some (Expr.fvar l.1 l.2) := by
    intro l hl
    obtain ⟨p, hp⟩ := List.getElem?_of_mem (hleaf l hl)
    obtain ⟨ty, hx⟩ := hidx p _ hp
    rw [Nat.zero_add] at hx
    obtain ⟨rfl, -⟩ : l.1 = p ∧ l.2 = ty := by
      injection hx with a b
      exact ⟨a, b⟩
    exact hp
  refine ctxOk_of_openers m.acval_closed (fvs := fvs.take i)
    (Aa := fun j => Γ.getD (k - 1 - j) default) (Δa := Γ.drop (k - i))
    (by rw [List.length_drop]; omega) ?_ ?_ ?_ (e := x) (n := i) ?_
    (Expr.fvarLeaves_lt_of_wscoped hwx) ?_ ?_
  · intro j y hy
    have hj : j < i := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hj] at hy
    obtain ⟨ty, hx⟩ := hidx j y hy
    exact ⟨ty, by rw [hx, Nat.zero_add]⟩
  · intro y hy
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hy
    have hji : j < i := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hji] at hj
    obtain ⟨ty, rfl⟩ := hidx j y hj
    have hw := hws _ (List.mem_of_getElem? hj)
    rw [Nat.zero_add] at hw ⊢
    simp only [Expr.WScoped, Nat.zero_add] at hw ⊢
    exact ⟨hji, hw.2⟩
  · intro j y hy
    have hj : j < i := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hj] at hy
    exact hdoms j y hy
  · intro l hl
    have hlt := Expr.fvarLeaves_lt_of_wscoped hwx l hl
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hpos l hl)
  · intro j hj
    rw [List.getElem?_drop, show k - i + (i - 1 - j) = k - 1 - j from by omega]
    have hjl : k - 1 - j < Γ.length := by omega
    rw [List.getD, List.getElem?_eq_getElem hjl]
    rfl
  · intro j hj ρ hρ
    have hd := Sat_drop hρ (i - j)
    rw [List.drop_drop, show k - i + (i - j) = k - j from by omega] at hd
    have e : (fun l => ρ (l + (i - 1 - j) + 1)) = fun l => ρ (l + (i - j)) := by
      funext l; congr 1; omega
    rw [e]
    exact hokΓ j (by omega) _ hd


/-!
## The direct structure's stage runs, as rows

The claims a P carrier answers at one fuel and assignment
(`ClaimsAt`), the three row shapes the direct install reads off them
(inference, sort, definitional equality — each at a context), and
**the opened type** (`opened_of`): a closed, graded type opened at
its own variables yields its `.pi` context, the per-binder readings,
the hereditary gradings and the `CtxOk` correspondences at every
depth — everything a stage's frame walk consumes, in one record.
-/


variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The claims at one fuel -/

/-- The claims a P carrier answers at fuel `F` and assignment `φ`. -/
structure ClaimsAt (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (F : Nat) : Prop where
  whnf : WhnfClaim μ m φ F
  defeq : DefEqClaim μ m φ F
  infer : InferClaim μ m φ F
  reads : InferReads m μ φ F
  sort : SortSemAt m μ φ F

/-- A P carrier answers them (the sealed capstone). -/
theorem claimsAt_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    (φ : Name → Nat) (F : Nat) : ClaimsAt μ mp.base2 φ F :=
  have h := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp φ) F
  have hr : InferReads mp.base2 μ φ F :=
    inferReads_of hμ (Rules.RulesInputs.ofSem mp φ)
  ⟨h.2.1, h.2.2.1, h.2.2.2, hr, sortSemAt_of_claims h.2.1 h.2.2.2 hr⟩

namespace ClaimsAt

variable {m : EnvModel V env} {F : Nat}

/-- An inference run at a context: the type reads, both readings are
graded, and the subject inhabits the type. -/
theorem inferRow (hc : ClaimsAt μ m φ F) {d : Nat} {e t : Expr}
    {Δ : List AnnotTerm} {ea : AnnotTerm}
    (hi : inferTypeCore μ env F d e = .ok t)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e) (hC : CtxOk m φ d Δ e)
    (hea : denoteMeta m.acval env φ d e = some ea) :
    ∃ ta, denoteMeta m.acval env φ d t = some ta ∧
      (∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ ea) ∧
      (∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨ta, hta⟩ := hc.reads hi hws hb hL hC hea
  obtain ⟨h1, h2, h3⟩ := hc.infer hi hws hb hL hC hea hta
  exact ⟨ta, hta, h1, h2, h3⟩

/-- An inference run whose type is a sort: the subject is graded and
lands in that universe. -/
theorem sortRow (hc : ClaimsAt μ m φ F) {d : Nat} {e t : Expr} {u : Level}
    {Δ : List AnnotTerm} {ea : AnnotTerm}
    (hi : inferTypeCore μ env F d e = .ok t)
    (hens : ensureSortCore μ env F d t = .ok u)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e) (hC : CtxOk m φ d Δ e)
    (hea : denoteMeta m.acval env φ d e = some ea) :
    ∀ ρ : Nat → V, Sat V Δ ρ →
      WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V) :=
  hc.sort hC hws hb hL hi (ConLeche.ensureSortCore_inv hens) hea

/-- A definitional-equality run at a context: the readings interpret
alike. -/
theorem defEqRow (hc : ClaimsAt μ m φ F) {d : Nat} {a b : Expr}
    {Δ : List AnnotTerm} {aa ba : AnnotTerm}
    (h : ConLeche.isDefEqCore μ env F d a b = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b)
    (hCa : CtxOk m φ d Δ a) (hCb : CtxOk m φ d Δ b)
    (haa : denoteMeta m.acval env φ d a = some aa)
    (hbA : denoteMeta m.acval env φ d b = some ba)
    (hoka : ∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ aa)
    (hokb : ∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ ba) :
    ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ aa = interp V ρ ba :=
  hc.defeq h hwa hba hLa hwb hbb hLb hCa hCb haa hbA hoka hokb

end ClaimsAt

/-! ## The opened type -/

/-- **The opened type record**: a closed, bounded type with a graded
reading, opened at its own variables. -/
structure Opened {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (k : Nat) (e : Expr) (fvs : List Expr) (o : Expr)
    (Γ : List AnnotTerm) (R : AnnotTerm) : Prop where
  /-- the context has one entry per binder -/
  len : Γ.length = k
  /-- the opened body reads to the core at depth `k` -/
  body : denoteMeta m.acval env φ k o = some R
  /-- each variable's annotation reads to its entry at its own depth -/
  doms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
    denoteMeta m.acval env φ i (Expr.fvarTypeD x)
      = some (Γ.getD (k - 1 - i) default)
  /-- the entries are graded under the earlier ones -/
  okΓ : ∀ i, i < k → ∀ ρ : Nat → V, Sat V (Γ.drop (k - i)) ρ →
    WellDenotedV V ρ (Γ.getD (k - 1 - i) default)
  /-- the core is graded under all of them -/
  okR : ∀ ρ : Nat → V, Sat V Γ ρ → WellDenotedV V ρ R
  /-- the variables are indexed by position, annotated at their own
  depth by bounded, leaf-bounded terms over the earlier variables -/
  var : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
    (∃ ty, x = Expr.fvar i ty) ∧
    Expr.WScoped i (Expr.fvarTypeD x) ∧
    (Expr.fvarTypeD x).looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded (Expr.fvarTypeD x) ∧
    ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs
  /-- the opened body is scoped at `k` over the variables -/
  bodyScoped : Expr.WScoped k o ∧ o.looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded o ∧
    ∀ l ∈ o.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs
  /-- any term over the variables correlates with the context at its
  depth -/
  ctx : ∀ {i : Nat}, i ≤ k → ∀ {x : Expr}, Expr.WScoped i x →
    (∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) →
    CtxOk m φ i (Γ.drop (k - i)) x

/-- The opened type record, from the opening, the closedness and the
reading's grading. -/
theorem opened_of {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {k : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars k e 0 = some (fvs, o)) (hcl : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    {T : AnnotTerm} (hT : denoteMeta m.acval env φ 0 e = some T)
    (hokT : ∀ ρ : Nat → V, WellDenotedV V ρ T) :
    ∃ (Γ : List AnnotTerm) (R : AnnotTerm),
      PiTeleAV k T Γ R ∧ Opened m φ k e fvs o Γ R := by
  obtain ⟨Γ, R, htele, hbody, hdoms⟩ := openPisAtFvars_denotePTele k hop hT
  have hlen : Γ.length = k := htele.length
  have hidx := openPisAtFvars_index k e 0 hop
  have hlenF : fvs.length = k := openPisAtFvars_length k hop
  obtain ⟨hwsF, hwsO⟩ := openPisAtFvars_WScoped k e 0 hop
    (Expr.WScoped.of_not_hasFvar hcl)
  obtain ⟨hbO, hbF⟩ := openPisAtFvars_bounded k hop hb
  have hleaves := openPisAtFvars_leaves k hop
  have hnil : e.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl
  -- a leaf reachable from the opening is an opener
  have hopener : ∀ l, (l ∈ o.fvarLeaves ∨ ∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvs := by
    intro l hl
    rcases hleaves l hl with h | h
    · rw [hnil] at h; exact absurd h List.not_mem_nil
    · exact h
  -- an opener's annotation is bounded and leaf-bounded
  have hLB : ∀ y ∈ fvs, Expr.LeavesBounded (Expr.fvarTypeD y) := by
    intro y hy l hl
    have hmem : Expr.fvar l.1 l.2 ∈ fvs := by
      refine hopener l (Or.inr ⟨y, hy, ?_⟩)
      obtain ⟨p, hp⟩ := List.getElem?_of_mem hy
      obtain ⟨ty, rfl⟩ := hidx p y hp
      simp only [Expr.fvarTypeD] at hl
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl
    have := hbF _ hmem
    simpa [Expr.fvarTypeD] using this
  obtain ⟨hgΓ, hgR⟩ := piTeleAV_graded (V := V) htele (Δ₀ := [])
    (fun ρ _ => hokT ρ)
  simp only [List.append_nil] at hgΓ hgR
  refine ⟨Γ, R, htele, ⟨hlen, by simpa using hbody, fun i x hx => by
    simpa using hdoms i x hx, hgΓ, hgR, ?_, ?_, ?_⟩⟩
  · intro i x hx
    have hik : i < k := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      omega
    obtain ⟨ty, rfl⟩ := hidx i x hx
    rw [Nat.zero_add] at *
    have hw := hwsF _ (List.mem_of_getElem? hx)
    simp only [Expr.WScoped] at hw
    refine ⟨⟨ty, rfl⟩, hw.2, ?_, hLB _ (List.mem_of_getElem? hx), ?_⟩
    · simpa [Expr.fvarTypeD] using hbF _ (List.mem_of_getElem? hx)
    · intro l hl
      refine hopener l (Or.inr ⟨_, List.mem_of_getElem? hx, ?_⟩)
      simp only [Expr.fvarTypeD] at hl
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl
  · refine ⟨by simpa using hwsO, hbO, ?_, fun l hl => hopener l (Or.inl hl)⟩
    intro l hl
    have hmem := hopener l (Or.inl hl)
    have := hbF _ hmem
    simpa [Expr.fvarTypeD] using this
  · intro i hik x hwx hleaf
    exact ctxOk_opened hop hcl hlen (fun i x hx => by simpa using hdoms i x hx)
      hgΓ hik hwx hleaf


/-!
## The direct structure's telescope walks

The tower leaves' hereditary premises (`ParamsOkT`, `MkPre`, `RecPre`,
`FieldsOkB`) walk a binder list in `cons` form; the opened-type record
(`Opened`) hands out gradings in `Sat`-of-`drop` form.  This module
bridges the two:

* `PiTeleAV.unique`/`piTeleAV_of_stripPisAV`: the `.pi` context of a
  reading is its `stripPisAV` peel reversed — the leaves are spelled
  over the peel, the frames over the context;
* `hereditaryWalk`: any predicate that descends one binder at a time
  (graded domain, then the tail under every member) holds along the
  peel from the reading's gradings and its base case at the full
  context;
* `fieldsOkB_of_frame`: the field chain's `FieldsOkB` from the
  gradings and the per-field bounds;
* `sat_of_spineFit`: a fitting spine satisfies the entries it fits.
-/


/-! ## The peel and the context -/

theorem PiTeleAV.unique :
    ∀ {k : Nat} {T : AnnotTerm} {Γ Γ' : List AnnotTerm} {R R' : AnnotTerm},
      PiTeleAV k T Γ R → PiTeleAV k T Γ' R' → Γ = Γ' ∧ R = R' := by
  intro k T Γ Γ' R R' h
  induction h generalizing Γ' R' with
  | nil => intro h'; cases h'; exact ⟨rfl, rfl⟩
  | @cons k u v A B R Γ₁ h ih =>
    intro h'
    obtain ⟨u', v', A', B', Γ₂, hT, hΓ, h₂⟩ := h'.succ_inv
    obtain ⟨rfl, rfl, rfl, rfl⟩ : u = u' ∧ v = v' ∧ A = A' ∧ B = B' := by
      injection hT with a b c d
      exact ⟨a, b, c, d⟩
    obtain ⟨rfl, rfl⟩ := ih h₂
    exact ⟨hΓ.symm, rfl⟩

/-- A successful peel is a `.pi` context: the peel's domains reversed. -/
theorem piTeleAV_of_stripPisAV :
    ∀ {k : Nat} {T : AnnotTerm} {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm},
      stripPisAV k T = some (pps, b) →
      PiTeleAV k T (pps.map (·.2.2)).reverse b
  | 0, T, pps, b, h => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .nil
  | k + 1, .pi u v A B, pps, b, h => by
    simp only [stripPisAV, Option.map_eq_some_iff] at h
    obtain ⟨⟨pps', b'⟩, hst, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have := piTeleAV_of_stripPisAV hst
    simpa [List.reverse_cons] using PiTeleAV.cons (A := A) (u := u) (v := v) this
  | k + 1, .bvar _, _, _, h | k + 1, .sort _, _, _, h | k + 1, .const _ _, _, _, h
  | k + 1, .app _ _, _, _, h | k + 1, .lam _ _ _, _, _, h
  | k + 1, .eqE _ _, _, _, h
  | k + 1, .fst _, _, _, h | k + 1, .snd _, _, _, h
  | k + 1, .prf, _, _, h => by
    simp [stripPisAV] at h

/-- The peel's entries, read off the reversed context. -/
theorem getD_reverse_of_peel {pps : List (Nat × Nat × AnnotTerm)} {k : Nat}
    (hlen : pps.length = k) {i : Nat} (hi : i < k) {p : Nat × Nat × AnnotTerm}
    (hp : pps[i]? = some p) :
    ((pps.map (·.2.2)).reverse).getD (k - 1 - i) default = p.2.2 := by
  rw [List.getD, List.getElem?_reverse (by simp; omega)]
  simp only [List.length_map, hlen]
  rw [show k - 1 - (k - 1 - i) = i from by omega, List.getElem?_map, hp]
  rfl

/-! ## The hereditary walk -/

/-- **The hereditary walk**: a binder-descending predicate holds along
a peel whose entries are graded under the earlier ones, from its base
case at the full context. -/
theorem hereditaryWalk {Q : (Nat → V) → List (Nat × Nat × AnnotTerm) → Prop}
    {n : Nat} {Γ : List AnnotTerm} {pps : List (Nat × Nat × AnnotTerm)}
    (hΓ : Γ.length = n) (hlen : pps.length = n)
    (hent : ∀ i, i < n → ∃ p, pps[i]? = some p ∧
      p.2.2 = Γ.getD (n - 1 - i) default)
    (okΓ : ∀ i, i < n → ∀ ρ : Nat → V, Sat V (Γ.drop (n - i)) ρ →
      WellDenotedV V ρ (Γ.getD (n - 1 - i) default))
    (hnil : ∀ ρ : Nat → V, Sat V Γ ρ → Q ρ [])
    (hcons : ∀ (ρ : Nat → V) (d : Nat × Nat × AnnotTerm)
      (ds : List (Nat × Nat × AnnotTerm)), d ∈ pps →
      WellDenotedV V ρ d.2.2 →
      (∀ a, a ∈ˢ interp V ρ d.2.2 → Q (cons a ρ) ds) → Q ρ (d :: ds)) :
    ∀ (i : Nat), i ≤ n → ∀ ρ : Nat → V, Sat V (Γ.drop (n - i)) ρ →
      Q ρ (pps.drop i) := by
  -- descend on the remaining length
  suffices ∀ (m i : Nat), n - i = m → i ≤ n → ∀ ρ : Nat → V,
      Sat V (Γ.drop (n - i)) ρ → Q ρ (pps.drop i) from
    fun i => this (n - i) i rfl
  intro m
  induction m with
  | zero =>
    intro i hm hi ρ hρ
    have hin : i = n := by omega
    rw [hin, Nat.sub_self, List.drop_zero] at hρ
    rw [hin, ← hlen, List.drop_length]
    exact hnil ρ hρ
  | succ m ih =>
  intro i hm hi ρ hρ
  by_cases hin : i = n
  · rw [hin, Nat.sub_self, List.drop_zero] at hρ
    rw [hin, ← hlen, List.drop_length]
    exact hnil ρ hρ
  · have hlt : i < n := by omega
    obtain ⟨p, hp, hpe⟩ := hent i hlt
    have hdrop : pps.drop i = p :: pps.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by omega)]
      congr 1
      rw [List.getElem?_eq_getElem (by omega)] at hp
      exact Option.some.inj hp
    rw [hdrop]
    refine hcons ρ p _ (List.mem_of_getElem? hp) ?_ fun a ha => ?_
    · rw [hpe]; exact okΓ i hlt ρ hρ
    · refine ih (i + 1) (by omega) (by omega) (cons a ρ) ?_
      rw [show n - (i + 1) = n - i - 1 from by omega,
        List.drop_eq_getElem_cons (l := Γ) (i := n - i - 1) (by omega)]
      have hG : Γ[n - i - 1] = Γ.getD (n - 1 - i) default := by
        rw [List.getD, List.getElem?_eq_getElem (by omega)]
        simp only [Option.getD_some]
        congr 1; omega
      rw [hG, show n - i - 1 + 1 = n - i from by omega]
      rw [hpe] at ha
      exact Sat_cons V hρ ha

/-! ## The field chain -/

/-- The field entries of a context, in binder order, from position
`j`: entry `nP + j + t` of an opening of length `k`. -/
@[expose] def fieldsFrom (Γ : List AnnotTerm) (k nP nF j : Nat) : List AnnotTerm :=
  (List.range (nF - j)).map fun t => Γ.getD (k - 1 - (nP + j + t)) default

theorem fieldsFrom_succ {Γ : List AnnotTerm} {k nP nF j : Nat} (hj : j < nF) :
    fieldsFrom Γ k nP nF j
      = Γ.getD (k - 1 - (nP + j)) default :: fieldsFrom Γ k nP nF (j + 1) := by
  unfold fieldsFrom
  rw [show nF - j = (nF - (j + 1)) + 1 from by omega, List.range_succ_eq_map,
    List.map_cons, List.map_map]
  rw [Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro t _
  show Γ.getD (k - 1 - (nP + j + (t + 1))) default
    = Γ.getD (k - 1 - (nP + (j + 1) + t)) default
  congr 2
  omega

/-- **The field chain is `FieldsOkB`-graded** from the gradings and
the per-field bounds, at every valuation satisfying the parameters and
the earlier fields. -/
theorem fieldsOkB_of_frame {w : Nat} {Γ : List AnnotTerm} {k nP nF : Nat}
    (hk : k = nP + nF) (hΓ : Γ.length = k)
    (okΓ : ∀ i, i < k → ∀ ρ : Nat → V, Sat V (Γ.drop (k - i)) ρ →
      WellDenotedV V ρ (Γ.getD (k - 1 - i) default))
    (hbnd : ∀ j, j < nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      w ≠ 0 → interp V ρ (Γ.getD (k - 1 - (nP + j)) default) ∈ˢ (univ w : V)) :
    ∀ (j : Nat), j ≤ nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsOkB w ρ (fieldsFrom Γ k nP nF j) := by
  suffices ∀ (m j : Nat), nF - j = m → j ≤ nF → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsOkB w ρ (fieldsFrom Γ k nP nF j) from
    fun j => this (nF - j) j rfl
  intro m
  induction m with
  | zero =>
    intro j hm hj ρ hρ
    have hjn : j = nF := by omega
    subst hjn
    simp only [fieldsFrom, Nat.sub_self, List.range_zero, List.map_nil]
    trivial
  | succ m ih =>
    intro j hm hj ρ hρ
    have hlt : j < nF := by omega
    rw [fieldsFrom_succ hlt]
    refine ⟨(okΓ (nP + j) (by omega) ρ hρ).1, hbnd j hlt ρ hρ, fun a ha => ?_⟩
    refine ih (j + 1) (by omega) (by omega) (cons a ρ) ?_
    rw [show k - (nP + (j + 1)) = k - (nP + j) - 1 from by omega,
      List.drop_eq_getElem_cons (l := Γ) (i := k - (nP + j) - 1) (by omega)]
    have hG : Γ[k - (nP + j) - 1] = Γ.getD (k - 1 - (nP + j)) default := by
      rw [List.getD, List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr 1; omega
    rw [hG, show k - (nP + j) - 1 + 1 = k - (nP + j) from by omega]
    exact Sat_cons V hρ ha

/-! ## Spines and satisfaction -/

/-- A fitting spine satisfies the entries it fits, pushed onto the
ambient context (the entries in binder order become the context's
innermost-first prefix). -/
theorem sat_of_spineFit :
    ∀ {Ds : List AnnotTerm} {as : List V} {Δ₀ : List AnnotTerm} {ρ : Nat → V},
      Sat V Δ₀ ρ → SpineFit ρ Ds as →
      Sat V (Ds.reverse ++ Δ₀) (consList as ρ)
  | [], [], _, _, h, _ => by simpa using h
  | [], _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, [], _, _, _, hsp => hsp.elim
  | D :: Ds, a :: as, Δ₀, ρ, h, hsp => by
    rw [consList_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    exact sat_of_spineFit (Sat_cons V h hsp.1) hsp.2

/-- `SpineFit` along the peel's domains from `Sat` of the peeled
context (the converse, at the context's own valuation). -/
theorem spineFit_of_sat :
    ∀ {Ds : List AnnotTerm} {Δ₀ : List AnnotTerm} {ρ : Nat → V},
      Sat V (Ds.reverse ++ Δ₀) ρ →
      SpineFit (fun j => ρ (j + Ds.length)) Ds
        ((List.range Ds.length).reverse.map ρ) := by
  intro Ds
  induction Ds with
  | nil => intro Δ₀ ρ _; simp [SpineFit]
  | cons D Ds ih =>
    intro Δ₀ ρ h
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at h
    have hd := Sat_drop h Ds.length
    rw [List.drop_append_of_le_length (by simp),
      List.drop_eq_nil_of_le (by simp), List.nil_append] at hd
    obtain ⟨h0, -⟩ := Sat_cons_inv hd
    rw [List.length_cons, List.range_succ, List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.map_cons]
    refine ⟨?_, ?_⟩
    · have e : (fun j => ρ (j + (Ds.length + 1))) = fun j => ρ (j + 1 + Ds.length) := by
        funext j; congr 1; omega
      rw [e]
      simpa using h0
    · have := ih (Δ₀ := D :: Δ₀) (ρ := ρ) h
      have e : cons (ρ Ds.length) (fun j => ρ (j + (Ds.length + 1)))
          = fun j => ρ (j + Ds.length) := by
        funext j
        cases j with
        | zero => show ρ Ds.length = ρ (0 + Ds.length); rw [Nat.zero_add]
        | succ j => show ρ (j + (Ds.length + 1)) = ρ (j + 1 + Ds.length); congr 1; omega
      rw [e]
      exact this


/-!
## The direct structure's two parameter frames, identified

The type former's parameter telescope and the constructor's are opened
at their own variables (`checkStructCtor`), and `checkStructDomsAt`
pins the domains definitionally, binder by binder, each at its own
frame.  `paramFrames` turns the pins into the semantic identification
the leaves need: the two contexts have the same satisfying valuations
at every depth, and the corresponding entries interpret alike under
them.  With it, a fit of the former's parameter domains is a fit of
the constructor's, and the field chain graded at the constructor's
frame is graded at the former's.

Also here: the closedness of readings (`bvarsBelow_of_reading`, the
wire-side currency of `TowerWire`) and the Π-bit congruence
(`piR_congr_bit`).
-/


open ConLeche ConLeche.Semantics ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetModel


/-! ## Small kit -/

/-- A reading at depth `d` of a term scoped at `d` mentions no variable
at or above `d`. -/
theorem bvarsBelow_of_reading {m : EnvModel V env} {d : Nat} {e : Expr}
    (hw : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    {ea : AnnotTerm} (h : denoteMeta m.acval env φ d e = some ea) :
    Term.bvarsBelow d ea.erase :=
  denote_bvarsBelow m.cval_closed d e hw hb (denoteMeta_erase m.acval_erase d e h)


/-! ## The identification -/

/-- **The two parameter frames, identified** from the binder-domain
pins: at every depth `i ≤ nP` the constructor's context and the
former's have the same satisfying valuations, and below `nP` the
`i`-th entries interpret alike under the constructor's context. -/
theorem paramFrames {m : EnvModel V env} {F : Nat}
    (hc : ClaimsAt μ m φ F) {nP nF : Nat}
    {tty cty : Expr} {tfvs cfvs : List Expr} {trest crest : Expr}
    {Γt Γc : List AnnotTerm} {Rt Rc : AnnotTerm}
    (hT : Opened m φ nP tty tfvs trest Γt Rt)
    (hC : Opened m φ (nP + nF) cty cfvs crest Γc Rc)
    (hpin : ∀ i, i < nP → ∃ a b, cfvs[i]? = some a ∧ tfvs[i]? = some b ∧
      ConLeche.isDefEqCore μ env F i (Expr.fvarTypeD a) (Expr.fvarTypeD b)
        = .ok true) :
    ∀ i, i ≤ nP →
      (∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - i)) ρ ↔
        Sat V (Γt.drop (nP - i)) ρ) ∧
      (i < nP → ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - i)) ρ →
        interp V ρ (Γc.getD (nP + nF - 1 - i) default)
          = interp V ρ (Γt.getD (nP - 1 - i) default)) := by
  suffices ∀ i j, j ≤ i → j ≤ nP →
      (∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - j)) ρ ↔
        Sat V (Γt.drop (nP - j)) ρ) ∧
      (j < nP → ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - j)) ρ →
        interp V ρ (Γc.getD (nP + nF - 1 - j) default)
          = interp V ρ (Γt.getD (nP - 1 - j) default)) from
    fun i hi => this i i (Nat.le_refl _) hi
  intro i
  induction i with
  | zero =>
    intro j hj _
    obtain rfl : j = 0 := by omega
    refine ⟨fun ρ => ?_, fun _ ρ hρ => ?_⟩
    · rw [Nat.sub_zero, Nat.sub_zero, List.drop_eq_nil_of_le (by have := hC.len; omega),
        List.drop_eq_nil_of_le (by have := hT.len; omega)]
    · -- the head binder's pin, at the empty frame
      obtain ⟨a, b, ha, hb, hdeq⟩ := hpin 0 (by omega)
      obtain ⟨-, hwa, hba, hLa, hleafa⟩ := hC.var 0 a ha
      obtain ⟨-, hwb, hbb, hLb, hleafb⟩ := hT.var 0 b hb
      have hCa : CtxOk m φ 0 (Γc.drop (nP + nF - 0)) (Expr.fvarTypeD a) :=
        hC.ctx (by omega) hwa hleafa
      have hCb : CtxOk m φ 0 (Γt.drop (nP - 0)) (Expr.fvarTypeD b) :=
        hT.ctx (by omega) hwb hleafb
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by have := hT.len; omega)] at hCb
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by have := hC.len; omega)] at hCa hρ
      have hda := hC.doms 0 a ha
      have hdb := hT.doms 0 b hb
      exact hc.defEqRow hdeq hwa hba hLa hwb hbb hLb hCa hCb hda hdb
        (fun ρ hρ => by
          have := hC.okΓ 0 (by omega) ρ
          rw [Nat.sub_zero, List.drop_eq_nil_of_le (by have := hC.len; omega)] at this
          exact this hρ)
        (fun ρ hρ => by
          have := hT.okΓ 0 (by omega) ρ
          rw [Nat.sub_zero, List.drop_eq_nil_of_le (by have := hT.len; omega)] at this
          exact this hρ) ρ hρ
  | succ i ih =>
    intro j hj hjn
    rcases Nat.lt_or_ge j (i + 1) with hjl | hjg
    · exact ih j (by omega) hjn
    obtain rfl : j = i + 1 := by omega
    obtain ⟨ihsat, iheq⟩ := ih i (Nat.le_refl _) (by omega)
    have hlt : i < nP := by omega
    -- the contexts at depth `i + 1` are the depth-`i` ones with the
    -- `i`-th entries on top
    have hdc : Γc.drop (nP + nF - (i + 1))
        = Γc.getD (nP + nF - 1 - i) default :: Γc.drop (nP + nF - i) := by
      rw [show nP + nF - (i + 1) = nP + nF - i - 1 from by omega,
        List.drop_eq_getElem_cons (l := Γc) (i := nP + nF - i - 1)
          (by rw [hC.len]; omega)]
      have hG : Γc[nP + nF - i - 1]'(by have := hC.len; omega)
          = Γc.getD (nP + nF - 1 - i) default := by
        rw [List.getD, List.getElem?_eq_getElem (by rw [hC.len]; omega)]
        simp only [Option.getD_some]
        congr 1; omega
      rw [hG, show nP + nF - i - 1 + 1 = nP + nF - i from by omega]
    have hdt : Γt.drop (nP - (i + 1))
        = Γt.getD (nP - 1 - i) default :: Γt.drop (nP - i) := by
      rw [show nP - (i + 1) = nP - i - 1 from by omega,
        List.drop_eq_getElem_cons (l := Γt) (i := nP - i - 1)
          (by rw [hT.len]; omega)]
      have hG : Γt[nP - i - 1]'(by have := hT.len; omega)
          = Γt.getD (nP - 1 - i) default := by
        rw [List.getD, List.getElem?_eq_getElem (by rw [hT.len]; omega)]
        simp only [Option.getD_some]
        congr 1; omega
      rw [hG, show nP - i - 1 + 1 = nP - i from by omega]
    have hsat : ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - (i + 1))) ρ ↔
        Sat V (Γt.drop (nP - (i + 1))) ρ := by
      intro ρ
      rw [hdc, hdt]
      constructor
      · intro h
        obtain ⟨h0, htl⟩ := Sat_cons_inv h
        have := Sat_cons V ((ihsat _).mp htl) (by
          rw [← iheq hlt _ htl]; exact h0)
        rwa [cons_eta] at this
      · intro h
        obtain ⟨h0, htl⟩ := Sat_cons_inv h
        have htl' := (ihsat _).mpr htl
        have := Sat_cons V htl' (by rw [iheq hlt _ htl']; exact h0)
        rwa [cons_eta] at this
    refine ⟨hsat, fun hlt' ρ hρ => ?_⟩
    -- the pin at depth `i + 1`, with the former's comparand transferred
    -- to the constructor's context
    obtain ⟨a, b, ha, hb, hdeq⟩ := hpin (i + 1) hlt'
    obtain ⟨-, hwa, hba, hLa, hleafa⟩ := hC.var (i + 1) a ha
    obtain ⟨-, hwb, hbb, hLb, hleafb⟩ := hT.var (i + 1) b hb
    have hCa : CtxOk m φ (i + 1) (Γc.drop (nP + nF - (i + 1)))
        (Expr.fvarTypeD a) := hC.ctx (by omega) hwa hleafa
    have hCb₀ : CtxOk m φ (i + 1) (Γt.drop (nP - (i + 1)))
        (Expr.fvarTypeD b) := hT.ctx (by omega) hwb hleafb
    -- the entries of the two depth-`(i+1)` contexts interpret alike
    -- under the constructor's: position `p` is binder `i - p`
    have hent : ∀ (p : Nat) (A₁ A₂ : AnnotTerm),
        (Γt.drop (nP - (i + 1)))[p]? = some A₁ →
        (Γc.drop (nP + nF - (i + 1)))[p]? = some A₂ →
        ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - (i + 1))) ρ →
          interp V (fun j => ρ (j + p + 1)) A₁
            = interp V (fun j => ρ (j + p + 1)) A₂ := by
      intro p A₁ A₂ hA₁ hA₂ ρ hρ
      have hpl : p < i + 1 := by
        have := (List.getElem?_eq_some_iff.mp hA₂).1
        rw [List.length_drop, hC.len] at this
        omega
      rw [List.getElem?_drop] at hA₁ hA₂
      have hj : nP - (i + 1) + p = nP - 1 - (i - p) := by omega
      have hj' : nP + nF - (i + 1) + p = nP + nF - 1 - (i - p) := by omega
      rw [hj] at hA₁
      rw [hj'] at hA₂
      have e1 : A₁ = Γt.getD (nP - 1 - (i - p)) default := by
        rw [List.getD, hA₁]; rfl
      have e2 : A₂ = Γc.getD (nP + nF - 1 - (i - p)) default := by
        rw [List.getD, hA₂]; rfl
      subst e1 e2
      have hd := Sat_drop hρ (p + 1)
      rw [List.drop_drop, show nP + nF - (i + 1) + (p + 1) = nP + nF - (i - p)
        from by omega] at hd
      have e : (fun j => ρ (j + p + 1)) = fun j => ρ (j + (p + 1)) := by
        funext j; rw [Nat.add_assoc]
      rw [e]
      exact ((ih (i - p) (by omega) (by omega)).2 (by omega) _ hd).symm
    have hCb : CtxOk m φ (i + 1) (Γc.drop (nP + nF - (i + 1)))
        (Expr.fvarTypeD b) :=
      hCb₀.transfer (by rw [List.length_drop, hC.len]; omega)
        (fun ρ hρ => (hsat ρ).mp hρ) hent
    have hda := hC.doms (i + 1) a ha
    have hdb := hT.doms (i + 1) b hb
    exact hc.defEqRow hdeq hwa hba hLa hwb hbb hLb hCa hCb hda hdb
      (fun ρ hρ => hC.okΓ (i + 1) (by omega) ρ hρ)
      (fun ρ hρ => hT.okΓ (i + 1) (by omega) ρ ((hsat ρ).mp hρ)) ρ hρ


/-!
## The direct block's family laws

The block's own capability laws, from the leaves' semantic summary:

* `formerFold` — the former applied along a fitting parameter spine is
  the instantiated carrier (`structTyAV_fold` under the hereditary
  premise);
* `structUnitLawP` — a fieldless family is unit-like (its carrier is
  `unitSet`, both regimes);
* `structEtaLawP0` — a fieldless family's η law: the member is the
  point and so is the constructor's application.
-/


open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)


/-! ## Fits and folds -/

/-- A value-level fit of a Π-tower reading, of the tower's own
length, is a fit of its domains. -/
theorem spineFit_of_teleFit :
    ∀ {pds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm} {ρ : Nat → V}
      {ts : List V} {rest : V},
      ts.length = pds.length →
      TeleFit V ρ (mkPisAV pds b) ts rest →
      SpineFit ρ (pds.map (·.2.2)) ts
  | [], _, _, [], _, _, _ => trivial
  | [], _, _, _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, _, _, [], _, hlen, _ => by simp at hlen
  | d :: pds, b, ρ, t :: ts, rest, hlen, h => by
    cases h with
    | cons ht hfit =>
      exact ⟨ht, spineFit_of_teleFit (by simpa using hlen) hfit⟩


/-!
## The direct block's stage data

The readings the leaves are built over, packaged per stored constant:
`FormerData` (the type former's Π-peel, its bits, gradings, bounds
and level dependence) and — later in the file — the constructor's.
Each is derived once from the stage's run (`formerData_of`) and
crossed to the later stage environments (`FormerData.cross`), where
the readings survive because the block's constants are stored and
the head's slot mentions none of them.
-/


/-! ## Kit -/

theorem mkPisAV_inj :
    ∀ {pps₁ pps₂ : List (Nat × Nat × AnnotTerm)} {b₁ b₂ : AnnotTerm},
      pps₁.length = pps₂.length → mkPisAV pps₁ b₁ = mkPisAV pps₂ b₂ →
      pps₁ = pps₂ ∧ b₁ = b₂
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | d₁ :: pps₁, d₂ :: pps₂, b₁, b₂, hlen, h => by
    simp only [mkPisAV, AnnotTerm.pi.injEq] at h
    obtain ⟨hu, hv, hA, hB⟩ := h
    obtain ⟨rfl, rfl⟩ := mkPisAV_inj (by simpa using hlen) hB
    refine ⟨?_, rfl⟩
    congr 1
    exact Prod.ext hu (Prod.ext hv hA)

/-- A `.pi` context is a successful peel, with the peel's domains
reversed. -/
theorem stripPisAV_of_piTeleAV :
    ∀ {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R →
      ∃ pps : List (Nat × Nat × AnnotTerm),
        stripPisAV k T = some (pps, R) ∧ (pps.map (·.2.2)).reverse = Γ := by
  intro k T Γ R h
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons k u v A B R Γ' _ ih =>
    obtain ⟨pps, hst, hΓ⟩ := ih
    refine ⟨(u, v, A) :: pps, ?_, ?_⟩
    · simp only [stripPisAV, hst, Option.map_some]
    · simp [hΓ]

theorem DomsBelow.drop {k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} (j : Nat), DomsBelow k ds →
      DomsBelow (k + j) (ds.drop j)
  | _, 0, h => by simpa using h
  | [], _ + 1, _ => trivial
  | _ :: ds, j + 1, h => by
    rw [List.drop_succ_cons, show k + (j + 1) = k + 1 + j from by omega]
    exact DomsBelow.drop (k := k + 1) (ds := ds) j h.2

/-! ## The former's data -/

/-- **The type former's reading, peeled**: at every assignment the
stored type reads as the Π-tower over the parameter data ending in
the result sort, with nonzero codomain bits, graded, bounded, and
depending only on the block's level parameters. -/
structure FormerData {env : Env} (m : EnvModel V env) (cvT : ConstantVal)
    (nP : Nat) (resSort : Level)
    (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)) : Prop where
  read : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvT.type
    = some (mkPisAV (pps ψ) (.sort (resSort.eval ψ)))
  len : ∀ ψ : Name → Nat, (pps ψ).length = nP
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ pps ψ → d.2.1 ≠ 0
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    WellDenotedV V ρ (mkPisAV (pps ψ) (.sort (resSort.eval ψ)))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (pps ψ)
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvT.levelParams, ψ₁ p = ψ₂ p) →
    pps ψ₁ = pps ψ₂ ∧ resSort.eval ψ₁ = resSort.eval ψ₂

/-- The former's data, from its `checkConstantVal` run at the
pre-block environment and the annotated telescope shape. -/
theorem formerData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {cvT cvTa : ConstantVal} {nP : Nat} {resSort : Level}
    {bs : List (Expr × ConLeche.BinderMeta)}
    (hccv : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cvT = .ok cvTa)
    (hstrip : cvTa.type.stripPis nP = some (bs, .sort resSort)) :
    ∃ pps : (Name → Nat) → List (Nat × Nat × AnnotTerm),
      FormerData mp.base2 cvTa nP resSort pps := by
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', htp', htr', hst,
    hens, rfl⟩ := ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' htp' htr' hst hens hstrip
  have hw : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded type' := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  obtain ⟨fvs, hop⟩ := openPisAtFvars_of_stripPis_sort nP 0 hstrip
  -- the bits: the opened body is `Sort resSort`, of sort `succ resSort`
  obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ :=
    piBits_of_infer hμ nP hop hst hens
  obtain rfl := inferTypeCore_sort_inv hib
  obtain rfl := ensureSortCore_sort_eq hensb
  -- per assignment: the reading, its peel, its grading
  have hper : ∀ ψ : Name → Nat, ∃ pps : List (Nat × Nat × AnnotTerm),
      denoteMeta mp.base2.acval env ψ 0 type'
        = some (mkPisAV pps (.sort (resSort.eval ψ))) ∧
      pps.length = nP ∧
      (∀ d ∈ pps, d.2.1 ≠ 0) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV pps (.sort (resSort.eval ψ)))) ∧
      DomsBelow 0 pps := by
    intro ψ
    have hc := claimsAt_of hμ mp ψ F
    obtain ⟨Ta, hTa⟩ := acceptedReads_of mp.base2 ψ hst hw hbt' hL
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hst hw hbt' hL (CtxOk.nil hnil) hTa
    have hokT' : ∀ ρ : Nat → V, WellDenotedV V ρ Ta := fun ρ =>
      hokT ρ (Sat_nil V ρ)
    obtain ⟨Γ, R, htele, hop'⟩ := opened_of hop htf' hbt' hTa hokT'
    have hR : R = .sort (resSort.eval ψ) := by
      have := hop'.body
      rw [denoteMeta_sort] at this
      exact (Option.some.inj this).symm
    subst hR
    obtain ⟨pps, hst', -⟩ := stripPisAV_of_piTeleAV htele
    obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
    subst hTeq
    refine ⟨pps, hTa, hlen, ?_, hokT', ?_⟩
    · intro d hd
      have := stripPisAV_bits nP (hbits ψ) hTa hst' d hd
      simp only [Level.eval, Nat.succ_ne_zero, iff_false] at this
      exact this
    · exact (stripPisAV_below hst' (bvarsBelow_of_reading hw hbt' hTa)).1
  refine ⟨fun ψ => Classical.choose (hper ψ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ψ => (Classical.choose_spec (hper ψ)).1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.2
  · intro ψ₁ ψ₂ hφ
    have h2 := (Classical.choose_spec (hper ψ₂)).1
    have h1 : denoteMeta mp.base2.acval env ψ₂ 0 type'
        = some (mkPisAV (Classical.choose (hper ψ₁))
          (.sort (resSort.eval ψ₁))) := by
      rw [← denoteMeta_params_ext mp.base2 hφ 0 type' htp']
      exact (Classical.choose_spec (hper ψ₁)).1
    obtain ⟨hp, hb⟩ := mkPisAV_inj
      (by rw [(Classical.choose_spec (hper ψ₁)).2.1,
        (Classical.choose_spec (hper ψ₂)).2.1])
      (Option.some.inj (h1.symm.trans h2))
    exact ⟨hp, AnnotTerm.sort.inj hb⟩

/-- The former's data crosses a cons whose slot does not mention the
stored type (any block cons after the former's). -/
theorem FormerData.cross {m : EnvModel V env} {cvT : ConstantVal}
    {nP : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : FormerData m cvT nP resSort pps)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hat : ConsCrossAt c₀ cvT.type)
    (hcb : ConstsBound env cvT.type)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    FormerData m₂ cvT nP resSort pps where
  read ψ := by
    rw [hac]
    exact denoteMeta_cons_mono hfresh hat ψ 0 hcb (h.read ψ)
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params


/-!
## The former's cons

`stageFormer`: the P step at the type former's cons, for a given
field chain `Fs`.  The leaf is `structTyAV (resSort.eval ψ) (pps ψ)
(Fs ψ)`; the chain's hereditary grading at the former's parameter
frame is the one premise the two installs of the former differ in —
the *dummy* install (`Fs = []`, whose premise is trivial) serves the
constructor-stage claims that grade the real chain, and the *real*
install builds the model the rest of the block extends.
-/


theorem stripPisAV_mkPisAV :
    ∀ (pps : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm),
      stripPisAV pps.length (mkPisAV pps b) = some (pps, b)
  | [], _ => rfl
  | d :: pps, b => by
    simp only [List.length_cons, mkPisAV, stripPisAV, stripPisAV_mkPisAV pps b,
      Option.map_some]

end ConLeche.Model
