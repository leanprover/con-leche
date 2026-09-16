module

public import ConLeche.Model.Annot.EnvModel
public import ConLeche.Model.Steps.Stuck
public import ConLeche.Kernel.Inductives.MutualInstall
public import ConLeche.Model.Annot.BitRestrict
public import ConLeche.Model.Annot.BitErase
public import ConLeche.Model.Annot.BitInst
public import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Model.Inductives.MutualFormersKit
public import ConLeche.Verify.EraseAnnots
public import ConLeche.Verify.Shift
import ConLeche.Model.Steps.CapsRows
import ConLeche.Verify.Denote.Install
import ConLeche.Verify.InferLeaves

public section

/-!
# The reading transfer kit and the restored pin's reading (task #315, M6 s9′)

The nested assembly reads a restored constructor at the SCRATCH
environment (the auxiliary block's formers consed on top of the prefix
one) but wants the reading at the PREFIX model.  This file is the
transfer that moves a reading between two environments and two leaf
valuations (`nt_denoteMeta_transfer`, and its spine form), the
arithmetic of the formers' conses that supplies its premises
(`nt_consMutualFormers_append`, `nt_consMutualFormers_find?_cases`,
`nt_findPreserved_take`, `nt_findProj?_take`), the two syntactic facts
a reading carries (`nt_looseBVarsBounded_of_denoteMeta`,
`nt_fvarsBelow_of_abstractRange_noFvar`), and the assembly's
`nestEntry` core: the restored pin's reading at a deeper depth
(`nt_denoteMeta_restoredPin`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo MutualFormerA openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The formers' conses -/

/-- The conses of an appended former list are the two conses in order. -/
theorem nt_consMutualFormers_append :
    ∀ (l₁ l₂ : List MutualFormerA) (env : Env),
      ConLeche.consMutualFormers (l₁ ++ l₂) env
        = ConLeche.consMutualFormers l₂ (ConLeche.consMutualFormers l₁ env)
  | [], _, _ => rfl
  | f :: fs, l₂, env => by
    show ConLeche.consMutualFormers (fs ++ l₂) ⟨.indInfo f.cvTa {} :: env.consts⟩ = _
    rw [nt_consMutualFormers_append fs l₂]
    rfl

/-- A name found past the formers' conses is either found before them
or is one of the formers' own. -/
theorem nt_consMutualFormers_find?_cases :
    ∀ {fms : List MutualFormerA} {env : Env} {n : Name} {ci : ConstantInfo},
      (ConLeche.consMutualFormers fms env).find? n = some ci →
      env.find? n = some ci ∨ ∃ f ∈ fms, f.cvTa.name = n
  | [], _, _, _, h => Or.inl h
  | f :: fs, env, n, ci, h => by
    replace h : (ConLeche.consMutualFormers fs
      ⟨.indInfo f.cvTa {} :: env.consts⟩).find? n = some ci := h
    rcases nt_consMutualFormers_find?_cases h with h' | ⟨g, hg, hgn⟩
    · rcases Decidable.em (f.cvTa.name = n) with hn | hn
      · exact Or.inr ⟨f, List.mem_cons_self, hn⟩
      · rw [find?_cons_of_name_ne (c := .indInfo f.cvTa {}) hn] at h'
        exact Or.inl h'
    · exact Or.inr ⟨g, List.mem_cons_of_mem _ hg, hgn⟩

/-- A projection-table absence survives the formers' conses (no former
is a projection table). -/
theorem nt_findProj?_consMutualFormers :
    ∀ (fms : List MutualFormerA) {env : Env} (sn : Name) (i : Nat),
      env.findProj? sn i = none →
      (ConLeche.consMutualFormers fms env).findProj? sn i = none
  | [], _, _, _, h => h
  | f :: fs, env, sn, i, h => by
    show (ConLeche.consMutualFormers fs ⟨.indInfo f.cvTa {} :: env.consts⟩).findProj? sn i = none
    exact nt_findProj?_consMutualFormers fs sn i
      (findProj?_cons_of_base_none (c₀ := .indInfo f.cvTa {}) (fun _ hh => nomatch hh) sn i h)

/-- The formers' conses split at any prefix. -/
theorem nt_consMutualFormers_split (fms : List MutualFormerA) (env : Env) (k : Nat) :
    ConLeche.consMutualFormers fms env
      = ConLeche.consMutualFormers (fms.drop k) (ConLeche.consMutualFormers (fms.take k) env) := by
  rw [← nt_consMutualFormers_append, List.take_append_drop]

/-- **A prefix of the formers' conses is preserved by all of them**:
the tail's names are fresh at the prefix environment, so nothing the
prefix finds is shadowed. -/
theorem nt_findPreserved_take {fms : List MutualFormerA} {env : Env} (k : Nat)
    (hfresh : ∀ f ∈ fms, env.find? f.cvTa.name = none)
    (hnd : (fms.map (·.cvTa.name)).Nodup) :
    FindPreserved (ConLeche.consMutualFormers (fms.take k) env)
      (ConLeche.consMutualFormers fms env) := by
  have hsplit : ((fms.take k).map (·.cvTa.name) ++ (fms.drop k).map (·.cvTa.name)).Nodup := by
    rw [← List.map_append, List.take_append_drop]; exact hnd
  have hfresh' : ∀ g ∈ fms.drop k,
      (ConLeche.consMutualFormers (fms.take k) env).find? g.cvTa.name = none := by
    intro g hg
    have hgm : g ∈ fms := by
      rw [← List.take_append_drop k fms]; exact List.mem_append_right _ hg
    cases hfind : (ConLeche.consMutualFormers (fms.take k) env).find? g.cvTa.name with
    | none => rfl
    | some ci =>
      rcases nt_consMutualFormers_find?_cases hfind with h' | ⟨f, hf, hfn⟩
      · rw [hfresh g hgm] at h'; exact nomatch h'
      · exact absurd hfn ((List.nodup_append.mp hsplit).2.2 _
          (List.mem_map_of_mem (f := (·.cvTa.name)) hf) _
          (List.mem_map_of_mem (f := (·.cvTa.name)) hg))
  rw [nt_consMutualFormers_split fms env k]
  intro n ci h
  exact (consMutualFormers_extend hfresh' (List.nodup_append.mp hsplit).2.1).1 h

/-- A projection-table absence at a prefix of the formers' conses is
one at all of them. -/
theorem nt_findProj?_take {fms : List MutualFormerA} {env : Env} (k : Nat) :
    ∀ (sn : Name) (i : Nat),
      (ConLeche.consMutualFormers (fms.take k) env).findProj? sn i = none →
      (ConLeche.consMutualFormers fms env).findProj? sn i = none := by
  intro sn i h
  rw [nt_consMutualFormers_split fms env k]
  exact nt_findProj?_consMutualFormers _ sn i h

/-! ## The transfer -/

/-- **THE TRANSFER**: a term that resolves at `env₁` reads the same at
`env₂` with a valuation that agrees on everything `env₁` finds — the
environment crossing (`denoteMeta_env_restrict`) followed by the leaf
congruence (`denoteMeta_congr_of_resolve`). -/
theorem nt_denoteMeta_transfer {env₁ env₂ : Env}
    {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    (hF : FindPreserved env₁ env₂)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₁.findProj? sn i = none → env₂.findProj? sn i = none)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → acval₁ n = acval₂ n) :
    ∀ (d : Nat) (e : Expr), Expr.constsResolve env₁ e = true →
      denoteMeta acval₂ env₂ φ d e = denoteMeta acval₁ env₁ φ d e := by
  intro d e hres
  rw [denoteMeta_env_restrict hF hproj d e hres]
  exact (denoteMeta_congr_of_resolve hag d e hres).symm

/-- The transfer, transposed to a read spine. -/
theorem nt_denoteMetaSpine_transfer {env₁ env₂ : Env}
    {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    (hF : FindPreserved env₁ env₂)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₁.findProj? sn i = none → env₂.findProj? sn i = none)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → acval₁ n = acval₂ n) :
    ∀ (d : Nat) {as : List Expr} {vs : List AnnotTerm},
      (∀ a ∈ as, Expr.constsResolve env₁ a = true) →
      (DenoteMetaSpine acval₂ env₂ φ d as vs ↔ DenoteMetaSpine acval₁ env₁ φ d as vs) := by
  intro d as
  induction as with
  | nil =>
    intro vs _
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; exact .nil
  | cons a as ih =>
    intro vs hres
    constructor
    · intro h
      cases h with
      | cons ha htl =>
        refine .cons ?_ ((ih (fun x hx => hres x (List.mem_cons_of_mem _ hx))).mp htl)
        rw [← nt_denoteMeta_transfer hF hproj hag d a (hres a List.mem_cons_self)]
        exact ha
    · intro h
      cases h with
      | cons ha htl =>
        refine .cons ?_ ((ih (fun x hx => hres x (List.mem_cons_of_mem _ hx))).mpr htl)
        rw [nt_denoteMeta_transfer hF hproj hag d a (hres a List.mem_cons_self)]
        exact ha

/-! ## The shape of an opened telescope's reading -/

/-- **The binder slots of an opened Π-telescope's reading**: the `u`
slot is `0` and the `v` slot is a bit.  The opening is what forces the
`.forallE` at every step — at a `.const` head the reading is the leaf
`acval n ψ`, which may itself be a `.pi`, so the syntactic telescope
must be carried. -/
theorem nt_stripPisAV_denoteMeta_shape {acval : Name → (Name → Nat) → AnnotTerm}
    {env : Env} {φ : Name → Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {fvs : List Expr} {o : Expr} {ea : AnnotTerm}
      {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm},
      openPisAtFvars n e d = some (fvs, o) →
      denoteMeta acval env φ d e = some ea →
      stripPisAV n ea = some (pps, b) →
      ∀ p ∈ pps, p.1 = 0 ∧ p.2.1 ≤ 1
  | 0, _, _, _, _, _, pps, _, _, _, hst => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hst
    intro p hp
    exact absurd hp (by simp)
  | n + 1, d, e, fvs, o, ea, pps, b, hopen, hden, hst => by
    match e, hopen with
    | .forallE dom body mb, hopen =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hden
      simp only [stripPisAV, Option.map_eq_some_iff] at hst
      obtain ⟨⟨pps', b'⟩, hst', heq⟩ := hst
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [openPisAtFvars] at hopen
      split at hopen
      · next hopen' =>
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · refine ⟨rfl, ?_⟩
          show pwBit φ mb.pw ≤ 1
          unfold pwBit; split <;> omega
        · exact nt_stripPisAV_denoteMeta_shape n hopen' hba hst' p hp
      · exact nomatch hopen
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

/-! ## A reading is closed -/

/-- Instantiating a bound variable cannot hide a loose one: the
substituted term is bounded at `k` only if the original is bounded at
`k + 1`. -/
theorem nt_looseBVarsBounded_instantiate1_inv (v : Expr) :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 v k).looseBVarsBounded k = true →
      e.looseBVarsBounded (k + 1) = true := by
  intro e
  induction e with
  | bvar i =>
    intro k h
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
    rcases Decidable.em (i = k) with h1 | h1
    · omega
    · rw [Expr.instantiate1, if_neg h1] at h
      rcases Decidable.em (i > k) with h2 | h2
      · rw [if_pos h2] at h
        simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
        omega
      · omega
  | fvar _ _ _ => intro _ _; rfl
  | sort _ => intro _ _; rfl
  | const _ _ => intro _ _; rfl
  | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro k h
    rw [Expr.instantiate1] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty body _ ihty ihbody =>
    intro k h
    rw [Expr.instantiate1] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨ihty k h.1, ihbody (k + 1) h.2⟩
  | forallE ty body _ ihty ihbody =>
    intro k h
    rw [Expr.instantiate1] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨ihty k h.1, ihbody (k + 1) h.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro k h
    rw [Expr.instantiate1] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihty k h.1.1, ihval k h.1.2⟩, ihbody (k + 1) h.2⟩
  | proj _ _ e ihe =>
    intro k h
    rw [Expr.instantiate1] at h
    simp only [Expr.looseBVarsBounded] at h ⊢
    exact ihe k h

/-- **A term that reads is closed**: `denoteMeta` has no `.bvar`
clause, and each binder clause reads the body already opened. -/
theorem nt_looseBVarsBounded_of_denoteMeta {acval : Name → (Name → Nat) → AnnotTerm}
    {env : Env} {φ : Name → Nat} :
    ∀ (d : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta acval env φ d e = some ea → e.looseBVarsBounded 0 = true := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 _ _ => intro _ _; rfl
  | case2 _ _ _ => intro _ _; rfl
  | case3 _ _ _ _ _ _ => intro _ _; rfl
  | case4 _ _ _ _ _ _ => intro _ _; rfl
  | case5 _ _ _ _ => intro _ _; rfl
  | case6 d ty body _ ihty ihbody =>
    intro ea h
    obtain ⟨ta, ba, hta, hba, -⟩ := denoteMeta_forallE_inv h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihty hta, nt_looseBVarsBounded_instantiate1_inv (.fvar d ty) body 0 (ihbody hba)⟩
  | case7 d ty body _ ihty ihbody =>
    intro ea h
    obtain ⟨ta, ba, hta, hba, -⟩ := denoteMeta_lam_inv h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihty hta, nt_looseBVarsBounded_instantiate1_inv (.fvar d ty) body 0 (ihbody hba)⟩
  | case8 _ _ _ ihf iha =>
    intro ea h
    obtain ⟨fa, aa, hfa, haa, -⟩ := denoteMeta_app_inv h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf hfa, iha haa⟩
  | case9 d ty val body =>
    intro ea h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 _ _ _ _ ihe =>
    intro ea h
    obtain ⟨ia, hia, -⟩ := denoteMeta_proj_inv h
    simp only [Expr.looseBVarsBounded]
    exact ihe hia
  | case11 _ _ _ => intro _ _; rfl
  | case12 _ _ _ => intro _ _; rfl
  | case13 _ _ _ => intro _ _; rfl
  | case14 _ _ _ => intro _ _; rfl
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea h
    cases x with
    | bvar i =>
      have hb : denoteMeta acval env φ d (.bvar i) = none := by rw [denoteMeta.eq_def]
      rw [hb] at h; exact nomatch h
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

/-! ## Abstraction leaves no free variable behind -/

/-- **An abstraction that erases every `fvar` bounds them**: the
`fvar` clause of `abstractRange` keeps an out-of-range variable, so a
`fvar`-free abstract says every variable was in range. -/
theorem nt_fvarsBelow_of_abstractRange_noFvar {k : Nat} :
    ∀ {e : Expr} (c : Nat), (e.abstractRange 0 k c).hasFvar = false → e.fvarsBelow k := by
  intro e
  induction e with
  | bvar _ => intro _ _; trivial
  | sort _ => intro _ _; trivial
  | const _ _ => intro _ _; trivial
  | lit _ => intro _ _; trivial
  | fvar idx ty _ =>
    intro c h
    rw [Expr.abstractRange] at h
    split at h
    · next hr => exact (show idx < k from by omega)
    · next hr => exact absurd h (by rw [Expr.hasFvar]; exact fun hh => nomatch hh)
  | app f a ihf iha =>
    intro c h
    rw [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact ⟨ihf c h.1, iha c h.2⟩
  | lam ty body _ ihty ihbody =>
    intro c h
    rw [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact ⟨ihty c h.1, ihbody (c + 1) h.2⟩
  | forallE ty body _ ihty ihbody =>
    intro c h
    rw [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact ⟨ihty c h.1, ihbody (c + 1) h.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro c h
    rw [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at h
    exact ⟨ihty c h.1.1, ihval c h.1.2, ihbody (c + 1) h.2⟩
  | proj _ _ e ihe =>
    intro c h
    rw [Expr.abstractRange, Expr.hasFvar] at h
    exact ihe c h

/-- Bounded free variables give the erased term's well-scopedness
(erasure replaces every annotation by a closed sort). -/
theorem nt_WScoped_eraseAnnots_of_fvarsBelow {d : Nat} :
    ∀ {e : Expr}, e.fvarsBelow d → Expr.WScoped d e.eraseAnnots := by
  intro e
  induction e with
  | bvar _ => intro _; simp only [Expr.eraseAnnots, Expr.WScoped]
  | sort _ => intro _; simp only [Expr.eraseAnnots, Expr.WScoped]
  | const _ _ => intro _; simp only [Expr.eraseAnnots, Expr.WScoped]
  | lit _ => intro _; simp only [Expr.eraseAnnots, Expr.WScoped]
  | fvar idx _ _ =>
    intro h
    simp only [Expr.eraseAnnots, Expr.WScoped]
    exact ⟨h, trivial⟩
  | app _ _ ihf iha =>
    intro h
    simp only [Expr.eraseAnnots, Expr.WScoped]
    exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ _ ihty ihbody =>
    intro h
    simp only [Expr.eraseAnnots, Expr.WScoped]
    exact ⟨ihty h.1, ihbody h.2⟩
  | forallE _ _ _ ihty ihbody =>
    intro h
    simp only [Expr.eraseAnnots, Expr.WScoped]
    exact ⟨ihty h.1, ihbody h.2⟩
  | letE _ _ _ ihty ihval ihbody =>
    intro h
    simp only [Expr.eraseAnnots, Expr.WScoped]
    exact ⟨ihty h.1, ihval h.2.1, ihbody h.2.2⟩
  | proj _ _ _ ihe =>
    intro h
    simp only [Expr.eraseAnnots, Expr.WScoped]
    exact ihe h

/-! ## The restored pin's reading -/

/-- The pin's syntactic spelling is closed (every component reads). -/
theorem nt_pin_bounded {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} {J : Name} {lvls : List Level}
    {DsE : List Expr} {Ds : List AnnotTerm}
    (hDs : DenoteMetaSpine acval env φ d DsE Ds) :
    (Expr.mkAppN (.const J lvls) DsE).looseBVarsBounded 0 = true :=
  looseBVarsBounded_mkAppN rfl (fun x hx => by
    obtain ⟨v, hv⟩ := hDs.mem x hx
    exact nt_looseBVarsBounded_of_denoteMeta d x hv)

/-- The pin's free variables are the opener's. -/
theorem nt_pin_fvarsBelow {nP : Nat} {J : Name} {lvls : List Level} {DsE : List Expr}
    (hfv : (Expr.abstractRange (Expr.mkAppN (.const J lvls) DsE) 0 nP 0).hasFvar = false) :
    (Expr.mkAppN (.const J lvls) DsE).fvarsBelow nP :=
  nt_fvarsBelow_of_abstractRange_noFvar 0 hfv

/-- A lift distributes over an application spine. -/
theorem nt_liftN_mkAppN (n k : Nat) : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    AnnotTerm.liftN n (AnnotTerm.mkAppN f as) k
      = AnnotTerm.mkAppN (AnnotTerm.liftN n f k) (as.map fun a => AnnotTerm.liftN n a k)
  | [], _ => rfl
  | a :: as, f => by
    simp only [AnnotTerm.mkAppN_cons, List.map_cons, nt_liftN_mkAppN n k as,
      AnnotTerm.liftN_app]

/-- A term fixed by every one-step lift is fixed by every lift. -/
theorem nt_liftN_eq_self_of_one {e : AnnotTerm} (h : ∀ k, AnnotTerm.liftN 1 e k = e) :
    ∀ (n k : Nat), AnnotTerm.liftN n e k = e
  | 0, k => AnnotTerm.liftN_zero e k
  | n + 1, k => by
    rw [show n + 1 = 1 + n from by omega, ← AnnotTerm.liftN_liftN e 1 n k,
      nt_liftN_eq_self_of_one h n k, h k]

/-- **THE PIN'S READING at a deeper depth** (the assembly's `nestEntry`
core): the abstraction re-opened at the parameter variables reads, at
any depth past the opener's, as the container's leaf applied to the
lifted components. -/
theorem nt_denoteMeta_restoredPin {env : Env} (m : EnvModel V env) {φ : Name → Nat} {nP i : Nat}
    {J : Name} {lvls : List Level} {DsE : List Expr} {Ds : List AnnotTerm} {fvsP : List Expr}
    (hlenP : fvsP.length = nP)
    (hidx : ∀ k, k < nP → ∃ ty, fvsP[k]? = some (.fvar k ty))
    (hfv : (Expr.abstractRange (Expr.mkAppN (.const J lvls) DsE) 0 nP 0).hasFvar = false)
    {ci : ConstantInfo} (hf : env.find? J = some ci)
    (hlen : lvls.length = ci.toConstantVal.levelParams.length)
    (hDs : DenoteMetaSpine m.acval env φ nP DsE Ds) :
    denoteMeta m.acval env φ (nP + i)
        (Expr.instSeq fvsP (nP - 1) (Expr.abstractRange (Expr.mkAppN (.const J lvls) DsE) 0 nP 0))
      = some (AnnotTerm.mkAppN (m.acval J (Level.substFn φ ci.toConstantVal.levelParams lvls))
          (Ds.map (·.liftN i 0))) := by
  have hb : (Expr.mkAppN (.const J lvls) DsE).looseBVarsBounded 0 = true := nt_pin_bounded hDs
  have hws : Expr.WScoped nP (Expr.mkAppN (.const J lvls) DsE).eraseAnnots :=
    nt_WScoped_eraseAnnots_of_fvarsBelow (nt_pin_fvarsBelow hfv)
  have hread : denoteMeta m.acval env φ nP (Expr.mkAppN (.const J lvls) DsE)
      = some (AnnotTerm.mkAppN
          (m.acval J (Level.substFn φ ci.toConstantVal.levelParams lvls)) Ds) :=
    denoteMeta_mkAppN hDs (denoteMeta_const hf hlen)
  rw [denoteMeta_congr_eraseAnnots (nP + i) _ (Expr.mkAppN (.const J lvls) DsE)
      (Expr.eraseAnnots_openAbstract _ hb fvsP hlenP hidx),
    ← denoteMeta_eraseAnnots (nP + i) (Expr.mkAppN (.const J lvls) DsE),
    denoteMeta_lift m.acval_closed hws (nP + i) (Nat.le_add_right _ _),
    denoteMeta_eraseAnnots nP (Expr.mkAppN (.const J lvls) DsE), hread,
    show nP + i - nP = i from by omega]
  simp only [Option.map_some, nt_liftN_mkAppN,
    nt_liftN_eq_self_of_one (m.acval_closed J _) i 0]

end ConLeche.Model
