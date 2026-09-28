module

public import ConLeche.Model.Annot.BitRename
public import ConLeche.Model.Annot.LocList
public import ConLeche.Verify.Inductives.ClassAbs
public import ConLeche.Verify.Level
import ConLeche.Model.Annot.BitInst
import ConLeche.Verify.InstList

public section

/-!
# The class abstraction, READ (PROOFPLAN T3, the substitution law P1)

The class check abstracts every recognised class occurrence of a
constructor's crest to the class's hole (`classAbs`, spec
`classAbsSpec`, `ClassAbs.lean`), top-down, the occurrence matched
SYNTACTICALLY: parameters equal up to the free variables' annotations
(`Expr.eraseFVarTys`) at equal levels, else up to level equivalence
(`Expr.eqUpToLevels`).  This file is the model's reading of that
abstraction.

1. **Equal-up-to readings.**  `Expr.SemEq` — structural equality with
   free variables compared by index, levels by their values at EVERY
   assignment, binder data equal — is what the reading cannot see
   (`denoteMeta_semEq`); both comparisons the abstraction runs land in it
   (`Expr.semEq_of_erasedEq`, `Expr.semEq_of_eqUpToLevels`).
2. **The replacement congruence** (`classAbsSpec_read`), generic in the
   occurrence recogniser `occ`: the abstraction by `occ` and the one by
   its restriction to a set `F` of holes (`occF`) read alike at every
   valuation `Good` admits, PROVIDED every occurrence of a hole outside
   `F` reads (at `Good`) as its head part abstracted by `occF`.  With
   `F = ∅` the second side is the term itself (`classAbsSpec_none`):
   the abstracted term reads as the concrete one when every hole outside
   `F` carries the reading of what it replaced.  With `F` the free holes
   and the own group of a class fact it is the hole form (P1) — see the
   module's last section and the DESIGN record CLASSCHECK / P2B.
3. **The class check's recogniser** (`classOcc?`): an occurrence is its
   class's key up to `SemEq` (`classOcc_spec`), and the recogniser is
   spine-coherent (`classOcc_app`).  Hence `classAbs_read`: at a
   valuation carrying, in every container class's hole slot, the value of
   the class's member-abstracted key, the abstracted term reads as the
   concrete one.  The coarser (defeq) tier `aliasOcc?` is the same
   congruence, its head obligation the defeq's soundness
   (`aliasAbs_read`).
-/

/-! ## 1. What the reading cannot see -/

namespace ConLeche

/-- **Structural equality up to what the reading does not read**: free
variables by index (annotations free), universe levels by their value at
every assignment, binder data equal. -/
@[expose] def Expr.SemEq : Expr → Expr → Prop
  | .bvar i, .bvar j => i = j
  | .fvar i _, .fvar j _ => i = j
  | .sort u, .sort v => ∀ φ, Level.eval φ u = Level.eval φ v
  | .const n us, .const n' us' => n = n' ∧ us.length = us'.length ∧
      ∀ φ, Level.EvalEqList φ us us'
  | .app f a, .app g b => Expr.SemEq f g ∧ Expr.SemEq a b
  | .lam ty b m, .lam ty' b' m' => m = m' ∧ Expr.SemEq ty ty' ∧ Expr.SemEq b b'
  | .forallE ty b m, .forallE ty' b' m' => m = m' ∧ Expr.SemEq ty ty' ∧ Expr.SemEq b b'
  | .letE ty v b, .letE ty' v' b' => Expr.SemEq ty ty' ∧ Expr.SemEq v v' ∧ Expr.SemEq b b'
  | .lit l, .lit l' => l = l'
  | .proj s i e, .proj s' i' e' => s = s' ∧ i = i' ∧ Expr.SemEq e e'
  | _, _ => False

theorem Level.evalEqList_refl (φ : Name → Nat) : ∀ us : List Level, Level.EvalEqList φ us us
  | [] => trivial
  | _ :: us => ⟨rfl, Level.evalEqList_refl φ us⟩

theorem Expr.SemEq.refl : ∀ e : Expr, Expr.SemEq e e := by
  intro e
  induction e <;> simp_all [Expr.SemEq, Level.evalEqList_refl]

/-- Erasure-equal terms are `SemEq`. -/
theorem Expr.semEq_of_erasedEq : ∀ {a b : Expr}, Expr.ErasedEq a b → Expr.SemEq a b := by
  intro a
  induction a with
  | bvar i => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.SemEq]
  | fvar i ty => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.SemEq]
  | sort u => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.SemEq]
  | const n us =>
    intro b h
    cases b <;> simp_all [Expr.ErasedEq, Expr.SemEq, Level.evalEqList_refl]
  | lit l => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.SemEq]
  | app f a ihf iha =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq, Expr.SemEq] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam t bd m iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq, Expr.SemEq] at h ⊢
    exact ⟨h.1, iht h.2.1, ihb h.2.2⟩
  | forallE t bd m iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq, Expr.SemEq] at h ⊢
    exact ⟨h.1, iht h.2.1, ihb h.2.2⟩
  | letE t v bd iht ihv ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq, Expr.SemEq] at h ⊢
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i x ih =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq, Expr.SemEq] at h ⊢
    exact ⟨h.1, h.2.1, ih h.2.2⟩

/-- The annotation-erased comparison is erasure equality. -/
theorem Expr.erasedEq_of_eraseFVarTys : ∀ {a b : Expr},
    a.eraseFVarTys = b.eraseFVarTys → Expr.ErasedEq a b := by
  intro a
  induction a <;> intro b <;> cases b <;>
    simp_all [Expr.eraseFVarTys, Expr.replaceFVars, Expr.ErasedEq]

/-- Pointwise level equivalence is pointwise equal value. -/
theorem Level.evalEqList_of_isEquivList {us vs : List Level}
    (h : Level.isEquivList us vs = some true) :
    us.length = vs.length ∧ ∀ φ, Level.EvalEqList φ us vs := by
  refine ⟨?_, Level.isEquivList_sound h⟩
  have h0 := Level.isEquivList_sound h (fun _ => 0)
  clear h
  induction us generalizing vs with
  | nil => cases vs <;> simp_all [Level.EvalEqList]
  | cons u us ih =>
    cases vs with
    | nil => simp [Level.EvalEqList] at h0
    | cons v vs => simp [ih h0.2]

/-- **The level-equivalence comparison lands in `SemEq`.** -/
theorem Expr.semEq_of_eqUpToLevels : ∀ {a b : Expr},
    Expr.eqUpToLevels a b = true → Expr.SemEq a b := by
  intro a
  induction a with
  | bvar i => intro b h; cases b <;> simp_all [Expr.eqUpToLevels, Expr.SemEq]
  | fvar i ty => intro b h; cases b <;> simp_all [Expr.eqUpToLevels, Expr.SemEq]
  | sort u =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq] at h ⊢
    exact Level.isEquiv_sound (by simpa using h)
  | const n us =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq, Bool.and_eq_true,
      beq_iff_eq] at h ⊢
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, Level.evalEqList_of_isEquivList (by simpa using h2)⟩
  | lit l => intro b h; cases b <;> simp_all [Expr.eqUpToLevels, Expr.SemEq]
  | app f a ihf iha =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq,
      Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam t bd m iht ihb =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq, Bool.and_eq_true,
      beq_iff_eq] at h ⊢
    exact ⟨h.1.1, iht h.1.2, ihb h.2⟩
  | forallE t bd m iht ihb =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq, Bool.and_eq_true,
      beq_iff_eq] at h ⊢
    exact ⟨h.1.1, iht h.1.2, ihb h.2⟩
  | letE t v bd iht ihv ihb =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq,
      Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s i x ih =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq, Bool.and_eq_true,
      beq_iff_eq] at h ⊢
    exact ⟨h.1.1, h.1.2, ih h.2⟩

theorem Expr.SemEq.instantiate1 :
    ∀ {e e' v v' : Expr} {k : Nat}, Expr.SemEq e e' → Expr.SemEq v v' →
      Expr.SemEq (e.instantiate1 v k) (e'.instantiate1 v' k) := by
  intro e
  induction e with
  | bvar i =>
    intro e' v v' k he hv
    match e', he with
    | .bvar j, he =>
      obtain rfl : i = j := he
      simp only [Expr.instantiate1]
      split
      · exact hv
      · split <;> simp [Expr.SemEq]
  | fvar idx ty =>
    intro e' v v' k he hv
    match e', he with
    | .fvar j ty', he => simpa [Expr.instantiate1, Expr.SemEq] using he
  | sort u =>
    intro e' v v' k he hv
    match e', he with
    | .sort u', he => simpa [Expr.instantiate1, Expr.SemEq] using he
  | const n us =>
    intro e' v v' k he hv
    match e', he with
    | .const n' us', he => simpa [Expr.instantiate1, Expr.SemEq] using he
  | app f a ihf iha =>
    intro e' v v' k he hv
    match e', he with
    | .app g b, he => exact ⟨ihf he.1 hv, iha he.2 hv⟩
  | lam ty body m ihty ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .lam ty' body' m', he => exact ⟨he.1, ihty he.2.1 hv, ihbody he.2.2 hv⟩
  | forallE ty body m ihty ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .forallE ty' body' m', he => exact ⟨he.1, ihty he.2.1 hv, ihbody he.2.2 hv⟩
  | letE ty vl body ihty ihv ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .letE ty' vl' body', he => exact ⟨ihty he.1 hv, ihv he.2.1 hv, ihbody he.2.2 hv⟩
  | lit l =>
    intro e' v v' k he hv
    match e', he with
    | .lit l', he => simpa [Expr.instantiate1, Expr.SemEq] using he
  | proj sn i pe ih =>
    intro e' v v' k he hv
    match e', he with
    | .proj sn' i' pe', he => exact ⟨he.1, he.2.1, ih he.2.2 hv⟩

/-- `SemEq` terms have the same loose bound variables. -/
theorem Expr.SemEq.looseBVarsBounded : ∀ {a b : Expr}, Expr.SemEq a b →
    ∀ k, a.looseBVarsBounded k = b.looseBVarsBounded k := by
  intro a
  induction a with
  | bvar i => intro b h k; cases b <;> simp_all [Expr.SemEq, Expr.looseBVarsBounded]
  | app f a ihf iha =>
    intro b h k
    cases b <;> simp only [Expr.SemEq] at h
    simp [Expr.looseBVarsBounded, ihf h.1, iha h.2]
  | lam t bd m iht ihb =>
    intro b h k
    cases b <;> simp only [Expr.SemEq] at h
    simp [Expr.looseBVarsBounded, iht h.2.1, ihb h.2.2]
  | forallE t bd m iht ihb =>
    intro b h k
    cases b <;> simp only [Expr.SemEq] at h
    simp [Expr.looseBVarsBounded, iht h.2.1, ihb h.2.2]
  | letE t v bd iht ihv ihb =>
    intro b h k
    cases b <;> simp only [Expr.SemEq] at h
    simp [Expr.looseBVarsBounded, iht h.1, ihv h.2.1, ihb h.2.2]
  | proj s i x ih =>
    intro b h k
    cases b <;> simp only [Expr.SemEq] at h
    simp [Expr.looseBVarsBounded, ih h.2.2]
  | _ => intro b h k; cases b <;> simp_all [Expr.SemEq, Expr.looseBVarsBounded]

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo BinderMeta)

universe w

section Read

variable {env : Env} {φ : Name → Nat} {acval : Name → (Name → Nat) → AnnotTerm}

/-- **`SemEq` terms read alike** — (i) and (ii) of the P2A record: the
annotation-erased and the level-equivalent comparison. -/
theorem denoteMeta_semEq :
    ∀ {e₁ e₂ : Expr}, Expr.SemEq e₁ e₂ →
      ∀ d : Nat, denoteMeta acval env φ d e₁ = denoteMeta acval env φ d e₂
  | .bvar i, e₂, he, _ => by
    match e₂, he with
    | .bvar j, he => obtain rfl : i = j := he; rfl
  | .fvar i ty, e₂, he, d => by
    match e₂, he with
    | .fvar j ty', he =>
      obtain rfl : i = j := he
      simp [denoteMeta_fvar]
  | .sort u, e₂, he, _ => by
    match e₂, he with
    | .sort u', he => rw [denoteMeta, denoteMeta, he φ]
  | .const n us, e₂, he, _ => by
    match e₂, he with
    | .const n' us', he =>
      obtain ⟨rfl, hlen, hev⟩ := he
      rw [denoteMeta, denoteMeta]
      cases env.find? n with
      | none => rfl
      | some ci =>
        simp only [hlen, Level.substFn_congr (hev φ)]
  | .app f a, e₂, he, d => by
    match e₂, he with
    | .app g b, he =>
      obtain ⟨h1, h2⟩ := he
      simp only [denoteMeta_app, denoteMeta_semEq h1 d, denoteMeta_semEq h2 d]
  | .forallE ty body m, e₂, he, d => by
    match e₂, he with
    | .forallE ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ := he
      simp only [denoteMeta_forallE, denoteMeta_semEq h1 d,
        denoteMeta_semEq (Expr.SemEq.instantiate1 h2
          (show Expr.SemEq (.fvar d ty) (.fvar d ty') from rfl)) (d + 1)]
  | .lam ty body m, e₂, he, d => by
    match e₂, he with
    | .lam ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ := he
      simp only [denoteMeta_lam, denoteMeta_semEq h1 d,
        denoteMeta_semEq (Expr.SemEq.instantiate1 h2
          (show Expr.SemEq (.fvar d ty) (.fvar d ty') from rfl)) (d + 1)]
  | .letE ty vl body, e₂, he, d => by
    match e₂, he with
    | .letE ty' vl' body', he => rw [denoteMeta, denoteMeta]
  | .lit l, e₂, he, _ => by
    match e₂, he with
    | .lit l', he => obtain rfl : l = l' := he; rfl
  | .proj s i e, e₂, he, d => by
    match e₂, he with
    | .proj s' i' e', he =>
      obtain ⟨rfl, rfl, h⟩ := he
      simp only [denoteMeta_proj, denoteMeta_semEq h d]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

end Read

/-! ## 2. The replacement congruence, generic in the recogniser -/

/-- Two optional readings agree: both absent, or both present and
related. -/
@[expose] def OptAgree (P : AnnotTerm → AnnotTerm → Prop) :
    Option AnnotTerm → Option AnnotTerm → Prop
  | some a2, some a1 => P a2 a1
  | none, none => True
  | _, _ => False

theorem OptAgree.refl {P : AnnotTerm → AnnotTerm → Prop} (hP : ∀ a, P a a) :
    ∀ o : Option AnnotTerm, OptAgree P o o
  | none => trivial
  | some a => hP a

/-- **Value agreement** at every admissible base valuation, `d` local
values above it. -/
@[expose] def ValAgree (V : Type w) [SetTheory V] (Good : (Nat → V) → Prop) (d : Nat)
    (a2 a1 : AnnotTerm) : Prop :=
  ∀ (vals : List V) (τ : Nat → V), vals.length = d → Good τ →
    interp V (consList vals τ) a2 = interp V (consList vals τ) a1

/-- A recogniser restricted to the holes `F` keeps: the occurrences of
the other holes are not recognised. -/
@[expose] def occRestrict (occ : Expr → Option (Expr × Nat)) (F : Expr → Bool) :
    Expr → Option (Expr × Nat) := fun x =>
  match occ x with
  | some (h, n) => if F h then some (h, n) else none
  | none => none

theorem occRestrict_eq_none_of {occ : Expr → Option (Expr × Nat)} {F : Expr → Bool} {x h : Expr}
    {n : Nat} (hx : occ x = some (h, n)) (hF : F h = false) : occRestrict occ F x = none := by
  simp [occRestrict, hx, hF]

theorem occRestrict_eq_some_of {occ : Expr → Option (Expr × Nat)} {F : Expr → Bool} {x h : Expr}
    {n : Nat} (hx : occ x = some (h, n)) (hF : F h = true) :
    occRestrict occ F x = some (h, n) := by
  simp [occRestrict, hx, hF]

theorem occRestrict_eq_none {occ : Expr → Option (Expr × Nat)} {F : Expr → Bool} {x : Expr}
    (hx : occ x = none) : occRestrict occ F x = none := by
  simp [occRestrict, hx]

/-- The empty recogniser abstracts nothing. -/
theorem classAbsSpec_none : ∀ e : Expr, classAbsSpec (fun _ => none) none e = e := by
  intro e
  induction e <;> simp_all [classAbsSpec]

theorem occRestrict_false (occ : Expr → Option (Expr × Nat)) :
    occRestrict occ (fun _ => false) = fun _ => none := by
  funext x
  simp only [occRestrict]
  split <;> simp

/-- **What the congruence needs of a recogniser** `occ` and the kept
holes `F`: a recognised occurrence is an application spine whose head
part is recognised with one index fewer (so the abstraction's `some`
mode never leaves the spine), its hole a free variable; and an
occurrence of a hole outside `F` reads, at every admissible valuation,
as its head part abstracted by the restriction. -/
structure AbsReadHyps (V : Type w) [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (H : Nat) (Good : (Nat → V) → Prop)
    (occ : Expr → Option (Expr × Nat)) (F : Expr → Bool) : Prop where
  spine : ∀ x h n, occ x = some (h, n + 1) → ∃ f a, x = .app f a ∧ occ f = some (h, n)
  hole : ∀ x h n, occ x = some (h, n) → ∃ i ty, h = .fvar i ty
  head : ∀ x h, occ x = some (h, 0) → F h = false →
    ∀ d as2 as1, LocList H d as2 → LocList H d as1 →
      OptAgree (ValAgree V Good d) (denoteMeta acval env φ (H + d) h)
        (denoteMeta acval env φ (H + d)
          ((classAbsSpec (occRestrict occ F) none x).instantiateList as1 0))

section Congr

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm} {H : Nat} {Good : (Nat → V) → Prop}
  {occ : Expr → Option (Expr × Nat)} {F : Expr → Bool}

theorem optAgree_refl' {d : Nat} (o : Option AnnotTerm) : OptAgree (ValAgree V Good d) o o :=
  OptAgree.refl (fun _ _ _ _ _ => rfl) o

/-- Application congruence of the agreement. -/
theorem optAgree_app {d : Nat} {f2 f1 a2 a1 : Option AnnotTerm}
    (hf : OptAgree (ValAgree V Good d) f2 f1) (ha : OptAgree (ValAgree V Good d) a2 a1) :
    OptAgree (ValAgree V Good d) (do let f ← f2; let a ← a2; some (.app f a))
      (do let f ← f1; let a ← a1; some (.app f a)) := by
  cases f2 <;> cases f1 <;> cases a2 <;> cases a1 <;> simp_all [OptAgree]
  intro vals τ hvl hτ
  simp [hf vals τ hvl hτ, ha vals τ hvl hτ]

theorem interp_projAV_congr {ρ : Nat → V} :
    ∀ (n : Nat) {e2 e1 : AnnotTerm}, interp V ρ e2 = interp V ρ e1 →
      interp V ρ (projAV n e2) = interp V ρ (projAV n e1)
  | 0, _, _, h => by simp [projAV, h]
  | n + 1, _, _, h => interp_projAV_congr n (by simp [h])

/-- A hole read at depth `H + d`, opened or not. -/
theorem hole_inst {h : Expr} (hh : ∃ i ty, h = .fvar i ty) (as : List Expr) :
    h.instantiateList as 0 = h := by
  obtain ⟨i, ty, rfl⟩ := hh
  simp [Expr.instantiateList]

/-- Two openings at the same indices read alike. -/
theorem denoteMeta_inst_locList {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2)
    (h1 : LocList H d as1) (e : Expr) :
    denoteMeta acval env φ (H + d) (e.instantiateList as2 0)
      = denoteMeta acval env φ (H + d) (e.instantiateList as1 0) := by
  apply denoteMeta_semEq
  have key : ∀ (e : Expr) (k : Nat), Expr.SemEq (e.instantiateList as2 k)
      (e.instantiateList as1 k) := by
    intro e
    induction e with
    | bvar j =>
      intro k
      by_cases hjk : j < k
      · simp only [Expr.instantiateList, if_pos hjk]
        exact Expr.SemEq.refl _
      · by_cases hj : j - k < d
        · obtain ⟨ty2, hty2⟩ := h2.2 (j - k) hj
          obtain ⟨ty1, hty1⟩ := h1.2 (j - k) hj
          obtain ⟨hl2, hg2⟩ := List.getElem?_eq_some_iff.mp hty2
          obtain ⟨hl1, hg1⟩ := List.getElem?_eq_some_iff.mp hty1
          simp only [Expr.instantiateList, if_neg hjk, dif_pos hl2, dif_pos hl1, hg2, hg1]
          exact rfl
        · simp only [Expr.instantiateList, if_neg hjk, h2.1, h1.1, dif_neg hj]
          exact Expr.SemEq.refl _
    | app f a ihf iha =>
      intro k; simp only [Expr.instantiateList]; exact ⟨ihf k, iha k⟩
    | lam t b m iht ihb =>
      intro k; simp only [Expr.instantiateList]; exact ⟨rfl, iht k, ihb (k + 1)⟩
    | forallE t b m iht ihb =>
      intro k; simp only [Expr.instantiateList]; exact ⟨rfl, iht k, ihb (k + 1)⟩
    | letE t v b iht ihv ihb =>
      intro k; simp only [Expr.instantiateList]; exact ⟨iht k, ihv k, ihb (k + 1)⟩
    | proj s i x ih =>
      intro k; simp only [Expr.instantiateList]; exact ⟨rfl, rfl, ih k⟩
    | _ => intro k; simp only [Expr.instantiateList]; exact Expr.SemEq.refl _
  exact key e 0

set_option maxHeartbeats 1600000 in
/-- **The replacement congruence** (see the module docstring): the
abstraction by `occ` and by its restriction to `F` read alike, opened at
any `d` locals, at every admissible valuation — and the `some` mode's
version at a recognised occurrence. -/
theorem classAbsSpec_read_both (hyp : AbsReadHyps V acval env φ H Good occ F) :
    ∀ e : Expr,
      (∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V Good d)
          (denoteMeta acval env φ (H + d) ((classAbsSpec occ none e).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict occ F) none e).instantiateList as1 0))) ∧
      (∀ h n, occ e = some (h, n) →
        ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V Good d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec occ (some (h, n)) e).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((if F h then classAbsSpec (occRestrict occ F) (some (h, n)) e
              else classAbsSpec (occRestrict occ F) none e).instantiateList as1 0))) := by
  -- the `some` mode at a head part (index count `0`)
  have hzero : ∀ (e h : Expr), occ e = some (h, 0) →
      ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
      OptAgree (ValAgree V Good d)
        (denoteMeta acval env φ (H + d)
          ((classAbsSpec occ (some (h, 0)) e).instantiateList as2 0))
        (denoteMeta acval env φ (H + d)
          ((if F h then classAbsSpec (occRestrict occ F) (some (h, 0)) e
            else classAbsSpec (occRestrict occ F) none e).instantiateList as1 0)) := by
    intro e h he d as2 as1 h2 h1
    have hh := hyp.hole e h 0 he
    cases hF : F h with
    | true =>
      simp only [classAbsSpec, if_true, hole_inst hh]
      exact optAgree_refl' (V := V) _
    | false =>
      simp only [classAbsSpec, Bool.false_eq_true, if_false, hole_inst hh]
      exact hyp.head e h he hF d as2 as1 h2 h1
  intro e
  induction e with
  | app f a ihf iha =>
    -- the `some` mode, by the index count
    have hsome : ∀ h n, occ (.app f a) = some (h, n) →
        ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V Good d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec occ (some (h, n)) (.app f a)).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((if F h then classAbsSpec (occRestrict occ F) (some (h, n)) (.app f a)
              else classAbsSpec (occRestrict occ F) none (.app f a)).instantiateList as1 0)) := by
      intro h n he d as2 as1 h2 h1
      rcases n with _ | n
      · exact hzero _ h he d as2 as1 h2 h1
      · obtain ⟨f', a', hfa, hf'⟩ := hyp.spine _ h n he
        obtain ⟨rfl, rfl⟩ : f = f' ∧ a = a' := by simpa using hfa
        have hF1 := ihf.2 h n hf' d as2 as1 h2 h1
        have hA1 := iha.1 d as2 as1 h2 h1
        cases hF : F h with
        | true =>
          simp only [hF, if_true] at hF1 ⊢
          simp only [classAbsSpec, Expr.instantiateList, denoteMeta_app]
          exact optAgree_app hF1 hA1
        | false =>
          simp only [hF, Bool.false_eq_true, if_false] at hF1 ⊢
          have hR : occRestrict occ F (.app f a) = none := occRestrict_eq_none_of he hF
          simp only [classAbsSpec, hR, Expr.instantiateList, denoteMeta_app]
          exact optAgree_app hF1 hA1
    refine ⟨fun d as2 as1 h2 h1 => ?_, hsome⟩
    cases he : occ (.app f a) with
    | none =>
      have hR : occRestrict occ F (.app f a) = none := occRestrict_eq_none he
      simp only [classAbsSpec, he, hR, Expr.instantiateList, denoteMeta_app]
      exact optAgree_app (ihf.1 d as2 as1 h2 h1) (iha.1 d as2 as1 h2 h1)
    | some p =>
      obtain ⟨h, n⟩ := p
      have hs := hsome h n he d as2 as1 h2 h1
      -- the `none` mode at a recognised occurrence IS the `some` mode
      have hL : classAbsSpec occ none (.app f a) = classAbsSpec occ (some (h, n)) (.app f a) := by
        rcases n with _ | n
        · simp [classAbsSpec, he]
        · simp [classAbsSpec, he]
      rw [hL]
      cases hF : F h with
      | true =>
        have hR : occRestrict occ F (.app f a) = some (h, n) := occRestrict_eq_some_of he hF
        have hL' : classAbsSpec (occRestrict occ F) none (.app f a)
            = classAbsSpec (occRestrict occ F) (some (h, n)) (.app f a) := by
          rcases n with _ | n
          · simp [classAbsSpec, hR]
          · simp [classAbsSpec, hR]
        rw [hL']
        simpa [hF] using hs
      | false => simpa [hF] using hs
  | lam ty b bm iht ihb | forallE ty b bm iht ihb =>
    refine ⟨fun d as2 as1 h2 h1 => ?_, fun h n he => ?_⟩
    rotate_left
    · rcases n with _ | n
      · exact hzero _ h he
      · obtain ⟨f', a', hfa, -⟩ := hyp.spine _ h n he
        exact nomatch hfa
    have hT := iht.1 d as2 as1 h2 h1
    simp only [classAbsSpec, Expr.instantiateList]
    first
    | rw [denoteMeta_lam, denoteMeta_lam]
    | rw [denoteMeta_forallE, denoteMeta_forallE]
    revert hT
    cases hA2 : denoteMeta acval env φ (H + d)
        ((classAbsSpec occ none ty).instantiateList as2 0)
      <;> cases hA1 : denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict occ F) none ty).instantiateList as1 0)
      <;> simp [OptAgree]
    rename_i A2 A1
    intro hA
    rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons]
    have hB := ihb.1 (d + 1) _ _ (h2.cons ((classAbsSpec occ none ty).instantiateList as2 0))
      (h1.cons ((classAbsSpec (occRestrict occ F) none ty).instantiateList as1 0))
    rw [show H + (d + 1) = H + d + 1 by omega] at hB
    revert hB
    cases denoteMeta acval env φ (H + d + 1)
        ((classAbsSpec occ none b).instantiateList
          (Expr.fvar (H + d) ((classAbsSpec occ none ty).instantiateList as2 0) :: as2) 0)
      <;> cases denoteMeta acval env φ (H + d + 1)
        ((classAbsSpec (occRestrict occ F) none b).instantiateList
          (Expr.fvar (H + d) ((classAbsSpec (occRestrict occ F) none ty).instantiateList as1 0)
            :: as1) 0)
      <;> simp [OptAgree]
    rename_i b2 b1
    intro hb vals τ hvl hτ
    have hbx : ∀ x : V, interp V (cons x (consList vals τ)) b2
        = interp V (cons x (consList vals τ)) b1 := by
      intro x
      have := hb (vals ++ [x]) τ (by simp [hvl]) hτ
      simpa [consList_append] using this
    first
    | (simp only [interp_lam, hA vals τ hvl hτ]; exact lamR_congr fun x _ => hbx x)
    | (simp only [interp_pi, hA vals τ hvl hτ]; exact piR_congr fun x _ => hbx x)
  | proj sn i x ihx =>
    refine ⟨fun d as2 as1 h2 h1 => ?_, fun h n he => ?_⟩
    rotate_left
    · rcases n with _ | n
      · exact hzero _ h he
      · obtain ⟨f', a', hfa, -⟩ := hyp.spine _ h n he
        exact nomatch hfa
    have hX := ihx.1 d as2 as1 h2 h1
    simp only [classAbsSpec, Expr.instantiateList, denoteMeta_proj]
    revert hX
    cases denoteMeta acval env φ (H + d) ((classAbsSpec occ none x).instantiateList as2 0)
      <;> cases denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict occ F) none x).instantiateList as1 0)
      <;> simp [OptAgree]
    rename_i e2 e1
    intro he
    cases env.findProj? sn i with
    | some entry =>
      intro vals τ hvl hτ
      exact interp_projAV_congr _ (he vals τ hvl hτ)
    | none =>
      rcases i with _ | _ | i
      · intro vals τ hvl hτ
        simp [he vals τ hvl hτ]
      · intro vals τ hvl hτ
        simp [he vals τ hvl hτ]
      · simp [AnnotTerm.projPair?]
  | letE t v b =>
    refine ⟨fun d as2 as1 h2 h1 => ?_, fun h n he => ?_⟩
    rotate_left
    · rcases n with _ | n
      · exact hzero _ h he
      · obtain ⟨f', a', hfa, -⟩ := hyp.spine _ h n he
        exact nomatch hfa
    simp only [classAbsSpec, Expr.instantiateList]
    rw [denoteMeta, denoteMeta]
    trivial
  | _ =>
    refine ⟨fun d as2 as1 h2 h1 => ?_, fun h n he => ?_⟩
    rotate_left
    · rcases n with _ | n
      · exact hzero _ h he
      · obtain ⟨f', a', hfa, -⟩ := hyp.spine _ h n he
        exact nomatch hfa
    simp only [classAbsSpec]
    rw [denoteMeta_inst_locList h2 h1]
    exact optAgree_refl' (V := V) _

/-- **The replacement congruence.** -/
theorem classAbsSpec_read (hyp : AbsReadHyps V acval env φ H Good occ F) (e : Expr) {d : Nat}
    {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V Good d)
      (denoteMeta acval env φ (H + d) ((classAbsSpec occ none e).instantiateList as2 0))
      (denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict occ F) none e).instantiateList as1 0)) :=
  (classAbsSpec_read_both hyp e).1 d as2 as1 h2 h1

end Congr

/-! ## 3. The class check's recogniser -/

section Occ

open ConLeche (ClassInfo classOcc? classAbs)

theorem Expr.mkAppN_append' (f : Expr) (as bs : List Expr) :
    Expr.mkAppN f (as ++ bs) = Expr.mkAppN (Expr.mkAppN f as) bs := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih _

/-- A term is its head applied to its arguments. -/
theorem Expr.mkAppN_getAppFn_getAppArgs : ∀ e : Expr,
    Expr.mkAppN e.getAppFn e.getAppArgs = e
  | .app f a => by
    rw [Expr.getAppFn, Expr.getAppArgs, Expr.mkAppN_append', Expr.mkAppN_getAppFn_getAppArgs f]
    rfl
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .proj .. => rfl

/-- `SemEq` spines. -/
theorem Expr.SemEq.mkAppN : ∀ {as bs : List Expr} {f g : Expr}, Expr.SemEq f g →
    as.length = bs.length → (∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b → Expr.SemEq a b) →
    Expr.SemEq (Expr.mkAppN f as) (Expr.mkAppN g bs)
  | [], [], _, _, hfg, _, _ => hfg
  | a :: as, b :: bs, f, g, hfg, hl, hab =>
    Expr.SemEq.mkAppN (as := as) (bs := bs) (f := .app f a) (g := .app g b)
      ⟨hfg, hab 0 a b rfl rfl⟩ (by simpa using hl) (fun i a' b' h1 h2 => hab (i + 1) a' b' h1 h2)
  | [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _ => by simp at hl

theorem Expr.erasedEq_eraseFVarTys : ∀ e : Expr, Expr.ErasedEq e e.eraseFVarTys := by
  intro e
  induction e <;> simp_all [Expr.eraseFVarTys, Expr.replaceFVars, Expr.ErasedEq]

theorem Expr.eraseFVarTys_idem (e : Expr) : e.eraseFVarTys.eraseFVarTys = e.eraseFVarTys := by
  induction e <;> simp_all [Expr.eraseFVarTys, Expr.replaceFVars]

/-- Erasure-equal lists are pointwise `SemEq`. -/
theorem semEq_of_map_erase {as bs : List Expr}
    (h : as.map Expr.eraseFVarTys = bs.map Expr.eraseFVarTys) :
    as.length = bs.length ∧ ∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b → Expr.SemEq a b := by
  refine ⟨by simpa using congrArg List.length h, fun i a b ha hb => ?_⟩
  have := congrArg (·[i]?) h
  simp only [List.getElem?_map, ha, hb, Option.map_some, Option.some.injEq] at this
  exact Expr.semEq_of_erasedEq (Expr.erasedEq_of_eraseFVarTys this)

/-- Pointwise level-equivalent lists are pointwise `SemEq`. -/
theorem semEq_of_zip_eqUpToLevels {as bs : List Expr}
    (h : ((as.zip bs).all fun (a, b) => a.eqUpToLevels b) = true) :
    ∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b → Expr.SemEq a b := by
  intro i a b ha hb
  rw [List.all_eq_true] at h
  have hz : (as.zip bs)[i]? = some (a, b) := by simp [List.getElem?_zip_eq_some, ha, hb]
  exact Expr.semEq_of_eqUpToLevels (h (a, b) (List.mem_of_getElem? hz))

/-- **What the class check's recogniser needs of the classes**: every
container class's hole is a variable below the frame `H`; its erased
parameters are its parameters erased, as many as the container's; its
key is scoped at `H` with no loose bound variable; classes of one
inductive have one parameter count. -/
structure ClassOccWF (cls : List ClassInfo) (H : Nat) : Prop where
  hole : ∀ c ∈ cls, ∀ h, c.hole = some h → ∃ i ty, h = .fvar i ty ∧ i < H
  dsE : ∀ c ∈ cls, c.hole.isSome → c.dsE = c.dsA.map Expr.eraseFVarTys
  len : ∀ c ∈ cls, c.hole.isSome → c.dsA.length = c.nPc
  keyScoped : ∀ c ∈ cls, c.hole.isSome →
    Expr.WScoped H (Expr.mkAppN (.const c.key.ind c.key.lvls) c.dsA) ∧
    (Expr.mkAppN (.const c.key.ind c.key.lvls) c.dsA).looseBVarsBounded 0 = true
  nPc : ∀ c ∈ cls, ∀ c' ∈ cls, c.hole.isSome → c'.hole.isSome → c.key.ind = c'.key.ind →
    c.nPc = c'.nPc

/-- A class's member-abstracted key. -/
@[expose] def classKeyA (c : ClassInfo) : Expr := Expr.mkAppN (.const c.key.ind c.key.lvls) c.dsA

/-- **An occurrence is its class's key**, up to `SemEq`, applied to the
index arguments. -/
theorem classOcc_spec {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {x h : Expr}
    {n : Nat} (hx : classOcc? cls x = some (h, n)) :
    ∃ c ∈ cls, c.hole = some h ∧ ∃ us, x.getAppFn = .const c.key.ind us ∧
      c.nPc ≤ x.getAppArgs.length ∧ n = x.getAppArgs.length - c.nPc ∧
      Expr.SemEq (Expr.mkAppN (.const c.key.ind us) (x.getAppArgs.take c.nPc)) (classKeyA c) := by
  unfold classOcc? at hx
  split at hx
  · rename_i I us hI
    dsimp only at hx
    split at hx
    · exact nomatch hx
    · rename_i cs c0 rest hcs
      have hmem : ∀ c ∈ c0 :: rest, c ∈ cls ∧ c.hole.isSome ∧ c.key.ind = I ∧
          c.nPc ≤ x.getAppArgs.length := by
        intro c hc
        rw [← hcs] at hc
        simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        exact ⟨hc.1, hc.2.1.1, hc.2.1.2, hc.2.2⟩
      obtain ⟨hc0, hc0h, hc0I, -⟩ := hmem c0 (List.mem_cons_self ..)
      -- the pick, from either search
      have hpick : ∀ c, c ∈ c0 :: rest →
          (c.hole.map fun h' => (h', x.getAppArgs.length - c.nPc)) = some (h, n) →
          (Level.isEquivList us c.key.lvls = some true ∨ us = c.key.lvls) →
          ((x.getAppArgs.take c0.nPc).map Expr.eraseFVarTys = c.dsE ∨
            ((x.getAppArgs.take c0.nPc).length = c.dsA.length ∧
              (((x.getAppArgs.take c0.nPc).zip c.dsA).all fun (a, b) => a.eqUpToLevels b) =
                true)) →
          ∃ c ∈ cls, c.hole = some h ∧ ∃ us, x.getAppFn = .const c.key.ind us ∧
            c.nPc ≤ x.getAppArgs.length ∧ n = x.getAppArgs.length - c.nPc ∧
            Expr.SemEq (Expr.mkAppN (.const c.key.ind us) (x.getAppArgs.take c.nPc))
              (classKeyA c) := by
        intro c hc hp hlv hps
        obtain ⟨hcc, hch, hcI, hcle⟩ := hmem c hc
        have hN : c0.nPc = c.nPc := hwf.nPc c0 hc0 c hcc hc0h hch (hc0I.trans hcI.symm)
        obtain ⟨h', hh'⟩ := Option.isSome_iff_exists.mp hch
        rw [hh'] at hp
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        refine ⟨c, hcc, hh', us, by rw [hI, hcI], hcle, rfl, ?_⟩
        rw [← hN]
        unfold classKeyA
        have hlvl : us.length = c.key.lvls.length ∧ ∀ φ, Level.EvalEqList φ us c.key.lvls := by
          rcases hlv with hlv | rfl
          · exact Level.evalEqList_of_isEquivList hlv
          · exact ⟨rfl, fun φ => Level.evalEqList_refl φ _⟩
        rcases hps with hps | ⟨hl, hz⟩
        · rw [hwf.dsE c hcc hch] at hps
          obtain ⟨hl, hpw⟩ := semEq_of_map_erase hps
          exact Expr.SemEq.mkAppN ⟨rfl, hlvl⟩ hl hpw
        · exact Expr.SemEq.mkAppN ⟨rfl, hlvl⟩ hl (semEq_of_zip_eqUpToLevels hz)
      split at hx
      · rename_i c hfind
        have hc := List.mem_of_find?_eq_some hfind
        have hcond := List.find?_some hfind
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        exact hpick c hc hx (Or.inr hcond.1) (Or.inl hcond.2)
      · split at hx
        · rename_i c hfind
          have hc := List.mem_of_find?_eq_some hfind
          have hcond := List.find?_some hfind
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hcond
          obtain ⟨hlv, hps⟩ := hcond
          refine hpick c hc hx (Or.inl hlv) ?_
          rcases hps with hps | ⟨hl, hz⟩
          · exact Or.inl hps
          · exact Or.inr ⟨hl, hz⟩
        · exact nomatch hx
  · exact nomatch hx

/-- **The recogniser is spine-coherent**: an occurrence with index
arguments left is an application whose function part is the same
occurrence with one index fewer. -/
theorem classOcc_app {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {x h : Expr}
    {n : Nat} (hx : classOcc? cls x = some (h, n + 1)) :
    ∃ f a, x = .app f a ∧ classOcc? cls f = some (h, n) := by
  obtain ⟨c, hc, hch, us, hfn, hle, hn, -⟩ := classOcc_spec hwf hx
  cases x with
  | app f a =>
    refine ⟨f, a, rfl, ?_⟩
    have hargs : (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] := rfl
    have hfn' : f.getAppFn = .const c.key.ind us := hfn
    rw [hargs, List.length_append, List.length_singleton] at hn
    have hN : c.nPc ≤ f.getAppArgs.length := by omega
    have hchs : c.hole.isSome := by rw [hch]; rfl
    have hfilt : cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
          decide (c'.nPc ≤ (f.getAppArgs ++ [a]).length))
        = cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
          decide (c'.nPc ≤ f.getAppArgs.length)) := by
      apply List.filter_congr
      intro c' hc'
      by_cases hh : c'.hole.isSome
      · by_cases hI : c'.key.ind = c.key.ind
        · have := hwf.nPc c' hc' c hc hh hchs hI
          simp [hh, hI, this]
          omega
        · have hI' : (c'.key.ind == c.key.ind) = false := by simpa using hI
          simp [hI']
      · simp [hh]
    unfold classOcc? at hx ⊢
    rw [show (Expr.app f a).getAppFn = f.getAppFn from rfl, hfn'] at hx
    rw [hfn']
    dsimp only at hx ⊢
    rw [hargs, hfilt] at hx
    have hmem : ∀ c', c' ∈ cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
        decide (c'.nPc ≤ f.getAppArgs.length)) → c'.nPc = c.nPc := by
      intro c' hc'
      simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
      exact hwf.nPc c' hc'.1 c hc hc'.2.1.1 hchs hc'.2.1.2
    revert hmem hx
    generalize cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
        decide (c'.nPc ≤ f.getAppArgs.length)) = cs
    intro hx hmem
    match cs, hx, hmem with
    | [], hx, _ => exact nomatch hx
    | c0 :: rest, hx, hmem =>
      have h0 := hmem c0 (List.mem_cons_self ..)
      have htake : (f.getAppArgs ++ [a]).take c0.nPc = f.getAppArgs.take c0.nPc :=
        List.take_append_of_le_length (by omega)
      simp only [htake, List.length_append, List.length_singleton] at hx
      simp only
      have hpk : ∀ c', c' ∈ c0 :: rest → ∀ o : Option (Expr × Nat),
          (c'.hole.map fun h' => (h', f.getAppArgs.length + 1 - c'.nPc)) = some (h, n + 1) →
          (c'.hole.map fun h' => (h', f.getAppArgs.length - c'.nPc)) = some (h, n) := by
        intro c' hc' _ hp
        have := hmem c' hc'
        cases hh : c'.hole with
        | none => rw [hh] at hp; exact nomatch hp
        | some h' =>
          rw [hh] at hp
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp ⊢
          exact ⟨hp.1, by omega⟩
      split at hx
      · rename_i c1 hf1
        try rw [hf1]
        exact hpk c1 (List.mem_of_find?_eq_some hf1) none hx
      · rename_i hf1
        try rw [hf1]
        split at hx
        · rename_i c1 hf2
          try rw [hf2]
          exact hpk c1 (List.mem_of_find?_eq_some hf2) none hx
        · exact nomatch hx
  | _ =>
    simp only [Expr.getAppArgs, List.length_nil] at hn hle
    omega

/-- A recognised occurrence with no index argument left is its
parameters' spine, its class's key up to `SemEq`. -/
theorem classOcc_head {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {x h : Expr}
    (hx : classOcc? cls x = some (h, 0)) :
    ∃ c ∈ cls, c.hole = some h ∧ Expr.SemEq x (classKeyA c) := by
  obtain ⟨c, hc, hch, us, hfn, hle, hn, hsem⟩ := classOcc_spec hwf hx
  refine ⟨c, hc, hch, ?_⟩
  rw [List.take_of_length_le (by omega), ← hfn, Expr.mkAppN_getAppFn_getAppArgs] at hsem
  exact hsem

end Occ

/-! ## 4. The abstracted term reads as the concrete one (T3, true values) -/

section True

open ConLeche (ClassInfo classOcc? classAbs)

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm}

/-- **The true class valuation**: every container class's hole slot
holds the value of the class's member-abstracted key (read at the
frame `H`). -/
@[expose] def ClassesTrue (V : Type w) [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (cls : List ClassInfo) (H : Nat) (τ : Nat → V) : Prop :=
  ∀ c ∈ cls, ∀ i ty, c.hole = some (.fvar i ty) → ∀ a,
    denoteMeta acval env φ H (classKeyA c) = some a → τ (H - 1 - i) = interp V τ a

/-- A hole read `d` locals above the frame, against a frame-scoped term
lifted: the agreement is the valuation's equation at the hole. -/
theorem hole_agree_lift
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {H : Nat} {Good : (Nat → V) → Prop} {i : Nat} (hi : i < H) (ty : Expr) {K x : Expr}
    (hK : Expr.WScoped H K) (hKb : K.looseBVarsBounded 0 = true) (hx : Expr.SemEq x K)
    (hden : (denoteMeta acval env φ H K).isSome)
    (hgood : ∀ τ, Good τ → ∀ a, denoteMeta acval env φ H K = some a → τ (H - 1 - i) = interp V τ a)
    {d : Nat} {as1 : List Expr} :
    OptAgree (ValAgree V Good d) (denoteMeta acval env φ (H + d) (.fvar i ty))
      (denoteMeta acval env φ (H + d) (x.instantiateList as1 0)) := by
  have hxb : x.looseBVarsBounded 0 = true := by rw [Expr.SemEq.looseBVarsBounded hx 0]; exact hKb
  rw [Expr.instantiateList_eq_self hxb, denoteMeta_semEq hx, denoteMeta_lift hacl hK (H + d)
    (by omega), denoteMeta_fvar]
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hden
  rw [ha]
  simp only [Option.map_some, OptAgree]
  intro vals τ hvl hτ
  rw [interp_bvar, show H + d - 1 - i = (H - 1 - i) + vals.length by omega, consList_apply_add,
    hgood τ hτ a ha, show H + d - H = vals.length by omega, interp_liftN, shiftE_consList]

/-- **T3 at true values** (the substitution law's ground case): at every
valuation carrying the true class values (`ClassesTrue`), the class
abstraction of a term reads as the term — opened at any `d` locals. -/
theorem classAbs_read
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    (hden : ∀ c ∈ cls, c.hole.isSome → (denoteMeta acval env φ H (classKeyA c)).isSome)
    (e : Expr) {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V (ClassesTrue V acval env φ cls H) d)
      (denoteMeta acval env φ (H + d) ((classAbs cls e).instantiateList as2 0))
      (denoteMeta acval env φ (H + d) (e.instantiateList as1 0)) := by
  have hyp : AbsReadHyps V acval env φ H (ClassesTrue V acval env φ cls H) (classOcc? cls)
      (fun _ => false) := by
    refine ⟨fun x h n hx => classOcc_app hwf hx, fun x h n hx => ?_, fun x h hx _ d' as2' as1' _ _ => ?_⟩
    · obtain ⟨c, hc, hch, -⟩ := classOcc_spec hwf hx
      obtain ⟨i, ty, rfl, -⟩ := hwf.hole c hc h hch
      exact ⟨i, ty, rfl⟩
    · obtain ⟨c, hc, hch, hsem⟩ := classOcc_head hwf hx
      obtain ⟨i, ty, rfl, hi⟩ := hwf.hole c hc h hch
      have hchs : c.hole.isSome := by rw [hch]; rfl
      rw [occRestrict_false, classAbsSpec_none]
      exact hole_agree_lift hacl hi ty (hwf.keyScoped c hc hchs).1 (hwf.keyScoped c hc hchs).2
        hsem (hden c hc hchs) (fun τ hτ a ha => hτ c hc i ty hch a ha)
  have h := classAbsSpec_read hyp e h2 h1
  rwa [occRestrict_false, classAbsSpec_none, ← classAbs_eq_spec] at h

end True

/-! ## 5. The coarser tier: aliases -/

section Alias

open ConLeche (ClassInfo ClassAlias aliasOcc? classAbs classAbsGo)

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm}

/-- An alias's key: its inductive at its levels, applied to its
(hole-form, annotation-erased) parameters. -/
@[expose] def aliasKey (a : ClassAlias) : Expr := Expr.mkAppN (.const a.ind a.lvls) a.ps

/-- **What the alias recogniser needs**: every alias's hole a variable
below the frame, its parameters as many as its parameter count, its key
frame-scoped with no loose bound variable. -/
structure AliasWF (al : List ClassAlias) (H : Nat) : Prop where
  hole : ∀ a ∈ al, ∃ i ty, a.hole = .fvar i ty ∧ i < H
  len : ∀ a ∈ al, a.ps.length = a.nPc
  keyScoped : ∀ a ∈ al, Expr.WScoped H (aliasKey a) ∧ (aliasKey a).looseBVarsBounded 0 = true

theorem aliasOcc_spec {al : List ClassAlias} {x h : Expr} {n : Nat}
    (hx : aliasOcc? al x = some (h, n)) :
    ∃ a ∈ al, a.hole = h ∧ ∃ us, x.getAppFn = .const a.ind us ∧ a.nPc ≤ x.getAppArgs.length ∧
      n = x.getAppArgs.length - a.nPc ∧ Level.isEquivList us a.lvls = some true ∧
      (x.getAppArgs.take a.nPc).map Expr.eraseFVarTys = a.ps := by
  unfold aliasOcc? at hx
  split at hx
  · rename_i I us hI
    dsimp only at hx
    obtain ⟨a, hfind, hpa⟩ := Option.map_eq_some_iff.mp hx
    have ha := List.mem_of_find?_eq_some hfind
    have hc := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hI', hle⟩, hlv⟩, hps⟩ := hc
    simp only [Prod.mk.injEq] at hpa
    exact ⟨a, ha, hpa.1, us, by rw [hI, hI'], hle, hpa.2.symm, hlv, hps⟩
  · exact nomatch hx

theorem aliasOcc_app {al : List ClassAlias} {x h : Expr} {n : Nat}
    (hx : aliasOcc? al x = some (h, n + 1)) :
    ∃ f a, x = .app f a ∧ aliasOcc? al f = some (h, n) := by
  obtain ⟨b, hb, hbh, us, hfn, hle, hn, -⟩ := aliasOcc_spec hx
  cases x with
  | app f a =>
    refine ⟨f, a, rfl, ?_⟩
    have hargs : (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] := rfl
    unfold aliasOcc? at hx ⊢
    rw [show (Expr.app f a).getAppFn = f.getAppFn from rfl] at hx
    split at hx
    · rename_i I us' hI
      try rw [hI]
      dsimp only at hx ⊢
      rw [hargs] at hx
      obtain ⟨a0, hfind, hpa⟩ := Option.map_eq_some_iff.mp hx
      simp only [Prod.mk.injEq, List.length_append, List.length_singleton] at hpa
      have hc0 := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.length_append,
        List.length_singleton] at hc0
      have hN : a0.nPc ≤ f.getAppArgs.length := by omega
      -- the first alias for `x` is the first for its function part
      have hfind' : al.find? (fun b => b.ind == I && decide (b.nPc ≤ f.getAppArgs.length) &&
          Level.isEquivList us' b.lvls == some true &&
          (f.getAppArgs.take b.nPc).map Expr.eraseFVarTys == b.ps) = some a0 := by
        rw [List.find?_eq_some_iff_append] at hfind ⊢
        obtain ⟨-, pre, post, hsplit, hpre⟩ := hfind
        refine ⟨?_, pre, post, hsplit, fun b hbm => ?_⟩
        · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          rw [List.take_append_of_le_length hN] at hc0
          exact ⟨⟨⟨hc0.1.1.1, hN⟩, hc0.1.2⟩, hc0.2⟩
        · have := hpre b hbm
          simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
            decide_eq_false_iff_not, Nat.not_le, List.length_append,
            List.length_singleton] at this ⊢
          by_cases hbN : b.nPc ≤ f.getAppArgs.length
          · rw [List.take_append_of_le_length hbN] at this
            rcases this with ((h1 | h1) | h1) | h1
            · exact Or.inl (Or.inl (Or.inl h1))
            · omega
            · exact Or.inl (Or.inr h1)
            · exact Or.inr h1
          · exact Or.inl (Or.inl (Or.inr (by omega)))
      rw [hfind']
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      exact ⟨hpa.1, by omega⟩
    · exact nomatch hx
  | _ =>
    simp only [Expr.getAppArgs, List.length_nil] at hn hle
    omega

/-- **The alias holes read their keys**: every alias's hole slot holds
the value of its (hole-form) key. -/
@[expose] def AliasTrue (V : Type w) [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (al : List ClassAlias) (H : Nat) (τ : Nat → V) : Prop :=
  ∀ a ∈ al, ∀ i ty, a.hole = .fvar i ty → ∀ r,
    denoteMeta acval env φ H (aliasKey a) = some r → τ (H - 1 - i) = interp V τ r

/-- **The alias pass reads as its input** at every valuation whose
alias holes read their keys. -/
theorem aliasAbs_read
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {al : List ClassAlias} {H : Nat} (hwf : AliasWF al H)
    (hden : ∀ a ∈ al, (denoteMeta acval env φ H (aliasKey a)).isSome)
    (e : Expr) {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V (AliasTrue V acval env φ al H) d)
      (denoteMeta acval env φ (H + d)
        ((classAbsGo (aliasOcc? al) none {} e).1.instantiateList as2 0))
      (denoteMeta acval env φ (H + d) (e.instantiateList as1 0)) := by
  have hyp : AbsReadHyps V acval env φ H (AliasTrue V acval env φ al H) (aliasOcc? al)
      (fun _ => false) := by
    refine ⟨fun x h n hx => aliasOcc_app hx, fun x h n hx => ?_,
      fun x h hx _ d' as2' as1' _ _ => ?_⟩
    · obtain ⟨a, ha, rfl, -⟩ := aliasOcc_spec hx
      obtain ⟨i, ty, hi, -⟩ := hwf.hole a ha
      exact ⟨i, ty, hi⟩
    · obtain ⟨a, ha, rfl, us, hfn, hle, hn, hlv, hps⟩ := aliasOcc_spec hx
      obtain ⟨i, ty, hi, hiH⟩ := hwf.hole a ha
      have hsem : Expr.SemEq x (aliasKey a) := by
        have hlen : x.getAppArgs.length = a.nPc := by omega
        have hx' : x = Expr.mkAppN (.const a.ind us) (x.getAppArgs.take a.nPc) := by
          rw [List.take_of_length_le (by omega), ← hfn, Expr.mkAppN_getAppFn_getAppArgs]
        rw [hx']
        unfold aliasKey
        have hlvl := Level.evalEqList_of_isEquivList hlv
        have hps' : (x.getAppArgs.take a.nPc).map Expr.eraseFVarTys
            = a.ps.map Expr.eraseFVarTys := by
          rw [hps]
          -- the alias's parameters are erased already
          rw [← hps, List.map_map]
          apply List.map_congr_left
          intro p _
          exact (Expr.eraseFVarTys_idem p).symm
        obtain ⟨hl, hpw⟩ := semEq_of_map_erase hps'
        exact Expr.SemEq.mkAppN ⟨rfl, hlvl⟩ hl hpw
      rw [hi, occRestrict_false, classAbsSpec_none]
      exact hole_agree_lift hacl hiH ty (hwf.keyScoped a ha).1 (hwf.keyScoped a ha).2 hsem
        (hden a ha) (fun τ hτ r hr => hτ a ha i ty hi r hr)
  have h := classAbsSpec_read hyp e h2 h1
  rw [occRestrict_false, classAbsSpec_none] at h
  rwa [(classAbsGo_spec _ e none {} (fun _ _ h => by simp at h)).1]

end Alias

/-! ## 6. Hole form (P1): the abstraction against a partial one -/

section Hole

open ConLeche (ClassInfo classOcc? classAbs)

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm}

/-- The class abstraction restricted to the holes `F` (a class fact's
free holes and own group): the other classes' occurrences stay
concrete. -/
@[expose] def classAbsF (cls : List ClassInfo) (F : Expr → Bool) (e : Expr) : Expr :=
  classAbsSpec (occRestrict (classOcc? cls) F) none e

/-- **P1 in hole form**: at every valuation `Good` admits, the class
abstraction reads as its restriction to the holes `F`, provided every
occurrence of a class outside `F` reads (at `Good`) as its
`F`-abstracted head.  At `F = ∅` this is `classAbs_read`; at a class
fact's `F` it is the reading of the abstracted crest at a STAGE value
(own group and free holes arbitrary, every other class read as its key
in hole form) — the head obligation is where the other classes'
coherence enters (DESIGN CLASSCHECK / P2B). -/
theorem classAbs_read_hole {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    {F : Expr → Bool} {Good : (Nat → V) → Prop}
    (hhead : ∀ x h, classOcc? cls x = some (h, 0) → F h = false →
      ∀ d as2 as1, LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V Good d) (denoteMeta acval env φ (H + d) h)
          (denoteMeta acval env φ (H + d) ((classAbsF cls F x).instantiateList as1 0)))
    (e : Expr) {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V Good d)
      (denoteMeta acval env φ (H + d) ((classAbs cls e).instantiateList as2 0))
      (denoteMeta acval env φ (H + d) ((classAbsF cls F e).instantiateList as1 0)) := by
  have hyp : AbsReadHyps V acval env φ H Good (classOcc? cls) F := by
    refine ⟨fun x h n hx => classOcc_app hwf hx, fun x h n hx => ?_, hhead⟩
    obtain ⟨c, hc, hch, -⟩ := classOcc_spec hwf hx
    obtain ⟨i, ty, rfl, -⟩ := hwf.hole c hc h hch
    exact ⟨i, ty, rfl⟩
  rw [classAbs_eq_spec]
  exact classAbsSpec_read hyp e h2 h1

end Hole

end ConLeche.Model
