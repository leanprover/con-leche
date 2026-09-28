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

end ConLeche.Model
