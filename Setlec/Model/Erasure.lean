import Setlec.Kernel.Core

/-!
# Codomain-annotation erasure (task #100, stage 1)

The refactor towards *raw* storage (the environment keeps expression
trees without binder codomain-sort annotations) is carried on the proof
side by the **erasure view**: a witness for a raw tree `e` is an
annotated twin `ê` with `ê.eraseCod = e`, and a witness for a whole raw
environment is an annotated shadow environment that erases to it
(`RawEnvModel`, `Setlec/Model/RawEnv.lean`).

This module is the seam library: the erasure map itself, hereditarily
(including inside `fvar` type annotations, so that twins survive binder
opening), and its commutation with every syntactic operation the
checker performs on stored trees, plus the transfer of the *raw-side*
syntactic certificates.

Three groups:

* **commutation** — `instantiate1`, `instantiateList`,
  `instantiateLevelParams`, `abstract1`, `abstractRange`: erasure is
  structural, so substitution and abstraction commute with it verbatim.
  These are what keeps a twin a twin across reduction.
* **invariance** — `hasFvar`, `looseBVarsBounded`, `constsResolve`,
  `Env.find?`: predicates that read no annotation, hence transfer
  raw→annotated for free (an install-time certificate checked on the
  stored raw tree is a certificate about the witness).
* **guards** — `natLitSupported`/`strLitSupported` inspect *annotated*
  declaration shapes, so they are not erasure-invariant.  Their **raw
  forms** (this module) drop exactly the `mb.cod` conjuncts; each is
  erasure-invariant and implied by its annotated original, so the raw
  guard is what a raw-storage kernel can test and the annotated guard
  stays a witness-side obligation.
-/

namespace Setlec

/-! ## The erasure map -/

/-- Drop the codomain-sort annotation of one binder. -/
def BinderMeta.eraseCod (m : BinderMeta) : BinderMeta := ⟨m.bi, none⟩

@[simp] theorem BinderMeta.eraseCod_bi (m : BinderMeta) :
    m.eraseCod.bi = m.bi := rfl

@[simp] theorem BinderMeta.eraseCod_cod (m : BinderMeta) :
    m.eraseCod.cod = none := rfl

/-- Erase all binder codomain-sort annotations, hereditarily (including
inside `fvar` type annotations, so that twins survive binder opening).
A *raw* tree — what a raw-storage kernel stores and computes with — is
a fixed point of this map; an annotation witness for a raw tree `e` is
an annotated twin `ê` with `ê.eraseCod = e`. -/
def Expr.eraseCod : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx n ty => .fvar idx n ty.eraseCod
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app f.eraseCod a.eraseCod
  | .lam n ty b m => .lam n ty.eraseCod b.eraseCod m.eraseCod
  | .forallE n ty b m => .forallE n ty.eraseCod b.eraseCod m.eraseCod
  | .letE n ty v b => .letE n ty.eraseCod v.eraseCod b.eraseCod
  | .lit l => .lit l
  | .proj s i e => .proj s i e.eraseCod

def ConstantVal.eraseCod (cv : ConstantVal) : ConstantVal :=
  { cv with type := cv.type.eraseCod }

def RecRuleFire.eraseCod : RecRuleFire → RecRuleFire
  | .nested lvls pins => .nested lvls (pins.map Expr.eraseCod)
  | f => f

def RecRule.eraseCod (r : RecRule) : RecRule :=
  { r with fire := r.fire.eraseCod, rhs := r.rhs.eraseCod }

def ProjEntry.eraseCod (p : ProjEntry) : ProjEntry :=
  { p with ty := p.ty.eraseCod }

def ConstantInfo.eraseCod : ConstantInfo → ConstantInfo
  | .axiomInfo cv => .axiomInfo cv.eraseCod
  | .defnInfo cv v h => .defnInfo cv.eraseCod v.eraseCod h
  | .thmInfo cv v => .thmInfo cv.eraseCod v.eraseCod
  | .indInfo cv caps => .indInfo cv.eraseCod caps
  | .ctorInfo cv nP nF => .ctorInfo cv.eraseCod nP nF
  | .recInfo cv mI rP rules => .recInfo cv.eraseCod mI rP (rules.map RecRule.eraseCod)
  | .projInfo e => .projInfo e.eraseCod

/-- Erase a whole stored environment (the shadow environment's
projection back to what a raw-storage kernel actually stores). -/
def Env.eraseCod (env : Env) : Env := ⟨env.consts.map ConstantInfo.eraseCod⟩

/-! ## Erasure is idempotent: raw trees are the fixed points -/

theorem Expr.eraseCod_idem : ∀ e : Expr, e.eraseCod.eraseCod = e.eraseCod
  | .bvar _ | .sort _ | .const .. | .lit _ => rfl
  | .fvar _ _ ty => by simp [Expr.eraseCod, Expr.eraseCod_idem ty]
  | .app f a => by simp [Expr.eraseCod, Expr.eraseCod_idem f, Expr.eraseCod_idem a]
  | .lam _ ty b m => by
    simp [Expr.eraseCod, BinderMeta.eraseCod, Expr.eraseCod_idem ty,
      Expr.eraseCod_idem b]
  | .forallE _ ty b m => by
    simp [Expr.eraseCod, BinderMeta.eraseCod, Expr.eraseCod_idem ty,
      Expr.eraseCod_idem b]
  | .letE _ ty v b => by
    simp [Expr.eraseCod, Expr.eraseCod_idem ty, Expr.eraseCod_idem v,
      Expr.eraseCod_idem b]
  | .proj _ _ e => by simp [Expr.eraseCod, Expr.eraseCod_idem e]

/-! ## Environment lookup -/

theorem ConstantInfo.name_eraseCod (ci : ConstantInfo) :
    ci.eraseCod.name = ci.name := by
  cases ci <;> rfl

theorem ConstantInfo.toConstantVal_eraseCod (ci : ConstantInfo) :
    ci.eraseCod.toConstantVal = ci.toConstantVal.eraseCod := by
  cases ci <;> rfl

theorem Env.find?_eraseCod (env : Env) (n : Name) :
    env.eraseCod.find? n = (env.find? n).map ConstantInfo.eraseCod := by
  show (env.consts.map ConstantInfo.eraseCod).find? _ = _
  have hp : ((fun x : ConstantInfo => x.name == n) ∘ ConstantInfo.eraseCod) =
      (fun x : ConstantInfo => x.name == n) := by
    funext ci
    simp [Function.comp, ConstantInfo.name_eraseCod]
  rw [Env.find?, List.find?_map, hp]

/-- `find?` misses transfer between a raw environment and its
witness. -/
theorem Env.find?_eq_none_of_eraseCod {env : Env} {n : Name}
    (h : env.eraseCod.find? n = none) : env.find? n = none := by
  rw [Env.find?_eraseCod] at h
  cases hh : env.find? n with
  | none => rfl
  | some ci => rw [hh] at h; simp at h

/-! ## Commutation with substitution and abstraction -/

/-- Erasure commutes with binder-body opening: the danger zone of any
position-based annotation oracle (substitution moves positions) is a
one-line structural fact in the erasure view. -/
theorem Expr.eraseCod_instantiate1 (v : Expr) :
    ∀ (e : Expr) (d : Nat),
      (e.instantiate1 v d).eraseCod = e.eraseCod.instantiate1 v.eraseCod d
  | .bvar i, d => by
    simp only [Expr.instantiate1, Expr.eraseCod]
    by_cases h1 : i = d
    · simp [h1]
    · by_cases h2 : i > d <;> simp [h1, h2, Expr.eraseCod]
  | .fvar _ _ _, _ => by simp [Expr.instantiate1, Expr.eraseCod]
  | .sort _, _ => by simp [Expr.instantiate1, Expr.eraseCod]
  | .const _ _, _ => by simp [Expr.instantiate1, Expr.eraseCod]
  | .app f a, d => by
    simp [Expr.instantiate1, Expr.eraseCod, Expr.eraseCod_instantiate1 v f d,
      Expr.eraseCod_instantiate1 v a d]
  | .lam _ ty b _, d => by
    simp [Expr.instantiate1, Expr.eraseCod, Expr.eraseCod_instantiate1 v ty d,
      Expr.eraseCod_instantiate1 v b (d + 1)]
  | .forallE _ ty b _, d => by
    simp [Expr.instantiate1, Expr.eraseCod, Expr.eraseCod_instantiate1 v ty d,
      Expr.eraseCod_instantiate1 v b (d + 1)]
  | .letE _ ty vl b, d => by
    simp [Expr.instantiate1, Expr.eraseCod, Expr.eraseCod_instantiate1 v ty d,
      Expr.eraseCod_instantiate1 v vl d, Expr.eraseCod_instantiate1 v b (d + 1)]
  | .lit _, _ => by simp [Expr.instantiate1, Expr.eraseCod]
  | .proj _ _ e, d => by
    simp [Expr.instantiate1, Expr.eraseCod, Expr.eraseCod_instantiate1 v e d]

/-- Erasure commutes with bulk instantiation (task #50's
`instantiateList`); the `bvar` clause's recursion into the replacement
is handled by the induction hypothesis at the shorter prefix. -/
theorem Expr.eraseCod_instantiateList :
    ∀ (e : Expr) (vs : List Expr) (d : Nat),
      (e.instantiateList vs d).eraseCod =
        e.eraseCod.instantiateList (vs.map Expr.eraseCod) d
  | .bvar j, vs, d => by
    rw [Expr.eraseCod, Expr.instantiateList, Expr.instantiateList]
    by_cases h1 : j < d
    · simp [h1, Expr.eraseCod]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : j - d < vs.length
      · rw [dif_pos h2, dif_pos (by simpa using h2)]
        rw [Expr.eraseCod_instantiateList vs[j - d] (vs.take (j - d)) d]
        simp [List.map_take]
      · rw [dif_neg h2, dif_neg (by simpa using h2)]
        simp [Expr.eraseCod]
  | .fvar _ _ _, _, _ => by simp [Expr.instantiateList, Expr.eraseCod]
  | .sort _, _, _ => by simp [Expr.instantiateList, Expr.eraseCod]
  | .const _ _, _, _ => by simp [Expr.instantiateList, Expr.eraseCod]
  | .lit _, _, _ => by simp [Expr.instantiateList, Expr.eraseCod]
  | .app f a, vs, d => by
    simp [Expr.instantiateList, Expr.eraseCod,
      Expr.eraseCod_instantiateList f vs d, Expr.eraseCod_instantiateList a vs d]
  | .lam _ ty b _, vs, d => by
    simp [Expr.instantiateList, Expr.eraseCod,
      Expr.eraseCod_instantiateList ty vs d,
      Expr.eraseCod_instantiateList b vs (d + 1)]
  | .forallE _ ty b _, vs, d => by
    simp [Expr.instantiateList, Expr.eraseCod,
      Expr.eraseCod_instantiateList ty vs d,
      Expr.eraseCod_instantiateList b vs (d + 1)]
  | .letE _ ty vl b, vs, d => by
    simp [Expr.instantiateList, Expr.eraseCod,
      Expr.eraseCod_instantiateList ty vs d,
      Expr.eraseCod_instantiateList vl vs d,
      Expr.eraseCod_instantiateList b vs (d + 1)]
  | .proj _ _ e, vs, d => by
    simp [Expr.instantiateList, Expr.eraseCod,
      Expr.eraseCod_instantiateList e vs d]
termination_by e vs => (vs.length, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp [List.length_take]; omega)
    | (apply Prod.Lex.right; simp; omega)

/-- Erasure commutes with level-parameter instantiation: the
annotations it substitutes into are the ones erasure drops. -/
theorem Expr.eraseCod_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ e : Expr, (e.instantiateLevelParams ks us).eraseCod =
      e.eraseCod.instantiateLevelParams ks us
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ _ ty => by
    simp [Expr.instantiateLevelParams, Expr.eraseCod,
      Expr.eraseCod_instantiateLevelParams ks us ty]
  | .app f a => by
    simp [Expr.instantiateLevelParams, Expr.eraseCod,
      Expr.eraseCod_instantiateLevelParams ks us f,
      Expr.eraseCod_instantiateLevelParams ks us a]
  | .lam _ ty b _ => by
    simp [Expr.instantiateLevelParams, Expr.eraseCod, BinderMeta.eraseCod,
      Expr.eraseCod_instantiateLevelParams ks us ty,
      Expr.eraseCod_instantiateLevelParams ks us b]
  | .forallE _ ty b _ => by
    simp [Expr.instantiateLevelParams, Expr.eraseCod, BinderMeta.eraseCod,
      Expr.eraseCod_instantiateLevelParams ks us ty,
      Expr.eraseCod_instantiateLevelParams ks us b]
  | .letE _ ty v b => by
    simp [Expr.instantiateLevelParams, Expr.eraseCod,
      Expr.eraseCod_instantiateLevelParams ks us ty,
      Expr.eraseCod_instantiateLevelParams ks us v,
      Expr.eraseCod_instantiateLevelParams ks us b]
  | .proj _ _ e => by
    simp [Expr.instantiateLevelParams, Expr.eraseCod,
      Expr.eraseCod_instantiateLevelParams ks us e]

/-- Erasure commutes with binder closing. -/
theorem Expr.eraseCod_abstract1 (d : Nat) :
    ∀ (e : Expr) (k : Nat), (e.abstract1 d k).eraseCod = e.eraseCod.abstract1 d k
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar idx _ _, k => by
    by_cases h : idx = d <;> simp [Expr.abstract1, Expr.eraseCod, h]
  | .app f a, k => by
    simp [Expr.abstract1, Expr.eraseCod, Expr.eraseCod_abstract1 d f k,
      Expr.eraseCod_abstract1 d a k]
  | .lam _ ty b _, k => by
    simp [Expr.abstract1, Expr.eraseCod, Expr.eraseCod_abstract1 d ty k,
      Expr.eraseCod_abstract1 d b (k + 1)]
  | .forallE _ ty b _, k => by
    simp [Expr.abstract1, Expr.eraseCod, Expr.eraseCod_abstract1 d ty k,
      Expr.eraseCod_abstract1 d b (k + 1)]
  | .letE _ ty v b, k => by
    simp [Expr.abstract1, Expr.eraseCod, Expr.eraseCod_abstract1 d ty k,
      Expr.eraseCod_abstract1 d v k, Expr.eraseCod_abstract1 d b (k + 1)]
  | .proj _ _ e, k => by
    simp [Expr.abstract1, Expr.eraseCod, Expr.eraseCod_abstract1 d e k]

/-- Erasure commutes with bulk binder closing (task #72's
`abstractRange`). -/
theorem Expr.eraseCod_abstractRange (d k : Nat) :
    ∀ (e : Expr) (c : Nat),
      (e.abstractRange d k c).eraseCod = e.eraseCod.abstractRange d k c
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar idx _ _, c => by
    by_cases h : d ≤ idx ∧ idx < d + k <;>
      simp [Expr.abstractRange, Expr.eraseCod, h]
  | .app f a, c => by
    simp [Expr.abstractRange, Expr.eraseCod, Expr.eraseCod_abstractRange d k f c,
      Expr.eraseCod_abstractRange d k a c]
  | .lam _ ty b _, c => by
    simp [Expr.abstractRange, Expr.eraseCod, Expr.eraseCod_abstractRange d k ty c,
      Expr.eraseCod_abstractRange d k b (c + 1)]
  | .forallE _ ty b _, c => by
    simp [Expr.abstractRange, Expr.eraseCod, Expr.eraseCod_abstractRange d k ty c,
      Expr.eraseCod_abstractRange d k b (c + 1)]
  | .letE _ ty v b, c => by
    simp [Expr.abstractRange, Expr.eraseCod, Expr.eraseCod_abstractRange d k ty c,
      Expr.eraseCod_abstractRange d k v c,
      Expr.eraseCod_abstractRange d k b (c + 1)]
  | .proj _ _ e, c => by
    simp [Expr.abstractRange, Expr.eraseCod, Expr.eraseCod_abstractRange d k e c]

/-! ## Erasure-invariant predicates (raw-transferable certificates) -/

/-- `hasFvar` is erasure-invariant (a raw-side input-closedness
certificate transfers to the witness). -/
theorem Expr.hasFvar_eraseCod : ∀ e : Expr, e.eraseCod.hasFvar = e.hasFvar
  | .bvar _ | .sort _ | .const .. | .lit _ => rfl
  | .fvar _ _ _ => rfl
  | .app f a => by
    simp [Expr.eraseCod, Expr.hasFvar, Expr.hasFvar_eraseCod f, Expr.hasFvar_eraseCod a]
  | .lam _ ty b _ => by
    simp [Expr.eraseCod, Expr.hasFvar, Expr.hasFvar_eraseCod ty, Expr.hasFvar_eraseCod b]
  | .forallE _ ty b _ => by
    simp [Expr.eraseCod, Expr.hasFvar, Expr.hasFvar_eraseCod ty, Expr.hasFvar_eraseCod b]
  | .letE _ ty v b => by
    simp [Expr.eraseCod, Expr.hasFvar, Expr.hasFvar_eraseCod ty,
      Expr.hasFvar_eraseCod v, Expr.hasFvar_eraseCod b]
  | .proj _ _ e => by simp [Expr.eraseCod, Expr.hasFvar, Expr.hasFvar_eraseCod e]

/-- `looseBVarsBounded` is erasure-invariant. -/
theorem Expr.looseBVarsBounded_eraseCod :
    ∀ (e : Expr) (k : Nat), e.eraseCod.looseBVarsBounded k = e.looseBVarsBounded k
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => rfl
  | .fvar _ _ _, _ => rfl
  | .app f a, k => by
    simp [Expr.eraseCod, Expr.looseBVarsBounded, Expr.looseBVarsBounded_eraseCod f k,
      Expr.looseBVarsBounded_eraseCod a k]
  | .lam _ ty b _, k => by
    simp [Expr.eraseCod, Expr.looseBVarsBounded, Expr.looseBVarsBounded_eraseCod ty k,
      Expr.looseBVarsBounded_eraseCod b (k + 1)]
  | .forallE _ ty b _, k => by
    simp [Expr.eraseCod, Expr.looseBVarsBounded, Expr.looseBVarsBounded_eraseCod ty k,
      Expr.looseBVarsBounded_eraseCod b (k + 1)]
  | .letE _ ty v b, k => by
    simp [Expr.eraseCod, Expr.looseBVarsBounded, Expr.looseBVarsBounded_eraseCod ty k,
      Expr.looseBVarsBounded_eraseCod v k, Expr.looseBVarsBounded_eraseCod b (k + 1)]
  | .proj _ _ e, k => by
    simp [Expr.eraseCod, Expr.looseBVarsBounded, Expr.looseBVarsBounded_eraseCod e k]

/-- `constsResolve` is erasure-invariant on both the expression and the
environment (it reads only lookup success, which erasure preserves). -/
theorem Expr.constsResolve_eraseCod (env : Env) :
    ∀ e : Expr, e.eraseCod.constsResolve env.eraseCod = e.constsResolve env
  | .bvar _ | .sort _ => rfl
  | .lit (.natVal _) => by
    simp only [Expr.eraseCod, Expr.constsResolve, Env.find?_eraseCod,
      Option.isSome_map]
  | .lit (.strVal _) => by
    simp only [Expr.eraseCod, Expr.constsResolve, Env.find?_eraseCod,
      Option.isSome_map]
  | .const _ _ => by
    simp only [Expr.eraseCod, Expr.constsResolve, Env.find?_eraseCod,
      Option.isSome_map]
  | .fvar _ _ ty => by
    simpa [Expr.eraseCod, Expr.constsResolve] using
      Expr.constsResolve_eraseCod env ty
  | .app f a => by
    simp [Expr.eraseCod, Expr.constsResolve, Expr.constsResolve_eraseCod env f,
      Expr.constsResolve_eraseCod env a]
  | .lam _ ty b _ => by
    simp [Expr.eraseCod, Expr.constsResolve, Expr.constsResolve_eraseCod env ty,
      Expr.constsResolve_eraseCod env b]
  | .forallE _ ty b _ => by
    simp [Expr.eraseCod, Expr.constsResolve, Expr.constsResolve_eraseCod env ty,
      Expr.constsResolve_eraseCod env b]
  | .letE _ ty v b => by
    simp [Expr.eraseCod, Expr.constsResolve, Expr.constsResolve_eraseCod env ty,
      Expr.constsResolve_eraseCod env v, Expr.constsResolve_eraseCod env b]
  | .proj _ _ e => by
    simp only [Expr.eraseCod, Expr.constsResolve, Env.find?_eraseCod,
      Option.isSome_map, Expr.constsResolve_eraseCod env e]

/-! ## Inversion: erasure is constructor-wise

Twin tracking through reduction rests on these — a twin of a term with
a known head decomposes into twins of that head's parts (the spike's
`interp_twin_beta` open-coded the `app`/`lam` cases). -/

theorem Expr.eraseCod_eq_bvar {e : Expr} {i : Nat} (h : e.eraseCod = .bvar i) :
    e = .bvar i := by
  cases e <;> simp_all [Expr.eraseCod]

theorem Expr.eraseCod_eq_sort {e : Expr} {u : Level} (h : e.eraseCod = .sort u) :
    e = .sort u := by
  cases e <;> simp_all [Expr.eraseCod]

theorem Expr.eraseCod_eq_const {e : Expr} {n : Name} {us : List Level}
    (h : e.eraseCod = .const n us) : e = .const n us := by
  cases e <;> simp_all [Expr.eraseCod]

theorem Expr.eraseCod_eq_lit {e : Expr} {l : Literal} (h : e.eraseCod = .lit l) :
    e = .lit l := by
  cases e <;> simp_all [Expr.eraseCod]

theorem Expr.eraseCod_eq_fvar {e : Expr} {idx : Nat} {n : Name} {t : Expr}
    (h : e.eraseCod = .fvar idx n t) :
    ∃ ty, e = .fvar idx n ty ∧ ty.eraseCod = t := by
  cases e <;> simp_all [Expr.eraseCod]

theorem Expr.eraseCod_eq_app {e f a : Expr} (h : e.eraseCod = .app f a) :
    ∃ f' a', e = .app f' a' ∧ f'.eraseCod = f ∧ a'.eraseCod = a := by
  cases e <;> simp_all [Expr.eraseCod]
  exact ⟨_, _, ⟨rfl, rfl⟩, h.1, h.2⟩

theorem Expr.eraseCod_eq_lam {e : Expr} {n : Name} {ty b : Expr} {m : BinderMeta}
    (h : e.eraseCod = .lam n ty b m) :
    ∃ ty' b' m', e = .lam n ty' b' m' ∧ ty'.eraseCod = ty ∧ b'.eraseCod = b ∧
      m'.eraseCod = m := by
  cases e <;> simp_all [Expr.eraseCod]
  exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, h.2.1, h.2.2.1, h.2.2.2⟩

theorem Expr.eraseCod_eq_forallE {e : Expr} {n : Name} {ty b : Expr}
    {m : BinderMeta} (h : e.eraseCod = .forallE n ty b m) :
    ∃ ty' b' m', e = .forallE n ty' b' m' ∧ ty'.eraseCod = ty ∧
      b'.eraseCod = b ∧ m'.eraseCod = m := by
  cases e <;> simp_all [Expr.eraseCod]
  exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, h.2.1, h.2.2.1, h.2.2.2⟩

theorem Expr.eraseCod_eq_letE {e : Expr} {n : Name} {ty v b : Expr}
    (h : e.eraseCod = .letE n ty v b) :
    ∃ ty' v' b', e = .letE n ty' v' b' ∧ ty'.eraseCod = ty ∧ v'.eraseCod = v ∧
      b'.eraseCod = b := by
  cases e <;> simp_all [Expr.eraseCod]
  exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, h.2.1, h.2.2.1, h.2.2.2⟩

theorem Expr.eraseCod_eq_proj {e : Expr} {s : Name} {i : Nat} {t : Expr}
    (h : e.eraseCod = .proj s i t) :
    ∃ t', e = .proj s i t' ∧ t'.eraseCod = t := by
  cases e <;> simp_all [Expr.eraseCod]

/-! ## The literal-support guards, raw

`natLitSupported`/`strLitSupported` pin the *annotated* stored types of
the `Nat`/`String` basis declarations, so they are the one family of
syntactic environment checks erasure does not preserve.  The raw forms
below drop exactly the `mb.cod` conjuncts — they are what a raw-storage
kernel can test — and each comes with its erasure congruence: the
annotated guard on the witness environment implies the raw guard on
what the kernel stores, so the raw kernel's literal paths are open
wherever the model's are. -/

/-- `natSuccOk` without the codomain annotation. -/
def natSuccOkRaw : Option ConstantInfo → Bool
  | some (.ctorInfo cv _ _) =>
    cv.levelParams.isEmpty &&
    (match cv.type with
     | .forallE _ (.const c1 []) (.const c2 []) _ => c1 == natName && c2 == natName
     | _ => false)
  | _ => false

/-- `listTyOk` without the codomain annotation. -/
def listTyOkRaw : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE _ (.sort u1) (.sort u2) _ =>
         u1 == .succ (.param p) && u2 == .succ (.param p)
       | _ => false)
    | _ => false
  | none => false

/-- `listNilTyOk` without the codomain annotation. -/
def listNilTyOkRaw : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE _ (.sort u1) (.app (.const l1 us1) (.bvar 0)) _ =>
         u1 == .succ (.param p) && l1 == listName && us1 == [.param p]
       | _ => false)
    | _ => false
  | none => false

/-- `listConsTyOk` without the codomain annotations. -/
def listConsTyOkRaw : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE _ (.sort u1)
           (.forallE _ (.bvar 0)
             (.forallE _ (.app (.const l1 us1) (.bvar 1))
               (.app (.const l2 us2) (.bvar 2)) _) _) _ =>
         u1 == .succ (.param p) && l1 == listName && l2 == listName &&
           us1 == [.param p] && us2 == [.param p]
       | _ => false)
    | _ => false
  | none => false

/-- `charOfNatTyOk` without the codomain annotation. -/
def charOfNatTyOkRaw : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      (match ci.toConstantVal.type with
       | .forallE _ (.const c1 []) (.const c2 []) _ => c1 == natName && c2 == charName
       | _ => false)
  | none => false

/-- `stringOfListTyOk` without the codomain annotation. -/
def stringOfListTyOkRaw : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      (match ci.toConstantVal.type with
       | .forallE _ (.app (.const l1 us1) (.const c1 [])) (.const c2 []) _ =>
         l1 == listName && us1 == [.zero] && c1 == charName && c2 == stringName
       | _ => false)
  | none => false

/-- The `Nat`-literal guard a raw-storage kernel can test. -/
def natLitSupportedRaw (env : Env) : Bool :=
  natIndOk (env.find? natName) && natZeroOk (env.find? natZeroName) &&
    natSuccOkRaw (env.find? natSuccName)

/-- The `String`-literal guard a raw-storage kernel can test. -/
def strLitSupportedRaw (env : Env) : Bool :=
  natLitSupportedRaw env &&
    stringTyOk (env.find? stringName) &&
    stringOfListTyOkRaw (env.find? stringOfListName) &&
    listTyOkRaw (env.find? listName) &&
    listNilTyOkRaw (env.find? listNilName) &&
    listConsTyOkRaw (env.find? listConsName) &&
    charTyOk (env.find? charName) &&
    charOfNatTyOkRaw (env.find? charOfNatName)

/-! ### Per-declaration guard congruences -/

section GuardCongruences

variable {ci? : Option ConstantInfo}

theorem natIndOk_erase (h : natIndOk ci? = true) :
    natIndOk (ci?.map ConstantInfo.eraseCod) = true := by
  unfold natIndOk at h
  split at h
  · rename_i cv caps
    simp_all [natIndOk, ConstantInfo.eraseCod, ConstantVal.eraseCod,
      Expr.eraseCod]
  · exact absurd h (by simp)

theorem natZeroOk_erase (h : natZeroOk ci? = true) :
    natZeroOk (ci?.map ConstantInfo.eraseCod) = true := by
  unfold natZeroOk at h
  split at h
  · rename_i cv nP nF
    simp_all [natZeroOk, ConstantInfo.eraseCod, ConstantVal.eraseCod,
      Expr.eraseCod]
  · exact absurd h (by simp)

theorem stringTyOk_erase (h : stringTyOk ci? = true) :
    stringTyOk (ci?.map ConstantInfo.eraseCod) = true := by
  unfold stringTyOk at h
  split at h
  · rename_i ci
    simp_all [stringTyOk, ConstantInfo.toConstantVal_eraseCod,
      ConstantVal.eraseCod, Expr.eraseCod]
  · exact absurd h (by simp)

theorem charTyOk_erase (h : charTyOk ci? = true) :
    charTyOk (ci?.map ConstantInfo.eraseCod) = true := by
  unfold charTyOk at h
  split at h
  · rename_i ci
    simp_all [charTyOk, ConstantInfo.toConstantVal_eraseCod,
      ConstantVal.eraseCod, Expr.eraseCod]
  · exact absurd h (by simp)

theorem natSuccOkRaw_erase (h : natSuccOk ci? = true) :
    natSuccOkRaw (ci?.map ConstantInfo.eraseCod) = true := by
  unfold natSuccOk at h
  split at h
  · rename_i cv nP nF
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i heq
      simp_all [natSuccOkRaw, ConstantInfo.eraseCod, ConstantVal.eraseCod,
        Expr.eraseCod]
    · exact absurd h2 (by simp)
  · exact absurd h (by simp)

theorem listTyOkRaw_erase (h : listTyOk ci? = true) :
    listTyOkRaw (ci?.map ConstantInfo.eraseCod) = true := by
  unfold listTyOk at h
  split at h
  · rename_i ci
    split at h
    · rename_i p hlps
      split at h
      · rename_i heq
        simp_all [listTyOkRaw, ConstantInfo.toConstantVal_eraseCod,
          ConstantVal.eraseCod, Expr.eraseCod]
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem listNilTyOkRaw_erase (h : listNilTyOk ci? = true) :
    listNilTyOkRaw (ci?.map ConstantInfo.eraseCod) = true := by
  unfold listNilTyOk at h
  split at h
  · rename_i ci
    split at h
    · rename_i p hlps
      split at h
      · rename_i heq
        simp_all [listNilTyOkRaw, ConstantInfo.toConstantVal_eraseCod,
          ConstantVal.eraseCod, Expr.eraseCod]
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem listConsTyOkRaw_erase (h : listConsTyOk ci? = true) :
    listConsTyOkRaw (ci?.map ConstantInfo.eraseCod) = true := by
  unfold listConsTyOk at h
  split at h
  · rename_i ci
    split at h
    · rename_i p hlps
      split at h
      · rename_i heq
        simp_all [listConsTyOkRaw, ConstantInfo.toConstantVal_eraseCod,
          ConstantVal.eraseCod, Expr.eraseCod]
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem charOfNatTyOkRaw_erase (h : charOfNatTyOk ci? = true) :
    charOfNatTyOkRaw (ci?.map ConstantInfo.eraseCod) = true := by
  unfold charOfNatTyOk at h
  split at h
  · rename_i ci
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i heq
      simp_all [charOfNatTyOkRaw, ConstantInfo.toConstantVal_eraseCod,
        ConstantVal.eraseCod, Expr.eraseCod]
    · exact absurd h2 (by simp)
  · exact absurd h (by simp)

theorem stringOfListTyOkRaw_erase (h : stringOfListTyOk ci? = true) :
    stringOfListTyOkRaw (ci?.map ConstantInfo.eraseCod) = true := by
  unfold stringOfListTyOk at h
  split at h
  · rename_i ci
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i heq
      simp_all [stringOfListTyOkRaw, ConstantInfo.toConstantVal_eraseCod,
        ConstantVal.eraseCod, Expr.eraseCod]
    · exact absurd h2 (by simp)
  · exact absurd h (by simp)

end GuardCongruences

/-- **Guard congruence, `Nat` literals**: the annotated guard on the
witness environment implies the raw guard on what the kernel stores. -/
theorem natLitSupportedRaw_erase {env : Env} (h : natLitSupported env = true) :
    natLitSupportedRaw env.eraseCod = true := by
  simp only [natLitSupported, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [natLitSupportedRaw, Env.find?_eraseCod, Bool.and_eq_true]
  exact ⟨⟨natIndOk_erase h1, natZeroOk_erase h2⟩, natSuccOkRaw_erase h3⟩

/-- **Guard congruence, `String` literals**. -/
theorem strLitSupportedRaw_erase {env : Env} (h : strLitSupported env = true) :
    strLitSupportedRaw env.eraseCod = true := by
  simp only [strLitSupported, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  simp only [strLitSupportedRaw, Env.find?_eraseCod, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨natLitSupportedRaw_erase h0, stringTyOk_erase h1⟩,
    stringOfListTyOkRaw_erase h2⟩, listTyOkRaw_erase h3⟩,
    listNilTyOkRaw_erase h4⟩, listConsTyOkRaw_erase h5⟩,
    charTyOk_erase h6⟩, charOfNatTyOkRaw_erase h7⟩

end Setlec
