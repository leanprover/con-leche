module

public import ConLeche.Verify.PropRead
public import ConLeche.Verify.PropWhen
public import ConLeche.Verify.EnvWF
public import ConLeche.Verify.Abstract
public import ConLeche.Verify.Subst

public section

/-!
# Annotation commutes with instantiation: the copies' stored types
(task #298)

**What this is for.**  The nested route's elimination mints a copy `A`
of a container member `J` at a pin `J Ds` by *instantiating*: the copy's
type is the container's stored type, level-instantiated and applied to
the pin's components, closed over the block's parameter telescope
(`mkCopy`, `ConLeche/Kernel/Inductives/NestedElim.lean`), and its
constructors the container's the same way (`elimCtors`,
`replaceAllNested`).  The auxiliary block is then installed, which
**re-annotates** those types — and the annotation pass *recomputes*
every binder datum that is not a real input annotation
(`pwWritten pw = !pw.isNever`, `ConLeche/Kernel/Core.lean`), i.e. every
`.never` one, which is every Type-valued binder.  The model lane
(DESIGN §M.21) needs the copies' STORED types to be the container's at
the pin *on the nose, data included*; up to data it has them already.

**The mechanism.**  A recomputed datum is `annotPwPi`'s, and
`annotPwPi` asks the **head-symbol reader** `typeSortPW` first
(`ConLeche/Kernel/PropRead.lean`) and only falls back to inference when
the reader declines.  The reader is a *syntactic* function of the head
symbol, the arity and the binder data — so on the reader's branch the
recomputation commutes with instantiation for elementary reasons, and
this module proves exactly that:

* `SortAgree find? A v` — "`v` reads, for the head reader, like a
  variable declared of type `A`": at every arity, the datum the reader
  computes from `v`'s head is the one it computes from `A`'s telescope.
  This is the hypothesis a *pin component* has to meet, and it is what
  the pin's typing (`pinsOkAux`) says in reader terms.
* `typeSortPW_instantiate1_congr` — the reader cannot tell an opened
  binder from a `SortAgree` value: substituting one for the other
  leaves every reading unchanged.
* `typeSortPW_instantiateLevelParams` — the reader commutes with level
  instantiation through `substPW`, which is the datum's own
  substitution (`Level.zeronessOf_subst`, `Level.substPW_comp`).

Both are one *equation* per reading, with no inference, no reduction and
no environment invariant beyond the stored types' level-parameter
bound (`EnvWF`).

**What is NOT here** — and is the task's honest frontier: the
inference fallback.  Where the reader declines (a `.proj`- or
redex-headed codomain), the datum is `Level.zeronessOf` of an INFERRED
sort, and its stability under instantiation is the general
inference-substitution theorem the tree does not have.  DESIGN's
`#### K.4` states it.
-/

namespace ConLeche

open Expr

/-! ## The spine under instantiation -/

theorem Expr.getAppFn_instantiate1 (v : Expr) :
    ∀ (e : Expr) (d : Nat),
      (e.instantiate1 v d).getAppFn = (e.getAppFn.instantiate1 v d).getAppFn := by
  intro e
  induction e <;> intro d
  case app f a ihf _ => exact ihf d
  all_goals rfl

theorem Expr.numArgs_instantiate1 (v : Expr) :
    ∀ (e : Expr) (d : Nat),
      (e.instantiate1 v d).numArgs
        = (e.getAppFn.instantiate1 v d).numArgs + e.numArgs := by
  intro e
  induction e <;> intro d
  case app f a ihf _ =>
    show (f.instantiate1 v d).numArgs + 1 = _
    rw [ihf d]
    show _ = ((f.getAppFn).instantiate1 v d).numArgs + (f.numArgs + 1)
    omega
  all_goals rfl

theorem Expr.getAppFn_instantiateLevelParams (ks : List Name) (vs : List Level) :
    ∀ (e : Expr),
      (e.instantiateLevelParams ks vs).getAppFn
        = e.getAppFn.instantiateLevelParams ks vs := by
  intro e
  induction e <;> try rfl
  case app f a ihf _ => exact ihf

theorem Expr.numArgs_instantiateLevelParams (ks : List Name) (vs : List Level) :
    ∀ (e : Expr), (e.instantiateLevelParams ks vs).numArgs = e.numArgs := by
  intro e
  induction e <;> try rfl
  case app f a ihf _ => exact congrArg (· + 1) ihf

/-! ## `SortAgree`: a value the head reader cannot tell from a variable -/

/-- **`v` reads like a variable declared of type `A`.**  The
head-symbol reader (`typeSortPW`) answers "what is the zero-ness of the
sort of this type?" from a head symbol and an arity: at an `fvar` head
it peels the DECLARED type's never-data binders and reads the residual
sort (`residualPW (A.peelNeverPis n)`); at a constant head it reads the
stored type the same way and instantiates.  `SortAgree find? A v` says
the two answers coincide at every arity — unapplied (where the reader's
own `∀`/`Sort` cases can fire on `v`, which they never do on a
variable) and at every positive arity.

This is the ONE hypothesis the substitution congruence below needs of
the substituted value, and it is what a pin component's typing says in
the reader's terms: `D : A` gives `typeSortPW find? D = residualPW
(A.peelNeverPis 0)` wherever the reader is complete for `D`. -/
def SortAgree (find? : Name → Option ConstantInfo) (A v : Expr) : Prop :=
  typeSortPW find? v = residualPW (A.peelNeverPis 0) ∧
    ∀ n : Nat, headTypePW find? v.getAppFn (v.numArgs + (n + 1))
      = residualPW (A.peelNeverPis (n + 1))

theorem headTypePW_bvar (find? : Name → Option ConstantInfo) (i n : Nat) :
    headTypePW find? (.bvar i) n = none := rfl

theorem headTypePW_fvar (find? : Name → Option ConstantInfo) (idx n : Nat)
    (A : Expr) :
    headTypePW find? (.fvar idx A) n = residualPW (A.peelNeverPis n) := rfl

/-- The head reader at a positive arity cannot tell the opened binder
from a `SortAgree` value: substituting one for the other leaves every
reading unchanged.  (Positive arity is the *applied* case; the
unapplied one is `typeSortPW_instantiate1_congr`'s `bvar` branch, which
is where `SortAgree`'s first conjunct is spent.) -/
theorem headTypePW_instantiate1_congr (find? : Name → Option ConstantInfo)
    {A v : Expr} (idx : Nat) (h : SortAgree find? A v) :
    ∀ (e : Expr) (d n : Nat),
      headTypePW find? ((e.instantiate1 v d).getAppFn)
          ((e.instantiate1 v d).numArgs + (n + 1))
        = headTypePW find? ((e.instantiate1 (.fvar idx A) d).getAppFn)
          ((e.instantiate1 (.fvar idx A) d).numArgs + (n + 1)) := by
  intro e
  induction e <;> intro d n
  case bvar i =>
    by_cases hi : i = d
    · have hfv : headTypePW find? (Expr.fvar idx A).getAppFn
          ((Expr.fvar idx A).numArgs + (n + 1))
            = residualPW (A.peelNeverPis (n + 1)) := by
        show residualPW (A.peelNeverPis (0 + (n + 1))) = _
        rw [Nat.zero_add]
      show headTypePW find? ((if i = d then v else _).getAppFn)
          ((if i = d then v else _).numArgs + (n + 1))
        = headTypePW find? ((if i = d then (Expr.fvar idx A) else _).getAppFn)
          ((if i = d then (Expr.fvar idx A) else _).numArgs + (n + 1))
      rw [if_pos hi, if_pos hi, hfv]
      exact h.2 n
    · show headTypePW find? ((if i = d then v else _).getAppFn)
          ((if i = d then v else _).numArgs + (n + 1))
        = headTypePW find? ((if i = d then (Expr.fvar idx A) else _).getAppFn)
          ((if i = d then (Expr.fvar idx A) else _).numArgs + (n + 1))
      rw [if_neg hi, if_neg hi]
  case app f a ihf _ =>
    have harg : ∀ m : Nat, m + 1 + (n + 1) = m + (n + 1 + 1) := fun m => by omega
    show headTypePW find? ((f.instantiate1 v d).getAppFn)
        ((f.instantiate1 v d).numArgs + 1 + (n + 1))
      = headTypePW find? ((f.instantiate1 (.fvar idx A) d).getAppFn)
        ((f.instantiate1 (.fvar idx A) d).numArgs + 1 + (n + 1))
    rw [harg, harg]
    exact ihf d (n + 1)
  all_goals rfl

/-- **The reader cannot see a `SortAgree` substitution.**  Every
reading `typeSortPW` makes of a term with the value substituted in is
the reading it makes with the binder opened at a variable of the
declared type — which is what makes the annotation pass's *recomputed*
data agree, node by node, on the two sides. -/
theorem typeSortPW_instantiate1_congr (find? : Name → Option ConstantInfo)
    {A v : Expr} (idx : Nat) (h : SortAgree find? A v) :
    ∀ (e : Expr) (d : Nat),
      typeSortPW find? (e.instantiate1 v d)
        = typeSortPW find? (e.instantiate1 (.fvar idx A) d) := by
  intro e d
  cases e
  case bvar i =>
    by_cases hi : i = d
    · show typeSortPW find? (if i = d then v else _)
        = typeSortPW find? (if i = d then (Expr.fvar idx A) else _)
      rw [if_pos hi, if_pos hi]
      exact h.1
    · show typeSortPW find? (if i = d then v else _)
        = typeSortPW find? (if i = d then (Expr.fvar idx A) else _)
      rw [if_neg hi, if_neg hi]
  case app f a =>
    have hz := headTypePW_instantiate1_congr find? idx h f d 0
    rw [Nat.zero_add] at hz
    show headTypePW find? ((f.instantiate1 v d).getAppFn)
        ((f.instantiate1 v d).numArgs + 1)
      = headTypePW find? ((f.instantiate1 (.fvar idx A) d).getAppFn)
        ((f.instantiate1 (.fvar idx A) d).numArgs + 1)
    exact hz
  all_goals rfl

/-! ## The reader under level instantiation -/

/-- The peeled residual of a type whose level parameters are within
`ps` has its own within `ps`. -/
theorem Expr.allLevelParamsDefined_peelNeverPis {ps : List Name} :
    ∀ (k : Nat) {T R : Expr}, T.peelNeverPis k = some R →
      T.allLevelParamsDefined ps = true → R.allLevelParamsDefined ps = true := by
  intro k
  induction k with
  | zero =>
    intro T R h hT
    rw [← Expr.peelNeverPis_zero_inv h]; exact hT
  | succ k ih =>
    intro T R h hT
    obtain ⟨ty, b, m, rfl, -, hb⟩ := Expr.peelNeverPis_succ_inv h
    rw [Expr.allLevelParamsDefined, Bool.and_eq_true, Bool.and_eq_true] at hT
    exact ih hb hT.1.2

/-- `headTypePW` unfolded at a constant head. -/
theorem headTypePW_const (find? : Name → Option ConstantInfo) (I : Name)
    (us : List Level) (n : Nat) :
    headTypePW find? (.const I us) n =
      match find? I with
      | some ci =>
        if ci.isTowerEntry then none else
        if us.length = ci.toConstantVal.levelParams.length then
          (residualPW (ci.toConstantVal.type.peelNeverPis n)).map
            (Level.substPW ci.toConstantVal.levelParams us)
        else none
      | none => none := rfl

/-- **The head reader commutes with level instantiation**, through the
datum's own substitution `substPW`.  The constant-head case is
`Level.substPW_comp` — the stored type is NOT instantiated, only the
use-site levels are — and the `fvar` case is `Level.zeronessOf_subst`.

The hypothesis is the environment's: every stored type's levels are
within its declared parameters (`ConstWF`, hence `EnvWF`). -/
theorem headTypePW_instantiateLevelParams (find? : Name → Option ConstantInfo)
    {ks : List Name} {vs : List Level}
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true)
    {hd : Expr} {n : Nat} {pw : PropWhen} (h : headTypePW find? hd n = some pw) :
    headTypePW find? (hd.instantiateLevelParams ks vs) n
      = some (Level.substPW ks vs pw) := by
  rcases headTypePW_some_inv find? h with
    ⟨I, us, ci, u, rfl, hf, hnt, hlen, hpeel, rfl⟩ | ⟨idx, ty, u, rfl, hpeel, rfl⟩
  · have hpd : (Level.zeronessOf u).paramsDefined ci.toConstantVal.levelParams = true := by
      refine Level.zeronessOf_paramsDefined ?_
      have := Expr.allLevelParamsDefined_peelNeverPis n hpeel (hdef I ci hf)
      simpa [Expr.allLevelParamsDefined] using this
    show headTypePW find? (.const I (us.map (Level.subst ks vs))) n = _
    rw [headTypePW_const, hf]
    simp only [hnt, Bool.false_eq_true, if_false, List.length_map, hlen, if_true,
      hpeel, residualPW, Option.map_some]
    exact congrArg some
      (Level.substPW_comp (pw := Level.zeronessOf u) hlen hpd).symm
  · show residualPW ((ty.instantiateLevelParams ks vs).peelNeverPis n) = _
    rw [Expr.peelNeverPis_instantiateLevelParams n ks vs hpeel]
    exact congrArg some (Level.zeronessOf_subst ks vs u)

/-- **The reader commutes with level instantiation.**  Every datum the
reader answers with is the instantiated datum of the instantiated
term — a `∀`'s stored datum is `substPW`'d by
`Expr.instantiateLevelParams` itself, a `Sort`'s is `.never` either
way, and a head application's is `headTypePW`'s. -/
theorem typeSortPW_instantiateLevelParams (find? : Name → Option ConstantInfo)
    {ks : List Name} {vs : List Level}
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true)
    {T : Expr} {pw : PropWhen} (h : typeSortPW find? T = some pw) :
    typeSortPW find? (T.instantiateLevelParams ks vs)
      = some (Level.substPW ks vs pw) := by
  cases T
  case forallE ty b m =>
    have : pw = m.pw := (Option.some.inj h).symm
    subst this; rfl
  case sort u =>
    have : pw = .never := (Option.some.inj h).symm
    subst this
    rw [Level.substPW_never]
    rfl
  case const nm us =>
    show headTypePW find? (Expr.const nm (us.map (Level.subst ks vs))) 0 = _
    exact headTypePW_instantiateLevelParams find? hdef (hd := .const nm us) h
  case fvar idx ty =>
    show headTypePW find? (Expr.fvar idx (ty.instantiateLevelParams ks vs)) 0 = _
    exact headTypePW_instantiateLevelParams find? hdef (hd := .fvar idx ty) h
  case app f a =>
    show headTypePW find? ((f.instantiateLevelParams ks vs).getAppFn)
        ((f.instantiateLevelParams ks vs).numArgs + 1) = _
    rw [Expr.getAppFn_instantiateLevelParams, Expr.numArgs_instantiateLevelParams]
    exact headTypePW_instantiateLevelParams find? hdef
      (hd := f.getAppFn) (n := f.numArgs + 1) h
  all_goals exact nomatch h

/-- The reader's environment hypothesis, discharged: every stored
type's level parameters are within its own declared list (`ConstWF`'s
second conjunct). -/
theorem EnvWF.storedLevelParamsDefined {env : Env} (henv : EnvWF env) :
    ∀ n ci, env.find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams
        = true :=
  fun _ _ h => (henv _ (List.mem_of_find?_eq_some h)).2.1

/-! ## The open/close roundtrip, the other way round -/

/-- Opening a binder body and closing it again is the identity: the
body's own free variables are below `d` (so none is captured) and its
loose bound variables are within the binder (so none is shifted).  The
mirror of `abstract1_instantiate1`. -/
theorem Expr.instantiate1_abstract1 {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), WScoped d e → e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar d ty) k).abstract1 d k = e := by
  intro e
  induction e <;> intro k hw hb <;>
    simp_all [WScoped, Expr.looseBVarsBounded, Expr.abstract1, Expr.instantiate1]
  case bvar i =>
    have h1 : ¬ (i > k) := by omega
    by_cases h2 : i = k
    · simp [h2, Expr.abstract1]
    · simp [h1, h2, Expr.abstract1]
  case fvar idx ty' ih =>
    have : ¬ (idx = d) := by omega
    simp [this]

/-! ## The annotation pass's binder clause, with its datum -/

/-- The datum `annotPwPi` writes when the head reader answers. -/
theorem annotPwPi_of_reader {env : Env} {r : CoreFns CheckM} {d : Nat}
    {body' : Expr} {pw : PropWhen}
    (h : typeSortPW env.find? body' = some pw) :
    annotPwPi r env d body' = .ok pw := by
  unfold annotPwPi
  rw [h]; rfl

/-- The datum `annotPwLam` writes when the head reader answers. -/
theorem annotPwLam_of_reader {env : Env} {r : CoreFns CheckM} {d : Nat}
    {body' : Expr} {pw : PropWhen}
    (h : proofPW env.find? body' = some pw) :
    annotPwLam r env d body' = .ok pw := by
  unfold annotPwLam
  rw [h]; rfl

/-- Inversion for `annotate` on ∀-binders **with the datum**: a written
input datum is kept, a placeholder one is `annotPwPi`'s.
(`annotateCore_forallE_inv` takes the datum existentially; the copies'
alignment is precisely a claim about it.) -/
theorem annotateCore_forallE_inv_pw {env : Env} {fuel d : Nat}
    {ty body e' : Expr} {m : BinderMeta}
    (h : annotateCore mode env (fuel + 1) d (.forallE ty body m) = .ok e') :
    ∃ ty' body', annotateCore mode env fuel d ty = .ok ty' ∧
      annotateCore mode env fuel (d + 1)
        (body.instantiate1 (.fvar d ty')) = .ok body' ∧
      ((pwWritten m.pw = true ∧ e' = .forallE ty' (body'.abstract1 d) ⟨m.pw⟩) ∨
        (pwWritten m.pw = false ∧ ∃ pw,
          annotPwPi (pureFns mode env fuel) env (d + 1) body' = .ok pw ∧
          e' = .forallE ty' (body'.abstract1 d) ⟨pw⟩)) := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def] at h
  cases hty : annotateCore mode env fuel d ty with
  | error e => rw [hty] at h; exact nomatch h
  | ok ty' =>
  rw [hty] at h; dsimp only at h
  cases hbody : annotateCore mode env fuel (d + 1)
      (body.instantiate1 (.fvar d ty')) with
  | error e => rw [hbody] at h; exact nomatch h
  | ok body' =>
  rw [hbody] at h; dsimp only at h
  refine ⟨ty', body', rfl, hbody, ?_⟩
  revert h
  split
  · next hc =>
    cases hpw : annotPwPi (pureFns mode env fuel) env (d + 1) body' with
    | error e => intro h; exact nomatch h
    | ok pw =>
      intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inr ⟨by simpa using hc, pw, rfl, h.symm⟩
  · next hc =>
    intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    refine Or.inl ⟨?_, h.symm⟩
    simpa using hc

/-- Inversion for `annotate` on λ-binders **with the datum** (the ∀
twin). -/
theorem annotateCore_lam_inv_pw {env : Env} {fuel d : Nat}
    {ty body e' : Expr} {m : BinderMeta}
    (h : annotateCore mode env (fuel + 1) d (.lam ty body m) = .ok e') :
    ∃ ty' body', annotateCore mode env fuel d ty = .ok ty' ∧
      annotateCore mode env fuel (d + 1)
        (body.instantiate1 (.fvar d ty')) = .ok body' ∧
      ((pwWritten m.pw = true ∧ e' = .lam ty' (body'.abstract1 d) ⟨m.pw⟩) ∨
        (pwWritten m.pw = false ∧ ∃ pw,
          annotPwLam (pureFns mode env fuel) env (d + 1) body' = .ok pw ∧
          e' = .lam ty' (body'.abstract1 d) ⟨pw⟩)) := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def] at h
  cases hty : annotateCore mode env fuel d ty with
  | error e => rw [hty] at h; exact nomatch h
  | ok ty' =>
  rw [hty] at h; dsimp only at h
  cases hbody : annotateCore mode env fuel (d + 1)
      (body.instantiate1 (.fvar d ty')) with
  | error e => rw [hbody] at h; exact nomatch h
  | ok body' =>
  rw [hbody] at h; dsimp only at h
  refine ⟨ty', body', rfl, hbody, ?_⟩
  revert h
  split
  · next hc =>
    cases hpw : annotPwLam (pureFns mode env fuel) env (d + 1) body' with
    | error e => intro h; exact nomatch h
    | ok pw =>
      intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inr ⟨by simpa using hc, pw, rfl, h.symm⟩
  · next hc =>
    intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    refine Or.inl ⟨?_, h.symm⟩
    simpa using hc

/-! ## `AnnotStable`: the annotation pass's fixed points -/

/-- **A term the annotation pass returns unchanged.**  Every binder's
datum is either a real input annotation — which the pass keeps by
construction (`pwWritten`) — or exactly the head reader's answer on the
opened body, which is what `annotPwPi`/`annotPwLam` write when the
reader answers.

The datum is required to be the READER's answer even where the input
datum is a real annotation the pass would keep (`pwWritten`): a written
datum is not preserved by level instantiation — `substPW` can collapse
`ifAllZero [u]` to `.never` at `u := 1`, after which the pass recomputes
— so the reader's answer is the only form that transports.

`.letE` and `.proj` have no clause, and that is not an oversight: the
pass rewrites a `let` to its ζ reduct and re-spells a projection's
display name at the type's head, so neither is ever a fixed point in
general.  Stored types are ζ-free by construction; a `.proj` inside one
is the restriction this predicate carries. -/
inductive AnnotStable (find? : Name → Option ConstantInfo) : Nat → Expr → Prop where
  | bvar {d i} : AnnotStable find? d (.bvar i)
  | fvar {d idx ty} : AnnotStable find? d (.fvar idx ty)
  | sort {d u} : AnnotStable find? d (.sort u)
  | const {d n us} : AnnotStable find? d (.const n us)
  | lit {d l} : AnnotStable find? d (.lit l)
  | app {d f a} : AnnotStable find? d f → AnnotStable find? d a →
      AnnotStable find? d (.app f a)
  | forallE {d ty body m} :
      AnnotStable find? d ty →
      AnnotStable find? (d + 1) (body.instantiate1 (.fvar d ty)) →
      typeSortPW find? (body.instantiate1 (.fvar d ty)) = some m.pw →
      AnnotStable find? d (.forallE ty body m)
  | lam {d ty body m} :
      AnnotStable find? d ty →
      AnnotStable find? (d + 1) (body.instantiate1 (.fvar d ty)) →
      proofPW find? (body.instantiate1 (.fvar d ty)) = some m.pw →
      AnnotStable find? d (.lam ty body m)

/-! ## `AnnotRel`: the same term up to annotated leaves -/

/-- **Two terms that differ only at `R`-related leaves.**  The
elimination's mint puts the pin's components — RAW, as the stream
carries them — where the container's stored type had its parameters;
the auxiliary install annotates the result, and what it produces is the
same term with each component ANNOTATED.  `R` is the leaf relation
"raw component ↦ its annotation". -/
inductive AnnotRel (R : Expr → Expr → Prop) : Expr → Expr → Prop where
  | base {a b} : R a b → AnnotRel R a b
  | bvar (i : Nat) : AnnotRel R (.bvar i) (.bvar i)
  | fvar (idx : Nat) (ty : Expr) : AnnotRel R (.fvar idx ty) (.fvar idx ty)
  | sort (u : Level) : AnnotRel R (.sort u) (.sort u)
  | const (n : Name) (us : List Level) : AnnotRel R (.const n us) (.const n us)
  | lit (l : Literal) : AnnotRel R (.lit l) (.lit l)
  | app {f f' a a'} : AnnotRel R f f' → AnnotRel R a a' →
      AnnotRel R (.app f a) (.app f' a')
  | forallE {ty ty' b b'} (m : BinderMeta) : AnnotRel R ty ty' → AnnotRel R b b' →
      AnnotRel R (.forallE ty b m) (.forallE ty' b' m)
  | lam {ty ty' b b'} (m : BinderMeta) : AnnotRel R ty ty' → AnnotRel R b b' →
      AnnotRel R (.lam ty b m) (.lam ty' b' m)
  | letE {ty ty' v v' b b'} : AnnotRel R ty ty' → AnnotRel R v v' → AnnotRel R b b' →
      AnnotRel R (.letE ty v b) (.letE ty' v' b')
  | proj (s : Name) (i : Nat) {e e'} : AnnotRel R e e' →
      AnnotRel R (.proj s i e) (.proj s i e')

theorem AnnotRel.refl (R : Expr → Expr → Prop) : ∀ e : Expr, AnnotRel R e e := by
  intro e
  induction e with
  | bvar i => exact .bvar i
  | fvar idx ty _ => exact .fvar idx ty
  | sort u => exact .sort u
  | const n us => exact .const n us
  | lit l => exact .lit l
  | app f a ihf iha => exact .app ihf iha
  | forallE ty b m iht ihb => exact .forallE m iht ihb
  | lam ty b m iht ihb => exact .lam m iht ihb
  | letE ty v b iht ihv ihb => exact .letE iht ihv ihb
  | proj s i e ih => exact .proj s i ih

/-- The relation survives opening a binder: the substituted value is
the same on both sides, and the `R`-related leaves are bvar-closed, so
the substitution does not reach them. -/
theorem AnnotRel.instantiate1 {R : Expr → Expr → Prop}
    (hRc : ∀ a b, R a b → a.looseBVarsBounded 0 = true ∧ b.looseBVarsBounded 0 = true)
    (x : Expr) : ∀ {e e' : Expr}, AnnotRel R e e' → ∀ k : Nat,
      AnnotRel R (e.instantiate1 x k) (e'.instantiate1 x k) := by
  intro e e' hr
  induction hr with
  | base hab =>
    intro k
    obtain ⟨ha, hb⟩ := hRc _ _ hab
    rw [Expr.instantiate1_eq_self (Expr.looseBVarsBounded_mono (Nat.zero_le k) ha),
      Expr.instantiate1_eq_self (Expr.looseBVarsBounded_mono (Nat.zero_le k) hb)]
    exact .base hab
  | bvar i =>
    intro k
    show AnnotRel R (if i = k then x else _) (if i = k then x else _)
    by_cases hi : i = k
    · rw [if_pos hi]; exact AnnotRel.refl R x
    · rw [if_neg hi]
      split <;> exact .bvar _
  | fvar idx ty => intro k; exact .fvar idx ty
  | sort u => intro k; exact .sort u
  | const n us => intro k; exact .const n us
  | lit l => intro k; exact .lit l
  | app _ _ ihf iha => intro k; exact .app (ihf k) (iha k)
  | forallE m _ _ iht ihb => intro k; exact .forallE m (iht k) (ihb (k + 1))
  | lam m _ _ iht ihb => intro k; exact .lam m (iht k) (ihb (k + 1))
  | letE _ _ _ iht ihv ihb => intro k; exact .letE (iht k) (ihv k) (ihb (k + 1))
  | proj s i _ ih => intro k; exact .proj s i (ih k)

/-! ## The pass on a stable term -/

private theorem annot_bvar {env : Env} {f d i : Nat} {r : Expr}
    (h : annotateCore mode env (f + 1) d (.bvar i) = .ok r) : r = .bvar i := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

private theorem annot_fvar {env : Env} {f d idx : Nat} {ty r : Expr}
    (h : annotateCore mode env (f + 1) d (.fvar idx ty) = .ok r) : r = .fvar idx ty := by
  rw [annotateCore_succ] at h
  simp only [annotateBody] at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
  · simp only [throw, throwThe, MonadExceptOf.throw] at h; exact nomatch h

private theorem annot_sort {env : Env} {f d : Nat} {u : Level} {r : Expr}
    (h : annotateCore mode env (f + 1) d (.sort u) = .ok r) : r = .sort u := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

private theorem annot_const {env : Env} {f d : Nat} {n : Name} {us : List Level}
    {r : Expr} (h : annotateCore mode env (f + 1) d (.const n us) = .ok r) :
    r = .const n us := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

private theorem annot_lit {env : Env} {f d : Nat} {l : Literal} {r : Expr}
    (h : annotateCore mode env (f + 1) d (.lit l) = .ok r) : r = .lit l := by
  rw [annotateCore_succ] at h
  cases l with
  | natVal n =>
    simp only [annotateBody] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
    · simp only [throw, throwThe, MonadExceptOf.throw] at h; exact nomatch h
  | strVal s =>
    simp only [annotateBody] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
    · simp only [throw, throwThe, MonadExceptOf.throw] at h; exact nomatch h

/-- **THE ANNOTATION THEOREM (task #298).**  Annotating a term whose
`R`-leaves annotate to their partners, and whose partner is
`AnnotStable`, returns the partner — *data included*.

Read with `R` = "the pin's raw component ↦ its annotation" it says: the
auxiliary install's annotation of a minted copy reproduces the
container's stored type at the ANNOTATED pin, binder data and all.
Read with `R = ⊥` (`annotateCore_eq_self` below) it says the pass is
the identity on its own fixed points — the idempotence the copies'
alignment ultimately rests on.

The hypotheses are the two the leaf relation owes (`hRok`: a raw leaf
annotates to its partner whenever it annotates at all; `hRc`: both are
bvar-closed, so no binder opening reaches inside them) and the two the
term owes (`WScoped`, `looseBVarsBounded`: the open/close roundtrip). -/
theorem annotateCore_of_annotRel {env : Env} {R : Expr → Expr → Prop}
    (hRok : ∀ a b, R a b → ∀ (f d' : Nat) (x : Expr),
      annotateCore mode env f d' a = .ok x → x = b)
    (hRc : ∀ a b, R a b → a.looseBVarsBounded 0 = true ∧ b.looseBVarsBounded 0 = true) :
    ∀ (F : Nat) (e e' : Expr) (d : Nat) (r : Expr),
      AnnotRel R e e' → AnnotStable env.find? d e' →
      WScoped d e' → e'.looseBVarsBounded 0 = true →
      annotateCore mode env F d e = .ok r → r = e' := by
  intro F
  induction F with
  | zero =>
    intro e e' d r _ _ _ _ h
    rw [annotateCore_zero] at h
    simp only [throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  | succ f ih =>
    intro e e' d r hrel hst hw hb h
    cases hrel with
    | base hab => exact hRok _ _ hab _ _ _ h
    | bvar i => exact annot_bvar h
    | fvar idx ty => exact annot_fvar h
    | sort u => exact annot_sort h
    | const n us => exact annot_const h
    | lit l => exact annot_lit h
    | app hrf hra =>
      obtain ⟨fA, aA, hf1, ha1, rfl⟩ := annotateCore_app_inv h
      cases hst with
      | app hsf hsa =>
        simp only [WScoped] at hw
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
        rw [ih _ _ _ _ hrf hsf hw.1 hb.1 hf1, ih _ _ _ _ hra hsa hw.2 hb.2 ha1]
    | forallE m hrty hrb =>
      rename_i ty₀ ty' b₀ b'
      obtain ⟨tyA, bodyA, hty1, hb1, hcase⟩ := annotateCore_forallE_inv_pw h
      cases hst with
      | forallE hsty hsb hpw =>
        simp only [WScoped] at hw
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
        obtain rfl : ty' = tyA := (ih _ _ _ _ hrty hsty hw.1 hb.1 hty1).symm
        obtain rfl : bodyA = b'.instantiate1 (.fvar d ty') :=
          ih _ _ _ _ (AnnotRel.instantiate1 hRc _ hrb 0) hsb
            (WScoped.instantiate1 hw.1 0 hw.2)
            (looseBVarsBounded_instantiate1 b' 0 hb.2) hb1
        have hround : (b'.instantiate1 (.fvar d ty')).abstract1 d = b' :=
          Expr.instantiate1_abstract1 b' 0 hw.2 hb.2
        rcases hcase with ⟨-, rfl⟩ | ⟨-, pw, hpwEq, rfl⟩
        · rw [hround]
        · have hval : pw = m.pw :=
            Except.ok.inj (hpwEq.symm.trans (annotPwPi_of_reader hpw))
          rw [hround, hval]
    | lam m hrty hrb =>
      rename_i ty₀ ty' b₀ b'
      obtain ⟨tyA, bodyA, hty1, hb1, hcase⟩ := annotateCore_lam_inv_pw h
      cases hst with
      | lam hsty hsb hpw =>
        simp only [WScoped] at hw
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
        obtain rfl : ty' = tyA := (ih _ _ _ _ hrty hsty hw.1 hb.1 hty1).symm
        obtain rfl : bodyA = b'.instantiate1 (.fvar d ty') :=
          ih _ _ _ _ (AnnotRel.instantiate1 hRc _ hrb 0) hsb
            (WScoped.instantiate1 hw.1 0 hw.2)
            (looseBVarsBounded_instantiate1 b' 0 hb.2) hb1
        have hround : (b'.instantiate1 (.fvar d ty')).abstract1 d = b' :=
          Expr.instantiate1_abstract1 b' 0 hw.2 hb.2
        rcases hcase with ⟨-, rfl⟩ | ⟨-, pw, hpwEq, rfl⟩
        · rw [hround]
        · have hval : pw = m.pw :=
            Except.ok.inj (hpwEq.symm.trans (annotPwLam_of_reader hpw))
          rw [hround, hval]
    | letE _ _ _ => exact nomatch hst
    | proj s i _ => exact nomatch hst

/-- **The annotation pass is the identity on its fixed points.** -/
theorem annotateCore_eq_self {env : Env} {F : Nat} {e : Expr} {d : Nat} {r : Expr}
    (hst : AnnotStable env.find? d e) (hw : WScoped d e)
    (hb : e.looseBVarsBounded 0 = true)
    (h : annotateCore mode env F d e = .ok r) : r = e :=
  annotateCore_of_annotRel (R := fun _ _ => False)
    (fun _ _ hf => nomatch hf) (fun _ _ hf => nomatch hf) F e e d r
    (AnnotRel.refl _ e) hst hw hb h

end ConLeche
