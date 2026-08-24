import Setlec.Model.Annotate
import Setlec.Model.Erasure

/-!
# The decoration pass: rebuilding the twin from a raw tree (task #100)

A raw-storage kernel stores trees without binder codomain-sort
annotations and must put them back before `infer`/`whnf`/`defeq` — which
read annotations — can run.  `decorate` is the **proof-side spec** of
that rebuild: a structural pass that does *no checking at all*, only
filling each binder's `cod` from a memo (`DecorMemo`, the proof-side
view of the interned `inferC`/`codOfC` pair of task #100 stage 2).

Its theorem is a syntactic identification, not a semantic one:

> `decorate_eq` — on an annotated tree `e`, decorating its erasure
> returns `e` **exactly**, provided the memo agrees with `e`'s
> annotations at every binder (`CodAgree`).

Truthfulness then costs nothing: `decorate_sound` rewrites through the
identification and hands the goal to `annotate_sound`.  That is the
point of the split — the decoration pass carries no semantic burden of
its own, because the annotations it restores are the very ones the
annotation pass already justified.

## Two erasures

`Expr.eraseCod` is hereditary: it descends into `fvar` type
annotations, which is what makes twins survive binder opening during
reduction simulation.  A decoration pass opens binders itself, at
variables whose types it has *already decorated*, so it must not
re-decorate them — its `fvar` clause is the identity.  The matching
erasure is therefore the **shallow** one, `Expr.eraseCodS`, which
leaves `fvar` annotations alone.

The two agree on everything a declaration stores (`eraseCodS_eq` at
`hasFvar = false`, the install-time certificate), so the top-level
statement is unaffected; the shallow form only tracks decorate's own
opened variables.  Keeping the fvar clause non-recursive is also what
makes `decorate` terminate on `sizeB` — the measure `AnnotOk` uses,
for the same reason.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

/-! ## The shallow erasure -/

/-- Erase binder codomain annotations, **not** descending into `fvar`
type annotations (see the module docstring). -/
def Expr.eraseCodS : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx n ty => .fvar idx n ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app f.eraseCodS a.eraseCodS
  | .lam n ty b m => .lam n ty.eraseCodS b.eraseCodS m.eraseCod
  | .forallE n ty b m => .forallE n ty.eraseCodS b.eraseCodS m.eraseCod
  | .letE n ty v b => .letE n ty.eraseCodS v.eraseCodS b.eraseCodS
  | .lit l => .lit l
  | .proj s i e => .proj s i e.eraseCodS

/-- On `fvar`-free trees — every stored declaration, by the install
certificate — the two erasures agree. -/
theorem Expr.eraseCodS_eq : ∀ (e : Expr), e.hasFvar = false →
    e.eraseCodS = e.eraseCod
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => rfl
  | .fvar .., h => absurd h (by simp [Expr.hasFvar])
  | .app f a, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.eraseCodS, Expr.eraseCod, Expr.eraseCodS_eq f h.1,
      Expr.eraseCodS_eq a h.2]
  | .lam _ ty b _, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.eraseCodS, Expr.eraseCod, Expr.eraseCodS_eq ty h.1,
      Expr.eraseCodS_eq b h.2]
  | .forallE _ ty b _, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.eraseCodS, Expr.eraseCod, Expr.eraseCodS_eq ty h.1,
      Expr.eraseCodS_eq b h.2]
  | .letE _ ty v b, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.eraseCodS, Expr.eraseCod, Expr.eraseCodS_eq ty h.1.1,
      Expr.eraseCodS_eq v h.1.2, Expr.eraseCodS_eq b h.2]
  | .proj _ _ e, h => by
    simp only [Expr.hasFvar] at h
    simp [Expr.eraseCodS, Expr.eraseCod, Expr.eraseCodS_eq e h]

/-- The shallow erasure commutes with binder opening at a free
variable — the one substitution a decoration pass performs.  (`fvar`s
are shallow-erasure fixed points, so no side condition is needed.) -/
theorem Expr.eraseCodS_instantiate1_fvar (idx : Nat) (n : Name) (ty : Expr) :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar idx n ty) k).eraseCodS =
        e.eraseCodS.instantiate1 (.fvar idx n ty) k
  | .bvar i, k => by
    simp only [Expr.instantiate1, Expr.eraseCodS]
    by_cases h1 : i = k
    · simp [h1, Expr.eraseCodS]
    · by_cases h2 : i > k <;> simp [h1, h2, Expr.eraseCodS]
  | .fvar _ _ _, _ => by simp [Expr.instantiate1, Expr.eraseCodS]
  | .sort _, _ => by simp [Expr.instantiate1, Expr.eraseCodS]
  | .const _ _, _ => by simp [Expr.instantiate1, Expr.eraseCodS]
  | .lit _, _ => by simp [Expr.instantiate1, Expr.eraseCodS]
  | .app f a, k => by
    simp [Expr.instantiate1, Expr.eraseCodS,
      Expr.eraseCodS_instantiate1_fvar idx n ty f k,
      Expr.eraseCodS_instantiate1_fvar idx n ty a k]
  | .lam _ t b _, k => by
    simp [Expr.instantiate1, Expr.eraseCodS,
      Expr.eraseCodS_instantiate1_fvar idx n ty t k,
      Expr.eraseCodS_instantiate1_fvar idx n ty b (k + 1)]
  | .forallE _ t b _, k => by
    simp [Expr.instantiate1, Expr.eraseCodS,
      Expr.eraseCodS_instantiate1_fvar idx n ty t k,
      Expr.eraseCodS_instantiate1_fvar idx n ty b (k + 1)]
  | .letE _ t v b, k => by
    simp [Expr.instantiate1, Expr.eraseCodS,
      Expr.eraseCodS_instantiate1_fvar idx n ty t k,
      Expr.eraseCodS_instantiate1_fvar idx n ty v k,
      Expr.eraseCodS_instantiate1_fvar idx n ty b (k + 1)]
  | .proj _ _ e, k => by
    simp [Expr.instantiate1, Expr.eraseCodS,
      Expr.eraseCodS_instantiate1_fvar idx n ty e k]

/-! ## Closing what was opened

`Setlec/Verify/Abstract.lean` has the roundtrip in the direction
`abstract` then `instantiate`; the decoration pass needs the other
one — it opens a binder, decorates, and closes again. -/

theorem Expr.instantiate1_abstract1 {d : Nat} {n : Name} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), WScoped d e → e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar d n ty) k).abstract1 d k = e := by
  intro e
  induction e <;> intro k hw hb <;>
    simp_all [Expr.instantiate1, Expr.abstract1, WScoped,
      Expr.looseBVarsBounded]
  case bvar i =>
    by_cases h1 : i = k
    · simp [h1, Expr.abstract1]
    · have h2 : ¬ (i > k) := by omega
      simp [h1, h2, Expr.abstract1]
  case fvar idx nm t =>
    intro hd
    omega

/-! ## The memo and the pass -/

/-- The lookups a decoration pass performs, as partial functions of
(depth, node): the proof-side view of the interned `inferC`/`codOfC`
memos.  A `∀`-binder's codomain sort is `codOf` of its opened body; a
`λ`-binder's is `codOf` of that body's *inferred type*, hence the two
components. -/
structure DecorMemo where
  /-- The inference memo (`IState.inferC`). -/
  ty : Nat → Expr → Option Expr
  /-- The codomain-sort memo (`IState.codOfC`). -/
  cod : Nat → Expr → Option Level

/-- Rebuild the annotated twin of a raw tree: structural everywhere,
filling each binder's codomain sort from the memo.  No inference, no
reduction, no definitional equality — the pass is *pure bookkeeping*,
which is exactly why its theorem (`decorate_eq`) is syntactic. -/
def decorate (M : DecorMemo) : Nat → Expr → Expr
  | _, .bvar i => .bvar i
  | _, .fvar idx n ty => .fvar idx n ty
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | _, .lit l => .lit l
  | d, .app f a => .app (decorate M d f) (decorate M d a)
  | d, .proj s i e => .proj s i (decorate M d e)
  | d, .letE n ty v b =>
    .letE n (decorate M d ty) (decorate M d v) (decorate M d b)
  | d, .forallE n ty b m =>
    let ty' := decorate M d ty
    let b' := decorate M (d + 1) (b.instantiate1 (.fvar d n ty'))
    .forallE n ty' (b'.abstract1 d) ⟨m.bi, M.cod (d + 1) b'⟩
  | d, .lam n ty b m =>
    let ty' := decorate M d ty
    let b' := decorate M (d + 1) (b.instantiate1 (.fvar d n ty'))
    .lam n ty' (b'.abstract1 d) ⟨m.bi, (M.ty (d + 1) b').bind (M.cod (d + 1))⟩
termination_by _d e => e.sizeB
decreasing_by
  all_goals first
    | (simp [Expr.sizeB]; omega)
    | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
    | (simp [Expr.sizeB])

/-- The memo agrees with an annotated tree's annotations, at the keys
`decorate` looks them up under.  This is the hypothesis that carries
the *whole* content of decoration correctness — the flip discharges it
from the interned memos' `ISOK` clauses. -/
def CodAgree (M : DecorMemo) : Nat → Expr → Prop
  | _, .bvar _ | _, .fvar .. | _, .sort _ | _, .const .. | _, .lit _ => True
  | d, .app f a => CodAgree M d f ∧ CodAgree M d a
  | d, .proj _ _ e => CodAgree M d e
  -- `annotate`'s `letE` clause zeta-reduces (value transparency, see
  -- DESIGN.md), so its output — and hence every decoration target — is
  -- let-free; there is nothing for a memo to agree with.
  | _, .letE .. => False
  | d, .forallE n ty b m =>
    CodAgree M d ty ∧
    CodAgree M (d + 1) (b.instantiate1 (.fvar d n ty)) ∧
    M.cod (d + 1) (b.instantiate1 (.fvar d n ty)) = m.cod
  | d, .lam n ty b m =>
    CodAgree M d ty ∧
    CodAgree M (d + 1) (b.instantiate1 (.fvar d n ty)) ∧
    (M.ty (d + 1) (b.instantiate1 (.fvar d n ty))).bind (M.cod (d + 1)) = m.cod
termination_by _d e => e.sizeB
decreasing_by
  all_goals first
    | (simp [Expr.sizeB]; omega)
    | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
    | (simp [Expr.sizeB])

/-! ## The identification -/

/-- **Decoration recovers the twin exactly.**  Decorating the (shallow)
erasure of an annotated tree returns that tree, whenever the memo
agrees with its annotations at every binder.  Everything decoration has
to get right sits in `CodAgree`; the rest is bookkeeping, and the proof
says so. -/
theorem decorate_eq_aux (M : DecorMemo) :
    ∀ (k : Nat) (e : Expr), e.sizeB ≤ k → ∀ (d : Nat), WScoped d e →
      e.looseBVarsBounded 0 = true → CodAgree M d e →
      decorate M d e.eraseCodS = e := by
  intro k
  induction k with
  | zero =>
    intro e hk
    exact absurd hk (by have := Expr.sizeB_pos e; omega)
  | succ k ih =>
    intro e hk d hw hb hA
    cases e with
    | bvar i => simp [Expr.eraseCodS, decorate]
    | fvar idx n t => simp [Expr.eraseCodS, decorate]
    | sort u => simp [Expr.eraseCodS, decorate]
    | const n us => simp [Expr.eraseCodS, decorate]
    | lit l => simp [Expr.eraseCodS, decorate]
    | app f a =>
      simp only [Expr.sizeB] at hk
      simp only [WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [CodAgree] at hA
      simp only [Expr.eraseCodS, decorate]
      rw [ih f (by omega) d hw.1 hb.1 hA.1, ih a (by omega) d hw.2 hb.2 hA.2]
    | proj s i e =>
      simp only [Expr.sizeB] at hk
      simp only [WScoped] at hw
      simp only [Expr.looseBVarsBounded] at hb
      simp only [CodAgree] at hA
      simp only [Expr.eraseCodS, decorate]
      rw [ih e (by omega) d hw hb hA]
    | letE n ty v b => exact absurd hA (by simp [CodAgree])
    | forallE n ty b m =>
      simp only [Expr.sizeB] at hk
      simp only [WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [CodAgree] at hA
      simp only [Expr.eraseCodS, decorate]
      rw [ih ty (by omega) d hw.1 hb.1 hA.1]
      rw [← Expr.eraseCodS_instantiate1_fvar]
      rw [ih (b.instantiate1 (.fvar d n ty))
        (by rw [Expr.sizeB_instantiate1 _ rfl]; omega) (d + 1)
        (hw.1.instantiate1 0 hw.2)
        (looseBVarsBounded_instantiate1 b 0 hb.2) hA.2.1]
      rw [Expr.instantiate1_abstract1 b 0 hw.2 hb.2, hA.2.2]
      cases m
      rfl
    | lam n ty b m =>
      simp only [Expr.sizeB] at hk
      simp only [WScoped] at hw
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [CodAgree] at hA
      simp only [Expr.eraseCodS, decorate]
      rw [ih ty (by omega) d hw.1 hb.1 hA.1]
      rw [← Expr.eraseCodS_instantiate1_fvar]
      rw [ih (b.instantiate1 (.fvar d n ty))
        (by rw [Expr.sizeB_instantiate1 _ rfl]; omega) (d + 1)
        (hw.1.instantiate1 0 hw.2)
        (looseBVarsBounded_instantiate1 b 0 hb.2) hA.2.1]
      rw [Expr.instantiate1_abstract1 b 0 hw.2 hb.2, hA.2.2]
      cases m
      rfl

@[inherit_doc decorate_eq_aux]
theorem decorate_eq (M : DecorMemo) {e : Expr} {d : Nat} (hw : WScoped d e)
    (hb : e.looseBVarsBounded 0 = true) (hA : CodAgree M d e) :
    decorate M d e.eraseCodS = e :=
  decorate_eq_aux M e.sizeB e (Nat.le_refl _) d hw hb hA

/-- On a stored (`fvar`-free) tree the two erasures agree, so the
identification is about the erasure the environment actually keeps. -/
theorem decorate_eraseCod_eq (M : DecorMemo) {e : Expr} {d : Nat}
    (hf : e.hasFvar = false) (hw : WScoped d e)
    (hb : e.looseBVarsBounded 0 = true) (hA : CodAgree M d e) :
    decorate M d e.eraseCod = e := by
  rw [← Expr.eraseCodS_eq e hf]
  exact decorate_eq M hw hb hA

/-! ## Truthfulness, for free

The decoration pass carries no semantic burden: the annotations it puts
back are the ones the annotation pass already justified, and
`decorate_eq` says they are put back *identically*.  So `AnnotOk` of a
decorated raw tree is `annotate_sound` after one rewrite — this is the
payoff of splitting the pass in two. -/

/-- **Decoration is truthful.**  If the kernel's annotation pass turned
`e` into `e'`, then decorating what a raw-storage kernel keeps of `e'`
reproduces `e'`, whose annotations `annotate_sound` justifies. -/
theorem decorate_sound (m : EnvModel V env) {F : Nat} (M : DecorMemo)
    {e e' : Expr} {d : Nat}
    (hann : annotateCore env F d e = .ok e')
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hfA : e'.hasFvar = false) (hbA : e'.looseBVarsBounded 0 = true)
    (hA : CodAgree M d e')
    (ρ : Nat → V) (hok : FvarsOk V m.val env φ d ρ e) :
    AnnotOk V m.val env φ d ρ (decorate M d e'.eraseCod) := by
  rw [decorate_eraseCod_eq M hfA (annotateCore_WScoped F e hann hw) hbA hA]
  exact annotate_sound m e hann hw hb hLb ρ hok

end Setlec
