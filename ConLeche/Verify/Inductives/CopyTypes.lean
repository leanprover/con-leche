module

public import ConLeche.Kernel.Inductives.NestedElim
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
recomputation commutes with instantiation for elementary reasons.

**What is proved here.**

* `SortAgree find? A v` — "`v` reads, for the head reader, like a
  variable declared of type `A`": at every arity, the datum the reader
  computes from `v`'s head is the one it computes from `A`'s telescope.
  This is the hypothesis a *pin component* has to meet.
* `typeSortPW_instantiate1_congr` — the reader cannot tell an opened
  binder from a `SortAgree` value: substituting one for the other
  leaves every reading unchanged.
* `typeSortPW_instantiateLevelParams` — the reader commutes with level
  instantiation through `substPW`, the datum's own substitution
  (`Level.zeronessOf_subst`, `Level.substPW_comp`), under `EnvWF`'s
  bound on stored types' level parameters.
* `AnnotStable find? d e` — the pass's fixed points: at every binder
  either the datum is a real input annotation, which the pass keeps by
  construction, or it is the reader's answer on the opened body.
* `AnnotRel R e e'` — two terms differing only at `R`-related,
  bvar-closed leaves ("the raw pin component and its annotation").
* **`annotateCore_of_annotRel`** — THE THEOREM: annotating `e` returns
  `e'`, *binder data included*, whenever the leaves annotate to their
  partners and `e'` is `AnnotStable`, `WScoped` and bvar-closed.  With
  `R = ⊥` it is `annotateCore_eq_self`: the pass is the identity on its
  own fixed points.
* `typeSortPW_sort`, `typeSortPW_forallE`, `typeSortPW_mkAppN_const`
  and the two transports `typeSortPW_at_pin` / `typeSortPW_at_levels`:
  what a copy's binder obligations are discharged by.

**What is NOT here** — the task's honest frontier.  Where the reader
DECLINES (a `.proj`- or redex-headed codomain), the datum is
`Level.zeronessOf` of an INFERRED sort, and its stability under
instantiation is the general inference-substitution theorem the tree
does not have; and the *telescope* bookkeeping that turns these node
facts into the copy's whole stored type (`instPis`, `closeTelescope`,
`normCtorValM`) is the model lane's next step.  DESIGN's `#### K.4`
states both.
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
stored type the same way and instantiates; at a λ head it peels the
binder against an argument (the β clause, task #301).  `SortAgree find?
A v` says the two answers coincide at every arity — unapplied (where
the reader's own `∀`/`Sort` cases can fire on `v`, which they never do
on a variable) and at every positive arity.

This is the ONE hypothesis the substitution congruence below needs of
the substituted value, and it is what a pin component's typing says in
the reader's terms: `D : A` gives `typeSortPW find? D = residualPW
(A.peelNeverPis 0)` wherever the reader is complete for `D`.

The readers consulted here are the annotation pass's own grade
(`beta := true`): these are facts about the data `annotPwPi` writes. -/
def SortAgree (find? : Name → Option ConstantInfo) (A v : Expr) : Prop :=
  typeSortPW find? true v = residualPW (A.peelNeverPis 0) ∧
    ∀ n : Nat, headTypePW find? true v.getAppFn (v.numArgs + (n + 1))
      = residualPW (A.peelNeverPis (n + 1))

/-- `SortAgree` in the reader's own arity-indexed form: the first
conjunct is `n = 0`, the second is `n = k + 1` through
`typePWAt_spine`. -/
theorem SortAgree.at {find? : Name → Option ConstantInfo} {A v : Expr}
    (h : SortAgree find? A v) (n : Nat) :
    typePWAt find? true v n = residualPW (A.peelNeverPis n) := by
  cases n with
  | zero => exact h.1
  | succ n => rw [typePWAt_spine]; exact h.2 n

/-- The arity-indexed form IS `SortAgree`. -/
theorem SortAgree.of_at {find? : Name → Option ConstantInfo} {A v : Expr}
    (h : ∀ n : Nat, typePWAt find? true v n = residualPW (A.peelNeverPis n)) :
    SortAgree find? A v :=
  ⟨h 0, fun n => by rw [headTypePW, ← typePWAt_spine]; exact h (n + 1)⟩

/-- A variable reads like itself. -/
theorem SortAgree.fvar_refl (find? : Name → Option ConstantInfo) (idx : Nat)
    (A : Expr) : SortAgree find? A (.fvar idx A) :=
  SortAgree.of_at fun _ => rfl

/-- **The λ rule** (task #301): a λ reads like a ∀ whose codomain its
body reads like.  This is the shape a *dependent* container's family
parameter takes at a pin — `Std.DTreeMap.Raw α (fun a => β a)` against
the declared domain `α → Type v` — and before the reader had a λ clause
BOTH readers declined on it, so the annotator inferred and the copies'
data were out of reach (the kernel lane's measurement, DESIGN `#### K.7`).

The `.never` hypothesis is the ∀ side's: `peelNeverPis` walks only
never-data binders, and a *type-family* parameter's binder always
carries `.never` (its codomain is a `Sort`, whose own sort is a
successor).  Where it fails, the ∀ side reads `none` at every positive
arity and the equality is about the λ's side alone — which is why the
one-directional form (`SortAgreeW.lam`) needs no hypothesis at all. -/
theorem SortAgree.lam {find? : Name → Option ConstantInfo}
    {ty Ab ty' b : Expr} {m m' : BinderMeta} (hnev : m.pw.isNever = true)
    (hb : SortAgree find? Ab b) :
    SortAgree find? (.forallE ty Ab m) (.lam ty' b m') := by
  refine SortAgree.of_at fun n => ?_
  cases n with
  | zero => rfl
  | succ n =>
    show typePWAt find? true b n
      = residualPW ((Expr.forallE ty Ab m).peelNeverPis (n + 1))
    rw [show (Expr.forallE ty Ab m).peelNeverPis (n + 1) = Ab.peelNeverPis n from by
      simp only [Expr.peelNeverPis, hnev, if_true]]
    exact hb.at n

theorem headTypePW_bvar (find? : Name → Option ConstantInfo) (beta : Bool)
    (i n : Nat) : headTypePW find? beta (.bvar i) n = none := by
  cases n <;> rfl

theorem headTypePW_fvar (find? : Name → Option ConstantInfo) (beta : Bool)
    (idx n : Nat) (A : Expr) :
    headTypePW find? beta (.fvar idx A) n = residualPW (A.peelNeverPis n) := rfl

/-- **The reader cannot see a `SortAgree` substitution.**  Every
reading the reader makes of a term with the value substituted in is the
reading it makes with the binder opened at a variable of the declared
type — which is what makes the annotation pass's *recomputed* data
agree, node by node, on the two sides.  The λ case is the β clause's:
the reading descends into the body, where the induction hypothesis is
the same statement one binder down. -/
theorem typePWAt_instantiate1_congr (find? : Name → Option ConstantInfo)
    {A v : Expr} (idx : Nat) (h : SortAgree find? A v) :
    ∀ (e : Expr) (d n : Nat),
      typePWAt find? true (e.instantiate1 v d) n
        = typePWAt find? true (e.instantiate1 (.fvar idx A) d) n := by
  intro e
  induction e with
  | bvar i =>
    intro d n
    by_cases hi : i = d
    · show typePWAt find? true (if i = d then v else _) n
        = typePWAt find? true (if i = d then (Expr.fvar idx A) else _) n
      rw [if_pos hi, if_pos hi]
      exact h.at n
    · show typePWAt find? true (if i = d then v else _) n
        = typePWAt find? true (if i = d then (Expr.fvar idx A) else _) n
      rw [if_neg hi, if_neg hi]
  | app f a ihf _ => intro d n; exact ihf d (n + 1)
  | lam ty b m _ ihb =>
    intro d n
    cases n with
    | zero => rfl
    | succ n =>
      show typePWAt find? true (b.instantiate1 v (d + 1)) n
        = typePWAt find? true (b.instantiate1 (.fvar idx A) (d + 1)) n
      exact ihb (d + 1) n
  | _ => intro d n; cases n <;> rfl

/-- The head reader at a positive arity cannot tell the opened binder
from a `SortAgree` value (`typePWAt_instantiate1_congr` at the spine). -/
theorem headTypePW_instantiate1_congr (find? : Name → Option ConstantInfo)
    {A v : Expr} (idx : Nat) (h : SortAgree find? A v) :
    ∀ (e : Expr) (d n : Nat),
      headTypePW find? true ((e.instantiate1 v d).getAppFn)
          ((e.instantiate1 v d).numArgs + (n + 1))
        = headTypePW find? true ((e.instantiate1 (.fvar idx A) d).getAppFn)
          ((e.instantiate1 (.fvar idx A) d).numArgs + (n + 1)) := by
  intro e d n
  rw [headTypePW, headTypePW, ← typePWAt_spine, ← typePWAt_spine]
  exact typePWAt_instantiate1_congr find? idx h e d (n + 1)

/-- **The reader cannot see a `SortAgree` substitution** (the unapplied
reading). -/
theorem typeSortPW_instantiate1_congr (find? : Name → Option ConstantInfo)
    {A v : Expr} (idx : Nat) (h : SortAgree find? A v) :
    ∀ (e : Expr) (d : Nat),
      typeSortPW find? true (e.instantiate1 v d)
        = typeSortPW find? true (e.instantiate1 (.fvar idx A) d) :=
  fun e d => typePWAt_instantiate1_congr find? idx h e d 0

/-! ## `ProofAgree`: the λ-binder reader's twin

`AnnotStable`'s λ clause reads `proofPW` of the opened body, so the
copies' λ binders need the same substitution congruence for the *proof*
reader that `SortAgree` buys for the type reader.  At the annotation
pass's grade the two readers coincide on a λ (`proofPW_eq_head`), so one
hypothesis about the head does for both. -/

/-- At the annotation grade (`beta := true`) `proofPW` IS its head
reader: the λ clause `headProofPW` gained at task #301 answers with the
same datum `proofPW`'s own λ clause does. -/
theorem proofPW_eq_head (find? : Name → Option ConstantInfo) (a : Expr) :
    proofPW find? true a = headProofPW find? true a.getAppFn := by
  cases a <;> rfl

/-- **`v` reads like a variable declared of type `A` for the λ-binder
reader**: "is this term a proof?" of the value is "is this type a
proposition?" of the declared type. -/
def ProofAgree (find? : Name → Option ConstantInfo) (A v : Expr) : Prop :=
  headProofPW find? true v.getAppFn = typeSortPW find? true A

/-- A variable reads like itself. -/
theorem ProofAgree.fvar_refl (find? : Name → Option ConstantInfo) (idx : Nat)
    (A : Expr) : ProofAgree find? A (.fvar idx A) := by rfl

/-- **The λ rule for the proof reader** (task #301): a λ reads like a ∀
whose datum it carries.  The obligation is the DATUM's, not the
reader's: the annotated component's λ datum and the container's binder
datum are both "the zero-ness of the sort of the codomain", and the
kernel lane measured them equal at every λ-pin of the corpus (both
`.never`: a type family's body is a type, and a type is not a proof). -/
theorem ProofAgree.lam {find? : Name → Option ConstantInfo}
    {ty Ab ty' b : Expr} {m m' : BinderMeta} (hpw : m'.pw = m.pw) :
    ProofAgree find? (.forallE ty Ab m) (.lam ty' b m') := by
  show headProofPW find? true (.lam ty' b m') = some m.pw
  rw [show headProofPW find? true (.lam ty' b m') = some m'.pw from rfl, hpw]

/-- **The proof reader cannot see the substitution** either, given both
agreements at the leaf. -/
theorem headProofPW_instantiate1_congr (find? : Name → Option ConstantInfo)
    {A v : Expr} (idx : Nat) (hp : ProofAgree find? A v) :
    ∀ (e : Expr) (d : Nat),
      headProofPW find? true ((e.instantiate1 v d).getAppFn)
        = headProofPW find? true ((e.instantiate1 (.fvar idx A) d).getAppFn) := by
  intro e
  induction e with
  | bvar i =>
    intro d
    by_cases hi : i = d
    · show headProofPW find? true ((if i = d then v else _).getAppFn)
        = headProofPW find? true ((if i = d then (Expr.fvar idx A) else _).getAppFn)
      rw [if_pos hi, if_pos hi]
      exact hp
    · show headProofPW find? true ((if i = d then v else _).getAppFn)
        = headProofPW find? true ((if i = d then (Expr.fvar idx A) else _).getAppFn)
      rw [if_neg hi, if_neg hi]
  | app f a ihf _ => intro d; exact ihf d
  | _ => intro d; rfl

theorem proofPW_instantiate1_congr (find? : Name → Option ConstantInfo)
    {A v : Expr} (idx : Nat) (hp : ProofAgree find? A v) :
    ∀ (e : Expr) (d : Nat),
      proofPW find? true (e.instantiate1 v d)
        = proofPW find? true (e.instantiate1 (.fvar idx A) d) := by
  intro e d
  rw [proofPW_eq_head, proofPW_eq_head]
  exact headProofPW_instantiate1_congr find? idx hp e d

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
theorem headTypePW_const (find? : Name → Option ConstantInfo) (beta : Bool)
    (I : Name) (us : List Level) (n : Nat) :
    headTypePW find? beta (.const I us) n =
      match find? I with
      | some ci =>
        if ci.isTowerEntry then none else
        if us.length = ci.toConstantVal.levelParams.length then
          (residualPW (ci.toConstantVal.type.peelNeverPis n)).map
            (Level.substPW ci.toConstantVal.levelParams us)
        else none
      | none => none := rfl

/-- The reader's answer at a CONSTANT head, inverted: the lookup
succeeded on a non-tower entry at the right number of levels, and the
stored type peeled to a sort. -/
theorem typePWAt_const_some_inv (find? : Name → Option ConstantInfo)
    (beta : Bool) {I : Name} {us : List Level} {n : Nat} {pw : PropWhen}
    (h : typePWAt find? beta (.const I us) n = some pw) :
    ∃ ci u, find? I = some ci ∧ ci.isTowerEntry = false ∧
      us.length = ci.toConstantVal.levelParams.length ∧
      ci.toConstantVal.type.peelNeverPis n = some (.sort u) ∧
      pw = Level.substPW ci.toConstantVal.levelParams us (Level.zeronessOf u) := by
  simp only [typePWAt] at h
  cases hf : find? I with
  | none => rw [hf] at h; exact nomatch h
  | some ci =>
    rw [hf] at h
    dsimp only at h
    split at h
    · exact nomatch h
    · next hnt =>
      split at h
      · next hlen =>
        cases hr : residualPW (ci.toConstantVal.type.peelNeverPis n) with
        | none => rw [hr] at h; exact nomatch h
        | some pw0 =>
          rw [hr] at h
          obtain ⟨u, hu, rfl⟩ := residualPW_some_inv hr
          exact ⟨ci, u, rfl, Bool.eq_false_iff.mpr hnt, hlen, hu,
            (Option.some.inj h).symm⟩
      · exact nomatch h

/-- **The reader commutes with level instantiation**, at every arity and
either grade, through the datum's own substitution `substPW`.  The
constant-head case is `Level.substPW_comp` — the stored type is NOT
instantiated, only the use-site levels are — the `fvar` case is
`Level.zeronessOf_subst`, a ∀'s datum is `substPW`'d by
`Expr.instantiateLevelParams` itself, a `Sort`'s is `.never` either way,
and the β clause simply descends into the body.

The hypothesis is the environment's: every stored type's levels are
within its declared parameters (`ConstWF`, hence `EnvWF`). -/
theorem typePWAt_instantiateLevelParams (find? : Name → Option ConstantInfo)
    (beta : Bool) {ks : List Name} {vs : List Level}
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true) :
    ∀ (e : Expr) (n : Nat) (pw : PropWhen), typePWAt find? beta e n = some pw →
      typePWAt find? beta (e.instantiateLevelParams ks vs) n
        = some (Level.substPW ks vs pw) := by
  intro e
  induction e with
  | const I us =>
    intro n pw h
    obtain ⟨ci, u, hf, hnt, hlen, hpeel, rfl⟩ := typePWAt_const_some_inv find? beta h
    have hpd : (Level.zeronessOf u).paramsDefined ci.toConstantVal.levelParams = true := by
      refine Level.zeronessOf_paramsDefined ?_
      have := Expr.allLevelParamsDefined_peelNeverPis n hpeel (hdef I ci hf)
      simpa [Expr.allLevelParamsDefined] using this
    show typePWAt find? beta (.const I (us.map (Level.subst ks vs))) n = _
    rw [← headTypePW, headTypePW_const, hf]
    simp only [hnt, Bool.false_eq_true, if_false, List.length_map, hlen, if_true,
      hpeel, residualPW, Option.map_some]
    exact congrArg some
      (Level.substPW_comp (pw := Level.zeronessOf u) hlen hpd).symm
  | fvar idx ty _ =>
    intro n pw h
    obtain ⟨u, hu, rfl⟩ := residualPW_some_inv h
    show residualPW ((ty.instantiateLevelParams ks vs).peelNeverPis n) = _
    rw [Expr.peelNeverPis_instantiateLevelParams n ks vs hu]
    exact congrArg some (Level.zeronessOf_subst ks vs u)
  | app f a ihf _ => intro n pw h; exact ihf (n + 1) pw h
  | lam ty b m _ ihb =>
    intro n pw h
    cases n with
    | zero => exact nomatch h
    | succ n =>
      cases beta with
      | false => exact nomatch h
      | true => exact ihb n pw h
  | forallE ty b m _ _ =>
    intro n pw h
    cases n with
    | zero => obtain rfl : pw = m.pw := (Option.some.inj h).symm; rfl
    | succ n => exact nomatch h
  | sort u =>
    intro n pw h
    cases n with
    | zero =>
      obtain rfl : pw = PropWhen.never := (Option.some.inj h).symm
      show typePWAt find? beta (.sort (Level.subst ks vs u)) 0 = _
      rw [Level.substPW_never]
      rfl
    | succ n => exact nomatch h
  | _ => intro n pw h; cases n <;> exact nomatch h

/-- **The head reader commutes with level instantiation.** -/
theorem headTypePW_instantiateLevelParams (find? : Name → Option ConstantInfo)
    (beta : Bool) {ks : List Name} {vs : List Level}
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true)
    {hd : Expr} {n : Nat} {pw : PropWhen} (h : headTypePW find? beta hd n = some pw) :
    headTypePW find? beta (hd.instantiateLevelParams ks vs) n
      = some (Level.substPW ks vs pw) :=
  typePWAt_instantiateLevelParams find? beta hdef hd n pw h

/-- **The reader commutes with level instantiation.**  Every datum the
reader answers with is the instantiated datum of the instantiated
term. -/
theorem typeSortPW_instantiateLevelParams (find? : Name → Option ConstantInfo)
    (beta : Bool) {ks : List Name} {vs : List Level}
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true)
    {T : Expr} {pw : PropWhen} (h : typeSortPW find? beta T = some pw) :
    typeSortPW find? beta (T.instantiateLevelParams ks vs)
      = some (Level.substPW ks vs pw) :=
  typePWAt_instantiateLevelParams find? beta hdef T 0 pw h

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
    (h : typeSortPW env.find? true body' = some pw) :
    annotPwPi r env d body' = .ok pw := by
  unfold annotPwPi
  rw [h]; rfl

/-- The datum `annotPwLam` writes when the head reader answers. -/
theorem annotPwLam_of_reader {env : Env} {r : CoreFns CheckM} {d : Nat}
    {body' : Expr} {pw : PropWhen}
    (h : proofPW env.find? true body' = some pw) :
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

**The obligation is only at a `.never` binder.**  A real input
annotation (`pwWritten`, i.e. anything but `.never`) the pass KEEPS by
construction, so such a binder owes nothing; and a minted copy inherits
its data from the container's stored type, so at those binders the
copy's datum IS the container's on the nose.  What is left is exactly
the `.never` binders — every Type-valued codomain — and there the
obligation is that the reader answers `.never` again, which is the
reader's most robust case (a `Sort` codomain, a `∀` codomain whose own
datum is `.never`, or a constant-headed one whose stored result sort is
never zero).

Note that the predicate is stated of the term the pass is to REPRODUCE,
not of the term it starts from: a written datum is not preserved by
level instantiation — `substPW` collapses `ifAllZero [u]` to `.never` at
`u := 1` — so the `.never` binders of the INSTANTIATED type are the ones
that must be discharged, and they are more than the container's own.

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
      (pwWritten m.pw = true ∨
        typeSortPW find? true (body.instantiate1 (.fvar d ty)) = some m.pw) →
      AnnotStable find? d (.forallE ty body m)
  | lam {d ty body m} :
      AnnotStable find? d ty →
      AnnotStable find? (d + 1) (body.instantiate1 (.fvar d ty)) →
      (pwWritten m.pw = true ∨
        proofPW find? true (body.instantiate1 (.fvar d ty)) = some m.pw) →
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
        rcases hcase with ⟨-, rfl⟩ | ⟨hnw, pw, hpwEq, rfl⟩
        · rw [hround]
        · rcases hpw with hwr | hrd
          · rw [hwr] at hnw; exact nomatch hnw
          · have hval : pw = m.pw :=
              Except.ok.inj (hpwEq.symm.trans (annotPwPi_of_reader hrd))
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
        rcases hcase with ⟨-, rfl⟩ | ⟨hnw, pw, hpwEq, rfl⟩
        · rw [hround]
        · rcases hpw with hwr | hrd
          · rw [hwr] at hnw; exact nomatch hnw
          · have hval : pw = m.pw :=
              Except.ok.inj (hpwEq.symm.trans (annotPwLam_of_reader hrd))
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

/-! ## Discharging the `.never` obligation

The three shapes a copy's binder codomain has.  A former's codomain is
a `Sort`; a telescope's inner node is a `∀` and reuses its neighbour's
datum (the chain read); a constructor's codomain is the container
applied to the pin and the indices, and the reader answers from the
container's STORED result sort.  All three are `rfl` or one `mkAppN`
walk — no inference, which is the point. -/

@[simp] theorem typeSortPW_sort (find? : Name → Option ConstantInfo)
    (beta : Bool) (u : Level) :
    typeSortPW find? beta (.sort u) = some .never := rfl

@[simp] theorem typeSortPW_forallE (find? : Name → Option ConstantInfo)
    (beta : Bool) (ty b : Expr) (m : BinderMeta) :
    typeSortPW find? beta (.forallE ty b m) = some m.pw := rfl

theorem Expr.getAppFn_mkAppN (f : Expr) :
    ∀ (args : List Expr), (Expr.mkAppN f args).getAppFn = f.getAppFn := by
  intro args
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => exact ih (.app f a)

theorem Expr.numArgs_mkAppN (f : Expr) :
    ∀ (args : List Expr), (Expr.mkAppN f args).numArgs = f.numArgs + args.length := by
  intro args
  induction args generalizing f with
  | nil => rfl
  | cons a as ih =>
    show (Expr.mkAppN (.app f a) as).numArgs = _
    rw [ih (.app f a)]
    show f.numArgs + 1 + as.length = _
    simp only [List.length_cons]
    omega

/-- **A constructor's codomain reads off the container's stored result
sort.**  `I` applied to `args` inhabits `Sort u` with `u` the residual
of `I`'s stored type after `args.length` never-data binders — which is
what a former's telescope has (`∀ p⃗ ı⃗, Sort u` carries `.never` at
every binder). -/
theorem typeSortPW_mkAppN_const (find? : Name → Option ConstantInfo)
    (beta : Bool) {I : Name} {us : List Level} {ci : ConstantInfo} {u : Level}
    {args : List Expr}
    (hf : find? I = some ci) (hnt : ci.isTowerEntry = false)
    (hlen : us.length = ci.toConstantVal.levelParams.length)
    (hpeel : ci.toConstantVal.type.peelNeverPis args.length = some (.sort u)) :
    typeSortPW find? beta (Expr.mkAppN (.const I us) args)
      = some (Level.substPW ci.toConstantVal.levelParams us (Level.zeronessOf u)) := by
  rw [typeSortPW, typePWAt_spine, Expr.getAppFn_mkAppN, Expr.numArgs_mkAppN]
  show typePWAt find? beta (.const I us) (0 + args.length + 0) = _
  rw [Nat.zero_add, Nat.add_zero, ← headTypePW, headTypePW_const, hf]
  simp only [hnt, Bool.false_eq_true, if_false, hlen, if_true, hpeel, residualPW,
    Option.map_some]

/-! ## The two transports of the datum obligation

`AnnotStable`'s obligation at a binder is a reading of the OPENED body.
The elimination changes that body twice — the container's parameters
become the pin's components, and the container's level parameters
become the occurrence's levels — and these are the two lemmas that move
the obligation across, with no inference on either side. -/

/-- The container's reading, at the pin: substituting a `SortAgree`
component for the opened parameter leaves the datum alone. -/
theorem typeSortPW_at_pin (find? : Name → Option ConstantInfo)
    {A v b : Expr} (idx k : Nat) {pw : PropWhen} (hsa : SortAgree find? A v)
    (h : typeSortPW find? true (b.instantiate1 (.fvar idx A) k) = some pw) :
    typeSortPW find? true (b.instantiate1 v k) = some pw :=
  (typeSortPW_instantiate1_congr find? idx hsa b k).trans h

/-- The λ twin: substituting a `ProofAgree` component for the opened
parameter leaves a λ binder's datum alone — the transport
`AnnotStable`'s λ clause needs, which K.4 did not have. -/
theorem proofPW_at_pin (find? : Name → Option ConstantInfo)
    {A v b : Expr} (idx k : Nat) {pw : PropWhen} (hp : ProofAgree find? A v)
    (h : proofPW find? true (b.instantiate1 (.fvar idx A) k) = some pw) :
    proofPW find? true (b.instantiate1 v k) = some pw :=
  (proofPW_instantiate1_congr find? idx hp b k).trans h

/-- The container's reading, at the occurrence's levels: the datum
travels by its own substitution. -/
theorem typeSortPW_at_levels (find? : Name → Option ConstantInfo)
    {ks : List Name} {vs : List Level}
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true)
    {b : Expr} {pw : PropWhen} (h : typeSortPW find? true b = some pw) :
    typeSortPW find? true (b.instantiateLevelParams ks vs)
      = some (Level.substPW ks vs pw) :=
  typeSortPW_instantiateLevelParams find? true hdef h

/-! ## The pin components' obligation, and the λ shape (task #301)

The copies read the container's stored former AT THE PIN, so the
reader's answers have to survive replacing the container's parameters by
the pin's components — `typeSortPW_at_pin` and `proofPW_at_pin` above,
whose hypotheses are `SortAgree`/`ProofAgree`.  The model lane states
the per-component premise in the ONE-DIRECTIONAL grade (`…W`): wherever
the PARAMETER's side answers, the COMPONENT's side answers the same.
That is all the transport of an obligation needs — the container's
binders are the ones that are stable — and it is where a λ component
used to fail both readers.
-/

/-- The reader at arity `n` on a term: unapplied, `typeSortPW`; applied
to `n` further arguments, `headTypePW` at the head.  This is the
arity-indexed reader itself (`readAt_eq`). -/
@[expose] def readAt (find? : Name → Option ConstantInfo) (v : Expr) :
    Nat → Option PropWhen
  | 0 => typeSortPW find? true v
  | n + 1 => headTypePW find? true v.getAppFn (v.numArgs + (n + 1))

theorem readAt_eq (find? : Name → Option ConstantInfo) (v : Expr) (n : Nat) :
    readAt find? v n = typePWAt find? true v n := by
  cases n with
  | zero => rfl
  | succ n => rw [readAt, headTypePW, ← typePWAt_spine]

/-- **Where the declared type answers, the value answers the same** (the
∀-binder reader). -/
@[expose] def SortAgreeW (find? : Name → Option ConstantInfo) (A v : Expr) : Prop :=
  ∀ (n : Nat) (pw : PropWhen), residualPW (A.peelNeverPis n) = some pw →
    readAt find? v n = some pw

/-- The same for the λ-binder reader: a variable of type `A` is a proof
exactly when `A` is a proposition. -/
@[expose] def ProofAgreeW (find? : Name → Option ConstantInfo) (A v : Expr) : Prop :=
  ∀ pw : PropWhen, typeSortPW find? true A = some pw →
    headProofPW find? true v.getAppFn = some pw

theorem SortAgree.toW {find? : Name → Option ConstantInfo} {A v : Expr}
    (h : SortAgree find? A v) : SortAgreeW find? A v := by
  intro n pw hpw
  rw [readAt_eq, h.at n]; exact hpw

theorem ProofAgree.toW {find? : Name → Option ConstantInfo} {A v : Expr}
    (h : ProofAgree find? A v) : ProofAgreeW find? A v := by
  intro pw hpw; rw [ProofAgree] at h; rw [h]; exact hpw

/-- A variable reads like itself, for both readers. -/
theorem SortAgreeW.fvar_refl (find? : Name → Option ConstantInfo) (idx : Nat)
    (A : Expr) : SortAgreeW find? A (.fvar idx A) :=
  (SortAgree.fvar_refl find? idx A).toW

theorem ProofAgreeW.fvar_refl (find? : Name → Option ConstantInfo) (idx : Nat)
    (A : Expr) : ProofAgreeW find? A (.fvar idx A) :=
  (ProofAgree.fvar_refl find? idx A).toW

/-- **The λ rule, one-directional** (task #301): no hypothesis on the
∀'s datum — where it is not `.never` the ∀ side reads `none` at every
positive arity and there is nothing to match. -/
theorem SortAgreeW.lam {find? : Name → Option ConstantInfo}
    {ty Ab ty' b : Expr} {m m' : BinderMeta} (hb : SortAgreeW find? Ab b) :
    SortAgreeW find? (.forallE ty Ab m) (.lam ty' b m') := by
  intro n pw h
  cases n with
  | zero => exact nomatch h
  | succ n =>
    simp only [Expr.peelNeverPis] at h
    split at h
    · show readAt find? (.lam ty' b m') (n + 1) = some pw
      rw [readAt_eq]
      show typePWAt find? true b n = some pw
      rw [← readAt_eq]
      exact hb n pw h
    · exact nomatch h

/-- **The λ rule for the proof reader** (task #301).  The obligation is
the DATUM's, not the reader's: the annotated component's λ datum and the
container's binder datum are both "the zero-ness of the sort of the
codomain", and at every λ-pin of the corpus the kernel lane measured
them equal (both `.never` — a type family's body is a type, and a type
is not a proof). -/
theorem ProofAgreeW.lam {find? : Name → Option ConstantInfo}
    {ty Ab ty' b : Expr} {m m' : BinderMeta} (hpw : m'.pw = m.pw) :
    ProofAgreeW find? (.forallE ty Ab m) (.lam ty' b m') :=
  (ProofAgree.lam (ty := ty) (Ab := Ab) (ty' := ty') (b := b) hpw).toW

/-- **A pin component reads like the parameter it replaces**: the shapes
that discharge the model lane's per-component premise.

* `fvar` — an OPENER: the component IS the block's parameter variable,
  declared at the parameter's domain.  Every non-dependent container's
  pin is made of these.
* `lam` — a λ against a ∀ (task #301): the body reads like the
  codomain and the λ carries the binder's datum.  This is a *dependent*
  container's family parameter, `Std.DTreeMap.Raw α (fun a => β a)`
  against `α → Type v`; the rule is closed under nesting, so a family
  of a family reads too.
* `reads` — the escape hatch: a component the two readers already agree
  on (a constant-headed one whose stored type peels to the same
  residual, say). -/
inductive CompReads (find? : Name → Option ConstantInfo) : Expr → Expr → Prop where
  | fvar {A : Expr} (idx : Nat) : CompReads find? A (.fvar idx A)
  | lam {ty Ab ty' b : Expr} {m m' : BinderMeta} :
      CompReads find? Ab b → m'.pw = m.pw →
      CompReads find? (.forallE ty Ab m) (.lam ty' b m')
  | reads {A v : Expr} : SortAgreeW find? A v → ProofAgreeW find? A v →
      CompReads find? A v

theorem CompReads.sortAgreeW {find? : Name → Option ConstantInfo} :
    ∀ {A v : Expr}, CompReads find? A v → SortAgreeW find? A v := by
  intro A v h
  induction h with
  | fvar idx => exact SortAgreeW.fvar_refl _ idx _
  | lam _ _ ihb => exact ihb.lam
  | reads hs _ => exact hs

theorem CompReads.proofAgreeW {find? : Name → Option ConstantInfo} :
    ∀ {A v : Expr}, CompReads find? A v → ProofAgreeW find? A v := by
  intro A v h
  induction h with
  | fvar idx => exact ProofAgreeW.fvar_refl _ idx _
  | lam _ hpw _ => exact ProofAgreeW.lam hpw
  | reads _ hp => exact hp

/-- **The model lane's per-pin premise, from the components' shapes.**
The conclusion is `PinCompsAgree`'s body
(`ConLeche/Model/Inductives/CopyReads.lean`): per pin, of the annotation
the pin check computes at the block's openers, every component reads
like the container's parameter domain it replaces, for both readers.
With the reader's λ clause in place (task #301) the λ components — the
nine the kernel lane measured, `Lean.Json`/`Lean.PrefixTreeNode` ×
`Std.DTreeMap.*` and five fixtures — are covered by `CompReads.lam`
instead of being a reader gap. -/
theorem pinCompsAgree_of_compReads {F : Nat} {envAux : Env} {nP : Nat}
    {fvsA : List Expr} {pins : List NestedPin}
    (h : ∀ q ∈ pins, ∀ (Jn : Name) (lvls : List Level) (Ds : List Expr),
      q.pin = Expr.mkAppN (.const Jn lvls) Ds →
      ∀ (cvTJ : ConstantVal) (capsJ : IndCaps),
        envAux.find? Jn = some (.indInfo cvTJ capsJ) →
      ∀ (argsA dsA : List Expr) (restA : Expr),
        annotateCore mode envAux F nP (Expr.instantiateList
          (Expr.abstractRange q.pin 0 nP 0) fvsA.reverse)
          = .ok (Expr.mkAppN (.const Jn lvls) argsA) →
        Expr.instPisAt argsA
            (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls) = some (dsA, restA) →
        ∀ (i : Nat) (A a : Expr), dsA[i]? = some A → argsA[i]? = some a →
          CompReads envAux.find? A a) :
    ∀ q ∈ pins, ∀ (Jn : Name) (lvls : List Level) (Ds : List Expr),
      q.pin = Expr.mkAppN (.const Jn lvls) Ds →
      ∀ (cvTJ : ConstantVal) (capsJ : IndCaps),
        envAux.find? Jn = some (.indInfo cvTJ capsJ) →
      ∀ (argsA dsA : List Expr) (restA : Expr),
        annotateCore mode envAux F nP (Expr.instantiateList
          (Expr.abstractRange q.pin 0 nP 0) fvsA.reverse)
          = .ok (Expr.mkAppN (.const Jn lvls) argsA) →
        Expr.instPisAt argsA
            (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls) = some (dsA, restA) →
        ∀ (i : Nat) (A a : Expr), dsA[i]? = some A → argsA[i]? = some a →
          SortAgreeW envAux.find? A a ∧ ProofAgreeW envAux.find? A a :=
  fun q hq Jn lvls Ds hpin cvTJ capsJ hf argsA dsA restA hann hAt i A a hA ha =>
    ⟨(h q hq Jn lvls Ds hpin cvTJ capsJ hf argsA dsA restA hann hAt i A a hA ha).sortAgreeW,
      (h q hq Jn lvls Ds hpin cvTJ capsJ hf argsA dsA restA hann hAt i A a hA ha).proofAgreeW⟩

end ConLeche
