module

public import Fragment.Rules
public import Fragment.Scope

@[expose] public section

/-!
# Declarations: what the checker accepts

The environment grows by **definitions** and by **inductive blocks**.
This file says, relationally, what the checker checks before storing
either — `DefOk` and `IndOk` — and what it stores (`Env.add`,
`IndSpec.install`).  Nothing here is semantic; the environment section
(`Install.lean`) proves that an environment built by these checks has
a model.

**Definitions** (`DefOk`; con-leche's `checkDefnVal`,
`ConLeche/Kernel/Checker.lean:36-52`): the declared type has a sort,
the value's inferred type is definitionally equal to the declared
type, the name is fresh, and both terms are closed, mention only
stored constants and use only the declared level parameters.

**Inductive blocks** (`IndOk`; con-leche's uniform installer,
`ConLeche/Kernel/Inductives/BlockTail.lean`, with its recogniser
`BlockParts.lean` and the generators of `GenRec.lean`).  A block
is given by a **specification** (`IndSpec`): a type former with level
parameters, a parameter telescope, an index telescope and a result
sort, and constructors whose fields are *ordinary* (any domain not
mentioning the block), *recursive* (the family at the block's
parameters and some index expressions) or *reflexive* (a function
space into the family — the one shape that makes an inductive type
large).  The types of the former, the constructors and the recursor,
and the recursor's rules, are **generated** from the specification
(`indType`, `ctorType`, `recType`, `ruleRhs`); the checker's checks
are then: the generated former's and constructors' types have sorts
(`Infer`) in the environment as it stands when each is added (the
recursive fields' domains mention the former), every field's sort
respects the universe bound, the elimination level is admissible, and
the generated recursor's type has a sort.  Con-leche recognises the
block's shape from the stream's records and compares the stream's
recursor with the generated one (task #175 S2, #220); the fragment
takes the shape as given and stores the generated recursor — the same
environment either way.

The de Bruijn bookkeeping is the one unavoidable cost of the
generators: an expression of the specification lives under the
parameters and the earlier fields, and reappears in a minor premise
under the motive, the earlier minors, the fields and the earlier
inductive hypotheses, and in a rule under the motive, all the minors
and the fields.  `atCtx` is the one lifting that moves it
(con-leche's `ClassGen.ihParts`, `GenRec.lean:138`, opens it at a depth).

Contexts are innermost first throughout, as in `Rules.lean`: a
telescope `[Aₙ, …, A₁]` binds `A₁` outermost, and `Aᵢ` may mention the
variables of `A₁ … Aᵢ₋₁` as `bvar 0 … bvar (i-2)`.
-/

namespace Fragment

/-! ## Telescopes over contexts -/

namespace Expr

/-- `∀ Γ, b` over a context (innermost first), every binder annotated
`pw`. -/
def mkPis (pw : PropWhen) : List Expr → Expr → Expr
  | [], b => b
  | A :: Γ, b => mkPis pw Γ (pi A pw b)

/-- `fun Γ => b` over a context, every binder annotated `pw`. -/
def mkLams (pw : PropWhen) : List Expr → Expr → Expr
  | [], b => b
  | A :: Γ, b => mkLams pw Γ (lam A pw b)

@[simp] theorem mkPis_nil (pw : PropWhen) (b : Expr) : mkPis pw [] b = b := rfl
@[simp] theorem mkPis_cons (pw : PropWhen) (A : Expr) (Γ : List Expr) (b : Expr) :
    mkPis pw (A :: Γ) b = mkPis pw Γ (pi A pw b) := rfl
@[simp] theorem mkLams_nil (pw : PropWhen) (b : Expr) : mkLams pw [] b = b := rfl
@[simp] theorem mkLams_cons (pw : PropWhen) (A : Expr) (Γ : List Expr) (b : Expr) :
    mkLams pw (A :: Γ) b = mkLams pw Γ (lam A pw b) := rfl

theorem mkPis_append (pw : PropWhen) (Γ Δ : List Expr) (b : Expr) :
    mkPis pw (Γ ++ Δ) b = mkPis pw Δ (mkPis pw Γ b) := by
  induction Γ generalizing b with
  | nil => rfl
  | cons A Γ ih => simp [ih]

theorem mkLams_append (pw : PropWhen) (Γ Δ : List Expr) (b : Expr) :
    mkLams pw (Γ ++ Δ) b = mkLams pw Δ (mkLams pw Γ b) := by
  induction Γ generalizing b with
  | nil => rfl
  | cons A Γ ih => simp [ih]

/-- The variables of the `n` binders sitting `o` binders up, as a
spine (outermost first): `bvar (o + n - 1), …, bvar o`. -/
def varsAt (o n : Nat) : List Expr := (List.range n).map fun k => bvar (o + n - 1 - k)

/-- Lift each entry of a context by a function of how many entries of
the same context sit below it (the head of an innermost-first context
sits above all the others). -/
def liftCtx (f : Nat → Expr → Expr) : List Expr → List Expr
  | [] => []
  | A :: Γ => f Γ.length A :: liftCtx f Γ

@[simp] theorem liftCtx_nil (f : Nat → Expr → Expr) : liftCtx f [] = [] := rfl
@[simp] theorem liftCtx_cons (f : Nat → Expr → Expr) (A : Expr) (Γ : List Expr) :
    liftCtx f (A :: Γ) = f Γ.length A :: liftCtx f Γ := rfl

theorem length_liftCtx (f : Nat → Expr → Expr) : ∀ Γ : List Expr, (liftCtx f Γ).length = Γ.length
  | [] => rfl
  | _ :: Γ => by simp [length_liftCtx f Γ]

/-- **The lifting into a minor premise or a rule.**  An expression of
the specification stands under the parameters and `k` earlier fields
(and `d` binders of its own, a reflexive field's telescope); in a
minor premise or a rule it stands under the parameters, `o` more
binders (the motive and some minors), all `nF` fields, `l` earlier
inductive hypotheses and its own `d`: the fields and hypotheses in
between shift the earlier fields by `nF - k + l`, the motive and
minors shift the parameters by `o` more. -/
def atCtx (nF k l o d : Nat) (e : Expr) : Expr :=
  (e.liftN (nF - k + l) d).liftN o (nF + l + d)

end Expr

namespace IndSpec

open Expr

variable (S : IndSpec)

/-- The number of parameters. -/
def nP : Nat := S.params.length
/-- The number of indices. -/
def nI : Nat := S.indices.length
/-- The number of constructors. -/
def n : Nat := S.ctors.length
/-- The block's level parameters as levels. -/
def lvls : List Level := S.lparams.map .param
/-- The annotation of every binder whose body is a member of the
family or the family itself — a proposition exactly when the result
sort is zero. -/
def pw : PropWhen := Level.zeroness S.sort
/-- The elimination level: the fresh parameter, or `Prop`. -/
def ℓ : Level := if S.large then .param S.elim else .zero
/-- The annotation of the recursor's binders: a proposition exactly
when the elimination level is zero. -/
def q : PropWhen := Level.zeroness S.ℓ
/-- The recursor's level parameters: the elimination parameter in
front of the block's, if large. -/
def recLparams : List Name := if S.large then S.elim :: S.lparams else S.lparams
/-- The recursor's level parameters as levels. -/
def recLvls : List Level := S.recLparams.map .param

/-- The family applied to the parameter variables sitting `o` binders
up and to the index expressions `es`. -/
def famAt (o : Nat) (es : List Expr) : Expr :=
  mkAppN (.const S.name S.lvls) (varsAt o S.nP ++ es)

/-- The family at the parameter variables (`e + nI` up) and the index
variables (`0` up): the type of a major premise. -/
def famVars (e : Nat) : Expr := S.famAt (e + S.nI) (varsAt 0 S.nI)

/-! ### The class of a nested block -/

/-- **The class's arguments** under `o` binders above the parameters:
the container's other arguments with the member `I params idx` at
position `p` (outermost first). -/
def classArgs (N : NestInfo) (o : Nat) : List Expr :=
  (N.args.take N.p).map (liftN o ·) ++ [S.famAt o (N.idx.map (liftN o ·))] ++
    (N.args.drop N.p).map (liftN o ·)

/-- **The class** `K.{lsK} args[member]` under `o` binders above the
parameters: the domain of a container field, the major of the
auxiliary recursor. -/
def classTy (N : NestInfo) (o : Nat) : Expr := mkAppN (.const N.K.name N.lsK) (S.classArgs N o)

/-- A field's domain, with `k` earlier fields.  (A container field's
is the class, when the block has one.) -/
def fieldDom (k : Nat) : Field → Expr
  | .ordinary A => A
  | .recursive es => S.famAt k es
  | .reflexive tele es => mkPis S.pw tele (S.famAt (k + tele.length) es)
  | .container =>
    match S.nest with
    | some N => S.classTy N k
    | none => .sort .zero

/-- A constructor's field context: the domains, innermost first (the
head has all the others as earlier fields). -/
def fieldCtx : List Field → List Expr
  | [] => []
  | f :: fs => S.fieldDom fs.length f :: fieldCtx fs

theorem length_fieldCtx : ∀ fs : List Field, (S.fieldCtx fs).length = fs.length
  | [] => rfl
  | _ :: fs => by simp only [fieldCtx, List.length_cons, length_fieldCtx fs]

/-- The field context moved under `o` binders inserted between the
parameters and the fields. -/
def fieldCtxAt (c : CtorSpec) (o : Nat) : List Expr :=
  liftCtx (fun k A => A.liftN o k) (S.fieldCtx c.fields)

/-- The index context moved under `o` binders inserted between the
parameters and the indices. -/
def indicesAt (o : Nat) : List Expr := liftCtx (fun t T => T.liftN o t) S.indices

/-! ### The generated types -/

/-- **The type former's type** `∀ params indices, Sort u`; no binder is
a proposition. -/
def indType : Expr := mkPis .never (S.indices ++ S.params) (.sort S.sort)

/-- **A constructor's type** `∀ params fields, I params idx`; every
binder is a proposition exactly when the family is. -/
def ctorType (c : CtorSpec) : Expr :=
  mkPis S.pw (S.fieldCtx c.fields ++ S.params) (S.famAt c.fields.length c.idx)

/-- The motive's type, under the parameters:
`∀ indices (t : I params indices), Sort ℓ`. -/
def motiveTy : Expr := mkPis .never (S.famVars 0 :: S.indices) (.sort S.ℓ)

/-- The fields with an inductive hypothesis, outermost first, each
with its number of earlier fields. -/
def _root_.Fragment.CtorSpec.recFields (c : CtorSpec) : List (Nat × Field) :=
  ((List.range c.fields.length).filterMap fun k =>
    match c.fields[c.fields.length - 1 - k]? with
    | some f => if f.isRec then some (k, f) else none
    | none => none)

/-- **An inductive hypothesis' type** for the field with `k` earlier
fields, `l` earlier hypotheses, `o` binders between the parameters
and the fields (the motive sits `nF + l + o - 1` binders above):
`motive es f` at a recursive field, `∀ tele, motive es (f tele)` at a
reflexive one. -/
def ihTy (nF k l o : Nat) : Field → Expr
  | .ordinary _ => .sort .zero
  | .recursive es =>
    mkAppN (.bvar (nF + l + o - 1)) (es.map (atCtx nF k l o 0) ++ [.bvar (nF - 1 - k + l)])
  | .reflexive tele es =>
    let m := tele.length
    mkPis S.q (liftCtx (fun t T => atCtx nF k l o t T) tele)
      (mkAppN (.bvar (nF + l + o - 1 + m))
        (es.map (atCtx nF k l o m) ++ [mkAppN (.bvar (nF - 1 - k + l + m)) (varsAt 0 m)]))
  | .container => mkAppN (.bvar (nF + l + o - 2)) [.bvar (nF - 1 - k + l)]

/-- The inductive hypotheses of a constructor under `o` binders
between the parameters and the fields, as a context (innermost
first). -/
def ihCtxAt (c : CtorSpec) (o : Nat) : List Expr :=
  (c.recFields.mapIdx fun l kf => S.ihTy c.fields.length kf.1 l o kf.2).reverse

/-- The inductive hypotheses of a constructor in minor premise `j`, as
a context (innermost first). -/
def ihCtx (c : CtorSpec) (j : Nat) : List Expr :=
  (c.recFields.mapIdx fun l kf => S.ihTy c.fields.length kf.1 l (j + 1) kf.2).reverse

/-- **A minor premise** for constructor `j`, under the parameters, the
motive and the `j` earlier minors:
`∀ fields ihs, motive idx (C params fields)`. -/
def minorTy (c : CtorSpec) (j : Nat) : Expr :=
  let nF := c.fields.length
  let nIh := c.recFields.length
  mkPis S.q (S.ihCtx c j ++ S.fieldCtxAt c (j + 1))
    (mkAppN (.bvar (nIh + nF + j))
      (c.idx.map (atCtx nF nF nIh (j + 1) 0) ++
        [mkAppN (.const c.name S.lvls) (varsAt (nIh + nF + j + 1) S.nP ++ varsAt nIh nF)]))

/-- The minor premises, as a context under the motive (innermost
first). -/
def minorsCtx : List Expr :=
  ((List.range S.n).map fun j => S.minorTy (S.ctors.getD j ⟨"", [], []⟩) j).reverse

/-- **The recursor's type**
`∀ params (motive : motiveTy) minors indices (t : I params indices), motive indices t`
(con-leche's `classGenRecTy`, `GenRec.lean:181`). -/
def recType : Expr :=
  mkPis S.q (S.famVars (S.n + 1) :: S.indicesAt (S.n + 1) ++ S.minorsCtx ++ [S.motiveTy] ++ S.params)
    (mkAppN (.bvar (1 + S.nI + S.n)) (varsAt 1 S.nI ++ [.bvar 0]))

/-- **An inductive hypothesis' value** in a rule, for the field with
`k` earlier fields under all `nF` fields, the `n` minors and the
motive: the recursor at the parameters, motive and minors, the
field's index expressions and the field (under the field's own
telescope at a reflexive field). -/
def ihVal (nF k : Nat) : Field → Expr
  | .ordinary _ => .sort .zero
  | .container => .sort .zero
  | .recursive es =>
    mkAppN (.const S.recName S.recLvls)
      (varsAt (nF + S.n + 1) S.nP ++ [.bvar (nF + S.n)] ++ varsAt nF S.n ++
        es.map (atCtx nF k 0 (S.n + 1) 0) ++ [.bvar (nF - 1 - k)])
  | .reflexive tele es =>
    let m := tele.length
    mkLams S.q (liftCtx (fun t T => atCtx nF k 0 (S.n + 1) t T) tele)
      (mkAppN (.const S.recName S.recLvls)
        (varsAt (m + nF + S.n + 1) S.nP ++ [.bvar (m + nF + S.n)] ++ varsAt (m + nF) S.n ++
          es.map (atCtx nF k 0 (S.n + 1) m) ++ [mkAppN (.bvar (m + nF - 1 - k)) (varsAt 0 m)]))

/-- The context of a rule: the parameters, the motive, the minors and
the constructor's fields (under the motive and all minors). -/
def ruleCtx (c : CtorSpec) : List Expr :=
  S.fieldCtxAt c (S.n + 1) ++ S.minorsCtx ++ [S.motiveTy] ++ S.params

/-- A rule's type body, under its context: `motive idx (C params fields)`
— what the minor premise concludes, without the inductive hypotheses. -/
def ruleBodyTy (c : CtorSpec) : Expr :=
  let nF := c.fields.length
  mkAppN (.bvar (nF + S.n))
    (c.idx.map (atCtx nF nF 0 (S.n + 1) 0) ++
      [mkAppN (.const c.name S.lvls) (varsAt (nF + S.n + 1) S.nP ++ varsAt 0 nF)])

/-- **A rule's type**: `∀ params motive minors fields, motive idx (C params fields)`
— the recursor's binder prefix with the constructor's fields in place
of the indices and the major (con-leche generates the rule and
type-checks it, `classRuleOk`, `GenRec.lean:427`; the stream's rules
are never read; the fragment infers the rule's type likewise). -/
def ruleType (c : CtorSpec) : Expr := mkPis S.q (S.ruleCtx c) (S.ruleBodyTy c)

/-- **A rule's right-hand side** for constructor `j`:
`fun params motive minors fields => minor_j fields ihs`
(con-leche's `classGenRule`, `GenRec.lean:193`). -/
def ruleRhs (c : CtorSpec) (j : Nat) : Expr :=
  let nF := c.fields.length
  mkLams S.q (S.ruleCtx c)
    (mkAppN (.bvar (nF + S.n - 1 - j))
      (varsAt 0 nF ++ c.recFields.map fun kf => S.ihVal nF kf.1 kf.2))

/-- The recursor's rules, one per constructor. -/
def rules : List RecRule :=
  (List.range S.n).map fun j =>
    let c := S.ctors.getD j ⟨"", [], []⟩
    ⟨c.name, c.fields.length, S.ruleRhs c j, none⟩

/-! ### The nested block's recursors

A block with a class has two recursors with one telescope prefix —
the parameters, the motive for the block, the motive for the class,
the minor premises for the block's constructors and the minor
premises for the container's constructors *at the instantiation* —
differing in the major: the block's family at its indices for `T.rec`,
the class for `T.rec_1` (con-leche's `classGenRecTy`, `GenRec.lean`).
The container's constructors are read in the block's own terms
(`classCtor`): the member field becomes a recursive field of the block
at the member's index expressions, a recursive field of the container
becomes a container field, an ordinary field has the container's
parameters replaced by the class's arguments. -/

/-- The container's field with `k` earlier fields, in the block's
terms. -/
def classField (N : NestInfo) (k : Nat) : Field → Field
  | .ordinary A =>
    if N.isMember k (.ordinary A) then .recursive (N.idx.map (liftN k ·))
    else .ordinary (instChainAt (A.instL N.K.lparams N.lsK) (S.classArgs N 0) k)
  | .recursive _ => .container
  | f => f

/-- The container's fields (innermost first), in the block's terms. -/
def classFields (N : NestInfo) : List Field → List Field
  | [] => []
  | f :: rest => S.classField N rest.length f :: classFields N rest

@[simp] theorem classFields_nil (N : NestInfo) : S.classFields N [] = [] := rfl
@[simp] theorem classFields_cons (N : NestInfo) (f : Field) (rest : List Field) :
    S.classFields N (f :: rest) = S.classField N rest.length f :: S.classFields N rest := rfl

theorem length_classFields (N : NestInfo) : ∀ fs : List Field, (S.classFields N fs).length = fs.length
  | [] => rfl
  | _ :: rest => by simp [length_classFields N rest]

theorem classFields_getElem? (N : NestInfo) : ∀ (fs : List Field) (i : Nat),
    (S.classFields N fs)[i]? = (fs[i]?).map fun f => S.classField N (fs.length - 1 - i) f
  | [], _ => rfl
  | f :: fs, 0 => by simp
  | f :: fs, i + 1 => by
    have : (f :: fs).length - 1 - (i + 1) = fs.length - 1 - i := by simp; omega
    rw [this]
    simp only [classFields_cons, List.getElem?_cons_succ]
    exact classFields_getElem? N fs i

/-- A constructor of the container, in the block's terms: its fields
translated, no indices. -/
def classCtor (N : NestInfo) (c : CtorSpec) : CtorSpec := ⟨c.name, S.classFields N c.fields, []⟩

/-- The extras of the nested recursors' prefix: two motives and all
minor premises. -/
def oN (N : NestInfo) : Nat := 2 + S.n + N.nK

/-- **The class's motive's type**, under the parameters and the
block's motive: `∀ (t : K args[member]), Sort ℓ`. -/
def motiveTy1 (N : NestInfo) : Expr := mkPis .never [S.classTy N 1] (.sort S.ℓ)

/-- **A minor premise of the block's constructor `j`** in a nested
block: as `minorTy`, under the two motives and the `j` earlier minors. -/
def minorTyN (c : CtorSpec) (j : Nat) : Expr :=
  let nF := c.fields.length
  let nIh := c.recFields.length
  let o := 2 + j
  mkPis S.q (S.ihCtxAt c o ++ S.fieldCtxAt c o)
    (mkAppN (.bvar (nIh + nF + o - 1))
      (c.idx.map (atCtx nF nF nIh o 0) ++
        [mkAppN (.const c.name S.lvls) (varsAt (nIh + nF + o) S.nP ++ varsAt nIh nF)]))

/-- **A minor premise of the container's constructor `j`** at the
instantiation: under the two motives, the block's minors and the `j`
earlier class minors, `∀ fields ihs, motive_1 (C.{lsK} args[member] fields)`
— the fields the translated ones, a member field's hypothesis the
block's motive at the member, a container field's the class's. -/
def minorTyK (N : NestInfo) (c : CtorSpec) (j : Nat) : Expr :=
  let c' := S.classCtor N c
  let nF := c'.fields.length
  let nIh := c'.recFields.length
  let o := 2 + S.n + j
  mkPis S.q (S.ihCtxAt c' o ++ S.fieldCtxAt c' o)
    (mkAppN (.bvar (nIh + nF + o - 2))
      [mkAppN (.const c.name N.lsK) (S.classArgs N (nIh + nF + o) ++ varsAt nIh nF)])

/-- The block's minors in a nested block, as a context (innermost
first). -/
def minorsCtxN : List Expr :=
  ((List.range S.n).map fun j => S.minorTyN (S.ctors.getD j ⟨"", [], []⟩) j).reverse

/-- The class's minors, as a context (innermost first). -/
def minorsCtxK (N : NestInfo) : List Expr :=
  ((List.range (N.nK)).map fun j => S.minorTyK N (N.K.ctors.getD j ⟨"", [], []⟩) j).reverse

/-- The extras of the nested recursors' prefix, as a context: the
class's minors, the block's minors, the class's motive, the block's
motive (innermost first). -/
def extrasN (N : NestInfo) : List Expr :=
  S.minorsCtxK N ++ S.minorsCtxN ++ [S.motiveTy1 N, S.motiveTy]

/-- The context of `T.rec`: the major at the family, the indices, the
extras, the parameters. -/
def recCtxN (N : NestInfo) : List Expr :=
  S.famVars (S.oN N) :: S.indicesAt (S.oN N) ++ S.extrasN N ++ S.params

/-- **`T.rec`'s type** in a nested block:
`∀ params motive motive_1 minors minors_1 indices (t : I params indices), motive indices t`. -/
def recTypeN (N : NestInfo) : Expr :=
  mkPis S.q (S.recCtxN N) (mkAppN (.bvar (S.nI + S.oN N)) (varsAt 1 S.nI ++ [.bvar 0]))

/-- The context of `T.rec_1`: the major at the class, the extras, the
parameters. -/
def rec1Ctx (N : NestInfo) : List Expr := S.classTy N (S.oN N) :: S.extrasN N ++ S.params

/-- **`T.rec_1`'s type**: the same prefix, the major at the class,
the class's motive at it. -/
def rec1Type (N : NestInfo) : Expr :=
  mkPis S.q (S.rec1Ctx N) (mkAppN (.bvar (S.oN N - 1)) [.bvar 0])

/-- **An inductive hypothesis' value** in a rule of a nested block:
`T.rec` at the field for a recursive field, `T.rec_1` at the field
for a container field — each at the parameters and all the extras. -/
def ihValN (N : NestInfo) (nF k : Nat) : Field → Expr
  | .ordinary _ => .sort .zero
  | .recursive es =>
    mkAppN (.const S.recName S.recLvls)
      (varsAt (nF + S.oN N) S.nP ++ varsAt nF (S.oN N) ++
        es.map (atCtx nF k 0 (S.oN N) 0) ++ [.bvar (nF - 1 - k)])
  | .reflexive tele es =>
    let m := tele.length
    mkLams S.q (liftCtx (fun t T => atCtx nF k 0 (S.oN N) t T) tele)
      (mkAppN (.const S.recName S.recLvls)
        (varsAt (m + nF + S.oN N) S.nP ++ varsAt (m + nF) (S.oN N) ++
          es.map (atCtx nF k 0 (S.oN N) m) ++ [mkAppN (.bvar (m + nF - 1 - k)) (varsAt 0 m)]))
  | .container =>
    mkAppN (.const N.aux S.recLvls)
      (varsAt (nF + S.oN N) S.nP ++ varsAt nF (S.oN N) ++ [.bvar (nF - 1 - k)])

/-- The context of a rule of a nested block: the parameters, the
extras and the constructor's fields (the block's or the translated
container's). -/
def ruleCtxN (N : NestInfo) (c : CtorSpec) : List Expr :=
  S.fieldCtxAt c (S.oN N) ++ S.extrasN N ++ S.params

/-- A `T.rec` rule's type body: `motive idx (C params fields)`. -/
def ruleBodyTyN (N : NestInfo) (c : CtorSpec) : Expr :=
  let nF := c.fields.length
  mkAppN (.bvar (nF + S.oN N - 1))
    (c.idx.map (atCtx nF nF 0 (S.oN N) 0) ++
      [mkAppN (.const c.name S.lvls) (varsAt (nF + S.oN N) S.nP ++ varsAt 0 nF)])

/-- A `T.rec` rule's type. -/
def ruleTypeN (N : NestInfo) (c : CtorSpec) : Expr := mkPis S.q (S.ruleCtxN N c) (S.ruleBodyTyN N c)

/-- A `T.rec_1` rule's type body: `motive_1 (C.{lsK} args[member] fields)`. -/
def rule1BodyTy (N : NestInfo) (c : CtorSpec) : Expr :=
  let nF := (S.classCtor N c).fields.length
  mkAppN (.bvar (nF + S.oN N - 2))
    [mkAppN (.const c.name N.lsK) (S.classArgs N (nF + S.oN N) ++ varsAt 0 nF)]

/-- A `T.rec_1` rule's type. -/
def rule1Type (N : NestInfo) (c : CtorSpec) : Expr :=
  mkPis S.q (S.ruleCtxN N (S.classCtor N c)) (S.rule1BodyTy N c)

/-- **A `T.rec` rule's right-hand side** for the block's constructor
`j`: `fun params motives minors fields => minor_j fields ihs`. -/
def ruleRhsN (N : NestInfo) (c : CtorSpec) (j : Nat) : Expr :=
  let nF := c.fields.length
  mkLams S.q (S.ruleCtxN N c)
    (mkAppN (.bvar (nF + N.nK + S.n - 1 - j))
      (varsAt 0 nF ++ c.recFields.map fun kf => S.ihValN N nF kf.1 kf.2))

/-- **A `T.rec_1` rule's right-hand side** for the container's
constructor `j`: `fun params motives minors fields => minor_1_j fields ihs`. -/
def rule1Rhs (N : NestInfo) (c : CtorSpec) (j : Nat) : Expr :=
  let c' := S.classCtor N c
  let nF := c'.fields.length
  mkLams S.q (S.ruleCtxN N c')
    (mkAppN (.bvar (nF + N.nK - 1 - j))
      (varsAt 0 nF ++ c'.recFields.map fun kf => S.ihValN N nF kf.1 kf.2))

/-- `T.rec`'s rules, one per constructor of the block. -/
def rulesN (N : NestInfo) : List RecRule :=
  (List.range S.n).map fun j =>
    let c := S.ctors.getD j ⟨"", [], []⟩
    ⟨c.name, c.fields.length, S.ruleRhsN N c j, none⟩

/-- `T.rec_1`'s rules, one per constructor of the container, each
with its stored instantiation: the container's levels and the class's
arguments. -/
def rules1 (N : NestInfo) : List RecRule :=
  (List.range (N.nK)).map fun j =>
    let c := N.K.ctors.getD j ⟨"", [], []⟩
    ⟨c.name, c.fields.length, S.rule1Rhs N c j, some (N.lsK, S.classArgs N 0)⟩

/-! ### What is stored -/

/-- The type former's constant. -/
def indInfo : ConstInfo := ⟨S.lparams, S.indType, .induct S.nP S.nI (S.ctors.map (·.name)) S⟩

/-- A constructor's constant. -/
def ctorInfo (c : CtorSpec) : ConstInfo :=
  ⟨S.lparams, S.ctorType c, .ctor S.name S.nP c.fields.length⟩

/-- The recursor's constant: `nP` parameters, one motive, `n` minors,
`nI` indices, the generated rules. -/
def recInfo : ConstInfo := ⟨S.recLparams, S.recType, .recursor S.nP 1 S.n S.nI S.rules⟩

/-- The environment with the type former added. -/
def envInd (env : Env) : Env := env.add S.name S.indInfo

/-- The environment with the type former and the constructors added,
in order. -/
def envCtors (env : Env) : Env :=
  S.ctors.foldl (fun e c => e.add c.name (S.ctorInfo c)) (S.envInd env)

/-- `T.rec`'s constant in a nested block: `nP` parameters, two
motives, `n + nK` minors, `nI` indices. -/
def recInfoN (N : NestInfo) : ConstInfo :=
  ⟨S.recLparams, S.recTypeN N, .recursor S.nP 2 (S.n + N.nK) S.nI (S.rulesN N)⟩

/-- `T.rec_1`'s constant: the same prefix, no indices. -/
def rec1Info (N : NestInfo) : ConstInfo :=
  ⟨S.recLparams, S.rec1Type N, .recursor S.nP 2 (S.n + N.nK) 0 (S.rules1 N)⟩

/-- **The installed nested block**: former, constructors, the two
recursors. -/
def installN (N : NestInfo) (env : Env) : Env :=
  ((S.envCtors env).add S.recName (S.recInfoN N)).add N.aux (S.rec1Info N)

/-- **The installed block**: former, constructors, recursor — and the
auxiliary recursor for a nested block. -/
def install (env : Env) : Env :=
  match S.nest with
  | none => (S.envCtors env).add S.recName S.recInfo
  | some N => S.installN N env

end IndSpec

/-! ## Scope -/

namespace Expr

/-- **A term in scope** of an environment and level parameters, under
`k` binders: closed at `k`, every constant stored, every level
parameter declared. -/
def Scoped (env : Env) (ps : List Name) (k : Nat) (e : Expr) : Prop :=
  e.closedAt k = true ∧ (∀ c ∈ e.consts, (env.find? c).isSome) ∧ e.lparamsIn ps = true

end Expr

/-! ## The checks -/

variable [LevelOracle]

/-- **A definition is accepted** (con-leche's `checkDefnVal`): the
name is fresh, the declared type's type reduces to a sort, the
value's inferred type is definitionally equal to the declared type,
and both terms are in scope (closed, stored constants, declared level
parameters). -/
def DefOk (env : Env) (c : Name) (ci : ConstInfo) : Prop :=
  env.find? c = none ∧
  (∃ s u, Infer env [] ci.type s ∧ Red env [] s (.sort u)) ∧
  (∃ v T, ci.kind = .defn v ∧ Infer env [] v T ∧ DefEq env [] T ci.type ∧
    Expr.Scoped env ci.lparams 0 v) ∧
  Expr.Scoped env ci.lparams 0 ci.type

namespace IndSpec

variable (S : IndSpec)

/-- The scope of a field's pieces: with `k` earlier fields, an
ordinary domain is in scope under the parameters and them; a recursive
field's index expressions too; a reflexive field's telescope entries
under the earlier telescope entries as well, and its index
expressions under the whole telescope; a recursive or reflexive
field's index expressions are as many as the indices.  No piece
mentions the block (it is not stored in `env`): that is **strict
positivity** in the shape the fragment admits (con-leche's
`nestPos`, `ConLeche/Kernel/Inductives/Positivity.lean:1453`). -/
def fieldScoped (env : Env) (k : Nat) : Field → Prop
  | .ordinary A => Expr.Scoped env S.lparams (S.nP + k) A
  | .recursive es => es.length = S.nI ∧ ∀ e ∈ es, Expr.Scoped env S.lparams (S.nP + k) e
  | .reflexive tele es =>
    (∀ t T, tele[t]? = some T → Expr.Scoped env S.lparams (S.nP + k + (tele.length - 1 - t)) T) ∧
    es.length = S.nI ∧ (∀ e ∈ es, Expr.Scoped env S.lparams (S.nP + k + tele.length) e)
  | .container => S.nest.isSome = true

/-- **No field reads an earlier recursive field**: an ordinary domain,
a reflexive field's telescope entries and its index expressions, and
a recursive field's index expressions do not use the variable of any
earlier recursive or reflexive field (con-leche's `structUsedLater`
guard, `StructParts.lean:393`, run by `nestCtors`, `Positivity.lean:1247`:
the model reads the domains at a frame with arbitrary recursive slots). -/
def fieldNoRecDep (earlier : List Field) : Field → Prop
  | .ordinary A => ∀ i f, earlier[i]? = some f → f.isRec = true → A.usesVar i = false
  | .recursive es => ∀ i f, earlier[i]? = some f → f.isRec = true →
      ∀ e ∈ es, e.usesVar i = false
  | .reflexive tele es =>
    (∀ i f, earlier[i]? = some f → f.isRec = true →
      (∀ (t : Nat) (T : Expr), tele[t]? = some T → T.usesVar (tele.length - 1 - t + i) = false) ∧
      ∀ e ∈ es, e.usesVar (tele.length + i) = false)
  | .container => True

/-- **The class is in scope**: when the block has one, the container
is stored, with as many levels as it has parameters; the class's
arguments and the member's index expressions are closed under the
block's parameters, mention stored constants and use the block's level
parameters (so the class reads alike wherever the block's parameters
do); the member fills the one missing parameter position; the container
is positive in it (`NestInfo.Positive`) and is not the block itself;
the container's constructors' fields are in the container's scope and
its constructors are stored (both as checked when the container was
installed: the translated constructors and the rules of `T.rec_1` are
read against them). -/
def NestScoped (env : Env) : Prop :=
  ∀ N, S.nest = some N →
    (env.find? N.K.name).isSome ∧ N.K.name ≠ S.name ∧
    N.lsK.length = N.K.lparams.length ∧ (∀ l ∈ N.lsK, l.paramsIn S.lparams = true) ∧
    N.args.length + 1 = N.nPK ∧ N.idx.length = S.nI ∧
    (∀ e ∈ N.args, Expr.Scoped env S.lparams S.nP e) ∧
    (∀ e ∈ N.idx, Expr.Scoped env S.lparams S.nP e) ∧
    N.Positive ∧
    (∀ c ∈ N.K.ctors, ∀ i f, c.fields[i]? = some f →
      N.KS.fieldScoped env (c.fields.length - 1 - i) f) ∧
    (∀ c ∈ N.K.ctors, (env.find? c.name).isSome)

/-- **The specification is in scope** of the environment: every
expression of it is closed at its depth, mentions only stored
constants (so never the block itself) and uses only the block's level
parameters; the elimination parameter is not one of them, and they
are distinct. -/
def Scoped (env : Env) : Prop :=
  (∀ i A, S.params[i]? = some A → Expr.Scoped env S.lparams (S.nP - 1 - i) A) ∧
  (∀ t T, S.indices[t]? = some T → Expr.Scoped env S.lparams (S.nP + (S.nI - 1 - t)) T) ∧
  S.sort.paramsIn S.lparams = true ∧
  (∀ c ∈ S.ctors,
    (∀ i f, c.fields[i]? = some f → S.fieldScoped env (c.fields.length - 1 - i) f) ∧
    (∀ i f, c.fields[i]? = some f → fieldNoRecDep (c.fields.drop (i + 1)) f) ∧
    c.idx.length = S.nI ∧
    (∀ e ∈ c.idx, Expr.Scoped env S.lparams (S.nP + c.fields.length) e)) ∧
  (S.large = true → S.elim ∉ S.lparams) ∧
  S.lparams.Nodup ∧
  S.NestScoped env

/-- The universe bound on a field of sort `v`: the family is a
proposition, or `v ≤ u` (official's "universe level of `type_of(arg)`
is too big" check, `checkStructFieldSortsI`,
`ConLeche/Kernel/Inductives/SumInstall.lean:124`). -/
def FieldBound (v : Level) : Prop :=
  LevelOracle.eq S.sort .zero = true ∨ LevelOracle.le v S.sort = true

/-- "The result sort is never `Prop`": `1 ≤ u` at every valuation
(con-leche's `Level.isNeverZero`). -/
def NeverProp : Prop := LevelOracle.le (.succ .zero) S.sort = true

/-- **The subsingleton criterion** for a field of sort `v` at
position `i` (innermost first) of a constructor with index
expressions `idx`: the field is a proposition, or it is one of the
result's indices (official's `elim_only_at_universe_zero` at one
constructor; con-leche's `checkStructFieldSortsI`).  Required only of a
large eliminator on a block whose sort may be `Prop`. -/
def SubsingletonField (v : Level) (i : Nat) (idx : List Expr) : Prop :=
  S.large = true → ¬ S.NeverProp → (LevelOracle.eq v .zero = true ∨ Expr.bvar i ∈ idx)

/-- **The block is accepted** (con-leche's `checkBlock`,
`ConLeche/Kernel/Inductives/BlockTail.lean:143`):

* the block's names are distinct and fresh;
* the specification is in scope (closed, stored constants, declared
  level parameters — positivity included);
* the generated type former's type has a sort in the current
  environment;
* each generated constructor's type has a sort in the environment
  holding the former, every field's domain has a sort respecting the
  universe bound and, where a large eliminator asks it, the
  subsingleton criterion, and so does every binder of a reflexive
  field's telescope (the domain's sort implies it; the fragment lists
  it, as the checker infers it);
* each rule's type (`ruleType`, the recursor's binder prefix with the
  constructor's fields in place of the indices and the major) has a
  sort in the environment holding the former and the constructors;
* a large eliminator on a block whose sort may be `Prop` has at most
  one constructor (official's `elim_only_at_universe_zero`);
* the generated recursor's type has a sort in the environment holding
  the former and the constructors.

The recursor's rules are generated and stored, not checked: they
mention the recursor.  Con-leche does type its generated rules, in
the environment holding the recursors without their rules
(`classRuleOk`, `GenRec.lean:427`); the fragment stores them as is. -/
def Ok (env : Env) : Prop :=
  (S.name :: S.recName :: S.ctors.map (·.name)).Nodup ∧
  (∀ m ∈ S.name :: S.recName :: S.ctors.map (·.name), env.find? m = none) ∧
  S.Scoped env ∧
  (∃ T, Infer env [] S.indType T) ∧
  (∀ c ∈ S.ctors,
    (∃ T, Infer (S.envInd env) [] (S.ctorType c) T) ∧
    (∀ i A, (S.fieldCtx c.fields)[i]? = some A →
      ∃ s v, Infer (S.envInd env) ((S.fieldCtx c.fields).drop (i + 1) ++ S.params) A s ∧
        Red (S.envInd env) ((S.fieldCtx c.fields).drop (i + 1) ++ S.params) s (.sort v) ∧
        S.FieldBound v ∧ S.SubsingletonField v i c.idx) ∧
    (∀ i tele es, c.fields[i]? = some (.reflexive tele es) → ∀ t T, tele[t]? = some T →
      ∃ s w, Infer (S.envInd env)
          (tele.drop (t + 1) ++ (S.fieldCtx c.fields).drop (i + 1) ++ S.params) T s ∧
        Red (S.envInd env) (tele.drop (t + 1) ++ (S.fieldCtx c.fields).drop (i + 1) ++ S.params)
          s (.sort w) ∧
        S.FieldBound w) ∧
    (∃ T, Infer (S.envCtors env) [] (S.ruleType c) T)) ∧
  (S.large = true → ¬ S.NeverProp → S.ctors.length ≤ 1) ∧
  (∃ T, Infer (S.envCtors env) [] S.recType T)

/-- **A nested block is accepted** (con-leche's `checkBlock` with
the positivity walk through the container and the generated recursors
of every class, `Positivity.lean`, `GenRec.lean`): as `Ok` for the
former and the constructors, and then

* the container is stored with its specification, which is plain
  (depth one) and positive in the member's position;
* the container's sort at the instantiation is the block's sort
  (official's N3), and so is the member parameter's domain sort —
  the member, a fibre of the block, is a member of that domain;
* the class, at the block's parameters, has a sort in the environment
  holding the former: its arguments fit the container's parameters;
* **large elimination is refused unless the sort is never `Prop`**
  (`blockLargeElimAllowed`, `BlockRec.lean:82`): the subsingleton
  criterion is never consulted for a nested block;
* the two recursors' types and every rule's type have sorts in the
  environment holding the former and the constructors. -/
def OkN (N : NestInfo) (env : Env) : Prop :=
  S.nest = some N ∧
  (S.name :: S.recName :: N.aux :: S.ctors.map (·.name)).Nodup ∧
  (∀ m ∈ S.name :: S.recName :: N.aux :: S.ctors.map (·.name), env.find? m = none) ∧
  S.Scoped env ∧
  (∃ T, Infer env [] S.indType T) ∧
  (∀ c ∈ S.ctors,
    (∃ T, Infer (S.envInd env) [] (S.ctorType c) T) ∧
    (∀ i A, (S.fieldCtx c.fields)[i]? = some A →
      ∃ s v, Infer (S.envInd env) ((S.fieldCtx c.fields).drop (i + 1) ++ S.params) A s ∧
        Red (S.envInd env) ((S.fieldCtx c.fields).drop (i + 1) ++ S.params) s (.sort v) ∧
        S.FieldBound v) ∧
    (∀ i tele es, c.fields[i]? = some (.reflexive tele es) → ∀ t T, tele[t]? = some T →
      ∃ s w, Infer (S.envInd env)
          (tele.drop (t + 1) ++ (S.fieldCtx c.fields).drop (i + 1) ++ S.params) T s ∧
        Red (S.envInd env) (tele.drop (t + 1) ++ (S.fieldCtx c.fields).drop (i + 1) ++ S.params)
          s (.sort w) ∧
        S.FieldBound w) ∧
    (∃ T, Infer (S.envCtors env) [] (S.ruleTypeN N c) T)) ∧
  (∃ ci, env.find? N.K.name = some ci ∧ ci.kind = .induct N.nPK 0 (N.K.ctors.map (·.name)) N.K.spec) ∧
  LevelOracle.eq (N.K.sort.subst N.K.lparams N.lsK) S.sort = true ∧
  LevelOracle.eq (N.memberLevel.subst N.K.lparams N.lsK) S.sort = true ∧
  (∃ T, Infer (S.envInd env) S.params (S.classTy N 0) T) ∧
  (S.large = true → S.NeverProp) ∧
  (∀ c ∈ N.K.ctors, ∃ T, Infer (S.envCtors env) [] (S.rule1Type N c) T) ∧
  (∃ T, Infer (S.envCtors env) [] (S.recTypeN N) T) ∧
  (∃ T, Infer (S.envCtors env) [] (S.rec1Type N) T)

end IndSpec

/-- `IndOk env S`: the block `S` is accepted on top of `env` — by the
plain checks, or the nested ones when it has a class. -/
def IndOk (env : Env) (S : IndSpec) : Prop :=
  match S.nest with
  | none => S.Ok env
  | some N => S.OkN N env

end Fragment
