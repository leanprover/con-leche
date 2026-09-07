import ConLeche.Kernel.Core

/-!
# The direct install's generators (families, spines, rule bodies)

The syntactic generators every direct install reads and compares
against the stream — the type-former family, constructor spines, rule
bodies, the Π-to-λ rewrites — and `DirectParts`, the shape the
in-process modeller reads (`Frontend/InModel/Kit.lean`).  Written for
the simple-structure route (a non-recursive, single-constructor,
index-free inductive installed from the reference checks alone),
deleted at task #210 Part C; the fixpoint route is the one consumer.

This module holds the **pure** recognition layer.  It is a conservative
filter: a block that does not match falls through to the modeled path
unchanged, so a `false` here never costs a verdict.

The checks mirror what the reference kernels do when *adding* an
inductive declaration, restricted to this class (line numbers:
lean4lean `Lean4Lean/Inductive/Add.lean`, a line-by-line port of the
official `src/kernel/inductive/inductive.cpp`; nanoda
`checker/src/inductive.rs`):

* the type former's type is a `∀`-telescope of exactly `numParams`
  binders ending in a `Sort` — `checkInductiveTypes` (`Add.lean:60-116`,
  nanoda `check_inductive_spec_0th`, `inductive.rs:375`); *index-free* means the
  telescope ends there.
* the result level may be anything (task #175 W4c/O4, the user's
  ruling that every supported `.proj` is served directly): a provably
  `Prop` result (`isProp`) selects the squash-regime install — the
  official kernel's `Prop` escape hatch on the field-universe bound
  (`Add.lean:225`), projection entries only for the `Prop`-prefix of
  the fields (a data field of a `Prop` structure is not projectable,
  `infer_proj`'s restriction), K for the fieldless case.
* the constructor's type is a `∀`-telescope whose first `numParams`
  binder domains are the type former's, ending in the type former
  applied to **exactly** those parameters at the declaration's own
  level parameters — `checkConstructors` (`Add.lean:218-223`) and
  `isValidIndAppIdx` (`Add.lean:157-165`, nanoda `is_valid_ind_app`, `inductive.rs:711`).
* no recursive occurrence: every binder domain of the constructor
  resolves already in the *pre-block* environment, which subsumes
  `checkPositivity`/`hasIndOcc` (`Add.lean:184-199`) for this class and
  is exactly what the model construction needs (the type former's value
  is defined from the field types' interpretations in the old
  environment).
* the recursor's type is **exactly** the generated shape
  (`Add.lean:477-483`): params → one motive → one minor → no indices →
  major → `motive t`, with the motive dependent
  (`∀ (t : T p⃗), Sort ℓ`, `Add.lean:326`), the minor the constructor's
  field telescope ending in `motive (C p⃗ f⃗)` (`Add.lean:384-388`), and
  either a fresh elimination level parameter in front
  (`getRecLevelParams`, `Add.lean:416-417`) — the large eliminator
  (`isLargeEliminator`, `Add.lean:257-259`) — or, for a propositional
  structure with a non-`Prop` field, the small eliminator (motive into
  `Prop`, the block's own level parameters).  Both shapes are
  recognised (`DirectParts.large`).
* the single rule's right-hand side is
  `λ p⃗ motive minor f⃗, minor f⃗` (`mkRecRules`, `Add.lean:441-447`).

The per-field universe bound (`Add.lean:225-228`,
nanoda `check_ctor`, `inductive.rs:809`) needs inference, and the
recursor is **generated** here (`directRecTy`/`directRecRhs`, task
#175 S2) and compared against the stream's by one closed `isDefEq`;
both live in the monadic `checkDirectStruct`
(`ConLeche/Kernel/Direct/Install.lean`).

The direct path installs **native tower-backed projection entries**
(`checkDirectProj`, task #175 wiring): `.proj T i` nodes are typed by
the entry's stored type and reduced by the structural rule, and the
model reads them by the uniform tower projection.  The capability
record (`directCaps`) claims structure eta (the tower's own law),
unit-likeness for the fieldless case, and K for the fieldless
propositional case.
-/

namespace ConLeche

/-- The type former applied to its parameter variables, `bvar` indices
offset by `o` (the number of binders crossed since the parameters). -/
def directFam (T : Name) (lps : List Name) (nP o : Nat) : Expr :=
  Expr.mkAppN (.const T (lps.map .param))
    ((List.range nP).map fun k => Expr.bvar (o + nP - 1 - k))

/-- The constructor applied to the parameter and field variables, as
spelled inside the recursor's minor premise (parameters sit above the
motive binder). -/
def directCtorSpine (C : Name) (lps : List Name) (nP nF : Nat) : Expr :=
  Expr.mkAppN (.const C (lps.map .param))
    (((List.range nP).map fun i => Expr.bvar (nF + nP - i)) ++
     (List.range nF).map fun j => Expr.bvar (nF - 1 - j))

/-- The recursor rule's right-hand side body: the minor premise applied
to the field variables. -/
def directRuleBody (nF : Nat) : Expr :=
  Expr.mkAppN (.bvar nF) ((List.range nF).map fun j => Expr.bvar (nF - 1 - j))

/-! ## The generated recursor (task #175 S2: fabricate-and-compare)

The reference kernels *generate* the recursor from the block
(lean4lean `Inductive/Add.lean:326-483`, official
`inductive.cpp`'s `mk_rec_infos`) and store what they generated.  So
does the direct route: the recursor type and its rule are built here,
syntactically, from the **annotated** type former and constructor
types, and the stream's recursor is compared against the generated
type by one closed `isDefEq` (`checkDirectRec`).  What is stored is
the generated form — which is what makes its reading syntactic in the
model (`ConLeche/SetP/Direct/DirectRecReadP.lean`): no pin at an opened
frame is consumed anywhere.

The generators are written over a **list** of constructors (one minor
premise and one rule per constructor) though the recogniser admits
one: the multi-constructor extension changes the recogniser and the
proofs, not the generated shapes.

**Binder infos** are the export's: the former's parameter binders keep
theirs, every generated binder is `.default` (the standard-axiom pins,
`stdAxiomOk`, compare the stored `Iff.rec`/`Nonempty.rec` against the
exported shapes up to names and data but not infos).

**Binder data.**  Every binder the generator introduces or re-emits at
the recursor's own telescope carries the elimination datum
`Level.zeronessOf ℓ`: the codomain of each is `motive t : Sort ℓ`
(through `imax`'s right-argument rule), so this is exactly what the
verified-mode inference validates (`(forall-cod)`, `(lam-cod-*)`) and
what the stream's annotated recursor carries at the same binders (the
defeq sites compare data by `==`; the datum is canonical).  The motive's own
binder `(t : T p⃗)` has codomain `Sort ℓ : Sort (ℓ+1)`, hence `.never`.
The domains are re-emitted verbatim, their inner data untouched. -/

/-- The parameter variables as seen from under `o` extra binders:
`p_k = bvar (o + nP - 1 - k)` — `directFam`'s argument spine. -/
def directPsAt (o nP : Nat) : List Expr :=
  (List.range nP).map fun k => Expr.bvar (o + nP - 1 - k)

/-- The recursor's elimination level: the fresh parameter at the large
eliminator, `zero` at the small one. -/
def directElimLevel (elim : Name) (large : Bool) : Level :=
  if large then .param elim else .zero

/-- The constructor applied to the parameter and field variables, as
spelled under `o` binders between the parameters and the fields (the
motive and the earlier minor premises); `directCtorSpine` is the
`o = 1` case (`directCtorSpine_eq_at`). -/
def directCtorSpineAt (C : Name) (lps : List Name) (o nP nF : Nat) : Expr :=
  Expr.mkAppN (.const C (lps.map .param))
    (directPsAt (o + nF) nP ++ (List.range nF).map fun j => Expr.bvar (nF - 1 - j))

/-- Replace the body under the first `k` `∀`-binders, resetting their
codomain data to `pw` (the domains are kept). -/
def Expr.replacePisPw (pw : PropWhen) : Nat → Expr → Expr → Option Expr
  | 0, _, b => some b
  | k + 1, .forallE ty rest _, b =>
    (replacePisPw pw k rest b).map fun r => .forallE ty r ⟨pw⟩
  | _ + 1, _, _ => none

/-- Convert the first `k` `∀`-binders into `λ`-binders with datum `pw`
over a body (`pisToLams` with the datum supplied instead of the
`.never` placeholder). -/
def Expr.pisToLamsPw (pw : PropWhen) : Nat → Expr → Expr → Option Expr
  | 0, _, b => some b
  | k + 1, .forallE ty rest _, b =>
    (pisToLamsPw pw k rest b).map fun r => .lam ty r ⟨pw⟩
  | _ + 1, _, _ => none

/-! ## The generated recursor at an indexed family (task #175 indexed)

A non-recursive family `T : ∀ p⃗ ı⃗, Sort w` with constructors
`C_k : ∀ p⃗ f⃗, T p⃗ e⃗_k` (the index expressions `e⃗_k` arbitrary terms
over the parameters and the fields) has the recursor

    ∀ p⃗ {motive : ∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ}
      (minor_k : ∀ f⃗, motive e⃗_k (C_k p⃗ f⃗))…
      ı⃗ (t : T p⃗ ı⃗), motive ı⃗ t

(lean4lean `Inductive/Add.lean:326-483`, official `mk_rec_infos`):
the index binders are the type former's own telescope past the
parameters, re-emitted twice — at the motive (over the parameters
alone) and after the minors (lifted under the motive and the `n`
minors); the minor's conclusion applies the motive to the
constructor's residual index expressions (lifted under the extras)
before the constructor spine.  The rules are `directRecRhs`'s: a
rule binds no index (`rulePrefix = nP + 1 + n`).  At `nIdx = 0` every
generator below is the index-free one above. -/

/-- The family applied to its parameter variables and its index
variables: `e` extra binders sit between the parameters and the
indices (the motive and the minors), `o` binders below the index
frame. -/
def directFamI (T : Name) (lps : List Name) (nP nIdx e o : Nat) : Expr :=
  Expr.mkAppN (.const T (lps.map .param)) (directPsAt (o + e + nIdx) nP ++ directPsAt o nIdx)

/-- A constructor residual's shape at an indexed family: the family
at exactly the parameter variables (`o` binders below the parameter
frame) followed by `nIdx` index expressions. -/
def directCtorResidOk (T : Name) (lps : List Name) (nP o nIdx : Nat) (cbody : Expr) : Bool :=
  cbody.getAppFn == .const T (lps.map .param) &&
  cbody.getAppArgs.length == nP + nIdx &&
  cbody.getAppArgs.take nP == directPsAt o nP

/-- The motive's type `∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ` at the parameters'
frame, over the former's index telescope `itele = ∀ ı⃗, Sort w` (scoped
at the parameters); every binder's codomain is a type former, never a
proposition. -/
def directMotiveTyI (T : Name) (lps : List Name) (nP nIdx : Nat) (ℓ : Level) (itele : Expr) :
    Option Expr :=
  Expr.replacePisPw .never nIdx itele
    (.forallE (directFamI T lps nP nIdx 0 0) (.sort ℓ) ⟨.never⟩)

/-- The pieces of a recognised simple-structure block. -/
structure DirectParts where
  /-- the type former -/
  cvT : ConstantVal
  /-- the single constructor -/
  cvC : ConstantVal
  /-- parameter count -/
  nP : Nat
  /-- field count -/
  nF : Nat
  /-- the recursor -/
  cvR : ConstantVal
  /-- the recursor's fresh elimination level parameter (`large` only;
  `.anonymous` for a small eliminator) -/
  elim : Name
  /-- the structure's result sort -/
  resSort : Level
  /-- the single rule's right-hand side (as exported) -/
  rhs : Expr
  /-- **large eliminator** (task #175 W4c/O4): the recursor carries a
  fresh elimination level parameter in front and its motive lands in
  `Sort elim`; `false` is the small eliminator (`motive : T p⃗ → Prop`,
  the recursor's level parameters are the block's own) that Lean
  generates for a propositional structure with a non-`Prop` field. -/
  large : Bool
  /-- **propositional result** (task #175 W4c/O4): the result sort is
  provably `Prop` (`Level.isEquiv resSort .zero`).  Selects the
  squash-regime install: no field-universe bound (the official
  kernel's `Prop` escape hatch), entries only for the `Prop`-prefix of
  the fields, K for the fieldless case. -/
  isProp : Bool
  deriving Repr

/-- The *shape* facts the model reads off the stored (annotated)
types — everything that annotation cannot change, checked on both the
raw block (recognition) and the annotated constants (install).

The binder-domain correspondences are deliberately **not** here: the
reference kernels compare the constructor's parameter domains to the
type former's by `isDefEq` (`Add.lean:220-222`) and build the
recursor's telescope from `whnf`-peeled domains (`Add.lean:79-95`), so
a syntactic pin would wrongly reject; `checkDirectCtor` pins the
parameter domains definitionally over the opened telescopes, and the
recursor is generated and compared as a whole (`checkDirectRec`, task
#175 S2). -/
def directShape (T C : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP nF : Nat) (tty cty rty : Expr) : Bool :=
  match tty.stripPis nP, cty.stripPis (nP + nF), rty.stripPis (nP + 3) with
  | some (_, .sort _), some (_, cbody), some (rbs, rbody) =>
    cbody == directFam T lps nP nF &&
    rbody == Expr.app (.bvar 2) (.bvar 0) &&
    (match rbs[nP]? with
     | some (.forallE mmaj (.sort s') _, _) =>
       -- the motive's codomain: `Sort elim` for the large eliminator,
       -- `Prop` for the small one (task #175 W4c/O4)
       (if large then s' == .param elim else s' == .zero) &&
         mmaj == directFam T lps nP 0
     | _ => false) &&
    (match rbs[nP + 1]? with
     | some (mindom, _) =>
       match mindom.stripPis nF with
       | some (_, mbody) =>
         mbody == Expr.app (.bvar nF) (directCtorSpine C lps nP nF)
       | none => false
     | none => false) &&
    (match rbs[nP + 2]? with
     | some (majdom, _) => majdom == directFam T lps nP 2
     | none => false)
  | _, _, _ => false

/-- Recognise a direct simple-structure block (see the module docs).
`none` means "not this class" — the caller falls through to the modeled
path, so this is never an error source. -/
def directPartsCore? (block : List ConstantInfo) : Option DirectParts :=
  match block with
  | [.indInfo cvT _, .ctorInfo cvC nP nF, .recInfo cvR mI rP [rule]] =>
    let T := cvT.name
    let C := cvC.name
    let lps := cvT.levelParams
    -- the shape facts common to both eliminator shapes
    if cvR.name == T.str "rec" && cvC.levelParams == lps &&
        reservedBasisNames.contains T == false &&
        reservedBasisNames.contains C == false &&
        reservedBasisNames.contains cvR.name == false &&
        mI == nP + 2 && rP == nP + 2 &&
        rule.ctor == C && rule.nfields == nF &&
        (match rule.rhs.stripLams (nP + 2 + nF) with
         | some (_, rbody) => rbody == directRuleBody nF
         | none => false) then
      match cvT.type.stripPis nP with
      | some (_, .sort s) =>
        let isProp := Level.isEquiv s .zero == some true
        -- the large eliminator: a fresh elimination level parameter in
        -- front of the block's own; else the small eliminator at the
        -- block's own level parameters (task #175 W4c/O4)
        let large? : Option Name :=
          match cvR.levelParams with
          | elim :: relps =>
            if relps == lps && !lps.contains elim &&
                directShape T C lps elim true nP nF cvT.type cvC.type
                  cvR.type then
              some elim
            else none
          | [] => none
        match large? with
        | some elim =>
          some ⟨cvT, cvC, nP, nF, cvR, elim, s, rule.rhs, true, isProp⟩
        | none =>
          if cvR.levelParams == lps &&
              directShape T C lps .anonymous false nP nF cvT.type cvC.type
                cvR.type then
            some ⟨cvT, cvC, nP, nF, cvR, .anonymous, s, rule.rhs, false,
              isProp⟩
          else none
      | _ => none
    else none
  | _ => none

/-- The parameter spine of the generated projection types, spelled at
the frame of the final `∀ p⃗ (t : T p⃗), _` telescope: `p_k = bvar
(nP - k)` (the `instPisAtLift` walk lowers each entry once per
substitution step, landing them at `bvar (nP - 1 - k)` under the
subject binder). -/
def directProjPs (nP : Nat) : List Expr :=
  (List.range nP).map fun k => Expr.bvar (nP - k)

/-- The `j`-th earlier-field substitute in a **tower entry's**
generated type (task #175 wiring): the first-class node `t.j`
(`.proj T j` of the subject), at `directProjArg`'s frame (subject
`t = bvar 0`).  No `projFnName` chain — each field's entry stands
alone, which is what makes O4's per-field entry branch real. -/
def directProjArgP (T : Name) (j : Nat) : Expr :=
  Expr.proj T j (Expr.bvar 0)

/-- `directProjResid` in the `.proj`-node spelling: the constructor
telescope peeled at the parameters and the first `i` subject
projections, threaded incrementally (step `i → i + 1` is a single
`instantiate1Lift`). -/
def directProjResidP (T : Name) (nP : Nat) (cty : Expr) : Nat → Option Expr
  | 0 => Expr.instPisAtLift (directProjPs nP) cty
  | i + 1 => (directProjResidP T nP cty i).bind
      (Expr.instPisAtLift [directProjArgP T i])

/-- Does `bvar i` occur loose in `e`?  (Not through fvar type
annotations — the generated telescopes are fvar-free.) -/
def Expr.hasLooseBVar : Nat → Expr → Bool
  | i, .bvar j => i == j
  | _, .fvar .. => false
  | _, .sort _ => false
  | _, .const .. => false
  | _, .lit _ => false
  | i, .app f a => hasLooseBVar i f || hasLooseBVar i a
  | i, .lam ty b _ => hasLooseBVar i ty || hasLooseBVar (i + 1) b
  | i, .forallE ty b _ => hasLooseBVar i ty || hasLooseBVar (i + 1) b
  | i, .letE t v b =>
    hasLooseBVar i t || hasLooseBVar i v || hasLooseBVar (i + 1) b
  | i, .proj _ _ e => hasLooseBVar i e

/-- `hasLooseBVar` with the packed bound's cutoff (task #214, P4): a
node whose loose-bvar bound is at or below `i` has no `bvar i`, so the
walk stops there without descending — `directProjGuards`' O(nF²)
`directUsedLater` calls then touch only the spine of a large
telescope, never its shared instance towers.  Read as `hasLooseBVar`
by `Expr.hasLooseBVarB_eq` (`ConLeche/Verify/Direct/DirectBody.lean`). -/
def Expr.hasLooseBVarB (i : Nat) (e : Expr) : Bool :=
  if e.bvarB ≤ i then false else
  match e with
  | .bvar j => i == j
  | .fvar .. => false
  | .sort _ => false
  | .const .. => false
  | .lit _ => false
  | .app f a => hasLooseBVarB i f || hasLooseBVarB i a
  | .lam ty b _ => hasLooseBVarB i ty || hasLooseBVarB (i + 1) b
  | .forallE ty b _ => hasLooseBVarB i ty || hasLooseBVarB (i + 1) b
  | .letE t v b =>
    hasLooseBVarB i t || hasLooseBVarB i v || hasLooseBVarB (i + 1) b
  | .proj _ _ e => hasLooseBVarB i e

/-- **Field `j` is used by a later field** — the official
`infer_proj`'s `has_loose_bvars(binding_body(r))` at step `j`: the
field's variable occurs in the constructor telescope's remainder after
binder `j` (a later field's domain; the result never mentions a
field). -/
def directUsedLater (cty : Expr) (nP j : Nat) : Bool :=
  match cty.stripPis (nP + j + 1) with
  | some (_, rest) => rest.hasLooseBVarB 0
  | none => false

/-- **The projection guard levels** (task #175 W4c/O4): for field `i`,
its own sort joined with the sorts of the earlier fields that a later
field uses — the level a `.proj T i` use on a `Prop`-declared
structure must instantiate to `Prop` (the official `infer_proj`
restriction, both of its clauses, as one level).  `sorts` are the
fields' sorts in order (`checkDirectFieldSorts`). -/
def directProjGuards (cty : Expr) (nP nF : Nat) (sorts : List Level) :
    List Level :=
  (List.range nF).map fun i =>
    (List.range i).foldl
      (fun acc j =>
        if directUsedLater cty nP j then .max acc (sorts.getD j .zero)
        else acc)
      (sorts.getD i .zero)

/-- **The projection bodies of a recognised block** (task #175 S1),
one walk of the constructor telescope: after the parameters are
replaced by the loose variables `directProjPs nP` (parameter `k` at
`bvar (nP - k)`, the subject reserved at `bvar 0`), the fields are
peeled one at a time — field `i`'s domain is body `i`, and the field
is replaced by the subject's projection `.proj T i (bvar 0)` before
the walk continues (`directProjResidP`'s step).  So `bodies[i] =
F_i[p⃗ ↦ bvars, f_j ↦ .proj T j (bvar 0)]`, scoped at `nP + 1`: what
a `.proj T i e` use instantiates in one `instantiateList` along the
subject type's arguments and the subject (`ProjEntry.typeAt`).  The
table holds every field (the official `infer_proj` restriction at a
`Prop`-declared structure is the per-use guard level,
`directProjGuards`); no entry is annotated, inferred or pinned. -/
def directProjBodiesGo (T : Name) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE fdom body _ =>
    (directProjBodiesGo T k (i + 1) (body.instantiate1Lift (directProjArgP T i))).map
      (fdom :: ·)
  | _ + 1, _, _ => none

def directProjBodies (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr) :=
  match Expr.instPisAtLift (directProjPs nP) cty with
  | some r => (directProjBodiesGo T nF 0 r).map List.toArray
  | none => none

end ConLeche
