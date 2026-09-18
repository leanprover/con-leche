# Nested inductives, in an abstract calculus

What the kernel does to a nested inductive, what the model remembers for
each installed type, and how the soundness proof goes — written in terms
of operators and n-ary least fixpoints, so that the expansion, the block
model, and the nested-through-nested case can be seen without the tree's
names.  A short table at the end says where each object lives in the tree.
Indices are suppressed throughout: every "set" is really a family over the
type's index values, and every operator is index-respecting; nothing below
changes when they are put back.

## 0. The calculus

**Sets and operators.**  `V` is the ambient set theory.  An *operator* is a
map `Φ : V^k → V^k` (a *k-tuple operator*); it is *monotone* when
`X⃗ ⊆ X⃗'` pointwise implies `Φ(X⃗) ⊆ Φ(X⃗')` pointwise.  Every monotone
operator has a least fixpoint

    μX⃗. Φ(X⃗)   :=   ⋂ { Z⃗ | Φ(Z⃗) ⊆ Z⃗ }        (intersection of closed tuples)

characterised by two laws that are used constantly:

* **leastness** — if `Φ(Z⃗) ⊆ Z⃗` then `μΦ ⊆ Z⃗`;
* **fixpoint** — `Φ(μΦ) = μΦ`.

**Parameters.**  A type former with parameters is an operator *family*
`Φ(a⃗) : V^k → V^k`, monotone in `X⃗` for each fixed `a⃗`.  Positivity of a
parameter position means `Φ` is also monotone in that `a_i`.

**Constructor operators.**  A constructor `c : (f₁ : D₁) → … → (f_m : D_m) → T_j`
of a block contributes to component `j` the set of tuples
`{ c(f⃗) | f_i ∈ ⟦D_i⟧(a⃗, X⃗, f₁..f_{i-1}) }`; a field domain `D_i` may
mention the parameters, the recursive variables `X⃗` (only positively), and
earlier fields.  The block's operator is the union over its constructors,
component by component.

**Sections and Bekić.**  For a `(k+n)`-tuple operator `Ψ` and a tuple
`Z⃗ ∈ V^{k+n}`, the *section of Ψ at the segment `[k, k+n)` over Z⃗* is the
`n`-tuple operator

    Ψ|_Z⃗ (Y⃗)  :=  ( Ψ(Z⃗[k..k+n ↦ Y⃗]) )_{k..k+n}

— the last `n` components of `Ψ`, with the first `k` held at `Z⃗`'s values.
**Bekić's theorem** (segment form): if `L⃗ = μΨ`, then

    (L⃗)_{k..k+n}  =  μY⃗. Ψ|_L⃗ (Y⃗)                                        (B)

— a segment of the joint least fixpoint is the least fixpoint of its own
section over the joint fixpoint.  It holds for *every* segment at once;
nothing is sequential about it.

**Bekić against another presentation.**  Suppose `Φ'` is some other
`n`-tuple operator.  Then

    μY⃗. Ψ|_L⃗ (Y⃗)  =  μΦ'       if   ∀Y⃗.  Ψ|_L⃗ (Y⃗) = Φ'(Y⃗)              (B-whole)

and, weaker, if the two agree only *at* `μΦ'` and `Ψ|_L⃗` is dominated by
`Φ'` below it:

    μY⃗. Ψ|_L⃗ (Y⃗)  =  μΦ'       if   Ψ|_L⃗(μΦ') = Φ'(μΦ')  ∧  ∀Y⃗ ⊆ μΦ'. Ψ|_L⃗(Y⃗) ⊆ Φ'(Y⃗)     (B-at)

(B-whole) is a one-line congruence.  (B-at) needs the domination
hypothesis, and that hypothesis is where every difficulty in this story
lives.

## 1. Inductives as definitions

Semantically an installed inductive block `T⃗ = T₁..T_k` with parameters
`α⃗` is a *definition*

    T⃗  :=  λα⃗.  μX⃗. Φ_T⃗(α⃗)(X⃗)

and a member applied to parameters denotes a component of the fixpoint:
`⟦T_j(a⃗)⟧ = (μX⃗. Φ_T⃗(a⃗)(X⃗))_j`.  The environment is a list of such
definitions; a later type's operator may *use* an earlier definition —
that is what "nested" means.

**Nested.**  `T` is nested when a field domain of one of its constructors
has the shape `J(s⃗)` where `J` is an *earlier* inductive (the *container*)
and the argument list `s⃗` mentions `T`'s own recursive variable:

    Tree  :=  μX. { node(l) | l ∈ ⟦List⟧(X) }                     (container List at s = X)

Semantically this is unproblematic: `⟦List⟧(X) = μY. Φ_List(X)(Y)` is a
perfectly good monotone function of `X` (positivity of `List` in `α`, and
of `X` in `s⃗`), so `Φ_Tree(X) = { node(l) | l ∈ μY. Φ_List(X)(Y) }` is
monotone and `μX. Φ_Tree(X)` exists.  The *direct* semantics is "an
operator containing another μ".

**The kernel cannot work with `⟦List⟧`.**  It only has syntax, and
`List` is a sealed name whose constructors mention `List`, not `Tree`.
Positivity, universe levels, and above all the *recursor* need the
container's constructors to be *visible at the instantiation*.  Hence the
expansion.

## 2. What the kernel does: the expansion

Given a block `T⃗` with parameters `α⃗` and a nested occurrence `J(s⃗)`:

1. **Mint a copy.**  Create a fresh type `J'` (a *pin*, or *mimic*; in the
   tree the name is `_nested.J_i`) whose constructors are `J`'s with the
   substitution `α⃗_J ↦ s⃗` applied, and with every occurrence of the
   instantiated container `J(s⃗)` rewritten to `J'`.  Record the pin's
   *components* `s⃗` — the tuple of arguments the copy was taken at.
2. **Iterate.**  The copy's constructors may now contain *new* nested
   occurrences: either from `s⃗` (e.g. `List (Option Tree)` puts
   `Option Tree` inside `List`'s field `α`), or from `J`'s own nesting
   (if `J` was itself nested, its field `K(t⃗)` becomes `K(t⃗[α⃗_J↦s⃗])`).
   Each is a further pin; the process is a worklist over types, and it
   terminates because every pin's expression is a strict subterm of some
   constructor type instantiated at earlier pins' components.
3. **Install the auxiliary block.**  `{T⃗, J'₁, …, J'_n}` is now an
   ordinary *mutual* block with no nesting.  Check it exactly as a mutual
   block: positivity, universes, generate its recursors (one per member,
   including one per pin), check the stream's constructors and recursors
   against the generated ones.  This is the whole of "everything official
   checks of a nested block it checks *there*."
4. **Restore.**  The stream's declarations are in *user form* — they
   mention `List Tree`, not `J'`.  Rewrite `J'_i ↦ J_i(s⃗_i)` back in the
   generated constructors and recursors; the pin's recursor becomes
   `T.rec_i`.  Install the user-form `T⃗`.  Whether the auxiliary block is
   then *discarded* (current design) or *kept* (the backup design) is the
   fork discussed in §5.

**Semantically** the auxiliary block is a `(k+n)`-tuple operator `Ψ`:

    Ψ_j(X⃗, Y⃗)  =  Φ_T_j(X⃗)  with every  ⟦J_i(s⃗_i)⟧  replaced by the variable  Y_i      (members)
    Ψ_{k+i}(X⃗, Y⃗)  =  Φ_{J_i}(s⃗_i[X⃗,Y⃗])(Y_i)                                              (pins)

where in the pin row, `s⃗_i[X⃗,Y⃗]` means the components with members read
as `X⃗` and any further pins read as the corresponding `Y`, and any nested
occurrence *inside* `J_i`'s own constructors likewise read as its pin.  The
block being installed is then modelled as the member segment of the joint
fixpoint:

    ⟦T⃗⟧  :=  (μ(X⃗,Y⃗). Ψ(X⃗,Y⃗))_{0..k}                                   (aux)

## 3. What we remember for each type: the block model

For every installed inductive the model keeps a *block model*
`d = ⟨k, nP, Φ_d, pins, …⟩`:

* `k` members, `nP` parameters, index data;
* **the operator `Φ_d`, at width `k`, as a function of a parameter frame**
  — this is the `Φ_T⃗(α⃗)` of §1;
* for a nested type, its **pin table**: for each of its own pins, the
  container's name and the components `s⃗` (both as syntax and as
  readings), and a *pin carrier* `pinCar_i(X⃗)` — the pin's slot as a
  function of the members' tuple;

**Stored versus re-derived.**  Not everything the proof needs about a
container is *fixed* by these laws, and the difference matters.  A
*member*'s parameter telescope is determined: the law `former` carries a
reading equation for the member's stored type, and readings are functions,
so any two valid models of the same block agree on it — it is
*re-derived* at the use site, never recorded.  A *pin*'s universe and
index data are **not** determined: the laws constrain them only by a
membership, a length, and a congruence, and the universe is a bare field.
Two valid models of the same container may therefore differ on a pin's
syntactic data, and no argument from the semantics can close that gap —
which is why the block being installed *records* the tie between its
own pins and the container's (one clause, on the one structure that
binds the container's model, whose single producer holds the fact for
free).  A second thing is recorded for the same reason, one level down:
that a *nested field*'s parameter arguments mention a member of the
container's own group.  The opened form of a constructor keeps a nested
field's head and its argument count and drops the parameter part, so the
fact cannot be read back where it is wanted; it is carried from the
container's own restore, where the field's spine is still visibly the
pin re-opened.  It is recorded as a *mention* and not as an equality:
the restore closes the pin over the parameters and reopens it at the
constructor's own variables, and those differ from the block's by
definitional unfolding, so the two spines need not be equal — but a
mention survives both steps, and a mention is all the proof asks for.
Uniqueness of models is never needed: semantic facts meet at the
readings, and syntactic facts that no law fixes are recorded.

The laws, of which two matter here:

    leaf:     ⟦T_j(a⃗)⟧  =  (μX⃗. Φ_d(a⃗)(X⃗))_j                                      (the definition of §1)
    pinLeaf:  ⟦J_i(s⃗_i[a⃗, μΦ_d(a⃗)])⟧  =  pinCar_i(μΦ_d(a⃗))                       (the entry law)

`pinLeaf` says: the *container applied to the pin's components*, read at
the true carrier, is exactly the pin's slot.  It is what makes the restored
constructor `node : List Tree → Tree` well-typed against a carrier that was
built from `J'`.

**The crucial representational fact.**  `Φ_d` is the *narrow* operator.
For a nested `T`, the model constructs `⟦T⃗⟧` via (aux) as a segment of the
wide `μΨ`, and then *packages* the result at width `k`:

    Φ_d(a⃗)(X⃗)  =  Ψ_{0..k}( X⃗,  μY⃗. Ψ_{k..k+n}(X⃗, Y⃗) )                        (compose)

— the members' rows of `Ψ`, with the pins *solved internally* by an inner
`μ` at each `X⃗`.  Bekić says `μΦ_d = (μΨ)_{0..k}`, so this is a correct
definition.  But the wide operator `Ψ` is a *local of the construction*:
once `T` is installed, a later block that uses `T` as a container sees only
`Φ_d`, `pinCar`, and the laws — never `Ψ`.  Everything hard in §5 traces to
this.

## 4. The proof: discharging `pinLeaf`

Fix the block being installed, its wide operator `Ψ`, `L⃗ = μΨ`, and a pin
`i` with container `J` and components `s⃗`.  We need

    ⟦J(s⃗[L⃗])⟧  =  L_{k+i}.                                                     (goal)

The right side is a segment of `μΨ`; Bekić (B) at the one-element segment
`{k+i}` gives

    L_{k+i}  =  μY. Ψ_{k+i}(L⃗[k+i ↦ Y])  =  μY. Φ_J(s⃗[L⃗])(Y)       — IF the pin row reads its components at L⃗.

The left side is, by `J`'s own `leaf`, `μY. Φ_J(s⃗[L⃗])(Y)`.  So the goal
reduces to *agreement of two presentations of the same one-tuple operator*,
and the question is whether that agreement is whole-space (B-whole) or
only at the carrier (B-at).

**Case A — the container is not itself nested, and `s⃗` mentions no other
pin.**  Then `Ψ_{k+i}(X⃗,Y⃗) = Φ_J(s⃗[X⃗])(Y_i)` reads only `X⃗` and `Y_i`;
the section over `L⃗` is `Y ↦ Φ_J(s⃗[L⃗])(Y)` *for every* `Y`, and
`Φ' := Φ_J(s⃗[L⃗])` is the same function.  (B-whole) applies; the
discharge is definitional.  `Tree`/`List` is this case.

**Case B — `s⃗` mentions another pin `i'`.**  E.g. `List (Option Tree)`:
pin `i = List` at `s = Option Tree`, and `Option Tree` is itself pin `i'`.
Then `Ψ_{k+i}` reads `Y_{i'}`, and the section over `L⃗` is
`Y ↦ Φ_List(L_{k+i'})(Y)`, while `Φ' = Φ_List(⟦Option Tree⟧)`.  These agree
on the whole space iff `L_{k+i'} = ⟦Option(L⃗)⟧` — which is (goal) at pin
`i'`.  So (goal) at `i` follows from (goal) at `i'` by (B-whole) plus
congruence, and pin `i'`'s expression is a *strict subterm* of pin `i`'s.
This is an induction over the **containment** order on pins — a syntactic,
well-founded order (a pin cannot occur inside its own components).  Still
no domination, no candidate tuples: everything is at `L⃗`.

**Case C — the container is itself nested.**  This is §5.

The *inclusion* form of the goal, `⟦J(s⃗[L⃗])⟧ ⊆ L_{k+i}`, is what the
block-model construction actually consumes (the field domain of the
restored constructor must land in the slot), and it is even easier in
cases A and B: it is leastness of `μΦ_J(s⃗[L⃗])` against `L_{k+i}`, which
is closed under `Φ_J(s⃗[L⃗])` because `L⃗` is closed under `Ψ` — again
unfolded along containment, using only that container operators are
monotone in their parameters (positivity).

## 5. Nested through nested

Let the container be itself nested:

    Tree'(α)  :=  μX. { node(l) | l ∈ ⟦List⟧(X) }             — Tree' has one own pin, List at s = X
    Foo       :=  μZ. { mk(t)   | t ∈ ⟦Tree'⟧(Z) }            — Foo nests through Tree'

**The kernel's expansion** mints pin 1 = `Tree'(Foo)` with components
`[Foo]`; its constructor `node : List (Tree' Foo) → Tree'_Foo` contains
`List (Tree' Foo)`, so pin 2 = `List` at `s = Tree' Foo` — whose
component is *pin 1's expression* — with constructor
`cons : Tree'_Foo → List_2 → List_2`.  Auxiliary block `{Foo, Tree'_Foo, List_2}`:

    Ψ_0(Z, Y₁, Y₂) = { mk(t)   | t ∈ Y₁ }
    Ψ_1(Z, Y₁, Y₂) = { node(l) | l ∈ Y₂ }
    Ψ_2(Z, Y₁, Y₂) = { nil } ∪ { cons(h, t) | h ∈ Y₁, t ∈ Y₂ }

`L⃗ = μΨ`.  The direct semantics agrees: `(μΨ)_0 = ⟦Foo⟧` by Bekić at the
member segment, and unfolding the inner `μ` gives exactly `Foo`'s
definition.

**The proof at pin 1.**  (goal): `⟦Tree'(L_0)⟧ = L_1`.  Bekić at the
segment `{1}`:

    L_1  =  μY. Ψ_1(L_0, Y, L_2)  =  μY. { node(l) | l ∈ L_2 }  =  { node(l) | l ∈ L_2 }

— the section is **constant in `Y`**, because `Ψ_1` reads its own pin
`List` as the *separate* variable `Y₂`, held at `L_2` by the section.  The
other presentation is `Tree'`'s stored narrow operator,

    Φ_{Tree'}(L_0)(Y)  =  { node(l) | l ∈ ⟦List⟧(Y) }  =  { node(l) | l ∈ μW. Φ_List(Y)(W) }

which *solves `List` internally* (this is (compose) for `Tree'`) and is not
constant in `Y`.  So (B-whole) is unavailable at width one: the two
operators agree at `Y = L_1` only if `L_2 = ⟦List⟧(L_1)` — which is (goal)
at pin 2 — and (goal) at pin 2, by the same computation, needs
`L_1 = ⟦Tree'⟧(L_0)`, i.e. (goal) at pin 1.  **That is the cycle.**  It is
not a cycle among the copies (they are one joint `μ`); it is a cycle in the
*identification* of copies with containers' *separately solved* fixpoints,
and it arises exactly when the container solves its own pins inside its
stored operator while the auxiliary block exposes them as variables.

**Resolution 1 — widen the segment.**  Take Bekić at the segment `{1,2}`
— the container's whole *instance* (its copy plus the copies of its own
pins):

    (L_1, L_2)  =  μ(Y₁,Y₂). ( Ψ_1(L_0,Y₁,Y₂), Ψ_2(L_0,Y₁,Y₂) )
                =  μ(Y₁,Y₂). ( {node(l) | l ∈ Y₂},  {nil} ∪ {cons(h,t) | h ∈ Y₁, t ∈ Y₂} )

and compare with `Tree'`'s **wide** operator `Ψ^{Tree'}` at `α ↦ L_0`,
whose rows are `( {node(l) | l ∈ W}, Φ_List(Y)(W) )` — the same two rows.
Agreement is whole-space and definitional; (B-whole) applies; the
identification of the whole instance with `⟦Tree'⟧(L_0)`'s own auxiliary
fixpoint is one line, and `L_1 = ⟦Tree'⟧(L_0)` falls out by (compose) for
`Tree'`.  This is what the pure-set-model experiment (`SegCopy`) proved,
for this shape and for a copied instance instantiated at another copy.
**What it needs is `Ψ^{Tree'}` — the container's wide operator — which the
stored block model of `Tree'` does not carry (§3).**  Three things follow,
each checked against the tree:

* *Giving the model the wide operator is cheap.*  One field `Ψaux` on the
  block model with two laws (`Φ = compose(Ψaux)`, `pinCar = pinsCar(Ψaux)`);
  the nested construction promotes its local and both laws are `rfl`; every
  non-nested route has no pins, so `Ψaux := Φ` and the laws are trivial.
  About ten sites, all but one vacuous.  No kernel change.
* *The instance is the* closure, *not the kernel's mint partition, and it
  is computable model-side.*  The container's own pins are a stored field
  of its block model; matching them against the block's pins is a pure
  function of data the model already holds.  (The kernel's partition of
  pins by which type minted them is a different, coarser thing and is not
  what the segment needs.)
* *Contiguity is not required.*  The kernel's worklist does interleave
  instances (two nested containers in one constructor mint both roots
  before expanding either — an accepted input), and Bekić's segment
  theorem is stated for a contiguous range.  But the joint tuple can be
  *reindexed*: pulling back the wide operator along a permutation is a
  definitional congruence, after which the instance is a range.  One
  reindexing lemma, no kernel change, no effect on the accept set.

What survives Resolution 1 is smaller and no longer an ordering problem
*within* an instance: the identification at an instance's *root* pin is
still stated at the root's component values, which are auxiliary carriers
whenever the root's components mention other pins (so a candidate tuple
and the component family are still needed there); there is an induction
over *instances* for targets outside a segment; and it is acyclic by
argument — a cross-instance edge is parameter-headed (nothing required) or
constant-headed with the head a constant of the source container's own
declaration, hence declared strictly earlier.  A cycle would need two
containers mentioning each other, which makes them one mutual group and
hence one instance.

**Resolution 2 — keep the copies (the backup design).**  Never discard
the auxiliary block: `Tree'` is stored *as* `{Tree', List_Tree'}` with
`Ψ^{Tree'}` as its operator, and `Foo`'s block is formed by *instantiating
and copying* `Tree'`'s stored block at `α ↦ Foo` rather than re-expanding.
Then the wide operator is what is stored, the instance is contiguous by
construction (it is one copied run), and Resolution 1 is literal.  The
cost moves to the user-form ↔ stored-form translation of constructors and
recursors, which the stream requires in user form.

**Resolution 3 — (B-at) with an ordered induction (the current route).**
Keep the narrow stored model.  Use (B-at): agreement *at* the carrier plus
domination below it.  The domination hypothesis is an *inclusion at
another pin* — `⟦J'(s⃗)⟧ ⊆ L_{k+i'}` for the pins the section reads — and
proving it needs those pins' identifications first.  So the proof states
each pin's identification not at `L⃗` but at a *candidate* tuple `Z⃗`
(closed under `Ψ`, ranging over the intersection that defines `μ`), and
runs an induction over pins with a well-founded measure.  Two orders are
in play: **containment** (case B above; syntactic) and **declaration
order** of the containers (for edges whose domain head is a constant of an
earlier-declared type — a kernel record certifies the order).  Their union
is not acyclic on accepted inputs, but the two inductions consume
different facts and run one after the other: the declaration-order pass
establishes every pin's inclusion, and the containment pass then upgrades
inclusions to equalities using the first pass's *finished* conclusion.
The parameter-headed edges (the container's field is its parameter, as
`List`'s `α`) carry no obligation in the first pass at all, which is what
breaks the apparent cycle `Tree' → List → Tree'`: the return edge is
parameter-headed.  This route works, but it is the long way round a fact
that Resolution 1 states in one line — because it lacks the object
Resolution 1 needs.

## 6. Where this lives in the tree

| calculus | tree |
|---|---|
| `μX⃗.Φ`, leastness, fixpoint | `lfpTuple`, `lfpTuple_le`, `lfpTuple_fixed` (`SetTheory/Derive/LfpTuple.lean`) |
| (B) Bekić at a segment | `lfpTuple_seg`, `lfpTuple_eq_section` |
| (B-whole) | `lfpTuple_seg_congr` (`SetTheory/Derive/LfpCompose.lean`) |
| (B-at) | `lfpTuple_seg_congr_at`, `lfpTuple_eq_of_at` |
| (compose): narrow from wide | `composeΦ`, `pinsCar`, `lfpTuple_composeΦ`; `ofNested` in `Model/Inductives/BlockComposed.lean` |
| the block model and its laws | `BlockModel`, `IsBlockModel` (`leaf`, `pinLeaf`, `functor`, `pinMono`) in `Model/Inductives/BlockRep.lean` |
| the expansion | `replaceIfNested`, `mkCopies`, the worklist `elimLoop` in `Kernel/Inductives/NestedElim.lean`; `checkNested` in `Kernel/Inductives/NestedInstall.lean` |
| the pin table | `NestedPin` (`grpBase`, `grpSize`, components), read back as `NestedPinSynFacts` |
| the aux block's install | `checkMutualCore` on `{T⃗, J'⃗}` in a scratch environment |
| restore | `restoreNested`, `restoreRules`, `restoreRecTys` |
| Resolution 1's experiment | `SetModel/SegCopy.lean` |
| Resolution 3's apparatus | `pinLfpAt` (candidate tuples), `pins_le_of_declOrder`, `hentR` in `Model/Inductives/NestedFit.lean` / `NestedPinLeafAll.lean`; the declaration-order record `declPos`/`nestedPinOrderAt` |

## 7. What is settled and what is not

Settled: the calculus of §0–§4; that Case A and Case B need nothing beyond
(B-whole) and containment; that the nested-through-nested cycle is an
artefact of the narrow stored operator (§5, verified both by the
experiment and by reading the stored model); that Resolution 3's two
passes consume different facts and can be sequenced.

Also settled, by reading the stored model and by two accepted witnesses:
Resolution 1 *can* be adopted in the current design without any kernel
change — the wide operator is one mostly-trivial field, the instance is
the closure computed from the stored pin table, and interleaving is
handled by reindexing rather than by contiguity.  Adopting it deletes the
domination hypothesis and the within-instance transfer machinery of
Resolution 3 outright, and leaves a smaller residue: the component family
at instance roots, an induction over instances, and the declaration-order
record for cross-instance constant-headed edges.

Decided: Resolution 1 is adopted, in stages so that each stands alone —
first expose the wide operator on the block model (strictly additive),
then the reindexing lemma (pure set theory, general), then the
identification at the instance closure (the step that can fail; if it
does, the first two remain).  Resolution 3's machinery is not deleted
until the third step lands.  In parallel, the two things every design
needs: the reading of a rewritten term (§8, item 1) and the second
residual's syntactic correspondence.

Not settled: the exact cost of the residue — the component family at
instance roots, the induction over instances, and whether the closure's
identification is as cheap as the experiment suggests once the readings
are threaded.

## 8. What the abstraction hides

Everything above is stated at sets and operators.  The tree works with
syntax — kernel expressions, their readings as annotated terms, and the
interpretation of those at a frame — and the bulk of the proof engineering
is showing that the syntax the kernel produces *reads as* the operator
written here.  Five things live entirely below this document's level and
are where the cost is:

1. **Reading through the rewrite.**  "The copy's constructors are `J`'s at
   the substitution" is one clause in §2.  In the tree the stored
   constructor is the *rewrite* of the *normalisation* of the *minted*
   copy, and there is no semantic theorem about the rewrite at all — every
   theorem about it is syntactic.  The reading of a rewritten term, as a
   relation transporting readings through the rewrite (congruence at every
   constructor plus one firing case, closed under binder opening), is a
   new object every design needs.  This is why the whole-space agreement
   that is definitional in the pure experiment is an *instantiation law* in
   the tree.
2. **Frames.**  `s⃗[L⃗]` is a substitution here.  In the tree a term is read
   at a frame (bound variables to sets); the container's frame is built
   from the components' readings at the block's frame; every transport
   between them is a lemma.  The rule that the copy's slot is read at the
   block's frame and does not move while the container's side is read at
   the frame that varies is real and this notation collapses it.
3. **Environments and naming.**  §1 has one list of definitions.  The tree
   has an environment model per environment, readings that cross
   environments in one variance direction only, and a *choice* of block
   model per container with no uniqueness — see §3's stored-versus-derived
   note for what that costs and how it is paid.
4. **Reflexive fields.**  `f_i ∈ ⟦D_i⟧` treats a function-space domain like
   any other.  In the tree every reflexive case is a separate arm: the
   reading opens a binder tower, and the rewrite must be shown inert on it.
5. **Recorded versus derived facts.**  This document has no notion of a
   certification check.  The tree obtains syntactic facts the model cannot
   derive by having the kernel *check* them — each such check is a
   recorded, numbered, measured obligation, and *deciding* whether a fact
   needs one or can be derived from what the model already holds is a
   recurring design question with a standing preference for deriving.

Outside the document's scope altogether: the recursors and iota rules
(large, and done for this route), the cached checker's simulation of the
pure one (deferred until the model side is finished), the switch of the
kernel's dispatch from the old route to this one with its accept-set
re-measurement, and indices.

