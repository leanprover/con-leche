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

and, between the two and at the strength the theory actually asks for,
if they agree on the tuples below a tuple `C` closed under both — a
least fixpoint is an intersection of closed tuples, and every closed
tuple may be clamped to `C` without changing that intersection:

    μY⃗. Ψ|_L⃗ (Y⃗)  =  μΦ'    if  Ψ|_L⃗(C) ⊆ C ∧ Φ'(C) ⊆ C ∧ ∀Y⃗ ⊆ C. Ψ|_L⃗(Y⃗) = Φ'(Y⃗)   (B-below)

(B-whole) is a one-line congruence.  (B-at) needs the domination
hypothesis, and that hypothesis is where every difficulty in this story
lives.  (B-below) needs no relation between the two operators at all,
only a common closed bound.

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
   The mint is syntax only, so on the model side "the copy's constructors
   are `J`'s at the substitution" is not a definition but a *transport* —
   a rewritten term's reading is the original's with each rewritten
   occurrence read as the mimic's carrier — and it is proved by a
   congruence between a term and its rewrite with one firing case.
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
* **the wide operator `Ψ_d`, at width `k + n`** — one row per member and
  one per pin, the pins still variables;
* for a nested type, its **pin table**: for each of its own pins, the
  container's name and the components `s⃗` (both as syntax and as
  readings), and a *pin carrier* `pinCar_i(X⃗)` — the pin's slot as a
  function of the members' tuple;
* **the auxiliary block's constructor data at every component** — the
  members' as always, and one *copy record* per pin (the container's
  constructors instantiated at the pin: field domains, recursive flags,
  field targets in `members ++ pins`, telescopes, index expressions,
  result readings, injection).  Together they give a constructor
  decomposition at each of the `k + n` components, which is what
  reading `Ψ_d` fibrewise needs;

**Stored versus re-derived.**  Not everything the proof needs about a
container is *fixed* by the laws listed below, and the difference matters.  A
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
That mention is recorded twice over, on the field's *opened* spine and
on the stored constructor's own: the opened spine is the one the
readings work on, the stored one is what the checker's record about the
classification is tested against, and a mention travels only from the
stored form to the opened one — an opened variable's type annotation
can carry a mention the stored form does not have.
A third is recorded for a different reason again: that no projection
node in a container's stored constructor type names one of that
container's own members.  That is true, and the constant check is what
makes it true — a member being declared has no projection table yet, so
such a node is rejected at the block's own installation — but the fact
is an *insertion-time* one, and a projection-slot check is satisfied
more easily in a larger environment, so nothing a later reader knows
about the environment it sees recovers it.  It rides on the block's
record from the door the constructor came through.
A fourth is of a different kind again: it is about the ELIMINATION's own
output rather than about a container.  A copy is the container's
constructors at the pin's components with every group occurrence
rewritten, so a container field that nests through a FURTHER container
carrying one of the container's own members becomes, in the copy, a
field at one of the block's own pins — and the block's classification
says so.  Neither direction of that correspondence is derivable: the
copies come from a rewrite the model tier has no theorem about, so both
are recorded at the install, one each way.  A REFLEXIVE such field gets
its own record on the same walk: its stored domain is a function space,
so the record that dispatches on the domain's head sees a `Π` and says
nothing there, and the twin asks the same question of the telescope's
body — which is also why the mention above is carried on that body as
well as on the two spines.
Uniqueness of models is never needed: semantic facts meet at the
readings, and syntactic facts that no law fixes are recorded.

The laws, of which four matter here:

    leaf:     ⟦T_j(a⃗)⟧  =  (μX⃗. Φ_d(a⃗)(X⃗))_j                                      (the definition of §1)
    pinLeaf:  ⟦J_i(s⃗_i[a⃗, μΦ_d(a⃗)])⟧  =  pinCar_i(μΦ_d(a⃗))                       (the entry law)
    fibre:    x ∈ Φ_d(a⃗)(X⃗)_j(t)  ⟺  x = c(f⃗), c a constructor of member j whose fields
              fit at X⃗ and whose index expressions read t                      (the narrow fibre)
    auxFibre: x ∈ Ψ_d(a⃗)(Z⃗)_c(t)  ⟺  the same at COMPONENT c — a member's row or a
              copy's — with every recursive field read at Z_{tgt} ITSELF        (the wide fibre)

`pinLeaf` says: the *container applied to the pin's components*, read at
the true carrier, is exactly the pin's slot.  It is what makes the restored
constructor `node : List Tree → Tree` well-typed against a carrier that was
built from `J'`.

**Narrow and wide.**  `Φ_d` is the *narrow* operator.  For a nested `T`
the model constructs `⟦T⃗⟧` via (aux) as a segment of the wide `μΨ_d`, and
then *packages* the result at width `k`:

    Φ_d(a⃗)(X⃗)     =  Ψ_d(a⃗)( X⃗, pinCar_d(a⃗)(X⃗) )_{0..k}                      (compose)
    pinCar_d(a⃗)(X⃗) =  μY⃗. Ψ_d(a⃗)_{k..k+n}(X⃗, Y⃗)                              (pins)

— the members' rows of `Ψ_d`, with the pins *solved internally* by an
inner `μ` at each `X⃗`, and the pins' carriers that inner `μ`.  Bekić says
`μΦ_d = (μΨ_d)_{0..k}`, so this is a correct definition.  Both equations
are *laws of the block model*, so the wide operator is not lost when the
construction ends: a later block that uses `T` as a container reads
`Ψ_d` off `T`'s stored model.  §5 is what that buys.  A block with no
pins is its own wide operator, and both laws are trivial there.

The two fibres stand in the same relation: `fibre` IS `auxFibre` at a
member and at the *extended* tuple `(X⃗, pinCar(X⃗))`, and that is a
theorem, not a second assumption — the class readers are the members'
there and the class fit over the extended tuple is the member's fit at
`X⃗`.  What the narrow one cannot do is the converse: it says nothing
at a tuple that is not extended, and a container instance's copies
inside a later block are read at exactly such tuples.  Hence `auxFibre`
is the stored law and `fibre` its restriction.

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
stored block model of `Tree'` carries (§3).**  Three things follow,
each checked against the tree:

* *The model has the wide operator.*  One field `Ψaux` on the block
  model, carrying (compose) and (pins) of §3 as laws together with its
  functor laws at width `k + n`; the nested construction promotes its
  local and the two composition laws are `rfl`; every non-nested route
  has no pins, so `Ψaux := Φ` and the laws are trivial.  Eight law
  sites, all but one vacuous.  No kernel change.
* *The instance is the* closure, *not the kernel's mint partition.*  The
  container's own pins are a stored field of its block model, and the
  segment is that table matched against the block's pins.  (The kernel's
  partition of pins by which type minted them is a different, coarser
  thing and is not what the segment needs.)  **The matching is not an
  injection.**  The expansion mints one copy per distinct pin
  EXPRESSION, so two of the container's own pins whose components differ
  only in parameter positions the block instantiates alike arrive at one
  copy — `K α (J α β)` and `K β (J α β)` at `α = β`.  Two of the
  container's classes then share a component of the block's tuple, and
  the index-set form of Bekić, which is stated for an injection, does
  not apply as it stands.  What it wants instead is the tuples that are
  constant on the matching's fibres, and the container's operator
  preserving them.  It does preserve them, but only THERE: at a tuple
  that tells two identified classes apart their rows genuinely differ,
  as soon as the classes' own container is recursive, so the fibres are
  not a convenience but the exact domain of the agreement.  What makes
  the two rows agree on them is that the two classes share their copy
  in the block: one copy is one constructor list read once, hence one
  row.
* *Contiguity is not required.*  The kernel's worklist does interleave
  instances (two nested containers in one constructor mint both roots
  before expanding either — an accepted input), and Bekić's segment
  theorem is stated for a contiguous range.  But Bekić holds at an
  arbitrary *index set* just as well: the same proof, with the segment
  `[a, a+s)` replaced by the image of an injection `σ : [0,s) → [0,N)`
  and the join `Z[a..a+s ↦ Y⃗]` by `Z[σ i ↦ Y_i]`, gives

      (L⃗)_{σ i}  =  μY⃗. Ψ|^σ_L⃗ (Y⃗) _i                                (B-set)

  and its congruence against another presentation, of which the
  contiguous form is the case `σ = (a + ·)`.  One reindexing lemma, no
  kernel change, no effect on the accept set.
* *The identification needs the container's CONSTRUCTORS, not just its
  operator.*  The agreement `hΦ` above is a statement about the
  container's wide operator at *every* tuple, and (compose)/(pins)
  determine it only at the tuples of the form `(X⃗, pinCar(X⃗))`.  So
  the block model must expose the wide operator FIBREWISE too — a
  constructor decomposition at every component, members and pins
  alike, which is the auxiliary block's constructor data.  That is a
  representation change, not an annotation, and it is the real price
  of Resolution 1.  **It is paid**: the block model carries one copy
  record per pin and the law `auxFibre` (§3), the narrow `fibre` is now
  a theorem about it, and a block with no pins discharges the wide law
  from the narrow one.  A second, cheap clause came with it — that a
  pin component's index-tuple set IS the pin's, which nothing in the
  earlier laws forced.

What survives Resolution 1 is smaller and no longer an ordering problem
*within* an instance.  What it is, exactly, is the **comparison of two
copies of one container at two instantiations**, related only through
that container — and that is not an accident of the proof but the
content of nested-through-nested itself: the block's copy of the
container's own pin and the container's own record of that pin are both
copies of the *pin's* container, minted at different substitutions.  The
machinery for it already exists, in this route's own vocabulary (the
transfer between two copies of one container, §6).  What does NOT
survive is the domination: no inclusion at another pin is required, no
candidate tuple ranges over closed tuples, and no ordered induction
sequences the pins.

The comparison does carry a BOUND, which the domination did not have in
the same sense: it holds for tuples below the container's OWN carrier,
because the run's copy-versus-container readings are stated at prefixes
that fit the container's domains, and a container-recursive field's
domain is its carrier.  That bound is a fact about a type already
installed, so it needs nothing from any other pin — it is not (B-at)'s
`hle` in disguise — and the identification therefore uses **(B-below)**
with the container's own wide carrier as `C`: closed under the
container's operator because it IS its least fixpoint, and closed under
the copies' section because the two agree at it.

Besides the comparison there is still an induction over *instances* for
targets outside a segment; and it is acyclic by argument — a
cross-instance edge is parameter-headed (nothing required) or
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
| (B-below) | `lfpTuple_congr_le`, `lfpTuple_set_congr_le` (same file; `meetT` clamps the closed tuples) |
| (B-set), (B-whole) at an index set | `lfpTuple_set`, `lfpTuple_set_congr` (same file; `setJoin`, `setSec`) |
| (B-at) | `lfpTuple_seg_congr_at`, `lfpTuple_eq_of_at` |
| (compose): narrow from wide | `composeΦ`, `pinsCar`, `lfpTuple_composeΦ`; `ofNested` in `Model/Inductives/BlockComposed.lean` |
| the block model and its laws | `BlockModel`, `IsBlockModel` (`leaf`, `pinLeaf`, `functor`, `fibre`, `pinMono`) in `Model/Inductives/BlockRep.lean` |
| the wide operator, stored | `BlockModel.Ψaux` with `auxFunctor`, `auxCompose`, `auxPinsCar` (same file) |
| the copies' constructor data | `PinCtors`, the field `BlockModel.pinCtors`, the class readers `ctorsT`/`FssT`/`tgtsT`/`slotAtT`/`ChainFitT` (same file) |
| the wide fibre | `IsBlockModel.auxFibre`, `auxPinIdx`; `BlockModel.fibre_of_auxFibre`, `auxFibre_of_noPins` (same file) |
| the expansion | `replaceIfNested`, `mkCopies`, the worklist `elimLoop` in `Kernel/Inductives/NestedElim.lean`; `checkNested` in `Kernel/Inductives/NestedInstall.lean` |
| the rewrite at the readings | `RewriteRel`, `replaceAllNested_rel`, `denoteMeta_of_rewriteRel` (`Model/Inductives/NestedRewriteRead.lean`) |
| the pin table | `NestedPin` (`grpBase`, `grpSize`, components), read back as `NestedPinSynFacts` |
| the aux block's install | `checkMutualCore` on `{T⃗, J'⃗}` in a scratch environment |
| restore | `restoreNested`, `restoreRules`, `restoreRecTys` |
| Resolution 1's identification | `ofNested_pin_block_wide`, `ofNested_pin_block_of_wide` (`Model/Inductives/BlockComposed.lean`) |
| its agreement, reduced to the fits | `ofNested_hΦ_of_fit` (same file) |
| the fits at the container's members | `CopyCtorShape.fit_iff_wide`, `hfit_wide_mem_of_inst`, `hfit_wide_of_inst` (`Model/Inductives/NestedFit.lean`) |
| the transfer between two copies of one container | `chainFitT_congr_mem`, `copyTransfer_via`, `copyTransfer_iff` (`Model/Inductives/NestedPinLeafAll.lean`) |
| the fit at a container's own-pin class | `pinClassFit_of_transfer`, `hfit_wide_pin_of_class` (same file) |
| the identification assembled | `ofNested_pin_block_of_wide_inst` (`Model/Inductives/NestedFit.lean`) |
| Resolution 1's experiment | `SetModel/SegCopy.lean` |
| Resolution 3's apparatus | `pinLfpAt` (candidate tuples), `pins_le_of_declOrder`, `hentR` in `Model/Inductives/NestedFit.lean` / `NestedPinLeafAll.lean`; the declaration-order record `declPos`/`nestedPinOrderAt` |

## 7. What is settled and what is not

Settled: the calculus of §0–§4; that Case A and Case B need nothing beyond
(B-whole) and containment; that the nested-through-nested cycle is an
artefact of the narrow stored operator (§5, verified both by the
experiment and by reading the stored model); that Resolution 3's two
passes consume different facts and can be sequenced.

Also settled: Resolution 1 needs no kernel change.  The wide operator is
a stored field of the block model, the instance is the closure computed
from the stored pin table, and interleaving is handled by reindexing
rather than by contiguity — (B-set).  The identification itself is
proved at the set-theoretic layer, and it carries NO domination
hypothesis: (B-at)'s `hle` — an inclusion at ANOTHER pin, which is what
forced Resolution 3's ordered induction — has no counterpart on the
wide route.  Its agreement is, however, bounded: it holds below the
container's own carrier and not on the whole tuple space (§5), so the
congruence it feeds is the one for two operators agreeing on the tuples
below a common closed tuple.

Also settled: the representation Resolution 1 asks for.  The block
model remembers the auxiliary block's constructor data at every
component and reads its wide operator fibrewise (`auxFibre`), the
narrow fibre is that law restricted to the members, and a pin
component's index set is the pin's.

Decided: Resolution 1 is adopted, in stages so that each stands alone —
first expose the wide operator on the block model (strictly additive),
then the reindexing lemma (pure set theory, general), then the
identification at the instance closure (the step that can fail; if it
does, the first two remain).  Resolution 3's machinery is not deleted
until the third step lands.  In parallel, the two things every design
needs: the reading of a rewritten term (§8, item 1 — landed, §6) and the
second residual's syntactic correspondence.

Three named things, the first of them now landed.

**(i) The bound — LANDED.**  `hΦ` as first stated quantified over the
whole tuple space, and the run cannot supply that: the
copy-versus-container reading of an ORDINARY field is stated at
prefixes fitting the container's domains, and a container-recursive
field's domain is the container's carrier — so the comparison is
available below that carrier and not above it.  (The existing
two-copies transfer carries the same premise, independently.)  The
repair was set-theoretic and local, and it is made: (B-below) is proved
at the tuple layer and at an index set, and the identification takes
its agreement below the container's own wide carrier.

**(ii) and (iii) The fit equivalence.**  With the bound in place, `hΦ`
reduces to a FIT equivalence, one clause per class of the container: a
spine fits the block's copy of class `i` at the joined tuple exactly
when it is the container's own class fit at the free tuple.  It splits
in two:

* at the container's **members** the block records the comparison
  directly — a copy of a member is a copy of the group the worklist
  minted, and the group carries the container's constructors
  instantiated at the pin's components.  This half is PROVED, at one
  constructor and at the whole group: at the wide width the two arms
  for a container-recursive field (at a member, and at one of the
  container's own pins) collapse into one, because the container's own
  pin is a variable on both sides.  What the group's wrapper reads off
  the instance beyond what the narrow one read is two facts about the
  instance map: a container-recursive field at one of the container's
  own pins lands on the image of that class, and a rewritten
  container-ordinary field lands OUTSIDE the instance, where the joined
  tuple is the block's own carrier and the run's entry applies
  verbatim.  The entries are needed at the second kind of field only;
* at the copies of the container's **own pins** it does not.  Such a
  copy belongs to a group of its own, whose container is the pin's
  container `K`, not the container `J` whose instance is being
  identified; and `J`'s own pin record is `K`'s constructors
  instantiated at `J`'s components.  So both sides are copies of ONE
  container at two instantiations, and the comparison is the transfer
  between two copies rather than a fact the run states about either.
  This half is now the transfer applied once per direction, whose
  conclusion at a pin class IS the container's class fit, with premises
  symmetric in the two sides: each side's slots inside the container's
  domains, each side's own entries at its rewritten ordinary fields,
  and the two tuples agreeing at every recursive field's target.

**The identification is assembled.**  The two halves, the agreement's
reduction to them, the reindexing and the congruence below a common
bound compose into one theorem: a pin's carrier at the block's carrier
is its container's least tuple, with the container's side read entirely
off its stored model.  What is not yet done is reading its inputs off
the RUN, and one obstacle there is now exactly located.  The instance
map itself is recorded: the checker computes, for each copy, which of
its container's own pins each of its fields lands on, and that a
rewritten ordinary field lands outside the instance.  But a container's
own pins are counted TWICE in the tree and the two counts have never
been tied together — once by position in the table the checker reads
off the container's mimic recursors, and once by position in the
container's stored block model, which is where the identification's
reindexing has to be stated.  The bridge between the two used to say only
that each table entry is SOME model pin, not WHICH; it now also says
which, position by position, and that repair recorded nothing new — the
checker already certifies the table at the container's own
instantiation to be the recorded pin list verbatim, and moving it to
another instantiation is a map, so the position was there to be kept
and was being thrown away.

One arrow further along is now carried too.  To know which of the
container's own pins a field of that container lands on, one reads the
field's stored domain and finds its spine in the table.  Two facts make
that work, and both are facts the checker establishes about the block it
is INSTALLING rather than about a container installed earlier: that a
container's own pins are spelled differently from one another, and that
a member's field spine IS its pin.  Both now travel on a container's
block model, the way the table already did.  The second was the more
expensive: what the model held was that such a field's arguments MENTION
a member of the group, which is enough to know a pin was minted and not
enough to say which, and strengthening a mention to the spine itself
meant carrying head, arguments and a DEFINITE lift depth down from the
restore, where they are all still visible, through every tier in
between.  The carry turned out to be cheap where it looked expensive:
the restore's own walk already hands the restored domain as the pin
lifted past the field's binders, and it was the tiers above that were
throwing head and depth away — because their only consumer was a
mention, and a mention survives any lift.  What the new consumer needs
is an EQUATION, and an equation does not.

The two spellings of "the container's own scope" then have to be shown
to agree, and they do: the reader instantiates a field's cut with the
parameter openers reversed from the depth the field's earlier binders
add, and the model closes a recorded pin over the parameters and reopens
it at the descending cuts.  Both send the `i`-th parameter to the `i`-th
opener, so on a pin — closed, standing in the parameter context — they
compute the same expression.

A third fact of the same family travels with them, and it is the one
that is easiest to believe already recorded.  The table a consumer looks
a field's spine up in is written in the container's own scope, at
synthetic parameter variables — so its entries are the recorded pins
with every parameter variable's TYPE ANNOTATION replaced by a stand-in.
Erasing annotations is not injective in general, so "the container's
pins are spelled differently from one another" does not by itself say
that the table's entries are; what makes it true here is that a pin's
variables are the block's own parameter openers, so a given position
carries one annotation throughout and the erasure loses nothing.  That,
too, is a fact about the block's own installation, and it is carried the
way the other two are.

What is still to be built is the consumer: the reindexing itself, as
clauses on the object that holds a block's own pins, and the two sites
that would switch to it.  Until those land the tree still takes the long
way round (Resolution 3) there.

**The instance map is not an injection, and the identification no
longer asks it to be.**  The expansion's dedup by pin expression
identifies two of the container's own pins whenever they instantiate
alike, and a three-line block exhibits it.  The comparison is
therefore stated on the tuples constant along the matching's fibres
rather than on an injective segment, and the container's operator's
rows are constant there — a fact about a type already installed,
proved from the copies' constructor data and produced from the same
two inputs as the fit at those classes.

That agreement is exact in its domain, and the domain is where the
fixpoint theory reads it: the tuples of the container's own wide
space, constant along the fibres, below the container's own carrier —
the same three conditions the fit carries.  Outside them it is FALSE
rather than merely unproved, so the earlier free-tuple form of the
hypothesis could have had no producer.  One consequence survives as an
obligation of its own: the container's carrier's own fibre-constancy,
which the fixpoint law used to hand back for free and which now needs
either a meet over each fibre or the pins' entry law at the two
identified pins.

(The colliding shape is also one this checker rejects today, in its
model generator rather than in its kernel, so no accepted stream
exhibits it yet.)

Beyond these three the residue is unchanged: the component family at
instance roots whose components mention other pins, an induction over
instances, and the declaration-order record for cross-instance
constant-headed edges — and the exact cost of that residue, in
particular whether the closure's identification is as cheap as the
experiment suggests once the readings are threaded.

The induction over instances is not something the identification can
absorb, and the reason is worth stating because it is easy to hope
otherwise.  The identification hands back an EQUALITY — a pin's slot is
its container's least tuple at the pin's components — so the inclusion
the block-model construction consumes at that pin is immediate from it,
with no ordering among the pins of one instance.  But the identification
itself is stated with the copies' ENTRY identities as a hypothesis, and
it spends them at exactly one place: a rewritten container-ordinary
field, whose target lies outside the instance.  Those entries are what
the inclusion produces.  So the identification at one instance consumes
the inclusion at pins of OTHER instances, and the induction over
instances is the thing that must still supply them.  What the
identification removes is the ordering WITHIN an instance, and nothing
more.

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
   new object every design needs; it now exists (`RewriteRel` and its
   transport, §6).  This is why the whole-space agreement that is
   definitional in the pure experiment is an *instantiation law* in the
   tree.
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

