#import "../lib.typ": *

#let Sort = $sans("Sort")$
#let red = sym.arrow.r.squiggly
#let pt = $sans("pt")$
#let Mod = $op("Mod")$
#let Val = $op("Val")$
#let Asm = $op("Asm")$
#let Acc = $op("Acc")$
#let Fl = $op("Fl")$
#let Cmp = $op("Cmp")$
#let Valid = $op("Valid")$
#let Checked = $op("Checked")$
#let Compared = $op("Compared")$
#let Pass = $op("Pass")$
#let New = $op("New")$
#let Decl = $op("Decl")$
#let Prf = $op("Prf")$
#let One = $op("One")$
#let refines = sym.prec.eq
#let agr = $scripts(asymp)$

= Checking module by module <sec:modular>

A module is checked against the views its imports present. These may
hide definition values or theorem proofs, so the environment used to
check an imported declaration can differ from the environment in
which it is used. We show how local checks nevertheless give each
module a model, with agreement on shared constants. The argument
first uses an abstract interface; we then supply it from the
set-theoretic models of §3 and §4.

== Environment models in the abstract <sec:mod-iface>

Let $C$ be the context of the module we are checking, built from a
family of views $(E_x)_(x in X)$ its imports present. To check the declarations,
we need a model of $C$ that preserves the values already assigned by
the imports' models. This requires agreement wherever two sources
store a name of $C$.

In general, write
#src("whitepaper/Fragment/ModularSemantics.lean", 104, 120)[$c in E$]
when an environment $E$ stores a name $c$, and $Mod(E)$ for its models.
A model $m in Mod(E)$ assigns each name $c in E$ a value $m(c) in Val$;
all proofs will receive one distinguished value $pi in Val$.
Models $m in Mod(E)$ and $m' in Mod(E')$
#src("whitepaper/Fragment/ModularSemantics.lean", 94, 100)[_agree on_]
an environment $C$ when they give the same value to every name of $C$
that both $E$ and $E'$ store:
$
  m agr_C m' quad :<==> quad
    forall c in C. thin c in E and c in E' ==> m(c) = m'(c).
$
A family of models $(m_x in Mod(E_x))_(x in X)$ is _compatible for
$C$_ when $m_x agr_C m_y$ for all $x,y in X$.

#definition(name: "The model interface")[
  A consistency proof must provide
  #src("whitepaper/Fragment/ModularSemantics.lean", 121, 139)[three laws].
  An _assembly_ relation identifies contexts built from source
  environments, with every stored name supplied by a source:
  $
    Asm(C,(E_x)) ==> forall c in C. thin exists x in X. thin c in E_x.
  $
  _Amalgamation_ turns source models compatible for $C$ into a model
  of $C$ that agrees on $C$ with each of them:
  $
    Asm(C,(E_x)) and (forall x,y in X. thin m_x agr_C m_y) ==>
    exists m_C in Mod(C). thin forall x in X. thin m_C agr_C m_x.
  $
  Finally, for environments $Gamma$, $Gamma'$ and declaration data $D$,
  acceptance of $D$ over $Gamma$, producing $Gamma'$, must give a
  _conservative step_. If $Fl(D)$ is the set of names $D$ flags as
  proofs, then
  $
    Acc(Gamma,D,Gamma') ==> forall m in Mod(Gamma). thin
      exists m' in Mod(Gamma'). \
    (forall c in Gamma. thin m'(c) = m(c)) and
    (forall c in Fl(D). thin m'(c) = pi).
  $
] <def:mod-iface>

The step must extend _every_ context model. For example, a context
assuming a name $c : sans("Nat")$ can receive $c$'s value $5$ from an import.
Adding an axiom $c = 0$ would leave some model, but none preserving
that imported value. The conservative step excludes this extension.

An environment $V$
#src("whitepaper/Fragment/ModularSemantics.lean", 145, 146)[_refines_]
an environment $E$, written $V refines E$, when it is assembled from $E$ alone.
Amalgamation of the one-source family then
#src("whitepaper/Fragment/ModularSemantics.lean", 150, 160)[restricts]
any model $m in Mod(E)$ to a model of $V$, preserving the value $m(c)$
at every $c in V$
(and assembly ensures $c in E$).
Amalgamation of the empty family supplies a model for any context
assembled from no sources.

== Developments

Number modules by natural numbers. For
#src("whitepaper/Fragment/ModularSemantics.lean", 166, 174)[module $i in NN$],
write $Gamma_i$ for its context, $D_i$ for its declarations and $E_i$
for its own environment, which is to be validated.
Its sources form a list $X_i$ of pairs $(j,V)$ of a module $j in NN$
and a view $V$ read from module $j$. Each source must refine its module's own environment,
so that the model can be restricted to what the importer reads.
Module numbers will place imports before importers.

Module $i$ records each occurrence of a name $c$ as either
#src("whitepaper/Fragment/ModularSemantics.lean", 180, 181)[_declared by_]
one module $h in NN$, written $Decl_i (c,h)$, or a
#src("whitepaper/Fragment/ModularSemantics.lean", 183, 184)[_proof of_]
one statement $s$, written $Prf_i (c,s)$. The two possibilities are disjoint.
The occurrences $(i,c)$ and $(j,c)$ of $c$ in modules $i$ and $j$ are
#src("whitepaper/Fragment/ModularSemantics.lean", 186, 191)[_interchangeable_]
when these records agree:
$
  (i,c) approx (j,c) quad :<==> quad
    (exists h. thin Decl_i (c,h) and Decl_j (c,h)) or
    (exists s. thin Prf_i (c,s) and Prf_j (c,s)).
$
For each name this is an
#src("whitepaper/Fragment/ModularSemantics.lean", 206, 211)[equivalence relation].
Statements need no structure yet; the set-theoretic instance uses the
level parameters and type, compared syntactically. Comparisons always
use the same name in both environments.

== Validity

To amalgamate the sources' models for module $i$, their copies of a
context name must be interchangeable with $i$'s occurrence. For an
environment $E$, abbreviate assembly of $E$ from the views in $X_i$ by
$Asm_i (E)$, and write
#src("whitepaper/Fragment/ModularSemantics.lean", 219, 225)[$One_i (E)$]
for this _one-copy condition_:
$
  One_i (E) quad :<==> quad forall c in E. thin forall (j,V) in X_i. thin
    c in V ==> (i,c) approx (j,c).
$
A module may either check its declarations over the assembled context,
or obtain its whole own environment by comparison with its sources.
The latter case will serve challenge–solution comparison.

#definition(name: "Valid module")[
  The #src("whitepaper/Fragment/ModularSemantics.lean", 227, 246)[validity conditions]
  are
  $
    New_i & :<==> forall c in E_i without Gamma_i. thin
      Decl_i (c,i) or (c in Fl(D_i) and exists s. thin Prf_i (c,s)), \
    Checked_i & :<==> Asm_i (Gamma_i) and One_i (Gamma_i)
      and Acc(Gamma_i,D_i,E_i) and New_i, \
    Compared_i & :<==> Asm_i (E_i) and One_i (E_i), \
    Valid_i & :<==> (forall (j,V) in X_i. thin j < i and V refines E_j) \
      & quad and (Checked_i or Compared_i).
  $
] <def:valid>

The source condition makes induction and restriction possible. The
condition $New_i$ ensures that a checked module introduces only its
own declarations or proofs whose value the step fixes to $pi$.

== Compatible models and the theorem <sec:mod-thm>

The induction must construct models together with their agreement.
For $k in NN$, a family $m_i in Mod(E_i)$, for $i < k$, is
#src("whitepaper/Fragment/ModularSemantics.lean", 251, 255)[_compatible_]
when interchangeable occurrences have equal values and every proof
has value $pi$:
$
  Cmp_k ((m_i)) quad :<==> quad
  & (forall i,j < k. thin forall c in E_i. thin c in E_j and
    (i,c) approx (j,c) ==> m_i (c) = m_j (c)) \
  & and (forall i < k. thin forall c in E_i. thin forall s. thin
    Prf_i (c,s) ==> m_i (c) = pi).
$
The proof clause permits independent proofs of the same statement
under the same name, without comparing their bodies.

Compatibility concerns values because hidden bodies can refer to
names that have a different meaning in the importer. Let module $j$
define names $d := 0$ and $c := d$, presenting only $c : sans("Nat")$ as
an assumption. Module $k$ reads all of $j$, proves $e : c = 0$ by
unfolding, and presents $c$ and $e$ as assumptions. Independently,
module $l$ defines $d := 1$. A module $i$ importing $k$ and $l$ sees
$c : sans("Nat")$, $e : c = 0$ and $d := 1$. The two definitions of
$d$ never meet in a context. Restoring $c := d$ in $i$ would make it
unfold to $1$, contradicting $e$; a model instead takes $c$'s value
from $j$ and $d$'s from $l$. There is no combined environment of
bodies and no renaming of names.

#theorem(name: "Modular checking")[
  For every $k in NN$, if the modules $i < k$ are valid, they have a
  #src("whitepaper/Fragment/ModularSemantics.lean", 301, 305)[compatible family of models]:
  $
    (forall i < k. thin Valid_i) ==> \
      exists (m_i in Mod(E_i))_(i < k). thin Cmp_k ((m_i)).
  $
] <thm:mod>

#proof[
  Induct on $k$, starting with the empty family. For each source
  $(j,V) in X_k$, restrict the earlier model $m_j$ to $V$. Whenever
  two sources store a name $c$ of the target, the one-copy condition
  makes their occurrences interchangeable through $(k,c)$.
  Compatibility of the earlier family therefore makes the restricted
  models compatible for that target.

  If $k$ is checked, amalgamate to obtain a model of $Gamma_k$, then
  extend it by the conservative step. If $k$ is compared, amalgamate
  directly to obtain a model of $E_k$.

  It remains to preserve compatibility. A name inherited from a
  source keeps that source's value, hence agrees with all earlier
  interchangeable occurrences. A new proof gets $pi$, as earlier
  proofs do. A name declared by $k$ has no earlier interchangeable
  occurrence: validity
  #src("whitepaper/Fragment/ModularSemantics.lean", 273, 287)[bounds declaring modules]
  by the module storing the name. This bound follows by strong
  induction, tracing an inherited name to an earlier source; a new
  non-proof name is declared by the current module itself.
  These cases also show that every proof in $E_k$ has value $pi$,
  giving both clauses of $Cmp_(k+1)$.
]

Taking $k = i+1$ and forgetting compatibility gives
#src("whitepaper/Fragment/ModularSemantics.lean", 395, 399)[a model of each $E_i$]
whenever every module through $i$ is valid.

== The set-theoretic instance <sec:mod-instance>

We now supply @def:mod-iface using the models of §3 and §4. Write
$E(c)$ for the entry an environment $E$ stores under a name $c in E$; it has level parameters
$arrow(p)$, a type $T$ and a kind. An
#src("whitepaper/Fragment/Env.lean", 83, 86)[_assumption_]
retains just the parameters and type. Its model obligation is the
typing law of @def:model, with no unfolding law.
The instance's #src("whitepaper/Fragment/ModularInstance.lean", 61, 82)[value $m(c)$]
of a model $m$ at a name $c$ is the function assigning $c$ its set at every list of concrete levels;
$pi$ is the constant function with value $pt$.

*Assembly.* An entry's laws transfer when everything they read is
read alike. Accordingly,
#src("whitepaper/Fragment/ModularModel.lean", 225, 236)[assembly]
requires each $C(c)$, for $c in C$, to come from some source $E_x$ at the same name,
either unchanged or as an assumption of the same parameters and type
(#src("whitepaper/Fragment/Modular.lean", 23, 26)[entry refinement]).
The #src("whitepaper/Fragment/ModularModel.lean", 192, 195)[common part]
$E_x^C$ consists of $E_x$'s entries at names also stored by $C$.

The retained entry must be
#src("whitepaper/Fragment/ModularModel.lean", 210, 223)[in scope in this common part]:
its type and any retained value or rule body are closed, mention only
constants in the common part and use only the entry's declared level
parameters, as in §3 and §4. A recursor's rules must also read the same constructor
entries in source and target, with their types in scope. Hiding a
value removes its unfolding law and therefore its value dependencies;
an assumption needs only its type's dependencies.

For a retained plain type former (one without nesting), assembly also
requires the block's
#src("whitepaper/Fragment/Decl.lean", 699, 710)[specification scope]
from @sec:ind-checks in the common part, with the type former
and its constructors present there, and their exact generated entries
in $C$. These conditions do not apply when the type
former is hidden as an assumption. The models
#src("whitepaper/Fragment/BlockModel.lean", 46, 66)[retain the block facts]
from @sec:ind-model: scope, generated entries, the constructed family
and constructor sets, and the
#src("whitepaper/Fragment/IndSem.lean", 601, 622)[field universe bound]
at every fitting parameter list, for every family in the result
universe. These facts are needed when a later block uses this one
as a container.

*Amalgamation.* Choose each name's value from any source storing it,
and use $pi$ if no source does. On names of $C$, compatibility makes
this assignment agree with every such source. Interpretation
#src("whitepaper/Fragment/Hygiene.lean", 593, 595)[depends only on mentioned constants],
so scope in the common part transfers the typing, unfolding and
recursor laws. The block facts transfer for the same reason, with
assembly supplying the generated entries in $C$. This
#src("whitepaper/Fragment/ModularModel.lean", 253, 260)[proves amalgamation].
Assembly also #src("whitepaper/Fragment/ModularModel.lean", 374, 386)[makes $C$ closed]:
its stored terms are in scope and its rules name stored constructors,
because each common part is contained in $C$.

*The conservative step.* Definitions and blocks use the installation
results of §3 and §4. A
#src("whitepaper/Fragment/Decl.lean", 608, 618)[theorem $c : T := v$]
passes the definition check and additionally has a propositional type:
$tack T => S red Sort u$ for some type $S$ and level $u$ with $u eq.dot 0$. It is stored as an
assumption of $T$. Installing the checked definition and then
forgetting its value
#src("whitepaper/Fragment/InstallThm.lean", 249, 255)[extends every model],
assigning the theorem the point.

Declaration data consist of a sequential list and proof flags.
#src("whitepaper/Fragment/ModularInstance.lean", 45, 48)[Acceptance]
requires a closed context, the checks of §3 and §4 (or the theorem
check) at each successive declaration, and
#src("whitepaper/Fragment/ModularModel.lean", 87, 92)[justified flags]:
a flagged declaration is a theorem or a definition whose type is
inferred to be a proposition. A flag need not mark every theorem.
The chosen installation assigns such a definition the point
#src("whitepaper/Fragment/ModularModel.lean", 61, 81)[at every list of levels],
even those of the wrong length; the typing law alone constrains only
correctly sized lists. Sequential installation therefore gives
#src("whitepaper/Fragment/ModularModel.lean", 100, 107)[the conservative step],
preserving old values and assigning flagged names $pi$.

== The local checks <sec:mod-local>

For this instance,
#src("whitepaper/Fragment/ModularModel.lean", 403, 404)[$E_i = Gamma_i + D_i$],
the context extended by the declaration list. Each module $i$ presents
a set of views $cal(V)_i$ and imports earlier modules; its sources are
#src("whitepaper/Fragment/ModularModel.lean", 412, 413)[every view of every import],
paired with the module presenting it. The
#src("whitepaper/Fragment/ModularModel.lean", 425, 457)[checks divide by who runs them]:

- At the presenting module, check that each view refines its own
  environment. This runs once, however many modules import it.
- At the importer, check that imports are earlier and the context is
  assembled from their views, with the one-copy condition. This uses
  the context, the views and the records of declaring modules or
  proof statements; it needs no import's own environment.
- For the declarations, check sequential acceptance and proof flags.
  Record each newly declared name as declared by $i$, or, if flagged,
  as a proof of its actual statement $(arrow(p),T)$, its level
  parameters $arrow(p)$ and type $T$.

Alternatively, a module passes by
#src("whitepaper/Fragment/ModularModel.lean", 459, 469)[comparison]:
check its views as above, require earlier imports, and assemble
$E_i$ itself from their views with the one-copy condition.
Write $Pass_i$ for acceptance by either alternative. These concrete
checks #src("whitepaper/Fragment/ModularInstance.lean", 100, 125)[imply abstract validity]:
$
  (forall j <= i. thin Pass_j) ==> Valid_i.
$
The imports' view checks supply source refinement. For a checked
module, context assembly supplies closure, while the records of new
declarations give $New_i$. Thus @def:valid applies, and
@thm:mod #src("whitepaper/Fragment/ModularInstance.lean", 130, 144)[gives compatible models].

#corollary(name: "Consequences of the local checks")[
  Assume $Pass_j$ for every $j <= i$. Then
  #src("whitepaper/Fragment/ModularInstance.lean", 147, 151)[$exists m in Mod(E_i)$],
  and #src("whitepaper/Fragment/ModularInstance.lean", 166, 174)[every stored type is inhabited]
  in such a model, at every correctly sized level instantiation.

  Let $B$ be the empty Prop block of @cor:consistency, with no level
  parameters, parameters, indices or constructors, and with large
  elimination. If $E_i$ stores its generated recursor entry
  $a_B^(sans("rec"))$ under a name $r_B$, then
  #src("whitepaper/Fragment/ModularInstance.lean", 155, 163)[no closed term inhabits its type former $I_B$]:
  $
    E_i (r_B) = a_B^(sans("rec")) ==> forall e. thin
      not (tack e => I_B) "over" E_i.
  $
] <cor:mod>

Model existence follows from @thm:mod; inhabitation is the model's
typing law. The last claim is the recursor argument of
@cor:consistency, which uses only the existence of a model.

== What runs in parallel

The local checks read a module and its imports' views, so modules can
be checked together once those data are available. Acceptance still
requires every relevant module to pass. The
#src("whitepaper/Fragment/ModularSemantics.lean", 316, 352)[model construction]
has the same dependencies: restrict the imports' models, amalgamate,
and extend for checked declarations. Its compatibility proof uses
the earlier family too, but the numbering adds no inputs to the
construction of a module's model.

== Comparing a module <sec:mod-compare>

A _challenge_ specifies required constants; its assumptions are
_holes_, fixing level parameters and types. A solution supplies
entries at the same names. Represent it by an earlier module offering
the needed views, and record the challenge's occurrences as the
solution does. The comparison alternative checks assembly of the
challenge's whole own environment, including specified values and
rules. An assumption may be filled by any kind of entry with the
required type; a retained non-assumption must agree exactly.

Assembly checks dependencies and block conditions as above, and supplies
a model directly, so the challenge's declarations need no separate
type check. If the relevant modules pass, @thm:mod gives models
agreeing on interchangeable occurrences, and @cor:mod makes every
hole's type inhabited in the challenge's model. A challenge storing
the empty Prop block's recursor therefore cannot also have a hole of
that proposition's type and pass with an accepted solution.

#remark(name: "A syntactic illustration")[
  The #src("whitepaper/Fragment/ModularSyntactic.lean", 83, 91)[models]
  may instead be realisations by terms of a fixed ground theory:
  each constant is assigned a term of its realised type, equal to
  its realised value when a definition. Compatible realisations
  #src("whitepaper/Fragment/ModularSyntactic.lean", 176, 183)[amalgamate]
  by choosing a source term for each name. The
  #src("whitepaper/Fragment/ModularSyntactic.lean", 130, 135)[step]
  realises a fresh definition by its value under the old realisation;
  a substitution lemma gives its typing. This
  #src("whitepaper/Fragment/ModularSyntactic.lean", 212, 234)[instance]
  handles definitions only, with no flagged proofs. It illustrates
  the interface; connecting a syntactic consistency proof of Lean
  would require a separate argument, including the shared proof value.
]

== Lean's module system in these terms <sec:mod-lean>

The table maps Lean's module system to the notions above. An exported
level need not be self-contained; a view used in assembly must
satisfy the scope conditions.

#table(
  columns: (1fr, 1fr),
  stroke: none,
  table.header[*Lean*][*Here*],
  [An exported level, with the imported dependencies of retained
    types and values],
  [A view retaining entries whose laws have the required dependencies;
    a value may be hidden while its type is kept],
  [The private level, available under `import all`],
  [Full own declarations; with their context, they can supply the own
    environment as a view],
  [The language server's level], [No role in the argument],
  [Imports and modules reached through `public import` re-exports],
  [The modules supplying the sources],
  [The environment built from the loaded levels], [The context $Gamma_i$],
  [An unavailable theorem proof or hidden definition value],
  [An assumption of the same type; a theorem may carry a proof flag],
  [Copies merged on import, allowed for theorems of the same statement],
  [Interchangeable occurrences of the same name],
  [Declarations of one name never loaded together],
  [Different declaring modules; compatibility imposes no equality],
  [A private name `_private.…`], [An ordinary name with its declaring module
    or proof statement],
  [An exported value mentioning a non-exported constant],
  [Retain the value where its dependencies are available; otherwise
    retain an assumption if its type is complete, or omit the entry],
  [`backward.privateInPublic`, which can export private constants],
  [Additional entries available to satisfy view dependencies],
)

#real[
  Con-leche chooses how each imported constant appears in the context:
  in full, as an assumption, or omitted. This depends on
  #src("ConLeche/Cached/ModStore.lean", 143, 167)[what its retained laws read]:
  types, values, rules, block entries and projection data, including
  dependencies from pinned operations. The importer checks where
  these dependencies come from and that all copies it sees are
  interchangeable. Hiding a value removes its unfolding dependencies.

  One mode checks modules through views of a shared store of installed
  constants. With `--modular=isolated`, each module is
  #src("ConLeche/Cached/ModIso.lean", 280, 286)[checked over its own context],
  using exported data and the private data available under `import all`.
  The #src("ConLeche/Cached/ModIso.lean", 54, 73)[form of an imported constant]
  depends on that level and the availability of dependencies. The
  #src("ConLeche/Verify/Modular/Interface.lean", 150, 171)[verified local checks]
  connect these choices to the theorem. Provided the store lists every
  constant under its name in module order, the two computations
  #src("ConLeche/Verify/Modular/IsoCtx.lean", 575, 587)[give the same verdict],
  placing installed constants over the isolated context.

  With `--compare CHALLENGE SOLUTION`, con-leche compares as in
  @sec:mod-compare and lists the holes. The test suite checks compatibility with Lean
  on accepted developments.

  Con-leche's #src("ConLeche/MainTheorem.lean", 131, 145)[modular theorem]
  applies the #src("ConLeche/Modular/Generic.lean", 302, 306)[generic theorem]
  to #src("ConLeche/Model/Modular/Instance.lean", 244, 264)[its model instance].
  Values are semantic terms indexed by level valuations. Each source
  is an earlier module's own environment exposing only the names the
  importer reads alike; amalgamation chooses values from these sources.
  Proof statements consist of level parameters and types. The home
  check justifies a proof flag for a theorem, or for a definition or
  opaque constant whose type is inferred to be a proposition.
]
