#import "../lib.typ": *

#let Sort = $sans("Sort")$
#let red = sym.arrow.r.squiggly
#let pt = $sans("pt")$
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked
#let St = $op("St")$
#let Mod = $op("Mod")$
#let Val = $op("Val")$
#let Name = $op("Name")$
#let Env = $op("Env")$
#let Decls = $op("Decls")$
#let Asm = $op("Asm")$
#let Acc = $op("Acc")$
#let Fl = $op("Fl")$
#let Sc = $op("Sc")$
#let Cl = $op("Cl")$
#let BSc = $op("BSc")$
#let Cmp = $op("Cmp")$
#let Valid = $op("Valid")$
#let Checked = $op("Checked")$
#let Compared = $op("Compared")$
#let DeclsOk = $op("DeclsOk")$
#let Pass = $op("Pass")$
#let New = $op("New")$
#let Check = $op("Check")$
#let Flags = $op("Flags")$
#let PropTy = $op("PropTy")$
#let Closed = $op("Closed")$
#let imp = $op("imp")$
#let names = $op("names")$
#let home = $sans("home")$
#let prf = $sans("proof")$
#let refines = sym.prec.eq

= Checking module by module <sec:modular>

Large developments are divided into modules so that each part can be
checked once against what its imports make available. Independent
modules can then be checked in parallel. In Lean, importers see the
statements of theorems and may also see definitions without their bodies.

We show that if every module passes its local checks, every module's
environment has a model, and these models agree wherever modules share
a constant. In the set-theoretic instance, no module can then prove an
empty proposition whose generated recursor it stores (@cor:mod).

We first state what the argument needs from environment models, then
define modules and their checks. The theorem also explains parallel
checking and comparison with a solution; @sec:mod-lean gives the
mapping to Lean's module system.

== Environment models in the abstract <sec:mod-iface>

Fix a type $Env$ of environments and a type $Name$ of constant names. Write
#src("whitepaper/Fragment/ModularSemantics.lean", 95, 96)[$St(E) subset.eq Name$]
for the names an environment $E$ stores. No structure on stored
entries is needed yet.

A consistency proof supplies a type $Mod(E)$ of models and a type
$Val$ of values, with each model $m$ assigning a value $m(c)$ to every
name. The modular argument uses only the laws stated below.

For a family $(E_x)_(x in X)$ and a target environment $C$, a
_designation_ is a relation $sigma subset.eq Name times X$.
The assertion $sigma(c,x)$ designates source $x$ for the name $c$;
assembly will also require a designated source that stores the name.

#definition(name: "Compatible for an environment")[
  Given models $m_x in Mod(E_x)$ with values $m_x (c) in Val$, define
  $
    Cmp_C^sigma ((m_x)) quad :<==> quad
      forall c in St(C). thin forall x,y in X. quad
      sigma(c,x) and sigma(c,y) and c in St(E_x) inter St(E_y)
      ==> m_x (c) = m_y (c).
  $
] <def:compatible-for>

Agreement is required on names the target stores, so that a model of
the target can preserve the values of all designated sources.

#definition(name: "What a consistency proof provides")[
  The #src("whitepaper/Fragment/ModularSemantics.lean", 88, 127)[interface]
  consists of the following data and laws.

  + *Models and values.* For each environment $E$, a type $Mod(E)$,
    an operation giving a value to each name, and a distinguished
    proof value:
    $
      m in Mod(E), c in Name |-> m(c) in Val, quad pi in Val.
    $
  + *Assembly.* A relation $Asm(C,(E_x),sigma)$ satisfying
    $
      Asm(C,(E_x),sigma) ==> forall c in St(C). thin
        exists x in X. thin sigma(c,x) and c in St(E_x).
    $
  + *Amalgamation.* For every family $m_x in Mod(E_x)$,
    $
      Asm(C,(E_x),sigma) and Cmp_C^sigma ((m_x)) ==> \
      exists m_C in Mod(C). thin forall c in St(C). thin forall x in X. quad
        sigma(c,x) and c in St(E_x) ==> m_C (c) = m_x (c).
    $
  + *A conservative step.* A type of declaration data $D$, a set
    $Fl(D) subset.eq Name$ of flagged names, and an acceptance
    relation $Acc(Gamma,D,Gamma')$ satisfying
    $
      Acc(Gamma,D,Gamma') ==> forall m in Mod(Gamma). thin
        exists m' in Mod(Gamma'). \
      (forall c in St(Gamma). thin m'(c) = m(c)) and
      (forall c in Fl(D). thin m'(c) = pi).
    $
] <def:mod-iface>

For an illustration of why the step must extend _every_ model, let
$Gamma$ assume $c : sans("Nat")$ and let $m$ interpret $c$ as $5$,
as an imported definition $c := 5$ requires. Adding an axiom stating
$c = 0$ gives $Gamma + D$ a model, but none that extends $m$. A step
that guaranteed only some model of $Gamma + D$ could therefore change
an imported value and prevent amalgamation with the imports' models.

Assembly describes which parts of the sources the target retains,
so its definition belongs to the particular consistency proof.
Amalgamation must preserve every designated source's value; the step
then preserves the particular context model obtained this way.

#definition(name: "Refinement")[
  An environment $Gamma$
  #src("whitepaper/Fragment/ModularSemantics.lean", 133, 135)[_refines_]
  $E$ when it is assembled from $E$ alone, with every name designated:
  $
    Gamma refines E quad :<==> quad
      Asm(Gamma,(E)_(x in {*}),Name times {*}).
  $
] <def:refines>

#lemma(name: "Restriction")[
  Refinement gives
  #src("whitepaper/Fragment/ModularSemantics.lean", 139, 147)[restriction of models]:
  $
    Gamma refines E ==> St(Gamma) subset.eq St(E) and \
      forall m in Mod(E). thin exists m' in Mod(Gamma). thin
        forall c in St(Gamma). thin m'(c) = m(c).
  $
] <lem:restrict>

#proof[
  The inclusion follows from the source property of assembly. The
  one-member family $(m)$ is compatible because its source indices
  are equal, so amalgamation gives the required restriction $m'$.
]

The empty family is compatible too. Thus an environment assembled
from no sources has a model:
$
  Asm(C,(),emptyset) ==> exists m in Mod(C).
$
This supplies the initial case whenever an instance assembles an empty
context from no imports.

A small syntactic instance also satisfies the interface
(@rem:mod-syntactic). We return to it after the modular argument.

== Environments of modules <sec:mod-env>

A module has a _context_ $Gamma_i$, an environment containing the
constants available to its declarations, and an _own environment_
$E_i$ containing its context and declarations. The module context
$Gamma_i$ is an environment of constants; the variable contexts
$Gamma$ of §2 are a separate notion.

A _view_ is an environment the module presents to importers. It may
omit entries or hide information, provided it refines the own
environment, so that its models can be obtained by restriction.

#definition(name: "Development")[
  A #src("whitepaper/Fragment/ModularSemantics.lean", 155, 164)[development]
  assigns the following data to each $i in bb(N)$:
  $
    & imp_i in op("List")(bb(N)), quad Gamma_i,E_i in Env, \
    & D_i in Decls, quad cal(V)_i in op("List")(Env), \
    & kappa_i : Name -> {home(j) mid(|) j in bb(N)}
      union {prf(s) mid(|) s in cal(S)}.
  $
  Here $cal(S)$ is a type of statements, and the two forms of
  #src("whitepaper/Fragment/ModularSemantics.lean", 81, 86)[key]
  are disjoint.
] <def:development>

For a fixed name $c$, equal keys identify its occurrences in different
modules. The identifier is the pair $(c,kappa_i (c))$: all ordinary
constants declared by module $j$ have key $home(j)$. Different names
with that key are still different constants.

Proofs may instead have a statement key $prf(s)$. The theorem will
ensure that every stored name with such a key has value $pi$.
The abstract argument imposes no structure on $s$. In the
set-theoretic instance below, it is the pair of level parameters and
type, compared syntactically.

Every comparison uses the same name in both environments. A context,
an own environment or a view may contain constants imported from
several modules. There is no combined environment for the whole
development, and no renaming of constants is assumed.

=== Assembly for the set-theoretic model

Fix the set theory and level oracle assumed in §2 and §4. We now give
the instance for the environments of §3 and §4. A stored
entry $a$ has level parameters $arrow(p)_a$, type $T_a$ and kind
$K_a$; write $E(c) = a$ for its lookup. We use this entry notation
only for this instance.

An #src("whitepaper/Fragment/Env.lean", 83, 86)[_assumption_]
has a type and no value, so its only model obligation is the typing
law of @def:model and it has no $delta$ rule.

To transfer an entry's model laws, we require its dependencies to have
the same values in the source and target. For a definition, hiding the
value removes the unfolding law, so only the type's dependencies need
to remain.

#definition(name: "Refinement of constants")[
  For two stored entries, define
  #src("whitepaper/Fragment/Modular.lean", 23, 26)[refinement] by
  $
    a <= b quad :<==> quad a = b or
      (K_a = sans("assumed") and arrow(p)_a = arrow(p)_b and T_a = T_b).
  $
] <def:const-le>

Thus an assumption can replace a definition, a type former, a
constructor or a recursor with the same level parameters and type.
A retained entry that is not an assumption must equal its source entry.

*Scope and the common part.* For a term $e$, environment $A$, level
parameters $arrow(p)$ and available variables $Delta$, write
#src("whitepaper/Fragment/Decl.lean", 580, 584)[$Cl(A,arrow(p),Delta,e)$]
for
$
  Cl(A,arrow(p),Delta,e) quad :<==> quad
    op("FV")(e) subset.eq Delta and
    op("consts")(e) subset.eq St(A) and
    op("lparams")(e) subset.eq {arrow(p)}.
$
The three sets collect free variables, constant names and level
parameters; taking $Delta = emptyset$ requires a closed term.

For sources $(E_x)$ designated by $sigma$ for $C$, the
#src("whitepaper/Fragment/ModularModel.lean", 189, 193)[common part]
is
$
  E_x^C = E_x "restricted to" {c in St(C) mid(|) sigma(c,x)}.
$
It retains source entries at names the target stores under the source's
meaning. The entries themselves may differ, since the target may hide
a definition's value.

For assumptions, definitions, constructors and recursors, define the
#src("whitepaper/Fragment/ModularModel.lean", 208, 221)[scope needed by an entry's laws]
by
$
  Sc(A,C,a) quad :<==> quad
    & Cl(A,arrow(p)_a,emptyset,T_a) \
    & and (forall v. thin K_a = sans("defn")(v)
      ==> Cl(A,arrow(p)_a,emptyset,v)) \
    & and (forall R. thin K_a = sans("recursor")(R) ==> \
    & quad forall (d,r) in R. thin Cl(A,arrow(p)_a,emptyset,r) and \
    & quad exists b. thin A(d) = b and C(d) = b
      and Cl(A,arrow(p)_b,emptyset,T_b)).
$
A rule $(d,r)$ names a constructor and a right-hand side; the
recursor's other stored counts are left implicit. Requiring
$A(d) = C(d)$ makes the rule read the same constructor entry in both
environments. The additional clause for type formers is given below.

#definition(name: "Assembly")[
  Write $I_B$ for a block's name, $c_d$ for constructor specification
  $d$'s name, and $a_B$, $a_(B,d)$ for their generated entries
  (@sec:ind-checks). A block is _plain_ when it has no nesting.
  Using the full scope predicate $Sc$, including its type-former
  clause below, the instance's
  #src("whitepaper/Fragment/ModularModel.lean", 223, 235)[assembly relation]
  is
  $
    Asm(C,(E_x),sigma) quad :<==> quad
    & (forall c in St(C). thin exists x in X. thin
      sigma(c,x) and c in St(E_x) \
    & quad and C(c) <= E_x (c) and Sc(E_x^C,C,C(c))) \
    & and (forall c in St(C). thin forall B. thin
      K_(C(c)) "is a type former for the plain block" B ==> \
    & quad C(I_B) = a_B and
      (forall d in op("ctors")(B). thin C(c_d) = a_(B,d))).
  $
] <def:assembled>

The first clause checks the dependencies of the retained entry,
so an assumption requires only its type's dependencies. The second
requires exact generated entries for a retained plain block; it does
not apply when the type former is retained as an assumption.

*Inductive blocks.* The scope conditions on a block are those of
@sec:ind-checks, now read in the source environment $A$. Write
#src("whitepaper/Fragment/Decl.lean", 699, 710)[$BSc(A,B)$]
for that specification-scope predicate:
$
  BSc(A,B) quad :<==> quad
    B "satisfies the specification-scope conditions of §4 over" A.
$
This is the entire specification-scope check: the parameter, index
and field scopes, the result sort's level scope, index-list lengths,
the restriction on later fields' dependence on reflexive fields, and
distinct level parameters with a fresh elimination parameter. For a
plain block, the check permits only ordinary and reflexive fields.
For a type former with block $B$, the full entry condition is
$
  Sc(A,C,a) quad :<==> quad
    & Cl(A,arrow(p)_a,emptyset,T_a) \
    & and (B "is plain" ==> BSc(A,B) and I_B in St(A) \
    & quad and (forall d in op("ctors")(B). thin c_d in St(A))).
$

The models used here retain the construction facts of @sec:ind-model,
because a later block may use a plain block as a container.
For each stored plain block $B$, these
#src("whitepaper/Fragment/BlockModel.lean", 46, 66)[additional model laws]
are
$
  & BSc(E,B) and B "has no container fields", \
  & E(I_B) = a_B, quad
    forall d in op("ctors")(B). thin E(c_d) = a_(B,d), \
  & forall arrow(n). thin M(I_B,arrow(n)) = op("family")_B (M,arrow(n)), \
  & forall d in op("ctors")(B). thin forall arrow(n). thin
    M(c_d,arrow(n)) = op("constructor")_(B,d) (M,arrow(n)), \
  & forall arrow(n),arrow(X). thin arrow(X) "fits the parameters of" B ==> \
  & quad B "satisfies the field universe bound of §4 at" (M,arrow(n),arrow(X)).
$
Here $op("family")_B$ and $op("constructor")_(B,d)$ denote the type
former's and constructor's sets constructed in @sec:ind-model. The
#src("whitepaper/Fragment/IndSem.lean", 601, 622)[field universe bound]
is the one stated there for every family in the result universe,
at fitting parameter values. These laws add no new construction;
amalgamation must preserve the existing sets and their bound.

For such a model $m$ with assignment $M$, the abstract values are
$
  Mod(E) = {m mid(|) m "satisfies these model laws over" E}, quad
  m(c) = (arrow(n) |-> M(c,arrow(n))), quad pi = (arrow(n) |-> pt).
$

An environment is
#src("whitepaper/Fragment/InstallDef.lean", 84, 94)[closed]
when its stored terms are in scope and its recursor rules name stored
constructors. Precisely,
$
  Closed(C) quad :<==> quad forall c in St(C). thin
    & Cl(C,arrow(p)_(C(c)),emptyset,T_(C(c))) \
    & and (forall v. thin K_(C(c)) = sans("defn")(v) ==>
      Cl(C,arrow(p)_(C(c)),emptyset,v)) \
    & and (forall R. thin K_(C(c)) = sans("recursor")(R) ==>
      forall (d,r) in R. thin \
    & quad Cl(C,arrow(p)_(C(c)),emptyset,r) and d in St(C)).
$
Assembly #src("whitepaper/Fragment/ModularModel.lean", 374, 387)[implies closure]:
$
  Asm(C,(E_x),sigma) ==> Closed(C).
$
Since each common part is contained in $C$, scope in the common part
implies scope in $C$. This is the closure hypothesis needed by the
declaration step below.

#theorem(name: "Amalgamation")[
  The instance satisfies
  #src("whitepaper/Fragment/ModularModel.lean", 252, 260)[the amalgamation law]:
  $
    Asm(C,(E_x),sigma) and Cmp_C^sigma ((m_x)) ==> \
    exists m_C in Mod(C). thin forall c in St(C). thin forall x in X. quad
      sigma(c,x) and c in St(E_x) ==> m_C (c) = m_x (c).
  $
] <thm:amalg>

#proof[
  For every name with a designated source that stores it, choose one
  source's value. Use $pi$ when there is no such source.
  Compatibility makes the choice agree with every designated source
  on names stored in $C$.

  Take $c in St(C)$ and the source $x$ provided by assembly.
  If $C(c)$ is not an assumption, it equals $E_x (c)$. Its laws read
  only terms and entries covered by $Sc(E_x^C,C,C(c))$. Interpretation
  #src("whitepaper/Fragment/Hygiene.lean", 593, 595)[depends only on mentioned constants],
  and the chosen assignment agrees with $m_x$ on $E_x^C$. Thus the
  typing, unfolding and recursor laws transfer. If $C(c)$ is an
  assumption, only typing transfers; its type and level parameters
  equal those of $E_x (c)$.

  For a retained plain block, scope in the common part makes the
  constructed family, constructors and field bound unchanged by this
  transfer. Assembly's second clause supplies the exact generated
  entries in $C$. These are precisely the additional block facts
  required of $m_C$.
]

=== The step for declarations

A _theorem_ has a statement $T$ and a checked proof $v$. Its statement
must be a proposition. Define
$
  PropTy_E (T) quad :<==> quad exists S,u. thin
    (tack T => S red Sort u) "over" E and u eq.dot 0.
$
The #src("whitepaper/Fragment/Decl.lean", 608, 618)[theorem check]
is the definition check of §3 on $c : T := v$, together with
$PropTy_E (T)$. The stored entry is an assumption with parameters
$arrow(p)$ and type $T$; its proof is not stored.

Installing a theorem
#src("whitepaper/Fragment/InstallThm.lean", 249, 255)[extends a model]
by installing the checked definition and forgetting its value. This
preserves every old constant's value and gives the theorem the point,
because its type is a proposition. More generally, for an accepted
definition with propositional type,
#src("whitepaper/Fragment/ModularModel.lean", 61, 81)[the chosen value satisfies]
$
  PropTy_E (T) ==> forall arrow(n). thin M'(c,arrow(n)) = pt.
$
This holds even on lists of the wrong length, because it is a property
of the chosen installation. A model's typing law by itself constrains
only correctly sized instantiations.

Write $D = (d_1,dots,d_r)$ for a list of declarations, $names(d)$ for
the names a declaration stores, and $p(c)$ for its Boolean proof
flag. Let $Gamma^0 = Gamma$ and let $Gamma^t$ store $d_t$ over
$Gamma^(t-1)$. Thus
#src("whitepaper/Fragment/ModularModel.lean", 404, 410)[$E_i = Gamma_i + D_i$]
in the instance. In the abstract notation $D_i$ includes the flags;
here we display the list and flags separately as $(D_i,p_i)$.

Write $op("Ok")_E (d)$ for the checks of a definition (§3), theorem
(above) or inductive block (§4). The
#src("whitepaper/Fragment/Modular.lean", 200, 209)[sequential check]
and the #src("whitepaper/Fragment/ModularModel.lean", 54, 59)[proof predicate]
are
$
  Check(Gamma,D) & :<==> forall 1 <= t <= r. thin op("Ok")_(Gamma^(t-1)) (d_t), \
  op("Proof")_E (d) & :<==> d "is a theorem" or
    (d "is a definition with type" T and PropTy_E (T)).
$
The #src("whitepaper/Fragment/ModularModel.lean", 85, 90)[flag condition]
and #src("whitepaper/Fragment/ModularInstance.lean", 41, 48)[acceptance]
are
$
  Flags(Gamma,D,p) & :<==> forall 1 <= t <= r. thin
    forall c in names(d_t). thin p(c) = "yes" ==> op("Proof")_(Gamma^(t-1)) (d_t), \
  Fl(D,p) & = {c mid(|) exists d in D. thin c in names(d) and p(c) = "yes"}, \
  Acc(Gamma,(D,p),Gamma') & :<==> Gamma' = Gamma + D and
    Check(Gamma,D) and Flags(Gamma,D,p) and Closed(Gamma).
$
Theorems may be flagged; flags are not required on every theorem.

The installation theorems of §3 and §4 and the theorem step above
#src("whitepaper/Fragment/ModularModel.lean", 100, 107)[give]
$
  Acc(Gamma,(D,p),Gamma') ==> forall m in Mod(Gamma). thin
    exists m' in Mod(Gamma'). \
  (forall c in St(Gamma). thin m'(c) = m(c)) and
  (forall c in Fl(D,p). thin m'(c) = pi).
$
Together with @thm:amalg, this proves that the models just described
#src("whitepaper/Fragment/ModularInstance.lean", 61, 80)[provide the interface]
of @def:mod-iface.

== The local checks <sec:mod-local>

Module $i$ draws from its imports' views. Define its
#src("whitepaper/Fragment/ModularSemantics.lean", 170, 176)[sources and designations]
by
$
  X_i & = {(j,V) mid(|) j in imp_i, V in cal(V)_j}, \
  sigma_i (c,(j,V)) & :<==> kappa_i (c) = kappa_j (c), \
  Asm_i (E) & :<==> Asm(E,(V)_((j,V) in X_i),sigma_i).
$
Matching keys designate a source for a name; assembly then requires
such a source to store the name and satisfy the dependency conditions.

#definition(name: "Valid module")[
  The #src("whitepaper/Fragment/ModularSemantics.lean", 178, 198)[abstract checks]
  are
  $
    New_i & :<==> forall c in St(E_i) without St(Gamma_i). thin
      kappa_i (c) = home(i) or \
      & quad ((exists s. thin kappa_i (c) = prf(s)) and c in Fl(D_i)), \
    Checked_i & :<==> Asm_i (Gamma_i) and Acc(Gamma_i,D_i,E_i) and New_i, \
    Compared_i & :<==> Asm_i (E_i), \
    Valid_i & :<==> (forall V in cal(V)_i. thin V refines E_i)
      and (forall j in imp_i. thin j < i) \
      & quad and (Checked_i or Compared_i).
  $
] <def:valid>

A checked module extends a context model, while a compared module
obtains its model directly from imported views. Both check their own
views and import order, so that restriction and induction apply.

#definition(name: "Local checks")[
  In the set-theoretic instance, put $s(a) = (arrow(p)_a,T_a)$.
  The #src("whitepaper/Fragment/ModularModel.lean", 421, 443)[local checks]
  have three groups: $op("Home")_i$ checks views,
  $op("Import")_i$ checks the context, and $Check$, $Flags$ and
  $op("OwnKeys")_i$ check the declarations. Their conjunction is
  $DeclsOk_i$:
  $
    op("Home")_i & :<==> forall V in cal(V)_i. thin V refines E_i, \
    op("Import")_i & :<==> (forall j in imp_i. thin j < i) and Asm_i (Gamma_i), \
    op("OwnKeys")_i & :<==> forall d in D_i. thin forall c in names(d). thin
      kappa_i (c) = cases(
        prf(s(E_i (c))) & "if" p_i (c) = "yes",
        home(i) & "otherwise"), \
    DeclsOk_i & :<==> op("Home")_i and op("Import")_i and Check(Gamma_i,D_i) \
      & quad and Flags(Gamma_i,D_i,p_i) and op("OwnKeys")_i.
  $
] <def:local>

Write $Pass_i$ when the concrete checks accept module $i$, either
by checking declarations ($DeclsOk_i$) or by comparison:
#src("whitepaper/Fragment/ModularModel.lean", 445, 454)[the two alternatives]
are
$
  Pass_i quad :<==> quad DeclsOk_i or
    (op("Home")_i and (forall j in imp_i. thin j < i) and Asm_i (E_i)).
$
Thus $Pass_i$ concerns the concrete checks, while $Valid_i$ is the
abstract condition used by the theorem. The former
#src("whitepaper/Fragment/ModularInstance.lean", 94, 111)[implies the latter]:
$
  Pass_i ==> Valid_i.
$
For a checked module, assembly makes $Gamma_i$ closed, as acceptance
requires. Every name in $E_i$ outside $Gamma_i$ is declared by $D_i$,
so $op("OwnKeys")_i$ implies $New_i$. The comparison case is immediate.

The check per home reads the module and its views, so it is performed
once however many modules import it. The check per importer uses its
context and keys together with the imports' views and keys; it needs
no access to their own environments.

A hidden definition value contributes no value dependencies, but its
type must still be in scope under matching keys. Similarly, a context may
select only some entries of a view if every retained law's dependencies
and the block conditions remain satisfied. A definition is checked
in its home context, where the values it needs may be visible. An
importer transfers its laws by assembly; it does not recheck the
original value against a context that hides those dependencies.

== The theorem <sec:mod-thm>

The induction constructs models together with their compatibility,
because amalgamation must preserve the imports' values. If two
designated sources store $c$ but give it different values, no target
model can preserve both:
$
  m_C (c) = m_x (c) and m_C (c) = m_y (c) ==> m_x (c) = m_y (c).
$

#definition(name: "Compatible family of a development")[
  For models $m_i in Mod(E_i)$ with $i < k$, define
  #src("whitepaper/Fragment/ModularSemantics.lean", 200, 207)[compatibility]
  by
  $
    Cmp_k ((m_i)) quad :<==> quad
    & (forall i,j < k. thin forall c in St(E_i) inter St(E_j). thin
      kappa_i (c) = kappa_j (c) ==> m_i (c) = m_j (c)) \
    & and (forall i < k. thin forall c in St(E_i). thin forall s. thin
      kappa_i (c) = prf(s) ==> m_i (c) = pi).
  $
] <def:compatible>

The first clause provides agreement between imports. The second
allows two modules to introduce a proof of the same statement under
the same name, without comparing their proof bodies.

#lemma(name: "Homes are earlier")[
  #src("whitepaper/Fragment/ModularSemantics.lean", 225, 227)[Validity bounds home keys]:
  $
    (forall j <= i. thin Valid_j) ==> forall c in St(E_i). thin forall h. thin
      kappa_i (c) = home(h) ==> h <= i.
  $
] <lem:home-le>

#proof[
  By strong induction on $i$. If $i$ is compared, assembly supplies
  a source $(j,V) in X_i$ storing $c$ with the same key. If $i$ is
  checked and $c in St(Gamma_i)$, context assembly supplies such a
  source too. The import order gives $j < i$, and refinement gives
  $c in St(E_j)$. Induction yields $h <= j < i$.

  In the remaining case $i$ is checked and $c$ is new. The condition
  $New_i$ gives a home key $home(i)$ or a proof key. Since the two
  key forms are disjoint, a home key here has $h = i$.
]

#theorem(name: "Modular checking")[
  Every valid finite prefix has a compatible family of models:
  $
    (forall i < k. thin Valid_i) ==> \
      exists (m_i in Mod(E_i))_(i < k). thin Cmp_k ((m_i)).
  $
  The #src("whitepaper/Fragment/ModularSemantics.lean", 254, 258)[generic theorem]
  therefore #src("whitepaper/Fragment/ModularInstance.lean", 115, 128)[applies to modules passing the concrete checks]
  in the set-theoretic instance.
] <thm:mod>

#proof[
  We induct on $k$, starting with the compatible empty family at
  $k = 0$. Suppose $(m_j)_(j < k)$ is compatible and module $k$ is
  valid; we construct its model from the imports' models.

  _Restrict the imports' models._ For each $(j,V) in X_k$, the
  import order gives $j < k$, and the home check gives
  $V refines E_j$. By @lem:restrict choose $m_(j,V) in Mod(V)$ with
  $
    St(V) subset.eq St(E_j), quad
    forall c in St(V). thin m_(j,V) (c) = m_j (c).
  $
  These view models are compatible under $sigma_k$. Indeed, if two
  sources are designated for $c$ and both store it, then
  $
    kappa_j (c) = kappa_k (c) = kappa_(j') (c), quad
    m_(j,V) (c) = m_j (c) = m_(j') (c) = m_(j',V') (c).
  $
  The middle equality is compatibility below $k$.

  _Amalgamate and extend._ If $k$ is checked, $Asm_k (Gamma_k)$
  gives a model $m_C$ of $Gamma_k$ with the view models' values.
  The step at $Acc(Gamma_k,D_k,E_k)$ extends it to $m_k in Mod(E_k)$,
  preserving all context values and giving flagged names value $pi$.
  If $k$ is compared, $Asm_k (E_k)$ gives $m_k$ directly by
  amalgamation.

  In both cases, each $c in St(E_k)$ satisfies at least one of
  $
    & exists (j,V) in X_k. thin c in St(V) and
      kappa_k (c) = kappa_j (c) and m_k (c) = m_j (c), \
    & kappa_k (c) = home(k), \
    & exists s. thin kappa_k (c) = prf(s) and m_k (c) = pi.
  $
  For a checked module the first case covers context names; the
  other two follow from $New_k$ and the step. For a compared module
  every name satisfies the first case.

  _Preserve compatibility._ Let $i < k$ and
  $c in St(E_k) inter St(E_i)$ with equal keys. In the first case,
  compatibility below $k$ gives $m_j (c) = m_i (c)$. In the second,
  $kappa_i (c) = home(k)$ contradicts @lem:home-le, since $i < k$.
  In the third, the earlier model gives $m_i (c) = pi$ by the proof
  clause of compatibility. Thus $m_k (c) = m_i (c)$.

  Finally suppose $c in St(E_k)$ has a proof key. In the first case
  the source has the same proof key and gives $c$ value $pi$. The
  second case is impossible, and the third gives the value directly.
  Both clauses of $Cmp_(k+1)$ therefore hold.
]

#corollary(name: "Every module has a model")[
  Under #src("whitepaper/Fragment/ModularSemantics.lean", 340, 345)[the abstract interface],
  $
    (forall j <= i. thin Valid_j) ==> exists m in Mod(E_i).
  $
  In the set-theoretic instance, assume $Pass_j$ for every
  $j <= i$. Then the following hold.

  + #src("whitepaper/Fragment/ModularInstance.lean", 132, 135)[Model existence]:
    $exists m in Mod(E_i)$.
  + Let $B$ be the empty Prop block of @cor:consistency. It has no
    level parameters, parameters, indices or constructors, and has large
    elimination. Write $r_B$ for its recursor name and $a_B^(sans("rec"))$
    for the generated recursor entry. If $E_i$ stores that entry, then
    #src("whitepaper/Fragment/ModularInstance.lean", 139, 146)[no closed term inhabits it]:
    $
      E_i (r_B) = a_B^(sans("rec")) ==> forall e. thin
        not (tack e => I_B) "over" E_i.
    $
  + Every stored type is inhabited in a model:
    #src("whitepaper/Fragment/ModularInstance.lean", 151, 158)[there is $m in Mod(E_i)$]
    with assignment $M$ such that
    $
      forall (c.\{arrow(p)\} : T) in E_i. thin
      forall arrow(ell),phi,rho. thin |arrow(ell)| = |arrow(p)| ==> \
      M(c,phi(arrow(ell))) in lden T[arrow(p) := arrow(ell)] rden_rho.
    $
] <cor:mod>

The first claim reads the family at $k = i+1$. The second uses the
recursor argument of @cor:consistency in that model. The third is its
typing law, with the required number of level arguments. For an
assumption used as a proposition, it says that the proposition holds
in this model.

== What runs in parallel <sec:mod-par>

The local checks read a module and its imports' views and keys, so
they can run as soon as those data are available. Modules with their
inputs available can be checked at the same time, while acceptance
of the development still requires every relevant module to pass.

The construction of $m_i$ has the same import dependencies: restrict
its imports' models to views, amalgamate, and apply the step for a
checked module. A compared module uses amalgamation alone.
The proof that the enlarged family remains compatible also compares
$m_i$ with the earlier models and uses @lem:home-le. The numbering
supplies an induction order; it adds no inputs to the construction of
$m_i$.

== Comparing a module <sec:mod-compare>

A _challenge_ is an environment specifying required constants. An
assumption in it is a _hole_: it fixes the level parameters and type
but leaves the kind unspecified. A solution must supply entries at
the same names. Definitions and other entries retained with their
kind must agree exactly, including values and recursor rules.

Represent the solution by an earlier module $s$ offering the needed
entries in its views, and the challenge by a module $i$ that imports
$s$. Give each compared name its source's key; the comparison then
checks
$
  op("Home")_i and (forall j in imp_i. thin j < i) and Asm_i (E_i).
$
This compares the challenge's whole own environment, including its
specified declaration values, and checks the dependencies and block
conditions in @def:assembled. Because assembly supplies a model
directly, the challenge's declarations need no separate type check.

A hole may stand for a proof, a definition or an entry of another kind
with the required type. Thus understanding a challenge requires
knowing its holes. The comparison fixes every non-assumption entry
and every hole's type.

Assume $Pass_j$ for every $j <= i$. Then @thm:mod gives the challenge
a model agreeing with the solution's on names stored under the same
key, and @cor:mod makes every hole's type inhabited in that model. In particular, if the challenge
stores the empty Prop block's recursor as in that corollary, it cannot
also have a hole of that empty proposition's type and pass validation
with a solution passing its local checks.

#remark(name: "A syntactic illustration")[
  In a type system with a fixed ground theory, let $t[theta]$ replace
  constants by ground terms. A model is a
  #src("whitepaper/Fragment/ModularSyntactic.lean", 83, 91)[realisation]:
  $
    theta "realises" E quad :<==> quad
      forall c,A,w. thin E(c) = (A,w) ==> \
      theta(c) :_0 A[theta] and
      (forall v. thin w = sans("some")(v) ==> theta(c) = v[theta]).
  $
  Here $:_0$ denotes typing in the ground theory and $w$ is an
  optional definition value. Environments and derivations mention
  only stored constants, and substitution depends only on mentioned
  constants. The assumed
  #src("whitepaper/Fragment/ModularSyntactic.lean", 60, 63)[substitution lemma]
  sends a derivation to a ground typing derivation under a realisation.

  #src("whitepaper/Fragment/ModularSyntactic.lean", 170, 177)[Assembly]
  copies entries from designated sources, possibly dropping values,
  with dependencies designated as the same source's. Compatible
  realisations therefore #src("whitepaper/Fragment/ModularSyntactic.lean", 179, 186)[amalgamate]
  by choosing each constant's realising term from a source. The
  #src("whitepaper/Fragment/ModularSyntactic.lean", 130, 135)[step]
  for a fresh definition $c : A := v$ sets $theta'(c) = v[theta]$ and
  preserves old values; the substitution lemma gives its typing.
  The #src("whitepaper/Fragment/ModularSyntactic.lean", 215, 236)[interface values]
  are optional ground terms, with
  $
    m(c) = sans("some")(theta(c)), quad pi = sans("none"),
    quad Fl(D) = emptyset.
  $

  This instance handles definitions only: no axioms, no inductive
  types, and nothing flagged as a proof. It illustrates the interface
  without showing that a syntactic consistency proof of Lean fits it.
  A shared proof value suits set models; a syntactic proof may
  distinguish proofs of different propositions. Applying the interface
  to another consistency proof requires a separate argument.
] <rem:mod-syntactic>

== Lean's module system in these terms <sec:mod-lean>

The following table describes the mapping from Lean's module system.
Its left column concerns Lean; the right column uses the mathematical
notions above. An exported level need not be self-contained, whereas
a view used in assembly must satisfy its scope conditions.

#table(
  columns: (1fr, 1fr),
  stroke: none,
  table.header[*Lean*][*Here*],
  [An exported level, with the imported dependencies of retained
    types and values],
  [A view, after retaining only entries whose laws have the required
    dependencies; a value can be hidden while its type is retained],
  [The private level, available under `import all`],
  [Own declarations with full information; together with their
    context, they can supply the own environment as a view],
  [The language server's level], [No role in this argument],
  [Modules loaded for elaboration: imports and modules reached
    through their `public import` re-exports], [The indices in $imp_i$],
  [The environment built from the loaded levels], [The context $Gamma_i$],
  [A theorem whose proof is unavailable, or a definition whose value
    is hidden],
  [An assumption of the same type; a theorem may carry a proof flag],
  [Copies of one name merged on import, allowed for theorems with
    the same statement], [The same name and proof statement key],
  [Two declarations of one name never loaded together],
  [Different home keys; compatibility imposes no equality between them],
  [A private name of the form `_private.…`],
  [An ordinary name, keyed by its home unless flagged as a proof],
  [An exported value mentioning a non-exported constant],
  [A retained value only where its dependencies are available under
    matching keys; otherwise an assumption if its type is complete,
    or no entry],
  [`backward.privateInPublic`, which can export private constants],
  [Additional entries available to satisfy view dependencies],
)

#real[
  Con-leche builds an importer's context by choosing the form in which
  each imported constant appears: in full, as an assumption of its
  type, or not at all. The choice depends on
  #src("ConLeche/Cached/ModStore.lean", 143, 167)[what the retained laws read]:
  the type and any retained value, rules, block entries and projection
  data. The importer checks the modules these dependencies come from,
  using their keys; pinned operations contribute dependencies too.
  Hiding a value removes the dependencies of its unfolding law.

  In the isolated mode,
  #src("ConLeche/Cached/ModIso.lean", 54, 73)[the form of an imported constant]
  is determined by the imported level and the availability of its
  dependencies. The context uses the imports' exported data, and
  their private data where `import all` makes it available. The home
  and importer checks above correspond to
  #src("ConLeche/Verify/Modular/Interface.lean", 150, 171)[checks on these entries and their dependencies].

  Con-leche has two checking modes. One checks each module at a view
  of a shared store of installed constants. With `--modular=isolated`,
  it #src("ConLeche/Cached/ModIso.lean", 280, 286)[checks over its own context].
  Provided the store's index lists every constant under its name in
  module order, the two computations
  #src("ConLeche/Verify/Modular/IsoCtx.lean", 575, 587)[give the same verdict],
  with installed constants placed over the isolated context.

  With `--compare CHALLENGE SOLUTION`, con-leche compares the
  challenge with its solution as in @sec:mod-compare and lists the
  holes. The checks aim to accept developments accepted by Lean;
  that compatibility is tested on developments, not proved here.

  Con-leche's #src("ConLeche/MainTheorem.lean", 131, 145)[modular theorem]
  gives compatible models of the own environments of all modules
  passing its verified local checks. Its proof applies the
  #src("ConLeche/Modular/Generic.lean", 256, 260)[generic modular theorem]
  to #src("ConLeche/Model/Modular/Instance.lean", 236, 253)[its graded model instance].
  Values in that instance are semantic terms indexed by level
  valuations; amalgamation chooses each name's value from a designated
  source.
  Proof keys record level parameters and types. A proof flag is
  justified by the home module's check: the declaration is a theorem,
  or a definition or opaque constant whose type is inferred to be a
  proposition. No constant name is renamed.
]
