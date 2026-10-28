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
#let Bnd = $op("Bnd")$
#let Cmp = $op("Cmp")$
#let Valid = $op("Valid")$
#let Checked = $op("Checked")$
#let Compared = $op("Compared")$
#let Local = $op("Local")$
#let Validated = $op("Validated")$
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

§3 and §4 extend an environment one declaration at a time. We now
organise declarations into modules. Each module has an environment
of imports and declarations of its own. We prove that local checks
give a compatible family of models, one model for each module.

We first state the properties of environment models used by the
argument. Then we define modules, their local checks and the theorem.
Parallel checking and comparison with a solution follow from the same
construction. @sec:mod-lean gives the mapping to Lean's module system.

== Environment models in the abstract <sec:mod-iface>

Fix a type $Env$ of environments and a type $Name$ of constant names. Write
#src("whitepaper/Fragment/ModularSemantics.lean", 95, 96)[$St(E) subset.eq Name$]
for the names an environment $E$ stores. No structure on stored
entries is needed yet.

A model $m in Mod(E)$ assigns every name a value $m(c) in Val$.
The consistency proof chooses these types and operations. The
interface below states the laws they must satisfy.

For a family $(E_x)_(x in X)$ and a target environment $C$, a
_designation_ is a relation $sigma subset.eq Name times X$.
The assertion $sigma(c,x)$ designates source $x$ for the name $c$.
It does not by itself say that $E_x$ stores $c$.

#definition(name: "Compatible for an environment")[
  Given models $m_x in Mod(E_x)$ with values $m_x(c) in Val$, define
  $
    Cmp_C^sigma((m_x)) quad :<==> quad
      forall c in St(C). thin forall x,y in X. quad
      sigma(c,x) and sigma(c,y) and c in St(E_x) inter St(E_y)
      ==> m_x(c) = m_y(c).
  $
] <def:compatible-for>

Thus designated sources must agree wherever the target stores their
name. A model of the target can then preserve all their values.

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
      Asm(C,(E_x),sigma) and Cmp_C^sigma((m_x)) ==> \
      exists m_C in Mod(C). thin forall c in St(C). thin forall x in X. quad
        sigma(c,x) and c in St(E_x) ==> m_C(c) = m_x(c).
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

Assembly describes which parts of the source environments the target
retains. Its definition belongs to the particular consistency proof.
The interface requires both a source for every stored name and a model
that preserves every designated source's value.

The step extends _every_ model of the context. The modular argument
applies it to the particular model obtained by amalgamating imports.
Existence of some model after the step would not ensure preservation
of those imported values.

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
  one-member family $(m)$ is compatible, since its only two possible
  source indices are equal. Amalgamation gives $m'$.
]

The empty family is compatible too. Thus an environment assembled
from no sources has a model:
$
  Asm(C,(),emptyset) ==> exists m in Mod(C).
$
This supplies the initial case whenever an instance assembles an empty
context from no imports.

*An illustration by syntax.* A second instance uses realisations in
a fixed ground theory. Write $t[theta]$ for simultaneous substitution
of ground terms for constants, and $t :_0 A$ for ground typing. An
entry is a type $A$ with an optional value $w$, written
$E(c) = (A,w)$. Write $op("consts")(t)$ for the constants mentioned
by $t$.

The environments are scoped: every constant mentioned by a stored
type or value is stored. A
#src("whitepaper/Fragment/ModularSyntactic.lean", 83, 91)[realisation]
satisfies
$
  theta "realises" E quad :<==> quad
  forall c,A,w. thin E(c) = (A,w) ==> \
    theta(c) :_0 A[theta] and
    (forall v. thin w = sans("some")(v) ==> theta(c) = v[theta]).
$
The system assumes that derivations mention only stored constants.
Its #src("whitepaper/Fragment/ModularSyntactic.lean", 60, 63)[substitution lemma]
is
$
  (E tack t : A) and (theta "realises" E)
    ==> t[theta] :_0 A[theta].
$
Substitution also depends only on the values of the constants a term
mentions.

#src("whitepaper/Fragment/ModularSyntactic.lean", 170, 177)[Assembly]
in this instance is
$
  Asm(C,(E_x),sigma) quad :<==> quad
    forall c,A,w. thin C(c) = (A,w) ==> \
    exists x in X, w'. thin sigma(c,x) and E_x(c) = (A,w') \
    and (forall v. thin w = sans("some")(v) ==> w' = sans("some")(v)) \
    and (forall d in op("consts")(A). thin sigma(d,x)) \
    and (forall v. thin w = sans("some")(v) ==>
      forall d in op("consts")(v). thin sigma(d,x)).
$
Each entry comes from a designated source, with its value kept or
omitted. Its dependencies must be designated as that source's too.
Compatible realisations therefore
#src("whitepaper/Fragment/ModularSyntactic.lean", 179, 186)[amalgamate]
by choosing each constant's realising term from a designated source.

Acceptance adds fresh definitions whose values have their declared
types. The #src("whitepaper/Fragment/ModularSyntactic.lean", 130, 135)[step]
realises a new definition $c : A := v$ by
$theta'(c) = v[theta]$, preserving $theta$ on old names. The
substitution lemma gives its typing. The
#src("whitepaper/Fragment/ModularSyntactic.lean", 215, 236)[interface values]
are optional terms:
$
  Val = {sans("none")} union {sans("some")(t) mid(|) t "a ground term"},
  quad m(c) = sans("some")(theta(c)), quad pi = sans("none"), quad Fl(D) = emptyset.
$

This instance illustrates the interface. It handles definitions only:
no axioms, no inductive types, and nothing flagged as a proof. It does
not show that a syntactic consistency proof of Lean fits the
interface. A shared proof value suits set models; a syntactic proof
may distinguish proofs of different propositions. Whether another
consistency proof provides this interface requires a separate argument.

== Environments of modules <sec:mod-env>

A module has a _context_ $Gamma_i$, an environment containing the
constants available to its declarations, and an _own environment_
$E_i$ containing its context and declarations. Here $Gamma_i$ is an
environment of constants; inference still uses the empty variable
context unless stated otherwise.

A _view_ is an environment the module presents to importers. A view
may omit entries or hide information. Refinement will ensure that its
models can be obtained from models of the own environment.

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
modules. The identifier is the pair $(c,kappa_i(c))$: all ordinary
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
has a type and no value. Its only model obligation is the typing law
of @def:model. It has no $delta$ rule.

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

Call a block _plain_ when it has no nesting.

*Scope.* For a term $e$, environment $A$, level parameters
$arrow(p)$ and variables $Delta$, write
#src("whitepaper/Fragment/Decl.lean", 580, 584)[$Cl(A,arrow(p),Delta,e)$]
for
$
  Cl(A,arrow(p),Delta,e) quad :<==> quad
    op("FV")(e) subset.eq Delta and
    op("consts")(e) subset.eq St(A) and
    op("lparams")(e) subset.eq {arrow(p)}.
$
Here $op("FV")$, $op("consts")$ and $op("lparams")$ collect free
variables, constant names and level parameters. For $Delta = emptyset$
the term is closed.

For a plain block $B$, let $Q_B$ list its expression pieces
with the variables available at each piece: the parameter and index
domains, ordinary field domains, reflexive field telescope domains
and index expressions, and each constructor's result indices.
These are the scopes of @sec:ind-checks. Write $n_I$ for its number
of indices, $u_B$ for its result level, and $ell_B$ for its elimination
parameter. The
#src("whitepaper/Fragment/Decl.lean", 699, 710)[scope condition on the specification]
is
$
  BSc(A,B) quad :<==> quad
    & (forall (e,Delta) in Q_B. thin Cl(A,arrow(p)_B,Delta,e)) \
    & and op("lparams")(u_B) subset.eq {arrow(p)_B}
      and arrow(p)_B "has distinct entries" \
    & and (B "has large elimination" ==> ell_B in.not {arrow(p)_B}) \
    & and (forall d in op("ctors")(B). thin |arrow(e)_d| = n_I) \
    & and (forall f "reflexive in" B. thin |arrow(e)_f| = n_I) \
    & and (forall f "a field of" B. thin
      op("FV")(op("pieces")(f)) inter op("earlierRecVars")(f) = emptyset) \
    & and (forall f "a field of" B. thin
      f "is ordinary or reflexive").
$
In the penultimate line, $op("pieces")(f)$ means the domain of an
ordinary field, or the telescope domains and index expressions of a
reflexive field. Free variables of a list of pieces means the union
of their free variables. The set $op("earlierRecVars")(f)$ contains the
variables of earlier reflexive fields. Constructor result indices
may depend on those variables.

For a family $(E_x)$ designated by $sigma$ for $C$, define the
#src("whitepaper/Fragment/ModularModel.lean", 189, 193)[common part]
by
$
  E_x^C = E_x "restricted to" {c in St(C) mid(|) sigma(c,x)}.
$
It stores source entries at those names; its entries need not equal
$C$'s entries.

Write $I_B$ for a block's name and $c_d$ for constructor specification
$d$'s name. For an entry $a$, define the
#src("whitepaper/Fragment/ModularModel.lean", 208, 221)[scope needed by its laws]:
$
  Sc(A,C,a) quad :<==> quad
    & Cl(A,arrow(p)_a,emptyset,T_a) \
    & and (forall v. thin K_a = sans("defn")(v)
      ==> Cl(A,arrow(p)_a,emptyset,v)) \
    & and (forall R. thin K_a = sans("recursor")(R) ==> \
    & quad forall (d,r) in R. thin Cl(A,arrow(p)_a,emptyset,r) and \
    & quad exists b. thin A(d) = b and C(d) = b
      and Cl(A,arrow(p)_b,emptyset,T_b)) \
    & and (forall B. thin K_a "is a type former for the plain block" B ==> \
    & quad BSc(A,B) and I_B in St(A)
      and (forall d in op("ctors")(B). thin c_d in St(A))).
$
In the recursor clause, $(d,r)$ names a rule's constructor and
right-hand side; the other stored counts are left implicit.
The equality $A(d) = C(d)$ ensures that the recursor law reads the
same constructor entry in both environments.

#definition(name: "Assembly")[
  Let $a_B$ and $a_(B,d)$ be the type former and constructor entries
  generated by a block
  (@sec:ind-checks). The instance's
  #src("whitepaper/Fragment/ModularModel.lean", 223, 235)[assembly relation]
  is
  $
    Asm(C,(E_x),sigma) quad :<==> quad
    & (forall c in St(C). thin exists x in X. thin
      sigma(c,x) and c in St(E_x) \
    & quad and C(c) <= E_x(c) and Sc(E_x^C,C,C(c))) \
    & and (forall c in St(C). thin forall B. thin
      K_(C(c)) "is a type former for the plain block" B ==> \
    & quad C(I_B) = a_B and
      (forall d in op("ctors")(B). thin C(c_d) = a_(B,d))).
  $
] <def:assembled>

The first clause checks the laws of the _retained_ entry. An
assumption therefore requires only its type's dependencies. The
second clause requires exact generated entries for a retained plain
block. If its type former is retained only as an assumption, that
clause does not apply.

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
The common parts are contained in $C$, so their scope conditions give
these properties in $C$.

*The models used here.* The instance retains the model laws of §3
and §4 and the construction facts needed when a later block uses a
plain block as a container. For each stored plain block $B$, these
#src("whitepaper/Fragment/BlockModel.lean", 46, 66)[additional facts]
are
$
  & BSc(E,B) and B "has no container fields", \
  & E(I_B) = a_B, quad
    forall d in op("ctors")(B). thin E(c_d) = a_(B,d), \
  & forall arrow(n). thin M(I_B,arrow(n)) = op("family")_B(M,arrow(n)), \
  & forall d in op("ctors")(B). thin forall arrow(n). thin
    M(c_d,arrow(n)) = op("constructor")_(B,d)(M,arrow(n)), \
  & forall arrow(n),arrow(X). thin arrow(X) "fits the parameters of" B
    ==> Bnd_B(M,arrow(n),arrow(X)).
$
The family and constructor sets are those constructed in
@sec:ind-model. To state the field bound, fix $M$, $arrow(n)$ and
parameter values $arrow(X)$. Evaluate levels at the valuation of
$B$'s parameters given by $arrow(n)$, and let $nu$ be the value of
$u_B$. For a constructor $d$, a family $W$, and a prefix
$arrow(F)$ fitting its fields relative to $W$, let
$cal(A)_(B,d)(W,arrow(F))$ contain the following denoted domains:
the next field's domain when it is ordinary, or every domain of the
next field's reflexive telescope, at every fitting telescope prefix.
The #src("whitepaper/Fragment/IndSem.lean", 601, 622)[field bound]
is
$
  Bnd_B(M,arrow(n),arrow(X)) quad :<==> quad nu > 0 ==> \
    forall W in cal(U)_nu. thin forall d in op("ctors")(B). thin
    forall arrow(F) "a fitting proper prefix for" d "relative to" W. \
    forall A in cal(A)_(B,d)(W,arrow(F)). thin A in cal(U)_nu.
$
Here $W in cal(U)_nu$ means that every fibre of $W$ lies in that
universe, as in @sec:ind-model. The parameters $M$, $arrow(n)$ and
$arrow(X)$ are implicit in $cal(A)$. The bound is vacuous when
$nu = 0$.
These facts are retained in the model; amalgamation must preserve
them along with typing, unfolding and the recursor laws.

For such a model $m$ with assignment $M$, the abstract values are
$
  Mod(E) = {m mid(|) m "satisfies these model laws over" E}, quad
  m(c) = (arrow(n) |-> M(c,arrow(n))), quad pi = (arrow(n) |-> pt).
$

#theorem(name: "Amalgamation")[
  The instance satisfies
  #src("whitepaper/Fragment/ModularModel.lean", 252, 260)[the amalgamation law]:
  $
    Asm(C,(E_x),sigma) and Cmp_C^sigma((m_x)) ==> \
    exists m_C in Mod(C). thin forall c in St(C). thin forall x in X. quad
      sigma(c,x) and c in St(E_x) ==> m_C(c) = m_x(c).
  $
] <thm:amalg>

#proof[
  For every name with a designated source that stores it, choose one
  source's value. Use $pi$ when there is no such source.
  Compatibility makes the choice agree with every designated source
  on names stored in $C$.

  Take $c in St(C)$ and the source $x$ provided by assembly.
  If $C(c)$ is not an assumption, it equals $E_x(c)$. Its laws read
  only terms and entries covered by $Sc(E_x^C,C,C(c))$. Interpretation
  #src("whitepaper/Fragment/Hygiene.lean", 593, 595)[depends only on mentioned constants],
  and the chosen assignment agrees with $m_x$ on $E_x^C$. Thus the
  typing, unfolding and recursor laws transfer. If $C(c)$ is an
  assumption, only typing transfers; its type and level parameters
  equal those of $E_x(c)$.

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
  PropTy_E(T) quad :<==> quad exists S,u. thin
    (tack T => S red Sort u) "over" E and u eq.dot 0.
$
The #src("whitepaper/Fragment/Decl.lean", 608, 618)[theorem check]
is the definition check of §3 on $c : T := v$, together with
$PropTy_E(T)$. The stored entry is an assumption with parameters
$arrow(p)$ and type $T$; its proof is not stored.

Installing a theorem
#src("whitepaper/Fragment/InstallThm.lean", 249, 255)[extends a model]
by installing the checked definition and forgetting its value.
Old constant values are preserved. Its chosen value is the point.
More generally, for an accepted definition with propositional type,
#src("whitepaper/Fragment/ModularModel.lean", 61, 81)[the chosen value satisfies]
$
  PropTy_E(T) ==> forall arrow(n). thin M'(c,arrow(n)) = pt.
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

Write $op("Ok")_E(d)$ for the checks of a definition (§3), theorem
(above) or inductive block (§4). The
#src("whitepaper/Fragment/Modular.lean", 200, 209)[sequential check]
and the #src("whitepaper/Fragment/ModularModel.lean", 54, 59)[proof predicate]
are
$
  Check(Gamma,D) & :<==> forall 1 <= t <= r. thin op("Ok")_(Gamma^(t-1))(d_t), \
  op("Proof")_E(d) & :<==> d "is a theorem" or
    (d "is a definition with type" T and PropTy_E(T)).
$
The #src("whitepaper/Fragment/ModularModel.lean", 85, 90)[flag condition]
and #src("whitepaper/Fragment/ModularInstance.lean", 41, 48)[acceptance]
are
$
  Flags(Gamma,D,p) & :<==> forall 1 <= t <= r. thin
    forall c in names(d_t). thin p(c) = "yes" ==> op("Proof")_(Gamma^(t-1))(d_t), \
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
  sigma_i(c,(j,V)) & :<==> kappa_i(c) = kappa_j(c), \
  Asm_i(E) & :<==> Asm(E,(V)_((j,V) in X_i),sigma_i).
$
A source is designated only when it gives the same name the same key.
Assembly also checks that the source stores that name.

#definition(name: "Valid module")[
  The #src("whitepaper/Fragment/ModularSemantics.lean", 178, 198)[abstract checks]
  are
  $
    New_i & :<==> forall c in St(E_i) without St(Gamma_i). thin
      kappa_i(c) = home(i) or \
      & quad ((exists s. thin kappa_i(c) = prf(s)) and c in Fl(D_i)), \
    Checked_i & :<==> Asm_i(Gamma_i) and Acc(Gamma_i,D_i,E_i) and New_i, \
    Compared_i & :<==> Asm_i(E_i), \
    Valid_i & :<==> (forall V in cal(V)_i. thin V refines E_i)
      and (forall j in imp_i. thin j < i) \
      & quad and (Checked_i or Compared_i).
  $
] <def:valid>

A checked module extends a context model. A compared module obtains
its model directly from imported views. Both must check their own
views and import order.

#definition(name: "Local checks")[
  In the set-theoretic instance, put $s(a) = (arrow(p)_a,T_a)$.
  The #src("whitepaper/Fragment/ModularModel.lean", 421, 443)[local checks]
  have three groups:
  $
    op("Home")_i & :<==> forall V in cal(V)_i. thin V refines E_i, \
    op("Import")_i & :<==> (forall j in imp_i. thin j < i) and Asm_i(Gamma_i), \
    op("OwnKeys")_i & :<==> forall d in D_i. thin forall c in names(d). thin
      kappa_i(c) = cases(
        prf(s(E_i(c))) & "if" p_i(c) = "yes",
        home(i) & "otherwise"), \
    Local_i & :<==> op("Home")_i and op("Import")_i and Check(Gamma_i,D_i) \
      & quad and Flags(Gamma_i,D_i,p_i) and op("OwnKeys")_i.
  $
] <def:local>

The #src("whitepaper/Fragment/ModularModel.lean", 445, 454)[alternative validation]
is
$
  Validated_i quad :<==> quad Local_i or
    (op("Home")_i and (forall j in imp_i. thin j < i) and Asm_i(E_i)).
$
These checks #src("whitepaper/Fragment/ModularInstance.lean", 94, 111)[imply abstract validity]:
$
  Validated_i ==> Valid_i.
$
For a checked module, assembly makes $Gamma_i$ closed, as acceptance
requires. Every name in $E_i$ outside $Gamma_i$ is declared by $D_i$,
so $op("OwnKeys")_i$ implies $New_i$. The comparison case is immediate.

The check per home reads the module and its views. It is performed
once, independently of how many modules import it. The check per
importer reads its context, its keys and its imports' views and keys.
It does not read the imports' own environments.

A hidden definition value contributes no value dependencies. Its type
must still be in scope under matching keys. Similarly, a context may
select only some entries of a view if every retained law's dependencies
and the block conditions remain satisfied. A definition is checked
in its home context, where the values it needs may be visible. An
importer transfers its laws by assembly; it does not recheck the
original value against a context that hides those dependencies.

== The theorem <sec:mod-thm>

The induction constructs models together with their compatibility.
Existence of unrelated models would not suffice for amalgamation.
For example, if two designated sources store $c$ but give it different
values, no target model can preserve both:
$
  m_C(c) = m_x(c) and m_C(c) = m_y(c) ==> m_x(c) = m_y(c).
$

#definition(name: "Compatible family of a development")[
  For models $m_i in Mod(E_i)$ with $i < k$, define
  #src("whitepaper/Fragment/ModularSemantics.lean", 200, 207)[compatibility]
  by
  $
    Cmp_k((m_i)) quad :<==> quad
    & (forall i,j < k. thin forall c in St(E_i) inter St(E_j). thin
      kappa_i(c) = kappa_j(c) ==> m_i(c) = m_j(c)) \
    & and (forall i < k. thin forall c in St(E_i). thin forall s. thin
      kappa_i(c) = prf(s) ==> m_i(c) = pi).
  $
] <def:compatible>

The first clause provides agreement between imports. The second
allows two modules to introduce a proof of the same statement under
the same name, without comparing their proof bodies.

#lemma(name: "Homes are earlier")[
  #src("whitepaper/Fragment/ModularSemantics.lean", 225, 227)[Validity bounds home keys]:
  $
    (forall j <= i. thin Valid_j) ==> forall c in St(E_i). thin forall h. thin
      kappa_i(c) = home(h) ==> h <= i.
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
      exists (m_i in Mod(E_i))_(i < k). thin Cmp_k((m_i)).
  $
  This is #src("whitepaper/Fragment/ModularSemantics.lean", 254, 258)[the generic theorem];
  it #src("whitepaper/Fragment/ModularInstance.lean", 115, 128)[applies to validated modules]
  in the set-theoretic instance.
] <thm:mod>

#proof[
  By induction on $k$. The empty family at $k = 0$ is compatible.
  Suppose $(m_j)_(j < k)$ is compatible and module $k$ is valid.

  _Restrict the imports' models._ For each $(j,V) in X_k$, the
  import order gives $j < k$, and the home check gives
  $V refines E_j$. By @lem:restrict choose $m_(j,V) in Mod(V)$ with
  $
    St(V) subset.eq St(E_j), quad
    forall c in St(V). thin m_(j,V)(c) = m_j(c).
  $
  These view models are compatible under $sigma_k$. Indeed, if two
  sources are designated for $c$ and both store it, then
  $
    kappa_j(c) = kappa_k(c) = kappa_(j')(c), quad
    m_(j,V)(c) = m_j(c) = m_(j')(c) = m_(j',V')(c).
  $
  The middle equality is compatibility below $k$.

  _Amalgamate and extend._ If $k$ is checked, $Asm_k(Gamma_k)$
  gives a model $m_C$ of $Gamma_k$ with the view models' values.
  The step at $Acc(Gamma_k,D_k,E_k)$ extends it to $m_k in Mod(E_k)$,
  preserving all context values and giving flagged names value $pi$.
  If $k$ is compared, $Asm_k(E_k)$ gives $m_k$ directly by
  amalgamation.

  In both cases, each $c in St(E_k)$ satisfies at least one of
  $
    & exists (j,V) in X_k. thin c in St(V) and
      kappa_k(c) = kappa_j(c) and m_k(c) = m_j(c), \
    & kappa_k(c) = home(k), \
    & exists s. thin kappa_k(c) = prf(s) and m_k(c) = pi.
  $
  For a checked module the first case covers context names; the
  other two follow from $New_k$ and the step. For a compared module
  every name satisfies the first case.

  _Preserve compatibility._ Let $i < k$ and
  $c in St(E_k) inter St(E_i)$ with equal keys. In the first case,
  compatibility below $k$ gives $m_j(c) = m_i(c)$. In the second,
  $kappa_i(c) = home(k)$ contradicts @lem:home-le, since $i < k$.
  In the third, the earlier model gives $m_i(c) = pi$ by the proof
  clause of compatibility. Thus $m_k(c) = m_i(c)$.

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
  In the set-theoretic instance, assume $Validated_j$ for every
  $j <= i$. Then the following hold.

  + #src("whitepaper/Fragment/ModularInstance.lean", 132, 135)[Model existence]:
    $exists m in Mod(E_i)$.
  + Let $B$ be the empty Prop block of @cor:consistency. It has no
    level parameters, parameters, indices or constructors, and has large
    elimination. Write $r_B$ for its recursor name and $a_B^sans("rec")$
    for the generated recursor entry. If $E_i$ stores that entry, then
    #src("whitepaper/Fragment/ModularInstance.lean", 139, 146)[no closed term inhabits it]:
    $
      E_i(r_B) = a_B^sans("rec") ==> forall e. thin
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

The local checks read a module and its imports' views and keys.
Once those data are available, a module's checks can run independently
of checks of other modules. Modules whose inputs are available may
therefore be checked at the same time. Acceptance of the development
still requires every relevant module to pass its checks.

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

Represent the solution by an earlier module $s$ that offers the
needed entries in its views. Represent the challenge by a module $i$
whose imports include $s$. Give each compared name the key of its
source. The validation condition is
$
  op("Home")_i and (forall j in imp_i. thin j < i) and Asm_i(E_i).
$
It compares the challenge's whole own environment, including its
specified declaration values. It also checks the dependencies and
block conditions in @def:assembled. The challenge's declarations
need not be type-checked separately.

A hole may stand for a proof, a definition or an entry of another kind
with the required type. Thus understanding a challenge requires
knowing its holes. The comparison fixes every non-assumption entry
and every hole's type.

Assume every module through $i$ is validated. By @thm:mod, the
challenge has a model agreeing with the solution's on
names stored under the same key. By @cor:mod, every hole's type is
inhabited in the challenge's model. In particular, if the challenge
stores the empty Prop block's recursor as in that corollary, it cannot
also have a hole of that empty proposition's type and pass validation
with a validated solution.

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
  Con-leche constructs contexts from imported presentations.
  #src("ConLeche/Cached/ModStore.lean", 143, 167)[The dependencies of a presentation]
  include its type and any retained value, rules, block entries and
  projection data. The importer must make these available under the
  source's keys. The implementation also accounts for names used by
  pinned operations. Hiding a value removes its value dependencies.

  In the isolated mode, a constant's
  #src("ConLeche/Cached/ModIso.lean", 54, 73)[presentation]
  is computed from the imported level and its gates: the full entry,
  an assumption of its type, or no entry. The context uses the imports'
  exported data, and their private data where `import all` makes it
  available. It does not add private data merely to complete an
  exported entry. The abstract home and importer checks are realised
  by #src("ConLeche/Verify/Modular/Interface.lean", 150, 171)[checks on presentations and their dependencies].

  Con-leche has two checking modes. One checks each module at a view
  of a shared store of installed constants. With `--modular=isolated`,
  it #src("ConLeche/Cached/ModIso.lean", 280, 286)[checks over its own context].
  Provided the store's name index lists all unit constants in module
  order, the two computations
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
  Values in that instance are leaves indexed by level valuations;
  amalgamation chooses each name's leaf from a designated source.
  Proof keys record level parameters and types. A proof flag is
  justified by the home module's check: the declaration is a theorem,
  or a definition or opaque constant whose type is inferred to be a
  proposition. No constant name is renamed.
]
