#import "../lib.typ": *

// Notation local to this file, matching §3 and §7.
#let Mod = $op("Mod")$
#let Pass = $op("Pass")$
#let Cmp = $op("Cmp")$
#let From = $op("src")$
#let Side = $op("Pf")$
#let Sh = $op("Sh")$
#let consts = $op("consts")$
#let Nat = $sans("Nat")$
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked

= Comparing a challenge with a solution <sec:compare>

A _challenge_ states what is asked: theorems without proofs,
definitions without values, and assumptions. A _solution_ supplies
them. The checker checks the solution as it checks any input. It then
checks the challenge as any input, with one exception: an open
statement of the challenge is accepted when the solution _justifies_
it. This section states the rule, shows that an accepted challenge has
a model, and shows why the rule compares more than the open statement
itself. @sec:cmp-modular compares module by module: there the
challenge is one more module, which imports the solution, and its
declarations that the solution already holds are read from the
solution instead of being checked.

== Holes and justification <sec:cmp-what>

#definition(name: "Challenge, hole, solution")[
  A _challenge_ is an input that the checker checks declaration by
  declaration, as in @sec:env and @sec:ind; write $E_c$ for its
  environment. A _hole_ of the challenge is an assumption it declares:
  a name with level parameters and a type, and no value,
  $
    (n.\{arrow(p)\} : T).
  $
  In Lean these are the challenge's axioms other than the built-in
  ones, and its declarations whose
  value uses `sorry`, each read as the assumption of its statement.
  A _solution_ is an environment $E_s$ that the checker has accepted.
]

An assumption can state anything, an empty proposition included, so
the checker does not accept a hole on its own. With a solution, a hole
is accepted when the solution stores a constant of the same name that
states the same, and everything the statement reads means the same in
both environments. The second condition is a closure condition on
names.

#definition(name: "Shared names, justified hole")[
  A set $Sh$ of names is _shared_ between $E_c$ and $E_s$ when, for
  every $d in Sh$, the solution stores $d$ and
  + either $E_c$ stores $d$ with the same entry as $E_s$,
  + or $E_c$ stores $d$ as an assumption $(d.\{arrow(p)\} : T)$, and
    $E_s$ stores $d$, of any kind, with level parameters $arrow(q)$,
    as many as $arrow(p)$, and a type $T_s$ such that
    $
      T = T_s [arrow(q) := arrow(p)];
    $
  and every constant that the type or the value of $d$'s entry in
  $E_c$ reads is in $Sh$ again. A hole of the challenge is _justified_
  by $E_s$ when its name lies in a shared set.
]

The level parameters are compared by position. A declaration's level
parameters are bound by the declaration, and a model reads a
constant's set off a list of levels by position (@def:model). Renaming
them changes none of the constant's instances:

#lemma(name: "Renaming level parameters")[
  Let $T$ use only the level parameters $arrow(q)$, and let
  $arrow(p)$ be distinct names, as many as $arrow(q)$. Then for every
  level list $arrow(ell)$ with $|arrow(ell)| = |arrow(q)|$,
  #src("whitepaper/Fragment/Compare.lean", 114, 120)[renaming does not change the instances]:
  $
    T[arrow(q) := arrow(p)][arrow(p) := arrow(ell)] = T[arrow(q) := arrow(ell)].
  $
] <lem:cmp-rename>

So a hole and the solution's constant it is justified by have the same
instances: at every level list, they have the same type.

== The challenge has a model <sec:cmp-model>

Let $M_s$ be a model of the solution's environment $E_s$. The model
$M_c$ of the challenge is built along the challenge's check, as in
@sec:env and @sec:ind, and it keeps one more fact: on every shared
name stored so far it agrees with the solution's model,
$
  forall d in Sh. thin forall arrow(k). thin
    M_c (d, arrow(k)) = M_s (d, arrow(k)).
$
Here $Sh$ is a shared set read in the challenge's final environment,
holding the names of all justified holes. Three facts carry the
construction. The first says that a denotation reads the model only at
the constants the term reads:

#lemma(name: "Denotation is local")[
  If two assignments $M$ and $M'$ agree on every constant a term $e$
  reads, then
  #src("whitepaper/Fragment/Compare.lean", 151, 156)[$e$ denotes the same in both, and is well-denoted in both alike]:
  $
    (forall d in consts(e). thin M(d) = M'(d)) ==>
      lden e rden_rho "in" M = lden e rden_rho "in" M'
      and (rho models e "in" M <==> rho models e "in" M').
  $
] <lem:cmp-local>

The second gives a justified hole the solution model's set:

#lemma(name: "A justified hole")[
  Let $E_c$ be closed, with a model $M_c$, and let
  $(n.\{arrow(p)\} : T)$ be a fresh assumption whose type is in scope
  of $E_c$. Let $E_s$, with a model $M_s$, store $n$ with level
  parameters $arrow(q)$ and type $T_s$, with
  $T = T_s [arrow(q) := arrow(p)]$, and let $M_c$ and $M_s$ agree on
  every constant $T$ reads. Then
  #src("whitepaper/Fragment/Compare.lean", 268, 286)[$M_c$ extends to a model of the environment with the hole, with the solution model's set at $n$]:
  $
    exists M'_c in Mod(E_c, (n.\{arrow(p)\} : T)). thin
      M'_c (n) = M_s (n) and forall d in E_c. thin M'_c (d) = M_c (d).
  $
] <lem:cmp-hole>

#proof[
  Old laws survive the new set at $n$, because no stored term reads
  the fresh name (@sec:env). For the new typing law, fix $arrow(ell)$
  and $phi$. By @lem:cmp-rename, $T[arrow(p) := arrow(ell)]$ is
  $T_s [arrow(q) := arrow(ell)]$. It reads the constants $T$ reads, on
  which the two models agree, so by @lem:cmp-local it denotes the same
  set in both and is well-denoted in both alike. The typing law of $M_s$
  puts $M_s (n, phi(arrow(ell)))$ in that set. A hole has no value, so
  there is no unfolding law to show.
]

The third gives a constant that both environments store alike the
solution model's set:

#lemma(name: "A shared constant")[
  Let $E_c$ be closed, with a model $M_c$, and let $E_s$, with a
  model $M_s$, store a fresh name $d$ as a definition or an
  assumption, whose type and value are in scope of $E_c$. If $M_c$ and
  $M_s$ agree on every constant that the type and the value read, then
  #src("whitepaper/Fragment/Compare.lean", 305, 321)[$M_c$ extends to a model of the environment with $d$'s entry, with the solution model's set at $d$].
] <lem:cmp-shared>

The typing and unfolding laws of the new constant are those of $M_s$,
carried over by @lem:cmp-local. Both lemmas extend a model at
#src("whitepaper/Fragment/Compare.lean", 167, 185)[a given set], as
@sec:env extends it at a definition's value.

#theorem(name: "The challenge has a model")[
  Let $E_s$ have a model $M_s$, and let the checker accept the
  challenge with its holes justified by $E_s$. Then the challenge's
  environment has a model $M_c$, which agrees with $M_s$ on every
  shared name:
  $
    exists M_c in Mod(E_c). thin forall d in Sh. thin M_c (d) = M_s (d).
  $
] <thm:cmp-model>

#proof[
  Induction along the challenge's check, with the agreement on the
  shared names stored so far as the invariant. A declaration none of
  whose names is shared takes its own step (@sec:env, @sec:ind), which
  keeps every stored constant's set. A shared definition or assumption
  takes @lem:cmp-shared: everything it reads is shared and stored
  before it, so the invariant gives the agreement the lemma asks for.
  A justified hole takes @lem:cmp-hole, with the agreement on its
  type's constants from the invariant in the same way. Both give the
  new name the solution model's set, so the invariant holds again.
]

A hole whose statement is an empty proposition is never justified:
by the typing law of $M_s$, as in the proof of @lem:cmp-hole, the
solution model's set at the hole would be a member of the statement's
set, which is empty.

== Why the statement's reads must be shared <sec:cmp-attack>

The closure condition is needed. Let the challenge declare a
definition and a hole that reads it,
$
  f : Nat := 3, quad quad t : f = 5.
$
A solution declares its own $f : Nat := 5$, and proves $t$ by
unfolding it. The solution's $t$ has the name of the hole and, as a
term, the hole's statement. But the statement reads $f$, and the two
environments store $f$ with different values. So $f$ is in no shared
set, $t$ is not justified, and the checker rejects the challenge.

Without the closure condition, @thm:cmp-model would fail at this
hole. The solution model's set at $t$ lies in $lden f = 5 rden$ in
$M_s$, where $f$ is $5$. In every model of $E_c$ the unfolding law
makes $f$ the set $3$, so $lden f = 5 rden$ is empty there, and the
environment with $t$ has no model at all.

#real[
  Con-leche compares two `lean4export` files,
  `con-leche --compare CHALLENGE.ndjson SOLUTION.ndjson`. It checks
  the solution's file in full, then the challenge's file
  #src("ConLeche/Cached/Decls.lean", 110, 116)[with the solution's environment justifying its holes].
  It compares compiled modules by the same rule,
  `con-leche --olean --compare CHALLENGE SOLUTION`: the solution's
  closure is checked in full, then the challenge's closure, read from
  the trusted directories alone, is checked in full with its holes
  justified by the solution's environment. What the challenge's
  closure holds
  #src("ConLeche/Verify/CompareInput.lean", 140, 142)[depends only on the files under the trusted directories]:
  it is the same on two file systems that agree on every path the
  reader forms there, so an accepted run speaks of the trusted files
  alone. In both modes,
  everything the challenge imports is part of what is checked.

  A hole is an axiom other than the built-in ones (`propext`,
  `Classical.choice`, `Quot.sound`, the compiler-trust family), or
  #src("ConLeche/Cached/Justify.lean", 52, 61)[a definition, theorem or opaque constant whose value uses `sorry`],
  read as the axiom of its statement;
  #src("ConLeche/Cached/Justify.lean", 69, 77)[an axiom at the name of a constant the checker computes with]
  (a certified `Nat` operation, a compiler-trust operation) takes its
  own check instead.
  #src("ConLeche/Cached/Justify.lean", 200, 216)[The check of a hole]
  asks for the justification, then checks the hole's type as any
  axiom's, and installs the axiom.
  #src("ConLeche/Cached/Justify.lean", 185, 196)[The justification]
  looks the name up in the solution, compares the statements up to
  the names of the level parameters, and walks everything the
  statement reads: each name reached must be
  #src("ConLeche/Cached/Justify.lean", 117, 126)[the same constant in both],
  where a definition, theorem or axiom may be the solution's at the
  challenge's level-parameter names, and a hole the statement of the
  solution's constant. The walk follows a constant's laws, and
  #src("ConLeche/Cached/Justify.lean", 148, 162)[from a type former its constructors and its block's recursors, and every name of the same record],
  so an inductive block is shared whole, at the same level-parameter
  names, or not at all.

  The proof takes a shared inductive block whole: every constant of
  the block gets the solution model's set, and the block's laws read
  only shared constants. It renames
  #src("ConLeche/Model/Solution.lean", 16, 24)[the solution's model to the challenge's level-parameter names]
  and follows the challenge's check:
  #src("ConLeche/Model/Solution/Fold.lean", 17, 25)[a shared record takes the solution's sets, a justified hole the solution's value, any other record its own step].
  The capstone
  #src("ConLeche/MainTheorem.lean", 133, 141)[states] @thm:cmp-model
  for the checker's functions: if `checkDecls` accepts the solution's
  records and `checkChallenge` accepts the challenge's with them, the
  challenge's own constants have a model.
  #src("ConLeche/MainTheorem.lean", 561, 568)[Its corollary for the command line]
  says the same of an exit 0 of
  `--compare CHALLENGE.ndjson SOLUTION.ndjson`, and
  #src("ConLeche/MainTheorem.lean", 536, 547)[a challenge file with a hole of type `False` is never solved].

  The tool #link("https://github.com/leanprover/comparator")[leanprover/comparator] makes the same kind of check with a
  different rule. A theorem must be a theorem on both sides, and a
  definition a definition; every other constant the statements reach is
  compared with Lean's own equality on declarations, level-parameter
  names, binder names and annotations included. Con-leche accepts as
  the justification of a hole a constant of any kind that states the
  same, compares only what the statement reads, closed under reads, and
  compares definitions, theorems and axioms up to the names of their
  level parameters.
]

== Comparing modules <sec:cmp-modular>

When a development is checked module by module (@sec:modular), the
challenge $c$ is one more module, and it passes the local checks of
@sec:mod-local like any other module. Its imports are its own imports
and the solution $s$, with the solution's full own environment as the
view. So its context $Gamma_c$ is assembled from the views of both, and
every two copies of a context name in these views agree (@def:valid).

A declaration of the challenge is a _copy_ when a view it imports
stores one of its names. A copy is not one of the challenge's
declarations $D_c$. Its names are names of the context $Gamma_c$, read
from the module $From_c (n)$ like any imported name, and its entry in
$E_c$ is the context's entry. The checker compares a copy with that
entry. Let the entry have level parameters $arrow(q)$ and type $T$, and
let the copy have level parameters $arrow(p)$, distinct and as many as
$arrow(q)$. A hole, a theorem or an opaque constant is a copy of the
entry's statement,
$
  T_c = T [arrow(q) := arrow(p)];
$
a definition has the entry's value too, renamed in the same way, and
an inductive block is the same block. Every other declaration of the
challenge is its own, in $D_c$, and is checked. A hole among them is
rejected: no view supplies its value.

The closure condition of @sec:cmp-what has no counterpart here. The
challenge and the solution are read in one context. A name that a
copy's statement reads is one entry of $Gamma_c$, whichever views
store it, and the agreement of copies gives every copy of it one value
in the models.

#theorem(name: "The challenge has a solution, module by module")[
  Let the modules $j <= c$ pass their local checks. There is a
  compatible family of models
  #src("whitepaper/Fragment/Compare.lean", 366, 407)[in which the type of every entry of the challenge's context is inhabited by the value of the module it is read from]:
  $
    & (forall j <= c. thin Pass_j) ==>
      exists (m_j in Mod(E_j))_(j <= c). thin Cmp_(c+1) ((m_j)) and \
    & quad forall (n.\{arrow(q)\} : T) in Gamma_c. thin forall phi, rho, arrow(ell). thin
      m_(From_c (n)) (n)(phi(arrow(ell))) in lden T[arrow(q) := arrow(ell)] rden_rho "in" m_c.
  $
  The same holds of $T$ renamed to distinct level parameters
  $arrow(p)$ with $|arrow(p)| = |arrow(q)|$, so of every copy:
  $
    m_(From_c (n)) (n)(phi(arrow(ell))) in
      lden T[arrow(q) := arrow(p)][arrow(p) := arrow(ell)] rden_rho "in" m_c.
  $
] <thm:cmp>

#proof[
  @thm:mod, through the local checks (@sec:mod-local), gives the
  compatible family. A checked declaration stores only fresh names, so
  #src("whitepaper/Fragment/ModularModel.lean", 158, 173)[every entry of $Gamma_c$ is an entry of $E_c$],
  and the typing law of $m_c$ (@def:model) puts $m_c (n)(phi(arrow(ell)))$
  in its type. Compatibility says that $m_c (n) = m_(From_c (n)) (n)$.
  For a renamed statement, @lem:cmp-rename gives
  $T[arrow(q) := arrow(p)][arrow(p) := arrow(ell)] = T[arrow(q) := arrow(ell)]$.
]

The copies take the place of the justified holes of
@sec:cmp-model: the value at a copy is the value of the module it is
read from, the solution's for a hole the solution fills. The model of
the challenge needs no construction of its own, since @thm:mod builds
it as it builds every module's.

The attack of @sec:cmp-attack fails here in two ways. If the
challenge declares $f : Nat := 3$ itself and the solution declares
$f : Nat := 5$, the challenge's $f$ is a copy of the solution's, and a
definition is a copy only with the entry's value; the checker rejects
it.

In the second way, a module $a$ declares $f : Nat := 3$, and the
challenge imports $a$ and has the hole $t : f = 5$. A solution that
does not import $a$ declares its own $f : Nat := 5$ and proves $t$ by
unfolding it. The challenge's views then store two copies of $f$,
$a$'s and the solution's. Whichever of them the challenge reads $f$
from, the module of the other copy declares $f$ itself, and that copy
is no proof. Such a copy
#src("whitepaper/Fragment/Compare.lean", 345, 360)[agrees only as a proof],
so the challenge does not pass its local checks. In an accepted
challenge that imports $a$, $f$ is $a$'s $f$, and it is $3$ in every
model of the compatible family.

#real[
  The modular modes compare by this rule: `--olean --compare` with
  `--module`, `--modular` or `--schedule`, and `--check-graph --compare`.
  The challenge is
  #src("ConLeche/Driver/CompareModule.lean", 11, 23)[one more module of a modular run]
  over the closures of the challenge and the solution, with
  `import all` of the solution added to its header. It loads what Lean
  loads for such a module, under Lean's rule for two loaded copies of
  one name, applied to every loaded name: two copies of a name are one
  constant, or the module is rejected. So a solution that declares its
  own $f$ beside the challenge's import of $a$ is rejected as the
  attack above is.
  #src("ConLeche/Driver/Worker.lean", 106, 123)[A record of the challenge some name of which a loaded module stores is a copy],
  and its names are read into the context like any imported name.
  #src("ConLeche/Driver/Worker.lean", 191, 223)[The check of a copy]
  asks a hole (an axiom, or a definition whose value uses `sorry`), a
  theorem or an opaque constant to have the loaded constant's
  statement, a definition its value too, both up to the names of the
  level parameters, and an inductive block to be the same record. A
  model reads a constant's level parameters by position, so a renamed
  copy has the laws of the loaded constant. Every other record is
  checked as any module's, and
  #src("ConLeche/Driver/Worker.lean", 233, 240)[a hole among them is rejected].
  Each module of the challenge's closure is read from the trusted
  directories alone.

  #src("ConLeche/MainTheorem.lean", 447, 487)[The modular capstones]
  state @thm:cmp for an exit 0 of every command of such a run, and of
  the run in one process: on every snapshot that agrees with the run's
  under the challenge's directories, every module of the challenge's
  closure, the challenge with its copies among them, has a model of
  its constants, and a name a module sees as another module's has the
  value that module's model gives it. In particular,
  #src("ConLeche/MainTheorem.lean", 490, 525)[a challenge whose closure holds a theorem of type `False` is never solved].
]
