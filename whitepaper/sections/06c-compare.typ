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

A _challenge_ states what is asked: statements whose proofs, or
values, are left open. A _solution_ supplies them. The checker checks
the solution as it checks any input. It then checks the challenge as
any input, with one exception: an open statement of the challenge is
accepted when the solution _justifies_ it. This section states the
rule, shows that the constants of an accepted challenge have a model,
and shows why the rule compares more than the open statement itself.
@sec:cmp-modular compares module by module: there the challenge is one
more module, which imports the solution, and its declarations that the
solution already holds are read from the solution instead of being
checked.

== Holes and justification <sec:cmp-what>

#definition(name: "Challenge, hole, solution")[
  A _challenge_ is an input that the checker checks declaration by
  declaration, as in @sec:env and @sec:ind; write $E_c$ for its
  environment. A _hole_ of the challenge is an assumption it declares:
  a name $n$ with level parameters $arrow(p)$ and a type $T$, and no
  value,
  $
    (n.\{arrow(p)\} : T).
  $
  A _solution_ is an environment $E_s$ that the checker has accepted.
]

An assumption can state anything, an empty proposition included, so
the checker does not accept a hole on its own. With a solution, a hole
is accepted when the solution stores a constant of the same name that
states the same, and everything the statement reads means the same in
both environments. The second condition is a closure condition on
names: a name the statement reads must itself be stored alike, and so
must every name that this name's entry reads, and so on.

#definition(name: "Shared names, justified hole")[
  A set $Sh$ of names is
  #src("whitepaper/Fragment/Compare.lean", 361, 365)[_shared_]
  between $E_c$ and $E_s$ when every $d in Sh$ satisfies two
  conditions. First, $E_s$ stores $d$, and $E_c$ stores $d$ as a
  definition or an assumption, in one of two ways:
  + $E_c$ stores $d$ with the same entry as $E_s$, or
  + $E_c$ stores $d$ as an assumption $(d.\{arrow(p)\} : T)$ with
    distinct level parameters $arrow(p)$, and $E_s$ stores $d$, of any
    kind, with level parameters $arrow(q)$, as many as $arrow(p)$, and
    a type $T_s$ such that
    $
      T = T_s [arrow(q) := arrow(p)].
    $
  Second, every constant that the type or the value of $d$'s entry in
  $E_c$ reads is in $Sh$ again. A hole of the challenge is
  #src("whitepaper/Fragment/Compare.lean", 369, 369)[_justified_]
  by $E_s$ when its name lies in a shared set. The
  #src("whitepaper/Fragment/Compare.lean", 376, 385)[challenge check]
  is the check of §3 and §4, with one more step: a fresh hole whose
  type is in scope and which $E_s$ justifies is stored as an
  assumption.
]

The level parameters are compared by position. A declaration's level
parameters are bound by the declaration, and a model reads a
constant's set off a list of levels by position (@def:model). Renaming
them changes none of the constant's instances:

#lemma(name: "Renaming level parameters")[
  Let $T$ use only the level parameters $arrow(q)$, and let
  $arrow(p)$ be distinct names, as many as $arrow(q)$. Then for every
  level list $arrow(ell)$ with $|arrow(ell)| = |arrow(q)|$,
  #src("whitepaper/Fragment/Compare.lean", 124, 127)[renaming does not change the instances]:
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
  forall d in Sh. thin M_c (d) = M_s (d),
$
where, for two assignments $M$ and $M'$ and a name $d$, $M(d) = M'(d)$
means agreement at every list of natural numbers:
$M(d, arrow(k)) = M'(d, arrow(k))$ for all $arrow(k)$. Here $Sh$ is a
shared set read in the challenge's final environment, holding the
names of all justified holes. Three facts carry the construction. The
first says that a denotation reads the model only at the constants the
term reads:

#lemma(name: "Denotation is local")[
  Let $M$ and $M'$ be assignments and $e$ a term, and write
  $consts(e)$ for the constants $e$ reads. If $M$ and $M'$ agree on
  $consts(e)$, then at every valuation and every variable environment
  $rho$
  #src("whitepaper/Fragment/Compare.lean", 161, 163)[$e$ denotes the same in both, and is well-denoted in both alike]:
  $
    (forall d in consts(e). thin M(d) = M'(d)) ==>
      lden e rden_rho "in" M = lden e rden_rho "in" M'
      and (rho models e "in" M <==> rho models e "in" M').
  $
] <lem:cmp-local>

The second gives a justified hole the solution model's set:

#lemma(name: "A justified hole")[
  Let $E_c$ be closed, with a model $M_c$, and let
  $(n.\{arrow(p)\} : T)$ be a fresh assumption, with distinct level
  parameters $arrow(p)$ and a type in scope of $E_c$. Let $E_s$, with
  a model $M_s$, store $n$ with level parameters $arrow(q)$, as many as
  $arrow(p)$, and a type $T_s$ that uses only $arrow(q)$, with
  $T = T_s [arrow(q) := arrow(p)]$, and let $M_c$ and $M_s$ agree on
  every constant $T$ reads. Then
  #src("whitepaper/Fragment/Compare.lean", 284, 293)[$M_c$ extends to a model of the environment with the hole, with the solution model's set at $n$]:
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
  model $M_s$, store an entry $D$ at a name $d$ fresh in $E_c$, a
  definition or an assumption whose type and value are in scope of
  $E_c$. If $M_c$ and $M_s$ agree on every constant that the type and
  the value read, then
  #src("whitepaper/Fragment/Compare.lean", 319, 328)[$M_c$ extends to a model of the environment with $d$'s entry, with the solution model's set at $d$]:
  $
    exists M'_c in Mod(E_c, D). thin
      M'_c (d) = M_s (d) and forall d' in E_c. thin M'_c (d') = M_c (d').
  $
] <lem:cmp-shared>

The typing and unfolding laws of the new constant are those of $M_s$,
carried over by @lem:cmp-local. Both lemmas extend a model at
#src("whitepaper/Fragment/Compare.lean", 179, 192)[a given set], as
@sec:env extends it at a definition's value.

#theorem(name: "The challenge has a model")[
  Let the checker accept the solution, and accept the challenge with
  its holes justified by the solution's environment $E_s$. Then
  #src("whitepaper/Fragment/Compare.lean", 675, 677)[the constants of the challenge have a model]
  (@def:input-model), a hole holding as the assumption of its
  statement: for the challenge's declarations $D_c$,
  $ exists M. thin M "is a model of the constants of" D_c. $
] <thm:cmp-model>

The statement does not mention the solution. Its model is a device of
the proof, the source of the holes' sets.

#proof[
  Take a model $M_s$ of $E_s$, as in the proof of @thm:accepted-model.
  #src("whitepaper/Fragment/Compare.lean", 548, 552)[Induction along the challenge's check]
  builds a model $M_c$ of the challenge's environment that agrees with
  $M_s$ on the shared names stored so far. A declaration none of
  whose names is shared takes its own step (@sec:env, @sec:ind), which
  keeps every stored constant's set. A shared definition or assumption
  takes @lem:cmp-shared: everything it reads is shared and stored
  before it, so the agreement so far is the agreement the lemma asks
  for. A justified hole takes @lem:cmp-hole, with the agreement on its
  type's constants in the same way. Both give the new name the
  solution model's set, so the agreement extends to it.
  Every constant of the challenge is stored in its final environment
  as declared, so it holds in $M_c$, as in @thm:accepted-model.
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
  con-leche compares two `lean4export` files,
  `con-leche --compare CHALLENGE.ndjson SOLUTION.ndjson`. It checks
  the solution's file in full, then the challenge's file
  #src("ConLeche/Cached/Decls.lean", 110, 116)[with the solution's environment justifying its holes].
  It compares compiled modules by the same rule,
  `con-leche --olean --compare CHALLENGE SOLUTION`: the solution's
  closure is checked in full, then the challenge's closure, read from
  the trusted directories alone, is checked in full with its holes
  justified by the solution's environment; what that closure holds
  #src("ConLeche/Verify/CompareInput.lean", 140, 142)[depends only on the files under the trusted directories],
  so an accepted run speaks of the trusted files alone. In both modes,
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
  #src("ConLeche/Model/PureChecker.lean", 41, 47)[states] @thm:cmp-model
  for the checker's functions: if `checkDecls` accepts the solution's
  records and `checkChallenge` accepts the challenge's with them, the
  challenge's own constants have a model.
  #src("ConLeche/MainTheorem.lean", 61, 66)[Its corollary for the command line]
  says the same of an exit 0 of
  `--compare CHALLENGE.ndjson SOLUTION.ndjson`. A model of the
  challenge holds no hole of type `False`, since `False` denotes the
  empty set.

  The rule is a design choice, and another tool chooses differently:
  #link("https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator")[`lake comparator`] makes the same kind of check with a
  stricter rule. A theorem must be a theorem on both sides, and a
  definition a definition; every other constant the statements reach is
  compared with Lean's own equality on declarations, level-parameter
  names, binder names and annotations included. con-leche accepts as
  the justification of a hole a constant of any kind that states the
  same, compares only what the statement reads, closed under reads, and
  compares definitions, theorems and axioms up to the names of their
  level parameters.
]

== Comparing modules <sec:cmp-modular>

When a development is checked module by module (@sec:modular), the
challenge $c$ is one more module, and it passes the local checks of
@sec:mod-local like any other module. It imports the imported views
of its own imports and one more, the solution $s$ with the solution's
full own environment. So its context $Gamma_c$ is assembled from these
imported views, and every two copies of a context name in them agree
(@def:valid).

A declaration of the challenge is a _copy_ when one of its names is
already stored by an imported view. A copy is not one of the
challenge's declarations $D_c$. Each name $n$ of a copy is a name of
the context $Gamma_c$, read from the module $From_c (n)$ like any
imported name, and its entry in $E_c$ is the context's entry. The
checker compares the copy with that entry. Let the entry have level
parameters $arrow(q)$ and type $T$, and let the copy have level
parameters $arrow(p)$, distinct and as many as $arrow(q)$, and type
$T_c$. A hole, a theorem or an opaque constant is a copy when it
states the entry's statement,
$
  T_c = T [arrow(q) := arrow(p)];
$
a definition has the entry's value too, renamed in the same way, and
an inductive block is the same block. Every other declaration of the
challenge is its own, in $D_c$, and is checked. A hole among them is
rejected: no imported view supplies its value.

The closure condition of @sec:cmp-what has no counterpart here. The
challenge and the solution are read in one context. A name that a
copy's statement reads is one entry of $Gamma_c$, whichever imported
views store it, and the agreement of copies gives every copy of it one
value in the models.

#theorem(name: "The challenge has a model, module by module")[
  Let the modules $j <= c$ pass their local checks. Then there are
  assignments $M_j$, for $j <= c$, such that
  + #src("whitepaper/Fragment/Compare.lean", 771, 776)[every module $j <= c$ has a model $M_j$ of the constants of $D_j$]
    (@def:input-model);
  + $M_j (n) = M_(j') (n)$ whenever $j$ sees $n$ as $j'$'s, for
    $j, j' <= c$, as in @thm:mod-input;
  + every copy holds in the challenge's model: for every entry
    $(n.\{arrow(q)\} : T)$ of $Gamma_c$ and distinct level parameters
    $arrow(p)$ with $|arrow(p)| = |arrow(q)|$, the entry
    #src("whitepaper/Fragment/Compare.lean", 715, 720)[renamed to $arrow(p)$]
    (its type, and a definition's value, renamed; an inductive block's
    entry unchanged) holds in $M_c$.
] <thm:cmp>

#proof[
  @thm:mod-input, through the local checks (@sec:mod-local), gives the
  models and their agreement. A checked declaration stores only fresh
  names, so
  #src("whitepaper/Fragment/ModularModel.lean", 167, 168)[every entry of $Gamma_c$ is an entry of $E_c$],
  and it holds in $M_c$ as every constant of $E_c$ does. A model reads
  a constant's level parameters by position, so by @lem:cmp-rename
  #src("whitepaper/Fragment/Compare.lean", 743, 744)[a copy holds where the constant does].
  The challenge sees each copy's name as the module it is read from,
  so $M_c$ gives it that module's value, the solution's for a hole the
  solution fills.
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
unfolding it. The challenge's imported views then store two copies of
$f$, $a$'s and the solution's. Whichever of them the challenge reads
$f$ from, the other copy comes from a module that declares $f$
itself, not from an earlier module both import. Of the cases of
agreement that @def:valid asks for, only the last is left for it, and
#src("whitepaper/Fragment/Compare.lean", 695, 701)[such a copy agrees only as a proof]:
both copies would have to be proofs, and a definition of $f$ as $3$
or $5$ is none. So the challenge does not pass its local checks. In an accepted
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
  #src("ConLeche/Driver/Worker.lean", 105, 122)[A record of the challenge some name of which a loaded module stores is a copy],
  and its names are read into the context like any imported name.
  #src("ConLeche/Driver/Worker.lean", 208, 240)[The check of a copy]
  asks a hole (an axiom, or a definition whose value uses `sorry`), a
  theorem or an opaque constant to have the loaded constant's
  statement, a definition its value too, both up to the names of the
  level parameters, and an inductive block to be the same record, its
  recursors reading their ι equations off their own types. A
  model reads a constant's level parameters by position, so a renamed
  copy has the laws of the loaded constant. Every other record is
  checked as any module's, and
  #src("ConLeche/Driver/Worker.lean", 250, 257)[a hole among them is rejected].
  Each module of the challenge's closure is read from the trusted
  directories alone.

  #src("ConLeche/MainTheorem.lean", 138, 175)[The modular capstones]
  state @thm:cmp for an exit 0 of every command of such a run, and of
  the run in one process: on every snapshot that agrees with the run's
  under the challenge's directories, every module of the challenge's
  closure, the challenge with its copies among them, has a model of
  its constants, and a name a module sees as another module's has the
  value that module's model gives it. In particular,
  #src("ConLeche/MainTheorem.lean", 179, 198)[a challenge module with a constant of type `False`, a hole `x : False` among them, is never solved].
]
