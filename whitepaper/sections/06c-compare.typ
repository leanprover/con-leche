#import "../lib.typ": *

// Notation local to this file, matching §3 and §7.
#let Mod = $op("Mod")$
#let Valid = $op("Valid")$
#let Cmp = $op("Cmp")$
#let From = $op("src")$
#let Side = $op("Pf")$
#let Nat = $sans("Nat")$
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked

= Comparing a challenge with a solution <sec:compare>

A _challenge_ is a module that states what is asked: theorems without
proofs, and definitions without values. A _solution_ is a module that
supplies them. The checker compares the two and accepts when the
solution answers the challenge. This section says what is compared,
and what an accepted comparison means in the model: the challenge's
statements hold, each with the solution's value as its witness, and
every name the challenge imports means what it means in the module
that declares it. The argument is a case of @sec:modular.

== Challenges and solutions <sec:cmp-what>

#definition(name: "Challenge, holes, solution")[
  A _challenge_ is a module $c$ of a development, with own names
  $N_c$, the names its declarations introduce. Its _holes_ are the
  own names left open, a set $H_c subset.eq N_c$. In Lean these are the
  module's axioms and the declarations whose value uses `sorry`. In the
  challenge's environment a hole is an assumption, its level
  parameters and its type:
  $
    n in H_c ==> E_c (n) = (n.\{arrow(p)\} : T).
  $
  Everything $c$ imports is fixed. A _solution_ is an earlier module
  $s < c$ whose own environment stores every name of $N_c$.
]

The challenge is not checked. It is a module validated by comparison
(@sec:mod-local): its own environment is its context,
$
  E_c = Gamma_c,
$
#src("whitepaper/Fragment/ModularModel.lean", 724, 731)[assembled]
from the views of its imports, which are its own imports and the
solution. The challenge reads each of its own names from the
solution: $From_c (n) = s$. It reads each name it imports from that
name's _home_, the module that declares it.

== The comparison rule <sec:cmp-rule>

Assembly (@sec:mod-instance) compares every entry of $E_c$ with the
entry the module it is read from stores under the same name. For the
three kinds of names this gives three rules.

+ *A hole is filled* by the solution's entry of its name with the
  same level parameters and type. The entry may be of any kind that
  states something: a definition, a theorem, or an assumption. An
  assumption of $E_c$ refines all of these, and assembly allows nothing
  else in its place.
+ *Every other declaration of $c$* is the solution's entry,
  unchanged. A theorem is stored as an assumption of its statement, so
  for a theorem only the statement is compared.
+ *An imported name is identified by its home*. The challenge reads
  it from its home, and every other copy of it that the challenge
  loads must agree with the home's copy (@sec:mod-thm). What the copies
  contain does not decide it.

Level parameters are compared by position. A declaration's level
parameters are bound by the declaration, and the models read a
constant's set off a list of levels by position (@def:model). Renaming
them changes none of the constant's laws:

#lemma(name: "Renaming level parameters")[
  Let $T$ use only the level parameters $arrow(p)$, and let
  $arrow(q)$ be distinct names, as many as $arrow(p)$. Then for every
  level list $arrow(ell)$ with $|arrow(ell)| = |arrow(p)|$,
  #src("whitepaper/Fragment/Compare.lean", 90, 96)[renaming does not change the instances]:
  $
    T[arrow(p) := arrow(q)][arrow(q) := arrow(ell)] = T[arrow(p) := arrow(ell)].
  $
] <lem:cmp-rename>

So the comparison may first rename the solution's level parameters to
the challenge's, position by position, and then compare. The renamed
entry has the same instances, hence the same laws, and the model of
the solution serves it unchanged. Below, entries are compared at equal
names.

The comparison checks no types. Assembly checks that the challenge's
entries are the solution's or assumptions of their types, that what
each entry reads is in scope, and the block conditions of @sec:ind.
@thm:mod then supplies the challenge's model from the solution's.

== Why the home decides <sec:cmp-home>

The third rule is needed because the challenge cannot see every
value it relies on. Let a module $a$ declare
$
  f : Nat := 3,
$
and present $f$ to its importers as an assumption $f : Nat$, its
value hidden. The challenge $c$ imports $a$ and has one hole,
$
  t : f = 5.
$
A solution $s$ that does not import $a$ declares its own $f : Nat := 5$,
and proves $t$ by unfolding it.

Consider a comparison that matches every entry of the challenge with
the solution's entry of the same name and with nothing else, so that
the challenge reads $f$ from $s$. The challenge's entry $f : Nat$ is an
assumption of the type of $s$'s definition, so the match succeeds. The
environment $E_c$ stores $f : Nat$ and $t : f = 5$, and it has a model
in which every hole is inhabited: the one that gives $f$ the value $5$. This is what
@cor:mod states, every stored type is inhabited in some model of $E_c$,
and it is true here. But the challenge asked about $a$'s $f$,
which is $3$, and $3 = 5$ is false. A statement of the form "the
challenge's environment has a model with every hole inhabited" says
nothing about what the imported names mean.

The statement we want fixes the imported names: in the model of the
challenge, every imported name has the value its home's model gives
it. Then $f$ is $3$, the type of $t$ is the empty proposition $3 = 5$,
and no model inhabits it. So no comparison that gives this statement
can accept $s$.

The modular theorem gives it once $c$ reads $f$ from its home $a$.
No separate check is needed: the agreement of copies (@sec:mod-thm)
enforces the rule. The solution's view stores $f$, so its copy must
agree with $a$'s. It is not $a$'s copy, and $s$ does not read $f$ from
$a$, since $f$ is not in its context. That leaves the third case of
agreement:

#lemma(name: "The home rule")[
  Let module $i$ be valid, $n$ a name of its context, and $(j,V)$ an
  imported view storing $n$ with $j != From_i (n)$, where $n$ is not
  in $Gamma_j$: module $j$ declares $n$ itself. Then
  #src("whitepaper/Fragment/Compare.lean", 130, 135)[both copies are proofs]:
  $
    Side_i (n,(j,V)) and forall (h,W) in X_i. thin
      h = From_i (n) and n in W ==> Side_i (n,(h,W)).
  $
] <lem:cmp-home>

A solution that declares an imported name itself is therefore rejected,
unless both copies are proofs of one statement. Two such copies get
the point in every model, so they agree.

== The challenge has a solution <sec:cmp-thm>

#theorem(name: "The challenge has a solution")[
  Let the modules $j <= c$ be valid, the challenge $c$ by comparison.
  There is a compatible family of models
  #src("whitepaper/Fragment/Compare.lean", 154, 162)[in which the type of every entry of the challenge is inhabited by the value of the module it is read from]:
  $
    & (forall j <= c. thin Valid_j) and E_c = Gamma_c ==>
      exists (m_j in Mod(E_j))_(j <= c). thin Cmp_(c+1) ((m_j)) and \
    & quad forall (n.\{arrow(p)\} : T) in E_c. thin forall phi, rho, arrow(ell). thin
      m_(From_c (n)) (n)(phi(arrow(ell))) in lden T[arrow(p) := arrow(ell)] rden_rho "in" m_c.
  $
] <thm:cmp>

#proof[
  @thm:mod gives the compatible family. Compatibility says that
  $m_c (n) = m_(From_c (n)) (n)$ for every name $n$ of $Gamma_c = E_c$,
  and the typing law of $m_c$ (@def:model) puts $m_c (n)$ in its
  type.
]

Read for the two kinds of names, the theorem says what was asked.
A hole is read from the solution, so its type is inhabited in the
challenge's model by the solution's value. An imported name is read
from its home, so it has the home's value, and the holes' types are
read with it. In the example of @sec:cmp-home, every model of the
family gives $f$ the value $3$, and the type of $t$ is empty; so no
solution of that challenge is accepted.

The consistency argument applies as well. If the challenge stores the
recursor of an empty proposition, as in @cor:mod, that proposition has
no closed inhabitant, and the challenge cannot also have a hole of that
type that an accepted solution fills.

== Locality <sec:cmp-local>

The theorem speaks of the challenge's environment, its holes, and the
models of the modules it reads its names from. The solution enters
only through the values of the holes. What an accepted comparison
means is therefore fixed by the challenge and by what it imports, and
these must come from a source the reader trusts.

#real[
  Con-leche compares compiled modules,
  `con-leche --olean --compare CHALLENGE SOLUTION`. The challenge and
  everything it imports are read from the trusted directories
  (#src("ConLeche/Driver/Compare.lean", 236, 242)[the challenge's lookup]),
  the solution's closure from those directories first and from the
  search path after them; a module the trusted directories hold is
  read from there on both sides. The challenge's read
  #src("ConLeche/Verify/Frontend/Olean/Local.lean", 469, 471)[depends only on the files under the trusted directories]:
  on two file systems that agree on every path the reader forms there,
  it has the same outcomes, failure included.

  A hole is #src("ConLeche/Driver/Compare.lean", 114, 120)[an axiom of the challenge module, or a declaration whose value uses `sorry`].
  #src("ConLeche/Driver/Compare.lean", 136, 178)[The comparison] fills
  it with the solution's definition, theorem, opaque constant or
  axiom of the same type, after renaming the solution's level
  parameters to the challenge's; it compares every other declaration
  of the challenge the same way, and identifies an imported name by
  its home, the first module of the challenge's closure that stores it,
  or, for a theorem, by its statement. The solution's closure is then
  checked as any closure is. The compared run is a development of two
  modules,
  #src("ConLeche/Model/Modular/Compare.lean", 571, 573)[the solution and the challenge],
  and the modular theorem
  #src("ConLeche/Model/Modular/Compare.lean", 652, 665)[reads the challenge's model off the solution's],
  carried across the renaming by
  #src("ConLeche/Model/Copies.lean", 421, 422)[a model of a renamed copy].
  The capstone
  #src("ConLeche/MainTheorem.lean", 357, 379)[states] @thm:cmp
  for an exit 0 of the run: the challenge's model gives every name the
  solution's value, and every hole is inhabited. The challenge's
  environment holds what it imports with the bodies, and a model makes
  every definition denote its value and every recursor rule hold, so
  the statement alone excludes the attacks: a challenge that imports
  `def f : Nat := 3` and has a hole `t : f = 5` has no model with `t`
  inhabited, and the constructors of a challenge's
  `inductive T | a | b` denote different sets, whatever the solution's
  `T` is. The home rule is a rule of the comparison, not part of the
  statement. Together with locality,
  #src("ConLeche/MainTheorem.lean", 402, 410)[an accepted comparison is a property of the trusted files]:
  on every file system that agrees with the run's under the trusted
  directories, the challenge's read gives an environment with a model
  in which every hole is inhabited.

  The same comparison also runs module by module, with `--module`,
  `--modular` or `--schedule`: the challenge is
  #src("ConLeche/Driver/CompareModule.lean", 210, 211)[one more module of a modular run]
  over both closures, its names read from the modules of the
  solution's closure that declare them, and each module of the
  challenge's closure is read from the trusted directories alone.
  #src("ConLeche/MainTheorem.lean", 517, 525)[The modular capstones]
  state the same for an exit 0 of every command of such a run: every
  module has a model of its own environment, a name a module reads from
  another means the same in both models, and the challenge's model
  inhabits every hole. A name the challenge reads from a module that
  defines it, body hidden or not, is that definition's value there.

  Con-leche also compares two `lean4export` files, the input
  comparator works on,
  `con-leche --compare CHALLENGE.ndjson SOLUTION.ndjson`. An export
  has no modules and so no homes: every declaration of the challenge
  file is the challenge's own and is compared by its content, so the
  solution's `f := 5` does not meet a challenge file's `f := 3`, and
  the solution's file is checked in full.
  #src("ConLeche/MainTheorem.lean", 901, 923)[Its capstone] states the
  same conclusion over the challenge file's bytes, which are all the
  challenge's meaning depends on.

  The tool #link("https://github.com/leanprover/comparator")[leanprover/comparator] makes the same kind of check with a
  different rule. A theorem must be a theorem on both sides, and a
  definition a definition; every other constant the statements reach is
  compared with Lean's own equality on declarations, level-parameter
  names, binder names and annotations included; and a constant is
  looked up by its name, with no notion of a home. Con-leche fills a
  hole with an entry of any kind that states something, compares only
  what the model reads, and identifies an imported name by its home.
]
