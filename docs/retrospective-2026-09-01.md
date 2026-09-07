# Retrospective memo — why the Θ sort-coherence campaign keeps failing, and what to do instead

Step-back analysis, 2026-09-01.  Charter: diagnose the failure mode of the
#151 Θ lane, survey the literature for proof strategies, and recommend
concretely for both lanes.  Everything cited from the repo was read in
`<main-checkout>/.claude/worktrees/retrospective` (branch
`agent/retrospective` = `agent/theta-runbatch` @ f69ba325) and
`<main-checkout>/.claude/worktrees/retro-nbe` (`agent/nbe-lr` @ d199167b).
Literature claims are cited to fetched sources; unverified items are marked.

---

## EXECUTIVE SUMMARY

1. **Why it failed**: the tier proves conversion metatheory for an
   *untyped* algorithm of a theory whose untyped metatheory is broken —
   provably, in the literature (Carneiro's thesis: Lean's defeq is a
   non-transitive underapproximation, SR and CR fail; lean4lean: "untyped
   conversion is not an option [for Lean] because of t-proof-irrel", and
   the corresponding injectivity theorems sit in its repo as sorries
   under *"theorems which we can't prove :("*).  Every refutation in the
   record is one mechanism: a θ-entry's argument does work at the image
   the core lacks — Lévy's redex-creation case III, the exact case where
   backward simulation is false in pure λ-calculus already.
2. **The record's three genuine discoveries are the field's standard
   ingredients**: per-entry typing (= Lennon-Bertrand's "untyped
   conversion is term-directed *typed* conversion"), provenance
   predicates (TeleBuilt/EnvBuilt — both lanes found it independently),
   and the forward dichotomy — which **is van Daalen's Square Brackets
   Lemma** (Endrullis-de Vrijer RTA 2008), published proof, never
   mechanized in any prover.
3. **What to do**: (Θ) build the dichotomy as SqBL over the gate-free
   kit — one focused round, falsifier probe first (K-row
   left-linearity); if a fourth wall appears, exit via mode-gated
   checker certification (the #152/#10 precedent) instead of further
   statement-space search.  (NbE) the remaining chain is standard
   (closest cribs: McTT's `per_univ_elem` uniqueness via evaluation
   functionality; AÖV/CPP-2024 FT architecture); keep the conditional Π
   clause — baked-in convergence is the literature's pattern only
   because its theories normalize, which Lean's does not.  (Global) no
   typed-conversion-equivalence third route exists for Lean's theory;
   con-leche v1 is already past the published frontier (nobody has verified
   a DTT checker against a set model — the only architectural precedent
   is HOL/Candle), so treat #151 as research and portfolio accordingly.

---

## A. DIAGNOSIS

### A.0 What the tier is actually claiming (for orientation)

The tier's centerpiece is stated in
`ConLeche/SetR/Annot/SortCoh/Claims.lean:7-31`: *"a true defeq verdict plus
sort-computation runs on both arguments forces numeral agreement"* — a
**valuation-free, purely syntactic** statement about the untyped checker's
runs.  The Θ walk (`SortCoh/Theta.lean:19-32`) exists because defeq's
congruence cases open binders with *each side's own* domain; a `ThetaEntry`
carries the annotation pair and the argument pair, and θ (`thetaSubst₁/₂`)
substitutes entries back to relate the opened cores to the closed subjects.
The three remaining sorries are `layerRunCell_of` (ThetaLock.lean:2499),
`runStepF_step` (:8375, 22/25 arms done), `thetaLoopLock_of` (:11057);
`certSortAgree_of` (:11162) was discharged (ThetaRunBatch.md §"SORRY #4
DISCHARGED", :7230).

### A.1 The failure record, compressed to its mechanism

Every major refutation in the record has **one shared mechanism**, and the
record itself says so:

1. **`ThetaDefeqSimF` refuted** (ThetaRunBatch.md:3787-3922,
   `_tmp/delta151.lean`): two distinct proofs `pa, pb` of one proposition are
   kernel-defeq via `proofIrrel`; placed in **head position and applied**, the
   images are a pair the kernel *cannot even type* (`infer` throws "function
   expected").  The book's own words: *"the Θ relation is not closed under
   application contexts, because the kernel's `proofIrrel` is not a
   CONGRUENCE rule … The reference kernel is sound anyway because it only
   ever applies `proofIrrel` to WELL-TYPED terms … That is typing — i.e.
   Object 1."*
2. **`certSortAgree_of` refuted + two landed theorems above it**
   (ThetaRunBatch.md:4607-4700): same geometry — *"`proofIrrel` relates two
   IN-ZONE leaves at DIFFERENT indices, and θ then sends them to two
   UNRELATED entries"* — named as **the uniform root cause across all seven
   residues** (:4696).
3. **image-landing ⟹ core-shape is FALSE** (the convergence event,
   ThetaRunBatch.md:9688-9745, `_tmp/inverse151.lean`): a telescope entry
   whose argument is `fun _ => Sort 0`; the core `.app (.fvar d) (.sort 0)`
   is inert, its θ-image is a β-redex reaching a sort.  *"θ can fire a β the
   core cannot, because the telescope's argument supplies a λ the core's own
   head never had. The same shape as the δ-sim refutation."*  This killed the
   whole disposal family: route (a), (a)-at-the-reduct, and (b)'s carriage.
4. **`Clean` transport refuted** (ThetaRunBatch.md:6773-6836): whnfCore's β
   can contract a non-leaf to a leaf, so a zone-cleanliness predicate cannot
   be transported from cores to their whnf outputs.
5. **The composite-column obstruction, six appearances**
   (concat wall :5238, descent :5338, C2-indexing :5427, emitters :6117,
   `TeleZoneAnn` does not survive `concat`, …), finally tamed only by
   **provenance predicates**: `TeleBuilt`/`RowBuilt` (:8719-9420) —
   hereditary, with *definitional inversion*, introduced at the push sites
   the walk itself executes.
6. **Model-side arbitration closed** (the lane's earlier findings, restated
   in `ConLeche/NbE/DESIGN.md:333-340` from the other side):
   `kind_not_semantic`, `piC_dom_not_determined` (a denotation does not
   determine the Π family), universes overlapping at `pt` — the untagged set
   model cannot supply structure agreement.

The sim kit is one-directional by construction: `SubstSim.lean:266-296`
(`WhnfCoreSubstSimF` etc.) has shape *core-run ⟹ image-`RawReach`*, and the
fit-check record (:9624-9686) is explicit that *"the inverse is the refuted
transport's own shape."*

### A.2 Hypothesis (i): subject-reduction-strength metatheory about an untyped algorithm — **CONFIRMED, with a sharpening**

The record confirms it in its own voice, three times: the δ-sim refutation
ends at "that is typing"; the PROJ-(b) stop is titled *"the entry AGREEMENT
is load-bearing, and it is typing"* (:3569); `witness_killed_by_typing`
records that any kernel-typeability premise on the frame subjects excludes
the witness and *"no syntactic premise does"* (:3890-3899).

The sharpening, which matters for strategy: **adding typing does not buy the
standard SR package here, because for Lean's theory that package is refuted
in-tree.**  The TT tombstone (`ConLeche/TTVerify/DESIGN.md:1580-1660`) records:
Π-domain-injectivity refuted by `propext`; the official kernel's global
justification "everything reduction sees descends from a well-typed term"
*is* subject reduction, which the TT layer refutes by design; and the
verification-architecture ruling records unique typing, SR, and
executable-defeq transitivity/stability all refuted or contradicted by the
arena's own tests.  So the campaign was attempting something *strictly
harder* than what MetaCoq does for PCUIC: proving conversion metatheory
without typing, for a theory where even the typed metatheory
(SR/UT/injectivity) fails.  The official kernel's real safety argument is
not a theorem of this shape at all — it is *"we only ever feed defeq terms
we typed, and we trust the outcome"*; the literature confirms Lean's defeq
is not transitive (see B.2), i.e. some of what the tier chased is false in
the reference theory, not merely hard.

### A.3 Hypothesis (ii): forward-only is intrinsic — **CONFIRMED; it is the classic residual/creation asymmetry**

Substitution is a forward simulation and provably not a bisimulation.  The
mechanized witness (:9693-9708) is precisely a **created redex** in Lévy's
classification (see B.4): substituting a λ-valued entry for a variable in
applied position creates a β-redex that has no ancestor in the core.  Every
"disposal" route that needed image-landing ⟹ core-shape was asking for
backward simulation across redex creation, which is false in the pure
λ-calculus already — no amount of walk-side bookkeeping could have made it
true.  The surviving candidate (widened waiver `InZoneHeaded` + forward
dichotomy, :9747-9826) is exactly the correct classical move: **classify
image steps into residuals of core steps vs. steps at θ-created positions**,
i.e. run *with* the simulation's grain.  Section C.1 grounds this in the
standardization/residuals literature.

### A.4 Hypothesis (iii): the tier is the price of retrofitting the collapse — **PARTLY CONFIRMED, reframed**

True: the v1 model collapsed exactly the structure (levels, Π-domains) that
`interp2` now needs, and the model cannot return it (A.1 item 6); the
annotations are the carrier; hence a syntactic coherence tier.  But the NbE
lane shows the price is **not intrinsic to collapse-freedom**: its slice
never inverts the model (*"the model is only ever applied forward
(`univ ∘ eval φ`), never inverted"*, `ConLeche/NbE/DESIGN.md:100-111`), and
class 2 (cross-run sort agreement) is *"absent from this slice,
structurally."*  So the correct statement is: the tier is the price of
extracting structure agreement **from an untyped substitution-based
algorithm's intermediate states**.  The collapse-free upgrade made the debt
visible; the substitution regime is what makes it expensive.

### A.5 Hypothesis (iv): statements false because they generalize over configurations the walk never produces — **CONFIRMED; provenance-first is the systematic answer, and both lanes discovered it independently**

The pattern repeats with remarkable regularity:

* Θ lane: `TeleBuilt`/`RowBuilt` (provenance: *the push sites built this
  telescope*) is what finally made the composite column travel, after six
  extensional formulations died (:8719-9420, §F records).
* NbE lane, the same law from the other side
  (`ConLeche/NbE/DESIGN.md:253-258`): `EnvOk` (extensional) refuted, its
  repair `EnvTyped` (denotational) refuted too, and the finding elevated to
  a **methodological law**: *"in a δ-unfolding checker, an environment
  invariant phrased about denotations is never enough, because unfolding
  re-runs syntax"* — the only workable invariant is `EnvBuilt`, *the checker
  built it*, with `EnvTyped` demoted to a *derived* invariant of built
  environments.

Every refutation witness in A.1 is a configuration satisfying all the
syntactic side conditions (`SubjInv`, `Based`, `PairedLeaves`, pool
discipline — the δ-sim record checks each one) that the real walk never
emits.  The systematic recipe the record supports:

> **State every walk-level lemma over an inductively defined reachability/
> provenance judgment generated by the checker itself, with the invariant as
> a derived theorem of built states — never over the extensional closure of
> the states' syntactic description.**

This is not exotic: it is the same move as the POPL-2018 school indexing
logical relations by *derivations* of reducibility rather than by raw terms
(B.1/B.3), and the same as the in-house Std.HashMap pattern the project
CLAUDE.md already mandates for data structures ("the structure carries its
invariant; downstream never re-proves it").  The Θ lane applied it late and
locally (TeleBuilt), after each wall; applying it *first* — making
`ThetaRelD` itself the provenance judgment, with `SubjInv`/`Based`/pool
facts as theorems *about* it rather than premises *on* it — is the
form-level lesson.

### A.6 One more root the hypotheses miss: completeness-of-a-partial-decider statements

The δ-sim consequence note (:3906-3921) makes a distinction that deserves
top billing: the refuted statements conclude `∃ L', defeqLoop … = .ok true`
— **completeness claims about a partial, gate-carrying decision procedure on
transformed inputs** — while the kit that works (`SubstSim`, `RawReach`)
concludes membership in a **positive, gate-free inductive reduction
relation** with the reduct exhibited.  Completeness claims need closure
properties (congruence, stability under the transform) that Lean's defeq
demonstrably lacks (`proofIrrel` non-congruence is a fact of the reference
theory, not of this formalization).  Rule of thumb the record supports:
**conclusions of walk-level lemmas should be inductive relations or
syntactic equations, never `∃ fuel, run = .ok true`** — runs appear in
premises (what the checker did), relations in conclusions (what must
follow).  The NbE lane learned the matching lesson from the other end: its
LR is stated over fuel-free relational mirrors (`EvalsTo`/`Applies`,
functional by `eval_fun`), not over the fueled functions
(`ConLeche/NbE/DESIGN.md:325-332`).

### A.7 Why it *kept* failing (process, briefly)

The iteration protocol worked as designed — every false statement was
refuted quickly and mechanically, statements were frozen, waivers named.
What it could not do is repair the **statement-space**: the campaign was
exploring a family of claims most of which are false for one reason
(A.1's shared mechanism), and each probe eliminated one formulation at a
time.  The three genuinely load-bearing discoveries (per-entry typing +
`ZoneAnn`, provenance predicates, the forward dichotomy) are exactly the
three ingredients a typed, provenance-indexed, forward-simulation
formulation would have had on day one.  That is hindsight, but it is
transferable hindsight: it is the shape of the NbE lane's remaining chain,
and the shape the literature uses.

---

## B. LITERATURE

All sources below were fetched and read by the research effort behind this
memo (primary PDFs / repos); claims that could not be verified are marked.

### B.1 MetaCoq / PCUIC — untyped conversion + confluence; no backward simulation exists anywhere

Sources read: *Coq Coq Correct!* (POPL 2020,
https://sozeau.gitlabpages.inria.fr/www/research/publications/Coq_Coq_Correct-POPL20.pdf);
*Touring the MetaCoq Project* (arXiv:2107.07670); Lennon-Bertrand, *What
does it take to certify a conversion checker?* (FSCD 2025,
arXiv:2502.15500); MetaRocq repo README.

* PCUIC's conversion is **untyped, on raw terms** — the closure of
  reduction up to α-cumulativity; typing touches it only through the
  cumulativity rule (*Touring* §2.2.1, *CCC* Fig. 2).  There is no mutual
  typing/defeq induction.
* **All inversions go through confluence, never backward simulation.**
  Substitution facts are forward-only (parallel-substitution Thm 2.1);
  Π-injectivity and "undirected conversion = joinability" come from
  parallel reduction + Takahashi's triangle property (*CCC* §2.3.2,
  *Touring* §3.2.3).  Nothing of the shape "reduction of a substituted term
  implies reduction of the original" is stated anywhere.
* **Well-typedness is a function argument.**  The conversion algorithm is
  defined by well-founded recursion on accessibility derived from an SN
  *axiom stated only for well-typed terms*; `wellformed` is a parameter of
  `reduce_stack`; soundness holds by construction on well-typed inputs only
  (*CCC* §3.1-3.5: *"termination and correctness are intertwined … it takes
  well-typed terms as arguments"*).
* Lennon-Bertrand's FSCD 2025 paper is the sharpest statement of our
  situation: *"although no type is visible in the definition of untyped
  conversion, the name 'untyped' is misleading … types are still present in
  invariants, silently keeping the algorithm on rails.  **Untyped
  conversion may thus be more aptly characterised as term-directed typed
  conversion.**"* (§4).  His Fig. 6 makes well-typedness an explicit
  precondition of every algorithmic judgment; his Corollary 3 (*types
  classify normal forms*: a normal form typed at `U` is a type, at
  `Π x:A.B` is a function, …) **is exactly sort coherence**, and his Fig. 1
  dependency table shows it needs injectivity of type constructors only —
  no normalization for positive soundness.  §5 reports Abel-Altenkirch
  **standardization** as the missing-in-MetaCoq companion: *"if a term is
  convertible to a weak-head normal form, it weak-head reduces to a
  weak-head normal form with the same shape."*
* On proof irrelevance (§4.4): SProp *"comes with similar threat to
  completeness of neutral comparison"*; Rocq copes by carrying universe
  information term-directedly; **Lean "re-infers the type of neutrals on
  the fly if their untyped comparison fails"** — i.e. the reference kernel
  itself pays a typing channel at exactly the point where our δ-sim
  refutation lives.

### B.2 lean4lean — our target statements are open conjectures for Lean's theory; backward simulation only along renamings

Sources read: Carneiro, *Lean4Lean: Verifying a Typechecker for Lean, in
Lean* (arXiv:2403.14064v3); the lean4lean repo at commit `8223d223`
(2026-08-29), source inspected directly.

* Soundness target: the `VExpr` typing judgment — **a single typed
  defeq judgment** `Γ ⊢ e ≡ e' : α` with `t-proof-irrel` and `t-extra`
  rules.  §8, verbatim: untyped conversion à la MetaCoq *"is unfortunately
  not an option [for Lean] because of the `t-proof-irrel` rule."*  This is
  the published confirmation of our δ-sim refutation's mechanism.
* **Conjectures 2.7/2.9/2.10 (unique typing; sort/Π-injectivity i.e. sort
  coherence; strengthening) are open.**  In the repo,
  `Theory/Typing/Injectivity.lean` holds `sort_inv`, `forallE_inv`,
  `sort_forallE_inv` as three `sorry`s under the comment *"A bunch of
  important structural theorems which we can't prove :("*.  Unique typing
  is now proved modulo those sorries (`UniqueTyping.lean`, via a
  re-indexed `IsDefEqStrong` judgment — `Strong.lean`, 1180 lines, 0
  sorries — repairing the stratification-vs-substitution failure the paper
  §2.4 describes).
* The in-progress attack (`ChurchRosser.lean`, 2 sorries left in the
  iota-rule cases) is instructive: **reduction is typed and
  context-indexed** (`ParRed : List VExpr → VExpr → VExpr → Prop`, with
  defeq side conditions in the iota rule), and confluence is proved **up to
  an inductive `NormalEq`** whose constructors include `proofIrrel` *with
  three typing premises* — Carneiro's concrete answer to "proofIrrel is not
  a congruence on untyped terms": don't make it one; bake it into a typed
  normal-equality and prove that transitive separately.
* **Grep-verified: every backward simulation in lean4lean is along a
  renaming** (`ParRed.weakN_inv`, `WHRed.weakU_inv`, …, each still carrying
  a typing hypothesis); **no substitution-inversion lemma exists anywhere
  in the repo.**  The step our routes (a)/(b) needed is not merely
  unproved in the field — it is never even stated.
* The checker verification layer is Hoare-style positive soundness on
  well-typed inputs only (`Methods.WF`), fuel-based (fuel = 1000), with
  termination deliberately unproved — Lean's defeq is **known
  non-terminating** (the Abel-Coquand `om` construction is reproduced as
  Lean code in the paper) and the checker known incomplete.

### B.3 Typed NbE, PER models, partiality — convergence is baked into the relation; the real external lemma is determinism

Sources read: Abel's habilitation *Normalization by Evaluation: Dependent
Types and Impredicativity* (2013, https://www.cse.chalmers.se/~abela/habil.pdf);
Abel/Coquand/Dybjer LICS 2007; Abel/Vezzosi/Winterhalter ICFP 2017;
Abel/Öhman/Vezzosi POPL 2018; *Martin-Löf à la Coq* (CPP 2024,
arXiv:2310.06376); the McTT Rocq sources
(https://github.com/Beluga-lang/McTT, ICFP 2025 — paper text itself not
fetchable, claims from sources + abstract); Danielsson ICFP 2012.

* **Partiality**: Abel uses partial applicative structures on paper and
  Bove-Capretta-style *inductive graph relations* (`⟦t⟧ρ ↘ a`) when
  type-theoretic.  Not fuel, not coinduction.  McTT likewise: evaluation is
  an inductive relation, no fuel; the executable NbE lives in an extraction
  layer.  MetaCoq moved fuel *out* of the verified checker; lean4lean keeps
  fuel and specifies everything as *"if it returns … then the judgment
  holds"*.
* **Convergence is baked into semantic membership by definition**, across
  every project surveyed: Abel §3.3 `⟦t⟧(ρ) ∈ B :⟺ ∃b ∈ B. ⟦t⟧(ρ) ↘ b`,
  `A → B = {f | ∀a∈A. ∃b∈B. f·a ↘ b}`; AÖV POPL 2018 defines all judgments
  on whnfs closed under weak-head expansion (existential reduces-to
  clauses), with normalization a *corollary* of the FT (Thm 3.28); McTT's
  `rel_mod_eval`/`rel_mod_app`/`rel_exp` are all ∃-evaluates-and-related.
  **No surveyed project threads convergence as side premises on
  transitivity/uniqueness lemmas.**
* **The hidden external lemma is functionality/determinism of evaluation,
  not convergence.**  AÖV Lemma 2.5 (determinism) is cited in the proofs of
  irrelevance, symmetry, and Transitivity (Lemma 3.9); McTT proves
  `functional_eval` and uses it (via a rewrite tactic) in
  `per_univ_elem_right_irrel` — **which is literally our code-uniqueness
  lemma** (`CodesKUnique`), resolved there by (i) baked-in convergence and
  (ii) functionality.  Abel's pen-and-paper version needs no determinism
  lemma only because evaluation is stipulated to be a partial *function*.
* **Code-indexing is the standard construction.**  Abel's `Set_k`/`El_k`
  inductive-recursive universes of *codes* (§4.3-4.7: the Kripke logical
  relation is defined "by induction on type values `A ∈ Set_k`");
  Abel/Coquand/Dybjer 2007 prove "equal codes yield well-defined equal
  PERs" using injectivity of code constructors; AÖV index by reducibility
  *derivations* (with irrelevance proved a posteriori); CPP 2024 uses
  small induction-recursion (`LR ℓ Γ A P`); McTT indexes the PER by type
  values with the element relation as an output
  (`DF a ≈ a' ∈ per_univ_elem i ↘ R`).  The NbE lane's `TyCode`/`CodesK`
  is squarely in this family.
* **One load-bearing nuance from McTT** (read in its sources): the
  completeness/PER side is ∃-shaped, but the **soundness/gluing side's
  structural Π clause uses a ∀-hypothesis evaluation premise**
  (`∀ b, ⟦B⟧ρ↦c ↘ b → …`) — convergence as hypothesis inside negative
  positions, ∃ only at judgment boundaries.  Determinism reconciles the
  two directions.
* Caveat this survey adds on our behalf (inference, not citation): the
  surveyed theories are normalizing, so their FTs can *produce* the
  baked-in convergence.  Lean's theory is not (lean4lean reproduces the
  Abel-Coquand non-termination witness as Lean code), so a fully ∃-shaped
  relation would make the FT prove normalization we cannot have.  The
  gluing-side pattern (∀-inside, ∃ only where a machine run is in hand)
  is the one available to us — see C.2.

### B.4 Standardization, residuals — the forward dichotomy is van Daalen's Reduction-under-Substitution Lemma, and nobody has mechanized it

Sources read: Endrullis & de Vrijer, *Reduction under Substitution* (RTA
2008, http://joerg.endrullis.de/assets/papers/lambda-reduction-under-substitution-2008.pdf);
Bonelli & Barenbaum, *Superdevelopments for Weak Reduction* (EPTCS 15,
2010, arXiv:1001.4429); Accattoli & Guerrieri, *Open Call-by-Value*
(arXiv:1609.00322); Accattoli–Faggian–Guerrieri, *Factorize Factorization*
(CSL 2021); Lancelot–Accattoli–Vemclefs, *Barendregt's Theory of the
λ-Calculus, Refreshed and Formalized* (ITP 2025); Huet JFP 1994; Stark's
Isabelle/AFP *Residuated Transition Systems* (2022); Guidi (Matita, JFR
2012); Copes/Szasz/Tasistro (Agda, arXiv:1807.01871); McKinna–Pollack.

* **The Θ lane's surviving candidate has a name and a published proof.**
  Van Daalen's RuS Lemma (Endrullis–de Vrijer Lemma 6): given
  `M[x:=L] ↠ N`, there is a prefix context `C` such that `M ↠ C[B₁…Bₙ]`
  with each `Bᵢ` an *x-vector* (a position headed by a substituted
  variable) and `N = C[A₁…Aₙ]` with `Bᵢ[x:=L] ↠ Aᵢ` — i.e. the image
  reduction decomposes into a **core-performed prefix** plus reductions
  **entirely at θ-supplied positions**.  The weak-head specialization,
  the **Square Brackets Lemma** (Lemma 7), is *verbatim* the widened
  waiver + forward dichotomy: `M[x:=L] ↠ λy.P` implies **either**
  `M ↠ λy.P'` with `P'[x:=L] ↠ P` (mirror) **or** `M ↠ xQ` — the core
  reduces to an x-headed term, i.e. `InZoneHeaded` (ThetaRunBatch.md:9751).
  Theorem 13 generalizes to simultaneous substitution; Corollary 1 to
  context filling with capture (telescopes); Theorem 23 makes the prefix
  substitution-independent.  Provenance: van Daalen's 1980 Automath
  thesis; Barendregt Exercise 15.4.8; Barendregt–Manzonetto *A Lambda
  Calculus Satellite* (2022) §1.3.
* **The proof is mechanization-ready**: a four-clause inductive relation
  `⤳` (Lemma 9: x-vector-absorbing / off-zone var / app / λ), stability
  under substitution (Lemma 11), and one commutation lemma
  `⤳ · ↠ ⊆ ↠ · ⤳` (Lemma 12) whose three cases are: step in the prefix
  (mirror), step below the prefix (absorbed into θ-side), step **at the
  interface** — resolved by *refining the prefix context* so the created
  redex counts as below.  **No mechanization of RuS/SqBL was found in any
  prover** (targeted search; absence of evidence).
* **Lévy's redex-creation classification** (Bonelli–Barenbaum §1,
  verbatim): creation types I/II (*upward*) and **III:
  `(λx.C[x Q]) λy.P → C'[(λy.P)Q']`** — substituting a λ for a variable
  in applied position.  Type III is exactly the convergence witness
  (`_tmp/inverse151.lean`); superdevelopments deliberately cover only
  I+II, *because* III is not invertible.  Weak reduction adds a type IV
  (substitution unblocks a weak redex).
* **The backward direction is a theorem when entries are inert.**
  Accattoli–Guerrieri Lemma 42: substitution of *inert* terms (variables
  applied to things — Grégoire–Leroy's "accumulators") creates no
  redexes, and one-step backward simulation holds outright.  So the
  refuted image⟹core transport fails **exactly and only** at λ-supplying
  entries — the widened waiver absorbs precisely the terms Lemma 42
  excludes.  The Θ record and the literature agree to the letter.
* Caveats: RuS is proved for pure β.  Extensions: van Oostrom's *Finite
  Family Developments* (RTA '97) generalizes to orthogonal higher-order
  patterns — but Lean's rules (proofIrrel, K-like ι, η) are **not**
  orthogonal, and **βη breaks head factorization** (Accattoli et al. CSL
  2021, Example 4.6, explicit counterexample; their Prop. 4.5 gives a
  per-rule "linear swap" test that either proves modular factorization or
  hands back a countermodel).  Mechanized standardization since
  McKinna–Pollack uniformly *avoids* residuals/positions in favour of
  Plotkin/Xi/Kashima-style inductive relations (Abel's Abella proof; ITP
  2025; Guidi; Copes et al.) — the same style as the RuS `⤳` relation.

### B.5 Confluence / parallel reduction / postponement — the field's two ways to avoid the false inverse

* **Confluence-based inversion is the dominant kernel technique**
  (MetaCoq): Takahashi triangle for parallel reduction (on context/term
  pairs, because of let-ins) ⟹ "conversion = joinability up to
  α-cumulativity" ⟹ every injectivity/inversion fact, and transitivity
  of the directed relation (*Touring* §3.2.3).  Substitutivity of
  parallel reduction is forward-only (ITP 2025 Lemma 9); **no inversion
  dual exists in the literature** — RuS is the accepted substitute.
* **The Accattoli–Lancelot light-genericity recipe** (FoSSaCS 2024,
  hal-04406343, Thm 3.1 with the proof on p. 9) obtains
  "t{x←u} h-normalizing ⟹ t{x←s} h-normalizing" **without ever
  inverting an image step**: (1) backward *termination* (not steps) by
  contrapositive of forward simulation of divergence; (2) run the *core*
  to its own head normal form; (3) push forward through the substitution
  (forward simulation); (4) induct on the shape of the **core normal
  form** (normal genericity, a 6-case induction).  This is the cheapest
  known form of "forward simulation + join analysis".
* Eta postponement is mechanized (Isabelle `HOL-Proofs-Lambda`,
  `eta_postponement`); Hindley strong postponement fails for β and the
  linear-swap condition is the checkable replacement (CSL 2021 §2).
* A Lean 4 confluence framework now exists: arXiv:2512.09280 (Dec 2025),
  Takahashi/diamond/Newman/Hindley-Rosen, 10,367 lines, zero
  axioms/sorries — infrastructure, not residuals, but relevant if a
  RawReach confluence lemma is attempted.

### B.6 Set-theoretic models — con-leche is past the published frontier; the untyped-conversion obstruction is classical

Sources read: Werner *Sets in Types, Types in Sets* (TACS 1997); Barras
*Sets in Coq, Coq in Sets* (JFR 2010) + habilitation + cic-model repo;
Lee–Werner (LMCS 2011); Timany–Sozeau *Consistency of pCuIC*
(arXiv:1710.03912); Carneiro *The Type Theory of Lean* (MSc 2019,
re-verified quotes); Miquel–Werner *The not so simple proof-irrelevant
model of CC* (TYPES 2002); Werner LMCS 2008; Abel–Coquand LMCS 2020;
Gilbert et al. POPL 2019; Kumar–Arthan–Myreen–Owens JAR 2016.

* **Universe levels**: every model uses one inaccessible (or Grothendieck
  universe) per level, `Typeᵢ ↦ V_{κᵢ}`, cumulativity = ⊆.  Werner/
  Barras/Lee–Werner/Timany–Sozeau handle **concrete metalevel indices
  only — no level variables, no imax**.  **Carneiro 2019 is the only
  model interpreting `imax` and level variables** (valuation semantics;
  levels eliminated *before* the model via type-directed "proof
  splitting", which **needs unique typing**); he notes (§1.2) that
  Barras's **Aczel function encoding** lets soundness skip unique typing
  entirely — and this escape is now load-bearing, because lean4lean
  downgraded unique typing to a conjecture resting on sorried injectivity
  lemmas.
* **The untyped-conversion obstruction is classical** (Miquel–Werner
  §2.4 "the unattainable soundness"): the proof-irrelevant model's
  β-soundness conjecture is *false* on raw terms; restricting to
  well-typed terms is circular with soundness; root cause verbatim —
  *"the identification of all proof-terms requires to forget the domain
  of the corresponding functions."*  Barras (JFR 2010) cites exactly this
  as why *"it is not as easy as expected to build set theoretical models
  of type systems which consider type convertibility as an untyped
  relation"* — his equality is judgmental (typed) throughout.  The v1
  collapse's troubles are this phenomenon, rediscovered mechanically.
* **The four citable forms of "untyped proof-irrelevant conversion
  breaks"**: (D1) Werner LMCS 2008 §2.4 — the non-linear untyped K rule
  *"allows an encoding of Klop's counter-example and thus breaks the
  Church-Rosser property (for untyped terms)"*; (D2) Abel–Coquand LMCS
  2020 — a **closed** Lean term (propext only) with no weak-head normal
  form; (D3) Gilbert et al. POPL 2019, Appendix A — runnable Lean
  subject-reduction failure, and §4.5: with proof irrelevance
  *"conversion can not be defined independently from typing"* and the
  Abel-school logical-relations technique *"does not apply"*; (D4)
  Carneiro's thesis §3.1-3.1.2 — Lean's `⇔` is *"a decidable
  non-transitive underapproximation"*, SR fails directly from
  non-transitivity, CR fails, and the bridge lemma 3.4.(3)
  (`⇔ ⟹ ≡`) requires **both sides already typed at a shared type**.
  **No published abstract statement of "proofIrrel is not a congruence on
  untyped terms" exists** — the δ-sim refutation may be a novel packaging
  of D1+D4 (worth writing up).
* Live shipped-kernel issues (cited by Lennon-Bertrand FSCD 2025):
  lean4#2258 (unit-like eta defeq transitivity failure), #12520
  (function-eta transitivity failure), #3213 (Prop-structure eta —
  *"break[s] both the transitivity and congruence of definitional
  equality"*).  Relevant to the restrictions-are-findings rule: the
  reference kernel itself is verdict-incoherent at these corners.
* **Nobody has ever verified an executable dependent-type-theory checker
  against a set-theoretic model.**  lean4lean: declarative spec only, few
  functions verified, *"the proof of soundness has not been formalized"*
  (TYPES 2025 abstract); MetaCoq: declarative typing with SN/guard/SR
  axiomatized; Barras: model, no checker.  The **only** kernel verified
  against mechanized set-theoretic semantics is HOL Light/Candle
  (Kumar–Arthan–Myreen–Owens, JAR 56:221-259) — which uses **exactly the
  parametric-`SetTheory` architecture** (`is_set_theory (mem : U→U→bool)`
  over a type variable), for a conversion-free logic.  **ConLeche's v1
  fourteen theorems already stand past the published frontier for DTT.**

---

## C. STRATEGY RECOMMENDATIONS

Graded: confidence = how sure I am the route closes what it claims;
cost = engineering volume relative to a "conv-soundness unit" (the
lane's own pricing habit).

### C.1 Θ lane — the three sorries

**Θ-1 (PRIMARY): build the forward dichotomy as the Square Brackets
Lemma, decoupled from the kernel.**  Confidence: **medium-high** for the
statement, **high** that this is the right formulation.  Cost: moderate
(one focused round).

The surviving candidate (ThetaRunBatch.md:9747-9826) is van Daalen's
SqBL with `InZoneHeaded` as the x-vector branch — the head
classification already proved there is the SqBL case split at depth 0.
Build it the literature's way, not as a walk lemma:

1. State it over `substAK` and **gate-free** `RawReach` only (no μ/env
   gates in the induction — `SubstSim.lean`'s design comment already
   argues gates are recoverable at a sort-successful endpoint by
   determinism).  This makes it a pure rewriting lemma with a
   published proof skeleton: the four-clause absorbing relation
   (Endrullis-de Vrijer Lemma 9), substitution stability (L11), and the
   commutation lemma (L12) whose interface case — the created-redex
   row — is resolved by *prefix refinement*, not by inversion.
2. Only the **weak-head corollary** is needed (SqBL, not full RuS):
   "image trace lands on `.sort` ⟹ core reaches a sort, or core
   reaches an in-zone-headed term."  That is strictly weaker than the
   prefix-context version and avoids multi-hole context machinery.
3. **Where the fourth wall would be** (the probe's own honest question):
   RuS is proved for pure β; `RawReach` also has δ/ι/lit/proj rows.
   δ (closed unfolding) and lit rows cannot consume in-zone material and
   should absorb trivially; the risk rows are ι-with-rescue and any
   non-left-linear behavior — Werner LMCS 2008 §2.4 shows an untyped
   *K-like* rule breaks CR via Klop's counterexample, so **check first
   whether the K/eta rescue rows appear in `RawReach`'s induction at
   all** (they carry fabrication data existentially; if their firing
   cannot depend on in-zone equality of two subterms, left-linearity is
   moot).  Run this check as a probe *before* the induction — it is the
   cheap falsifier.
4. Novelty note: no mechanization of RuS/SqBL exists in any prover.
   Landing it would be both the lock's missing step and a publishable
   artifact.

**Θ-2 (COMPLEMENT, cheaper if it fits): the light-genericity recipe —
join at the core's own landing instead of classifying image steps.**
Confidence: medium.  Cost: low-moderate, *if* the join fact is cheap.

Accattoli-Lancelot's proof shape (B.5) transposed to the lock: the lock
rows already hold **core whnf runs** (`w₁`,`w₂` via `ThetaCoreOut` —
ThetaLock.lean:10940-11070); push them forward with the landed sim tiers
(`WhnfSubstSimF`) to get image `RawReach` to `θ(w)`; the landing gives
image `RawReach` to `.sort ℓ`; then a **joinability/determinism fact for
gate-free `RawReach`** identifies the two endpoints' heads, and the
proved head-classification table routes `θ(w)`: `w` a sort ⟹ per-kind
refutations fire; `w` in-zone-headed ⟹ waiver.  No step inversion
anywhere.  The new cost center is `RawReach` confluence (Takahashi
infrastructure now exists in Lean 4, arXiv:2512.09280) — subject to the
same K-row left-linearity check as Θ-1.3; if that check fails, Θ-2 dies
and Θ-1's absorbing-relation route (which does not need confluence) is
the survivor.

**Θ-3 (STRUCTURAL, for the remaining typed residues): supply the typing
companion per-entry, and treat it as the checker's job where the walk
cannot reconstruct it.**  Confidence: high for the mechanism; cost:
already partially paid.

The seven-consumer residue family (irrel/rescue/etaL/etaR/projCong/
certSortAgree/δ-sim) is the literature's typing channel: the reference
kernel *re-infers types of neutrals* when untyped comparison fails
(Lennon-Bertrand §4.4; confirmed in lean4lean's `isDefEqProofIrrel`),
i.e. **the algorithm itself pays typing exactly where the Θ lane's
residues sit**.  Two sub-moves:

* the per-entry repair (`EntryTyped` + `ZoneAnn`, found suppliable at
  both push sites — ThetaRunBatch.md:4703-4770) is the honest,
  already-designed carrier: it is Lennon-Bertrand's "types are still
  present in invariants, silently keeping the algorithm on rails" made
  explicit.  Continue it; do not look for an untyped substitute — B.2
  and B.6 say none exists (lean4lean §8: untyped conversion "is
  unfortunately not an option [for Lean] because of t-proof-irrel").
* where the *walk* cannot recover a fact the *kernel* has (the projCong
  pattern), use the established checker-change lane: change #10
  (structure-name comparison, DESIGN.md:10319) deleted that residue
  outright, and task #152 (λ codomain sort, DESIGN.md:10114) is the
  user-granted precedent for cheap, mode-gated front-door checks.  A
  candidate worth pricing: at the `irrel`/eta-rescue rows, have the
  verified mode record the two inferred types' sort agreement (the
  kernel already computes both types there — this is certification of
  a discarded intermediate, the same species as changes #126-#146, not
  a new reduction-affecting check).  This converts the deepest residues
  from unproved metatheory into certified-run facts.  Defensibility
  note: the shipped kernel is itself verdict-incoherent at these
  corners (lean4#2258/#12520/#3213), so verdict-narrowing deviations
  are findings, not liabilities — report them per the standing rule.

**Θ-4 (GUARDRAIL): stop stating completeness-of-defeq conclusions.**
Confidence: high.  Any lemma concluding `∃ L', defeqLoop … = .ok true`
on transformed inputs is betting against Carneiro §3.1.1
(non-transitivity) and the congruence refutation; the record's own
distinction (A.6) should become a standing statement-design rule:
runs in premises, inductive relations/equations in conclusions.

### C.2 NbE lane — the remaining chain, against the literature

**The chain (BinaryFT → CodeConv → adequacy → capstone) is standard**,
and the closest published structures to crib from are:

* **McTT** for code uniqueness: its `per_univ_elem_right_irrel`
  (uniqueness of the element-relation across two codings of one type)
  is `CodesKUnique`, resolved there by evaluation **functionality**
  (`functional_eval`) — which the lane has (`eval_fun`).  Crib the
  proof shape: simultaneous induction on the code with
  symmetry/transitivity as mutual IHs.
* **AÖV POPL 2018 / Martin-Löf à la Coq (CPP 2024)** for the FT
  architecture; note CPP 2024 deliberately chose **untyped** small-step
  reduction with typing bundled as side conditions at judgment
  boundaries — the lane's `EvalsTo`/ledger design is the same choice,
  independently made.

**Premise-vs-relation for convergence — recommendation: keep the
conditional (partial-correctness) Π clause; get transitivity and code
uniqueness from PER-by-code-induction + functionality, not from baked-in
convergence.**  Confidence: medium-high.  Reasoning:

* The literature bakes convergence in (B.3) — but every surveyed theory
  is normalizing, so their FTs can *produce* the ∃-clauses.  Lean's
  theory is not (Abel-Coquand's closed non-normalizing term, D2);  a
  fully ∃-shaped `BLR` would eventually demand normalization facts that
  are false in the full theory and unprovable even for the slice
  without an SN development.  lean4lean's "if it returns, then…"
  discipline is the published pattern for non-normalizing targets, and
  it is the lane's current shape.
* `BLRTrans`'s two gaps have standard resolutions that don't need
  convergence-in-general: the **domain diagonal** should come from
  proving the PER laws by *structural induction on the code* (symmetry
  and transitivity mutually, IH at subcodes supplies `a ~ a` from
  `a ~ b` at the domain code) — this is how AÖV Lemma 3.9 and McTT do
  it, with determinism reconciling middles; the **middle convergence**
  should be carried as an *equi-convergence* component of the Π clause
  (`u·a` converges iff `v·b` does, for related pairs) — a fact `conv`'s
  verdict can certify (both sides ran), which restores chaining without
  asserting convergence outright.  If equi-convergence proves awkward,
  the honest fallback is the lane's current premise-at-use-site form,
  which the record already justifies ("at the use site the machine ran
  the applications") — that is a legitimate, lean4lean-style shape, not
  a compromise.
* Keep fuel out of the relation (already done — `EvalsTo`, functional
  by `eval_fun`); this matches MetaCoq (fuel exiled from the verified
  core), AÖV (relational big-step), McTT (inductive evaluation).

**One warning transfer from the Θ lane**: `CodeConv`'s open step
("hereditary alignment of `B x` with `B' x` does not follow from the
conversion run") is the created-redex phenomenon in semantic clothing —
a codomain body that is neutral at the fresh point is a Π at a Π-shaped
instance (`ConLeche/NbE/DESIGN.md:516-523`).  The lane's recorded
constraint (*never* attempt machine-level verdict-stability under
instantiation) is exactly right per B.4; the semantic quantification
over instances **is** the relation.  Expect `CodeConv` to need the
binary FT's full strength, not a shortcut through `conv_sound`.

### C.3 Global

**G-1: There is no third route through typed-conversion equivalence.**
Confidence: high.  The MetaCoq equivalence (untyped conversion ⟷ typed
spec) rests on confluence + SR + Π-injectivity, all of which hold for
PCUIC and are refuted or open for Lean's theory (Carneiro §3.1-4.1;
lean4lean's Injectivity sorries; the in-tree TT refutation record,
`ConLeche/TTVerify/DESIGN.md:1580-1660` — Π-injectivity refuted by
propext, SR refuted by design).  The TT bridge is moreover deleted
(T7b, 2026-08-29); resurrecting it for this purpose would re-buy a
refuted program.  The field's honest position is: for Lean-shaped
theories these are open research problems (lean4lean: "theorems which
we can't prove :(").

**G-2: Recognize the frontier position and portfolio accordingly.**
Nobody has verified an executable DTT checker against a set model
(B.6); the v1 fourteen `_R` theorems are already past the published
frontier, and the collapse-free upgrade is research, not engineering.
Concretely:

* **Θ lane**: one more focused round on Θ-1 (SqBL), with Θ-1.3's
  falsifier probe first.  If it lands, the lock closes on real
  mathematics with a first-mechanization bonus.  If the probe or the
  induction hits the fourth wall in the non-β rows, take Θ-3's
  checker-certification exit and close the tier at bounded cost rather
  than continue statement-space search — the record shows that search
  has linear cost per candidate and adversarial candidates are
  plentiful.
* **NbE lane**: continue as the strategic successor — its measured
  deletions (substitution transport ~170 vs ~8.6k lines; environment
  weakening 397 lines unconditional) are structural, and its remaining
  chain matches published proof shapes almost clause-for-clause (C.2).
  The Θ lane's hardest lessons (provenance-first, typed residues,
  created redexes) are already encoded in its design constraints.
* **Methodology, both lanes**: adopt provenance-first statement design
  as a standing rule (A.5) — new walk/machine-level statements
  quantify over checker-built configurations by construction, with
  extensional side conditions derived, not assumed.  And keep the
  model applied forward only (`univ ∘ eval`), never inverted — the
  model-side arbitration refutations and Miquel-Werner say the same
  thing from two sides.

**G-3: Publishable findings are accumulating — bank them.**  The
mechanized congruence refutation (no published abstract form exists —
B.6), the projCong reference-kernel gap (ThetaRunBatch.md:7291, now
checker change #10), and a SqBL mechanization would each be citable;
the first and third jointly make a paper-shaped unit ("untyped
conversion metatheory for a Lean-shaped kernel: refutations and the
reduction-under-substitution repair").

---

## Appendix: what each of the three sorries waits on, mapped to the recommendations

| sorry | current blocker (census, ThetaRunBatch.md:6954) | recommendation |
|---|---|---|
| `layerRunCell_of` (ThetaLock.lean:2499) | the deep object `SortDefeqThetaT` (θ-stability of kernel runs) | Θ-4 says the completeness form is the wrong currency; Θ-3's certification exit or the (π-premise) route from the convergence entry |
| `runStepF_step` (:8375, 3/25 arms left) | three named residues, typed (etaL/etaR/projCong-successor) | Θ-3 (per-entry typing carrier; checker-certification for walk-unrecoverable facts) |
| `thetaLoopLock_of` (:11057) | composite-column export + seam-row disposal at sort landings | Θ-1 (SqBL dichotomy) with Θ-2 as the cheaper variant if the K-row check passes |
