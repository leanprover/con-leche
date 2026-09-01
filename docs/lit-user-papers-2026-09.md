# Literature report: three user-supplied papers (2026-09-01)

Scope: the three papers the user supplied as "slightly related". All three PDFs were
downloaded and read in full (pdftotext, `paper1.txt`/`paper2.txt`/`paper3.txt` in this
scratchpad). Assessed against the project's lanes:
(a) Θ lane — forward dichotomy / van Daalen RuS for untyped whnf/defeq under telescope
substitution; open: dichotomy engine over a kit with non-left-linear K-like rows, the
ι-branch asymmetry (stuck-major rescue runs infer/whnf the substituted side never runs),
lock conclusion as deterministic-run-output equations.
(b) NbE lane — glued NbE + untyped conversion verified via BLR/CodesK; BLOCKED on the
spine-shortcut coherence lemma ≡ application congruence of untyped conv ≡
verdict-stability-under-instantiation; options: confluence-licensed slice-1 tier vs
re-planning the app case's code transport; slice 2 = proofIrrel where congruence fails
for Lean's theory.
(c) Background — set models of DTT with universes; nobody has verified an executable
checker against a set model; lean4lean unique-typing/injectivity open.

Cross-check: headings of `docs/lit-metacoq-lean4lean-2026-09.md`,
`docs/lit-nbe-per-partiality-2026-09.md`, `docs/lit-standardization-setmodels-2026-09.md`,
`docs/retrospective-2026-09-01.md` were read; none of the three papers below is covered
there (the surveys cite their *predecessors*: Abel et al. 2018, Gilbert et al. 2019,
Pujet et al., Abel–Coquand 2020, lean4lean). All three are new inputs.

The three papers form one coherent cluster: the "metatheory of Lean's actual type
theory" program, run from two directions — Carneiro/Coquand et al. attacking
injectivity without normalisation (paper 1), and the Gallinette group attacking
Acc-in-SProp (paper 2) and strong transport / definitional UIP (paper 3).

---

## Paper 1 — Definitional Inversion, Without Normalisation

**Bibliographic data.** Mario Carneiro, Thierry Coquand (Chalmers), Adrien Frabetti
Mathieu (ENS PSL/IRIF), Meven Lennon-Bertrand, Paul-André Melliès (Univ. Paris
Cité/INRIA/CNRS/IRIF), Stephanie Weirich (UPenn). *Definitional Inversion, Without
Normalisation.* arXiv:2607.13662v1 [cs.LO], 15 Jul 2026. Preprint in ACM format with a
"Note to reviewers" — under submission, venue not yet determined (see COULD NOT VERIFY).

**What it proves.** A new proof technique, based on Scott-domain/finitary-projection
models, for *definitional inversion* (injectivity + no-confusion of type constructors)
in dependent type theories, **independent of both normalisation and confluence**, in a
weak ambient metatheory. Abstract (p. 1): "We contribute a new proof technique, based on
domain theory, to prove key meta-theoretic properties of dependent type systems:
definitional inversion properties, i.e. injectivity and no-confusion of type
constructors. This proof technique is independent of normalisation, and indeed applies
even for the 'type-in-type' rule". Explicitly motivated by kernel-verification projects
(p. 1): "intended for, the metatheory of systems such as Idris, Lean, or dependent
Haskell, whose underlying type theory is known to be non-normalising, as well as
projects such as MetaRocq or Lean4Lean, where Gödel's second incompleteness theorem
means we cannot show normalisation of the object logic in itself."

Core system MLTT_η (Π with β+η, 𝒰:𝒰, conversion as a *typed judgement*), for which
"subject reduction was open" (§1, p. 3). Machinery: domain D ≅ [D⇒D] + ↑(D×[D⇒D]) + ↑1
with λ(⊥)=⊥ (that coalescing is what validates η, §2.1/§2.5); semantic typing on compact
elements (Fig. 2); a logical relation between *syntactic* terms indexed by *semantic
witnesses* (compacts) instead of normal forms (§2.6), with neutrals collapsed to ⊥.
Metatheoretic cost is tiny (§1, p. 4): "we do not need strong logical principles, such
as induction-recursion, to show this: basic induction on natural numbers is enough."

Main results (all for MLTT_η, extended in §3):
- Thm 2.32 disjointness (Π ≢ 𝒰); Cor 2.37 **injectivity of Π** ("If Γ ⊢ Π_{x:A}B ≡
  Π_{x:A′}B′ : 𝒰, then Γ ⊢ A ≡ A′ : 𝒰 and Γ, x:A ⊢ B ≡ B′ : 𝒰", §2.8);
- Thm 2.38 **subject reduction**, Thm 2.39 progress — first for this system;
- §3 extensions, each by adding codes to the domain: Σ/unit with η (surjective
  pairing — the case where untyped confluence is dead, Klop), a fixed-point combinator
  Y (explicitly non-normalising), ℕ with large elimination, proof-relevant Id with
  transport, and a **universe Prop of strict propositions with definitional proof
  irrelevance** (§3.6: model constraint "if u :ₙ a :ₙ Prop then u = ⊥");
- Thm 3.1: definitional UIP (the K rule) is **not derivable** in MLTT_η — the model
  separates ref_⊥ from ref_U;
- sort injectivity 𝒰ᵢ ≡ 𝒰ⱼ ⇒ i = j for stratified hierarchies by sharpening one clause
  (§3, "Universe hierarchies"), with the model collapsing all levels to a single U —
  "the model may forget as much as it likes, as long as it keeps elements for (1)
  injectivity properties we wish to obtain, and (2) constructors that can be eliminated
  by later operations" (§3, p. 18).

Mechanised **three times** (§4): Agda (𝒰:𝒰, Π, Y, ℕ, Id), **Lean** (all of §3 incl.
Σ/1 and Prop; Id transport only), Rocq (partial; uses funext/propext/proof-irrelevance
axioms). Formalisations are anonymised supplementary material (not fetchable).

Explicit limitations stated by the authors: no inversion for *neutrals* (§2.6: "our
technique does not directly apply to obtain definitional inversion properties for
neutrals, such as the fact that x M ≡ y N implies…"); and conclusion (§5, p. 25): "we
still are far from having covered all the nitty-gritty details of these systems, around
e.g. (co-)inductive types or **proof irrelevance with axiom K**, and scaling our
approach remains a significant challenge." Also §5 on lean4lean specifically:
"Lean4Lean, on the other hand, has focused on feature parity from the start, meaning
that until now we lacked good meta-theoretic backing to verify the algorithm. Hopefully
our proof technique will help unblock both projects."

**Bearing on (a)/(b)/(c).**
- **(c) — strongest hit.** This is the live attack on exactly the lean4lean open
  conjectures (Π-injectivity/no-confusion → unique typing), by lean4lean's own author
  plus the MetaRocq/Gallinette axis, and one of the three mechanisations is *in Lean*
  intended "for future inclusion in the Lean4Lean … projects" (§4). It does not close
  those conjectures for Lean's real theory yet (no inductives beyond ℕ/Id, no K-flavoured
  proof irrelevance, no defeq algorithm), but it changes the outlook from "open, no
  technique" to "technique demonstrated on the hard fragments (η + non-normalising +
  weak metatheory), scaling in progress". Any setlec claim of the form "lean4lean's
  injectivity is an open conjecture" should now carry this citation as the active
  frontier. Note the technique proves properties of *declarative typed conversion*, not
  of an executable checker, and uses a *domain* model, not a set model — so setlec's
  "nobody has verified an executable DTT checker against a set model" novelty claim is
  untouched.
- **(a) — indirect.** The paper is the field's cleanest confirmation of the premise
  behind the Θ lane's caution about K-like rows: "The extensionality equation defeats
  confluence-based approaches" (§1) and the whole point of the paper is to *route
  around* confluence rather than repair it. It does not provide a RuS/dichotomy lemma
  and is not a substitute for the Θ engine. One strategic pointer (§5, p. 25): with
  inversions "established by other means, it seems possible to rely on confluence to
  show other properties" — i.e., semantic-inversion-first, typed-confluence-second,
  citing Carneiro 2019. That is structurally the setlec architecture (model first,
  syntactic engine second) stated as a program by others; usable as external validation
  in DESIGN-level argumentation, not as a lemma.
- **(b) — mostly negative information, which is itself useful.** The paper does *not*
  supply the missing spine-shortcut lemma: its logical relation is over declarative
  conversion, its neutrals are degenerate (⊥), and the authors explicitly defer
  proof-irrelevance-with-K (Lean's slice-2 theory). Its Thm 3.1 (definitional UIP
  underivable in MLTT_η) is about the theory *without* the K rule, so it neither
  contradicts nor helps slice 2. **No current ruling changes.**

**Verdict.** Not "slightly related" — this is the most on-target external development
for setlec's (c) frontier, though it delivers a technique and a program rather than a
lemma setlec can import today.

---

## Paper 2 — Definitional Proof Irrelevance Made Accessible

**Bibliographic data.** Thiago Felicissimo, Yann Leray, Nicolas Tabareau (Inria
Gallinette), Loïc Pujet (ICube, Strasbourg), Éric Tanter (U. Chile & Inria), Théo
Winterhalter (Inria Deducteam). *Definitional Proof Irrelevance Made Accessible.*
LICS 2026 (41st Annual Symposium on Logic in Computer Science), LIPIcs vol. 380
(eds. Faggian, Katoen), article 41, pp. 41:1–41:26. DOI 10.4230/LIPIcs.LICS.2026.41.
Rocq formalization on Zenodo (10.5281/zenodo.20213920).

**What it proves.** Reconciles Acc (accessibility) elimination into Type with a
definitionally proof-irrelevant universe — the exact combination that makes Lean's
conversion undecidable. Background facts restated with citations (§1, p. 41:3):
"elimination of Acc breaks decidability of conversion regardless of function
extensionality or (im)predicativity [Gilbert et al.]"; on Lean's mitigation: "the
implementation of definitional equality becomes different from its specification (e.g.,
it is no longer transitive)… Lean makes all well-foundedness proofs opaque by default
since v4.19 (2024)."

Two theories over CIC^obs (observational equality in SProp):
- **T=Acc**: Acc-elimination computes only *propositionally* (Acc-el-prop, Fig. 2) →
  decidable typing, injectivity of function types (inherited from CIC^obs, §2 end);
- **T≡Acc**: adds the definitional rule Acc-el-def (Lean-like) → conversion
  undecidable, but **canonicity holds** (Cor 12/13, §3), proven via an Abel-et-al-style
  logical relation whose Ω-level clause is *mere well-typedness* (no proof reduction),
  with the Acc-el case handled by **well-founded induction over a semantic relation
  extracted from the set model** (Assumption B).
- **Conservativity** (Thm 16, §4): T≡Acc is conservative over T=Acc, via
  Winterhalter–Sozeau–Tabareau's ETT→ITT decorating translation with heterogeneous
  equality; and since proofs are irrelevant, the costly elaboration can be skipped in
  implementations ("the proof system may as well save the completed proof as an opaque
  constant", §1). Corollary 17: propositional canonicity for T=Acc.
- **Set-theoretic model** (§5): consistency of both theories + discharge of Assumptions
  A/B, "in intuitionistic ZF set theory [IZF_R] with a countable hierarchy of
  Grothendieck universes, embedded in the type theory of Rocq… we do not use Rocq's
  dependent types, meaning that we are effectively working in HOL with ZF axioms"
  (p. 41:16). Key device for model-level injectivity (p. 41:16–17): "we interpret types
  as triplets which include their set of elements, an integer encoding their head type
  former, and a list of subtypes on which we want injectivity" — e.g. Π̂ carries
  ⟨ℓ; n; A; graph of B⟩ as its label so that equal Π-sets have equal domains/codomains.
  The model validates arbitrary SProp axioms that hold in it (funext, propext, LEM).
  Caveat stated by the authors (p. 41:18): the SOGAT-interpretation step "is only
  carried out on paper"; the rest is formalized in Rocq.
- Implementation in a modified Rocq (local rewrite rules; `#[rewrite_rules(Acc_el_def)]`
  proof-mode switch), with benchmarks (gcd, System F evaluator) showing definitional
  unfolding beats propositional rewriting by orders of magnitude (Tables 1–2).

**Bearing on (a)/(b)/(c).**
- **Memory item "Acc large-elim outlook"** (upstream may remove Acc large elimination):
  this paper is the *design blueprint* for that move — ambient decidable theory with
  propositional unfolding + an opt-in definitional mode that is conservative — and it
  documents Lean already half-way there (opaque wf proofs since v4.19). Strengthens the
  outlook; no setlec action needed now, but if Lean adopts a T=Acc-shaped kernel, the
  checker's whnf-fuel frontier at wf-recursion unfoldings (init-full memory) would
  shrink by design.
- **(c)**: the §5 model is the closest published relative of setlec's own set-theoretic
  tier: IZF + ω Grothendieck universes, formalized (modulo the paper-only SOGAT step),
  Ω interpreted as P{∅} with proof irrelevance for free, Acc via the impredicative
  set-theoretic encoding, and — most transferable — the **head-tag/label triple trick**
  for making type formers injective *in the model*, delivering semantic no-confusion
  (Assumption A) for closed terms. If setlec ever needs model-level Π-injectivity or a
  "no closed proof of Eq between differently-headed types" fact, this is the reference
  construction. It models a *declarative theory*, not an executable checker, so the
  setlec novelty claim stands.
- **(a)/(b)**: essentially none. The canonicity logical relation deliberately never
  evaluates proofs and says nothing about untyped algorithmic conversion; nothing here
  touches RuS, the dichotomy engine, or verdict stability.

**Verdict.** Genuinely "slightly related" for the two live lanes; its value to setlec
is concentrated in (c) (the formalized IZF model with head-tagged types) and in
corroborating the Acc-outlook memory. One paragraph of relevance, kept: it is the
paper that turns "Lean's Acc+proofIrrel undecidability" from folklore-with-citations
into a worked dual-theory design with a formalized set model, and both of its
companion results (canonicity machinery, conservativity translation) are the imported
foundations of paper 3, which *is* relevant to lane (b).

---

## Paper 3 — Consolidating Equality in a Proof Irrelevant Universe

**Bibliographic data.** Thiago Felicissimo, Rafael Bocquet, Kenji Maillard, Nicolas
Tabareau (Inria Gallinette), Éric Tanter (U. Chile), Théo Winterhalter (Inria
Deducteam). *Consolidating Equality in a Proof Irrelevant Universe.* HAL preprint
hal-05688985v1, submitted 10 Jul 2026 (no venue on the PDF; two Rocq formalizations,
one per proof, built on Poiret et al. FSCD 2026 and on paper 2's artifact).

**What it proves.** The metatheory of *Lean-style equality in SProp with strong
transport* (elimination into Type). The theory TT^sEq = MLTT + impredicative
proof-irrelevant 𝒰_Ω hosting Eq, with transp computing by either
- **TranspIrr** (Lean's rule): `transp A x P p x e ≡ p` whenever the endpoints are
  convertible, or
- **TranspMotive** (their novel strengthening): `transp A x P p y e ≡ p` "whenever
  P[x:=a] ≡ P[x:=b]" (Fig. 2) — fires on convertibility of the *motive instances*.

Main results:
1. **Decidability of conversion** (Cor 4.13), for both rules: "The proofs with
   TranspIrr in particular solve the open problem raised by Abel and Coquand [2020]
   regarding decidability of conversion" (§1/Formalization note, p. 5). This is the
   first positive decidability result for the Lean-shaped SProp-equality fragment
   (η for functions included; no inductives beyond ℕ; no Acc — that piece is paper 2's,
   and per fn. 2 full Lean conversion stays undecidable because of Acc).
2. **Injectivity of type formers** (Cor 4.15) for Π (with level equalities) and Eq.
3. **Propositional canonicity** (Cor 5.6) assuming FunExt + propositional injectivity
   axioms, via conservativity of CIC^obs over TT^sEq (Thm 5.5, Hofmann/Winterhalter-style
   decorating translation) + CIC^obs canonicity; consistency en passant; supports
   PropExt/LEM/choice but "not Hilbert's ε operator, for which any form of canonicity
   seems hopeless" (§1).
4. **Correctness of evaluation-via-erasure** (Thm 6.1): erase proofs/transports/types
   to an untyped target, evaluate, reflect the result as a propositional equality —
   "a first step towards validating a native evaluation mechanism as provided in Lean"
   (i.e. `native_decide`, whose current status is "an unverified axiom in any Lean
   proof obtained through this mechanism" — §1, citing ofReduceBool/ofReduceNat).
   Implemented as Rocq Ltac2 tactics; TranspMotive itself implemented in a PR slated
   for Rocq 9.3.

Proof technique for (1) — the part that matters to setlec:
- Normalization is **typed through and through**. Normal forms include a pseudo-term
  ✠_P for "an arbitrary proof of P" (proofs are never reduced, only typed — §4.2: the
  usual whnf-based clause "would not work here: indeed, by Abel and Coquand's [2020]
  counterexample, their weak-head normal forms might not exist"), and annotated
  neutrals `transpNf(…, P_a^nf, …, P_b^nf, …)` carrying the normal forms of both motive
  instances. §4.1 (p. 13): "Untyped one-step reduction and weak-head normal and neutral
  forms are all indexed by a typed context, which may seem irrelevant, but is necessary
  due to the normalization premise of Rule Transp." The non-left-linear TranspMotive
  guard is realized as *mutually defined reduction and normalization* (Rule Transp
  requires `P[x:=a] ⇓ Tⁿᶠ` and `P[x:=b] ⇓ Tⁿᶠ`; TranspNe fires when `P_a^nf ≠ P_b^nf`).
- **Instability under non-injective substitution is explicit** (§4.1, p. 13): "the
  condition of having distinct normal forms is not stable under renaming. For instance
  the variables x, y are distinct normal forms in context x:𝒰, y:𝒰 that are equated
  after renaming by [z/x, z/y]… they are still preserved by injective renamings"
  (Lemma 4.4); the whole logical relation is Kripke over *injective renamings only*
  (LRAtPi).
- The **convert middleman** (§4.3): a silent coercion `convert(A,B,t)` (conversion-wise
  the identity, Lemma 4.3) with OTT-style reduction rules that recurse on type heads
  and get *stuck* — a "transient neutral" — when the heads differ; this lets them prove
  "Reducibility of convert" (Lemma 4.10: reducibility transports along *mere
  conversion* between two independently-reducible types) **before** any no-confusion or
  injectivity is available, breaking exactly the circularity "conversion-stability of
  the logical relation is needed during the fundamental lemma but provable only after
  it" (§4, p. 9–10). Transient neutrals are refuted afterwards (Cor 4.14). Determinism
  of the mutually-defined reduction/normalization package is Lemma 4.5.
- Open conjecture left by the authors (§4.4 end): "does strict canonicity hold for
  TT^sEq in the absence of additional propositional axioms such as FunExt?"
- Related work (§7) places Felicissimo–Winterhalter's typed-confluence line as strictly
  weaker here: "such confluence techniques cannot handle η-conversion for functions,
  and are also not enough to prove decidability of conversion."

**Bearing on (a)/(b)/(c).**
- **(b) — the main event.** Three distinct consequences:
  1. *The slice-2 ruling is corroborated, not overturned.* The context's claim —
     application congruence of *untyped* conv fails under proofIrrel and the official
     kernel pays by re-inferring types inside defeq — is exactly mirrored here: the
     complete algorithm this paper verifies is typed at every judgment, compares proofs
     by *typing* (✠_P) rather than reduction, and its neutral side-conditions
     (`P_a^nf ≠ P_b^nf`, `A^nf ≠ B^nf`) survive only **injective** renamings — a crisp,
     machine-checked formal locus of verdict-instability-under-instantiation
     (instantiating a shared fresh variable is a non-injective substitution). So: the
     ruling that untyped verdict-stability cannot be licensed for the proofIrrel slice
     stands, now with a stronger citation than issue #3213 folklore.
  2. *A third option for the blocked app case.* The convert-middleman is a reusable
     recipe for precisely the shape of setlec's blocker: needing to transport a
     reducibility/CodesK witness along a mere conversion (the spine-shortcut coherence)
     during the fundamental proof, before congruence/no-confusion are available. The
     recipe: add a semantic stuck-coercion to the domain of codes, prove its
     reducibility by double induction on the two code witnesses (their Lemma 4.10),
     run the fundamental lemma, then refute the stuck cases (their Cor 4.14). This is a
     concrete re-plan candidate for "re-plan the app case's code transport" that does
     not require the βδ-confluence tier. Cost: the BLR/CodesK domain grows by transient
     neutrals, and reduction/normalization may need to be mutually defined. Whether it
     fits the glued-NbE machine (vs their term-rewriting setting) needs a design pass;
     it does not import as a lemma.
  3. *Slice-2 upgrade in outlook.* For the βη + SProp-Eq + strong-transport fragment
     there now exists a complete, formalized, *typed* decision procedure with
     injectivity (Cor 4.15) — i.e. the "kernel pays by re-inferring types" strategy has
     a machine-checked completeness counterpart for the first time. If setlec's slice 2
     is ever specified as "certified against a typed reference algorithm", this is that
     reference. (Still short of Lean: no general inductives, no K for Id — their Eq has
     UIP definitionally by SProp placement, which is the Lean situation — and no Acc.)
- **(a) — technique precedent, not a lemma.** TranspMotive is a genuinely
  **non-left-linear K-like rule** (it fires on a derived equality of two computed
  objects), and the paper shows one disciplined way to make an engine deterministic
  around such a rule: internalize the rule's guard as normalization side-conditions,
  add an *annotated neutral* (transpNf carries P_a^nf, P_b^nf — the outputs of the
  extra subsidiary computations) for the guard-failure branch, and prove determinism
  (Lemma 4.5) for the mutually-defined package. Structurally this is the same move the
  Θ lane needs for the ι-branch asymmetry: the stuck-major rescue path's extra
  infer/whnf calls become recorded outputs in the trace object, and the lock conclusion
  becomes determinism of the enriched relation. Also a warning label for the Θ
  dichotomy: their guarded-rule verdicts are stable only under injective renamings —
  telescope substitution is not injective, so any dichotomy clause whose guard compares
  computed normal forms will exhibit exactly the substituted-side/unsubstituted-side
  divergence the Θ lane already fights; the paper confirms this is intrinsic, not an
  artifact of setlec's kernel.
- **(c)**: consistency here is inherited from Pujet et al.'s set model via CIC^obs
  (Assumption A again discharged semantically by head-tagged types); still no
  executable checker verified against a set model — novelty claim intact. The
  evaluation-via-erasure theorem is also the first formal justification schema for
  `native_decide`-style mechanisms, relevant background if setlec ever meets streams
  using ofReduceBool/ofReduceNat (currently out of scope: no-nonstandard-axioms ruling
  treats tolerated-axiom uses by skip-and-decline).

**Verdict.** The most operationally relevant of the three for the blocked NbE lane:
it does not unblock the ruling by licensing untyped instantiation-stability (it
reinforces that this is impossible for the proofIrrel slice), but it contributes (i) a
formal, citable incarnation of the instability (injective-renaming-only stability of
distinct-normal-form guards), and (ii) the convert-middleman recipe as a concrete
candidate for the "re-plan the app case" branch of the ruling.

---

## Cross-cutting summary for the rulings

- **No standing ruling is invalidated.** In particular: conditional-forms ruling
  untouched; slice-2 "congruence fails for Lean's theory" *confirmed* with sharper
  citations (paper 3 §4.1, Lemma 4.4, TranspNe); the "nobody verified an executable
  checker against a set model" novelty claim survives all three papers.
- **New candidate technique for the (b) blocker**: paper 3's convert middleman
  (transport reducibility along mere conversion via a stuck semantic coercion, refuted
  post-fundamental-lemma) — a third option beside "confluence-licensed slice-1 tier"
  and the previously vague "re-plan app-case code transport"; it makes the re-plan
  branch concrete.
- **New candidate technique bank for (a)**: paper 3's mutual reduction/normalization
  with annotated neutrals + determinism lemma, as a template for the ι-branch
  asymmetry and the lock conclusion; paper 1 as the authoritative statement that
  confluence-free inversion is viable when K-like/η rows kill CR (validating the
  model-first architecture).
- **(c) frontier moved**: lean4lean injectivity/unique-typing now has an active,
  partially-mechanized attack (paper 1, with Carneiro as first author and a Lean
  formalization earmarked for Lean4Lean). Watch for the de-anonymized artifact and a
  proof-irrelevance-with-K extension — that extension is the piece that would matter
  to setlec's slice 2.

---

## VERIFIED FACTS

Read directly in the papers' full text (files paper1.txt / paper2.txt / paper3.txt in
this scratchpad):

1. Paper 1 authorship, arXiv id 2607.13662v1 (15 Jul 2026), abstract claims, MLTT_η
   definition, Thm 2.31/2.32, Cor 2.37, Thm 2.38/2.39, Thm 3.1, the §3 extension list
   (Σ/1/Y/ℕ/Id/Prop), the triple mechanization table (Agda/Lean/Rocq) and its coverage
   gaps, the Rocq version's use of funext/propext/PI axioms, the "basic induction on
   natural numbers is enough" claim, the neutrals limitation, and the §5 statements
   about Lean4Lean/MetaRocq and about proof-irrelevance-with-K being future work.
2. Paper 2 authorship, LICS 2026 vol. 380 art. 41 (41:1–41:26), the T=Acc/T≡Acc rule
   split (Acc-el-prop vs Acc-el-def), Thm 11 (fundamental), Cor 12/13 (canonicity,
   effective canonicity), Thm 16 (conservativity), Cor 17, §5 model in IZF_R + ω
   Grothendieck universes in HOL-over-ZF style, the head-tagged-triple interpretation
   of types, Assumptions A/B and their discharge, the authors' statement that the SOGAT
   interpretation step is paper-only, Lean v4.19 opaque-wf-proofs claim (their
   assertion), and the benchmark tables' headline shape.
3. Paper 3 authorship, hal-05688985v1 (10 Jul 2026), TranspIrr vs TranspMotive rules
   verbatim, the claim of solving Abel–Coquand's open decidability problem, Cor 4.13
   (decidability), Cor 4.14 (no transient neutrals), Cor 4.15 (injectivity), Lemma 4.4
   (injective-renaming-only stability, with the x,y/z counterexample), Lemma 4.5
   (determinism), Lemma 4.10 (reducibility of convert), Thm 5.5 (conservativity of
   CIC^obs), Cor 5.6 (propositional canonicity), Thm 6.1 (erasure correctness), the ✠
   pseudo-normal-form / typed-context-indexed-reduction design, the strict-canonicity
   open conjecture, and the §7 comparison to Felicissimo–Winterhalter typed confluence.
4. The three existing setlec surveys' section headings (only headings, per instructions)
   contain none of these three papers.

## COULD NOT VERIFY

1. Paper 1's venue/peer-review status (arXiv v1 only; ACM format + "Note to reviewers"
   ⇒ under submission somewhere, target unknown) and its anonymized formalizations
   (links are anonymized; not fetched; axiom footprints and completeness of the Lean
   development unchecked).
2. Paper 2's Zenodo artifact and Yann-Leray/acc-in-sprop repo contents (not downloaded;
   the formalization-gap statement is the authors' own). The claim that CIC^obs "will
   be available in a future release of Rocq".
3. Paper 3's publication venue (pure preprint), its two Rocq artifacts, the Rocq 9.3
   PR for TranspMotive, and the Poiret et al. FSCD 2026 dependency (cited as accepted;
   not read). Its formalization covers only two proof-relevant universe levels (stated
   by the authors; the countable-hierarchy presentation is paper-level).
4. All performance numbers (papers 2/3) taken at face value.
5. Whether the convert-middleman technique actually composes with setlec's glued-NbE /
   CodesK machinery (design question, not a literature fact).
